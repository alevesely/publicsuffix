// test.c - written by ale in milan on 27 jan 2015
// use Public Suffix List (PSL)
// see https://publicsuffix.org/list/
//
// compile:
// gcc -W -Wall -std=gnu99 -g -o test test.c -lidn2 -lunistring
//
// run:
// ./test fulltest.dat -t
//
// This file contains scrap code to make a library that uses the PSL.
// That is a header, an implementation, and client code chapters.
// Search ----- (five dashes) for subdivisions.

/*
Copyright (C) 2015-2021 Alessandro Vesely

This code is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This code is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License version 3
along with this code.  If not, see <http://www.gnu.org/licenses/>.
*/

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdint.h>
#include <search.h>
#include <ctype.h>
#include <errno.h>
#include <syslog.h>

#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>

// LIBIDN2
#include <iconv.h>
#include <idn2.h>
#include <unicase.h>
#include <unistring/version.h>

#include <assert.h>

// ----- imported utility function -----
#include <stdarg.h> 

void fl_report(int severity, char const* fmt, ...)
{
	char const *logmsg;
	switch (severity) // see liblog/logger.c
	{
		case LOG_EMERG:
		case LOG_ALERT:
			logmsg = "ALERT";
			break;

		case LOG_CRIT:
			logmsg = "CRIT";
			break;

		case LOG_ERR:
		default:
			logmsg = "ERR";
			break;

		case LOG_WARNING:
			logmsg = "WARN";
			break;

		case LOG_NOTICE:
		case LOG_INFO:
			logmsg = "INFO";
			break;

		case LOG_DEBUG:
			logmsg = "DEBUG";
			break;
	}
	
	fprintf(stderr, "%s: ", logmsg);
	va_list ap;
	va_start(ap, fmt);
	vfprintf(stderr, fmt, ap);
	va_end(ap);
	fputc('\n', stderr);
}

// ----- header to be included by client -----
#if !defined PUBLICSUFFIX_H_INCLUDED

struct publicsuffix_trie;
typedef struct publicsuffix_trie publicsuffix_trie;

char *org_domain(publicsuffix_trie const *pst, char const *domain);
void publicsuffix_done(publicsuffix_trie *pst);
publicsuffix_trie *publicsuffix_init(char const *fname, publicsuffix_trie *old);

// define a reporting function for this library item
#if defined __GNUC__
__attribute__ ((format(printf, 2, 3)))
#endif
static void (*do_report)(int severity, char const* fmt, ...) = &fl_report;

#define PUBLICSUFFIX_H_INCLUDED
#endif

// ----- library code -----
#if ! defined NDEBUG
#define DEBUG_PUBLICSUFFIX 1
#endif

/*
* This code reuses Bryan McQuade's design of domain-registry-provider, see
* https://code.google.com/p/domain-registry-provider/wiki/DesignDoc
*
* This algorithm is documented below, after generic function(s), besides
* structures definitions.
*/

static size_t reverse_labels(char *domain, size_t len, char ***rtc_labels)
/*
* Domain must be a valid, normalized utf-8 domain name.
* It is modified by replacing dots with '\0'.
* The third argument, labels, will be set to a NULL-terminated array of
* pointers to the resulting labels, or NULL for failure.
* The return value is the number of non-NULL labels, or 0 for failure.
*/
{
	assert(domain);
	assert(strlen(domain) == len);
	assert(rtc_labels);

	// trim trailing and leading dots
	while (len > 0 && domain[len-1] == '.')
		domain[--len] = 0;

	while (len > 0 && *domain == '.')
	{
		++domain;
		--len;
	}

	/*
	Various objects and parameters in the DNS have size limits.  They are
	listed below.  Some could be easily changed, others are more
	fundamental. --RFC 1035

	labels          63 octets or less
	names           255 octets or less

	That is not exact for utf-8 encoding.  However, max 128 labels is ok.
	*/
	*rtc_labels = NULL;
	if (len == 0 || len > 255*4)
		return 0;

	char *labels[128];
	size_t count = 0;
	
	// backward, starting off-string
	char *prev = &domain[len], *s = &domain[len];
	while (len-- > 0)
	{
		int ch = *(unsigned char*)--s;

		if (ch == '.' || len == 0)
		{
			char *label = s;
			if (ch == '.')
			{
				*s = 0;
				++label;
			}

			size_t l_len = prev - label;
			if (l_len == 0 || l_len > 63*4)
				return 0;

			labels[count] = label;
			++count;
			prev = s;
		}
	}

	char **rtc = malloc(sizeof(char*)*(count + 1));
	if (rtc)
	{
		memcpy(rtc, labels, sizeof(char*) * count);
		rtc[count] = NULL;
	}
	*rtc_labels = rtc;

	return count;
}

/* 
* A suffix trie is used to store rules, where each node represents a 
* label.  Root nodes are the TLDs.  A node's children are the labels on
* its right.  Labels are stored in a string table, sorted.
*
* A node holds the offset in the string table of the label it represents.  
* The final nodes are stored in three arrays, one for all nodes, one for
* non-leaf nodes only and one for flags.  This is done so in order to
* save space:  Leaf nodes don't need trie_node's elements, the array
* index of their first child and the total number of children.  And
* 1-byte flags would result in odd-sized structures.  However, in order
* to keep arrays parallel to one another, with trie_node's shorter, if a
* node has children, then all its siblings must be trie_node's.  In
* particular, all root nodes must be trie_node's.
*
* A non-leaf node is represented by two elements accessed by the same
* index into two arrays.  One array of trie_node elements which hold
* just those extra members, and a longer array of string_node elements
* which hold the index to the label.
*
* Finally, flags are stored in an array of chars, one for each node.
*
* All the children of a given node are stored consecutively (one after
* another, without gaps) after the first child.
* 
* Initialization consists of about twice as much lines of code as the runtime
* functions, and it uses more than twelve times as much memory.  Memory used
* at runtime is allocated in one big chunk, while initialization uses small
* amounts allocated as needed and linked into lists.  The corresponding
* structures are defined right before the code which uses them, so that it is
* clear that functions defined earlier don't use them.  More detailed
* comments are there too.
*
* Initialization code comes after run-time code, before test code.
*/

// trie nodes, only for non-leaf nodes
struct trie_node // 4 bytes
{
	uint16_t first_child;
#define MAX_NUM_TRIE_NODES 0xffffU

	uint16_t num_children;
#define MAX_NUM_CHILDREN 0xffffU
};

// string table entry, for each name
typedef struct string_node
{
	uint16_t n;
} string_node;

/*
* Data structures used to perform the search. Should be
* populated once at startup by a call to publicsuffix_init.
*/
typedef struct publicsuffix_trie
{
	trie_node *node_table; // allocated
	string_node *str;
	unsigned char *flag_table;
	char* string_table;
	void* bound; // out of allocated area (for checking)

	size_t num_root_nodes, num_trie_nodes;
	size_t num_strings; // total number of (string) nodes
	time_t old_time;
	off_t old_size;
	char old_fname[];
} publicsuffix_trie;

typedef struct bsearch_key
{
	publicsuffix_trie const *pst;
	char const *component;
} bsearch_key;

static int bsearch_cmp(void const *k, void const *el)
{
	bsearch_key const *const key = k;
	char const *a = key->component;
	string_node const *const str = el;
	char const *b = key->pst->string_table + str->n;

	assert(el >= (void*)(key->pst->node_table) && el < key->pst->bound);
	assert((void*)b >= (void*)(key->pst->node_table) && (void*)b < key->pst->bound);

	int c, d;
	do c = *(unsigned char const*)a++, d = *(unsigned char const*)b++;
	while (c && c == d);

	return c - d;
}

static trie_node *
string2trie(publicsuffix_trie const *pst, string_node *node)
{
	assert(pst);
	assert(node);

	size_t const n = node - pst->str;
	if (n < pst->num_trie_nodes)
		return &pst->node_table[n];

	return NULL;
}

static inline unsigned char
node_flag(publicsuffix_trie const *pst, string_node *node)
{
	size_t const size = node - pst->str;
	if (size < pst->num_strings)
		return pst->flag_table[size];

	return 0;
}

typedef enum flag_mask
{
	flag_mask_is_tld = 1,
	flag_mask_has_star_child = 2,
	flag_mask_is_final = 4,
	flag_mask_is_exception = 8
} flag_mask;

static inline int
node_has_star_child(publicsuffix_trie const *pst, string_node *node)
{
	return node_flag(pst, node) & flag_mask_has_star_child;
}

static inline int
node_is_exception(publicsuffix_trie const *pst, string_node *node)
{
	return node_flag(pst, node) & flag_mask_is_exception;
}

static inline int
node_is_final(publicsuffix_trie const *pst, string_node *node)
{
	return node_flag(pst, node) & flag_mask_is_final;
}


static string_node *
find_node(publicsuffix_trie const *pst, char *component, string_node *parent)
/*
* Find the child of the parent node matching this component.
*/
{
	assert(pst);
	assert(component);
	assert(parent == NULL ||
		(parent >= pst->str && parent - pst->str < (int)pst->num_strings));

	bsearch_key key;
	key.pst = pst;
	key.component = component;

	string_node *base;
	size_t size;
	if (parent == NULL) // root
	{
		base = pst->str;
		size = pst->num_root_nodes;
	}
	else
	{
		trie_node const *const node = string2trie(pst, parent);
		if (node == NULL) // parent is a leaf node
			return NULL;

		base = &pst->str[node->first_child];
		size = node->num_children;
	}

	string_node *current =
		bsearch(&key, base, size, sizeof(string_node), bsearch_cmp);
	assert(size > 0 || current == NULL);

#if 0
	if (size > 0 && current == NULL)
	/*
	* We didn't find an exact match, so see if there's a wildcard
	* match.  From https://publicsuffix.org/list/: "The wildcard
	* character * (asterisk) matches any valid sequence of characters
	* in a hostname part. (Note: the list uses Unicode, not Punycode
	* forms, and is encoded using UTF-8.) Wildcards may only be used to
	* wildcard an entire level. That is, they must be surrounded by
	* dots (or implicit dots, at the beginning of a line)."
	*/
	{
		key.component = "*";
		current =
			bsearch(&key, base, size, sizeof(string_node), bsearch_cmp);
	}
#endif
	return current;
}

char *org_domain(publicsuffix_trie const *pst, char const *c_domain)
/*
* c_domain must be normalized utf-8
*/
{
	if (c_domain && *c_domain == '.')
		return NULL;

	char *org = NULL;
	char *domain = c_domain? strdup(c_domain): NULL;
	if (domain == NULL || pst == NULL)
		return NULL;


	size_t len = strlen(domain);
	char **labels;
	size_t nlabels = reverse_labels(domain, len, &labels);

	if (nlabels)
	{
		struct
		{
			string_node *parent;
			size_t i;
		} stars[nlabels];
		size_t next_star = 0, best_match = 0;
		string_node *current = NULL, *parent;

		for (size_t i = 0; i < nlabels; ++i)
		/*
		* Loop reversed labels until either not found or exception.
		*
		* Update: 15 May 2021.
		* It is possible to have multiple matches.  For example,
		* cloud.jelastic.open.tim.it also matches it.  Non-final matches
		* don't count.  Stars imply backtracking.
		*
		* Algorithm
		* https://publicsuffix.org/list/
		*
		* 1 Match domain against all rules and take note of the matching
		*   ones.
		* 2 If no rules match, the prevailing rule is "*".
		* 3 If more than one rule matches, the prevailing rule is the
		*   one which is an exception rule.
		* 4 If there is no matching exception rule, the prevailing rule
		*   is the one with the most labels.
		* 5 If the prevailing rule is a exception rule, modify it by
		*   removing the leftmost label.
		* 6 The public suffix is the set of labels from the domain which
		*   match the labels of the prevailing rule, using the matching
		*   algorithm above.
		* 7 The registered or registrable domain is the public suffix
		*   plus one additional label.
		*/
		{
			parent = current;
			if (i < nlabels)
				current = find_node(pst, labels[i], parent);
			else
				current = NULL;

			if (current == NULL)  // backtracking
			{
				if (next_star)
				{
					--next_star;
					current = find_node(pst, "*", stars[next_star].parent);
					i = stars[next_star].i;
				}
				else
					break;
			}

#if defined DEBUG_PUBLICSUFFIX
			printf("%2zu %s: %s -> %s%s%s%s\n",
				i, labels[i],
				parent? &pst->string_table[parent->n]: "TOP",
				node_is_exception(pst, current)? "!": "",
				node_has_star_child(pst, current)? "*": "",
				node_is_final(pst, current)? "/": "",
				&pst->string_table[current->n]);
#endif // DEBUG_PUBLICSUFFIX

			if (node_has_star_child(pst, current))
			{
				stars[next_star].parent = current;
				stars[next_star].i = i + 1;
				next_star += 1;
			}

			if (node_is_final(pst, current)) // match
			{
				if (node_is_exception(pst, current))
				{
					best_match = i; // by point 5
					break; // by point 3
				}

				// by point 4, length is i+1
				if (i >= best_match)
					best_match = i + 1;
			}
		}

		++best_match; // by point 7
		if (best_match > nlabels || best_match == 1)
		{
			free(domain);
			free(labels);
			return NULL;
		}


		len = 0;
		for (size_t i = 0; i < best_match; ++i)
			len += strlen(labels[i]) + 1;

		org = malloc(len);
		if (org)
		{
			*org = 0;
			for (size_t i = best_match;;)
			{
				strcat(org,  labels[--i]);
				if (i == 0)
					break;

				strcat(org, ".");
			}
		}
		free(labels);
	}
	free(domain);

	return org;
}

// ----- initialization code (still part of library) -----
/*
* Initialization uses structures named loose_*.  A loose_trie represents
* a node element.  They are created by read_rules() ordered by label,
* acording to the next pointer.
*
* The labels are initially allocated with (variable size) loose_trie.
* After populating the tree, there are three steps to transform it in
* the runtime structure.
*
* Each step is performed by traversing the tree according to the next
* pointer and calling the relevant callback, either before (head) or
* after (tail) recursion.
*
* Step 1 creates a linked list of loose_labels and replaces the label
* in loose_trie's union.  The total size of string_table is then known,
* and hence the total size of the memory used at runtime.
*
* The string_table is built in publicsuffix_init().  Step 2 and step 3
* copy the nodes.  Then the loose structures are freed.
*/

typedef struct loose_label
{
	struct loose_label *next;
	uint16_t n; // offset in the string table
	char label[];
} loose_label;

typedef struct loose_trie // variable size struct
{
	struct loose_trie *next, *child, *parent;
	size_t num_children;
	uint16_t n; // offset of corresponding trie_node/ string_node
	uint16_t not_used; // round to 32 byte offset, maybe sizeof(unsigned)
	unsigned int is_tld: 1;
	unsigned int has_star_child: 1;
	unsigned int is_exception: 1;
	unsigned int is_string: 1;
	unsigned int is_first_child: 1;
	unsigned int is_final: 1;
	unsigned int u_is_ll: 1;
	union // turned to ll in step 1 -- MUST be last element
	{
		loose_label *ll;
		char label[sizeof(loose_label*)];
	} u;
} loose_trie;

typedef struct loose_init
{
	FILE *fp; // debug output
	publicsuffix_trie *pst;
	loose_label *string_loose;
	loose_trie *boundary;
	void *reserve;
	size_t string_size, max_num_children;
	size_t num_strings; // number of string_loose
	uint16_t next_str, next_node;
} loose_init;

static loose_trie *add_trie_node(loose_trie **prev, char const *label)
/*
* Add trie nodes maintaining sort order.  The label is copied verbatim
* inside new structs at this stage.
* Return the node found, or NULL for memory failure.
*/
{
	assert(prev);
	assert(label);

	loose_trie *p;
	int cmp;

	while ((p = *prev) != NULL && (cmp = strcmp(p->u.label, label)) < 0)
		prev = &p->next;

	if (p && cmp == 0)
		return p; // found

	size_t len = strlen(label) + 1;
	len -= len >= sizeof p->u.label? sizeof p->u.label: len;
	loose_trie *pn = calloc(1, sizeof *p + len);
	if (pn)
	{
		pn->next = p;
		*prev = pn;
		strcpy(pn->u.label, label);
	}

	return pn;
}

typedef int (*w_traverse_cb)(loose_trie*, void *, int);
typedef enum {w_traverse_head, w_traverse_tail} w_traverse_mode;

static int
w_traverse(loose_trie *parent, w_traverse_mode mode,
	w_traverse_cb cb, void *cb_arg, int depth)
{
	assert(cb);

	int rtc = 0;

	loose_trie *t = parent;
	if (mode == w_traverse_head)
	{
		while (t)
		{
			if ((rtc = (*cb)(t, cb_arg, depth)) < 0)
				return rtc;
			t = t->next;
		}
		t = parent;
	}

	while (t)
	{
		if (t->child &&
			(rtc = w_traverse(t->child, mode, cb, cb_arg, depth + 1)) < 0)
				return rtc;

		loose_trie *next = t->next;
		if (mode != w_traverse_head &&
			(rtc = (*cb)(t, cb_arg, depth)) < 0)
				return rtc;

		t = next;
	}

	return rtc;
}

static int read_rules(FILE *fp, char const *fname, loose_trie **root)
/*
* Populate the root node with all rules.
* Return number of bad lines, or -1 if out of memory
*/
{
	char buf[512];
	char *s;
	int lineno = 0, bad = 0;

	while ((s = fgets(buf, sizeof buf, fp)) != NULL)
	{
		int ch;

		++lineno;
		if (strchr(s, '\n') == NULL) // line too long
		{
			(*do_report)(LOG_CRIT, "Line too long at %s:%d: \"%.10s...\"",
				fname, lineno, buf);

			// discard the overflow, it's ok if it is a comment
			while ((ch = fgetc(fp)) != '\n' && ch != EOF)
				continue;
		}

		if (s[0] == '/' && s[1] == '/') // comment
			continue;

		int is_exception = 0;
		if (*(unsigned char*)s == '!')
		{
			is_exception = 1;
			++s;
		}

		char *const buf_start = s;
		int is_ascii = 1;
		while ((ch = *(unsigned char *)s++) != 0)
		{
			if (ch & 0x80) // utf-8, check it is a valid sequence
			{
				int m = 0x40;
				is_ascii = (ch & m) != 0? 0: -1;
				while ((ch & m) != 0 && is_ascii == 0)
				{
					is_ascii = (*(unsigned char*)s++ & 0xc0) == 0x80? 0: -1;
					m >>= 1;
				}
				continue;
			}

			if (isspace(ch)) // end of rule
			{
				*--s = 0;
				break;
			}
		}

		if (ch == 0)
		{
			++bad;
			continue;
		}

		assert(*s == 0);

		size_t len = s - buf_start;
		if (len == 0) // empty line
			continue;

		if (is_ascii < 0)
		{
			(*do_report)(LOG_CRIT, "Bad UTF-8 sequence at %s:%d: \"%s\"",
				fname, lineno, buf);
			++bad;
			continue;
		}

		uint8_t norm[128];
		size_t ulen = sizeof norm - 1;
		uint8_t* norm_check = u8_tolower((uint8_t*)buf_start, len, NULL, UNINORM_NFC, norm, &ulen);
		if (norm_check != &norm[0])
		{
			(*do_report)(LOG_CRIT, "Failed u8_tolower at %s:%d: %s, len = %zu for \"%s\"",
				fname, lineno, strerror(errno), ulen, buf_start);
			free(norm_check);
			++bad;
			continue;
		}

		norm_check[ulen] = 0;
		if (strcmp((char*)norm_check, buf_start))
			(*do_report)(LOG_INFO, "Input: %s, normalized: %s\n", buf_start, norm_check);

		char **labels;
		size_t nlabels = reverse_labels(buf_start, len, &labels);
		if (labels == NULL)
		{
			(*do_report)(LOG_CRIT, "Invalid domain at %s:%d for \"%s\"",
				fname, lineno, buf_start);
			++bad;
			continue;
		}

		loose_trie *node = add_trie_node(root, labels[0]);
		if (node)
			node->is_tld = 1;
		for (size_t i = 1; i < nlabels && node; ++i)
		{
			if (strcmp(labels[i], "*") == 0)
				node->has_star_child = 1;
			node = add_trie_node(&node->child, labels[i]);
		}

		free(labels);
		if (node == NULL) // out of memory
			return -1;

		node->is_exception = is_exception;
		node->is_final = 1;
	}

	return bad;
}

static int wt_free(loose_trie* t, void *v, int depth)
{
	assert(t);

	free(t);
	return 0;

	(void)v; (void)depth;
}

static int wt_step1(loose_trie* t, void *v, int depth)
/*
* Count trie nodes and fill basic properties (flags, children).
* Count labels and create loose labels.  Turn u.label into u.ll.
* Return 0, or -1 for memory failure.
*/
{
	assert(t);
	assert(t->num_children == 0); // first time visited
	assert(v);
	assert(t->u_is_ll == 0);
	assert(depth > 0 || t->is_tld);

	loose_init *ini = v;
	publicsuffix_trie *pst = ini->pst;

	// there is string node (a.k.a. leaf node) for each element,
	// num_trie_nodes is also increased, but later decreased.
	pst->num_strings += 1;
	pst->num_trie_nodes += 1;
	pst->num_root_nodes += depth == 0;

	if (t->child)
	{
		t->child->is_first_child = 1;

		size_t num_children = 0, leaf_children = 0;
		for (loose_trie *p = t->child; p; p = p->next)
		{
			++num_children;
			p->parent = t;
			if (p->child == NULL)
				++leaf_children;
		}
		if (num_children > ini->max_num_children)
			ini->max_num_children = num_children;

		t->num_children = num_children;

		// when all children are leaves, they don't have to be full nodes:
		// decrease num_trie_nodes accordingly
		if (num_children == leaf_children)
		{
			pst->num_trie_nodes -= num_children;
			for (loose_trie *p = t->child; p; p = p->next)
				p->is_string = 1;
		}
	}

	// Find or insert a loose_label element and move the label string there.
	char const* const label = t->u.label;
	size_t len = strlen(label);

	loose_label **ll = &ini->string_loose, *l;
	int cmp;
	while ((l = *ll) != NULL && (cmp = strcmp(l->label, label)) < 0)
		ll = &l->next;

	if (l == NULL || cmp > 0)
	{
		loose_label *ln = malloc(len + 1 + sizeof(loose_label));
		if (ln == NULL)
			return -1;

		++ini->num_strings;
		ini->string_size += len + 1;
		strcpy(ln->label, label);
		ln->next = l;
		*ll = l = ln;
	}

	t->u_is_ll = 1;
	t->u.ll = l;
	return 0;
}

#if DEBUG_PUBLICSUFFIX
static int wt_print(loose_trie* t, void *v, int depth)
{
	assert(t);
	loose_init *ini = v;
	assert(ini && ini->fp);

	fprintf(ini->fp, "%2d  %-7s %s %s %s %s ",
		depth, t->is_string? "string": "full",
		t->is_tld? "TLD": "   ",
		t->has_star_child? "*": " ",
		t->is_exception? "!": " ",
		t->is_final? "/": " ");

	int len = 0;
	for (loose_trie *p = t; p; p = p->parent)
		len += fprintf(ini->fp, "%s%s", len? ".": "",
			p->u_is_ll? p->u.ll->label: p->u.label);

	if (t->child)
		fprintf(ini->fp, "%*zu -> %s%s",
			len < 40? 40 - len: 4, t->num_children,
			t->child->u_is_ll? t->child->u.ll->label: t->child->u.label,
			t->num_children > 1? ", ...": "");
	fputc('\n', ini->fp);

	return 0;
}
#endif //DEBUG_PUBLICSUFFIX

static int wt_step2(loose_trie* t, void *v, int depth)
// write full nodes but don't set first_child pointer
{
	assert(t);
	assert(v);
	assert(t->u_is_ll == 1);
	assert(depth == 0 || t->parent != NULL);  // non-root nodes have a parent
	assert(t->is_string == 0 || depth > 0);   // leaf nodes are non-root

	loose_init *ini = v;
	publicsuffix_trie *pst = ini->pst;

	if (t->is_string == 0) // full node
	{
		uint16_t n = ini->next_node++;

		// trie part
		trie_node *node = &pst->node_table[n];
		memset(node, 0, sizeof *node);
		node->num_children = t->num_children;

		// string part
		pst->str[n].n = t->u.ll->n;
		t->n = n;
#if DEBUG_PUBLICSUFFIX
		if (ini->fp)
			fprintf(ini->fp, "node[%5d ] = %5d   /* \"%s\" %s */\n",
				n, t->u.ll->n, &pst->string_table[t->u.ll->n],
				t->is_tld? "TLD": "   ");
#endif // DEBUG_PUBLICSUFFIX
	}

	return 0;
	(void)depth; // not used
}

static int wt_step3(loose_trie* t, void *v, int depth)
// write leaf nodes, set first_child pointer, and flags
{
	assert(t);
	assert(v);
	assert(t->u_is_ll == 1);
	assert(depth == 0 || t->parent != NULL);
	assert(t->is_first_child == 0 || depth > 0);

	loose_init *ini = v;
	publicsuffix_trie *pst = ini->pst;

	if (t->is_string == 1) // leaf node
	{
		uint16_t n = ini->next_node++;
		pst->str[n].n = t->u.ll->n;
		t->n = n;
#if DEBUG_PUBLICSUFFIX
		if (ini->fp)
			fprintf(ini->fp, "node[%5d ] = %5d   /* \"%s\" */\n",
				n, t->u.ll->n, &pst->string_table[t->u.ll->n]);
#endif // DEBUG_PUBLICSUFFIX
	}

	if (t->is_first_child)
	{
		trie_node *parent = &pst->node_table[t->parent->n];
		parent->first_child = t->n;
	}

	pst->flag_table[t->n] = 
		(t->is_tld? flag_mask_is_tld: 0) |
		(t->has_star_child? flag_mask_has_star_child: 0) |
		(t->is_final? flag_mask_is_final: 0) |
		(t->is_exception? flag_mask_is_exception: 0);

	return 0;
}

void publicsuffix_done(publicsuffix_trie *pst)
{
	if (pst)
	{
		free(pst->node_table);
		free(pst);
	}
}

publicsuffix_trie *publicsuffix_init(char const *fname, publicsuffix_trie *old)
/*
* If old is given, check if it needs an update and return immediately if not.
* If an update is needed, do the initialization and free the old structure
* before allocating the final chunk of memory --at that point initialization
* cannot fail but for malloc.
* If old is not given, use the file size as an estimate of the final chunk size
* and allocate it before starting initialization.  That way, the final heap
* should be shrinkable.
*/
{
	assert(fname);

#if 0
	if (_LIBUNISTRING_VERSION != _libunistring_version) // (major<<8) + minor
		(*do_report)(LOG_WARNING,
			"unistring version mismatch, expecting %d, have %d",
			_LIBUNISTRING_VERSION, _libunistring_version);
	if (!idn2_check_version(IDN2_VERSION))
	{
		(*do_report)(LOG_WARNING,
			"IDN2 version mismatch, expecting %s", IDN2_VERSION);
	}
#endif

	struct stat stat_dat;
	int rtc = stat(fname, &stat_dat);
	if (rtc)
		(*do_report)(LOG_CRIT, "cannot stat %s: %s", fname, strerror(errno));
	else if (old && old->old_time == stat_dat.st_mtime &&
		old->old_size == stat_dat.st_size && strcmp(fname, old->old_fname) == 0)
	{
		(*do_report)(LOG_INFO, "%s not changed", fname);
		rtc = 1;
	}

	if (rtc)
		return old;

	publicsuffix_trie *pst = NULL;
	FILE *fp = fopen(fname, "r");
	if (fp)
	{
		pst = calloc(1, sizeof *pst + strlen(fname) + 1);
		if (pst)
		{
			pst->old_time = stat_dat.st_mtime;
			pst->old_size = stat_dat.st_size;
			strcpy(pst->old_fname, fname);

			loose_init ini;
			memset(&ini, 0, sizeof ini);
			ini.pst = pst;
			if (old == NULL)
				ini.reserve = malloc(stat_dat.st_size);

			loose_trie *root = NULL;
			rtc = read_rules(fp, fname, &root) < 0;
			if (rtc == 0)
			{

				rtc = w_traverse(root, w_traverse_head, wt_step1, &ini, 0);
				if (rtc == 0 &&
					(pst->num_trie_nodes > MAX_NUM_TRIE_NODES ||
					ini.max_num_children > MAX_NUM_CHILDREN ||
					pst->num_strings > UINT16_MAX))
				{
					if (pst->num_trie_nodes > MAX_NUM_TRIE_NODES)
						(*do_report)(LOG_CRIT, "Too many trie nodes %zu, max %u",
							pst->num_trie_nodes, MAX_NUM_TRIE_NODES);
					if (ini.max_num_children > MAX_NUM_CHILDREN)
						(*do_report)(LOG_CRIT, "Too many child nodes %zu, max %u",
							ini.max_num_children, MAX_NUM_CHILDREN);
					if (pst->num_strings > UINT16_MAX)
						(*do_report)(LOG_CRIT, "Too many string nodes %zu, max %u",
							pst->num_strings, UINT16_MAX);
					rtc = -1;
				}
			}

			if (rtc == 0)
			{
				size_t const tot_alloc =
					pst->num_trie_nodes * sizeof(trie_node) +
					pst->num_strings * sizeof(string_node) +
					pst->num_strings * sizeof(unsigned char) +
					ini.string_size;

#if DEBUG_PUBLICSUFFIX
				ini.fp = fopen("debug_tables.dump", "w");
				if (ini.fp)
				{
					fprintf(ini.fp,
						"%#8zx root nodes\n"
						"%#8zx trie nodes (max=%#x)\n"
						"%#8zx total string nodes (max=%#x)\n"
						"%#8zx max children (max=%#x)\n\n",
						pst->num_root_nodes,
						pst->num_trie_nodes, MAX_NUM_TRIE_NODES,
						pst->num_strings, UINT16_MAX,
						ini.max_num_children, MAX_NUM_CHILDREN);
					fprintf(ini.fp, "%8zu num_strings in string table\n\n",
						ini.num_strings);

					fprintf(ini.fp,
						"%8zu  %zu trie_nodes of size %zu +\n"
						"%8zu  %zu num_strings of size %zu +\n"
						"%8zu  %zu flags of size 1 +\n"
						"%8zu  total string table size =\n"
						"%8zu\n\n",
						pst->num_trie_nodes * sizeof(trie_node),
						pst->num_trie_nodes,  sizeof(trie_node),
						pst->num_strings * sizeof(string_node),
						pst->num_strings,  sizeof(string_node),
						pst->num_strings, pst->num_strings,
						ini.string_size,
						tot_alloc);

					fputs("\n==Nodes:\n", ini.fp);
					w_traverse(root, w_traverse_head, wt_print, &ini, 0);
				}
#endif // DEBUG_PUBLICSUFFIX

				free(ini.reserve);
				ini.reserve = NULL;
				publicsuffix_done(old);
				old = NULL;

				pst->node_table = malloc(tot_alloc);
				if (pst->node_table)
				{
					pst->str = (string_node*)
						(pst->node_table + pst->num_trie_nodes);
					pst->flag_table = (unsigned char*) (pst->str + pst->num_strings);
					pst->string_table = (char*) (pst->flag_table + pst->num_strings);
					pst->bound = pst->string_table + ini.string_size;
					assert(pst->bound == (char*)(pst->node_table) + tot_alloc);

					// copy all labels in the string table;
#if DEBUG_PUBLICSUFFIX
					if (ini.fp)
						fputs("\n==Strings:\n", ini.fp);
#endif // DEBUG_PUBLICSUFFIX
					uint16_t n = 0;
					char *const st = pst->string_table;
					for (loose_label *ll = ini.string_loose; ll; ll= ll->next)
					{
						size_t const len = strlen(ll->label) + 1;
						memcpy(&st[n], ll->label, len);
#if DEBUG_PUBLICSUFFIX
						if (ini.fp)
							fprintf(ini.fp, " \"%s\" %*s/*%3zu %#6x */\n",
								ll->label, (int)(len < 40? 40 - len: 0), "", len, n);
#endif // DEBUG_PUBLICSUFFIX
						ll->n = n;
						n += len;
					}

					// step2 and step 3 cannot fail
#if DEBUG_PUBLICSUFFIX
					if (ini.fp)
						fputs("\n==Step 2:\n", ini.fp);
#endif // DEBUG_PUBLICSUFFIX
					w_traverse(root, w_traverse_head, wt_step2, &ini, 0);
#if DEBUG_PUBLICSUFFIX
					if (ini.fp)
						fputs("\n==Step 3:\n", ini.fp);
#endif // DEBUG_PUBLICSUFFIX
					w_traverse(root, w_traverse_head, wt_step3, &ini, 0);

#if DEBUG_PUBLICSUFFIX
					if (ini.fp)
					{
						fclose(ini.fp);
						ini.fp = NULL;
					}
#endif // DEBUG_PUBLICSUFFIX
				}
				else rtc = -1;
			}

			for (loose_label *ll = ini.string_loose; ll;)
			{
				loose_label *tmp = ll->next;
				free(ll);
				ll = tmp;
			}
			w_traverse(root, w_traverse_tail, wt_free, NULL, 0);
			free(ini.reserve);
			if (rtc)
			{
				free(pst->node_table);
				free(pst);
				pst = old;
				(*do_report)(LOG_CRIT, "Cannot init publicsuffix%s",
					pst? " (old data retained)": "");
			}
		}
		fclose(fp);
	}
	else // fopen failure
	{
		pst = old;
		(*do_report)(LOG_CRIT, "cannot read %s: %s%s",
			fname, strerror(errno), pst? " (old data retained)": "");
	}

	return pst;
}

// ----- test code, i.e. client using the library -----

/*
* This code tests the library using test_psl.txt
*/
static inline const char *chk(char const *p) {return p? p: "NULL";}

static char*
norm_org_domain(publicsuffix_trie const *pst, char const *c_domain)
{
	if (c_domain == NULL)
		return org_domain(pst, NULL);


	char norm[256*4];
	size_t ulen = sizeof norm - 1;

	char* n = (char*)u8_tolower((const uint8_t*)c_domain, strlen(c_domain),
		NULL, UNINORM_NFC, (uint8_t*)norm, &ulen);
	if (n != &norm[0] || ulen >= sizeof norm)
		return NULL;

	norm[ulen] = 0;

	char *out = NULL;
	if (idn2_to_unicode_8z8z(norm, &out, 0) != IDN2_OK)
		return NULL;

	int eq = strcmp(out, norm) == 0;
	printf("\nLooking up %s%s%s%s\n", c_domain,
		eq? "": "  (",
		eq? "": out,
		eq? "": ")");
	char *rtc = org_domain(pst, out);
	free(out);

	if (eq)
		return rtc;

	if (idn2_to_ascii_8z(rtc, &out, 0) != IDN2_OK)
		out = NULL;

	free(rtc);
	return out;
}

static int check(publicsuffix_trie *pst, char const *in, char const *out)
{
	char *od = norm_org_domain(pst, in);
	int rtc = od == NULL || out == NULL? od != out: strcmp(od, out);
	if (rtc)
		printf("%s: expect %s, have %s\n", chk(in), chk(out), chk(od));
	free(od);
	return rtc;
}

void public_test(publicsuffix_trie *pst)
{
	size_t check_calls = 0, errs = 0;
#define checkPublicSuffix(a, b) if (check(pst, a, b)) ++errs; ++check_calls;
//#include "test_pls.h"
#include "test_psl.txt"
	printf("%zu/%zu errors\n", errs, check_calls);
}



int main(int argc, char *argv[])
{
	int rtc = 1;

	if (_LIBUNISTRING_VERSION != _libunistring_version) // (major<<8) + minor
		fprintf(stderr, "unistring version mismatch, expecting %d, have %d\n",
			_LIBUNISTRING_VERSION, _libunistring_version);
	if (!idn2_check_version(IDN2_VERSION))
	{
		fprintf(stderr, "IDN2 version mismatch, expecting %s\n", IDN2_VERSION);
	}
	else if (argc > 1)
	{
		publicsuffix_trie *pst = publicsuffix_init(argv[1], NULL);
		if (pst)
		{
			for (int i = 2; i < argc; ++i)
			{
				if (strcmp(argv[i], "-t") == 0)
				{
					public_test(pst);
					continue;
				}
				char *od = norm_org_domain(pst, argv[i]);
				printf("%s -> %s\n", argv[i], od? od: "null");
				free(od);
			}
			publicsuffix_done(pst);
		}
	}
	else fprintf(stderr, "usage: %s rule-file domain...\n", argv[0]);

	return rtc;
}
