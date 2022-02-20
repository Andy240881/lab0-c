// SPDX-License-Identifier: GPL-2.0
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "harness.h"
#include "list.h"
#include "queue.h"

typedef unsigned char u8;
#define likely(x) __builtin_expect(!!(x), 1)
#define unlikely(x) __builtin_expect(!!(x), 0)
typedef int
    __attribute__((nonnull(2, 3))) (*list_cmp_func_t)(void *,
                                                      const struct list_head *,
                                                      const struct list_head *);
int sort_comp(void *p, const struct list_head *a, const struct list_head *b)
{
    // cppcheck-suppress nullPointer
    return strcmp(list_entry(a, element_t, list)->value,
                  // cppcheck-suppress nullPointer
                  list_entry(b, element_t, list)->value);
}
/*
 * Returns a list organized in an intermediate format suited
 * to chaining of merge() calls: null-terminated, no reserved or
 * sentinel head node, "prev" links not maintained.
 */
__attribute__((nonnull(2, 3, 4))) static struct list_head *
merge(void *priv, list_cmp_func_t cmp, struct list_head *a, struct list_head *b)
{
    struct list_head *head = NULL, **tail = &head;

    for (;;) {
        /* if equal, take 'a' -- important for sort stability */
        if (cmp(priv, a, b) <= 0) {
            *tail = a;
            tail = &a->next;
            a = a->next;
            if (!a) {
                *tail = b;
                break;
            }
        } else {
            *tail = b;
            tail = &b->next;
            b = b->next;
            if (!b) {
                *tail = a;
                break;
            }
        }
    }
    return head;
}

/*
 * Combine final list merge with restoration of standard doubly-linked
 * list structure.  This approach duplicates code from merge(), but
 * runs faster than the tidier alternatives of either a separate final
 * prev-link restoration pass, or maintaining the prev links
 * throughout.
 */
__attribute__((nonnull(2, 3, 4, 5))) static void merge_final(
    void *priv,
    list_cmp_func_t cmp,
    struct list_head *head,
    struct list_head *a,
    struct list_head *b)
{
    struct list_head *tail = head;
    u8 count = 0;

    for (;;) {
        /* if equal, take 'a' -- important for sort stability */
        if (cmp(priv, a, b) <= 0) {
            tail->next = a;
            a->prev = tail;
            tail = a;
            a = a->next;
            if (!a)
                break;
        } else {
            tail->next = b;
            b->prev = tail;
            tail = b;
            b = b->next;
            if (!b) {
                b = a;
                break;
            }
        }
    }

    /* Finish linking remainder of list b on to tail */
    tail->next = b;
    do {
        /*
         * If the merge is highly unbalanced (e.g. the input is
         * already sorted), this loop may run many iterations.
         * Continue callbacks to the client even though no
         * element comparison is needed, so the client's cmp()
         * routine can invoke cond_resched() periodically.
         */
        if (unlikely(!++count))
            cmp(priv, b, b);
        b->prev = tail;
        tail = b;
        b = b->next;
    } while (b);

    /* And the final links to make a circular doubly-linked list */
    tail->next = head;
    head->prev = tail;
}

/**
 * list_sort - sort a list
 * @priv: private data, opaque to list_sort(), passed to @cmp
 * @head: the list to sort
 * @cmp: the elements comparison function
 *
 * The comparison function @cmp must return > 0 if @a should sort after
 * @b ("@a > @b" if you want an ascending sort), and <= 0 if @a should
 * sort before @b *or* their original order should be preserved.  It is
 * always called with the element that came first in the input in @a,
 * and list_sort is a stable sort, so it is not necessary to distinguish
 * the @a < @b and @a == @b cases.
 *
 * This is compatible with two styles of @cmp function:
 * - The traditional style which returns <0 / =0 / >0, or
 * - Returning a boolean 0/1.
 * The latter offers a chance to save a few cycles in the comparison
 * (which is used by e.g. plug_ctx_cmp() in block/blk-mq.c).
 *
 * A good way to write a multi-word comparison is::
 *
 *	if (a->high != b->high)
 *		return a->high > b->high;
 *	if (a->middle != b->middle)
 *		return a->middle > b->middle;
 *	return a->low > b->low;
 *
 *
 * This mergesort is as eager as possible while always performing at least
 * 2:1 balanced merges.  Given two pending sublists of size 2^k, they are
 * merged to a size-2^(k+1) list as soon as we have 2^k following elements.
 *
 * Thus, it will avoid cache thrashing as long as 3*2^k elements can
 * fit into the cache.  Not quite as good as a fully-eager bottom-up
 * mergesort, but it does use 0.2*n fewer comparisons, so is faster in
 * the common case that everything fits into L1.
 *
 *
 * The merging is controlled by "count", the number of elements in the
 * pending lists.  This is beautifully simple code, but rather subtle.
 *
 * Each time we increment "count", we set one bit (bit k) and clear
 * bits k-1 .. 0.  Each time this happens (except the very first time
 * for each bit, when count increments to 2^k), we merge two lists of
 * size 2^k into one list of size 2^(k+1).
 *
 * This merge happens exactly when the count reaches an odd multiple of
 * 2^k, which is when we have 2^k elements pending in smaller lists,
 * so it's safe to merge away two lists of size 2^k.
 *
 * After this happens twice, we have created two lists of size 2^(k+1),
 * which will be merged into a list of size 2^(k+2) before we create
 * a third list of size 2^(k+1), so there are never more than two pending.
 *
 * The number of pending lists of size 2^k is determined by the
 * state of bit k of "count" plus two extra pieces of information:
 *
 * - The state of bit k-1 (when k == 0, consider bit -1 always set), and
 * - Whether the higher-order bits are zero or non-zero (i.e.
 *   is count >= 2^(k+1)).
 *
 * There are six states we distinguish.  "x" represents some arbitrary
 * bits, and "y" represents some arbitrary non-zero bits:
 * 0:  00x: 0 pending of size 2^k;           x pending of sizes < 2^k
 * 1:  01x: 0 pending of size 2^k; 2^(k-1) + x pending of sizes < 2^k
 * 2: x10x: 0 pending of size 2^k; 2^k     + x pending of sizes < 2^k
 * 3: x11x: 1 pending of size 2^k; 2^(k-1) + x pending of sizes < 2^k
 * 4: y00x: 1 pending of size 2^k; 2^k     + x pending of sizes < 2^k
 * 5: y01x: 2 pending of size 2^k; 2^(k-1) + x pending of sizes < 2^k
 * (merge and loop back to state 2)
 *
 * We gain lists of size 2^k in the 2->3 and 4->5 transitions (because
 * bit k-1 is set while the more significant bits are non-zero) and
 * merge them away in the 5->2 transition.  Note in particular that just
 * before the 5->2 transition, all lower-order bits are 11 (state 3),
 * so there is one list of each smaller size.
 *
 * When we reach the end of the input, we merge all the pending
 * lists, from smallest to largest.  If you work through cases 2 to
 * 5 above, you can see that the number of elements we merge with a list
 * of size 2^k varies from 2^(k-1) (cases 3 and 5 when x == 0) to
 * 2^(k+1) - 1 (second merge of case 5 when x == 2^(k-1) - 1).
 */
__attribute__((nonnull(2, 3))) void list_sort(void *priv,
                                              struct list_head *head,
                                              list_cmp_func_t cmp)
{
    struct list_head *list = head->next, *pending = NULL;
    size_t count = 0; /* Count of pending */

    if (list == head->prev) /* Zero or one elements */
        return;

    /* Convert to a null-terminated singly-linked list. */
    head->prev->next = NULL;

    /*
     * Data structure invariants:
     * - All lists are singly linked and null-terminated; prev
     *   pointers are not maintained.
     * - pending is a prev-linked "list of lists" of sorted
     *   sublists awaiting further merging.
     * - Each of the sorted sublists is power-of-two in size.
     * - Sublists are sorted by size and age, smallest & newest at front.
     * - There are zero to two sublists of each size.
     * - A pair of pending sublists are merged as soon as the number
     *   of following pending elements equals their size (i.e.
     *   each time count reaches an odd multiple of that size).
     *   That ensures each later final merge will be at worst 2:1.
     * - Each round consists of:
     *   - Merging the two sublists selected by the highest bit
     *     which flips when count is incremented, and
     *   - Adding an element from the input as a size-1 sublist.
     */
    do {
        size_t bits;
        struct list_head **tail = &pending;

        /* Find the least-significant clear bit in count */
        for (bits = count; bits & 1; bits >>= 1)
            tail = &(*tail)->prev;
        /* Do the indicated merge */
        if (likely(bits)) {
            struct list_head *a = *tail, *b = a->prev;

            a = merge(priv, cmp, b, a);
            /* Install the merged result in place of the inputs */
            a->prev = b->prev;
            *tail = a;
        }

        /* Move one element from input list to pending */
        list->prev = pending;
        pending = list;
        list = list->next;
        pending->next = NULL;
        count++;
    } while (list);

    /* End of input; merge together all the pending lists. */
    list = pending;
    pending = pending->prev;
    for (;;) {
        struct list_head *next = pending->prev;

        if (!next)
            break;
        list = merge(priv, cmp, pending, list);
        pending = next;
    }
    /* The final merge, rebuilding prev links */
    merge_final(priv, cmp, head, pending, list);
}

/* Notice: sometimes, Cppcheck would find the potential NULL pointer bugs,
 * but some of them cannot occur. You can suppress them by adding the
 * following line.
 *   cppcheck-suppress nullPointer
 */

/*
 * Create empty queue.
 * Return NULL if could not allocate space.
 */
struct list_head *q_new()
{
    struct list_head *head = malloc(sizeof(struct list_head));
    if (!head) {
        return NULL;
    }
    INIT_LIST_HEAD(head);
    return head;
}

/* Free all storage used by queue */
void q_free(struct list_head *l)
{
    if (l == NULL) {
        return;
    }
    element_t *iter, *tmp;

    list_for_each_entry_safe (iter, tmp, l, list)
        q_release_element(iter);
    free(l);
}

/*
 * Attempt to insert element at head of queue.
 * Return true if successful.
 * Return false if q is NULL or could not allocate space.
 * Argument s points to the string to be stored.
 * The function must explicitly allocate space and copy the string into it.
 */
bool q_insert_head(struct list_head *head, char *s)
{
    if (head == NULL) {
        return false;
    }
    element_t *item = malloc(sizeof(element_t));
    if (item == NULL) {
        return false;
    }
    item->value = strdup(s);
    if (item->value == NULL) {
        q_release_element(item);
        return false;
    }
    // cppcheck-suppress nullPointer
    element_t *q = list_entry(head, element_t, list);
    if (q == NULL) {
        q_release_element(item);
        return false;
    }
    list_add(&item->list, head);
    return true;
}

/*
 * Attempt to insert element at tail of queue.
 * Return true if successful.
 * Return false if q is NULL or could not allocate space.
 * Argument s points to the string to be stored.
 * The function must explicitly allocate space and copy the string into it.
 */
bool q_insert_tail(struct list_head *head, char *s)
{
    if (head == NULL) {
        return false;
    }
    element_t *item = malloc(sizeof(element_t));
    if (item == NULL) {
        return false;
    }
    item->value = strdup(s);
    if (item->value == NULL) {
        q_release_element(item);
        return false;
    }
    list_add_tail(&item->list, head);
    return true;
}

/*
 * Attempt to remove element from head of queue.
 * Return target element.
 * Return NULL if queue is NULL or empty.
 * If sp is non-NULL and an element is removed, copy the removed string to *sp
 * (up to a maximum of bufsize-1 characters, plus a null terminator.)
 *
 * NOTE: "remove" is different from "delete"
 * The space used by the list element and the string should not be freed.
 * The only thing "remove" need to do is unlink it.
 *
 * REF:
 * https://english.stackexchange.com/questions/52508/difference-between-delete-and-remove
 */
element_t *q_remove_head(struct list_head *head, char *sp, size_t bufsize)
{
    if (!head || list_empty(head))
        return NULL;
    // cppcheck-suppress nullPointer
    element_t *q = container_of(head->next, element_t, list);
    if (!q) {
        return NULL;
    }
    list_del_init(head->next);
    if (sp != NULL) {
        strncpy(sp, q->value, bufsize - 1);
        sp[bufsize - 1] = '\0';
    }
    return q;
}

/*
 * Attempt to remove element from tail of queue.
 * Other attribute is as same as q_remove_head.
 */
element_t *q_remove_tail(struct list_head *head, char *sp, size_t bufsize)
{
    if (!head || list_empty(head))
        return NULL;
    // cppcheck-suppress nullPointer
    element_t *q = container_of(head->prev, element_t, list);
    if (!q) {
        return NULL;
    }
    list_del_init(head->prev);
    if (sp != NULL) {
        strncpy(sp, q->value, bufsize - 1);
        sp[bufsize - 1] = '\0';
    }
    return q;
}

/*
 * WARN: This is for external usage, don't modify it
 * Attempt to release element.
 */
void q_release_element(element_t *e)
{
    free(e->value);
    free(e);
}

/*
 * Return number of elements in queue.
 * Return 0 if q is NULL or empty
 */
int q_size(struct list_head *head)
{
    if (!head)
        return 0;

    int len = 0;
    struct list_head *li;

    list_for_each (li, head)
        len++;
    return len;
}

/*
 * Delete the middle node in list.
 * The middle node of a linked list of size n is the
 * ⌊n / 2⌋th node from the start using 0-based indexing.
 * If there're six element, the third member should be return.
 * Return NULL if list is NULL or empty.
 */
bool q_delete_mid(struct list_head *head)
{
    // https://leetcode.com/problems/delete-the-middle-node-of-a-linked-list/
    int len = q_size(head);
    if (len == 0)
        return NULL;
    int i = 0;
    element_t *iter, *tmp;
    list_for_each_entry_safe (iter, tmp, head, list)
        if (i != len / 2) {
            i++;
        } else {
            list_del_init(&iter->list);
            q_release_element(iter);
            break;
        }
    return true;
}

/*
 * Delete all nodes that have duplicate string,
 * leaving only distinct strings from the original list.
 * Return true if successful.
 * Return false if list is NULL.
 *
 * Note: this function always be called after sorting, in other words,
 * list is guaranteed to be sorted in ascending order.
 */
bool q_delete_dup(struct list_head *head)
{
    // https://leetcode.com/problems/remove-duplicates-from-sorted-list-ii/
    if (!head || list_empty(head))
        return false;
    if (list_is_singular(head))
        return true;
    element_t *iter, *tmp;
    int flag = 0;
    list_for_each_entry_safe (iter, tmp, head, list)
        if ((iter->list.next != head) &&
            !strcmp(iter->value,
                    // cppcheck-suppress nullPointer
                    list_entry(iter->list.next, element_t, list)->value)) {
            list_del(&iter->list);
            q_release_element(iter);
            flag = 1;
        } else if (flag) {
            list_del(&iter->list);
            q_release_element(iter);
            flag = 0;
        }
    return true;
}

/*
 * Attempt to swap every two adjacent nodes.
 */
void q_swap(struct list_head *head)
{
    // https://leetcode.com/problems/swap-nodes-in-pairs/
    if (!head || list_empty(head) || list_is_singular(head))
        return;
    struct list_head *current = head->next;
    struct list_head *next = NULL;
    while (current != head && current->next != head) {
        next = current->next;
        list_move_tail(next, current);
        current = current->next;
    }
}

/*
 * Reverse elements in queue
 * No effect if q is NULL or empty
 * This function should not allocate or free any list elements
 * (e.g., by calling q_insert_head, q_insert_tail, or q_remove_head).
 * It should rearrange the existing ones.
 */
void q_reverse(struct list_head *head)
{
    if (head == NULL)
        return;
    if (list_empty(head))
        return;
    struct list_head *current = head->prev;
    struct list_head *next = NULL;
    next = current->prev;
    list_move_tail(current, head);
    current = next;
    while (current != head) {
        next = current->prev;
        list_move_tail(current, head);
        current = next;
    }
}

/*
 * Sort elements of queue in ascending order
 * No effect if q is NULL or empty. In addition, if q has only one
 * element, do nothing.
 */
void q_sort(struct list_head *head)
{
    if (!head || list_empty(head) || list_is_singular(head))
        return;
    list_sort(NULL, head, sort_comp);
}