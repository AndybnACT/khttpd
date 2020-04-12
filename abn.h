#ifndef __ABN_H
#define __ABN_H

#define KERNEL_MODE

#ifndef KERNEL_MODE
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "debug.h"
#endif /* !KERNEL_MODE */

#ifdef KERNEL_MODE
#include <linux/slab.h>
#include <linux/types.h>

#define malloc(size) kmalloc((size), GFP_KERNEL)
#define free(ptr) kfree(ptr)
#define CONFIG_DEBUG_LEVEL 2
#define dprintf(lvl, fmt, args...)                             \
    do {                                                       \
        if (CONFIG_DEBUG_LEVEL && (lvl) <= CONFIG_DEBUG_LEVEL) \
            printk((fmt), ##args);                             \
    } while (0)
#define printf(fmt, args...) \
    {                        \
        printk(fmt, ##args); \
    }
#endif /* KERNEL_MODE */

#define STACKALLOC 5
typedef struct bn {
    int cnt;
    int cap;
    uint64_t *heap;
    uint64_t stack[STACKALLOC];
} bn;

uint64_t *bn_getnum(bn *b)
{
    return b->heap ? b->heap : b->stack;
}

static inline void bn_init(bn *b)
{
    b->cnt = 0;
    b->cap = STACKALLOC;
    b->heap = NULL;
    memset(b->stack, 0, STACKALLOC * sizeof(uint64_t));
}

static inline void bn_set(bn *b, uint64_t num)
{
    // assert b->cnt == 0;
    uint64_t *n = bn_getnum(b);
    n[0] = num;
    b->cnt = 1;
    return;
}

static inline void bn_free(bn *bn)
{
    if (bn->heap)
        free(bn->heap);
}

bn *bn_realloc(bn *orig, int newcap)
{
    dprintf(3, "%p bn_realloc %d => %d\n", orig, orig->cap, newcap);
    if (newcap > STACKALLOC) {
        uint64_t *src = bn_getnum(orig);
        uint64_t *heap = (uint64_t *) malloc(newcap * sizeof(uint64_t));
        if (!heap)
            return NULL;

        memset(heap, 0, newcap * sizeof(uint64_t));
        memcpy(heap, src, orig->cap * sizeof(uint64_t));
        bn_free(orig);

        orig->cap = newcap;
        orig->heap = heap;
    }
    return orig;
}
bn *bn_alloc(bn *orig, int cap)
{
    if (cap > STACKALLOC) {
        bn_free(orig);
        uint64_t *heap = (uint64_t *) malloc(cap * sizeof(uint64_t));
        if (!heap)
            return NULL;
        orig->cap = cap;
        orig->cnt = 0;
        orig->heap = heap;
    }
    return orig;
}

static inline int bn_assign(bn *dst, bn *src)
{
#define GAP 2
    if (dst->cap < src->cnt) {
        dst = bn_alloc(dst, src->cnt + GAP);
        if (!dst) {
            dprintf(2, "error reallocing\n");
            return -1;
        }
        // FIXME: ugly code, but important
        // if there are dirty bits up there, shld may regards them as shifted
        // bits, corrupting the entire number;
        memset((dst->heap) + src->cnt, 0, GAP * sizeof(uint64_t));
    }
#undef GAP
    uint64_t *d = bn_getnum(dst);
    uint64_t *s = bn_getnum(src);
    memcpy(d, s, src->cnt * sizeof(uint64_t));
    dst->cnt = src->cnt;
    return 0;
}

static inline uint8_t __add_ll(uint64_t *dst,
                               uint64_t src1,
                               uint64_t src2,
                               uint8_t c)
{
    uint8_t rc;
    uint64_t res;
    // Since carry is either 0 or 1, we only need at most 65 (but not 66) bits
    // to hold the result from src1 + src2 + carry. Even if both of them have
    // all bits set.
    // FIXME: should assert rc != 0 || rc != 1
    __asm__(
        "xor %%rsi, %%rsi\n\t"
        "movb %4, %%sil\n\t"
        "movq %2, %1\n\t"
        "addq %3, %1\n\t"
        "setc %0\n\t"
        "addq %%rsi, %1\n\t"
        "setc %%cl\n\t"
        "orb %%cl, %0\n\t"
        : "=&r"(rc), "=&r"(res)
        : "r"(src1), "r"(src2), "r"(c)
        : "rsi", "cl");
    *dst = res;
    return rc;
}

static inline void bn_add(bn *dst, bn *src1, bn *src2)
{
    int maxcap;
    int mincap;
    int left;
    uint64_t *d;
    uint64_t *s1;
    uint64_t *s2;
    int i;
    uint8_t c = 0;

    if (src1->cnt > src2->cnt) {
        maxcap = src1->cnt + 1;
        mincap = src2->cnt;
        s1 = bn_getnum(src1);
        s2 = bn_getnum(src2);
    } else {
        maxcap = src2->cnt + 1;
        mincap = src1->cnt;
        s1 = bn_getnum(src2);
        s2 = bn_getnum(src1);
    }

    if (dst->cap < maxcap) {
        dst = bn_realloc(dst, maxcap * 2);
        if (!dst) {
            dprintf(1, "error reallocing in bn_add\n");
            return;
        }
    }
    d = bn_getnum(dst);

    for (i = 0; i < mincap; i++) {
        // d[i] = s1[i] + s2[i] + c;// This CODE is not SAFE
        // if (s1[i] > ~s2[i]) {    // Consider s2 = u64_max, s1 = 0, c = 1
        //     c = 1;
        // } else {
        //     c = 0;
        // }
        c = __add_ll(d + i, s1[i], s2[i], c);
        dprintf(10, "d[%d] = 0x%llx, carry = %d\n", i, d[i], c);
    }

    left = maxcap - mincap - 1;
    while (left > 0) {  // unlikely
        d[i] = s1[i] + c;
        if (s1[i] > ~c) {  // unlikely
            c = 1;
        } else {
            c = 0;
        }
        i++;
        left--;
    }

    dst->cnt = i;
    if (c) {
        d[i] += c;
        dst->cnt++;
    }
    return;
}

static inline void __bn_shld(bn *dst, uint8_t amount)
{
    uint64_t *num;

    if (dst->cnt + 1 > dst->cap) {
        dst = bn_realloc(dst, dst->cap * 2);
        if (!dst) {
            dprintf(2, "error reallocing in shl\n");
            return;
        }
    }

    num = bn_getnum(dst);
    uint64_t tmp = 0;
    for (int i = 0; i <= dst->cnt; i++) {
        uint64_t tmp2;
        uint64_t res = 0;
        // dprintf(10, "%llx %llx\n", tmp, num[i]);
        __asm__(
            "movq (%3), %0\n\t"
            "movq  %0, %1\n\t"
            "shldq %%cl, %2, %1"
            : "=&r"(tmp2), "=&r"(res)
            : "r"(tmp), "r"(num + i), "c"(amount)
            :);
        tmp = tmp2;
        num[i] = res;
        // dprintf(10, "%llx %llx\n", tmp, num[i]);
    }
    if (num[dst->cnt])
        dst->cnt++;
}

static inline void __bn_shrd(bn *dst, uint8_t amount)
{
    uint64_t *num;
    if (amount >= 64) {  // unlikely
        return;
    }

    num = bn_getnum(dst);
    uint64_t tmp = 0;
    for (int i = dst->cnt - 1; i >= 0; i--) {
        uint64_t tmp2;
        uint64_t res = 0;
        __asm__(
            "movq (%3), %0\n\t"
            "movq  %0, %1\n\t"
            "shrdq %%cl, %2, %1"
            : "=&r"(tmp2), "=&r"(res)
            : "r"(tmp), "r"(num + i), "c"(amount)
            :);
        tmp = tmp2;
        num[i] = res;
    }
    if (!num[dst->cnt - 1])
        dst->cnt--;
}

static inline void bn_shl(bn *dst, uint32_t left)
{
    int move_B = left / 8;
    int move_l = move_B / sizeof(uint64_t);

    if (dst->cnt + move_l + 1 > dst->cap) {
        dst = bn_realloc(dst, dst->cnt + (move_l * 2) + 1);
        if (!dst) {
            dprintf(2, "error reallocing in shl\n");
            return;
        }
    }
    char *stream = (char *) bn_getnum(dst);
    memmove(stream + move_B, stream, dst->cnt * sizeof(uint64_t));
    memset(stream, 0, move_B);
    dst->cnt += move_l;
    if (((uint64_t *) (stream))[dst->cnt]) {
        dst->cnt++;
    }
    if (left % 8) {
        dprintf(3, "%u bits remaining\n", left % 8);
        __bn_shld(dst, left % 8);
    }
}

// static inline void bn_shr(bn *dst, uint32_t right)
// {
//     dprintf(0, "ERROR, NOT IMPLEMENTMENT\n");
//     return;
// }

static inline uint8_t __sub_ll(uint64_t *dst,
                               uint64_t src1,
                               uint64_t src2,
                               uint8_t c)
{
    uint8_t rc;
    uint64_t res;
    // do src1 - carry - src2
    __asm__(
        "subq %4, %2\n\t"
        "setc %0\n\t"
        "subq %3, %2\n\t"
        "setc %%sil\n\t"
        "orb %%sil, %0\n\t"
        "movq %2, %1\n\t"
        : "=&r"(rc), "=r"(res)
        : "r"(src1), "r"(src2), "r"((uint64_t) c)
        : "rsi");
    *dst = res;
    return rc;
}

static inline void bn_sub(bn *dst, bn *src1, bn *src2)
{
    int borrow = 0;
    uint64_t *d, *s1, *s2;
    if (dst->cap < src1->cnt) {
        dst = bn_realloc(dst, src1->cnt);
        if (!dst) {
            dprintf(1, "realloc fails on bn_sub\n");
            return;
        }
    }

    d = bn_getnum(dst);
    s1 = bn_getnum(src1);
    s2 = bn_getnum(src2);
    for (size_t i = 0; i < src1->cnt; i++) {
        borrow = __sub_ll(d + i, s1[i], s2[i], borrow);
        if (d[i])
            dst->cnt = i + 1;
    }
    return;
}

struct prod {
    uint64_t lo;
    uint64_t hi;
};

static inline struct prod __mul_ll(uint64_t src1, uint64_t src2)
{
    struct prod ret;
    ret.lo = src1;
    // what a neat inline asm is it?
    // https://github.com/chenshuo/recipes/blob/master/basic/int128.h#L26
    __asm__("mulq %2\n\t" : "=d"(ret.hi), "+a"(ret.lo) : "r"(src2) :);
    return ret;
}

/*                          var   | loop index |   boundary   |   width
 *                        ===============================================
 *     A3, A2, A1, A0 --> mpcand  |      j     |   *wcand_p   |  larger
 *   x B3, B2, B1, B0 --> mplier  |      i     |   *wlier_p   |  smaller
 *  ---------------------------------------------------------------------
 */
static inline void bn_mul_comba(bn *dst, bn *src1, bn *src2)
{
    uint64_t *d, *mpcand, *mplier;
    struct prod prod;
    int *wcand_p, *wlier_p;
    int i, j;
    int index = 0;
    int width = src1->cnt + src2->cnt;
    uint8_t carry;
    if (dst->cap < width) {
        dst = bn_realloc(dst, width + 2);
        if (!dst) {
            dprintf(1, "realloc fails on bn_mul_comba\n");
            return;
        }
    }
    d = bn_getnum(dst);
    memset(d, 0, width * sizeof(uint64_t));
    dst->cnt = 0;
    if (src1->cnt > src2->cnt) {
        mpcand = bn_getnum(src1);
        mplier = bn_getnum(src2);
        wcand_p = &src1->cnt;
        wlier_p = &src2->cnt;
    } else {
        mpcand = bn_getnum(src2);
        mplier = bn_getnum(src1);
        wcand_p = &src2->cnt;
        wlier_p = &src1->cnt;
    }

    while (index < width - 1) {
        if (index < *wlier_p) {
            i = index;
            j = 0;
        } else {
            i = *wlier_p - 1;
            j = index - i;
        }

        while (i >= 0 && j < *wcand_p) {
            dprintf(10, "Doing A[%d] x B[%d]\n", j, i);
            if (mpcand[j] == 0 || mplier[i] == 0) {
                dprintf(10, "zero element --> skipping\n");
                goto skip;
            }
            carry = 0;
            prod = __mul_ll(mpcand[j], mplier[i]);
            carry = __add_ll(d + index, d[index], prod.lo, carry);
            carry = __add_ll(d + index + 1, d[index + 1], prod.hi, carry);
            if (carry) {
                d[index + 2]++;
            }
            if (d[index])
                dst->cnt = index + 1;
        skip:
            i--;
            j++;
        }
        dprintf(10, "\n");
        index++;
    }
    dst->cnt = d[index] ? index + 1 : dst->cnt;
}

static inline void bn_print(bn *b)
{
    uint64_t *num = bn_getnum(b);
    if (!b->cnt) {
        printf("empty\n");
        return;
    }
    printf("[%d, cap=%d]: ", b->cnt, b->cap);
    printf("0x%llx", num[b->cnt - 1]);
    for (int i = b->cnt - 2; i >= 0; i--) {
        printf("%016llx", num[i]);
    }
    printf("\n");
}

#ifdef KERNEL_MODE
#undef malloc
#undef free
#undef printf
#endif /* KERNEL_MODE */

#endif /* __ABN_H */
