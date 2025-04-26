/*
 * mm-buddy.c - Buddy System based malloc lab (using heap-relative offsets)
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include "mm.h"
#include "memlib.h"

team_t team = {
    "team 3",
    "goochul-im",
    "gooch123@naver.com",
    "",
    ""};

#define ALIGNMENT 8
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4
#define DSIZE 8
#define INFOSIZE 12
#define CHUNKSIZE (1 << 12)

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) < (y) ? (x) : (y))
#define PACK(size, n_bit, p_bit, a_bit) (((size) & ~0x7) | ((p_bit) << 1) | ((n_bit) << 2) | (a_bit))

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_A_BIT(p) (GET(p) & 0x1)
#define GET_P_BIT(p) (GET(p) & 0x2)
#define GET_N_BIT(p) (GET(p) & 0x4)

#define SET_SIZE(p, size) (GET(p) = (GET(p) & 0x7) | ((size) & ~0x7))
#define SET_A_BIT(p, a_bit) (GET(p) = (GET(p) & ~0x1) | ((a_bit) & 0x1))
#define SET_P_BIT(p, p_bit) (GET(p) = (GET(p) & ~0x2) | (((p_bit) & 0x1) << 1))
#define SET_N_BIT(p, n_bit) (GET(p) = (GET(p) & ~0x4) | (((n_bit) & 0x1) << 2))

#define PUT_ADDR(p, addr) (PUT((p), (unsigned int)((char *)(addr) - (char *)mem_heap_lo())))
#define GET_ADDR(p) ((char *)mem_heap_lo() + GET(p))

#define GET_PAYLOAD(p) ((char *)(p) + DSIZE)
#define GET_NEXT_P(p) ((char *)(p) + GET_SIZE(p) - WSIZE)
#define GET_PREV_P(p) ((char *)(p) + WSIZE)

#define PUT_PREV(p, addr) (PUT_ADDR(GET_PREV_P(p), (addr)))
#define PUT_NEXT(p, addr) (PUT_ADDR(GET_NEXT_P(p), (addr)))

#define NEXT_BLOCK_P(bp) (GET_ADDR(GET_NEXT_P(bp)))
#define PREV_BLOCK_P(bp) (GET_ADDR(GET_PREV_P(bp)))

#define MIN_K 4
#define MAX_K 17

static size_t translate_size(size_t size);
static size_t get_asize(size_t size);
static void *divide_block(int exponent, int dest);
static void *merge_buddy(void *bp, void *buddy);
static void *extend_heap(size_t words);
static void *find_fit(size_t size);
static unsigned int log2_pow2(size_t n);
static unsigned int pow2_of_k(int k);
static void save_block(int exponent, char *bp);
static void *find_my_buddy(void *bp);
static int is_valid_area(void *p);

char *ava_list[14];

int mm_init(void)
{
    memset(ava_list, 0, sizeof(ava_list));
    char *bp;
    if ((bp = (char *)extend_heap(CHUNKSIZE / WSIZE)) == NULL)
        return -1;
    return 0;
}

void *mm_malloc(size_t size)
{
    char *bp;
    if ((bp = find_fit(size + INFOSIZE)) == NULL)
        return NULL;

    SET_A_BIT(bp, 1);
    SET_P_BIT(bp, 0);
    SET_N_BIT(bp, 0);

    return GET_PAYLOAD(bp);
}

void mm_free(void *ptr)
{
    while (1)
    {
        void *buddy = find_my_buddy(ptr);

        if (!is_valid_area(buddy))
            break;
        if (GET_A_BIT(buddy))
            break;
        if (GET_SIZE(ptr) != GET_SIZE(buddy))
            break;

        ptr = merge_buddy(ptr, buddy);
    }

    int exp = log2_pow2(GET_SIZE(ptr)) - MIN_K;
    save_block(exp, ptr);
}

void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(bp, PACK(size, 0, 0, 0));
    int exp = log2_pow2(size) - MIN_K;
    save_block(exp, bp);
    return bp;
}

static void *find_fit(size_t size)
{
    char *bp = NULL;

    size_t asize = get_asize(size);
    int idx = log2_pow2(asize) - MIN_K;

    for (int i = idx; i < 14; i++)
    {
        if (ava_list[i] != NULL)
        {
            bp = divide_block(i, idx);
            return bp;
        }
    }

    bp = extend_heap(CHUNKSIZE / WSIZE);
    int chunk_exp = log2_pow2(CHUNKSIZE) - MIN_K;
    return divide_block(chunk_exp, idx);
}

static void *divide_block(int exponent, int dest)
{
    char *bp = ava_list[exponent];
    ava_list[exponent] = NEXT_BLOCK_P(bp);

    while (exponent > dest)
    {
        exponent--;
        char *buddy = bp + (1 << (exponent + MIN_K));
        save_block(exponent, buddy);
        SET_SIZE(bp, (1 << (exponent + MIN_K)));
    }

    SET_A_BIT(bp, 1);
    return bp;
}

static void save_block(int exponent, char *bp)
{
    PUT(bp, PACK((1 << (exponent + MIN_K)), 0, 0, 0));
    PUT_NEXT(bp, ava_list[exponent]);
    ava_list[exponent] = bp;
}

static void *find_my_buddy(void *bp)
{
    size_t size = GET_SIZE(bp);
    unsigned int offset = (unsigned int)((char *)bp - (char *)mem_heap_lo());
    unsigned int buddy_offset = offset ^ size;
    return (char *)mem_heap_lo() + buddy_offset;
}

static void *merge_buddy(void *bp, void *buddy)
{
    char *criteria_block = MIN(bp, buddy);
    SET_SIZE(criteria_block, GET_SIZE(bp) << 1);
    return criteria_block;
}

static int is_valid_area(void *bp)
{
    return (mem_heap_lo() <= (char *)bp && (char *)bp <= mem_heap_hi());
}

static size_t translate_size(size_t size)
{
    if (size == 0)
        return 1;
    size--;
    size |= size >> 1;
    size |= size >> 2;
    size |= size >> 4;
    size |= size >> 8;
    size |= size >> 16;
    size++;
    return size;
}

static size_t get_asize(size_t size)
{
    if (size < (1 << 4))
        size = (1 << 4);
    if (size > (1 << 17))
        size = (1 << 17);
    return translate_size(size);
}

static unsigned int log2_pow2(size_t n)
{
    unsigned int k = 0;
    while (n > 1)
    {
        n >>= 1;
        k++;
    }
    return k;
}
