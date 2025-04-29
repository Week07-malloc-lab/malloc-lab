/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <stdint.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "team 3",
    /* First member's full name */
    "goochul-im",
    /* First member's email address */
    "gooch123@naver.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

#define ALIGNMENT 8

/* 사이즈를 8의 배수로 올림 */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t))) // 이건 뭐지;;

#define WSIZE 4
#define DSIZE 8
#define INFOSIZE 12
#define CHUNKSIZE (1 << 12) // 추가 할당될 힙 크기 (최대 128KB)

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) < (y) ? (x) : (y))
#define PACK(size, n_bit, p_bit, a_bit) (((size) & ~0x7) | ((p_bit) << 1) | ((n_bit) << 2) | (a_bit))

// 헤더 주소 p를 받아서 size만 설정
#define SET_SIZE(p, size) (GET(p) = (GET(p) & 0x7) | ((size) & ~0x7))

// 헤더 주소 p를 받아서 a_bit만 설정
#define SET_A_BIT(p, a_bit) (GET(p) = (GET(p) & ~0x1) | ((a_bit) & 0x1))

// 헤더 주소 p를 받아서 p_bit만 설정
#define SET_P_BIT(p, p_bit) (GET(p) = (GET(p) & ~0x2) | (((p_bit) & 0x1) << 1))

// 헤더 주소 p를 받아서 n_bit만 설정
#define SET_N_BIT(p, n_bit) (GET(p) = (GET(p) & ~0x4) | (((n_bit) & 0x1) << 2))

#define GET(p) (*(unsigned int *)(p))              // 인자 p가 참조하는 워드를 읽어서 리턴
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // 인자 p가 가리키는 워드에 val 저장

#define GET_SIZE(p) (GET(p) & ~0x7)                       // 헤더의 사이즈 비트 리턴
#define GET_A_BIT(p) (GET(p) & 0x1)                       // 헤더의 할당 비트 리턴
#define GET_P_BIT(p) (GET(p) & 0x2)                       // 헤더의 RPEV 비트 리턴
#define GET_N_BIT(p) (GET(p) & 0x4)                       // 헤더의 넥스트 비트 리턴
#define GET_PAYLOAD(p) ((char *)(p) + DSIZE)              // 블록의 페이로드 주소 반환
#define GET_NEXT_P(p) ((char *)(p) + GET_SIZE(p) - WSIZE) // 블록의 NEXT 워드 주소 반환
#define GET_PREV_P(p) ((char *)(p) + WSIZE)               // 블록의 PREV 워드 주소 반환

#define PUT_PREV(p, addr) (PUT(GET_PREV_P(p), (addr))) // 블록의 PREV 워드에 주소 저장
#define PUT_NEXT(p, addr) (PUT(GET_NEXT_P(p), (addr))) // 블록의 NEXT 워드에 주소 저장

#define NEXT_BLOCK_P(bp) ((void *)GET(GET_NEXT_P(bp))) // 다음 블록의 시작 포인터 리턴
#define PREV_BLOCK_P(bp) ((void *)GET(GET_PREV_P(bp))) // 이전 블록의 시작 포인터 리턴

#define MIN_K 4  // 최소 2^4 바이트
#define MAX_K 17 // 최대 2^17 바이트

static size_t translate_size(size_t size);         // 비트 연산으로 정렬
static size_t get_aszie(size_t size);              // 크기 정렬
static void *divide_block(int exponent, int dest); // 분할 후 할당
static void *merge_buddy(void *bp, void *buddy);   // 버디 병합
static void *extend_heap(size_t words);            // 힙 추가 할당
static void *find_fit(size_t size);                // 가장 적절한 블록 찾기
static unsigned int log2_pow2(size_t n);           // 이 사이즈가 몇 거듭제곱인지
static unsigned int pow2_of_k(int k);              // 지수를 2의 거듭제곱으로 변환
static void save_block(int exponet, char *bp);     // 해당 블록의 헤더 설정하고 리스트에 저장
static void *find_my_buddy(void *bp);              // 버디 블록 찾기
static int is_valid_area(void *p);                 // 유효한 주소인가?

char *ava_list[14]; // 각 크기를 담을 리스트

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
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
    // printf("bp 값 : %p, heap_low : %p, heap_high : %p", bp, mem_heap_lo(), mem_heap_hi);

    SET_A_BIT(bp, 1);

    SET_P_BIT(bp, 0);
    SET_N_BIT(bp, 0);

    // if (!is_valid_area(bp) || !is_valid_area(bp + GET_SIZE(bp)))
    // {
    //     printf("\n%d번째 할당\n", cnt);
    //     printf("힙 영역을 벗어났습니다!!\nbp = %p ~ %p\n힙 시작 = %p\n힙 끝 = %p\n", bp, bp + GET_SIZE(bp), mem_heap_lo(), mem_heap_hi());
    //     printf("블록 크기 : %d, 힙 영역 크기 : %d\n", GET_SIZE(bp), mem_heap_hi() - mem_heap_lo());
    //     printf("현재 요청한 사이즈 : %d\n", size);
    //     return NULL;
    // }

    return GET_PAYLOAD(bp);
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    ptr = ptr - DSIZE;
    if ((int)ptr % 8 != 0)
    {
        printf("ptr이 8의 배수가 아닙니다 !!\n");
    }

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

    int exp = log2_pow2(GET_SIZE(ptr)) - MIN_K; // MIN_K == 4

    if (exp > 13)
    {
        printf("SIZE ERROR");
        return;
    }

    save_block(exp, ptr);
}

static void *merge_buddy(void *bp, void *buddy)
{
    void *criteria_block = MIN(bp, buddy); // 버디와 bp 둘 중 주소가 작은 블록 기준

    // 버디가 맨 앞일때
    if (!GET_P_BIT(buddy))
    {
        int idx = log2_pow2(GET_SIZE(buddy)) - 4;
        // 버디의 뒤에 리스트가 존재하면
        if (GET_N_BIT(buddy))
        {
            char *next = NEXT_BLOCK_P(buddy);
            SET_P_BIT(next, 0);
            ava_list[idx] = next;
        }
        else // 버디 혼자 리스트에 있었다면
        {
            ava_list[idx] = NULL;
        }
    }
    // 버디가 중간에 있을 때
    else if ((GET_N_BIT(buddy) & GET_P_BIT(buddy)) == 1)
    {
        char *prev = PREV_BLOCK_P(buddy);
        char *next = NEXT_BLOCK_P(buddy);

        PUT_NEXT(prev, next);
        PUT_PREV(next, prev);
        SET_N_BIT(prev, 1);
        SET_P_BIT(next, 1);
    }
    // 버디가 맨 뒤일때
    else
    {
        char *prev = PREV_BLOCK_P(buddy);
        SET_N_BIT(prev, 0);
    }

    PUT(criteria_block, PACK(GET_SIZE(bp) << 1, 0, 0, 0));
    return criteria_block;
}

static void *find_my_buddy(void *bp)
{
    size_t size = GET_SIZE(bp); // 현재 블록의 size 가져오기
    return (void *)((unsigned int)bp ^ size);
}

static int is_valid_area(void *bp)
{
    return (mem_heap_lo() <= bp && bp <= mem_heap_hi());
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
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

static size_t translate_size(size_t size)
{
    if (size == 0)
        return 1; // 0의 경우는 특별히 2^0 == 1로 취급

    size--; // 경계 처리 (n이 이미 2^k일 때 변환을 막음)
    size |= size >> 1;
    size |= size >> 2;
    size |= size >> 4;
    size |= size >> 8;
    size |= size >> 16;
    size++; // 다음 2^k로 올림

    return size;
}

static size_t get_aszie(size_t size)
{
    if (size < (1 << 4))
        size = (1 << 4); // 최소 16바이트로 강제
    if (size > (1 << 17))
        size = (1 << 17); // 최대 2^17(131072)로 강제 (선택사항)

    return translate_size(size);
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; // 워드가 2의 배수라면 WSIZE 곱해서 대입
                                                              // 아니라면 +1 해서 2의 배수로 만든다음 WSIZE 곱해서 대입
    if ((long)(bp = mem_sbrk(size)) == -1)                    // 사이즈만큼 힙 영역에서 더 할당한 다음 bp에 시작 포인터 반환
        return NULL;

    PUT(bp, PACK(size, 0, 0, 0)); // 헤더에 사이즈와 인코딩 비트 할당
    int exp = log2_pow2(size) - MIN_K;
    save_block(exp, bp); // ava_list에 새 블록을 저장
    return bp;
}

static void *find_fit(size_t size)
{
    char *bp = NULL;

    size_t asize = get_aszie(size); // 사이즈를 2의 거듭제곱으로 변환
    int idx = log2_pow2(asize) - 4; // 이 사이즈가 2의 몇 거듭제곱인지

    if (ava_list[idx] != NULL) // 해당 블록이 이미 가용 리스트에 존재하면
    {
        bp = ava_list[idx];
        if (GET_N_BIT(bp)) // 다음 블록이 있다면
        {
            char *next_bp = NEXT_BLOCK_P(bp);
            SET_P_BIT(next_bp, 0);
            SET_N_BIT(bp, 0);
            ava_list[idx] = next_bp;
        }
        else
        {
            ava_list[idx] = NULL;
        }
    }
    else // 해당 블록이 가용 리스트에 존재하지 않는다면 탐색하기
    {
        int flag = 0;
        for (int i = idx; i < 14; i++)
        {
            if (ava_list[i] != NULL)
            {
                bp = divide_block(i, idx);
                flag = 1;
                break;
            }
        }
        if (!flag) // 더 큰 블록이 가용 리스트에 존재하지 않음
        {
            // 항상 CHUNKSIZE로 확장
            bp = extend_heap(CHUNKSIZE / WSIZE);

            // 확장한 힙을 분할하여 asize 크기까지 맞춰서 사용
            int chunk_exp = log2_pow2(CHUNKSIZE) - MIN_K;
            bp = divide_block(chunk_exp, idx);
        }
    }

    PUT(bp, PACK(asize, 0, 0, 1));
    return bp;
}

static void *divide_block(int exponent, int dest)
{
    char *bp = ava_list[exponent]; // 분할할 블록
    if (GET_N_BIT(bp))             // 다음 블록이 만약에 있다면
    {
        SET_N_BIT(bp, 0);                 // 연결 끊기
        char *next_bp = NEXT_BLOCK_P(bp); // 다음 블록 저장
        SET_P_BIT(next_bp, 0);            // 다음 블록의 P 비트 0
        ava_list[exponent] = next_bp;     // 리스트의 맨 처음은 다음 블록
    }
    else
    {
        ava_list[exponent] = NULL;
    }

    // TODO: 블록 분할해서 bp + size/2 블록은 리스트에 새로 등록
    while (exponent > dest)
    {
        char *buddy = bp + (GET_SIZE(bp) >> 1); // 버디 분할
        size_t half = GET_SIZE(bp) >> 1;
        PUT(buddy, PACK(half, 0, 0, 0)); // ← buddy 헤더
        SET_SIZE(bp, half);              // ← 앞쪽 블록 헤더

        save_block(exponent - 1, buddy); // 버디를 리스트에 저장
        exponent -= 1;
    }

    SET_A_BIT(bp, 1);
    SET_P_BIT(bp, 0);
    SET_N_BIT(bp, 0);
    return bp;
}

static void save_block(int exponet, char *bp)
{
    if (ava_list[exponet] == NULL) // 리스트에 아무것도 없으면
    {
        PUT(bp, PACK(pow2_of_k(exponet + MIN_K), 0, 0, 0)); // 블록의 헤더 설정
    }
    else // 리스트에 이미 블록들이 있으면
    {
        char *fisrt_bp = ava_list[exponet];                 // 리스트의 첫번째 블록
        PUT(bp, PACK(pow2_of_k(exponet + MIN_K), 1, 0, 0)); // 블록의 헤더 설정, NEXT 비트 1로 설정
        PUT_NEXT(bp, fisrt_bp);                             // NEXT 워드에 fisrt 블록 설정
        SET_P_BIT(fisrt_bp, 1);                             // first 블록의 P 비트 설정
        PUT_PREV(fisrt_bp, bp);                             // first 블록의 PREV 워드에 bp 블록 설정
    }
    ava_list[exponet] = bp; // 리스트의 첫번째에 bp 설정
}

static unsigned int pow2_of_k(int k)
{
    return 1U << k;
}

static unsigned int log2_pow2(size_t n)
{
    int k = 0;

    while (n > 1)
    {
        n >>= 1; // 오른쪽으로 1비트 이동 (나누기 2)
        k++;
    }

    return k;
}