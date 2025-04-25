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

#include "mm.h"
#include "memlib.h"

team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* 더블 워드 정렬 */
#define ALIGNMENT 8

/* 사이즈를 8의 배수로 올림 */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t))) // 이건 뭐지;;

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 12) // 추가 할당될 힙 크기 (4KB?)

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define PACK(size, alloc) ((size) | (alloc)) // 헤더와 푸터에 저장할 정보를 만들어서 리턴
                                             // 아마 alloc에는 0과 1만 넣어줘서 이 블록이 할당인지 가용인지 나타내는듯

#define GET(p) (*(unsigned int *)(p))              // 인자 p가 참조하는 워드를 읽어서 리턴
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // 인자 p가 가리키는 워드에 val 저장

#define GET_SIZE(p) (GET(p) & ~0x7) // 헤더 or 푸터의 size 비트 리턴
#define GET_ALLOC(p) (GET(p) & 0x1) // 헤더 or 푸터의 할당 비트 리턴

#define HDRP(bp) ((char *)(bp) - WSIZE)                      // 헤더를 가리키는 포인터 리턴
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 푸터를 가리키는 포인터 리턴

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // 다음 블록의 시작 포인터 리턴
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 이전 블록의 시작 포인터 리턴

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);       // first fit으로 적절한 가용 블록 리턴
static void place(void *bp, size_t asize); // 남은 블록 분할
static char *heap_listp;

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);                            // 초기화 패딩 블록
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 블록의 헤더
    // 왜 DSIZE인가? 프롤로그 블록은 헤더 + 푸터로 2워드 크기이기 때문에
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 블록의 푸터
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     // 에필로그 블록
    heap_listp += (2 * WSIZE);

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    // int newsize = ALIGN(size + SIZE_T_SIZE); // size를 정렬해서 newsize로 만들고
    // void *p = mem_sbrk(newsize);             // 할당 후 시작 주소를 리턴, 아마 brk를 리턴하는듯
    // if (p == (void *)-1)
    //     return NULL;
    // else
    // {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }

    size_t asize; // 정렬 사이즈
    size_t extend_size;
    char *bp;

    if (size == 0)
        return NULL;

    if (size <= DSIZE)     // 만약 데이터가 8보다 작으면
        asize = 2 * DSIZE; // 블록의 크기는 16 -> 헤더 8, 데이터 + 패딩 = 8
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE); // ??뭐야이거

    if ((bp = find_fit(asize)) != NULL) // 묵시적 가용 리스트에서 적절한 블록을 할당해주고
    {
        place(bp, asize); // 해당 가용 블록을 할당해주고
        return bp;
    }
    // 적절한 가용 블록을 찾지 못했으면
    extend_size = MAX(asize, CHUNKSIZE);                 // 힙 영역을 확장
    if ((bp = extend_heap(extend_size / WSIZE)) == NULL) // WSIZE로 나누어주는 이유는 워드 단위로 인자를 받기 때문
        return NULL;                                     // extend_heap에서 병합을 수행하기 때문에 기존 가용의 끝부터 할당
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0)); // 해당 블록의 헤더 할당 비트를 0으로
    PUT(FTRP(ptr), PACK(size, 0)); // 해당 블록의 푸터 할당 비트를 0으로

    coalesce(ptr);
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

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; // 워드가 2의 배수라면 WSIZE 곱해서 대입
                                                              // 아니라면 +1 해서 2의 배수로 만든다음 WSIZE 곱해서 대입
    if ((long)(bp = mem_sbrk(size)) == -1)                    // 사이즈만큼 힙 영역에서 더 할당한 다음 bp에 시작 포인터 반환
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));         // 가용 블록 헤더
    PUT(FTRP(bp), PACK(size, 0));         // 가용 블록 푸터
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // NEXT_BLKP로 bp 블록의 다음 포인터 받아서, HDRP로 그 블록의 헤더를 받고, PACK으로
                                          // 에필로그 정보를 만든다음, PUT으로 그 정보를 저장

    return coalesce(bp); // 원래 가용 리스트의 끝이 가용 블록이었을 수도 있으니까 병합해서 리턴해주기
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // bp의 이전 블록 푸터 할당 비트
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // bp의 다음 블록 헤더 할당 비트
    size_t size = GET_SIZE(HDRP(bp));                   // bp가 가리키는 현재 블록의 크기

    if (prev_alloc && next_alloc)
    {              // 둘 다 할당 블록이면
        return bp; // 현재 블록 포인터만 반환
    }
    else if (prev_alloc && !next_alloc) // 다음 블록만 가용 블록이면
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 다음 블록을 병합하기 위해 다음 블록 사이즈도 추가
        PUT(HDRP(bp), PACK(size, 0));          // 현재 블록의 헤더의 사이즈 비트 바꾸기
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) // 이전 블록만 가용 블록이면
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));   // 이전 블록의 헤더에서 사이즈 가져와서 더하기
        PUT(FTRP(bp), PACK(size, 0));            // 현재 블록의 푸터에 새 사이즈 저장
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록의 헤더에 새 사이즈 저장
        bp = PREV_BLKP(bp);                      // bp 포인터 옮기기
    }
    else
    {                                            // 이전, 다음 블록 모두 가용 블록이면
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));   // 다음 블록 사이즈 더하기
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));   // 이전 블록 사이즈 더하기
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 다음 블록 푸터에 새 사이즈 저장
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록 헤더에 새 사이즈 저장
        bp = PREV_BLKP(bp);                      // bp 포인터 옮기기
    }
    return bp;
}

static void *find_fit(size_t asize) // first fit 구현
{
    char *bp = heap_listp + DSIZE;                           // heap_listp는 항상 프롤로그 블록의 중간
    while ((GET_SIZE(HDRP(bp)) | !GET_ALLOC(HDRP(bp))) != 0) // bp가 에필로그 블록이 아니면
    {
        size_t bp_size = GET_SIZE(HDRP(bp));
        int alloc = GET_ALLOC(HDRP(bp));
        if (alloc == 1 || bp_size < asize)
        {
            bp += bp_size;
            continue;
        }

        return bp;
    }

    return NULL;
}

static void place(void *bp, size_t asize)
{
    size_t bp_size = GET_SIZE(HDRP(bp)); // 현재 블록 사이즈
    size_t remain_size = bp_size - asize;

    if (remain_size >= 2 * DSIZE)
    { // 최소 블록은 16바이트 이상 (헤더 + 푸터 + 페이로드 8바이트)
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        PUT(HDRP(NEXT_BLKP(bp)), PACK(remain_size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(remain_size, 0));
    }
    else
    {
        PUT(HDRP(bp), PACK(bp_size, 1));
        PUT(FTRP(bp), PACK(bp_size, 1));
    }
}