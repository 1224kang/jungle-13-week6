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

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "team 3",
    /* First member's full name */
    "Minseo Kang",
    /* First member's email address */
    "cherrykang2003@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7) //

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
#define WSIZE 4
#define DSIZE 8 //double word size(bytes)
#define CHUNKSIZE (1<<12) //힙이 부족할 때 한 번에 늘리는 기본 크기 //4KB(4096byte)

#define MAX(x,y) ((x)>(y)?(x):(y))
#define PACK(size,alloc) ((size)|(alloc)) //header,footer 저장

//read and write a word at address p
#define GET(p) (*(unsigned int*)(p)) //인자 p가 참조하는 워드 읽어서 반환
#define PUT(p,val) (*(unsigned int*)(p)=(val)) //인자 p가 가리키는 워드에 val 저장 

//Read the size and allocated fields from address p
#define GET_SIZE(p) (GET(p)&~0x7)
#define GET_ALLOC(p) (GET(p)&0x1)

//Given block ptr bp, compute address of its header and footer
#define HDRP(bp) ((char*)(bp)-WSIZE) //헤더 가리키는 포인터 반환
#define FTRP(bp) ((char*)(bp)+GET_SIZE(HDRP(bp))-DSIZE) //푸터 포인터 반환

//Given block ptr bp, compute address of next and previous blocks
#define NEXT_BLKP(bp) ((char*)(bp)+GET_SIZE(((char*)(bp)-WSIZE))) //다음 블록 페이로드 포인터  
#define PREV_BLKP(bp) ((char*)(bp)-GET_SIZE(((char*)(bp)-DSIZE))) //이전 블록의 bp


/*
 * mm_init - initialize the malloc package.
 */
static char *heap_listp; //프롤로그 블록을 가리키는 포인터

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place (void *bp,size_t asize);

int mm_init(void)
{
    /*create the initial empty heap*/
    if ((heap_listp=mem_sbrk(4*WSIZE))==(void *)-1)
        return -1;
    PUT(heap_listp,0); //패딩
    PUT(heap_listp+(1*WSIZE),PACK(DSIZE,1)); //prologue header
    PUT(heap_listp+(2*WSIZE),PACK(DSIZE,1)); //prologue footer
    PUT(heap_listp+(3*WSIZE),PACK(0,1)); //epilogue header
    heap_listp+=(2*WSIZE);

    //Extend the empty heap with a free block of CHUNKSIZE bytes
    if (extend_heap(CHUNKSIZE/WSIZE)==NULL)
        return -1;
    return 0;
}

static void *extend_heap(size_t words){
    char *bp;
    size_t size;

    //allocate an even number of words to maintain alignment
    size=(words%2)?(words+1)*WSIZE:words*WSIZE; //double word 정렬
    if((long)(bp=mem_sbrk(size))==-1)
        return NULL;
    
    //Initialize free block header/footer and the epilogue header
    PUT(HDRP(bp),PACK(size,0)); //free block header
    PUT(FTRP(bp),PACK(size,0)); //free block footer
    PUT(HDRP(NEXT_BLKP(bp)),PACK(0,1)); //new epilogue header

    //return if the previous block was free
    return coalesce(bp);

}


/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize; //헤더,푸터를 고려한 최소블록 크기
    size_t extendsize; //적합한 공간이 없을 때 힙을 확장할 크기 
    char *bp;

    if (size==0){
        return NULL;
    }

    //오버헤드 및 정렬 요건을 포함하도록 블록 크기 조정 
    if(size<=DSIZE){
        asize=2*DSIZE; //최소블록크기=16byte
    }
    else
        //size=payload, DSIZE=헤더+풋터
        //DSIZE-1=7을 더하고 나눴다 곱하면 올림이 된다.. 
        asize=DSIZE*((size+(DSIZE)+(DSIZE-1))/DSIZE); 

    //search the free list for a fit
    if ((bp=find_fit(asize))!=NULL){
        place(bp,asize);
        return bp;
    }

    //no fit found. get more memory and place the block
    extendsize=MAX(asize,CHUNKSIZE);
    if((bp=extend_heap(extendsize/WSIZE))==NULL)
        return NULL;
    place(bp,asize);
    return bp;
    
}



/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size=GET_SIZE(HDRP(bp)); //반납하려는 블록 크기 

    PUT(HDRP(bp),PACK(size,0));
    PUT(FTRP(bp),PACK(size,0));
    coalesce(bp);
}

static void *coalesce(void *bp){
    size_t prev_alloc=GET_ALLOC(FTRP(PREV_BLKP(bp))); //전 블록이 할당되었는지 확인
    size_t next_alloc=GET_ALLOC(HDRP(NEXT_BLKP(bp))); //다음 블록이 할당되었는지 확인 
    size_t size=GET_SIZE(HDRP(bp));

    //이전,이후 블록 모두 할당됨
    if (prev_alloc && next_alloc){
        return bp;
    }

    //이전 블록만 할당됨
    else if (prev_alloc && !next_alloc){
        size+=GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp),PACK(size,0));
        PUT(FTRP(bp),PACK(size,0));
    }

    //이후 블록만 할당됨
    else if (!prev_alloc && next_alloc){
        size+=GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp),PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        bp=PREV_BLKP(bp);
    }

    //앞뒤 모두 가용 가능
    else{
        size+=GET_SIZE(HDRP(NEXT_BLKP(bp)))+GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)),PACK(size,0));
        bp=PREV_BLKP(bp);
    }
    return bp;

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
    copySize = GET_SIZE(HDRP(oldptr))-DSIZE; //페이지크기
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

/*
 * find_fit - 묵시적 가용 리스트, first fit
 */
static void *find_fit(size_t asize){
    void* bp;

    for (bp=heap_listp;GET_SIZE(HDRP(bp))>0;bp=NEXT_BLKP(bp)){
        if(!GET_ALLOC(HDRP(bp))&& asize<=GET_SIZE(HDRP(bp))){
            return bp;
        }
    }
    return NULL;
}

/*
 * place - 요청한 블록을 가용 블록의 시작 부분에 배치해야. 나머지는 최소 블록 크기와 같거나 큰 경우에만 분할 
 */
static void place(void *bp,size_t asize){ //asize=이번 요청에 필요한 블록 크기 
    size_t csize=GET_SIZE(HDRP(bp)); //csize=지금 찾은 가용블록이 실제로 가진 크기 

    //최소블록 크기와 같거나 큰 경우인지 확인
    if((csize-asize)>=(2*DSIZE)){
        PUT(HDRP(bp),PACK(asize,1));
        PUT(FTRP(bp),PACK(asize,1));
        bp=NEXT_BLKP(bp);

        PUT(HDRP(bp),PACK((csize-asize),0));
        PUT(FTRP(bp),PACK(csize-asize,0));
    }
    else{
        PUT(HDRP(bp),PACK(csize,1));
        PUT(FTRP(bp),PACK(csize,1));
    }
}