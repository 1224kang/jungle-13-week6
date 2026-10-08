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

//명시적 가용 리스트 포인터
#define PRED(bp) (*(void**)(bp))
#define SUCC(bp) (*(void**)((char*)(bp)+DSIZE))

/*
 * mm_init - initialize the malloc package.
 */
static char *heap_listp; //프롤로그 블록을 가리키는 포인터

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void *best_fit(size_t asize);
static void place (void *bp,size_t asize);

//명시 가용리스트
static void *free_listp; //명시적리스트에서 가용리스트의 시작점을 가리킬 때 사용 
static void delete_free_listp(void *bp); //가용리스트에서 삭제
static void insert_free_listp(void *bp); //가용리스트에 삽입

int mm_init(void)
{
    free_listp=NULL;

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
 *  원소 할당된 후에 Free_listp에서 해당 원소 삭제 
 */
static void delete_free_listp(void *bp){
    
    //가용 리스트 맨 앞 원소인 경우
    if (PRED(bp)==NULL){
        if(SUCC(bp)==NULL){ //원소가 한개만 있을 때
            free_listp=NULL;
            return;
        }
        void *next=SUCC(bp);
        PRED(next)=NULL;
        free_listp=next;

        SUCC(bp)=NULL;
        return;
    }
    else if(SUCC(bp)==NULL){
        void *before=PRED(bp);
        SUCC(before)=NULL;
        return;
    }
    else{
        void *before=PRED(bp);
        void *next=SUCC(bp);

        SUCC(before)=next;
        PRED(next)=before;

        PRED(bp)=NULL;
        SUCC(bp)=NULL;
        return;
    }
}

/*
 * 블록 반환될 때 free_listp에 원소 추가 (LIFO)
 */
static void insert_free_listp(void *bp){
    void *curr=free_listp;

    //가용리스트가 비어있는 경우 
    if (free_listp==NULL){
        free_listp=bp;
        PRED(bp)=NULL;
        SUCC(bp)=NULL;
    }
    else{
        PRED(bp)=NULL;
        SUCC(bp)=curr;
        PRED(curr)=bp;
        free_listp=bp;
    }
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
        asize=3*DSIZE; //최소블록크기=24byte
    }
    else
        //size=payload, DSIZE=헤더+풋터
        //DSIZE-1=7을 더하고 나눴다 곱하면 올림이 된다.. 
        asize=DSIZE*((size+(DSIZE)+(DSIZE-1))/DSIZE); 

    //search the free list for a fit
    if ((bp=best_fit(asize))!=NULL){
        delete_free_listp(bp); //명시적 가용 리스트에서 삭제(할당되었으므로)
        place(bp,asize); //요청한 블록을 할당 + 분할 
        return bp;
    }

    //no fit found. get more memory and place the block
    extendsize=MAX(asize,CHUNKSIZE);
    if((bp=extend_heap(extendsize/WSIZE))==NULL)
        return NULL;
    delete_free_listp(bp);
    place(bp,asize);
    return bp;
    
}



/*
 * mm_free 
 */
void mm_free(void *bp)
{
    size_t size=GET_SIZE(HDRP(bp)); //반납하려는 블록 크기 
    
    PUT(HDRP(bp),PACK(size,0));
    PUT(FTRP(bp),PACK(size,0));

    coalesce(bp);
}

/*
 * coalesce - 연결 
 */
static void *coalesce(void *bp){
    size_t prev_alloc=GET_ALLOC(FTRP(PREV_BLKP(bp))); //전 블록이 할당되었는지 확인
    size_t next_alloc=GET_ALLOC(HDRP(NEXT_BLKP(bp))); //다음 블록이 할당되었는지 확인 
    size_t size=GET_SIZE(HDRP(bp));

    //이전,이후 블록 모두 할당됨
    if (prev_alloc && next_alloc){
        // return bp;
    }

    //이전 블록만 할당됨
    else if (prev_alloc && !next_alloc){
        delete_free_listp(NEXT_BLKP(bp));

        size+=GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp),PACK(size,0));
        PUT(FTRP(bp),PACK(size,0));
    }

    //이후 블록만 할당됨
    else if (!prev_alloc && next_alloc){
        delete_free_listp(PREV_BLKP(bp)); 
        
        size+=GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp),PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        bp=PREV_BLKP(bp);
    }

    //앞뒤 모두 가용 가능
    else{
        delete_free_listp(PREV_BLKP(bp));
        delete_free_listp(NEXT_BLKP(bp));

        size+=GET_SIZE(HDRP(NEXT_BLKP(bp)))+GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)),PACK(size,0));
        bp=PREV_BLKP(bp);
    }

    insert_free_listp(bp);
    return bp;

}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t extendsize; //적합한 공간이 없을 때 힙을 확장할 크기 
    size_t asize;
    size_t csize;
    size_t copySize;

    if (ptr==NULL){
        return mm_malloc(size);
    }

    if(size==0){
        mm_free(ptr);
        return NULL;
    }

    //다음 블록이 free일 때만 : csize=현재 블록 크기 + 다음 블록 크기 
    csize=GET_SIZE(HDRP(ptr)); //다음 블록이 할당 or 에필로그면 현재 블록크기만큼만 가용 가능.
    if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr)))){ 
        csize+=GET_SIZE(HDRP(NEXT_BLKP(ptr)));
    }
    
    //헤더,풋터를 포함한 필요한 크기 
    if(size<=DSIZE){
        asize=3*DSIZE;
    }
    else
        asize=DSIZE*((size+(DSIZE)+(DSIZE-1))/DSIZE); 

    //필요한 크기가 현재 블록 크기보다 작을 때 
    if(asize<=csize){
        //만약 ptr이 이미 할당된 상태라면
        if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr))))
            delete_free_listp(NEXT_BLKP(ptr));
        PUT(HDRP(ptr),PACK(csize,1)); 
        PUT(FTRP(ptr),PACK(csize,1)); 
        //기존 사이즈보다 더 작을 경우에 분할할 수 있으면 분할하기
        place(ptr,asize);
        // coalesce(NEXT_BLKP(ptr)); //🚨
        return ptr;
    }

    size_t nsize=GET_SIZE(HDRP(NEXT_BLKP(ptr))); //다음 블록 크기 
    //가용 가능한 다음 블록이 요구 데이터보다 작을 때(부족함)->새로할당+복사+해제
    if (asize>csize){ 

        //에필로그인 경우
        if(nsize==0){
            extendsize=MAX(asize-csize,CHUNKSIZE);
            void *bp=extend_heap(extendsize/WSIZE);
            if (bp==NULL) return NULL;
            //extend_heap 에서 자동으로 insert_free_listp 처리함
            delete_free_listp(bp);

            //새로 할당 받은 힙 메모리를 현재 블록에 할당
            csize+=GET_SIZE(HDRP(bp));
            PUT(HDRP(ptr),PACK(csize,1)); //헤더 할당
            PUT(FTRP(ptr),PACK(csize,1)); //헤더 할당
            place(ptr,asize);
            
            return ptr;
        }
            
        newptr=mm_malloc(size);
        copySize=GET_SIZE(HDRP(oldptr))-DSIZE; //payload만 복사
        if(size<copySize)
            copySize=size;
        memcpy(newptr,oldptr,copySize); //oldptr->newptr에 복사 
        mm_free(oldptr);
        return newptr;
    }
}

/*
 * find_fit - 묵시적 가용 리스트, first fit
 */
static void *find_fit(size_t asize){
    void* bp;

    for (bp=free_listp;bp!=NULL;bp=SUCC(bp)){
        if(!GET_ALLOC(HDRP(bp))&& asize<=GET_SIZE(HDRP(bp))){
            return bp;
        }
    }
    return NULL;
}

/*
 * find_best_fit - best fit 방식 사용
 */
static void *best_fit(size_t asize){

    void *bp;
    void *best_bp=NULL;

    for(bp=free_listp;bp!=NULL;bp=SUCC(bp)){
        
        if(!GET_ALLOC(HDRP(bp)) && asize<=GET_SIZE(HDRP(bp))){
            if(best_bp==NULL || GET_SIZE(HDRP(best_bp))>GET_SIZE(HDRP(bp))){
                best_bp=bp;
            }
            
        }
    }
    return best_bp;

}

/*
 * place - 요청한 블록을 가용 블록의 시작 부분에 배치해야. 나머지는 최소 블록 크기와 같거나 큰 경우에만 분할 
 * (가용리스트 삭제기능 없음 -> bp가 꼭 가용 블록일 필요는 없음.)
 */
static void place(void *bp,size_t asize){ //asize=이번 요청에 필요한 블록 크기 
    size_t csize=GET_SIZE(HDRP(bp)); //csize=지금 찾은 가용블록이 실제로 가진 크기 

    //최소블록 크기와 같거나 큰 경우인지 확인
    if((csize-asize)>=(3*DSIZE)){
        PUT(HDRP(bp),PACK(asize,1));
        PUT(FTRP(bp),PACK(asize,1));

        //가용리스트에서 삭제 
        // delete_free_listp(bp);

        //뒤에 남은 블록을 분할
        bp=NEXT_BLKP(bp);
        PUT(HDRP(bp),PACK((csize-asize),0));
        PUT(FTRP(bp),PACK(csize-asize,0));

        //가용리스트에 삽입 
        insert_free_listp(bp);
        
    }
    else{
        //그냥 전체 다 할당
        PUT(HDRP(bp),PACK(csize,1));
        PUT(FTRP(bp),PACK(csize,1));

        //가용리스트에서 삭제 
        // delete_free_listp(bp);
    }
}


