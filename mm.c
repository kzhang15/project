/*
 * mm.c
 * Kewei Zhang  Keweiz
 * This version of Malloc uses a segregated free list. It contains 
   multiple free list that contain a specific size. For example, seg free list 1
   contains all the free blocks that are of size 8, seg free list 2 contains all the free
   blocks that are of size 16 or lower and so forth. When malloc is called, it searches for a free block
   that fits the allocated size. If found, try to the split the block and return the block. If not found,
   extend the heap. When function free is called, it puts the block back into the seg list and try to 
   coalesce it if possible.
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
#define WSIZE 4
#define DSIZE 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)


inline unsigned int PACK(int size, int alloc) {
  return size | alloc;
}

inline unsigned int GET(char  *p ) { 
  return (*(unsigned int*)p);  
}

inline void PUT(unsigned int *p, unsigned int val) {
  p = (unsigned int *) p;
  *p = val;

}
inline unsigned int GET_SIZE(char* p) {
  return (GET(p) & 0x7ffffffe);
}

inline unsigned int GET_ALLOC(char* p) {
  return (GET(p) & 0x1);
}

inline char* FOOTER(char*p) {
  return (p+GET_SIZE(p)-WSIZE);
}

inline char*NEXT_FREE(char*p) {
  return (*(char**)(p+WSIZE));
}


/* global variables */    
static char** heap_listp;  //point at the beginning of the heap 
static char* prevPtr;   //save the prev ptr

/*helper functions*/
static char* extend_heap(int size);
static int getIndex(size_t asize);
static char* place(unsigned int asize, char*bp, char*prev);
static void* first_fit(unsigned int asize, int index);
static void relink(char*bp, char*prev);
static void* find_prev(char* p);
static int in_heap(const void *p);
static int aligned(const void *p);
/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
  
  char* prologue;
  char* epilogue;
  if((heap_listp = mem_sbrk(10*DSIZE)) == (void *)-1) 
    return -1;
  *(heap_listp+0) = NULL;  //size <=32
  *(heap_listp+1) = NULL;  //size <= 64
  *(heap_listp+2) = NULL;  //size <= 128
  *(heap_listp+3) = NULL;  //size <= 256
  *(heap_listp+4) = NULL; //size <= 512
  *(heap_listp+5) = NULL;  //size <= 1024
  *(heap_listp+6) = NULL;  //size <= 2048
  *(heap_listp+7) = NULL;  //size <= 4096
  *(heap_listp+8) = NULL;  //size > 4096
  prologue  = (char*)(heap_listp + 9);
  PUT((unsigned int *)prologue,PACK(0,1));
  epilogue = prologue + WSIZE;
  PUT((unsigned int *)epilogue,PACK(0,1));  
  return 0;
}


/* 
   extend the heap if it is full
 */
static char* extend_heap(int size) {
  char*bp = mem_sbrk(size);
  if (bp == (void*)-1)
    return bp;
  PUT((unsigned int*)(bp-WSIZE),PACK(size,1)); /* header*/
  PUT((unsigned int*)(bp+size-DSIZE),PACK(size,1)); /*footer*/
  PUT((unsigned int*)(bp+size-WSIZE),PACK(0,1)); /*new epilogue block*/
  return bp;
}


/* 
 return the index of the free list
 that the asize belongs to
*/
static int getIndex(size_t asize) {
  int index;
  if (asize <=32) {
    index = 0;
  }
  else if (asize<=64) {
    index = 1;
  }
  else if (asize<= 128) {
    index = 2;
  }
  else if (asize<= 256 ) {
    index = 3;
   }
  else if (asize<= 512) {
    index = 4;
   }
   else if (asize<=1024) {
     index = 5;
   }
   else if (asize<=2048) {
     index = 6;
   }
   else if (asize<= 4096) {
     index = 7;
   }
   else
     index = 8;
  return index;
}


/*
  search through all the the freeblocks
  in the seglist. Return NULL if no freeblocks 
  fit the size. Return the freeblock if the freeblock
  fits the size
*/
static void* first_fit(unsigned int asize, int index) { 
  prevPtr = NULL;
  char* ptr = *(heap_listp+index);
  while (ptr != NULL) { 
    if (GET_SIZE(ptr) >= asize) {
      return ptr;
    }
    else {
      prevPtr = ptr;
      ptr = NEXT_FREE(ptr);   
    }
  }
  index++;
  while (index <= 8) {
    ptr = *(heap_listp+index);
    if (ptr == NULL)
      index++;
    else {
      prevPtr = NULL;
      return ptr; 
    }
  }
  return NULL;     
}

/*
  delete the free block, bp, from the seg free list that bp 
  belongs to
*/
static void relink(char*bp, char*prev) {
   int index = getIndex(GET_SIZE(bp));
  if (prev == NULL) {
    *(index+heap_listp) = NEXT_FREE(bp);
  }
  else {
    prev = prev + WSIZE;
    *((char**)prev) = NEXT_FREE(bp);
  }

}


/*
  change the block into from free into allocated
  if possible, split the block and put the split block
  back into the seg free list
 */
static char* place (unsigned int asize, char* bp, char*prev) { 
  int csize = GET_SIZE(bp);
  int diff = csize - asize;
  if (diff > 2*DSIZE) {
    char* newbp;
    relink(bp,prev);
    PUT((unsigned int *)bp,PACK(asize,1));
    PUT((unsigned int *)FOOTER(bp),PACK(asize,1));
    newbp = bp + asize;
    PUT((unsigned int *)newbp,PACK(diff,0));
    PUT((unsigned int*)FOOTER(newbp),PACK(diff,0));
    free(newbp+WSIZE); 
  }
  else {
    PUT((unsigned int *)bp,PACK(csize,1));
    PUT((unsigned int *)FOOTER(bp),PACK(csize,1));
    relink(bp,prev);
  }
  return (bp+WSIZE); // so it points the payload
}

 /* Malloc:
    given a size, add 8 additonal bytes for header and footer.
    search the seglist for a freeblock that fits the size. If no
    blocks are found, extend the heap
 */
void *malloc (size_t size) {
  size_t asize;
  char*bp;
  int index;
  if (size == 0)
    return NULL;
  size += 8;
  if (size %8 == 0)
    asize = size;
  else
    asize = ((size/8)+1)*8;
    //change the size to the mulitple of asize
  index = getIndex(asize); //get the index to the right seg free list
  bp = first_fit(asize,index);
  if (bp == NULL) {
    bp = extend_heap(asize);
    return bp;
  }
  else {
    return (place(asize,bp,prevPtr));
  }
}

/*
  find the prev pointer to the block, p
*/
static void* find_prev(char* p) {
  int index = getIndex(GET_SIZE(p));
  prevPtr = NULL;
  char* ptr = *(heap_listp+index);
  while (ptr != p) { 
    prevPtr = ptr;
    ptr = NEXT_FREE(ptr);   
  }
  return prevPtr;
}


/*
   check if whether left or right block is free
   if so, first use relink to 
    delete that block and the current block, bp. 
   then combine then and put it back to the seg list.
*/

static void coalesce(char*bp) {
  int leftAlloc = GET_ALLOC(bp - WSIZE);
  int rightAlloc = GET_ALLOC(bp+ GET_SIZE(bp));
  char* rightBlock;
  char* leftBlock;
  int newSize;
  if (leftAlloc == 1 && rightAlloc ==1)  /* case 1 do not coalesce*/
    return;
  else if (leftAlloc ==0 && rightAlloc == 1) { /* case 2 coalesce leftblock */
    leftBlock = bp - GET_SIZE(bp-WSIZE);
    relink(bp,NULL);
    relink(leftBlock,find_prev(leftBlock));	 /* case 3 coalesce rightblock*/
    newSize = GET_SIZE(leftBlock) + GET_SIZE(bp);
    PUT((unsigned int *)leftBlock,PACK(newSize,0));
    PUT((unsigned int*)FOOTER(leftBlock),PACK(newSize,0));
    char * nextFreeBlock = *(getIndex(GET_SIZE(leftBlock)) + heap_listp); /* put new block into seg list*/
    *(getIndex(GET_SIZE(leftBlock))+heap_listp) = leftBlock;
    *((char**)(leftBlock+WSIZE)) = nextFreeBlock;
    
  }
  else if (leftAlloc ==1 && rightAlloc == 0) { /*case 3 coalesce rightblock*/
    rightBlock = bp + GET_SIZE(bp);
    relink(bp,NULL);
    relink(rightBlock,find_prev(rightBlock));
    newSize = GET_SIZE(rightBlock) + GET_SIZE(bp);
    PUT((unsigned int *)bp,PACK(newSize,0));
    PUT((unsigned int*)FOOTER(bp),PACK(newSize,0));
    char * nextFreeBlock = *(getIndex(GET_SIZE(bp)) + heap_listp);  /* put new block into seg list*/
    *(getIndex(GET_SIZE(bp))+heap_listp) = bp;
    *((char**)(bp+WSIZE)) = nextFreeBlock;
  }
  else {
    rightBlock = bp + GET_SIZE(bp); /* case 4 coalesce left and right block*/
    leftBlock = bp - GET_SIZE(bp-WSIZE);
    relink(bp,NULL);
    relink(rightBlock,find_prev(rightBlock));
    relink(leftBlock,find_prev(leftBlock));
    newSize = GET_SIZE(rightBlock) + GET_SIZE(bp) + GET_SIZE(leftBlock);
    PUT((unsigned int *)leftBlock,PACK(newSize,0));
    PUT((unsigned int*)FOOTER(leftBlock),PACK(newSize,0));
    char * nextFreeBlock = *(getIndex(GET_SIZE(leftBlock)) + heap_listp); /* put new block into seg list*/
    *(getIndex(GET_SIZE(leftBlock))+heap_listp) = leftBlock;
    *((char**)(leftBlock+WSIZE)) = nextFreeBlock;    
  } 
  return;
}


/* Free:
 * free the allocated block and coalesce the free block 
 */
void free (void *ptr) {
  
  if(!ptr) return;
  ptr = ptr- WSIZE;  //so it points at the head
  PUT((unsigned int *)ptr,PACK(GET_SIZE(ptr),0));        /*free the block*/
  PUT((unsigned int *)FOOTER(ptr),PACK(GET_SIZE(ptr),0));
 
  int size = GET_SIZE(ptr);
  char* nextFreeBlock = *(getIndex(size) + heap_listp); /*put into the seg list*/
  *((char**)(ptr+WSIZE)) = nextFreeBlock;
  *(getIndex(size) + heap_listp) = ptr;
  
  coalesce(ptr);
  return;
}

/* Realloc:
 * increases the size of the specified block of memory. Reallocates it if needed
 */
void *realloc(void *oldptr, size_t size) {
   char *bp;
  unsigned int oldsize;
  if (oldptr == NULL) {
	bp = malloc(size);
	return bp;
  }
  if (size == 0) {
    free(oldptr);  
    return NULL;
  }
  /*find new block of appropriate size */
  bp = malloc(size);
  if (bp == NULL)
	return 0;
  oldsize = GET_SIZE(oldptr - WSIZE);
  if (oldsize > size)
    oldsize = size;
  /* copy necessary memory into new block */
  memcpy(bp, oldptr, oldsize);
  /* free old block */
  free(oldptr);
  return bp;
}

/* Calloc:
 * 
 * allocates the specified number of bytes and initializes them to zero
 * 
 */
void *calloc (size_t nmemb, size_t size) {
    size_t bytes = nmemb * size;
    void *newptr;
    newptr = malloc(bytes);
    /* set all bytes to zero */
    memset(newptr, 0, bytes);
    return newptr;
  }


/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
  return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
  return (size_t)ALIGN(p) == (size_t)p;
}

/*
 * mm_checkheap
 */


/*check whether the bucket size works*/
int checkBucketSize(char* c, int index) {
  if (index == 0) {
    if (GET_SIZE(c) > 32)
      return 0;
  }
  else if (index == 1) {
    if (GET_SIZE(c) > 64)
      return 0;
  }
  else if (index == 2) {
    if (GET_SIZE(c) > 128)
      return 0;
  }
  else if (index == 3) {
     if (GET_SIZE(c) > 256)
       return 0;
  }
  else if (index == 4) {
     if (GET_SIZE(c) > 512)
       return 0;
  }
  else if (index == 5) {
    if (GET_SIZE(c) > 1024)
     return 0;
  } 
  else if (index == 6) {
    if (GET_SIZE(c) > 2048)
      return 0;
   }
  else if (index == 7) {
    if (GET_SIZE(c) > 4096)
      return 0;
  }
  else {
    if (GET_SIZE(c) <=4096)
      return 0;
  }
  return 1;
}

void mm_checkheap(int verbose) {
  
  if (verbose == 1) //redirect standard output
    dup2(2,1);
  unsigned int index = 0;
  char*prologue = (char*)(heap_listp+9);
  char*begin = prologue +WSIZE;
  if (GET_ALLOC(prologue) != 1)
    printf("invalid prologue header\n");   //check prologue 
  if (GET_SIZE(prologue) !=0)
    printf("invalid prologue header\n");
  
  while (GET_ALLOC(begin)!=1 && GET_SIZE(prologue) !=0) {
    if (GET_ALLOC(begin) != 1)  {
      char* ptr = *(heap_listp+getIndex(GET_SIZE(begin))); 
      while (ptr != NULL) { 
	if (ptr == begin)   //search for the block in the bucket
	  break;
	else
	  ptr = NEXT_FREE(ptr);
      }
      if (ptr == NULL)
	printf("did not find bucket\n");
      if (GET_ALLOC(begin) != GET_ALLOC(begin+GET_SIZE(begin)))
	printf("block is wrong\n");
      if (!(aligned + WSIZE))
	printf("align is in wrong\n");
      begin = begin + GET_SIZE(begin);
    }
  }
  
  if (GET_ALLOC(prologue) != 1)
    printf("invalid epilogue \n");  //check epilogue
  if (GET_SIZE(prologue) !=0)
    printf("invalid epilogue \n");
  
  while (index <=8) {  
    char* ptr = *(heap_listp+index);  //check bucket
    while (ptr != NULL) {
      if (!in_heap(ptr))
	printf("free pointer is out of bound\n");
      if (!aligned(ptr+WSIZE))
	printf("not aligned\n");
      if (GET_ALLOC(ptr)==1)
	printf("not free block\n");
      if (!checkBucketSize(ptr,index))
	printf("wrong bucket size\n");
      ptr = NEXT_FREE(ptr);
    }   
    index++;
  }
}
