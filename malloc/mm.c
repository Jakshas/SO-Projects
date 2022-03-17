/*Jakub Szajner 315700 jestem jedynym autorem kodu źródłowego
  Wykozystałem funkcje pomocnicze z pliku mm-implicit.c wszytskie jakie były
  dostepne Struktura zajetego bloku to |header|zawarość| a wolnego to
  |header|puste|foother|. W zajetych blokach nie potrzebujemy footera bo footer
  przydaje sie gdy złączamy wolne bloki z Mój algorytm używa zoptymalizowanych
  boundary tagów i uzywa strategi best fit do znajdowania bloków. Planowałem
  jeszcze urzyć listy wolnych bloków ale pomimo tego ze sama lista działała
  prawidłowo i dało sie na niej wykonywać poprawnie akcje przyspieszajace kod to
  jakiekolwiek dodanie takiego wolnego bloku sprawiało, że kod wykonujacy testy
  się zapętlał i rzucał błędem Segmentation fault. Pisze o tym w opisie ponieważ
  jest to bardzo dziwne i niestandardowe zachowanie programu. Po ponad dwóch
  dniach prób naprawiania tego kodu nie znalazłem przycyny. Wracając do opisu
  działania programu malloc jelsi nie znajdzie zadnego miejsca porzeza stos
  wywołaniem sbrk. Realloc stara się poszeżać zaalokowany blok zanim zaalokuje
  nowy blok a ten zwolni.
*/

#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stddef.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.
 * When you hand in, remove the #define DEBUG line. */
// #define DEBUG
#ifdef DEBUG
#define debug(fmt, ...) printf("%s: " fmt "\n", __func__, __VA_ARGS__)
#define msg(...) printf(__VA_ARGS__)
#else
#define debug(fmt, ...)
#define msg(...)
#endif

#define __unused __attribute__((unused))

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* !DRIVER */

typedef int32_t word_t; /* Heap is bascially an array of 4-byte words. */

typedef enum {
  FREE = 0,     /* Block is free */
  USED = 1,     /* Block is used */
  PREVFREE = 2, /* Previous block is free (optimized boundary tags) */
} bt_flags;

static word_t *heap_start; /* Address of the first block */
static word_t *heap_end;   /* Address past last byte of last block */
static word_t *last;       /* Points at last block */
static word_t *free_start; // free list start block
static word_t *free_last;  // free list last block

/* --=[ boundary tag handling ]=-------------------------------------------- */

static inline word_t bt_size(word_t *bt) {
  return *bt & ~(USED | PREVFREE);
}

static inline int bt_used(word_t *bt) {
  return *bt & USED;
}

static inline int bt_free(word_t *bt) {
  return !(*bt & USED);
}

/* Given boundary tag address calculate it's buddy address. */
static inline word_t *bt_footer(word_t *bt) {
  return (void *)bt + bt_size(bt) - sizeof(word_t);
}

/* Given payload pointer returns an address of boundary tag. */
static inline word_t *bt_fromptr(void *ptr) {
  return (word_t *)ptr - 1;
}

/* Creates boundary tag(s) for given block. */
static inline void bt_make(word_t *bt, size_t size, bt_flags flags) {
  *bt = size | flags;
  if (bt_free(bt))
    *bt_footer(bt) = size | flags;
}

/* Previous block free flag handling for optimized boundary tags. */
static inline bt_flags bt_get_prevfree(word_t *bt) {
  return *bt & PREVFREE;
}

static inline void bt_clr_prevfree(word_t *bt) {
  if (bt)
    *bt &= ~PREVFREE;
}

static inline void bt_set_prevfree(word_t *bt) {
  *bt |= PREVFREE;
}

/* Returns address of payload. */
static inline void *bt_payload(word_t *bt) {
  return bt + 1;
}

/* Returns address of next block or NULL. */
static inline word_t *bt_next(word_t *bt) {
  if (bt == last) {
    return NULL;
  } else {
    return (void *)bt + bt_size(bt);
  }
}

/* Returns address of previous block or NULL. */
static inline word_t *bt_prev(word_t *bt) {
  if (bt == heap_start) {
    return NULL;
  } else {
    return (void *)bt - bt_size(bt - 1);
  }
}

/* --=[ miscellanous procedures ]=------------------------------------------ */

/* Calculates block size incl. header, footer & payload,
 * and aligns it to block boundary (ALIGNMENT). */
static inline size_t blksz(size_t size) {
  return (size + sizeof(word_t) + ALIGNMENT - 1) & -ALIGNMENT;
}
// returns addres of next free block
static inline word_t *bt_next_free(word_t *bt) {
  return bt + 1;
}
// returns addres of prev free block
static inline word_t *bt_prev_free(word_t *bt) {
  return bt + 2;
}
// returns next free block
static inline word_t *get_next_free(word_t *bt) {
  word_t *bytes_to_next = bt_next_free(bt);
  if (*bytes_to_next == 0)
    return NULL;
  return (void *)bt + *bytes_to_next;
}
// returns prev free block
static inline word_t *get_prev_free(word_t *bt) {
  word_t *bytes_to_next = bt_prev_free(bt);
  if (*bytes_to_next == 0)
    return NULL;
  return (void *)bt - *bytes_to_next;
}
// add block to free list
static inline void add_to_free_list(word_t *bt) {
  if (bt_free(bt)) {
    if (free_start == NULL) {
      free_start = bt;
      free_last = bt;
      *bt_next_free(bt) = 0;
      *bt_prev_free(bt) = 0;
    } else {
      int diff = (void *)bt - (void *)free_last;
      *bt_next_free(free_last) = diff;
      free_last = bt;
      *bt_prev_free(bt) = diff;
      *bt_next_free(bt) = 0;
    }
  }
}
// remove block from free list
static inline void remove_from_free_list(word_t *bt) {
  word_t *prev = get_prev_free(bt);
  word_t *next = get_next_free(bt);
  // do acording to other in list
  if (free_start == bt && !prev && !next) {
    free_start = NULL;
    free_last = NULL;
  } else {
    if (free_start == bt && !prev && next) {
      *bt_prev_free(next) = 0;
      free_start = next;
    } else {
      if (free_last == bt && prev && !next) {
        *bt_next_free(prev) = 0;
        free_last = prev;
      } else {
        if (prev && next) {
          int diff = (void *)next - (void *)prev;
          *bt_next_free(prev) = diff;
          *bt_prev_free(next) = diff;
        }
      }
    }
  }
}
// give more memory
static void *morecore(size_t size) {
  void *ptr = mem_sbrk(size);
  if (ptr == (void *)-1)
    return NULL;
  return ptr;
}
// splits block acording to size
static inline void split(word_t *bt, size_t size) {
  if (bt_size(bt) == size) {
    return;
  }
  // making two new blocks
  // remove_from_free_list(bt);
  word_t *bt2 = (void *)bt + size;
  bt_make(bt2, bt_size(bt) - size, FREE);
  bt_make(bt, size, USED);
  // add_to_free_list(bt2);
  if (bt == last) {
    last = bt2;
  }
}
// merges two blocks
static inline void merge(word_t *first, word_t *second, bt_flags flag) {
  // get size of two blocks set flags and make new block
  size_t size = bt_size(first) + bt_size(second);
  if (second == last)
    last = first;
  // if (bt_free(first))
  //   remove_from_free_list(first);
  // if (bt_free(second))
  //   remove_from_free_list(second);
  word_t *next = bt_next(second);
  if (flag && FREE > 0) {
    flag |= bt_get_prevfree(first);
    if (next != NULL) {
      bt_set_prevfree(next);
    }
  } else {
    if (next != NULL) {
      bt_clr_prevfree(next);
    }
  }
  // if(flag && FREE){
  //   add_to_free_list(first);
  // }
  bt_make(first, size, flag);
}

/* --=[ mm_init ]=---------------------------------------------------------- */

int mm_init(void) {
  /* Pad heap start so first payload is at ALIGNMENT. */
  void *ptr = morecore(ALIGNMENT - sizeof(word_t));
  if (!ptr)
    return -1;
  heap_start = NULL;
  heap_end = NULL;
  last = NULL;
  free_start = NULL;
  free_last = NULL;
  return 0;
}

/* --=[ malloc ]=----------------------------------------------------------- */

#if 0
/* First fit startegy. */
static word_t *find_fit(size_t reqsz) {
  if (heap_start == NULL) {
    return NULL;
  }
  // find first block
  word_t *bt = heap_start;
  while ((bt != NULL && bt_used(bt)) ||
         (bt != NULL && bt_free(bt) && bt_size(bt) < reqsz)) {
    bt = bt_next(bt);
  }
  // split found block
  if (bt != NULL && bt_size(bt) >= reqsz) {
    split(bt, reqsz);
    return bt;
  }
  return NULL;
}
#else
/* Best first startegy. */
static word_t *find_fit(size_t reqsz) {
  if (heap_start == NULL) {
    return NULL;
  }
  // find first fitting block
  word_t *bt = heap_start;
  while ((bt != NULL && bt_used(bt)) ||
         (bt != NULL && bt_free(bt) && bt_size(bt) < reqsz)) {
    bt = bt_next(bt);
  }
  // find best block compare
  word_t *best = bt;
  while (bt != NULL) {
    if ((bt != NULL && bt_free(bt) && bt_size(bt) >= reqsz &&
         bt_size(bt) < bt_size(best))) {
      best = bt;
    }
    bt = bt_next(bt);
  }
  // split best block
  if (best != NULL && bt_size(best) >= reqsz) {
    split(best, reqsz);
    return best;
  }
  return NULL;
}
#endif

void *malloc(size_t size) {
  if (size == 0) {
    return NULL;
  }
  size = blksz(size);
  word_t *bt = find_fit(size);
  // if free block not found try expanding las block if it is not free add new
  // block
  if (bt == NULL) {
    if (last && bt_free(last)) {
      size_t difference = size - bt_size(last);
      bt = morecore(difference);
      bt_make(bt, difference, USED);
      merge(last, bt, USED | bt_get_prevfree(last));
      // remove_from_free_list(last);
      // mm_checkheap(0);
      return bt_payload(last);
    }
    bt = morecore(size);
    last = bt;
  }
  // if first element add it as heap_start, end and last
  if (heap_start == NULL) {
    heap_start = bt;
    heap_end = bt;
    last = bt;
  }
  // make bt and remove prevfree from next
  bt_make(bt, size, USED);
  word_t *next = bt_next(bt);
  if (next != NULL)
    bt_clr_prevfree(next);
  // remove_from_free_list(bt);
  //  mm_checkheap(0);
  return bt_payload(bt);
}

/* --=[ free ]=------------------------------------------------------------- */

void free(void *ptr) {
  if (ptr == NULL)
    return;
  // get block
  word_t *bt = bt_fromptr(ptr);
  int8_t make = 0;
  // if prev free merge
  word_t *next = bt_next(bt);
  if (bt_get_prevfree(bt)) {
    word_t *prev = bt_prev(bt);
    make = 1;
    merge(prev, bt, FREE);
    bt = prev;
    if (next != NULL)
      bt_set_prevfree(next);
  }
  // if next free merge
  if (next != NULL && bt_free(next)) {
    make = 1;
    merge(bt, next, FREE);
    if (bt_next(next) != NULL)
      bt_set_prevfree(bt_next(next));
  }
  // if not merged change to free
  if (make == 0) {
    bt_make(bt, bt_size(bt), FREE);
    if (next != NULL)
      bt_set_prevfree(next);
    // add_to_free_list(bt);
  }

  // mm_checkheap(0);
}

/* --=[ realloc ]=---------------------------------------------------------- */

void *realloc(void *old_ptr, size_t size) {
  /* If size == 0 then this is just free, and we return NULL. */
  if (size == 0) {
    free(old_ptr);
    return NULL;
  }
  /* If old_ptr is NULL, then this is just malloc. */
  if (!old_ptr)
    return malloc(size);
  // get word and if it is less than size split block
  word_t *bt = bt_fromptr(old_ptr);
  word_t *next = bt_next(bt);
  if (blksz(size) <= bt_size(bt)) {
    // if (next != NULL)
    //   bt_set_prevfree(next);
    split(bt, blksz(size));
    return old_ptr;
  }
  // if next free get size you need and split
  if (next != NULL && bt_free(next) &&
      blksz(size) <= bt_size(bt) + bt_size(next)) {
    split(next, blksz(size) - bt_size(bt));
    merge(bt, next, USED | bt_get_prevfree(bt));
    return old_ptr;
  }
  // default make new big block and free old
  void *new_ptr = malloc(size);
  memcpy(new_ptr, old_ptr, (bt_size(bt) - sizeof(word_t)));
  free(old_ptr);
  // mm_checkheap(0);
  return new_ptr;
}

/* --=[ calloc ]=----------------------------------------------------------- */

void *calloc(size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *new_ptr = malloc(bytes);

  /* If malloc() fails, skip zeroing out the memory. */
  if (new_ptr)
    memset(new_ptr, 0, bytes);

  return new_ptr;
}

/* --=[ mm_checkheap ]=----------------------------------------------------- */

void mm_checkheap(int verbose) {
  // write heap and free list
  word_t *block = heap_start;
  printf("heap:\n");
  while (block != NULL) {
    printf("\taddr: %p\n", block);
    printf("\tprevious: %d\n", bt_get_prevfree(block));
    printf("\tfree: %d\n", bt_free(block));
    printf("\tsize: %d\n\n", bt_size(block));
    block = bt_next(block);
  }
  printf("heap end\n");
  word_t *fr = free_start;
  printf("free\n");
  while (fr != NULL) {
    printf("\taddr: %p\n", fr);
    printf("\tprevious: %d\n", bt_get_prevfree(fr));
    printf("\tfree: %d\n", bt_free(fr));
    printf("\tsize: %d\n\n", bt_size(fr));
    fr = get_next_free(fr);
  }
  printf("free end\n");
}