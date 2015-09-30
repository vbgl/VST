#include "threads.h"
/* #include <stdio.h> */
#include <stddef.h>

/*
gcc -Wall -c threads.c
gcc -Wall -pthread threads.o thread_example1.c -o thread_example1 && ./thread_example1
../../compcert/clightgen thread_example1.c
make -C .. progs/thread_example1.vo
*/

void* malloc(size_t);
void free(void *);

struct ab {
  lock_t lock;
  int a;
  int b; /* invariant : b=2a */
};

void* f(void *args) {
  struct ab *ab = (struct ab*)args;
  int t;
  lock_t l;
  l = ab->lock;
  acquire(l);
  t = ab->a;
  ab->a = t + 1;
  t = ab->b;
  ab->b = t + 2;
  release(l);
  exit_thread();
  return NULL;
}

int main (void) {
  struct ab *ab = (struct ab*)malloc(sizeof(struct ab));
  int a, b;
  void *l;
  void *(*pf)(void*);
  /* printf("%lu\n", sizeof(struct ab)); */
  l = (void*)new_lock();
  make_lock(l);
  ab->lock = l;
  ab->a = 1;
  ab->b = 2;
  release(l);
  
  pf=&f; /* we don't need this, but this is easier to debug */
  spawn_thread(pf, (void*)ab);
  
  acquire(l);
  a = ab->a;
  while(a == 1) {
    release(l);
    acquire(l);
    a = ab->a;
  }
  b = ab->b;
  release(l);
  /* printf("a,b=%d,%d\n", ab->a, ab->b); */
  
  free_lock(l);
  return b;
}

