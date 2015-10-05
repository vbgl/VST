#include "threads.h"
#include <stddef.h>
/* #include <stdio.h> */

/* compile with gcc -pthread:
   gcc -Wall -c threads.c && gcc -Wall -pthread threads.o thread_example1.c -o thread_example1 && ./thread_example1 || echo $?
   
   precompile with compcert:
   ../../compcert/clightgen thread_example1.c && make -C .. progs/thread_example1.vo
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
  acquire(&ab->lock);
  t = ab->a;
  ab->a = t + 1;
  t = ab->b;
  ab->b = t + 2;
  release(&ab->lock);
  exit_thread();
  return NULL;
}

int main (void) {
  struct ab *ab = (struct ab*)malloc(sizeof(struct ab));
  int a, b;
  /* void *l; */
  /* void *(*pf)(void*); */
  /* printf("%lu\n", sizeof(struct ab)); */
  /* l = (void*)newlock(); */
  makelock(&ab->lock);
  ab->a = 1;
  ab->b = 2;
  release(&ab->lock);
  
  /* pf=&f; /\* we don't need this, but this is easier to debug *\/ */
  spawn_thread(&f, (void*)ab);
  
  acquire(&ab->lock);
  a = ab->a;
  while(a == 1) {
    release(&ab->lock);
    acquire(&ab->lock);
    a = ab->a;
  }
  b = ab->b;
  release(&ab->lock);
  /* printf("a,b=%d,%d\n", ab->a, ab->b); */
  
  freelock(&ab->lock);
  return b;
}

