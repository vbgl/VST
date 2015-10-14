#include "threads.h"
#include <stddef.h>

/* compile with gcc -pthread:
   gcc -Wall -c threads.c && gcc -Wall -pthread threads.o thread_example2.c -o thread_example2 && ./thread_example2 || echo $?
   
   precompile with compcert:
   ../../compcert/clightgen thread_example2.c && make -C .. progs/thread_example2.vo
*/

void* malloc(size_t);
void free(void *);

struct ab {
  lock_t lock;
  lock_t join;
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
  release(&ab->join);
  exit_thread();
  return NULL;
}

int main (void) {
  struct ab *ab = (struct ab*)malloc(sizeof(struct ab));
  makelock(&ab->lock);
  makelock(&ab->join);
  ab->a = 1;
  ab->b = 2;
  release(&ab->lock);
  spawn_thread(&f, (void*)ab);
  acquire(&ab->join);
  freelock(&ab->lock);
  freelock(&ab->join);
  return 0;
}

