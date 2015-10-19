#include "threads.h"
#include <stddef.h>

/* compile with gcc -pthread:
   gcc -Wall -c threads.c && gcc -Wall -pthread threads.o thread_example_aquinas.c -o thread_example_aquinas && ./thread_example_aquinas || echo $?
   
   precompile with compcert:
   ../../compcert/clightgen thread_example_aquinas.c && make -C .. progs/thread_example_aquinas.vo
*/

struct t {
  lock_t l;
  int p1;
  int p2;
  int p3;
};

void* f(void* y) {
  int temp;
  struct t* x = (struct t*)y;
  while(1) {
    acquire(&(x->l));
    temp = x->p1; x->p1 = temp * 2;
    temp = x->p2; x->p2 = temp * 2;
    temp = x->p1;
    if(temp > 10) {
      x->p3 = 0;
      release(&(x->l));
      return NULL;
    }
    release(&(x->l));
  }
}

int main() {
  struct t x;
  int i, y, z;
  x.p1 = 0;
  x.p2 = 0;
  x.p3 = 1;
  i = 0;
  makelock(&x.l);
  spawn_thread(f, &x);
  y = x.p3;
  while(y) {
    x.p1 = i;
    x.p2 = i;
    release(&x.l);
    i++;
    acquire(&x.l);
    y = x.p3;
  }
  freelock(&x.l);
  y = x.p1;
  z = x.p2;
  if(y != z) i = *(int*)NULL;
  return 0;
}
