#include <stddef.h>

int zero = 0;
int *ctr = &zero;

void reset() {
  int* ctr0 = ctr;
  *ctr0 = 0;
}

void incr() {
  int* ctr0 = ctr;
  int t = *ctr0;
  *ctr0 = t +1;
}

int read() {
  int* ctr0 = ctr;
  int t = *ctr0;
  return t;
}

int main()
{
  int t;
  reset();
  incr();
  incr();
  t = read();
  return t;
}
