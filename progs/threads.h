/* as far as I could determine, mutexes are 24 chars long on 32 bits,
   40 chars long on 64 bit linux machines */
/* typedef struct {char a[8]; void* b[4];} lock_t; */
typedef struct lock_t {char a[8]; void* b[4];} lock_t;

void makelock(lock_t *lock);

void freelock(lock_t *lock);

void acquire(lock_t *lock);

void release(lock_t *lock);

void spawn_thread(void* (*f)(void*), void* args);

void exit_thread(void);

/* condition variables are 48 chars */
typedef struct cond_t {char a[48];} cond_t;

void wait(cond_t *cv, lock_t *lock);

void signal(cond_t *cv);
