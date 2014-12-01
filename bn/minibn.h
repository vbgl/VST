/* Copyright (C) 1995-1997 Eric Young (eay@cryptsoft.com)
 * All rights reserved.
 *
 * This package is an SSL implementation written
 * by Eric Young (eay@cryptsoft.com).
 * The implementation was written so as to conform with Netscapes SSL.
 *
 * This library is free for commercial and non-commercial use as long as
 * the following conditions are aheared to.  The following conditions
 * apply to all code found in this distribution, be it the RC4, RSA,
 * lhash, DES, etc., code; not just the SSL code.  The SSL documentation
 * included with this distribution is covered by the same copyright terms
 * except that the holder is Tim Hudson (tjh@cryptsoft.com).
 *
 * Copyright remains Eric Young's, and as such any Copyright notices in
 * the code are not to be removed.
 * If this package is used in a product, Eric Young should be given attribution
 * as the author of the parts of the library used.
 * This can be in the form of a textual message at program startup or
 * in documentation (online or textual) provided with the package.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. All advertising materials mentioning features or use of this software
 *    must display the following acknowledgement:
 *    "This product includes cryptographic software written by
 *     Eric Young (eay@cryptsoft.com)"
 *    The word 'cryptographic' can be left out if the rouines from the library
 *    being used are not cryptographic related :-).
 * 4. If you include any Windows specific code (or a derivative thereof) from
 *    the apps directory (application code) you must include an acknowledgement:
 *    "This product includes software written by Tim Hudson (tjh@cryptsoft.com)"
 *
 * THIS SOFTWARE IS PROVIDED BY ERIC YOUNG ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * The licence and distribution terms for any publically available version or
 * derivative of this code cannot be changed.  i.e. this code cannot simply be
 * copied and put under another distribution licence
 * [including the GNU Public Licence.]
 */
/* ====================================================================
 * Copyright (c) 1998-2006 The OpenSSL Project.  All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in
 *    the documentation and/or other materials provided with the
 *    distribution.
 *
 * 3. All advertising materials mentioning features or use of this
 *    software must display the following acknowledgment:
 *    "This product includes software developed by the OpenSSL Project
 *    for use in the OpenSSL Toolkit. (http://www.openssl.org/)"
 *
 * 4. The names "OpenSSL Toolkit" and "OpenSSL Project" must not be used to
 *    endorse or promote products derived from this software without
 *    prior written permission. For written permission, please contact
 *    openssl-core@openssl.org.
 *
 * 5. Products derived from this software may not be called "OpenSSL"
 *    nor may "OpenSSL" appear in their names without prior written
 *    permission of the OpenSSL Project.
 *
 * 6. Redistributions of any form whatsoever must retain the following
 *    acknowledgment:
 *    "This product includes software developed by the OpenSSL Project
 *    for use in the OpenSSL Toolkit (http://www.openssl.org/)"
 *
 * THIS SOFTWARE IS PROVIDED BY THE OpenSSL PROJECT ``AS IS'' AND ANY
 * EXPRESSED OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE OpenSSL PROJECT OR
 * ITS CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 * NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
 * OF THE POSSIBILITY OF SUCH DAMAGE.
 * ====================================================================
 *
 * This product includes cryptographic software written by Eric Young
 * (eay@cryptsoft.com).  This product includes software written by Tim
 * Hudson (tjh@cryptsoft.com).
 *
 */
/* ====================================================================
 * Copyright 2002 Sun Microsystems, Inc. ALL RIGHTS RESERVED.
 *
 * Portions of the attached software ("Contribution") are developed by
 * SUN MICROSYSTEMS, INC., and are contributed to the OpenSSL project.
 *
 * The Contribution is licensed pursuant to the Eric Young open source
 * license provided above.
 *
 * The binary polynomial arithmetic software is originally written by
 * Sheueling Chang Shantz and Douglas Stebila of Sun Microsystems
 * Laboratories. */

/* LENB: cut and pasted from base.h. TODO: Maybe we can cut this down further? */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
/*#include <sys/types.h>*/

typedef struct bignum_st BIGNUM;

/* BN_generate_prime_ex sets |ret| to a prime number of |bits| length. If safe
 * is non-zero then the prime will be such that (ret-1)/2 is also a prime.
 * (This is needed for Diffie-Hellman groups to ensure that the only subgroups
 * are of size 2 and (p-1)/2.).
 *
 * If |add| is not NULL, the prime will fulfill the condition |ret| % |add| ==
 * |rem| in order to suit a given generator. (If |rem| is NULL then |ret| %
 * |add| == 1.)
 *
 * If |cb| is not NULL, it will be called during processing to give an
 * indication of progress. See the comments for |BN_GENCB|. It returns one on
 * success and zero otherwise. 
 * LENB: don't support cb, don't support safe, take ADD==NULL and remove rem */
 int BN_generate_prime_ex(BIGNUM *ret, int bits); 

/* ******************************* BN_CTX operations******************** */
typedef struct bignum_ctx BN_CTX;
/* BN_CTX_new returns a new, empty BN_CTX or NULL on allocation failure. */
BN_CTX *BN_CTX_new(void);

/* BN_clear_free erases and frees the data referenced by |bn| and, if |bn| was
 * originally allocated on the heap, frees |bn| also. */
void BN_clear_free(BIGNUM *bn);

/* BN_CTX_free frees all BIGNUMs contained in |ctx| and then frees |ctx|
 * itself. */
void BN_CTX_free(BN_CTX *ctx);

/* BN_CTX_start "pushes" a new entry onto the |ctx| stack and allows future
 * calls to |BN_CTX_get|. */
void BN_CTX_start(BN_CTX *ctx);

/* BN_CTX_get returns a new |BIGNUM|, or NULL on allocation failure. Once
 * |BN_CTX_get| has returned NULL, all future calls will also return NULL until
 * |BN_CTX_end| is called. */
BIGNUM *BN_CTX_get(BN_CTX *ctx);

/* BN_CTX_end invalidates all |BIGNUM|s returned from |BN_CTX_get| since the
 * matching |BN_CTX_start| call. */
void BN_CTX_end(BN_CTX *ctx);

/* ********************************************************************** */

/* *************************************** BN_GENCB ************************* */
/* BN_GENCB holds a callback function that is used by generation functions that
 * can take a very long time to complete. Use |BN_GENCB_set| to initialise a
 * |BN_GENCB| structure.
 *
 * The callback receives the address of that |BN_GENCB| structure as its last
 * argument and the user is free to put an arbitary pointer in |arg|. The other
 * arguments are set as follows:
 *   event=BN_GENCB_GENERATED, n=i:   after generating the i'th possible prime
 *                                    number.
 *   event=BN_GENCB_PRIME_TEST, n=-1: when finished trial division primality
 *                                    checks.
 *   event=BN_GENCB_PRIME_TEST, n=i:  when the i'th primality test has finished.
 *
 * The callback can return zero to abort the generation progress or one to
 * allow it to continue.
 *
 * When other code needs to call a BN generation function it will often take a
 * BN_GENCB argument and may call the function with other argument values. */
#define BN_GENCB_GENERATED 0
#define BN_GENCB_PRIME_TEST 1

typedef struct bn_gencb_st BN_GENCB;

struct bn_gencb_st {
  void *arg;        /* callback-specific data */
  int (*callback)(int event, int n, struct bn_gencb_st *);
};

/* BN_GENCB_set configures |callback| to call |f| and sets |callout->arg| to
 * |arg|. */

/* LENB: NOT YET CALLED ANYWHERE
 * void BN_GENCB_set(BN_GENCB *callback,
 *                                int (*f)(int event, int n,
 *                                         struct bn_gencb_st *),
 *                                void *arg);
 */

/* BN_GENCB_call calls |callback|, if not NULL, and returns the return value of
 * the callback, or 1 if |callback| is NULL. */
int BN_GENCB_call(BN_GENCB *callback, int event, int n);

/* ************************************************************************* */

/* BN provides support for working with arbitary sized integers. For example,
 * although the largest integer supported by the compiler might be 64 bits, BN
 * will allow you to work with numbers until you run out of memory. */

/* ** LENB: Take OPENSSL_32_BIT values *******************************
/* BN_ULONG is the native word size when working with big integers. */
#define BN_ULONG uint32_t
#define BN_BITS2 32
#define BN_BYTES	4

/* LENB: from internal.h */
#define BN_MASK2	(0xffffffffffffffffL) //from internal.h
#define BN_BITS4	16
#define BN_MASK2l	(0xffff)
#define BN_MASK2h1	(0xffff8000L)
#define BN_MASK2h	(0xffff0000L)
#define BN_TBIT		(0x80000000L)

#define LBITS(a) ((a) & BN_MASK2l)
#define HBITS(a) (((a) >> BN_BITS4) & BN_MASK2l)

/* BN_prime_checks is magic value that can be used as the |checks| argument to
 * the primality testing functions in order to automatically select a number of
 * Miller-Rabin checks that gives a false positive rate of ~2^{-80}. */
#define BN_prime_checks 0

/* BN_init initialises a stack allocated |BIGNUM|. */
void BN_init(BIGNUM *bn);

/* BN_copy sets |dest| equal to |src| and returns |dest|. */
BIGNUM *BN_copy(BIGNUM *dest, const BIGNUM *src);

/* BN_value_one returns a static BIGNUM with value 1. */
const BIGNUM *BN_value_one(void);

/* BN_bin2bn sets |*ret| to the value of |len| bytes from |in|, interpreted as
 * a big-endian number, and returns |ret|. If |ret| is NULL then a fresh
 * |BIGNUM| is allocated and returned. It returns NULL on allocation
 * failure. */
BIGNUM *BN_bin2bn(const uint8_t *in, size_t len, BIGNUM *ret);

/* BN_hex2bn parses the leading hex number from |in|, which may be proceeded by
 * a '-' to indicate a negative number and may contain trailing, non-hex data.
 * If |outp| is not NULL, it constructs a BIGNUM equal to the hex number and
 * stores it in |*outp|. If |*outp| is NULL then it allocates a new BIGNUM and
 * updates |*outp|. It returns the number of bytes of |in| processed or zero on
 * error. */
int BN_hex2bn(BIGNUM **outp, const char *in);

/* BN_set_word sets |bn| to |value|. It returns one on success or zero on
 * allocation failure. */
int BN_set_word(BIGNUM *bn, BN_ULONG value);

/* BN_num_bits returns the minimum number of bits needed to represent the
 * absolute value of |bn|. */
unsigned BN_num_bits(const BIGNUM *bn);

/* bn_wexpand ensures that |bn| has at least |words| works of space without
 * altering its value. It returns one on success or zero on allocation
 * failure. */
BIGNUM *bn_wexpand(BIGNUM *bn, unsigned words);

/* BN_num_bytes returns the
 minimum number of bytes needed to represent the
 * absolute value of |bn|. */
unsigned BN_num_bytes(const BIGNUM *bn);

/* BN_with_flags initialises a stack allocated |BIGNUM| with pointers to the
 * contents of |in| but with |flags| ORed into the flags field.
 *
 * Note: the two BIGNUMs share state and so |out| should /not/ be passed to
 * |BN_free|. */
void BN_with_flags(BIGNUM *out, const BIGNUM *in, int flags);

/* BN_is_negative returns one if |bn| is negative and zero otherwise. */
int BN_is_negative(const BIGNUM *bn);

/* BN_is_zero returns one if |bn| is zero and zero otherwise. */
int BN_is_zero(const BIGNUM *bn);

/* BN_is_one returns one if |bn| equals one and zero otherwise. */
int BN_is_one(const BIGNUM *bn);

/* BN_cmp returns a value less than, equal to or greater than zero if |a| is
 * less than, equal to or greater than |b|, respectively. */
int BN_cmp(const BIGNUM *a, const BIGNUM *b);

/* BN_ucmp returns a value less than, equal to or greater than zero if the
 * absolute value of |a| is less than, equal to or greater than the absolute
 * value of |b|, respectively. */
int BN_ucmp(const BIGNUM *a, const BIGNUM *b);

/* BN_add sets |r| = |a| + |b|, where |r| may be the same pointer as either |a|
 * or |b|. It returns one on success and zero on allocation failure. */
int BN_add(BIGNUM *r, const BIGNUM *a, const BIGNUM *b);

/* BN_sub sets |r| = |a| - |b|, where |r| must be a distinct pointer from |a|
 * and |b|. It returns one on success and zero on allocation failure. */
int BN_sub(BIGNUM *r, const BIGNUM *a, const BIGNUM *b);

/* BN_mul sets |r| = |a| * |b|, where |r| may be the same pointer as |a| or
 * |b|. Returns one on success and zero otherwise. */
int BN_mul(BIGNUM *r, const BIGNUM *a, const BIGNUM *b,
                          BN_CTX *ctx);

/* BN_div divides |numerator| by |divisor| and places the result in |quotient|
 * and the remainder in |rem|. Either of |quotient| or |rem| may be NULL, in
 * which case the respective value is not returned. The result is rounded
 * towards zero; thus if |numerator| is negative, the remainder will be zero or
 * negative. It returns one on success or zero on error. */
int BN_div(BIGNUM *quotient, BIGNUM *rem,
                          const BIGNUM *numerator, const BIGNUM *divisor,
                          BN_CTX *ctx);

/* BN_mod is a helper macro that calls |BN_div| and discards the quotient. */
#define BN_mod(rem, numerator, divisor, ctx) \
  BN_div(NULL, (rem), (numerator), (divisor), (ctx))

/* BN_mod_inverse sets |out| equal to |a|^-1, mod |n|. If either of |a| or |n|
 * have |BN_FLG_CONSTTIME| set then the operation is performed in constant
 * time. If |out| is NULL, a fresh BIGNUM is allocated. It returns the result
 * or NULL on error. */
BIGNUM *BN_mod_inverse(BIGNUM *out, const BIGNUM *a,
                                      const BIGNUM *n, BN_CTX *ctx);

/* BN_gcd sets |r| = gcd(|a|, |b|). It returns one on success and zero
 * otherwise. */
int BN_gcd(BIGNUM *r, const BIGNUM *a, const BIGNUM *b,
                          BN_CTX *ctx);

int BN_mod_exp(BIGNUM *r, const BIGNUM *a, const BIGNUM *p,
                              const BIGNUM *m, BN_CTX *ctx);

struct bignum_st {
  BN_ULONG *d; /* Pointer to an array of 'BN_BITS2' bit chunks in little-endian
                  order. */
  int top;   /* Index of last used element in |d|, plus one. */
  int dmax;  /* Size of |d|, in words. */
  int neg;   /* one if the number is negative */
  int flags; /* bitmask of BN_FLG_* values */
};

#define BN_FLG_MALLOCED 0x01
#define BN_FLG_STATIC_DATA 0x02
/* avoid leaking exponent information through timing, BN_mod_exp_mont() will
 * call BN_mod_exp_mont_consttime, BN_div() will call BN_div_no_branch,
 * BN_mod_inverse() will call BN_mod_inverse_no_branch. */
#define BN_FLG_CONSTTIME 0x04

