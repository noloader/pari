/* Copyright (C) 2016  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

#include "pari.h"
#include "paripriv.h"
#include "anal.h"

/* return good chunk size for sieve, 16 | chunk + 2 */
static ulong
optimize_chunk(ulong a, ulong b)
{
  /* TODO: Optimize size (surely < 512k to stay in L1 cache, but not so large */
  /* as to force recalculating too often). */
  /* Guesstimate: greater of sqrt(n) * lg(n) or 1M */
  ulong chunk = maxuu(0x100000, usqrt(b) * expu(b));
  ulong tmp = (b - a) / chunk + 1;

  if (tmp == 1)
    chunk = b - a + 16;
  else
    chunk = (b - a) / tmp + 15;
  /* Don't take up more than 2/3 of the stack */
  chunk = minuu(chunk, avma - stack_lim(avma, 2));
  /* ensure 16 | chunk + 2 */
  return (((chunk + 2)>>4)<<4) - 2;
}
static void
sieve_init(forprime_t *T, ulong a, ulong b)
{
  T->sieveb = b;
  T->chunk = optimize_chunk(a, b);
  T->sieve = (unsigned char*)stack_malloc(((T->chunk+2) >> 4) + 1);
  T->cache[0] = 0;
  /* >> 1 [only odds] + 3 [convert from bits to bytes] */
  T->a = a;
  T->end = minuu(a + T->chunk, b);
  T->pos = T->maxpos = 0;
}

enum {PRST_none, PRST_diffptr, PRST_sieve, PRST_unextprime, PRST_nextprime};

static void
u_forprime_set_prime_table(forprime_t *T, ulong a)
{
  T->strategy = PRST_diffptr;
  if (a < 3)
  {
    T->p = 0;
    T->d = diffptr;
  }
  else
    T->p = init_primepointer_lt(a, &T->d);
}

/* Set p so that p + q the smallest integer = c (mod q) and > original p.
 * Assume 0 < c < q. Set p = 0 on overflow */
static void
arith_set(forprime_t *T)
{
  ulong r = T->p % T->q; /* 0 <= r <= min(p, q-1) */
  pari_sp av = avma;
  GEN d = adduu(T->p - r, T->c);
  if (T->c > r) d = subiu(d, T->q);
  /* d = c mod q,  d = c > r? p-r+c-q: p-r+c, so that
   *  d <= p  and  d+q = c>r? p-r+c  : p-r+c+q > p */
  T->p = itou_or_0(d); avma = av; /* d = 0 is impossible */
}

/* run through primes in arithmetic progression = c (mod q).
 * Assume (c,q)=1, 0 <= c < q */
int
u_forprime_arith_init(forprime_t *T, ulong a, ulong b, ulong c, ulong q)
{
  ulong maxp, maxp2;
  if (a > b || b < 2)
  {
    T->strategy = PRST_diffptr; /* paranoia */
    T->p = 0; /* empty */
    T->b = 0; /* empty */
    T->d = diffptr;
    return 0;
  }
  maxp = maxprime();
  if (q != 1 && c != 2 && odd(q)) {
    /* only allow *odd* primes. If c = 2, then p = 2 must be included :-( */
    if (!odd(c)) c += q;
    q <<= 1;
  }
  T->q = q;
  T->c = c;
  T->strategy = PRST_none; /* unknown */
  T->sieve = NULL; /* unused for now */
  if (!odd(b) && b > 2) b--;
  T->b = b;
  if (maxp >= b) { /* [a,b] \subset prime table */
    u_forprime_set_prime_table(T, a);
    return 1;
  }
  /* b > maxp */
  if (a >= maxp)
  {
    T->p = a - 1;
    if (T->q > 1) arith_set(T);
  }
  else
    u_forprime_set_prime_table(T, a);

  maxp2 = (maxp & HIGHMASK)? 0 : maxp*maxp;
  /* FIXME: should sieve as well if q != 1, adapt sieve code */
  if (q != 1 || (maxp2 && maxp2 <= a)
             || T->b - maxuu(a,maxp) < maxp / expu(b))
  { if (T->strategy==PRST_none) T->strategy = PRST_unextprime; }
  else
  { /* worth sieving */
#ifdef LONG_IS_64BIT
    const ulong UPRIME_MAX = 18446744073709551557UL;
#else
    const ulong UPRIME_MAX = 4294967291UL;
#endif
    ulong sieveb;
    if (b > UPRIME_MAX) b = UPRIME_MAX;
    sieveb = b;
    if (maxp2 && maxp2 < b) sieveb = maxp2;
    if (T->strategy==PRST_none) T->strategy = PRST_sieve;
    sieve_init(T, maxuu(maxp+2, a), sieveb);
  }
  return 1;
}

/* will run through primes in [a,b] */
int
u_forprime_init(forprime_t *T, ulong a, ulong b)
{ return u_forprime_arith_init(T, a,b, 0,1); }
/* now only run through primes <= c; assume c <= b above */
void
u_forprime_restrict(forprime_t *T, ulong c) { T->b = c; }

/* b = NULL: loop forever */
int
forprime_init(forprime_t *T, GEN a, GEN b)
{
  long lb;
  a = gceil(a); if (typ(a) != t_INT) pari_err_TYPE("forprime_init",a);
  if (signe(a) <= 0) a = gen_1;
  if (b && typ(b) != t_INFINITY)
  {
    b = gfloor(b);
    if (typ(b) != t_INT) pari_err_TYPE("forprime_init",b);
    if (signe(b) < 0 || cmpii(a,b) > 0)
    {
      T->strategy = PRST_nextprime; /* paranoia */
      T->bb = gen_0;
      T->pp = gen_0;
      return 0;
    }
    lb = lgefint(b);
  }
  else if (!b || inf_get_sign(b) > 0)
    lb = lgefint(a) + 4;
  else /* b == -oo */
  {
    T->strategy = PRST_nextprime; /* paranoia */
    T->bb = gen_0;
    T->pp = gen_0;
    return 0;
  }
  T->bb = b;
  T->pp = cgeti(lb);
  /* a, b are positive integers, a <= b */
  if (lgefint(a) == 3) /* lb == 3 implies b != NULL */
    return u_forprime_init(T, uel(a,2), lb == 3? uel(b,2): ULONG_MAX);
  T->strategy = PRST_nextprime;
  affii(subiu(a,1), T->pp);
  return 1;
}

/* assume a <= b <= maxprime()^2, a,b odd, sieve[n] corresponds to
 *   a+16*n, a+16*n+2, ..., a+16*n+14 (bits 0 to 7)
 * maxpos = index of last sieve cell. */
static void
sieve_block(ulong a, ulong b, ulong maxpos, unsigned char* sieve)
{
  ulong p = 2, lim = usqrt(b), sz = (b-a) >> 1;
  byteptr d = diffptr+1;
  (void)memset(sieve, 0, maxpos+1);
  for (;;)
  { /* p is odd */
    ulong k, r;
    NEXT_PRIME_VIADIFF(p, d); /* starts at p = 3 */
    if (p > lim) break;

    /* solve a + 2k = 0 (mod p) */
    r = a % p;
    if (r == 0)
      k = 0;
    else
    {
      k = p - r;
      if (odd(k)) k += p;
      k >>= 1;
    }
    /* m = a + 2k is the smallest odd m >= a, p | m */
    /* position n (corresponds to a+2n) is sieve[n>>3], bit n&7 */
    while (k <= sz) { sieve[k>>3] |= 1 << (k&7); k += p; /* 2k += 2p */ }
  }
}

/* T->cache is a 0-terminated list of primes, return the first one and
 * remove it from list. Most of the time the list contains a single prime */
static ulong
shift_cache(forprime_t *T)
{
  long i;
  T->p = T->cache[0];
  for (i = 1;; i++)  /* remove one prime from cache */
    if (! (T->cache[i-1] = T->cache[i]) ) break;
  return T->p;
}

ulong
u_forprime_next(forprime_t *T)
{
  if (T->strategy == PRST_diffptr)
  {
    for(;;)
    {
      if (!*(T->d))
      {
        T->strategy = T->sieve? PRST_sieve: PRST_unextprime;
        if (T->q != 1) { arith_set(T); if (!T->p) return 0; }
        /* T->p possibly not a prime if q != 1 */
        break;
      }
      else
      {
        NEXT_PRIME_VIADIFF(T->p, T->d);
        if (T->p > T->b) return 0;
        if (T->q == 1 || T->p % T->q == T->c) return T->p;
      }
    }
  }
  if (T->strategy == PRST_sieve)
  {
    ulong n;
    if (T->cache[0]) return shift_cache(T);
NEXT_CHUNK:
    for (n = T->pos; n < T->maxpos; n++)
      if (T->sieve[n] != 0xFF)
      {
        unsigned char mask = T->sieve[n];
        ulong p = T->a + (n<<4);
        long i = 0;
        T->pos = n;
        if (!(mask &  1)) T->cache[i++] = p;
        if (!(mask &  2)) T->cache[i++] = p+2;
        if (!(mask &  4)) T->cache[i++] = p+4;
        if (!(mask &  8)) T->cache[i++] = p+6;
        if (!(mask & 16)) T->cache[i++] = p+8;
        if (!(mask & 32)) T->cache[i++] = p+10;
        if (!(mask & 64)) T->cache[i++] = p+12;
        if (!(mask &128)) T->cache[i++] = p+14;
        T->cache[i] = 0;
        T->pos = n+1;
        return shift_cache(T);
      }
    /* n = T->maxpos, last cell: check p <= b */
    if (T->maxpos && n == T->maxpos && T->sieve[n] != 0xFF)
    {
      unsigned char mask = T->sieve[n];
      ulong p = T->a + (n<<4);
      long i = 0;
      T->pos = n;
      if (!(mask &  1) && p <= T->sieveb) T->cache[i++] = p;
      if (!(mask &  2) && p <= T->sieveb-2) T->cache[i++] = p+2;
      if (!(mask &  4) && p <= T->sieveb-4) T->cache[i++] = p+4;
      if (!(mask &  8) && p <= T->sieveb-6) T->cache[i++] = p+6;
      if (!(mask & 16) && p <= T->sieveb-8) T->cache[i++] = p+8;
      if (!(mask & 32) && p <= T->sieveb-10) T->cache[i++] = p+10;
      if (!(mask & 64) && p <= T->sieveb-12) T->cache[i++] = p+12;
      if (!(mask &128) && p <= T->sieveb-14) T->cache[i++] = p+14;
      if (i)
      {
        T->cache[i] = 0;
        T->pos = n+1;
        return shift_cache(T);
      }
    }

    if (T->maxpos && T->end >= T->sieveb) /* done with sieves ? */
    {
      if (T->sieveb == T->b && T->b != ULONG_MAX) return 0;
      T->strategy = PRST_unextprime;
    }
    else
    { /* initialize next chunk */
      if (T->maxpos == 0)
        T->a |= 1; /* first time; ensure odd */
      else
        T->a = (T->end + 2) | 1;
      T->end = T->a + T->chunk; /* may overflow */
      if (T->end < T->a || T->end > T->sieveb) T->end = T->sieveb;
      /* end and a are odd; sieve[k] contains the a + 8*2k + (0,2,...,14).
       * The largest k is (end-a) >> 4 */
      T->pos = 0;
      T->maxpos = (T->end - T->a) >> 4;
      sieve_block(T->a, T->end, T->maxpos, T->sieve);
      goto NEXT_CHUNK;
    }
  }
  if (T->strategy == PRST_unextprime)
  {
    if (T->q == 1)
      T->p = unextprime(T->p + 1);
    else
    {
      do {
        T->p += T->q;
        if (T->p < T->q) return 0; /* overflow */
      } while (!uisprime(T->p));
    }
    if (!T->p) /* overflow ulong, switch to GEN */
      T->strategy = PRST_nextprime;
    else
    {
      if (T->p > T->b) return 0;
      return T->p;
    }
  }
  return 0; /* overflow */
}

GEN
forprime_next(forprime_t *T)
{
  pari_sp av;
  GEN p;
  if (T->strategy != PRST_nextprime)
  {
    ulong q = u_forprime_next(T);
    if (q) { affui(q, T->pp); return T->pp; }
    /* failure */
    if (T->strategy != PRST_nextprime) return NULL; /* we're done */
    /* overflow ulong, switch to GEN */
    affui(ULONG_MAX, T->pp); /* initialize */
  }
  av = avma;
  p = nextprime(addiu(T->pp, 1));
  if (T->bb && absi_cmp(p, T->bb) > 0) { avma = av; return NULL; }
  affii(p, T->pp); avma = av; return T->pp;
}

void
forprime(GEN a, GEN b, GEN code)
{
  pari_sp av = avma;
  forprime_t T;

  if (!forprime_init(&T, a,b)) { avma = av; return; }

  push_lex(T.pp,code);
  while(forprime_next(&T))
  {
    closure_evalvoid(code); if (loop_break()) break;
    /* p changed in 'code', complain */
    if (get_lex(-1) != T.pp)
      pari_err(e_MISC,"prime index read-only: was changed to %Ps", get_lex(-1));
  }
  pop_lex(1); avma = av;
}

int
forcomposite_init(forcomposite_t *C, GEN a, GEN b)
{
  pari_sp av = avma;
  a = gceil(a); if (typ(a)!=t_INT) pari_err_TYPE("forcomposite",a);
  if (b) {
    b = gfloor(b);if (typ(b)!=t_INT) pari_err_TYPE("forcomposite",b);
  }
  if (signe(a) < 0) pari_err_DOMAIN("forcomposite", "a", "<", gen_0, a);
  if (cmpiu(a, 4) < 0) a = utoipos(4);
  C->first = 1;
  if (!forprime_init(&C->T, a,b))
  {
    C->n = gen_1; /* in case caller forgets to check the return value */
    C->b = gen_0;
    avma = av; return 0;
  }
  C->n = setloop(a);
  C->b = b;
  C->p = NULL; return 1;
}

GEN
forcomposite_next(forcomposite_t *C)
{
  if (C->first) /* first call ever */
  {
    C->first = 0;
    C->p = forprime_next(&C->T);
  }
  else
    C->n = incloop(C->n);
  if (C->p)
  {
    if (cmpii(C->n, C->p) < 0) return C->n;
    C->n = incloop(C->n);
    /* n = p+1 */
    C->p = forprime_next(&C->T); /* nextprime(p) > n */
    if (C->p) return C->n;
  }
  if (!C->b || cmpii(C->n, C->b) <= 0) return C->n;
  return NULL;
}

void
forcomposite(GEN a, GEN b, GEN code)
{
  pari_sp av = avma;
  forcomposite_t T;
  GEN n;
  if (!forcomposite_init(&T,a,b)) return;
  push_lex(T.n,code);
  while((n = forcomposite_next(&T)))
  {
    closure_evalvoid(code); if (loop_break()) break;
    /* n changed in 'code', complain */
    if (get_lex(-1) != n)
      pari_err(e_MISC,"index read-only: was changed to %Ps", get_lex(-1));
  }
  pop_lex(1); avma = av;
}
