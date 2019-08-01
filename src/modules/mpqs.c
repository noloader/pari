/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/* Written by Thomas Papanikolaou and Xavier Roblot
 *
 * Implementation of the Self-Initializing Multi-Polynomial Quadratic Sieve
 * based on code developed as part of the LiDIA project
 * (http://www.informatik.tu-darmstadt.de/TI/LiDIA/)
 *
 * Extensively modified by The PARI group.
 */
/* Notation commonly used in this file, and sketch of algorithm:
 *
 * Given an odd integer N > 1 to be factored, we throw in a small odd squarefree
 * multiplier k so as to make kN = 1 mod 4 and to have many small primes over
 * which X^2 - kN splits.  We compute a factor base FB of such primes then
 * look for values x0 such that Q0(x0) = x0^2 - kN can be decomposed over FB,
 * up to a possible factor dividing k and a possible "large prime". Relations
 * involving the latter can be combined into full relations which don't; full
 * relations, by Gaussian elimination over F2 for the exponent vectors lead us
 * to an expression X^2 - Y^2 divisible by N and hopefully to a nontrivial
 * splitting when we compute gcd(X + Y, N).  Note that this can never
 * split prime powers.
 *
 * Candidates x0 are found by sieving along arithmetic progressions modulo the
 * small primes in FB and evaluation of candidates picks out those x0 where
 * many of these progressions coincide, resulting in a highly divisible Q0(x0).
 *
 * The Multi-Polynomial version improves this by choosing a modest subset of
 * FB primes (let A be their product) and forcing these to divide Q0(x).
 * Write Q(x) = Q0(2Ax + B) = (2Ax + B)^2 - kN = 4A(Ax^2 + Bx + C), where B is
 * suitably chosen.  For each A, there are 2^omega_A possible values for B
 * but we'll use only half of these, since the other half is easily covered by
 * exploiting the symmetry x -> -x of the original Q0. The "Self-Initializating"
 * bit refers to the fact that switching from one B to the next is fast, whereas
 * switching to the next A involves some recomputation (C is never needed).
 * Thus we quickly run through many polynomials sharing the same A.
 *
 * The sieve ranges over values x0 such that |x0| < M  (we use x = x0 + M
 * as array subscript).  The coefficients A are chosen so that A*M ~ sqrt(kN).
 * Then |B| is bounded by ~ (j+4)*A, and |C| = -C ~ (M/4)*sqrt(kN), so
 * Q(x0)/(4A) takes values roughly between -|C| and 3|C|.
 *
 * Refinements. We do not use the smallest FB primes for sieving, incorporating
 * them only after selecting candidates).  The substition of 2Ax+B into
 * X^2 - kN, with odd B, forces 2 to occur; when kN is 1 mod 8, it occurs at
 * least to the 3rd power; when kN = 5 mod 8, it occurs exactly to the 2nd
 * power.  We never sieve on 2 and always pull out the power of 2 directly. The
 * prime factors of k show up whenever 2Ax + B has a factor in common with k;
 * we don't sieve on these either but easily recognize them in a candidate. */
#include "pari.h"
#include "paripriv.h"

/** DEBUG **/
/* #define MPQS_DEBUG_VERBOSE 1 */
#include "mpqs.h"

#define REL_OFFSET 20
#define REL_MASK ((1UL<<REL_OFFSET)-1)
#define MAX_PE_PAIR 60
#define DEFAULT_VEC_LEN 17

static GEN rel_q(GEN c) { return gel(c,3); }
static GEN rel_Y(GEN c) { return gel(c,1); }
static GEN rel_p(GEN c) { return gel(c,2); }

static void
frel_add(hashtable *frel, GEN R)
{
  ulong h = hash_GEN(R);
  if (!hash_search2(frel, (void*)R, h))
    hash_insert2(frel, (void*)R, (void*)1, h);
}
static void
vec_frel_add(hashtable *frel, GEN V)
{
  long i, l = lg(V);
  for (i = 1; i<l ; i++)
    frel_add(frel, gel(V,i));
}

static GEN
vec_extend(GEN frel, GEN rel, long nfrel)
{
  long lfrel = lg(frel)-1;
  if (nfrel > lfrel)
  {
    lfrel *= 2;
    frel = vec_lengthen(frel, lfrel);
    if (DEBUGLEVEL >= 4) err_printf("MPQS: extending store to %ld\n",lfrel);
  }
  gel(frel, nfrel) = rel;
  return frel;
}

/*********************************************************************/
/**                                                                 **/
/**                         INITIAL SIZING                          **/
/**                                                                 **/
/*********************************************************************/
/* number of decimal digits of argument - for parameter choosing and for
 * diagnostics */
static long
decimal_len(GEN N)
{ pari_sp av = avma; return gc_long(av, 1+logint(N,stoi(10))); }

/* To be called after choosing k and putting kN into the handle:
 * Pick up the requested parameter set for the given size of kN in decimal
 * digits and fill in various fields in the handle.  Return 0 when kN is
 * too large, 1 when we're ok. */
static int
mpqs_set_parameters(mpqs_handle_t *h)
{
  long i, s, D;
  const mpqs_parameterset_t *P;

  h->digit_size_kN = D = decimal_len(h->kN);
  if (D > MPQS_MAX_DIGIT_SIZE_KN) return 0;
  i = maxss(0, D - 9);
  if (D >= 90)
    pari_warn(warner, "MPQS: factoring this number will take several hours:\nN = %Ps", h->N);

  P = &(mpqs_parameters[i]);
  h->tolerance      = P->tolerance;
  h->lp_scale       = P->lp_scale;
  /* make room for prime factors of k if any: */
  h->size_of_FB     = s = P->size_of_FB + h->_k->omega_k;
  /* for the purpose of Gauss elimination etc., prime factors of k behave
   * like real FB primes, so take them into account when setting the goal: */
  h->target_no_rels = (s >= 200 ? s + 70 : (mpqs_int32_t)(s * 1.35));
  h->M              = P->M;
  h->omega_A        = P->omega_A;
  h->no_B           = 1UL << (P->omega_A - 1);
  h->pmin_index1    = P->pmin_index1;
  /* certain subscripts into h->FB should also be offset by omega_k: */
  h->index0_FB      = 3 + h->_k->omega_k;
  /* following are converted from % to parts per thousand: */
  h->first_sort_point = P->first_sort_point;
  h->sort_pt_interval = P->sort_pt_interval;

  if (DEBUGLEVEL >= 5)
  {
    err_printf("MPQS: kN = %Ps\n", h->kN);
    err_printf("MPQS: kN has %ld decimal digits\n", D);
    err_printf("\t(estimated memory needed: %4.1fMBy)\n",
               (s + 1)/8388608. * h->target_no_rels);
  }
  return 1;
}

/*********************************************************************/
/**                                                                 **/
/**                       OBJECT HOUSEKEEPING                       **/
/**                                                                 **/
/*********************************************************************/

/* factor base constructor. Really a home-grown memalign(3c) underneath.
 * We don't want FB entries to straddle L1 cache line boundaries, and
 * malloc(3c) only guarantees alignment adequate for all primitive data
 * types of the platform ABI - typically to 8 or 16 byte boundaries.
 * Also allocate the inv_A_H array.
 * The FB array pointer is returned for convenience */
static mpqs_FB_entry_t *
mpqs_FB_ctor(mpqs_handle_t *h)
{
  /* leave room for slots 0, 1, and sentinel slot at the end of the array */
  long size_FB_chunk = (h->size_of_FB + 3) * sizeof(mpqs_FB_entry_t);
  /* like FB, except this one does not have a sentinel slot at the end */
  long size_IAH_chunk = (h->size_of_FB + 2) * sizeof(mpqs_inv_A_H_t);
  char *fbp = (char*)stack_malloc(size_FB_chunk + 64);
  char *iahp = (char*)stack_malloc(size_IAH_chunk + 64);
  long fbl, iahl;

  h->FB_chunk = (void *)fbp;
  h->invAH_chunk = (void *)iahp;
  /* round up to next higher 64-bytes-aligned address */
  fbl = (((long)fbp) + 64) & ~0x3FL;
  /* and put the actual array there */
  h->FB = (mpqs_FB_entry_t *)fbl;

  iahl = (((long)iahp) + 64) & ~0x3FL;
  h->inv_A_H = (mpqs_inv_A_H_t *)iahl;
  return (mpqs_FB_entry_t *)fbl;
}

/* sieve array constructor;  also allocates the candidates array
 * and temporary storage for relations under construction */
static void
mpqs_sieve_array_ctor(mpqs_handle_t *h)
{
  long size = (h->M << 1) + 1;
  mpqs_int32_t size_of_FB = h->size_of_FB;

  h->sieve_array = (unsigned char *) stack_malloc(size * sizeof(unsigned char));
  h->sieve_array_end = h->sieve_array + size - 2;
  h->sieve_array_end[1] = 255; /* sentinel */
  h->candidates = (long *)stack_malloc(MPQS_CANDIDATE_ARRAY_SIZE * sizeof(long));
  /* whereas mpqs_self_init() uses size_of_FB+1, we just use the size as
   * it is, not counting FB[1], to start off the following estimate */
  if (size_of_FB > MAX_PE_PAIR) size_of_FB = MAX_PE_PAIR;
  /* and for tracking which primes occur in the current relation: */
  h->relaprimes = (long *) stack_malloc((size_of_FB << 1) * sizeof(long));
}

/* mpqs() calls the following (after recording avma) to allocate GENs for
 * the current polynomial and self-initialization scratchpad data on the
 * PARI stack.  This space is released by mpqs() itself at the end. */
static void
mpqs_poly_ctor(mpqs_handle_t *h)
{
  mpqs_int32_t i;
  long size_per = h->omega_A * sizeof(mpqs_per_A_prime_t);

  h->per_A_pr = (mpqs_per_A_prime_t *) stack_calloc(size_per);
  /* Sizing:  A is the product of omega_A primes, each well below word
   * size.
   * |B| is bounded by (omega_A + 4) * A, so can have at most one word
   * more, and that's generous.
   * |C| is less than A*M^2, so can take at most two words more than A.
   * The array H holds residues modulo A, so the same size as used for A
   * is sufficient. */
  h->A = cgeti(h->omega_A + 2);
  h->B = cgeti(h->omega_A + 3);
#ifdef MPQS_DEBUG
  h->C = cgeti(h->omega_A + 4);
#endif
  for (i = 0; i < h->omega_A; i++)
    h->per_A_pr[i]._H = cgeti(h->omega_A + 2);
  /* the handle starts out all zero, so in particular bin_index and index_i
   * are initially 0.
   * TODO: index_j currently initialized in mqps() but this is going to
   * change. */
}

/* TODO: relationsdb handle */

/*********************************************************************/
/**                                                                 **/
/**                        FACTOR BASE SETUP                        **/
/**                                                                 **/
/*********************************************************************/
/* fill in the best-guess multiplier k for N. We force kN = 1 mod 4.
 * Caller should proceed to fill in kN */
static ulong
mpqs_find_k(mpqs_handle_t *h)
{
  const pari_sp av = avma;
  const long N_mod_8 = mod8(h->N), N_mod_4 = N_mod_8 & 3;
  forprime_t S;
  struct {
    const mpqs_multiplier_t *_k;
    long np; /* number of primes in factorbase so far for this k */
    double value; /* the larger, the better */
  } cache[MPQS_POSSIBLE_MULTIPLIERS];
  ulong p, i, nbk;

  for (i = nbk = 0; i < numberof(cand_multipliers); i++)
  {
    const mpqs_multiplier_t *cand_k = &cand_multipliers[i];
    long k = cand_k->k;
    double v;
    if ((k & 3) != N_mod_4) continue; /* want kN = 1 (mod 4) */
    v = -0.35 * log2((double)k);
    if ((k & 7) == N_mod_8) v += M_LN2; /* kN = 1 (mod 8) */
    cache[nbk].np = 0;
    cache[nbk]._k = cand_k;
    cache[nbk].value = v;
    if (++nbk == MPQS_POSSIBLE_MULTIPLIERS) break; /* enough */
  }
  /* next test is an impossible situation: kills spurious gcc-5.1 warnings
   * "array subscript is above array bounds" */
  if (nbk > MPQS_POSSIBLE_MULTIPLIERS) nbk = MPQS_POSSIBLE_MULTIPLIERS;
  u_forprime_init(&S, 2, ULONG_MAX);
  while ( (p = u_forprime_next(&S)) )
  {
    long kroNp = kroiu(h->N, p), seen = 0;
    if (!kroNp) return p;
    for (i = 0; i < nbk; i++)
    {
      if (cache[i].np > MPQS_MULTIPLIER_SEARCH_DEPTH) continue;
      seen++;
      if (krouu(cache[i]._k->k % p, p) == kroNp) /* kronecker(k*N, p)=1 */
      {
        cache[i].value += log2((double) p)/p;
        cache[i].np++;
      }
    }
    if (!seen) break; /* we're gone through SEARCH_DEPTH primes for all k */
  }
  if (!p) pari_err_OVERFLOW("mpqs_find_k [ran out of primes]");
  {
    long best_i = 0;
    double v = cache[0].value;
    for (i = 1; i < nbk; i++)
      if (cache[i].value > v) { best_i = i; v = cache[i].value; }
    h->_k = cache[best_i]._k; return gc_ulong(av,0);
  }
}

/******************************/
/* Create a factor base of 'size' primes p_i such that legendre(k*N, p_i) != -1
 * We could have shifted subscripts down from their historical arrangement,
 * but this seems too risky for the tiny potential gain in memory economy.
 * The real constraint is that the subscripts of anything which later shows
 * up at the Gauss stage must be nonnegative, because the exponent vectors
 * there use the same subscripts to refer to the same FB entries.  Thus in
 * particular, the entry representing -1 could be put into FB[0], but could
 * not be moved to FB[-1] (although mpqs_FB_ctor() could be easily adapted
 * to support negative subscripts).-- The historically grown layout is:
 * FB[0] is unused.
 * FB[1] is not explicitly used but stands for -1.
 * FB[2] contains 2 (always).
 * Before we are called, the size_of_FB field in the handle will already have
 * been adjusted by _k->omega_k, so there's room for the primes dividing k,
 * which when present will occupy FB[3] and following.
 * The "real" odd FB primes begin at FB[h->index0_FB].
 * FB[size_of_FB+1] is the last prime p_i.
 * FB[size_of_FB+2] is a sentinel to simplify some of our loops.
 * Thus we allocate size_of_FB+3 slots for FB.
 *
 * If a prime factor of N is found during the construction, it is returned
 * in f, otherwise f = 0. */

/* returns the FB array pointer for convenience */
static mpqs_FB_entry_t *
mpqs_create_FB(mpqs_handle_t *h, ulong *f)
{
  mpqs_FB_entry_t *FB = mpqs_FB_ctor(h);
  const pari_sp av = avma;
  mpqs_int32_t size = h->size_of_FB;
  long i;
  mpqs_uint32_t k = h->_k->k;
  forprime_t S;

  FB[2].fbe_p = 2;
  /* the fbe_logval and the fbe_sqrt_kN for 2 are never used */
  FB[2].fbe_flags = MPQS_FBE_CLEAR;
  (void)u_forprime_init(&S, 3, ULONG_MAX);

  /* the first loop executes h->_k->omega_k = 0, 1, or 2 times */
  for (i = 3; i < h->index0_FB; i++)
  {
    mpqs_uint32_t kp = (ulong)h->_k->kp[i-3];
    if (MPQS_DEBUGLEVEL >= 7) err_printf(",<%lu>", (ulong)kp);
    FB[i].fbe_p = kp;
    /* we *could* flag divisors of k here, but so far I see no need,
     * and no flags bit has been assigned for the purpose */
    FB[i].fbe_flags = MPQS_FBE_CLEAR;
    FB[i].fbe_flogp = (float) log2((double) kp);
    FB[i].fbe_sqrt_kN = 0;
  }
  /* now i == h->index0_FB */
  while (i < size + 2)
  {
    ulong p = u_forprime_next(&S);
    if (p > k || k % p)
    {
      ulong kN_mod_p = umodiu(h->kN, p);
      long kr = krouu(kN_mod_p, p);
      if (kr != -1)
      {
        if (kr == 0) { *f = p; return FB; }
        FB[i].fbe_p = (mpqs_uint32_t) p;
        FB[i].fbe_flags = MPQS_FBE_CLEAR;
        /* dyadic logarithm of p; single precision suffices */
        FB[i].fbe_flogp = (float) log2((double)p);
        /* cannot yet fill in fbe_logval because the scaling multiplier
         * depends on the largest prime in FB, as yet unknown */

        /* x such that x^2 = kN (mod p_i) */
        FB[i++].fbe_sqrt_kN = (mpqs_uint32_t)Fl_sqrt(kN_mod_p, p);
      }
    }
  }
  set_avma(av);
  if (MPQS_DEBUGLEVEL >= 7)
  {
    err_printf("MPQS: FB [-1,2");
    for (i = 3; i < h->index0_FB; i++) err_printf(",<%lu>", FB[i].fbe_p);
    for (; i < size + 2; i++) err_printf(",%lu", FB[i].fbe_p);
    err_printf("]\n");
  }

  FB[i].fbe_p = 0;              /* sentinel */
  h->largest_FB_p = FB[i-1].fbe_p; /* at subscript size_of_FB + 1 */

  /* locate the smallest prime that will be used for sieving */
  for (i = h->index0_FB; FB[i].fbe_p != 0; i++)
    if (FB[i].fbe_p >= h->pmin_index1) break;
  h->index1_FB = i;
  /* with our parameters this will never fall of the end of the FB */
  *f = 0; return FB;
}

/*********************************************************************/
/**                                                                 **/
/**                      MISC HELPER FUNCTIONS                      **/
/**                                                                 **/
/*********************************************************************/

/* Effect of the following:  multiplying the base-2 logarithm of some
 * quantity by log_multiplier will rescale something of size
 *    log2 ( sqrt(kN) * M / (largest_FB_prime)^tolerance )
 * to 232.  Note that sqrt(kN) * M is just A*M^2, the value our polynomials
 * take at the outer edges of the sieve interval.  The scale here leaves
 * a little wiggle room for accumulated rounding errors from the approximate
 * byte-sized scaled logarithms for the factor base primes which we add up
 * in the sieving phase.-- The threshold is then chosen so that a point in
 * the sieve has to reach a result which, under the same scaling, represents
 *    log2 ( sqrt(kN) * M / (largest_FB_prime)^tolerance )
 * in order to be accepted as a candidate. */
/* The old formula was...
 *   log_multiplier =
 *      127.0 / (0.5 * log2 (handle->dkN)
 *               + log2((double)M)
 *               - tolerance * log2((double)handle->largest_FB_p)
 *               );
 * and we used to use this with a constant threshold of 128. */

/* NOTE: We used to divide log_multiplier by an extra factor 2, and in
 * compensation we were multiplying by 2 when the fbe_logp fields were being
 * filled in, making all those bytes even.  Tradeoff: the extra bit of
 * precision is helpful, but interferes with a possible sieving optimization
 * (artifically shift right the logp's of primes in A, and just run over both
 * arithmetical progressions  (which coincide in this case)  instead of
 * skipping the second one, to avoid the conditional branch in the
 * mpqs_sieve() loops).  We could still do this, but might lose a little bit
 * accuracy for those primes.  Probably no big deal. */
static void
mpqs_set_sieve_threshold(mpqs_handle_t *h)
{
  mpqs_FB_entry_t *FB = h->FB;
  long i;
  double log_maxval;
  double log_multiplier;

  h->l2sqrtkN = 0.5 * log2(h->dkN);
  h->l2M = log2((double)h->M);
  log_maxval = h->l2sqrtkN + h->l2M - MPQS_A_FUDGE;
  log_multiplier = 232.0 / log_maxval;
  h->sieve_threshold =
    (unsigned char) (log_multiplier *
                     (log_maxval
                      - h->tolerance * log2((double)h->largest_FB_p)
                      )
                     ) + 1;
  /* That "+ 1" really helps - we may want to tune towards somewhat smaller
   * tolerances  (or introduce self-tuning one day)... */

  /* If this turns out to be <128, scream loudly.
   * That means that the FB or the tolerance or both are way too
   * large for the size of kN.  (Normally, the threshold should end
   * up in the 150...170 range.) */
  if (h->sieve_threshold < 128) {
    h->sieve_threshold = 128;
    pari_warn(warner,
        "MPQS: sizing out of tune, FB size or tolerance\n\ttoo large");
  }

  /* Now fill in the byte-sized approximate scaled logarithms of p_i */
  if (DEBUGLEVEL >= 5)
  {
    err_printf("MPQS: computing logarithm approximations for p_i in FB\n");
  }
  for (i = h->index0_FB; i < h->size_of_FB + 2; i++)
  {
    FB[i].fbe_logval =
      (unsigned char) (log_multiplier * FB[i].fbe_flogp);
  }
}

/* Given the partially populated handle, find the optimum place in the FB
 * to pick prime factors for A from.  The lowest admissible subscript is
 * index0_FB, but unless kN is very small, we stay away a bit from that.
 * The highest admissible is size_of_FB + 1, where the largest FB prime
 * resides.  The ideal corner is about (sqrt(kN)/M) ^ (1/omega_A),
 * so that A will end up of size comparable to sqrt(kN)/M;  experimentally
 * it seems desirable to stay slightly below this.  Moreover, the selection
 * of the individual primes happens to err on the large side, for which we
 * compensate a bit, using the (small positive) quantity MPQS_A_FUDGE.
 * We rely on a few auxiliary fields in the handle to be already set by
 * mqps_set_sieve_threshold() before we are called.
 * Return 1 on success, and 0 otherwise. */
static int
mpqs_locate_A_range(mpqs_handle_t *h)
{
  /* i will be counted up to the desirable index2_FB + 1, and omega_A is never
   * less than 3, and we want
   *   index2_FB - (omega_A - 1) + 1 >= index0_FB + omega_A - 3,
   * so: */
  long i = h->index0_FB + 2*(h->omega_A) - 4;
  double l2_target_pA;
  mpqs_FB_entry_t *FB = h->FB;

  h->l2_target_A = (h->l2sqrtkN - h->l2M - MPQS_A_FUDGE);
  l2_target_pA = h->l2_target_A / h->omega_A;

  /* find the sweet spot, normally shouldn't take long */
  while ((FB[i].fbe_p != 0) && (FB[i].fbe_flogp <= l2_target_pA)) i++;

#ifdef MPQS_DEBUG_LOCATE_A_RANGE
  err_printf("MPQS DEBUG: omega_A=%ld, index0=%ld, i=%ld\n",
             (long) h->omega_A, (long) h->index0_FB, i);
#endif

  /* check whether this hasn't walked off the top end... */
  /* The following should actually NEVER happen. */
  if (i > h->size_of_FB - 3)
  { /* this isn't going to work at all. */
    pari_warn(warner,
        "MPQS: sizing out of tune, FB too small or\n\tway too few primes in A");
    return 0;
  }
  h->index2_FB = i - 1;
#ifdef MPQS_DEBUG_LOCATE_A_RANGE
  err_printf("MPQS DEBUG: index2_FB = %ld\n", i - 1);
#endif
  /* GN20050723
   * assert: index0_FB + (omega_A - 3) [the lowest FB subscript eligible to
   * be used in picking primes for A]  plus  (omega_A - 2)  does not exceed
   * index2_FB  [the subscript from which the choice of primes for A starts,
   * putting omega_A - 1 of them at or below index2_FB, and the last and
   * largest one above, cf. mpqs_si_choose_primes() below].
   * Moreover, index2_FB indicates the last prime below the ideal size, unless
   * (when kN is very small) the ideal size was too small to use. */

  return 1;
}

/*********************************************************************/
/**                                                                 **/
/**                       SELF-INITIALIZATION                       **/
/**                                                                 **/
/*********************************************************************/

#ifdef MPQS_DEBUG
/* Debug-only helper routine: check correctness of the root z mod p_i
 * by evaluting A * z^2 + B * z + C mod p_i  (which should be 0).
 * C is written as (B*B-kN)/(4*A) */
static void
check_root(mpqs_handle_t *h, long p, long start)
{
  long z = start - ((long)(h->M) % p);
  if (smodis(addii(h->C, mulsi(z, addii(h->B, mulsi(z, h->A)))), p))
  {
    err_printf("MPQS: p = %ld\n", p);
    err_printf("MPQS: A = %Ps\n", h->A);
    err_printf("MPQS: B = %Ps\n", h->B);
    err_printf("MPQS: C = %Ps\n", h->C);
    err_printf("MPQS: z = %ld\n", z);
    pari_err_BUG("MPQS: self_init: found wrong polynomial");
  }
}
#endif

/* There are four parts to self-initialization, which are exercised at
 * somewhat different times:
 * - choosing a new coefficient A  (selecting the prime factors to go into it,
 *   and doing the required bookkeeping in the FB entries, including clearing
 *   out the flags from the previous cohort), together with:
 * - doing the actual computations attached to a new A
 * - choosing a new B keeping the same A (very much simpler and quicker)
 * - and a small common bit that needs to happen in both cases.
 * As to the first item, the new scheme works as follows:
 * We pick omega_A - 1 prime factors for A below the index2_FB point which
 * marks their ideal size, and one prime above this point, choosing the
 * latter so as to get log2(A) as close as possible to l2_target_A.
 * The lower prime factors are chosen using bit patterns of constant weight,
 * gradually moving away from index2_FB towards smaller FB subscripts.
 * If this bumps into index0_FB  (might happen for very small input),  we
 * back up by increasing index2_FB by two, and from then on choosing only
 * bit patterns with either or both of their bottom bits set, so at least
 * one of the omega_A - 1 smaller prime factor will be beyond the original
 * index2_FB point.  In this way we avoid re-using A's which had already
 * been done.
 * (The choice of the upper "flyer" prime is of course constrained by the
 * size of the FB, which normally should never be anywhere close to becoming
 * a problem.  In unfortunate cases, e.g. for very small kN, we might have
 * to live with a rather non-optimal choice.
 * Then again, MPQS as such is surprisingly robust.  One day, I had got the
 * order of entries in mpqs_parameterset_t mixed up, and was running on a
 * smallish N with a huuuuge factor base and extremely tiny sieve interval,
 * and it still managed to factor it fairly quickly...)
 *
 * Mathematically, there isn't much more to this than the usual formula for
 * solving a quadratic  (over the field of p elements for each prime p in
 * the FB which doesn't divide A),  solving a linear equation for each of
 * the primes which do divide A, and precomputing differences between roots
 * mod p so we can adjust the roots quickly when we change B.
 * See Thomas Sosnowski's diploma thesis.
 */

/* Helper function:
 * Increment *x (!=0) to a larger value which has the same number of 1s in its
 * binary representation.  Wraparound can be detected by the caller as long as
 * we keep total_no_of_primes_for_A strictly less than BITS_IN_LONG.
 *
 * Changed switch to increment *x in all cases to the next larger number
 * which (a) has the same count of 1 bits and (b) does not arise from the
 * old value by moving a single 1 bit one position to the left  (which was
 * undesirable for the sieve). --GN based on discussion with TP */
INLINE void
mpqs_increment(mpqs_uint32_t *x)
{
  mpqs_uint32_t r1_mask, r01_mask, slider=1UL;

  /* 32-way computed jump handles 22 out of 32 cases */
  switch (*x & 0x1F)
  {
  case 29:
    (*x)++; break; /* shifts a single bit, but we postprocess this case */
  case 26:
    (*x) += 2; break; /* again */
  case 1: case 3: case 6: case 9: case 11:
  case 17: case 19: case 22: case 25: case 27:
    (*x) += 3; return;
  case 20:
    (*x) += 4; break; /* again */
  case 5: case 12: case 14: case 21:
    (*x) += 5; return;
  case 2: case 7: case 13: case 18: case 23:
    (*x) += 6; return;
  case 10:
    (*x) += 7; return;
  case 8:
    (*x) += 8; break; /* and again */
  case 4: case 15:
    (*x) += 12; return;
  default: /* 0, 16, 24, 28, 30, 31 */
    /* isolate rightmost 1 */
    r1_mask = ((*x ^ (*x - 1)) + 1) >> 1;
    /* isolate rightmost 1 which has a 0 to its left */
    r01_mask = ((*x ^ (*x + r1_mask)) + r1_mask) >> 2;
    /* simple cases.  Both of these shift a single bit one position to the
       left, and will need postprocessing */
    if (r1_mask == r01_mask) { *x += r1_mask; break; }
    if (r1_mask == 1) { *x += r01_mask; break; }
    /* general case -- idea: add r01_mask, kill off as many 1 bits as possible
     * to its right while at the same time filling in 1 bits from the LSB. */
    if (r1_mask == 2) { *x += (r01_mask>>1) + 1; return; }
    while (r01_mask > r1_mask && slider < r1_mask)
    {
      r01_mask >>= 1; slider <<= 1;
    }
    *x += r01_mask + slider - 1;
    return;
  }
  /* post-process all cases which couldn't be finalized above.  If we get
     here, slider still has its original value. */
  r1_mask = ((*x ^ (*x - 1)) + 1) >> 1;
  r01_mask = ((*x ^ (*x + r1_mask)) + r1_mask) >> 2;
  if (r1_mask == r01_mask) { *x += r1_mask; return; }
  if (r1_mask == 1) { *x += r01_mask; return; }
  if (r1_mask == 2) { *x += (r01_mask>>1) + 1; return; }
  while (r01_mask > r1_mask && slider < r1_mask)
  {
    r01_mask >>= 1; slider <<= 1;
  }
  *x += r01_mask + slider - 1;
  return;
}

/* self-init (1): advancing the bit pattern, and choice of primes for A.
 * The first time this is called, it finds h->bin_index == 0, which tells us
 * to initialize things from scratch.  On later occasions, we need to begin
 * by clearing the MPQS_FBE_DIVIDES_A bit in the fbe_flags of the former
 * prime factors of A.  We use, of course, the per_A_pr array for finding
 * them.  Upon successful return, that array will have been filled in, and
 * the flag bits will have been turned on again in the right places.
 * We return 1 (true) when we could set things up successfully, and 0 when
 * we found we'd be using more bits to the left in bin_index than we have
 * matching primes for in the FB.  In the latter case, bin_index will be
 * zeroed out, index2_FB will be incremented by 2, index2_moved will be
 * turned on, and the caller, after checking that index2_FB has not become
 * too large, should just call us again, which then is guaranteed to succeed:
 * we'll start again with a right-justified sequence of 1 bits in bin_index,
 * now interpreted as selecting primes relative to the new index2_FB. */
#ifndef MPQS_DEBUG_SI_CHOOSE_PRIMES
#  define MPQS_DEBUG_SI_CHOOSE_PRIMES 0
#endif
INLINE int
mpqs_si_choose_primes(mpqs_handle_t *h)
{
  mpqs_FB_entry_t *FB = h->FB;
  mpqs_per_A_prime_t *per_A_pr = h->per_A_pr;
  double l2_last_p = h->l2_target_A;
  mpqs_int32_t omega_A = h->omega_A;
  int i, j, v2, prev_last_p_idx;
  int room = h->index2_FB - h->index0_FB - omega_A + 4;
  /* GN 20050723:  I.e., index2_FB minus (index0_FB + omega_A - 3) plus 1
   * The notion of room here (cf mpqs_locate_A_range() above) is the number
   * of primes at or below index2_FB which are eligible for A.
   * At the very least, we need omega_A - 1 of them, and it is guaranteed
   * by mpqs_locate_A_range() that at least this many are available when we
   * first get here.  The logic here ensures that the lowest FB slot used
   * for A is never less than index0_FB + omega_A - 3.  In other words, when
   * omega_A == 3 (very small kN), we allow ourselves to reach all the way
   * down to index0_FB;  otherwise, we keep away from it by at least one
   * position.  For omega_A >= 4 this avoids situations where the selection
   * of the smaller primes here has advanced to a lot of very small ones, and
   * the single last larger one has soared away to bump into the top end of
   * the FB. */
  mpqs_uint32_t room_mask;
  mpqs_int32_t p;
  ulong bits;

  /* XXX also clear the index_j field here? */
  if (h->bin_index == 0)
  { /* first time here, or after increasing index2_FB, initialize to a pattern
     * of omega_A - 1 consecutive right-justified 1 bits.
     * Caller will have ensured that there are enough primes for this in the
     * FB below index2_FB. */
    h->bin_index = (1UL << (omega_A - 1)) - 1;
    prev_last_p_idx = 0;
  }
  else
  { /* clear out the old flags */
    for (i = 0; i < omega_A; i++)
      MPQS_FLG(i) &= ~MPQS_FBE_DIVIDES_A;
    prev_last_p_idx = MPQS_I(omega_A-1);

    /* find out how much maneuvering room we have before we're up against
     * the index0_FB wall */
    if (room > 30) room = 30;
    room_mask = ~((1UL << room) - 1);

    /* bump bin_index to the next acceptable value.  If index2_moved is off,
     * call mpqs_increment() just once;  otherwise, repeat until there's
     * something in the least significant 2 bits - this to ensure that we
     * never re-use an A which we'd used before increasing index2_FB - but
     * also stop if something shows up in the forbidden bits on the left
     * where we'd run out of bits or out of subscripts  (i.e. walk beyond
     * index0_FB + omega_A - 3). */
    mpqs_increment(&h->bin_index);
    if (h->index2_moved)
    {
      while ((h->bin_index & (room_mask | 0x3)) == 0)
        mpqs_increment(&h->bin_index);
    }
    /* ok so did we fall off the edge on the left? */
    if ((h->bin_index & room_mask) != 0)
    {
      /* Yes.  Turn on the index2_moved flag in the handle */
      h->index2_FB += 2;        /* caller to check this isn't too large!!! */
      h->index2_moved = 1;
      h->bin_index = 0;
      if (MPQS_DEBUG_SI_CHOOSE_PRIMES || (MPQS_DEBUGLEVEL >= 5))
        err_printf("MPQS: wrapping, more primes for A now chosen near FB[%ld] = %ld\n",
                   (long)h->index2_FB,
                   (long)FB[h->index2_FB].fbe_p);
      return 0;                 /* back off - caller should retry */
    }
  }
  /* assert: we aren't occupying any of the room_mask bits now, and if
   * index2_moved had already been on, at least one of the two LSBs is on */
  bits = h->bin_index;
  if (MPQS_DEBUG_SI_CHOOSE_PRIMES || (MPQS_DEBUGLEVEL >= 6))
    err_printf("MPQS: new bit pattern for primes for A: 0x%lX\n", bits);

  /* map bits to FB subscripts, counting downward with bit 0 corresponding
   * to index2_FB, and accumulate logarithms against l2_last_p */
  j = h->index2_FB;
  v2 = vals((long)bits);
  if (v2) { j -= v2; bits >>= v2; }
  for (i = omega_A - 2; i >= 0; i--)
  {
    MPQS_I(i) = j;
    l2_last_p -= MPQS_LP(i);
    MPQS_FLG(i) |= MPQS_FBE_DIVIDES_A;
    bits &= ~1UL;
    if (!bits) break;           /* that was the i=0 iteration */
    v2 = vals((long)bits);
    j -= v2;
    bits >>= v2;
  }
  /* Choose the larger prime.  Note we keep index2_FB <= size_of_FB - 3 */
  for (j = h->index2_FB + 1; (p = FB[j].fbe_p) != 0; j++)
    if (FB[j].fbe_flogp > l2_last_p) break;
  /* GN 20050724: The following trick avoids generating a relatively large
   * proportion of duplicate relations when the last prime happens to fall
   * into an area where there are large gaps from one FB prime to the next,
   * and would otherwise often be repeated  (so that successive A's would
   * wind up too similar to each other).  While this trick isn't perfect,
   * it seems to get rid of a major part of the potential duplication. */
  if (p != 0 && j == prev_last_p_idx) { j++; p = FB[j].fbe_p; }
  MPQS_I(omega_A - 1) = (p == 0 ? /* did we fall off the end of the FB? */
                         h->size_of_FB + 1 : /* then improvise */
                         j);
  MPQS_FLG(omega_A - 1) |= MPQS_FBE_DIVIDES_A;

  if (MPQS_DEBUG_SI_CHOOSE_PRIMES || (MPQS_DEBUGLEVEL >= 6))
  {
    err_printf("MPQS: chose primes for A");
    for (i = 0; i < omega_A; i++)
      err_printf(" FB[%ld]=%ld%s", (long) MPQS_I(i), (long) MPQS_AP(i),
                 i < omega_A - 1 ? "," : "\n");
  }
  return 1;
}

/* compute coefficients of the sieving polynomial for self initializing
 * variant. Coefficients A and B are returned and several tables are
 * updated. A and B are kept on the PARI stack in preallocated GENs; so is C
 * when MPQS_DEBUG */
static void
mpqs_self_init(mpqs_handle_t *h)
{
  const ulong size_of_FB = h->size_of_FB + 1;
  mpqs_FB_entry_t *FB = h->FB;
  mpqs_inv_A_H_t *inv_A_H = h->inv_A_H;
  const pari_sp av = avma;
  GEN p1, p2;
  GEN A = h->A;
  GEN B = h->B;
  mpqs_per_A_prime_t *per_A_pr = h->per_A_pr;
  long i, j;
  long inv_A2;
  ulong p;

#ifdef MPQS_DEBUG_AVMA
  err_printf("MPQS DEBUG: enter self init, avma = 0x%lX\n", (ulong)avma);
#endif

  /* when all of the B's have already been used, choose new A ;
     this is indicated by setting index_j to 0 */
  if (++h->index_j == (mpqs_uint32_t)h->no_B)
  {
    h->index_j = 0;
    h->index_i++; /* count finished A's */
  }

  if (h->index_j == 0)
  /* "mpqs_self_init_A()" */
  { /* compute first polynomial with new A */
    if (!mpqs_si_choose_primes(h))
    {
      /* We ran out of room towards small primes, and index2_FB was raised.
       * Check that we're still ok in that direction before re-trying the
       * operation, which then is guaranteed to succeed. The invariant we
       * maintain towards the top end is that h->size_of_FB - h->index2_FB >= 3,
       * but note that our size_of_FB is one larger. */

      /* "throw exception up to caller." ( bin_index set to impossible value
       * 0 by mpqs_si_choose_primes() */
      if (size_of_FB - h->index2_FB < 4) return;
      (void) mpqs_si_choose_primes(h);
    }
    /* assert: bin_index and per_A_pr are now populated with consistent
     * values */

    /* compute A = product of omega_A primes given by bin_index */
    p1 = NULL;
    for (i = 0; i < h->omega_A; i++)
    {
      p = (ulong) MPQS_AP(i);
      p1 = p1 ? muliu(p1, p): utoipos(p);
    }
    affii(p1, A); set_avma(av);

    /* Compute H[i], 0 <= i < omega_A.  Also compute the initial
     * B = sum(v_i*H[i]), by taking all v_i = +1 */
    /* TODO: following needs to be changed later for segmented FB and sieve
     * interval, where we'll want to precompute several B's. */
    p2 = NULL;
    for (i = 0; i < h->omega_A; i++)
    {
      p = (ulong) MPQS_AP(i);
      p1 = divis(A, (long)p);
      p1 = muliu(p1, Fl_inv(umodiu(p1, p), p));
      p1 = muliu(p1, MPQS_SQRT(i));
      affii(remii(p1, A), MPQS_H(i));
      p2 = p2 ? addii(p2, MPQS_H(i)) : MPQS_H(i);
    }
    affii(p2, B);
    set_avma(av);                  /* must happen outside the loop */

    /* ensure B = 1 mod 4 */
    if (mod2(B) == 0)
      affii(addii(B, mului(mod4(A), A)), B); /* B += (A % 4) * A; */

    p1 = shifti(A, 1);
    /* compute the roots z1, z2, of the polynomial Q(x) mod p_j and
     * initialize start1[i] with the first value p_i | Q(z1 + i p_j)
     * initialize start2[i] with the first value p_i | Q(z2 + i p_j)
     * The following loop "miraculously" does The Right Thing for the
     * primes dividing k (where sqrt_kN is 0 mod p).  Primes dividing A
     * are skipped here, and are handled further down in the common part
     * of SI. */
    for (j = 3; (ulong)j <= size_of_FB; j++)
    {
      ulong mb, tmp1, tmp2, m;
      if (FB[j].fbe_flags & MPQS_FBE_DIVIDES_A) continue;
      p = (ulong)FB[j].fbe_p; m = h->M % p;
      inv_A2 = Fl_inv(umodiu(p1, p), p); /* = 1/(2*A) mod p_j */
      mb = umodiu(B, p); if (mb) mb = p - mb;
      /* mb = -B mod p */
      tmp1 = Fl_sub(mb, FB[j].fbe_sqrt_kN, p);
      tmp1 = Fl_mul(tmp1, inv_A2, p);
      FB[j].fbe_start1 = (mpqs_int32_t)Fl_add(tmp1, m, p);

      tmp2 = Fl_add(mb, FB[j].fbe_sqrt_kN, p);
      tmp2 = Fl_mul(tmp2, inv_A2, p);
      FB[j].fbe_start2 = (mpqs_int32_t)Fl_add(tmp2, m, p);
      for (i = 0; i < h->omega_A - 1; i++)
      {
        ulong h = umodiu(MPQS_H(i), p) << 1; if (h > p) h -= p;
        MPQS_INV_A_H(i,j) = Fl_mul(h, inv_A2, p); /* 1/A * H[i] mod p_j */
      }
    }
  }
  else
  /* "mpqs_self_init_B()" */
  { /* no "real" computation -- use recursive formula */
    /* The following exploits that B is the sum of omega_A terms +-H[i].
     * Each time we switch to a new B, we choose a new pattern of signs;
     * the precomputation of the inv_A_H array allows us to change the
     * two arithmetic progressions equally fast.  The choice of sign
     * patterns does *not* follow the bit pattern of the ordinal number
     * of B in the current cohort;  rather, we use a Gray code, changing
     * only one sign each time.  When the i-th rightmost bit of the new
     * ordinal number index_j of B is 1, the sign of H[i] is changed;
     * the next bit to the left tells us whether we should be adding or
     * subtracting the difference term.  We never need to change the sign
     * of H[omega_A-1] (the topmost one), because that would just give us
     * the same sieve items Q(x) again with the opposite sign of x.  This
     * is why we only precomputed inv_A_H up to i = omega_A - 2. */

    ulong v2 = 0;               /* 2-valuation of h->index_j */

    j = h->index_j;
    /* could use vals() here, but we need to right shift the bit pattern
     * anyway in order to find out which inv_A_H entries must be added to or
     * subtracted from the modular roots */
    while ((j & 1) == 0) { v2++; j >>= 1; }

    /* v2 = v_2(index_j), determine new starting positions for sieving */
    p1 = shifti(MPQS_H(v2), 1);
    if (j & 2)
    { /* j = 3 mod 4 */
      for (j = 3; (ulong)j <= size_of_FB; j++)
      {
        if (FB[j].fbe_flags & MPQS_FBE_DIVIDES_A) continue;
        p = (ulong)FB[j].fbe_p;
        FB[j].fbe_start1 = Fl_sub(FB[j].fbe_start1, MPQS_INV_A_H(v2,j), p);
        FB[j].fbe_start2 = Fl_sub(FB[j].fbe_start2, MPQS_INV_A_H(v2,j), p);
      }
      p1 = addii(B, p1);
    }
    else
    { /* j = 1 mod 4 */
      for (j = 3; (ulong)j <= size_of_FB; j++)
      {
        if (FB[j].fbe_flags & MPQS_FBE_DIVIDES_A) continue;
        p = (ulong)FB[j].fbe_p;
        FB[j].fbe_start1 = Fl_add(FB[j].fbe_start1, MPQS_INV_A_H(v2,j), p);
        FB[j].fbe_start2 = Fl_add(FB[j].fbe_start2, MPQS_INV_A_H(v2,j), p);
      }
      p1 = subii(B, p1);
    }
    affii(p1, B);
  }
  set_avma(av);

  /* p=2 is a special case.  start1[2], start2[2] are never looked at,
   * so don't bother setting them. */

  /* now compute zeros of polynomials that have only one zero mod p
     because p divides the coefficient A */

  p1 = diviiexact(subii(h->kN, sqri(B)), shifti(A, 2)); /* coefficient -C */
  for (i = 0; i < h->omega_A; i++)
  {
    ulong tmp, s;
    p = (ulong) MPQS_AP(i);
    tmp = Fl_div(umodiu(p1, p), umodiu(B, p), p); s = (tmp + h->M) % p;
    FB[MPQS_I(i)].fbe_start1 = (mpqs_int32_t)s;
    FB[MPQS_I(i)].fbe_start2 = (mpqs_int32_t)s;
  }

  if (MPQS_DEBUGLEVEL >= 6)
    err_printf("MPQS: chose Q_%ld(x) = %Ps x^2 %c %Ps x + C\n",
               (long) h->index_j, h->A,
               signe(h->B) < 0? '-': '+', absi_shallow(h->B));

  set_avma(av);

#ifdef MPQS_DEBUG
  /* stash C into the handle.  Since check_root() is the only thing which
   * uses it, and only for debugging, C doesn't even exist as a field in
   * the handle unless we're built with MPQS_DEBUG. */
  affii(negi(p1), h->C);
  for (j = 3; j <= size_of_FB; j++)
  {
    check_root(h, FB[j].fbe_p, FB[j].fbe_start1);
    check_root(h, FB[j].fbe_p, FB[j].fbe_start2); set_avma(av);
  }
  if (DEBUGLEVEL >= 6)
    PRINT_IF_VERBOSE("MPQS: checking of roots of Q(x) was successful\n");
#endif

#ifdef MPQS_DEBUG_AVMA
  err_printf("MPQS DEBUG: leave self init, avma = 0x%lX\n", (ulong)avma);
#endif
}

/*********************************************************************/
/**                                                                 **/
/**                           THE SIEVE                             **/
/**                                                                 **/
/*********************************************************************/

/* Main sieving routine:
 * p4 = 4*p (used for loop unrolling)
 * log_p: approximation for log(p)
 * begin: points to a sieve array
 * end: points to the end of the sieve array
 * starting_sieving_index: marks the first FB element used for sieving */
INLINE void
mpqs_sieve_p(unsigned char *begin, unsigned char *end,
             long p4, long p, unsigned char log_p)
{
  register unsigned char *e = end - p4;
  /* Loop unrolled some time ago. It might be better to let the compiler worry
   * about *this* kind of optimization, based on its knowledge of whatever
   * useful tricks the machine instruction set architecture is offering
   * ("speculative loads" being the buzzword). --GN */
  while (e - begin >= 0) /* signed comparison */
  {
    (*begin) += log_p, begin += p;
    (*begin) += log_p, begin += p;
    (*begin) += log_p, begin += p;
    (*begin) += log_p, begin += p;
  }
  while (end - begin >= 0) /* again */
    (*begin) += log_p, begin += p;
}

static void
mpqs_sieve(mpqs_handle_t *h)
{
  long p, l = h->index1_FB;
  mpqs_FB_entry_t *ptr_FB;
  unsigned char *sieve_array = h->sieve_array;
  unsigned char *sieve_array_end = h->sieve_array_end;

  for (ptr_FB = &(h->FB[l]); (p = ptr_FB->fbe_p) != 0; ptr_FB++, l++)
  {
    unsigned char log_p = ptr_FB->fbe_logval;
    long start1 = ptr_FB->fbe_start1;
    long start2 = ptr_FB->fbe_start2;

    /* sieve with FB[l] from start_1[l] */
    /* if start1 != start2 sieve with FB[l] from start_2[l] */
    /* Maybe it is more efficient not to have a conditional branch in
     * the present loop body, and instead to right-shift log_p one bit
     * based on a flag bit telling us that we're on a one-root prime?
     * And instead roll the two invocations of mpqs_sieve_p into one. */
    mpqs_sieve_p(sieve_array + start1, sieve_array_end, p << 2, p, log_p);
    if (start1 != start2)
      mpqs_sieve_p(sieve_array + start2, sieve_array_end, p << 2, p, log_p);
  }
}

/******************************/

/* Could make shameless use of the fact that M is divisible by 4, but
 * let the compiler worry about loop unrolling.  Indeed I wonder whether
 * modern compilers woudln't have an easier time optimizing this if it
 * were written as array accesses.  Doing so. */
static long
mpqs_eval_sieve(mpqs_handle_t *h)
{
  long x = 0, count = 0, M_2 = h->M << 1;
  unsigned char th = h->sieve_threshold;
  unsigned char *sieve_array = h->sieve_array;
  long *candidates = h->candidates;

  /* The following variation on the original is marginally faster with a
   * good optimizing compiler.  Exploiting the sentinel, we don't need to
   * check for x < M_2 in the inner while loop - this more than makes up
   * for the "lack" of explicit unrolling.  Optimizations like loop
   * unrolling are best left to the compiler anyway... */
  while (count < MPQS_CANDIDATE_ARRAY_SIZE - 1)
  {
    while (sieve_array[x] < th) x++;
    if (x >= M_2) break;
    candidates[count++] = x++;
  }

  candidates[count] = 0; return count;
}

/*********************************************************************/
/**                                                                 **/
/**                     CONSTRUCTING RELATIONS                      **/
/**                                                                 **/
/*********************************************************************/

/* Main relation routine */
static void
mpqs_add_factor(GEN relp, long *i, ulong ei, ulong pi)
{
  ++*i;
  relp[*i]=pi | (ei<<REL_OFFSET);
}

/* only used for debugging */
static void
split_relp(GEN rel, GEN *pt_relp, GEN *pt_relc)
{
  long j, l = lg(rel);
  GEN relp = cgetg(l, t_VECSMALL);
  GEN relc = cgetg(l, t_VECSMALL);
  for (j=1; j<l; j++)
  {
    relc[j] = rel[j]>>REL_OFFSET;
    relp[j] = rel[j]&REL_MASK;
  }
  *pt_relp = relp;
  *pt_relc = relc;
}

#ifdef MPQS_DEBUG
static GEN
mpqs_factorback(mpqs_handle_t *h, GEN relp)
{
  GEN N = h->N, Q = gen_1;
  long j, l = lg(relp);
  for (j = 1; j < l; j++)
  {
    long e = relp[j]>>REL_OFFSET, i = relp[j]&REL_MASK;
    if (i == 1) Q = Fp_neg(Q,N); /* special case -1 */
    else Q = Fp_mul(Q, Fp_powu(utoipos(h->FB[i].fbe_p), e, N), N);
  }
  return Q;
}
static void
mpqs_check_rel(mpqs_handle_t *h, GEN c)
{
  pari_sp av = avma;
  int LP = (lg(c) == 4);
  GEN rhs = mpqs_factorback(h, rel_p(c));
  GEN Y = rel_Y(c), Qx_2 = remii(sqri(Y), h->N);
  if (LP) rhs = modii(mulii(rhs, rel_q(c)), h->N);
  if (!equalii(Qx_2, rhs))
  {
    GEN relpp, relpc;
    split_relp(rel_p(c), &relpp, &relpc);
    err_printf("MPQS: %Ps : %Ps %Ps\n", Y, relpp,relpc);
    err_printf("\tQx_2 = %Ps\n", Qx_2);
    err_printf("\t rhs = %Ps\n", rhs);
    pari_err_BUG(LP? "MPQS: wrong large prime relation found"
                   : "MPQS: wrong full relation found");
  }
  PRINT_IF_VERBOSE(LP? "\b(;)": "\b(:)");
  set_avma(av);
}
#endif

/* NB FREL, LPREL are actually FNEW, LPNEW when we get called */
static long
mpqs_eval_cand(mpqs_handle_t *h, long number_of_cand, GEN *FREL, GEN *LPREL)
{
  pari_sp av = avma;
  mpqs_FB_entry_t *FB = h->FB;
  GEN A = h->A, B = h->B, frel, lprel;
  long *relaprimes = h->relaprimes, *candidates = h->candidates;
  long nfrel = 1, nlprel = 1, number_of_relations = 0;
  ulong i, pi;
  int pii;

  frel = cgetg(DEFAULT_VEC_LEN, t_VEC);
  lprel = cgetg(DEFAULT_VEC_LEN, t_VEC);
  for (i = 0; i < (ulong)number_of_cand; i++)
  {
    pari_sp btop = avma;
    GEN Qx, Qx_part, Y, relp = cgetg(MAX_PE_PAIR+1,t_VECSMALL);
    long powers_of_2, p, x = candidates[i], nb = 0;
    int relaprpos = 0;

#ifdef MPQS_DEBUG_VERYVERBOSE
    err_printf("%c", (char)('0' + i%10));
#endif
    /* Y = |2*A*x + B|, Qx = Y^2/(4*A) = Q(x) */
    Y = absi_shallow( addii(mulis(A, 2 * (x - h->M)), B) );
    Qx = subii(sqri(Y), h->kN);

    /* When N is small, it may happen that N | Qx outright. In any case, when
     * no extensive prior trial division / Rho / ECM was attempted, gcd(Qx,N)
     * may turn out to be a nontrivial factor of N (not in FB or we'd have
     * found it already, but possibly smaller than the large prime bound). This
     * is too rare to check for here in the inner loop, but it will be caught
     * if such an LP relation is ever combined with another. */

    /* Qx cannot possibly vanish here */
    if (!signe(Qx)) { PRINT_IF_VERBOSE("<+>"); continue; }
    else if (signe(Qx) < 0) {
      setabssign(Qx);
      mpqs_add_factor(relp, &nb, 1, 1); /* i = 1, ei = 1, pi */
    }

    /* Qx > 0, divide by powers of 2; we're really dealing with 4*A*Q(x), so we
     * always have at least 2^2 here, and at least 2^3 when kN = 1 mod 4 */
    powers_of_2 = vali(Qx);
    Qx = shifti(Qx, -powers_of_2);
    mpqs_add_factor(relp, &nb, powers_of_2, 2); /* i = 1, ei = 1, pi */

    /* Pass 1 over odd primes in FB: pick up all possible divisors of Qx
     * including those sitting in k or in A, and remember them in relaprimes.
     * Do not yet worry about possible repeated factors, these will be found in
     * the Pass 2. Pass 1 recognizes divisors of A by their corresponding flags
     * bit in the FB entry. (Divisors of k are ignored at this stage.)
     * We construct a preliminary table of FB subscripts and "exponents" of FB
     * primes which divide Qx. (We store subscripts, not the primes themselves.)
     * We distinguish three cases:
     * 0) prime in A which does not divide Qx/A,
     * 1) prime not in A which divides Qx/A,
     * 2) prime in A which divides Qx/A.
     * Cases 1 and 2 need checking for repeated factors, kind 0 doesn't.
     * Cases 0 and 1 contribute 1 to the exponent in the relation, case 2
     * contributes 2.
     * Factors in common with k are simpler: if they occur, they occur
     * exactly to the first power, and this makes no difference in Pass 1,
     * so they behave just like every normal odd FB prime. */
    for (Qx_part = A, pi = 3; (p = FB[pi].fbe_p); pi++)
    {
      long xp = x % p;
      ulong ei = FB[pi].fbe_flags & MPQS_FBE_DIVIDES_A;
      /* Here we used that MPQS_FBE_DIVIDES_A = 1. */

      if (xp == FB[pi].fbe_start1 || xp == FB[pi].fbe_start2)
      { /* p divides Q(x)/A and possibly A, case 2 or 3 */
        relaprimes[relaprpos++] = pi;
        relaprimes[relaprpos++] = 1 + ei;
        Qx_part = muliu(Qx_part, p);
      }
      else if (ei)
      { /* p divides A but does not divide Q(x)/A, case 1 */
        relaprimes[relaprpos++] = pi;
        relaprimes[relaprpos++] = 0;
      }
    }
    /* We have accumulated the known factors of Qx except for possible repeated
     * factors and for possible large primes.  Divide off what we have.
     * This is faster than dividing off A and each prime separately. */
    Qx = diviiexact(Qx, Qx_part);

#ifdef MPQS_DEBUG_AVMA
    err_printf("MPQS DEBUG: eval loop 3, avma = 0x%lX\n", (ulong)avma);
#endif
    /* Pass 2: deal with repeated factors and store tentative relation. At this
     * point, the only primes which can occur again in the adjusted Qx are
     * those in relaprimes which are followed by 1 or 2. We must pick up those
     * followed by a 0, too. */
    PRINT_IF_VERBOSE("a");
    for (pii = 0; pii < relaprpos; pii += 2)
    {
      ulong r, ei = relaprimes[pii+1];
      GEN q;

      pi = relaprimes[pii];
      /* p | k (identified by its index before index0_FB)* or p | A (ei = 0) */
      if ((mpqs_int32_t)pi < h->index0_FB || ei == 0)
      {
        mpqs_add_factor(relp, &nb, 1, pi);
        continue;
      }
      p = FB[pi].fbe_p;
      /* p might still divide the current adjusted Qx. Try it. */
      switch(cmpiu(Qx, p))
      {
        case 0: ei++; Qx = gen_1; break;
        case 1:
          q = absdiviu_rem(Qx, p, &r);
          while (r == 0) { ei++; Qx = q; q = absdiviu_rem(Qx, p, &r); }
          break;
      }
      mpqs_add_factor(relp, &nb, ei, pi);
    }

#ifdef MPQS_DEBUG_AVMA
    err_printf("MPQS DEBUG: eval loop 4, avma = 0x%lX\n", (ulong)avma);
#endif
    PRINT_IF_VERBOSE("\bb");
    setlg(relp, nb+1);
    if (is_pm1(Qx))
    {
      GEN rel = gerepilecopy(btop, mkvec2(Y, relp));
      frel = vec_extend(frel, rel, nfrel++);
      number_of_relations++;
#ifdef MPQS_DEBUG
      mpqs_check_rel(h, rel);
#endif
    }
    else if (cmpiu(Qx, h->lp_bound) > 0)
    { /* TODO: check for double large prime */
      PRINT_IF_VERBOSE("\b.");
      set_avma(btop);
    }
    else
    {
      GEN rel = gerepilecopy(btop, mkvec3(Y,relp,Qx));
      lprel = vec_extend(lprel, rel, nlprel++);
#ifdef MPQS_DEBUG
      mpqs_check_rel(h, rel);
#endif
    }

  } /* for */
  PRINT_IF_VERBOSE("\n");
  if (nfrel==1) frel=NULL;   else setlg(frel, nfrel);
  if (nlprel==1) lprel=NULL; else setlg(lprel, nlprel);
  *FREL = frel; *LPREL = lprel;
  if (!frel && !lprel) { set_avma(av); return 0; }
  if (!frel) *LPREL = gerepilecopy(av, lprel);
  else gerepileall(av, lprel ? 2: 1, FREL, LPREL);
  return number_of_relations;
}

/*********************************************************************/
/**                                                                 **/
/**                      COMBINING RELATIONS                        **/
/**                                                                 **/
/*********************************************************************/
static void
rel_to_ei(GEN ei, GEN relp)
{
  long j, l = lg(relp);
  for (j=1; j<l; j++)
  {
    long e = relp[j]>>REL_OFFSET;
    long i = relp[j]&REL_MASK;
    ei[i] += e;
  }
}

static GEN
combine_large_primes(mpqs_handle_t *h, GEN rel1, GEN rel2)
{
  pari_sp av = avma;
  GEN new_Y, new_Y1, Y1 = rel_Y(rel1), Y2 = rel_Y(rel2);
  long l, lei = h->size_of_FB + 1, nb = 0;
  GEN ei, relp, inv_q, q = rel_q(rel1);

  if (!invmod(q, h->N, &inv_q)) /* can happen */
  {
    inv_q = gcdii(inv_q, h->N);
    if (is_pm1(inv_q) || equalii(inv_q, h->N)) /* pity */
    {
#ifdef MPQS_DEBUG
      err_printf("MPQS: skipping relation with non-invertible q\n");
#endif
      set_avma(av); return NULL;
    }
    return inv_q;
  }
  ei = zero_zv(lei);
  relp = cgetg(MAX_PE_PAIR+1,t_VECSMALL);

  rel_to_ei(ei, rel_p(rel1));
  rel_to_ei(ei, rel_p(rel2));
  new_Y = modii(mulii(mulii(Y1, Y2), inv_q), h->N);
  new_Y1 = subii(h->N, new_Y);
  if (abscmpii(new_Y1, new_Y) < 0) new_Y = new_Y1;
  if (odd(ei[1])) mpqs_add_factor(relp, &nb, 1, 1);
  for (l = 2; l <= lei; l++)
    if (ei[l]) mpqs_add_factor(relp, &nb, ei[l],l);
  setlg(relp, nb+1);
  if (DEBUGLEVEL >= 6)
  {
    GEN relpp, relpc, rel1p, rel1c, rel2p, rel2c;
    split_relp(relp,&relpp,&relpc);
    split_relp(rel1,&rel1p,&rel1c);
    split_relp(rel2,&rel2p,&rel2c);
    err_printf("MPQS: combining\n");
    err_printf("    {%Ps @ %Ps : %Ps}\n", q, Y1, rel1p, rel1c);
    err_printf("  * {%Ps @ %Ps : %Ps}\n", q, Y2, rel2p, rel2c);
    err_printf(" == {%Ps, %Ps}\n", relpp, relpc);
  }
#ifdef MPQS_DEBUG
  {
    pari_sp av1 = avma;
    if (!equalii(modii(sqri(new_Y), h->N), mpqs_factorback(h, relp)))
      pari_err_BUG("MPQS: combined large prime relation is false");
    set_avma(av1);
  }
#endif
  return gerepilecopy(av, mkvec2(new_Y, relp));
}

static GEN
mpqs_combine_large_primes(mpqs_handle_t *h, hashtable *lprel, GEN LPNEW, hashtable *frel)
{
  long j, lpnew = lg(LPNEW);
  for (j = 1; j < lpnew; j++)
  {
    GEN rel = gel(LPNEW,j);
    ulong q = itou(rel_q(rel));
    GEN f, col = hash_haskey_GEN(lprel, (void*)q);
    if (!col)
      hash_insert(lprel, (void*)q, (void*)rel);
    else if ((f = combine_large_primes(h, rel, col)))
    {
      if (typ(f) == t_INT) return f;
      frel_add(frel, f);
    }
  }
  return NULL;
}

/*********************************************************************/
/**                                                                 **/
/**                    FROM RELATIONS TO DIVISORS                   **/
/**                                                                 **/
/*********************************************************************/

/* create an F2m from a relations list; rows = size_of_FB+1 */
static GEN
stream_read_F2m(GEN rel, long rows)
{
  long i, cols = lg(rel)-1;
  GEN m;
  long space = 2*((nbits2nlong(rows)+3)*cols+1);
  if ((long)((GEN)avma - (GEN)pari_mainstack->bot) < space)
  {
    pari_sp av = avma;
    m = gclone(zero_F2m(rows, cols));
    if (DEBUGLEVEL>=4)
      err_printf("MPQS: allocating %ld words for Gauss\n",space);
    set_avma(av);
  }
  else
    m = zero_F2m_copy(rows, cols);
  for (i = 1; i <= cols; i++)
  {
    GEN relp = gmael(rel,i,2);
    long j, l = lg(relp);
    for (j = 1; j < l; j++)
      if (odd(relp[j]>>REL_OFFSET)) F2m_set(m, relp[j]&REL_MASK, i);
  }
  return m;
}

static GEN
mpqs_add_relation(GEN Y_prod, GEN N, GEN ei, GEN r)
{
  pari_sp av = avma;
  GEN res = remii(mulii(Y_prod, gel(r,1)), N);
  rel_to_ei(ei, gel(r,2));
  return gerepileuptoint(av, res);
}

static int
split(GEN N, GEN *e, GEN *res)
{
  ulong mask;
  long flag;
  GEN base;
  if (MR_Jaeschke(N)) { *e = gen_1; return 1; } /* probable prime */
  if (Z_issquareall(N, &base))
  { /* squares could cost us a lot of time */
    if (DEBUGLEVEL >= 5) err_printf("MPQS: decomposed a square\n");
    *res = base; *e = gen_2; return 1;
  }
  mask = 7;
  /* 5th/7th powers aren't worth the trouble. OTOH once we have the hooks for
   * dealing with cubes, higher powers can be handled essentially for free) */
  if ((flag = is_357_power(N, &base, &mask)))
  {
    if (DEBUGLEVEL >= 5)
      err_printf("MPQS: decomposed a %s power\n", uordinal(flag));
    *res = base; *e = utoipos(flag); return 1;
  }
  *e = gen_0; return 0; /* known composite */
}

static GEN
mpqs_solve_linear_system(mpqs_handle_t *h, GEN frel)
{
  mpqs_FB_entry_t *FB = h->FB;
  pari_sp av = avma, av2;
  long i, j, H_cols, H_rows, res_last, res_next, res_size, res_max, done, rank;
  GEN N = h->N, X_plus_Y, D1, res, new_res, ei, m, ker_m;

  m = stream_read_F2m(frel, h->size_of_FB+1);
  if (DEBUGLEVEL >= 7)
    err_printf("\\\\ MATRIX READ BY MPQS\nFREL=%Ps\n",m);

  ker_m = F2m_ker_sp(m,0); rank = lg(ker_m)-1;
  clone_unlock(m);

  if (DEBUGLEVEL >= 4)
  {
    if (DEBUGLEVEL >= 7)
    {
      err_printf("\\\\ KERNEL COMPUTED BY MPQS\n");
      err_printf("KERNEL=%Ps\n",ker_m);
    }
    err_printf("MPQS: Gauss done: kernel has rank %ld, taking gcds...\n", rank);
  }

  H_rows = lg(m)-1;
  H_cols = rank;

  if (!H_cols)
  { /* trivial kernel. Fail gracefully: main loop may look for more relations */
    if (DEBUGLEVEL >= 3)
      pari_warn(warner, "MPQS: no solutions found from linear system solver");
    return gc_NULL(av); /* no factors found */
  }

  /* If the rank is r, we can expect up to 2^r pairwise coprime factors,
   * but it may happen that a kernel basis vector contributes nothing new to
   * the decomposition.  We allocate room for up to eight factors initially,
   * adjusting this as we go along. In the upper half of our vector, we store
   * information about which factors we know to be composite (zero) or believe
   * to be composite (NULL) or suspect to be prime (one), or an exponent
   * (t_INT >= 2) if it is a proper power */
  ei = cgetg(h->size_of_FB + 2, t_VECSMALL);
  av2 = avma;
  if (rank > (long)BITS_IN_LONG - 2)
    res_max = LONG_MAX; /* the common case, unfortunately */
  else
    res_max = 1L<<rank; /* max number of factors we can hope for */
  res_size = 8; /* no. of factors we can store in this res */
  res = const_vec(2*res_size, NULL);
  res_next = res_last = 1;

  for (i = 1; i <= H_cols; i++)
  { /* loop over kernel basis */
    GEN X = gen_1, Y_prod = gen_1;
    pari_sp av3;
    memset((void *)(ei+1), 0, (h->size_of_FB + 1) * sizeof(long));

    av3 = avma;
    for (j = 1; j <= H_rows; j++)
    {
      if (F2m_coeff(ker_m, j, i))
        Y_prod = mpqs_add_relation(Y_prod, N, ei, gel(frel,j));
      if (gc_needed(av3,1))
      {
        if(DEBUGMEM>1) pari_warn(warnmem,"[1]: mpqs_solve_linear_system");
        Y_prod = gerepileuptoint(av3, Y_prod);
      }
    }
    Y_prod = gerepileuptoint(av3, Y_prod);

    av3 = avma;
    for (j = 2; j <= h->size_of_FB + 1; j++)
      if (ei[j])
      {
        if (ei[j] & 1) pari_err_BUG("MPQS (relation is a nonsquare)");
        X = remii(mulii(X, Fp_powu(utoipos(FB[j].fbe_p), (ulong)ei[j]>>1, N)),
                  N);
        if (gc_needed(av3,1))
        {
          if(DEBUGMEM>1) pari_warn(warnmem,"[2]: mpqs_solve_linear_system");
          X = gerepileupto(av3, X);
        }
      }
    X = gerepileuptoint(av3, X);
    if (MPQS_DEBUGLEVEL >= 1)
    {
      if (!dvdii(subii(sqri(X), sqri(Y_prod)), N))
      { /* shouldn't happen */
        err_printf("MPQS: X^2 - Y^2 != 0 mod N\n");
        err_printf("\tindex i = %ld\n", i);
        pari_warn(warner, "MPQS: wrong relation found after Gauss");
      }
    }
    /* At this point, gcd(X-Y, N) * gcd(X+Y, N) = N:
     * 1) N | X^2 - Y^2, so it divides the LHS;
     * 2) let P be any prime factor of N. If P | X-Y and P | X+Y, then P | 2X
     * But X is a product of powers of FB primes => coprime to N.
     * Hence we work with gcd(X+Y, N) alone. */
    done = 0; /* # probably-prime factors (or powers whose bases we don't
                 want to handle any further) */
    X_plus_Y = addii(X, Y_prod);
    if (res_next < 3)
    { /* we still haven't decomposed, and want both a gcd and its cofactor. */
      D1 = gcdii(X_plus_Y, N);
      if (is_pm1(D1) || equalii(D1,N)) { set_avma(av3); continue; }
      /* got something that works */
      if (DEBUGLEVEL >= 5)
        err_printf("MPQS: splitting N after %ld kernel vector%s\n",
                   i+1, (i? "s" : ""));
      gel(res,1) = diviiexact(N, D1);
      gel(res,2) = D1;
      res_last = res_next = 3;

      if ( split(gel(res,1),  &gel(res,res_size+1), &gel(res,1)) ) done++;
      if ( split(D1, &gel(res,res_size+2), &gel(res,2)) ) done++;
      if (done == 2) break; /* both factors look prime or were powers */
      if (res_max == 2) break; /* two out of two possible factors seen */
      if (DEBUGLEVEL >= 5)
        err_printf("MPQS: got two factors, looking for more...\n");
    }
    else
    { /* we already have factors */
      for (j=1; j < res_next; j++)
      { /* loop over known-composite factors */
        if (gel(res,res_size+j) && gel(res,res_size+j) != gen_0)
        {
          done++; continue; /* skip probable primes etc */
        }
        /* actually, also skip square roots of squares etc.  They are a lot
         * smaller than the original N, and should be easy to deal with later */
        av3 = avma;
        D1 = gcdii(X_plus_Y, gel(res,j));
        if (is_pm1(D1) || equalii(D1, gel(res,j))) { set_avma(av3); continue; }
        /* got one which splits this factor */
        if (DEBUGLEVEL >= 5)
          err_printf("MPQS: resplitting a factor after %ld kernel vectors\n",
                     i+1);
        /* first make sure there's room for another factor */
        if (res_next > res_size)
        { /* need to reallocate (rare) */
          long t, s = minss(2*res_size, res_max);
          GEN RES = cgetg(2*s+1, t_VEC);
          for (t=2*s; t>=res_next; t--) gel(RES,t) = NULL;
          for (t=1; t<res_next; t++)
          { /* on-stack contents of RES must be rejuvenated */
            icopyifstack(gel(res,t), gel(RES,t)); /* factors */
            if (gel(res,res_size+t)) /* primality tags */
              icopyifstack(gel(res,res_size+t), gel(RES,s+t));
          }
          res = RES; res_size = s; /* res_next unchanged */
        }
        /* divide into existing factor and store the new gcd */
        diviiz(gel(res,j), D1, gel(res,j));
        gel(res,res_next) = D1;

        /* following overwrites the old known-composite indication at j */
        if (split( gel(res,j), &gel(res,res_size+j), &gel(res,j)) ) done++;
        /* Don't increment done when the newly stored factor seems to be
         * prime or otherwise devoid of interest - this happens later
         * when we revisit it during the present inner loop. */
        (void)split(D1, &gel(res,res_size+res_next), &gel(res,res_next));
        if (++res_next > res_max) break; /* all possible factors seen */
      } /* loop over known composite factors */

      if (res_next > res_last)
      {
        if (DEBUGLEVEL >= 5)
          err_printf("MPQS: got %ld factors%s\n", res_last - 1,
                     (done < res_last ? ", looking for more..." : ""));
        res_last = res_next;
      }
      /* break out of the outer loop if we have seen res_max factors, or
       * when all current factors are probable primes */
      if (res_next > res_max || done == res_next - 1) break;
    } /* end case of further splitting of existing factors */
    if (gc_needed(av2,1))
    {
      long t;
      if(DEBUGMEM>1) pari_warn(warnmem,"[3]: mpqs_solve_linear_system");
      /* gcopy would have a problem with our NULL pointers... */
      new_res = cgetg(lg(res), t_VEC);
      for (t=2*res_size; t>=res_next; t--) new_res[t] = 0;
      for (t=1; t<res_next; t++)
      {
        icopyifstack(gel(res,t), gel(new_res,t));
        if (gel(res,res_size+t))
          icopyifstack(gel(res,res_size+t), gel(new_res,res_size+t));
      }
      res = gerepileupto(av2, new_res);
    }
  } /* for (loop over kernel basis) */

  if (res_next < 3) return gc_NULL(av); /* no factors found */

  /* normal case:  convert internal format to ifac format as described in
   * basemath/ifactor1.c  (value, exponent, class [unknown, known composite,
   * known prime]) */
  res_last = res_next - 1; /* number of distinct factors found */
  new_res = cgetg(3*res_last + 1, t_VEC);
  if (DEBUGLEVEL >= 6)
    err_printf("MPQS: wrapping up vector of %ld factors\n", res_last);
  for (i=1,j=1; i <= res_last; i++)
  {
    GEN F = gel(res, res_size+i);
    icopyifstack(gel(res,i), gel(new_res,j++)); /* factor */
    /* exponent */
    gel(new_res,j++) = F ? (F == gen_0 ? gen_1
                                       : (isonstack(F) ? icopy(F) : F))
                         : gen_1;
    gel(new_res,j++) = F; /* class, known composite or unknown */
    if (DEBUGLEVEL >= 6)
      err_printf("\tpackaging %ld: %Ps ^%ld (%s)\n", i, res[i],
                 itos(gel(new_res,j-2)), (F == gen_0 ? "comp." : "unknown"));
  }
  return gerepileupto(av, new_res);
}

/*********************************************************************/
/**                                                                 **/
/**               MAIN ENTRY POINT AND DRIVER ROUTINE               **/
/**                                                                 **/
/*********************************************************************/
static void
toolarge()
{ pari_warn(warner, "MPQS: number too big to be factored with MPQS,\n\tgiving up"); }
/* All percentages below are actually fixed-point quantities scaled by 10
 * (value of 1 means 0.1%, 1000 means 100%) */

/* Factors N using the self-initializing multipolynomial quadratic sieve
 * (SIMPQS).  Returns one of the two factors, or (usually) a vector of factors
 * and exponents and information about which ones are still composite, or NULL
 * when something goes wrong or when we can't seem to make any headway. */
GEN
mpqs(GEN N)
{
  const long size_N = decimal_len(N);
  mpqs_handle_t H;
  GEN fact; /* will in the end hold our factor(s) */
  mpqs_FB_entry_t *FB; /* factor base */

  ulong p; /* auxiliary var */
  /* bookkeeping */
  long tc;              /* # of candidates found in one iteration */
  long tff = 0;         /* # recently found full rels from sieving */
  long tfc;             /* # full rels recently combined from LPs */
  double tfc_ratio = 0; /* recent (tfc + tff) / tff */
  ulong sort_interval;  /* determine when to sort and merge */
  long percentage = 0;  /* scaled by 10, see comment above */
  long total_partial_relations = 0, total_no_cand = 0;
  long good_iterations = 0, iterations = 0;

  pari_timer T;
  GEN fnew, vnew;
  long nvnew;
  hashtable lprel, frel;
  pari_sp av = avma;

  if (DEBUGLEVEL >= 4) err_printf("MPQS: number to factor N = %Ps\n", N);
  if (size_N > MPQS_MAX_DIGIT_SIZE_KN) { toolarge(); return NULL; }

  if (DEBUGLEVEL >= 4)
  {
    timer_start(&T);
    err_printf("MPQS: factoring number of %ld decimal digits\n", size_N);
  }

  H.N = N;
  H.bin_index = 0;
  H.index_i = 0;
  H.index_j = 0;
  H.index2_moved = 0;
  p = mpqs_find_k(&H);
  if (p) { set_avma(av); return utoipos(p); }
  if (DEBUGLEVEL >= 5) err_printf("MPQS: found multiplier %ld for N\n",
                                  H._k->k);
  H.kN = muliu(N, H._k->k);
  if (!mpqs_set_parameters(&H)) { toolarge(); return NULL; }

  sort_interval = H.first_sort_point;

  if (DEBUGLEVEL >= 5)
    err_printf("MPQS: creating factor base and allocating arrays...\n");
  FB = mpqs_create_FB(&H, &p);
  if (p) { set_avma(av); return utoipos(p); }
  mpqs_sieve_array_ctor(&H);
  mpqs_poly_ctor(&H);

  H.lp_bound = minss(H.largest_FB_p, MPQS_LP_BOUND);
  /* don't allow large primes to have room for two factors both bigger than
   * what the FB contains (...yet!) */
  H.lp_bound *= minss(H.lp_scale, H.largest_FB_p - 1);

  H.dkN = gtodouble(H.kN);
  /* compute the threshold and fill in the byte-sized scaled logarithms */
  mpqs_set_sieve_threshold(&H);

  if (!mpqs_locate_A_range(&H)) return NULL;

  if (DEBUGLEVEL >= 4)
  {
    err_printf("MPQS: sieving interval = [%ld, %ld]\n", -(long)H.M, (long)H.M);
    /* that was a little white lie, we stop one position short at the top */
    err_printf("MPQS: size of factor base = %ld\n",
               (long)H.size_of_FB);
    err_printf("MPQS: striving for %ld relations\n",
               (long)H.target_no_rels);
    err_printf("MPQS: coefficients A will be built from %ld primes each\n",
               (long)H.omega_A);
    err_printf("MPQS: primes for A to be chosen near FB[%ld] = %ld\n",
               (long)H.index2_FB,
               (long)FB[H.index2_FB].fbe_p);
    err_printf("MPQS: smallest prime used for sieving FB[%ld] = %ld\n",
               (long)H.index1_FB,
               (long)FB[H.index1_FB].fbe_p);
    err_printf("MPQS: largest prime in FB = %ld\n",
               (long)H.largest_FB_p);
    err_printf("MPQS: bound for `large primes' = %ld\n", (long)H.lp_bound);
  }

  if (DEBUGLEVEL >= 5)
    err_printf("MPQS: sieve threshold = %u\n",
               (unsigned int)H.sieve_threshold);

  if (DEBUGLEVEL >= 4)
    err_printf("MPQS: first sorting at %ld%%, then every %3.1f%% / %3.1f%%\n",
               sort_interval/10, H.sort_pt_interval/10.,
               H.sort_pt_interval/20.);

  /* main loop which
   * - computes polynomials and their zeros (SI)
   * - does the sieving
   * - tests candidates of the sieve array */

  /* Let (A, B_i) the current pair of coeffs. If i == 0 a new A is generated */
  H.index_j = (mpqs_uint32_t)-1;  /* increment below will have it start at 0 */

  if (DEBUGLEVEL >= 5) err_printf("MPQS: starting main loop\n");

  hash_init_GEN(&frel, H.target_no_rels, gequal, 1);
  hash_init_ulong(&lprel,H.target_no_rels, 1);
  vnew = cgetg((long)(sort_interval * (H.target_no_rels/1000.))+2, t_VEC);
  nvnew = 1;
  for(;;)
  {
    long i, fnb;
    iterations++;
    /* self initialization: compute polynomial and its zeros */
    mpqs_self_init(&H);
    if (H.bin_index == 0)
    { /* have run out of primes for A */
      /* We might change some parameters.  For the moment, simply give up */
      if (DEBUGLEVEL >= 2)
        err_printf("MPQS: Ran out of primes for A, giving up.\n");
      return gc_NULL(av);
    }

    memset((void*)(H.sieve_array), 0, (H.M << 1) * sizeof(unsigned char));
    mpqs_sieve(&H);

    tc = mpqs_eval_sieve(&H);
    total_no_cand += tc;
    if (DEBUGLEVEL >= 6)
      err_printf("MPQS: found %lu candidate%s\n", tc, (tc==1? "" : "s"));

    if (tc)
    {
      GEN lpnew;
      long t = mpqs_eval_cand(&H, tc, &fnew, &lpnew);
      tff += t;
      good_iterations++;
      if (fnew) vec_frel_add(&frel, fnew);
      if (lpnew) vnew = vec_extend(vnew, lpnew, nvnew++);
    }
    percentage = (long)((1000.0 * frel.nb) / H.target_no_rels);
    if ((ulong)percentage < sort_interval) continue;
    /* most main loops continue here! */

    /* Extra processing when we have completed a sort interval: */
    if (DEBUGLEVEL >= 3)
    {
      if (DEBUGLEVEL >= 4)
        err_printf("\nMPQS: passing the %3.1f%% sort point, time = %ld ms\n",
                   sort_interval/10., timer_delay(&T));
      else
        err_printf("\nMPQS: passing the %3.1f%% sort point\n",
                   sort_interval/10.);
    }

    /* combine whatever there is to be combined */
    tfc = 0;
    /* build full relations out of large prime relations */
    fnb = frel.nb;
    for (i=1; i<nvnew; i++)
    {
      GEN fact = mpqs_combine_large_primes(&H, &lprel, gel(vnew,i) , &frel);
      if (fact)
      { /* factor found during combining */
        if (DEBUGLEVEL >= 4)
        {
          err_printf("\nMPQS: split N whilst combining, time = %ld ms\n",
              timer_delay(&T));
          err_printf("MPQS: found factor = %Ps\n", fact);
        }
        return gerepileupto(av, fact);
      }
    }
    nvnew = 1;
    tfc = frel.nb - fnb;
    if (DEBUGLEVEL >= 4)
      err_printf("MPQS: combined %ld full relation%s\n", tfc, (tfc!=1 ? "s" : ""));
    total_partial_relations += tfc;

    percentage = (long)((1000.0 * frel.nb) / H.target_no_rels);
    /* Estimate the current full relations yield rate: we see each time through
     * the main loop how many full relations we're getting from the sieve
     * (tff since previous checkpoint), but only at checkpoints do we see how
     * many we're typically combining (tfc).  So we're producing (tfc+tff)/tff
     * as many full rels, and when we get close to 100%, we should bias the
     * next interval by the inverse ratio. Avoid drawing conclusions from
     * too-small samples during very short follow-on intervals (in this case
     * re-use an earlier estimated ratio). */
    if (tfc >= 16 && tff >= 20) tfc_ratio = (tfc + tff + 0.) / tff;
    tff = 0; /* reset this count (tfc is always fresh) */

    if (percentage >= 1000) /* when Gauss had failed */
      sort_interval = percentage + 2;
    else if (percentage >= 820)
    {
      if (tfc_ratio > 1.)
      {
        if (percentage + (H.sort_pt_interval>> 1) * tfc_ratio > 994)
          sort_interval = (ulong)(percentage + 2 +
            (1000 - percentage) / tfc_ratio); /* aim for a slight overshoot */
        else if (percentage >= 980)
          sort_interval = percentage + 8;
        else
          sort_interval = percentage + (H.sort_pt_interval >> 1);
      }
      else
      {
        if (percentage >= 980)
          sort_interval = percentage + 10;
        else
          sort_interval = percentage + (H.sort_pt_interval >> 1);
        if (sort_interval >= 1000 && percentage < 1000)
          sort_interval = 1000;
      }
    }
    else
      sort_interval = percentage + H.sort_pt_interval;

    if (DEBUGLEVEL >= 4)
    {
      err_printf("MPQS: done sorting and combining, time = %ld ms\n",
                 timer_delay(&T));
      err_printf("MPQS: found %3.1f%% of the required relations\n",
                 percentage/10.);
      if (DEBUGLEVEL >= 5)
      { /* GN20050708: present code doesn't succeed in discarding all dups,
         * so don't lie about it */
        err_printf("MPQS: found %ld full relations\n", frel.nb);
        if (H.lp_scale > 1)
          err_printf("MPQS:   (%ld of these from partial relations)\n",
                     total_partial_relations);
        err_printf("MPQS: Net yield: %4.3g full relations per 100 candidates\n",
                   (frel.nb * 100.) / (total_no_cand? total_no_cand: 1));
        err_printf("MPQS:            %4.3g full relations per 100 polynomials\n",
                   (frel.nb * 100.) / iterations);
        err_printf("MPQS: %4.1f%% of the polynomials yielded no candidates\n",
                   (100.0 * (iterations - good_iterations)) / iterations);
        err_printf("MPQS: next sort point at %3.1f%%\n", sort_interval/10.);
      }
    }
    if (percentage < 1000) continue; /* main loop */

    /* percentage >= 1000, hence frel.nb > size of FB: try finishing it off */
    if (DEBUGLEVEL >= 4)
      err_printf("\nMPQS: starting Gauss over F_2 on %ld distinct relations\n",
                 frel.nb);
    fact = mpqs_solve_linear_system(&H, hash_keys(&frel));
    if (fact)
    { /* solution found */
      if (DEBUGLEVEL >= 4)
      {
        err_printf("\nMPQS: time in Gauss and gcds = %ld ms\n", timer_delay(&T));
        if (typ(fact) == t_INT) err_printf("MPQS: found factor = %Ps\n", fact);
        else
        {
          long j, nf = (lg(fact)-1)/3;
          if (nf == 2)
            err_printf("MPQS: found factors = %Ps\n\tand %Ps\n",
                        fact[1], fact[4]);
          else
          {
            err_printf("MPQS: found %ld factors =\n", nf);
            for (j=1; j<=nf; j++)
              err_printf("\t%Ps%s\n", fact[3*j-2], (j<nf ? "," : ""));
          }
        }
      }
      /* fact not safe for a gerepilecopy(): segfaults on one of the NULL
       * markers. However, it is a nice connected object, and it resides
       * already the top of the stack, so... --GN */
      return gerepileupto(av, fact);
    }
    else
    {
      if (DEBUGLEVEL >= 4)
      {
        err_printf("\nMPQS: time in Gauss and gcds = %ld ms\n",timer_delay(&T));
        err_printf("MPQS: no factors found.\n");
        if (percentage <= MPQS_ADMIT_DEFEAT)
          err_printf("\nMPQS: restarting sieving ...\n");
        else
          err_printf("\nMPQS: giving up.\n");
      }
      if (percentage > MPQS_ADMIT_DEFEAT)
        return gc_NULL(av);
    }
  } /* main loop */
}
