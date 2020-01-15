/* Copyright (C) 2020  The PARI group.

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

/* if x a famat, assume it is a true unit (very costly to check even that
 * it's an algebraic integer) */
GEN
bnfisunit(GEN bnf, GEN x)
{
  long tx = typ(x), i, r1, RU, e, n, prec;
  pari_sp av = avma;
  GEN t, rlog, logunit, ex, nf, pi2_sur_w, rx, emb, arg;

  bnf = checkbnf(bnf); nf = bnf_get_nf(bnf);
  logunit = bnf_get_logfu(bnf); RU = lg(logunit);
  n = bnf_get_tuN(bnf); /* # { roots of 1 } */
  if (tx == t_MAT)
  { /* famat, assumed OK */
    if (lg(x) != 3) pari_err_TYPE("bnfisunit [not a factorization]", x);
  } else {
    x = nf_to_scalar_or_basis(nf,x);
    if (typ(x) != t_COL)
    { /* rational unit ? */
      GEN v;
      long s;
      if (typ(x) != t_INT || !is_pm1(x)) return cgetg(1,t_COL);
      s = signe(x); set_avma(av); v = zerocol(RU);
      gel(v,RU) = mkintmodu((s > 0)? 0: n>>1, n);
      return v;
    }
    if (!isint1(Q_denom(x))) { set_avma(av); return cgetg(1,t_COL); }
  }

  r1 = nf_get_r1(nf);
  rlog = real_i(logunit);
  prec = nf_get_prec(nf);
  for (i = 1;; i++)
  {
    rx = nflogembed(nf,x,&emb, MEDDEFAULTPREC);
    if (rx)
    {
      GEN logN = RgV_sum(rx); /* log(Nx), should be ~ 0 */
      if (gexpo(logN) > -20)
      { /* precision problem ? */
        if (typ(logN) != t_REAL) { set_avma(av); return cgetg(1,t_COL); } /*no*/
        if (i == 1 && typ(x) != t_MAT &&
            !is_pm1(nfnorm(nf, x))) { set_avma(av); return cgetg(1, t_COL); }
      }
      else
      {
        ex = RU == 1? cgetg(1,t_COL)
                    : RgM_solve(rlog, rx); /* ~ fundamental units exponents */
        if (ex) { ex = grndtoi(ex, &e); if (e < -4) break; }
      }
    }
    if (i == 1)
      prec = nbits2prec(gexpo(x) + 128);
    else
    {
      if (i > 4) pari_err_PREC("bnfisunit");
      prec = precdbl(prec);
    }
    if (DEBUGLEVEL) pari_warn(warnprec,"bnfisunit",prec);
    nf = nfnewprec_shallow(nf, prec);
  }
  /* choose a large embedding => small relative error */
  for (i = 1; i < RU; i++)
    if (signe(gel(rx,i)) > -1) break;
  if (RU == 1) t = gen_0;
  else
  {
    t = imag_i( row_i(logunit,i, 1,RU-1) );
    t = RgV_dotproduct(t, ex);
    if (i > r1) t = gmul2n(t, -1);
  }
  if (typ(emb) != t_MAT) arg = garg(gel(emb,i), prec);
  else
  {
    GEN p = gel(emb,1), e = gel(emb,2);
    long j, l = lg(p);
    arg = NULL;
    for (j = 1; j < l; j++)
    {
      GEN a = gmul(gel(e,j), garg(gel(gel(p,j),i), prec));
      arg = arg? gadd(arg, a): a;
    }
  }
  t = gsub(arg, t); /* = arg(the missing root of 1) */
  pi2_sur_w = divru(mppi(prec), n>>1); /* 2pi / n */
  e = umodiu(roundr(divrr(t, pi2_sur_w)), n);
  if (n > 2)
  {
    GEN z = algtobasis(nf, bnf_get_tuU(bnf)); /* primitive root of 1 */
    GEN ro = RgV_dotproduct(row(nf_get_M(nf), i), z);
    GEN p2 = roundr(divrr(garg(ro, prec), pi2_sur_w));
    e *= Fl_inv(umodiu(p2,n), n);
    e %= n;
  }
  gel(ex,RU) = mkintmodu(e, n);
  setlg(ex, RU+1); return gerepilecopy(av, ex);
}

/* S a list of prime ideal in idealprimedec format. Return res:
 * res[1] = generators of (S-units / units), as polynomials
 * res[2] = [perm, HB, den], for bnfissunit
 * res[3] = []
 * res[4] = S-regulator ( = R * det(res[2]) * prod log(Norm(S[i])))
 * res[5] = S class group
 * res[6] = S */
GEN
bnfsunit0(GEN bnf, GEN S, long flag, long prec)
{
  pari_sp av = avma;
  long i, lS, nH;
  GEN nf, M, U, H, Sunit, card, sreg, res, den, S2, perm, dep, B, A, p1, U1;

  if (!is_vec_t(typ(S))) pari_err_TYPE("bnfsunit",S);
  bnf = checkbnf(bnf);
  nf = bnf_get_nf(bnf);

  res=cgetg(7,t_VEC);
  gel(res,3) = cgetg(1,t_VEC); /* dummy */
  gel(res,4) = bnf_get_reg(bnf);
  gel(res,5) = bnf_get_clgp(bnf);
  gel(res,6) = S; lS = lg(S);
  if (lS == 1)
  {
    gel(res,1) = cgetg(1, t_VEC);
    gel(res,2) = mkvec3(cgetg(1,t_VECSMALL), cgetg(1,t_MAT), gen_1);
    return gerepilecopy(av, res);
  }

  M = cgetg(lS,t_MAT); /* relation matrix for the S class group */
  for (i = 1; i < lS; i++)
  {
    GEN pr = gel(S,i); checkprid(pr);
    gel(M,i) = isprincipal(bnf,pr);
  }
  M = shallowconcat(M, diagonal_shallow(bnf_get_cyc(bnf)));

  /* S class group */
  H = ZM_hnfall(M, &U, 1);
  card = gen_1;
  if (lg(H) > 1)
  { /* non trivial */
    GEN A, u, gen = bnf_get_gen(bnf), D = ZM_snf_group(H, NULL, &u);
    long l = lg(D);
    A = cgetg(l, t_VEC); card = ZV_prod(D);
    for(i = 1; i < l; i++) gel(A,i) = idealfactorback(nf, gen, gel(u,i), 1);
    gel(res,5) = mkvec3(card, D, A);
  }

  /* S-units */
  U1 = U; setlg(U1,lS); for (i = 1; i < lS; i++) setlg(U1[i], lS);
 /* U1 = upper left corner of U, invertible. S * U1 = principal ideals
  * whose generators generate the S-units */
  p1 = zeromat(0, lS-1); /* junk for mathnfspec */
  H = mathnfspec(U1, &perm, &dep, &B, &p1); /* dep has 0 rows */
 /*                   [ H B  ]            [ H^-1   - H^-1 B ]
  * perm o HNF(U1) =  [ 0 Id ], inverse = [  0         Id   ]
  * S * HNF(U1) = integral generators for S-units  = Sunit */
  Sunit = cgetg(lS, t_VEC);
  S2 = vecpermute(S, perm);
  nH = lg(H) - 1; setlg(S2, nH + 1);
  for (i = 1; i < lS; i++)
  {
    GEN C = NULL, E, v;
    if (i <= nH) E = gel(H,i); else { C = gel(S2,i), E = gel(B,i-nH); }
    v = gel(isprincipalfact(bnf, C, S2, E, flag | nf_FORCE), 2);
    if (flag == nf_GEN) v = nf_to_scalar_or_alg(nf, v);
    gel(Sunit,i) = v;
  }
  H = ZM_inv(H,&den);
  A = shallowconcat(H, ZM_neg(ZM_mul(H,B))); /* top part of inverse * den */
  /* HNF in split form perm + (H B) */
  gel(res,1) = Sunit;
  gel(res,2) = mkvec3(perm, A, den);

  /* S-regulator */
  sreg = mpmul(bnf_get_reg(bnf), card);
  for (i = 1; i < lS; i++)
  {
    GEN p = pr_get_p( gel(S,i) );
    sreg = mpmul(sreg, logr_abs(itor(p,prec)));
  }
  gel(res,4) = sreg;
  return gerepilecopy(av,res);
}
GEN
bnfsunit(GEN bnf,GEN S,long prec) { return bnfsunit0(bnf,S,nf_GEN,prec); }

/* v_S(x), x in famat form */
static GEN
sunit_famat_val(GEN nf, GEN S, GEN x)
{
  long i, l = lg(S);
  GEN v = cgetg(l, t_VEC);
  for (i = 1; i < l; i++) gel(v,i) = famat_nfvalrem(nf, x, gel(S,i), NULL);
  return v;
}
/* v_S(x), x algebraic number */
static GEN
sunit_val(GEN nf, GEN S, GEN x, GEN N)
{
  long i, l = lg(S);
  GEN v = zero_zv(l-1), N0 = N;
  for (i = 1; i < l; i++)
  {
    GEN P = gel(S,i), p = pr_get_p(P);
    if (dvdii(N, p)) { v[i] = nfval(nf,x,P); (void)Z_pvalrem(N0, p, &N0); }
  }
  return is_pm1(N0)? v: NULL;
}

/* if *px a famat, assume it's an S-unit */
static GEN
make_unit(GEN nf, GEN bnfS, GEN *px)
{
  GEN den, gen, v, w, HB, perm, S = gel(bnfS,6), x = *px;
  long cH, i, l = lg(S);

  if (l == 1) return cgetg(1, t_COL);
  w = gel(bnfS,2); perm = gel(w,1); HB = gel(w,2); den = gel(w,3);
  cH = nbrows(HB);
  if (typ(x) == t_MAT && lg(x) == 3)
  {
    v = sunit_famat_val(nf, S, x); /* x = S v */
    w = vecpermute(v, perm);
    v = ZM_ZC_mul(HB, w);
    w += cH; w[0] = evaltyp(t_COL) | evallg(lg(HB) - cH);
  }
  else
  {
    GEN N;
    x = nf_to_scalar_or_basis(nf,x);
    switch(typ(x))
    {
      case t_INT:  N = x; if (!signe(N)) return NULL; break;
      case t_FRAC: N = mulii(gel(x,1),gel(x,2)); break;
      default: { GEN d = Q_denom(x); N = mulii(idealnorm(nf,gmul(x,d)), d); }
    }
    /* relevant primes divide N */
    if (is_pm1(N)) return zerocol(l-1);
    v = sunit_val(nf, S, x, N);
    if (!v) return NULL;
    w = vecsmallpermute(v, perm);
    v = ZM_zc_mul(HB, w);
    w += cH; w[0] = evaltyp(t_VECSMALL) | evallg(lg(HB) - cH);
    w = zc_to_ZC(w);
  }
  if (!is_pm1(den)) for (i = 1; i <= cH; i++)
  {
    GEN r;
    gel(v,i) = dvmdii(gel(v,i), den, &r);
    if (r != gen_0) return NULL;
  }
  v = shallowconcat(v, w); /* append bottom of w (= [0 Id] part) */
  gen = gel(bnfS,1);
  for (i = 1; i < l; i++)
  {
    GEN e = gel(v,i);
    if (signe(e)) x = famat_mulpow_shallow(x, gel(gen,i), negi(e));
  }
  *px = x; return v;
}

static int
checkbnfS_i(GEN v)
{
  GEN S, g, w;
  if (typ(v) != t_VEC || lg(v) != 7) return 0;
  g = gel(v,1); w = gel(v,2); S = gel(v,6);
  if (typ(g) != t_VEC || !is_vec_t(typ(S)) || lg(S) != lg(g)) return 0;
  return typ(w) == t_VEC && lg(w) == 4 && typ(gel(w,1)) == t_VECSMALL;
}

/* Analog to bnfisunit, for S-units. Let v the result
 * If x not an S-unit, v = []~, else
 * x = \prod_{i=0}^r e_i^v[i] * prod{i=r+1}^{r+s} s_i^v[i]
 * where the e_i are the field units (cf bnfisunit), and the s_i are
 * the S-units computed by bnfsunit (in the same order) */
GEN
bnfissunit(GEN bnf, GEN bnfS, GEN x)
{
  pari_sp av = avma;
  GEN w, nf, v = NULL;

  bnf = checkbnf(bnf);
  if (!checkbnfS_i(bnfS)) pari_err_TYPE("bnfissunit",bnfS);
  nf = bnf_get_nf(bnf);
  if ( (w = make_unit(nf, bnfS, &x)) ) v = bnfisunit(bnf, x);
  if (!v || lg(v) == 1) { set_avma(av); return cgetg(1,t_COL); }
  return gerepilecopy(av, shallowconcat(v, w));
}
