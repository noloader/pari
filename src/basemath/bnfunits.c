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
      gel(v,RU) = utoi((s > 0)? 0: n>>1);
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
  gel(ex,RU) = utoi(e); setlg(ex, RU+1); return gerepilecopy(av, ex);
}

/* S a list of prime ideal in idealprimedec format. If pH != NULL, set it to
 * the HNF of the S-class group and return bnfsunit, else return bnfunits */
static GEN
bnfsunit_i(GEN bnf, GEN S, GEN *pH, GEN *pperm, GEN *pA, GEN *pden)
{
  const long FLAG = nf_FORCE | (pH? nf_GEN: nf_GENMAT);
  long i, nH, lS = lg(S);
  GEN M, U, H, Sunit, den, S2, perm, dep, B, C, U1;

  if (!is_vec_t(typ(S))) pari_err_TYPE("bnfsunit",S);
  bnf = checkbnf(bnf);
  if (lS == 1)
  {
    *pperm = cgetg(1,t_VECSMALL);
    *pA = cgetg(1,t_MAT);
    *pden = gen_1; return cgetg(1,t_VEC);
  }
  M = cgetg(lS,t_MAT); /* relation matrix for the S class group */
  for (i = 1; i < lS; i++)
  {
    GEN pr = gel(S,i); checkprid(pr);
    gel(M,i) = isprincipal(bnf,pr);
  }
  /* S class group */
  M = shallowconcat(M, diagonal_shallow(bnf_get_cyc(bnf)));
  H = ZM_hnfall(M, &U, 1); if (pH) *pH = H;
  /* S-units */
  U1 = U; setlg(U1,lS); for (i = 1; i < lS; i++) setlg(U1[i], lS);
 /* U1 = upper left corner of U, invertible. S * U1 = principal ideals
  * whose generators generate the S-units */
  C = zeromat(0, lS-1); /* junk for mathnfspec */
  H = mathnfspec(U1, &perm, &dep, &B, &C); /* dep has 0 rows */
 /*                   [ H B  ]            [ H^-1   - H^-1 B ]
  * perm o HNF(U1) =  [ 0 Id ], inverse = [  0         Id   ]
  * S * HNF(U1) = integral generators for S-units  = Sunit */
  Sunit = cgetg(lS, t_VEC);
  S2 = vecpermute(S, perm);
  nH = lg(H) - 1; setlg(S2, nH + 1);
  for (i = 1; i < lS; i++)
  {
    GEN C = NULL, E;
    if (i <= nH) E = gel(H,i); else { C = gel(S2,i), E = gel(B,i-nH); }
    gel(Sunit,i) = gel(isprincipalfact(bnf, C, S2, E, FLAG), 2);
  }
  H = ZM_inv(H,&den);
  *pperm = perm;
  *pA = shallowconcat(H, ZM_neg(ZM_mul(H,B))); /* top inverse * den */
  *pden = den; return Sunit;
}
GEN
bnfsunit(GEN bnf,GEN S,long prec)
{
  pari_sp av = avma;
  long i, l = lg(S);
  GEN v, R, h, nf, perm, A, den, U, H = NULL;
  bnf = checkbnf(bnf); nf = bnf_get_nf(bnf);
  v = cgetg(7, t_VEC);
  gel(v,1) = U = bnfsunit_i(bnf, S, &H, &perm, &A, &den);
  gel(v,2) = mkvec3(perm, A, den);
  gel(v,3) = cgetg(1,t_VEC); /* dummy */
  h = gen_1;
  if (l == 1)
    gel(v,5) = bnf_get_clgp(bnf);
  else
  { /* non trivial S-class group */
    GEN A, u, gen = bnf_get_gen(bnf), D = ZM_snf_group(H, NULL, &u);
    long lD = lg(D);
    A = cgetg(lD, t_VEC); h = ZV_prod(D);
    for(i = 1; i < lD; i++) gel(A,i) = idealfactorback(nf, gen, gel(u,i), 1);
    gel(v,5) = mkvec3(h, D, A);
  }
  R = bnf_get_reg(bnf);
  if (l > 1)
  { /* S-regulator and S-units*/
    R = mpmul(R, h);
    for (i = 1; i < l; i++)
    {
      GEN p = pr_get_p( gel(S,i) );
      R = mpmul(R, logr_abs(itor(p,prec)));
      gel(U,i) = nf_to_scalar_or_alg(nf, gel(U,i));
    }
  }
  gel(v,4) = R;
  gel(v,6) = S; return gerepilecopy(av, v);
}
GEN
bnfunits(GEN bnf, GEN S)
{
  pari_sp av = avma;
  GEN perm, A, den, U, fu, tu;
  bnf = checkbnf(bnf);
  U = bnfsunit_i(bnf, S? S: cgetg(1,t_VEC), NULL, &perm, &A, &den);
  if (!S) S = cgetg(1,t_VEC);
  fu = bnf_compactfu(bnf);
  if (!fu)
  {
    long i, l;
    fu = bnf_has_fu(bnf); if (!fu) bnf_build_units(bnf);
    fu = shallowcopy(fu); l = lg(fu);
    for (i = 1; i < l; i++) gel(fu,i) = to_famat_shallow(gel(fu,i),gen_1);
  }
  tu = nf_to_scalar_or_basis(bnf_get_nf(bnf), bnf_get_tuU(bnf));
  U = shallowconcat(U, vec_append(fu, to_famat_shallow(tu,gen_1)));
  return gerepilecopy(av, mkvec5(U, S, perm, A, den));
}
GEN
sunits_mod_units(GEN bnf, GEN S)
{
  pari_sp av = avma;
  GEN perm, A, den;
  bnf = checkbnf(bnf);
  return gerepilecopy(av, bnfsunit_i(bnf, S, NULL, &perm, &A, &den));
}

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
make_unit(GEN nf, GEN U, GEN *px)
{
  GEN den, v, w, A, perm, gen = gel(U,1), S = gel(U,2), x = *px;
  long cH, i, l = lg(S);

  if (l == 1) return cgetg(1, t_COL);
  perm = gel(U,3); A = gel(U,4); den = gel(U,5);
  cH = nbrows(A);
  if (typ(x) == t_MAT && lg(x) == 3)
  {
    v = sunit_famat_val(nf, S, x); /* x = S v */
    w = vecpermute(v, perm);
    v = ZM_ZC_mul(A, w);
    w += cH; w[0] = evaltyp(t_COL) | evallg(lg(A) - cH);
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
    v = ZM_zc_mul(A, w);
    w += cH; w[0] = evaltyp(t_VECSMALL) | evallg(lg(A) - cH);
    w = zc_to_ZC(w);
  }
  if (!is_pm1(den)) for (i = 1; i <= cH; i++)
  {
    GEN r;
    gel(v,i) = dvmdii(gel(v,i), den, &r);
    if (r != gen_0) return NULL;
  }
  v = shallowconcat(v, w); /* append bottom of w (= [0 Id] part) */
  for (i = 1; i < l; i++)
  {
    GEN e = gel(v,i);
    if (signe(e)) x = famat_mulpow_shallow(x, gel(gen,i), negi(e));
  }
  *px = x; return v;
}

static GEN
bnfissunit_i(GEN bnf, GEN x, GEN U)
{
  GEN w, nf, v = NULL;
  bnf = checkbnf(bnf);
  nf = bnf_get_nf(bnf);
  if ( (w = make_unit(nf, U, &x)) ) v = bnfisunit(bnf, x);
  if (!v || lg(v) == 1) return NULL;
  return mkvec2(v, w);
}
static int
checkU(GEN U)
{
  GEN g, S, perm;
  if (typ(U) != t_VEC || lg(U) != 6) return 0;
  g = gel(U,1); S = gel(U,2); perm = gel(U,3);
  return typ(g) == t_VEC && is_vec_t(typ(S)) && typ(perm) == t_VECSMALL
         && lg(S) == lg(perm);
}
GEN
bnfisunit0(GEN bnf, GEN x, GEN U)
{
  pari_sp av = avma;
  GEN z;
  if (!U) return bnfisunit(bnf, x);
  if (!checkU(U)) pari_err_TYPE("bnfisunit",U);
  z = bnfissunit_i(bnf, x, U);
  if (!z) { set_avma(av); return cgetg(1,t_COL); }
  return gerepilecopy(av, shallowconcat(gel(z,2), gel(z,1)));
}

/* OBSOLETE */
static int
checkbnfS_i(GEN v)
{
  GEN S, g, w;
  if (typ(v) != t_VEC || lg(v) != 7) return 0;
  g = gel(v,1); w = gel(v,2); S = gel(v,6);
  if (typ(g) != t_VEC || !is_vec_t(typ(S)) || lg(S) != lg(g)) return 0;
  return typ(w) == t_VEC && lg(w) == 4 && typ(gel(w,1)) == t_VECSMALL;
}
/* OBSOLETE */
GEN
bnfissunit(GEN bnf, GEN bnfS, GEN x)
{
  pari_sp av = avma;
  GEN z, U;
  if (!checkbnfS_i(bnfS)) pari_err_TYPE("bnfissunit",bnfS);
  U = mkvec5(gel(bnfS,1), gel(bnfS,6), gmael(bnfS,2,1), gmael(bnfS,2,2),
             gmael(bnfS,2,3));
  z = bnfissunit_i(bnf, x, U);
  if (!z) { set_avma(av); return cgetg(1,t_COL); }
  return gerepilecopy(av, shallowconcat(gel(z,1), gel(z,2)));
}
