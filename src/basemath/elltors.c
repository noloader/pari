/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/********************************************************************/
/**                                                                **/
/**         TORSION OF ELLIPTIC CURVES over NUMBER FIELDS          **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"
static int
smaller_x(GEN p, GEN q)
{
  int s = absi_cmp(denom(p), denom(q));
  return (s<0 || (s==0 && absi_cmp(numer(p),numer(q)) < 0));
}

/* best generator in cycle of length k */
static GEN
best_in_cycle(GEN e, GEN p, long k)
{
  GEN p0 = p,q = p;
  long i;

  for (i=2; i+i<k; i++)
  {
    q = elladd(e,q,p0);
    if (ugcd(i,k)==1 && smaller_x(gel(q,1), gel(p,1))) p = q;
  }
  return (gsigne(ec_dmFdy_evalQ(e,p)) < 0)? ellneg(e,p): p;
}

/* <p,q> = E_tors, possibly NULL (= oo), p,q independent unless NULL
 * order p = k, order q = 2 unless NULL */
static GEN
tors(GEN e, long k, GEN p, GEN q, GEN v)
{
  GEN r;
  if (q)
  {
    long n = k>>1;
    GEN p1, best = q, np = ellmul(e,p,utoipos(n));
    if (n % 2 && smaller_x(gel(np,1), gel(best,1))) best = np;
    p1 = elladd(e,q,np);
    if (smaller_x(gel(p1,1), gel(best,1))) q = p1;
    else if (best == np) { p = elladd(e,p,q); q = np; }
    p = best_in_cycle(e,p,k);
    if (v)
    {
      p = ellchangepointinv(p,v);
      q = ellchangepointinv(q,v);
    }
    r = cgetg(4,t_VEC);
    gel(r,1) = utoipos(2*k);
    gel(r,2) = mkvec2(utoipos(k), gen_2);
    gel(r,3) = mkvec2copy(p, q);
  }
  else
  {
    if (p)
    {
      p = best_in_cycle(e,p,k);
      if (v) p = ellchangepointinv(p,v);
      r = cgetg(4,t_VEC);
      gel(r,1) = utoipos(k);
      gel(r,2) = mkvec( gel(r,1) );
      gel(r,3) = mkvec( gcopy(p) );
    }
    else
    {
      r = cgetg(4,t_VEC);
      gel(r,1) = gen_1;
      gel(r,2) = cgetg(1,t_VEC);
      gel(r,3) = cgetg(1,t_VEC);
    }
  }
  return r;
}

/* Using Lutz-Nagell */

/* p in Z[X] of degree 3. Return vector of x/4, x integral root of p */
static GEN
ratroot(GEN p)
{
  GEN L, a, ld;
  long i, t, v = ZX_valrem(p, &p);

  if (v == 3) return ellinf();
  if (v == 2) return mkvec2(gen_0, gmul2n(negi(gel(p,2)), -2));

  L = cgetg(4,t_VEC); t = 1;
  if (v == 1) gel(L,t++) = gen_0;
  ld = divisors(gel(p,2));
  for (i=1; i<lg(ld); i++)
  {
    a = gel(ld,i);
    if (!signe(poleval(p,a))) gel(L,t++) = gmul2n(a, -2);
    a = negi(a);
    if (!signe(poleval(p,a))) gel(L,t++) = gmul2n(a, -2);
  }
  setlg(L,t); return L;
}

static int
is_new_torsion(GEN e, GEN v, GEN p, long t2) {
  GEN pk = p, pkprec = NULL;
  long k,l;

  for (k=2; k<=6; k++)
  {
    pk = elladd(e,pk,p); /* = [k] p */
    if (ell_is_inf(pk)) return 1;

    for (l=2; l<=t2; l++)
      if (gequal(gel(pk,1),gmael(v,l,1))) return 1;

    if (pkprec && k<=5)
      if (gequal(gel(pk,1),gel(pkprec,1))) return 1;
    pkprec=pk;
  }
  return 0;
}

static GEN
nagelllutz(GEN e)
{
  GEN ld, pol, p1, lr, r, v, w2, w3;
  long i, j, nlr, t, t2, k, k2;
  pari_sp av=avma;

  e = ellintegralmodel(e, &v);
  pol = RgX_rescale(ec_bmodel(e), utoipos(4));
  r = cgetg(17, t_VEC);
  gel(r,1) = ellinf();
  lr = ratroot(pol); nlr=lg(lr)-1;
  for (t=1,i=1; i<=nlr; i++)
  {
    GEN x = gel(lr,i), y = gmul2n(gneg(ec_h_evalx(e,x)), -1);
    gel(r,++t) = mkvec2(x, y);
  }
  ld = absi_factor(gmul2n(ell_get_disc(e), 4));
  p1 = gel(ld,2); k = lg(p1);
  for (i=1; i<k; i++) gel(p1,i) = shifti(gel(p1,i), -1);
  ld = divisors(ld);
  for (t2=t,j=1; j<lg(ld); j++)
  {
    GEN d = gel(ld,j);
    lr = ratroot(ZX_Z_sub(pol, shifti(sqri(d), 6)));
    for (i=1; i<lg(lr); i++)
    {
      GEN x = gel(lr,i), y = gmul2n(gsub(d, ec_h_evalx(e,x)), -1);
      p1 = mkvec2(x, y);
      if (is_new_torsion(e,r,p1,t2))
      {
        gel(r,++t) = p1;
        gel(r,++t) = mkvec2(x, gsub(y, d));
      }
    }
  }
  if (t == 1) { avma = av; return tors(e,1,NULL,NULL,v); }

  if (nlr < 3)
  {
    w2 = mkvec( utoipos(t) );
    for (k=2; k<=t; k++)
      if (ellorder_Q(e,gel(r,k)) == t) break;
    if (k>t) pari_err_BUG("elltors (bug1)");

    w3 = mkvec( gel(r,k) );
  }
  else
  {
    if (t&3) pari_err_BUG("elltors (bug2)");
    t2 = t>>1;
    w2 = mkvec2(utoipos(t2), gen_2);
    for (k=2; k<=t; k++)
      if (ellorder_Q(e,gel(r,k)) == t2) break;
    if (k>t) pari_err_BUG("elltors (bug3)");

    p1 = ellmul(e,gel(r,k),utoipos(t>>2));
    k2 = (!ell_is_inf(p1) && gequal(gel(r,2),p1))? 3: 2;
    w3 = mkvec2(gel(r,k), gel(r,k2));
  }
  if (v)
  {
    gel(v,1) = ginv(gel(v,1));
    w3 = ellchangepoint(w3,v);
  }
  return gerepilecopy(av, mkvec3(utoipos(t), w2,w3));
}

/* Finds a multiplicative upper bound for #E_tor; assume integral model */
static long
torsbound(GEN e)
{
  GEN D = ell_get_disc(e);
  pari_sp av = avma, av2;
  long m, b, bold, nb;
  forprime_t S;
  long CM = ellQ_get_CM(e);
  nb = expi(D) >> 3;
  /* nb = number of primes to try ~ 1 prime every 8 bits in D */
  b = bold = 5040; /* = 2^4 * 3^2 * 5 * 7 */
  m = 0;
  (void)u_forprime_init(&S, 3, ULONG_MAX);
  av2 = avma;
  while (m < nb || (b > 12 && b != 16))
  {
    ulong p = u_forprime_next(&S);
    if (!p) pari_err_BUG("torsbound [ran out of primes]");
    if (!umodiu(D, p)) continue;

    b = ugcd(b, p+1 - ellap_CM_fast(e,p,CM));
    avma = av2;
    if (b == 1) break;
    if (b == bold) m++; else { bold = b; m = 0; }
  }
  avma = av; return b;
}

/* Using Doud's algorithm */

static GEN
myround(GEN x, long *e)
{
  GEN y = grndtoi(x,e);
  if (*e > -5 && prec2nbits(gprecision(x)) < gexpo(y) - 10)
    pari_err_PREC("elltors");
  return y;
}

/* E the curve, w in C/Lambda ~ E of order n, returns q = pointell(w) as a
 * rational point on the curve, or NULL if q is not rational. */
static GEN
torspnt(GEN E, GEN w, long n, long prec)
{
  GEN p = cgetg(3,t_VEC), q = pointell(E, w, prec);
  long e;
  gel(p,1) = gmul2n(myround(gmul2n(gel(q,1),2), &e),-2);
  if (e > -5 || typ(gel(p,1)) == t_COMPLEX) return NULL;
  gel(p,2) = gmul2n(myround(gmul2n(gel(q,2),3), &e),-3);
  if (e > -5 || typ(gel(p,2)) == t_COMPLEX) return NULL;
  return (oncurve(E,p)
      && ell_is_inf(ellmul(E,p,utoipos(n)))
      && ellorder_Q(E,p) == n)? p: NULL;
}

static GEN
elltors_doud(GEN e)
{
  long B, i, ord, prec, k = 1;
  pari_sp av=avma;
  GEN v,w,w1,w22,w1j,w12,p,tor1,tor2;
  GEN om;

  e = ellintegralmodel(e, &v);
  B = torsbound(e); /* #E_tor | B */
  if (B == 1) { avma = av; return tors(e,1,NULL,NULL, v); }

  /* prec >= size of sqrt(D) */
  prec = DEFAULTPREC + ((lgefint(ell_get_disc(e))-2) >> 1);
  om = ellR_omega(e, prec);
  w1 = gel(om,1);
  w22 = gmul2n(gel(om,2),-1);
  if (B % 4)
  { /* cyclic of order 1, p, 2p, p <= 5 */
    p = NULL;
    for (i=10; i>1; i--)
    {
      if (B%i != 0) continue;
      w1j = gdivgs(w1,i);
      p = torspnt(e,w1j,i,prec);
      if (!p && i%2==0)
      {
        p = torspnt(e,gadd(w22,w1j),i,prec);
        if (!p) p = torspnt(e,gadd(w22,gmul2n(w1j,1)),i,prec);
      }
      if (p) { k = i; break; }
    }
    return gerepileupto(av, tors(e,k,p,NULL, v));
  }

  ord = 0; tor1 = tor2 = NULL;
  w12 = gmul2n(w1,-1);
  if ((p = torspnt(e,w12,2,prec))) { tor1 = p; ord++; }
  w = w22;
  if ((p = torspnt(e,w,2,prec))) { tor2 = p; ord += 2; }
  if (!ord)
  {
    w = gadd(w12,w22);
    if ((p = torspnt(e,w,2,prec))) { tor2 = p; ord += 2; }
  }
  p = NULL;
  switch(ord)
  {
    case 0: /* no point of order 2 */
      for (i=9; i>1; i-=2)
      {
        if (B%i != 0) continue;
        w1j = gdivgs(w1,i);
        p = torspnt(e,w1j,i,prec);
        if (p) { k = i; break; }
      }
      break;

    case 1: /* 1 point of order 2: w1 / 2 */
      for (i=12; i>2; i-=2)
      {
        if (B%i != 0) continue;
        w1j = gdivgs(w1,i);
        p = torspnt(e,w1j,i,prec);
        if (!p && i%4==0) p = torspnt(e,gadd(w22,w1j),i,prec);
        if (p) { k = i; break; }
      }
      if (!p) { p = tor1; k = 2; }
      break;

    case 2: /* 1 point of order 2: w = w2/2 or (w1+w2)/2 */
      for (i=5; i>1; i-=2)
      {
        if (B%i != 0) continue;
        w1j = gdivgs(w1,i);
        p = torspnt(e,gadd(w,w1j),2*i,prec);
        if (p) { k = 2*i; break; }
      }
      if (!p) { p = tor2; k = 2; }
      tor2 = NULL; break;

    case 3: /* 2 points of order 2: w1/2 and w2/2 */
      for (i=8; i>2; i-=2)
      {
        if (B%(2*i) != 0) continue;
        w1j = gdivgs(w1,i);
        p = torspnt(e,w1j,i,prec);
        if (p) { k = i; break; }
      }
      if (!p) { p = tor1; k = 2; }
      break;
  }
  return gerepileupto(av, tors(e,k,p,tor2, v));
}

/* return a rational point of order pk = p^k on E, or NULL if E(Q)[k] = O.
 * *fk is either NULL (pk = 4 or prime) or elldivpol(p^(k-1)).
 * Set *fk to elldivpol(p^k) */
static GEN
tpoint(GEN E, long pk, GEN *fk)
{
  GEN f = elldivpol(E,pk,0), g = *fk, v;
  long i, l;
  *fk = f;
  if (g) f = RgX_div(f, g);
  v = nfrootsQ(f); l = lg(v);
  for (i = 1; i < l; i++)
  {
    GEN x = gel(v,i);
    GEN y = ellordinate(E,x,0);
    if (lg(y) != 1) return mkvec2(x,gel(y,1));
  }
  return NULL;
}
/* return E(Q)[2] */
static GEN
t2points(GEN E, GEN *f2)
{
  long i, l;
  GEN v;
  *f2 = ec_bmodel(E);
  v = nfrootsQ(*f2); l = lg(v);
  for (i = 1; i < l; i++)
  {
    GEN x = gel(v,i);
    GEN y = ellordinate(E,x,0);
    if (lg(y) != 1) gel(v,i) = mkvec2(x,gel(y,1));
  }
  return v;
}

static GEN
elltors_divpol(GEN E)
{
  GEN T2 = NULL, p, P, Q, v;
  long v2, r2, B;

  E = ellintegralmodel(E, &v);
  B = torsbound(E); /* #E_tor | B */
  if (B == 1) return tors(E,1,NULL,NULL, v);
  v2 = vals(B); /* bound for v_2(point order) */
  B >>= v2;
  p = const_vec(9, NULL);
  r2 = 0;
  if (v2) {
    GEN f;
    T2 = t2points(E, &f);
    switch(lg(T2)-1)
    {
      case 0:  v2 = 0; break;
      case 1:  r2 = 1; if (v2 == 4) v2 = 3; break;
      default: r2 = 2; v2--; break; /* 3 */
    }
    if (v2) gel(p,2) = gel(T2,1);
    /* f = f_2 */
    if (v2 > 1) { gel(p,4) = tpoint(E,4, &f); if (!gel(p,4)) v2 = 1; }
    /* if (v2>1) now f = f4 */
    if (v2 > 2) { gel(p,8) = tpoint(E,8, &f); if (!gel(p,8)) v2 = 2; }
  }
  B <<= v2;
  if (B % 3 == 0) {
    GEN f3 = NULL;
    gel(p,3) = tpoint(E,3,&f3);
    if (!gel(p,3)) B /= (B%9)? 3: 9;
    if (gel(p,3) && B % 9 == 0)
    {
      gel(p,9) = tpoint(E,9,&f3);
      if (!gel(p,9)) B /= 3;
    }
  }
  if (B % 5 == 0) {
    GEN junk = NULL;
    gel(p,5) = tpoint(E,5,&junk);
    if (!gel(p,5)) B /= 5;
  }
  if (B % 7 == 0) {
    GEN junk = NULL;
    gel(p,7) = tpoint(E,7,&junk);
    if (!gel(p,7)) B /= 7;
  }
  /* B is the exponent of E_tors(Q), r2 is the rank of its 2-Sylow,
   * for i > 1, p[i] is a point of order i if one exists and i is a prime power
   * and NULL otherwise */
  if (r2 == 2) /* 2 cyclic factors */
  { /* C2 x C2 */
    if (B == 2) return tors(E,2, gel(T2,1), gel(T2,2), v);
    else if (B == 6)
    { /* C2 x C6 */
      P = elladd(E, gel(p,3), gel(T2,1));
      Q = gel(T2,2);
    }
    else
    { /* C2 x C4 or C2 x C8 */
      P = gel(p, B);
      Q = gel(T2,2);
      if (gequal(Q, ellmul(E, P, utoipos(B>>1)))) Q = gel(T2,1);
    }
  }
  else /* cyclic */
  {
    Q = NULL;
    if (v2)
    {
      if (B>>v2 == 1)
        P = gel(p, B);
      else
        P = elladd(E, gel(p, B>>v2), gel(p,1<<v2));
    }
    else P = gel(p, B);
  }
  return tors(E,B, P, Q, v);
}
GEN
elltors(GEN e)
{
  pari_sp av = avma;
  checkell_Q(e);
  return gerepileupto(av, elltors_divpol(e));
}

GEN
elltors0(GEN e, long flag)
{
  checkell_Q(e);
  switch(flag)
  {
    case 0: return elltors(e);
    case 1: return nagelllutz(e);
    case 2: return elltors_doud(e);
    default: pari_err_FLAG("elltors");
  }
  return NULL; /* not reached */
}

/* order of points */

/* assume e is defined over Q (use Mazur's theorem) */
long
ellorder_Q(GEN E, GEN P)
{
  pari_sp av = avma;
  GEN dx, dy, d4, d6, D, Pp, Q;
  forprime_t T;
  ulong a4, p;
  long k;
  if (ell_is_inf(P)) return 1;

  dx = Q_denom(gel(P,1));
  dy = Q_denom(gel(P,2));
  if (ell_is_integral(E)) /* integral model, try Nagell Lutz */
    if (cmpiu(dx, 4) > 0 || cmpiu(dy, 8) > 0) return 0;

  d4 = Q_denom(ell_get_c4(E));
  d6 = Q_denom(ell_get_c6(E));
  D = ell_get_disc (E);
  /* choose not too small prime p dividing neither a coefficient of the
     short Weierstrass form nor of P and leading to good reduction */

  u_forprime_init(&T, 100003, ULONG_MAX);
  while ( (p = u_forprime_next(&T)) )
    if (Rg_to_Fl(d4, p) && Rg_to_Fl(d6, p) && Rg_to_Fl(D, p)
     && Rg_to_Fl(dx, p) && Rg_to_Fl(dy, p)) break;

  /* transform E into short Weierstrass form Ep modulo p and P to Pp on Ep,
   * check whether the order of Pp on Ep is <= 12 */
  Pp = point_to_a4a6_Fl(E, P, p, &a4);
  for (Q = Fle_dbl(Pp, a4, p), k = 2;
       !ell_is_inf(Q) && k <= 12;
       Q = Fle_add(Q, Pp, a4, p), k++) /* empty */;

  if (k != 13)
    /* check over Q; one could also run more tests modulo primes */
    for (Q = elladd(E, P, P), k = 2;
        !ell_is_inf(Q) && k <= 12;
        Q = elladd(E, Q, P), k++) /* empty */;

  avma = av;
  return (k == 13 ? 0 : k);
}

GEN
ellorder(GEN E, GEN P, GEN o)
{
  pari_sp av = avma;
  GEN fg, r, E0 = E;
  checkell(E); checkellpt(P);
  if (ell_is_inf(P)) return gen_1;
  if (ell_get_type(E)==t_ELL_Q)
  {
    GEN p = NULL;
    if (is_rational_t(typ(gel(P,1))) && is_rational_t(typ(gel(P,2))))
      return utoi( ellorder_Q(E, P) );
    if (RgV_is_FpV(P,&p) && p)
    {
      E = ellinit(E,p,0);
      if (lg(E)==1) pari_err_IMPL("ellorder for curve with singular reduction");
    }
  }
  checkell_Fq(E);
  fg = ellff_get_field(E);
  if (!o) o = ellff_get_o(E);
  if (typ(fg)==t_FFELT)
    r = FF_ellorder(E, P, o);
  else
  {
    GEN p = fg, e = ellff_get_a4a6(E);
    GEN Pp = FpE_changepointinv(RgE_to_FpE(P,p), gel(e,3), p);
    r = FpE_order(Pp, o, gel(e,1), p);
  }
  if (E != E0) obj_free(E);
  return gerepileuptoint(av, r);
}

GEN
orderell(GEN e, GEN z) { return ellorder(e,z,NULL); }
