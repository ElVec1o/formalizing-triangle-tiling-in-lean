import Erdos634.Draft.LaczFormal53Basis

/-!
# Laczkovich Thm 5.3, case (vii), the four target shapes

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995), Thm 5.1/5.3), Beeson, Beeson-Zhang.  Formalization debt.

The tile `(pi/4, pi/8, 5 pi/8)` has sides `(w, u, v) = (sin pi/4, sin pi/8, sin 5pi/8)` (times a scale).  A target side that is a
nonnegative integer combination `n w + m u + k v` has coordinates `(0, n/2, m + k, k)` in the basis `1, sqrt2, u, sqrt2 u`
(`v = (1 + sqrt2) u`).  If the target angles are `(1,1,6)`, `(1,3,4)`, `(2,2,4)`, `(2,3,3)` (units of `pi/8`), the law of sines gives the
proportionality of its three sides to `(u,u,w)`, `(u,v,1)`, `(w,w,1)`, `(w,v,v)`, and the area relation `Hh(L) = N^2/4`
(`Hh` = Heron form, tile `Hh = 1/4`).  Each shape is impossible: `shape116`, `shape134`, `shape224`, `shape233`.
-/

namespace Erdos634.Lacz53

namespace E4

def sub (x y : E4) : E4 := ⟨x.a - y.a, x.b - y.b, x.c - y.c, x.d - y.d⟩
def ofQ (r : ℚ) : E4 := ⟨r, 0, 0, 0⟩
def sideE (n m k : ℚ) : E4 := ⟨0, n / 2, m + k, k⟩
def wE : E4 := ⟨0, 1 / 2, 0, 0⟩
def uE : E4 := ⟨0, 0, 1, 0⟩
def vE : E4 := ⟨0, 0, 1, 1⟩
def oneE : E4 := ⟨1, 0, 0, 0⟩

/-- Heron form on coefficient tuples. -/
def hhE (x y z : E4) : E4 :=
  sub (sub (sub (add (smul 2 ((x.mul x).mul (y.mul y))) (add (smul 2 ((y.mul y).mul (z.mul z)))
    (smul 2 ((z.mul z).mul (x.mul x))))) ((x.mul x).mul (x.mul x))) ((y.mul y).mul (y.mul y)))
    ((z.mul z).mul (z.mul z))

theorem ev_add (x y : E4) : (x.add y).ev = x.ev + y.ev := by
  simp only [ev, add]; push_cast; ring

theorem ev_sub (x y : E4) : (x.sub y).ev = x.ev - y.ev := by
  simp only [ev, sub]; push_cast; ring

theorem ev_smul (r : ℚ) (x : E4) : (x.smul r).ev = r * x.ev := by
  simp only [ev, smul]; push_cast; ring

theorem ev_ofQ (r : ℚ) : (ofQ r).ev = r := by
  simp [ev, ofQ]

theorem ev_sideE (n m k : ℚ) :
    (sideE n m k).ev = n * (Real.sqrt 2 / 2) + m * uu + k * ((1 + Real.sqrt 2) * uu) := by
  simp only [ev, sideE]; push_cast; ring

theorem ev_wE : wE.ev = Real.sqrt 2 / 2 := by unfold ev wE; push_cast; ring
theorem ev_uE : uE.ev = uu := by unfold ev uE; push_cast; ring
theorem ev_vE : vE.ev = (1 + Real.sqrt 2) * uu := by unfold ev vE; push_cast; ring
theorem ev_oneE : oneE.ev = 1 := by unfold ev oneE; push_cast; ring

theorem ev_hhE (x y z : E4) :
    (hhE x y z).ev = 2 * x.ev ^ 2 * y.ev ^ 2 + 2 * y.ev ^ 2 * z.ev ^ 2 + 2 * z.ev ^ 2 * x.ev ^ 2
      - x.ev ^ 4 - y.ev ^ 4 - z.ev ^ 4 := by
  simp only [hhE, ev_sub, ev_add, ev_smul, ev_mul]; push_cast; ring

end E4

open E4

set_option maxHeartbeats 4000000 in
/-- Shape `(1,1,6)`: `s = (u, u, w)`. -/
theorem shape116 {na ma ka nb mb kb nc mc kc N : ℚ}
    (h1 : 0 ≤ na) (h2 : 0 ≤ ma) (h3 : 0 ≤ ka) (h4 : 0 ≤ nb) (h5 : 0 ≤ mb) (h6 : 0 ≤ kb)
    (h7 : 0 ≤ nc) (h8 : 0 ≤ mc) (h9 : 0 ≤ kc)
    (hab : (sideE na ma ka).mul uE = (sideE nb mb kb).mul uE)
    (hac : (sideE na ma ka).mul wE = (sideE nc mc kc).mul uE)
    (hbc : (sideE nb mb kb).mul wE = (sideE nc mc kc).mul uE)
    (hH : hhE (sideE na ma ka) (sideE nb mb kb) (sideE nc mc kc) = ofQ (N ^ 2 / 4))
    (hpos : 0 < na + ma + ka) : False := by
  have a1 := congrArg E4.a hab; have b1 := congrArg E4.b hab
  have c1 := congrArg E4.c hab; have d1 := congrArg E4.d hab
  have a2 := congrArg E4.a hac; have b2 := congrArg E4.b hac
  have c2 := congrArg E4.c hac; have d2 := congrArg E4.d hac
  have a3 := congrArg E4.a hbc; have b3 := congrArg E4.b hbc
  have c3 := congrArg E4.c hbc; have d3 := congrArg E4.d hbc
  simp only [sideE, uE, wE, E4.mul] at a1 b1 c1 d1 a2 b2 c2 d2 a3 b3 c3 d3
  have e1 : ka = 0 := by linarith
  have e2 : kb = 0 := by linarith
  have e3 : mb = ma := by linarith
  have e4 : kc = mc := by linarith
  have e5 : kc = na := by linarith
  have e6 : kc = nb := by linarith
  have e7 : mb = nc := by linarith
  subst e1 e2 e3 e4 e5 e6 e7
  have hb := congrArg E4.b hH
  have ha := congrArg E4.a hH
  simp only [hhE, sideE, ofQ, E4.mul, E4.add, E4.smul, E4.sub] at hb ha
  have hq : mb ^ 2 * (mb ^ 2 + 3 * kc ^ 2) = 0 := by linear_combination (-2) * hb
  have hmb : mb = 0 := by
    rcases mul_eq_zero.1 hq with h | h
    · exact pow_eq_zero_iff (two_ne_zero) |>.1 h
    · nlinarith [sq_nonneg mb, sq_nonneg kc]
  subst hmb
  have hN : N ^ 2 = 2 * (kc ^ 2) ^ 2 := by linear_combination (-4) * ha
  have := sq_eq_two_sq hN
  have hk : kc = 0 := by nlinarith [sq_nonneg kc]
  subst hk
  simp at hpos

/-- Shape `(1,3,4)`: `s = (u, v, 1)`.  The linear conditions already force the side `La` to vanish. -/
theorem shape134 {na ma ka nb mb kb nc mc kc : ℚ}
    (h1 : 0 ≤ na) (h2 : 0 ≤ ma) (h3 : 0 ≤ ka) (h4 : 0 ≤ nb) (h5 : 0 ≤ mb) (h6 : 0 ≤ kb)
    (h7 : 0 ≤ nc) (h8 : 0 ≤ mc) (h9 : 0 ≤ kc)
    (hab : (sideE na ma ka).mul vE = (sideE nb mb kb).mul uE)
    (hac : (sideE na ma ka).mul oneE = (sideE nc mc kc).mul uE)
    (hbc : (sideE nb mb kb).mul oneE = (sideE nc mc kc).mul vE)
    (hpos : 0 < na + ma + ka) : False := by
  have a1 := congrArg E4.a hab; have b1 := congrArg E4.b hab
  have c1 := congrArg E4.c hab; have d1 := congrArg E4.d hab
  have a2 := congrArg E4.a hac; have b2 := congrArg E4.b hac
  have c2 := congrArg E4.c hac; have d2 := congrArg E4.d hac
  have a3 := congrArg E4.a hbc; have b3 := congrArg E4.b hbc
  have c3 := congrArg E4.c hbc; have d3 := congrArg E4.d hbc
  simp only [sideE, uE, vE, oneE, E4.mul] at a1 b1 c1 d1 a2 b2 c2 d2 a3 b3 c3 d3
  have e1 : na = 0 := by linarith
  have e2 : ma = 0 := by linarith
  have e3 : ka = 0 := by linarith
  linarith

set_option maxHeartbeats 4000000 in
/-- Shape `(2,3,3)`: `s = (w, v, v)`. -/
theorem shape233 {na ma ka nb mb kb nc mc kc N : ℚ}
    (h1 : 0 ≤ na) (h2 : 0 ≤ ma) (h3 : 0 ≤ ka) (h4 : 0 ≤ nb) (h5 : 0 ≤ mb) (h6 : 0 ≤ kb)
    (h7 : 0 ≤ nc) (h8 : 0 ≤ mc) (h9 : 0 ≤ kc)
    (hab : (sideE na ma ka).mul vE = (sideE nb mb kb).mul wE)
    (hac : (sideE na ma ka).mul vE = (sideE nc mc kc).mul wE)
    (hbc : (sideE nb mb kb).mul vE = (sideE nc mc kc).mul vE)
    (hH : hhE (sideE na ma ka) (sideE nb mb kb) (sideE nc mc kc) = ofQ (N ^ 2 / 4))
    (hpos : 0 < na + ma + ka) : False := by
  have a1 := congrArg E4.a hab; have b1 := congrArg E4.b hab
  have c1 := congrArg E4.c hab; have d1 := congrArg E4.d hab
  have a2 := congrArg E4.a hac; have b2 := congrArg E4.b hac
  have c2 := congrArg E4.c hac; have d2 := congrArg E4.d hac
  have a3 := congrArg E4.a hbc; have b3 := congrArg E4.b hbc
  have c3 := congrArg E4.c hbc; have d3 := congrArg E4.d hbc
  simp only [sideE, wE, vE, E4.mul] at a1 b1 c1 d1 a2 b2 c2 d2 a3 b3 c3 d3
  have e1 : ma = 0 := by linarith
  have e2 : ka = 0 := by linarith
  have e3 : nb = 0 := by linarith
  have e4 : nc = 0 := by linarith
  have e5 : mb = 0 := by linarith
  have e6 : kb = kc := by linarith
  have e7 : mc = 0 := by linarith
  have e8 : kc = na := by linarith
  subst e1 e2 e3 e4 e5 e7
  subst e6
  subst e8
  have hb := congrArg E4.b hH
  simp only [hhE, sideE, ofQ, E4.mul, E4.add, E4.smul, E4.sub] at hb
  have hq : kb ^ 4 = 0 := by linear_combination 2 * hb
  have : kb = 0 := pow_eq_zero_iff (by norm_num) |>.1 hq
  subst this
  simp at hpos

set_option maxHeartbeats 4000000 in
/-- Shape `(2,2,4)`: `s = (w, w, 1)`. -/
theorem shape224 {na ma ka nb mb kb nc mc kc N : ℚ}
    (h1 : 0 ≤ na) (h2 : 0 ≤ ma) (h3 : 0 ≤ ka) (h4 : 0 ≤ nb) (h5 : 0 ≤ mb) (h6 : 0 ≤ kb)
    (h7 : 0 ≤ nc) (h8 : 0 ≤ mc) (h9 : 0 ≤ kc)
    (hab : (sideE na ma ka).mul wE = (sideE nb mb kb).mul wE)
    (hac : (sideE na ma ka).mul oneE = (sideE nc mc kc).mul wE)
    (hbc : (sideE nb mb kb).mul oneE = (sideE nc mc kc).mul wE)
    (hH : hhE (sideE na ma ka) (sideE nb mb kb) (sideE nc mc kc) = ofQ (N ^ 2 / 4))
    (hpos : 0 < na + ma + ka) : False := by
  have a1 := congrArg E4.a hab; have b1 := congrArg E4.b hab
  have c1 := congrArg E4.c hab; have d1 := congrArg E4.d hab
  have a2 := congrArg E4.a hac; have b2 := congrArg E4.b hac
  have c2 := congrArg E4.c hac; have d2 := congrArg E4.d hac
  have a3 := congrArg E4.a hbc; have b3 := congrArg E4.b hbc
  have c3 := congrArg E4.c hbc; have d3 := congrArg E4.d hbc
  simp only [sideE, wE, oneE, E4.mul] at a1 b1 c1 d1 a2 b2 c2 d2 a3 b3 c3 d3
  have e1 : na = 0 := by linarith
  have e2 : nb = 0 := by linarith
  have e3 : nc = 0 := by linarith
  have e4 : kb = ka := by linarith
  have e8 : ma = kc - kb := by linarith
  have e9 : mb = kc - kb := by linarith
  have e10 : mc = 2 * kb - kc := by linarith
  subst e1 e2 e3
  subst e4
  subst e8 e9 e10
  have hb := congrArg E4.b hH
  simp only [hhE, sideE, ofQ, E4.mul, E4.add, E4.smul, E4.sub] at hb
  have hq : (2 * kb ^ 2 - 4 * kb * kc + kc ^ 2) * (2 * kb ^ 2 - 2 * kb * kc + kc ^ 2) = 0 := by
    linear_combination (-1) * hb
  have hk : kb = 0 ∧ kc = 0 := by
    rcases mul_eq_zero.1 hq with h | h
    · have hkb : kb = 0 := sq_eq_two_sq (x := kc - 2 * kb) (y := kb) (by linarith [h])
      refine ⟨hkb, ?_⟩
      subst hkb
      nlinarith
    · constructor <;> nlinarith [sq_nonneg kb, sq_nonneg (kb - kc)]
  obtain ⟨h1', h2'⟩ := hk
  subst h1' h2'
  simp at hpos

end Erdos634.Lacz53
