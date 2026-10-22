import Erdos634.Draft.BeesonT24General

/-!
# Beeson Theorem 24 (arXiv 1206.2229v4, p. 88): the existential step, unconditional statement

Beeson: for a tile `(a,b,c)` with `3 alpha + 2 beta = pi` (`c | a^2`, i.e. `a^2 + c b = c^2`), `gcd(a,b) = 1`
and `a^2 c < b (a^2 + b^2)`, for some `N` some isosceles triangle with base angles `alpha + beta` is `N`-tiled.
Beeson's choice: `M = lam a b c`, `p = a c rho`, an integer `rho` in an interval of length growing with `lam`
(`lam` large), then `h >= ab` is `x a + y b` (coin problem).  Here: `lam = c^2 (a(b+1) + D) + 1`
(`D = c (a^2+b^2)`), `rho = floor((lam a^3 (a+c) + a(b+1)) / D) + 1`, and `h - a >= ab` is `x' a + y b` by
Mathlib's `Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le`; `X = x' + 1 >= 1`, so the hypothesis `X >= 1` of
`beeson_thm24` is met (Beeson allows `x = 0`; this is a harmless strengthening: `h >= ab + a`, and `r > 0` strict).
Credit Beeson (arXiv 1206.2229), Beeson-Zhang, Zhang, Laczkovich.  UNAUDITED.
-/

namespace Erdos634.BeesonT24Exists

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.ZhangPara Erdos634.ZhangSporadic Erdos634.BeesonT14Chart Erdos634.BeesonT14Abs
  Erdos634.BeesonT14Piece Erdos634.BeesonT14Gen Erdos634.BeesonT14General Erdos634.BeesonT24Gen
  Erdos634.BeesonT24General

theorem choose_params (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (h : a * a + c * b = c * c)
    (hg : Nat.gcd a b = 1) (hlt : a * a * c < b * (a * a + b * b)) :
    ∃ lam rho X Y : ℕ, 0 < lam ∧ 0 < rho ∧ 1 ≤ X ∧ c * c * rho < lam * a * b * (a + c) ∧
      lam * a ^ 3 * (a + c) < rho * c * (a * a + b * b) ∧
      X * a + Y * b + lam * a ^ 3 * (a + c) = rho * c * (a * a + b * b) := by
  have hc : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0; simp at h; omega
    · exact h0
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_lt hlt
  set D := c * (a * a + b * b) with hD
  have hDpos : 0 < D := by positivity
  set lam := c * c * (a * (b + 1) + D) + 1 with hlam
  set Nn := lam * a ^ 3 * (a + c) + a * (b + 1) with hNn
  set rho := Nn / D + 1 with hrho
  have h1 : Nn < rho * D := by
    have := Nat.lt_mul_div_succ Nn hDpos
    rw [hrho, mul_comm]; exact this
  have h2 : rho * D ≤ Nn + D := by
    have := Nat.div_mul_le_self Nn D
    rw [hrho]; nlinarith
  have hlampos : 0 < lam := by omega
  -- r > 0
  have hr : c * c * rho < lam * a * b * (a + c) := by
    have hQ : 0 < a * (a + c) * c := by positivity
    have key : c * c * (rho * D) < lam * a * b * (a + c) * D := by
      have l1 : c * c * (rho * D) ≤ c * c * (Nn + D) := Nat.mul_le_mul_left _ h2
      have l2 : c * c * (Nn + D) = a * (a + c) * c * lam * (a * a * c) + c * c * (a * (b + 1) + D) := by
        rw [hNn]; ring
      have l3 : lam * a * b * (a + c) * D = a * (a + c) * c * lam * (a * a * c + e + 1) := by
        rw [hD]
        have : lam * a * b * (a + c) * (c * (a * a + b * b)) = a * (a + c) * c * lam * (b * (a * a + b * b)) := by ring
        rw [this, he]
      have l4 : c * c * (a * (b + 1) + D) < lam := by omega
      have l5 : lam ≤ a * (a + c) * c * lam * (e + 1) := by
        have : 1 ≤ a * (a + c) * c * (e + 1) := Nat.mul_pos hQ (by omega)
        nlinarith
      have l6 : a * (a + c) * c * lam * (a * a * c + e + 1) =
          a * (a + c) * c * lam * (a * a * c) + a * (a + c) * c * lam * (e + 1) := by ring
      omega
    exact lt_of_mul_lt_mul_right (by simpa [mul_comm, mul_assoc, mul_left_comm] using key) (Nat.zero_le D)
  have hh : lam * a ^ 3 * (a + c) + a * (b + 1) ≤ rho * c * (a * a + b * b) := by
    have : rho * D = rho * c * (a * a + b * b) := by rw [hD]; ring
    omega
  obtain ⟨H, hH⟩ := Nat.exists_eq_add_of_le hh
  have hHge : a * (b + 1) ≤ H + a * (b + 1) := by omega
  -- coin problem for H' = H + a*b  (H' = h - a, with h = lam..+ a(b+1) + H - lam.. )
  have hcoin : ∃ x y : ℕ, x * a + y * b = H + a * b := by
    apply Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le a b (H + a * b)
    · rw [hg]; exact one_dvd _
    · have : a.pred * b.pred ≤ a * b := Nat.mul_le_mul (Nat.pred_le _) (Nat.pred_le _)
      omega
  obtain ⟨x, y, hxy⟩ := hcoin
  have hapos : 0 < a * (b + 1) := Nat.mul_pos ha (Nat.succ_pos b)
  refine ⟨lam, rho, x + 1, y, hlampos, by rw [hrho]; exact Nat.succ_pos _, Nat.le_add_left 1 x, hr, ?_, ?_⟩
  · linarith [hH, hapos]
  · have e1 : (x + 1) * a = x * a + a := by ring
    have e2 : a * (b + 1) = a * b + a := by ring
    linarith [hH, hxy, e1, e2]

set_option maxHeartbeats 16000000 in
/-- Beeson Thm 24 as printed (existential form): a tile `(a,b,c)` with `a^2 + c b = c^2`, `gcd(a,b) = 1`,
`a^2 c < b(a^2+b^2)`: for some `lam, n` an isosceles triangle with squared sides `(mu a)^2, (mu c)^2, (mu c)^2`
(`mu = lam a b (a+c)`; base angles `alpha + beta`) is `Dis`-dissected into `n` copies of the tile `(c,b,a)`. -/
theorem beeson_thm24_exists (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (h : a * a + c * b = c * c)
    (hg : Nat.gcd a b = 1) (hlt : a * a * c < b * (a * a + b * b)) :
    ∃ (lam n : ℕ) (T : Tri) (x0 y0 x1 y1 x2 y2 : ℝ) (_ : 0 < det3 x0 y0 x1 y1 x2 y2), 0 < lam ∧
      dist (T.pts 0) (T.pts 1) ^ 2 = (c : ℝ) ^ 2 ∧ dist (T.pts 0) (T.pts 2) ^ 2 = (b : ℝ) ^ 2 ∧
      dist (T.pts 1) (T.pts 2) ^ 2 = (a : ℝ) ^ 2 ∧
      (x1 - x0) ^ 2 + (y1 - y0) ^ 2 = ((lam * a * b * (a + c) * a : ℕ) : ℝ) ^ 2 ∧
      (x2 - x0) ^ 2 + (y2 - y0) ^ 2 = ((lam * a * b * (a + c) * c : ℕ) : ℝ) ^ 2 ∧
      (x2 - x1) ^ 2 + (y2 - y1) ^ 2 = ((lam * a * b * (a + c) * c : ℕ) : ℝ) ^ 2 ∧
      Dis T (TriSet x0 y0 x1 y1 x2 y2) n := by
  obtain ⟨lam, rho, X, Y, hl, hρ, hX, hr, hh, hxy⟩ := choose_params a b c ha hb h hg hlt
  obtain ⟨T, x0, y0, x1, y1, x2, y2, hd, h1, h2, h3, h4, h5, h6, hD⟩ :=
    beeson_thm24 a b c lam rho X Y ha hb hl hρ hX h hr hh hxy
  exact ⟨lam, _, T, x0, y0, x1, y1, x2, y2, hd, hl, h1, h2, h3, h4, h5, h6, hD⟩

/-- Hypothesis witnesses (all three hypotheses of `beeson_thm24_exists` hold): `(2,3,4)`, `(3,8,9)`, `(4,15,16)`.
For Beeson's example `(12,7,16)` the inequality fails (`2304 > 1351`), consistent with his remark. -/
theorem hyp_witnesses :
    (2 * 2 + 4 * 3 = 4 * 4 ∧ Nat.gcd 2 3 = 1 ∧ 2 * 2 * 4 < 3 * (2 * 2 + 3 * 3)) ∧
    (3 * 3 + 9 * 8 = 9 * 9 ∧ Nat.gcd 3 8 = 1 ∧ 3 * 3 * 9 < 8 * (3 * 3 + 8 * 8)) ∧
    (4 * 4 + 16 * 15 = 16 * 16 ∧ Nat.gcd 4 15 = 1 ∧ 4 * 4 * 16 < 15 * (4 * 4 + 15 * 15)) := by
  norm_num


#print axioms beeson_thm24_exists

end Erdos634.BeesonT24Exists
