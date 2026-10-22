import Erdos634.Draft.BeesonT4M1
import Erdos634.ARAGeom

/-!
# Beeson (arXiv 1206.2229v4) Theorem 25 (i), the isosceles-alpha tiling equation

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Thm 25, Lemma 24), Laczkovich (DCG 48 (2012)),
Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.

Printed Theorem 25 (i): `3 alpha + 2 beta = pi`, ABC isosceles with base angles `alpha`, `N`-tiled, `s = a/c`, `M` the
coloring number.  Then `M^2 <= 2 N` and `N = M^2 (1+s)(2-s^2) / ((1-s)(2+s)^2)`.  Formalized as
`t25_i` (in the cleared-denominator form `N (1-s)(2+s)^2 = M^2 (1+s)(2-s^2)`; `M` is the `thm1` flux integer, the
blacks-minus-whites count by `thm1_colouring`), via the area relation `ARAGeom.area_heron` (sides `Lambda c * (s, s, s(2-s^2))`).
NOT formalized: Theorem 25 (ii) (integer sides `(mk, k^2-m^2, k^2)`, `2k+m | M`, `N(k-m) = j^2 (m+k)(2k^2-m^2)`): it needs
the coprimality argument modulo `2k+m` (the case `2 | gcd`), not in Lean.
Project hypothesis (H1) `alpha not in Q * pi` replaces Beeson's Lemma 1 (Laczkovich 5.1, 5.3; not in Lean).
Vertex order as in `thm1`: angles `(alpha, alpha, alpha+2beta)` at target vertices `0, 1, 2`.
-/

open scoped Classical

namespace Erdos634.BeesonColoring

open Erdos634.Geometry

variable {N : ℕ}

theorem aux_s {s : ℝ} (h0 : 0 < s) (h1 : s < 1) :
    s ^ 2 < 1 ∧ 0 < 2 - s ^ 2 ∧ 0 < 4 - s ^ 2 ∧ (1 - s) * (2 + s) ^ 2 ≤ 2 * ((1 + s) * (2 - s ^ 2)) := by
  have q : s ^ 2 < 1 := by nlinarith
  refine ⟨q, by linarith, by linarith, by nlinarith [mul_pos h0 h0, mul_pos h0 (mul_pos h0 h0)]⟩

open Erdos634.Geometry.A1Field in
theorem t25_i (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (e0 : D.target.angleAt 0 = α) (e1 : D.target.angleAt 1 = α)
    (e2 : D.target.angleAt 2 = α + 2 * β) :
    ∃ M : ℤ, 0 < M ∧ 0 < a / c ∧ a / c < 1 ∧
      (N : ℝ) * ((1 - a / c) * (2 + a / c) ^ 2) = (M : ℝ) ^ 2 * ((1 + a / c) * (2 - (a / c) ^ 2)) ∧
      (M : ℝ) ^ 2 ≤ 2 * N := by
  obtain ⟨ha, hb, hc, hαpos, hβpos⟩ := model_abc_pos h
  obtain ⟨s, hs0, hs1, sA, sB, sG, s2A, sAB, s3A, s2B⟩ := sin_table hrel hαpos hβpos
  have hsδ : 0 < Real.sin (α + β) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  -- model sides from the law of sines
  have hfull := h
  have hfull := h
  obtain ⟨σ, h0, o0, h1', o1, h2', o2⟩ := h
  have ea : a = circD D.model * Real.sin α := by rw [← o0, oppLen_eq, h0]
  have eb : b = circD D.model * Real.sin β := by rw [← o1, oppLen_eq, h1']
  have ec : c = circD D.model * Real.sin (α + β) := by rw [← o2, oppLen_eq, h2', sG]
  have hD : 0 < circD D.model := circD_pos _
  have hDne := hD.ne'
  have hsδne := hsδ.ne'
  have hsa : a / c = s := by rw [ea, ec, sA]; field_simp
  have hcs : a = s * c := by rw [← hsa]; field_simp
  have hbs : b = (1 - s ^ 2) * c := by rw [eb, ec, sB]; ring
  have hDt : circD D.target = (circD D.target / circD D.model) * circD D.model := by field_simp
  set Λ := circD D.target / circD D.model with hΛ
  have hsum : a + b + c = c * ((2 - s) * (1 + s)) := by rw [hcs, hbs]; ring
  have hpos : 0 < c * ((2 - s) * (1 + s)) := mul_pos hc (mul_pos (by linarith) (by linarith))
  -- target sides: X_k = Λ * c * (poly) given the angle
  have side : ∀ (k : Fin 3) (x : ℝ), Real.sin (D.target.angleAt k) = x * Real.sin (α + β) →
      D.target.oppLen k = Λ * c * x := by
    intro k x hx
    rw [oppLen_eq, hx, hDt, ec]; ring
  rw [hsa]
  obtain ⟨M, hMp, hM⟩ := (thm1 D hα hrel hfull).1 ⟨e0, e1, e2⟩
  have h1 : 0 < 1 - s := by linarith
  have h2 : 0 < 1 + s := by linarith
  have hΛpos : 0 < Λ := div_pos (circD_pos _) hD
  rw [side 0 s (by rw [e0, sA]), side 1 s (by rw [e1, sA]),
    side 2 (s * (2 - s ^ 2)) (by rw [e2, sAB]), hsum] at hM
  have hM' : (M : ℝ) = Λ * (s * (2 + s) / (1 + s)) := by
    refine mul_right_cancel₀ hpos.ne' (hM.trans ?_)
    field_simp
    ring
  -- area
  have hA := Erdos634.ARA.area_heron D
  have hHm : Erdos634.ARA.Hh (D.model.oppLen 0) (D.model.oppLen 1) (D.model.oppLen 2)
      = Erdos634.ARA.Hh a b c := by
    rw [← Erdos634.ARA.Hh_perm D.model σ, o0, o1, o2]
  rw [hHm, side 0 s (by rw [e0, sA]), side 1 s (by rw [e1, sA]),
    side 2 (s * (2 - s ^ 2)) (by rw [e2, sAB]), hcs, hbs] at hA
  unfold Erdos634.ARA.Hh at hA
  obtain ⟨q1, q2, q3, q4⟩ := aux_s hs0 hs1
  have hc4 : 0 < c ^ 4 * s ^ 2 * (4 - s ^ 2) := by positivity
  have hsq : ((N : ℝ) * (1 - s ^ 2)) ^ 2 = (Λ ^ 2 * s ^ 2 * (2 - s ^ 2)) ^ 2 := by
    refine mul_right_cancel₀ hc4.ne' ?_
    linear_combination hA
  have hN1 : (N : ℝ) * (1 - s ^ 2) = Λ ^ 2 * s ^ 2 * (2 - s ^ 2) := by
    have hl : 0 ≤ (N : ℝ) * (1 - s ^ 2) := mul_nonneg (Nat.cast_nonneg N) (by linarith)
    have hr : 0 ≤ Λ ^ 2 * s ^ 2 * (2 - s ^ 2) := by positivity
    exact (pow_left_inj₀ hl hr two_ne_zero).mp hsq
  have heq : (N : ℝ) * ((1 - s) * (2 + s) ^ 2) = (M : ℝ) ^ 2 * ((1 + s) * (2 - s ^ 2)) := by
    rw [hM']
    have : (N : ℝ) = Λ ^ 2 * s ^ 2 * (2 - s ^ 2) / (1 - s ^ 2) := by
      rw [eq_div_iff (by linarith)]
      exact hN1
    rw [this]
    have n1 : 1 - s ≠ 0 := h1.ne'
    have n2 : 1 + s ≠ 0 := h2.ne'
    have n3 : 1 - s ^ 2 ≠ 0 := (by linarith : (0:ℝ) < 1 - s ^ 2).ne'
    field_simp
    ring
  refine ⟨M, hMp, hs0, hs1, heq, ?_⟩
  have hd := q4
  have hpp : 0 < (1 - s) * (2 + s) ^ 2 := by positivity
  have hM2 : (0 : ℝ) ≤ (M : ℝ) ^ 2 := sq_nonneg _
  refine le_of_mul_le_mul_right ?_ hpp
  calc (M : ℝ) ^ 2 * ((1 - s) * (2 + s) ^ 2) ≤ (M : ℝ) ^ 2 * (2 * ((1 + s) * (2 - s ^ 2))) :=
        mul_le_mul_of_nonneg_left hd hM2
    _ = 2 * ((M : ℝ) ^ 2 * ((1 + s) * (2 - s ^ 2))) := by ring
    _ = 2 * N * ((1 - s) * (2 + s) ^ 2) := by rw [← heq]; ring

end Erdos634.BeesonColoring

#print axioms Erdos634.BeesonColoring.t25_i
