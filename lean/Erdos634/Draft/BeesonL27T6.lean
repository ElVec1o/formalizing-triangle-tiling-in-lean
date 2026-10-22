import Erdos634.Draft.BeesonT4Final
import Erdos634.ARAGeom

/-!
# Beeson (arXiv 1206.2229v4) Lemma 27 (the area table) and Theorem 6

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Lemma 27, Thm 6), Laczkovich (DCG 48 (2012)),
Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.

`lemma27`: with `Lambda = circD target / circD model` and `s = a / c`, an `N`-tiling of a target of each of the five
shapes of Lemma 11 gives `N = Lambda^2 * R(s)`, `R` the printed table (the last printed entry reads
`s^2 (2-s^2)(3-s^2)`; the exponent is garbled in the text extraction, checked by the printed 77-tiling:
`77/64 = (1/4)(7/4)(11/4)`).  Proof: `ARAGeom.area_heron` (Heron form of the area relation) and the law of sines; it does
not use (H1).  `t6`: Theorem 6 for the shapes `(alpha, alpha+2beta, alpha)` and `(2alpha, alpha, 2beta)` (target vertices
`0,1,2` = `(alpha, alpha, alpha+2beta)` and `(2alpha, alpha, 2beta)`): `N + M1 M2 != 0`, the printed formula for `s^2`,
and `s` rational (via Lemma 28, `s = kappa (2 - s^2)`).  (H1) `alpha notin Q*pi` is used through `t4_final`.
-/

open scoped Classical

namespace Erdos634.BeesonColoring

open Erdos634.Geometry Erdos634.Geometry.A1Field

variable {N : ℕ}

theorem lem27_core {N Λ c s : ℝ} (hΛ : 0 < Λ) (hs0 : 0 < s) (hs1 : s < 1) (hc : 0 < c) (hN : 0 ≤ N)
    (x y z Den Num : ℝ) (hDen : 0 < Den) (hNum : 0 ≤ Num)
    (hA : N ^ 2 * Erdos634.ARA.Hh (s * c) ((1 - s ^ 2) * c) c
      = Erdos634.ARA.Hh (Λ * c * x) (Λ * c * y) (Λ * c * z))
    (hid : Erdos634.ARA.Hh x y z * Den ^ 2 = Num ^ 2 * (s ^ 2 * (1 - s ^ 2) ^ 2 * (4 - s ^ 2))) :
    N * Den = Λ ^ 2 * Num := by
  have hM : 0 < c ^ 4 * (s ^ 2 * (1 - s ^ 2) ^ 2 * (4 - s ^ 2)) := by
    have q : s ^ 2 < 1 := by nlinarith
    have : 0 < 1 - s ^ 2 := by linarith
    have : 0 < 4 - s ^ 2 := by linarith
    positivity
  have hsq : (N * Den) ^ 2 = (Λ ^ 2 * Num) ^ 2 := by
    refine mul_right_cancel₀ hM.ne' ?_
    unfold Erdos634.ARA.Hh at hA hid
    linear_combination Den ^ 2 * hA + (Λ * c) ^ 4 * hid
  exact (pow_left_inj₀ (mul_nonneg hN hDen.le) (by positivity) two_ne_zero).mp hsq

set_option maxHeartbeats 1000000 in
theorem lemma27 (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi) (h : D.model.ThreeAlphaData α β a b c) :
    ((D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = α + β) →
      (N : ℝ) = (circD D.target / circD D.model) ^ 2 * (2 - (a / c) ^ 2)) ∧
    ((D.target.angleAt 0 = β ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = 3 * α) →
      (N : ℝ) = (circD D.target / circD D.model) ^ 2 * ((1 - (a / c) ^ 2) ^ 2 * (3 - (a / c) ^ 2))) ∧
    ((D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α + β ∧ D.target.angleAt 2 = α) →
      (N : ℝ) = (circD D.target / circD D.model) ^ 2 * (1 / (1 - (a / c) ^ 2))) ∧
    ((D.target.angleAt 0 = α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + 2 * β) →
      (N : ℝ) = (circD D.target / circD D.model) ^ 2 *
        ((a / c) ^ 2 * (2 - (a / c) ^ 2) / (1 - (a / c) ^ 2))) ∧
    ((D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = 2 * β) →
      (N : ℝ) = (circD D.target / circD D.model) ^ 2 *
        ((a / c) ^ 2 * (2 - (a / c) ^ 2) * (3 - (a / c) ^ 2))) := by
  obtain ⟨ha, hb, hc, hαpos, hβpos⟩ := model_abc_pos h
  obtain ⟨s, hs0, hs1, sA, sB, sG, s2A, sAB, s3A, s2B⟩ := sin_table hrel hαpos hβpos
  have hsδ : 0 < Real.sin (α + β) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
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
  have hΛpos : 0 < Λ := div_pos (circD_pos _) hD
  have side : ∀ (k : Fin 3) (x : ℝ), Real.sin (D.target.angleAt k) = x * Real.sin (α + β) →
      D.target.oppLen k = Λ * c * x := by
    intro k x hx
    rw [oppLen_eq, hx, hDt, ec]; ring
  have hA0 := Erdos634.ARA.area_heron D
  have hHm : Erdos634.ARA.Hh (D.model.oppLen 0) (D.model.oppLen 1) (D.model.oppLen 2)
      = Erdos634.ARA.Hh a b c := by
    rw [← Erdos634.ARA.Hh_perm D.model σ, o0, o1, o2]
  rw [hHm, hcs, hbs] at hA0
  have q : s ^ 2 < 1 := by nlinarith
  have p1 : 0 < 1 - s ^ 2 := by linarith
  have p2 : 0 < 2 - s ^ 2 := by linarith
  have p3 : 0 < 3 - s ^ 2 := by linarith
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [hsa]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨e0, e1, e2⟩
    have hA := hA0
    rw [side 0 (s * (2 - s ^ 2)) (by rw [e0, s2A]), side 1 (1 - s ^ 2) (by rw [e1, sB]),
      side 2 1 (by rw [e2]; ring)] at hA
    have := lem27_core hΛpos hs0 hs1 hc hN _ _ _ 1 (2 - s ^ 2) one_pos p2.le hA
      (by unfold Erdos634.ARA.Hh; ring)
    linarith
  · rintro ⟨e0, e1, e2⟩
    have hA := hA0
    rw [side 0 (1 - s ^ 2) (by rw [e0, sB]), side 1 (1 - s ^ 2) (by rw [e1, sB]),
      side 2 (s * (1 - s ^ 2) * (3 - s ^ 2)) (by rw [e2, s3A])] at hA
    have := lem27_core hΛpos hs0 hs1 hc hN _ _ _ 1 ((1 - s ^ 2) ^ 2 * (3 - s ^ 2)) one_pos
      (by positivity) hA (by unfold Erdos634.ARA.Hh; ring)
    linarith
  · rintro ⟨e0, e1, e2⟩
    have hA := hA0
    rw [side 0 1 (by rw [e0]; ring), side 1 1 (by rw [e1]; ring),
      side 2 s (by rw [e2, sA])] at hA
    have := lem27_core hΛpos hs0 hs1 hc hN _ _ _ (1 - s ^ 2) 1 p1 zero_le_one hA
      (by unfold Erdos634.ARA.Hh; ring)
    rw [mul_one_div, eq_div_iff p1.ne']
    linarith
  · rintro ⟨e0, e1, e2⟩
    have hA := hA0
    rw [side 0 s (by rw [e0, sA]), side 1 s (by rw [e1, sA]),
      side 2 (s * (2 - s ^ 2)) (by rw [e2, sAB])] at hA
    have := lem27_core hΛpos hs0 hs1 hc hN _ _ _ (1 - s ^ 2) (s ^ 2 * (2 - s ^ 2)) p1
      (by positivity) hA (by unfold Erdos634.ARA.Hh; ring)
    field_simp
    linarith
  · rintro ⟨e0, e1, e2⟩
    have hA := hA0
    rw [side 0 (s * (2 - s ^ 2)) (by rw [e0, s2A]), side 1 s (by rw [e1, sA]),
      side 2 (s * (1 - s ^ 2) * (3 - s ^ 2)) (by rw [e2, s2B])] at hA
    have := lem27_core hΛpos hs0 hs1 hc hN _ _ _ 1 (s ^ 2 * (2 - s ^ 2) * (3 - s ^ 2)) one_pos
      (by positivity) hA (by unfold Erdos634.ARA.Hh; ring)
    linarith

end Erdos634.BeesonColoring

#print axioms Erdos634.BeesonColoring.lemma27
