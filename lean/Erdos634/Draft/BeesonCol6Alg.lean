import Mathlib
import Erdos634.Draft.BeesonT4M1

/-!
# Beeson (arXiv 1206.2229 v4) Lemma 28 (the quantity kappa) and Lemma 48 (scaling by kappa)

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Theorem 4 table, Lemma 28, Lemma 48), Beeson-Rosu, Laczkovich,
Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.

* `lemma28_*`: for `0 < s < 1`, `Lambda ≠ 0` and the printed rows `(M1, M2)` of Theorem 4 (taken as hypotheses: they are
  the colouring integers of the tiling, obtained elsewhere), `kappa = (M1+M2)/(M2-M1)` equals `-s`, `s`, `s/(2-s^2)`,
  `s/(2-s^2)` for the shapes `(beta,3alpha,beta)`, `(alpha+beta,alpha,alpha+beta)`, `(alpha,alpha+2beta,alpha)`,
  `(2alpha,alpha,2beta)`; `M1 = M2` for `(2alpha,beta,alpha+beta)`; and `0 < kappa < 1`, `s = kappa (2-s^2)`, the quartic.
  `lemma28_rows_agree`: the proof's derivation from `M1 (a+b+c) = M2 (a-b-c)` with `a:b:c = s : 1-s^2 : 1`.
* `lemma48`: the tile scaled by `kappa` (`a = kappa sin alpha`, ...): the four printed formulas, with `s = 2 sin (alpha/2)`.
-/

namespace Erdos634.BeesonCol6

/-- the quantity `kappa` of Definition 8. -/
noncomputable def kap (M1 M2 : ℝ) : ℝ := (M1 + M2) / (M2 - M1)

theorem kap_eq {M1 M2 k : ℝ} (hne : M2 - M1 ≠ 0) (h : M1 + M2 = k * (M2 - M1)) : kap M1 M2 = k := by
  unfold kap; rw [div_eq_iff hne]; exact h

/-- shape `(2alpha,beta,alpha+beta)`: `M1 = M2`, `kappa` undefined (division by zero). -/
theorem lemma28_shape1 {Λ s : ℝ} : (Λ * s) - Λ * s = 0 := sub_self _

/-- shape `(beta,3alpha,beta)`: `kappa = -s`. -/
theorem lemma28_shape2 {Λ s : ℝ} (hΛ : Λ ≠ 0) (h0 : 0 < s) (h1 : s < 1) :
    (-Λ * (1 - s) ^ 2 * (1 + s)) - Λ * (1 - s) * (1 + s) ^ 2 ≠ 0 ∧
    kap (Λ * (1 - s) * (1 + s) ^ 2) (-Λ * (1 - s) ^ 2 * (1 + s)) = -s := by
  have a : (1 - s) ≠ 0 := by intro h; linarith
  have b : (1 + s) ≠ 0 := by intro h; linarith
  have hne : (-Λ * (1 - s) ^ 2 * (1 + s)) - Λ * (1 - s) * (1 + s) ^ 2 ≠ 0 := by
    have : (-Λ * (1 - s) ^ 2 * (1 + s)) - Λ * (1 - s) * (1 + s) ^ 2 = -2 * Λ * (1 - s) * (1 + s) := by ring
    rw [this]; simp [hΛ, a, b]
  exact ⟨hne, kap_eq hne (by ring)⟩

/-- shape `(alpha+beta,alpha,alpha+beta)`: `kappa = s`. -/
theorem lemma28_shape3 {Λ s : ℝ} (hΛ : Λ ≠ 0) (h0 : 0 < s) (h1 : s < 1) :
    (-Λ / (1 - s)) - Λ / (1 + s) ≠ 0 ∧ kap (Λ / (1 + s)) (-Λ / (1 - s)) = s := by
  have a : (1 - s) ≠ 0 := by intro h; linarith
  have b : (1 + s) ≠ 0 := by intro h; linarith
  have hne : (-Λ / (1 - s)) - Λ / (1 + s) ≠ 0 := by
    have : (-Λ / (1 - s)) - Λ / (1 + s) = -2 * Λ / ((1 - s) * (1 + s)) := by field_simp; ring
    rw [this]; simp [hΛ, a, b]
  exact ⟨hne, kap_eq hne (by field_simp; ring)⟩

/-- shape `(alpha,alpha+2beta,alpha)`: `kappa = s/(2-s^2)`. -/
theorem lemma28_shape4 {Λ s : ℝ} (hΛ : Λ ≠ 0) (h0 : 0 < s) (h1 : s < 1) :
    (-Λ * s * (2 - s) / (1 - s)) - Λ * s * (2 + s) / (1 + s) ≠ 0 ∧
    kap (Λ * s * (2 + s) / (1 + s)) (-Λ * s * (2 - s) / (1 - s)) = s / (2 - s ^ 2) := by
  have a : (1 - s) ≠ 0 := by intro h; linarith
  have b : (1 + s) ≠ 0 := by intro h; linarith
  have c : (2 - s ^ 2) ≠ 0 := by intro h; nlinarith
  have hne : (-Λ * s * (2 - s) / (1 - s)) - Λ * s * (2 + s) / (1 + s) ≠ 0 := by
    have : (-Λ * s * (2 - s) / (1 - s)) - Λ * s * (2 + s) / (1 + s)
        = -2 * Λ * s * (2 - s ^ 2) / ((1 - s) * (1 + s)) := by field_simp; ring
    rw [this]; simp [hΛ, h0.ne', a, b, c]
  exact ⟨hne, kap_eq hne (by field_simp; ring)⟩

/-- shape `(2alpha,alpha,2beta)`: `kappa = s/(2-s^2)`. -/
theorem lemma28_shape5 {Λ s : ℝ} (hΛ : Λ ≠ 0) (h0 : 0 < s) (h1 : s < 1) :
    (-Λ * s * (2 - s) * (1 + s)) - Λ * s * (1 - s) * (2 + s) ≠ 0 ∧
    kap (Λ * s * (1 - s) * (2 + s)) (-Λ * s * (2 - s) * (1 + s)) = s / (2 - s ^ 2) := by
  have c : (2 - s ^ 2) ≠ 0 := by intro h; nlinarith
  have hne : (-Λ * s * (2 - s) * (1 + s)) - Λ * s * (1 - s) * (2 + s) ≠ 0 := by
    have : (-Λ * s * (2 - s) * (1 + s)) - Λ * s * (1 - s) * (2 + s) = -2 * Λ * s * (2 - s ^ 2) := by ring
    rw [this]; simp [hΛ, h0.ne', c]
  exact ⟨hne, kap_eq hne (by field_simp; ring)⟩

/-- the last two shapes: the printed consequences of `kappa = s/(2-s^2)`. -/
theorem lemma28_props {s κ : ℝ} (h0 : 0 < s) (h1 : s < 1) (hκ : κ = s / (2 - s ^ 2)) :
    0 < κ ∧ κ < 1 ∧ s = κ * (2 - s ^ 2) ∧ κ ^ 2 * s ^ 4 - (4 * κ ^ 2 + 1) * s ^ 2 + 4 * κ ^ 2 = 0 := by
  have c : (0 : ℝ) < 2 - s ^ 2 := by nlinarith
  have e : s = κ * (2 - s ^ 2) := by rw [hκ]; field_simp
  refine ⟨by rw [hκ]; positivity, ?_, e, ?_⟩
  · rw [hκ, div_lt_one c]; nlinarith
  · have : (κ * (2 - s ^ 2)) ^ 2 = s ^ 2 := by rw [← e]
    linear_combination this

/-- derivation inside the printed proof: the two flux rows agree, `M1 (a+b+c) = M2 (a-b-c)` with `a:b:c = s : 1-s^2 : 1`. -/
theorem lemma28_rows_agree {M1 M2 s : ℝ} (hM1 : M1 ≠ 0) (h0 : 0 < s) (h1 : s < 1)
    (h : M1 * (s + (1 - s ^ 2) + 1) = M2 * (s - (1 - s ^ 2) - 1)) :
    M2 - M1 ≠ 0 ∧ kap M1 M2 = s / (2 - s ^ 2) := by
  have a : (1 - s) ≠ 0 := by intro h; linarith
  have b : (2 + s) ≠ 0 := by intro h; linarith
  have c : (2 - s ^ 2) ≠ 0 := by intro h; nlinarith
  have hM2 : M2 = -M1 * ((2 - s) * (1 + s)) / ((2 + s) * (1 - s)) := by
    field_simp; linear_combination h
  have hne : M2 - M1 ≠ 0 := by
    have : M2 - M1 = -2 * M1 * (2 - s ^ 2) / ((2 + s) * (1 - s)) := by rw [hM2]; field_simp; ring
    rw [this]; simp [hM1, a, b, c]
  exact ⟨hne, kap_eq hne (by rw [hM2]; field_simp; ring)⟩

open Erdos634.BeesonColoring in
/-- **Lemma 48.**  `3 alpha + 2 beta = pi`, the tile `(a,b,c) = kappa (sin alpha, sin beta, sin gamma)`, `gamma = 2 alpha + beta`,
`s = 2 sin (alpha/2)`: the four printed formulas. -/
theorem lemma48 {α β κ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (hα : 0 < α) (hβ : 0 < β) (hκ : κ ≠ 0)
    (ha : a = κ * Real.sin α) (hb : b = κ * Real.sin β) (hc : c = κ * Real.sin (2 * α + β)) :
    κ * Real.sin (2 * α) / c = (2 * Real.sin (α / 2)) * (2 - (2 * Real.sin (α / 2)) ^ 2) ∧
    Real.sin (2 * α) = (2 - (2 * Real.sin (α / 2)) ^ 2) * Real.sin α ∧
    κ * Real.sin (2 * β) / c = (2 * Real.sin (α / 2)) * (1 + 2 * Real.sin (α / 2)) * (1 - 2 * Real.sin (α / 2)) *
      (3 - (2 * Real.sin (α / 2)) ^ 2) ∧
    κ * Real.sin (3 * α) / c = (2 * Real.sin (α / 2)) * (1 + 2 * Real.sin (α / 2)) * (1 - 2 * Real.sin (α / 2)) *
      (3 - (2 * Real.sin (α / 2)) ^ 2) := by
  obtain ⟨s, hs0, hs1, sA, sB, sG, s2A, sAB, s3A, s2B⟩ := sin_table hrel hα hβ
  have hpi := Real.pi_pos
  have hsδ : 0 < Real.sin (α + β) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hδ : α + β = Real.pi / 2 - α / 2 := by linarith
  have hcos : Real.sin (α + β) = Real.cos (α / 2) := by rw [hδ, Real.sin_pi_div_two_sub]
  have hsα : Real.sin α = 2 * Real.sin (α / 2) * Real.cos (α / 2) := by
    have := Real.sin_two_mul (α / 2); rwa [show 2 * (α / 2) = α by ring] at this
  have hs : s = 2 * Real.sin (α / 2) := by
    have h1 : s * Real.sin (α + β) = 2 * Real.sin (α / 2) * Real.sin (α + β) := by
      rw [← sA, hsα, hcos]
    exact mul_right_cancel₀ hsδ.ne' h1
  rw [hc, sG]
  have hne : κ * Real.sin (α + β) ≠ 0 := mul_ne_zero hκ hsδ.ne'
  rw [← hs]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [s2A]; field_simp
  · rw [s2A, sA]; ring
  · rw [s2B]; field_simp; ring
  · rw [s3A]; field_simp; ring

/-- non-vacuity of `lemma28_rows_agree` (s = 1/2, M1 = 5, M2 = -9) and of `lemma48` (alpha = beta = pi/5, kappa = 1). -/
theorem lemma28_rows_wit : ∃ M1 M2 s : ℝ, M1 ≠ 0 ∧ 0 < s ∧ s < 1 ∧
    M1 * (s + (1 - s ^ 2) + 1) = M2 * (s - (1 - s ^ 2) - 1) :=
  ⟨5, -9, 1 / 2, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem lemma48_wit :
    (1 : ℝ) * Real.sin (2 * (Real.pi / 5)) / (1 * Real.sin (2 * (Real.pi / 5) + Real.pi / 5)) =
      (2 * Real.sin ((Real.pi / 5) / 2)) * (2 - (2 * Real.sin ((Real.pi / 5) / 2)) ^ 2) :=
  (lemma48 (α := Real.pi / 5) (β := Real.pi / 5) (κ := 1) (a := Real.sin (Real.pi / 5)) (b := Real.sin (Real.pi / 5))
    (c := 1 * Real.sin (2 * (Real.pi / 5) + Real.pi / 5)) (by ring) (by positivity) (by positivity) one_ne_zero
    (by simp) (by simp) rfl).1

end Erdos634.BeesonCol6

#print axioms Erdos634.BeesonCol6.lemma28_shape2
#print axioms Erdos634.BeesonCol6.lemma28_shape3
#print axioms Erdos634.BeesonCol6.lemma28_shape4
#print axioms Erdos634.BeesonCol6.lemma28_shape5
#print axioms Erdos634.BeesonCol6.lemma28_props
#print axioms Erdos634.BeesonCol6.lemma28_rows_agree
#print axioms Erdos634.BeesonCol6.lemma48
