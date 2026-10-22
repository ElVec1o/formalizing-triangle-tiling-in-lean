-- Draft/LaczFormalCombi3c.lean -- Laczkovich, DCG 48 (2012), Lemma 3.8, the cases s/m = 3/5, 4/5, 4/7 (alpha = 3 pi/10, 2 pi/5,
-- 2 pi/7): the arithmetic part of the proof, complete (core `lem38_sub` + degree fact `sin_not_ratfn`, no tiling).
-- Conclusion in each case: z = w = 0 and one side is an integer multiple of sin alpha, the other of cos alpha.
-- NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Comput. Geom. 48 (2012) 330-372, Lemma 3.8; Combinatorica 10 (1990)), Beeson, Beeson-Zhang.
import Mathlib
import Erdos634.Draft.LaczFormalCombi3b

open scoped Classical
open Polynomial IntermediateField

namespace Erdos634.Laczkovich.Combi3

theorem sin_pos_lt {θ : ℝ} (h0 : 0 < θ) (h1 : θ < Real.pi / 2) : 0 < Real.sin θ :=
  Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])

theorem cos_pos_lt {θ : ℝ} (h0 : 0 < θ) (h1 : θ < Real.pi / 2) : 0 < Real.cos θ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩

private theorem irr5 : Irrational (Real.sqrt 5) := by
  have := (Nat.Prime.irrational_sqrt (p := 5) (by norm_num)); simpa using this

theorem cos_pi5_irr : Irrational (Real.cos (Real.pi / 5)) := by
  rw [Real.cos_pi_div_five]
  have := ((irr5.natCast_add 1).div_natCast (m := 4) (by norm_num))
  simpa using this

theorem cos_2pi5_irr : Irrational (Real.cos (2 * Real.pi / 5)) := by
  have e : Real.cos (2 * Real.pi / 5) = (Real.sqrt 5 - 1) / 4 := by
    have h2 : 2 * Real.pi / 5 = 2 * (Real.pi / 5) := by ring
    rw [h2, Real.cos_two_mul, Real.cos_pi_div_five]
    have : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
    nlinarith [this]
  rw [e]
  have := ((irr5.sub_natCast 1).div_natCast (m := 4) (by norm_num))
  simpa using this

theorem cos_2pi7_irr : Irrational (Real.cos (2 * Real.pi / 7)) := by
  rintro ⟨q, hq⟩
  have hint : IsIntegral ℚ (Real.cos (2 * ((1 : ℕ) : ℝ) * Real.pi / ((7 : ℕ) : ℝ))) := by
    have e : (2 * ((1 : ℕ) : ℝ) * Real.pi / ((7 : ℕ) : ℝ)) = 2 * Real.pi / 7 := by push_cast; ring
    rw [e, ← hq]; exact isIntegral_algebraMap
  have hdeg : (minpoly ℚ (Real.cos (2 * ((1 : ℕ) : ℝ) * Real.pi / ((7 : ℕ) : ℝ)))).natDegree ≤ 2 := by
    have e : (2 * ((1 : ℕ) : ℝ) * Real.pi / ((7 : ℕ) : ℝ)) = 2 * Real.pi / 7 := by push_cast; ring
    rw [e, ← hq]
    have := minpoly.eq_X_sub_C ℝ q
    rw [show ((q : ℝ)) = algebraMap ℚ ℝ q from rfl, this]
    simp
  have := Erdos634.Draft.BeesonRow4A.lemma43_totient 1 7 (by norm_num) (by norm_num) hint hdeg
  revert this; decide +kernel

/-- the generic instance: `theta in (0, pi/2)` and the two hypotheses of `lem38_sub`. -/
theorem lem38_theta (θ : ℝ) (h0 : 0 < θ) (h1 : θ < Real.pi / 2) (hirr : Irrational (Real.cos θ))
    (hS : ¬ ∃ r q : ℚ[X], aeval (Real.cos θ) q ≠ 0 ∧ Real.sin θ * aeval (Real.cos θ) q = aeval (Real.cos θ) r)
    (x y z u v w t : ℕ) (ht : 0 < t)
    (h : ((x : ℝ) * Real.cos θ + y * Real.sin θ + z) * ((u : ℝ) * Real.cos θ + v * Real.sin θ + w)
        = (t / 2) * Real.cos θ * Real.sin θ) :
    (x = 0 ∧ z = 0 ∧ v = 0 ∧ w = 0) ∨ (y = 0 ∧ z = 0 ∧ u = 0 ∧ w = 0) :=
  lem38_sub _ _ (cos_pos_lt h0 h1) (sin_pos_lt h0 h1) (by rw [Real.sin_sq]) hirr hS x y z u v w t ht h

/-- **Lemma 3.8, case `s/m = 4/5` (`alpha = 2 pi/5`).** -/
theorem lem38_case45 (x y z u v w t : ℕ) (ht : 0 < t)
    (h : ((x : ℝ) * Real.cos (2 * Real.pi / 5) + y * Real.sin (2 * Real.pi / 5) + z) *
        ((u : ℝ) * Real.cos (2 * Real.pi / 5) + v * Real.sin (2 * Real.pi / 5) + w)
        = (t / 2) * Real.cos (2 * Real.pi / 5) * Real.sin (2 * Real.pi / 5)) :
    (x = 0 ∧ z = 0 ∧ v = 0 ∧ w = 0) ∨ (y = 0 ∧ z = 0 ∧ u = 0 ∧ w = 0) := by
  have e : (2 * ((1 : ℕ) : ℝ) * Real.pi / ((5 : ℕ) : ℝ)) = 2 * Real.pi / 5 := by push_cast; ring
  have hlt : 2 * Real.pi / 5 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hpos : 0 < 2 * Real.pi / 5 := by positivity
  refine lem38_theta _ hpos hlt cos_2pi5_irr ?_ x y z u v w t ht h
  have := sin_not_ratfn 1 5 5 (by norm_num) (by norm_num) (by norm_num) (by decide) (dvd_refl 5) (by decide +kernel)
    (by rw [e]; exact (sin_pos_lt hpos hlt).ne')
  rwa [e] at this

/-- **Lemma 3.8, case `s/m = 4/7` (`alpha = 2 pi/7`).** -/
theorem lem38_case47 (x y z u v w t : ℕ) (ht : 0 < t)
    (h : ((x : ℝ) * Real.cos (2 * Real.pi / 7) + y * Real.sin (2 * Real.pi / 7) + z) *
        ((u : ℝ) * Real.cos (2 * Real.pi / 7) + v * Real.sin (2 * Real.pi / 7) + w)
        = (t / 2) * Real.cos (2 * Real.pi / 7) * Real.sin (2 * Real.pi / 7)) :
    (x = 0 ∧ z = 0 ∧ v = 0 ∧ w = 0) ∨ (y = 0 ∧ z = 0 ∧ u = 0 ∧ w = 0) := by
  have e : (2 * ((1 : ℕ) : ℝ) * Real.pi / ((7 : ℕ) : ℝ)) = 2 * Real.pi / 7 := by push_cast; ring
  have hlt : 2 * Real.pi / 7 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hpos : 0 < 2 * Real.pi / 7 := by positivity
  refine lem38_theta _ hpos hlt cos_2pi7_irr ?_ x y z u v w t ht h
  have := sin_not_ratfn 1 7 7 (by norm_num) (by norm_num) (by norm_num) (by decide) (dvd_refl 7) (by decide +kernel)
    (by rw [e]; exact (sin_pos_lt hpos hlt).ne')
  rwa [e] at this

/-- **Lemma 3.8, case `s/m = 3/5` (`alpha = 3 pi/10`).**  Here `cos alpha = sin(pi/5)` has degree 4 and `sin alpha = cos(pi/5)`
degree 2 (the printed text has the two degrees the other way round); the legs are swapped. -/
theorem lem38_case35 (x y z u v w t : ℕ) (ht : 0 < t)
    (h : ((x : ℝ) * Real.cos (3 * Real.pi / 10) + y * Real.sin (3 * Real.pi / 10) + z) *
        ((u : ℝ) * Real.cos (3 * Real.pi / 10) + v * Real.sin (3 * Real.pi / 10) + w)
        = (t / 2) * Real.cos (3 * Real.pi / 10) * Real.sin (3 * Real.pi / 10)) :
    (x = 0 ∧ z = 0 ∧ v = 0 ∧ w = 0) ∨ (y = 0 ∧ z = 0 ∧ u = 0 ∧ w = 0) := by
  have e : (2 * ((1 : ℕ) : ℝ) * Real.pi / ((10 : ℕ) : ℝ)) = Real.pi / 5 := by push_cast; ring
  have hc : Real.cos (3 * Real.pi / 10) = Real.sin (Real.pi / 5) := by
    rw [← Real.cos_pi_div_two_sub]; congr 1; ring
  have hs : Real.sin (3 * Real.pi / 10) = Real.cos (Real.pi / 5) := by
    rw [← Real.sin_pi_div_two_sub]; congr 1; ring
  rw [hc, hs] at h
  have hlt : Real.pi / 5 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hpos : 0 < Real.pi / 5 := by positivity
  have hS : ¬ ∃ r q : ℚ[X], aeval (Real.cos (Real.pi / 5)) q ≠ 0 ∧
      Real.sin (Real.pi / 5) * aeval (Real.cos (Real.pi / 5)) q = aeval (Real.cos (Real.pi / 5)) r := by
    have := sin_not_ratfn 1 10 5 (by norm_num) (by norm_num) (by norm_num) (by decide) (by norm_num) (by decide +kernel)
      (by rw [e]; exact (sin_pos_lt hpos hlt).ne')
    rwa [e] at this
  have := lem38_theta (Real.pi / 5) hpos hlt cos_pi5_irr hS y x z v u w t ht
    (by linear_combination h)
  rcases this with h1 | h1
  · right; exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2⟩
  · left; exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2⟩

/-- Non-vacuity: a side `cos alpha` and a side `sin alpha` (two tiles of area `cos sin / 2`) satisfy the hypothesis of each case,
and the conclusions hold for it. -/
theorem lem38_witnesses :
    (∃ x y z u v w t : ℕ, 0 < t ∧
      ((x : ℝ) * Real.cos (2 * Real.pi / 5) + y * Real.sin (2 * Real.pi / 5) + z) *
        ((u : ℝ) * Real.cos (2 * Real.pi / 5) + v * Real.sin (2 * Real.pi / 5) + w)
        = (t / 2) * Real.cos (2 * Real.pi / 5) * Real.sin (2 * Real.pi / 5) ∧
      ((x = 0 ∧ z = 0 ∧ v = 0 ∧ w = 0) ∨ (y = 0 ∧ z = 0 ∧ u = 0 ∧ w = 0))) ∧
    (∃ x y z u v w t : ℕ, 0 < t ∧
      ((x : ℝ) * Real.cos (2 * Real.pi / 7) + y * Real.sin (2 * Real.pi / 7) + z) *
        ((u : ℝ) * Real.cos (2 * Real.pi / 7) + v * Real.sin (2 * Real.pi / 7) + w)
        = (t / 2) * Real.cos (2 * Real.pi / 7) * Real.sin (2 * Real.pi / 7) ∧
      ((x = 0 ∧ z = 0 ∧ v = 0 ∧ w = 0) ∨ (y = 0 ∧ z = 0 ∧ u = 0 ∧ w = 0))) ∧
    (∃ x y z u v w t : ℕ, 0 < t ∧
      ((x : ℝ) * Real.cos (3 * Real.pi / 10) + y * Real.sin (3 * Real.pi / 10) + z) *
        ((u : ℝ) * Real.cos (3 * Real.pi / 10) + v * Real.sin (3 * Real.pi / 10) + w)
        = (t / 2) * Real.cos (3 * Real.pi / 10) * Real.sin (3 * Real.pi / 10) ∧
      ((x = 0 ∧ z = 0 ∧ v = 0 ∧ w = 0) ∨ (y = 0 ∧ z = 0 ∧ u = 0 ∧ w = 0))) := by
  refine ⟨⟨1, 0, 0, 0, 1, 0, 2, by norm_num, by push_cast; ring, Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩,
    ⟨1, 0, 0, 0, 1, 0, 2, by norm_num, by push_cast; ring, Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩,
    ⟨1, 0, 0, 0, 1, 0, 2, by norm_num, by push_cast; ring, Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩⟩

end Erdos634.Laczkovich.Combi3

#print axioms Erdos634.Laczkovich.Combi3.lem38_sub
#print axioms Erdos634.Laczkovich.Combi3.sin_not_ratfn
#print axioms Erdos634.Laczkovich.Combi3.lem38_case45
#print axioms Erdos634.Laczkovich.Combi3.lem38_case47
#print axioms Erdos634.Laczkovich.Combi3.lem38_case35
#print axioms Erdos634.Laczkovich.Combi3.lem38_witnesses
