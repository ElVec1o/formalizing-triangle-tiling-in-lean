import Erdos634.Draft.BeesonL27T6

/-!
# Beeson (arXiv 1206.2229v4) Theorem 6 (with Lemma 28 for the last two shapes)

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Lemma 27, Lemma 28, Thm 6), Laczkovich (DCG 48 (2012)),
Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.

Printed Theorem 6: for the shapes `(alpha, alpha+2beta, alpha)` and `(2alpha, alpha, 2beta)` tiled by `N` copies of `T`,
`N + M1 M2 != 0`, `s^2 = 2(2N+M1M2)/(N+M1M2)` resp. `s^2 = (M1+M2)^2 / (2(N+M1M2))`, hence `s^2 in Q`, hence
`s = kappa (2 - s^2) in Q` (Lemma 28, `kappa = (M1+M2)/(M2-M1)`) and `T` is rational.  Formalized as `t6` from `t4_final`
(Theorem 4 with `M1, M2`) and `lemma27`.  Target vertices `0,1,2`: `(alpha, alpha, alpha+2beta)` and `(2alpha, alpha, 2beta)`.
Project hypothesis (H1) `alpha notin Q*pi` replaces Beeson's Lemma 1 (Laczkovich 5.1, 5.3; not in Lean).
-/

open scoped Classical

namespace Erdos634.BeesonColoring

open Erdos634.Geometry Erdos634.Geometry.A1Field

variable {N : ℕ}

/-- Lemma 28 + the last step of Theorem 6: `s (M2 - M1) = (M1 + M2)(2 - s^2)`, `M2 != M1`, `s^2 in Q` give `s in Q`. -/
theorem rat_of_kappa (s : ℝ) (M1 M2 : ℤ) (hne : (M2 : ℝ) - M1 ≠ 0)
    (hk : s * ((M2 : ℝ) - M1) = ((M1 : ℝ) + M2) * (2 - s ^ 2)) (hq : ∃ q2 : ℚ, (q2 : ℝ) = s ^ 2) :
    ∃ q : ℚ, (q : ℝ) = s := by
  obtain ⟨q2, hq2⟩ := hq
  refine ⟨((M1 : ℚ) + M2) / ((M2 : ℚ) - M1) * (2 - q2), ?_⟩
  push_cast
  rw [hq2, div_mul_eq_mul_div, div_eq_iff hne]
  linarith

set_option maxHeartbeats 1000000 in
theorem t6 (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) :
    ((D.target.angleAt 0 = α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + 2 * β) →
      ∃ M1 M2 : ℤ, (M1 : ℝ) = (circD D.target / circD D.model) * ((a / c) * (2 + a / c) / (1 + a / c)) ∧
        (M2 : ℝ) = -((circD D.target / circD D.model) * ((a / c) * (2 - a / c) / (1 - a / c))) ∧
        (N : ℝ) + M1 * M2 ≠ 0 ∧
        (a / c) ^ 2 = 2 * (2 * N + M1 * M2) / (N + M1 * M2) ∧ ∃ q : ℚ, (q : ℝ) = a / c) ∧
    ((D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = 2 * β) →
      ∃ M1 M2 : ℤ, (M1 : ℝ) = (circD D.target / circD D.model) * ((a / c) * (1 - a / c) * (2 + a / c)) ∧
        (M2 : ℝ) = -((circD D.target / circD D.model) * ((a / c) * (2 - a / c) * (1 + a / c))) ∧
        (N : ℝ) + M1 * M2 ≠ 0 ∧
        (a / c) ^ 2 = ((M1 : ℝ) + M2) ^ 2 / (2 * (N + M1 * M2)) ∧ ∃ q : ℚ, (q : ℝ) = a / c) := by
  obtain ⟨hΛ, hs0, hs1⟩ := t4_aux D hrel h
  obtain ⟨T1, -, -, R4, -⟩ := t4_final D hα hrel h
  obtain ⟨-, -, -, L4, L5⟩ := lemma27 D hrel h
  set Λ := circD D.target / circD D.model with hΛd
  set s := a / c with hsd
  have p1 : 0 < 1 - s := by linarith
  have p2 : 0 < 1 + s := by linarith
  have p3 : 0 < 2 + s := by linarith
  have p4 : 0 < 2 - s := by linarith
  have p5 : 0 < 2 - s ^ 2 := by nlinarith
  have p6 : 0 < 1 - s ^ 2 := by nlinarith
  have p7 : 0 < 3 - s ^ 2 := by nlinarith
  refine ⟨?_, ?_⟩
  · intro e
    obtain ⟨M1, M2, h1, h2, -, -⟩ := T1 e
    have hN := L4 e
    have hsum : (N : ℝ) + M1 * M2 = -(2 * Λ ^ 2 * s ^ 2 / (1 - s ^ 2)) := by
      rw [hN, h1, h2]; field_simp; ring
    have hne : (N : ℝ) + M1 * M2 ≠ 0 := by
      rw [hsum]; have : 0 < 2 * Λ ^ 2 * s ^ 2 / (1 - s ^ 2) := by positivity
      linarith
    have hb : s ^ 2 = 2 * (2 * N + M1 * M2) / (N + M1 * M2) := by
      rw [eq_div_iff hne]
      rw [hN, h1, h2]; field_simp; ring
    refine ⟨M1, M2, h1, h2, hne, hb, ?_⟩
    have hm : (M2 : ℝ) - M1 ≠ 0 := by
      rw [h1, h2]
      have : 0 < Λ * (s * (2 - s) / (1 - s)) + Λ * (s * (2 + s) / (1 + s)) := by positivity
      intro z; linarith
    refine rat_of_kappa s M1 M2 hm ?_ ?_
    · rw [h1, h2]; field_simp; ring
    · refine ⟨2 * (2 * N + M1 * M2) / (N + M1 * M2), ?_⟩
      push_cast; exact hb.symm
  · intro e
    obtain ⟨M1, M2, h1, h2, -, -⟩ := R4 e
    have hN := L5 e
    have hsum : (N : ℝ) + M1 * M2 = 2 * Λ ^ 2 * s ^ 2 := by
      rw [hN, h1, h2]; ring
    have hne : (N : ℝ) + M1 * M2 ≠ 0 := by
      rw [hsum]; positivity
    have hb : s ^ 2 = ((M1 : ℝ) + M2) ^ 2 / (2 * (N + M1 * M2)) := by
      rw [eq_div_iff (by rw [hsum]; positivity)]
      rw [hsum, h1, h2]; ring
    refine ⟨M1, M2, h1, h2, hne, hb, ?_⟩
    have hm : (M2 : ℝ) - M1 ≠ 0 := by
      rw [h1, h2]
      have : 0 < Λ * (s * (2 - s) * (1 + s)) + Λ * (s * (1 - s) * (2 + s)) := by positivity
      intro z; linarith
    refine rat_of_kappa s M1 M2 hm ?_ ?_
    · rw [h1, h2]; ring
    · refine ⟨((M1 : ℚ) + M2) ^ 2 / (2 * (N + M1 * M2)), ?_⟩
      push_cast; exact hb.symm

end Erdos634.BeesonColoring

#print axioms Erdos634.BeesonColoring.t6
