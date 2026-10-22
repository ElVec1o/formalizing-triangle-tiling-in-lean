import Erdos634.Draft.BeesonT6

/-!
# Beeson (arXiv 1206.2229v4) Lemma 28 and Definition 8, as a standalone statement

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Def. 8, Lemma 28), Laczkovich (DCG 48 (2012)),
Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.

Def 8: when `M1 != M2`, `kappa = (M1 + M2)/(M2 - M1)`.  Lemma 28: in the triquadratic shape `(2alpha, beta, alpha+beta)`,
`M1 = M2` (kappa undefined); otherwise `kappa = -s, s, s/(2-s^2), s/(2-s^2)` for `(beta,3alpha,beta)`,
`(alpha+beta,alpha,alpha+beta)`, `(alpha,alpha+2beta,alpha)`, `(2alpha,alpha,2beta)`; in the last two `0<kappa<1`,
`s = kappa (2-s^2)` and `kappa^2 s^4 - (4kappa^2+1)s^2 + 4kappa^2 = 0`.  Here `s = a/c` and the shape orderings are the
vertex orderings of `t4_final`.  Project hypothesis (H1) `alpha notin Q*pi` replaces Beeson's Lemma 1 (as in `t4_final`).
Print note: the printed list orders the shapes as above; `t4_final` reads `(alpha, alpha, alpha+2beta)` for `(alpha,alpha+2beta,alpha)`.
-/

open scoped Classical

namespace Erdos634.BeesonColoring

open Erdos634.Geometry Erdos634.Geometry.A1Field

/-- the common conclusion for the two shapes with `kappa = s/(2-s^2)` -/
theorem kappa_props (s κ : ℝ) (h0 : 0 < s) (h1 : s < 1) (hk : κ = s / (2 - s ^ 2)) :
    0 < κ ∧ κ < 1 ∧ s = κ * (2 - s ^ 2) ∧ κ ^ 2 * s ^ 4 - (4 * κ ^ 2 + 1) * s ^ 2 + 4 * κ ^ 2 = 0 := by
  have p : 0 < 2 - s ^ 2 := by nlinarith
  have hs : s = κ * (2 - s ^ 2) := by rw [hk]; field_simp
  refine ⟨by rw [hk]; positivity, ?_, hs, ?_⟩
  · rw [hk, div_lt_one p]; nlinarith
  · have : κ ^ 2 * s ^ 4 - (4 * κ ^ 2 + 1) * s ^ 2 + 4 * κ ^ 2 = (κ * (2 - s ^ 2)) ^ 2 - s ^ 2 := by ring
    rw [this, ← hs]; ring

theorem kap_shape1 (Λ s M1 M2 : ℝ) (hΛ : 0 < Λ) (h0 : 0 < s) (h1 : s < 1)
    (e1 : M1 = Λ * (s * (2 + s) / (1 + s))) (e2 : M2 = -(Λ * (s * (2 - s) / (1 - s)))) :
    M2 - M1 ≠ 0 ∧ (M1 + M2) / (M2 - M1) = s / (2 - s ^ 2) := by
  have p1 : 0 < 1 - s := by linarith
  have n1 : (1 - s) ≠ 0 := by linarith
  have n2 : (1 + s) ≠ 0 := by linarith
  have n3 : (1 - s ^ 2) ≠ 0 := by nlinarith
  have n4 : (2 - s ^ 2) ≠ 0 := by nlinarith
  have n5 : (4 - 2 * s ^ 2) ≠ 0 := by nlinarith
  have n6 : Λ ≠ 0 := hΛ.ne'
  have n7 : s ≠ 0 := h0.ne'
  have p2 : 0 < 1 + s := by linarith
  have p5 : 0 < 2 - s ^ 2 := by nlinarith
  have hd : M2 - M1 = -(Λ * s * (4 - 2 * s ^ 2) / (1 - s ^ 2)) := by
    rw [e1, e2]; field_simp; ring
  have hs : M1 + M2 = -(Λ * s * (2 * s) / (1 - s ^ 2)) := by
    rw [e1, e2]; field_simp; ring
  have hp : 0 < 1 - s ^ 2 := by nlinarith
  have hne : M2 - M1 ≠ 0 := by
    rw [hd]; have : 0 < Λ * s * (4 - 2 * s ^ 2) / (1 - s ^ 2) := by
      apply div_pos (mul_pos (mul_pos hΛ h0) (by nlinarith)) hp
    linarith
  refine ⟨hne, ?_⟩
  rw [div_eq_div_iff hne n4, hd, hs]; field_simp; ring

theorem kap_shape4 (Λ s M1 M2 : ℝ) (hΛ : 0 < Λ) (h0 : 0 < s) (h1 : s < 1)
    (e1 : M1 = Λ * (s * (1 - s) * (2 + s))) (e2 : M2 = -(Λ * (s * (2 - s) * (1 + s)))) :
    M2 - M1 ≠ 0 ∧ (M1 + M2) / (M2 - M1) = s / (2 - s ^ 2) := by
  have p1 : 0 < 1 - s := by linarith
  have n1 : (1 - s) ≠ 0 := by linarith
  have n2 : (1 + s) ≠ 0 := by linarith
  have n3 : (1 - s ^ 2) ≠ 0 := by nlinarith
  have n4 : (2 - s ^ 2) ≠ 0 := by nlinarith
  have n5 : (4 - 2 * s ^ 2) ≠ 0 := by nlinarith
  have n6 : Λ ≠ 0 := hΛ.ne'
  have n7 : s ≠ 0 := h0.ne'
  have p5 : 0 < 2 - s ^ 2 := by nlinarith
  have hd : M2 - M1 = -(Λ * s * (4 - 2 * s ^ 2)) := by rw [e1, e2]; ring
  have hs : M1 + M2 = -(Λ * s * (2 * s)) := by rw [e1, e2]; ring
  have hne : M2 - M1 ≠ 0 := by
    rw [hd]; have : 0 < Λ * s * (4 - 2 * s ^ 2) := mul_pos (mul_pos hΛ h0) (by nlinarith)
    linarith
  refine ⟨hne, ?_⟩
  rw [div_eq_div_iff hne n4, hd, hs]; ring

theorem kap_shape2 (Λ s M1 M2 : ℝ) (hΛ : 0 < Λ) (h0 : 0 < s) (h1 : s < 1)
    (e1 : M1 = Λ * ((1 - s) * (1 + s) ^ 2)) (e2 : M2 = -(Λ * ((1 - s) ^ 2 * (1 + s)))) :
    M2 - M1 ≠ 0 ∧ (M1 + M2) / (M2 - M1) = -s := by
  have p1 : 0 < 1 - s := by linarith
  have n1 : (1 - s) ≠ 0 := by linarith
  have n2 : (1 + s) ≠ 0 := by linarith
  have n3 : (1 - s ^ 2) ≠ 0 := by nlinarith
  have n4 : (2 - s ^ 2) ≠ 0 := by nlinarith
  have n5 : (4 - 2 * s ^ 2) ≠ 0 := by nlinarith
  have n6 : Λ ≠ 0 := hΛ.ne'
  have n7 : s ≠ 0 := h0.ne'
  have hd : M2 - M1 = -(2 * Λ * (1 - s ^ 2)) := by rw [e1, e2]; ring
  have hs : M1 + M2 = 2 * Λ * s * (1 - s ^ 2) := by rw [e1, e2]; ring
  have hp : 0 < 1 - s ^ 2 := by nlinarith
  have hne : M2 - M1 ≠ 0 := by
    rw [hd]; have : 0 < 2 * Λ * (1 - s ^ 2) := by positivity
    linarith
  refine ⟨hne, ?_⟩
  rw [hd, hs]; field_simp

theorem kap_shape3 (Λ s M1 M2 : ℝ) (hΛ : 0 < Λ) (h0 : 0 < s) (h1 : s < 1)
    (e1 : M1 = Λ * (1 / (1 + s))) (e2 : M2 = -(Λ * (1 / (1 - s)))) :
    M2 - M1 ≠ 0 ∧ (M1 + M2) / (M2 - M1) = s := by
  have p1 : 0 < 1 - s := by linarith
  have n1 : (1 - s) ≠ 0 := by linarith
  have n2 : (1 + s) ≠ 0 := by linarith
  have n3 : (1 - s ^ 2) ≠ 0 := by nlinarith
  have n4 : (2 - s ^ 2) ≠ 0 := by nlinarith
  have n5 : (4 - 2 * s ^ 2) ≠ 0 := by nlinarith
  have n6 : Λ ≠ 0 := hΛ.ne'
  have n7 : s ≠ 0 := h0.ne'
  have p2 : 0 < 1 + s := by linarith
  have hd : M2 - M1 = -(2 * Λ / (1 - s ^ 2)) := by rw [e1, e2]; field_simp; ring
  have hs : M1 + M2 = -(2 * Λ * s / (1 - s ^ 2)) := by rw [e1, e2]; field_simp; ring
  have hp : 0 < 1 - s ^ 2 := by nlinarith
  have hne : M2 - M1 ≠ 0 := by
    rw [hd]; have : 0 < 2 * Λ / (1 - s ^ 2) := by positivity
    linarith
  refine ⟨hne, ?_⟩
  rw [hd, hs]; field_simp

variable {N : ℕ}

/-- **Beeson Lemma 28** (UNAUDITED; (H1)).  `kappa := (M1 + M2)/(M2 - M1)` (Def. 8), `s = a/c`. -/
theorem lemma28 (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) :
    -- triquadratic: M1 = M2 (kappa undefined)
    ((D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = α + β) →
      ∃ M1 M2 : ℤ, M1 = M2 ∧ M1 ≠ 0) ∧
    -- (beta, 3 alpha, beta): kappa = -s
    ((D.target.angleAt 0 = β ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = 3 * α) →
      ∃ M1 M2 : ℤ, (M2 : ℝ) - M1 ≠ 0 ∧ ((M1 : ℝ) + M2) / ((M2 : ℝ) - M1) = -(a / c)) ∧
    -- (alpha+beta, alpha, alpha+beta): kappa = s
    ((D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α + β ∧ D.target.angleAt 2 = α) →
      ∃ M1 M2 : ℤ, (M2 : ℝ) - M1 ≠ 0 ∧ ((M1 : ℝ) + M2) / ((M2 : ℝ) - M1) = a / c) ∧
    -- (alpha, alpha+2beta, alpha) [t4_final order (alpha,alpha,alpha+2beta)] and (2alpha, alpha, 2beta):
    -- kappa = s/(2-s^2), 0 < kappa < 1, s = kappa (2-s^2), quartic
    (∀ (_ : (D.target.angleAt 0 = α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + 2 * β) ∨
        (D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = 2 * β)),
      ∃ M1 M2 : ℤ, (M2 : ℝ) - M1 ≠ 0 ∧
        ∃ κ : ℝ, κ = ((M1 : ℝ) + M2) / ((M2 : ℝ) - M1) ∧ κ = (a / c) / (2 - (a / c) ^ 2) ∧
          0 < κ ∧ κ < 1 ∧ a / c = κ * (2 - (a / c) ^ 2) ∧
          κ ^ 2 * (a / c) ^ 4 - (4 * κ ^ 2 + 1) * (a / c) ^ 2 + 4 * κ ^ 2 = 0) := by
  obtain ⟨hΛ, hs0, hs1⟩ := t4_aux D hrel h
  obtain ⟨T1, T2, T3, T4, T5⟩ := t4_final D hα hrel h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e
    obtain ⟨M1, M2, h1, h2, hn1, -, -⟩ := T5 e
    exact ⟨M1, M2, by exact_mod_cast h1.trans h2.symm, hn1⟩
  · intro e
    obtain ⟨M1, M2, h1, h2, -, -⟩ := T2 e
    obtain ⟨hne, hk⟩ := kap_shape2 _ _ _ _ hΛ hs0 hs1 h1 h2
    exact ⟨M1, M2, hne, hk⟩
  · intro e
    obtain ⟨M1, M2, h1, h2, -, -⟩ := T3 e
    obtain ⟨hne, hk⟩ := kap_shape3 _ _ _ _ hΛ hs0 hs1 h1 h2
    exact ⟨M1, M2, hne, hk⟩
  · intro e
    rcases e with e | e
    · obtain ⟨M1, M2, h1, h2, -, -⟩ := T1 e
      obtain ⟨hne, hk⟩ := kap_shape1 _ _ _ _ hΛ hs0 hs1 h1 h2
      obtain ⟨q0, q1, q2, q3⟩ := kappa_props _ _ hs0 hs1 hk
      exact ⟨M1, M2, hne, _, rfl, hk, q0, q1, q2, q3⟩
    · obtain ⟨M1, M2, h1, h2, -, -⟩ := T4 e
      obtain ⟨hne, hk⟩ := kap_shape4 _ _ _ _ hΛ hs0 hs1 h1 h2
      obtain ⟨q0, q1, q2, q3⟩ := kappa_props _ _ hs0 hs1 hk
      exact ⟨M1, M2, hne, _, rfl, hk, q0, q1, q2, q3⟩

end Erdos634.BeesonColoring

#print axioms Erdos634.BeesonColoring.lemma28
