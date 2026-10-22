import Erdos634.Draft.BeesonT4M1

/-!
# Beeson (arXiv 1206.2229v4) Lemma 48: scaling the tile by `kappa`

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Lemma 48 and Lemma 24), Laczkovich (DCG 48 (2012)),
Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.

Printed Lemma 48: for `3 alpha + 2 beta = pi`, `s = 2 sin(alpha/2)`, and the tile scaled by `kappa`
(`(a,b,c) = kappa (sin alpha, sin beta, sin gamma)`, `gamma = pi - alpha - beta`):
`kappa sin 2alpha / c = s(2-s^2)`, `sin 2alpha = (2-s^2) sin alpha`,
`kappa sin 2beta / c = kappa sin 3alpha / c = s(1+s)(1-s)(3-s^2)`.  Derived here from `sin_table` (Lemma 24)
after identifying its `s` with `2 sin(alpha/2)`.  No dissection and no H1 needed.
-/

namespace Erdos634.BeesonColoring

theorem lemma48 {α β κ s c : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (hα : 0 < α) (hβ : 0 < β)
    (hκ : 0 < κ) (hs : s = 2 * Real.sin (α / 2)) (hc : c = κ * Real.sin (α + β)) :
    0 < s ∧ s < 1 ∧ κ * Real.sin α / c = s ∧
      κ * Real.sin (2 * α) / c = s * (2 - s ^ 2) ∧
      Real.sin (2 * α) = (2 - s ^ 2) * Real.sin α ∧
      κ * Real.sin (2 * β) / c = κ * Real.sin (3 * α) / c ∧
      κ * Real.sin (3 * α) / c = s * (1 + s) * (1 - s) * (3 - s ^ 2) := by
  obtain ⟨s0, h0, h1, sA, sB, sG, s2A, sAB, s3A, s2B⟩ := sin_table hrel hα hβ
  have hpi := Real.pi_pos
  have hδ : Real.sin (α + β) = Real.cos (α / 2) := by
    rw [show α + β = Real.pi / 2 - α / 2 by linarith, Real.sin_pi_div_two_sub]
  have hδpos : 0 < Real.sin (α + β) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hsα : Real.sin α = s * Real.sin (α + β) := by
    rw [hs, hδ, show α = 2 * (α / 2) by ring, Real.sin_two_mul]; ring_nf
  have hss : s = s0 := by
    have : (s - s0) * Real.sin (α + β) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hδpos.ne'
  subst hss
  have hcpos : 0 < c := by rw [hc]; positivity
  refine ⟨h0, h1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsα, hc]; field_simp
  · rw [s2A, hc]; field_simp
  · rw [s2A, hsα]; ring
  · rw [s2B, s3A]
  · rw [s3A, hc]; field_simp; ring

/-- the hypotheses of `lemma48` are satisfiable (e.g. `alpha = beta = pi/5`, `kappa = 1`). -/
theorem lemma48_hyps_wit : ∃ α β : ℝ, 3 * α + 2 * β = Real.pi ∧ 0 < α ∧ 0 < β :=
  ⟨Real.pi / 5, Real.pi / 5, by ring, by positivity, by positivity⟩

end Erdos634.BeesonColoring

#print axioms Erdos634.BeesonColoring.lemma48
