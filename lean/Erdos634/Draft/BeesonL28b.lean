import Erdos634.Draft.BeesonL28
import Erdos634.Draft.FluxDRow4AnyLabel

/-!
# Beeson (arXiv 1206.2229v4) Lemma 28 with the PRINTED vertex order and the printed hypothesis

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Lemma 27, Def. 8, Lemma 28), Laczkovich
(DCG 48 (2012)), Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.
SUPERSEDED by BeesonL28c3.lemma28_printed2 (2026-10-22): the triquadratic clause here (∃ M1 M2, M1 = M2) is
trivially true and the κ clauses are existential; do not cite this lemma as the printed Lemma 28. Kept because
BeesonL28bWit77 still uses it.

Printed Lemma 28 lists the angles of `ABC` "at A, B, C": `(beta, 3alpha, beta)`, `(alpha+beta, alpha,
alpha+beta)`, `(alpha, alpha+2beta, alpha)`, `(2alpha, alpha, 2beta)`, triquadratic `(2alpha, beta, alpha+beta)`.
`BeesonL28.lemma28` (internal order of `t4_final`) used `(beta,beta,3alpha)`, `(alpha+beta,alpha+beta,alpha)`,
`(alpha,alpha,alpha+2beta)` for the first, second and third of these.  Here each shape is stated with the
printed vertex data, by applying `lemma28` to the same dissection with the target relabelled by the
transposition of vertices 1 and 2 (`relabelTarget'`; same tiles, same model).
Hypotheses.  The printed section assumes `3alpha + 2beta = pi` (`hrel`, the case of the section) and that
`delta/pi` is irrational, `delta = alpha + beta` (Lemma 27 divides by `sin delta`, `sin(alpha+beta)=sin gamma`);
`delta_irr_iff` shows this is equivalent to `alpha notin Q pi` (project (H1), which replaces Beeson's Lemma 1).
The hypotheses are satisfiable: the 77-tiling by (2,3,4) satisfies all of them (`BeesonL28Wit77`).
Triquadratic clause: exactly the printed `M1 = M2` (and then `M2 - M1 = 0`, Def. 8 does not apply);
`BeesonL28` adds `M1 != 0`, which is a true strengthening (`M1 = Lambda s > 0`) and is dropped here.
LIMIT (PARTIAL): `M1, M2` are integers pinned, as in Beeson's proof, only through their Theorem 4 values
(`t4_final`); that these are the colour-count combinations `R+B-Y-W`, `R+Y-B-W` is the separate Theorem 4 statement.
-/

open scoped Classical

namespace Erdos634.BeesonColoring

open Erdos634.Geometry

theorem delta_irr_iff {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi) :
    (¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) ↔ ¬ ∃ r : ℚ, α + β = (r : ℝ) * Real.pi := by
  constructor
  · rintro h ⟨r, hr⟩
    exact h ⟨1 - 2 * r, by push_cast; linarith⟩
  · rintro h ⟨r, hr⟩
    exact h ⟨(1 - r) / 2, by push_cast; linarith⟩

section relabel
variable {N : ℕ}

private theorem cA' (p q r : Plane) : cornerAngle p q r = cornerAngle r q p :=
  EuclideanGeometry.angle_comm (V := Plane) p q r

theorem relabel12_angle (D : CongruentDissection N) :
    (D.relabelTarget' (Equiv.swap 1 2)).target.angleAt 0 = D.target.angleAt 0 ∧
    (D.relabelTarget' (Equiv.swap 1 2)).target.angleAt 1 = D.target.angleAt 2 ∧
    (D.relabelTarget' (Equiv.swap 1 2)).target.angleAt 2 = D.target.angleAt 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [Tri.angleAt]
    simp [CongruentDissection.relabelTarget', Erdos634.NormalPosition.relabelTri,
      Equiv.swap_apply_of_ne_of_ne]
    try rw [cA']

end relabel

variable {N : ℕ}

/-- **Beeson Lemma 28 as printed** (UNAUDITED): shapes listed at `A, B, C` as in the paper, hypothesis
`delta/pi` irrational with `delta = alpha + beta`.  `s = a/c`.

SUPERSEDED by `BeesonL28c3.lemma28_printed2` (2026-10-22): the triquadratic clause `∃ M1 M2, M1 = M2` is
trivially true and the κ clauses are existential; do not cite this lemma as the printed Lemma 28. -/
theorem lemma28_printed (D : CongruentDissection N) {α β a b c : ℝ}
    (hδ : ¬ ∃ r : ℚ, α + β = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) :
    -- triquadratic (2α, β, α+β): M1 = M2, so κ is undefined
    ((D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = α + β) →
      ∃ M1 M2 : ℤ, M1 = M2) ∧
    -- (β, 3α, β): κ = -s
    ((D.target.angleAt 0 = β ∧ D.target.angleAt 1 = 3 * α ∧ D.target.angleAt 2 = β) →
      ∃ M1 M2 : ℤ, (M2 : ℝ) - M1 ≠ 0 ∧ ((M1 : ℝ) + M2) / ((M2 : ℝ) - M1) = -(a / c)) ∧
    -- (α+β, α, α+β): κ = s
    ((D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + β) →
      ∃ M1 M2 : ℤ, (M2 : ℝ) - M1 ≠ 0 ∧ ((M1 : ℝ) + M2) / ((M2 : ℝ) - M1) = a / c) ∧
    -- (α, α+2β, α) and (2α, α, 2β): κ = s/(2-s²), 0 < κ < 1, s = κ(2-s²), quartic
    (∀ (_ : (D.target.angleAt 0 = α ∧ D.target.angleAt 1 = α + 2 * β ∧ D.target.angleAt 2 = α) ∨
        (D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = 2 * β)),
      ∃ M1 M2 : ℤ, (M2 : ℝ) - M1 ≠ 0 ∧
        ∃ κ : ℝ, κ = ((M1 : ℝ) + M2) / ((M2 : ℝ) - M1) ∧ κ = (a / c) / (2 - (a / c) ^ 2) ∧
          0 < κ ∧ κ < 1 ∧ a / c = κ * (2 - (a / c) ^ 2) ∧
          κ ^ 2 * (a / c) ^ 4 - (4 * κ ^ 2 + 1) * (a / c) ^ 2 + 4 * κ ^ 2 = 0) := by
  have hα := (delta_irr_iff hrel).mpr hδ
  obtain ⟨t1, t2, t3, t4⟩ := lemma28 D hα hrel h
  have hm : (D.relabelTarget' (Equiv.swap 1 2)).model = D.model := rfl
  obtain ⟨r0, r1, r2⟩ := relabel12_angle D
  obtain ⟨u1, u2, u3, u4⟩ := lemma28 (D.relabelTarget' (Equiv.swap 1 2)) hα hrel (hm ▸ h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e
    obtain ⟨M1, M2, h1, -⟩ := t1 e
    exact ⟨M1, M2, h1⟩
  · rintro ⟨e0, e1, e2⟩
    exact u2 ⟨by rw [r0, e0], by rw [r1, e2], by rw [r2, e1]⟩
  · rintro ⟨e0, e1, e2⟩
    exact u3 ⟨by rw [r0, e0], by rw [r1, e2], by rw [r2, e1]⟩
  · rintro (⟨e0, e1, e2⟩ | e)
    · exact u4 (Or.inl ⟨by rw [r0, e0], by rw [r1, e2], by rw [r2, e1]⟩)
    · exact t4 (Or.inr e)

end Erdos634.BeesonColoring

#print axioms Erdos634.BeesonColoring.lemma28_printed
#print axioms Erdos634.BeesonColoring.relabel12_angle
