import Erdos634.Draft.BeesonH1Arith
import Erdos634.Draft.BeesonShapesL5L6L11
import Erdos634.Draft.FluxCRow12

/-!
# Beeson (arXiv 1206.2229 v4) Lemma 1 (H1), conditional on the two Laczkovich theorems

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Lemma 1), Laczkovich (Discrete Math 140 (1995), Theorems 5.1 and
5.3), Conway-Jones (trigonometric Diophantine background), Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.

Printed Lemma 1: `3 alpha + 2 beta = pi`, an `N`-tiling of `ABC` by `T` with angles `(alpha, beta, gamma)`, `ABC` not similar to `T`
==> `alpha`, `beta` are not rational multiples of `pi`.  Proof: Laczkovich Thm 5.1 (geometry) + the arithmetic check
(`BeesonH1Arith.list_check`, `no_right_angle`) + Laczkovich Thm 5.3 (geometry) for the one surviving triple `(pi/4, pi/8, 5 pi/8)`.

The two geometric inputs are carried as NAMED hypotheses (Props), not axioms:
* `Lacz51` (Theorem 5.1, as a statement about a real `CongruentDissection` whose tile has angle multiset `{alpha, beta, 2alpha+beta}`,
  all rational multiples of pi, and whose target is not similar to the tile (AAA, `Triple3`)): some tile angle is `pi/2`
  (case (ii)) or the angle triple is in the list (iii)-(vii).
* `Lacz53` (Theorem 5.3, only the instance Beeson uses): the tile `(pi/4, pi/8, 5 pi/8)` has no congruent dissection of a
  triangle not similar to it.
Non-vacuity: `Lacz51`/`Lacz53` are statements about ALL dissections, true in the literature, not provable here (no Lean geometry of
Theorem 5.1: Laczkovich's field-automorphism argument on tilings).  Their premises are satisfiable arithmetically
(`BeesonH1Arith.rational_solution_pi5/pi7`); `lemma1_of_laczkovich` is therefore not vacuous in the premises, only conditional.
-/

namespace Erdos634.BeesonH1

open Erdos634 Erdos634.Geometry Erdos634.BeesonColoring

open scoped Classical

/-- Laczkovich Theorem 5.1 for the tile `(alpha, beta, 2 alpha + beta)` (named hypothesis; geometry, not in Lean). -/
def Lacz51 : Prop :=
  ∀ {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ} (x y z : ℚ),
    D.model.ThreeAlphaData α β a b c →
    α = (x : ℝ) * Real.pi → β = (y : ℝ) * Real.pi → 2 * α + β = (z : ℝ) * Real.pi →
    ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β) →
    (x = 1/2 ∨ y = 1/2 ∨ z = 1/2) ∨ InLaczList x y z

/-- Laczkovich Theorem 5.3, the instance Beeson uses (named hypothesis; geometry, not in Lean). -/
def Lacz53 : Prop :=
  ∀ {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ},
    D.model.ThreeAlphaData α β a b c →
    α = Real.pi / 4 → β = Real.pi / 8 →
    ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β) → False

/-- **Beeson Lemma 1** (`T-L1`), conditional on `Lacz51`, `Lacz53`: `alpha` is not a rational multiple of `pi`. -/
theorem lemma1_of_laczkovich (h51 : Lacz51) (h53 : Lacz53) {N : ℕ} (D : CongruentDissection N)
    {α β a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) :
    ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi := by
  rintro ⟨r, hr⟩
  have hπ : 0 < Real.pi := Real.pi_pos
  obtain ⟨σ, h0, -, h1, -, -, -⟩ := id h
  have hαpos : 0 < α := h0 ▸ D.model.angleAt_pos' (σ 0)
  have hβpos : 0 < β := h1 ▸ D.model.angleAt_pos' (σ 1)
  set y : ℚ := (1 - 3 * r) / 2 with hy
  have hβ : β = (y : ℝ) * Real.pi := by
    rw [hy]; push_cast; rw [hr] at hrel; linarith
  have hz : 2 * α + β = ((2 * r + y : ℚ) : ℝ) * Real.pi := by
    push_cast; rw [hr, hβ]; ring
  have hr0 : 0 < r := by
    have : (0 : ℝ) < (r : ℝ) * Real.pi := hr ▸ hαpos
    have : (0 : ℝ) < (r : ℝ) := by
      by_contra hc; push_neg at hc; nlinarith
    exact_mod_cast this
  have hy0 : 0 < y := by
    have : (0 : ℝ) < (y : ℝ) * Real.pi := hβ ▸ hβpos
    have : (0 : ℝ) < (y : ℝ) := by
      by_contra hc; push_neg at hc; nlinarith
    exact_mod_cast this
  have hq : 3 * r + 2 * y = 1 := by rw [hy]; ring
  rcases h51 D r y (2 * r + y) h hr hβ hz hns with hrt | hl
  · exact no_right_angle hr0 hy0 hq rfl hrt
  · obtain ⟨hx, hy'⟩ := list_check hr0 hy0 hq rfl hl
    refine h53 D h ?_ ?_ hns
    · rw [hr, hx]; push_cast; ring
    · rw [hβ, hy']; push_cast; ring

/-- **Consumer plug (T-L6)**: `lemma6` with `H1` discharged by `lemma1_of_laczkovich`.  In the similar case the first disjunct is
the hypothesis itself, so no irrationality is needed there. -/
theorem lemma6_of_laczkovich (h51 : Lacz51) (h53 : Lacz53) {N : ℕ} (D : CongruentDissection N)
    {α β a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (h : D.model.ThreeAlphaData α β a b c) :
    Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β) ∨
    ((∀ k, vcount D k (2 * α + β) = 0) ∧ (∑ k, vcount D k α) = 3 ∧ (∑ k, vcount D k β) = 2 ∧
      (∑ k, (vcount D k α + vcount D k β)) = 5) := by
  by_cases hs : Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)
  · exact Or.inl hs
  · exact lemma6 D (lemma1_of_laczkovich h51 h53 D hrel h hs) hrel h

end Erdos634.BeesonH1

#print axioms Erdos634.BeesonH1.lemma1_of_laczkovich
#print axioms Erdos634.BeesonH1.lemma6_of_laczkovich
