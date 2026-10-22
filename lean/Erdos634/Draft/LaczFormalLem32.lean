-- Draft/LaczFormalLem32.lean -- ALGEBRAIC HALF of Laczkovich (DCG 48 (2012)) Lemma 3.2: if the vertex equations
--   alpha + beta + gamma = pi,  p_i alpha + q_i beta + r_i gamma = delta_i,  p_j alpha + q_j beta + r_j gamma = delta_j
-- have nonzero determinant D_ij, then alpha, beta, gamma are rational linear combinations of pi, delta_i, delta_j (Cramer's rule), hence lie in any
-- Q-span containing pi, delta_i, delta_j (e.g. the span of the angles of the target).
-- NOT the lemma itself: the geometric input [Laczkovich, Combinatorica 10 (1990), Lemma 10] (an irregular tiling has a vertex pair with D_ij != 0)
-- is NOT in Lean (that paper is not in the sources directory).  Label NOTE, UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012) Lemma 3.2; Combinatorica 1990), Beeson, Beeson-Zhang.
import Mathlib

open scoped BigOperators

namespace Erdos634.Draft.LaczFormal

/-- The determinant `D_ij` of Lemma 3.2. -/
def detD (pi qi ri pj qj rj : ℤ) : ℤ :=
  (qi * rj - ri * qj) - (pi * rj - ri * pj) + (pi * qj - qi * pj)

theorem cramer_alpha {α β γ π' δi δj : ℝ} {pi qi ri pj qj rj : ℤ}
    (h0 : α + β + γ = π') (hi : pi * α + qi * β + ri * γ = δi) (hj : pj * α + qj * β + rj * γ = δj) :
    (detD pi qi ri pj qj rj : ℝ) * α = (qi * rj - ri * qj : ℤ) * π' + (qj - rj : ℤ) * δi + (ri - qi : ℤ) * δj := by
  unfold detD; push_cast
  linear_combination ((qi:ℝ) * rj - ri * qj) * h0 + ((qj:ℝ) - rj) * hi + ((ri:ℝ) - qi) * hj

theorem cramer_beta {α β γ π' δi δj : ℝ} {pi qi ri pj qj rj : ℤ}
    (h0 : α + β + γ = π') (hi : pi * α + qi * β + ri * γ = δi) (hj : pj * α + qj * β + rj * γ = δj) :
    (detD pi qi ri pj qj rj : ℝ) * β = (-(pi * rj - ri * pj) : ℤ) * π' + (rj - pj : ℤ) * δi + (pi - ri : ℤ) * δj := by
  unfold detD; push_cast
  linear_combination (-((pi:ℝ) * rj - ri * pj)) * h0 + ((rj:ℝ) - pj) * hi + ((pi:ℝ) - ri) * hj

theorem cramer_gamma {α β γ π' δi δj : ℝ} {pi qi ri pj qj rj : ℤ}
    (h0 : α + β + γ = π') (hi : pi * α + qi * β + ri * γ = δi) (hj : pj * α + qj * β + rj * γ = δj) :
    (detD pi qi ri pj qj rj : ℝ) * γ = (pi * qj - qi * pj : ℤ) * π' + (pj - qj : ℤ) * δi + (qi - pi : ℤ) * δj := by
  unfold detD; push_cast
  linear_combination ((pi:ℝ) * qj - qi * pj) * h0 + ((pj:ℝ) - qj) * hi + ((qi:ℝ) - pi) * hj

/-- Generic form: `x` with `D x = c0 pi + c1 di + c2 dj` (integers) lies in a `Q`-span containing `pi, di, dj`. -/
theorem mem_span_of_cramer {S : Set ℝ} {x π' δi δj : ℝ} {D c0 c1 c2 : ℤ} (hD : D ≠ 0)
    (hx : (D : ℝ) * x = (c0 : ℝ) * π' + (c1 : ℝ) * δi + (c2 : ℝ) * δj)
    (hp : π' ∈ Submodule.span ℚ S) (hi : δi ∈ Submodule.span ℚ S) (hj : δj ∈ Submodule.span ℚ S) :
    x ∈ Submodule.span ℚ S := by
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD
  have hx' : x = ((c0 : ℚ) / D : ℚ) • π' + ((c1 : ℚ) / D : ℚ) • δi + ((c2 : ℚ) / D : ℚ) • δj := by
    simp only [Rat.smul_def]; push_cast
    field_simp
    linarith
  rw [hx']
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ hp) (Submodule.smul_mem _ _ hi))
    (Submodule.smul_mem _ _ hj)

/-- **Lemma 3.2, algebraic half.**  If `D_ij != 0`, all three tile angles lie in every `Q`-span that contains `pi` and the two vertex values. -/
theorem lemma32_alg {S : Set ℝ} {α β γ π' δi δj : ℝ} {pi qi ri pj qj rj : ℤ}
    (hD : detD pi qi ri pj qj rj ≠ 0)
    (h0 : α + β + γ = π') (hi : pi * α + qi * β + ri * γ = δi) (hj : pj * α + qj * β + rj * γ = δj)
    (hp : π' ∈ Submodule.span ℚ S) (hdi : δi ∈ Submodule.span ℚ S) (hdj : δj ∈ Submodule.span ℚ S) :
    α ∈ Submodule.span ℚ S ∧ β ∈ Submodule.span ℚ S ∧ γ ∈ Submodule.span ℚ S := by
  refine ⟨?_, ?_, ?_⟩
  · refine mem_span_of_cramer (c0 := qi * rj - ri * qj) (c1 := qj - rj) (c2 := ri - qi) hD ?_ hp hdi hdj
    have := cramer_alpha h0 hi hj
    push_cast at this ⊢; linarith
  · refine mem_span_of_cramer (c0 := -(pi * rj - ri * pj)) (c1 := rj - pj) (c2 := pi - ri) hD ?_ hp hdi hdj
    have := cramer_beta h0 hi hj
    push_cast at this ⊢; linarith
  · refine mem_span_of_cramer (c0 := pi * qj - qi * pj) (c1 := pj - qj) (c2 := qi - pi) hD ?_ hp hdi hdj
    have := cramer_gamma h0 hi hj
    push_cast at this ⊢; linarith

/-- Non-vacuity: the tile `(pi/6, pi/3, pi/2)`, vertex 1 `= 2 alpha` (value `pi/3`), vertex 2 `= gamma` (value `pi/2`), `D = -2 != 0`;
the conclusion puts `pi/6` in the span of `{pi, pi/3, pi/2}`. -/
theorem lemma32_alg_witness :
    detD 2 0 0 0 0 1 ≠ 0 ∧
    (Real.pi / 6) ∈ Submodule.span ℚ ({Real.pi, Real.pi / 3, Real.pi / 2} : Set ℝ) := by
  refine ⟨by decide, ?_⟩
  have hp := Submodule.subset_span (R := ℚ) (show Real.pi ∈ ({Real.pi, Real.pi / 3, Real.pi / 2} : Set ℝ) by simp)
  have h3 := Submodule.subset_span (R := ℚ) (show Real.pi / 3 ∈ ({Real.pi, Real.pi / 3, Real.pi / 2} : Set ℝ) by simp)
  have h2 := Submodule.subset_span (R := ℚ) (show Real.pi / 2 ∈ ({Real.pi, Real.pi / 3, Real.pi / 2} : Set ℝ) by simp)
  exact (lemma32_alg (S := {Real.pi, Real.pi / 3, Real.pi / 2}) (α := Real.pi / 6) (β := Real.pi / 3) (γ := Real.pi / 2)
    (π' := Real.pi) (δi := Real.pi / 3) (δj := Real.pi / 2) (pi := 2) (qi := 0) (ri := 0) (pj := 0) (qj := 0) (rj := 1)
    (by decide) (by ring) (by push_cast; ring) (by push_cast; ring) hp h3 h2).1

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.lemma32_alg
#print axioms Erdos634.Draft.LaczFormal.lemma32_alg_witness
