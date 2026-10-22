-- Draft/FluxFRow15Close.lean — ROW 15 (rationality_proofs.md §5, Theorem RAT row 15) closed for a
-- REAL `CongruentDissection`: target `(2α, α, 2β)` (angles at target vertices 0, 1, 2), model
-- angles `α, β` at model vertices 0, 1, `3α + 2β = π`, `α ∉ ℚπ`  ⟹  `s = a/c ∈ ℚ` and
-- `b = (1 − s²) c`, i.e. `a : b : c` is rational.  No hypothesis beyond these.
--
-- Assembly only:
-- * `Row15.setup` (Draft/FluxFRow15Setup.lean): flux + law of sines + area;
-- * `CongruentDissection.side_word_threeAlpha` (Draft/FluxDSideWord.lean, pre-existing): real words
--   of the sides `X` (opposite `2α`) and `Y` (opposite `α`);
-- * `Row15Conj.row15_algebraic` (Draft/FluxFRow15Conj.lean): degree split + conjugate principle,
--   dispatching to the ten-leaf files' leaves 4–10 with every bridge hypothesis derived.
-- Beeson III Thm 2 and F4 are not used (as in the paper).  No real tiling of the row-15 target is
-- known, so the hypothesis bundle has no joint Lean witness; ingredients are witnessed below.
--
-- Formalization debt (paper-level PROVED); not progress on the three /goal outcomes.
import Erdos634.Draft.FluxFRow15Setup
import Erdos634.Draft.FluxFRow15Conj
import Erdos634.Draft.FluxDSideWord

open scoped Classical

namespace Erdos634.Geometry

variable {N : ℕ}

/-- **ROW 15, closed for a real `CongruentDissection`.** -/
theorem Row15.rational_real (D : CongruentDissection N) (α β : ℝ)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (hm0 : D.model.angleAt 0 = α) (hm1 : D.model.angleAt 1 = β)
    (hP0 : D.target.angleAt 0 = 2 * α) (hP1 : D.target.angleAt 1 = α) :
    ∃ r : ℚ, D.model.oppLen 0 = (r : ℝ) * D.model.oppLen 2 ∧
      D.model.oppLen 1 = (1 - (r : ℝ) ^ 2) * D.model.oppLen 2 := by
  have hm2 : D.model.angleAt 2 = 2 * α + β := by
    have := D.model.angleAt_sum; rw [hm0, hm1] at this; linarith
  have hP2 : D.target.angleAt 2 = 2 * β := by
    have := D.target.angleAt_sum; rw [hP0, hP1] at this; linarith
  have h3 : D.model.ThreeAlphaData α β (D.model.oppLen 0) (D.model.oppLen 1) (D.model.oppLen 2) :=
    ⟨1, hm0, rfl, hm1, rfl, hm2, rfl⟩
  obtain ⟨s, S, hs0, hs1, hc, ha, hb, hXY, -, hSY, hArea⟩ := Row15.setup D hirr hrel h3 hP0 hP1 hP2
  obtain ⟨na, nb, nc, hwY⟩ := D.side_word_threeAlpha h3 1
  obtain ⟨ma, mb, mc, hwX⟩ := D.side_word_threeAlpha h3 0
  set c := D.model.oppLen 2 with hcdef
  set Y := D.target.oppLen 1 with hYdef
  have hYpos : 0 < Y := D.target.oppLen_pos 1
  rw [ha, hb] at hwY hwX
  rw [hXY] at hwX
  have hy : 0 < Y / c := div_pos hYpos hc
  obtain ⟨r, hr⟩ := Erdos634.Row15Conj.row15_algebraic s (Y / c) S N na nb nc ma mb mc hs0 hs1 hy
    (by field_simp; linarith [hSY])
    hArea
    (by field_simp; linear_combination hwY)
    (by field_simp; linear_combination hwX)
  refine ⟨r, ?_, ?_⟩
  · rw [ha, hr]
  · rw [hb, hr]

/-- **Non-vacuity of `row15_algebraic`'s hypotheses** (joint): `s = 1/2`, `S = 5`, `N = 77`,
`y = 4`, `Y`-word `4c`, `X`-word `7c` satisfy all of them at once (`h(1/2) = 5/4`,
`g(1/2) = 77/16`, `77·25/16 = 25·77/16`). -/
theorem Row15.algebraic_witness :
    ∃ r : ℚ, ((1 : ℝ) / 2) = r :=
  Erdos634.Row15Conj.row15_algebraic (1 / 2) 4 5 77 0 0 4 0 0 7 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **Non-vacuity of the angle hypotheses**: for `α ∈ (0, π/3)`, `β = (π − 3α)/2 > 0` and the
target `(2α, α, 2β)` is a genuine triangle's angle triple (positive, sum `π`).  Irrational `α/π`
in this range exist; no real tiling of the row-15 target is known, so the full bundle has no Lean
witness. -/
theorem Row15.rational_real_angle_witness (α : ℝ) (h0 : 0 < α) (h1 : α < Real.pi / 3) :
    let β := (Real.pi - 3 * α) / 2
    0 < β ∧ 3 * α + 2 * β = Real.pi ∧ α + β + (2 * α + β) = Real.pi ∧
      0 < 2 * β ∧ 2 * α + α + 2 * β = Real.pi := by
  intro β
  refine ⟨by simp only [β]; linarith, by simp only [β]; ring, by simp only [β]; ring,
    by simp only [β]; linarith, by simp only [β]; ring⟩

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row15.rational_real
#print axioms Erdos634.Geometry.Row15.algebraic_witness
#print axioms Erdos634.Geometry.Row15.rational_real_angle_witness
