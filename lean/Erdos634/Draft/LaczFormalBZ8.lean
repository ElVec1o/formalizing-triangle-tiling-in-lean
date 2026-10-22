-- Draft/LaczFormalBZ8.lean -- regularity is AUTOMATIC for the equilateral target, the 2 pi/3 tile and alpha not in Q pi (Beeson-Zhang, Sect. 2.2: "any vertex is one of the types of Table 2"; Laczkovich's
-- hypothesis "regular" in Theorem 2.1 is then a consequence), and the PolyTiling form of the witness for `caseIII_tri_irr`.
--   `regular_of_irr`          : T : PolyTiling N 3, gamma = 2 pi/3, alpha not in Q pi, all polygon angles pi/3  =>  RegularPQ T.C;
--   `polyTiling_of_dissection`: a CongruentDissection of an equilateral triangle by the tile `TwoPiThreeData` is a PolyTiling (model relabeled so that the angles are (alpha, beta, gamma));
--   `bz_thm21_dissection`     : for such a dissection (alpha not in Q pi) the PolyTiling is regular and satisfies Thm21Concl.
-- UNAUDITED.  Credit: Beeson-Zhang (arXiv 2604.01314v1), Laczkovich (DCG 48 (2012), Thm 2.1).
import Erdos634.Draft.LaczFormalBZ7

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

theorem regular_of_irr (T : PolyTiling N 3) (hγ : angleAt T.C.model 2 = 2 * Real.pi / 3)
    (hα : ¬ ∃ r : ℚ, angleAt T.C.model 0 = (r : ℝ) * Real.pi) (hPang : ∀ i, T.P.angle i = Real.pi / 3) : RegularPQ T.C := by
  classical
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  obtain ⟨idx, hidx, hidxA⟩ := exists_idx_both T.C
  refine ⟨idx, hidxA, fun X => ?_⟩
  have hαβ : T.C.model.angleAt 0 + T.C.model.angleAt 1 = Real.pi / 3 := by
    have := Erdos634.Draft.LaczFormal.angleAt_sum T.C.model
    have hγ' : T.C.model.angleAt 2 = 2 * Real.pi / 3 := hγ
    linarith
  have hγ' : T.C.model.angleAt 2 = 2 * Real.pi / 3 := hγ
  have hα' : ¬ ∃ r : ℚ, T.C.model.angleAt 0 = (r : ℝ) * Real.pi := hα
  by_cases hvert : ∃ j k, (T.C.tile j).pts k = X
  · exact (vertex_type T.C T.P T.region_eq idx hidxA hγ' hαβ hα' hPang hvert).1
  · show cnt T.C idx X 0 = cnt T.C idx X 1
    rw [cnt_zero_of_not_vertex' T.C idx hvert 0, cnt_zero_of_not_vertex' T.C idx hvert 1]

/-- A congruent dissection of an equilateral triangle by the tile `(α, π/3 - α, 2π/3)` is a `PolyTiling` (model relabeled to `(α, β, γ)`). -/
noncomputable def polyTiling_of_dissection (D : CongruentDissection N) {α a b c : ℝ}
    (h : D.model.TwoPiThreeData α a b c)
    (heq : ∀ j : Fin 3, dist (D.target.pts j) (D.target.pts (j + 1)) = dist (D.target.pts 0) (D.target.pts 1)) : PolyTiling N 3 :=
  have hP := Classical.choose_spec (exists_convpoly_of_equilateral D.target heq)
  { C := relabel D.toRegion (Classical.choose h)
    P := Classical.choose (exists_convpoly_of_equilateral D.target heq)
    region_eq := by rw [hP.1]; rfl }

theorem polyTiling_angles (D : CongruentDissection N) {α a b c : ℝ}
    (h : D.model.TwoPiThreeData α a b c)
    (heq : ∀ j : Fin 3, dist (D.target.pts j) (D.target.pts (j + 1)) = dist (D.target.pts 0) (D.target.pts 1)) :
    angleAt (polyTiling_of_dissection D h heq).C.model 0 = α ∧ angleAt (polyTiling_of_dissection D h heq).C.model 1 = Real.pi / 3 - α ∧
      angleAt (polyTiling_of_dissection D h heq).C.model 2 = 2 * Real.pi / 3 ∧
      (∀ i, (polyTiling_of_dissection D h heq).P.angle i = Real.pi / 3) := by
  have hP := Classical.choose_spec (exists_convpoly_of_equilateral D.target heq)
  have hσ := Classical.choose_spec h
  obtain ⟨h0, -, h1, -, h2, -⟩ := hσ
  set σ := Classical.choose h
  refine ⟨?_, ?_, ?_, hP.2⟩
  · show angleAt (relabel D.toRegion σ).model 0 = α
    rw [relabel_angleAt]; exact h0
  · show angleAt (relabel D.toRegion σ).model 1 = _
    rw [relabel_angleAt]; exact h1
  · show angleAt (relabel D.toRegion σ).model 2 = _
    rw [relabel_angleAt]; exact h2

/-- **Beeson-Zhang Theorem 5.2 as Laczkovich's Theorem 2.1 for the real tilings of an equilateral triangle by a `2π/3` tile with `α ∉ ℚπ`**: the associated `PolyTiling` is regular and satisfies a
conclusion of Theorem 2.1 (conclusion (iv)). -/
theorem bz_thm21_dissection (D : CongruentDissection N) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoPiThreeData α a b c)
    (heq : ∀ j : Fin 3, dist (D.target.pts j) (D.target.pts (j + 1)) = dist (D.target.pts 0) (D.target.pts 1)) :
    ∃ T : PolyTiling N 3, RegularPQ T.C ∧ Thm21Concl T.C T.P := by
  obtain ⟨hA0, hA1, hA2, hP⟩ := polyTiling_angles D h heq
  set T := polyTiling_of_dissection D h heq with hT
  have hα' : ¬ ∃ r : ℚ, angleAt T.C.model 0 = (r : ℝ) * Real.pi := by rw [hA0]; exact hα
  have hreg := regular_of_irr T hA2 hα' hP
  exact ⟨T, hreg, caseIII_tri_irr T hreg hA2 hα'⟩

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.regular_of_irr
#print axioms Erdos634.Draft.LaczFormal.RG.bz_thm21_dissection
