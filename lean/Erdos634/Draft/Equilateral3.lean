-- Draft/Equilateral3.lean — `CongruentDissection 3`: the equilateral triangle cut into three
-- (30°,30°,120°) triangles from its centre.
-- Imported via AllNew8.lean:183 → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.Draft.CentroidSplit
import Erdos634.Draft.SumTwoSquares

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.CentroidSplit Erdos634.Draft.SumTwoSquares

namespace Erdos634.Draft.Equilateral3

theorem exists_dissection_3_model : ∃ (D : CongruentDissection 3) (h : det3 0 0 6 0 3 (Real.sqrt 3) ≠ 0),
    D.model = mkTri 0 0 6 0 3 (Real.sqrt 3) h := by
  set r : ℝ := Real.sqrt 3 with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by norm_num)
  have hr2 : r ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have dT : det3 0 0 6 0 3 (3 * r) ≠ 0 := by unfold det3; nlinarith
  have d0 : det3 0 0 6 0 3 r ≠ 0 := by unfold det3; nlinarith
  have d1 : det3 6 0 3 (3 * r) 3 r ≠ 0 := by unfold det3; nlinarith
  have d2 : det3 3 (3 * r) 0 0 3 r ≠ 0 := by unfold det3; nlinarith
  set T : Tri := mkTri 0 0 6 0 3 (3 * r) dT
  set T0 : Tri := mkTri 0 0 6 0 3 r d0
  set T1 : Tri := mkTri 6 0 3 (3 * r) 3 r d1
  set T2 : Tri := mkTri 3 (3 * r) 0 0 3 r d2
  have hG : G T = mkPt 3 r := by
    unfold G
    ext i; fin_cases i <;> simp [T, mkTri, mkPt_zero, mkPt_one] <;> ring
  obtain ⟨hcov, h01, h12, h02⟩ := centroid_split T T0 T1 T2
    (by show mkPt (0 : ℝ) 0 = mkPt 0 0; rfl) (by show mkPt (6 : ℝ) 0 = mkPt 6 0; rfl)
    (by rw [hG]; rfl)
    (by show mkPt (6 : ℝ) 0 = mkPt 6 0; rfl) (by show mkPt (3 : ℝ) (3 * r) = mkPt 3 (3 * r); rfl)
    (by rw [hG]; rfl)
    (by show mkPt (3 : ℝ) (3 * r) = mkPt 3 (3 * r); rfl) (by show mkPt (0 : ℝ) 0 = mkPt 0 0; rfl)
    (by rw [hG]; rfl)
  have s36 : dist (mkPt (0 : ℝ) 0) (mkPt 6 0) = 6 := dsq _ _ _ _ _ (by norm_num) (by norm_num)
  have c1 : T1.Congruent T0 := by
    refine SssCongruent.congruent_of_dist_three ?_ ?_ ?_
    · show dist (mkPt (6 : ℝ) 0) (mkPt 3 (3 * r)) = dist (mkPt (0 : ℝ) 0) (mkPt 6 0)
      rw [s36]; exact dsq _ _ _ _ _ (by norm_num) (by nlinarith)
    · show dist (mkPt (3 : ℝ) (3 * r)) (mkPt 3 r) = dist (mkPt (6 : ℝ) 0) (mkPt 3 r)
      exact eqsq dist_nonneg dist_nonneg (by rw [dist_sq_mkPt, dist_sq_mkPt]; nlinarith)
    · show dist (mkPt (3 : ℝ) r) (mkPt 6 0) = dist (mkPt (3 : ℝ) r) (mkPt 0 0)
      exact eqsq dist_nonneg dist_nonneg (by rw [dist_sq_mkPt, dist_sq_mkPt]; nlinarith)
  have c2 : T2.Congruent T0 := by
    refine SssCongruent.congruent_of_dist_three ?_ ?_ ?_
    · show dist (mkPt (3 : ℝ) (3 * r)) (mkPt 0 0) = dist (mkPt (0 : ℝ) 0) (mkPt 6 0)
      rw [s36]; exact dsq _ _ _ _ _ (by norm_num) (by nlinarith)
    · show dist (mkPt (0 : ℝ) 0) (mkPt 3 r) = dist (mkPt (6 : ℝ) 0) (mkPt 3 r)
      exact eqsq dist_nonneg dist_nonneg (by rw [dist_sq_mkPt, dist_sq_mkPt]; nlinarith)
    · show dist (mkPt (3 : ℝ) r) (mkPt 3 (3 * r)) = dist (mkPt (3 : ℝ) r) (mkPt 0 0)
      exact eqsq dist_nonneg dist_nonneg (by rw [dist_sq_mkPt, dist_sq_mkPt]; nlinarith)
  refine ⟨⟨⟨T, ![T0, T1, T2], ?_, ?_⟩, T0, ?_⟩, d0, rfl⟩
  · rw [← hcov]
    ext x
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl (Or.inl hi)
      · exact Or.inl (Or.inr hi)
      · exact Or.inr hi
    · rintro ((h | h) | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | exact h01 | exact h01.symm | exact h12 | exact h12.symm | exact h02 | exact h02.symm
  · intro i; fin_cases i
    · exact Tri.Congruent.refl T0
    · exact c1
    · exact c2

theorem exists_dissection_3 : Nonempty (CongruentDissection 3) := by
  obtain ⟨D, -, -⟩ := exists_dissection_3_model
  exact ⟨D⟩

end Erdos634.Draft.Equilateral3

#print axioms Erdos634.Draft.Equilateral3.exists_dissection_3
