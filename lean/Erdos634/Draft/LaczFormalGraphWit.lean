-- Draft/LaczFormalGraphWit.lean -- WITNESS for D0 (`LaczFormalGraphLocal.vertex_fan_interior`): an explicit `Dissection 3` (the equilateral triangle
-- (0,0),(6,0),(3,3 sqrt 3) cut into three triangles from its centroid, as in `LaczFormalL6Wit2`) with an interior vertex `V` = the
-- centroid; the hypotheses of `vertex_fan_interior` hold, so its conclusion (the cyclic fan of the three tiles at `V`) is non-vacuous.
-- UNAUDITED.
import Erdos634.Draft.LaczFormalGraphLocal
import Erdos634.Draft.CentroidSplit
import Erdos634.Draft.LaczFormalGraphSide
import Erdos634.Draft.LaczFormalGraphCorner
import Erdos634.Draft.LaczFormalL6Wit3

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.CentroidSplit

namespace Erdos634.Draft.LaczFormal.Graph

theorem dT'' : det3 0 0 6 0 3 (3 * Real.sqrt 3) ≠ 0 := by
  have h0 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  unfold det3; nlinarith

theorem centroid_dissection_witness :
    ∃ (D : Dissection 3) (V : Plane), V ∈ interior D.target.carrier ∧ (∃ i k, (D.tile i).pts k = V) ∧
      (∃ i k, (D.tile i).pts k = D.target.pts 0) := by
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
  refine ⟨⟨T, ![T0, T1, T2], ?_, ?_⟩, mkPt 3 r, ?_, ⟨0, 2, rfl⟩, 0, 0, rfl⟩
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
  · rw [← hG]
    exact (T.mem_interior_iff_coord_pos _).mpr (fun k => by rw [coord_G]; norm_num)

/-- **Non-vacuity of D0**: the hypotheses of `vertex_fan_interior` are satisfied by this dissection, and the conclusion holds. -/
theorem vertex_fan_interior_witness :
    ∃ (D : Dissection 3) (V : Plane) (p q : AtV D V → V2) (e : ℕ → AtV D V),
      (∀ s, SecOK (p s) (q s)) ∧ (∀ n, Par (p (e (n + 1))) (q (e n))) := by
  obtain ⟨D, V, hV, hvert, -⟩ := centroid_dissection_witness
  obtain ⟨p, q, e, hok, -, -, -, hP, -, -, -⟩ := vertex_fan_interior D V hV hvert
  exact ⟨D, V, p, q, e, hok, hP⟩

/-- A `Dissection 2` (the equilateral triangle cut by an altitude, as in `LaczFormalL6Wit3.exists_D2`) with a vertex `V` of the tiling in
the relative interior of a side of the target. -/
theorem side_dissection_witness :
    ∃ (D : Dissection 2) (V : Plane) (m : Fin 3), D.target.basis.coord m V = 0 ∧
      (∀ j, j ≠ m → 0 < D.target.basis.coord j V) ∧ ∃ i k, (D.tile i).pts k = V := by
  have hs := halve_split TT3 P0 P1
    (by show mkPt (0 : ℝ) 0 = mkPt 0 0; rfl) (by rw [mid_eq]; rfl)
    (by show mkPt (3 : ℝ) (3 * Real.sqrt 3) = mkPt 3 (3 * Real.sqrt 3); rfl)
    (by show mkPt (6 : ℝ) 0 = mkPt 6 0; rfl) (by rw [mid_eq]; rfl)
    (by show mkPt (3 : ℝ) (3 * Real.sqrt 3) = mkPt 3 (3 * Real.sqrt 3); rfl)
  obtain ⟨hcov, hdis⟩ := hs
  refine ⟨⟨TT3, ![P0, P1], ?_, ?_⟩, Mid TT3, 2, ?_, ?_, 0, 1, ?_⟩
  · rw [← hcov]
    ext x
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
    · rintro (h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | exact hdis | exact hdis.symm
  · show TT3.basis.coord 2 (Mid TT3) = 0
    rw [coord_Mid]; simp
  · intro j hj
    show 0 < TT3.basis.coord j (Mid TT3)
    rw [coord_Mid]; simp [hj]
  · show P0.pts 1 = Mid TT3
    rw [mid_eq]; rfl

/-- **Non-vacuity of the side fan**: the hypotheses of `vertex_fan_side` hold for this dissection, and its conclusion holds. -/
theorem vertex_fan_side_witness :
    ∃ (D : Dissection 2) (V : Plane) (pT : V2) (p q : AtV D V → V2) (e : ℕ → Option (AtV D V)),
      pT ≠ 0 ∧ (∀ s, SecOK (p s) (q s)) ∧ (∀ n, Par (extP pT p (e (n + 1))) (extQ pT q (e n))) := by
  obtain ⟨D, V, m, h0, hpos, hvert⟩ := side_dissection_witness
  obtain ⟨pT, p, q, e, hpT, -, hok, -, -, -, hP, -, -, -⟩ := vertex_fan_side D V m h0 hpos hvert
  exact ⟨D, V, pT, p, q, e, hpT, hok, hP⟩

/-- **Non-vacuity of the corner fan**: a corner of the centroid 3-split is a vertex of a tile, and the corner fan exists. -/
theorem vertex_fan_corner_witness :
    ∃ (D : Dissection 3) (pT qT : V2) (p q : AtV D (D.target.pts 0) → V2) (e : ℕ → AtV D (D.target.pts 0) ⊕ Bool),
      SecOK pT qT ∧ 0 < crs pT qT ∧ (∀ s, SecOK (p s) (q s)) := by
  obtain ⟨D, V, -, -, hc⟩ := centroid_dissection_witness
  obtain ⟨pT, qT, p, q, e, h1, h2, -, -, -, h5, -⟩ := vertex_fan_corner D 0 hc
  exact ⟨D, pT, qT, p, q, e, h1, h2, h5⟩

end Erdos634.Draft.LaczFormal.Graph
