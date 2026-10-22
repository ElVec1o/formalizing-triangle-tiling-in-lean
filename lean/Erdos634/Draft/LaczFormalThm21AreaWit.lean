-- Draft/LaczFormalThm21AreaWit.lean -- witness for Lemma 4.1 (LaczFormalThm21Area): the unit square cut along a diagonal
-- into two congruent right isosceles triangles (a genuine CongruentRegionDissection of a parallelogram; tile angles pi/4, pi/4, pi/2).
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Lemma 4.1).
import Erdos634.Draft.LaczFormalThm21Def
import Erdos634.CertCoord

open MeasureTheory Erdos634.Geometry Erdos634.AreaDet Erdos634.RegionDissection Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.Thm21

theorem mkPt_10 : mkPt 1 0 = pb 0 := by ext i; fin_cases i <;> simp [mkPt, pb_apply_self]
theorem mkPt_01 : mkPt 0 1 = pb 1 := by ext i; fin_cases i <;> simp [mkPt, pb_apply_self]
theorem mkPt_00 : mkPt 0 0 = 0 := by ext i; fin_cases i <;> simp [mkPt]
theorem mkPt_11 : mkPt 1 1 = reflC := by ext i; fin_cases i <;> simp [mkPt, reflC, pb_apply_self]

theorem hdet0 : det3 1 0 0 1 0 0 ≠ 0 := by norm_num [det3]
theorem hdet1 : det3 0 1 1 0 1 1 ≠ 0 := by norm_num [det3]

/-- model tile: vertices (1,0), (0,1), (0,0); the right angle is at vertex 2. -/
noncomputable def sqT0 : Tri := mkTri 1 0 0 1 0 0 hdet0
/-- the point reflection of it through (1/2,1/2): vertices (0,1), (1,0), (1,1). -/
noncomputable def sqT1 : Tri := mkTri 0 1 1 0 1 1 hdet1

theorem sqT0_carrier : sqT0.carrier = stdCarrier := by
  unfold Tri.carrier stdCarrier
  congr 1
  ext x
  simp only [sqT0, mkTri_pts, Set.mem_range, mkPt_10, mkPt_01, mkPt_00]
  constructor
  · rintro ⟨i, rfl⟩; fin_cases i
    · exact ⟨1, by simp⟩
    · exact ⟨2, by simp⟩
    · exact ⟨0, by simp⟩
  · rintro ⟨i, rfl⟩; fin_cases i
    · exact ⟨2, by simp⟩
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

theorem sqT1_carrier : sqT1.carrier = stdCarrier2 := by
  unfold Tri.carrier stdCarrier2
  congr 1
  ext x
  simp only [sqT1, mkTri_pts, Set.mem_range, mkPt_11, mkPt_01, mkPt_10]
  constructor
  · rintro ⟨i, rfl⟩; fin_cases i
    · exact ⟨1, by simp⟩
    · exact ⟨2, by simp⟩
    · exact ⟨0, by simp⟩
  · rintro ⟨i, rfl⟩; fin_cases i
    · exact ⟨2, by simp⟩
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

theorem pgramSet_unit : pgramSet 0 (pb 0) (pb 1) = stdSquare := by
  rw [pgramSet_eq]
  ext x
  simp only [Set.mem_image, zero_add]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [pgMap_apply]
    have : y 0 • pb 0 + y 1 • pb 1 = y := by ext i; fin_cases i <;> simp [pb_apply_self]
    rw [this]; exact hy
  · intro hx
    refine ⟨x, hx, ?_⟩
    rw [pgMap_apply]
    ext i; fin_cases i <;> simp [pb_apply_self]

theorem sqT0_sqT1_congruent : sqT1.Congruent sqT0 := by
  refine ⟨(IsometryEquiv.neg Plane).trans (IsometryEquiv.addLeft reflC), Equiv.refl _, fun k => ?_⟩
  fin_cases k
  · show reflC + -(mkPt 0 1) = mkPt 1 0
    rw [mkPt_01, mkPt_10]; simp [reflC]
  · show reflC + -(mkPt 1 0) = mkPt 0 1
    rw [mkPt_01, mkPt_10]; simp [reflC]
  · show reflC + -(mkPt 1 1) = mkPt 0 0
    rw [mkPt_11, mkPt_00]; simp

/-- **The witness:** the unit square as a congruent dissection into two right isosceles triangles. -/
noncomputable def sqDiss : CongruentRegionDissection 2 where
  region := pgramSet 0 (pb 0) (pb 1)
  tile := ![sqT0, sqT1]
  covers := by
    rw [pgramSet_unit, ← stdCarrier_union_stdCarrier2, ← sqT0_carrier, ← sqT1_carrier]
    ext x; simp [Fin.exists_fin_two]
  interiors_disjoint := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simpa [sqT0_carrier, sqT1_carrier] using interior_stdCarrier_disjoint
    · simpa [sqT0_carrier, sqT1_carrier] using interior_stdCarrier_disjoint.symm
    · exact absurd rfl hij
  model := sqT0
  tiles_congruent := by
    intro i
    fin_cases i
    · exact Tri.Congruent.refl _
    · exact sqT0_sqT1_congruent

theorem sqT0_angle2 : angleAt sqT0 2 = InnerProductGeometry.angle (pb 0 - 0) (pb 1 - 0) := by
  show EuclideanGeometry.angle (mkPt 1 0) (mkPt 0 0) (mkPt 0 1) = _
  rw [mkPt_10, mkPt_00, mkPt_01]; rfl

/-- Hypotheses of `lemma41'` hold on the witness: the angle hypothesis (trivially, `u = pb 0, w = pb 1` are the model's
edges at the right-angle vertex) and `|w| = 1 * a` (`a = sideOpp 0 = 1`). -/
theorem sq_hang : Real.sin (InnerProductGeometry.angle (pb 0) (pb 1)) = Real.sin (angleAt sqDiss.model 2) := by
  show _ = Real.sin (angleAt sqT0 2)
  rw [sqT0_angle2]; simp

theorem sq_side_a : sideOpp sqDiss.model 0 = 1 := by
  show dist (mkPt 0 1) (mkPt 0 0) = 1
  rw [mkPt_01, mkPt_00]
  simp [pb]

theorem sq_norm_w : ‖pb 1‖ = 1 * sideOpp sqDiss.model 0 := by
  rw [sq_side_a]; simp [pb]

/-- Lemma 4.1 non-vacuously: on the unit-square witness it returns `|w| / |u| = q * (sin alpha / sin beta)`. -/
theorem lemma41_witness : ∃ q : ℚ, ‖pb 1‖ / ‖pb 0‖ =
    q * (Real.sin (angleAt sqDiss.model 0) / Real.sin (angleAt sqDiss.model 1)) :=
  lemma41' sqDiss 0 (pb 0) (pb 1) rfl sq_hang 1 one_pos (by simpa using sq_norm_w)

/-- The unit square as a `ConvPoly 4`. -/
noncomputable def sqPoly : ConvPoly 4 where
  v := ![mkPt 0 0, mkPt 1 0, mkPt 1 1, mkPt 0 1]
  three_le := by norm_num
  left := by
    intro i j hji hji1
    fin_cases i <;> fin_cases j <;> first | (exfalso; revert hji hji1; decide) | simp [cross2, mkPt]

/-- The unit-square polygon tiling (two congruent right isosceles triangles). -/
noncomputable def sqTiling : PolyTiling 2 4 where
  C := sqDiss
  P := sqPoly
  region_eq := by
    have hpg : sqPoly.v 0 + sqPoly.v 2 = sqPoly.v 1 + sqPoly.v 3 := by
      show mkPt 0 0 + mkPt 1 1 = mkPt 1 0 + mkPt 0 1
      ext i; fin_cases i <;> simp [mkPt]
    show pgramSet 0 (pb 0) (pb 1) = _
    rw [poly4_carrier sqPoly hpg]
    show _ = pgramSet (mkPt 0 0) (mkPt 1 0 - mkPt 0 0) (mkPt 0 1 - mkPt 0 0)
    rw [mkPt_10, mkPt_01, mkPt_00]; simp

theorem sq_hpg : sqTiling.P.v 0 + sqTiling.P.v 2 = sqTiling.P.v 1 + sqTiling.P.v 3 := by
  show mkPt 0 0 + mkPt 1 1 = mkPt 1 0 + mkPt 0 1
  ext i; fin_cases i <;> simp [mkPt]

/-- `lemma41_poly` fires on the witness (hypotheses: parallelogram, angle `π/2 = γ` at `v0`, side `v3 v0` = `1 · a`). -/
theorem lemma41_poly_witness :
    (∃ q : ℚ, sqTiling.P.side 0 / sqTiling.P.side 3 = q * (Real.sin (angleAt sqTiling.C.model 0) / Real.sin (angleAt sqTiling.C.model 1))) ∨
    (∃ q : ℚ, sqTiling.P.side 3 / sqTiling.P.side 0 = q * (Real.sin (angleAt sqTiling.C.model 0) / Real.sin (angleAt sqTiling.C.model 1))) := by
  refine lemma41_poly sqTiling sq_hpg (Or.inl ?_) 1 one_pos (Or.inr ?_)
  · show cornerAngle (mkPt 0 1) (mkPt 0 0) (mkPt 1 0) = angleAt sqT0 2
    show _ = EuclideanGeometry.angle (mkPt 1 0) (mkPt 0 0) (mkPt 0 1)
    unfold cornerAngle
    rw [EuclideanGeometry.angle_comm]
  · rw [Nat.cast_one, one_mul]
    show _ = sideOpp sqDiss.model 0
    rw [sq_side_a]
    show dist (mkPt 0 1) (mkPt 0 0) = 1
    rw [mkPt_01, mkPt_00]; simp [pb]

/-! ## The unit-square witness is a REGULAR tiling and satisfies Concl1 (controls for `RegularPQ`, `Concl1`, `ConvPoly`) -/

theorem sq_tile_pts (i : Fin 2) (k : Fin 3) : (sqDiss.tile i).pts k = (if i = 0 then sqT0 else sqT1).pts k := by
  fin_cases i <;> rfl

theorem sq_swap_pts (i : Fin 2) : (sqDiss.tile (i + 1)).pts 1 = (sqDiss.tile i).pts 0 := by
  fin_cases i
  · show mkPt 1 0 = mkPt 1 0; rfl
  · show mkPt 0 1 = mkPt 0 1; rfl

theorem sq_swap_pts' (i : Fin 2) : (sqDiss.tile (i + 1)).pts 0 = (sqDiss.tile i).pts 1 := by
  fin_cases i
  · show mkPt 0 1 = mkPt 0 1; rfl
  · show mkPt 1 0 = mkPt 1 0; rfl

theorem angleAt_of_iso {T U : Tri} (f : Plane ≃ᵢ Plane) (hf : ∀ k, f (T.pts k) = U.pts k) (v : Fin 3) :
    angleAt U v = angleAt T v := by
  unfold angleAt cornerAngle
  rw [← hf (v + 1), ← hf v, ← hf (v + 2)]
  have := (f.toRealAffineIsometryEquiv.toAffineIsometry).angle_map (T.pts (v + 1)) (T.pts v) (T.pts (v + 2))
  simpa using this

noncomputable def sqF : Plane ≃ᵢ Plane := (IsometryEquiv.neg Plane).trans (IsometryEquiv.addLeft reflC)

theorem sqF_pts (k : Fin 3) : sqF (sqT1.pts k) = sqT0.pts k := by
  fin_cases k
  · show reflC + -(mkPt 0 1) = mkPt 1 0
    rw [mkPt_01, mkPt_10]; simp [reflC]
  · show reflC + -(mkPt 1 0) = mkPt 0 1
    rw [mkPt_01, mkPt_10]; simp [reflC]
  · show reflC + -(mkPt 1 1) = mkPt 0 0
    rw [mkPt_11, mkPt_00]; simp

theorem sq_angle_eq (v : Fin 3) : angleAt sqDiss.model v = angleAt (sqDiss.tile 1) v :=
  angleAt_of_iso sqF sqF_pts v

theorem sq_angle_eq0 (v : Fin 3) : angleAt sqDiss.model v = angleAt (sqDiss.tile 0) v := rfl

/-- The unit-square tiling is regular in the sense of `RegularPQ` (with `idx = id`: each diagonal endpoint carries one `α` and one `β`). -/
theorem sq_regular : RegularPQ sqDiss := by
  refine ⟨fun _ => 1, fun i v => ?_, fun X => ?_⟩
  · fin_cases i
    · exact sq_angle_eq0 v
    · exact sq_angle_eq v
  · unfold cntR
    refine Finset.card_nbij' (fun p => (p.1 + 1, (1 : Fin 3))) (fun p => (p.1 + 1, (0 : Fin 3))) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Equiv.Perm.coe_one, id_eq] at hp ⊢
      obtain ⟨h1, h2⟩ := hp
      rw [h2] at h1
      exact ⟨by rw [sq_swap_pts]; exact h1, trivial⟩
    · intro p hp
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Equiv.Perm.coe_one, id_eq] at hp ⊢
      obtain ⟨h1, h2⟩ := hp
      rw [h2] at h1
      exact ⟨by rw [sq_swap_pts']; exact h1, trivial⟩
    · intro p hp
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Equiv.Perm.coe_one, id_eq] at hp
      obtain ⟨i, k⟩ := p
      simp only at hp ⊢
      obtain ⟨h1, h2⟩ := hp
      subst h2
      ext
      · simp only; fin_cases i <;> rfl
      · rfl
    · intro p hp
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Equiv.Perm.coe_one, id_eq] at hp
      obtain ⟨i, k⟩ := p
      simp only at hp ⊢
      obtain ⟨h1, h2⟩ := hp
      subst h2
      ext
      · simp only; fin_cases i <;> rfl
      · rfl

theorem sq_side_b : sideOpp sqDiss.model 1 = 1 := by
  show dist (mkPt 0 0) (mkPt 1 0) = 1
  rw [mkPt_00, mkPt_10]; simp [pb]

/-- **Control for `Concl1`:** the unit-square witness satisfies conclusion (i) of Theorem 2.1 (ratio of sides 1 = 1 * sin α / sin β). -/
theorem sq_concl1 : Concl1 sqDiss sqPoly := by
  refine ⟨⟨rfl, fun i => ?_⟩, ⟨0, ?_⟩, Or.inl ⟨1, ?_⟩⟩
  · fin_cases i <;> (show _ + _ = _ + _; ext j; fin_cases j <;> simp [sqPoly, mkPt])
  · show cornerAngle (mkPt 0 1) (mkPt 0 0) (mkPt 1 0) = angleAt sqT0 2
    show _ = EuclideanGeometry.angle (mkPt 1 0) (mkPt 0 0) (mkPt 0 1)
    unfold cornerAngle
    rw [EuclideanGeometry.angle_comm]
  · have h := side_ratio_eq_sin sqDiss.model
    rw [sq_side_a, sq_side_b] at h
    have e0 : sqPoly.side 0 = 1 := by
      show dist (mkPt 0 0) (mkPt 1 0) = 1
      rw [mkPt_00, mkPt_10]; simp [pb]
    have e1 : sqPoly.side 1 = 1 := by
      show dist (mkPt 1 0) (mkPt 1 1) = 1
      rw [mkPt_10, mkPt_11]; simp [pb, reflC]
    rw [e0, e1, ← h]; norm_num

end Erdos634.Draft.LaczFormal.Thm21
