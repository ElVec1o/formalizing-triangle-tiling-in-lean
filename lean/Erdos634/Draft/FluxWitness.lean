-- Draft/FluxWitness.lean — NON-VACUITY WITNESS and NEGATIVE CONTROL for `Dissection.flux_cancel`
-- (Draft/FluxCancel.lean).  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).  Design: (private working notes, not included) §5.
--
-- * Every hypothesis of `flux_cancel` is exhibited on the REAL kernel-checked 44-tiling
--   `Tiling44Bridge.dissection` (target `(16,16,22)·8`, 44 copies of `(2,3,4)·8`) with the nonlinear
--   odd weight `cubeX d = (d_x)³`; the conclusion is evaluated: both sides equal `1485/16`
--   (`tiles44_flux_cubeX`).  The float check `check_flux_numeric.out` reported 92.8125 = 1485/16.
-- * The dissection is genuinely NOT edge-to-edge (`tiling44_T_junction`): vertex 1 of piece 8,
--   `(78, 2√15)`, lies in the open segment of piece 7's edge 2, from `(85, 3√15)` to `(64, 0)`.
-- * Negative control: the weight `f ≡ 1` is not odd (`one_not_odd`), and without oddness the
--   conclusion is FALSE on the same dissection: the tiles' perimeters sum to `3168`, the target's is
--   `432` (`flux_cancel_44_needs_odd`).
--
-- Local re-derivations (import weight; named plainly): `target44_pts0/1/2` re-derive
-- `Tiling44WallSetup.tiling44_targetTri_pts0/1/2` (that module imports SideWall and CollarDisjointM4);
-- `dist_of_sq'` and `target44_d01/d12/d20` re-derive `Draft.ApexWitness44.dist_of_sq`/`tgt_d01…`.
import Erdos634.Draft.FluxCancel
import Erdos634.Tiling44Bridge

open scoped Classical

namespace Erdos634.Draft.FluxWitness

open Erdos634.Geometry Erdos634.Z15Real Erdos634.Tiling44Bridge Erdos634.CertCoord

/-- The nonlinear odd weight `f(d) = (d_x)³`. -/
noncomputable def cubeX (d : Dir) : ℝ := (d.1 0) ^ 3

theorem cubeX_odd (d : Dir) : cubeX (Dir.neg d) = - cubeX d := by
  have h : (Dir.neg d).1 0 = -(d.1 0) := by simp [Dir.neg]
  unfold cubeX
  rw [h]
  ring

/-- **`lem:cancel` on the real 44-tiling.** -/
theorem flux_cancel_44 :
    ∑ i, (dissection.tile i).flux cubeX = dissection.target.flux cubeX :=
  dissection.flux_cancel cubeX cubeX_odd

/-! ## Evaluating the target side -/

theorem target44_pts0 : targetTri.pts 0 = mkPt 0 0 := by
  rw [targetTri_pts_eq]
  show mkPt (toR (zx (toZPt (Tiling44.t1 Tiling44.target))))
    (toR (zy (toZPt (Tiling44.t1 Tiling44.target)))) = mkPt 0 0
  have hx : zx (toZPt (Tiling44.t1 Tiling44.target)) = ((0:ℤ),(0:ℤ)) := by decide
  have hy : zy (toZPt (Tiling44.t1 Tiling44.target)) = ((0:ℤ),(0:ℤ)) := by decide
  rw [hx, hy]; simp [toR]

theorem target44_pts1 : targetTri.pts 1 = mkPt 176 0 := by
  rw [targetTri_pts_eq]
  show mkPt (toR (zx (toZPt (Tiling44.t2 Tiling44.target))))
    (toR (zy (toZPt (Tiling44.t2 Tiling44.target)))) = mkPt 176 0
  have hx : zx (toZPt (Tiling44.t2 Tiling44.target)) = ((176:ℤ),(0:ℤ)) := by decide
  have hy : zy (toZPt (Tiling44.t2 Tiling44.target)) = ((0:ℤ),(0:ℤ)) := by decide
  rw [hx, hy]; simp [toR]

theorem target44_pts2 : targetTri.pts 2 = mkPt 88 (24 * Real.sqrt 15) := by
  rw [targetTri_pts_eq]
  show mkPt (toR (zx (toZPt (Tiling44.t3 Tiling44.target))))
    (toR (zy (toZPt (Tiling44.t3 Tiling44.target)))) = mkPt 88 (24 * Real.sqrt 15)
  have hx : zx (toZPt (Tiling44.t3 Tiling44.target)) = ((88:ℤ),(0:ℤ)) := by decide
  have hy : zy (toZPt (Tiling44.t3 Tiling44.target)) = ((0:ℤ),(24:ℤ)) := by decide
  rw [hx, hy]; simp [toR]

theorem dist_of_sq' {x y : Plane} {s : ℝ} (hs : 0 ≤ s) (h : dist x y ^ 2 = s ^ 2) :
    dist x y = s :=
  (pow_left_inj₀ dist_nonneg hs two_ne_zero).mp h

theorem target44_d01 : dist (targetTri.pts 0) (targetTri.pts 1) = 176 :=
  dist_of_sq' (by norm_num) (by rw [targetTri_sides.1]; norm_num)
theorem target44_d12 : dist (targetTri.pts 1) (targetTri.pts 2) = 128 :=
  dist_of_sq' (by norm_num) (by rw [targetTri_sides.2.1]; norm_num)
theorem target44_d20 : dist (targetTri.pts 2) (targetTri.pts 0) = 128 :=
  dist_of_sq' (by norm_num) (by rw [targetTri_sides.2.2]; norm_num)

theorem target44_det_pos : 0 < targetTri.det := by
  unfold Tri.det
  rw [target44_pts0, target44_pts1, target44_pts2]
  simp only [PiLp.sub_apply, mkPt_zero, mkPt_one]
  have h15 : 0 < Real.sqrt 15 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith

/-- The target is ccw, so its left-hand unit on edge `k` is the normalised `pts (k+1) − pts k`. -/
theorem target44_leftUnit_x (k : Fin 3) :
    (targetTri.leftUnit k).1 0
      = (targetTri.pts (k + 1) 0 - targetTri.pts k 0)
          / dist (targetTri.pts k) (targetTri.pts (k + 1)) := by
  have hL : targetTri.leftDir k = targetTri.pts (k + 1) - targetTri.pts k := by
    unfold Tri.leftDir; rw [if_pos target44_det_pos]
  show (‖targetTri.leftDir k‖⁻¹ • targetTri.leftDir k) 0 = _
  rw [hL, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, ← dist_eq_norm,
    dist_comm (targetTri.pts (k + 1)) (targetTri.pts k), div_eq_inv_mul]

/-- **The target side of the identity, evaluated: `C_f(T) = 1485/16`** for `f(d) = d_x³`
(`176·1³ + 128·(−11/16)³ + 128·(−11/16)³`). -/
theorem target44_flux_cubeX : dissection.target.flux cubeX = 1485 / 16 := by
  show targetTri.flux cubeX = 1485 / 16
  have x0 := target44_leftUnit_x 0
  have x1 := target44_leftUnit_x 1
  have x2 := target44_leftUnit_x 2
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl,
    show (2:Fin 3) + 1 = 0 from rfl] at x0 x1 x2
  rw [target44_d01] at x0
  rw [target44_d12] at x1
  rw [target44_d20] at x2
  simp only [target44_pts0, target44_pts1, target44_pts2, mkPt_zero] at x0 x1 x2
  unfold Tri.flux cubeX
  rw [Fin.sum_univ_three]
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl,
    show (2:Fin 3) + 1 = 0 from rfl]
  rw [target44_d01, target44_d12, target44_d20, x0, x1, x2]
  norm_num

/-- **The witness identity: the 44 tiles' fluxes of `d ↦ d_x³` sum to exactly `1485/16`.**
A statement about all 44 pieces, obtained from `lem:cancel` plus the three target edges. -/
theorem tiles44_flux_cubeX : ∑ i, (dissection.tile i).flux cubeX = 1485 / 16 := by
  rw [flux_cancel_44, target44_flux_cubeX]

/-! ## The dissection is not edge-to-edge -/

theorem piece_pts (i : Fin Tiling44.tiles.length) (k : Fin 3) :
    (dissection.tile i).pts k
      = mkPt (toR (zx (toZPt (vertexOf Tiling44.tiles[i.val] k))))
          (toR (zy (toZPt (vertexOf Tiling44.tiles[i.val] k)))) :=
  pieceTri_pts _ (List.getElem_mem i.isLt) k

theorem len44 : 8 < Tiling44.tiles.length := by decide

/-- **A T-junction.**  Vertex 1 of piece 8, `(78, 2√15)`, lies in the OPEN segment of piece 7's
edge 2, from `(85, 3√15)` to `(64, 0)`, at parameter `1/3`: `Tiling44Bridge.dissection` is not
edge-to-edge, so `flux_cancel_44` exercises the non-edge-to-edge case. -/
theorem tiling44_T_junction :
    (dissection.tile ⟨8, len44⟩).pts 1
      ∈ openSegment ℝ ((dissection.tile ⟨7, by decide⟩).pts 2)
          ((dissection.tile ⟨7, by decide⟩).pts 0) := by
  rw [piece_pts, piece_pts, piece_pts]
  have a1 : zx (toZPt (vertexOf Tiling44.tiles[8] 1)) = ((78:ℤ),(0:ℤ)) := by decide
  have a2 : zy (toZPt (vertexOf Tiling44.tiles[8] 1)) = ((0:ℤ),(2:ℤ)) := by decide
  have b1 : zx (toZPt (vertexOf Tiling44.tiles[7] 2)) = ((85:ℤ),(0:ℤ)) := by decide
  have b2 : zy (toZPt (vertexOf Tiling44.tiles[7] 2)) = ((0:ℤ),(3:ℤ)) := by decide
  have c1 : zx (toZPt (vertexOf Tiling44.tiles[7] 0)) = ((64:ℤ),(0:ℤ)) := by decide
  have c2 : zy (toZPt (vertexOf Tiling44.tiles[7] 0)) = ((0:ℤ),(0:ℤ)) := by decide
  simp only [a1, a2, b1, b2, c1, c2]
  refine ⟨2/3, 1/3, by norm_num, by norm_num, by norm_num, ?_⟩
  ext i
  fin_cases i <;> simp [toR] <;> ring

/-! ## Negative control: oddness is not decorative -/

/-- The constant weight `1` is not odd. -/
theorem one_not_odd : ¬ ∀ d : Dir, (fun _ : Dir => (1:ℝ)) (Dir.neg d) = - (fun _ : Dir => (1:ℝ)) d := by
  intro h
  have := h (targetTri.leftUnit 0)
  norm_num at this

/-- Perimeter. -/
noncomputable def perim (T : Tri) : ℝ :=
  dist (T.pts 0) (T.pts 1) + dist (T.pts 1) (T.pts 2) + dist (T.pts 2) (T.pts 0)

theorem flux_one (T : Tri) : T.flux (fun _ : Dir => (1:ℝ)) = perim T := by
  unfold Tri.flux perim
  rw [Fin.sum_univ_three]
  simp only [smul_eq_mul, mul_one]
  rfl

theorem perim_congr {T U : Tri} (h : T.Congruent U) : perim T = perim U := by
  have hm := congrArg Multiset.sum h.sideMultiset_eq
  simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton] at hm
  unfold perim
  linarith

theorem model44_perim : perim dissection.model = 72 := by
  show perim (pieceTri headI_mem_tiles) = 72
  have e01 : Tiling44.dist2 (vertexOf Tiling44.tiles.headI 0) (vertexOf Tiling44.tiles.headI 1)
      = ((256:ℤ),(0:ℤ)) := by decide
  have e12 : Tiling44.dist2 (vertexOf Tiling44.tiles.headI 1) (vertexOf Tiling44.tiles.headI 2)
      = ((576:ℤ),(0:ℤ)) := by decide
  have e20 : Tiling44.dist2 (vertexOf Tiling44.tiles.headI 2) (vertexOf Tiling44.tiles.headI 0)
      = ((1024:ℤ),(0:ℤ)) := by decide
  have d01 : dist ((pieceTri headI_mem_tiles).pts 0) ((pieceTri headI_mem_tiles).pts 1) = 16 :=
    dist_of_sq' (by norm_num) (by rw [pieceTri_dist_sq _ headI_mem_tiles 0 1, e01]; simp [toR]; norm_num)
  have d12 : dist ((pieceTri headI_mem_tiles).pts 1) ((pieceTri headI_mem_tiles).pts 2) = 24 :=
    dist_of_sq' (by norm_num) (by rw [pieceTri_dist_sq _ headI_mem_tiles 1 2, e12]; simp [toR]; norm_num)
  have d20 : dist ((pieceTri headI_mem_tiles).pts 2) ((pieceTri headI_mem_tiles).pts 0) = 32 :=
    dist_of_sq' (by norm_num) (by rw [pieceTri_dist_sq _ headI_mem_tiles 2 0, e20]; simp [toR]; norm_num)
  unfold perim
  rw [d01, d12, d20]
  norm_num

/-- **Without oddness the conclusion is false on the same dissection**: for `f ≡ 1` the tiles'
fluxes (perimeters) sum to `44 · 72 = 3168`, the target's is `176 + 128 + 128 = 432`. -/
theorem flux_cancel_44_needs_odd :
    ∑ i, (dissection.tile i).flux (fun _ : Dir => (1:ℝ))
      ≠ dissection.target.flux (fun _ : Dir => (1:ℝ)) := by
  have hL : ∑ i, (dissection.tile i).flux (fun _ : Dir => (1:ℝ)) = 3168 := by
    have h1 : ∀ i, (dissection.tile i).flux (fun _ : Dir => (1:ℝ)) = 72 := by
      intro i
      rw [flux_one, perim_congr (dissection.tiles_congruent i), model44_perim]
    rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, tiles_length_eq_44]
    norm_num
  have hR : dissection.target.flux (fun _ : Dir => (1:ℝ)) = 432 := by
    show targetTri.flux (fun _ : Dir => (1:ℝ)) = 432
    rw [flux_one]
    unfold perim
    rw [target44_d01, target44_d12, target44_d20]
    norm_num
  rw [hL, hR]
  norm_num

end Erdos634.Draft.FluxWitness

#print axioms Erdos634.Draft.FluxWitness.flux_cancel_44
#print axioms Erdos634.Draft.FluxWitness.tiles44_flux_cubeX
#print axioms Erdos634.Draft.FluxWitness.tiling44_T_junction
#print axioms Erdos634.Draft.FluxWitness.flux_cancel_44_needs_odd
