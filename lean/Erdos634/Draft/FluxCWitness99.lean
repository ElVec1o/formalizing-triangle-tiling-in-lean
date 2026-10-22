-- Draft/FluxCWitness99.lean — the REAL 99-tiling (`Tiling99Bridge.dissection`: 99 copies of the
-- `(2,3,4)·16` tile in the isosceles target `(24,24,33)·16`) as a second certified witness for the
-- triangle-target boundary lemma (Draft/FluxCBoundary.lean).  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- Data proved here (all from the kernel-checked certificate): the model `(32,48,64)` has angles
-- `(β, γ, α)` at vertices `(0,1,2)` — the SAME `α44`, `β44` as the 44-tiling's model (equal cosines
-- `7/8`, `11/16`) — and is a `3α + 2β = π` tile (`data99`); the target `(528,384,384)` has angles
-- `(β, β, 3α)` (cosines `11/16, 11/16, 7/128`), is ccw, and its base has direction `0`.
-- Evaluated through the boundary lemma: `K_{χ₊}(model) = −80`, `K_{χ₋}(model) = 144`,
-- `K_{χ₊}(P) = −240`, `K_{χ₋}(P) = 1296`, base sign `+1`, hence `S₊ = 3`, `S₋ = 9` (both odd, as
-- `N = 99` is): R12's `(M, K) = (9, −3)`, the values ROW11_RATIONALITY.md §3.6 step 5 records from
-- the review controls (a reproduction of those float/symbolic controls, now kernel-checked).
--
-- Formalization debt; not progress on the three /goal outcomes.
-- Local re-derivations (named plainly): `m99_*`, `t99_*` follow `FluxGridWitness.m_*`/`t_*` and
-- `FluxWitness.target44_*` line for line on the other certificate.
import Erdos634.Draft.FluxCBoundary
import Erdos634.Draft.FluxRow11
import Erdos634.Draft.FluxGridWitness
import Erdos634.Tiling99Bridge

open scoped Classical

namespace Erdos634.Draft.FluxCWitness99

open Erdos634.Geometry Erdos634.Z15Real Erdos634.CertCoord Erdos634.Tiling99Bridge
open Erdos634.Draft.FluxGridWitness

/-! ## The model -/

/-- The model tile of the 99-tiling, `(32, 48, 64)`. -/
noncomputable abbrev M99 : Tri := pieceTri headI_mem_tiles

theorem m99_d01 : dist (M99.pts 0) (M99.pts 1) = 32 := by
  have e : Tiling99.dist2 (vertexOf Tiling99.tiles.headI 0) (vertexOf Tiling99.tiles.headI 1)
      = ((1024:ℤ),(0:ℤ)) := by decide
  exact Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num)
    (by rw [pieceTri_dist_sq _ headI_mem_tiles 0 1, e]; simp [toR]; norm_num)

theorem m99_d12 : dist (M99.pts 1) (M99.pts 2) = 48 := by
  have e : Tiling99.dist2 (vertexOf Tiling99.tiles.headI 1) (vertexOf Tiling99.tiles.headI 2)
      = ((2304:ℤ),(0:ℤ)) := by decide
  exact Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num)
    (by rw [pieceTri_dist_sq _ headI_mem_tiles 1 2, e]; simp [toR]; norm_num)

theorem m99_d20 : dist (M99.pts 2) (M99.pts 0) = 64 := by
  have e : Tiling99.dist2 (vertexOf Tiling99.tiles.headI 2) (vertexOf Tiling99.tiles.headI 0)
      = ((4096:ℤ),(0:ℤ)) := by decide
  exact Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num)
    (by rw [pieceTri_dist_sq _ headI_mem_tiles 2 0, e]; simp [toR]; norm_num)

theorem m99_opp : M99.oppLen 0 = 48 ∧ M99.oppLen 1 = 64 ∧ M99.oppLen 2 = 32 := by
  unfold Tri.oppLen
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl,
    show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl,
    show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
  exact ⟨m99_d12, m99_d20, m99_d01⟩

theorem m99_angle2 : M99.angleAt 2 = α44 := by
  have hcos : Real.cos (M99.angleAt 2) = 7 / 8 := by
    unfold Tri.angleAt
    simp only [show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
    rw [cos_cornerAngle (ne_of_dist m99_d20 (by norm_num)).symm (ne_of_dist m99_d12 (by norm_num)),
      dist_comm (M99.pts 0) (M99.pts 2), m99_d20, m99_d12, m99_d01]
    norm_num
  exact Real.injOn_cos (cornerAngle_mem _ _ _) (cornerAngle_mem _ _ _) (hcos.trans cos_α44.symm)

theorem m99_angle0 : M99.angleAt 0 = β44 := by
  have hcos : Real.cos (M99.angleAt 0) = 11 / 16 := by
    unfold Tri.angleAt
    simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl]
    rw [cos_cornerAngle (ne_of_dist m99_d01 (by norm_num)).symm (ne_of_dist m99_d20 (by norm_num)),
      dist_comm (M99.pts 1) (M99.pts 0), m99_d01, m99_d20, m99_d12]
    norm_num
  exact Real.injOn_cos (cornerAngle_mem _ _ _) (cornerAngle_mem _ _ _) (hcos.trans cos_β44.symm)

theorem m99_angle1 : M99.angleAt 1 = 2 * α44 + β44 := by
  have hs := M99.angleAt_sum
  rw [m99_angle0, m99_angle2] at hs
  have h := three_α_two_β
  linarith

/-- The relabelling `0 ↦ 2, 1 ↦ 0, 2 ↦ 1` (`FluxRow11Witness.τ`). -/
def τ : Equiv.Perm (Fin 3) := (finRotate 3).symm

theorem τ0 : τ 0 = 2 := by decide
theorem τ1 : τ 1 = 0 := by decide
theorem τ2 : τ 2 = 1 := by decide

/-- **The 99-model is a `3α + 2β = π` tile with `(a, b, c) = (32, 48, 64)`.** -/
theorem data99 : M99.ThreeAlphaData α44 β44 32 48 64 := by
  refine ⟨τ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [τ0]; exact m99_angle2
  · rw [τ0]; exact m99_opp.2.2
  · rw [τ1]; exact m99_angle0
  · rw [τ1]; exact m99_opp.1
  · rw [τ2]; exact m99_angle1
  · rw [τ2]; exact m99_opp.2.1

theorem m99_angles_mem (b : ZMod 2) :
    ∀ k, ((M99.angleAt k : ℝ) : Real.Angle) ∈ (GridChar.rank2 θ44 θ44_irr b 0).L := by
  have hγ : 2 * α44 + β44 = ((0 : ℤ) : ℝ) * Real.pi + ((1 : ℤ) : ℝ) * θ44 := by
    have h := three_α_two_β
    unfold θ44; push_cast; linarith
  have hβ : β44 = ((2 : ℤ) : ℝ) * Real.pi + ((-3 : ℤ) : ℝ) * θ44 := β44_eq
  have hα : α44 = ((-1 : ℤ) : ℝ) * Real.pi + ((2 : ℤ) : ℝ) * θ44 := α44_eq
  intro k
  fin_cases k
  · show ((M99.angleAt 0 : ℝ) : Real.Angle) ∈ _
    rw [m99_angle0, hβ]; exact GridChar.rank2_mem _ _ _ _ _ _
  · show ((M99.angleAt 1 : ℝ) : Real.Angle) ∈ _
    rw [m99_angle1, hγ]; exact GridChar.rank2_mem _ _ _ _ _ _
  · show ((M99.angleAt 2 : ℝ) : Real.Angle) ∈ _
    rw [m99_angle2, hα]; exact GridChar.rank2_mem _ _ _ _ _ _

/-! ## The target -/

theorem t99_pts0 : targetTri.pts 0 = mkPt 0 0 := by
  rw [targetTri_pts_eq]
  show mkPt (toR (zx (toZPt (Tiling99.t1 Tiling99.target))))
    (toR (zy (toZPt (Tiling99.t1 Tiling99.target)))) = mkPt 0 0
  have hx : zx (toZPt (Tiling99.t1 Tiling99.target)) = ((0:ℤ),(0:ℤ)) := by decide
  have hy : zy (toZPt (Tiling99.t1 Tiling99.target)) = ((0:ℤ),(0:ℤ)) := by decide
  rw [hx, hy]; simp [toR]

theorem t99_pts1 : targetTri.pts 1 = mkPt 528 0 := by
  rw [targetTri_pts_eq]
  show mkPt (toR (zx (toZPt (Tiling99.t2 Tiling99.target))))
    (toR (zy (toZPt (Tiling99.t2 Tiling99.target)))) = mkPt 528 0
  have hx : zx (toZPt (Tiling99.t2 Tiling99.target)) = ((528:ℤ),(0:ℤ)) := by decide
  have hy : zy (toZPt (Tiling99.t2 Tiling99.target)) = ((0:ℤ),(0:ℤ)) := by decide
  rw [hx, hy]; simp [toR]

theorem t99_pts2 : targetTri.pts 2 = mkPt 264 (72 * Real.sqrt 15) := by
  rw [targetTri_pts_eq]
  show mkPt (toR (zx (toZPt (Tiling99.t3 Tiling99.target))))
    (toR (zy (toZPt (Tiling99.t3 Tiling99.target)))) = mkPt 264 (72 * Real.sqrt 15)
  have hx : zx (toZPt (Tiling99.t3 Tiling99.target)) = ((264:ℤ),(0:ℤ)) := by decide
  have hy : zy (toZPt (Tiling99.t3 Tiling99.target)) = ((0:ℤ),(72:ℤ)) := by decide
  rw [hx, hy]; simp [toR]

theorem t99_d01 : dist (targetTri.pts 0) (targetTri.pts 1) = 528 :=
  Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num) (by rw [targetTri_sides.1]; norm_num)
theorem t99_d12 : dist (targetTri.pts 1) (targetTri.pts 2) = 384 :=
  Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num) (by rw [targetTri_sides.2.1]; norm_num)
theorem t99_d20 : dist (targetTri.pts 2) (targetTri.pts 0) = 384 :=
  Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num) (by rw [targetTri_sides.2.2]; norm_num)

theorem t99_opp : targetTri.oppLen 0 = 384 ∧ targetTri.oppLen 1 = 384 ∧ targetTri.oppLen 2 = 528 := by
  unfold Tri.oppLen
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl,
    show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl,
    show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
  exact ⟨t99_d12, t99_d20, t99_d01⟩

theorem t99_det_pos : 0 < targetTri.det := by
  unfold Tri.det
  rw [t99_pts0, t99_pts1, t99_pts2]
  simp only [PiLp.sub_apply, mkPt_zero, mkPt_one]
  have h15 : 0 < Real.sqrt 15 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith

theorem t99_angle0 : targetTri.angleAt 0 = β44 := by
  have hcos : Real.cos (targetTri.angleAt 0) = 11 / 16 := by
    unfold Tri.angleAt
    simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl]
    rw [cos_cornerAngle (ne_of_dist t99_d01 (by norm_num)).symm
      (ne_of_dist t99_d20 (by norm_num)), dist_comm (targetTri.pts 1) (targetTri.pts 0),
      t99_d01, t99_d20, t99_d12]
    norm_num
  exact Real.injOn_cos (cornerAngle_mem _ _ _) (cornerAngle_mem _ _ _) (hcos.trans cos_β44.symm)

theorem t99_angle1 : targetTri.angleAt 1 = β44 := by
  have hcos : Real.cos (targetTri.angleAt 1) = 11 / 16 := by
    unfold Tri.angleAt
    simp only [show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl]
    rw [cos_cornerAngle (ne_of_dist t99_d12 (by norm_num)).symm
      (ne_of_dist t99_d01 (by norm_num)), dist_comm (targetTri.pts 2) (targetTri.pts 1),
      t99_d12, t99_d01, t99_d20]
    norm_num
  exact Real.injOn_cos (cornerAngle_mem _ _ _) (cornerAngle_mem _ _ _) (hcos.trans cos_β44.symm)

theorem t99_angle2 : targetTri.angleAt 2 = 3 * α44 := by
  have hcos : Real.cos (targetTri.angleAt 2) = 7 / 128 := by
    unfold Tri.angleAt
    simp only [show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
    rw [cos_cornerAngle (ne_of_dist t99_d20 (by norm_num)).symm
      (ne_of_dist t99_d12 (by norm_num)), dist_comm (targetTri.pts 0) (targetTri.pts 2),
      t99_d20, t99_d12, t99_d01]
    norm_num
  have hc3 : Real.cos (3 * α44) = 7 / 128 := by rw [Real.cos_three_mul, cos_α44]; norm_num
  have hα0 : 0 ≤ α44 := (cornerAngle_mem _ _ _).1
  have hαle := α44_le
  exact Real.injOn_cos (cornerAngle_mem _ _ _) ⟨by linarith, by linarith⟩ (hcos.trans hc3.symm)

theorem hβ : β44 = ((2 : ℤ) : ℝ) * Real.pi + ((-3 : ℤ) : ℝ) * θ44 := β44_eq

theorem h3α : 3 * α44 = ((-3 : ℤ) : ℝ) * Real.pi + ((6 : ℤ) : ℝ) * θ44 := by
  unfold θ44; push_cast; ring

theorem t99_angles_mem (b : ZMod 2) :
    ∀ k, ((targetTri.angleAt k : ℝ) : Real.Angle) ∈ (GridChar.rank2 θ44 θ44_irr b 0).L := by
  intro k
  fin_cases k
  · show ((targetTri.angleAt 0 : ℝ) : Real.Angle) ∈ _
    rw [t99_angle0, hβ]; exact GridChar.rank2_mem _ _ _ _ _ _
  · show ((targetTri.angleAt 1 : ℝ) : Real.Angle) ∈ _
    rw [t99_angle1, hβ]; exact GridChar.rank2_mem _ _ _ _ _ _
  · show ((targetTri.angleAt 2 : ℝ) : Real.Angle) ∈ _
    rw [t99_angle2, h3α]; exact GridChar.rank2_mem _ _ _ _ _ _

/-- The target's base direction has angle `0` (the anchor). -/
theorem t99_leftUnit0_angle : (targetTri.leftUnit 0).angle = 0 := by
  have hL0 : targetTri.leftDir 0 = targetTri.pts 1 - targetTri.pts 0 := by
    unfold Tri.leftDir; rw [if_pos t99_det_pos]; rfl
  have hC : toC (targetTri.leftDir 0) = ((528 : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [toC_re, hL0, t99_pts1, t99_pts0]; simp
    · rw [toC_im, hL0, t99_pts1, t99_pts0]; simp
  rw [Tri.leftUnit_angle, hC, Complex.arg_ofReal_of_nonneg (by norm_num), Real.Angle.coe_zero]

/-! ## The boundary lemma on the 99-tiling -/

theorem paperK_m99 (b : ZMod 2) :
    (GridChar.rank2 θ44 θ44_irr b 0).paperK M99
      = -((if ((2 : ℤ) : ZMod 2) + b * ((-3 : ℤ) : ZMod 2) = 0 then 1 else -1) * 48
          + (if ((0 : ℤ) : ZMod 2) + b * ((1 : ℤ) : ZMod 2) = 0 then 1 else -1) * 64
          + (if ((-1 : ℤ) : ZMod 2) + b * ((2 : ℤ) : ZMod 2) = 0 then 1 else -1) * 32) := by
  have hγ : 2 * α44 + β44 = ((0 : ℤ) : ℝ) * Real.pi + ((1 : ℤ) : ℝ) * θ44 := by
    have h := three_α_two_β
    unfold θ44; push_cast; linarith
  have hα : α44 = ((-1 : ℤ) : ℝ) * Real.pi + ((2 : ℤ) : ℝ) * θ44 := α44_eq
  unfold GridChar.paperK
  rw [Fin.sum_univ_three, m99_angle0, m99_angle1, m99_angle2, hγ, hβ, hα, GridChar.rank2_chi,
    GridChar.rank2_chi, GridChar.rank2_chi, m99_opp.1, m99_opp.2.1, m99_opp.2.2]

theorem paperK_t99 (b : ZMod 2) :
    (GridChar.rank2 θ44 θ44_irr b 0).paperK targetTri
      = -((if ((2 : ℤ) : ZMod 2) + b * ((-3 : ℤ) : ZMod 2) = 0 then 1 else -1) * 768
          + (if ((-3 : ℤ) : ZMod 2) + b * ((6 : ℤ) : ZMod 2) = 0 then 1 else -1) * 528) := by
  unfold GridChar.paperK
  rw [Fin.sum_univ_three, t99_angle0, t99_angle1, t99_angle2, hβ, h3α, GridChar.rank2_chi,
    GridChar.rank2_chi, t99_opp.1, t99_opp.2.1, t99_opp.2.2]
  ring

theorem edgeSign_t99 (b : ZMod 2) :
    (GridChar.rank2 θ44 θ44_irr b 0).edgeSign targetTri 0 = 1 := by
  have hw : (GridChar.rank2 θ44 θ44_irr b 0).weight (targetTri.leftUnit 0) = 1 := by
    unfold GridChar.weight
    rw [t99_leftUnit0_angle]
    exact GridChar.val_anchor _
  have e2 : Real.pi - targetTri.angleAt (0 + 2)
      = ((4 : ℤ) : ℝ) * Real.pi + ((-6 : ℤ) : ℝ) * θ44 := by
    show Real.pi - targetTri.angleAt 2 = _
    rw [t99_angle2]; unfold θ44; push_cast; ring
  unfold GridChar.edgeSign
  rw [e2, GridChar.rank2_chi, hw, if_pos]
  · norm_num
  · have h4 : ((4 : ℤ) : ZMod 2) = 0 := by decide
    have h6 : ((-6 : ℤ) : ZMod 2) = 0 := by decide
    rw [h4, h6]; ring

/-- **The boundary lemma on the real 99-tiling, `χ₊`: `S₊ = 3`** (R12's `K = −3`). -/
theorem boundary_99_plus : ∃ S : ℤ, S = 3 ∧ (2 : ℤ) ∣ S - Tiling99.tiles.length
    ∧ |S| ≤ Tiling99.tiles.length := by
  obtain ⟨S, h2, hN, hk⟩ := dissection.triangle_boundary Gplus (GridChar.rank2_sq _ _ _ _)
    (m99_angles_mem 0) (t99_angles_mem 0)
  refine ⟨S, ?_, h2, hN⟩
  have e := hk 0
  change (S : ℝ) * Gplus.paperK M99 = Gplus.edgeSign targetTri 0 * Gplus.paperK targetTri at e
  unfold Gplus at e
  rw [paperK_m99, paperK_t99, edgeSign_t99, if_pos (by decide), if_pos (by decide),
    if_neg (by decide), if_neg (by decide)] at e
  have : (S : ℝ) = 3 := by linarith
  exact_mod_cast this

/-- **The boundary lemma on the real 99-tiling, `χ₋`: `S₋ = 9`** (R12's `M = 9`). -/
theorem boundary_99_minus : ∃ S : ℤ, S = 9 ∧ (2 : ℤ) ∣ S - Tiling99.tiles.length
    ∧ |S| ≤ Tiling99.tiles.length := by
  obtain ⟨S, h2, hN, hk⟩ := dissection.triangle_boundary Gminus (GridChar.rank2_sq _ _ _ _)
    (m99_angles_mem 1) (t99_angles_mem 1)
  refine ⟨S, ?_, h2, hN⟩
  have e := hk 0
  change (S : ℝ) * Gminus.paperK M99 = Gminus.edgeSign targetTri 0 * Gminus.paperK targetTri at e
  unfold Gminus at e
  rw [paperK_m99, paperK_t99, edgeSign_t99, if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide)] at e
  have : (S : ℝ) = 9 := by linarith
  exact_mod_cast this

end Erdos634.Draft.FluxCWitness99

#print axioms Erdos634.Draft.FluxCWitness99.data99
#print axioms Erdos634.Draft.FluxCWitness99.t99_angle2
#print axioms Erdos634.Draft.FluxCWitness99.boundary_99_plus
#print axioms Erdos634.Draft.FluxCWitness99.boundary_99_minus
