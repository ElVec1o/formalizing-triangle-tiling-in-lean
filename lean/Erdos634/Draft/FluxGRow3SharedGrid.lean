-- Draft/FluxGRow3SharedGrid.lean — P110/P111's item (2): a shared grid `θ₀` across the four
-- directions P110 named (`tile0'`'s hypotenuse, `tile1'`'s hypotenuse, `target`'s `BC`-direction,
-- and `target`'s other two edges), for the REAL, concrete `dissection'` witness (P106/P107/P108),
-- built via `FluxGRow3DirAngle.dir_angle_of_coords` (P111) applied to each edge's actual coordinate
-- vector. Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- Formalization debt on an already paper-level-PROVED result (row3 PROOF.md, Rule 0, PROVED, two
-- independent hostile reviews HOLD); NOT progress on the three /goal outcomes (this is explicitly a
-- Lean-infrastructure task, not a mathematical one).
--
-- EXISTENCE CHECK (P88 process, run before writing):
--   `ls -la lean/Erdos634/Draft/FluxGRow3SharedGrid.lean` -> "No such file or directory" (confirmed
--   absent; recorded verbatim in the outer report).
--   `grep -n "FluxGRow3SharedGrid" lean/Erdos634/All.lean` -> no output (file not referenced
--   anywhere in the checked module).
--
-- SURVEY (per dispatch instructions, done before writing):
--   - `Draft/FluxGRow3DirAngle.lean` (P111, 179 lines) read in full: supplies `dir_angle_of_coords`
--     (`d : Dir`, `d.1 0 = r cos θ`, `d.1 1 = r sin θ`, `r > 0` ⊢ `d.angle = (θ : Real.Angle)`) and
--     the raw-vector form `arg_toC_of_coords`. Its own §5 sanity check already computes `tile0'`'s
--     `B − A` angle as `-arccos(-3/4)`; this file needs the SAME vector's angle in the different,
--     shift-friendly form `α456 + π` (both are valid `θ`'s for `dir_angle_of_coords`, since the
--     lemma has no principal-branch restriction — it holds for ANY `θ` whose `cos`/`sin` match the
--     coordinates, not just the one in the standard range).
--   - `Draft/FluxGRow3WitnessBridge.lean` (P107, 246 lines) and `FluxGRow3AngleWitnessDissection.lean`
--     (P106, 337 lines) read in full: supply `target`, `tile0'`, `tile1'`, `model'`, `dissection'`
--     and every point/side-length fact used below (`target`'s vertex order `(B, C, A)`, `tile0'`'s
--     `(B, A, M)`, `tile1'`'s `(C, A, M)`, all as concrete `mkTri` coordinate triangles).
--   - `Draft/FluxGRow3TargetDirs.lean` (P100, 209 lines) read in full for the GRID-DEGREE bookkeeping
--     TEMPLATE: `IsGridA α θ₀ θ` (`Draft/FluxGRow3Weight.lean`), `gridK`/`gridJ`, and the pattern
--     "`dir(C→A) = θ₀ + (π−α)`, `dir(A→B) = θ₀ + (π+α)`" via `Tri.leftUnit_turn_of_pos` on the
--     SYMBOLIC `targetIso`. This file follows the SAME target bookkeeping shape (`(p,q) = (-1,2)` and
--     `(1,2)`) but for the CONCRETE numeric `target`/`tile0'`/`tile1'` of P106/P107, via coordinates
--     and `dir_angle_of_coords` rather than the abstract turn lemma `Tri.leftUnit_turn_of_pos` (which
--     only gives RELATIVE steps within one triangle, not the cross-triangle placement P110 needed).
--   - `Draft/FluxGRow3Cancel.lean` read for `isGridA_add_shift`/`gridK_add_shift`/`gridJ_add_shift`
--     (the general `(p,q)`-shift API `IsGridA` membership composes with), confirmed generic and
--     reused unedited.
--   - `Dissection.lean:1359` (`Tri.leftDir`), `:1606` (`Tri.leftUnit`) read for the exact `if 0 < T.det
--     then pts(k+1)-pts k else pts k - pts(k+1)` definition driving every computation below.
--
-- WHAT THIS FILE ESTABLISHES (P110's item (2), precisely):
--   `θ₀ := (target.leftUnit 0).angle` (the `B→C` direction, computed below to be literally `0`).
--   All four of `target.leftUnit 1`, `target.leftUnit 2`, `tile0'.leftUnit 0`, `tile1'.leftUnit 0`
--   are shown to be `IsGridA α456 θ₀`-members, with EXPLICIT `(k, j)` witnesses:
--     `target.leftUnit 1` and `tile1'.leftUnit 0` both sit at `(k,j) = (-1, 2)` (angle `π − α456`);
--     `target.leftUnit 2` and `tile0'.leftUnit 0` both sit at `(k,j) = (1, 2)` (angle `α456 + π`).
--   The file also proves the STRONGER, exact statement that makes this a genuine "shared grid" rather
--   than a coincidence of two separately-computed numbers: `tile0'.leftDir 0 = target.leftDir 2` and
--   `tile1'.leftDir 0 = target.leftDir 1` as RAW `Plane` VECTOR equalities (not just equal angles),
--   because in `dissection'`'s construction the two triangles' shared edge literally IS the target's
--   boundary edge, same points, same order — so `tile0'.leftUnit 0 = target.leftUnit 2` and
--   `tile1'.leftUnit 0 = target.leftUnit 1` as `Dir`s outright, angle equality falling out for free.
--
-- WHAT THIS FILE DOES NOT DO (read before citing this as further progress than it is):
--   - It does NOT build item (3) (the concrete-target flux computation parallel to
--     `targetIso_flux_gauss` for `target`/`dissection'` rather than the symbolic `targetIso`) or
--     item (4) (`gaussWeight_flux_cancel` assembly). Those remain fully open, exactly as P110 scoped
--     them; nothing here shortens them beyond supplying the now-closed grid-placement input they need
--     (`hgridBC`-style hypotheses on `target`/`tile0'`/`tile1'` are no longer axioms of convenience —
--     they are the PROVED facts `target_leftUnit0_isGridA` etc. below, with `θ₀ = 0` concretely).
--   - It does NOT touch `dissection'.toDissection`, `Dissection.flux_cancel`, or any consumer; it is
--     a standalone geometric fact about `target`/`tile0'`/`tile1'`'s directions.
--
-- Rediscovery check (Rule 0.5): grepped `lean/Erdos634` (`lean/Erdos634/*.lean` and
-- `lean/Erdos634/Draft/*.lean`) for `SharedGrid`, `target_leftDir`, `tile0'_leftDir`,
-- `tile1'_leftDir`, `target_leftUnit`, and any existing `IsGridA` instantiation naming `target`,
-- `tile0'`, or `tile1'` — no hits anywhere outside `FluxGRow3TargetDirs.lean`'s SYMBOLIC `targetIso`
-- computation (a different, abstract `Tri`, not this file's concrete numeric one). This file's
-- concrete-coordinate grid placement is new.
--
-- Hazard H59: `(e, f) = (3, 4)` is never evaluated or mentioned as a parameter pair below; every `3`,
-- `4`, `√7` appearing is the `3-√7-4` right-triangle data from row 3's witness (same disclaimer as
-- `FluxGRow3WitnessBridge.lean`/`FluxGRow3AngleWitnessDissection.lean`/`FluxGRow3DirAngle.lean`).
import Erdos634.Draft.FluxGRow3DirAngle
import Erdos634.Draft.FluxGRow3Cancel

namespace Erdos634.Draft.FluxGRow3SharedGrid

open Erdos634.Geometry Erdos634.CertCoord Complex
open Erdos634.Draft.FluxGRow3AngleWitnessDissection Erdos634.Draft.FluxGRow3WitnessBridge
open Erdos634.Draft.FluxGRow3DirAngle
open Erdos634.Geometry.Row3 Erdos634.Draft.FluxRow4Witness

/-! ## §1 `Tri.det` values for `target`, `tile0'`, `tile1'`

Pure algebra (`det3`'s definition matches `Tri.det`'s exactly on `mkTri`-built triangles): the
determinant of a `mkTri x0 y0 x1 y1 x2 y2` triangle is `det3 x0 y0 x1 y1 x2 y2` by direct unfolding,
no sign information needed for this step. -/

theorem det_mkTri (x0 y0 x1 y1 x2 y2 : ℝ) (hdet : det3 x0 y0 x1 y1 x2 y2 ≠ 0) :
    (mkTri x0 y0 x1 y1 x2 y2 hdet).det = det3 x0 y0 x1 y1 x2 y2 := by
  unfold Tri.det det3
  rw [mkTri_pts]
  simp [PiLp.sub_apply, mkPt_zero, mkPt_one]
  ring

theorem target_pts : target.pts = ![mkPt (-3) 0, mkPt 3 0, mkPt 0 sq7] := mkTri_pts _ _ _ _ _ _ _

theorem target_det3_eq : det3 (-3) 0 3 0 0 sq7 = 6 * sq7 := by unfold det3; ring

theorem target_det_eq : target.det = 6 * sq7 := by
  show (mkTri (-3) 0 3 0 0 sq7 hDTpos.ne').det = 6 * sq7
  rw [det_mkTri, target_det3_eq]

theorem target_det_pos : 0 < target.det := by
  rw [target_det_eq]; have := sq7_pos; linarith

theorem tile0'_det_eq : tile0'.det = -3 * sq7 := by
  show (mkTri (-3) 0 0 sq7 0 0 hdet0').det = -3 * sq7
  rw [det_mkTri, hdet0'_eval]

theorem tile0'_det_neg : tile0'.det < 0 := by
  rw [tile0'_det_eq]; have := sq7_pos; linarith

theorem tile1'_det_eq : tile1'.det = 3 * sq7 := by
  show (mkTri 3 0 0 sq7 0 0 hdet1').det = 3 * sq7
  rw [det_mkTri, hdet1'_eval]

theorem tile1'_det_pos : 0 < tile1'.det := by
  rw [tile1'_det_eq]; have := sq7_pos; linarith

/-! ## §2 `leftDir` unfolded at each triangle's actual orientation -/

theorem target_leftDir0 : target.leftDir 0 = target.pts 1 - target.pts 0 := by
  unfold Tri.leftDir; rw [if_pos target_det_pos]; rfl

theorem target_leftDir1 : target.leftDir 1 = target.pts 2 - target.pts 1 := by
  unfold Tri.leftDir; rw [if_pos target_det_pos]; rfl

theorem target_leftDir2 : target.leftDir 2 = target.pts 0 - target.pts 2 := by
  unfold Tri.leftDir; rw [if_pos target_det_pos]; rfl

theorem tile0'_leftDir0 : tile0'.leftDir 0 = tile0'.pts 0 - tile0'.pts 1 := by
  unfold Tri.leftDir; rw [if_neg (not_lt.mpr tile0'_det_neg.le)]; rfl

theorem tile1'_leftDir0 : tile1'.leftDir 0 = tile1'.pts 1 - tile1'.pts 0 := by
  unfold Tri.leftDir; rw [if_pos tile1'_det_pos]; rfl

/-! ## §3 The exact vector equalities: `tile0'`/`tile1'`'s hypotenuse edges ARE `target`'s
`AB`/`CA` edges, same points, same order

This is the sharp form of "shared grid": not merely equal angles computed two different ways, but
literally the same `Plane` vector, since `dissection'`'s tiles were built from the SAME coordinate
points as `target`. -/

theorem tile0'_leftDir0_eq_target_leftDir2 : tile0'.leftDir 0 = target.leftDir 2 := by
  rw [tile0'_leftDir0, target_leftDir2, tile0'_pts, target_pts]
  rfl

theorem tile1'_leftDir0_eq_target_leftDir1 : tile1'.leftDir 0 = target.leftDir 1 := by
  rw [tile1'_leftDir0, target_leftDir1, tile1'_pts, target_pts]
  rfl

theorem tile0'_leftUnit0_eq_target_leftUnit2 : tile0'.leftUnit 0 = target.leftUnit 2 := by
  apply Subtype.ext
  show ‖tile0'.leftDir 0‖⁻¹ • tile0'.leftDir 0 = ‖target.leftDir 2‖⁻¹ • target.leftDir 2
  rw [tile0'_leftDir0_eq_target_leftDir2]

theorem tile1'_leftUnit0_eq_target_leftUnit1 : tile1'.leftUnit 0 = target.leftUnit 1 := by
  apply Subtype.ext
  show ‖tile1'.leftDir 0‖⁻¹ • tile1'.leftDir 0 = ‖target.leftDir 1‖⁻¹ • target.leftDir 1
  rw [tile1'_leftDir0_eq_target_leftDir1]

theorem tile0'_leftUnit0_angle_eq_target_leftUnit2_angle :
    (tile0'.leftUnit 0).angle = (target.leftUnit 2).angle := by
  rw [tile0'_leftUnit0_eq_target_leftUnit2]

theorem tile1'_leftUnit0_angle_eq_target_leftUnit1_angle :
    (tile1'.leftUnit 0).angle = (target.leftUnit 1).angle := by
  rw [tile1'_leftUnit0_eq_target_leftUnit1]

/-! ## §4 `sin α456`, needed below (not previously recorded anywhere in the corpus) -/

theorem sin_α456 : Real.sin α456 = sq7 / 4 := by
  have hc := cos_α456
  have hpos : 0 < Real.sin α456 :=
    Real.sin_pos_of_pos_of_lt_pi α456_pos (by linarith [α456_lt_pi_div_two, Real.pi_pos])
  have hsq : Real.sin α456 ^ 2 = (sq7 / 4) ^ 2 := by
    have h7 := sq7_sq
    have hpyth := Real.sin_sq_add_cos_sq α456
    rw [hc] at hpyth
    have hrhs : (sq7 / 4 : ℝ) ^ 2 = 7 / 16 := by rw [div_pow, h7]; norm_num
    rw [hrhs]; nlinarith [hpyth]
  have hnn : (0:ℝ) ≤ sq7 / 4 := by have := sq7_pos; linarith
  exact (pow_left_inj₀ hpos.le hnn two_ne_zero).mp hsq

/-! ## §5 The four directions' absolute angles, via `dir_angle_of_coords` (P111), each expressed as
`θ₀ + p·α456 + q·(π/2)` with `θ₀ := (target.leftUnit 0).angle`, `q ∈ {0, 2}`

`target.leftDir 0 = (6, 0)` gives `θ₀ = 0` outright. -/

theorem target_leftDir0_coords : target.leftDir 0 0 = 6 ∧ target.leftDir 0 1 = 0 := by
  rw [target_leftDir0, target_pts]
  refine ⟨?_, ?_⟩ <;> simp [PiLp.sub_apply, mkPt_zero, mkPt_one] <;> norm_num

theorem target_leftUnit0_angle : (target.leftUnit 0).angle = ((0 : ℝ) : Real.Angle) := by
  obtain ⟨hx, hy⟩ := target_leftDir0_coords
  rw [Tri.leftUnit_angle]
  refine arg_toC_of_coords _ 6 0 (by norm_num) ?_ ?_
  · rw [hx]; norm_num
  · rw [hy]; norm_num

theorem target_leftDir1_coords :
    target.leftDir 1 0 = -3 ∧ target.leftDir 1 1 = sq7 := by
  rw [target_leftDir1, target_pts]
  refine ⟨?_, ?_⟩ <;> simp [PiLp.sub_apply, mkPt_zero, mkPt_one] <;> norm_num

theorem target_leftUnit1_angle :
    (target.leftUnit 1).angle = ((Real.pi - α456 : ℝ) : Real.Angle) := by
  obtain ⟨hx, hy⟩ := target_leftDir1_coords
  have hc : Real.cos (Real.pi - α456) = -3 / 4 := by
    rw [Real.cos_pi_sub, cos_α456]; norm_num
  have hs : Real.sin (Real.pi - α456) = sq7 / 4 := by
    rw [Real.sin_pi_sub, sin_α456]
  rw [Tri.leftUnit_angle]
  refine arg_toC_of_coords _ 4 _ (by norm_num) ?_ ?_
  · rw [hx, hc]; ring
  · rw [hy, hs]; ring

theorem target_leftDir2_coords :
    target.leftDir 2 0 = -3 ∧ target.leftDir 2 1 = -sq7 := by
  rw [target_leftDir2, target_pts]
  refine ⟨?_, ?_⟩ <;> simp [PiLp.sub_apply, mkPt_zero, mkPt_one] <;> norm_num

theorem target_leftUnit2_angle :
    (target.leftUnit 2).angle = ((α456 + Real.pi : ℝ) : Real.Angle) := by
  obtain ⟨hx, hy⟩ := target_leftDir2_coords
  have hc : Real.cos (α456 + Real.pi) = -3 / 4 := by
    rw [Real.cos_add_pi, cos_α456]; norm_num
  have hs : Real.sin (α456 + Real.pi) = -(sq7 / 4) := by
    rw [Real.sin_add_pi, sin_α456]
  rw [Tri.leftUnit_angle]
  refine arg_toC_of_coords _ 4 _ (by norm_num) ?_ ?_
  · rw [hx, hc]; ring
  · rw [hy, hs]; ring

theorem tile0'_leftUnit0_angle :
    (tile0'.leftUnit 0).angle = ((α456 + Real.pi : ℝ) : Real.Angle) := by
  rw [tile0'_leftUnit0_angle_eq_target_leftUnit2_angle, target_leftUnit2_angle]

theorem tile1'_leftUnit0_angle :
    (tile1'.leftUnit 0).angle = ((Real.pi - α456 : ℝ) : Real.Angle) := by
  rw [tile1'_leftUnit0_angle_eq_target_leftUnit1_angle, target_leftUnit1_angle]

/-! ## §6 The shared grid: `IsGridA α456 θ₀` membership for all four directions, with explicit
`(k, j)` witnesses, `θ₀ := (target.leftUnit 0).angle`

This is the precise deliverable P110 named as item (2): a SHARED reference direction `θ₀` (here
concretely `0`, `target`'s own `BC`-direction) such that every one of the four directions P110 listed
lies on the grid `θ₀ + ℤ·α456 + ℤ·(π/2)`. -/

/-- `θ₀ : ℝ`, the real-valued base reference `IsGridA` is parametrized by (matching
`FluxGRow3Weight.IsGridA (α θ₀ : ℝ) (θ : Real.Angle)`'s signature exactly — `θ₀` here is
`0`, and `target_leftUnit0_angle` records that this is literally `target`'s own `BC`-direction
(`(target.leftUnit 0).angle = ((0:ℝ) : Real.Angle)`), so `θ₀`'s coercion is not an arbitrary base
point but the concrete `BC` direction itself. -/
noncomputable def θ₀ : ℝ := 0

theorem θ₀_coe_eq_target_leftUnit0_angle : ((θ₀ : ℝ) : Real.Angle) = (target.leftUnit 0).angle := by
  rw [target_leftUnit0_angle]; unfold θ₀; norm_num

theorem θ₀_isGridA : IsGridA α456 θ₀ ((θ₀ : ℝ) : Real.Angle) := ⟨0, 0, by unfold θ₀; push_cast; ring⟩

/-- `target.leftUnit 1` (`CA`) sits at grid coordinates `(k, j) = (-1, 2)`: angle `θ₀ − α456 + π`. -/
theorem target_leftUnit1_isGridA :
    IsGridA α456 θ₀ (target.leftUnit 1).angle ∧
      (target.leftUnit 1).angle
        = (((θ₀ : ℝ) + ((-1 : ℤ) : ℝ) * α456 + ((2 : ℤ) : ℝ) * (Real.pi / 2) : ℝ) : Real.Angle) := by
  have hshift : (Real.pi - α456 : ℝ)
      = ((θ₀ : ℝ) + ((-1 : ℤ) : ℝ) * α456 + ((2 : ℤ) : ℝ) * (Real.pi / 2) : ℝ) := by
    unfold θ₀; push_cast; ring
  refine ⟨⟨-1, 2, by rw [target_leftUnit1_angle, hshift]⟩, ?_⟩
  rw [target_leftUnit1_angle, hshift]

/-- `target.leftUnit 2` (`AB`) sits at grid coordinates `(k, j) = (1, 2)`: angle `θ₀ + α456 + π`. -/
theorem target_leftUnit2_isGridA :
    IsGridA α456 θ₀ (target.leftUnit 2).angle ∧
      (target.leftUnit 2).angle
        = (((θ₀ : ℝ) + ((1 : ℤ) : ℝ) * α456 + ((2 : ℤ) : ℝ) * (Real.pi / 2) : ℝ) : Real.Angle) := by
  have hshift : (α456 + Real.pi : ℝ)
      = ((θ₀ : ℝ) + ((1 : ℤ) : ℝ) * α456 + ((2 : ℤ) : ℝ) * (Real.pi / 2) : ℝ) := by
    unfold θ₀; push_cast; ring
  refine ⟨⟨1, 2, by rw [target_leftUnit2_angle, hshift]⟩, ?_⟩
  rw [target_leftUnit2_angle, hshift]

/-- `tile1'`'s hypotenuse (`tile1'.leftUnit 0`) sits at the SAME grid coordinates as `target`'s `CA`
edge, `(k, j) = (-1, 2)` — not a coincidence: §3 already showed the two `Dir`s are literally equal. -/
theorem tile1'_leftUnit0_isGridA : IsGridA α456 θ₀ (tile1'.leftUnit 0).angle := by
  rw [tile1'_leftUnit0_angle_eq_target_leftUnit1_angle]
  exact target_leftUnit1_isGridA.1

/-- `tile0'`'s hypotenuse (`tile0'.leftUnit 0`) sits at the SAME grid coordinates as `target`'s `AB`
edge, `(k, j) = (1, 2)` — again from the exact `Dir` equality of §3, not a separate computation. -/
theorem tile0'_leftUnit0_isGridA : IsGridA α456 θ₀ (tile0'.leftUnit 0).angle := by
  rw [tile0'_leftUnit0_angle_eq_target_leftUnit2_angle]
  exact target_leftUnit2_isGridA.1

end Erdos634.Draft.FluxGRow3SharedGrid

#print axioms Erdos634.Draft.FluxGRow3SharedGrid.det_mkTri
#print axioms Erdos634.Draft.FluxGRow3SharedGrid.target_det_pos
#print axioms Erdos634.Draft.FluxGRow3SharedGrid.tile0'_det_neg
#print axioms Erdos634.Draft.FluxGRow3SharedGrid.tile1'_det_pos
#print axioms Erdos634.Draft.FluxGRow3SharedGrid.tile0'_leftDir0_eq_target_leftDir2
#print axioms Erdos634.Draft.FluxGRow3SharedGrid.tile1'_leftDir0_eq_target_leftDir1
#print axioms Erdos634.Draft.FluxGRow3SharedGrid.tile0'_leftUnit0_eq_target_leftUnit2
#print axioms Erdos634.Draft.FluxGRow3SharedGrid.tile1'_leftUnit0_eq_target_leftUnit1
#print axioms Erdos634.Draft.FluxGRow3SharedGrid.sin_α456
#print axioms Erdos634.Draft.FluxGRow3SharedGrid.target_leftUnit0_angle
#print axioms Erdos634.Draft.FluxGRow3SharedGrid.target_leftUnit1_angle
#print axioms Erdos634.Draft.FluxGRow3SharedGrid.target_leftUnit2_angle
#print axioms Erdos634.Draft.FluxGRow3SharedGrid.tile0'_leftUnit0_angle
#print axioms Erdos634.Draft.FluxGRow3SharedGrid.tile1'_leftUnit0_angle
#print axioms Erdos634.Draft.FluxGRow3SharedGrid.θ₀_isGridA
#print axioms Erdos634.Draft.FluxGRow3SharedGrid.target_leftUnit1_isGridA
#print axioms Erdos634.Draft.FluxGRow3SharedGrid.target_leftUnit2_isGridA
#print axioms Erdos634.Draft.FluxGRow3SharedGrid.tile1'_leftUnit0_isGridA
#print axioms Erdos634.Draft.FluxGRow3SharedGrid.tile0'_leftUnit0_isGridA
