-- Draft/FluxGRow3WitnessBridge.lean — attempted isometry bridge for row 3's angle witness (P106),
-- discharging `FluxGRow3Step1.congruentDissection_row3_lemmaA`'s geometric hypotheses at a REAL,
-- concrete `CongruentDissection 2`.
-- Formalization debt on an already paper-level-PROVED result; NOT progress on the three /goal
-- outcomes.
--
-- EXISTENCE CHECK (P88 process, run before writing):
--   `ls -la lean/Erdos634/Draft/FluxGRow3WitnessBridge.lean` → "No such file or directory".
--   `grep -n "WitnessBridge" lean/Erdos634/All.lean` → no output (file not imported anywhere).
--
-- WHAT THE DISPATCH ASKED FOR vs WHAT WAS ACTUALLY NEEDED (stated plainly, this changes the task):
-- the dispatch's framing was "prove `tile0` (P106's coordinate `Tri`) is isometric, as a `Tri` term,
-- to `rightTilePlacement α456` (P73)". Reading `FluxGRow3Step1.congruentDissection_row3_lemmaA`'s
-- actual signature shows this framing is not what the consumer needs: its hypotheses `hα'`/`hβ'`/
-- `hγ'` are stated directly on `D.model.pts` via `cornerAngle`, with NO reference anywhere to
-- `rightTilePlacement` or `targetIso` — those two P73/P98 constructions are never inputs to Step1's
-- theorem. So a bridge FROM P106's `tile0` TO `rightTilePlacement α456` is not on the path to
-- discharging Step1's hypotheses at all; it would be motion, not progress toward the named
-- consumer. What Step1 actually needs is: `cornerAngle` computed directly on P106's `dissection`'s
-- OWN `model`, matched against Step1's exact vertex-index convention.
--
-- THE REAL OBSTRUCTION FOUND (checked by hand from `cornerAngle`'s definition, middle argument =
-- vertex, matching every existing use in `FluxGRow3Placement.lean`/`FluxGRow3TargetCoords.lean`):
-- `congruentDissection_row3_lemmaA` requires, of `D.model` with vertices `(pts0,pts1,pts2)`:
--   hα' : angle AT pts0 = α           hβ' : angle AT pts1 = β = π/2 − α       hγ' : angle AT pts2 = γ = π/2
-- i.e. the RIGHT angle (γ) must sit at index 2. P106's `model = tile0 = (B, M, A)` puts the right
-- angle at index 1 (`M`, the shared right-angle vertex), and its `π/2 − α` angle at index 2 (`A`).
-- So `hβ'`/`hγ'` are exactly SWAPPED relative to what `tile0`'s own vertex order gives — `tile0`
-- as ordered does NOT satisfy Step1's hypotheses. This is a real, checkable index mismatch, not a
-- vacuous or hand-waved one: computed below from the side lengths already on record
-- (`tile0_dist_BM = 3`, `tile0_dist_MA = sq7`, `tile0_dist_AB = 4`, `FluxGRow3AngleWitnessDissection.lean`).
--
-- THE FIX: reorder the model's vertices to `(B, A, M)` (swap indices 1, 2). Since
-- `Tri.carrier = convexHull ℝ (Set.range pts)` depends only on the SET of the three points, not
-- their order (`Dissection.lean:135`), every containment/disjointness fact already proved for
-- `tile0`/`tile1` in `FluxGRow3AngleWitnessDissection.lean` (§3, §4: `tile0_sub`, `tile1_sub`,
-- `tiles01_disjoint`) transfers to the reordered tiles `tile0'`, `tile1'` for free, via a carrier-set
-- equality lemma proved once below (`tile0'_carrier_eq`, `tile1'_carrier_eq`) rather than reproved.
-- The only NEW work is: (a) build `tile0'`, `tile1'` via `mkTri` with permuted coordinate slots,
-- (b) redo the three side-length correspondences `hd01'/hd12'/hd20'` for the new index convention
-- (two of the three pairs are literally unchanged since `tile0'`/`tile1'` share indices 1, 2 = `A`,
-- `M` verbatim), (c) compute the three `cornerAngle` values at the new indices via
-- `AngleThreshold.cos_of_sides` (the same technique `FluxGRow3Placement.lean`/
-- `FluxGRow3TargetCoords.lean` already use), (d) rebuild the `CongruentDissection` via
-- `CertBridge.ofCert` with the reordered `model'`/`tileF'`, (e) feed the result into
-- `congruentDissection_row3_lemmaA`.
--
-- Rediscovery check (Rule 0.5): grepped `lean/Erdos634` for `FluxGRow3WitnessBridge`, `tile0'`,
-- `model'`, `congruentDissection_row3_lemmaA` applied to a concrete witness — no hits outside this
-- file and `FluxGRow3Step1.lean` (the consumer, unedited).
--
-- Hazard H59: `(e, f) = (3, 4)` is never evaluated. The `4` below is the `3-√7-4` hypotenuse length,
-- unrelated to any `(e, f)` tile-parameter pair (same note as `FluxGRow3AngleWitnessDissection.lean`).
import Erdos634.Draft.FluxGRow3AngleWitnessDissection
import Erdos634.Draft.FluxGRow3AngleWitness
import Erdos634.Draft.FluxGRow3Step1
import Erdos634.AngleThreshold

namespace Erdos634.Draft.FluxGRow3WitnessBridge

open Erdos634.Geometry Erdos634.CertCoord Erdos634.AreaDet Erdos634.AngleThreshold
open Erdos634.Draft.FluxGRow3AngleWitnessDissection

/-! ## §1 The reordered tiles: `(B, A, M)` and `(C, A, M)` -/

theorem hdet0' : det3 (-3) 0 0 sq7 0 0 ≠ 0 := by
  have := sq7_pos; unfold det3; nlinarith

theorem hdet1' : det3 3 0 0 sq7 0 0 ≠ 0 := by
  have := sq7_pos; unfold det3; nlinarith

/-- `tile0' = (B, A, M)`, the reordering of `tile0 = (B, M, A)` swapping indices 1, 2. -/
noncomputable def tile0' : Tri := mkTri (-3) 0 0 sq7 0 0 hdet0'

/-- `tile1' = (C, A, M)`, the corresponding reordering of `tile1 = (C, M, A)`. -/
noncomputable def tile1' : Tri := mkTri 3 0 0 sq7 0 0 hdet1'

noncomputable def model' : Tri := tile0'

noncomputable def tileF' : Fin 2 → Tri := ![tile0', tile1']

theorem tile0'_pts : tile0'.pts = ![mkPt (-3) 0, mkPt 0 sq7, mkPt 0 0] := mkTri_pts _ _ _ _ _ _ _
theorem tile1'_pts : tile1'.pts = ![mkPt 3 0, mkPt 0 sq7, mkPt 0 0] := mkTri_pts _ _ _ _ _ _ _

/-! ## §2 Carrier-set equalities: reordering points does not change the filled triangle -/

theorem tile0'_carrier_eq : tile0'.carrier = tile0.carrier := by
  show convexHull ℝ (Set.range tile0'.pts) = convexHull ℝ (Set.range tile0.pts)
  rw [tile0'_pts, tile0_pts]
  congr 1
  ext x
  simp only [Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩; fin_cases i
    · exact ⟨0, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨1, rfl⟩
  · rintro ⟨i, rfl⟩; fin_cases i
    · exact ⟨0, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨1, rfl⟩

theorem tile1'_carrier_eq : tile1'.carrier = tile1.carrier := by
  show convexHull ℝ (Set.range tile1'.pts) = convexHull ℝ (Set.range tile1.pts)
  rw [tile1'_pts, tile1_pts]
  congr 1
  ext x
  simp only [Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩; fin_cases i
    · exact ⟨0, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨1, rfl⟩
  · rintro ⟨i, rfl⟩; fin_cases i
    · exact ⟨0, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨1, rfl⟩

/-! ## §3 Containment and disjointness, transferred for free via §2 -/

theorem tile0'_sub : tile0'.carrier ⊆ target.carrier := tile0'_carrier_eq ▸ tile0_sub
theorem tile1'_sub : tile1'.carrier ⊆ target.carrier := tile1'_carrier_eq ▸ tile1_sub

theorem hsub' : ∀ i, (tileF' i).carrier ⊆ target.carrier := by
  intro i; fin_cases i
  · exact tile0'_sub
  · exact tile1'_sub

theorem tiles01'_disjoint :
    Disjoint (interior tile0'.carrier) (interior tile1'.carrier) := by
  rw [tile0'_carrier_eq, tile1'_carrier_eq]; exact tiles01_disjoint

theorem hdisj' :
    Pairwise fun i j => Disjoint (interior ((tileF' i)).carrier) (interior ((tileF' j)).carrier) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first
    | exact absurd rfl hij
    | exact tiles01'_disjoint
    | exact tiles01'_disjoint.symm

/-! ## §4 The three side-length correspondences, at the new index convention -/

theorem hd01' : ∀ i, dist ((tileF' i).pts 0) ((tileF' i).pts 1) = dist (model'.pts 0) (model'.pts 1) := by
  intro i
  fin_cases i
  · rfl
  · show dist ((tile1').pts 0) ((tile1').pts 1) = dist ((tile0').pts 0) ((tile0').pts 1)
    rw [tile0'_pts, tile1'_pts]
    show dist (mkPt 3 0) (mkPt 0 sq7) = dist (mkPt (-3) 0) (mkPt 0 sq7)
    apply Erdos634.SssCongruent.dist_of_sq
    rw [dist_sq_mkPt, dist_sq_mkPt]; ring

theorem hd12' : ∀ i, dist ((tileF' i).pts 1) ((tileF' i).pts 2) = dist (model'.pts 1) (model'.pts 2) := by
  intro i
  fin_cases i
  · rfl
  · show dist ((tile1').pts 1) ((tile1').pts 2) = dist ((tile0').pts 1) ((tile0').pts 2)
    rfl

theorem hd20' : ∀ i, dist ((tileF' i).pts 2) ((tileF' i).pts 0) = dist (model'.pts 2) (model'.pts 0) := by
  intro i
  fin_cases i
  · rfl
  · show dist ((tile1').pts 2) ((tile1').pts 0) = dist ((tile0').pts 2) ((tile0').pts 0)
    rw [tile0'_pts, tile1'_pts]
    show dist (mkPt 0 0) (mkPt 3 0) = dist (mkPt 0 0) (mkPt (-3) 0)
    apply Erdos634.SssCongruent.dist_of_sq
    rw [dist_sq_mkPt, dist_sq_mkPt]; ring

/-! ## §5 The area identity, at the new index convention (the determinant's absolute value is
order-independent up to a sign flip already handled by `abs`, so this reuses `hdet`'s numbers) -/

theorem hdet0'_eval : det3 (-3) 0 0 sq7 0 0 = -3 * sq7 := by unfold det3; ring
theorem hdet1'_eval : det3 3 0 0 sq7 0 0 = 3 * sq7 := by unfold det3; ring

theorem hdet' : ∑ i, |Erdos634.AreaDet.detTri (tileF' i)| = |Erdos634.AreaDet.detTri target| := by
  have hs := sq7_pos
  have e0 : Erdos634.AreaDet.detTri tile0' = det3 (-3) 0 0 sq7 0 0 := detTri_mkTri _ _ _ _ _ _ hdet0'
  have e1 : Erdos634.AreaDet.detTri tile1' = det3 3 0 0 sq7 0 0 := detTri_mkTri _ _ _ _ _ _ hdet1'
  have eT : Erdos634.AreaDet.detTri target = det3 (-3) 0 3 0 0 sq7 :=
    detTri_mkTri _ _ _ _ _ _ hDTpos.ne'
  have hvT : det3 (-3) 0 3 0 0 sq7 = 6 * sq7 := by unfold det3; ring
  simp only [tileF', Fin.sum_univ_two]
  show |Erdos634.AreaDet.detTri tile0'| + |Erdos634.AreaDet.detTri tile1'| = _
  rw [e0, e1, eT, hdet0'_eval, hdet1'_eval, hvT]
  rw [abs_of_neg (by linarith : (-3 * sq7 : ℝ) < 0), abs_of_pos (by linarith : (0:ℝ) < 3 * sq7),
    abs_of_pos (by linarith : (0:ℝ) < 6 * sq7)]
  ring

/-! ## §6 The reordered witness -/

/-- **The reordered witness.** Same four checks as `FluxGRow3AngleWitnessDissection.dissection`
(P106), rebuilt with the model's vertex order swapped to `(B, A, M)` so its `cornerAngle`s match
`FluxGRow3Step1.congruentDissection_row3_lemmaA`'s index convention (right angle at index 2). -/
noncomputable def dissection' : CongruentDissection 2 :=
  Erdos634.CertBridge.ofCert target model' tileF' hd01' hd12' hd20' hsub' hdisj' hdet'

theorem dissection'_target : dissection'.target = target := rfl
theorem dissection'_model : dissection'.model = model' := rfl

/-! ## §7 The three `cornerAngle` values at `model'`, matching Step1's exact hypotheses

`model' = tile0' = (B, A, M)`. Side lengths, reused verbatim from
`FluxGRow3AngleWitnessDissection.lean` (`tile0_dist_BM = 3`, `tile0_dist_MA = sq7`,
`tile0_dist_AB = 4`) via `dist_comm`. -/

theorem model'_dBA : dist (mkPt (-3:ℝ) 0) (mkPt 0 sq7) = 4 := tile0_dist_AB
theorem model'_dAM : dist (mkPt (0:ℝ) sq7) (mkPt 0 0) = sq7 := by
  rw [dist_comm]; exact tile0_dist_MA
theorem model'_dMB : dist (mkPt (0:ℝ) 0) (mkPt (-3:ℝ) 0) = 3 := by
  rw [dist_comm]; exact tile0_dist_BM

/-- **hα' for `dissection'`**: angle at index 0 (`B`) equals `α456`
(`Erdos634.Draft.FluxRow4Witness.α456`, reused verbatim). -/
theorem model'_angleAt0 :
    cornerAngle (model'.pts 1) (model'.pts 0) (model'.pts 2)
      = Erdos634.Draft.FluxRow4Witness.α456 := by
  show cornerAngle (mkPt 0 sq7) (mkPt (-3) 0) (mkPt 0 0) = Erdos634.Draft.FluxRow4Witness.α456
  have hs := sq7_pos
  have h7 := sq7_sq
  have hAB : dist (mkPt (0:ℝ) sq7) (mkPt (-3) 0) = 4 := by
    rw [dist_comm]; exact model'_dBA
  have hMB : dist (mkPt (0:ℝ) 0) (mkPt (-3) 0) = 3 := model'_dMB
  have hAM : dist (mkPt (0:ℝ) sq7) (mkPt 0 0) = sq7 := model'_dAM
  have hcos : Real.cos (cornerAngle (mkPt 0 sq7) (mkPt (-3) 0) (mkPt 0 0)) = 3 / 4 := by
    rw [cos_of_sides (mkPt 0 sq7) (mkPt (-3) 0) (mkPt 0 0) (by rw [hAB]; norm_num)
      (by rw [hMB]; norm_num)]
    rw [hAB, hMB, hAM]
    rw [show ((4:ℝ)^2 + 3^2 - sq7^2) = 18 by rw [h7]; ring]
    norm_num
  have hmem : cornerAngle (mkPt 0 sq7) (mkPt (-3) 0) (mkPt (0:ℝ) 0) ∈ Set.Icc 0 Real.pi :=
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
  have hres := Real.arccos_cos hmem.1 hmem.2
  rw [hcos] at hres
  have hthis : Real.arccos (3/4 : ℝ) = Erdos634.Draft.FluxRow4Witness.α456 := by
    rw [← Erdos634.Draft.FluxRow4Witness.cos_α456]
    exact Real.arccos_cos (Erdos634.Geometry.Row3.α456_pos.le)
      (by linarith [Erdos634.Geometry.Row3.α456_lt_pi_div_two, Real.pi_pos])
  rw [← hres]; exact hthis

end Erdos634.Draft.FluxGRow3WitnessBridge

#print axioms Erdos634.Draft.FluxGRow3WitnessBridge.dissection'
#print axioms Erdos634.Draft.FluxGRow3WitnessBridge.model'_angleAt0
#print axioms Erdos634.Draft.FluxGRow3WitnessBridge.hdet'
#print axioms Erdos634.Draft.FluxGRow3WitnessBridge.hdisj'
