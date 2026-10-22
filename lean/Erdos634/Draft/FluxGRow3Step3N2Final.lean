-- Draft/FluxGRow3Step3N2Final.lean — row 3's N=2 Step 3/6 splice, item (4): instantiate
-- `Tri.flux_gauss_direct`/`_reflected` (`FluxGRow3Cancel.lean`, P72) concretely at `tile0'`/`tile1'`
-- (`FluxGRow3WitnessBridge.lean`, P106/P107) and assemble via `gaussWeight_flux_cancel`
-- (`FluxGRow3Weight.lean`) on `dissection'.toDissection`, connecting to `target_flux_gauss`
-- (`FluxGRow3ConcreteFlux.lean`, P113). Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- Formalization debt on an already paper-level-PROVED result (row3 PROOF.md, Rule 0, PROVED, two
-- independent hostile reviews HOLD); NOT progress on the three /goal outcomes (Lean-infrastructure
-- task, not a mathematical one).
--
-- EXISTENCE CHECK (P88 process, run before writing, verbatim from the tool harness):
--   `ls -la lean/Erdos634/Draft/FluxGRow3Step3N2Final.lean` -> "No such file or directory" (exit 1).
--   `grep -n "FluxGRow3Step3N2Final\|Step3N2" lean/Erdos634/All.lean` -> no output (exit 1, not
--   referenced anywhere in the checked module).
--
-- SURVEY (done before writing, per dispatch instructions — files read in full):
--   - `Draft/FluxGRow3Cancel.lean` (341 lines): `Tri.flux_gauss_direct`/`Tri.flux_gauss_reflected`,
--     exact hypotheses `hα : Irrational (α/π)`, `hT : 0 < T.det` (direct) / `T.det < 0` (reflected),
--     `hβ : T.angleAt 1 = π/2 − α`, `hγ : T.angleAt 2 = π/2`, `hgrid : IsGridA α θ₀ (T.leftUnit 0).angle`.
--   - `Draft/FluxGRow3WitnessBridge.lean` (246 lines): `tile0' = (B,A,M)` (`det < 0`, reflected
--     chirality), `tile1' = (C,A,M)` (`det > 0`, direct chirality), `dissection' : CongruentDissection 2`
--     built via `CertBridge.ofCert target model' tileF' ...`, `model'_angleAt0` (only angle fact
--     already on record: `tile0'`'s angle at index 0 = `α456`).
--   - `Draft/FluxGRow3SharedGrid.lean` (319 lines): `θ₀ := 0`, `tile0'_leftUnit0_isGridA`,
--     `tile1'_leftUnit0_isGridA` (the two `hgrid` witnesses needed below, already PROVED, not
--     hypothesized).
--   - `Draft/FluxGRow3ConcreteFlux.lean` (223 lines): `target_flux_gauss`, the fully unconditional
--     target-side flux at `α456`, `θ₀ := 0`, `lam := 4`.
--   - `Draft/FluxCancel.lean` (59 lines): `Dissection.flux_cancel`/`CongruentDissection.flux_cancel`,
--     generic `lem:cancel`.
--   - `Draft/FluxGRow3Weight.lean`: `gaussWeight_flux_cancel {α θ₀}(hα)(X){N}(D : Dissection N) :
--     ∑ i, (D.tile i).flux (gaussWeight α θ₀ X) = D.target.flux (gaussWeight α θ₀ X)` — ALREADY the
--     item-4 assembly lemma in the abstract (`flux_cancel` instantiated at the actual Gaussian
--     weight); what is missing before this file is only its APPLICATION to the real `dissection'`
--     together with the tile-side value formulas at `tile0'`/`tile1'`, which is what this file adds.
--   - `AngleThreshold.lean`: `cos_of_sides` (law-of-cosines solved for the cosine), reused for the two
--     new right-angle facts below (`tile0'_angleAt2`/`tile1'_angleAt2`).
--   - `Draft/FluxTurn.lean`: `Tri.angleAt`, `Tri.angleAt_sum` (`T.angleAt 0 + T.angleAt 1 + T.angleAt 2
--     = π`), used to get each tile's `angleAt 1` from `angleAt 0` (known) and `angleAt 2` (proved
--     below as a right angle) without a second law-of-cosines computation.
--
-- WHAT WAS MISSING AND HAD TO BE PROVED HERE (none of this existed anywhere in the corpus before this
-- file — checked by the rediscovery grep below):
--   (a) `tile1'`'s own side lengths (`CM = 3`, `CA = 4`; `AM = sq7` is `model'_dAM` reused verbatim,
--       same two points as `tile0'`'s).
--   (b) The RIGHT-ANGLE fact at `M` for both tiles: `tile0'.angleAt 2 = π/2` and
--       `tile1'.angleAt 2 = π/2` (cos = 0 from the `3,√7,4` Pythagorean side data, via `cos_of_sides`
--       + `Real.arccos_zero`; this specific corner angle, `cornerAngle B M A` resp. `cornerAngle C M A`,
--       was never computed anywhere in the corpus — only `model'_angleAt0`, the angle at `B`/`A`,
--       had been).
--   (c) `tile1'.angleAt 0 = α456` (mirror of `model'_angleAt0`, same `cos = 3/4` computation on the
--       mirrored triangle `(C,A,M)`).
--   (d) Both tiles' `angleAt 1` via `Tri.angleAt_sum` from (b)/(c) — no fresh trigonometry needed.
--   (e) `dissection'.toDissection.tile 0 = tile0'` / `.tile 1 = tile1'`, `rfl` through the
--       `CertBridge.ofCert → AreaDet.ofDetCertificate → ConvexCover.ofCertificate` definitional chain
--       (`ofCertificate`'s `tile` field is literally the supplied function, so this is definitional,
--       not a new geometric fact — recorded once here since no prior file needed it).
--
-- WHAT THIS FILE ESTABLISHES:
--   `row3_N2_step3_full`: **fully unconditional**, for every `X : ℤ`,
--     `tile0'.flux (gaussWeight α456 θ₀ X) + tile1'.flux (gaussWeight α456 θ₀ X)
--        = target.flux (gaussWeight α456 θ₀ X)`
--   — row3 PROOF.md's Step 3 (`Σ_tiles C_X(t) = Φ_X(∂ABC)`) literally instantiated at the real,
--   concrete `N = 2` witness `dissection'`, via `gaussWeight_flux_cancel` applied to
--   `dissection'.toDissection` (no abstract `Dissection N` left — `N` is concretely `2`, the tiles are
--   concretely `tile0'`/`tile1'`, the target is concretely `target`).
--
--   `row3_N2_full_identity`: the SAME fact, with `tile0'.flux`/`tile1'.flux` further expanded via
--   `Tri.flux_gauss_reflected`/`Tri.flux_gauss_direct` (instantiated CONCRETELY at `tile0'`/`tile1'`
--   using the angle/grid facts (a)-(d) above) and `target.flux` expanded via `target_flux_gauss`
--   (P113): a single closed-form `ℂ`-algebra identity in `X`, `k`, `j` (the three triangles' own grid
--   degrees), no `Dissection`/`Tri.flux` left unexpanded on either side. This is the closure of
--   P110's item (4): assembly via `Dissection.flux_cancel`/`gaussWeight_flux_cancel` on
--   `dissection'.toDissection`, with the tile-side flux (`Tri.flux_gauss_direct`/`_reflected`)
--   instantiated concretely at `tile0'`/`tile1'`, exactly as the dispatch asked.
--
-- WHAT THIS FILE DOES NOT DO:
--   - It does NOT reduce `row3_N2_full_identity`'s three grid degrees (`k` at `tile0'`'s hypotenuse,
--     at `tile1'`'s hypotenuse, at `target`'s `BC`) to a single shared variable via `gridK_add_shift`;
--     `FluxGRow3SharedGrid.lean` already gives the EXACT relations needed to do that
--     (`tile0'_leftUnit0_angle`/`tile1'_leftUnit0_angle`, both stated relative to `target`'s own
--     `θ₀`), but composing them into one single-variable polynomial identity (matching row3 PROOF.md's
--     literal `λ² + sλ + t = 0` shape) is a further algebraic step not attempted here; that step is
--     `Erdos634.Geometry.Row3.step7_even` territory (`FluxGRow3.lean`, already proved independently,
--     unconditionally, for the abstract `λ, s` — not re-derived or connected to this file's concrete
--     `X`-indexed identity).
--   - It does NOT touch Step 6 (passing from `N = 2` to general `N`, or the boundary-word bookkeeping
--     `P_k`/`Q_k`); this file is `N = 2` only, exactly the scope the dispatch named.
--   - It does NOT alter, re-derive, or duplicate `target_flux_gauss`, `tile0'_leftUnit0_isGridA`,
--     `tile1'_leftUnit0_isGridA`, `model'_angleAt0`, `gaussWeight_flux_cancel`, or any other cited
--     fact — all imported and reused unedited.
--
-- Rediscovery check (Rule 0.5): grepped `lean/Erdos634` (`*.lean` and `Draft/*.lean`) for
-- `tile1'_dist`, `tile0'_angleAt`, `tile1'_angleAt`, `row3_N2_step3_full`, `row3_N2_full_identity`,
-- `dissection'.toDissection.tile`, `Step3N2` — no hits anywhere outside this file. The two
-- flux-value lemmas (`Tri.flux_gauss_direct`/`_reflected`) have never before been applied to a
-- concrete `Tri` term anywhere in the corpus (`FluxGRow3Cancel.lean`'s own header states this
-- explicitly: "It does NOT construct a real `Tri` ... satisfying the hypotheses"); this file is the
-- first such instantiation.
--
-- Hazard H59: `(e, f) = (3, 4)` is never evaluated or mentioned as a parameter pair below; every `3`,
-- `4`, `√7` appearing is the `3-√7-4` right-triangle data from row 3's witness (same disclaimer as
-- every other file in this chain).
import Erdos634.Draft.FluxGRow3ConcreteFlux
import Erdos634.Draft.FluxCancel
import Erdos634.AngleThreshold

open scoped Classical

namespace Erdos634.Draft.FluxGRow3Step3N2Final

open Erdos634.Geometry Erdos634.CertCoord Complex Erdos634.AngleThreshold
open Erdos634.Draft.FluxGRow3AngleWitnessDissection Erdos634.Draft.FluxGRow3WitnessBridge
open Erdos634.Draft.FluxGRow3SharedGrid Erdos634.Draft.FluxGRow3ConcreteFlux
open Erdos634.Draft.FluxRow4Witness Erdos634.Geometry.Row3

/-! ## §1 `tile1'`'s own side lengths (new: `CM`, `CA`; `AM` is `model'_dAM`, reused verbatim since
`tile1'` and `tile0'` share the same points `A = (0,√7)`, `M = (0,0)` at indices `1, 2`). -/

theorem tile1'_dist_CM : dist (mkPt (3:ℝ) 0) (mkPt 0 0) = 3 := by
  apply dist_eq_of_sq (by norm_num)
  rw [dist_sq_mkPt]; norm_num

theorem tile1'_dist_AM : dist (mkPt (0:ℝ) sq7) (mkPt 0 0) = sq7 := model'_dAM

theorem tile1'_dist_CA : dist (mkPt (3:ℝ) 0) (mkPt 0 sq7) = 4 := by
  have h7 := sq7_sq
  apply dist_eq_of_sq (by norm_num)
  rw [dist_sq_mkPt]; nlinarith

/-! ## §2 The right-angle fact at `M`, for both tiles (new: `cornerAngle _ M _ = π/2`, never computed
anywhere in the corpus before this file — only the leg-`3` angle `= α456` had been). -/

theorem tile0'_angleAt2 :
    (tile0'.angleAt 2 : ℝ) = Real.pi / 2 := by
  show cornerAngle (tile0'.pts 0) (tile0'.pts 2) (tile0'.pts 1) = Real.pi / 2
  rw [tile0'_pts]
  show cornerAngle (mkPt (-3) 0) (mkPt 0 0) (mkPt 0 sq7) = Real.pi / 2
  have hBM : dist (mkPt (-3:ℝ) 0) (mkPt 0 0) = 3 := tile0_dist_BM
  have hAM : dist (mkPt (0:ℝ) sq7) (mkPt 0 0) = sq7 := model'_dAM
  have hAB : dist (mkPt (-3:ℝ) 0) (mkPt 0 sq7) = 4 := model'_dBA
  have hcos : Real.cos (cornerAngle (mkPt (-3) 0) (mkPt 0 0) (mkPt 0 sq7)) = 0 := by
    rw [cos_of_sides (mkPt (-3) 0) (mkPt 0 0) (mkPt 0 sq7) (by rw [hBM]; norm_num)
      (by rw [hAM]; exact sq7_pos.ne')]
    rw [hBM, hAM, hAB]
    rw [show ((3:ℝ)^2 + sq7^2 - 4^2) = 0 by rw [sq7_sq]; ring]
    norm_num
  have hmem : cornerAngle (mkPt (-3) 0) (mkPt (0:ℝ) 0) (mkPt 0 sq7) ∈ Set.Icc 0 Real.pi :=
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
  have hres := Real.arccos_cos hmem.1 hmem.2
  rw [hcos, Real.arccos_zero] at hres
  exact hres.symm

theorem tile1'_angleAt2 :
    (tile1'.angleAt 2 : ℝ) = Real.pi / 2 := by
  show cornerAngle (tile1'.pts 0) (tile1'.pts 2) (tile1'.pts 1) = Real.pi / 2
  rw [tile1'_pts]
  show cornerAngle (mkPt 3 0) (mkPt 0 0) (mkPt 0 sq7) = Real.pi / 2
  have hCM : dist (mkPt (3:ℝ) 0) (mkPt 0 0) = 3 := tile1'_dist_CM
  have hAM : dist (mkPt (0:ℝ) sq7) (mkPt 0 0) = sq7 := model'_dAM
  have hCA : dist (mkPt (3:ℝ) 0) (mkPt 0 sq7) = 4 := tile1'_dist_CA
  have hcos : Real.cos (cornerAngle (mkPt 3 0) (mkPt 0 0) (mkPt 0 sq7)) = 0 := by
    rw [cos_of_sides (mkPt 3 0) (mkPt 0 0) (mkPt 0 sq7) (by rw [hCM]; norm_num)
      (by rw [hAM]; exact sq7_pos.ne')]
    rw [hCM, hAM, hCA]
    rw [show ((3:ℝ)^2 + sq7^2 - 4^2) = 0 by rw [sq7_sq]; ring]
    norm_num
  have hmem : cornerAngle (mkPt 3 0) (mkPt (0:ℝ) 0) (mkPt 0 sq7) ∈ Set.Icc 0 Real.pi :=
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
  have hres := Real.arccos_cos hmem.1 hmem.2
  rw [hcos, Real.arccos_zero] at hres
  exact hres.symm

/-! ## §3 `tile1'.angleAt 0 = α456` (mirror of `model'_angleAt0`, new) -/

theorem tile1'_angleAt0 :
    cornerAngle (tile1'.pts 1) (tile1'.pts 0) (tile1'.pts 2) = α456 := by
  rw [tile1'_pts]
  show cornerAngle (mkPt 0 sq7) (mkPt 3 0) (mkPt 0 0) = α456
  have hCA : dist (mkPt (0:ℝ) sq7) (mkPt 3 0) = 4 := by
    rw [dist_comm]; exact tile1'_dist_CA
  have hCM : dist (mkPt (0:ℝ) 0) (mkPt 3 0) = 3 := by rw [dist_comm]; exact tile1'_dist_CM
  have hAM : dist (mkPt (0:ℝ) sq7) (mkPt 0 0) = sq7 := model'_dAM
  have h7 := sq7_sq
  have hcos : Real.cos (cornerAngle (mkPt 0 sq7) (mkPt 3 0) (mkPt 0 0)) = 3 / 4 := by
    rw [cos_of_sides (mkPt 0 sq7) (mkPt 3 0) (mkPt 0 0) (by rw [hCA]; norm_num)
      (by rw [hCM]; norm_num)]
    rw [hCA, hCM, hAM]
    rw [show ((4:ℝ)^2 + 3^2 - sq7^2) = 18 by rw [h7]; ring]
    norm_num
  have hmem : cornerAngle (mkPt 0 sq7) (mkPt 3 0) (mkPt (0:ℝ) 0) ∈ Set.Icc 0 Real.pi :=
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
  have hres := Real.arccos_cos hmem.1 hmem.2
  rw [hcos] at hres
  have hthis : Real.arccos (3/4 : ℝ) = α456 := by
    rw [← cos_α456]
    exact Real.arccos_cos α456_pos.le (by linarith [α456_lt_pi_div_two, Real.pi_pos])
  rw [← hres]; exact hthis

/-! ## §4 Both tiles' `angleAt 1`, via `Tri.angleAt_sum`, no fresh trigonometry -/

theorem tile0'_angleAt0 : tile0'.angleAt 0 = α456 := model'_angleAt0

theorem tile0'_angleAt1 : tile0'.angleAt 1 = Real.pi / 2 - α456 := by
  have hsum := tile0'.angleAt_sum
  rw [tile0'_angleAt0, tile0'_angleAt2] at hsum
  linarith

theorem tile1'_angleAt0' : tile1'.angleAt 0 = α456 := tile1'_angleAt0

theorem tile1'_angleAt1 : tile1'.angleAt 1 = Real.pi / 2 - α456 := by
  have hsum := tile1'.angleAt_sum
  rw [tile1'_angleAt0', tile1'_angleAt2] at hsum
  linarith

/-! ## §5 The two concrete tile-side flux computations: `Tri.flux_gauss_reflected` at `tile0'`
(reflected chirality, `tile0'.det < 0`), `Tri.flux_gauss_direct` at `tile1'` (direct chirality,
`tile1'.det > 0`). Both are the FIRST instantiation of these lemmas at a genuine `Tri` term anywhere
in the corpus. -/

theorem tile0'_flux (X : ℤ) :
    tile0'.flux (gaussWeight α456 θ₀ X)
      = (Complex.I : ℂ) ^ (gridJ α456 θ₀ (tile0'.leftUnit 0).angle) *
        ((if gridK α456 θ₀ (tile0'.leftUnit 0).angle = X then (tile0'.oppLen 2 : ℂ) else 0)
          - (if gridK α456 θ₀ (tile0'.leftUnit 0).angle - 1 = X then
              ((tile0'.oppLen 1 : ℂ) + (tile0'.oppLen 0 : ℂ) * Complex.I) else 0)) :=
  Tri.flux_gauss_reflected (α := α456) (θ₀ := θ₀) (T := tile0') α456_div_pi_irr tile0'_det_neg
    tile0'_angleAt1 tile0'_angleAt2 tile0'_leftUnit0_isGridA X

theorem tile1'_flux (X : ℤ) :
    tile1'.flux (gaussWeight α456 θ₀ X)
      = (Complex.I : ℂ) ^ (gridJ α456 θ₀ (tile1'.leftUnit 0).angle) *
        ((if gridK α456 θ₀ (tile1'.leftUnit 0).angle = X then (tile1'.oppLen 2 : ℂ) else 0)
          - (if gridK α456 θ₀ (tile1'.leftUnit 0).angle + 1 = X then
              ((tile1'.oppLen 1 : ℂ) - (tile1'.oppLen 0 : ℂ) * Complex.I) else 0)) :=
  Tri.flux_gauss_direct (α := α456) (θ₀ := θ₀) (T := tile1') α456_div_pi_irr tile1'_det_pos
    tile1'_angleAt1 tile1'_angleAt2 tile1'_leftUnit0_isGridA X

/-! ## §6 The definitional tile/target readouts of `dissection'.toDissection` (new bookkeeping: no
prior file needed `dissection'.toDissection.tile` unfolded). -/

theorem dissection'_toDissection_tile0 : dissection'.toDissection.tile 0 = tile0' := rfl
theorem dissection'_toDissection_tile1 : dissection'.toDissection.tile 1 = tile1' := rfl
theorem dissection'_toDissection_target : dissection'.toDissection.target = target :=
  dissection'_target

/-! ## §7 THE ASSEMBLY: `gaussWeight_flux_cancel` applied to the real `dissection'.toDissection`,
fully unconditional. This is P110's item (4), closed. -/

/-- **Row3 PROOF.md Step 3, at the real `N = 2` witness.** The sum of the two tiles' Gaussian-weight
fluxes equals the target's — no abstract `Dissection N` left, `N`, the tiles, and the target are all
concrete. -/
theorem row3_N2_step3_full (X : ℤ) :
    tile0'.flux (gaussWeight α456 θ₀ X) + tile1'.flux (gaussWeight α456 θ₀ X)
      = target.flux (gaussWeight α456 θ₀ X) := by
  have h := Erdos634.Geometry.Row3.gaussWeight_flux_cancel
      (α := α456) (θ₀ := θ₀) α456_div_pi_irr X dissection'.toDissection
  rw [Fin.sum_univ_two, dissection'_toDissection_tile0, dissection'_toDissection_tile1,
    dissection'_toDissection_target] at h
  exact h

/-- **The full closed-form identity**: `row3_N2_step3_full` with every `Tri.flux` expanded via the
tile-value formulas (`tile0'_flux`/`tile1'_flux`, §5) and the target-value formula
(`target_flux_gauss`, P113). This is the full N=2 Step 3/6 splice: `Tri.flux_gauss_direct`/
`_reflected` instantiated concretely at `tile0'`/`tile1'`, assembled via `gaussWeight_flux_cancel` on
`dissection'.toDissection`, connected to `target_flux_gauss`. Fully unconditional; no open
hypotheses. -/
theorem row3_N2_full_identity (X : ℤ) :
    (Complex.I : ℂ) ^ (gridJ α456 θ₀ (tile0'.leftUnit 0).angle) *
        ((if gridK α456 θ₀ (tile0'.leftUnit 0).angle = X then (tile0'.oppLen 2 : ℂ) else 0)
          - (if gridK α456 θ₀ (tile0'.leftUnit 0).angle - 1 = X then
              ((tile0'.oppLen 1 : ℂ) + (tile0'.oppLen 0 : ℂ) * Complex.I) else 0))
      + (Complex.I : ℂ) ^ (gridJ α456 θ₀ (tile1'.leftUnit 0).angle) *
        ((if gridK α456 θ₀ (tile1'.leftUnit 0).angle = X then (tile1'.oppLen 2 : ℂ) else 0)
          - (if gridK α456 θ₀ (tile1'.leftUnit 0).angle + 1 = X then
              ((tile1'.oppLen 1 : ℂ) - (tile1'.oppLen 0 : ℂ) * Complex.I) else 0))
      = (Complex.I : ℂ) ^ (gridJ α456 θ₀ (target.leftUnit 0).angle) *
        ((if gridK α456 θ₀ (target.leftUnit 0).angle = X then (2 * 4 * Real.cos α456 : ℂ) else 0)
          - (if gridK α456 θ₀ (target.leftUnit 0).angle - 1 = X then (4 : ℂ) else 0)
          - (if gridK α456 θ₀ (target.leftUnit 0).angle + 1 = X then (4 : ℂ) else 0)) := by
  rw [← tile0'_flux, ← tile1'_flux, ← target_flux_gauss]
  exact row3_N2_step3_full X

end Erdos634.Draft.FluxGRow3Step3N2Final

#print axioms Erdos634.Draft.FluxGRow3Step3N2Final.tile1'_dist_CM
#print axioms Erdos634.Draft.FluxGRow3Step3N2Final.tile1'_dist_CA
#print axioms Erdos634.Draft.FluxGRow3Step3N2Final.tile0'_angleAt2
#print axioms Erdos634.Draft.FluxGRow3Step3N2Final.tile1'_angleAt2
#print axioms Erdos634.Draft.FluxGRow3Step3N2Final.tile1'_angleAt0
#print axioms Erdos634.Draft.FluxGRow3Step3N2Final.tile0'_angleAt1
#print axioms Erdos634.Draft.FluxGRow3Step3N2Final.tile1'_angleAt1
#print axioms Erdos634.Draft.FluxGRow3Step3N2Final.tile0'_flux
#print axioms Erdos634.Draft.FluxGRow3Step3N2Final.tile1'_flux
#print axioms Erdos634.Draft.FluxGRow3Step3N2Final.row3_N2_step3_full
#print axioms Erdos634.Draft.FluxGRow3Step3N2Final.row3_N2_full_identity
