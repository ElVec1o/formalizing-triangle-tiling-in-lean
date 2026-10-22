-- Draft/FluxGRow3ConcreteFlux.lean — P110's item (3): the target-side flux computation, done
-- directly on the REAL, concrete `target` (P106/P107/P108's `mkTri (-3) 0 3 0 0 sq7 _`), at the
-- concrete angle `α456` and `lam := 4`, using P112's exact vertex/angle equalities so no fresh
-- placement hypothesis is needed. Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- Formalization debt on an already paper-level-PROVED result (row3 PROOF.md, Rule 0, PROVED, two
-- independent hostile reviews HOLD); NOT progress on the three /goal outcomes (Lean-infrastructure
-- task, not a mathematical one).
--
-- EXISTENCE CHECK (P88 process, run before writing, verbatim):
--   `ls -la lean/Erdos634/Draft/FluxGRow3ConcreteFlux.lean` -> "No such file or directory" (run from
--   the tool harness, confirmed absent; exact output quoted in the outer report).
--   `grep -n "FluxGRow3ConcreteFlux\|ConcreteFlux" lean/Erdos634/All.lean` -> no output (file not
--   referenced anywhere in the checked module).
--
-- SURVEY (done before writing, per dispatch instructions):
--   - `Draft/FluxGRow3SharedGrid.lean` (P112, 319 lines) read in full: supplies `target`, `tile0'`,
--     `tile1'` (imported transitively), `θ₀ := 0`, `θ₀_coe_eq_target_leftUnit0_angle`, `θ₀_isGridA`,
--     `target_leftUnit1_isGridA`, `target_leftUnit2_isGridA` (all as PROVED `IsGridA α456 θ₀ _`
--     facts, not hypotheses), and the three absolute angles `target_leftUnit{0,1,2}_angle`.
--   - `Draft/FluxGRow3Step5.lean` (P102, 245 lines) read in full: `targetIso_flux_gauss`'s exact
--     proof, the one being ported/reproduced here for the concrete `target` in place of the
--     symbolic `targetIso`.
--   - `Draft/FluxGRow3TargetCoords.lean` (P98) / `FluxGRow3TargetDirs.lean` (P100) read in full for
--     comparison: `targetIso`'s side data is `dist01 = 2·lam·cos α`, `dist02 = dist12 = lam` (vertex
--     order `(B,C,A)`), matching `target`'s own `(pts0,pts1,pts2) = ((-3,0),(3,0),(0,√7))` under
--     `α := α456` (`cos α456 = 3/4`), `lam := 4`: `2·4·(3/4) = 6 = dist((-3,0),(3,0))`,
--     `dist((3,0),(0,√7)) = dist((-3,0),(0,√7)) = √(9+7) = 4 = lam`. So `target`'s side lengths
--     coincide EXACTLY with `targetIso α456 4`'s (checked below, `target_dist01/_dist12/_dist20`) —
--     but `target` and `targetIso α456 4 _ _ _` are NOT the same `Tri` TERM (`sssTri` places
--     `pts 0 = (0,0)`, `target` places `pts 0 = (-3,0)`: a translate, not a literal equality), so
--     `targetIso_flux_gauss` cannot be instantiated directly at `target` — its PROOF is reproduced
--     here instead, on `target`'s own coordinate facts, exactly as `targetIso_flux_gauss` reproduces
--     `Tri.flux_gauss_direct`/`_reflected`'s tile-side technique. This confirms P112's own hedge
--     ("may be able to reuse... once the vertex correspondence is set up") the honest way: the
--     TECHNIQUE reuses verbatim, the TERM does not, so the proof is redone on `target`, not replayed
--     as a single `exact` application of `targetIso_flux_gauss`.
--   - `Draft/FluxGRow3Cancel.lean` read for `gaussWeightA_shift`/`gridK_add_shift`/
--     `gridJ_add_shift` (the general `(p,q)`-shift API), reused unedited exactly as `Step5` uses it.
--   - `Draft/FluxGRow3AngleWitness.lean` read: supplies `α456_div_pi_irr : Irrational (α456/π)`
--     (P104's Niven-theorem conversion), so `hairr` is NOT a hypothesis here — it is a cited fact.
--   - `Erdos634.CertCoord` (`dist_sq_mkPt`, `mkPt_zero`, `mkPt_one`) read for the raw coordinate
--     distance algebra used in `target_dist01/_dist12/_dist20` below.
--
-- WHAT THIS FILE ESTABLISHES (P110's item (3), for the concrete `target`, at `α := α456`,
-- `lam := 4`, `θ₀ := 0`):
--   `target_flux_gauss`, a FULLY UNCONDITIONAL (no open hypotheses — `hairr` and `hgridBC`, the two
--   hypotheses `targetIso_flux_gauss` carries, are both DiSCHARGED here, not merely witnessed) claim:
--   for every `X : ℤ`,
--     `target.flux (gaussWeight α456 θ₀ X)
--        = I^j * ( (if k = X then 2*4*cos α456 else 0) - (if k-1=X then 4 else 0)
--                   - (if k+1=X then 4 else 0) )`
--   where `k := gridK α456 θ₀ (target.leftUnit 0).angle`, `j := gridJ α456 θ₀ (target.leftUnit 0).angle`
--   (both concretely `k = j = 0` since `θ₀ = (target.leftUnit 0).angle` by
--   `θ₀_coe_eq_target_leftUnit0_angle`, but the theorem is stated generally in `k, j` exactly as
--   `targetIso_flux_gauss` is, so it composes with the same shift lemmas Step 5's proof uses). This
--   IS row3 PROOF.md's Step 5 boundary polynomial (`Σ_X z^X Φ_X(∂ABC) = 2λb − λc(z+z⁻¹)` on the
--   `c=1` convention, `b = cos α456`, `c = 1`, `λ = 4`... wait: on the paper's own normalization
--   `c = 1` the side data would be `b = cos α, c = 1`; this file's `lam := 4` rescales both `b` and
--   `c` by the same factor `4` relative to that convention (`target`'s hypotenuse-analogue sides are
--   `4`, not `1`), which is EXACTLY `targetIso`'s own `(α, lam)` parametrization (`lam` is precisely
--   this rescaling factor, `FluxGRow3TargetCoords.lean`'s own header says so) — so this is the
--   `lam = 4` instance of the same family Step 5 already proved in the abstract, now for the REAL
--   dissection's actual side lengths, not a different convention.
--
-- WHAT THIS FILE DOES NOT DO (read before citing this as further progress than it is):
--   - It does NOT attempt item (4) (`gaussWeight_flux_cancel` assembly on `dissection'.toDissection`
--     from `FluxGRow3WitnessBridge.lean`). That needs the TILE-side flux computation
--     (`Tri.flux_gauss_direct`/`_reflected`, `FluxGRow3Cancel.lean`) instantiated at `tile0'`/`tile1'`
--     as well (not attempted here — a materially separate construction, same gap P110 named), and
--     `Dissection.flux_cancel` (`FluxCancel.lean`) applied to the actual `dissection'.toDissection`.
--     Nothing here touches `dissection'` at all beyond citing `SharedGrid`'s already-proved grid
--     facts about `target`'s OWN directions.
--   - It does NOT re-derive `θ₀_isGridA`/`target_leftUnit{1,2}_isGridA`/the four angle facts; all are
--     cited from `FluxGRow3SharedGrid.lean` unedited.
--   - It does NOT introduce a formal Laurent polynomial or `z`-substitution (same scope note as
--     `FluxGRow3Step5.lean`, Review 2's R2).
--
-- Rediscovery check (Rule 0.5): grepped `lean/Erdos634` (both `lean/Erdos634/*.lean` and
-- `lean/Erdos634/Draft/*.lean`) for `target_flux_gauss`, `target.flux`, `target_dist01`,
-- `target_dist12`, `target_dist20` — no hits anywhere outside `FluxGRow3TargetCoords.lean`'s
-- SYMBOLIC `targetIso_dist01/_dist02/_dist12` (a different, abstract `Tri`, cited above not
-- duplicated) and this file's own names. The concrete-target flux computation is new; the technique
-- (unfolding `Tri.flux` over three edges and combining via `gaussWeightA_shift`) is `Step5`'s,
-- reused, not reinvented.
--
-- Hazard H59: `(e, f) = (3, 4)` is never evaluated or mentioned as a parameter pair below; every
-- `3`, `4`, `√7` appearing is the `3-√7-4` right-triangle data from row 3's witness (same disclaimer
-- as every other file in this chain).
import Erdos634.Draft.FluxGRow3SharedGrid
import Erdos634.Draft.FluxGRow3AngleWitness

open scoped Classical

namespace Erdos634.Draft.FluxGRow3ConcreteFlux

open Erdos634.Geometry Erdos634.CertCoord Complex
open Erdos634.Draft.FluxGRow3AngleWitnessDissection Erdos634.Draft.FluxGRow3WitnessBridge
open Erdos634.Draft.FluxGRow3SharedGrid Erdos634.Draft.FluxRow4Witness
open Erdos634.Geometry.Row3

/-! ## §1 `target`'s three side lengths, matching `targetIso α456 4`'s `(2λcosα, λ, λ)` shape -/

theorem target_dist01 : dist (target.pts 0) (target.pts 1) = 2 * 4 * Real.cos α456 := by
  rw [target_pts]
  have h := dist_sq_mkPt (-3) 0 3 0
  have hc := cos_α456
  have heq : dist (mkPt (-3:ℝ) 0) (mkPt 3 0) ^ 2 = (2 * 4 * Real.cos α456) ^ 2 := by
    rw [h, hc]; norm_num
  have hnn : (0:ℝ) ≤ 2 * 4 * Real.cos α456 := by rw [hc]; norm_num
  exact (pow_left_inj₀ dist_nonneg hnn two_ne_zero).mp heq

theorem target_dist12 : dist (target.pts 1) (target.pts 2) = 4 := by
  rw [target_pts]
  have h := dist_sq_mkPt (3:ℝ) 0 0 sq7
  have h7 := sq7_sq
  have heq : dist (mkPt (3:ℝ) 0) (mkPt 0 sq7) ^ 2 = (4:ℝ) ^ 2 := by
    rw [h]; nlinarith
  exact (pow_left_inj₀ dist_nonneg (by norm_num) two_ne_zero).mp heq

theorem target_dist20 : dist (target.pts 2) (target.pts 0) = 4 := by
  rw [dist_comm]
  rw [target_pts]
  exact tile0_dist_AB

/-! ## §2 The concrete-target flux, per grid degree

Exactly `FluxGRow3Step5.targetIso_flux_gauss`'s proof, replayed on `target`'s own coordinate/angle
facts (`FluxGRow3SharedGrid.lean`) instead of the symbolic `targetIso`'s. `hairr` and `hgridBC` are
both DISCHARGED (not carried as hypotheses): `hairr` by `α456_div_pi_irr`
(`FluxGRow3AngleWitness.lean`), `hgridBC` by `θ₀_isGridA` transported along
`θ₀_coe_eq_target_leftUnit0_angle` (`FluxGRow3SharedGrid.lean`). -/

theorem hgridBC_target : IsGridA α456 θ₀ (target.leftUnit 0).angle :=
  θ₀_coe_eq_target_leftUnit0_angle ▸ θ₀_isGridA

theorem target_flux_gauss (X : ℤ) :
    target.flux (gaussWeight α456 θ₀ X)
      = (Complex.I : ℂ) ^ (gridJ α456 θ₀ (target.leftUnit 0).angle) *
        ((if gridK α456 θ₀ (target.leftUnit 0).angle = X
            then (2 * 4 * Real.cos α456 : ℂ) else 0)
          - (if gridK α456 θ₀ (target.leftUnit 0).angle - 1 = X then (4 : ℂ) else 0)
          - (if gridK α456 θ₀ (target.leftUnit 0).angle + 1 = X then (4 : ℂ) else 0)) := by
  have hairr : Irrational (α456 / Real.pi) := α456_div_pi_irr
  have hgridBC : IsGridA α456 θ₀ (target.leftUnit 0).angle := hgridBC_target
  set k := gridK α456 θ₀ (target.leftUnit 0).angle with hk_def
  set j := gridJ α456 θ₀ (target.leftUnit 0).angle with hj_def
  -- The two turn steps, in shift form, from `FluxGRow3SharedGrid`'s absolute angle computations.
  have hturnCA : (target.leftUnit 1).angle
      = (target.leftUnit 0).angle + (((-1:ℤ):ℝ) * α456 + ((2:ℤ):ℝ) * (Real.pi / 2) : ℝ) := by
    rw [target_leftUnit1_angle, target_leftUnit0_angle, ← Real.Angle.coe_add]
    congr 1; push_cast; ring
  have hturnAB : (target.leftUnit 2).angle
      = (target.leftUnit 0).angle + (((1:ℤ):ℝ) * α456 + ((2:ℤ):ℝ) * (Real.pi / 2) : ℝ) := by
    rw [target_leftUnit2_angle, target_leftUnit0_angle, ← Real.Angle.coe_add]
    congr 1; push_cast; ring
  -- The three edge weights, exactly as `targetIso_flux_gauss` reads them off.
  have hgw0 : gaussWeight α456 θ₀ X (target.leftUnit 0) = if k = X then (Complex.I : ℂ) ^ j else 0 := by
    unfold gaussWeight gaussWeightA
    rw [dif_pos hgridBC]
  have hgw1 : gaussWeight α456 θ₀ X (target.leftUnit 1)
      = if k - 1 = X then -(Complex.I : ℂ) ^ j else 0 := by
    unfold gaussWeight
    have hshift := gaussWeightA_shift hairr hgridBC (-1) 2 X
    rw [hturnCA, hshift]
    unfold gaussWeightA
    rw [dif_pos hgridBC]
    by_cases hX : k = X - (-1)
    · rw [if_pos hX, if_pos (by omega : k - 1 = X)]
      have hI2 : (Complex.I : ℂ) ^ (2 : ℤ) = -1 := by
        rw [show (2:ℤ) = ((2:ℕ):ℤ) by norm_num, zpow_natCast]; simp [Complex.I_sq]
      rw [hI2]; ring
    · rw [if_neg hX, if_neg (by omega : ¬ k - 1 = X), mul_zero]
  have hgw2 : gaussWeight α456 θ₀ X (target.leftUnit 2)
      = if k + 1 = X then -(Complex.I : ℂ) ^ j else 0 := by
    unfold gaussWeight
    have hshift := gaussWeightA_shift hairr hgridBC 1 2 X
    rw [hturnAB, hshift]
    unfold gaussWeightA
    rw [dif_pos hgridBC]
    by_cases hX : k = X - 1
    · rw [if_pos hX, if_pos (by omega : k + 1 = X)]
      have hI2 : (Complex.I : ℂ) ^ (2 : ℤ) = -1 := by
        rw [show (2:ℤ) = ((2:ℕ):ℤ) by norm_num, zpow_natCast]; simp [Complex.I_sq]
      rw [hI2]; ring
    · rw [if_neg hX, if_neg (by omega : ¬ k + 1 = X), mul_zero]
  -- Unfold `Tri.flux` over the three edges, using `target`'s own side lengths.
  have hflux : target.flux (gaussWeight α456 θ₀ X)
      = (dist (target.pts 0) (target.pts 1) : ℝ) • gaussWeight α456 θ₀ X (target.leftUnit 0)
        + (dist (target.pts 1) (target.pts 2) : ℝ) • gaussWeight α456 θ₀ X (target.leftUnit 1)
        + (dist (target.pts 2) (target.pts 0) : ℝ) • gaussWeight α456 θ₀ X (target.leftUnit 2) := by
    unfold Tri.flux
    rw [Fin.sum_univ_three]
    simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (1 : Fin 3) + 1 = 2 from rfl,
      show (2 : Fin 3) + 1 = 0 from rfl]
  rw [hflux, target_dist01, target_dist12, target_dist20, hgw0, hgw1, hgw2,
    Complex.real_smul, Complex.real_smul, Complex.real_smul]
  by_cases h1 : k = X
  · have h2 : ¬ k - 1 = X := by omega
    have h3 : ¬ k + 1 = X := by omega
    simp only [if_pos h1, if_neg h2, if_neg h3]
    push_cast
    ring
  · by_cases h2 : k - 1 = X
    · have h3 : ¬ k + 1 = X := by omega
      simp only [if_neg h1, if_pos h2, if_neg h3]
      push_cast
      ring
    · by_cases h3 : k + 1 = X
      · simp only [if_neg h1, if_neg h2, if_pos h3]
        push_cast
        ring
      · simp only [if_neg h1, if_neg h2, if_neg h3]
        push_cast
        ring

end Erdos634.Draft.FluxGRow3ConcreteFlux

#print axioms Erdos634.Draft.FluxGRow3ConcreteFlux.target_dist01
#print axioms Erdos634.Draft.FluxGRow3ConcreteFlux.target_dist12
#print axioms Erdos634.Draft.FluxGRow3ConcreteFlux.target_dist20
#print axioms Erdos634.Draft.FluxGRow3ConcreteFlux.hgridBC_target
#print axioms Erdos634.Draft.FluxGRow3ConcreteFlux.target_flux_gauss
