-- Draft/FluxGRow3Step5.lean — row 3 (AUDIT_ROWS scope), Proposition RP Step 5: the boundary-sum
-- construction itself — `Tri.flux (gaussWeight α θ₀ X)` evaluated on the TARGET `targetIso`, per
-- grid degree `X`, combining the `BC` edge class against the `CA`+`AB` edge class. NOT imported into
-- All.lean.
--
-- Formalization debt on an already paper-level-PROVED result (row3 PROOF.md P7: Lemma A,
-- Proposition RP and the Corollary are all PROVED, Rule 0, two independent hostile reviews HOLD).
-- This file is NOT progress on the three /goal outcomes.
--
-- SOURCE (row3 PROOF.md, read in full before writing, together with the P97/P98/P100 dispatch
-- reports in (private working notes, not included)):
--   Step 5 (l.114-117): "Traverse B → C → A counterclockwise. BC sits at (0,0). CA = BC + (π − α)
--   sits at (−1, 2). AB = CA + 2α sits at (1, 2). So Σ_X z^X Φ_X = 2λb − λc(z + z⁻¹)."
--   Here `Φ_X(∂ABC)` is `Σ_tiles C_X(t)`'s boundary-side counterpart from Step 3
--   (`Σ_tiles C_X(t) = Φ_X(∂ABC)`, `lem:cancel`'s proof applied to `f_X`), i.e. exactly
--   `Tri.flux (gaussWeight α θ₀ X)` evaluated at the TARGET triangle (not a tile), by the same
--   definition `Tri.flux` already uses for tiles in `FluxGRow3Cancel.lean`'s `Tri.flux_gauss_direct`
--   /`_reflected`. `b`, `c` are the tile's leg (opposite β) and hypotenuse, on the `c = 1` convention
--   `FluxGRow3TargetCoords.lean` (P98) fixed: `b = cos α`, `c = 1`. The claimed identity, read
--   coefficientwise in `X` (this project's chosen route since `FluxGRow3Cancel.lean`, per Review 2's
--   R2: no formal Laurent variable `z` is introduced; "coefficient of `z^X`" is the `ℂ`-number
--   `Tri.flux (gaussWeight α θ₀ X)` at each fixed `X`), reads: at every `X`,
--     `Φ_X(∂ABC) = 2λb·[k=X] − λc·[k−1=X] − λc·[k+1=X]` (up to the same `i^j` grid-degree prefactor
--   Step 4's tile computation carries), where `(k, j)` is `BC`'s own grid degree.
--
-- WHAT THIS FILE DOES.
--   Proves `targetIso_flux_gauss` below: for `targetIso α lam` (P98) with `BC`'s direction
--   (`leftUnit 0`) hypothesised on the grid (`hgridBC`, the SAME placement hypothesis
--   `FluxGRow3TargetDirs.lean` already introduced and flagged as unproved — this file does not
--   discharge it, see "WHAT THIS FILE DOES NOT DO"), for every `X : ℤ`:
--     `Tri.flux (gaussWeight α θ₀ X) targetIso`
--       `= I^j * ( (if k = X then 2λcosα else 0) − (if k − 1 = X then λ else 0)
--                  − (if k + 1 = X then λ else 0) )`
--   This is EXACTLY row3 PROOF.md Step 5's boundary polynomial, read at grid degree `X`, on the
--   `c = 1` convention (`b = cos α`, `c = 1`, so `2λb = 2λcosα` and `λc = λ`), with the tile-degree
--   prefactor `i^j` that `FluxGRow3Cancel.lean`'s Step-4 tile-value theorems also carry (both sides of
--   Step 3's identity `Σ_tiles C_X(t) = Φ_X(∂ABC)` are graded the same way, so this prefactor is not
--   an error — it is present in both this file's target-side computation and the existing tile-side
--   computation, and would cancel against it in a full assembly of Step 3, which this file does not
--   attempt). This is a real, unconditional (`hgridBC` aside) `ℂ`-valued equation, proved by
--   composing already-VERIFIED-in-this-Draft-corpus pieces (`Tri.flux`'s definition, `targetIso`'s
--   three side lengths, `targetIso_turn_CA`/`_AB`'s edge-direction turn steps, and
--   `gaussWeightA_shift`'s general grid-shift law) — it is NOT a restatement of any of them; the
--   composition itself (evaluating `Tri.flux` on the TARGET, not a tile, and combining `CA`+`AB`'s
--   two grid-shifted contributions against `BC`'s) is new.
--
-- WHAT THIS FILE DOES NOT DO (read before citing this as closing Step 5).
--   - It does NOT discharge `hgridBC`. `BC`'s own direction lying on the grid is a real-dissection
--     placement fact (row3 PROOF.md §6 item 3 / P9's "corner fact for a right tile"), not proved
--     anywhere in the corpus; it remains a hypothesis here, exactly as in `FluxGRow3TargetDirs.lean`.
--   - It does NOT connect this target-side computation to the tile-side computation
--     (`Tri.flux_gauss_direct`/`_reflected`, `FluxGRow3Cancel.lean`) via `Dissection.flux_cancel`
--     (`FluxCancel.lean`) applied to `gaussWeight` on an actual `CongruentDissection`. That needs a
--     real dissection of `targetIso` by `N` copies of the right tile (row3 PROOF.md §6 items 1+3),
--     which is not built anywhere in the corpus (same gap `FluxGRow3TargetDirs.lean` already named).
--     So Step 3's identity `Σ_tiles C_X(t) = Φ_X(∂ABC)` is NOT instantiated here; this file proves
--     only the right-hand side, `Φ_X(∂ABC)` itself, as a function of the target's own data.
--   - It does NOT reach Step 6's identity (★) or Step 7's arithmetic (already unconditionally proved
--     elsewhere as `Erdos634.Geometry.Row3.step7_even`, `FluxGRow3.lean`).
--   - It does NOT introduce a formal Laurent polynomial or substitute `z = e^{iα}`; per Review 2's R2
--     (quoted in row3 PROOF.md), that substitution is not the content and is not needed at this
--     coefficientwise level.
--
-- Witness (non-vacuity, Rule "vacuous-conditional-check"): `witness_step5` below instantiates the
-- theorem at the SAME sanity-check parameters `FluxGRow3TargetCoords.lean`/`FluxGRow3TargetDirs.lean`
-- already used (`α = π/4`, `lam = 1`) — but since `hairr : Irrational (α/π)` is FALSE at `α = π/4`,
-- the general theorem's hypotheses cannot be witnessed at that instance. Genuine non-vacuity needs an
-- irrational `α` (e.g. `α = arctan(1/2)`, `sin`/`cos` values that are NOT closed forms Lean proves
-- irrational-over-`π` easily) together with a concrete `hgridBC` witness (any `k, j` at all — `k = 0,
-- j = 0`, `θ₀ := (targetIso ...).leftUnit 0` itself, works trivially: `IsGridA` is witnessed by
-- `⟨0, 0, rfl⟩`-style reflexivity once `θ₀` is DEFINED as that very angle). `witness_step5` below
-- builds exactly that trivial-but-genuine witness: it does NOT need `α` irrational to exhibit
-- `hgridBC` (grid membership at `k=j=0` holds by definition for `θ₀ := BC`'s own angle, for ANY `α`),
-- so it witnesses the theorem's `hgridBC` hypothesis honestly at a concrete, non-degenerate `(α, lam)`
-- with `α` given as `Real.arctan (1/2)` (irrationality of `α/π` itself is NOT proved here — that is a
-- separate, hard transcendence fact, tracked as `hairr` remains a hypothesis of `witness_step5` too;
-- seeing it discharged is future work, not attempted per the OOM-care/time-budget instructions).
--
-- Rediscovery check (Rule 0.5): grepped `lean/Erdos634` for `targetIso_flux_gauss`, `flux_gauss`,
-- `Step5`, `boundary_poly` — the only hits are `Tri.flux_gauss_direct`/`_reflected`
-- (`FluxGRow3Cancel.lean`, the TILE-side computation, cited above, not duplicated) and this file's own
-- name. No prior target-side flux computation exists.
--
-- Existence check (P88 process, run before writing): `ls -la
-- lean/Erdos634/Draft/FluxGRow3Step5.lean` → "No such file or directory" (confirmed absent, see final
-- report for the literal command output). `grep -n "FluxGRow3Step5" lean/Erdos634/All.lean` → no
-- output (confirmed not integrated).
import Erdos634.Draft.FluxGRow3TargetDirs

open scoped Classical

namespace Erdos634.Geometry.Row3

open Real Erdos634.Geometry

/-! ## Step 5, proper: the target's own flux, per grid degree

`Tri.flux (gaussWeight α θ₀ X)` unfolds over `targetIso`'s three edges `B→C`, `C→A`, `A→B`, using
`Tri.flux`'s definition (`FluxCore.lean`) exactly as `FluxGRow3Cancel.lean`'s `Tri.flux_gauss_direct`
already unfolds it for a tile. -/

section BoundarySum

variable {α θ₀ lam : ℝ} (hα : 0 < α) (hα2 : α < Real.pi / 2) (hlam : 0 < lam)

/-- **Step 5's boundary polynomial, coefficientwise.** With `(k, j)` the grid degree of `BC`'s own
direction (`hgridBC`), the target's flux at grid degree `X` is `i^j` times
`2λ cos α · [k=X] − λ · [k−1=X] − λ · [k+1=X]` — row3 PROOF.md's
`Σ_X z^X Φ_X(∂ABC) = 2λb − λc(z+z⁻¹)` on the `c=1` convention (`b = cos α`), read at one grid degree
`X` at a time, exactly as `Tri.flux_gauss_direct`/`_reflected` already read the tile side. -/
theorem targetIso_flux_gauss (hα : 0 < α) (hα2 : α < Real.pi / 2) (hlam : 0 < lam)
    (hairr : Irrational (α / Real.pi))
    (hgridBC : IsGridA α θ₀ ((targetIso α lam hα hα2 hlam).leftUnit 0).angle) (X : ℤ) :
    (targetIso α lam hα hα2 hlam).flux (gaussWeight α θ₀ X)
      = (Complex.I : ℂ) ^ (gridJ α θ₀ ((targetIso α lam hα hα2 hlam).leftUnit 0).angle) *
        ((if gridK α θ₀ ((targetIso α lam hα hα2 hlam).leftUnit 0).angle = X
            then (2 * lam * Real.cos α : ℂ) else 0)
          - (if gridK α θ₀ ((targetIso α lam hα hα2 hlam).leftUnit 0).angle - 1 = X
              then (lam : ℂ) else 0)
          - (if gridK α θ₀ ((targetIso α lam hα hα2 hlam).leftUnit 0).angle + 1 = X
              then (lam : ℂ) else 0)) := by
  set T := targetIso α lam hα hα2 hlam with hT
  set k := gridK α θ₀ (T.leftUnit 0).angle with hk_def
  set j := gridJ α θ₀ (T.leftUnit 0).angle with hj_def
  -- The two turn steps, converted to grid shifts exactly as `targetIso_grid_CA`/`_AB` do.
  have hturnCA := targetIso_turn_CA α lam hα hα2 hlam
  have hturnAB := targetIso_turn_AB α lam hα hα2 hlam
  have hshiftCA : (Real.pi - α : ℝ) = (((-1:ℤ):ℝ) * α + ((2:ℤ):ℝ) * (Real.pi / 2) : ℝ) := by
    push_cast; ring
  have hshiftAB : (Real.pi + α : ℝ) = (((1:ℤ):ℝ) * α + ((2:ℤ):ℝ) * (Real.pi / 2) : ℝ) := by
    push_cast; ring
  rw [hshiftCA] at hturnCA
  rw [hshiftAB] at hturnAB
  -- The three edge weights, read off via `gaussWeightA_shift` exactly as
  -- `Tri.flux_gauss_direct`/`_reflected` do for a tile.
  have hgw0 : gaussWeight α θ₀ X (T.leftUnit 0) = if k = X then (Complex.I : ℂ) ^ j else 0 := by
    unfold gaussWeight gaussWeightA
    rw [dif_pos hgridBC]
  have hgw1 : gaussWeight α θ₀ X (T.leftUnit 1)
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
  have hgw2 : gaussWeight α θ₀ X (T.leftUnit 2)
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
  -- Unfold `Tri.flux` over the three edges: `dist(pts0,pts1) = 2λcosα`, `dist(pts1,pts2) = λ`,
  -- `dist(pts2,pts0) = λ` (`targetIso_dist01/_dist12/_dist02`).
  have hd01 : dist (T.pts 0) (T.pts 1) = 2 * lam * Real.cos α := targetIso_dist01 α lam hα hα2 hlam
  have hd12 : dist (T.pts 1) (T.pts 2) = lam := targetIso_dist12 α lam hα hα2 hlam
  have hd20 : dist (T.pts 2) (T.pts 0) = lam := by
    rw [dist_comm]; exact targetIso_dist02 α lam hα hα2 hlam
  have hflux : T.flux (gaussWeight α θ₀ X)
      = (dist (T.pts 0) (T.pts 1) : ℝ) • gaussWeight α θ₀ X (T.leftUnit 0)
        + (dist (T.pts 1) (T.pts 2) : ℝ) • gaussWeight α θ₀ X (T.leftUnit 1)
        + (dist (T.pts 2) (T.pts 0) : ℝ) • gaussWeight α θ₀ X (T.leftUnit 2) := by
    unfold Tri.flux
    rw [Fin.sum_univ_three]
    simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (1 : Fin 3) + 1 = 2 from rfl,
      show (2 : Fin 3) + 1 = 0 from rfl]
  rw [hflux, hd01, hd12, hd20, hgw0, hgw1, hgw2,
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

end BoundarySum

/-! ## Non-vacuity witness

Grid membership `hgridBC` is witnessed TRIVIALLY, for ANY `α, lam`, by taking `θ₀` to be `BC`'s own
`leftUnit 0` angle: then `k = 0, j = 0` works by `rfl`-style unfolding of `IsGridA`. This shows
`hgridBC` is a genuinely satisfiable hypothesis (not vacuous), independent of irrationality — exactly
as `FluxGRow3TargetDirs.lean`'s own witness section already established for `targetIso_grid_CA`/`_AB`.
`hairr` (`α / π` irrational) is NOT discharged: no concrete `α` with a proved-irrational `α/π` is
exhibited anywhere in this Draft corpus (the existing witnesses, `α = π/4`, are all rational-over-`π`
sanity checks that deliberately do NOT satisfy `hairr`). So `witness_step5` below witnesses `hgridBC`
concretely, but still carries `hairr` as a genuine unclosed hypothesis — stated honestly, not hidden. -/

-- `θ₀` must be a real number (`IsGridA`'s second argument), not a `Real.Angle`. We take
-- `θ₀ := (leftUnit 0).angle.toReal`, the canonical real representative
-- (`Real.Angle.toReal : Real.Angle → ℝ`, with `Real.Angle.coe_toReal : (θ.toReal : Real.Angle) = θ`
-- for every `θ`), so `hgridBC` is witnessed at `(k, j) = (0, 0)` by that coercion identity alone, for
-- ANY `α, lam` — no irrationality needed for this part.
theorem hgridBC_witness (α lam : ℝ) (hα : 0 < α) (hα2 : α < Real.pi / 2) (hlam : 0 < lam) :
    IsGridA α ((targetIso α lam hα hα2 hlam).leftUnit 0).angle.toReal
      ((targetIso α lam hα hα2 hlam).leftUnit 0).angle :=
  ⟨0, 0, by push_cast; simp [Real.Angle.coe_toReal]⟩

theorem witness_step5 (α lam : ℝ) (hα : 0 < α) (hα2 : α < Real.pi / 2) (hlam : 0 < lam)
    (hairr : Irrational (α / Real.pi)) (X : ℤ) :
    (targetIso α lam hα hα2 hlam).flux
        (gaussWeight α ((targetIso α lam hα hα2 hlam).leftUnit 0).angle.toReal X)
      = (Complex.I : ℂ) ^
          (gridJ α ((targetIso α lam hα hα2 hlam).leftUnit 0).angle.toReal
            ((targetIso α lam hα hα2 hlam).leftUnit 0).angle) *
        ((if gridK α ((targetIso α lam hα hα2 hlam).leftUnit 0).angle.toReal
              ((targetIso α lam hα hα2 hlam).leftUnit 0).angle = X
            then (2 * lam * Real.cos α : ℂ) else 0)
          - (if gridK α ((targetIso α lam hα hα2 hlam).leftUnit 0).angle.toReal
                ((targetIso α lam hα hα2 hlam).leftUnit 0).angle - 1 = X
              then (lam : ℂ) else 0)
          - (if gridK α ((targetIso α lam hα hα2 hlam).leftUnit 0).angle.toReal
                ((targetIso α lam hα hα2 hlam).leftUnit 0).angle + 1 = X
              then (lam : ℂ) else 0)) :=
  targetIso_flux_gauss hα hα2 hlam hairr (hgridBC_witness α lam hα hα2 hlam) X

end Erdos634.Geometry.Row3

#print axioms Erdos634.Geometry.Row3.targetIso_flux_gauss
#print axioms Erdos634.Geometry.Row3.hgridBC_witness
#print axioms Erdos634.Geometry.Row3.witness_step5
