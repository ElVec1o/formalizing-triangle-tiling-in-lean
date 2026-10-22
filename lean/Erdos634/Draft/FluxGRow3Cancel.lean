-- Draft/FluxGRow3Cancel.lean — row 3 (AUDIT_ROWS scope), Proposition RP Step 4: the tile-value
-- computation of `gaussWeight` on a right tile, both chiralities. Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
-- Source: (private working notes, not included) ("row3" below), §2 Proposition RP, Step 4, read in
-- full together with §5-6 and the E3/R2 record before writing anything here.
--
-- Formalization debt on an already paper-level-PROVED result (row3 PROOF.md P7: Lemma A,
-- Proposition RP and the Corollary are all PROVED, Rule 0, two independent hostile reviews HOLD).
-- This file is NOT progress on the three /goal outcomes.
--
-- WHAT THIS FILE DOES.
--   Row3 PROOF.md Step 4 computes, for a tile with an edge in the grid `G = θ₀ + ℤα + ℤ(π/2)`, the
--   tile's contribution to `Σ_X z^X Φ_X(tile)` as one of two formulas (direct / reflected chirality):
--     direct:    i^j (c·[k=X] − (b − ia)·[k+1=X])
--     reflected: i^j (c·[k=X] − (b + ia)·[k−1=X])
--   where (k, j) is the grid degree of the *hypotenuse*, directed ccw, and a, b, c are the tile's
--   legs/hypotenuse. This file proves BOTH formulas as unconditional `Tri`-level theorems about
--   `Tri.flux (gaussWeight α θ₀ X)`, for any `Tri` whose corner angles are (α, π/2 − α, π/2) in the
--   PROOF.md order and whose hypotenuse direction (`leftUnit 0`) lies on the grid — i.e. exactly
--   row3 PROOF.md's own hypotheses on a placed tile, stated abstractly (no `CongruentDissection`
--   needed to STATE or PROVE the tile-value formula itself).
--
--   Route taken, per the task's instruction to prefer genuine `ℂ`-algebra over `LaurentPolynomial`:
--   no formal Laurent variable `z` is introduced at all. Instead, `gaussWeight`'s own definition
--   (`gaussWeightA`, already built in `FluxGRow3Weight.lean`) is graded by an explicit integer `X`,
--   and the "coefficient of `z^X`" is read off directly as the `ℂ`-number `T.flux (gaussWeight α θ₀
--   X)`, for each fixed `X` in turn. This is exactly Row3's own recorded preference (§ "Review 2
--   record", R2): the *content* is in genuine `ℂ`-valued equations at each grid degree, not in a
--   polynomial ring; no substitution `z = e^{iα}` is made or needed here, and none of the
--   `LaurentPolynomial` API is used.
--
--   The bridge lemma making this possible (`gaussWeightA_shift` below) is new: it computes how
--   `gaussWeightA`'s value changes under shifting the angle by `p·α + q·(π/2)` for ARBITRARY
--   integers `p, q` (the existing file only had the special case `p = 0, q = 2`, i.e. shifting by
--   `π`, needed for oddness). It is proved by the same method as the existing `gridK_add_pi` /
--   `gridJ_add_pi` (`FluxGRow3Weight.lean`), generalized.
--
-- WHAT THIS FILE DOES NOT DO (read before citing this as progress on Proposition RP).
--   - It does NOT construct a real `Tri` (coordinates) satisfying the hypotheses of the two
--     theorems below. The hypotheses (`T.angleAt 0 = α`, `T.angleAt 1 = π/2 − α`,
--     `T.angleAt 2 = π/2`, grid membership of the hypotenuse direction) are exactly what a genuine
--     right-tile placement would supply, but no such placement is built here or anywhere in the
--     corpus (row3 PROOF.md §6 item 3 / P9: "the corner fact for a right tile ... not built
--     anywhere"). So these theorems are conditional on a witness that is NOT exhibited in Lean; the
--     Python witnesses in row3 PROOF.md §5 are numeric coordinates, not Lean `Tri` terms. This file
--     does not close that gap; see the final report.
--   - It does NOT build Steps 5-6's boundary computation (the analogous flux of the *target* ABC)
--     or the passage from finitely many tile contributions to the sums `P_k`, `Q_k` over an actual
--     `CongruentDissection`'s `N` tiles. That needs a real dissection of the isosceles target by `N`
--     copies of the right tile, which needs the same missing corner-fact/placement infrastructure.
--   - It does NOT re-derive Step 7 (the `λ² + sλ + t = 0` arithmetic and `Even N`): that is already
--     proved unconditionally, with witnesses, as `Erdos634.Geometry.Row3.step7_even` in
--     `FluxGRow3.lean` (verified present, no `sorry`, by reading that file in this session). Nothing
--     here duplicates it.
--
-- Reuse (cited, not re-derived): `gaussWeightA`, `IsGridA`, `gridK`, `gridJ`, `gridK_eq_of_spec`,
-- `gridJ_eq_of_spec`, `Complex.I_zpow_eq_of_mod4` (`FluxGRow3Weight.lean`); `Tri.flux`
-- (`FluxCore.lean`); `Tri.leftUnit_turn_of_pos`, `Tri.leftUnit_turn_of_neg`, `Tri.angleAt`,
-- `Tri.angleAt_sum`, `Tri.oppLen`, `Dir.angle` (`FluxTurn.lean`).
--
-- Rediscovery check (Rule 0.5): grepped `lean/Erdos634` for `gaussWeightA_shift`, `flux_gauss`,
-- `Tri.flux_gauss` — no hits outside this file.
import Erdos634.Draft.FluxGRow3Weight
import Erdos634.Draft.FluxTurn

open scoped Classical

namespace Erdos634.Geometry.Row3

open Real Erdos634.Geometry

/-! ## The general grid shift, arbitrary `(p, q)`

Generalizes `isGridA_add_pi` / `gridK_add_pi` / `gridJ_add_pi` (special case `p = 0, q = 2`) to an
arbitrary integer shift `p·α + q·(π/2)`. -/

theorem isGridA_add_shift {α θ₀ : ℝ} {θ : Real.Angle} (h : IsGridA α θ₀ θ) (p q : ℤ) :
    IsGridA α θ₀ (θ + ((p : ℝ) * α + (q : ℝ) * (Real.pi / 2) : ℝ)) := by
  obtain ⟨k, j, hk⟩ := h
  refine ⟨k + p, j + q, ?_⟩
  rw [hk, ← Real.Angle.coe_add]
  congr 1
  push_cast
  ring

theorem gridK_add_shift {α θ₀ : ℝ} (hα : Irrational (α / Real.pi)) {θ : Real.Angle}
    (h : IsGridA α θ₀ θ) (p q : ℤ) :
    gridK α θ₀ (θ + ((p : ℝ) * α + (q : ℝ) * (Real.pi / 2) : ℝ)) = gridK α θ₀ θ + p := by
  obtain ⟨k, j, hk⟩ := h
  have hspec : θ + ((p : ℝ) * α + (q : ℝ) * (Real.pi / 2) : ℝ)
      = ((θ₀ + ((k + p : ℤ) : ℝ) * α + ((j + q : ℤ) : ℝ) * (Real.pi / 2) : ℝ) : Real.Angle) := by
    rw [hk, ← Real.Angle.coe_add]; congr 1; push_cast; ring
  rw [gridK_eq_of_spec hα hspec, gridK_eq_of_spec hα hk]

theorem gridJ_add_shift {α θ₀ : ℝ} (hα : Irrational (α / Real.pi)) {θ : Real.Angle}
    (h : IsGridA α θ₀ θ) (p q : ℤ) :
    (4 : ℤ) ∣ (gridJ α θ₀ (θ + ((p : ℝ) * α + (q : ℝ) * (Real.pi / 2) : ℝ)) - (gridJ α θ₀ θ + q)) := by
  obtain ⟨k, j, hk⟩ := h
  have hspec : θ + ((p : ℝ) * α + (q : ℝ) * (Real.pi / 2) : ℝ)
      = ((θ₀ + ((k + p : ℤ) : ℝ) * α + ((j + q : ℤ) : ℝ) * (Real.pi / 2) : ℝ) : Real.Angle) := by
    rw [hk, ← Real.Angle.coe_add]; congr 1; push_cast; ring
  have hd1 : (4 : ℤ) ∣ (gridJ α θ₀ (θ + ((p : ℝ) * α + (q : ℝ) * (Real.pi / 2) : ℝ)) - (j + q)) :=
    gridJ_eq_of_spec hα hspec
  have hd2 : (4 : ℤ) ∣ (gridJ α θ₀ θ - j) := gridJ_eq_of_spec hα hk
  have hring : gridJ α θ₀ (θ + ((p : ℝ) * α + (q : ℝ) * (Real.pi / 2) : ℝ)) - (gridJ α θ₀ θ + q)
      = (gridJ α θ₀ (θ + ((p : ℝ) * α + (q : ℝ) * (Real.pi / 2) : ℝ)) - (j + q))
        - (gridJ α θ₀ θ - j) := by ring
  rw [hring]
  exact dvd_sub hd1 hd2

/-- **The shift law for `gaussWeightA`, arbitrary `(p, q)`.** Shifting the angle by `p·α + q·π/2`
shifts the grid degree `X` down by `p` and multiplies the value by `i^q`. This is row3 PROOF.md
Step 2's "adding `π` keeps `k` and adds `2` to `j`" (the special case `p = 0, q = 2`, already in
`FluxGRow3Weight.lean` as `gaussWeightA_odd`), generalized to the shifts Step 4 actually needs
(`p = ±1`, `q = ±1, ±2`). -/
theorem gaussWeightA_shift {α θ₀ : ℝ} (hα : Irrational (α / Real.pi)) {θ : Real.Angle}
    (h : IsGridA α θ₀ θ) (p q X : ℤ) :
    gaussWeightA α θ₀ X (θ + ((p : ℝ) * α + (q : ℝ) * (Real.pi / 2) : ℝ))
      = (Complex.I : ℂ) ^ q * gaussWeightA α θ₀ (X - p) θ := by
  have hgrid2 := isGridA_add_shift h p q
  have hk2 := gridK_add_shift hα h p q
  have hj2 := gridJ_add_shift hα h p q
  unfold gaussWeightA
  rw [dif_pos hgrid2, dif_pos h, hk2]
  by_cases hX : gridK α θ₀ θ + p = X
  · rw [if_pos hX]
    have hXp : gridK α θ₀ θ = X - p := by omega
    rw [if_pos hXp, Complex.I_zpow_eq_of_mod4 hj2, zpow_add₀ Complex.I_ne_zero]
    ring
  · have hXp : ¬ gridK α θ₀ θ = X - p := by omega
    rw [if_neg hX, if_neg hXp, mul_zero]

/-! ## Step 4: the tile value, both chiralities

Notation matches row3 PROOF.md exactly: a right tile with angles `α` (vertex 0), `β = π/2 − α`
(vertex 1), `π/2` (vertex 2, the right angle); `a = T.oppLen 0` (opposite `α`), `b = T.oppLen 1`
(opposite `β`), `c = T.oppLen 2` (the hypotenuse, opposite the right angle, and the length of edge
`leftUnit 0`, directed ccw with the tile on its left). `(k, j) = (gridK, gridJ)` of the hypotenuse's
direction. -/

section TileValue

variable {α θ₀ : ℝ} (hα : Irrational (α / Real.pi)) (T : Tri)

/-- **Step 4, direct copy** (`ccw` angles `α, β, π/2` at vertices `0, 1, 2`; the paper's "direct
copy" is `T.det > 0`, i.e. `leftUnit 0 → leftUnit 1 → leftUnit 2` is the ccw boundary walk). Matches
row3 PROOF.md exactly: `i^j (c·[k=X] − (b − ia)·[k+1=X])`. -/
theorem Tri.flux_gauss_direct (hα : Irrational (α / Real.pi)) (hT : 0 < T.det)
    (hβ : T.angleAt 1 = Real.pi / 2 - α) (hγ : T.angleAt 2 = Real.pi / 2)
    (hgrid : IsGridA α θ₀ (T.leftUnit 0).angle) (X : ℤ) :
    T.flux (gaussWeight α θ₀ X)
      = (Complex.I : ℂ) ^ (gridJ α θ₀ (T.leftUnit 0).angle) *
        ((if gridK α θ₀ (T.leftUnit 0).angle = X then (T.oppLen 2 : ℂ) else 0)
          - (if gridK α θ₀ (T.leftUnit 0).angle + 1 = X then
              ((T.oppLen 1 : ℂ) - (T.oppLen 0 : ℂ) * Complex.I) else 0)) := by
  set k := gridK α θ₀ (T.leftUnit 0).angle with hk_def
  set j := gridJ α θ₀ (T.leftUnit 0).angle with hj_def
  -- The two turn steps, rewritten as grid shifts by `(p,q) = (1,1)` then a further `(0,1)` (net
  -- `(1,2)` from `leftUnit 0`).
  have hturn1 : (T.leftUnit 1).angle
      = ((T.leftUnit 0).angle + (((1 : ℝ) * α + (1 : ℝ) * (Real.pi / 2) : ℝ) : Real.Angle)) := by
    have h := T.leftUnit_turn_of_pos hT 0
    simp only [show (0 : Fin 3) + 1 = 1 from rfl] at h
    have hcoe : ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle)
        = (((1 : ℝ) * α + (1 : ℝ) * (Real.pi / 2) : ℝ) : Real.Angle) := by
      rw [hβ]; congr 1; ring
    rw [h, hcoe]
  have hturn2 : (T.leftUnit 2).angle
      = ((T.leftUnit 0).angle + (((1 : ℝ) * α + (2 : ℝ) * (Real.pi / 2) : ℝ) : Real.Angle)) := by
    have h := T.leftUnit_turn_of_pos hT 1
    simp only [show (1 : Fin 3) + 1 = 2 from rfl] at h
    have hcoe : ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle) = ((Real.pi / 2 : ℝ) : Real.Angle) := by
      rw [hγ]; congr 1; ring
    rw [h, hcoe, hturn1, add_assoc]
    have hcoe2 : (((1 : ℝ) * α + (1 : ℝ) * (Real.pi / 2) : ℝ) : Real.Angle)
        + ((Real.pi / 2 : ℝ) : Real.Angle)
        = (((1 : ℝ) * α + (2 : ℝ) * (Real.pi / 2) : ℝ) : Real.Angle) := by
      rw [← Real.Angle.coe_add]; congr 1; ring
    rw [hcoe2]
  have hgw0 : gaussWeight α θ₀ X (T.leftUnit 0)
      = if k = X then (Complex.I : ℂ) ^ j else 0 := by
    unfold gaussWeight
    unfold gaussWeightA
    rw [dif_pos hgrid]
  have hgw1 : gaussWeight α θ₀ X (T.leftUnit 1)
      = if k + 1 = X then (Complex.I : ℂ) ^ (j + 1) else 0 := by
    unfold gaussWeight
    have hshift := gaussWeightA_shift hα hgrid 1 1 X
    push_cast at hshift
    rw [hturn1, hshift]
    unfold gaussWeightA
    rw [dif_pos hgrid]
    by_cases hX : k = X - 1
    · rw [if_pos hX, if_pos (by omega : k + 1 = X), zpow_add₀ Complex.I_ne_zero]; ring
    · rw [if_neg hX, if_neg (by omega : ¬ k + 1 = X), mul_zero]
  have hgw2 : gaussWeight α θ₀ X (T.leftUnit 2)
      = if k + 1 = X then -(Complex.I : ℂ) ^ j else 0 := by
    unfold gaussWeight
    have hshift := gaussWeightA_shift hα hgrid 1 2 X
    push_cast at hshift
    rw [hturn2, hshift]
    unfold gaussWeightA
    rw [dif_pos hgrid]
    by_cases hX : k = X - 1
    · rw [if_pos hX, if_pos (by omega : k + 1 = X)]
      have : (Complex.I : ℂ) ^ (2 : ℤ) = -1 := by
        rw [show (2:ℤ) = ((2:ℕ):ℤ) by norm_num, zpow_natCast]; simp [Complex.I_sq]
      rw [this]; ring
    · rw [if_neg hX, if_neg (by omega : ¬ k + 1 = X), mul_zero]
  -- Unfold `Tri.flux` over the three edges and substitute.
  have hflux : T.flux (gaussWeight α θ₀ X)
      = (T.oppLen 2 : ℝ) • gaussWeight α θ₀ X (T.leftUnit 0)
        + (T.oppLen 0 : ℝ) • gaussWeight α θ₀ X (T.leftUnit 1)
        + (T.oppLen 1 : ℝ) • gaussWeight α θ₀ X (T.leftUnit 2) := by
    unfold Tri.flux Tri.oppLen
    rw [Fin.sum_univ_three]
    simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (1 : Fin 3) + 1 = 2 from rfl,
      show (2 : Fin 3) + 1 = 0 from rfl, show (0 : Fin 3) + 2 = 2 from rfl,
      show (1 : Fin 3) + 2 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl]
  rw [hflux, hgw0, hgw1, hgw2, Complex.real_smul, Complex.real_smul, Complex.real_smul]
  by_cases h1 : k = X
  · have h2 : ¬ k + 1 = X := by omega
    simp only [if_pos h1, if_neg h2]
    ring
  · by_cases h2 : k + 1 = X
    · simp only [if_neg h1, if_pos h2]
      rw [zpow_add₀ Complex.I_ne_zero]
      simp only [zpow_one]
      ring
    · simp only [if_neg h1, if_neg h2]
      ring

/-- **Step 4, reflected copy** (`ccw` angles `α, π/2, β` at vertices `0, 1, 2`, i.e. the mirror
image: `T.det < 0`, so the ccw boundary walk is `leftUnit 0 → leftUnit 1 → leftUnit 2` reversed in
`Tri.leftUnit_turn_of_neg`'s sense). Matches row3 PROOF.md exactly:
`i^j (c·[k=X] − (b + ia)·[k−1=X])`. -/
theorem Tri.flux_gauss_reflected (hα : Irrational (α / Real.pi)) (hT : T.det < 0)
    (hβ : T.angleAt 1 = Real.pi / 2 - α) (hγ : T.angleAt 2 = Real.pi / 2)
    (hgrid : IsGridA α θ₀ (T.leftUnit 0).angle) (X : ℤ) :
    T.flux (gaussWeight α θ₀ X)
      = (Complex.I : ℂ) ^ (gridJ α θ₀ (T.leftUnit 0).angle) *
        ((if gridK α θ₀ (T.leftUnit 0).angle = X then (T.oppLen 2 : ℂ) else 0)
          - (if gridK α θ₀ (T.leftUnit 0).angle - 1 = X then
              ((T.oppLen 1 : ℂ) + (T.oppLen 0 : ℂ) * Complex.I) else 0)) := by
  set k := gridK α θ₀ (T.leftUnit 0).angle with hk_def
  set j := gridJ α θ₀ (T.leftUnit 0).angle with hj_def
  have hturn1 : (T.leftUnit 1).angle
      = ((T.leftUnit 0).angle + (((-1 : ℝ) * α + (-1 : ℝ) * (Real.pi / 2) : ℝ) : Real.Angle)) := by
    have h := T.leftUnit_turn_of_neg hT 0
    simp only [show (0 : Fin 3) + 1 = 1 from rfl] at h
    rw [hβ] at h
    -- `h : (leftUnit 0).angle = (leftUnit 1).angle + ↑(π − (π/2 − α))`
    have hsub : (T.leftUnit 1).angle
        = (T.leftUnit 0).angle - ((Real.pi - (Real.pi / 2 - α) : ℝ) : Real.Angle) := by
      rw [h]; abel
    have hcoe : -((Real.pi - (Real.pi / 2 - α) : ℝ) : Real.Angle)
        = (((-1 : ℝ) * α + (-1 : ℝ) * (Real.pi / 2) : ℝ) : Real.Angle) := by
      rw [← Real.Angle.coe_neg]; congr 1; ring
    rw [hsub, sub_eq_add_neg, hcoe]
  have hturn2 : (T.leftUnit 2).angle
      = ((T.leftUnit 0).angle + (((-1 : ℝ) * α + (-2 : ℝ) * (Real.pi / 2) : ℝ) : Real.Angle)) := by
    have h := T.leftUnit_turn_of_neg hT 1
    simp only [show (1 : Fin 3) + 1 = 2 from rfl] at h
    rw [hγ] at h
    -- `h : (leftUnit 1).angle = (leftUnit 2).angle + ↑(π − π/2)`
    have hsub : (T.leftUnit 2).angle
        = (T.leftUnit 1).angle - ((Real.pi - Real.pi / 2 : ℝ) : Real.Angle) := by
      rw [h]; abel
    have hcoe : -((Real.pi - Real.pi / 2 : ℝ) : Real.Angle) = ((-(Real.pi / 2) : ℝ) : Real.Angle) := by
      rw [← Real.Angle.coe_neg]; congr 1; ring
    rw [hsub, sub_eq_add_neg, hcoe, hturn1, add_assoc]
    have hcoe2 : (((-1 : ℝ) * α + (-1 : ℝ) * (Real.pi / 2) : ℝ) : Real.Angle)
        + ((-(Real.pi / 2) : ℝ) : Real.Angle)
        = (((-1 : ℝ) * α + (-2 : ℝ) * (Real.pi / 2) : ℝ) : Real.Angle) := by
      rw [← Real.Angle.coe_add]; congr 1; ring
    rw [hcoe2]
  have hgw0 : gaussWeight α θ₀ X (T.leftUnit 0)
      = if k = X then (Complex.I : ℂ) ^ j else 0 := by
    unfold gaussWeight gaussWeightA
    rw [dif_pos hgrid]
  have hgw1 : gaussWeight α θ₀ X (T.leftUnit 1)
      = if k = X + 1 then -(Complex.I : ℂ) ^ (j + 1) else 0 := by
    unfold gaussWeight
    have hshift := gaussWeightA_shift hα hgrid (-1) (-1) X
    push_cast at hshift
    rw [hturn1, hshift]
    unfold gaussWeightA
    rw [dif_pos hgrid]
    by_cases hX : k = X - (-1)
    · rw [if_pos hX, if_pos (by omega : k = X + 1)]
      have hI1 : (Complex.I : ℂ) ^ (-1 : ℤ) = -Complex.I := by
        rw [zpow_neg, zpow_one, Complex.inv_I]
      rw [hI1, zpow_add₀ Complex.I_ne_zero]; simp only [zpow_one]; ring
    · rw [if_neg hX, if_neg (by omega : ¬ k = X + 1), mul_zero]
  have hgw2 : gaussWeight α θ₀ X (T.leftUnit 2)
      = if k = X + 1 then -(Complex.I : ℂ) ^ j else 0 := by
    unfold gaussWeight
    have hshift := gaussWeightA_shift hα hgrid (-1) (-2) X
    push_cast at hshift
    rw [hturn2, hshift]
    unfold gaussWeightA
    rw [dif_pos hgrid]
    by_cases hX : k = X - (-1)
    · rw [if_pos hX, if_pos (by omega : k = X + 1)]
      have hI2 : (Complex.I : ℂ) ^ (-2 : ℤ) = -1 := by
        rw [show (-2:ℤ) = -(2:ℤ) by ring, zpow_neg,
          show (2:ℤ) = ((2:ℕ):ℤ) by norm_num, zpow_natCast, Complex.I_sq]
        norm_num
      rw [hI2]; ring
    · rw [if_neg hX, if_neg (by omega : ¬ k = X + 1), mul_zero]
  have hflux : T.flux (gaussWeight α θ₀ X)
      = (T.oppLen 2 : ℝ) • gaussWeight α θ₀ X (T.leftUnit 0)
        + (T.oppLen 0 : ℝ) • gaussWeight α θ₀ X (T.leftUnit 1)
        + (T.oppLen 1 : ℝ) • gaussWeight α θ₀ X (T.leftUnit 2) := by
    unfold Tri.flux Tri.oppLen
    rw [Fin.sum_univ_three]
    simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (1 : Fin 3) + 1 = 2 from rfl,
      show (2 : Fin 3) + 1 = 0 from rfl, show (0 : Fin 3) + 2 = 2 from rfl,
      show (1 : Fin 3) + 2 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl]
  rw [hflux, hgw0, hgw1, hgw2, Complex.real_smul, Complex.real_smul, Complex.real_smul]
  by_cases h1 : k = X
  · have h2 : ¬ k = X + 1 := by omega
    have h3 : ¬ k - 1 = X := by omega
    simp only [if_pos h1, if_neg h2, if_neg h3]
    ring
  · by_cases h2 : k = X + 1
    · have h3 : k - 1 = X := by omega
      simp only [if_neg h1, if_pos h2, if_pos h3]
      rw [zpow_add₀ Complex.I_ne_zero]
      simp only [zpow_one]
      ring
    · have h3 : ¬ k - 1 = X := by omega
      simp only [if_neg h1, if_neg h2, if_neg h3]
      ring

end TileValue

end Erdos634.Geometry.Row3

#print axioms Erdos634.Geometry.Row3.gaussWeightA_shift
#print axioms Erdos634.Geometry.Row3.Tri.flux_gauss_direct
#print axioms Erdos634.Geometry.Row3.Tri.flux_gauss_reflected
