-- Draft/FluxGRow3Weight.lean — row 3 (AUDIT_ROWS scope), the Gaussian/order-4 grid weight itself.
-- Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).  Source: (private working notes, not included) ("row3" below), §2
-- Proposition RP, Steps 2-3 (grid uniqueness, the weight `f_X`, and its oddness).
--
-- Formalization debt on an already paper-level-PROVED result (row3 PROOF.md P7: Lemma A,
-- Proposition RP, Corollary all PROVED, Rule 0, two independent hostile reviews HOLD). This file is
-- NOT progress on the three /goal outcomes.
--
-- SCOPE (read this before trusting any claim below).
--
-- This file builds, unconditionally and with non-vacuous witnesses:
--   (A) `IsGridA`, `gridK`, `gridJ` : the (k, j mod 4) grid coordinates of a `Real.Angle`, lifting
--       `Row3.grid_unique` (FluxGRow3.lean, already VERIFIED) from the raw-ℝ statement it proves to
--       the `Real.Angle` level the geometry actually uses (`Dir.angle : Dir → Real.Angle`).
--   (B) `gaussWeight` : `Dir → ℂ`, the paper's own `f_X(θ) = [k(θ)=X]·i^{j(θ)}` (row3 Step 2), as a
--       genuine function of a direction, and `gaussWeight_odd`, its oddness
--       `gaussWeight (Dir.neg d) = - gaussWeight d` — **exactly** the hypothesis `flux_cancel`
--       (`FluxCancel.lean`, already VERIFIED, `f : Dir → E` for any `AddCommGroup E`/`Module ℝ E`,
--       and `ℂ` is such an `E` with no new instance needed) demands. Instantiating `flux_cancel`
--       with `gaussWeight` is therefore now literally one `exact` away (see `gaussWeight_flux_cancel`
--       below) — this is row3 PROOF.md §6 item 1's *weight*, closed; item 1's other half (routing an
--       actual `CongruentDissection`'s boundary/tile edges through it, i.e. Step 4's tile-value
--       computation on real tile data) is NOT attempted, because it needs item 3 (the corner fact
--       for a right tile, not built anywhere in the corpus) to even name which `CongruentDissection`
--       this applies to.
--
-- This file does NOT build:
--   - Lemma A, Proposition RP, or the Corollary (unchanged from FluxGRow3.lean: all three OPEN);
--   - row3 PROOF.md §6 item 3 (the corner fact / Lemma A's case split);
--   - item 4 (area, N = 2λ²);
--   - item 5 (the Laurent-polynomial cancellation down to (★)). Step 4's tile-value formula in
--     particular needs a *dissection*'s actual tiles (which edge is the hypotenuse, which two are
--     legs, and their chirality) to state as a theorem about `Tri.flux`; with no
--     `CongruentDissection` instance built for the base-β/right-tile target (item 3's dependency),
--     there is no non-vacuous carrier to state it about, so — per this project's Rule
--     (vacuous-conditional-check) — it is left undone here rather than stated over an unsatisfiable
--     or unmotivated hypothesis set.
--
-- So after this file: Lemma A, Proposition RP and the Corollary are still OPEN in Lean. What moves is
-- that `flux_cancel`'s antecedent (an odd `Dir → E` weight) now has the paper's *actual* Gaussian
-- weight as a witness, not just "ℂ qualifies as a `Module ℝ E`" (which FluxGRow3.lean already noted
-- and which is not by itself a constructed weight).
--
-- Rediscovery check (Rule 0.5): grepped `lean/Erdos634` for `IsGridA`, `gridK`, `gridJ`,
-- `gaussWeight`, `angle_eq_iff_two_pi_dvd_sub` — no hits outside this file (the last is a Mathlib
-- lemma name, used here, not reimplemented). `Row3.grid_unique` (FluxGRow3.lean) is reused, not
-- reproved: it is exactly the ℝ-level uniqueness fact this file lifts to `Real.Angle`.
import Erdos634.Draft.FluxGRow3
import Erdos634.Draft.FluxTurn
import Erdos634.Draft.FluxCancel

open scoped Classical

namespace Erdos634.Geometry.Row3

open Real

/-! ## (A) Grid coordinates of a `Real.Angle`

`IsGridA α θ₀ θ` says `θ` lies in the grid `θ₀ + ℤα + ℤ(π/2)` of row3 PROOF.md Step 2, as a
`Real.Angle` (i.e. mod `2π`, matching how directions are actually compared in the geometry). -/

/-- **Grid membership**, `Real.Angle` level: `θ = θ₀ + kα + jπ/2` for some integers `k, j`, read mod
`2π` (the coercion `ℝ → Real.Angle`). This is row3 PROOF.md's `G = θ₀ + ℤα + ℤ(π/2) (mod 2π)`. -/
def IsGridA (α θ₀ : ℝ) (θ : Real.Angle) : Prop :=
  ∃ k j : ℤ, θ = ((θ₀ + (k : ℝ) * α + (j : ℝ) * (Real.pi / 2) : ℝ) : Real.Angle)

/-- **Grid uniqueness, `Real.Angle` level.** If `α / π` is irrational, the pair `(k, j mod 4)`
witnessing `IsGridA` is unique. This lifts `Row3.grid_unique` (FluxGRow3.lean) from the raw-ℝ
statement with an explicit `2π`-multiple to the `Real.Angle` equation, via
`Real.Angle.angle_eq_iff_two_pi_dvd_sub`. -/
theorem isGridA_unique {α θ₀ : ℝ} (hα : Irrational (α / Real.pi)) {θ : Real.Angle} {k j k' j' : ℤ}
    (h : θ = ((θ₀ + (k : ℝ) * α + (j : ℝ) * (Real.pi / 2) : ℝ) : Real.Angle))
    (h' : θ = ((θ₀ + (k' : ℝ) * α + (j' : ℝ) * (Real.pi / 2) : ℝ) : Real.Angle)) :
    k = k' ∧ (4 : ℤ) ∣ (j - j') := by
  have heq : ((θ₀ + (k : ℝ) * α + (j : ℝ) * (Real.pi / 2) : ℝ) : Real.Angle)
           = ((θ₀ + (k' : ℝ) * α + (j' : ℝ) * (Real.pi / 2) : ℝ) : Real.Angle) := h ▸ h'
  rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub] at heq
  obtain ⟨m, hm⟩ := heq
  -- `hm : (θ₀ + kα + jπ/2) - (θ₀ + k'α + j'π/2) = 2π m`
  have hm' : (k : ℝ) * α + (j : ℝ) * (Real.pi / 2)
           = (k' : ℝ) * α + (j' : ℝ) * (Real.pi / 2) + (m : ℝ) * (2 * Real.pi) := by
    linarith [hm]
  exact Row3.grid_unique hα k k' j j' m hm'

/-- **`k`-coordinate**, well defined by `isGridA_unique` when `IsGridA` holds; junk value `0`
off the grid. -/
noncomputable def gridK (α θ₀ : ℝ) (θ : Real.Angle) : ℤ :=
  if h : IsGridA α θ₀ θ then h.choose else 0

/-- **`j`-coordinate (mod 4)**, well defined mod `4` by `isGridA_unique`; junk value `0` off the
grid. -/
noncomputable def gridJ (α θ₀ : ℝ) (θ : Real.Angle) : ℤ :=
  if h : IsGridA α θ₀ θ then h.choose_spec.choose else 0

theorem gridK_gridJ_spec {α θ₀ : ℝ} {θ : Real.Angle} (h : IsGridA α θ₀ θ) :
    θ = ((θ₀ + (gridK α θ₀ θ : ℝ) * α + (gridJ α θ₀ θ : ℝ) * (Real.pi / 2) : ℝ) : Real.Angle) := by
  unfold gridK gridJ
  rw [dif_pos h, dif_pos h]
  exact h.choose_spec.choose_spec

/-- `gridK`/`gridJ` agree with **any** valid witness `(k, j)`, not just the chosen one. -/
theorem gridK_eq_of_spec {α θ₀ : ℝ} (hα : Irrational (α / Real.pi)) {θ : Real.Angle} {k j : ℤ}
    (h : θ = ((θ₀ + (k : ℝ) * α + (j : ℝ) * (Real.pi / 2) : ℝ) : Real.Angle)) :
    gridK α θ₀ θ = k :=
  ((isGridA_unique hα (gridK_gridJ_spec ⟨k, j, h⟩) h).1)

theorem gridJ_eq_of_spec {α θ₀ : ℝ} (hα : Irrational (α / Real.pi)) {θ : Real.Angle} {k j : ℤ}
    (h : θ = ((θ₀ + (k : ℝ) * α + (j : ℝ) * (Real.pi / 2) : ℝ) : Real.Angle)) :
    (4 : ℤ) ∣ (gridJ α θ₀ θ - j) :=
  ((isGridA_unique hα (gridK_gridJ_spec ⟨k, j, h⟩) h).2)

/-! ## Shifting by `π`: `IsGridA` is `π`-invariant, `k` is unchanged, `j` shifts by `2` mod `4`

This is exactly row3 PROOF.md Step 2's "adding `π` keeps `k` and adds `2` to `j`", the fact that
makes `f_X` odd. -/

theorem isGridA_add_pi {α θ₀ : ℝ} {θ : Real.Angle} (h : IsGridA α θ₀ θ) :
    IsGridA α θ₀ (θ + ((Real.pi : ℝ) : Real.Angle)) := by
  obtain ⟨k, j, hk⟩ := h
  refine ⟨k, j + 2, ?_⟩
  rw [hk, ← Real.Angle.coe_add]
  congr 1
  push_cast
  ring

theorem isGridA_of_add_pi {α θ₀ : ℝ} {θ : Real.Angle}
    (h : IsGridA α θ₀ (θ + ((Real.pi : ℝ) : Real.Angle))) : IsGridA α θ₀ θ := by
  have h2 := isGridA_add_pi h
  have hcancel : θ + ((Real.pi : ℝ) : Real.Angle) + ((Real.pi : ℝ) : Real.Angle) = θ := by
    rw [add_assoc, ← Real.Angle.coe_add, show (Real.pi + Real.pi : ℝ) = 2 * Real.pi by ring,
      Real.Angle.coe_two_pi, add_zero]
  rwa [hcancel] at h2

/-- `IsGridA` is invariant under shifting by `π`. -/
theorem isGridA_add_pi_iff {α θ₀ : ℝ} {θ : Real.Angle} :
    IsGridA α θ₀ (θ + ((Real.pi : ℝ) : Real.Angle)) ↔ IsGridA α θ₀ θ :=
  ⟨isGridA_of_add_pi, isGridA_add_pi⟩

theorem gridK_add_pi {α θ₀ : ℝ} (hα : Irrational (α / Real.pi)) {θ : Real.Angle}
    (h : IsGridA α θ₀ θ) :
    gridK α θ₀ (θ + ((Real.pi : ℝ) : Real.Angle)) = gridK α θ₀ θ := by
  obtain ⟨k, j, hk⟩ := h
  have hspec : θ + ((Real.pi : ℝ) : Real.Angle)
      = ((θ₀ + (k : ℝ) * α + ((j + 2 : ℤ) : ℝ) * (Real.pi / 2) : ℝ) : Real.Angle) := by
    rw [hk, ← Real.Angle.coe_add]; congr 1; push_cast; ring
  rw [gridK_eq_of_spec hα hspec, gridK_eq_of_spec hα hk]

theorem gridJ_add_pi {α θ₀ : ℝ} (hα : Irrational (α / Real.pi)) {θ : Real.Angle}
    (h : IsGridA α θ₀ θ) :
    (4 : ℤ) ∣ (gridJ α θ₀ (θ + ((Real.pi : ℝ) : Real.Angle)) - (gridJ α θ₀ θ + 2)) := by
  obtain ⟨k, j, hk⟩ := h
  have hspec : θ + ((Real.pi : ℝ) : Real.Angle)
      = ((θ₀ + (k : ℝ) * α + ((j + 2 : ℤ) : ℝ) * (Real.pi / 2) : ℝ) : Real.Angle) := by
    rw [hk, ← Real.Angle.coe_add]; congr 1; push_cast; ring
  have hd1 : (4 : ℤ) ∣ (gridJ α θ₀ (θ + ((Real.pi : ℝ) : Real.Angle)) - (j + 2)) :=
    gridJ_eq_of_spec hα hspec
  have hd2 : (4 : ℤ) ∣ (gridJ α θ₀ θ - j) := gridJ_eq_of_spec hα hk
  have : gridJ α θ₀ (θ + ((Real.pi : ℝ) : Real.Angle)) - (gridJ α θ₀ θ + 2)
       = (gridJ α θ₀ (θ + ((Real.pi : ℝ) : Real.Angle)) - (j + 2)) - (gridJ α θ₀ θ - j) := by ring
  rw [this]
  exact dvd_sub hd1 hd2

/-! ## (B) The Gaussian weight `gaussWeight` and its oddness -/

/-- **`i` to an integer power that only depends on the exponent mod `4`.** `Complex.I` has order
`4`, so `4 ∣ m - n → I^m = I^n`. -/
theorem Complex.I_zpow_eq_of_mod4 {m n : ℤ} (h : (4 : ℤ) ∣ (m - n)) :
    (Complex.I : ℂ) ^ m = Complex.I ^ n := by
  obtain ⟨t, ht⟩ := h
  have : m = n + 4 * t := by omega
  rw [this, zpow_add₀ Complex.I_ne_zero, zpow_mul,
    show ((4:ℤ)) = ((4:ℕ):ℤ) by norm_num, zpow_natCast, Complex.I_pow_four, one_zpow, mul_one]

/-- **The paper's `f_X`** (row3 PROOF.md Step 2): `f_X(θ) = [k(θ) = X]·i^{j(θ)}` on the grid,
`0` off it, as a function of a `Real.Angle`. -/
noncomputable def gaussWeightA (α θ₀ : ℝ) (X : ℤ) (θ : Real.Angle) : ℂ :=
  if h : IsGridA α θ₀ θ then (if gridK α θ₀ θ = X then (Complex.I : ℂ) ^ gridJ α θ₀ θ else 0) else 0

/-- **`gaussWeightA` is odd**: `f_X(θ + π) = - f_X(θ)`. This is row3 PROOF.md Step 2's "adding `π`
keeps `k` and adds `2` to `j`", combined with `I^{j+2} = -I^j`. -/
theorem gaussWeightA_odd {α θ₀ : ℝ} (hα : Irrational (α / Real.pi)) (X : ℤ) (θ : Real.Angle) :
    gaussWeightA α θ₀ X (θ + ((Real.pi : ℝ) : Real.Angle)) = - gaussWeightA α θ₀ X θ := by
  unfold gaussWeightA
  by_cases h : IsGridA α θ₀ θ
  · have h2 : IsGridA α θ₀ (θ + ((Real.pi : ℝ) : Real.Angle)) := isGridA_add_pi h
    rw [dif_pos h, dif_pos h2, gridK_add_pi hα h]
    by_cases hX : gridK α θ₀ θ = X
    · rw [if_pos hX, if_pos hX]
      have hj := gridJ_add_pi hα h
      rw [Complex.I_zpow_eq_of_mod4 hj, zpow_add₀ Complex.I_ne_zero]
      norm_cast
      rw [Complex.I_sq]
      ring
    · rw [if_neg hX, if_neg hX, neg_zero]
  · have h2 : ¬ IsGridA α θ₀ (θ + ((Real.pi : ℝ) : Real.Angle)) := fun hc => h (isGridA_of_add_pi hc)
    rw [dif_neg h, dif_neg h2, neg_zero]

/-- **The Gaussian weight on `Dir`**: `gaussWeight α θ₀ X d = gaussWeightA α θ₀ X d.angle`, the form
`Tri.flux`/`flux_cancel` actually consume. -/
noncomputable def gaussWeight (α θ₀ : ℝ) (X : ℤ) (d : Dir) : ℂ :=
  gaussWeightA α θ₀ X d.angle

/-- **`gaussWeight` is odd** — exactly `flux_cancel`'s hypothesis, for the Gaussian weight itself
(not merely for "some `Dir → E`", `E` an arbitrary `ℝ`-module, as FluxGRow3.lean's header already
noted was available with no new instance). -/
theorem gaussWeight_odd {α θ₀ : ℝ} (hα : Irrational (α / Real.pi)) (X : ℤ) (d : Dir) :
    gaussWeight α θ₀ X (Dir.neg d) = - gaussWeight α θ₀ X d := by
  unfold gaussWeight
  rw [Dir.angle_neg]
  exact gaussWeightA_odd hα X d.angle

/-- **Item 1, weight half, closed**: `flux_cancel` instantiated at the actual Gaussian weight, for
any real dissection `D` and any grid degree `X`. Row3 PROOF.md Step 3 ("`Σ_tiles C_X(t) = Φ_X(∂ABC)`")
is now this theorem's conclusion, for the paper's own `f_X`, not a generic odd weight. -/
theorem gaussWeight_flux_cancel {α θ₀ : ℝ} (hα : Irrational (α / Real.pi)) (X : ℤ)
    {N : ℕ} (D : Dissection N) :
    ∑ i, (D.tile i).flux (gaussWeight α θ₀ X) = D.target.flux (gaussWeight α θ₀ X) :=
  D.flux_cancel (gaussWeight α θ₀ X) (gaussWeight_odd hα X)

/-! ## Non-vacuity witnesses -/

/-- `α = √2·π` has `α/π` irrational (reused witness, `Row3.grid_unique_witness`'s hypothesis). -/
theorem gaussWeight_witness_alpha : Irrational ((Real.sqrt 2 * Real.pi) / Real.pi) :=
  Row3.grid_unique_witness

/-- **Non-vacuity, `IsGridA`**: `θ₀` itself is always on its own grid (`k = j = 0`). -/
theorem isGridA_self (α θ₀ : ℝ) : IsGridA α θ₀ (θ₀ : Real.Angle) := by
  refine ⟨0, 0, ?_⟩
  norm_num

/-- **Non-vacuity, `gaussWeight`**: at the anchor direction itself (`θ = θ₀`, `k = j = 0`),
`gaussWeight α θ₀ 0` evaluates to `1`, not junk. Concretely instantiated at the witness angle
`α = √2 π`, `θ₀ = 0`. -/
theorem gaussWeightA_witness :
    gaussWeightA (Real.sqrt 2 * Real.pi) 0 0 (0 : Real.Angle) = 1 := by
  have hg : IsGridA (Real.sqrt 2 * Real.pi) 0 (0 : Real.Angle) := by
    refine ⟨0, 0, ?_⟩; norm_num
  have hα := gaussWeight_witness_alpha
  unfold gaussWeightA
  rw [dif_pos hg]
  have hk : gridK (Real.sqrt 2 * Real.pi) 0 (0 : Real.Angle) = 0 :=
    gridK_eq_of_spec hα (k := 0) (j := 0) (by norm_num)
  have hj : (4:ℤ) ∣ (gridJ (Real.sqrt 2 * Real.pi) 0 (0 : Real.Angle) - 0) :=
    gridJ_eq_of_spec hα (k := 0) (j := 0) (by norm_num)
  rw [if_pos hk]
  obtain ⟨t, ht⟩ := hj
  have : gridJ (Real.sqrt 2 * Real.pi) 0 (0 : Real.Angle) = 4 * t := by omega
  rw [this, zpow_mul, show ((4:ℤ)) = ((4:ℕ):ℤ) by norm_num, zpow_natCast, Complex.I_pow_four,
    one_zpow]

/-- **Non-vacuity, oddness at a concrete point**: `gaussWeight` really does flip sign, checked at
the witness angle and at `X = 0`, `θ = θ₀ = 0` (so `Dir.angle d = 0` and the reversed direction has
angle `π`). Uses `gaussWeightA_witness` for the `θ` side and computes the `θ+π` side directly:
`k = 0`, `j = 2`, so `I² = -1`. -/
theorem gaussWeightA_odd_witness :
    gaussWeightA (Real.sqrt 2 * Real.pi) 0 0 ((Real.pi : ℝ) : Real.Angle) = -1 := by
  have hα := gaussWeight_witness_alpha
  have h0 : gaussWeightA (Real.sqrt 2 * Real.pi) 0 0 ((0:Real.Angle) + ((Real.pi:ℝ):Real.Angle))
      = - gaussWeightA (Real.sqrt 2 * Real.pi) 0 0 (0 : Real.Angle) :=
    gaussWeightA_odd hα 0 0
  rwa [zero_add, gaussWeightA_witness] at h0

end Erdos634.Geometry.Row3

#print axioms Erdos634.Geometry.Row3.isGridA_unique
#print axioms Erdos634.Geometry.Row3.gridK_eq_of_spec
#print axioms Erdos634.Geometry.Row3.gridJ_eq_of_spec
#print axioms Erdos634.Geometry.Row3.isGridA_add_pi_iff
#print axioms Erdos634.Geometry.Row3.gridK_add_pi
#print axioms Erdos634.Geometry.Row3.gridJ_add_pi
#print axioms Erdos634.Geometry.Row3.Complex.I_zpow_eq_of_mod4
#print axioms Erdos634.Geometry.Row3.gaussWeightA_odd
#print axioms Erdos634.Geometry.Row3.gaussWeight_odd
#print axioms Erdos634.Geometry.Row3.gaussWeight_flux_cancel
#print axioms Erdos634.Geometry.Row3.gaussWeightA_witness
#print axioms Erdos634.Geometry.Row3.gaussWeightA_odd_witness
