-- Draft/F1Bridge.lean — geometric bridge: F1Shape → F1Data (B-2 of prop:F1free).
--
-- `f1_data_of_branch1/2` and `f1_data_of_f1shape`:
-- from model `TwoPiThreeData α a b c` and one branch of `F1Shape D α`,
-- construct `F1Data` on the target with an explicit positive scale μ.
--
-- Method: law of sines (`Tri.lawSin`) + model side ratios.
-- Pattern mirrors `Draft/ThmIsoShBridge.lean`'s `base_alpha_of_isoTP`.
--
-- Key sine identity: sin(2π/3 − α) = sin(π/3 − α) + sin α.
-- ZERO sorry.  Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).

import Erdos634.Draft.ThmIsoShBridge
import Erdos634.Draft.FluxE2Pi3Row7

open scoped Classical

namespace Erdos634.Geometry

open Erdos634.Draft.TheoremPConditional
open A1Field (sin_angle_pos)

/-! ## Auxiliary -/

private lemma sin_two_pi3_sub (α : ℝ) :
    Real.sin (2 * Real.pi / 3 - α) = Real.sin (Real.pi / 3 - α) + Real.sin α := by
  have h3 : Real.sin (2 * Real.pi / 3 - α) = Real.sin (Real.pi / 3 + α) := by
    rw [show 2 * Real.pi / 3 - α = Real.pi - (Real.pi / 3 + α) by ring, Real.sin_pi_sub]
  rw [h3, Real.sin_add (Real.pi / 3) α, Real.sin_sub (Real.pi / 3) α]
  simp only [Real.cos_pi_div_three]; ring

lemma twoPiThreeData_swap (T : Tri) {α a b c : ℝ}
    (h : T.TwoPiThreeData α a b c) :
    T.TwoPiThreeData (Real.pi / 3 - α) b a c := by
  obtain ⟨σ, h0a, h0s, h1a, h1s, h2a, h2s⟩ := h
  have sw0 : (σ * Equiv.swap (0 : Fin 3) 1) 0 = σ 1 := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
  have sw1 : (σ * Equiv.swap (0 : Fin 3) 1) 1 = σ 0 := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
  have sw2 : (σ * Equiv.swap (0 : Fin 3) 1) 2 = σ 2 := by
    rw [Equiv.Perm.mul_apply]; congr 1
  exact ⟨σ * Equiv.swap 0 1,
    by rw [sw0, h1a],
    by rw [sw0, h1s],
    by rw [sw1, h0a]; ring,
    by rw [sw1, h0s],
    by rw [sw2, h2a],
    by rw [sw2, h2s]⟩

/-! ## Core bridge: Branch 1 -/

/-- From `TgtAngles D α (π/3) (2π/3−α)` and model `TwoPiThreeData α a b c`,
    construct `F1Data α a b c μ` with explicit μ > 0. -/
theorem f1_data_of_branch1 {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : TgtAngles D α (α + (Real.pi / 3 - α)) (α + 2 * (Real.pi / 3 - α))) :
    ∃ μ > 0, D.target.F1Data α a b c μ := by
  -- Normalise angle expressions
  have htN : TgtAngles D α (Real.pi / 3) (2 * Real.pi / 3 - α) := by
    obtain ⟨σt, h1, h2, h3⟩ := ht
    exact ⟨σt, h1, by linarith, by linarith⟩
  -- Extract all data
  obtain ⟨_, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  obtain ⟨σm, hα0m, ham, hβ1m, hbm, hγ2m, hcm⟩ := hm
  obtain ⟨σ, htα0, htπ31, ht2π3α2⟩ := htN
  -- Positivity
  have hsin_α : 0 < Real.sin α := by
    have := sin_angle_pos D.target (σ 0); rwa [htα0] at this
  have hna : a ≠ 0 := ha0.ne'
  -- Model law of sines: sin α · c = sin(π/3) · a
  have hm02 := D.model.lawSin (σm 0) (σm 2)
  rw [hα0m, hγ2m, ham, hcm] at hm02
  have hm02' : Real.sin α * c = Real.sin (Real.pi / 3) * a := by
    have : Real.sin (2 * Real.pi / 3) = Real.sin (Real.pi / 3) := by
      rw [show (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub]
    linarith [this ▸ hm02]
  -- Model law of sines: sin α · b = sin(π/3−α) · a
  have hm01 := D.model.lawSin (σm 0) (σm 1)
  rw [hα0m, hβ1m, ham, hbm] at hm01
  have hm01' : Real.sin α * b = Real.sin (Real.pi / 3 - α) * a := by linarith
  -- Target law of sines equations
  have ht01 := D.target.lawSin (σ 0) (σ 1); rw [htα0, htπ31] at ht01
  -- ht01 : sin α · oppLen(σ1) = sin(π/3) · oppLen(σ0)
  have ht02 := D.target.lawSin (σ 0) (σ 2); rw [htα0, ht2π3α2] at ht02
  -- ht02 : sin α · oppLen(σ2) = sin(2π/3-α) · oppLen(σ0)
  -- Rewrite sin(2π/3-α) using the sine identity
  have ht02' : Real.sin α * D.target.oppLen (σ 2) =
      (Real.sin (Real.pi / 3 - α) + Real.sin α) * D.target.oppLen (σ 0) := by
    rw [← sin_two_pi3_sub]; exact ht02
  -- Scale μ = oppLen(σ0) / a
  have hoppL0 : 0 < D.target.oppLen (σ 0) := D.target.oppLen_pos (σ 0)
  refine ⟨D.target.oppLen (σ 0) / a, div_pos hoppL0 ha0, div_pos hoppL0 ha0, ?_⟩
  -- Side equalities via mul_left_cancel₀ pattern
  -- (1) oppLen(σ0) = μ·a
  have hside0 : D.target.oppLen (σ 0) = D.target.oppLen (σ 0) / a * a :=
    (div_mul_cancel₀ _ hna).symm
  -- (2) oppLen(σ1) = μ·c  [from: oppLen1·a = oppLen0·c]
  have hkey1 : D.target.oppLen (σ 1) * a = D.target.oppLen (σ 0) * c :=
    mul_left_cancel₀ hsin_α.ne' (by
      have h1 : Real.sin α * (D.target.oppLen (σ 1) * a) =
          Real.sin (Real.pi / 3) * (D.target.oppLen (σ 0) * a) := by
        linear_combination a * ht01
      have h2 : Real.sin α * (D.target.oppLen (σ 0) * c) =
          Real.sin (Real.pi / 3) * (D.target.oppLen (σ 0) * a) := by
        linear_combination D.target.oppLen (σ 0) * hm02'
      linarith)
  have hside1 : D.target.oppLen (σ 1) = D.target.oppLen (σ 0) / a * c := by
    field_simp [hna]; linarith [hkey1]
  -- (3) oppLen(σ2) = μ·(a+b)  [from: oppLen2·a = oppLen0·(a+b)]
  have hkey2 : D.target.oppLen (σ 2) * a = D.target.oppLen (σ 0) * (a + b) :=
    mul_left_cancel₀ hsin_α.ne' (by
      have h1 : Real.sin α * (D.target.oppLen (σ 2) * a) =
          (Real.sin (Real.pi / 3 - α) + Real.sin α) * (D.target.oppLen (σ 0) * a) := by
        linear_combination a * ht02'
      have h2 : Real.sin α * (D.target.oppLen (σ 0) * (a + b)) =
          (Real.sin (Real.pi / 3 - α) + Real.sin α) * (D.target.oppLen (σ 0) * a) := by
        linear_combination D.target.oppLen (σ 0) * hm01'
      linarith)
  have hside2 : D.target.oppLen (σ 2) = D.target.oppLen (σ 0) / a * (a + b) := by
    field_simp [hna]; linarith [hkey2]
  -- Assemble GridTriData
  exact ⟨σ,
    by rw [htα0]; push_cast; ring,
    hside0,
    by rw [htπ31]; push_cast; ring,
    hside1,
    by rw [ht2π3α2]; push_cast; ring,
    hside2⟩

/-! ## Branch 2 bridge (reduces to Branch 1 with α ↔ β) -/

theorem f1_data_of_branch2 {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : TgtAngles D (Real.pi / 3 - α) (α + (Real.pi / 3 - α))
          (2 * α + (Real.pi / 3 - α))) :
    ∃ μ > 0, D.target.F1Data (Real.pi / 3 - α) b a c μ := by
  -- Rewrite ht in the canonical form for f1_data_of_branch1 with α' = π/3-α
  have htβ : TgtAngles D (Real.pi / 3 - α)
      ((Real.pi / 3 - α) + (Real.pi / 3 - (Real.pi / 3 - α)))
      ((Real.pi / 3 - α) + 2 * (Real.pi / 3 - (Real.pi / 3 - α))) := by
    have h1 : (Real.pi / 3 - α) + (Real.pi / 3 - (Real.pi / 3 - α)) =
        α + (Real.pi / 3 - α) := by ring
    have h2 : (Real.pi / 3 - α) + 2 * (Real.pi / 3 - (Real.pi / 3 - α)) =
        2 * α + (Real.pi / 3 - α) := by ring
    rw [h1, h2]; exact ht
  exact f1_data_of_branch1 D (twoPiThreeData_swap D.model hm) htβ

/-! ## Combined bridge -/

theorem f1_data_of_f1shape {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hm : D.model.TwoPiThreeData α a b c) (hF1 : F1Shape D α) :
    (∃ μ > 0, D.target.F1Data α a b c μ) ∨
    (∃ μ > 0, D.target.F1Data (Real.pi / 3 - α) b a c μ) := by
  rcases hF1 with h1 | h2
  · exact Or.inl (f1_data_of_branch1 D hm h1)
  · exact Or.inr (f1_data_of_branch2 D hm h2)

#check @f1_data_of_f1shape
#print axioms f1_data_of_f1shape

end Erdos634.Geometry
