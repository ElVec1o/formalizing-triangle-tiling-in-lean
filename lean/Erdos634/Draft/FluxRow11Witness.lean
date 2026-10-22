-- Draft/FluxRow11Witness.lean — NON-VACUITY WITNESS for `Row11.chi_identities` and
-- `Rationality.beeson_thm1` (Draft/FluxRow11.lean) on the REAL 44-tiling, with the target side
-- evaluated: `K = −2`, `M = 6` — the values of `check_flux_numeric.out` and EVIDENCE's control.
-- Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.Draft.FluxRow11
import Erdos634.Draft.FluxGridWitness

open scoped Classical

namespace Erdos634.Draft.FluxRow11Witness

open Erdos634.Geometry Erdos634.Tiling44Bridge Erdos634.Draft.FluxGridWitness

/-- The relabelling `0 ↦ 2, 1 ↦ 0, 2 ↦ 1` (model vertex 2 carries α, 0 carries β, 1 carries γ). -/
def τ : Equiv.Perm (Fin 3) := (finRotate 3).symm

theorem τ0 : τ 0 = 2 := by decide
theorem τ1 : τ 1 = 0 := by decide
theorem τ2 : τ 2 = 1 := by decide

theorem γ44_eq' : M44.angleAt 1 = 2 * α44 + β44 := by
  have h := γ44_eq
  have hr := three_α_two_β
  rw [h]; unfold θ44; push_cast; linarith

/-- **The model of the 44-tiling is a `3α + 2β = π` tile with `(a, b, c) = (16, 24, 32)`.** -/
theorem data44 : M44.ThreeAlphaData α44 β44 16 24 32 := by
  refine ⟨τ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [τ0]; rfl
  · rw [τ0]; exact m_opp.2.2
  · rw [τ1]; rfl
  · rw [τ1]; exact m_opp.1
  · rw [τ2]; exact γ44_eq'
  · rw [τ2]; exact m_opp.2.1

/-- **Rows 11/12 step C on the real 44-tiling, evaluated: `K = −2`, `M = 6`.** -/
theorem chi_identities_44 : ∃ K M : ℤ, K = -2 ∧ M = 6 ∧
    (2 : ℤ) ∣ K - Tiling44.tiles.length ∧ (2 : ℤ) ∣ M - Tiling44.tiles.length ∧
    dissection.target.flux (chiPlus α44 α44_irr).weight = (K : ℝ) * (32 + 24 - 16) ∧
    dissection.target.flux (chiMinus α44 α44_irr).weight = (M : ℝ) * (16 + 24 + 32) := by
  obtain ⟨K, M, hK2, hM2, -, -, hK, hM⟩ :=
    Row11.chi_identities dissection α44_irr three_α_two_β data44
  have ep : dissection.target.flux (chiPlus α44 α44_irr).weight = -80 := target_flux_plus
  have em : dissection.target.flux (chiMinus α44 α44_irr).weight = 432 := target_flux_minus
  refine ⟨K, M, ?_, ?_, hK2, hM2, hK, hM⟩
  · rw [ep] at hK
    have : (K : ℝ) = -2 := by linarith
    exact_mod_cast this
  · rw [em] at hM
    have : (M : ℝ) = 6 := by linarith
    exact_mod_cast this

end Erdos634.Draft.FluxRow11Witness

#print axioms Erdos634.Draft.FluxRow11Witness.chi_identities_44
