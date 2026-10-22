-- Draft/FluxCRow12Witness.lean — NON-VACUITY WITNESS for `Row12.flux_identities`, `Row12.ratio`,
-- `Row12.rational`, `Row12.rational_paper` (Draft/FluxCRow12.lean) on the REAL 44- and 99-tilings.
-- Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- Hypotheses exhibited: `α44 ∉ ℚπ` (`FluxGridWitness.α44_irr`, Niven via `BaseBetaE1`),
-- `3α + 2β = π` (`three_α_two_β`, from the cosines), the models are `3α + 2β = π` tiles
-- (`FluxRow11Witness.data44`: `(16,24,32)`; `FluxCWitness99.data99`: `(32,48,64)`), the targets have
-- angles `(β, β, 3α)` (`t_angle0/1/2`, `t99_angle0/1/2`).  Evaluated conclusions:
-- `(K, M) = (−2, 6)` at `N = 44` and `(−3, 9)` at `N = 99`, `a/c = 1/2 = (M+K)/(M−K)` in both — the
-- values of ROW11_RATIONALITY.md §3.6 step 5 (review controls): a REPRODUCTION, now kernel-checked
-- through the general theorem.  `rational_paper` is witnessed on the 44-tiling with its model
-- relabelled (`SssCongruent.permTri`) so that vertices `0, 1` carry `α, β`.
import Erdos634.Draft.FluxCRow12
import Erdos634.Draft.FluxRow11Witness
import Erdos634.Draft.FluxCWitness99

open scoped Classical

namespace Erdos634.Draft.FluxCRow12Witness

open Erdos634.Geometry Erdos634.Draft.FluxGridWitness

/-- **R12 on the real 44-tiling: `K = −2`, `M = 6`, `a/c = 16/32 = (M+K)/(M−K)`.** -/
theorem R12_44 : ∃ K M : ℤ, K = -2 ∧ M = 6 ∧ (2 : ℤ) ∣ K - 44 ∧ (2 : ℤ) ∣ M - 44 ∧
    (16 : ℝ) / 32 = ((M : ℝ) + K) / ((M : ℝ) - K) := by
  obtain ⟨K, M, hK2, hM2, -, -, -, hK, hM, -, -, hs⟩ :=
    Row12.ratio Erdos634.Tiling44Bridge.dissection α44_irr three_α_two_β
      Erdos634.Draft.FluxRow11Witness.data44 t_angle0 t_angle1 t_angle2
  rw [Erdos634.Tiling44Bridge.tiles_length_eq_44] at hK2 hM2
  change (K : ℝ) * (32 + 24 - 16) = Erdos634.Tiling44Bridge.targetTri.oppLen 2
    - 2 * Erdos634.Tiling44Bridge.targetTri.oppLen 0 at hK
  change (M : ℝ) * (16 + 24 + 32) = Erdos634.Tiling44Bridge.targetTri.oppLen 2
    + 2 * Erdos634.Tiling44Bridge.targetTri.oppLen 0 at hM
  rw [t_opp.2.2, t_opp.1] at hK hM
  have eK : (K : ℝ) = -2 := by linarith
  have eM : (M : ℝ) = 6 := by linarith
  exact ⟨K, M, by exact_mod_cast eK, by exact_mod_cast eM, by exact_mod_cast hK2,
    by exact_mod_cast hM2, hs⟩

/-- **R12 on the real 99-tiling: `K = −3`, `M = 9`, `a/c = 32/64 = (M+K)/(M−K)`.** -/
theorem R12_99 : ∃ K M : ℤ, K = -3 ∧ M = 9 ∧ (2 : ℤ) ∣ K - 99 ∧ (2 : ℤ) ∣ M - 99 ∧
    (32 : ℝ) / 64 = ((M : ℝ) + K) / ((M : ℝ) - K) := by
  obtain ⟨K, M, hK2, hM2, -, -, -, hK, hM, -, -, hs⟩ :=
    Row12.ratio Erdos634.Tiling99Bridge.dissection α44_irr three_α_two_β
      Erdos634.Draft.FluxCWitness99.data99 Erdos634.Draft.FluxCWitness99.t99_angle0
      Erdos634.Draft.FluxCWitness99.t99_angle1 Erdos634.Draft.FluxCWitness99.t99_angle2
  rw [Erdos634.Tiling99Bridge.tiles_length_eq_99] at hK2 hM2
  change (K : ℝ) * (64 + 48 - 32) = Erdos634.Tiling99Bridge.targetTri.oppLen 2
    - 2 * Erdos634.Tiling99Bridge.targetTri.oppLen 0 at hK
  change (M : ℝ) * (32 + 48 + 64) = Erdos634.Tiling99Bridge.targetTri.oppLen 2
    + 2 * Erdos634.Tiling99Bridge.targetTri.oppLen 0 at hM
  rw [Erdos634.Draft.FluxCWitness99.t99_opp.2.2, Erdos634.Draft.FluxCWitness99.t99_opp.1] at hK hM
  have eK : (K : ℝ) = -3 := by linarith
  have eM : (M : ℝ) = 9 := by linarith
  exact ⟨K, M, by exact_mod_cast eK, by exact_mod_cast eM, by exact_mod_cast hK2,
    by exact_mod_cast hM2, hs⟩

/-- **R12, rationality form, on the real 44-tiling.** -/
theorem R12_rational_44 : ∃ r : ℚ, (16 : ℝ) = (r : ℝ) * 32 :=
  Row12.rational Erdos634.Tiling44Bridge.dissection α44_irr three_α_two_β
    Erdos634.Draft.FluxRow11Witness.data44 t_angle0 t_angle1

/-! ## `rational_paper` on a relabelled 44-tiling -/

/-- The 44-model relabelled `0 ↦ 2, 1 ↦ 0, 2 ↦ 1`: vertex `0` carries `α`, vertex `1` carries `β`. -/
noncomputable def M44' : Tri := Erdos634.SssCongruent.permTri M44 Erdos634.Draft.FluxRow11Witness.τ

/-- The 44-tiling with the relabelled model. -/
noncomputable def D44' : CongruentDissection Tiling44.tiles.length where
  toDissection := Erdos634.Tiling44Bridge.dissection.toDissection
  model := M44'
  tiles_congruent := fun i => (Erdos634.Tiling44Bridge.dissection.tiles_congruent i).trans
    (Erdos634.SssCongruent.congruent_permTri M44 Erdos634.Draft.FluxRow11Witness.τ).symm

theorem M44'_pts (k : Fin 3) : M44'.pts k = M44.pts (Erdos634.Draft.FluxRow11Witness.τ k) := rfl

theorem M44'_angle0 : M44'.angleAt 0 = α44 := by
  unfold Tri.angleAt
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl, M44'_pts,
    Erdos634.Draft.FluxRow11Witness.τ0, Erdos634.Draft.FluxRow11Witness.τ1,
    Erdos634.Draft.FluxRow11Witness.τ2]
  rfl

theorem M44'_angle1 : M44'.angleAt 1 = β44 := by
  unfold Tri.angleAt
  simp only [show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl, M44'_pts,
    Erdos634.Draft.FluxRow11Witness.τ0, Erdos634.Draft.FluxRow11Witness.τ1,
    Erdos634.Draft.FluxRow11Witness.τ2]
  show cornerAngle (M44.pts 1) (M44.pts 0) (M44.pts 2) = _
  rfl

/-- **`row12_rational` (ROW11_RATIONALITY.md item 9 target statement) on a real tiling.** -/
theorem R12_rational_paper_44 : ∃ r : ℚ, D44'.model.oppLen 0 = (r : ℝ) * D44'.model.oppLen 2 :=
  Row12.rational_paper D44' α44 β44 three_α_two_β α44_irr ⟨M44'_angle0, M44'_angle1⟩
    ⟨t_angle0, t_angle1⟩

end Erdos634.Draft.FluxCRow12Witness

#print axioms Erdos634.Draft.FluxCRow12Witness.R12_44
#print axioms Erdos634.Draft.FluxCRow12Witness.R12_99
#print axioms Erdos634.Draft.FluxCRow12Witness.R12_rational_44
#print axioms Erdos634.Draft.FluxCRow12Witness.R12_rational_paper_44
