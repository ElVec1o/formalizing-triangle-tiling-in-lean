import Erdos634.BADTarget

/-!
# BAD layer L2, step S4: assembly (`BAD.L2`)

Written 2026-10-03.  UNAUDITED.  For a `CongruentDissection` whose model has the angle/side data of
the tile `(ef, f²-e², f²)` (angles `α, β, π-α-β`, `3α+2β = π`, `α/π` irrational) and whose target is
isosceles with base angles `α` (two legs `X`, base `Y`): the target's `(X,Y)` are integers and
`X t² + Y + X t⁻² = Σ_i ± t^{s_i} (p or q)` in `ℤ[T;T⁻¹]` with `N` terms.
Angle data are hypotheses here; `BADAngles.lean` derives them from side lengths.
-/

open LaurentPolynomial

namespace Erdos634.BADL2
open Erdos634.Geometry

noncomputable section

/-- boundary polynomial over `ℤ` with free `(X,Y)`. -/
def Bd (X Y : ℤ) : LaurentPolynomial ℤ := C X * T 2 + C Y + C X * T (-2)

theorem Bdry_eq_Bd (e f w : ℤ) :
    BAD.Bdry e f w = Bd (f ^ 2 * w) ((2 * f ^ 2 - e ^ 2) * w) := rfl

def Qv (X Y : ℝ) : LR := C Y + C X * T 2 + C X * T (-2)

theorem Qv_coeff2 (X Y : ℝ) : Qv X Y 2 = X := by
  simp [Qv, ← single_eq_C_mul_T, Finsupp.single_apply]

theorem Qv_coeff0 (X Y : ℝ) : Qv X Y 0 = Y := by
  simp [Qv, ← single_eq_C_mul_T, Finsupp.single_apply]

theorem mp_Bd (X Y : ℤ) : mp (Bd X Y) = Qv (X : ℝ) (Y : ℝ) := by
  simp only [Bd, Qv, map_add, map_mul, mp_C, mp_T]
  ring

theorem tsum_ofFn {N : ℕ} (e f : ℤ) (g : Fin N → ℤ × ℤ × Bool) :
    mp (BAD.tsum e f (List.ofFn g)) = ∑ i, mp (BAD.term e f (g i)) := by
  unfold BAD.tsum
  rw [List.map_ofFn, List.sum_ofFn, map_sum]
  rfl

/-- model data in the permutation form used by the tile lemma. -/
theorem model_perm {N : ℕ} (D : CongruentDissection N) (e f : ℤ) (α β : ℝ)
    (hmodel : ∃ σ : Equiv.Perm (Fin 3),
      D.model.angleAt (σ 0) = α ∧ D.model.oppLen (σ 0) = (e : ℝ) * f ∧
      D.model.angleAt (σ 1) = β ∧ D.model.oppLen (σ 1) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧
      D.model.angleAt (σ 2) = Real.pi - α - β ∧ D.model.oppLen (σ 2) = (f : ℝ) ^ 2) :
    ∃ ρ : Equiv.Perm (Fin 3), ∀ k, D.model.angleAt k = Ang α β (ρ k)
      ∧ D.model.oppLen k = Lenr e f (ρ k) := by
  obtain ⟨σ, a0, l0, a1, l1, a2, l2⟩ := hmodel
  refine ⟨σ.symm, fun k => ?_⟩
  have hk : k = σ (σ.symm k) := (σ.apply_symm_apply k).symm
  generalize σ.symm k = j at hk
  subst hk
  fin_cases j
  · exact ⟨by simpa [Ang] using a0, by simpa [Lenr] using l0⟩
  · exact ⟨by simpa [Ang] using a1, by simpa [Lenr] using l1⟩
  · exact ⟨by simpa [Ang] using a2, by simpa [Lenr] using l2⟩

theorem L2 {N : ℕ} (D : CongruentDissection N) (e f : ℤ) (α β : ℝ)
    (hα : ¬∃ r : ℚ, α = r * Real.pi) (hβ : 3 * α + 2 * β = Real.pi)
    (hmodel : ∃ σ : Equiv.Perm (Fin 3),
      D.model.angleAt (σ 0) = α ∧ D.model.oppLen (σ 0) = (e : ℝ) * f ∧
      D.model.angleAt (σ 1) = β ∧ D.model.oppLen (σ 1) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧
      D.model.angleAt (σ 2) = Real.pi - α - β ∧ D.model.oppLen (σ 2) = (f : ℝ) ^ 2)
    (X Y : ℝ)
    (htgt : D.target.angleAt 0 = α ∧ D.target.angleAt 1 = α ∧ D.target.oppLen 0 = X ∧
      D.target.oppLen 1 = X ∧ D.target.oppLen 2 = Y) :
    ∃ (X' Y' : ℤ) (l : List (ℤ × ℤ × Bool)), X = X' ∧ Y = Y' ∧ Bd X' Y' = BAD.tsum e f l := by
  obtain ⟨ρ, hρ⟩ := model_perm D e f α β hmodel
  obtain ⟨t0, t1, t2, t3, t4⟩ := htgt
  set anchor := (D.target.leftUnit 0).angle with hanc
  have hcancel := D.flux_cancel (E := LR) (gc α β hα hβ anchor).weight
    (gc α β hα hβ anchor).weight_odd
  have hT := target_flux α β hα hβ X Y D.target t0 t1 t2 t3 t4
  have htile : ∀ i : Fin N, ∃ (σ s : ℤ) (bb : Bool),
      (D.tile i).flux (gc α β hα hβ anchor).weight = mp (BAD.term e f (σ, s, bb)) := by
    intro i
    obtain ⟨τ, hτ⟩ := (D.tiles_congruent i).exists_perm
    refine tile_flux_form α β hα hβ anchor e f (D.tile i) (τ.trans ρ) ?_ ?_
    · intro k; rw [(hτ k).1, (hρ (τ k)).1]; rfl
    · intro k; rw [(hτ k).2, (hρ (τ k)).2]; rfl
  choose σ s bb hfl using htile
  let g : Fin N → ℤ × ℤ × Bool := fun i => (σ i, s i, bb i)
  have hsum : mp (BAD.tsum e f (List.ofFn g)) = Qv X Y := by
    rw [tsum_ofFn]
    have : ∀ i, mp (BAD.term e f (g i)) = (D.tile i).flux (gc α β hα hβ anchor).weight :=
      fun i => (hfl i).symm
    rw [Finset.sum_congr rfl fun i _ => this i, hcancel, hT]
    simp only [Qv, T_pow]
    norm_num
  set q := BAD.tsum e f (List.ofFn g) with hq
  have hX : X = ((q 2 : ℤ) : ℝ) := by rw [← mp_coeff, hsum, Qv_coeff2]
  have hY : Y = ((q 0 : ℤ) : ℝ) := by rw [← mp_coeff, hsum, Qv_coeff0]
  refine ⟨q 2, q 0, List.ofFn g, hX, hY, ?_⟩
  apply mp_injective
  rw [mp_Bd, ← hX, ← hY]
  exact hsum.symm

end

end Erdos634.BADL2

#print axioms Erdos634.BADL2.L2
