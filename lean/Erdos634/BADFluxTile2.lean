import Erdos634.BADFluxTile

/-!
# BAD layer L2, step S2b: the concrete grid character and the per-tile flux form

Written 2026-10-03.  UNAUDITED.  For the concrete `GridChar ℝ[T;T⁻¹]` built from `psi0`, a tile whose
angles/sides are the model `(α,β,π-α-β)`, `(ef, f²-e², f²)` permuted by `ρ` has
`flux = mp (BAD.term e f (σ,s,b))` (any orientation).
-/

open LaurentPolynomial

namespace Erdos634.BADL2
open Erdos634.Geometry

noncomputable section

def Ang (α β : ℝ) : Fin 3 → ℝ := ![α, β, Real.pi - α - β]
def Lenr (e f : ℤ) : Fin 3 → ℝ := ![(e : ℝ) * f, (f : ℝ) ^ 2 - (e : ℝ) ^ 2, (f : ℝ) ^ 2]

theorem phi_apply (α β : ℝ) (i j : ℤ) :
    phi α β (i, j) = (((i : ℝ) * α + (j : ℝ) * β : ℝ) : Real.Angle) := rfl

theorem psi0_pi : psi0 (3, 2) = -1 := by
  rw [psi0_apply, BAD.ee32']
  have : BAD.kk 3 2 = 0 := by decide
  rw [this]; simp

section conc
variable (α β : ℝ) (hα : ¬∃ r : ℚ, α = r * Real.pi) (hβ : 3 * α + 2 * β = Real.pi)
include hα hβ


theorem phi_pi : phi α β (3, 2) = ((Real.pi : ℝ) : Real.Angle) := by
  rw [phi_apply α β]
  refine congrArg _ ?_
  push_cast; linarith

/-- the concrete grid character. -/
def gc (anchor : Real.Angle) : GridChar LR :=
  ofAddChar (phi α β) psi0 (psi0_ker α β hα hβ) (3, 2) (phi_pi α β hα hβ) (psi0_pi) anchor

theorem chi_coord (anchor : Real.Angle) (i j : ℤ) (r : ℝ) (hr : r = i * α + j * β) :
    (gc α β hα hβ anchor).chi ((r : ℝ) : Real.Angle) = psi0 (i, j) := by
  have h := ofAddChar_chi (phi α β) psi0 (psi0_ker α β hα hβ) (3, 2) (phi_pi α β hα hβ) psi0_pi
    anchor (i, j)
  have e : phi α β (i, j) = ((r : ℝ) : Real.Angle) := by
    rw [phi_apply α β, hr]
  rw [← e]; exact h

theorem mem_coord (anchor : Real.Angle) (i j : ℤ) (r : ℝ) (hr : r = i * α + j * β) :
    ((r : ℝ) : Real.Angle) ∈ (gc α β hα hβ anchor).L := by
  have e : phi α β (i, j) = ((r : ℝ) : Real.Angle) := by
    rw [phi_apply α β, hr]
  rw [← e]
  exact AddMonoidHom.mem_range.mpr ⟨(i, j), rfl⟩

theorem mem_Ang (anchor : Real.Angle) (k : Fin 3) :
    ((Ang α β k : ℝ) : Real.Angle) ∈ (gc α β hα hβ anchor).L := by
  fin_cases k
  · exact mem_coord α β hα hβ anchor 1 0 _ (by simp [Ang])
  · exact mem_coord α β hα hβ anchor 0 1 _ (by simp [Ang])
  · exact mem_coord α β hα hβ anchor 2 1 _ (by simp [Ang]; linarith)

theorem chi_Ang (anchor : Real.Angle) (k : Fin 3) :
    (gc α β hα hβ anchor).chi ((Real.pi - Ang α β k : ℝ) : Real.Angle)
      = cEv (T 1 : LR) (T (-1)) k := by
  have T2 : (T (-2) : LR) = T (-1) * T (-1) := by rw [← T_add]; norm_num
  have T3 : (T 3 : LR) = T 1 * T 1 * T 1 := by rw [← T_add, ← T_add]; norm_num
  have c0 : (gc α β hα hβ anchor).chi ((Real.pi - α : ℝ) : Real.Angle) = T (-1) * T (-1) := by
    rw [chi_coord α β hα hβ anchor 2 2 (Real.pi - α) (by push_cast; linarith), psi0_apply]
    have e : BAD.ee 2 2 = 1 := by simp [BAD.ee]
    have k : BAD.kk 2 2 = -2 := by decide
    rw [e, k, T2]; simp only [Int.cast_one, map_one, one_mul]
  have c1 : (gc α β hα hβ anchor).chi ((Real.pi - β : ℝ) : Real.Angle) = T 1 * T 1 * T 1 := by
    rw [chi_coord α β hα hβ anchor 3 1 (Real.pi - β) (by push_cast; linarith), psi0_apply]
    have e : BAD.ee 3 1 = 1 := BAD.ee32
    have k : BAD.kk 3 1 = 3 := by decide
    rw [e, k, T3]; simp only [Int.cast_one, map_one, one_mul]
  have c2 : (gc α β hα hβ anchor).chi ((Real.pi - (Real.pi - α - β) : ℝ) : Real.Angle)
      = T (-1) := by
    rw [chi_coord α β hα hβ anchor 1 1 (Real.pi - (Real.pi - α - β)) (by push_cast; linarith),
      psi0_apply]
    have e : BAD.ee 1 1 = 1 := by simp [BAD.ee]
    have k : BAD.kk 1 1 = -1 := by decide
    rw [e, k]; simp only [Int.cast_one, map_one, one_mul]
  fin_cases k
  · exact c0
  · exact c1
  · exact c2

theorem val_form (anchor : Real.Angle) (θ : Real.Angle) :
    ∃ p : ℤ × ℤ, (gc α β hα hβ anchor).val θ = psi0 p :=
  ofAddChar_val (phi α β) psi0 (psi0_ker α β hα hβ) (3, 2) (phi_pi α β hα hβ) psi0_pi anchor θ

end conc

theorem alg_Len (e f : ℤ) (k : Fin 3) :
    algebraMap ℝ LR (Lenr e f k)
      = Lv (C ((e : ℝ) * f)) (C ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) (C ((f : ℝ) ^ 2)) k := by
  rw [← LaurentPolynomial.C_eq_algebraMap]
  fin_cases k <;> simp [Lenr, Lv]

theorem T_pow_neg (k : ℕ) : ((T (-1) : LR)) ^ k = T (-(k : ℤ)) := by
  rw [T_pow]; congr 1; ring

theorem T1_mul : (T 1 : LR) * T (-1) = 1 := by rw [← T_add]; simp

theorem mp_pTile (e f : ℤ) : mp (BAD.pTile e f)
    = C ((f : ℝ) ^ 2) + C ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * (T 1 : LR) ^ 2 + C ((e : ℝ) * f) * T 1 ^ 3 := by
  rw [← BAD.p_form]
  simp only [map_add, map_mul, mp_C, mp_T, T_pow]
  push_cast
  rfl

theorem mp_qTile (e f : ℤ) : mp (BAD.qTile e f)
    = C ((f : ℝ) ^ 2) * (T 1 : LR) ^ 3 + C ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * T 1 + C ((e : ℝ) * f) := by
  rw [← BAD.q_form]
  simp only [map_add, map_mul, mp_C, mp_T, T_pow]
  push_cast
  rfl

theorem tile_flux_form (α β : ℝ) (hα : ¬∃ r : ℚ, α = r * Real.pi) (hβ : 3 * α + 2 * β = Real.pi)
    (anchor : Real.Angle) (e f : ℤ) (Tt : Tri) (ρ : Equiv.Perm (Fin 3))
    (hang : ∀ k, Tt.angleAt k = Ang α β (ρ k)) (hlen : ∀ k, Tt.oppLen k = Lenr e f (ρ k)) :
    ∃ (σ s : ℤ) (bb : Bool),
      Tt.flux (gc α β hα hβ anchor).weight = mp (BAD.term e f (σ, s, bb)) := by
  set G := gc α β hα hβ anchor with hG
  have hL : ∀ k, ((Tt.angleAt k : ℝ) : Real.Angle) ∈ G.L := fun k => by
    rw [hang k]; exact mem_Ang α β hα hβ anchor _
  have h01 : ρ 0 ≠ ρ 1 := fun h => absurd (ρ.injective h) (by decide)
  have h02 : ρ 0 ≠ ρ 2 := fun h => absurd (ρ.injective h) (by decide)
  have h12 : ρ 1 ≠ ρ 2 := fun h => absurd (ρ.injective h) (by decide)
  have cE : ∀ k, G.chi ((Real.pi - Tt.angleAt k : ℝ) : Real.Angle)
      = cEv (T 1 : LR) (T (-1)) (ρ k) := fun k => by
    rw [hang k]; exact chi_Ang α β hα hβ anchor _
  have aL : ∀ k, algebraMap ℝ LR (Tt.oppLen k)
      = Lv (C ((e : ℝ) * f)) (C ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) (C ((f : ℝ) ^ 2)) (ρ k) :=
    fun k => by rw [hlen k]; exact alg_Len e f _
  have key : ∀ (p : ℤ × ℤ) (k : ℕ) (bb : Bool) (X : LR),
      X = (if bb then C ((f : ℝ) ^ 2) + C ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * (T 1 : LR) ^ 2
          + C ((e : ℝ) * f) * T 1 ^ 3
        else C ((f : ℝ) ^ 2) * (T 1 : LR) ^ 3 + C ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * T 1
          + C ((e : ℝ) * f)) →
      psi0 p * ((T (-1) : LR) ^ k * X)
        = mp (BAD.term e f (BAD.ee p.1 p.2, BAD.kk p.1 p.2 + -(k : ℤ), bb)) := by
    intro p k bb X hX
    rw [hX]
    cases bb
    · simp only [BAD.term, Bool.false_eq_true, if_false, map_mul, mp_C, mp_T, mp_qTile]
      rw [psi0_apply, T_pow_neg, T_add]; ring
    · simp only [BAD.term, if_true, map_mul, mp_C, mp_T, mp_pTile]
      rw [psi0_apply, T_pow_neg, T_add]; ring
  rcases Tt.det_pos_or_neg with hT | hT
  · rw [flux_pos_R G Tt hT hL, aL 2, aL 0, aL 1, cE 1, cE 2]
    obtain ⟨p, hp⟩ := val_form α β hα hβ anchor (Tt.leftUnit 0).angle
    have hp' : G.weight (Tt.leftUnit 0) = psi0 p := hp
    rw [hp']
    obtain ⟨k, h | h⟩ := brk_pos (C ((e : ℝ) * f)) (C ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) (C ((f : ℝ) ^ 2))
      (T 1) (T (-1)) T1_mul (ρ 0) (ρ 1) (ρ 2) h01 h02 h12
    · rw [h]; exact ⟨_, _, true, key p k true _ (by simp)⟩
    · rw [h]; exact ⟨_, _, false, key p k false _ (by simp)⟩
  · rw [flux_neg_R G Tt hT hL, aL 1, aL 0, aL 2, cE 2, cE 1]
    obtain ⟨p, hp⟩ := val_form α β hα hβ anchor (Tt.leftUnit 2).angle
    have hp' : G.weight (Tt.leftUnit 2) = psi0 p := hp
    rw [hp']
    obtain ⟨k, h | h⟩ := brk_neg (C ((e : ℝ) * f)) (C ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) (C ((f : ℝ) ^ 2))
      (T 1) (T (-1)) T1_mul (ρ 0) (ρ 1) (ρ 2) h01 h02 h12
    · rw [h]; exact ⟨_, _, true, key p k true _ (by simp)⟩
    · rw [h]; exact ⟨_, _, false, key p k false _ (by simp)⟩

end

end Erdos634.BADL2

#print axioms Erdos634.BADL2.tile_flux_form
#print axioms Erdos634.BADL2.chi_Ang
#print axioms Erdos634.BADL2.val_form
