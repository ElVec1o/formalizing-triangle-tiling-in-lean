import Erdos634.BADGridChar

/-!
# BAD layer L2, step S2: the tile flux in `ℝ[T;T⁻¹]` (12 finite cases)

Written 2026-10-03.  UNAUDITED.  R-generalised `flux_grid_of_pos/neg`; for a tile with angles
`(α,β,π-α-β)` permuted by `ρ` and sides `(ef, f²-e², f²)` permuted by `ρ`, `flux = ± T^s (p or q)`
(6 vertex orders x 2 orientations), as the image of a `BAD.term`.
-/

open LaurentPolynomial

namespace Erdos634.BADL2
open Erdos634.Geometry

noncomputable section

/-- integer Laurent polynomials into real ones. -/
def mp : LaurentPolynomial ℤ →+* LR := AddMonoidAlgebra.mapRingHom ℤ (Int.castRingHom ℝ)

theorem mp_C (z : ℤ) : mp (C z) = C (z : ℝ) := by
  show AddMonoidAlgebra.mapRingHom ℤ (Int.castRingHom ℝ) (AddMonoidAlgebra.single 0 z)
    = AddMonoidAlgebra.single 0 (z : ℝ)
  rw [AddMonoidAlgebra.mapRingHom_single]; rfl

theorem mp_T (n : ℤ) : mp (T n) = (T n : LR) := by
  show AddMonoidAlgebra.mapRingHom ℤ (Int.castRingHom ℝ) (AddMonoidAlgebra.single n 1)
    = AddMonoidAlgebra.single n 1
  rw [AddMonoidAlgebra.mapRingHom_single]; simp

theorem mp_coeff (x : LaurentPolynomial ℤ) (n : ℤ) : mp x n = ((x n : ℤ) : ℝ) :=
  AddMonoidAlgebra.mapRingHom_apply _ _ _

theorem mp_injective : Function.Injective mp := by
  intro x y h
  ext n
  have := congrArg (fun z : LR => z n) h
  simp only [mp_coeff] at this
  exact_mod_cast this

/-! ## generic tile flux over an `ℝ`-algebra -/

theorem pi_sub_mem' {R : Type*} [CommRing R] (G : GridChar R) (T : Tri)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) (k : Fin 3) :
    ((Real.pi - T.angleAt k : ℝ) : Real.Angle) ∈ G.L := by
  rw [Real.Angle.coe_sub]
  exact G.L.sub_mem G.pi_mem (h k)

theorem flux_pos_R {R : Type*} [CommRing R] [Algebra ℝ R] (G : GridChar R) (T : Tri)
    (hT : 0 < T.det) (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) :
    T.flux G.weight = G.weight (T.leftUnit 0) *
      (algebraMap ℝ R (T.oppLen 2) + G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle)
          * algebraMap ℝ R (T.oppLen 0)
        + G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle)
          * G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle) * algebraMap ℝ R (T.oppLen 1)) := by
  have t1 := T.leftUnit_turn_of_pos hT 0
  have t2 := T.leftUnit_turn_of_pos hT 1
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl] at t1 t2
  have w1 : G.weight (T.leftUnit 1)
      = G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle) * G.weight (T.leftUnit 0) := by
    unfold GridChar.weight
    rw [t1, G.val_add _ (pi_sub_mem' G T h 1)]
  have w2 : G.weight (T.leftUnit 2)
      = G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle) * G.weight (T.leftUnit 1) := by
    unfold GridChar.weight
    rw [t2, G.val_add _ (pi_sub_mem' G T h 2)]
  unfold Tri.flux Tri.oppLen
  rw [Fin.sum_univ_three]
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl,
    show (2:Fin 3) + 1 = 0 from rfl, show (0:Fin 3) + 2 = 2 from rfl,
    show (1:Fin 3) + 2 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl, Algebra.smul_def]
  rw [w2, w1]
  ring

theorem flux_neg_R {R : Type*} [CommRing R] [Algebra ℝ R] (G : GridChar R) (T : Tri)
    (hT : T.det < 0) (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) :
    T.flux G.weight = G.weight (T.leftUnit 2) *
      (algebraMap ℝ R (T.oppLen 1) + G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle)
          * algebraMap ℝ R (T.oppLen 0)
        + G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle)
          * G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle) * algebraMap ℝ R (T.oppLen 2)) := by
  have t0 := T.leftUnit_turn_of_neg hT 0
  have t1 := T.leftUnit_turn_of_neg hT 1
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl] at t0 t1
  have w1 : G.weight (T.leftUnit 1)
      = G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle) * G.weight (T.leftUnit 2) := by
    unfold GridChar.weight
    rw [t1, G.val_add _ (pi_sub_mem' G T h 2)]
  have w0 : G.weight (T.leftUnit 0)
      = G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle) * G.weight (T.leftUnit 1) := by
    unfold GridChar.weight
    rw [t0, G.val_add _ (pi_sub_mem' G T h 1)]
  unfold Tri.flux Tri.oppLen
  rw [Fin.sum_univ_three]
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl,
    show (2:Fin 3) + 1 = 0 from rfl, show (0:Fin 3) + 2 = 2 from rfl,
    show (1:Fin 3) + 2 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl, Algebra.smul_def]
  rw [w0, w1]
  ring

/-! ## the 12 finite cases -/

theorem perm3 (x y z : Fin 3) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (x = 0 ∧ y = 1 ∧ z = 2) ∨ (x = 0 ∧ y = 2 ∧ z = 1) ∨ (x = 1 ∧ y = 0 ∧ z = 2) ∨
    (x = 1 ∧ y = 2 ∧ z = 0) ∨ (x = 2 ∧ y = 0 ∧ z = 1) ∨ (x = 2 ∧ y = 1 ∧ z = 0) := by
  revert x y z; decide

def Lv {R : Type*} (a b c : R) : Fin 3 → R := ![a, b, c]
def cEv {R : Type*} [CommRing R] (t u : R) : Fin 3 → R := ![u * u, t * t * t, u]

theorem brk_pos {R : Type*} [CommRing R] (a b c t u : R) (hu : t * u = 1) (x y z : Fin 3)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ k : ℕ, (Lv a b c z + cEv t u y * Lv a b c x + cEv t u y * cEv t u z * Lv a b c y
        = u ^ k * (c + b * t ^ 2 + a * t ^ 3)) ∨
      (Lv a b c z + cEv t u y * Lv a b c x + cEv t u y * cEv t u z * Lv a b c y
        = u ^ k * (c * t ^ 3 + b * t + a)) := by
  rcases perm3 x y z hxy hxz hyz with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact ⟨0, Or.inl (by simp only [Lv, cEv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; linear_combination (b*t^2) * hu)⟩
  · exact ⟨1, Or.inr (by simp only [Lv, cEv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; linear_combination (-b) * hu)⟩
  · exact ⟨3, Or.inr (by simp only [Lv, cEv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; linear_combination (-b*u^2 - c*t^2*u^2 - c*t*u - c) * hu)⟩
  · exact ⟨3, Or.inl (by simp only [Lv, cEv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; linear_combination (-a*t^2*u^2 - a*t*u - a - b*t*u^2 - b*u) * hu)⟩
  · exact ⟨2, Or.inl (by simp only [Lv, cEv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; linear_combination (-b*t*u - b) * hu)⟩
  · exact ⟨0, Or.inr (by simp only [Lv, cEv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; linear_combination (b*t^2*u + b*t) * hu)⟩

theorem brk_neg {R : Type*} [CommRing R] (a b c t u : R) (hu : t * u = 1) (x y z : Fin 3)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ k : ℕ, (Lv a b c y + cEv t u z * Lv a b c x + cEv t u z * cEv t u y * Lv a b c z
        = u ^ k * (c + b * t ^ 2 + a * t ^ 3)) ∨
      (Lv a b c y + cEv t u z * Lv a b c x + cEv t u z * cEv t u y * Lv a b c z
        = u ^ k * (c * t ^ 3 + b * t + a)) := by
  rcases perm3 x y z hxy hxz hyz with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact ⟨1, Or.inr (by simp only [Lv, cEv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; linear_combination (-b) * hu)⟩
  · exact ⟨0, Or.inl (by simp only [Lv, cEv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; linear_combination (b*t^2) * hu)⟩
  · exact ⟨3, Or.inl (by simp only [Lv, cEv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; linear_combination (-a*t^2*u^2 - a*t*u - a - b*t*u^2 - b*u) * hu)⟩
  · exact ⟨3, Or.inr (by simp only [Lv, cEv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; linear_combination (-b*u^2 - c*t^2*u^2 - c*t*u - c) * hu)⟩
  · exact ⟨0, Or.inr (by simp only [Lv, cEv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; linear_combination (b*t^2*u + b*t) * hu)⟩
  · exact ⟨2, Or.inl (by simp only [Lv, cEv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; linear_combination (-b*t*u - b) * hu)⟩

end

end Erdos634.BADL2

#print axioms Erdos634.BADL2.brk_pos
#print axioms Erdos634.BADL2.brk_neg
#print axioms Erdos634.BADL2.flux_pos_R
#print axioms Erdos634.BADL2.flux_neg_R
#print axioms Erdos634.BADL2.mp_injective
