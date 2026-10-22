-- Draft/KMomentTri.lean — CASE A, node A3 (Lemma K, K2 half), route (b) "moments", step 2:
-- the monomial moment of a triangle is |det| times a ℚ-POLYNOMIAL in its corner coordinates,
-- and that polynomial commutes with every ring hom of fields of characteristic 0.
--
--   ∫_T x₀^i x₁^j = |det T| · Λ(Qm c_T i j),    Mom c i j := det(c) · Λ(Qm c i j),
--   φ (Mom c i j) = Mom (φ ∘ c) i j       for every ring hom φ : R →+* S.
--
-- Qm c i j = (affine form 0)^i (affine form 1)^j ∈ R[s, t] is the monomial pulled back by the
-- affine map carrying the reference triangle to T; Λ integrates R[s, t] over the reference
-- triangle using the rational values `qstd` (Draft/KMomentStd.lean).
-- Formalization debt on a paper-level PROVED node; NOT /goal progress.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
-- H59: no parameter pair (e, f) is evaluated here.
import Erdos634.Draft.KMomentStd
import Mathlib.MeasureTheory.Function.Jacobian

open MeasureTheory Set MvPolynomial

namespace Erdos634.KMoment

open Erdos634.Geometry Erdos634.AreaDet

section Alg

variable {R S : Type*} [Field R] [CharZero R] [Field S] [CharZero S]

/-- The affine coordinate forms of the map carrying the reference triangle onto corners `c`. -/
noncomputable def Lf (c : Fin 3 → Fin 2 → R) (v : Fin 2) : MvPolynomial (Fin 2) R :=
  C (c 0 v) + X 0 * C (c 1 v - c 0 v) + X 1 * C (c 2 v - c 0 v)

/-- The pulled-back monomial `x₀^i x₁^j`. -/
noncomputable def Qm (c : Fin 3 → Fin 2 → R) (i j : ℕ) : MvPolynomial (Fin 2) R :=
  Lf c 0 ^ i * Lf c 1 ^ j

/-- Integration over the reference triangle, with rational weights. -/
noncomputable def Λ (Q : MvPolynomial (Fin 2) R) : R :=
  ∑ m ∈ Q.support, coeff m Q * ((qstd (m 0) (m 1) : ℚ) : R)

/-- The determinant of corners `c` (twice the signed area). -/
def detc (c : Fin 3 → Fin 2 → R) : R :=
  (c 1 0 - c 0 0) * (c 2 1 - c 0 1) - (c 1 1 - c 0 1) * (c 2 0 - c 0 0)

/-- The signed monomial moment. -/
noncomputable def Mom (c : Fin 3 → Fin 2 → R) (i j : ℕ) : R := detc c * Λ (Qm c i j)

theorem map_Qm (φ : R →+* S) (c : Fin 3 → Fin 2 → R) (i j : ℕ) :
    map φ (Qm c i j) = Qm (fun k v => φ (c k v)) i j := by
  simp [Qm, Lf, map_mul, map_pow, map_add, map_C, map_X, map_sub]

theorem map_Λ (φ : R →+* S) (Q : MvPolynomial (Fin 2) R) : φ (Λ Q) = Λ (map φ Q) := by
  unfold Λ
  rw [support_map_of_injective Q φ.injective, map_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [map_mul, coeff_map, map_ratCast]

theorem map_detc (φ : R →+* S) (c : Fin 3 → Fin 2 → R) :
    φ (detc c) = detc (fun k v => φ (c k v)) := by
  simp [detc, map_sub, map_mul]

/-- **Naturality of the signed moment** under any ring hom of characteristic-0 fields. -/
theorem map_Mom (φ : R →+* S) (c : Fin 3 → Fin 2 → R) (i j : ℕ) :
    φ (Mom c i j) = Mom (fun k v => φ (c k v)) i j := by
  rw [Mom, map_mul, map_detc, map_Λ, map_Qm]; rfl

end Alg

/-! ## The real moment of a triangle -/

/-- Corner coordinates of a triangle. -/
def cT (T : Tri) : Fin 3 → Fin 2 → ℝ := fun k v => T.pts k v

theorem detc_cT (T : Tri) : detc (cT T) = T.det := by
  simp [detc, cT, Tri.det]

theorem integral_std_poly (Q : MvPolynomial (Fin 2) ℝ) :
    ∫ x in stdCarrier, eval (fun v => x v) Q = Λ Q := by
  simp_rw [eval_eq']
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl (fun m _ => ?_)
    simp_rw [Fin.prod_univ_two]
    rw [integral_const_mul, integral_std]
  · intro m _
    apply ContinuousOn.integrableOn_compact (isCompact_stdCarrier)
    apply Continuous.continuousOn
    apply continuous_const.mul
    apply continuous_finsetProd
    intro v _
    exact ((PiLp.continuous_apply 2 _ v)).pow _

theorem edgeMap_apply' (T : Tri) (x : Plane) :
    edgeMap T x = x 0 • (T.pts 1 - T.pts 0) + x 1 • (T.pts 2 - T.pts 0) := by
  rw [edgeMap, Module.Basis.constr_apply, Finsupp.sum_fintype _ _ (fun i => by simp),
    Fin.sum_univ_two, pb_repr, pb_repr]
  rfl

theorem place_coord (T : Tri) (x : Plane) (v : Fin 2) :
    (T.pts 0 + edgeMap T x) v = eval (fun w => x w) (Lf (cT T) v) := by
  rw [edgeMap_apply']
  simp [Lf, cT]
  ring

/-- **The moment formula**: `∫_T x₀^i x₁^j = |det T| · Λ(Qm c_T i j)`. -/
theorem integral_tri (T : Tri) (i j : ℕ) :
    ∫ x in T.carrier, (x 0) ^ i * (x 1) ^ j = |T.det| * Λ (Qm (cT T) i j) := by
  set L := (edgeMap T).toContinuousLinearMap with hL
  set f : Plane → Plane := fun x => T.pts 0 + L x with hf
  have himg : f '' stdCarrier = T.carrier := by
    rw [← placeMap_stdCarrier T]
    congr 1
  have hdet0 : LinearMap.det (edgeMap T) = T.det := by
    have := detTri_eq T
    rw [detTri] at this
    rw [this, Tri.det]; ring
  have hdet : L.det = T.det := by rw [hL, LinearMap.det_toContinuousLinearMap, hdet0]
  have hne : LinearMap.det (edgeMap T) ≠ 0 := by rw [hdet0]; exact T.det_ne_zero
  have hinj : Function.Injective L := fun x y h =>
    (LinearMap.equivOfDetNeZero _ hne).injective h
  rw [← himg, integral_image_eq_integral_abs_det_fderiv_smul volume (f' := fun _ => L)
    isCompact_stdCarrier.measurableSet
    (fun x _ => (L.hasFDerivAt.const_add (T.pts 0)).hasFDerivWithinAt)
    (fun x _ y _ h => hinj (add_left_cancel h))]
  simp only [hdet, smul_eq_mul]
  rw [integral_const_mul, ← integral_std_poly]
  congr 1
  refine setIntegral_congr_fun isCompact_stdCarrier.measurableSet (fun x _ => ?_)
  simp only [hL, LinearMap.coe_toContinuousLinearMap']
  rw [place_coord, place_coord, Qm, map_mul, map_pow, map_pow]

end Erdos634.KMoment

#print axioms Erdos634.KMoment.map_Mom
#print axioms Erdos634.KMoment.integral_tri
