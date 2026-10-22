import Erdos634.Congruence
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Draft/GapE120SSS.lean -- **SSS gives congruence** in the plane: two triangles with the same three side lengths (same vertex
    labelling) are `Tri.Congruent` (an isometry of the plane carrying vertices to vertices).  N-free, elementary: via
    `Plane ≃ₗᵢ ℂ`.  The converse `Tri.Congruent.dist_eq` was already in `Congruence.lean`.  Needed to state the certificate
    instance (`Refl.BridgeE120`) for an arbitrary dissection whose target/model have prescribed side lengths.  UNAUDITED. -/

namespace Erdos634.Geometry.SSS

open Complex

/-- the isometry `z ↦ u z + c` of `ℂ`, `|u| = 1`. -/
noncomputable def rotTrans (u c : ℂ) (hu : ‖u‖ = 1) : ℂ ≃ᵢ ℂ where
  toFun z := u * z + c
  invFun w := (starRingEnd ℂ u) * (w - c)
  left_inv z := by
    have : (starRingEnd ℂ u) * u = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]; simp
    simp only [add_sub_cancel_right]; rw [← mul_assoc, this, one_mul]
  right_inv w := by
    have : u * (starRingEnd ℂ u) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]; simp
    simp only; rw [← mul_assoc, this, one_mul]; ring
  isometry_toFun := by
    refine Isometry.of_dist_eq fun x y => ?_
    simp only [dist_eq_norm]
    rw [show u * x + c - (u * y + c) = u * (x - y) by ring, norm_mul, hu, one_mul]

/-- the isometry `z ↦ u · conj z + c` of `ℂ`, `|u| = 1`. -/
noncomputable def conjTrans (u c : ℂ) (hu : ‖u‖ = 1) : ℂ ≃ᵢ ℂ where
  toFun z := u * (starRingEnd ℂ z) + c
  invFun w := starRingEnd ℂ (starRingEnd ℂ u * (w - c))
  left_inv z := by
    have : (starRingEnd ℂ u) * u = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]; simp
    simp only [add_sub_cancel_right, map_mul, Complex.conj_conj]
    linear_combination z * this
  right_inv w := by
    have : u * (starRingEnd ℂ u) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]; simp
    simp only [map_mul, Complex.conj_conj]
    rw [← mul_assoc, this, one_mul]; ring
  isometry_toFun := by
    refine Isometry.of_dist_eq fun x y => ?_
    simp only [dist_eq_norm]
    rw [show u * (starRingEnd ℂ) x + c - (u * (starRingEnd ℂ) y + c) = u * (starRingEnd ℂ (x - y)) by
      rw [map_sub]; ring, norm_mul, hu, one_mul, Complex.norm_conj]


theorem eq_or_conj (s s' : ℂ) (h1 : s'.re = s.re) (h2 : Complex.normSq s' = Complex.normSq s) :
    s' = s ∨ s' = starRingEnd ℂ s := by
  have h3 : s'.im ^ 2 = s.im ^ 2 := by
    rw [Complex.normSq_apply, Complex.normSq_apply, h1] at h2
    nlinarith [h2]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h3 with h | h
  · left; exact Complex.ext h1 h
  · right; apply Complex.ext
    · simpa using h1
    · simpa using h

/-- two points at the same distances from `0` and from `e ≠ 0` coincide or are mirror images across the line `ℝ e`. -/
theorem same_dists (e v v' : ℂ) (he : e ≠ 0) (h0 : Complex.normSq v' = Complex.normSq v)
    (h1 : Complex.normSq (v' - e) = Complex.normSq (v - e)) :
    v' = v ∨ v' = (e / starRingEnd ℂ e) * starRingEnd ℂ v := by
  have hce : starRingEnd ℂ e ≠ 0 := by simpa using he
  have hre : (v' * starRingEnd ℂ e).re = (v * starRingEnd ℂ e).re := by
    rw [Complex.normSq_sub, Complex.normSq_sub, h0] at h1
    linarith
  have hn : Complex.normSq (v' * starRingEnd ℂ e) = Complex.normSq (v * starRingEnd ℂ e) := by
    rw [map_mul, map_mul, h0]
  rcases eq_or_conj _ _ hre hn with h | h
  · left
    exact mul_right_cancel₀ hce h
  · right
    have : v' * starRingEnd ℂ e = (e / starRingEnd ℂ e) * starRingEnd ℂ v * starRingEnd ℂ e := by
      rw [h, map_mul, Complex.conj_conj]
      field_simp
    exact mul_right_cancel₀ hce this

theorem sss_complex (z0 z1 z2 w0 w1 w2 : ℂ) (hne : z0 ≠ z1)
    (h01 : ‖z0 - z1‖ = ‖w0 - w1‖) (h12 : ‖z1 - z2‖ = ‖w1 - w2‖) (h02 : ‖z0 - z2‖ = ‖w0 - w2‖) :
    ∃ F : ℂ ≃ᵢ ℂ, F z0 = w0 ∧ F z1 = w1 ∧ F z2 = w2 := by
  set d := z1 - z0 with hd
  set e := w1 - w0 with he
  have hd0 : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hnorm : ‖e‖ = ‖d‖ := by
    rw [hd, he, ← norm_neg (z1 - z0), ← norm_neg (w1 - w0), neg_sub, neg_sub]; exact h01.symm
  have he0 : e ≠ 0 := by
    intro h; rw [h, norm_zero] at hnorm; exact hd0 (norm_eq_zero.mp hnorm.symm)
  set u := e / d with hu
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_div, hnorm]; exact div_self (norm_ne_zero_iff.mpr hd0)
  set F1 := rotTrans u (w0 - u * z0) hun with hF1
  have F1a : ∀ z, F1 z = u * z + (w0 - u * z0) := fun z => rfl
  have f0 : F1 z0 = w0 := by rw [F1a]; ring
  have f1 : F1 z1 = w1 := by
    rw [F1a]
    have : u * d = e := by rw [hu]; field_simp
    have h2 : u * z1 = u * d + u * z0 := by rw [hd]; ring
    rw [h2, this, he]; ring
  set w2' := F1 z2 with hw2'
  have d0 : dist w2' w0 = dist z2 z0 := by rw [← f0, hw2']; exact F1.dist_eq _ _
  have d1 : dist w2' w1 = dist z2 z1 := by rw [← f1, hw2']; exact F1.dist_eq _ _
  have e0 : Complex.normSq (w2' - w0) = Complex.normSq (w2 - w0) := by
    rw [← Complex.sq_norm, ← Complex.sq_norm, ← dist_eq_norm, ← dist_eq_norm, d0, dist_eq_norm, dist_eq_norm,
      ← norm_neg (z2 - z0), ← norm_neg (w2 - w0), neg_sub, neg_sub]
    rw [h02]
  have e1 : Complex.normSq ((w2' - w0) - e) = Complex.normSq ((w2 - w0) - e) := by
    have : (w2' - w0) - e = w2' - w1 := by rw [he]; ring
    have h2 : (w2 - w0) - e = w2 - w1 := by rw [he]; ring
    rw [this, h2, ← Complex.sq_norm, ← Complex.sq_norm, ← dist_eq_norm, ← dist_eq_norm, d1, dist_eq_norm,
      dist_eq_norm, ← norm_neg (z2 - z1), ← norm_neg (w2 - w1), neg_sub, neg_sub]
    rw [h12]
  rcases same_dists e (w2' - w0) (w2 - w0) he0 e0.symm e1.symm with h | h
  · refine ⟨F1, f0, f1, ?_⟩
    have : w2 = w2' := by linear_combination h
    rw [this]
  · have hce : starRingEnd ℂ e ≠ 0 := by simpa using he0
    have hu2 : ‖e / starRingEnd ℂ e‖ = 1 := by
      rw [norm_div, Complex.norm_conj]; exact div_self (norm_ne_zero_iff.mpr he0)
    set u2 := e / starRingEnd ℂ e with hu2d
    have hu2e : u2 * starRingEnd ℂ e = e := by rw [hu2d]; field_simp
    set R := conjTrans u2 (w0 - u2 * starRingEnd ℂ w0) hu2 with hR
    have Ra : ∀ z, R z = u2 * starRingEnd ℂ z + (w0 - u2 * starRingEnd ℂ w0) := fun z => rfl
    refine ⟨F1.trans R, ?_, ?_, ?_⟩
    · show R (F1 z0) = w0
      rw [f0, Ra]; ring
    · show R (F1 z1) = w1
      rw [f1, Ra]
      have : starRingEnd ℂ w1 = starRingEnd ℂ w0 + starRingEnd ℂ e := by rw [he, map_sub]; ring
      rw [this]
      linear_combination hu2e
    · show R (F1 z2) = w2
      rw [← hw2', Ra]
      have : w2 - w0 = u2 * starRingEnd ℂ (w2' - w0) := h
      rw [map_sub] at this
      linear_combination -this

end Erdos634.Geometry.SSS

namespace Erdos634.Geometry

open Erdos634.Geometry.SSS

/-- **SSS ⇒ congruence** (same vertex labelling): triangles of the plane with equal side lengths are related by an isometry
of the plane carrying `T.pts k` to `U.pts k`. -/
theorem Tri.congruent_of_dist (T U : Tri)
    (h01 : dist (T.pts 0) (T.pts 1) = dist (U.pts 0) (U.pts 1))
    (h12 : dist (T.pts 1) (T.pts 2) = dist (U.pts 1) (U.pts 2))
    (h02 : dist (T.pts 0) (T.pts 2) = dist (U.pts 0) (U.pts 2)) : T.Congruent U := by
  let e : ℂ ≃ₗᵢ[ℝ] Plane := Complex.orthonormalBasisOneI.repr
  have hne : e.symm (T.pts 0) ≠ e.symm (T.pts 1) := by
    intro h
    have := e.symm.injective h
    have hinj := T.indep.injective
    exact absurd (hinj this) (by decide)
  have nrm : ∀ x y : Plane, ‖e.symm x - e.symm y‖ = dist x y := by
    intro x y; rw [← map_sub, LinearIsometryEquiv.norm_map, dist_eq_norm]
  obtain ⟨F, f0, f1, f2⟩ := sss_complex (e.symm (T.pts 0)) (e.symm (T.pts 1)) (e.symm (T.pts 2))
    (e.symm (U.pts 0)) (e.symm (U.pts 1)) (e.symm (U.pts 2)) hne
    (by rw [nrm, nrm]; exact h01) (by rw [nrm, nrm]; exact h12) (by rw [nrm, nrm]; exact h02)
  refine ⟨e.symm.toIsometryEquiv.trans (F.trans e.toIsometryEquiv), Equiv.refl _, fun k => ?_⟩
  fin_cases k
  · show e (F (e.symm (T.pts 0))) = U.pts 0
    rw [f0]; simp
  · show e (F (e.symm (T.pts 1))) = U.pts 1
    rw [f1]; simp
  · show e (F (e.symm (T.pts 2))) = U.pts 2
    rw [f2]; simp

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Tri.congruent_of_dist
