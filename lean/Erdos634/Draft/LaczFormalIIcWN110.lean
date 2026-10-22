-- Draft/LaczFormalIIcWN110.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3, Fig. 8), R4: ORIENTED ROTATIONS between complex vectors.
-- `RotPos z1 z2 theta` := `z2 = c e^{i theta} z1` with `c > 0` (the ray of `z2` is the ray of `z1` rotated by `theta`).  Calculus: transitivity (angles add), symmetry, `RotPos z (-z) pi`, closedness (`RotPos z z theta` forces
-- `theta` in `2 pi Z`), uniqueness of the angle mod `2 pi`.  Bridge: an UNSIGNED angle `InnerProductGeometry.angle z1 z2 = theta` plus the sign of `Im (z2 / z1)` gives `RotPos z1 z2 (+-theta)` (`Complex.angle_eq_abs_arg`);
-- and the plane version through `toC` for `EuclideanGeometry.angle`.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN13
import Mathlib.Analysis.Complex.Angle

open scoped Classical Fin.NatCast
open Complex

namespace Erdos634.Draft.LaczFormal.WN

def RotPos (z1 z2 : ℂ) (θ : ℝ) : Prop := ∃ c : ℝ, 0 < c ∧ z2 = (c : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I) * z1)

theorem RotPos.trans {z1 z2 z3 : ℂ} {θ θ' : ℝ} (h1 : RotPos z1 z2 θ) (h2 : RotPos z2 z3 θ') : RotPos z1 z3 (θ + θ') := by
  obtain ⟨c1, hc1, e1⟩ := h1
  obtain ⟨c2, hc2, e2⟩ := h2
  refine ⟨c2 * c1, mul_pos hc2 hc1, ?_⟩
  rw [e2, e1]
  have : Complex.exp (((θ + θ' : ℝ) : ℂ) * Complex.I) = Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp ((θ' : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]; push_cast; ring_nf
  rw [this]; push_cast; ring

theorem RotPos.symm {z1 z2 : ℂ} {θ : ℝ} (h : RotPos z1 z2 θ) : RotPos z2 z1 (-θ) := by
  obtain ⟨c, hc, e⟩ := h
  refine ⟨1 / c, by positivity, ?_⟩
  rw [e]
  have h1 : Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) * Complex.exp ((θ : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add]; push_cast; ring_nf; exact Complex.exp_zero
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  calc z1 = ((1 / c : ℝ) : ℂ) * ((c : ℂ) * (Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) * Complex.exp ((θ : ℂ) * Complex.I) * z1)) := by
        rw [h1]; push_cast; field_simp
    _ = _ := by ring

theorem RotPos.neg_self {z : ℂ} : RotPos z (-z) Real.pi := by
  refine ⟨1, one_pos, ?_⟩
  rw [Complex.exp_pi_mul_I]; simp

theorem RotPos.refl_pos {z : ℂ} {c : ℝ} (hc : 0 < c) : RotPos z ((c : ℂ) * z) 0 := by
  refine ⟨c, hc, ?_⟩
  simp

theorem RotPos.shift {z1 z2 : ℂ} {θ : ℝ} (h : RotPos z1 z2 θ) (n : ℤ) : RotPos z1 z2 (θ + 2 * Real.pi * n) := by
  obtain ⟨c, hc, e⟩ := h
  refine ⟨c, hc, ?_⟩
  rw [e]
  have : Complex.exp (((θ + 2 * Real.pi * n : ℝ) : ℂ) * Complex.I) = Complex.exp ((θ : ℂ) * Complex.I) := by
    have : (((θ + 2 * Real.pi * n : ℝ)) : ℂ) * Complex.I = (θ : ℂ) * Complex.I + (n : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]; ring
  rw [this]

theorem RotPos.closed {z : ℂ} {θ : ℝ} (hz : z ≠ 0) (h : RotPos z z θ) : ∃ n : ℤ, θ = 2 * Real.pi * n := by
  obtain ⟨c, hc, e⟩ := h
  have h1 : (c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) = 1 := by
    have : z * ((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = z * 1 := by rw [mul_one]; nth_rewrite 2 [e]; ring
    exact mul_left_cancel₀ hz this
  have hn : ‖(c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by rw [h1]; simp
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc] at hn
  have : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by
    have h' : (θ : ℂ) * Complex.I = ((θ : ℝ) : ℂ) * Complex.I := rfl
    rw [h', Complex.norm_exp_ofReal_mul_I]
  rw [this, mul_one] at hn
  rw [hn] at h1
  simp at h1
  obtain ⟨n, hn'⟩ := Complex.exp_eq_one_iff.1 h1
  refine ⟨n, ?_⟩
  have := congrArg Complex.im hn'
  simp at this
  linarith

/-- Two angles for the same ray rotation differ by a multiple of `2 pi`. -/
theorem RotPos.unique {z1 z2 : ℂ} {θ θ' : ℝ} (hz : z1 ≠ 0) (h : RotPos z1 z2 θ) (h' : RotPos z1 z2 θ') : ∃ n : ℤ, θ' = θ + 2 * Real.pi * n := by
  have := h.symm.trans h'
  have hz2 : z2 ≠ 0 := by
    obtain ⟨c, hc, e⟩ := h
    rw [e]; exact mul_ne_zero (by exact_mod_cast hc.ne') (mul_ne_zero (Complex.exp_ne_zero _) hz)
  obtain ⟨n, hn⟩ := (h.symm.trans h').closed hz2
  exact ⟨n, by linarith⟩

theorem RotPos.ne_zero_right {z1 z2 : ℂ} {θ : ℝ} (hz : z1 ≠ 0) (h : RotPos z1 z2 θ) : z2 ≠ 0 := by
  obtain ⟨c, hc, e⟩ := h
  rw [e]; exact mul_ne_zero (by exact_mod_cast hc.ne') (mul_ne_zero (Complex.exp_ne_zero _) hz)

/-- From an unsigned angle and the sign of the imaginary part to an oriented rotation. -/
theorem rotPos_of_angle {z1 z2 : ℂ} (h1 : z1 ≠ 0) (h2 : z2 ≠ 0) {θ : ℝ} (hang : InnerProductGeometry.angle z1 z2 = θ) (hpos : 0 < (z2 / z1).im) :
    RotPos z1 z2 θ := by
  have ha := Complex.angle_eq_abs_arg h1 h2
  have hq : z2 / z1 ≠ 0 := div_ne_zero h2 h1
  have harg : 0 < Complex.arg (z2 / z1) := by
    have h0 : 0 ≤ Complex.arg (z2 / z1) := Complex.arg_nonneg_iff.2 hpos.le
    rcases h0.lt_or_eq with h | h
    · exact h
    · exfalso
      have := Complex.arg_eq_zero_iff.1 h.symm
      linarith [this.2]
  have hpi : Complex.arg (z2 / z1) < Real.pi ∨ Complex.arg (z2 / z1) = Real.pi := (Complex.arg_le_pi _).lt_or_eq
  have hne : Complex.arg (z2 / z1) ≠ Real.pi := by
    intro h
    have := Complex.arg_eq_pi_iff.1 h
    linarith [this.2, hpos]
  have hinv : Complex.arg (z1 / z2) = -Complex.arg (z2 / z1) := by
    have : z1 / z2 = (z2 / z1)⁻¹ := (inv_div z2 z1).symm
    rw [this, Complex.arg_inv, if_neg hne]
  have hθ : θ = Complex.arg (z2 / z1) := by
    rw [← hang, ha, hinv, abs_neg, abs_of_pos harg]
  refine ⟨‖z2 / z1‖, norm_pos_iff.2 hq, ?_⟩
  rw [hθ]
  have := Complex.norm_mul_exp_arg_mul_I (z2 / z1)
  calc z2 = (z2 / z1) * z1 := by field_simp
    _ = (((‖z2 / z1‖ : ℝ) : ℂ) * Complex.exp ((Complex.arg (z2 / z1) : ℂ) * Complex.I)) * z1 := by rw [this]
    _ = _ := by ring

theorem rotPos_of_angle_neg {z1 z2 : ℂ} (h1 : z1 ≠ 0) (h2 : z2 ≠ 0) {θ : ℝ} (hang : InnerProductGeometry.angle z1 z2 = θ) (hneg : (z2 / z1).im < 0) :
    RotPos z1 z2 (-θ) := by
  have h := rotPos_of_angle (z1 := z2) (z2 := z1) h2 h1 (θ := θ) (by rw [← hang]; exact InnerProductGeometry.angle_comm _ _) (by
    have : (z1 / z2) = (z2 / z1)⁻¹ := (inv_div z2 z1).symm
    rw [this, Complex.inv_im]
    have hns : 0 < Complex.normSq (z2 / z1) := Complex.normSq_pos.2 (div_ne_zero h2 h1)
    exact div_pos (by linarith) hns)
  exact h.symm

#print axioms RotPos.closed
#print axioms rotPos_of_angle
#print axioms rotPos_of_angle_neg

end Erdos634.Draft.LaczFormal.WN
