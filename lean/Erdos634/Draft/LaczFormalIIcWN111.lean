-- Draft/LaczFormalIIcWN111.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3, Fig. 8), R4: the CLOSURE of a ring quadrilateral gives `RingQuadA` / `RingQuadB`.
-- For four points `P0 P1 P2 P3` (= `V_{i-1} V_i W_i W_{i-1}`) with oriented rotations: turn `pi - B0` at `P1` (side `P0P1` to side `P1P2`), turn `A0` (resp. `B0`) at `P2`, and the side `P0P3` the rotation by `A0 + pi`
-- of `P0P1`, the telescoping identity `(P1-P0) + (P2-P1) + (P3-P2) + (P0-P3) = 0` read in real and imaginary parts is literally `RingQuadA A0 B0 gamma` (resp. `RingQuadB`).
-- `quad_turns_contra`: with right turns at `P2`, `P3` no such quadrilateral exists (the total turning would be `2 gamma`, not in `2 pi Z`).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3, Fig. 8), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN110
import Erdos634.Draft.LaczFormalRG12Ring

open scoped Classical Fin.NatCast
open Complex

namespace Erdos634.Draft.LaczFormal.WN

/-- The closure computation. -/
theorem quad_closure {A0 B0 : ℝ} {P0 P1 P2 P3 : ℂ} (hne : P1 ≠ P0) (τ2 : ℝ)
    (h1 : RotPos (P1 - P0) (P2 - P1) (Real.pi - B0)) (h2 : RotPos (P2 - P1) (P3 - P2) τ2)
    (h3 : RotPos (P1 - P0) (P0 - P3) (A0 + Real.pi)) :
    0 < ‖P2 - P1‖ ∧ 0 < ‖P3 - P2‖ ∧ 0 < ‖P0 - P3‖ ∧
      ‖P1 - P0‖ + ‖P2 - P1‖ * Real.cos (Real.pi - B0) + ‖P3 - P2‖ * Real.cos (Real.pi - B0 + τ2) + ‖P0 - P3‖ * Real.cos (A0 + Real.pi) = 0 ∧
      ‖P2 - P1‖ * Real.sin (Real.pi - B0) + ‖P3 - P2‖ * Real.sin (Real.pi - B0 + τ2) + ‖P0 - P3‖ * Real.sin (A0 + Real.pi) = 0 := by
  have hu : P1 - P0 ≠ 0 := sub_ne_zero.2 hne
  have hL : 0 < ‖P1 - P0‖ := norm_pos_iff.2 hu
  obtain ⟨c1, hc1, e1⟩ := h1
  obtain ⟨c2, hc2, e2⟩ := h2
  obtain ⟨c3, hc3, e3⟩ := h3
  set u := P1 - P0 with hu_def
  set E1 := Complex.exp (((Real.pi - B0 : ℝ) : ℂ) * Complex.I) with hE1
  set E2 := Complex.exp (((Real.pi - B0 + τ2 : ℝ) : ℂ) * Complex.I) with hE2
  set E3 := Complex.exp (((A0 + Real.pi : ℝ) : ℂ) * Complex.I) with hE3
  have hE1n : ‖E1‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hE2n : ‖E2‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hE3n : ‖E3‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have e2' : P3 - P2 = ((c2 * c1 : ℝ) : ℂ) * (E2 * u) := by
    rw [e2, e1]
    have : E2 = Complex.exp ((τ2 : ℂ) * Complex.I) * E1 := by
      rw [hE2, hE1, ← Complex.exp_add]; congr 1; push_cast; ring
    rw [this]; push_cast; ring
  have n1 : ‖P2 - P1‖ = c1 * ‖u‖ := by
    rw [e1, norm_mul, norm_mul, hE1n, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc1]; ring
  have n2 : ‖P3 - P2‖ = (c2 * c1) * ‖u‖ := by
    rw [e2', norm_mul, norm_mul, hE2n, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos hc2 hc1)]; ring
  have n3 : ‖P0 - P3‖ = c3 * ‖u‖ := by
    rw [e3, norm_mul, norm_mul, hE3n, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc3]; ring
  have hbr : (1 : ℂ) + (c1 : ℂ) * E1 + ((c2 * c1 : ℝ) : ℂ) * E2 + (c3 : ℂ) * E3 = 0 := by
    have h0 : u * ((1 : ℂ) + (c1 : ℂ) * E1 + ((c2 * c1 : ℝ) : ℂ) * E2 + (c3 : ℂ) * E3) = (P1 - P0) + (P2 - P1) + (P3 - P2) + (P0 - P3) := by
      rw [e1, e2', e3]; ring
    have : (P1 - P0) + (P2 - P1) + (P3 - P2) + (P0 - P3) = 0 := by ring
    exact (mul_eq_zero.1 (h0.trans this)).resolve_left hu
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [n1]; positivity
  · rw [n2]; positivity
  · rw [n3]; positivity
  · have h := congrArg Complex.re hbr
    have hL' : ((‖u‖ : ℝ) : ℂ) * ((1 : ℂ) + (c1 : ℂ) * E1 + ((c2 * c1 : ℝ) : ℂ) * E2 + (c3 : ℂ) * E3) = 0 := by rw [hbr]; ring
    have h2 := congrArg Complex.re hL'
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im, Complex.add_im, Complex.mul_im,
      hE1, hE2, hE3, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero, add_zero, Complex.zero_re] at h2
    rw [n1, n2, n3]
    nlinarith [h2]
  · have hL' : ((‖u‖ : ℝ) : ℂ) * ((1 : ℂ) + (c1 : ℂ) * E1 + ((c2 * c1 : ℝ) : ℂ) * E2 + (c3 : ℂ) * E3) = 0 := by rw [hbr]; ring
    have h2 := congrArg Complex.im hL'
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im, Complex.add_im, Complex.mul_im,
      hE1, hE2, hE3, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero, add_zero, Complex.zero_im] at h2
    rw [n1, n2, n3]
    nlinarith [h2]

theorem ringA_of_rot {A0 B0 γ : ℝ} (hs : A0 + B0 + γ = Real.pi) {P0 P1 P2 P3 : ℂ} (hne : P1 ≠ P0)
    (h1 : RotPos (P1 - P0) (P2 - P1) (Real.pi - B0)) (h2 : RotPos (P2 - P1) (P3 - P2) A0)
    (h3 : RotPos (P1 - P0) (P0 - P3) (A0 + Real.pi)) :
    RG.RingQuadA A0 B0 γ ‖P1 - P0‖ ‖P2 - P1‖ ‖P3 - P2‖ ‖P0 - P3‖ := by
  obtain ⟨hx, hm, hy, hre, him⟩ := quad_closure hne A0 h1 h2 h3
  have hA : A0 = Real.pi - B0 - γ := by linarith
  subst hA
  have c1 : Real.cos (Real.pi - B0) = -Real.cos B0 := Real.cos_pi_sub B0
  have c2 : Real.cos (Real.pi - B0 + (Real.pi - B0 - γ)) = Real.cos (γ + 2 * B0) := by
    rw [show Real.pi - B0 + (Real.pi - B0 - γ) = 2 * Real.pi - (γ + 2 * B0) by ring, Real.cos_two_pi_sub]
  have c3 : Real.cos (Real.pi - B0 - γ + Real.pi) = Real.cos (γ + B0) := by
    rw [show Real.pi - B0 - γ + Real.pi = 2 * Real.pi - (γ + B0) by ring, Real.cos_two_pi_sub]
  have s1 : Real.sin (Real.pi - B0) = Real.sin B0 := Real.sin_pi_sub B0
  have s2 : Real.sin (Real.pi - B0 + (Real.pi - B0 - γ)) = -Real.sin (γ + 2 * B0) := by
    rw [show Real.pi - B0 + (Real.pi - B0 - γ) = 2 * Real.pi - (γ + 2 * B0) by ring, Real.sin_two_pi_sub]
  have s3 : Real.sin (Real.pi - B0 - γ + Real.pi) = -Real.sin (γ + B0) := by
    rw [show Real.pi - B0 - γ + Real.pi = 2 * Real.pi - (γ + B0) by ring, Real.sin_two_pi_sub]
  rw [c1, c2, c3] at hre
  rw [s1, s2, s3] at him
  refine ⟨norm_pos_iff.2 (sub_ne_zero.2 hne), hx, hm, hy, ?_, ?_⟩
  · linarith
  · linarith

theorem ringB_of_rot {A0 B0 γ : ℝ} (hs : A0 + B0 + γ = Real.pi) {P0 P1 P2 P3 : ℂ} (hne : P1 ≠ P0)
    (h1 : RotPos (P1 - P0) (P2 - P1) (Real.pi - B0)) (h2 : RotPos (P2 - P1) (P3 - P2) B0)
    (h3 : RotPos (P1 - P0) (P0 - P3) (A0 + Real.pi)) :
    RG.RingQuadB A0 B0 γ ‖P1 - P0‖ ‖P2 - P1‖ ‖P3 - P2‖ ‖P0 - P3‖ := by
  obtain ⟨hx, hm, hy, hre, him⟩ := quad_closure hne B0 h1 h2 h3
  have hA : A0 = Real.pi - B0 - γ := by linarith
  subst hA
  have c1 : Real.cos (Real.pi - B0) = -Real.cos B0 := Real.cos_pi_sub B0
  have c2 : Real.cos (Real.pi - B0 + B0) = -1 := by rw [show Real.pi - B0 + B0 = Real.pi by ring, Real.cos_pi]
  have c3 : Real.cos (Real.pi - B0 - γ + Real.pi) = Real.cos (γ + B0) := by
    rw [show Real.pi - B0 - γ + Real.pi = 2 * Real.pi - (γ + B0) by ring, Real.cos_two_pi_sub]
  have s1 : Real.sin (Real.pi - B0) = Real.sin B0 := Real.sin_pi_sub B0
  have s2 : Real.sin (Real.pi - B0 + B0) = 0 := by rw [show Real.pi - B0 + B0 = Real.pi by ring, Real.sin_pi]
  have s3 : Real.sin (Real.pi - B0 - γ + Real.pi) = -Real.sin (γ + B0) := by
    rw [show Real.pi - B0 - γ + Real.pi = 2 * Real.pi - (γ + B0) by ring, Real.sin_two_pi_sub]
  rw [c1, c2, c3] at hre
  rw [s1, s2, s3] at him
  refine ⟨norm_pos_iff.2 (sub_ne_zero.2 hne), hx, hm, hy, ?_, ?_⟩
  · linarith
  · linarith

/-- No quadrilateral has the two `W`-turns `-A0`, `-B0` (right turns): the total turning would be `2 gamma`. -/
theorem quad_turns_contra {A0 B0 γ : ℝ} (hs : A0 + B0 + γ = Real.pi) (hγ : 0 < γ) (hA : 0 < A0) (hB : 0 < B0) {P0 P1 P2 P3 : ℂ} (hne : P1 ≠ P0)
    {τ2 τ3 : ℝ} (hτ : τ2 + τ3 = -(A0 + B0))
    (h1 : RotPos (P1 - P0) (P2 - P1) (Real.pi - B0)) (h2 : RotPos (P2 - P1) (P3 - P2) τ2) (h3 : RotPos (P3 - P2) (P0 - P3) τ3)
    (h4 : RotPos (P1 - P0) (P0 - P3) (A0 + Real.pi)) : False := by
  have hu : P1 - P0 ≠ 0 := sub_ne_zero.2 hne
  have h123 : RotPos (P1 - P0) (P0 - P3) (Real.pi - B0 + τ2 + τ3) := (h1.trans h2).trans h3
  obtain ⟨n, hn⟩ := RotPos.unique hu h123 h4
  have : A0 + B0 = Real.pi * n := by
    have hpi := Real.pi_pos
    nlinarith
  have hpi := Real.pi_pos
  have h0 : (0 : ℝ) < n := by
    by_contra hneg; push_neg at hneg
    nlinarith
  have h1' : (n : ℝ) < 1 := by
    by_contra hge; push_neg at hge
    nlinarith
  have : (0 : ℤ) < n := by exact_mod_cast h0
  have : n < (1 : ℤ) := by exact_mod_cast h1'
  omega

#print axioms ringA_of_rot
#print axioms ringB_of_rot
#print axioms quad_turns_contra

end Erdos634.Draft.LaczFormal.WN
