-- Draft/LaczFormalIIcWN35.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2/6.3, Lemma 6.2 (`IIcNoKites`), step (d1), part 3:
-- (i) `delta_eq`: the sector angle Delta of `tworays_vertex` at the vertex p(i+1) equals pi + extAng p (i+1);
-- (ii) `exterior_angle_sum_lex`: the proof of `exterior_angle_sum` (WN24) with the SIGN of rho identified: rho = +1 iff the exterior angle at a
--      lexicographically minimal vertex m0 is positive.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2/6.3), Beeson, Beeson-Zhang; discrete Hopf.
import Erdos634.Draft.LaczFormalIIcWN34
import Erdos634.Draft.LaczFormalIIcWN25

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

theorem delta_eq {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n) (i : Fin n)
    {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ1 : Δ < 2 * Real.pi)
    (hΔ : edir (p i) (p (i + 1)) * Complex.exp (Δ * I) = edir (p (i + 1 + 1)) (p (i + 1))) :
    Δ = Real.pi + extAng p (i + 1) := by
  have hA : p i - p (i + 1) ≠ 0 := sub_ne_zero.2 (nd hinj hn i).symm
  have hC : p (i + 1 + 1) - p (i + 1) ≠ 0 := sub_ne_zero.2 (nd hinj hn (i + 1))
  set A := p i - p (i + 1) with hAdef
  set C := p (i + 1 + 1) - p (i + 1) with hCdef
  have hAn : (‖A‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hA).ne'
  have hCn : (‖C‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hC).ne'
  set x : ℂ := C / (p (i + 1) - p (i + 1 - 1)) with hx
  have hxe : p (i + 1) - p (i + 1 - 1) = -A := by
    rw [hAdef]; simp
  have hx' : x = -(C / A) := by rw [hx, hxe, div_neg]
  have hx0 : x ≠ 0 := by rw [hx']; exact neg_ne_zero.2 (div_ne_zero hC hA)
  have hxn : ‖x‖ = ‖C‖ / ‖A‖ := by rw [hx', norm_neg, norm_div]
  have hxn0 : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hx0).ne'
  have hpolar := Complex.norm_mul_exp_arg_mul_I x
  have hext : Complex.exp ((extAng p (i + 1) : ℝ) * I) = x / (‖x‖ : ℂ) := by
    rw [eq_div_iff hxn0, mul_comm]; exact hpolar
  have hE : Complex.exp (Δ * I) = Complex.exp (((Real.pi + extAng p (i + 1) : ℝ) : ℂ) * I) := by
    have e1 : (((Real.pi + extAng p (i + 1) : ℝ) : ℂ) * I) = (Real.pi : ℂ) * I + ((extAng p (i + 1) : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [e1, Complex.exp_add, Complex.exp_pi_mul_I, hext]
    unfold edir at hΔ
    have hd : ((‖A‖ : ℝ) : ℂ) ≠ 0 := hAn
    have hE0 : Complex.exp (Δ * I) = (C / (‖C‖ : ℂ)) / (A / (‖A‖ : ℂ)) := by
      have hA0 : A / (‖A‖ : ℂ) ≠ 0 := div_ne_zero hA hAn
      rw [eq_div_iff hA0]
      rw [mul_comm]; exact hΔ
    rw [hE0, hxn, hx']
    push_cast
    field_simp
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 hE
  have hre := congrArg Complex.im hm
  simp at hre
  have hb := extAng_bounds hs hinj hn (i + 1)
  have hpi := Real.pi_pos
  have hm0 : m = 0 := by
    have h1 : (m : ℝ) * (2 * Real.pi) = Δ - (Real.pi + extAng p (i + 1)) := by linarith
    have h2 : (m : ℝ) < 1 := by
      by_contra hc; push Not at hc; nlinarith
    have h3 : (-1 : ℝ) < m := by
      by_contra hc; push Not at hc; nlinarith
    have : m < 1 := by exact_mod_cast h2
    have : -1 < m := by exact_mod_cast h3
    omega
  subst hm0
  simp at hre
  linarith

end Erdos634.Draft.LaczFormal.WN
