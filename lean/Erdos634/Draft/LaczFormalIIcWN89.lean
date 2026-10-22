-- Draft/LaczFormalIIcWN89.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3, p. 359), Lemma 6.2, R2: the Gamma_except ray at a CONCAVE vertex of a cycle points into the EXTERIOR, so the winding number vanishes near the vertex along it.
-- `ext_caseA/B`: the turning angle at a vertex whose kite axes satisfy `Z - Y = e^{i(a+b)} (X - Y)` (case A, turn `-(pi - a - b)`) resp. `X - Y = e^{i(a+b)} (Z - Y)` (case B, turn `pi - a - b`).
-- `chord_wind_zero_near`: with `OrientOK p sigma` and `sigma * extAng p k < 0` (concave), a point `Y + rho * w / |w|` has `wind p = 0` for small `rho > 0`, where `w` is the direction of `gexc_start_dir` (WN88, converted to complex form).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN46

open scoped Classical Fin.NatCast
open Complex

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

theorem arg_exp_real_mul_I' {x : ℝ} (hx : x ∈ Set.Ioc (-Real.pi) Real.pi) : Complex.arg (Complex.exp ((x : ℂ) * Complex.I)) = x := by
  rw [Complex.exp_mul_I]
  exact Complex.arg_cos_add_sin_mul_I hx

/-- Case A of `gexc_start_dir`: `Z - Y = e^{i(a+b)} (X - Y)`. -/
theorem ext_caseA (p : Fin n → ℂ) (k : Fin n) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b < Real.pi)
    (hne : p (k - 1) ≠ p k) (h : p (k + 1) - p k = Complex.exp (((a + b : ℝ) : ℂ) * Complex.I) * (p (k - 1) - p k)) :
    extAng p k = a + b - Real.pi := by
  unfold extAng
  have hne' : p k - p (k - 1) ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have e : (p (k + 1) - p k) / (p k - p (k - 1)) = Complex.exp (((a + b - Real.pi : ℝ) : ℂ) * Complex.I) := by
    rw [h]
    have : p (k - 1) - p k = -(p k - p (k - 1)) := by ring
    rw [this, mul_neg, neg_div, mul_div_assoc, div_self hne', mul_one]
    have hθ : (((a + b - Real.pi : ℝ)) : ℂ) = ((a + b : ℝ) : ℂ) - (Real.pi : ℂ) := by push_cast; ring
    rw [hθ, sub_mul, Complex.exp_sub, Complex.exp_pi_mul_I]
    ring
  rw [e]
  exact arg_exp_real_mul_I' ⟨by linarith, by linarith [Real.pi_pos]⟩

/-- Case B of `gexc_start_dir`: `X - Y = e^{i(a+b)} (Z - Y)`. -/
theorem ext_caseB (p : Fin n → ℂ) (k : Fin n) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b < Real.pi)
    (hne : p (k - 1) ≠ p k) (hne2 : p (k + 1) ≠ p k) (h : p (k - 1) - p k = Complex.exp (((a + b : ℝ) : ℂ) * Complex.I) * (p (k + 1) - p k)) :
    extAng p k = Real.pi - (a + b) := by
  unfold extAng
  have hne' : p (k + 1) - p k ≠ 0 := sub_ne_zero.2 hne2
  have hexp : Complex.exp (((a + b : ℝ) : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have e : (p (k + 1) - p k) / (p k - p (k - 1)) = Complex.exp (((Real.pi - (a + b) : ℝ) : ℂ) * Complex.I) := by
    have : p k - p (k - 1) = -(Complex.exp (((a + b : ℝ) : ℂ) * Complex.I) * (p (k + 1) - p k)) := by rw [← h]; ring
    rw [this]
    have hθ : (((Real.pi - (a + b) : ℝ)) : ℂ) = (Real.pi : ℂ) - ((a + b : ℝ) : ℂ) := by push_cast; ring
    rw [hθ, sub_mul, Complex.exp_sub, Complex.exp_pi_mul_I]
    field_simp
  rw [e]
  exact arg_exp_real_mul_I' ⟨by linarith [Real.pi_pos], by linarith⟩

/-- The vertex sector formula at the vertex `p k`, along the direction `theta` from the ray towards `p (k-1)`: winding number `0` if `theta` is in the exterior sector. -/
theorem vertex_wind_zero {p : Fin n → ℂ} {σ : ℝ} (hO : OrientOK p σ) (k : Fin n) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 2 * Real.pi)
    (hΔ : θ ≠ Real.pi + extAng p k) (hcond : ¬ (σ = -1 ↔ θ < Real.pi + extAng p k)) :
    ∃ r > 0, ∀ ρ : ℝ, 0 < ρ → ρ < r → wind p (pt (p k) (edir (p (k - 1)) (p k)) ρ θ) = 0 := by
  obtain ⟨r, hr, Δ, -, -, hΔe, -, hF⟩ := hO.2.2.2 (k - 1)
  have e1 : k - 1 + 1 = k := sub_add_cancel k 1
  rw [e1] at hΔe hF
  refine ⟨r, hr, fun ρ hρ hρr => ?_⟩
  have := hF ρ θ hρ hρr hθ0 hθ1 (by rw [hΔe]; exact hΔ)
  rw [this, if_neg]
  rw [hΔe]; exact hcond

/-- **R2, local exterior statement.** -/
theorem chord_wind_zero_near {p : Fin n → ℂ} {σ : ℝ} (hO : OrientOK p σ) (k : Fin n) (hconc : σ * extAng p k < 0)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b < Real.pi) (hne : p (k - 1) ≠ p k) (hne2 : p (k + 1) ≠ p k)
    {w : ℂ} (hw0 : w ≠ 0)
    (hcase : (p (k + 1) - p k = Complex.exp (((a + b : ℝ) : ℂ) * Complex.I) * (p (k - 1) - p k) ∧
        ∃ c : ℝ, 0 < c ∧ w = (c : ℂ) * (Complex.exp ((b : ℂ) * Complex.I) * (p (k - 1) - p k))) ∨
      (p (k - 1) - p k = Complex.exp (((a + b : ℝ) : ℂ) * Complex.I) * (p (k + 1) - p k) ∧
        ∃ c : ℝ, 0 < c ∧ w = (c : ℂ) * (Complex.exp ((a : ℂ) * Complex.I) * (p (k + 1) - p k)))) :
    ∃ r > 0, ∀ ρ : ℝ, 0 < ρ → ρ < r → wind p (p k + (ρ : ℂ) * (w / (‖w‖ : ℂ))) = 0 := by
  have hpi := Real.pi_pos
  have hσ : σ = 1 ∨ σ = -1 := hO.1.1
  have hXY : ‖p (k - 1) - p k‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hne)
  have hu : edir (p (k - 1)) (p k) = (p (k - 1) - p k) / (‖p (k - 1) - p k‖ : ℂ) := rfl
  have hXYc : (‖p (k - 1) - p k‖ : ℂ) ≠ 0 := by exact_mod_cast hXY
  rcases hcase with ⟨hA, c, hc, hw⟩ | ⟨hB, c, hc, hw⟩
  · have hext := ext_caseA p k ha hb hab hne hA
    have hσ1 : σ = 1 := by
      rcases hσ with h | h
      · exact h
      · exfalso; rw [h, hext] at hconc; nlinarith
    obtain ⟨r, hr, hz⟩ := vertex_wind_zero hO k (θ := b) hb (by linarith) (by rw [hext]; intro h; linarith) (by
      rw [hext, hσ1]; intro h; have := h.2 (by linarith); norm_num at this)
    refine ⟨r, hr, fun ρ hρ hρr => ?_⟩
    have := hz ρ hρ hρr
    convert this using 2
    unfold pt
    rw [hu, hw]
    have hnw : ‖(c : ℂ) * (Complex.exp ((b : ℂ) * Complex.I) * (p (k - 1) - p k))‖ = c * ‖p (k - 1) - p k‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    rw [hnw]
    push_cast
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    field_simp
  · have hext := ext_caseB p k ha hb hab hne hne2 hB
    have hσ1 : σ = -1 := by
      rcases hσ with h | h
      · exfalso; rw [h, hext] at hconc; nlinarith
      · exact h
    obtain ⟨r, hr, hz⟩ := vertex_wind_zero hO k (θ := 2 * Real.pi - b) (by linarith) (by linarith) (by rw [hext]; intro h; linarith) (by
      rw [hext, hσ1]; intro h; have := h.1 rfl; linarith)
    refine ⟨r, hr, fun ρ hρ hρr => ?_⟩
    have := hz ρ hρ hρr
    convert this using 2
    unfold pt
    have hne3 : (p (k + 1) - p k) = Complex.exp (-((a + b : ℝ) : ℂ) * Complex.I) * (p (k - 1) - p k) := by
      rw [hB, ← mul_assoc, ← Complex.exp_add]
      have : -((a + b : ℝ) : ℂ) * Complex.I + ((a + b : ℝ) : ℂ) * Complex.I = 0 := by ring
      rw [this, Complex.exp_zero, one_mul]
    have hw' : w = (c : ℂ) * (Complex.exp (-(b : ℂ) * Complex.I) * (p (k - 1) - p k)) := by
      rw [hw, hne3, ← mul_assoc (Complex.exp ((a : ℂ) * Complex.I)), ← Complex.exp_add]
      congr 3
      push_cast; ring
    have hexp : Complex.exp (((2 * Real.pi - b : ℝ) : ℂ) * Complex.I) = Complex.exp (-(b : ℂ) * Complex.I) := by
      have : (((2 * Real.pi - b : ℝ) : ℂ) * Complex.I) = -(b : ℂ) * Complex.I + (2 * Real.pi : ℝ) * Complex.I := by push_cast; ring
      rw [this, Complex.exp_add]
      have h2 : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
        have := Complex.exp_two_pi_mul_I
        push_cast at this ⊢; exact this
      rw [h2, mul_one]
    rw [hexp, hu, hw']
    have hnw : ‖(c : ℂ) * (Complex.exp (-(b : ℂ) * Complex.I) * (p (k - 1) - p k))‖ = c * ‖p (k - 1) - p k‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc, norm_mul]
      have : ‖Complex.exp (-(b : ℂ) * Complex.I)‖ = 1 := by
        have h' : (-(b : ℂ) * Complex.I) = ((-b : ℝ) : ℂ) * Complex.I := by push_cast; ring
        rw [h', Complex.norm_exp_ofReal_mul_I]
      rw [this, one_mul]
    rw [hnw]
    push_cast
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    field_simp

#print axioms chord_wind_zero_near

end Erdos634.Draft.LaczFormal.WN
