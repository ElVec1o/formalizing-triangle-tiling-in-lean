-- Draft/LaczFormalIIcWN93.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3, p. 358-359), Lemma 6.2, R2: an edge of Gamma_except ARRIVES at a CONCAVE vertex of a cycle from the INTERIOR (the gamma-gamma bisector lies in the reflex wedge),
-- so along it the winding number is `sigma <> 0` near the vertex.  Hence an exterior chord (winding number 0) cannot end at a concave vertex: its endpoint is convex.
-- `chord_arrival_wind_ne`: complex-plane form, directions as in `gexc_arrive_dir` (WN92).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN89

open scoped Classical Fin.NatCast
open Complex

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

theorem vertex_wind_int {p : Fin n → ℂ} {σ : ℝ} (hO : OrientOK p σ) (k : Fin n) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 2 * Real.pi)
    (hΔ : θ ≠ Real.pi + extAng p k) (hcond : (σ = -1 ↔ θ < Real.pi + extAng p k)) :
    ∃ r > 0, ∀ ρ : ℝ, 0 < ρ → ρ < r → wind p (pt (p k) (edir (p (k - 1)) (p k)) ρ θ) = σ := by
  obtain ⟨r, hr, Δ, -, -, hΔe, -, hF⟩ := hO.2.2.2 (k - 1)
  have e1 : k - 1 + 1 = k := sub_add_cancel k 1
  rw [e1] at hΔe hF
  refine ⟨r, hr, fun ρ hρ hρr => ?_⟩
  have := hF ρ θ hρ hρr hθ0 hθ1 (by rw [hΔe]; exact hΔ)
  rw [this, if_pos]
  rw [hΔe]; exact hcond

/-- **R2: arrival at a concave vertex is from the interior.** -/
theorem chord_arrival_wind_ne {p : Fin n → ℂ} {σ : ℝ} (hO : OrientOK p σ) (k : Fin n) (hconc : σ * extAng p k < 0)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b < Real.pi) (hne : p (k - 1) ≠ p k) (hne2 : p (k + 1) ≠ p k)
    {w : ℂ} (hw0 : w ≠ 0)
    (hcase : (p (k + 1) - p k = Complex.exp (((a + b : ℝ) : ℂ) * Complex.I) * (p (k - 1) - p k) ∧
        ∃ c : ℝ, 0 < c ∧ w = (c : ℂ) * -(Complex.exp ((a : ℂ) * Complex.I) * (p (k - 1) - p k))) ∨
      (p (k - 1) - p k = Complex.exp (((a + b : ℝ) : ℂ) * Complex.I) * (p (k + 1) - p k) ∧
        ∃ c : ℝ, 0 < c ∧ w = (c : ℂ) * -(Complex.exp ((b : ℂ) * Complex.I) * (p (k + 1) - p k)))) :
    ∃ r > 0, ∀ ρ : ℝ, 0 < ρ → ρ < r → wind p (p k + (ρ : ℂ) * (w / (‖w‖ : ℂ))) = σ := by
  have hpi := Real.pi_pos
  have hσ : σ = 1 ∨ σ = -1 := hO.1.1
  have hXY : ‖p (k - 1) - p k‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hne)
  have hu : edir (p (k - 1)) (p k) = (p (k - 1) - p k) / (‖p (k - 1) - p k‖ : ℂ) := rfl
  have hXYc : (‖p (k - 1) - p k‖ : ℂ) ≠ 0 := by exact_mod_cast hXY
  have hepi : Complex.exp ((Real.pi : ℂ) * Complex.I) = -1 := Complex.exp_pi_mul_I
  rcases hcase with ⟨hA, c, hc, hw⟩ | ⟨hB, c, hc, hw⟩
  · have hext := ext_caseA p k ha hb hab hne hA
    have hσ1 : σ = 1 := by
      rcases hσ with h | h
      · exact h
      · exfalso; rw [h, hext] at hconc; nlinarith
    obtain ⟨r, hr, hz⟩ := vertex_wind_int hO k (θ := Real.pi + a) (by linarith) (by linarith) (by rw [hext]; intro h; linarith) (by
      rw [hext, hσ1]; constructor
      · intro h; norm_num at h
      · intro h; linarith)
    refine ⟨r, hr, fun ρ hρ hρr => ?_⟩
    have := hz ρ hρ hρr
    rw [hσ1] at this ⊢
    convert this using 2
    unfold pt
    rw [hu, hw]
    have hnw : ‖(c : ℂ) * -(Complex.exp ((a : ℂ) * Complex.I) * (p (k - 1) - p k))‖ = c * ‖p (k - 1) - p k‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc, norm_neg, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    rw [hnw]
    have hexp : Complex.exp (((Real.pi + a : ℝ) : ℂ) * Complex.I) = -Complex.exp ((a : ℂ) * Complex.I) := by
      have : (((Real.pi + a : ℝ)) : ℂ) * Complex.I = (Real.pi : ℂ) * Complex.I + (a : ℂ) * Complex.I := by push_cast; ring
      rw [this, Complex.exp_add, hepi]; ring
    rw [hexp]
    push_cast
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    field_simp
  · have hext := ext_caseB p k ha hb hab hne hne2 hB
    have hσ1 : σ = -1 := by
      rcases hσ with h | h
      · exfalso; rw [h, hext] at hconc; nlinarith
      · exact h
    obtain ⟨r, hr, hz⟩ := vertex_wind_int hO k (θ := Real.pi - a) (by linarith) (by linarith) (by rw [hext]; intro h; linarith) (by
      rw [hext, hσ1]; constructor
      · intro _; linarith
      · intro _; rfl)
    refine ⟨r, hr, fun ρ hρ hρr => ?_⟩
    have := hz ρ hρ hρr
    rw [hσ1] at this ⊢
    convert this using 2
    unfold pt
    have hne3 : (p (k + 1) - p k) = Complex.exp (-((a + b : ℝ) : ℂ) * Complex.I) * (p (k - 1) - p k) := by
      rw [hB, ← mul_assoc, ← Complex.exp_add]
      have : -((a + b : ℝ) : ℂ) * Complex.I + ((a + b : ℝ) : ℂ) * Complex.I = 0 := by ring
      rw [this, Complex.exp_zero, one_mul]
    have hw' : w = (c : ℂ) * (Complex.exp (((Real.pi - a : ℝ) : ℂ) * Complex.I) * (p (k - 1) - p k)) := by
      rw [hw, hne3]
      have h1 : Complex.exp (((Real.pi - a : ℝ) : ℂ) * Complex.I) = -Complex.exp (-(a : ℂ) * Complex.I) := by
        have : (((Real.pi - a : ℝ)) : ℂ) * Complex.I = (Real.pi : ℂ) * Complex.I + (-(a : ℂ) * Complex.I) := by push_cast; ring
        rw [this, Complex.exp_add, hepi]; ring
      rw [h1]
      have h2 : Complex.exp ((b : ℂ) * Complex.I) * Complex.exp (-((a + b : ℝ) : ℂ) * Complex.I) = Complex.exp (-(a : ℂ) * Complex.I) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring_nf
      calc (c : ℂ) * -(Complex.exp ((b : ℂ) * Complex.I) * (Complex.exp (-((a + b : ℝ) : ℂ) * Complex.I) * (p (k - 1) - p k)))
          = (c : ℂ) * (-(Complex.exp ((b : ℂ) * Complex.I) * Complex.exp (-((a + b : ℝ) : ℂ) * Complex.I)) * (p (k - 1) - p k)) := by ring
        _ = _ := by rw [h2]
    rw [hu, hw']
    have hnw : ‖(c : ℂ) * (Complex.exp (((Real.pi - a : ℝ) : ℂ) * Complex.I) * (p (k - 1) - p k))‖ = c * ‖p (k - 1) - p k‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    rw [hnw]
    push_cast
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    field_simp

#print axioms chord_arrival_wind_ne

end Erdos634.Draft.LaczFormal.WN
