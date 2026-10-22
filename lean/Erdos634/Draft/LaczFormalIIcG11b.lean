-- Draft/LaczFormalIIcG11b.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3 / Thm 2.1 (v), the printed inequality G11: PURE PLANE GEOMETRY, part b.
--  `rho_alg`: rho - 1 = rho * (r e^{i gamma}) for rho = (sin beta / sin (alpha+beta)) e^{i alpha}, r = sin alpha / sin beta, gamma = pi - alpha - beta.
--  `side_dir`: the side vectors of an equiangular left-turning polygon: cv (V(n+1) - V n) = s_n w^n u0.
--  `g11_core`: (the log-spiral argument) for the spoke fan V_0..V_{k-1} -> E and the spoke V_k -> F with s_k = s_0:  either
--  r^(k-1) s_0 <= s_(k-1), or s_0 <= r s_(k-1), or the closed spokes V_(k-1)E and V_kF meet.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3, Fig. 9), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcG11a

open Erdos634.Geometry EuclideanGeometry
open scoped RealInnerProductSpace

namespace Erdos634.Draft.LaczFormal.Thm21

theorem cv_smul (c : ℝ) (x : Plane) : cv (c • x) = (c : ℂ) * cv x := by
  apply Complex.ext <;> simp [cv]

theorem cv_add (x y : Plane) : cv (x + y) = cv x + cv y := by
  apply Complex.ext <;> simp [cv]

set_option maxHeartbeats 3200000 in
theorem rho_alg {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hαβγ : α + β + γ = Real.pi) (hαβ : α + β < Real.pi) :
    (((Real.sin β / Real.sin (α + β) : ℝ) : ℂ) * ⟨Real.cos α, Real.sin α⟩ - 1) =
      (((Real.sin β / Real.sin (α + β) : ℝ) : ℂ) * ⟨Real.cos α, Real.sin α⟩) * (((Real.sin α / Real.sin β : ℝ) : ℂ) * Complex.exp (γ * Complex.I)) := by
  have hsb : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi hβ (by linarith)
  have hS : 0 < Real.sin (α + β) := Real.sin_pos_of_pos_of_lt_pi (by linarith) hαβ
  have hγ : γ = Real.pi - (α + β) := by linarith
  rw [omega_eq, hγ, Real.cos_pi_sub, Real.sin_pi_sub]
  have hsbne : Real.sin β ≠ 0 := hsb.ne'
  set A : ℝ := Real.sin β / Real.sin (α + β) with hAdef
  set B : ℝ := Real.sin α / Real.sin β with hBdef
  have hA : A * Real.sin (α + β) = Real.sin β := by rw [hAdef]; field_simp
  have hAB : A * B * Real.sin (α + β) = Real.sin α := by rw [hAdef, hBdef]; field_simp
  have hSdef : Real.sin (α + β) = Real.sin α * Real.cos β + Real.cos α * Real.sin β := Real.sin_add α β
  have hCdef : Real.cos (α + β) = Real.cos α * Real.cos β - Real.sin α * Real.sin β := Real.cos_add α β
  have hpa : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.one_re]
    apply mul_left_cancel₀ hS.ne'
    have e1 : Real.sin (α + β) * (A * Real.cos α - 1) = Real.cos α * Real.sin β - Real.sin (α + β) := by
      linear_combination (Real.cos α) * hA
    have e2 : Real.sin (α + β) * (A * Real.cos α * (B * (-Real.cos (α + β))) - A * Real.sin α * (B * Real.sin (α + β))) =
        -Real.cos α * Real.cos (α + β) * Real.sin α - Real.sin α ^ 2 * Real.sin (α + β) := by
      linear_combination (-Real.cos α * Real.cos (α + β) - Real.sin α * Real.sin (α + β)) * hAB
    have e3 : Real.cos α * Real.sin β - Real.sin (α + β) =
        -Real.cos α * Real.cos (α + β) * Real.sin α - Real.sin α ^ 2 * Real.sin (α + β) := by
      rw [hSdef, hCdef]
      linear_combination (Real.sin α * Real.cos β) * hpa
    linear_combination e1 - e2 + e3
  · simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im, Complex.one_im]
    apply mul_left_cancel₀ hS.ne'
    have e1 : Real.sin (α + β) * (A * Real.sin α) = Real.sin β * Real.sin α := by
      linear_combination (Real.sin α) * hA
    have e2 : Real.sin (α + β) * (A * Real.cos α * (B * Real.sin (α + β)) + A * Real.sin α * (B * (-Real.cos (α + β)))) =
        Real.sin α * (Real.cos α * Real.sin (α + β) - Real.sin α * Real.cos (α + β)) := by
      linear_combination (Real.cos α * Real.sin (α + β) - Real.sin α * Real.cos (α + β)) * hAB
    have e3 : Real.sin β * Real.sin α = Real.sin α * (Real.cos α * Real.sin (α + β) - Real.sin α * Real.cos (α + β)) := by
      rw [hSdef, hCdef]
      linear_combination (-Real.sin β * Real.sin α) * hpa
    linear_combination e1 - e2 + e3

theorem rho_ne_zero {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hαβ : α + β < Real.pi) :
    (((Real.sin β / Real.sin (α + β) : ℝ) : ℂ) * ⟨Real.cos α, Real.sin α⟩) ≠ 0 := by
  have hsb : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi hβ (by linarith)
  have hS : 0 < Real.sin (α + β) := Real.sin_pos_of_pos_of_lt_pi (by linarith) hαβ
  apply mul_ne_zero
  · exact Complex.ofReal_ne_zero.mpr (div_pos hsb hS).ne'
  · intro h
    have h1 : Real.cos α = 0 := congrArg Complex.re h
    have h2 : Real.sin α = 0 := congrArg Complex.im h
    have := Real.sin_sq_add_cos_sq α
    rw [h1, h2] at this; norm_num at this

set_option maxHeartbeats 3200000 in
theorem side_dir {V : ℕ → Plane} {γ : ℝ} (hγ0 : 0 < γ) (hγpi : γ < Real.pi)
    (hcr : ∀ n, 0 < cross2 (V (n + 1) - V n) (V (n + 2) - V (n + 1)))
    (hang : ∀ n, ∠ (V n) (V (n + 1)) (V (n + 2)) = Real.pi - γ) :
    (∀ n, V n ≠ V (n + 1)) ∧ ∃ u0 : ℂ, u0 ≠ 0 ∧ ∀ n, cv (V (n + 1) - V n) = (dist (V n) (V (n + 1)) : ℂ) * (Complex.exp (γ * Complex.I)) ^ n * u0 := by
  have hne : ∀ n, V n ≠ V (n + 1) := by
    intro n h
    have := hcr n
    have e : V (n + 1) - V n = 0 := by rw [← h]; simp
    rw [e] at this
    simp [cross2] at this
  have hspos : ∀ n, 0 < dist (V n) (V (n + 1)) := fun n => dist_pos.mpr (hne n)
  refine ⟨hne, ?_⟩
  set s : ℕ → ℝ := fun n => dist (V n) (V (n + 1)) with hs
  have hsnorm : ∀ n, ‖V (n + 1) - V n‖ = s n := by
    intro n; simp only [hs]; rw [dist_comm, dist_eq_norm]
  set ω : ℂ := Complex.exp (γ * Complex.I) with hω
  have hturn : ∀ n, cv (V (n + 2) - V (n + 1)) * (s n : ℂ) = (s (n + 1) : ℂ) * ω * cv (V (n + 1) - V n) := by
    intro n
    have := turn_step hγ0 hγpi (hne n) (hne (n + 1)) (hcr n) (hang n)
    rw [hsnorm n] at this
    have h2 : ‖V (n + 2) - V (n + 1)‖ = s (n + 1) := hsnorm (n + 1)
    rw [h2, ← omega_eq] at this
    exact this
  set u0 : ℂ := cv (V 1 - V 0) / (s 0 : ℂ) with hu0
  have hs0c : (s 0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hspos 0).ne'
  have hu0ne : u0 ≠ 0 := by
    simp only [hu0]
    apply div_ne_zero _ hs0c
    intro h
    have h1 := cv_eq_zero h
    apply hne 0
    have : V 1 = V 0 := sub_eq_zero.mp h1
    exact this.symm
  refine ⟨u0, hu0ne, ?_⟩
  intro n
  induction n with
  | zero =>
    show cv (V (0 + 1) - V 0) = (s 0 : ℂ) * ω ^ 0 * u0
    simp only [hu0]; field_simp
  | succ n ih =>
    have h := hturn n
    have hsn : (s n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hspos n).ne'
    rw [ih] at h
    have h' : cv (V (n + 2) - V (n + 1)) * (s n : ℂ) = (s (n + 1) : ℂ) * ω ^ (n + 1) * u0 * (s n : ℂ) := by
      rw [h]; ring
    exact mul_right_cancel₀ hsn h'

end Erdos634.Draft.LaczFormal.Thm21
