-- Draft/LaczFormalIIcG11c.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3 / Thm 2.1 (v), the printed inequality G11: PURE PLANE GEOMETRY, part c, `g11_core`.
-- Setting (k = m+1): an equiangular left-turning polygon chain V_0..V_{k+1} (angles pi - gamma, k gamma = pi), spokes V_n E (n <= k-1) with angle alpha at the start and beta at the end of each side
-- (E strictly left of the sides V_n V_{n+1}, n+1 < k), the spoke V_k F (F strictly left of V_k V_{k+1}, same angles), and s_k = s_0.  Then  (log spiral V_n - E = (V_0 - E) u^n, u = r e^{i gamma}, r = sin alpha / sin beta;
-- F - V_k = V_0 - E from s_k = s_0, e^{i k gamma} = -1)  either  r^(k-1) s_0 <= s_(k-1),  or  s_0 <= r s_(k-1),  or the closed spokes V_(k-1) E and V_k F meet.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3, Fig. 9), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcG11b

open Erdos634.Geometry EuclideanGeometry
open scoped RealInnerProductSpace

namespace Erdos634.Draft.LaczFormal.Thm21

set_option maxHeartbeats 12800000 in
theorem g11_core {m : ℕ} (hm : 2 ≤ m) (V : ℕ → Plane) (E F : Plane) (α β γ : ℝ)
    (hcr : ∀ n, 0 < cross2 (V (n + 1) - V n) (V (n + 2) - V (n + 1)))
    (hang : ∀ n, ∠ (V n) (V (n + 1)) (V (n + 2)) = Real.pi - γ)
    (hα : 0 < α) (hβ : 0 < β) (hαβγ : α + β + γ = Real.pi) (hγ0 : 0 < γ) (hkγ : ((m + 1 : ℕ) : ℝ) * γ = Real.pi)
    (hEa : ∀ n, n < m + 1 → ∠ (V (n + 1)) (V n) E = α) (hEb : ∀ n, n + 1 < m + 1 → ∠ (V n) (V (n + 1)) E = β)
    (hEl : ∀ n, n + 1 < m + 1 → 0 < cross2 (V (n + 1) - V n) (E - V n))
    (hFa : ∠ (V (m + 2)) (V (m + 1)) F = α) (hFb : ∠ (V (m + 1)) (V (m + 2)) F = β)
    (hFl : 0 < cross2 (V (m + 2) - V (m + 1)) (F - V (m + 1)))
    (hsym : dist (V (m + 1)) (V (m + 1 + 1)) = dist (V 0) (V (0 + 1))) :
    (Real.sin α / Real.sin β) ^ m * dist (V 0) (V (0 + 1)) ≤ dist (V m) (V (m + 1)) ∨
      dist (V 0) (V (0 + 1)) ≤ (Real.sin α / Real.sin β) * dist (V m) (V (m + 1)) ∨
      ∃ X, X ∈ segment ℝ (V m) E ∧ X ∈ segment ℝ (V (m + 1)) F := by
  have hpi := Real.pi_pos
  have hγpi : γ < Real.pi := by linarith
  have hαβ : α + β < Real.pi := by linarith
  obtain ⟨hne, u0, hu0, hB⟩ := side_dir hγ0 hγpi hcr hang
  have hsa : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα (by linarith)
  have hsb : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi hβ (by linarith)
  have hspos : ∀ n, 0 < dist (V n) (V (n + 1)) := fun n => dist_pos.mpr (hne n)
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℂ, ρ = ((Real.sin β / Real.sin (α + β) : ℝ) : ℂ) * ⟨Real.cos α, Real.sin α⟩ := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Real.sin α / Real.sin β := ⟨_, rfl⟩
  obtain ⟨ω, hω⟩ : ∃ ω : ℂ, ω = Complex.exp (γ * Complex.I) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℂ, u = (r : ℂ) * ω := ⟨_, rfl⟩
  have hrpos : 0 < r := by rw [hr]; exact div_pos hsa hsb
  have hρu : ρ - 1 = ρ * u := by
    rw [hρ, hu, hr, hω]; exact rho_alg hα hβ hαβγ hαβ
  have hρ0 : ρ ≠ 0 := by rw [hρ]; exact rho_ne_zero hα hβ hαβ
  have hωk : ω ^ (m + 1) = -1 := by rw [hω]; exact omega_pow_k hkγ
  have hr0c : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hrpos.ne'
  have hs0 : 0 < dist (V 0) (V (0 + 1)) := hspos 0
  obtain ⟨d, hdd⟩ : ∃ d : ℕ → ℂ, d = fun n => cv (V (n + 1) - V n) := ⟨_, rfl⟩
  have hdn : ∀ n, d n = cv (V (n + 1) - V n) := fun n => by rw [hdd]
  have hρE : ∀ n, n + 1 < m + 1 → cv (E - V n) = ρ * d n := by
    intro n hn
    have := rho_tri hα hβ hαβ (hne n) (hEl n hn) (hEa n (by omega)) (hEb n hn)
    rw [hdn, hρ]; exact this
  have hstep : ∀ n, cv (E - V (n + 1)) = cv (E - V n) - d n := by
    intro n
    rw [hdn]; simp only [cv_sub]; ring
  have hdstep : ∀ n, n + 1 < m → d (n + 1) = u * d n := by
    intro n hn
    have h1 := hρE n (by omega)
    have h2 := hρE (n + 1) (by omega)
    rw [hstep, h1] at h2
    apply mul_left_cancel₀ hρ0
    linear_combination (-1 : ℂ) * h2 + (d n) * hρu
  have hdpow : ∀ n, n < m → d n = u ^ n * d 0 := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [hdstep n hn, ih (by omega)]; ring
  have hEk : ∀ n, n < m + 1 → cv (E - V n) = ρ * u ^ n * d 0 := by
    intro n
    induction n with
    | zero => intro _; simpa using hρE 0 (by omega)
    | succ n ih =>
      intro hn
      rw [hstep, ih (by omega), hdpow n (by omega)]
      linear_combination (u ^ n * d 0) * hρu
  -- side directions
  have hdB : ∀ n, d n = (dist (V n) (V (n + 1)) : ℂ) * ω ^ n * u0 := by
    intro n; rw [hdn, hB n, hω]
  have hd0 : d 0 = (dist (V 0) (V (0 + 1)) : ℂ) * u0 := by
    rw [hdB 0]; simp
  have hdm1 : d (m + 1) = - d 0 := by
    rw [hdB (m + 1), hd0, hsym, hωk]; ring
  have hFρ : cv (F - V (m + 1)) = ρ * d (m + 1) := by
    have := rho_tri hα hβ hαβ (hne (m + 1)) hFl hFa hFb
    rw [hdn, hρ]; exact this
  -- t and s
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = dist (V m) (V (m + 1)) / (r ^ m * dist (V 0) (V (0 + 1))) := ⟨_, rfl⟩
  have hs0c : (dist (V 0) (V (0 + 1)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs0.ne'
  have hdmt : d m = (t : ℂ) * (u ^ m * d 0) := by
    rw [hdB m, hd0, hu, mul_pow, ht]
    push_cast
    field_simp
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = t * r ^ (m + 1) := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : Plane, X = V m + t • (E - V m) := ⟨_, rfl⟩
  have hcvX : cv (X - V (m + 1)) = -d m + (t : ℂ) * cv (E - V m) := by
    have : X - V (m + 1) = -(V (m + 1) - V m) + t • (E - V m) := by rw [hX]; abel
    rw [this, cv_add, cv_smul]
    have : cv (-(V (m + 1) - V m)) = - d m := by
      rw [hdn]; apply Complex.ext <;> simp [cv]
    rw [this]
  have hum : u ^ (m + 1) = - (r : ℂ) ^ (m + 1) := by
    rw [hu, mul_pow, hωk]; ring
  have hcv : cv (X - V (m + 1)) = (σ : ℂ) * cv (F - V (m + 1)) := by
    rw [hcvX, hEk m (by omega), hdmt, hFρ, hdm1, hσ]
    push_cast
    have : u ^ (m + 1) = u ^ m * u := pow_succ u m
    linear_combination ((t : ℂ) * u ^ m * d 0) * hρu + ((t : ℂ) * ρ * d 0) * hum + ((t : ℂ) * ρ * d 0) * (0 : ℂ) * hρu + 0 * this
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  rw [← hr] at h1 h2
  have hden : 0 < r ^ m * dist (V 0) (V (0 + 1)) := by positivity
  have htpos : 0 < t := by rw [ht]; exact div_pos (hspos m) hden
  have ht1 : t < 1 := by rw [ht, div_lt_one hden]; exact h1
  have hσeq : σ = r * dist (V m) (V (m + 1)) / dist (V 0) (V (0 + 1)) := by
    rw [hσ, ht]; field_simp; ring
  have hσpos : 0 < σ := by rw [hσ]; positivity
  have hσ1 : σ < 1 := by rw [hσeq, div_lt_one hs0]; exact h2
  refine h3 X ⟨1 - t, t, by linarith, htpos.le, by ring, by rw [hX]; module⟩ ⟨1 - σ, σ, by linarith, hσpos.le, by ring, ?_⟩
  have hz : X - V (m + 1) - σ • (F - V (m + 1)) = 0 := by
    apply cv_eq_zero
    rw [cv_sub, cv_smul, hcv]; ring
  have hXe : X = V (m + 1) + σ • (F - V (m + 1)) := by
    have := sub_eq_zero.mp hz
    rw [← this]; abel
  rw [hXe]; module

end Erdos634.Draft.LaczFormal.Thm21

#print axioms Erdos634.Draft.LaczFormal.Thm21.g11_core
