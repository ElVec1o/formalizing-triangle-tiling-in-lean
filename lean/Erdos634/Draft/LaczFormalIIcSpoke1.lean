-- Draft/LaczFormalIIcSpoke1.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, step 5 (one exceptional point): the similarity chain around the cycle of spoke triangles V_i V_{i+1} E forces alpha = beta.
-- Law of sines in each triangle (Mathlib `EuclideanGeometry.sin_angle_mul_dist_eq_sin_angle_mul_dist`): dist(V_{i+1},E) sin beta = dist(V_i,E) sin alpha; going once round the n-cycle gives (sin beta)^n = (sin alpha)^n, so sin alpha = sin beta, so alpha = beta since alpha + beta < pi.
-- NOTE, UNAUDITED.  Conditional on the SPOKE GEOMETRY (angle alpha at V_i, beta at V_{i+1} in the triangle with apex E, n-periodic), which is the step-3 statement `spokes_angle` and is NOT proved here.
-- Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Mathlib

open EuclideanGeometry

namespace Erdos634.Draft.LaczFormal.RG

/-- The one-point case of Lemma 6.3, algebraic core: an `n`-periodic closed chain of triangles `V i, V (i+1), E` with the same angles `alpha` at `V i` and `beta` at `V (i+1)` has `alpha = beta`. -/
theorem spoke_chain_alpha_eq_beta {n : ℕ} (hn : 0 < n) (V : ℕ → EuclideanSpace ℝ (Fin 2)) (E : EuclideanSpace ℝ (Fin 2)) (α β : ℝ)
    (hper : ∀ i, V (i + n) = V i) (hne : ∀ i, V i ≠ E)
    (hA : ∀ i, ∠ E (V i) (V (i + 1)) = α) (hB : ∀ i, ∠ (V i) (V (i + 1)) E = β)
    (hα : 0 < α) (hβ : 0 < β) (hαβ : α + β < Real.pi) : α = β := by
  have hpi := Real.pi_pos
  have sα : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα (by linarith)
  have sβ : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi hβ (by linarith)
  have step : ∀ i, dist (V (i + 1)) E * Real.sin β = dist (V i) E * Real.sin α := by
    intro i
    have h := EuclideanGeometry.sin_angle_mul_dist_eq_sin_angle_mul_dist (V i) (V (i + 1)) E
    rw [hB i, hA i, dist_comm E (V i)] at h
    linarith
  have chain : ∀ k, dist (V k) E * Real.sin β ^ k = dist (V 0) E * Real.sin α ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc dist (V (k + 1)) E * Real.sin β ^ (k + 1) = (dist (V (k + 1)) E * Real.sin β) * Real.sin β ^ k := by ring
        _ = (dist (V k) E * Real.sin α) * Real.sin β ^ k := by rw [step k]
        _ = Real.sin α * (dist (V k) E * Real.sin β ^ k) := by ring
        _ = dist (V 0) E * Real.sin α ^ (k + 1) := by rw [ih]; ring
  have hn' := chain n
  have hVn : V n = V 0 := by simpa using hper 0
  rw [hVn] at hn'
  have hd : 0 < dist (V 0) E := dist_pos.mpr (hne 0)
  have hpow : Real.sin β ^ n = Real.sin α ^ n := by
    have := mul_left_cancel₀ hd.ne' hn'
    exact this
  have hsin : Real.sin α = Real.sin β := by
    rcases lt_trichotomy (Real.sin α) (Real.sin β) with h | h | h
    · have := pow_lt_pow_left₀ h sα.le hn.ne'
      linarith
    · exact h
    · have := pow_lt_pow_left₀ h sβ.le hn.ne'
      linarith
  obtain ⟨k, hk | hk⟩ := Real.sin_eq_sin_iff.mp hsin
  · have h1 : (-1 : ℝ) < 2 * k ∧ (2 * k : ℝ) < 1 := by
      constructor <;> nlinarith
    have h2 : (-1 : ℤ) < 2 * k ∧ 2 * k < 1 := by exact_mod_cast h1
    have : k = 0 := by omega
    subst this; simpa using hk.symm
  · exfalso
    have h1 : (0 : ℝ) < 2 * k + 1 ∧ (2 * k + 1 : ℝ) < 1 := by
      constructor <;> nlinarith
    have h2 : (0 : ℤ) < 2 * k + 1 ∧ 2 * k + 1 < 1 := by exact_mod_cast h1
    omega

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.spoke_chain_alpha_eq_beta
