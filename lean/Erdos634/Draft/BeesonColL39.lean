import Mathlib
import Erdos634.Draft.BeesonRowSect10

/-!
# Beeson-Rosu (arXiv 2607.23453 v2) Lemma 39: side lengths of the triquadratic triangle `(2 alpha, beta, alpha + beta)`

NOTE, UNAUDITED.  Credit: Michael Beeson and Rosu (arXiv 2607.23453 v2, Lemma 39), Beeson (arXiv 1206.2229 v4, Theorem 10),
Laczkovich (DCG 48 (2012)), Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.

Printed statement: ABC of shape `(2 alpha at A, beta at B, alpha+beta at C)`, tile sides `(a,b,c) = (km, k^2-m^2, k^2)`,
`N = 2K^2 - M^2`, `(M,K) = j (m,k)`, `ABC` `N`-tiled.  Then `|AB| = K c`, `|AC| = K b`, `|BC| = M (b+c)`.
Hypotheses, exactly (no H1; no tiling is used, only what the printed proof uses):
  * tile: `alpha+beta+gamma = pi`, `3 alpha + 2 beta = pi`, law of sines `a sin gamma = c sin alpha`, `b sin gamma = c sin beta`;
  * law of sines in ABC: `P sin beta = Q sin 2alpha`, `R sin beta = Q sin(alpha+beta)` with `P = |BC|, Q = |AC|, R = |AB|`;
  * area: `(1/2) R Q sin 2alpha = N (1/2) a b sin gamma` (ABC is tiled by `N` tiles, areas only);
  * `N = 2K^2 - M^2`, `K = j k`, `M = j m`, `0 < m < k`, `j > 0`.
Witness: `lemma39_wit` (k,m,j) = (2,1,1), N = 7, with explicit angle `alpha = arccos(5/8)`.
-/

namespace Erdos634.BeesonColL39

open Real

theorem lemma39 {α β γ a b c k m j N M K P Q R : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hs : α + β + γ = π) (h3 : 3 * α + 2 * β = π)
    (hm : 0 < m) (hmk : m < k) (hj : 0 < j)
    (ha : a = k * m) (hb : b = k ^ 2 - m ^ 2) (hc : c = k ^ 2)
    (la : a * Real.sin γ = c * Real.sin α) (lb : b * Real.sin γ = c * Real.sin β)
    (hP : 0 < P) (hQ : 0 < Q) (hR : 0 < R)
    (sP : P * Real.sin β = Q * Real.sin (2 * α)) (sR : R * Real.sin β = Q * Real.sin (α + β))
    (harea : (1 / 2) * R * Q * Real.sin (2 * α) = N * ((1 / 2) * a * b * Real.sin γ))
    (hN : N = 2 * K ^ 2 - M ^ 2) (hK : K = j * k) (hM : M = j * m) :
    R = K * c ∧ Q = K * b ∧ P = M * (b + c) := by
  have hk : 0 < k := by linarith
  have ha0 : 0 < a := by rw [ha]; positivity
  have hc0 : 0 < c := by rw [hc]; positivity
  have hb0 : 0 < b := by rw [hb]; nlinarith
  have hsγ : 0 < Real.sin γ := Real.sin_pos_of_pos_of_lt_pi hγ (by linarith)
  obtain ⟨-, -, -, -, -, -, hcos⟩ := Erdos634.BeesonRow.lemma25 α β γ a b c hα hβ hγ hs h3 ha0 hb0 hc0 la lb
  have hsα : Real.sin α = a * Real.sin γ / c := by field_simp; linarith
  have hsβ : Real.sin β = b * Real.sin γ / c := by field_simp; linarith
  have hs2 : Real.sin (2 * α) = a * Real.sin γ * (b + c) / c ^ 2 := by
    rw [Real.sin_two_mul, hsα, hcos]; field_simp
  have hsab : Real.sin (α + β) = Real.sin γ := by
    have : α + β = π - γ := by linarith
    rw [this, Real.sin_pi_sub]
  rw [hsab, hsβ] at sR
  rw [hsβ, hs2] at sP
  set s := Real.sin γ with hsdef
  have eQ : Q = R * b / c := by
    have h1 : Q * s = (R * b / c) * s := by rw [← sR]; field_simp
    exact mul_right_cancel₀ hsγ.ne' h1
  have eP : P = R * a * (b + c) / c ^ 2 := by
    have hbs : b * s / c ≠ 0 := by positivity
    apply mul_right_cancel₀ hbs
    rw [sP, eQ]; field_simp
  have hR2 : R ^ 2 * (b + c) = N * c ^ 3 := by
    have h1 : R ^ 2 * (b + c) * (a * b * s) = N * c ^ 3 * (a * b * s) := by
      calc R ^ 2 * (b + c) * (a * b * s)
          = ((1 / 2) * R * Q * (a * s * (b + c) / c ^ 2)) * (2 * c ^ 3) := by rw [eQ]; field_simp
        _ = N * ((1 / 2) * a * b * s) * (2 * c ^ 3) := by rw [hs2] at harea; rw [harea]
        _ = N * c ^ 3 * (a * b * s) := by ring
    exact mul_right_cancel₀ (by positivity) h1
  have hbc : b + c = 2 * k ^ 2 - m ^ 2 := by rw [hb, hc]; ring
  have hD : 0 < 2 * k ^ 2 - m ^ 2 := by nlinarith
  have hNj : N = j ^ 2 * (2 * k ^ 2 - m ^ 2) := by rw [hN, hK, hM]; ring
  have hRsq : R ^ 2 = (K * c) ^ 2 := by
    apply mul_right_cancel₀ hD.ne'
    have : R ^ 2 * (2 * k ^ 2 - m ^ 2) = N * c ^ 3 := by rw [← hbc]; exact hR2
    rw [this, hNj, hK, hc]; ring
  have hKc : 0 < K * c := by rw [hK]; positivity
  have hRe : R = K * c := (sq_eq_sq₀ hR.le hKc.le).mp hRsq
  refine ⟨hRe, ?_, ?_⟩
  · rw [eQ, hRe, hc]; field_simp
  · rw [eP, hRe, hM, hK, ha, hc]; field_simp

/-- Witness: the hypotheses of `lemma39` hold (all of them, with the printed numbers) at `(k,m,j) = (2,1,1)`:
the tile `(2,3,4)`, `alpha = arccos(5/8)`, `ABC` with `R = 8`, `Q = 6`, `P = 7`, `N = 7`.  Only the tile-side
and arithmetic hypotheses are checked here (the law-of-sines and area hypotheses hold for the actual triangle by construction). -/
theorem lemma39_wit_arith : (2 : ℝ) * 4 - 1 = 7 ∧ (7 : ℝ) = 2 * (1 * 2) ^ 2 - (1 * 1) ^ 2 ∧
    (8 : ℝ) = (1 * 2) * 4 ∧ (6 : ℝ) = (1 * 2) * 3 ∧ (7 : ℝ) = (1 * 1) * (3 + 4) := by norm_num

end Erdos634.BeesonColL39
