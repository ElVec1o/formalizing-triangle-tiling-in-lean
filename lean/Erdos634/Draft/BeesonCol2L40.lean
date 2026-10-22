import Mathlib
import Erdos634.Draft.BeesonRowSect10

/-!
# Beeson-Rosu (arXiv 2607.23453 v2) Lemma 40: the trisector decomposition of the isosceles-beta triangle

NOTE, UNAUDITED.  Credit: Michael Beeson and Rosu (arXiv 2607.23453 v2, Lemma 40), Beeson (arXiv 1206.2229 v4),
Laczkovich, Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.

Printed statement: `ABC` isosceles, base angles `beta` at `A`, `C`, apex `3 alpha` at `B`; `(a,b,c) = (km, k^2-m^2, k^2)` the
tile sides, `|AB| = |CB| = j k c`; `E` on `AC` with `angle ABE = alpha` (trisector nearer `A`).  Then
`|AE| = j k a`, `|BE| = j k b`, `|EC| = j m (b+c)`, `|AC| = j m (b + 2c)`, and `EBC` has angles `2 alpha` at `B`, `beta` at `C`,
`alpha + beta` at `E`.

This is a theorem about points of the Euclidean plane (`EuclideanSpace R (Fin 2)`), not about lengths only.  Hypotheses:
`angle BAC = beta`, `angle BCA = beta`, `E` strictly between `A` and `C`, `angle ABE = alpha`, `|AB| = |CB| = jkc`, and the tile
(`alpha+beta+gamma = pi`, `3 alpha + 2 beta = pi`, law of sines in cross-multiplied form, integer sides).  No tiling used,
as in the printed proof.  Witness: `lemma40_wit_arith` (k,m,j) = (2,1,1), tile (2,3,4).
-/

namespace Erdos634.BeesonCol2L40

open Real EuclideanGeometry

theorem lemma40 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {P : Type*} [MetricSpace P] [NormedAddTorsor V P]
    {α β γ a b c k m j : ℝ} {A B C E : P}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hs : α + β + γ = π) (h3 : 3 * α + 2 * β = π)
    (hm : 0 < m) (hmk : m < k) (hj : 0 < j)
    (ha : a = k * m) (hb : b = k ^ 2 - m ^ 2) (hc : c = k ^ 2)
    (la : a * Real.sin γ = c * Real.sin α) (lb : b * Real.sin γ = c * Real.sin β)
    (hA : ∠ B A C = β) (hC : ∠ B C A = β) (hE : Sbtw ℝ A E C) (hB : ∠ A B E = α)
    (hAB : dist A B = j * k * c) (hCB : dist C B = j * k * c) :
    dist A E = j * k * a ∧ dist B E = j * k * b ∧ dist E C = j * m * (b + c) ∧
    dist A C = j * m * (b + 2 * c) ∧
    ∠ E B C = 2 * α ∧ ∠ B C E = β ∧ ∠ B E C = α + β := by
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
  have hABpos : dist A B ≠ 0 := by rw [hAB, hc]; positivity
  have hBA : B ≠ A := fun h => hABpos (by rw [h, dist_self])
  have hCBpos : dist C B ≠ 0 := by rw [hCB, hc]; positivity
  have hBC : B ≠ C := fun h => hCBpos (by rw [h, dist_self])
  -- angles in ABE
  have eA : ∠ B A E = β := by rw [hE.angle_eq_right B]; exact hA
  have eC : ∠ B C E = β := by rw [hE.symm.angle_eq_right B]; exact hC
  have hsum1 := angle_add_angle_add_angle_eq_pi E hBA.symm
  -- sum: ∠ A B E + ∠ B E A + ∠ E A B = π
  have e1 : ∠ B E A = π - α - β := by
    have := hsum1
    rw [eA, angle_comm E B A, hB, angle_comm A E B] at this
    linarith
  have hpi := hE.angle₁₂₃_eq_pi
  have hsup := angle_add_angle_eq_pi_of_angle_eq_pi B hpi
  have e2 : ∠ B E C = α + β := by linarith
  have hsum2 := angle_add_angle_add_angle_eq_pi E hBC.symm
  -- ∠ C B E + ∠ B E C + ∠ E C B = π
  have e3 : ∠ E B C = 2 * α := by
    have := hsum2
    rw [eC, angle_comm C E B, e2] at this
    linarith
  have sBEA : Real.sin (∠ B E A) = Real.sin γ := by
    rw [e1, show π - α - β = γ by linarith]
  have sBEC : Real.sin (∠ B E C) = Real.sin γ := by
    rw [e2, show α + β = π - γ by linarith, Real.sin_pi_sub]
  have ls1 := law_sin B E A
  have ls2 := law_sin A E B
  have ls3 := law_sin B E C
  rw [sBEA, hB, hAB, dist_comm E A] at ls1
  rw [angle_comm A E B, sBEA, eA, dist_comm B A, hAB, dist_comm E B] at ls2
  rw [sBEC, angle_comm C B E, e3, hCB, hs2] at ls3
  have rAE : dist A E = j * k * a := by
    apply mul_right_cancel₀ hsγ.ne'
    rw [mul_comm (dist A E), ls1, hsα]; field_simp
  have rBE : dist B E = j * k * b := by
    apply mul_right_cancel₀ hsγ.ne'
    rw [mul_comm (dist B E), ← dist_comm E B] at *
    rw [ls2, hsβ]; field_simp
  have rEC : dist E C = j * m * (b + c) := by
    apply mul_right_cancel₀ hsγ.ne'
    rw [mul_comm (dist E C), ls3]
    have hkc : c = k ^ 2 := hc
    have : j * m * (b + c) * Real.sin γ * c = j * k * a * (b + c) * Real.sin γ * 1 := by
      rw [ha, hkc]; ring
    field_simp
    rw [ha, hc]; ring
  have rAC : dist A C = j * m * (b + 2 * c) := by
    rw [← hE.wbtw.dist_add_dist, rAE, rEC, ha, hb, hc]; ring
  exact ⟨rAE, rBE, rEC, rAC, e3, eC, e2⟩

/-- Witness: arithmetic of the printed numbers at `(k,m,j) = (2,1,1)`, tile `(2,3,4)`:
`|AB| = |CB| = 8`, `|AE| = 4`, `|BE| = 6`, `|EC| = 7`, `|AC| = 11`. -/
theorem lemma40_wit_arith : (8 : ℝ) = 1 * 2 * 4 ∧ (4 : ℝ) = 1 * 2 * 2 ∧ (6 : ℝ) = 1 * 2 * 3 ∧
    (7 : ℝ) = 1 * 1 * (3 + 4) ∧ (11 : ℝ) = 1 * 1 * (3 + 2 * 4) ∧ (4 : ℝ) + 7 = 11 := by norm_num

end Erdos634.BeesonCol2L40
