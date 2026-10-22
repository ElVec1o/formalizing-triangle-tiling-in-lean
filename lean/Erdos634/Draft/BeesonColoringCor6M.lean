import Erdos634.Draft.BeesonColoringThm15
import Erdos634.Draft.BeesonCor6
import Erdos634.Draft.FluxFRow14AnyLabel
import Erdos634.Draft.FluxGridWitness
import Erdos634.Draft.FluxWitness

/-!
# Beeson (arXiv 1206.2229v4) Cor 6: the colouring parameter `M = L (b + c - a)`; Thm 15 as a package

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Cor 6, Thm 15), Laczkovich (DCG 48 (2012)), Beeson-Zhang.
Hypotheses: (H1) `alpha not in Q * pi` (named; Beeson's Lemma 1 not in Lean), where `alpha = arccos((b+c)/(2c))` is the
angle of the tile `(a,b,c)` opposite `a`; (H2) `M` is the flux integer of `thm15_only_if` (not shown equal to the
black-minus-white count of Beeson's Lemma 12).  Angles of the tile and of the Cor 6 target are derived from the
squared side lengths by the law of cosines (nothing assumed about angles).
-/

open scoped Classical

namespace Erdos634.BeesonColoring.Cor6M

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.FluxGridWitness

/-- the tile `(c, b, a)` with `a^2 + c b = c^2` has angles `(alpha, beta, 2 alpha + beta)`, `3 alpha + 2 beta = pi`,
and `cos alpha = (b + c)/(2c)`. -/
theorem model_angles (T : Tri) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (h : a * a + c * b = c * c)
    (d01 : dist (T.pts 0) (T.pts 1) = c) (d02 : dist (T.pts 0) (T.pts 2) = b)
    (d12 : dist (T.pts 1) (T.pts 2) = a) :
    Real.cos (T.angleAt 0) = ((b : ℝ) + c) / (2 * c) ∧ 3 * T.angleAt 0 + 2 * T.angleAt 1 = Real.pi ∧
      T.ThreeAlphaData (T.angleAt 0) (T.angleAt 1) a b c := by
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0; simp at h; omega
    · exact h0
  have hbc : b < c := by
    by_contra hcon; push Not at hcon
    have : c * c ≤ c * b := Nat.mul_le_mul_left c hcon
    nlinarith
  have hR : (a : ℝ) * a + c * b = c * c := by exact_mod_cast h
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hc' : (0 : ℝ) < c := by exact_mod_cast hcpos
  have hbc' : (b : ℝ) < c := by exact_mod_cast hbc
  have n01 : T.pts 0 ≠ T.pts 1 := ne_of_dist d01 hc'.ne'
  have n02 : T.pts 0 ≠ T.pts 2 := ne_of_dist d02 hb'.ne'
  have n12 : T.pts 1 ≠ T.pts 2 := ne_of_dist d12 ha'.ne'
  have cos0 : Real.cos (T.angleAt 0) = ((b : ℝ) + c) / (2 * c) := by
    unfold Tri.angleAt
    simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl]
    rw [cos_cornerAngle n01.symm n02.symm, dist_comm (T.pts 1) (T.pts 0), dist_comm (T.pts 2) (T.pts 0),
      d01, d02, d12]
    field_simp
    nlinarith [hR]
  have cos2 : Real.cos (T.angleAt 2) = ((b : ℝ) - c) / (2 * a) := by
    unfold Tri.angleAt
    simp only [show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
    rw [cos_cornerAngle n02 n12, d02, d12, d01]
    field_simp
    nlinarith [hR]
  have hγ0 : 0 ≤ T.angleAt 2 := (cornerAngle_mem _ _ _).1
  have hγπ : T.angleAt 2 ≤ Real.pi := (cornerAngle_mem _ _ _).2
  have hα0 : 0 ≤ T.angleAt 0 := (cornerAngle_mem _ _ _).1
  have hαπ : T.angleAt 0 ≤ Real.pi := (cornerAngle_mem _ _ _).2
  have hcneg : Real.cos (T.angleAt 2) < 0 := by
    rw [cos2]; exact div_neg_of_neg_of_pos (by linarith) (by positivity)
  have hγ2 : Real.pi / 2 < T.angleAt 2 := by
    by_contra hcon; push Not at hcon
    have := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) hcon
    linarith
  have hx : Real.cos (2 * T.angleAt 2 - Real.pi) = ((b : ℝ) + c) / (2 * c) := by
    rw [Real.cos_sub_pi, Real.cos_two_mul, cos2]
    have : (a : ℝ) ^ 2 = c * (c - b) := by nlinarith [hR]
    field_simp
    nlinarith [hR]
  have hang : T.angleAt 0 = 2 * T.angleAt 2 - Real.pi :=
    Real.injOn_cos ⟨hα0, hαπ⟩ ⟨by linarith, by linarith⟩ (cos0.trans hx.symm)
  have hsum := T.angleAt_sum
  refine ⟨cos0, by linarith, ?_⟩
  refine ⟨Equiv.refl _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp only [Equiv.refl_apply, Tri.oppLen, show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl]; exact d12
  · rfl
  · simp only [Equiv.refl_apply, Tri.oppLen, show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl]
    rw [dist_comm]; exact d02
  · simp only [Equiv.refl_apply]; linarith
  · simp only [Equiv.refl_apply, Tri.oppLen, show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
    exact d01

/-- the Cor 6 target: with `cos alpha = (b+c)/(2c)`, sides `u c^2, u b (b+2c), u c (b+c)` give angles
`(2 alpha, 2 beta, alpha)` at vertices `(0, 1, 2)`. -/
theorem target_angles (P : Tri) (α β u : ℝ) (b c : ℝ) (hb : 0 < b) (hc : 0 < c) (hu : 0 < u)
    (hcos : Real.cos α = (b + c) / (2 * c)) (hα0 : 0 ≤ α) (hαπ : α ≤ Real.pi)
    (hrel : 3 * α + 2 * β = Real.pi)
    (d01 : dist (P.pts 0) (P.pts 1) = u * c ^ 2) (d02 : dist (P.pts 0) (P.pts 2) = u * b * (b + 2 * c))
    (d12 : dist (P.pts 1) (P.pts 2) = u * c * (b + c)) :
    P.angleAt 0 = 2 * α ∧ P.angleAt 1 = 2 * β ∧ P.angleAt 2 = α := by
  have n01 : P.pts 0 ≠ P.pts 1 := ne_of_dist d01 (by positivity)
  have n02 : P.pts 0 ≠ P.pts 2 := ne_of_dist d02 (by positivity)
  have n12 : P.pts 1 ≠ P.pts 2 := ne_of_dist d12 (by positivity)
  have hαhalf : α ≤ Real.pi / 2 := by
    by_contra hcon; push Not at hcon
    have := Real.cos_neg_of_pi_div_two_lt_of_lt hcon (by linarith)
    rw [hcos] at this
    have : 0 < (b + c) / (2 * c) := by positivity
    linarith
  have a2 : P.angleAt 2 = α := by
    have hc2 : Real.cos (P.angleAt 2) = (b + c) / (2 * c) := by
      unfold Tri.angleAt
      simp only [show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
      rw [cos_cornerAngle n02 n12, d02, d12, d01]
      field_simp
      ring
    exact Real.injOn_cos (cornerAngle_mem _ _ _) ⟨hα0, hαπ⟩ (hc2.trans hcos.symm)
  have a0 : P.angleAt 0 = 2 * α := by
    have hc2 : Real.cos (P.angleAt 0) = Real.cos (2 * α) := by
      rw [Real.cos_two_mul, hcos]
      unfold Tri.angleAt
      simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl]
      rw [cos_cornerAngle n01.symm n02.symm, dist_comm (P.pts 1) (P.pts 0), dist_comm (P.pts 2) (P.pts 0),
        d01, d02, d12]
      field_simp
      ring
    exact Real.injOn_cos (cornerAngle_mem _ _ _) ⟨by linarith, by linarith⟩ hc2
  have hsum := P.angleAt_sum
  exact ⟨a0, by linarith, a2⟩

/-- the swap `1 <-> 2` of target vertices. -/
def swp : Equiv.Perm (Fin 3) := Equiv.swap 1 2
theorem swp0 : swp 0 = 0 := by decide
theorem swp1 : swp 1 = 2 := by decide
theorem swp2 : swp 2 = 1 := by decide

/-- the angle bookkeeping of a Cor 6 tiling: after the swap `1 <-> 2` of target vertices the target has angles
`(2 alpha, alpha, 2 beta)` and the model is the `3 alpha + 2 beta = pi` tile `(a, b, c)` with `alpha = angleAt 0`,
`cos alpha = (b+c)/(2c)`.  No hypothesis on `alpha` beyond the side lengths. -/
theorem cor6_prepare {N : ℕ} (a b c L : ℕ) (ha : 0 < a) (hb : 0 < b) (hL : 0 < L) (h : a * a + c * b = c * c)
    (D : CongruentDissection N)
    (m01 : dist (D.model.pts 0) (D.model.pts 1) ^ 2 = (c : ℝ) ^ 2)
    (m02 : dist (D.model.pts 0) (D.model.pts 2) ^ 2 = (b : ℝ) ^ 2)
    (m12 : dist (D.model.pts 1) (D.model.pts 2) ^ 2 = (a : ℝ) ^ 2)
    (t01 : dist (D.target.pts 0) (D.target.pts 1) ^ 2 = ((L * c ^ 2 : ℕ) : ℝ) ^ 2)
    (t02 : dist (D.target.pts 0) (D.target.pts 2) ^ 2 = ((L * b * (b + 2 * c) : ℕ) : ℝ) ^ 2)
    (t12 : dist (D.target.pts 1) (D.target.pts 2) ^ 2 = ((L * c * (b + c) : ℕ) : ℝ) ^ 2) :
    ∃ D' : CongruentDissection N, D'.model = D.model ∧
      Real.cos (D.model.angleAt 0) = ((b : ℝ) + c) / (2 * c) ∧
      3 * D.model.angleAt 0 + 2 * D.model.angleAt 1 = Real.pi ∧
      D.model.ThreeAlphaData (D.model.angleAt 0) (D.model.angleAt 1) a b c ∧
      D'.target.angleAt 0 = 2 * D.model.angleAt 0 ∧ D'.target.angleAt 1 = D.model.angleAt 0 ∧
      D'.target.angleAt 2 = 2 * D.model.angleAt 1 := by
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0; simp at h; omega
    · exact h0
  have hc' : (0 : ℝ) < c := by exact_mod_cast hcpos
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have dm01 := Erdos634.Draft.FluxWitness.dist_of_sq' (by positivity) m01
  have dm02 := Erdos634.Draft.FluxWitness.dist_of_sq' (by positivity) m02
  have dm12 := Erdos634.Draft.FluxWitness.dist_of_sq' (by positivity) m12
  obtain ⟨hcos, hrel, hdata⟩ := model_angles D.model a b c ha hb h dm01 dm02 dm12
  have dt01 := Erdos634.Draft.FluxWitness.dist_of_sq' (by positivity) t01
  have dt02 := Erdos634.Draft.FluxWitness.dist_of_sq' (by positivity) t02
  have dt12 := Erdos634.Draft.FluxWitness.dist_of_sq' (by positivity) t12
  push_cast at dt01 dt02 dt12
  obtain ⟨e0, e1, e2⟩ := target_angles D.target (D.model.angleAt 0) (D.model.angleAt 1) L b c hb' hc' hL' hcos
    (cornerAngle_mem _ _ _).1 (cornerAngle_mem _ _ _).2 hrel dt01 dt02 dt12
  set D' := D.relabelTarget' swp with hD'
  have hT : ∀ k, D'.target.pts k = D.target.pts (swp k) := fun k => rfl
  refine ⟨D', rfl, hcos, hrel, hdata, ?_, ?_, ?_⟩
  · rw [Row14AnyLabel.angleAt_of_pts swp hT, swp0]; exact e0
  · rw [Row14AnyLabel.angleAt_of_pts swp hT, swp1]; exact e2
  · rw [Row14AnyLabel.angleAt_of_pts swp hT, swp2]; exact e1

/-- **Beeson Cor 6, `M = L (b + c - a)`** (UNAUDITED; (H1), (H2)).  Any `CongruentDissection` of
`N = L^2 (b+c)(b+2c)` tiles with the tile `(c, b, a)` (`a^2 + c b = c^2`) and target with squared sides as in
`cor6_exists` has flux integer `M = L (b + c - a)` (and `0 < M`, `s = a/c = 2 sin(alpha/2)`), provided
`alpha = arccos((b+c)/(2c)) not in Q pi`. -/
theorem cor6_M {N : ℕ} (a b c L : ℕ) (ha : 0 < a) (hb : 0 < b) (hL : 0 < L) (h : a * a + c * b = c * c)
    (hN : N = L * L * ((b + c) * (b + 2 * c)))
    (hα : ¬ ∃ r : ℚ, Real.arccos (((b : ℝ) + c) / (2 * c)) = (r : ℝ) * Real.pi)
    (D : CongruentDissection N)
    (m01 : dist (D.model.pts 0) (D.model.pts 1) ^ 2 = (c : ℝ) ^ 2)
    (m02 : dist (D.model.pts 0) (D.model.pts 2) ^ 2 = (b : ℝ) ^ 2)
    (m12 : dist (D.model.pts 1) (D.model.pts 2) ^ 2 = (a : ℝ) ^ 2)
    (t01 : dist (D.target.pts 0) (D.target.pts 1) ^ 2 = ((L * c ^ 2 : ℕ) : ℝ) ^ 2)
    (t02 : dist (D.target.pts 0) (D.target.pts 2) ^ 2 = ((L * b * (b + 2 * c) : ℕ) : ℝ) ^ 2)
    (t12 : dist (D.target.pts 1) (D.target.pts 2) ^ 2 = ((L * c * (b + c) : ℕ) : ℝ) ^ 2) :
    ∃ M : ℤ, M = (L : ℤ) * (b + c - a) ∧ 0 < M ∧
      (2 * Real.sin (Real.arccos (((b : ℝ) + c) / (2 * c)) / 2) : ℝ) = (a : ℝ) / c := by
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0; simp at h; omega
    · exact h0
  have hac : a < c := by nlinarith
  obtain ⟨D', hD'm, hcos, hrel, hdata, e0, e1, e2⟩ := cor6_prepare a b c L ha hb hL h D m01 m02 m12 t01 t02 t12
  have hα0eq : D.model.angleAt 0 = Real.arccos (((b : ℝ) + c) / (2 * c)) := by
    rw [← hcos]
    exact (Real.arccos_cos (cornerAngle_mem _ _ _).1 (cornerAngle_mem _ _ _).2).symm
  have hα' : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi := by rwa [hα0eq]
  have hdat : D'.model.ThreeAlphaData (D.model.angleAt 0) (D.model.angleAt 1)
      (1 * ((a : ℤ) : ℝ)) (1 * ((b : ℤ) : ℝ)) (1 * ((c : ℤ) : ℝ)) := by
    rw [hD'm]; simpa using hdata
  obtain ⟨-, hs, -, -, M, hM, heq⟩ :=
    Erdos634.BeesonColoring.thm15_only_if D' (a : ℤ) (b : ℤ) (c : ℤ) one_pos hα' hrel hdat e0 e1 e2
  subst hN
  have hmul : ((b : ℤ) + c) * ((b : ℤ) + 2 * c) * (((L : ℤ) * (b + c - a)) ^ 2 - M ^ 2) = 0 := by
    push_cast at heq
    linear_combination heq
  have hsq : ((L : ℤ) * (b + c - a)) ^ 2 = M ^ 2 := by
    have := mul_eq_zero.mp hmul
    rcases this with h1 | h1
    · exact absurd h1 (by positivity)
    · linarith
  have hac' : (a : ℤ) < c := by exact_mod_cast hac
  have hLa : (0 : ℤ) < (L : ℤ) * (b + c - a) := by
    have : (0 : ℤ) < (L : ℤ) := by exact_mod_cast hL
    exact mul_pos this (by linarith)
  have hMeq : M = (L : ℤ) * (b + c - a) := ((sq_eq_sq₀ hM.le hLa.le).mp hsq.symm)
  refine ⟨M, hMeq, hM, ?_⟩
  rw [← hα0eq]
  simpa using hs

end Erdos634.BeesonColoring.Cor6M

#print axioms Erdos634.BeesonColoring.Cor6M.model_angles
#print axioms Erdos634.BeesonColoring.Cor6M.target_angles
#print axioms Erdos634.BeesonColoring.Cor6M.cor6_prepare
#print axioms Erdos634.BeesonColoring.Cor6M.cor6_M
