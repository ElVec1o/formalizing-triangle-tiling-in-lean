import Erdos634.Draft.BeesonColoringCor6M
import Erdos634.Draft.BeesonColoringThm1
import Erdos634.Draft.FDCScaleReduce

/-!
# Beeson (arXiv 1206.2229v4) Cor 6 with `M`, Thm 15 converse with `M`, Cor 7 (iff)

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Cor 6, Thm 15, Cor 7), Laczkovich (DCG 48 (2012)),
Beeson-Zhang.  Hypotheses: (H1) `alpha not in Q * pi` (Beeson's Lemma 1 not in Lean); (H2) `M` is the flux integer of
`thm15_only_if`, not shown equal to the black-minus-white count (Beeson's Lemma 12).  Witnessed at the tile `(2,3,4)`.
-/

open scoped Classical

namespace Erdos634.BeesonColoring.Cor7

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.FluxGridWitness Erdos634.BeesonCor6 Erdos634.BeesonT15Conv
  Erdos634.BeesonColoring.Cor6M Erdos634.Realizable

/-! ## A. Cor 6 with `M = L (b + c - a)` -/

theorem cor6_M_exists (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (h : a * a + c * b = c * c)
    (hg : Nat.gcd (Nat.gcd a b) c = 1)
    (hα : ¬ ∃ r : ℚ, Real.arccos (((b : ℝ) + c) / (2 * c)) = (r : ℝ) * Real.pi) :
    ∃ L : ℕ, 0 < L ∧ ∃ (T : Tri) (E : CongruentDissection (L * L * ((b + c) * (b + 2 * c)))),
      E.model = T ∧ dist (T.pts 0) (T.pts 1) ^ 2 = (c : ℝ) ^ 2 ∧ dist (T.pts 0) (T.pts 2) ^ 2 = (b : ℝ) ^ 2 ∧
      dist (T.pts 1) (T.pts 2) ^ 2 = (a : ℝ) ^ 2 ∧
      dist (E.target.pts 0) (E.target.pts 1) ^ 2 = ((L * c ^ 2 : ℕ) : ℝ) ^ 2 ∧
      dist (E.target.pts 0) (E.target.pts 2) ^ 2 = ((L * b * (b + 2 * c) : ℕ) : ℝ) ^ 2 ∧
      dist (E.target.pts 1) (E.target.pts 2) ^ 2 = ((L * c * (b + c) : ℕ) : ℝ) ^ 2 ∧
      ∃ M : ℤ, M = (L : ℤ) * (b + c - a) ∧ 0 < M := by
  obtain ⟨L, hL, T, E, hE, m01, m02, m12, t01, t02, t12⟩ := cor6_exists a b c ha hb h hg
  obtain ⟨M, hM, hMp, -⟩ := cor6_M a b c L ha hb hL h rfl hα E (by rw [hE]; exact m01)
    (by rw [hE]; exact m02) (by rw [hE]; exact m12) t01 t02 t12
  exact ⟨L, hL, T, E, hE, m01, m02, m12, t01, t02, t12, M, hM, hMp⟩

/-- witness: the tile `(2,3,4)` (`alpha = arccos(7/8) = alpha44 not in Q pi`): `M = 5 L`, `N = 77 L^2`. -/
theorem cor6_M_wit_234 :
    ∃ L : ℕ, 0 < L ∧ ∃ (T : Tri) (E : CongruentDissection (L * L * ((3 + 4) * (3 + 2 * 4)))),
      E.model = T ∧ ∃ M : ℤ, M = (L : ℤ) * (3 + 4 - 2) ∧ 0 < M := by
  have hα : ¬ ∃ r : ℚ, Real.arccos ((((3 : ℕ) : ℝ) + ((4 : ℕ) : ℝ)) / (2 * ((4 : ℕ) : ℝ))) = (r : ℝ) * Real.pi := by
    have h78 : (((3 : ℕ) : ℝ) + ((4 : ℕ) : ℝ)) / (2 * ((4 : ℕ) : ℝ)) = Real.cos α44 := by
      rw [cos_α44]; norm_num
    have h0 : 0 ≤ α44 := (cornerAngle_mem _ _ _).1
    rw [h78, Real.arccos_cos h0 (by linarith [α44_le, Real.pi_pos])]
    exact α44_irr
  obtain ⟨L, hL, T, E, hE, -, -, -, -, -, -, M, hM, hMp⟩ :=
    cor6_M_exists 2 3 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hα
  exact ⟨L, hL, T, E, hE, M, by simpa using hM, hMp⟩

/-! ## B. Thm 15 converse with `M = t j (b + c - a)` -/

/-- **Beeson Thm 15, converse, with `M`** (UNAUDITED; (H1), (H2)).  `c < 2b`: the tiling of `thm15_converse`
(`N = t^2 j^2 (b+c)(b+2c)`, `j = lcm(a,c)/c`) has flux integer `M = t j (b + c - a)`.  Together with
`BeesonColoring.thm15_only_if` this is Beeson's Theorem 15 (only if, converse). -/
theorem thm15_converse_M (a b c t : ℕ) (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) (h : a * a + c * b = c * c)
    (hcb : c < 2 * b)
    (hα : ¬ ∃ r : ℚ, Real.arccos (((b : ℝ) + c) / (2 * c)) = (r : ℝ) * Real.pi) :
    ∃ (T : Tri) (E : CongruentDissection (t * t * ((Nat.lcm a c / c) * (Nat.lcm a c / c) * ((b + c) * (b + 2 * c))))),
      E.model = T ∧
      ∃ M : ℤ, M = ((t * (Nat.lcm a c / c) : ℕ) : ℤ) * (b + c - a) ∧ 0 < M := by
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0; simp at h; omega
    · exact h0
  have hj : 0 < Nat.lcm a c / c :=
    Nat.div_pos (Nat.le_of_dvd (Nat.lcm_pos ha hcpos) (Nat.dvd_lcm_right a c)) hcpos
  obtain ⟨T, E, hE, m01, m02, m12, t01, t02, t12⟩ := thm15_converse a b c t ha hb ht h hcb
  have hN : t * t * ((Nat.lcm a c / c) * (Nat.lcm a c / c) * ((b + c) * (b + 2 * c))) =
      (t * (Nat.lcm a c / c)) * (t * (Nat.lcm a c / c)) * ((b + c) * (b + 2 * c)) := by ring
  obtain ⟨M, hM, hMp, -⟩ := cor6_M a b c (t * (Nat.lcm a c / c)) ha hb (Nat.mul_pos ht hj) h hN hα E
    (by rw [hE]; exact m01) (by rw [hE]; exact m02) (by rw [hE]; exact m12)
    (by simpa [Nat.mul_assoc] using t01) (by simpa [Nat.mul_assoc] using t02) (by simpa [Nat.mul_assoc] using t12)
  exact ⟨T, E, hE, M, hM, hMp⟩

/-- witness: tile `(2,3,4)`, `t = 1` (`j = 1`): `N = 77`, `M = 5`. -/
theorem thm15_converse_M_wit_234 :
    ∃ (T : Tri) (E : CongruentDissection (1 * 1 * ((Nat.lcm 2 4 / 4) * (Nat.lcm 2 4 / 4) * ((3 + 4) * (3 + 2 * 4))))),
      E.model = T ∧ ∃ M : ℤ, M = ((1 * (Nat.lcm 2 4 / 4) : ℕ) : ℤ) * (3 + 4 - 2) ∧ 0 < M := by
  have hα : ¬ ∃ r : ℚ, Real.arccos ((((3 : ℕ) : ℝ) + ((4 : ℕ) : ℝ)) / (2 * ((4 : ℕ) : ℝ))) = (r : ℝ) * Real.pi := by
    have h78 : (((3 : ℕ) : ℝ) + ((4 : ℕ) : ℝ)) / (2 * ((4 : ℕ) : ℝ)) = Real.cos α44 := by
      rw [cos_α44]; norm_num
    have h0 : 0 ≤ α44 := (cornerAngle_mem _ _ _).1
    rw [h78, Real.arccos_cos h0 (by linarith [α44_le, Real.pi_pos])]
    exact α44_irr
  exact thm15_converse_M 2 3 4 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hα

/-! ## C. Cor 7 -/

/-- **Beeson Cor 7, only if** (UNAUDITED; (H1)): if a triangle with angles `(2 alpha, alpha, 2 beta)` is tiled by the
tile (`ThreeAlphaData alpha beta A B C`), then `s = 2 sin(alpha/2)` is rational (Thm 13/15). -/
theorem cor7_only_if {N : ℕ} (D : CongruentDissection N) {α β A B C : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β A B C)
    (hP0 : D.target.angleAt 0 = 2 * α) (hP1 : D.target.angleAt 1 = α) (hP2 : D.target.angleAt 2 = 2 * β) :
    ∃ q : ℚ, 2 * Real.sin (α / 2) = (q : ℝ) := by
  obtain ⟨-, s, -, -, hs, -⟩ := Erdos634.BeesonColoring.thm13 D hα hrel h hP0 hP1 hP2
  exact ⟨s, hs.symm⟩

/-- `ThreeAlphaData` is preserved by `scaleDissection`'s model (sides multiplied by `|r|`, angles unchanged). -/
theorem scale_data {N : ℕ} (D : CongruentDissection N) (p : Plane) (r : ℝ) (hr : r ≠ 0) {α β a b c : ℝ}
    (h : D.model.ThreeAlphaData α β a b c) :
    (scaleDissection p r hr D).model.ThreeAlphaData α β (|r| * a) (|r| * b) (|r| * c) := by
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  refine ⟨σ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Erdos634.Draft.FDCScaleReduce.scale_model_angleAt]; exact h0
  · rw [Erdos634.Draft.FDCScaleReduce.scale_model_oppLen, o0]
  · rw [Erdos634.Draft.FDCScaleReduce.scale_model_angleAt]; exact h1
  · rw [Erdos634.Draft.FDCScaleReduce.scale_model_oppLen, o1]
  · rw [Erdos634.Draft.FDCScaleReduce.scale_model_angleAt]; exact h2
  · rw [Erdos634.Draft.FDCScaleReduce.scale_model_oppLen, o2]

end Erdos634.BeesonColoring.Cor7

#print axioms Erdos634.BeesonColoring.Cor7.cor6_M_exists
#print axioms Erdos634.BeesonColoring.Cor7.cor6_M_wit_234
#print axioms Erdos634.BeesonColoring.Cor7.thm15_converse_M
#print axioms Erdos634.BeesonColoring.Cor7.thm15_converse_M_wit_234
#print axioms Erdos634.BeesonColoring.Cor7.cor7_only_if
#print axioms Erdos634.BeesonColoring.Cor7.scale_data
