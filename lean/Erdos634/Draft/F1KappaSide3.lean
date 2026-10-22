/-
Draft/F1KappaSide3.lean — `F1MaGt1 N` PROVED (for the listed N) from the F1 pair arithmetic + `f1_bk_side`.
Mechanism: the F1 invariants `Ma b = μ(c−a)`, `Mb b = μ(c+a)` (`Ma Mb = N`, `Ma < Mb`, both odd at odd N) give
`c (Mb − Ma) = a (Mb + Ma)` and `μ a = κ b`, `κ = (Mb − Ma)/2`.  The target side opposite the α-corner has length `μ a = κ b`; its
word `P a + Q b + R c = κ b` is `b^κ` because `b/a` is irrational (iff `(Ma+Mb)² + 12N` is not a perfect square: `word_irr`);
a side covered only by b-edges is impossible (`f1_bk_side`: κ γ-corners, κ − 1 junctions).
UNAUDITED.  Formalization debt, NOT /goal progress.  No sorry, no native_decide.
-/
import Erdos634.Draft.F1KappaSide2
import Erdos634.Draft.CompositeF1Gen

open scoped Classical

namespace Erdos634.Draft.F1KappaSide

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.CompositeF1Gen

private lemma c_sq3 (T : Tri) {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
    c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
  obtain ⟨σ, -, ha, -, hb, hγ, hc⟩ := h
  have hl := T.lawCos_perm σ
  rw [ha, hb, hc, hγ,
      show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three] at hl
  linarith

/-- **The F1 pair `(Ma, Mb)` is impossible** when `Mb = Ma + 2κ`, `Ma Mb = N`, `(Ma+Mb)² + 12 N` is not a square and
`Ma² + Mb² ≠ 4 Ma Mb`. -/
theorem f1_pair_false {N : ℕ} (D : CongruentDissection N) {α a b c μ : ℝ}
    (hirr : IrrPi α) (hm : D.model.TwoPiThreeData α a b c) (hF1 : D.target.F1Data α a b c μ)
    (hμ : 0 < μ) (Ma Mb κ : ℕ) (hMa : 0 < Ma) (hκ0 : 0 < κ) (hprod : Ma * Mb = N)
    (hκ : Mb = Ma + 2 * κ) (hns : ¬ IsSquare (((Ma : ℤ) + Mb) ^ 2 + 12 * (N : ℤ)))
    (hne : Ma ^ 2 + Mb ^ 2 ≠ 4 * Ma * Mb)
    (e1 : (Ma : ℝ) * b = μ * (c - a)) (e2 : (Mb : ℝ) * b = μ * (c + a)) : False := by
  obtain ⟨-, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  have hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2 := c_sq3 D.model hm
  have hMaR : (0 : ℝ) < Ma := by exact_mod_cast hMa
  have hκR : (Mb : ℝ) = Ma + 2 * κ := by exact_mod_cast hκ
  -- hcr : c (Mb − Ma) = a (Mb + Ma)
  have hcr : c * ((Mb : ℝ) - Ma) = a * ((Mb : ℝ) + Ma) := by
    have : μ * ((Mb : ℝ) * (c - a) - Ma * (c + a)) = 0 := by
      linear_combination (-(Mb : ℝ)) * e1 + (Ma : ℝ) * e2
    have h0 := (mul_eq_zero.mp this).resolve_left hμ.ne'
    linarith
  -- μ a = κ b
  have hca : (c - a) * κ = a * Ma := by
    have h2 : (c - a) * (2 * κ) = a * (2 * Ma) := by
      linear_combination hcr - (c - a) * hκR
    linear_combination (1 / 2 : ℝ) * h2
  have hμa : μ * a = κ * b := by
    have : (Ma : ℝ) * (κ * b - μ * a) = 0 := by
      linear_combination (κ : ℝ) * e1 + μ * hca
    have h0 := (mul_eq_zero.mp this).resolve_left hMaR.ne'
    linarith
  -- distinctness
  have hbc : b ≠ c := by
    intro h; rw [← h] at hc2; nlinarith [mul_pos ha0 hb0]
  have hac : a ≠ c := by
    intro h
    rw [← h] at hcr
    have : a * (2 * Ma : ℝ) = 0 := by linarith
    nlinarith
  have hba : b ≠ a := by
    intro h
    rw [h] at hc2
    have h3 : c ^ 2 = 3 * a ^ 2 := by linear_combination hc2
    have h4 : ((Mb : ℝ) + Ma) ^ 2 = 3 * ((Mb : ℝ) - Ma) ^ 2 := by
      have : (a * ((Mb : ℝ) + Ma)) ^ 2 = (c * ((Mb : ℝ) - Ma)) ^ 2 := by rw [hcr]
      have ha2 : a ^ 2 ≠ 0 := by positivity
      apply mul_left_cancel₀ ha2
      nlinarith [this, h3]
    apply hne
    have h5 : ((Ma : ℝ) ^ 2 + Mb ^ 2) = 4 * Ma * Mb := by nlinarith [h4]
    exact_mod_cast h5
  -- the side opposite the α corner
  obtain ⟨-, hgrid⟩ := id hF1
  obtain ⟨σ, -, hopp, -, -, -, -⟩ := hgrid
  have e12 : ∀ k : Fin 3, k + 1 + 1 = k + 2 := by decide
  set i : Fin 3 := σ 0 + 1 with hi
  have hi1 : i + 1 = σ 0 + 2 := by rw [hi]; exact e12 _
  have hside : dist (D.target.pts i) (D.target.pts (i + 1)) = (κ : ℝ) * b := by
    rw [hi1, ← hμa, ← hopp]; rfl
  obtain ⟨p, q, r, hdist, hcrit⟩ := side_decomp_j D hm hac hbc hba i
  rw [hside] at hdist
  have hw := word_irr ha0 hb0 hc2 Ma Mb N κ hκ0 hprod hκ hcr hns p q r hdist.symm
  have hall := hcrit hw.1 hw.2
  exact f1_bk_side D hirr hm hF1 hba hbc hac (j := i) (k := κ) hκ0 hside hall

/-- **`F1MaGt1 N` from a finite list of admissible pairs.** -/
theorem f1MaGt1_of_list (N : ℕ)
    (hlist : ∀ Ma Mb : ℕ, 1 < Ma → Ma < Mb → Ma * Mb = N →
      ∃ κ : ℕ, 0 < κ ∧ Mb = Ma + 2 * κ ∧ ¬ IsSquare (((Ma : ℤ) + Mb) ^ 2 + 12 * (N : ℤ)) ∧
        Ma ^ 2 + Mb ^ 2 ≠ 4 * Ma * Mb) : F1MaGt1 N := by
  intro D α a b c μ hirr hm hF1 hμ Ma Mb h1 hp e1 e2
  obtain ⟨-, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  have hcA : a < c := by
    have hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2 := c_sq3 D.model hm
    have h2 : a ^ 2 < c ^ 2 := by nlinarith [mul_pos ha0 hb0]
    by_contra hle
    push Not at hle
    nlinarith [mul_le_mul hle hle hc0.le ha0.le]
  have hlt : Ma < Mb := by
    have : (Ma : ℝ) * b < (Mb : ℝ) * b := by rw [e1, e2]; nlinarith
    have := lt_of_mul_lt_mul_right this hb0.le
    exact_mod_cast this
  obtain ⟨κ, hκ0, hκ, hns, hne⟩ := hlist Ma Mb h1 hlt hp
  exact f1_pair_false D hirr hm hF1 hμ Ma Mb κ (by omega) hκ0 hp hκ hns hne e1 e2

end Erdos634.Draft.F1KappaSide

#print axioms Erdos634.Draft.F1KappaSide.f1_pair_false
#print axioms Erdos634.Draft.F1KappaSide.f1MaGt1_of_list
