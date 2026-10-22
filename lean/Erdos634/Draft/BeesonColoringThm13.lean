import Erdos634.Draft.FluxFRow15Close
import Erdos634.Draft.FluxFRow15AnyLabel

/-!
# Beeson (arXiv 1206.2229v4) Theorem 13 and Theorem 15 (only-if), thin wrappers

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Thm 13 and Thm 15), Laczkovich (DCG 48 (2012)),
Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.

Nothing here is a new proof: the statements are Beeson's, restated in his letters, and follow from
`Row15.setup` (flux character `chi_-` anchored at target vertex 0, law of sines, area) and
`Row15.rational_any_label` (rationality of `s`), both pre-existing.

PROJECT HYPOTHESES, named (not Beeson's): (H1) `alpha not in Q * pi`.  Beeson obtains the linear independence of
`alpha, beta` over `Q` from his Lemma 1 (Laczkovich Thm 5.1, 5.3, for a triangle `ABC` not similar to the tile);
neither is in Lean, so `alpha not in Q * pi` is taken as an explicit hypothesis, as everywhere else in the project.
(H2) The integer `M`.  Beeson defines `M` as the number of black tiles minus white tiles for the 2-colouring of his
Lemma 12.  Here `M` is the integer `S` produced by the flux layer (a signed count of the `N` tiles, `S = N mod 2`,
`S c = (1-s)(2+s) Y`); that it equals Beeson's black-minus-white count is NOT formalized (Lemma 12 is not in Lean).
All equations of Thm 13 / Thm 15 are in terms of this `M`, and `M > 0` is proved (Beeson's `M != 0`).
-/

open scoped Classical

namespace Erdos634.BeesonColoring

open Erdos634.Geometry

variable {N : ℕ}

/-- For a `3 alpha + 2 beta = pi` tile placement, `a = 2 sin(alpha/2) c` and `c > 0` (so `s = a/c = 2 sin(alpha/2)`). -/
theorem model_a_eq {T : Tri} {α β a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (h : T.ThreeAlphaData α β a b c) :
    0 < c ∧ a = 2 * Real.sin (α / 2) * c := by
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  obtain ⟨tγ, tα, -, -⟩ := threeAlpha_sin_table hrel
  have ls1 := T.lawSin (σ 0) (σ 2)
  rw [h0, o2, h2, o0, tα, tγ] at ls1
  have hαpos : 0 < α := h0 ▸ T.angleAt_pos' (σ 0)
  have hβpos : 0 < β := h1 ▸ T.angleAt_pos' (σ 1)
  have hπ := Real.pi_pos
  have hco : 0 < Real.cos (α / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hc : 0 < c := o2 ▸ T.oppLen_pos (σ 2)
  exact ⟨hc, mul_left_cancel₀ hco.ne' (by linear_combination (-1 : ℝ) * ls1)⟩

/-- **Beeson Theorem 13** (UNAUDITED; hypotheses (H1), (H2) of the module header).
`3 alpha + 2 beta = pi`, `ABC` (target vertices `0, 1, 2`) has angles `(2 alpha, alpha, 2 beta)` and is `N`-tiled by a
tile with angles `(alpha, beta, gamma)` and opposite sides `(a, b, c)` (any vertex order).  With `s = a/c`
(`= 2 sin(alpha/2)`): `s` is rational, `b = (1 - s^2) c`, and there is an integer `M > 0` with
`N / M^2 = (2 - s^2)(3 - s^2) / ((1 - s)^2 (2 + s)^2)` (the second tiling equation), also given cleared. -/
theorem thm13 (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hP0 : D.target.angleAt 0 = 2 * α) (hP1 : D.target.angleAt 1 = α)
    (hP2 : D.target.angleAt 2 = 2 * β) :
    ∃ (M : ℤ) (s : ℚ), 0 < M ∧ (s : ℝ) = a / c ∧ (s : ℝ) = 2 * Real.sin (α / 2) ∧
      b = (1 - (s : ℝ) ^ 2) * c ∧ 0 < s ∧ s < 1 ∧
      (N : ℚ) * ((1 - s) ^ 2 * (2 + s) ^ 2) = (M : ℚ) ^ 2 * ((2 - s ^ 2) * (3 - s ^ 2)) ∧
      (N : ℚ) / (M : ℚ) ^ 2 = (2 - s ^ 2) * (3 - s ^ 2) / ((1 - s) ^ 2 * (2 + s) ^ 2) := by
  obtain ⟨hcpos, haeq⟩ := model_a_eq hrel h
  obtain ⟨s, S, hs0, hs1, hc, ha, hb, -, -, hSc, harea⟩ := Row15.setup D hα hrel h hP0 hP1 hP2
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  have hd01 : σ 0 ≠ σ 1 := fun e => absurd (σ.injective e) (by decide)
  have hd20 : σ 2 ≠ σ 0 := fun e => absurd (σ.injective e) (by decide)
  have hd21 : σ 2 ≠ σ 1 := fun e => absurd (σ.injective e) (by decide)
  obtain ⟨r, hr1, hr2⟩ := Row15.rational_any_label D α β hα hrel hd01 hd20 hd21 h0 h1
    (t₀ := 0) (t₁ := 1) (by decide) hP0 hP1
  rw [o0, o2] at hr1
  have hsr : s = (r : ℝ) := by
    have : s * c = (r : ℝ) * c := ha.symm.trans hr1
    exact mul_right_cancel₀ hc.ne' this
  have hY : 0 < D.target.oppLen 1 := D.target.oppLen_pos 1
  have hSpos : (0 : ℝ) < S := by
    by_contra hn
    push Not at hn
    have := mul_nonpos_of_nonpos_of_nonneg hn hc.le
    have h' : 0 < (1 - s) * (2 + s) * D.target.oppLen 1 :=
      mul_pos (mul_pos (by linarith) (by linarith)) hY
    linarith
  have hq : (N : ℚ) * ((1 - r) ^ 2 * (2 + r) ^ 2) = (S : ℚ) ^ 2 * ((2 - r ^ 2) * (3 - r ^ 2)) := by
    have e : (N : ℝ) * ((1 - (r : ℝ)) ^ 2 * (2 + (r : ℝ)) ^ 2)
        = (S : ℝ) ^ 2 * ((2 - (r : ℝ) ^ 2) * (3 - (r : ℝ) ^ 2)) := by
      rw [hsr] at harea; linear_combination harea
    exact_mod_cast e
  have hr0 : (0 : ℝ) < r := hsr ▸ hs0
  have hr1' : (r : ℝ) < 1 := hsr ▸ hs1
  have hr0q : 0 < r := by exact_mod_cast hr0
  have hr1q : r < 1 := by exact_mod_cast hr1'
  have hSq : (0 : ℚ) < S := by exact_mod_cast hSpos
  have hden : (1 - r) ^ 2 * (2 + r) ^ 2 ≠ 0 := by
    apply mul_ne_zero <;> apply pow_ne_zero <;> linarith
  have hs2 : s = 2 * Real.sin (α / 2) :=
    mul_right_cancel₀ hc.ne' (ha.symm.trans haeq)
  refine ⟨S, r, by exact_mod_cast hSpos, ?_, ?_, ?_, hr0q, hr1q, hq, ?_⟩
  · rw [ha, hsr]; field_simp
  · rw [← hsr]; exact hs2
  · rw [hb, hsr]
  · rw [div_eq_div_iff (pow_ne_zero 2 hSq.ne') hden]
    linear_combination hq

end Erdos634.BeesonColoring

#print axioms Erdos634.BeesonColoring.model_a_eq
#print axioms Erdos634.BeesonColoring.thm13
