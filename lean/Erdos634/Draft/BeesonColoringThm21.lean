import Erdos634.Draft.BeesonColoringThm13
import Erdos634.Draft.FluxDRow13

/-!
# Beeson (arXiv 1206.2229v4) Theorem 21, Lemma 51, Lemma 53, Corollary 4 (isosceles, base angles `alpha + beta`)

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Lemma 51, Thm 21, Lemma 53, Cor 4), Laczkovich
(DCG 48 (2012)), Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.

The target is the isosceles triangle with base angles `alpha + beta` (target vertices `0, 1`) and vertex angle
`alpha` (target vertex `2`, Beeson's `B`), so `X = oppLen 0 = oppLen 1` (the equal sides `AB, BC`) and
`Y = oppLen 2` (the base `AC`).  Uses `Row13.boundary` (flux, sign pattern `2X - Y`), the law of sines, and the
area (Heron) identity.  Same project hypotheses as `BeesonColoringThm13.lean`: (H1) `alpha not in Q * pi`
(Beeson's Lemma 1 / Laczkovich 5.1, 5.3 not in Lean); (H2) `M` is the flux integer, not shown equal to Beeson's
Lemma 12 black-minus-white count.  `mu` is `M (1 + s)` (Thm 21); Lemma 51 reads `X = mu c`, `Y = mu a`.
-/

open scoped Classical

namespace Erdos634.BeesonColoring

open Erdos634.Geometry

variable {N : ℕ}

/-- `b = (1 - (2 sin(alpha/2))^2) c` for a `3 alpha + 2 beta = pi` tile placement. -/
theorem model_b_eq {T : Tri} {α β a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (h : T.ThreeAlphaData α β a b c) :
    b = (1 - 4 * Real.sin (α / 2) ^ 2) * c := by
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  obtain ⟨tγ, -, tβ, -⟩ := threeAlpha_sin_table hrel
  have ls2 := T.lawSin (σ 1) (σ 2)
  rw [h1, o2, h2, o1, tβ, tγ] at ls2
  have hαpos : 0 < α := h0 ▸ T.angleAt_pos' (σ 0)
  have hβpos : 0 < β := h1 ▸ T.angleAt_pos' (σ 1)
  have hπ := Real.pi_pos
  have hco : 0 < Real.cos (α / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  exact mul_left_cancel₀ hco.ne' (by linear_combination (-1 : ℝ) * ls2)

set_option maxHeartbeats 1000000 in
/-- **Beeson Theorem 21 with Lemma 51 and Lemma 53 and Corollary 4** (UNAUDITED; (H1), (H2)).  Target `ABC` with
angles `(alpha + beta, alpha + beta, alpha)` at target vertices `0, 1, 2`, `N`-tiled by the tile with angles
`(alpha, beta, gamma)` and opposite sides `(a, b, c)`.  Then `s = a/c = 2 sin(alpha/2)` is rational and there is an
integer `M > 0` with
* Thm 21: `N / M^2 = (1 + s)/(1 - s)` (cleared: `N (1 - s) = M^2 (1 + s)`), `s = (N - M^2)/(N + M^2)`;
* Lemma 51 with `mu = M (1 + s)`: `X = mu c` (both equal sides), `Y = mu a`;
* Lemma 53: `mu^2 c = N b` (i.e. `mu^2 = N b / c`);
* Cor 4: `M^2 = N (1 - s)/(1 + s)` and `s = Y / X`. -/
theorem thm21 (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hP0 : D.target.angleAt 0 = α + β) (hP1 : D.target.angleAt 1 = α + β)
    (hP2 : D.target.angleAt 2 = α) :
    ∃ (M : ℤ) (s : ℚ), 0 < M ∧ (s : ℝ) = a / c ∧ (s : ℝ) = 2 * Real.sin (α / 2) ∧
      0 < s ∧ s < 1 ∧ b = (1 - (s : ℝ) ^ 2) * c ∧
      (N : ℚ) * (1 - s) = (M : ℚ) ^ 2 * (1 + s) ∧
      (N : ℚ) / (M : ℚ) ^ 2 = (1 + s) / (1 - s) ∧
      s = ((N : ℚ) - (M : ℚ) ^ 2) / ((N : ℚ) + (M : ℚ) ^ 2) ∧
      D.target.oppLen 0 = (M : ℝ) * (1 + (s : ℝ)) * c ∧
      D.target.oppLen 1 = (M : ℝ) * (1 + (s : ℝ)) * c ∧
      D.target.oppLen 2 = (M : ℝ) * (1 + (s : ℝ)) * a ∧
      ((M : ℝ) * (1 + (s : ℝ))) ^ 2 * c = N * b ∧
      (M : ℚ) ^ 2 = N * ((1 - s) / (1 + s)) ∧
      (s : ℝ) = D.target.oppLen 2 / D.target.oppLen 0 := by
  obtain ⟨hcpos, haeq⟩ := model_a_eq hrel h
  have hbeq := model_b_eq hrel h
  obtain ⟨_, M0, _, _, _, _, _, hMb⟩ := Row13.boundary D hα hrel h hP0 hP1 hP2
  obtain ⟨_, _, _, _, _, r, hr⟩ := Row13.rational D hα hrel h hP0 hP1
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  obtain ⟨tγ, tα, tβ, -⟩ := threeAlpha_sin_table hrel
  have hαpos : 0 < α := h0 ▸ D.model.angleAt_pos' (σ 0)
  have hβpos : 0 < β := h1 ▸ D.model.angleAt_pos' (σ 1)
  have hπ := Real.pi_pos
  have hAB : Real.sin (α + β) = Real.cos (α / 2) := by
    rw [show α + β = Real.pi - (2 * α + β) by linarith, Real.sin_pi_sub, tγ]
  have lt0 := D.target.lawSin 0 2
  have lt1 := D.target.lawSin 1 2
  rw [hP0, hP2, hAB, tα] at lt0
  rw [hP1, hP2, hAB, tα] at lt1
  have hco : 0 < Real.cos (α / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs0 : 0 < Real.sin (α / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hs1 : Real.sin (α / 2) < 1 / 2 := by
    rw [← Real.sin_pi_div_six]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  have hX : 0 < D.target.oppLen 0 := D.target.oppLen_pos 0
  set u := Real.sin (α / 2) with hudef
  set X := D.target.oppLen 0 with hXdef
  set X₁ := D.target.oppLen 1 with hX1def
  set Y := D.target.oppLen 2 with hYdef
  have hY : Y = 2 * u * X := mul_left_cancel₀ hco.ne' (by linear_combination lt0)
  have hY1 : Y = 2 * u * X₁ := mul_left_cancel₀ hco.ne' (by linear_combination lt1)
  have hX1 : X₁ = X :=
    mul_left_cancel₀ (mul_pos two_pos hs0).ne' (by linear_combination hY - hY1)
  set s := 2 * u with hsdef
  have hsp : 0 < s := by linarith
  have hsl : s < 1 := by linarith
  have ha : a = s * c := haeq
  have hb : b = (1 - s ^ 2) * c := by rw [hbeq, hsdef]; ring
  -- area
  have hA := D.abs_detTri_target
  have hsq : Erdos634.AreaDet.detTri D.target ^ 2
      = (N : ℝ) ^ 2 * Erdos634.AreaDet.detTri D.model ^ 2 := by
    rw [← sq_abs (Erdos634.AreaDet.detTri D.target), hA, mul_pow, sq_abs]
  have hT := D.target.four_detTri_sq_symm
  have hMo := D.model.four_detTri_sq_symm
  rw [Tri.sum_pow_perm' D.model 2 σ, Tri.sum_pow_perm' D.model 4 σ, o0, o1, o2] at hMo
  rw [Fin.sum_univ_three, Fin.sum_univ_three, ← hXdef, ← hX1def, ← hYdef, hX1, hY] at hT
  rw [ha, hb] at hMo
  have hG : 0 < s ^ 2 * (4 - s ^ 2) := mul_pos (pow_pos hsp 2) (by nlinarith)
  have key : (s ^ 2 * (4 - s ^ 2)) * ((X ^ 2 - N * c ^ 2 * (1 - s ^ 2))
      * (X ^ 2 + N * c ^ 2 * (1 - s ^ 2))) = 0 := by
    rw [hsdef] at hT hMo ⊢
    linear_combination (-1 : ℝ) * hT + 4 * hsq + (N : ℝ) ^ 2 * hMo
  have hsum : 0 < X ^ 2 + N * c ^ 2 * (1 - s ^ 2) :=
    add_pos_of_pos_of_nonneg (pow_pos hX 2)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg N) (sq_nonneg c)) (by nlinarith))
  have hXsq : X ^ 2 = N * c ^ 2 * (1 - s ^ 2) := by
    rcases mul_eq_zero.mp key with e | e
    · exact absurd e hG.ne'
    · rcases mul_eq_zero.mp e with e' | e'
      · linarith
      · exact absurd e' hsum.ne'
  -- coloring: M0 (a + b + c) = 2X - Y
  rw [hX1, hY, ha, hb] at hMb
  have hXM : X = (M0 : ℝ) * c * (1 + s) := by
    have e : (2 - s) * ((M0 : ℝ) * c * (1 + s) - X) = 0 := by
      rw [hsdef] at hMb ⊢; linear_combination hMb
    have := (mul_eq_zero.mp e).resolve_left (by linarith)
    linarith
  have hM0 : (0 : ℝ) < M0 := by
    by_contra hn
    push Not at hn
    have := mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hn hcpos.le) (by linarith : (0 : ℝ) ≤ 1 + s)
    linarith
  have hmain : (N : ℝ) * (1 - s) = (M0 : ℝ) ^ 2 * (1 + s) := by
    have e : c ^ 2 * (1 + s) * ((M0 : ℝ) ^ 2 * (1 + s) - N * (1 - s)) = 0 := by
      rw [hXM] at hXsq; linear_combination hXsq
    have hne : c ^ 2 * (1 + s) ≠ 0 := (mul_pos (pow_pos hcpos 2) (by linarith)).ne'
    have := (mul_eq_zero.mp e).resolve_left hne
    linarith
  -- rationality: s = r
  have hsr : s = (r : ℝ) := by
    have : s * c = (r : ℝ) * c := ha.symm.trans hr
    exact mul_right_cancel₀ hcpos.ne' this
  have hr0q : (0 : ℚ) < r := by have : (0 : ℝ) < r := hsr ▸ hsp; exact_mod_cast this
  have hr1q : r < 1 := by have : (r : ℝ) < 1 := hsr ▸ hsl; exact_mod_cast this
  have hMq : (0 : ℚ) < M0 := by exact_mod_cast hM0
  have hmq : (N : ℚ) * (1 - r) = (M0 : ℚ) ^ 2 * (1 + r) := by
    have e : (N : ℝ) * (1 - (r : ℝ)) = (M0 : ℝ) ^ 2 * (1 + (r : ℝ)) := by rw [← hsr]; exact hmain
    exact_mod_cast e
  have h1r : (1 - r) ≠ 0 := by linarith
  have h1rp : (1 + r) ≠ 0 := by linarith
  have hM2 : (M0 : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 hMq.ne'
  have hNM : (N : ℚ) + (M0 : ℚ) ^ 2 ≠ 0 := by
    have : (0 : ℚ) < (M0 : ℚ) ^ 2 := by positivity
    have : (0 : ℚ) ≤ N := Nat.cast_nonneg N
    linarith
  refine ⟨M0, r, by exact_mod_cast hM0, ?_, ?_, hr0q, hr1q, ?_, hmq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr]; field_simp
  · rw [← hsr]
  · rw [hbeq, ← hsr, hsdef]; ring
  · rw [div_eq_div_iff hM2 h1r]; linear_combination hmq
  · rw [eq_div_iff hNM]; linear_combination (-1 : ℚ) * hmq
  · rw [← hsr, hXM]; ring
  · rw [hX1, ← hsr, hXM]; ring
  · rw [hY, hXM, ← hsr, ha]; ring
  · rw [← hsr]
    have e : (M0 : ℝ) ^ 2 * (1 + s) * (1 + s) * c = N * (1 - s) * (1 + s) * c := by
      rw [← hmain]
    have hb2 : b = (1 - s ^ 2) * c := hb
    rw [hb2]; linear_combination e
  · rw [eq_comm, mul_div_assoc', div_eq_iff h1rp]
    linear_combination hmq
  · rw [← hsr, hY]; field_simp

end Erdos634.BeesonColoring

#print axioms Erdos634.BeesonColoring.model_b_eq
#print axioms Erdos634.BeesonColoring.thm21
