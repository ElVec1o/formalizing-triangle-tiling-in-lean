-- Draft/LaczFormalRG12Ring.lean -- Laczkovich (DCG 48 (2012)), proof of Lemma 6.2, the metric step (16)/(17): in a ring of quadrilaterals R_i = V_{i-1} V_i W_i W_{i-1} (Fig. 8 (A) or (B)) with angles
-- alpha, beta at V_{i-1}, V_i, the lengths d_i = |V_i W_i| are strictly monotone in i (increasing if alpha > beta, decreasing if alpha < beta), which contradicts cyclicity.  PURE TRIG, no tiling data.
-- Each quadrilateral is recorded by the CLOSURE of its boundary walk (V_{i-1} -> V_i -> W_i -> W_{i-1} -> V_{i-1}) with exterior (turning) angles pi-alpha, pi-beta, pi-(gamma+beta), pi-(gamma+alpha) (A),
-- resp. pi-alpha, pi-beta, pi-(gamma+alpha), pi-(gamma+beta) (B); real and imaginary part of sum of side vectors = 0.  The mirror chirality gives the same length equations (conjugate).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Lemma 6.2), Beeson, Beeson-Zhang.
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic

namespace Erdos634.Draft.LaczFormal.RG

open Real

/-- Fig. 8 (A): angles alpha (at V_{i-1}), beta (V_i), gamma+beta (W_i), gamma+alpha (W_{i-1}); side lengths L = |V_{i-1}V_i|, x = |V_iW_i|, m = |W_iW_{i-1}|, y = |W_{i-1}V_{i-1}|.
Walk directions 0, pi-beta, -gamma-2beta, -gamma-beta; closure in real and imaginary part. -/
structure RingQuadA (α β γ L x m y : ℝ) : Prop where
  hL : 0 < L
  hx : 0 < x
  hm : 0 < m
  hy : 0 < y
  hre : L - x * cos β + m * cos (γ + 2 * β) + y * cos (γ + β) = 0
  him : x * sin β - m * sin (γ + 2 * β) - y * sin (γ + β) = 0

/-- Fig. 8 (B): angles alpha (V_{i-1}), beta (V_i), gamma+alpha (W_i), gamma+beta (W_{i-1}); then V_{i-1}V_i and W_{i-1}W_i are parallel.
Walk directions 0, pi-beta, pi, -gamma-beta. -/
structure RingQuadB (α β γ L x m y : ℝ) : Prop where
  hL : 0 < L
  hx : 0 < x
  hm : 0 < m
  hy : 0 < y
  hre : L - x * cos β - m + y * cos (γ + β) = 0
  him : x * sin β - y * sin (γ + β) = 0

lemma sign_facts {α β γ : ℝ} (hs : α + β + γ = π) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) :
    (β < α → 0 < sin (α - β) ∧ 0 < sin α - sin β) ∧ (α < β → sin (α - β) < 0 ∧ sin α - sin β < 0) := by
  have hc : 0 < cos ((α + β) / 2) := by
    apply cos_pos_of_mem_Ioo; constructor <;> linarith
  rw [sin_sub_sin]
  constructor
  · intro h
    refine ⟨sin_pos_of_pos_of_lt_pi (by linarith) (by linarith), ?_⟩
    have : 0 < sin ((α - β) / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    positivity
  · intro h
    refine ⟨?_, ?_⟩
    · have := sin_pos_of_pos_of_lt_pi (x := β - α) (by linarith) (by linarith)
      rw [show α - β = -(β - α) by ring, sin_neg]; linarith
    · have h1 : 0 < sin ((β - α) / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      have : sin ((α - β) / 2) = - sin ((β - α) / 2) := by
        rw [← sin_neg]; congr 1; ring
      rw [this]; nlinarith [mul_pos h1 hc]

/-- Key equation of case A: sin(beta)(x - y) = m sin(alpha-beta) + y (sin alpha - sin beta). -/
lemma ringA_key {α β γ L x m y : ℝ} (hs : α + β + γ = π) (h : RingQuadA α β γ L x m y) :
    sin β * (x - y) = m * sin (α - β) + y * (sin α - sin β) := by
  have h1 : γ + 2 * β = π - (α - β) := by linarith
  have h2 : γ + β = π - α := by linarith
  have := h.him
  rw [h1, h2, sin_pi_sub, sin_pi_sub] at this
  linarith

lemma ringB_key {α β γ L x m y : ℝ} (hs : α + β + γ = π) (h : RingQuadB α β γ L x m y) :
    sin β * (x - y) = y * (sin α - sin β) := by
  have h2 : γ + β = π - α := by linarith
  have := h.him
  rw [h2, sin_pi_sub] at this
  linarith

/-- One ring step: x - y has the sign of alpha - beta. -/
theorem ring_step {α β γ L x m y : ℝ} (hs : α + β + γ = π) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hne : α ≠ β) (h : RingQuadA α β γ L x m y ∨ RingQuadB α β γ L x m y) :
    (β < α ∧ y < x) ∨ (α < β ∧ x < y) := by
  have hsb : 0 < sin β := sin_pos_of_pos_of_lt_pi hβ (by linarith)
  obtain ⟨f1, f2⟩ := sign_facts hs hα hβ hγ
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · right; refine ⟨hlt, ?_⟩
    obtain ⟨g1, g2⟩ := f2 hlt
    rcases h with h | h
    · have k := ringA_key hs h
      have := h.hm; have := h.hy
      by_contra hc; push Not at hc
      nlinarith [mul_nonneg hsb.le (sub_nonneg.2 hc), mul_neg_of_pos_of_neg h.hm g1, mul_neg_of_pos_of_neg h.hy g2]
    · have k := ringB_key hs h
      by_contra hc; push Not at hc
      nlinarith [mul_nonneg hsb.le (sub_nonneg.2 hc), mul_neg_of_pos_of_neg h.hy g2]
  · left; refine ⟨hgt, ?_⟩
    obtain ⟨g1, g2⟩ := f1 hgt
    rcases h with h | h
    · have k := ringA_key hs h
      by_contra hc; push Not at hc
      nlinarith [mul_nonneg hsb.le (sub_nonneg.2 hc), mul_pos h.hm g1, mul_pos h.hy g2]
    · have k := ringB_key hs h
      by_contra hc; push Not at hc
      nlinarith [mul_nonneg hsb.le (sub_nonneg.2 hc), mul_pos h.hy g2]

/-- Laczkovich Lemma 6.2, steps (16)/(17): no cyclic ring with alpha != beta.  `d i = |V_i W_i|`, indices in `ZMod N`, `L i, m i` the other side lengths of `R_i`.  -/
theorem ring_monotone {N : ℕ} [NeZero N] {α β γ : ℝ} (hs : α + β + γ = π) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hne : α ≠ β) (d L m : ZMod N → ℝ)
    (hR : ∀ i, RingQuadA α β γ (L i) (d i) (m i) (d (i - 1)) ∨ RingQuadB α β γ (L i) (d i) (m i) (d (i - 1))) :
    False := by
  have hsum : ∑ i : ZMod N, (d i - d (i - 1)) = 0 := by
    rw [Finset.sum_sub_distrib]
    have : ∑ i : ZMod N, d (i - 1) = ∑ i : ZMod N, d i :=
      Fintype.sum_equiv (Equiv.subRight (1 : ZMod N)) _ _ (fun _ => rfl)
    linarith
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have : ∑ i : ZMod N, (d i - d (i - 1)) < 0 :=
      Finset.sum_neg (fun i _ => by
        rcases ring_step hs hα hβ hγ hne (hR i) with ⟨h1, _⟩ | ⟨_, h2⟩
        · linarith
        · linarith) Finset.univ_nonempty
    linarith
  · have : 0 < ∑ i : ZMod N, (d i - d (i - 1)) :=
      Finset.sum_pos (fun i _ => by
        rcases ring_step hs hα hβ hγ hne (hR i) with ⟨_, h1⟩ | ⟨h1, _⟩
        · linarith
        · linarith) Finset.univ_nonempty
    linarith

/-! ### Witnesses -/

/-- Non-vacuity of the structure with alpha != beta: Fig. 8 (B) with alpha = pi/2, beta = pi/3, gamma = pi/6, (L, x, m, y) = (2, 2, 1, sqrt 3). -/
theorem ringB_witness_ne : RingQuadB (π / 2) (π / 3) (π / 6) 2 2 1 (√3) ∧ π / 2 ≠ π / 3 := by
  have h3 : (0 : ℝ) < √3 := by positivity
  refine ⟨⟨by norm_num, by norm_num, by norm_num, h3, ?_, ?_⟩, by intro h; linarith [pi_pos]⟩
  · have : π / 6 + π / 3 = π / 2 := by ring
    rw [this, cos_pi_div_two, cos_pi_div_three]; ring
  · have : π / 6 + π / 3 = π / 2 := by ring
    rw [this, sin_pi_div_two, sin_pi_div_three]; ring

/-- Negative control: with `hne` dropped (alpha = beta = pi/4, gamma = pi/2) the hypotheses of `ring_monotone` ARE satisfiable (constant `d = 1`, `m = 1`, `L = 1 + sqrt 2`, type B),
so the conclusion `False` is not obtained for free; `hne` is what is used. -/
theorem ring_hyp_satisfiable_if_eq (N : ℕ) [NeZero N] :
    ∃ d L m : ZMod N → ℝ, ∀ i, RingQuadB (π / 4) (π / 4) (π / 2) (L i) (d i) (m i) (d (i - 1)) := by
  refine ⟨fun _ => 1, fun _ => 1 + √2, fun _ => 1, fun i => ⟨by positivity, by norm_num, by norm_num, by norm_num, ?_, ?_⟩⟩
  · have : π / 2 + π / 4 = π - π / 4 := by ring
    simp only [this, cos_pi_sub, cos_pi_div_four]; ring
  · have : π / 2 + π / 4 = π - π / 4 := by ring
    simp only [this, sin_pi_sub]; ring

end Erdos634.Draft.LaczFormal.RG

