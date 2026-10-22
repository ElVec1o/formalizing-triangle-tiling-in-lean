import Mathlib
import Erdos634.Draft.BeesonRowSect10

/-!
# Beeson (arXiv 1206.2229 v4), Lemmas 3, 9, 17, 18 and the arithmetic part of Lemma 38 (angle/trig algebra)

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4), Beeson-Zhang, Laczkovich (DCG 48 (2012)).
Formalization debt, not progress on the /goal outcomes.  Map rows T-L3, T-L9, T-L17, T-L18, T-L38 (arithmetic part).
Triangles are given by angles and sides linked through the law of sines in cross-multiplied form (as in `lemma25`).
H1 ("alpha is not a rational multiple of pi") is used only as an explicit hypothesis in `lemma17`, `lemma38_arith`;
it is WITNESSED by `Erdos634.BeesonRow.wit_h1_234`.
-/

namespace Erdos634.BeesonRow2

open Real

/-- Printed Lemma 3 (both directions), in the form `a^2 + c b = c^2` (equivalently `b = c - a^2/c`). -/
theorem lemma3 (α β γ a b c : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hs : α + β + γ = π)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (la : a * Real.sin γ = c * Real.sin α) (lb : b * Real.sin γ = c * Real.sin β) :
    3 * α + 2 * β = π ↔ a ^ 2 + c * b = c ^ 2 := by
  constructor
  · intro h3
    obtain ⟨-, -, -, -, -, h, -⟩ := Erdos634.BeesonRow.lemma25 α β γ a b c hα hβ hγ hs h3 ha hb hc la lb
    nlinarith [h]
  · intro h
    have hsγ : 0 < Real.sin γ := Real.sin_pos_of_pos_of_lt_pi hγ (by linarith)
    have hsβ : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi hβ (by linarith)
    have e1 : c ^ 2 * (Real.sin α ^ 2 + Real.sin β * Real.sin γ) = c ^ 2 * Real.sin γ ^ 2 := by
      have h1 : (a * Real.sin γ) ^ 2 + c * (b * Real.sin γ) * Real.sin γ = c ^ 2 * Real.sin γ ^ 2 := by
        nlinarith [h]
      rw [la, lb] at h1
      nlinarith [h1]
    have e2 : Real.sin α ^ 2 + Real.sin β * Real.sin γ = Real.sin γ ^ 2 := by
      have := mul_left_cancel₀ (pow_pos hc 2).ne' e1
      exact this
    have hβe : β = π - (α + γ) := by linarith
    have sb : Real.sin β = Real.sin α * Real.cos γ + Real.cos α * Real.sin γ := by
      rw [hβe, Real.sin_pi_sub, Real.sin_add]
    have sgα : Real.sin (γ - α) = Real.sin γ * Real.cos α - Real.cos γ * Real.sin α := Real.sin_sub _ _
    have key : Real.sin β * (Real.sin γ - Real.sin (γ - α)) = 0 := by
      rw [sgα, sb]
      have := Real.sin_sq_add_cos_sq α
      have := Real.sin_sq_add_cos_sq γ
      nlinarith [e2, sb]
    have hsg : Real.sin γ = Real.sin (γ - α) := by
      rcases mul_eq_zero.mp key with h0 | h0
      · exact absurd h0 hsβ.ne'
      · linarith
    obtain ⟨k, hk | hk⟩ := Real.sin_eq_sin_iff.mp hsg
    · exfalso
      have hkr : α = -(2 * (k : ℝ) * π) := by linarith
      have h1 : (k : ℝ) < 0 := by
        by_contra hh; push_neg at hh; nlinarith [Real.pi_pos]
      have h2 : -(1 : ℝ) / 2 < k := by
        by_contra hh; push_neg at hh
        nlinarith [Real.pi_pos]
      have h1' : k < 0 := by exact_mod_cast h1
      have h2' : (-1 : ℤ) < 2 * k := by
        have : (-1 : ℝ) < 2 * k := by linarith
        exact_mod_cast this
      omega
    · have hk2 : 2 * γ = α + (2 * k + 1) * π := by linarith
      have h1 : (-1 : ℝ) < 2 * k + 1 := by
        by_contra hh; push_neg at hh; nlinarith [Real.pi_pos]
      have h2 : (2 * k + 1 : ℝ) < 2 := by
        by_contra hh; push_neg at hh; nlinarith [Real.pi_pos]
      have h1' : (-1 : ℤ) < 2 * k + 1 := by exact_mod_cast h1
      have h2' : 2 * k + 1 < (2 : ℤ) := by exact_mod_cast h2
      have hk0 : k = 0 := by omega
      subst hk0
      simp at hk2
      linarith

/-- Printed Lemma 9: `c - b` is not an integer multiple of `a` (from `a^2 + c b = c^2`, `0 < b`). -/
theorem lemma9 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a ^ 2 + c * b = c ^ 2) :
    ¬ ∃ n : ℤ, c - b = (n : ℝ) * a := by
  rintro ⟨n, hn⟩
  have h1 : a = c * n := by
    have : a * (a - c * n) = 0 := by nlinarith [h, hn]
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 ha.ne'
    · linarith
  have hn0 : (0 : ℝ) < n := by
    by_contra hh; push_neg at hh; nlinarith
  have hn1 : (n : ℝ) < 1 := by
    by_contra hh; push_neg at hh; nlinarith
  have a0 : (0 : ℤ) < n := by exact_mod_cast hn0
  have a1 : n < (1 : ℤ) := by exact_mod_cast hn1
  omega

/-- Printed Lemma 17: `delta/pi` is irrational (H1 hypothesis), `delta = alpha + beta`. -/
theorem lemma17 (α β δ : ℝ) (hδ : δ = α + β) (h3 : 3 * α + 2 * β = π)
    (H1 : ¬ ∃ r : ℚ, α = (r : ℝ) * π) : ¬ ∃ r : ℚ, δ = (r : ℝ) * π := by
  rintro ⟨r, hr⟩
  apply H1
  refine ⟨1 - 2 * r, ?_⟩
  push_cast
  have : α = π - 2 * δ := by rw [hδ]; linarith
  rw [this, hr]; ring

/-- Printed Lemma 18: `alpha = pi - 2 delta`, `beta = 3 delta - pi`, `gamma = pi - delta`, `pi/3 < delta < pi/2`;
with `s = a/c`: `s = 2 cos delta`, `0 < s < 1`, `b/c = 1 - s^2`, `cos alpha = 1 - s^2/2`. -/
theorem lemma18 (α β γ a b c δ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hs : α + β + γ = π)
    (h3 : 3 * α + 2 * β = π) (hδ : δ = α + β) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (la : a * Real.sin γ = c * Real.sin α) (lb : b * Real.sin γ = c * Real.sin β) :
    α = π - 2 * δ ∧ β = 3 * δ - π ∧ γ = π - δ ∧ π / 3 < δ ∧ δ < π / 2 ∧
    a / c = 2 * Real.cos δ ∧ 0 < a / c ∧ a / c < 1 ∧ b / c = 1 - (a / c) ^ 2 ∧
    Real.cos α = 1 - (a / c) ^ 2 / 2 := by
  have e1 : α = π - 2 * δ := by rw [hδ]; linarith
  have e2 : β = 3 * δ - π := by rw [hδ]; linarith
  have e3 : γ = π - δ := by rw [hδ]; linarith
  have d1 : π / 3 < δ := by linarith
  have d2 : δ < π / 2 := by linarith
  have hcd : 0 < Real.cos δ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], d2⟩
  have hcd2 : Real.cos δ < 1 / 2 := by
    have : Real.cos δ < Real.cos (π / 3) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) d1
    rwa [Real.cos_pi_div_three] at this
  have hsd : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have sg : Real.sin γ = Real.sin δ := by rw [e3, Real.sin_pi_sub]
  have sa : Real.sin α = 2 * Real.sin δ * Real.cos δ := by rw [e1, Real.sin_pi_sub, Real.sin_two_mul]
  have sb : Real.sin β = Real.sin δ * (1 - 4 * Real.cos δ ^ 2) := by
    have h : Real.sin β = -Real.sin (3 * δ) := by
      rw [e2, Real.sin_sub_pi]
    rw [h, Real.sin_three_mul]
    nlinarith [Real.sin_sq_add_cos_sq δ]
  have hsc : 0 < Real.sin γ := by rw [sg]; exact hsd
  have hac : a / c = 2 * Real.cos δ := by
    rw [div_eq_iff hc.ne']
    have : a * Real.sin δ = c * (2 * Real.sin δ * Real.cos δ) := by rw [sg, sa] at la; exact la
    have := mul_right_cancel₀ hsd.ne' (show a * Real.sin δ = (2 * Real.cos δ * c) * Real.sin δ by linarith)
    linarith
  have hbc : b / c = 1 - 4 * Real.cos δ ^ 2 := by
    rw [div_eq_iff hc.ne']
    have h1 : b * Real.sin δ = c * (Real.sin δ * (1 - 4 * Real.cos δ ^ 2)) := by rw [sg, sb] at lb; exact lb
    have := mul_right_cancel₀ hsd.ne' (show b * Real.sin δ = ((1 - 4 * Real.cos δ ^ 2) * c) * Real.sin δ by
      nlinarith [Real.sin_sq_add_cos_sq δ, h1])
    linarith
  refine ⟨e1, e2, e3, d1, d2, hac, by rw [hac]; linarith, by rw [hac]; linarith, ?_, ?_⟩
  · rw [hbc, hac]; ring
  · rw [e1, Real.cos_pi_sub, Real.cos_two_mul, hac]; ring

/-- Arithmetic part of printed Lemma 38 (hypothesis (ii) of Lemma 8): if `alpha` is not a rational multiple of
`pi` and `3 alpha + 2 beta = pi`, then neither is `beta`, and `alpha/beta` is irrational.  (The geometric part, that
Lemma 8 then applies, is not here.)  H1 witnessed by `Erdos634.BeesonRow.wit_h1_234`. -/
theorem lemma38_arith (α β : ℝ) (h3 : 3 * α + 2 * β = π) (hβ : 0 < β)
    (H1 : ¬ ∃ r : ℚ, α = (r : ℝ) * π) :
    (¬ ∃ r : ℚ, β = (r : ℝ) * π) ∧ (¬ ∃ r : ℚ, α = (r : ℝ) * β) := by
  constructor
  · rintro ⟨r, hr⟩
    apply H1
    refine ⟨(1 - 2 * r) / 3, ?_⟩
    push_cast
    have : 3 * α = π - 2 * β := by linarith
    rw [hr] at this
    linarith
  · rintro ⟨r, hr⟩
    apply H1
    have hπ : π = (3 * (r : ℝ) + 2) * β := by rw [← h3, hr]; ring
    have hne : (3 * (r : ℝ) + 2) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hπ; exact Real.pi_ne_zero hπ
    refine ⟨r / (3 * r + 2), ?_⟩
    push_cast
    have hne' : (3 * (r : ℝ) + 2) ≠ 0 := hne
    rw [div_mul_eq_mul_div, eq_div_iff hne', hπ, hr]
    ring

/-- Lemma 38 arithmetic, H1 witnessed for the tile (2,3,4): `alpha = arccos(7/8)`, `beta = (pi - 3 alpha)/2`. -/
theorem wit_lemma38 :
    (¬ ∃ r : ℚ, (π - 3 * Real.arccos (7 / 8)) / 2 = (r : ℝ) * π) ∧
      (¬ ∃ r : ℚ, Real.arccos (7 / 8) = (r : ℝ) * ((π - 3 * Real.arccos (7 / 8)) / 2)) := by
  apply lemma38_arith (Real.arccos (7 / 8)) _ (by ring) _ Erdos634.BeesonRow.wit_h1_234
  have : Real.arccos (7 / 8) < π / 3 := by
    have h := Real.arccos_lt_arccos (x := 1 / 2) (y := 7 / 8) (by norm_num) (by norm_num) (by norm_num)
    have e : Real.arccos (1 / 2) = π / 3 := by
      rw [show (1 / 2 : ℝ) = Real.cos (π / 3) by rw [Real.cos_pi_div_three]]
      exact Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])
    linarith
  linarith

end Erdos634.BeesonRow2
