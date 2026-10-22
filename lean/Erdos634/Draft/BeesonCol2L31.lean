import Mathlib
import Erdos634.Draft.BeesonRowSect10

/-!
# Beeson-Rosu (arXiv 2607.23453 v2) Lemma 31 (two c edges): the two self-contained parts of the printed proof

NOTE, UNAUDITED.  Credit: Michael Beeson and Rosu (arXiv 2607.23453 v2, Lemma 31, improving Lemma 8 of Beeson, arXiv 1206.2229 v4),
Beeson-Zhang, Laczkovich.  Formalization debt, not progress on the /goal outcomes.

What this file proves (and ONLY this; the full Lemma 31 is NOT formalized, see the gap below):
* `l31_boundary_point`: first paragraph of the printed proof.  At a boundary point interior to a side the angles of the tiles
  sum to `pi`, `p alpha + q beta + r gamma = pi` with `r >= 1`; if `gamma > pi/2` and `alpha/beta` is irrational then
  `p = q = r = 1`.  (Hypotheses (i), (ii) of the lemma; no tiling used.)
* `side_has_c_edge`: second paragraph.  The combinatorial pigeon-hole: `n >= 1` tiles along a side, tile `i` having its edge on the
  segment `x_i x_{i+1}`; every tile with no c edge on the side has its gamma angle at `x_i` or `x_{i+1}`; no two gamma
  angles at one point (`2 gamma > pi`); none at the ends `x_0`, `x_n` (hypothesis (iii)).  Then some tile has its c edge on
  the side.  The geometric inputs (tile adjacency along the side, "a-edge ends carry beta, gamma; b-edge ends carry alpha,
  gamma") are the HYPOTHESES `hg`, `hinj`, `h0`, `hn`, named, not derived here.

GAP (quoted exactly, not attempted): the remainder of the proof, "Suppose, to the contrary, that there is just one tile with a
c edge on the side AC ... (A)-(E), the pigeon-hole argument ... Cases 1a, 1b, 1c, 2".  It needs tile placement at edge level
(a tile edge `P R` ending inside another tile's edge, "northwest of PR", the line through `P R`); the project's edge-level
placement layer (`prop:cornerpara` "matched by exactly one tile") is the missing ingredient.
-/

namespace Erdos634.BeesonCol2L31

open Real

theorem l31_boundary_point {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : π / 2 < γ)
    (hirr : ¬ ∃ q : ℚ, α = (q : ℝ) * β) (p q r : ℕ) (hr : 1 ≤ r)
    (h : (p : ℝ) * α + q * β + r * γ = π) (hs : α + β + γ = π) : r = 1 ∧ p = 1 ∧ q = 1 := by
  have hr1 : r = 1 := by
    by_contra hne
    have : 2 ≤ r := by omega
    have h2 : (2 : ℝ) ≤ r := by exact_mod_cast this
    have hp0 : (0 : ℝ) ≤ p * α := by positivity
    have hq0 : (0 : ℝ) ≤ q * β := by positivity
    nlinarith [Real.pi_pos]
  subst hr1
  have key : ((p : ℝ) - 1) * α = (1 - q) * β := by push_cast at h; linarith
  by_cases hp : p = 1
  · subst hp
    refine ⟨rfl, rfl, ?_⟩
    have : (1 - (q : ℝ)) * β = 0 := by simpa using key.symm
    have : (1 - (q : ℝ)) = 0 := (mul_eq_zero.mp this).resolve_right hβ.ne'
    have : (q : ℝ) = 1 := by linarith
    exact_mod_cast this
  · exfalso
    apply hirr
    refine ⟨((1 : ℚ) - q) / ((p : ℚ) - 1), ?_⟩
    have hp' : ((p : ℝ) - 1) ≠ 0 := by
      intro h0
      apply hp
      have : (p : ℝ) = 1 := by linarith
      exact_mod_cast this
    push_cast
    field_simp
    linarith

/-- Pigeon-hole core of "every side has at least one c edge". -/
theorem side_has_c_edge (n : ℕ) (hn : 1 ≤ n) (isC : Fin n → Prop)
    (g : Fin n → ℕ)
    (hg : ∀ i, ¬ isC i → g i = i.val ∨ g i = i.val + 1)
    (hinj : ∀ i j, ¬ isC i → ¬ isC j → g i = g j → i = j)
    (h0 : ∀ i, ¬ isC i → g i ≠ 0) (hn' : ∀ i, ¬ isC i → g i ≠ n) :
    ∃ i, isC i := by
  by_contra hno
  push_neg at hno
  have hmap : ∀ i : Fin n, g i ∈ Finset.Ioo 0 n := by
    intro i
    have := hg i (hno i)
    have h1 := h0 i (hno i)
    have h2 := hn' i (hno i)
    simp only [Finset.mem_Ioo]
    omega
  have := Finset.card_le_card_of_injOn g (s := Finset.univ) (t := Finset.Ioo 0 n)
    (fun i _ => hmap i) (fun i _ j _ hij => hinj i j (hno i) (hno j) hij)
  simp at this
  omega

/-- Hypothesis (ii) (`alpha/beta` irrational) follows from `alpha/pi` irrational for the family `3 alpha + 2 beta = pi`. -/
theorem l31_irr_of_h1 {α β : ℝ} (h3 : 3 * α + 2 * β = π) (H1 : ¬ ∃ r : ℚ, α = (r : ℝ) * π) :
    ¬ ∃ q : ℚ, α = (q : ℝ) * β := by
  rintro ⟨q, hq⟩
  have hβ : β = (π - 3 * α) / 2 := by linarith
  rw [hβ] at hq
  have key : α * (2 + 3 * (q : ℝ)) = q * π := by linarith
  by_cases h0 : (2 : ℝ) + 3 * q = 0
  · have : (q : ℝ) * π = 0 := by rw [← key, h0, mul_zero]
    have hq0 : (q : ℝ) = 0 := (mul_eq_zero.mp this).resolve_right Real.pi_pos.ne'
    rw [hq0] at h0; norm_num at h0
  · apply H1
    refine ⟨(q : ℚ) / (2 + 3 * q), ?_⟩
    push_cast
    rw [div_mul_eq_mul_div, eq_div_iff h0]
    linarith

/-- Witness: the hypotheses (i), (ii) hold for the integer tile `(2,3,4)` (`cos alpha = 7/8`, i.e. `(b+c)/(2c)`): `alpha/beta` is
irrational (via printed Lemma 27, `BeesonRow.lemma27_h1`), and `gamma = (pi + alpha)/2 > pi/2`. -/
theorem l31_hyp_wit (α β : ℝ) (hα : Real.cos α = 7 / 8) (h0 : 0 ≤ α) (hπ : α ≤ π) (h3 : 3 * α + 2 * β = π) :
    (¬ ∃ q : ℚ, α = (q : ℝ) * β) ∧ π / 2 < (π + α) / 2 ∧ 0 < α := by
  have hc : Real.cos α = (((3 : ℕ) : ℝ) + ((4 : ℕ) : ℝ)) / (2 * ((4 : ℕ) : ℝ)) := by rw [hα]; norm_num
  refine ⟨l31_irr_of_h1 h3 (Erdos634.BeesonRow.lemma27_h1 3 4 (by norm_num) (by norm_num) α hc h0 hπ), ?_, ?_⟩
  · have : 0 < α := by
      rcases h0.lt_or_eq with h | h
      · exact h
      · rw [← h] at hα; simp at hα; norm_num at hα
    linarith
  · rcases h0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hα; simp at hα; norm_num at hα

end Erdos634.BeesonCol2L31
