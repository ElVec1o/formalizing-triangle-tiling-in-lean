import Erdos634.Draft.LaczFormalT6

/-!
# Snover-Waiveris-Williams, Discrete Math. 91 (1991) 193-200: Lemma 1 and Corollary 1

NOTE, UNAUDITED.  Credit: Snover, Waiveris, Williams (Discrete Math. 91 (1991) Lemma 1, Cor. 1); Niven (Mathlib `niven`);
Laczkovich (Discrete Math. 140 (1995), where the reptile count is cited); Beeson.  Formalization debt, not progress on the /goal.

* `sww_lemma1`: `theta` a rational multiple of `pi` with `cos theta`, `sin theta` or `tan theta` rational is `0`, `pi/6`, `pi/4` or
  `pi/3` modulo `pi/2` (printed Lemma 1; `tan` is Lean's `sin / cos`, so at `cos theta = 0` it is the junk value `0`, consistent
  with `theta = pi/2 mod pi/2`).
* `sww_cor1`: the set of `n` for which no triangle is `n`-tiled (`CongruentDissection n` with `SimilarTM`) is infinite
  (here: every `n = 8 m + 7`, from `reptile_SWW`; the printed proof uses Lagrange's three-square theorem).
-/

open scoped Classical
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.LaczFormal

namespace Erdos634.Laczkovich9

theorem sq_mod8 (r : ℕ) : r ^ 2 % 8 = 0 ∨ r ^ 2 % 8 = 1 ∨ r ^ 2 % 8 = 4 := by
  have h := Nat.mod_lt r (by norm_num : 8 > 0)
  have e : r ^ 2 % 8 = (r % 8) ^ 2 % 8 := by rw [Nat.pow_mod]
  rw [e]
  interval_cases (r % 8) <;> simp

/-- **SWW Corollary 1.** -/
theorem sww_cor1 : Set.Infinite {n : ℕ | ¬ ∃ D : CongruentDissection n, SimilarTM D} := by
  have hmem : ∀ m : ℕ, (8 * m + 7) ∈ {n : ℕ | ¬ ∃ D : CongruentDissection n, SimilarTM D} := by
    intro m ⟨D, hs⟩
    rcases reptile_SWW D hs with ⟨x, hx⟩ | ⟨A, B, hAB, -⟩ | ⟨⟨m', hm'⟩, -⟩
    · have := sq_mod8 x
      have e : x ^ 2 = x * x := by ring
      omega
    · have h1 := sq_mod8 A
      have h2 := sq_mod8 B
      omega
    · have h1 := sq_mod8 m'
      omega
  exact Set.infinite_of_injective_forall_mem (f := fun m : ℕ => 8 * m + 7) (fun a b h => by simpa using h) hmem

/-- The conclusion of SWW Lemma 1: `0, pi/6, pi/4` or `pi/3` modulo `pi/2`. -/
def SWWAngle (θ : ℝ) : Prop :=
  ∃ k : ℤ, θ = k * (Real.pi / 2) ∨ θ = Real.pi / 6 + k * (Real.pi / 2) ∨ θ = Real.pi / 4 + k * (Real.pi / 2) ∨
    θ = Real.pi / 3 + k * (Real.pi / 2)

theorem swwAngle_of_cos_mem (θ : ℝ) (h : Real.cos θ ∈ ({-1, -1 / 2, 0, 1 / 2, 1} : Set ℝ)) : SWWAngle θ := by
  have hpi := Real.pi_pos
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h | h | h
  · -- cos θ = -1 = cos π
    obtain ⟨k, hk | hk⟩ := Real.cos_eq_cos_iff.mp (show Real.cos θ = Real.cos Real.pi by rw [h, Real.cos_pi])
    · exact ⟨2 - 4 * k, Or.inl (by push_cast; linarith)⟩
    · exact ⟨4 * k - 2, Or.inl (by push_cast; linarith)⟩
  · -- cos θ = -1/2 = cos (2π/3)
    have hc : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
      rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num
    obtain ⟨k, hk | hk⟩ := Real.cos_eq_cos_iff.mp (show Real.cos θ = Real.cos (2 * Real.pi / 3) by rw [h, hc])
    · exact ⟨1 - 4 * k, Or.inr (Or.inl (by push_cast; linarith))⟩
    · exact ⟨4 * k - 2, Or.inr (Or.inr (Or.inr (by push_cast; linarith)))⟩
  · obtain ⟨k, hk | hk⟩ := Real.cos_eq_cos_iff.mp (show Real.cos θ = Real.cos (Real.pi / 2) by rw [h, Real.cos_pi_div_two])
    · exact ⟨1 - 4 * k, Or.inl (by push_cast; linarith)⟩
    · exact ⟨4 * k - 1, Or.inl (by push_cast; linarith)⟩
  · obtain ⟨k, hk | hk⟩ := Real.cos_eq_cos_iff.mp (show Real.cos θ = Real.cos (Real.pi / 3) by rw [h, Real.cos_pi_div_three])
    · exact ⟨-4 * k, Or.inr (Or.inr (Or.inr (by push_cast; linarith)))⟩
    · exact ⟨4 * k - 1, Or.inr (Or.inl (by push_cast; linarith))⟩
  · obtain ⟨k, hk | hk⟩ := Real.cos_eq_cos_iff.mp (show Real.cos θ = Real.cos 0 by rw [h, Real.cos_zero])
    · exact ⟨-4 * k, Or.inl (by push_cast; linarith)⟩
    · exact ⟨4 * k, Or.inl (by push_cast; linarith)⟩

theorem swwAngle_cos (θ : ℝ) (hθ : ∃ r : ℚ, θ = r * Real.pi) (hc : ∃ q : ℚ, Real.cos θ = q) : SWWAngle θ :=
  swwAngle_of_cos_mem θ (niven hθ hc)

theorem swwAngle_sin (θ : ℝ) (hθ : ∃ r : ℚ, θ = r * Real.pi) (hs : ∃ q : ℚ, Real.sin θ = q) : SWWAngle θ := by
  obtain ⟨r, hr⟩ := hθ
  obtain ⟨q, hq⟩ := hs
  have h1 : ∃ r' : ℚ, Real.pi / 2 - θ = r' * Real.pi := ⟨1 / 2 - r, by push_cast; rw [hr]; ring⟩
  have h2 : ∃ q' : ℚ, Real.cos (Real.pi / 2 - θ) = q' := ⟨q, by rw [Real.cos_pi_div_two_sub, hq]⟩
  obtain ⟨k, hk | hk | hk | hk⟩ := swwAngle_cos _ h1 h2
  · exact ⟨1 - k, Or.inl (by push_cast; linarith)⟩
  · exact ⟨-k, Or.inr (Or.inr (Or.inr (by push_cast; linarith)))⟩
  · exact ⟨-k, Or.inr (Or.inr (Or.inl (by push_cast; linarith)))⟩
  · exact ⟨-k, Or.inr (Or.inl (by push_cast; linarith))⟩

theorem not_rat_sq_three (t : ℚ) (h : (t : ℝ) ^ 2 = 3) : False := by
  have h3 : Irrational (Real.sqrt 3) := by
    have := Nat.Prime.irrational_sqrt (p := 3) Nat.prime_three
    simpa using this
  apply h3
  refine ⟨|t|, ?_⟩
  push_cast
  rw [← h, Real.sqrt_sq_eq_abs]

theorem swwAngle_tan (θ : ℝ) (hθ : ∃ r : ℚ, θ = r * Real.pi) (ht : ∃ q : ℚ, Real.tan θ = q) : SWWAngle θ := by
  have hpi := Real.pi_pos
  by_cases hcos : Real.cos θ = 0
  · exact swwAngle_cos θ hθ ⟨0, by rw [hcos]; simp⟩
  obtain ⟨t, ht⟩ := ht
  obtain ⟨r, hr⟩ := hθ
  have htan : Real.sin θ = t * Real.cos θ := by
    rw [Real.tan_eq_sin_div_cos] at ht
    field_simp at ht; linarith
  have hsc := Real.sin_sq_add_cos_sq θ
  have hc2 : Real.cos θ ^ 2 * (1 + (t : ℝ) ^ 2) = 1 := by
    rw [htan] at hsc; nlinarith
  have hcpos : 0 < Real.cos θ ^ 2 := by positivity
  have h2θ : Real.cos (2 * θ) * (1 + (t : ℝ) ^ 2) = 1 - (t : ℝ) ^ 2 := by
    rw [Real.cos_two_mul]
    have : 2 * Real.cos θ ^ 2 - 1 = Real.cos θ ^ 2 * (1 - (t : ℝ) ^ 2) := by
      rw [htan] at hsc; nlinarith
    rw [this]
    have : Real.cos θ ^ 2 * (1 - (t : ℝ) ^ 2) * (1 + (t : ℝ) ^ 2) = Real.cos θ ^ 2 * (1 + (t : ℝ) ^ 2) * (1 - (t : ℝ) ^ 2) := by ring
    rw [this, hc2]; ring
  have hden : (1 + (t : ℝ) ^ 2) ≠ 0 := by positivity
  have hrat : ∃ q : ℚ, Real.cos (2 * θ) = q :=
    ⟨(1 - t ^ 2) / (1 + t ^ 2), by
      push_cast
      field_simp
      linarith⟩
  have h2rat : ∃ s : ℚ, 2 * θ = s * Real.pi := ⟨2 * r, by push_cast; rw [hr]; ring⟩
  have hmem := niven h2rat hrat
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h | h | h
  · exfalso; rw [h] at h2θ; nlinarith
  · exfalso; rw [h] at h2θ; apply not_rat_sq_three t; nlinarith
  · -- cos 2θ = 0
    obtain ⟨k, hk | hk⟩ := Real.cos_eq_cos_iff.mp (show Real.cos (2 * θ) = Real.cos (Real.pi / 2) by rw [h, Real.cos_pi_div_two])
    · exact ⟨-2 * k, Or.inr (Or.inr (Or.inl (by push_cast; linarith)))⟩
    · exact ⟨2 * k - 1, Or.inr (Or.inr (Or.inl (by push_cast; linarith)))⟩
  · exfalso; rw [h] at h2θ
    have : (t : ℝ) ^ 2 = 1 / 3 := by nlinarith
    apply not_rat_sq_three (3 * t)
    push_cast; nlinarith
  · -- cos 2θ = 1: t = 0, sin θ = 0
    have ht0 : (t : ℝ) = 0 := by rw [h] at h2θ; nlinarith
    have hs0 : Real.sin θ = 0 := by rw [htan, ht0]; ring
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hs0
    exact ⟨2 * k, Or.inl (by push_cast; linarith)⟩

/-- **SWW Lemma 1.** -/
theorem sww_lemma1 (θ : ℝ) (hθ : ∃ r : ℚ, θ = r * Real.pi)
    (h : (∃ q : ℚ, Real.cos θ = q) ∨ (∃ q : ℚ, Real.sin θ = q) ∨ (∃ q : ℚ, Real.tan θ = q)) : SWWAngle θ := by
  rcases h with h | h | h
  · exact swwAngle_cos θ hθ h
  · exact swwAngle_sin θ hθ h
  · exact swwAngle_tan θ hθ h

/-- Witness: `theta = pi/3` satisfies the hypotheses (cos = 1/2) and the conclusion is nontrivial. -/
theorem sww_lemma1_witness : SWWAngle (Real.pi / 3) :=
  sww_lemma1 (Real.pi / 3) ⟨1 / 3, by push_cast; ring⟩ (Or.inl ⟨1 / 2, by rw [Real.cos_pi_div_three]; norm_num⟩)

/-- Control (arithmetic only): `pi/5` is neither `pi/2` nor `pi/6` modulo `0`; the classes of `SWWAngle` are proper subsets. -/
theorem sww_control : ¬ (Real.pi / 5 = (1 : ℤ) * (Real.pi / 2) ∨ Real.pi / 5 = Real.pi / 6 + (0 : ℤ) * (Real.pi / 2)) := by
  have hpi := Real.pi_pos
  rintro (h | h) <;> push_cast at h <;> nlinarith

end Erdos634.Laczkovich9

#print axioms Erdos634.Laczkovich9.sww_cor1
#print axioms Erdos634.Laczkovich9.sww_lemma1
#print axioms Erdos634.Laczkovich9.sww_lemma1_witness
