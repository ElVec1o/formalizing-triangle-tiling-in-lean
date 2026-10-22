-- Draft/LaczFormalIIcWN102.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2, R3 (pure convex geometry), part 2: `edge_of_zero` and `chord_outside`.
-- `edge_of_zero`: a point weakly inside every edge half-plane of a strictly convex polygon `c` (sign `tau`) that lies on the line of the edge `j` lies on the edge.
-- `chord_outside`: a segment from `x` (winding number 0, off the polygon) whose open part misses the strictly convex polygon `c` stays strictly outside some half-plane of `c` for every parameter in `[0, 1)`.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN101

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

theorem idx_ne_sub (hn : 3 ≤ n) (j : Fin n) : j + 1 ≠ j - 1 := by
  intro h
  have h2 : j + 1 + 1 = j := by
    calc j + 1 + 1 = (j - 1) + 1 := by rw [h]
      _ = j := sub_add_cancel j 1
  apply fin_one_add_one_ne hn
  have : j + (1 + 1) = j + 0 := by rw [← add_assoc]; simpa using h2
  exact add_left_cancel this

theorem idx_ne_succ (hn : 3 ≤ n) (j : Fin n) : j + 1 ≠ j := by
  intro h
  apply fin_one_ne hn
  have : j + 1 = j + 0 := by simpa using h
  exact add_left_cancel this

theorem idx_ne_succ2 (hn : 3 ≤ n) (j : Fin n) : j + 1 + 1 ≠ j := by
  intro h
  apply fin_one_add_one_ne hn
  have : j + (1 + 1) = j + 0 := by rw [← add_assoc]; simpa using h
  exact add_left_cancel this

theorem edge_of_zero {c : Fin n → ℂ} {τ : ℝ} (hinj : Function.Injective c) (hn : 3 ≤ n) (h : SC c τ) (hτ : τ = 1 ∨ τ = -1) {z : ℂ}
    (hz : ∀ m : Fin n, 0 ≤ τ * sideFn (c m) (c (m + 1) - c m) z) (j : Fin n)
    (hj : τ * sideFn (c j) (c (j + 1) - c j) z = 0) : z ∈ segment ℝ (c j) (c (j + 1)) := by
  have hτ0 : τ ≠ 0 := by rcases hτ with rfl | rfl <;> norm_num
  have hd : c (j + 1) - c j ≠ 0 := sub_ne_zero.2 (nd hinj hn j)
  have hsj : sideFn (c j) (c (j + 1) - c j) z = 0 := by
    rcases mul_eq_zero.1 hj with h0 | h0
    · exact absurd h0 hτ0
    · exact h0
  -- z = c j + t d
  set t : ℝ := ((z - c j) / (c (j + 1) - c j)).re with ht
  have hzt : z = c j + (t : ℂ) * (c (j + 1) - c j) := by
    have him : ((z - c j) / (c (j + 1) - c j)).im = 0 := hsj
    have : (z - c j) / (c (j + 1) - c j) = (t : ℂ) := by
      apply Complex.ext
      · simp [ht]
      · simp [him]
    field_simp at this
    linear_combination this
  have hline : ∀ (u : ℝ) (x0 d' : ℂ), sideFn x0 d' (c j + (u : ℂ) * (c (j + 1) - c j)) = (1 - u) * sideFn x0 d' (c j) + u * sideFn x0 d' (c (j + 1)) :=
    fun u x0 d' => sideFn_lin x0 d' (c j) (c (j + 1)) u
  have hzero1 : sideFn (c (j - 1)) (c (j - 1 + 1) - c (j - 1)) (c j) = 0 := by
    rw [sub_add_cancel]
    have := sideFn_tip (x0 := c (j - 1)) (d := c j - c (j - 1)) (sub_ne_zero.2 (by
      have := nd hinj hn (j - 1); rwa [sub_add_cancel] at this))
    rwa [show c (j - 1) + (c j - c (j - 1)) = c j by ring] at this
  refine (segment_eq_image' ℝ (c j) (c (j + 1)) ▸ ?_)
  have ht0 : 0 ≤ t := by
    by_contra hneg
    push_neg at hneg
    have h1 := hz (j - 1)
    rw [hzt, hline, hzero1] at h1
    have hpos := h (j - 1) (j + 1) (by exact idx_ne_sub hn j) (by rw [sub_add_cancel]; exact idx_ne_succ hn j)
    rw [sub_add_cancel] at hpos h1
    nlinarith
  have ht1 : t ≤ 1 := by
    by_contra hgt
    push_neg at hgt
    have h1 := hz (j + 1)
    rw [hzt, hline, sideFn_base] at h1
    have hpos := h (j + 1) j (Ne.symm (idx_ne_succ hn j)) (Ne.symm (idx_ne_succ2 hn j))
    nlinarith
  refine ⟨t, ⟨ht0, ht1⟩, ?_⟩
  beta_reduce
  rw [Complex.real_smul]
  exact hzt.symm

/-- **Exterior chord.** -/
theorem chord_outside {c : Fin n → ℂ} {τ : ℝ} (hinj : Function.Injective c) (hn : 3 ≤ n) (hSC : SC c τ) (hτ : τ = 1 ∨ τ = -1) (x y : ℂ)
    (hx : x ∉ edgeSet c) (hx0 : wind c x = 0)
    (hmiss : ∀ s : ℝ, 0 < s → s < 1 → x + (s : ℂ) * (y - x) ∉ edgeSet c) :
    ∀ s : ℝ, 0 ≤ s → s < 1 → ∃ j : Fin n, τ * sideFn (c j) (c (j + 1) - c j) (x + (s : ℂ) * (y - x)) < 0 := by
  intro s0 hs0 hs1
  by_contra hcon
  push_neg at hcon
  have hnot : x + (s0 : ℂ) * (y - x) ∉ edgeSet c := by
    rcases hs0.eq_or_lt with h0 | h0
    · rw [← h0]; simpa using hx
    · exact hmiss s0 h0 hs1
  have hw : wind c (x + (s0 : ℂ) * (y - x)) = 0 := by
    rw [← hx0]
    symm
    apply wind_const_segment
    intro w hw
    rw [segment_eq_image'] at hw
    obtain ⟨u, ⟨hu0, hu1⟩, rfl⟩ := hw
    beta_reduce
    rw [Complex.real_smul]
    have e : x + (u : ℂ) * (x + (s0 : ℂ) * (y - x) - x) = x + ((u * s0 : ℝ) : ℂ) * (y - x) := by push_cast; ring
    rw [e]
    rcases (mul_nonneg hu0 hs0).eq_or_lt with h0 | h0
    · rw [← h0]; simpa using hx
    · exact hmiss _ h0 (by nlinarith)
  have hstrict : ∀ j : Fin n, 0 < τ * sideFn (c j) (c (j + 1) - c j) (x + (s0 : ℂ) * (y - x)) := by
    intro j
    rcases (hcon j).eq_or_lt with h0 | h0
    · exfalso
      exact hnot (by
        have := edge_of_zero hinj hn hSC hτ hcon j h0.symm
        exact Set.mem_iUnion.2 ⟨j, this⟩)
    · exact h0
  exact wind_ne_of_inside c τ hτ _ hstrict hw

#print axioms edge_of_zero
#print axioms chord_outside

end Erdos634.Draft.LaczFormal.WN
