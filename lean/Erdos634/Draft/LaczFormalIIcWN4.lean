-- Draft/LaczFormalIIcWN4.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2/6.3, Route B (winding-number interior), item B4:
-- a simple closed polygon has points off the polygon where the winding number is +1 or -1 (generic-height crossing sweep).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2/6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN2
import Erdos634.Draft.LaczFormalIIcWN3

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

/-- Distinct edges meet only in points that are endpoints of both (so no crossings, no overlaps, no T-junctions). -/
def SimplePoly (p : Fin n → ℂ) : Prop :=
  ∀ i j : Fin n, i ≠ j → ∀ z ∈ segment ℝ (p i) (p (i + 1)) ∩ segment ℝ (p j) (p (j + 1)),
    (z = p i ∨ z = p (i + 1)) ∧ (z = p j ∨ z = p (j + 1))

/-- The winding number is constant along a segment that avoids the polygon. -/
theorem wind_const_segment (p : Fin n → ℂ) {u v : ℂ} (h : ∀ z ∈ segment ℝ u v, z ∉ edgeSet p) :
    wind p u = wind p v := by
  set g : ℝ → ℝ := fun τ => wind p (u + τ • (v - u)) with hg
  have hmem : ∀ τ ∈ Set.Icc (0 : ℝ) 1, u + τ • (v - u) ∉ edgeSet p := by
    intro τ hτ
    apply h
    rw [segment_eq_image']
    exact ⟨τ, hτ, rfl⟩
  have hcont : ContinuousOn g (Set.Icc 0 1) := by
    intro τ hτ
    have hc : ContinuousAt (fun τ : ℝ => u + τ • (v - u)) τ := by fun_prop
    exact (ContinuousAt.comp (g := wind p) (f := fun τ : ℝ => u + τ • (v - u))
      (wind_continuousAt p _ (hmem τ hτ)) hc).continuousWithinAt
  have hint : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∃ k : ℤ, g τ = k := fun τ hτ => wind_int p _ (hmem τ hτ)
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨k0, hk0⟩ := hint 0 h0
  obtain ⟨k1, hk1⟩ := hint 1 h1
  have e0 : g 0 = wind p u := by simp [hg]
  have e1 : g 1 = wind p v := by simp [hg]
  rw [← e0, ← e1]
  by_contra hne
  have hivt : Set.uIcc (g 0) (g 1) ⊆ g '' Set.uIcc 0 1 := by
    apply intermediate_value_uIcc
    rwa [Set.uIcc_of_le zero_le_one]
  rw [hk0, hk1] at hne hivt
  have hne' : k0 ≠ k1 := fun h => hne (by rw [h])
  rcases lt_or_gt_of_ne hne' with hlt | hgt
  · have hm : ((k0 : ℝ) + 1 / 2) ∈ Set.uIcc (k0 : ℝ) (k1 : ℝ) := by
      rw [Set.uIcc_of_le (by exact_mod_cast hlt.le)]
      have : (k0 : ℝ) + 1 ≤ k1 := by exact_mod_cast hlt
      constructor <;> linarith
    obtain ⟨τ, hτ, hgτ⟩ := hivt hm
    rw [Set.uIcc_of_le zero_le_one] at hτ
    obtain ⟨k, hk⟩ := hint τ hτ
    rw [hk] at hgτ
    have : ((k - k0 : ℤ) : ℝ) = 1 / 2 := by push_cast; linarith
    have h2 : (2 : ℝ) * ((k - k0 : ℤ) : ℝ) = 1 := by linarith
    have : (2 * (k - k0) : ℤ) = 1 := by exact_mod_cast h2
    omega
  · have hm : ((k0 : ℝ) - 1 / 2) ∈ Set.uIcc (k0 : ℝ) (k1 : ℝ) := by
      rw [Set.uIcc_of_ge (by exact_mod_cast hgt.le)]
      have : (k1 : ℝ) + 1 ≤ k0 := by exact_mod_cast hgt
      constructor <;> linarith
    obtain ⟨τ, hτ, hgτ⟩ := hivt hm
    rw [Set.uIcc_of_le zero_le_one] at hτ
    obtain ⟨k, hk⟩ := hint τ hτ
    rw [hk] at hgτ
    have h2 : (2 : ℝ) * ((k0 - k : ℤ) : ℝ) = 1 := by push_cast; linarith
    have : (2 * (k0 - k) : ℤ) = 1 := by exact_mod_cast h2
    omega

theorem isCompact_edgeSet (p : Fin n → ℂ) : IsCompact (edgeSet p) := by
  refine isCompact_iUnion fun i => ?_
  rw [segment_eq_image]; exact isCompact_Icc.image (by fun_prop)

/-- A far-left point on the horizontal line `Im = c` where the winding number vanishes. -/
theorem exists_far_left (p : Fin n → ℂ) (c x : ℝ) : ∃ w : ℂ, w.im = c ∧ w.re < x ∧ wind p w = 0 := by
  obtain ⟨K, hK, hKs⟩ := Filter.mem_cocompact.1 (wind_eventually_zero p)
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  refine ⟨⟨-(max R 0 + |x| + 1), c⟩, rfl, ?_, ?_⟩
  · have := neg_abs_le x
    have := le_max_right R 0
    simp only; linarith
  · apply hKs
    intro hmem
    have h1 := hR hmem
    rw [mem_closedBall_zero_iff] at h1
    have h2 := Complex.abs_re_le_norm (⟨-(max R 0 + |x| + 1), c⟩ : ℂ)
    have h3 : |(⟨-(max R 0 + |x| + 1), c⟩ : ℂ).re| = max R 0 + |x| + 1 := by
      simp only [abs_neg]
      exact abs_of_nonneg (by have := le_max_right R 0; positivity)
    have := le_max_left R 0
    have := abs_nonneg x
    linarith

end Erdos634.Draft.LaczFormal.WN
