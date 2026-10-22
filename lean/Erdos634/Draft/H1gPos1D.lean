-- Draft/H1gPos1D.lean — ATOM H1.g (position half), sub-atom P3, purely one-dimensional part.
--
-- A finite family of closed real intervals `[lo k, hi k]` with pairwise disjoint interiors and a
-- congruence `R` (an equivalence relation) with `R (hi k) (lo k)`.  Let `Σ` be their union.
-- (1) `chain_start`: every `lo k` is joined to a START `p` of `Σ` (a point with a gap of `Σ` just
--     before it) by `[p, lo k] ⊆ Σ`, and `R p (lo k)`.
-- (2) `start_unique`: two starts of `Σ` below a common point `x`, each joined to `x` inside `Σ`, coincide.
-- This is the sorted/inductive "breakpoint chain along a maximal wall segment", with no geometry.
-- Formalization debt; NOT /goal progress.  Standard axioms, no sorry.
import Mathlib.Tactic

open Set

namespace Erdos634.H1gPos

/-- Membership in the union of the intervals `[lo k, hi k]`, `k ∈ s`. -/
def InSig {ι : Type*} (s : Finset ι) (lo hi : ι → ℝ) (t : ℝ) : Prop :=
  ∃ k ∈ s, lo k ≤ t ∧ t ≤ hi k

/-- `p` is a start of `Σ`: `p` is preceded by a gap. -/
def IsStart {ι : Type*} (s : Finset ι) (lo hi : ι → ℝ) (p : ℝ) : Prop :=
  ∃ ε > 0, ∀ t, p - ε < t → t < p → ¬ InSig s lo hi t

theorem exists_uniform_pos {ι : Type*} [DecidableEq ι] (S : Finset ι) (g : ι → ℝ)
    (hg : ∀ k ∈ S, 0 < g k) : ∃ ε > 0, ∀ k ∈ S, ε ≤ g k := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a S ha ih =>
    obtain ⟨ε, hε, h⟩ := ih (fun k hk => hg k (Finset.mem_insert_of_mem hk))
    refine ⟨min ε (g a), lt_min hε (hg a (Finset.mem_insert_self _ _)), ?_⟩
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (h k hk)

/-- **(1)** every left endpoint is joined to a start of `Σ` inside `Σ`, with `R p (lo k)`. -/
theorem chain_start {ι : Type*} [DecidableEq ι] (s : Finset ι) (lo hi : ι → ℝ)
    (hlt : ∀ k ∈ s, lo k < hi k)
    (hdisj : ∀ k ∈ s, ∀ k' ∈ s, k ≠ k' → Disjoint (Ioo (lo k) (hi k)) (Ioo (lo k') (hi k')))
    (R : ℝ → ℝ → Prop) (hsymm : ∀ a b, R a b → R b a)
    (htrans : ∀ a b c, R a b → R b c → R a c) (hR : ∀ k ∈ s, R (hi k) (lo k)) :
    ∀ k ∈ s, ∃ p, p ≤ lo k ∧ (∀ t, p ≤ t → t ≤ lo k → InSig s lo hi t) ∧
      IsStart s lo hi p ∧ R p (lo k) := by
  intro k0 hk0
  induction' hn : (s.filter fun k' => lo k' < lo k0).card using Nat.strong_induction_on
    with n ih generalizing k0
  by_cases hex : ∃ k' ∈ s, lo k' < lo k0 ∧ lo k0 ≤ hi k'
  · obtain ⟨k', hk', hlo, hhi⟩ := hex
    have hhk : hi k' = lo k0 := by
      by_contra hne
      have hgt : lo k0 < hi k' := lt_of_le_of_ne hhi (Ne.symm hne)
      have hkne : k' ≠ k0 := by rintro rfl; exact lt_irrefl _ hlo
      have h0 := hlt k0 hk0
      have hm : lo k0 < min (hi k') (hi k0) := lt_min hgt h0
      have hm1 := min_le_left (hi k') (hi k0)
      have hm2 := min_le_right (hi k') (hi k0)
      have hA : (lo k0 + min (hi k') (hi k0)) / 2 ∈ Ioo (lo k') (hi k') := ⟨by linarith, by linarith⟩
      have hB : (lo k0 + min (hi k') (hi k0)) / 2 ∈ Ioo (lo k0) (hi k0) := ⟨by linarith, by linarith⟩
      exact Set.disjoint_left.mp (hdisj k' hk' k0 hk0 hkne) hA hB
    have hsub : (s.filter fun k'' => lo k'' < lo k') ⊂ (s.filter fun k'' => lo k'' < lo k0) := by
      refine ⟨fun x hx => ?_, fun hsub => ?_⟩
      · simp only [Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, hx.2.trans hlo⟩
      · have := hsub (Finset.mem_filter.mpr ⟨hk', hlo⟩)
        simp only [Finset.mem_filter] at this
        exact lt_irrefl _ this.2
    have hcard := Finset.card_lt_card hsub
    obtain ⟨p, hp1, hp2, hp3, hp4⟩ := ih _ (hn ▸ hcard) k' hk' rfl
    refine ⟨p, hp1.trans hlo.le, ?_, hp3, ?_⟩
    · intro t h1 h2
      by_cases ht : t ≤ lo k'
      · exact hp2 t h1 ht
      · push Not at ht
        exact ⟨k', hk', ht.le, by rw [hhk]; exact h2⟩
    · refine htrans _ _ _ hp4 ?_
      rw [← hhk]; exact hsymm _ _ (hR k' hk')
  · push Not at hex
    set S' := s.filter fun k' => lo k' < lo k0 with hS'
    obtain ⟨ε, hε, hεg⟩ := exists_uniform_pos S' (fun k' => lo k0 - hi k') (by
      intro k hk
      simp only [hS', Finset.mem_filter] at hk
      have := hex k hk.1 hk.2
      simp only; linarith)
    refine ⟨lo k0, le_rfl, fun t h1 h2 => ?_, ⟨ε, hε, ?_⟩, ?_⟩
    · have : t = lo k0 := le_antisymm h2 h1
      exact ⟨k0, hk0, this.symm.le, by rw [this]; exact (hlt k0 hk0).le⟩
    · rintro t h1 h2 ⟨k, hk, hkl, hkh⟩
      have hkS : k ∈ S' := by
        simp only [hS', Finset.mem_filter]; exact ⟨hk, by linarith⟩
      have := hεg k hkS
      simp only at this
      linarith
    · -- R p p
      have := htrans _ _ _ (hsymm _ _ (hR k0 hk0)) (hR k0 hk0)
      exact this

/-- **(2)** two starts below a common point, each joined to it inside `Σ`, coincide. -/
theorem start_unique {ι : Type*} (s : Finset ι) (lo hi : ι → ℝ) {p p' x : ℝ}
    (hp : p ≤ x) (hp' : p' ≤ x)
    (hc : ∀ t, p ≤ t → t ≤ x → InSig s lo hi t) (hc' : ∀ t, p' ≤ t → t ≤ x → InSig s lo hi t)
    (hs : IsStart s lo hi p) (hs' : IsStart s lo hi p') : p = p' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨ε, hε, hg⟩ := hs'
    refine hg (max p (p' - ε / 2)) ?_ ?_ (hc _ (le_max_left _ _) ?_)
    · have := le_max_right p (p' - ε / 2); linarith
    · exact max_lt h (by linarith)
    · exact (max_le hp (by linarith))
  · obtain ⟨ε, hε, hg⟩ := hs
    refine hg (max p' (p - ε / 2)) ?_ ?_ (hc' _ (le_max_left _ _) ?_)
    · have := le_max_right p' (p - ε / 2); linarith
    · exact max_lt h (by linarith)
    · exact (max_le hp' (by linarith))

end Erdos634.H1gPos

#print axioms Erdos634.H1gPos.chain_start
#print axioms Erdos634.H1gPos.start_unique
