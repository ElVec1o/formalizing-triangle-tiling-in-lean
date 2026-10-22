-- Draft/LaczFormalIIcWN120.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3, p. 358), Lemma 6.2, `ExcInsideAll` step (iii): the counting with NON-UNIFORM capacities.
-- Printed: "u = v + N ... there are at least N convex vertices of C such that the corresponding edge VW arrives at an exceptional point belonging to C-degree ... the number of edges of Gamma_except ending at E is at most N/2 ...
-- Since there are at least N edges arriving at exceptional points belonging to C-degree, it follows that both E and F must be in C-degree."
-- Generalises WN69 `exc_all_inside` (one common capacity) to a capacity `cap e > 0` per exceptional point with `sum cap = M` (`exc_census`: the capacities `cnt gamma - cnt alpha` add up to M).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped Classical

namespace Erdos634.Draft.LaczFormal.WN

theorem exc_all_inside_gen {α β γ : Type*} (X : Finset α) (Y : Finset β) (E Ein : Finset γ) (hEin : Ein ⊆ E)
    (cap : γ → ℕ) (hpos : ∀ e ∈ E, 0 < cap e)
    (toY : α → β) (toE : α → γ) (P : α → Prop) (M : ℕ)
    (hcard : X.card = Y.card + M) (hsum : ∑ e ∈ E, cap e = M)
    (hY : ∀ x ∈ X, P x → toY x ∈ Y) (hinj : ∀ x ∈ X, ∀ x' ∈ X, P x → P x' → toY x = toY x' → x = x')
    (hE : ∀ x ∈ X, ¬ P x → toE x ∈ Ein)
    (hfib : ∀ e ∈ E, (X.filter (fun x => ¬ P x ∧ toE x = e)).card ≤ cap e) : Ein = E := by
  have h1 : (X.filter P).card ≤ Y.card := by
    apply Finset.card_le_card_of_injOn toY
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
      exact hY x hx.1 hx.2
    · intro x hx x' hx' h
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hx'
      exact hinj x hx.1 x' hx'.1 hx.2 hx'.2 h
  have h2 : M ≤ (X.filter (fun x => ¬ P x)).card := by
    have := Finset.filter_card_add_filter_neg_card_eq_card (s := X) P
    omega
  have h3 : (X.filter (fun x => ¬ P x)).card ≤ ∑ e ∈ Ein, cap e := by
    calc (X.filter (fun x => ¬ P x)).card = ∑ e ∈ Ein, ((X.filter (fun x => ¬ P x)).filter (fun x => toE x = e)).card := by
          apply Finset.card_eq_sum_card_fiberwise
          intro x hx
          have hx' := Finset.mem_filter.1 (Finset.mem_coe.1 hx)
          exact Finset.mem_coe.2 (hE x hx'.1 hx'.2)
      _ ≤ ∑ e ∈ Ein, cap e := by
          apply Finset.sum_le_sum
          intro e he
          refine le_trans (le_of_eq ?_) (hfib e (hEin he))
          congr 1
          ext x
          simp only [Finset.mem_filter]
          tauto
  have h4 : ∑ e ∈ E \ Ein, cap e + ∑ e ∈ Ein, cap e = ∑ e ∈ E, cap e := Finset.sum_sdiff hEin
  have h5 : ∑ e ∈ E \ Ein, cap e = 0 := by omega
  rw [Finset.sum_eq_zero_iff] at h5
  apply Finset.Subset.antisymm hEin
  intro e he
  by_contra hne
  have := h5 e (Finset.mem_sdiff.2 ⟨he, hne⟩)
  exact (hpos e he).ne' this

#print axioms exc_all_inside_gen

end Erdos634.Draft.LaczFormal.WN
