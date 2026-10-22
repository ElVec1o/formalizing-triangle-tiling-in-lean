-- Draft/LaczFormalIIcWN69.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2, step (d4): the counting that puts ALL exceptional points inside a Gamma_kite cycle C.
-- X = convex vertices, Y = concave vertices (|X| = |Y| + N by `u = v + N`), each convex vertex sends its Gamma_except edge either to a concave vertex (injectively) or to an
-- exceptional point of Ein (those inside C); an exceptional point receives at most `cap` edges, |E| * cap = N.  Then Ein = E.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped Classical

namespace Erdos634.Draft.LaczFormal.WN

theorem exc_all_inside {α β γ : Type*} (X : Finset α) (Y : Finset β) (E Ein : Finset γ) (hEin : Ein ⊆ E)
    (toY : α → β) (toE : α → γ) (P : α → Prop) (N cap : ℕ)
    (hcard : X.card = Y.card + N) (hN : 0 < N) (hcapE : E.card * cap = N)
    (hY : ∀ x ∈ X, P x → toY x ∈ Y) (hinj : ∀ x ∈ X, ∀ x' ∈ X, P x → P x' → toY x = toY x' → x = x')
    (hE : ∀ x ∈ X, ¬ P x → toE x ∈ Ein)
    (hfib : ∀ e ∈ E, (X.filter (fun x => ¬ P x ∧ toE x = e)).card ≤ cap) : Ein = E := by
  have h1 : (X.filter P).card ≤ Y.card := by
    apply Finset.card_le_card_of_injOn toY
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
      exact hY x hx.1 hx.2
    · intro x hx x' hx' h
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hx'
      exact hinj x hx.1 x' hx'.1 hx.2 hx'.2 h
  have h2 : N ≤ (X.filter (fun x => ¬ P x)).card := by
    have := Finset.filter_card_add_filter_neg_card_eq_card (s := X) P
    omega
  have h3 : (X.filter (fun x => ¬ P x)).card ≤ Ein.card * cap := by
    calc (X.filter (fun x => ¬ P x)).card
        = ∑ e ∈ Ein, ((X.filter (fun x => ¬ P x)).filter (fun x => toE x = e)).card := by
          apply Finset.card_eq_sum_card_fiberwise
          intro x hx
          have hx' := Finset.mem_filter.1 (Finset.mem_coe.1 hx)
          exact Finset.mem_coe.2 (hE x hx'.1 hx'.2)
      _ ≤ ∑ e ∈ Ein, cap := by
          apply Finset.sum_le_sum
          intro e he
          refine le_trans (le_of_eq ?_) (hfib e (hEin he))
          congr 1
          ext x
          simp only [Finset.mem_filter]
          tauto
      _ = Ein.card * cap := by simp
  have hcap : 0 < cap := by
    rcases Nat.eq_zero_or_pos cap with h | h
    · rw [h] at hcapE; simp at hcapE; omega
    · exact h
  have h4 : E.card * cap ≤ Ein.card * cap := by omega
  have h5 : E.card ≤ Ein.card := Nat.le_of_mul_le_mul_right h4 hcap
  exact Finset.eq_of_subset_of_card_le hEin h5

#print axioms exc_all_inside

end Erdos634.Draft.LaczFormal.WN
