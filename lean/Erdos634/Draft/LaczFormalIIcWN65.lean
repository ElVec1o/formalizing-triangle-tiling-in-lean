-- Draft/LaczFormalIIcWN65.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2 (`IIcNoKites`), step (i), ASSEMBLY:
-- `RingSetup.ring_order`: for a strictly convex outer polygon A, a strictly convex inner polygon c strictly inside it with N vertices, and disjoint exterior chords
-- A i -- c (w i) (exterior: strictly outside c except at the end), the map w is a rotation or a reflection of the cyclic order:  w (i+1) = w i + 1 for all i,  or  w (i+1) = w i - 1 for all i.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN64

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {N : ℕ} [NeZero N]

section Ring
variable {A c : Fin N → ℂ} {w : Fin N → Fin N} {τA τC : ℝ}

theorem RingSetup.step_const (R : RingSetup A c w τA τC) (i : Fin N) :
    (w (i + 1) = w i + 1) ↔ (w (i + 1 + 1) = w (i + 1) + 1) := by
  have hn := R.hN
  have h2 : i + 1 + 1 ≠ i := by
    intro h
    apply fin_one_add_one_ne hn
    calc (1 : Fin N) + 1 = (i + 1 + 1) - i := by abel
      _ = 0 := by rw [h]; simp
  have hneq : w (i + 1 + 1) ≠ w i := fun h => h2 (R.w_inj h)
  have a1 := R.adjacent i
  have a2 := R.adjacent (i + 1)
  constructor
  · intro h
    rcases a2 with h' | h'
    · exact h'
    · exfalso
      apply hneq
      -- w i = w (i+1) - 1 and w (i+1) = w (i+2) + 1  =>  w (i+2) = w i
      have : w (i + 1 + 1) = w (i + 1) - 1 := eq_sub_of_add_eq h'.symm
      rw [this, h]; simp
  · intro h
    rcases a1 with h' | h'
    · exact h'
    · exfalso
      apply hneq
      -- w i = w (i+1) + 1 and w (i+2) = w (i+1) + 1
      rw [h, h']

theorem RingSetup.ring_order (R : RingSetup A c w τA τC) : (∀ i, w (i + 1) = w i + 1) ∨ (∀ i, w (i + 1) = w i - 1) := by
  have hall : ∀ m : ℕ, (w ((m : Fin N) + 1) = w (m : Fin N) + 1) ↔ (w (((0 : ℕ) : Fin N) + 1) = w ((0 : ℕ) : Fin N) + 1) := by
    intro m
    induction m with
    | zero => exact Iff.rfl
    | succ m ih =>
      rw [Nat.cast_succ]
      exact (R.step_const (m : Fin N)).symm.trans ih
  by_cases h0 : w (((0 : ℕ) : Fin N) + 1) = w ((0 : ℕ) : Fin N) + 1
  · left
    intro i
    have := (hall i.val).2 h0
    rwa [Fin.cast_val_eq_self] at this
  · right
    intro i
    have h1 : ¬ (w ((i.val : Fin N) + 1) = w (i.val : Fin N) + 1) := fun h => h0 ((hall i.val).1 h)
    rw [Fin.cast_val_eq_self] at h1
    rcases R.adjacent i with h | h
    · exact absurd h h1
    · exact eq_sub_of_add_eq h.symm

#print axioms RingSetup.ring_order

end Ring

end Erdos634.Draft.LaczFormal.WN
