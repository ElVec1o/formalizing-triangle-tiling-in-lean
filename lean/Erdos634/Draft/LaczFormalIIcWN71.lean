-- Draft/LaczFormalIIcWN71.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2, item (3) (straight vertices on the innermost cycle), step 1: CYCLIC SHIFT of a polygon.
-- `rotP p a j = p (j + a)`: injectivity, `SimplePoly`, `edgeSet` and `extAng` are shift invariant (`extAng (rotP p a) j = extAng p (j + a)`).  Pure Mathlib/Fin bookkeeping.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN68

open scoped Classical Fin.NatCast
open Complex

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

/-- Cyclic shift of the vertex list. -/
def rotP (p : Fin n → ℂ) (a : Fin n) : Fin n → ℂ := fun j => p (j + a)

theorem rotP_inj {p : Fin n → ℂ} (h : Function.Injective p) (a : Fin n) : Function.Injective (rotP p a) := by
  intro i j hij
  exact add_right_cancel (h hij)

theorem rotP_simple {p : Fin n → ℂ} (hs : SimplePoly p) (a : Fin n) : SimplePoly (rotP p a) := by
  intro i j hij z hz
  have e : ∀ i : Fin n, i + 1 + a = i + a + 1 := fun i => add_right_comm i 1 a
  simp only [rotP, e] at hz ⊢
  have hne : i + a ≠ j + a := fun h => hij (add_right_cancel h)
  exact hs (i + a) (j + a) hne z hz

theorem rotP_edgeSet (p : Fin n → ℂ) (a : Fin n) : edgeSet (rotP p a) = edgeSet p := by
  have e : ∀ i : Fin n, i + 1 + a = i + a + 1 := fun i => add_right_comm i 1 a
  ext z
  simp only [edgeSet, Set.mem_iUnion, rotP, e]
  constructor
  · rintro ⟨i, hi⟩; exact ⟨i + a, hi⟩
  · rintro ⟨i, hi⟩
    refine ⟨i - a, ?_⟩
    have h1 : i - a + a = i := sub_add_cancel i a
    rw [h1]; exact hi

theorem rotP_extAng (p : Fin n → ℂ) (a j : Fin n) : extAng (rotP p a) j = extAng p (j + a) := by
  unfold extAng rotP
  have h1 : j + 1 + a = j + a + 1 := by rw [add_right_comm]
  have h2 : j - 1 + a = j + a - 1 := by rw [sub_add_eq_add_sub]
  rw [h1, h2]

end Erdos634.Draft.LaczFormal.WN
