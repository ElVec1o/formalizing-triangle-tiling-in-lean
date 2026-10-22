import Mathlib

/-!
# Beeson (arXiv 1206.2229 v4) Lemma 1, arithmetic half: the Laczkovich list against `3 alpha + 2 beta = pi`

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Lemma 1), Laczkovich (Discrete Math 140 (1995), Theorems 5.1, 5.3),
Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.  Pure arithmetic, no tiling, no H1.

Angles are in units of pi (rational numbers).  Printed proof of Lemma 1: Theorem 5.1 of Laczkovich says that if a triangle `T` is
dissected into triangles with rational angles `(x, y, z)` then, up to order, (i) `T` has those angles (similar), or (ii) one of
them is `1/2` (right tile), or `(x, y, z)` is one of the listed triples (iii)-(vii).  "The reader may easily check that the only
triple satisfying `3 alpha + 2 beta = pi` under any labeling is `(pi/4, pi/8, 5 pi/8)`" (then killed by Theorem 5.3).  This file
does that check (and the right-angle case, which the print leaves implicit).

NOT claimed: a classification of rational `alpha` by arithmetic alone.  The equation `3 alpha + 2 beta = pi` has infinitely many
rational solutions (`rational_solution_pi5`, `rational_solution_pi7`); they are excluded only by the geometric theorems.
-/

namespace Erdos634.BeesonH1

/-- `(a, b, c)` is a permutation of `(x, y, z)`. -/
def Perm3Q (a b c x y z : ℚ) : Prop :=
  (a = x ∧ b = y ∧ c = z) ∨ (a = x ∧ b = z ∧ c = y) ∨ (a = y ∧ b = x ∧ c = z) ∨
  (a = y ∧ b = z ∧ c = x) ∨ (a = z ∧ b = x ∧ c = y) ∨ (a = z ∧ b = y ∧ c = x)

/-- The triples of Laczkovich Theorem 5.1 (iii)-(vii), in units of pi (the (iv) triple repeats the first of (iii)). -/
def laczList : List (ℚ × ℚ × ℚ) :=
  [(1/6, 1/6, 2/3), (1/3, 1/12, 7/12), (1/3, 1/30, 19/30), (1/3, 7/30, 13/30),
   (1/10, 3/10, 6/10), (1/10, 2/10, 7/10),
   (1/8, 1/4, 5/8), (1/4, 1/3, 5/12), (1/12, 1/4, 2/3)]

def InLaczList (a b c : ℚ) : Prop :=
  ∃ t ∈ laczList, Perm3Q a b c t.1 t.2.1 t.2.2

/-- Every listed triple has angle sum `1` (sanity check of the transcription). -/
theorem laczList_sum : ∀ t ∈ laczList, t.1 + t.2.1 + t.2.2 = 1 := by
  intro t ht
  simp only [laczList, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- **The check printed in Lemma 1**: if `(x, y, 2x + y)` with `3x + 2y = 1`, `x, y > 0` is, in some order, a listed triple,
then `(x, y) = (1/4, 1/8)`, i.e. the triple `(pi/4, pi/8, 5 pi/8)`. -/
theorem list_check {x y z : ℚ} (hx : 0 < x) (hy : 0 < y) (hrel : 3 * x + 2 * y = 1) (hz : z = 2 * x + y)
    (h : InLaczList x y z) : x = 1/4 ∧ y = 1/8 := by
  obtain ⟨⟨p, q, r⟩, hm, hp⟩ := h
  simp only [laczList, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  simp only [Perm3Q] at hp
  rcases hm with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
  subst h1 h2 h3 <;>
  rcases hp with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ <;>
  first
  | (exfalso; rw [a1, a2] at hrel; norm_num at hrel; done)
  | exact ⟨a1, a2⟩

/-- **Right tile impossible**: no `(x, y, 2x + y)` with `3x + 2y = 1`, `x, y > 0` has an angle `1/2`. -/
theorem no_right_angle {x y z : ℚ} (hx : 0 < x) (hy : 0 < y) (hrel : 3 * x + 2 * y = 1) (hz : z = 2 * x + y) :
    ¬ (x = 1/2 ∨ y = 1/2 ∨ z = 1/2) := by
  rintro (h | h | h) <;> subst hz <;> linarith

/-- The rational solutions are infinite: `alpha = beta = pi/5`. -/
theorem rational_solution_pi5 : 3 * (1/5 : ℚ) + 2 * (1/5) = 1 ∧ (2 * (1/5 : ℚ) + 1/5 = 3/5) := by norm_num

/-- `(pi/7, 2pi/7, 4pi/7)`: a rational solution not in Laczkovich's list; excluded by Theorem 5.1, not by arithmetic. -/
theorem rational_solution_pi7 :
    3 * (1/7 : ℚ) + 2 * (2/7) = 1 ∧ (2 * (1/7 : ℚ) + 2/7 = 4/7) ∧ ¬ InLaczList (1/7) (2/7) (4/7) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rintro ⟨⟨p, q, r⟩, hm, hp⟩
  simp only [laczList, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  simp only [Perm3Q] at hp
  rcases hm with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
  subst h1 h2 h3 <;>
  rcases hp with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ <;>
  (revert a1 a2 a3; norm_num)

end Erdos634.BeesonH1

#print axioms Erdos634.BeesonH1.list_check
#print axioms Erdos634.BeesonH1.rational_solution_pi7
