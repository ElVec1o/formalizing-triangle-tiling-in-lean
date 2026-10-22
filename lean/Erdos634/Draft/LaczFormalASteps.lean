import Erdos634.Draft.LaczFormalAFrame

/-!
# Lemma A(j): the arithmetic cores of Steps B, C, D as hypothesis-free list lemmas (UNAUDITED)

Credit: AI assistant (Lemma A(k) proposal), Beeson-Rosu, Beeson, Laczkovich.  Hand proof
(private working notes, not included) sec. 2.  Axiom-clean, no `sorry`.

A cover of a segment (on one side of a line, by consecutive tile edges) is modelled by the list of its edge lengths, each a side
`a`, `b` or `c`.  PROVED: (B) the far cover of the chord `l`, whose first edge is `a` or `c`, has no partial sum `r b`,
`1 ≤ r ≤ f−1`; (C) a cover of a length `m a`, `m ≤ f−1`, consists of `m` edges `a`; (D) a far cover of total length `j b`,
`j ≤ f−1`, starting with `a` or `c`, does not exist (`far_cover_impossible`).
NOT PROVED (the geometry): that a real dissection supplies the list, i.e. the far cover of `l` from `J` ends at `D_j`
(Principle E1, H4), the standardness of the rows (Steps A, C geometry), and the 6-token walk bridge.
-/

namespace Erdos634.LaczCol

open Erdos634.LaczJunction

/-- `x` is one of the three side lengths. -/
def IsSide (e f x : ℕ) : Prop := x = ta e f ∨ x = tb e f ∨ x = tc e f

theorem sides_repr (e f : ℕ) : ∀ l : List ℕ, (∀ x ∈ l, IsSide e f x) →
    ∃ x y z : ℕ, l.sum = x * ta e f + y * tb e f + z * tc e f
  | [], _ => ⟨0, 0, 0, by simp⟩
  | h :: t, hl => by
    obtain ⟨x, y, z, hs⟩ := sides_repr e f t (fun w hw => hl w (List.mem_cons_of_mem _ hw))
    rcases hl h List.mem_cons_self with rfl | rfl | rfl
    · exact ⟨x + 1, y, z, by simp only [List.sum_cons, hs]; ring⟩
    · exact ⟨x, y + 1, z, by simp only [List.sum_cons, hs]; ring⟩
    · exact ⟨x, y, z + 1, by simp only [List.sum_cons, hs]; ring⟩

/-- **Step B.**  A cover starting with an edge `a` or `c` has no partial sum `r b` (`1 ≤ r ≤ f−1`): no far vertex at `D_r`. -/
theorem far_no_vertex (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f)
    (e1 : ℕ) (t : List ℕ) (h1 : e1 = ta e f ∨ e1 = tc e f)
    (hl : ∀ x ∈ e1 :: t, IsSide e f x) (r : ℕ) (hr1 : 1 ≤ r) (hr : r ≤ f - 1) (n : ℕ) (hn : 1 ≤ n) :
    ((e1 :: t).take n).sum ≠ r * tb e f := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨x, y, z, hs⟩ := sides_repr e f (t.take n') (fun w hw =>
    hl w (List.mem_cons_of_mem _ (List.mem_of_mem_take hw)))
  have hA := A2_not_sum e f x y z r he hef hco hr1 hr
  simp only [List.take_succ_cons, List.sum_cons, hs]
  rcases h1 with rfl | rfl
  · intro h; apply hA.1; linarith
  · intro h; apply hA.2; linarith

/-- **Step C.**  A cover of total length `m a`, `1 ≤ m ≤ f−1`, consists of exactly `m` edges `a`. -/
theorem horizontal_all_a (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f)
    (l : List ℕ) (hl : ∀ x ∈ l, IsSide e f x) (m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ f - 1)
    (hs : l.sum = m * ta e f) : (∀ x ∈ l, x = ta e f) ∧ l.length = m := by
  have hall : ∀ x ∈ l, x = ta e f := by
    intro x hx
    by_contra hne
    have hp := List.perm_cons_erase hx
    obtain ⟨u, v, w, hr⟩ := sides_repr e f (l.erase x)
      (fun q hq => hl q (List.mem_of_mem_erase hq))
    have hsum : l.sum = x + (l.erase x).sum := by rw [hp.sum_eq]; simp
    rcases hl x hx with h | h | h
    · exact hne h
    · subst h
      have := Erdos634.Draft.SideRunGArith.Aa he hef hco hm1 hm (x := u) (y := v + 1) (z := w)
        (by rw [hsum, hr] at hs; simp only [ta, tb, tc] at hs; linarith)
      omega
    · subst h
      have := Erdos634.Draft.SideRunGArith.Aa he hef hco hm1 hm (x := u) (y := v) (z := w + 1)
        (by rw [hsum, hr] at hs; simp only [ta, tb, tc] at hs; linarith)
      omega
  refine ⟨hall, ?_⟩
  have hrep : l = List.replicate l.length (ta e f) := List.eq_replicate_iff.mpr ⟨rfl, hall⟩
  rw [hrep, List.sum_replicate, smul_eq_mul] at hs
  have hpos : 0 < ta e f := by unfold ta; exact Nat.mul_pos he (by omega)
  exact Nat.eq_of_mul_eq_mul_right hpos hs

/-- **Step D (arithmetic).**  There is no cover starting with `a` or `c` of total length `j b`, `1 ≤ j ≤ f−1`. -/
theorem far_cover_impossible (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f)
    (e1 : ℕ) (t : List ℕ) (h1 : e1 = ta e f ∨ e1 = tc e f)
    (hl : ∀ x ∈ e1 :: t, IsSide e f x) (j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ f - 1)
    (hs : (e1 :: t).sum = j * tb e f) : False := by
  have := far_no_vertex e f he hef hco e1 t h1 hl j hj1 hj (e1 :: t).length (by simp)
  rw [List.take_length] at this
  exact this hs

#print axioms far_no_vertex
#print axioms horizontal_all_a
#print axioms far_cover_impossible

end Erdos634.LaczCol
