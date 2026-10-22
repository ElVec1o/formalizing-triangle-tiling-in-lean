import Erdos634.Draft.LaczFormalWalkAssemble
import Erdos634.Draft.LaczFormalBandLemma

/-!
# B1 from the walk: the counts `(0, Me, 2Me)` of the base word

Erdős #634, base-`β` band.  Credit: AI assistant (item 3, band program; Band Lemma and Prop. B1), Beeson–Roșu
(Lemmas 28, 30, 34), Beeson, Laczkovich, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.

* `total_eq_counts`: the length of a word of tokens is `#a·a + #b·b + #c·c`.
* `walk_total`: the word of the base walk has total length `M e (3f² − e²)` (the sum of the step lengths is the
  base, `walkT_dist_sum`).
* `b1_of_total`: **Proposition B1** for such a word: if it has at least `f` `c`-tokens and `f ≤ 2Me < f+e`, it has
  no `a`-token and exactly `2Me` `c`-tokens (`band_lemma`).
-/

namespace Erdos634.LaczJunction.Walk

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Grammar
open Erdos634.Draft.LaczFormal.Graph

variable {N : ℕ}

def countS (s : Side) (w : List Tok) : ℕ := w.countP (fun t => decide (t.side = s))

theorem total_eq_counts (e f : ℕ) (w : List Tok) :
    total e f w = countS .a w * ta e f + countS .b w * tb e f + countC w * tc e f := by
  induction w with
  | nil => simp [total, countS, countC]
  | cons t r ih =>
    have h1 : total e f (t :: r) = wt e f t + total e f r := by simp [total]
    rw [h1, ih]
    simp only [countS, countC, List.countP_cons]
    cases t <;> simp [wt, Tok.side, ta, tb, tc] <;> ring

theorem lenT_eq (e f : ℕ) (t : Tok) :
    lenOf (ta e f) (tb e f) (tc e f) t.side = (wt e f t : ℝ) := by
  cases t <;> simp [lenOf, wt, Tok.side, ta, tb, tc]

theorem walk_total {D : CongruentDissection N} {e f M : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    {L : List (Fin N × Plane × Plane)} {d : V2}
    (hL : WalkT D.toDissection d (D.target.pts p) (D.target.pts q) L)
    (hbt : ∀ x ∈ L, ∃ Z, BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f))
        (elemTok D α β x).side (elemTok D α β x).left (elemTok D α β x).right x.1 x.2.1 x.2.2 Z)
    (hbase : dist (D.target.pts p) (D.target.pts q) = ((M * e * (3 * f ^ 2 - e ^ 2) : ℕ) : ℝ)) :
    total e f (L.map (elemTok D α β)) = M * e * (3 * f ^ 2 - e ^ 2) := by
  have hsum := walkT_dist_sum hL
  have h2 : (L.map fun x => dist x.2.1 x.2.2) = L.map (fun x => ((wt e f (elemTok D α β x) : ℕ) : ℝ)) := by
    apply List.map_congr_left
    intro x hx
    obtain ⟨Z, hZ⟩ := hbt x hx
    rw [← lenT_eq]
    exact hZ.length
  rw [h2, hbase] at hsum
  have h3 : (((L.map (elemTok D α β)).map (wt e f)).sum : ℝ) =
      ((M * e * (3 * f ^ 2 - e ^ 2) : ℕ) : ℝ) := by
    rw [← hsum, List.map_map]
    push_cast [Nat.cast_list_sum]
    simp [Function.comp_def, List.map_map]
  exact_mod_cast h3

/-- **Proposition B1 (counts).** -/
theorem b1_of_total (e f M : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f) (hM : 1 ≤ M)
    (hlo : f ≤ 2 * M * e) (hhi : 2 * M * e < f + e) (w : List Tok)
    (htot : total e f w = M * e * (3 * f ^ 2 - e ^ 2)) (hC : f ≤ countC w) :
    (∀ t ∈ w, t.side ≠ .a) ∧ countC w = 2 * M * e := by
  rw [total_eq_counts] at htot
  obtain ⟨h0, -, h2⟩ := band_lemma e f M (countS .a w) (countS .b w) (countC w) he hef hcop hM hlo hhi
    htot hC
  refine ⟨fun t ht hta => ?_, h2⟩
  have : 0 < countS .a w := by
    unfold countS
    exact List.countP_pos_iff.mpr ⟨t, ht, by simpa using hta⟩
  omega

/-- Thin range: a word of the right total length cannot have `f` `c`-tokens if `2Me < f`. -/
theorem b1_thin (e f M : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f) (hM : 1 ≤ M)
    (hlt : 2 * M * e < f) (w : List Tok)
    (htot : total e f w = M * e * (3 * f ^ 2 - e ^ 2)) (hC : f ≤ countC w) : False := by
  rw [total_eq_counts] at htot
  exact band_lemma_thin e f M _ _ _ he hef hcop hM hlt htot hC

#print axioms b1_of_total
#print axioms walk_total

end Erdos634.LaczJunction.Walk
