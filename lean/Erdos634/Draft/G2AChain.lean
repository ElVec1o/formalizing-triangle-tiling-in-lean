/-
Draft/G2AChain.lean — an abstract combinatorial lemma on a finite cover of `[0,1]` by intervals with disjoint interiors:
if every interval has a "marked end" (left or right), no interval starting at `0` has its left end marked, and the right end of an
interval and the left end of its right neighbour are never both marked, then NO interval has its left end marked.
(Used for the `γ = 2α` legs with no `b`-edge: every `a`/`c` edge has exactly one `β` end; one `β` per boundary point.)
Pure real/Finset arithmetic.  UNAUDITED.  No sorry, no native_decide.
-/
import Mathlib

namespace Erdos634.Draft.G2AChain

/-- **Left neighbour.**  Every interval with `lo e > 0` has an interval `e'` ending exactly at `lo e`. -/
theorem left_neighbour {ι : Type*} [DecidableEq ι] (E : Finset ι) (lo hi : ι → ℝ)
    (hlt : ∀ e ∈ E, lo e < hi e) (h0 : ∀ e ∈ E, 0 ≤ lo e) (h1 : ∀ e ∈ E, hi e ≤ 1)
    (hgap : ∀ e ∈ E, ∀ e' ∈ E, e ≠ e' → hi e ≤ lo e' ∨ hi e' ≤ lo e)
    (hcov : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ e ∈ E, lo e ≤ t ∧ t ≤ hi e)
    {e : ι} (he : e ∈ E) (hpos : 0 < lo e) : ∃ e' ∈ E, e' ≠ e ∧ hi e' = lo e := by
  classical
  set S := E.filter (fun e'' => lo e'' < lo e) with hS
  have hle1 : lo e ≤ 1 := (hlt e he).le.trans (h1 e he)
  have hne : S.Nonempty := by
    obtain ⟨e₀, he₀, hl, -⟩ := hcov (lo e / 2) (by linarith) (by linarith)
    exact ⟨e₀, Finset.mem_filter.mpr ⟨he₀, by linarith⟩⟩
  obtain ⟨e', he'S, hmax⟩ := Finset.exists_max_image S hi hne
  have he'E : e' ∈ E := (Finset.mem_filter.mp he'S).1
  have he'lt : lo e' < lo e := (Finset.mem_filter.mp he'S).2
  have hne' : e' ≠ e := fun h => by rw [h] at he'lt; exact lt_irrefl _ he'lt
  have hle : hi e' ≤ lo e := by
    rcases hgap e' he'E e he hne' with h | h
    · exact h
    · exfalso
      have := hlt e he
      linarith
  refine ⟨e', he'E, hne', le_antisymm hle ?_⟩
  by_contra hcon
  push Not at hcon
  have hhi0 : 0 ≤ hi e' := (h0 e' he'E).trans (hlt e' he'E).le
  obtain ⟨e₁, he₁, hl, hr⟩ := hcov ((hi e' + lo e) / 2) (by linarith) (by linarith)
  have he₁S : e₁ ∈ S := Finset.mem_filter.mpr ⟨he₁, by linarith⟩
  have := hmax e₁ he₁S
  linarith

/-- **No left-marked interval.** -/
theorem no_left_marked {ι : Type*} [DecidableEq ι] (E : Finset ι) (lo hi : ι → ℝ)
    (hlt : ∀ e ∈ E, lo e < hi e) (h0 : ∀ e ∈ E, 0 ≤ lo e) (h1 : ∀ e ∈ E, hi e ≤ 1)
    (hgap : ∀ e ∈ E, ∀ e' ∈ E, e ≠ e' → hi e ≤ lo e' ∨ hi e' ≤ lo e)
    (hcov : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ e ∈ E, lo e ≤ t ∧ t ≤ hi e)
    (L R : ι → Prop) (hdich : ∀ e ∈ E, L e ∨ R e)
    (hL0 : ∀ e ∈ E, lo e = 0 → ¬ L e)
    (hclash : ∀ e ∈ E, ∀ e' ∈ E, e' ≠ e → hi e' = lo e → L e → R e' → False) :
    ∀ e ∈ E, ¬ L e := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨e₀, he₀, hL₀⟩ := hcon
  have hne : (E.filter L).Nonempty := ⟨e₀, Finset.mem_filter.mpr ⟨he₀, hL₀⟩⟩
  obtain ⟨e, heS, hmin⟩ := Finset.exists_min_image (E.filter L) lo hne
  have heE : e ∈ E := (Finset.mem_filter.mp heS).1
  have heL : L e := (Finset.mem_filter.mp heS).2
  rcases (h0 e heE).eq_or_lt with h | h
  · exact hL0 e heE h.symm heL
  · obtain ⟨e', he'E, hne', hhi⟩ := left_neighbour E lo hi hlt h0 h1 hgap hcov heE h
    have hL' : L e' := by
      rcases hdich e' he'E with hl | hr
      · exact hl
      · exact (hclash e heE e' he'E hne' hhi heL hr).elim
    have := hmin e' (Finset.mem_filter.mpr ⟨he'E, hL'⟩)
    have := hlt e' he'E
    linarith

end Erdos634.Draft.G2AChain

#print axioms Erdos634.Draft.G2AChain.left_neighbour
#print axioms Erdos634.Draft.G2AChain.no_left_marked
