-- Draft/LaczFormalIIcWN42.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, Lemma 6.2 (`IIcNoKites`), step (h), part 3:
-- `arc_simple`: if the closed chord p(a+d) -- p a meets `edgeSet p` only in its endpoints, then `arcPoly p a d` is a simple polygon.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN41

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

theorem edge_lt (p : Fin n → ℂ) (a : Fin n) {d : ℕ} (i : Fin (d + 1)) (hi : i.val < d) :
    arcPoly p a d i = p (phi a i.val) ∧ arcPoly p a d (i + 1) = p (phi a (i.val + 1)) := by
  refine ⟨rfl, ?_⟩
  have e : i = ⟨i.val, by omega⟩ := rfl
  rw [e]
  exact arcPoly_succ p a i.val hi

theorem arc_simple {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (a : Fin n) {d : ℕ} (hd2 : 2 ≤ d) (hdn : d + 2 ≤ n)
    (hchord : ∀ z ∈ segment ℝ (p (phi a d)) (p a), z ∈ edgeSet p → z = p a ∨ z = p (phi a d)) :
    SimplePoly (arcPoly p a d) := by
  intro i j hij z ⟨hz1, hz2⟩
  by_cases hi : i = Fin.last d
  · subst hi
    have hj : j ≠ Fin.last d := fun h => hij h.symm
    have hjlt : j.val < d := by
      have := j.isLt
      have : j.val ≠ d := fun h' => hj (Fin.ext (by simpa using h'))
      omega
    obtain ⟨e1, e2⟩ := edge_lt p a j hjlt
    rw [arcPoly_last, arcPoly_last_succ] at hz1 ⊢
    rw [e1, e2] at hz2
    rw [e1, e2]
    exact chord_edge hs hinj a hd2 hdn hchord hjlt hz1 hz2
  · have hilt : i.val < d := by
      have := i.isLt
      have : i.val ≠ d := fun h' => hi (Fin.ext (by simpa using h'))
      omega
    obtain ⟨e1, e2⟩ := edge_lt p a i hilt
    by_cases hj : j = Fin.last d
    · subst hj
      rw [arcPoly_last, arcPoly_last_succ] at hz2 ⊢
      rw [e1, e2] at hz1 ⊢
      have := chord_edge hs hinj a hd2 hdn hchord hilt hz2 hz1
      exact ⟨this.2, this.1⟩
    · have hjlt : j.val < d := by
        have := j.isLt
        have : j.val ≠ d := fun h' => hj (Fin.ext (by simpa using h'))
        omega
      obtain ⟨f1, f2⟩ := edge_lt p a j hjlt
      rw [e1, e2] at hz1 ⊢
      rw [f1, f2] at hz2 ⊢
      have hne : phi a i.val ≠ phi a j.val := by
        intro h
        have := phi_inj_nat a (by omega) (by omega) h
        exact hij (Fin.ext this)
      simp only [phi_succ] at hz1 hz2 ⊢
      have := hs (phi a i.val) (phi a j.val) hne z ⟨hz1, hz2⟩
      exact this

end Erdos634.Draft.LaczFormal.WN
