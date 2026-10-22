-- Draft/LaczFormalIIcWN40.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, Lemma 6.2 (`IIcNoKites`), step (h) ("C1 is convex"), part 1:
-- the polygon `arcPoly p a d` with vertices p a, p (a+1), ..., p (a+d), closed by the chord p (a+d) -> p a; its edge set; it is a simple injective polygon
-- when the open chord misses `edgeSet p`.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN38

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

/-- The polygon with vertices `p a, ..., p (a+d)` (indices mod `n`), closed by the chord from `p (a+d)` back to `p a`. -/
def arcPoly (p : Fin n → ℂ) (a : Fin n) (d : ℕ) : Fin (d + 1) → ℂ := fun i => p (phi a i.val)

theorem arcPoly_succ (p : Fin n → ℂ) (a : Fin n) {d : ℕ} (i : ℕ) (h : i < d) :
    arcPoly p a d ((⟨i, by omega⟩ : Fin (d + 1)) + 1) = p (phi a (i + 1)) := by
  have : ((⟨i, by omega⟩ : Fin (d + 1)) + 1).val = i + 1 := by
    exact Fin.val_add_one_of_lt (by rw [Fin.lt_def]; simp; omega)
  simp only [arcPoly, this]

theorem arcPoly_val (p : Fin n → ℂ) (a : Fin n) {d : ℕ} (i : ℕ) (h : i < d + 1) :
    arcPoly p a d ⟨i, h⟩ = p (phi a i) := rfl

theorem arcPoly_last_succ (p : Fin n → ℂ) (a : Fin n) (d : ℕ) : arcPoly p a d (Fin.last d + 1) = p a := by
  rw [Fin.last_add_one]
  simp [arcPoly, phi]

theorem arcPoly_last (p : Fin n → ℂ) (a : Fin n) (d : ℕ) : arcPoly p a d (Fin.last d) = p (phi a d) := by
  simp [arcPoly]

theorem mem_edgeSet_arc (p : Fin n → ℂ) (a : Fin n) (d : ℕ) (z : ℂ) :
    z ∈ edgeSet (arcPoly p a d) ↔
      (∃ i : ℕ, i < d ∧ z ∈ segment ℝ (p (phi a i)) (p (phi a (i + 1)))) ∨ z ∈ segment ℝ (p (phi a d)) (p a) := by
  unfold edgeSet
  rw [Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    by_cases h : i = Fin.last d
    · subst h
      right
      rwa [arcPoly_last, arcPoly_last_succ] at hi
    · left
      have hlt : i.val < d := by
        have := i.isLt
        have : i.val ≠ d := fun h' => h (Fin.ext (by simpa using h'))
        omega
      refine ⟨i.val, hlt, ?_⟩
      have e1 : i = ⟨i.val, by omega⟩ := rfl
      rw [e1, arcPoly_succ p a i.val hlt] at hi
      simpa [arcPoly] using hi
  · rintro (⟨i, hi, hz⟩ | hz)
    · refine ⟨⟨i, by omega⟩, ?_⟩
      rw [arcPoly_succ p a i hi]
      simpa [arcPoly] using hz
    · refine ⟨Fin.last d, ?_⟩
      rwa [arcPoly_last, arcPoly_last_succ]

end Erdos634.Draft.LaczFormal.WN
