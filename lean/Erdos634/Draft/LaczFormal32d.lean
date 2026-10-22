-- Draft/LaczFormal32d.lean -- WITNESS that the hypotheses of `lemma32_arith` are satisfiable: the 6-tile barycentric split of an equilateral
-- triangle into (pi/6, pi/3, pi/2) triangles.  Rows: 3 corners (2,0,0), centre (0,6,0), 3 edge midpoints (0,0,2).  Label NOTE, UNAUDITED.
-- Credit: Laczkovich (DCG 19 (1998) Lemma 10; DCG 48 (2012) Lemma 3.2), Beeson, Beeson-Zhang.
import Mathlib
import Erdos634.Draft.LaczFormal32c

open scoped BigOperators

namespace Erdos634.Draft.LaczFormal32

def wP : Fin 7 → ℕ := ![2, 2, 2, 0, 0, 0, 0]
def wQ : Fin 7 → ℕ := ![0, 0, 0, 6, 0, 0, 0]
def wR : Fin 7 → ℕ := ![0, 0, 0, 0, 2, 2, 2]
noncomputable def wc : Fin 7 → ℝ := ![1/3, 1/3, 1/3, 2, 1, 1, 1]
noncomputable def wa : Fin 7 → ℝ := fun _ => 1/3
def wC : Finset (Fin 7) := {0, 1, 2}

theorem witness_good : Good wC wa (1/6) (1/3) (1/2) wP wQ wR wc := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k; fin_cases k <;> simp [wP, wQ, wR, wc] <;> norm_num
  · intro k hk
    simp only [wC, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl <;> left <;> simp [wc, wa]
  · intro k hk
    simp only [wC, Finset.mem_insert, Finset.mem_singleton] at hk
    fin_cases k <;> simp_all [wc]
  · simp [Fin.sum_univ_succ, wP, wQ]
  · simp [Fin.sum_univ_succ, wQ, wR]
  · exact ⟨0, by simp [wP, wQ]⟩
  · exact ⟨0, by simp [wP, wR]⟩
  · exact ⟨3, by simp [wQ, wR]⟩

theorem witness_hyps :
    (∀ k ∈ wC, 0 < wa k ∧ wa k < 2 ∧ wa k ≠ 1) ∧ ∑ k ∈ wC, wa k < wC.card := by
  refine ⟨?_, ?_⟩
  · intro k _; simp [wa]; norm_num
  · simp [wC, wa]

theorem witness_conclusion :
    (1/6 : ℝ) ∈ Submodule.span ℚ (insert (1:ℝ) (wa '' (wC : Set (Fin 7)))) :=
  (lemma32_arith (by norm_num) (by norm_num) (by norm_num) (by norm_num) witness_hyps.1 witness_hyps.2 witness_good).1

#print axioms witness_conclusion

end Erdos634.Draft.LaczFormal32
