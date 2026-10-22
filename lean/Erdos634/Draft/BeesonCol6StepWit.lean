import Erdos634.Draft.BeesonCol6Step

/-!
# Non-vacuity of Lemma 29/30 hypotheses (`BeesonCol6Step`)

NOTE, UNAUDITED.  Credit: Beeson (arXiv 1206.2229 v4), Beeson-Rosu, Laczkovich.  The 3-4-5 triangle `(0,0),(3,0),(0,4)`
(pairwise distinct sides) and the two-tile parallelogram it forms with its point reflection in the midpoint of the
hypotenuse: `Model`, `Cong`, `Sep`, `Conn 0 1`, `ReachIn {0,1} 0 1` all hold.
-/

namespace Erdos634.BeesonCol6

/-- model: the 3-4-5 triangle. -/
noncomputable def wM : Model where
  P := ![((0 : ℝ), (0 : ℝ)), (3, 0), (0, 4)]
  nondeg := by simp [cr]
  distinct := by
    intro p q p' q' hpq hpq' h
    fin_cases p <;> fin_cases q <;> fin_cases p' <;> fin_cases q' <;> simp at hpq hpq' ⊢ <;>
      simp [sq] at h <;> norm_num at h

/-- two tiles: the model and its reflection in the midpoint of side `{1,2}` (vertex labels `1, 2` swapped). -/
def wv : Fin 2 → Fin 3 → ℝ × ℝ
  | 0 => ![((0 : ℝ), (0 : ℝ)), (3, 0), (0, 4)]
  | 1 => ![((3 : ℝ), (4 : ℝ)), (0, 4), (3, 0)]

theorem w_cong : Cong wM wv := by
  intro i p q
  fin_cases i <;> fin_cases p <;> fin_cases q <;> simp [wM, wv, sq] <;> norm_num

theorem w_sep : Sep wv := by
  intro i j p q p' q' r r' hij hpq hpr hqr hp'q' hp'r' hq'r' e1 e2
  fin_cases i <;> fin_cases j <;> simp at hij <;> fin_cases p <;> fin_cases q <;> simp at hpq <;> fin_cases r <;>
    simp at hpr hqr <;> fin_cases p' <;> fin_cases q' <;> simp at hp'q' <;> fin_cases r' <;> simp at hp'r' hq'r' <;>
    simp [wv, Prod.ext_iff] at e1 e2 <;> simp [wv, cr] <;> norm_num

theorem w_conn : Conn wv 0 1 := by
  refine ⟨by decide, 1, 2, 2, 1, by decide, ?_, ?_, by decide⟩ <;> simp [wv]

theorem w_reach : ReachIn wv (Set.univ : Set (Fin 2)) 0 1 :=
  Relation.ReflTransGen.single ⟨trivial, trivial, w_conn⟩

/-- Lemma 29 on the witness: the hypotenuse of tile 0 and that of tile 1 are parallel (instance of the theorem). -/
theorem w_lemma29 : cr (wv 0 2 - wv 0 1) (wv 1 2 - wv 1 1) = 0 :=
  lemma29_parallel w_cong w_sep w_reach 1 2 1 2 (by decide) (by decide) (by simp [wv, sq])

#print axioms Erdos634.BeesonCol6.w_sep
#print axioms Erdos634.BeesonCol6.w_lemma29

end Erdos634.BeesonCol6
