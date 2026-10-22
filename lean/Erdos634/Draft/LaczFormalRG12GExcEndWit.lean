-- Draft/LaczFormalRG12GExcEndWit.lean -- label-level WITNESSES for the combinatorics `sc1_comb` of L7 (statement (ii)): both a straight pair (`gamma alpha beta gamma beta alpha`-type table, labels of the next three sectors pairwise distinct) and a kite pair
-- (`gamma alpha alpha beta beta gamma`) satisfy every hypothesis of `sc1_comb` (so the lemma is not vacuous).  The full hypothesis sets of `sc1_core`, `sc2_left`, `sc2_right`, `gexc_end_kite_or_exc` are NOT jointly witnessed: Case IIc with all
-- hypotheses is refuted by Lemma 6.2 / 6.3 (named).  NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12GExcEndSc1

namespace Erdos634.Draft.LaczFormal.RG

/-- Tables of (label, far label of the `p`-side, far label of the `q`-side) of six consecutive sectors. -/
def witS : Fin 6 → Fin 3 × Fin 3 × Fin 3 := ![(2, 0, 1), (0, 2, 1), (1, 0, 2), (0, 2, 1), (1, 2, 0), (2, 1, 0)]
def witK : Fin 6 → Fin 3 × Fin 3 × Fin 3 := ![(2, 0, 1), (0, 2, 1), (0, 1, 2), (1, 2, 0), (1, 0, 2), (2, 1, 0)]

def labW (t : Fin 6 → Fin 3 × Fin 3 × Fin 3) (n : ℕ) : Fin 3 := (t ⟨n % 6, Nat.mod_lt _ (by norm_num)⟩).1
def pfW (t : Fin 6 → Fin 3 × Fin 3 × Fin 3) (n : ℕ) : Fin 3 := (t ⟨n % 6, Nat.mod_lt _ (by norm_num)⟩).2.1
def qfW (t : Fin 6 → Fin 3 × Fin 3 × Fin 3) (n : ℕ) : Fin 3 := (t ⟨n % 6, Nat.mod_lt _ (by norm_num)⟩).2.2

theorem witS_perm : ∀ n, labW witS n ≠ pfW witS n ∧ labW witS n ≠ qfW witS n ∧ pfW witS n ≠ qfW witS n := by
  have key : ∀ r : Fin 6, (witS r).1 ≠ (witS r).2.1 ∧ (witS r).1 ≠ (witS r).2.2 ∧ (witS r).2.1 ≠ (witS r).2.2 := by decide
  exact fun n => key _

theorem witK_perm : ∀ n, labW witK n ≠ pfW witK n ∧ labW witK n ≠ qfW witK n ∧ pfW witK n ≠ qfW witK n := by
  have key : ∀ r : Fin 6, (witK r).1 ≠ (witK r).2.1 ∧ (witK r).1 ≠ (witK r).2.2 ∧ (witK r).2.1 ≠ (witK r).2.2 := by decide
  exact fun n => key _

/-- The conclusion of `sc1_comb` holds for the straight table (all hypotheses verified by evaluation). -/
theorem witS_comb : labW witS (0 + 1) ≠ 2 ∧ labW witS (0 + 2) ≠ 2 ∧ labW witS (0 + 3) ≠ 2 ∧ qfW witS (0 + 1) ≠ 2 ∧ pfW witS (0 + 2) ≠ 2 ∧
    qfW witS (0 + 2) = 2 ∧ pfW witS (0 + 3) = 2 :=
  sc1_comb (labW witS) (pfW witS) (qfW witS) 0 witS_perm (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The conclusion of `sc1_comb` holds for the kite table. -/
theorem witK_comb : labW witK (0 + 1) ≠ 2 ∧ labW witK (0 + 2) ≠ 2 ∧ labW witK (0 + 3) ≠ 2 ∧ qfW witK (0 + 1) ≠ 2 ∧ pfW witK (0 + 2) ≠ 2 ∧
    qfW witK (0 + 2) = 2 ∧ pfW witK (0 + 3) = 2 :=
  sc1_comb (labW witK) (pfW witK) (qfW witK) 0 witK_perm (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Distinguishing feature: the straight table has three pairwise distinct labels `(m, m+1, m+2)`, the kite table does not. -/
theorem witS_straight : labW witS 0 ≠ labW witS 1 ∧ labW witS 0 ≠ labW witS 2 ∧ labW witS 1 ≠ labW witS 2 := by decide
theorem witK_kite : labW witK 1 = labW witK 2 := by decide

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.witS_comb
#print axioms Erdos634.Draft.LaczFormal.RG.witK_comb
