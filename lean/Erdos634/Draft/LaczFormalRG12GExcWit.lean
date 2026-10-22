-- Draft/LaczFormalRG12GExcWit.lean -- SHARPNESS witnesses for `fig5_comb` (Laczkovich DCG 48 (2012), Fig. 5 exclusion): with a = 0 the label pattern 2,2,0,1,1,0 (period 6) satisfies every hypothesis of `fig5_comb`
-- except the alpha-pair adjacency (its beta pair is adjacent: positions 3,4), and the pattern 2,2,1,0,0,1 satisfies all but the beta-pair adjacency.  So each of the two kite pairs is really used, and the
-- hypotheses are not jointly unsatisfiable for trivial reasons.  (The FULL hypothesis set of `kite_vertex_no_gamma_line` has no joint model: it is a step of the proof by contradiction of Lemma 6.2.  Individual
-- hypotheses: `AngGen` is witnessed by `angGen_witness`, `GKite` and `Fan6` by earlier witnesses; `GExc` itself is only a definition, no tiling with a `GExc` edge is exhibited here.)  NOTE, UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Sect. 6.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12GExc

namespace Erdos634.Draft.LaczFormal.RG

def ℓW1 (n : ℕ) : Fin 3 := ![2, 2, 0, 1, 1, 0] ⟨n % 6, Nat.mod_lt _ (by norm_num)⟩
def ℓW2 (n : ℕ) : Fin 3 := ![2, 2, 1, 0, 0, 1] ⟨n % 6, Nat.mod_lt _ (by norm_num)⟩

theorem ℓW1_periodic : ∀ n, ℓW1 (n + 6) = ℓW1 n := by intro n; simp [ℓW1, Nat.add_mod_right]
theorem ℓW2_periodic : ∀ n, ℓW2 (n + 6) = ℓW2 n := by intro n; simp [ℓW2, Nat.add_mod_right]

/-- All hypotheses of `fig5_comb` hold except the alpha pair (beta pair at positions 3, 4). -/
theorem fig5_comb_sharp_beta :
    ℓW1 0 = 2 ∧ ℓW1 (0 + 1) = 2 ∧ (ℓW1 (0 + 1) ≠ ℓW1 (0 + 2) ∧ ℓW1 (0 + 1) ≠ ℓW1 (0 + 3) ∧ ℓW1 (0 + 2) ≠ ℓW1 (0 + 3)) ∧
    (ℓW1 (0 + 4) ≠ ℓW1 (0 + 5) ∧ ℓW1 (0 + 4) ≠ ℓW1 (0 + 6) ∧ ℓW1 (0 + 5) ≠ ℓW1 (0 + 6)) ∧ (ℓW1 3 = 1 ∧ ℓW1 (3 + 1) = 1) := by
  decide

/-- All hypotheses of `fig5_comb` hold except the beta pair (alpha pair at positions 3, 4). -/
theorem fig5_comb_sharp_alpha :
    ℓW2 0 = 2 ∧ ℓW2 (0 + 1) = 2 ∧ (ℓW2 (0 + 1) ≠ ℓW2 (0 + 2) ∧ ℓW2 (0 + 1) ≠ ℓW2 (0 + 3) ∧ ℓW2 (0 + 2) ≠ ℓW2 (0 + 3)) ∧
    (ℓW2 (0 + 4) ≠ ℓW2 (0 + 5) ∧ ℓW2 (0 + 4) ≠ ℓW2 (0 + 6) ∧ ℓW2 (0 + 5) ≠ ℓW2 (0 + 6)) ∧ (ℓW2 3 = 0 ∧ ℓW2 (3 + 1) = 0) := by
  decide

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.fig5_comb_sharp_beta
#print axioms Erdos634.Draft.LaczFormal.RG.fig5_comb_sharp_alpha
