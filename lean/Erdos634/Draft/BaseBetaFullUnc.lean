-- Draft/BaseBetaFullUnc.lean — `thm:basebeta-full-unc` (companion) as ONE Lean statement:
-- no m = 1 base-β tiling for any coprime 1 ≤ e < f. The union of three separately audited clauses:
-- e = f − 1 (`R1Final.r1_no_tiling`), e = 1 with f ≥ 3 (`E1BaseWord.e1_family_f_ge_3_of_sides`),
-- 2 ≤ e ≤ f − 2 (`TheoremHCongruent.theorem_H_of_sides`). The member (1,2) falls under e = f − 1.
-- No new mathematics: a case split. Formalization debt, not /goal progress.
import Erdos634.Draft.TheoremHCongruent
import Erdos634.Draft.R1Final
import Erdos634.E1BaseWord

namespace Erdos634.Draft.BaseBetaFullUnc

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.BaseBetaTargetCoord

theorem basebeta_full_unc {N : ℕ} (D₀ : CongruentDissection N) {e f : ℕ}
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D₀.target.Congruent (baseBetaTarget (e : ℝ) f (by exact_mod_cast (show 0 < e by omega))
      (by exact_mod_cast hef)))
    (h0 : sideOpp D₀.model 0 = (e : ℝ) * f) (h1 : sideOpp D₀.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D₀.model 2 = (f : ℝ) ^ 2) : False := by
  by_cases hR1 : e + 1 = f
  · exact Erdos634.Draft.R1Final.r1_no_tiling D₀ he hR1 htgt D₀.model h0 h1 h2
      (Tri.Congruent.refl _)
  · by_cases he1 : e = 1
    · subst he1
      have hf3 : 3 ≤ f := by omega
      refine Erdos634.E1BaseWord.e1_family_f_ge_3_of_sides D₀ hf3 ?_ ?_ ?_ h2
      · convert htgt using 2 <;> simp
      · simpa using h0
      · simpa using h1
    · exact Erdos634.Draft.TheoremHCongruent.theorem_H_of_sides D₀ hco (by omega) (by omega)
        _ _ htgt h0 h1 h2

/-- Non-vacuity: at every coprime `1 ≤ e < f` the tile hypotheses are met by a real `Tri`
(`ModelWitnessE.tileTri`), and the target hypothesis by `Congruent.refl`; only the dissection
itself — the thing excluded — is not exhibited. -/
theorem hyps_nonvacuous {e f : ℕ} (he : 1 ≤ e) (hef : e < f) :
    ∃ T : Tri, sideOpp T 0 = (e : ℝ) * f ∧ sideOpp T 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧
      sideOpp T 2 = (f : ℝ) ^ 2 :=
  ⟨_, Erdos634.Draft.TheoremHCongruent.tileTri_sides
    (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)⟩

end Erdos634.Draft.BaseBetaFullUnc

#print axioms Erdos634.Draft.BaseBetaFullUnc.basebeta_full_unc
#print axioms Erdos634.Draft.BaseBetaFullUnc.hyps_nonvacuous
