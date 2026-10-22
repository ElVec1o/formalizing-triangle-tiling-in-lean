-- Draft/CaseALemmaVWitness.lean — joint witness for Draft/CaseALemmaVDissection.lean `lemmaV`
-- (Case A node A2, Lemma V): the real `CongruentDissection 2` of CaseALemmaHPiFour (isosceles right
-- triangle cut by its altitude), model angles (π/4, π/2, π/4) = (1, 2, 1)·π/4, n = 4, ℓ = 3.
-- Every hypothesis of `lemmaV` discharged on a genuine dissection; conclusion v₃(2) = 0 even.
-- `lemmaV_prime` has no joint witness: no Lean dissection with an odd prime N and rational angles
-- exists in the corpus (by Lemma V + the paper, none with N ∤ n can exist).
-- Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).  Formalization debt; NOT /goal progress.  H59: no (e, f) evaluated.
import Erdos634.Draft.CaseALemmaVDissection
import Erdos634.Draft.CaseALemmaHPiFour

namespace Erdos634.Draft.CaseALemmaVWitness

open Erdos634.Geometry Erdos634.Draft.CaseALemmaHPiFour Erdos634.Geometry.CaseA.LemmaV

theorem model_angles (k : Fin 3) :
    dissection.model.angleAt k = (![1, 2, 1] : Fin 3 → ℕ) k * Real.pi / (4 : ℕ) := by
  have h0 := model_angleAt0; have h1 := model_angleAt1
  have hs := dissection.model.angleAt_sum
  fin_cases k <;> simp <;> linarith

theorem lemmaV_witness : Even (padicValNat 3 2) :=
  lemmaV dissection (n := 4) (by norm_num) ![1, 2, 1] model_angles (by norm_num) (by norm_num)

end Erdos634.Draft.CaseALemmaVWitness

#print axioms Erdos634.Draft.CaseALemmaVWitness.lemmaV_witness
