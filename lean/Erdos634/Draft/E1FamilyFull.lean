-- Draft/E1FamilyFull.lean — `thm:e1family` (companion) for EVERY f ≥ 2, in
-- `E1BaseWord.e1_family_f_ge_3_congruent`'s form. Composition only; no new mathematics.
--   f ≥ 3 : `E1BaseWord.e1_family_f_ge_3_congruent` (the march).
--   f = 2 : `Draft.R1Final.r1_n11` (R1, the thick line e = f − 1 at (e,f) = (1,2)), whose hypotheses
--           are literally the same objects: `baseBetaTarget 1 2` and `MarchCompose.modelTri 2`
--           (proof arguments are irrelevant, so the two statements are definitionally aligned).
-- f = 2 (N = 11) is a REPRODUCTION of the settled row (data/SETTLED.tsv, 135-node search) by a
-- search-free route. NOT covered: the "in particular" prime clause (composes outside the theorem).
import Erdos634.E1BaseWord
import Erdos634.Draft.R1Final

namespace Erdos634.Draft.E1FamilyFull

open Erdos634.Geometry Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose

/-- **`thm:e1family`, every `f ≥ 2`.** No congruent dissection (any `N`, reflections allowed, not
edge-to-edge) of a triangle congruent to the `m = 1`, `e = 1` base-β target `baseBetaTarget 1 n`
into copies of a triangle congruent to the tile `modelTri n = (n, n² − 1, n²)`. -/
theorem e1_family_congruent {N : ℕ} (D₀ : CongruentDissection N) {n : ℕ} (hn2 : 2 ≤ n)
    (htgt : D₀.target.Congruent
      (baseBetaTarget 1 n one_pos (by exact_mod_cast (show 1 < n by omega))))
    (hmod : D₀.model.Congruent (modelTri n (by exact_mod_cast (show 1 < n by omega)))) :
    False := by
  rcases Nat.lt_or_ge n 3 with h | h3
  · obtain rfl : n = 2 := by omega
    exact Erdos634.Draft.R1Final.r1_n11 D₀ htgt hmod
  · exact Erdos634.E1BaseWord.e1_family_f_ge_3_congruent D₀ h3 htgt hmod

/-- **Non-vacuity**, for each branch of the case split (`n = 2` and `n = 3`): the parameter
hypothesis holds, and each congruence hypothesis is satisfiable (reflexivity). The hypotheses are
jointly unsatisfiable — that is the theorem. -/
theorem hyps_nonvacuous :
    (2 ≤ (2 : ℕ) ∧
      (baseBetaTarget 1 ((2 : ℕ) : ℝ) one_pos (by norm_num)).Congruent
        (baseBetaTarget 1 ((2 : ℕ) : ℝ) one_pos (by norm_num)) ∧
      (modelTri ((2 : ℕ) : ℝ) (by norm_num)).Congruent (modelTri ((2 : ℕ) : ℝ) (by norm_num))) ∧
    (2 ≤ (3 : ℕ) ∧
      (baseBetaTarget 1 ((3 : ℕ) : ℝ) one_pos (by norm_num)).Congruent
        (baseBetaTarget 1 ((3 : ℕ) : ℝ) one_pos (by norm_num)) ∧
      (modelTri ((3 : ℕ) : ℝ) (by norm_num)).Congruent (modelTri ((3 : ℕ) : ℝ) (by norm_num))) :=
  ⟨⟨by norm_num, Tri.Congruent.refl _, Tri.Congruent.refl _⟩,
   ⟨by norm_num, Tri.Congruent.refl _, Tri.Congruent.refl _⟩⟩

/-- The model at `n = 2` really is the tile `(2, 3, 4)` (sides `n, n² − 1, n²`). -/
theorem model_sides_2 :
    TilePlacement.sideOpp (modelTri ((2 : ℕ) : ℝ) (by norm_num)) 0 = 2 ∧
    TilePlacement.sideOpp (modelTri ((2 : ℕ) : ℝ) (by norm_num)) 1 = 3 ∧
    TilePlacement.sideOpp (modelTri ((2 : ℕ) : ℝ) (by norm_num)) 2 = 4 := by
  obtain ⟨m0, m1, m2⟩ := modelTri_sides (f := ((2 : ℕ) : ℝ)) (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · rw [m0]; norm_num
  · rw [m1]; norm_num
  · rw [m2]; norm_num

end Erdos634.Draft.E1FamilyFull

#print axioms Erdos634.Draft.E1FamilyFull.e1_family_congruent
#print axioms Erdos634.Draft.E1FamilyFull.hyps_nonvacuous
#print axioms Erdos634.Draft.E1FamilyFull.model_sides_2
