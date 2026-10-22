-- Draft/LaczFormalSWWWit.lean -- Snover-Waiveris-Williams (Discrete Math 91 (1991) 193-200): the three outcomes of
-- `LaczFormal.reptile_SWW` (N = k^2, N = A^2+B^2 with a right tile, N = 3m^2 with the 30-60-90 tile) are each
-- realised by a real `CongruentDissection` whose target is similar to the tile, and the theorem FIRES on each.
-- NOTE, UNAUDITED.  Credit: Snover-Waiveris-Williams, Golomb (rep-tiles), Beeson, Beeson-Rosu, Niven, Laczkovich.
import Erdos634.Draft.LaczFormalT6
import Erdos634.Draft.LaczFormalL8Wit
import Erdos634.Draft.HBCFalse3

open scoped Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional

namespace Erdos634.Draft.LaczFormal

theorem not_square_three : ¬ IsSquare 3 := by
  rintro ⟨r, hr⟩
  have : r ≤ 1 := by nlinarith
  interval_cases r <;> omega

theorem not_square_two : ¬ IsSquare 2 := by
  rintro ⟨r, hr⟩
  have : r ≤ 1 := by nlinarith
  interval_cases r <;> omega

/-- Outcome `N = k^2` (here `N = 4`, the scale-2 ladder of the equilateral tile): the hypothesis `SimilarTM` holds and
the theorem returns the first disjunct. -/
theorem sww_outcome_square : ∃ D : CongruentDissection 4, SimilarTM D ∧ IsSquare 4 :=
  ⟨D_i, D_i_similar, ⟨2, by norm_num⟩⟩

/-- Outcome `N = 3 m^2` (`N = 3`, the 30-60-90 triangle cut into three copies): `SimilarTM` is witnessed, `3` is not a
square, and `reptile_SWW` yields `3 = 3 m^2` with tile angles `(pi/6, pi/3, pi/2)`.  (The sum-of-two-squares disjunct is
refuted by arithmetic, so the output is genuinely the third disjunct.) -/
theorem sww_outcome_three :
    ∃ D : CongruentDissection 3, SimilarTM D ∧ ¬ IsSquare 3 ∧
      (∃ m : ℕ, 3 = 3 * m ^ 2) ∧ TileAngles D (Real.pi / 6) (Real.pi / 3) (Real.pi / 2) := by
  have hs : SimilarTM Erdos634.Draft.HBCFalse3.D3 := ⟨Erdos634.Draft.HBCFalse3.s, 1, Erdos634.Draft.HBCFalse3.D3_sim⟩
  refine ⟨_, hs, not_square_three, ?_⟩
  rcases reptile_SWW _ hs with h | ⟨A, B, hAB, -⟩ | h
  · exact absurd h not_square_three
  · exact absurd ⟨A, B, hAB⟩ Erdos634.Draft.HBCFalse3.three_not_sumsq
  · exact h

/-- Outcome `N = A^2 + B^2` with a right tile (`N = 2`, the right isosceles triangle cut along its altitude): `SimilarTM`
is witnessed, `2` is not a square, and `reptile_SWW` yields `2 = A^2+B^2` with `RightLegs`. -/
theorem sww_outcome_sumsq :
    ∃ D : CongruentDissection 2, SimilarTM D ∧ ¬ IsSquare 2 ∧
      ∃ A B : ℕ, 2 = A ^ 2 + B ^ 2 ∧ RightLegs D A B := by
  obtain ⟨D, ht, hm⟩ := exists_D2b
  have hs : SimilarTM D := D2b_similar D ht hm
  refine ⟨D, hs, not_square_two, ?_⟩
  rcases reptile_SWW D hs with h | h | ⟨⟨m, hm3⟩, -⟩
  · exact absurd h not_square_two
  · exact h
  · have : m ≤ 1 := by nlinarith
    interval_cases m <;> omega

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.sww_outcome_square
#print axioms Erdos634.Draft.LaczFormal.sww_outcome_three
#print axioms Erdos634.Draft.LaczFormal.sww_outcome_sumsq
