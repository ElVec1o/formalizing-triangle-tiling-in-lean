-- Draft/LaczFormalBZWit.lean -- WITNESS for Beeson-Zhang Theorem 5.2 (`RG.bz_thm52`) and its ingredients: the certified N = 1215 tiling (Herdt/Zhang; G3CEqui135Control.D) of the equilateral triangle of side 135*1890
-- by the tile 1890*(3,5,7) with gamma = 2 pi/3 and alpha not in Q pi satisfies EVERY hypothesis of `bz_thm52` (and of `bz_c_rational`, `bz_ab_comm`); the conclusions hold there (a/b = 3/5, c/a = 7/3).
-- This is the control that the hypotheses are not vacuous: they are jointly satisfied by a real tiling, while the hypothesis `NotComb` of `bz_lemma35` / `c not in Q a` of `bz_phi_eq` are exactly what fails there.
-- UNAUDITED.  Credit: Herdt, Zhang (the 1215-tiling), Beeson-Zhang, Laczkovich.
import Erdos634.Draft.LaczFormalBZ8
import Erdos634.Draft.G3CEqui135Control

open scoped Classical
open Erdos634.Geometry Erdos634.Draft.LaczFormal.Thm21 Erdos634.Draft.LaczFormal.RG Erdos634.Draft.LaczFormal.Graph

namespace Erdos634.Draft.LaczFormal.BZWit

open Erdos634.Draft.G3CEqui135Control

theorem dist_eq_oppLen (T : Tri) (j : Fin 3) : dist (T.pts j) (T.pts (j + 1)) = T.oppLen (j + 2) := by
  unfold Tri.oppLen
  have e1 : j + 2 + 1 = j := by fin_cases j <;> rfl
  have e2 : j + 2 + 2 = j + 1 := by fin_cases j <;> rfl
  rw [e1, e2]

/-- The target of the 1215-tiling has equal sides. -/
theorem heq : ∀ j : Fin 3, dist (D.target.pts j) (D.target.pts (j + 1)) = dist (D.target.pts 0) (D.target.pts 1) := by
  intro j
  have h0 : dist (D.target.pts 0) (D.target.pts 1) = D.target.oppLen 2 := dist_eq_oppLen D.target 0
  rw [h0, dist_eq_oppLen]
  fin_cases j
  · rfl
  · show D.target.oppLen 0 = D.target.oppLen 2
    rw [t_opp0, t_opp2]
  · show D.target.oppLen 1 = D.target.oppLen 2
    rw [t_opp1, t_opp2]

/-- **Non-vacuity.**  Every hypothesis of `bz_thm52` holds for the real 1215-tiling; the conclusion holds. -/
theorem bz_thm52_witness : Comm (1890 * 3) (1890 * 5) ∧ Comm (1890 * 3) (1890 * 7) :=
  bz_thm52 D α_irr data heq

/-- The conclusion of `bz_c_rational` on the real tiling (`c = (7/3) a`), with the hypothesis `a/b` commensurable (`3 a = ... `) exhibited. -/
theorem bz_c_rational_witness : ∃ r : ℚ, (1890 * 7 : ℝ) = (r : ℝ) * (1890 * 3) :=
  bz_c_rational D α_irr data ⟨5, 3, by norm_num, by norm_num, by norm_num⟩ heq

/-- NEGATIVE CONTROL: the hypothesis of `bz_phi_eq`/`bz_lemma35` that fails on the real tiling: `c` IS a rational multiple of `a` and `a` IS a nonnegative combination of `b, c`
(`5 * 3 = 3 * 5`), as it must be, since a tiling with `NotComb` would contradict `bz_lemma35_tri`. -/
theorem not_notComb_witness : ¬ NotComb (1890 * 3) (1890 * 5) (1890 * 7) := by
  intro h
  exact h 5 3 0 (by norm_num) (by norm_num)

theorem lemma35_witness : ¬ NotComb (1890 * 3) (1890 * 5) (1890 * 7) :=
  bz_lemma35_tri D α_irr data heq

/-- **The PolyTiling form** (Laczkovich's Theorem 2.1 language): the real 1215-tiling gives a regular `PolyTiling` of the equilateral triangle satisfying a conclusion of Theorem 2.1
(`regular_of_irr` and `caseIII_tri_irr` are exercised on a real tiling: regularity, `γ = 2π/3`, `α ∉ ℚπ`, all polygon angles `π/3`). -/
theorem thm21_witness : ∃ (N : ℕ) (T : PolyTiling N 3), RegularPQ T.C ∧ Thm21Concl T.C T.P :=
  ⟨_, bz_thm21_dissection D α_irr data heq⟩

end Erdos634.Draft.LaczFormal.BZWit

#print axioms Erdos634.Draft.LaczFormal.BZWit.bz_thm52_witness
#print axioms Erdos634.Draft.LaczFormal.BZWit.lemma35_witness
#print axioms Erdos634.Draft.LaczFormal.BZWit.thm21_witness
