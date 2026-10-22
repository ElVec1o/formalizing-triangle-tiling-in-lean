import Erdos634.Draft.ZhangThm1Full
import Erdos634.Draft.ZhangThm1FullWit

/-!
# Zhang Theorem 1, in the printed vocabulary (M3)

Printed ([5, Thm 1.2] = arXiv 2604.01314 Thm 1.2, quoted as Zhang arXiv 2512.22696v4, Thm 1): triangle `T` tiled by `R`; `R` not similar to `T`;
`R` not a right triangle; `R` does not have commensurable angles.  Then `R` has commensurable sides.
Vocabulary (BZ intro, Zhang Sec 1): *commensurable angles* = all angles of the tile are rational multiples of `pi`; *commensurable sides* = all pairwise
ratios of sides rational.  Here: `¬ (∀ k, ∃ r : ℚ, angle k = r * pi)` and `∀ i j, Comm (side i) (side j)`: a literal transcription, no weaker/stronger reading.
NOTE, UNAUDITED.  Credit Zhang, Beeson-Zhang, Beeson, Laczkovich.
-/

open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional

namespace Erdos634.Draft.ZhangRat9Printed
open Erdos634.Draft.LaczFormal.RG Erdos634.Geometry.Row14AnyLabel

variable {N : ℕ}

/-- "Not commensurable angles" is `∃ k, IrrPi (angle k)` (definitional). -/
theorem not_commAngles_iff (D : CongruentDissection N) :
    (¬ ∀ k, ∃ r : ℚ, D.model.angleAt k = (r : ℝ) * Real.pi) ↔ ∃ k, IrrPi (D.model.angleAt k) := by
  constructor
  · intro h
    by_contra h'
    exact h fun k => by
      by_contra hk
      exact h' ⟨k, hk⟩
  · rintro ⟨k, hk⟩ h
    exact hk (h k)

/-- **Zhang Theorem 1, printed form.** -/
theorem zhang_thm1_printed (D : CongruentDissection N)
    (hnc : ¬ ∀ k, ∃ r : ℚ, D.model.angleAt k = (r : ℝ) * Real.pi)
    (hns : ¬ SimilarTM D) (hnr : ∀ k, D.model.angleAt k ≠ Real.pi / 2) :
    ∀ i j, Comm (D.model.oppLen i) (D.model.oppLen j) := by
  obtain ⟨h1, h2⟩ := Erdos634.Draft.ZhangThm1Full.zhang_thm1 D ((not_commAngles_iff D).1 hnc) hns hnr
  have key : ∀ x y : Fin 3, Comm (D.model.oppLen x) (D.model.oppLen y) := by
    have s1 := comm_symm' h1
    have s2 := comm_symm' h2
    have s12 := comm_trans' s1 h2
    have s21 := comm_symm' s12
    intro x y
    fin_cases x <;> fin_cases y <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    all_goals first | assumption | exact comm_refl' _
  exact key

/-- Non-vacuity: the certified N=1215 dissection satisfies the printed hypotheses and the printed conclusion. -/
theorem zhang_thm1_printed_wit : ∃ (N : ℕ) (D : CongruentDissection N),
    (¬ ∀ k, ∃ r : ℚ, D.model.angleAt k = (r : ℝ) * Real.pi) ∧ ¬ SimilarTM D ∧
    (∀ k, D.model.angleAt k ≠ Real.pi / 2) ∧ ∀ i j, Comm (D.model.oppLen i) (D.model.oppLen j) := by
  obtain ⟨N, D, hirr, hns, hnr, -⟩ := Erdos634.Draft.ZhangThm1Full.zhang_thm1_wit
  have hnc := (not_commAngles_iff D).2 hirr
  exact ⟨N, D, hnc, hns, hnr, zhang_thm1_printed D hnc hns hnr⟩

end Erdos634.Draft.ZhangRat9Printed
#print axioms Erdos634.Draft.ZhangRat9Printed.zhang_thm1_printed
#print axioms Erdos634.Draft.ZhangRat9Printed.zhang_thm1_printed_wit
