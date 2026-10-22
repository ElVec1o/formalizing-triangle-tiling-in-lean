import Erdos634.Draft.LaczFormalTransportCor
import Erdos634.Draft.LaczFormalL25Wit

/-!
# Witnesses for the AAA transport corollaries

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94), Beeson, Beeson-Zhang, Zhang.

The hypotheses on `T'` are satisfiable: the explicit triangle produced by the theorem itself is such a `T'`; the corollary
then fires on it (an end-to-end check on the tiles `(2,3,4)`, `(5,3,7)`, `(12,7,16)`).  The corollaries apply to any
triangle with these angles.
-/

namespace Erdos634.LaczTransport

open Erdos634.Geometry Erdos634.Realizable Erdos634.LaczL22 Erdos634.LaczL24 Erdos634.LaczL25 Erdos634.LaczL26

/-- `thm24_first_any` on the tile `(2,3,4)`: a triangle `T'` with the hypotheses exists, and the conclusion holds for it. -/
theorem wit_thm24_first_any_234 :
    ∃ T' : Tri, dist (T'.pts 1) (T'.pts 0) = dist (T'.pts 1) (T'.pts 2) ∧
      cornerAngle (T'.pts 1) (T'.pts 0) (T'.pts 2)
        = cornerAngle (R234.Δ.pts 1) (R234.Δ.pts 0) (R234.Δ.pts 2) ∧
      ∃ (s : ℝ) (hs : 0 < s) (M : ℕ) (D' : CongruentDissection M),
        D'.target.carrier = T'.carrier ∧ D'.model.Congruent (scaleTri s hs.ne' R234.Δ) := by
  obtain ⟨T, q, hq, M, C, hC1, hC2, hiso, hang⟩ :=
    thm24_first R234 (1 / 2) (by norm_num) (by norm_num) (by simp [R234]; norm_num) (by simp [R234]; norm_num)
  exact ⟨T, hiso, hang, thm24_first_any R234 (1 / 2) (by norm_num) (by norm_num) (by simp [R234]; norm_num)
    (by simp [R234]; norm_num) T hiso hang⟩

theorem wit_thm25_first_any_537 :
    ∃ T' : Tri, cornerAngle (T'.pts 1) (T'.pts 0) (T'.pts 2)
        = cornerAngle (R537.Δ.pts 1) (R537.Δ.pts 0) (R537.Δ.pts 2) ∧
      cornerAngle (T'.pts 2) (T'.pts 1) (T'.pts 0) = Real.pi / 3 ∧
      ∃ (s : ℝ) (hs : 0 < s) (M : ℕ) (D' : CongruentDissection M),
        D'.target.carrier = T'.carrier ∧ D'.model.Congruent (scaleTri s hs.ne' R537.Δ) := by
  obtain ⟨T, q, hq, M, C, hC1, hC2, h0, h1⟩ := wit_thm25_first_537
  exact ⟨T, h0, h1, thm25_first_any R537 (by simp [R537]; norm_num) T h0 h1⟩

theorem wit_thm24_fourth_any_12716 :
    ∃ T' : Tri, dist (T'.pts 2) (T'.pts 0) = dist (T'.pts 2) (T'.pts 1) ∧
      cornerAngle (T'.pts 0) (T'.pts 2) (T'.pts 1)
        = cornerAngle (R12716.Δ.pts 1) (R12716.Δ.pts 0) (R12716.Δ.pts 2) ∧
      ∃ (s : ℝ) (hs : 0 < s) (M : ℕ) (D' : CongruentDissection M),
        D'.target.carrier = T'.carrier ∧ D'.model.Congruent (scaleTri s hs.ne' R12716.Δ) := by
  obtain ⟨T, q, hq, M, C, hC1, hC2, hiso, hang⟩ := wit_thm24_fourth_12716
  exact ⟨T, hiso, hang, thm24_fourth_any R12716 (3 / 4) (by norm_num) (by norm_num) (by simp [R12716]; norm_num)
    (by simp [R12716]; norm_num) (by norm_num) T hiso hang⟩

#print axioms transport_similar
#print axioms thm24_first_any
#print axioms thm25_first_any
#print axioms thm24_fourth_any
#print axioms wit_thm24_first_any_234
#print axioms wit_thm25_first_any_537
#print axioms wit_thm24_fourth_any_12716

end Erdos634.LaczTransport
