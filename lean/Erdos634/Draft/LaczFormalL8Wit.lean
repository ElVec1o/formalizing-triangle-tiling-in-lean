-- Draft/LaczFormalL8Wit.lean -- WITNESS for the hypotheses of `LaczFormalL8Gen.similar_reduction`: a real
-- `CongruentDissection 2` whose target (right isosceles triangle (0,0),(2,0),(1,1)) is similar to its tile with ratio
-- sqrt 2 and N = 2 is NOT a square (cut along the altitude to the hypotenuse; reuses `halve_split`).  UNAUDITED.
import Erdos634.Draft.LaczFormalL8Gen
import Erdos634.Draft.LaczFormalL6Wit3

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.CentroidSplit Erdos634.Draft.SumTwoSquares
  Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.FluxPaperWitness (cornerAngle_mem' dist_eq_of_sq)

namespace Erdos634.Draft.LaczFormal

theorem s2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem dTT2 : det3 0 0 2 0 1 1 ≠ 0 := by unfold det3; norm_num
theorem dQ0 : det3 0 0 1 0 1 1 ≠ 0 := by unfold det3; norm_num
theorem dQ1 : det3 2 0 1 0 1 1 ≠ 0 := by unfold det3; norm_num

noncomputable abbrev TT2 : Tri := mkTri 0 0 2 0 1 1 dTT2
noncomputable abbrev Q0 : Tri := mkTri 0 0 1 0 1 1 dQ0
noncomputable abbrev Q1 : Tri := mkTri 2 0 1 0 1 1 dQ1

theorem mid2_eq : Mid TT2 = mkPt 1 0 := by
  unfold Mid
  ext i; fin_cases i <;> simp [mkPt_zero, mkPt_one] <;> norm_num

theorem Q0_d01 : dist (Q0.pts 0) (Q0.pts 1) = 1 := by
  apply dist_eq_of_sq (by norm_num)
  show dist (mkPt 0 0) (mkPt 1 0) ^ 2 = 1 ^ 2
  rw [dist_sq_mkPt]; norm_num
theorem Q0_d12 : dist (Q0.pts 1) (Q0.pts 2) = 1 := by
  apply dist_eq_of_sq (by norm_num)
  show dist (mkPt 1 0) (mkPt 1 1) ^ 2 = 1 ^ 2
  rw [dist_sq_mkPt]; norm_num
theorem Q0_d20 : dist (Q0.pts 2) (Q0.pts 0) = Real.sqrt 2 := by
  apply dist_eq_of_sq (by positivity)
  show dist (mkPt 1 1) (mkPt 0 0) ^ 2 = Real.sqrt 2 ^ 2
  rw [dist_sq_mkPt, s2sq]; norm_num
theorem Q1_d01 : dist (Q1.pts 0) (Q1.pts 1) = 1 := by
  apply dist_eq_of_sq (by norm_num)
  show dist (mkPt 2 0) (mkPt 1 0) ^ 2 = 1 ^ 2
  rw [dist_sq_mkPt]; norm_num
theorem Q1_d12 : dist (Q1.pts 1) (Q1.pts 2) = 1 := by
  apply dist_eq_of_sq (by norm_num)
  show dist (mkPt 1 0) (mkPt 1 1) ^ 2 = 1 ^ 2
  rw [dist_sq_mkPt]; norm_num
theorem Q1_d20 : dist (Q1.pts 2) (Q1.pts 0) = Real.sqrt 2 := by
  apply dist_eq_of_sq (by positivity)
  show dist (mkPt 1 1) (mkPt 2 0) ^ 2 = Real.sqrt 2 ^ 2
  rw [dist_sq_mkPt, s2sq]; norm_num

theorem exists_D2b : ∃ D : CongruentDissection 2, D.target = TT2 ∧ D.model = Q0 := by
  have hs := halve_split TT2 Q0 Q1
    (by show mkPt (0 : ℝ) 0 = mkPt 0 0; rfl) (by rw [mid2_eq]; rfl)
    (by show mkPt (1 : ℝ) 1 = mkPt 1 1; rfl)
    (by show mkPt (2 : ℝ) 0 = mkPt 2 0; rfl) (by rw [mid2_eq]; rfl)
    (by show mkPt (1 : ℝ) 1 = mkPt 1 1; rfl)
  obtain ⟨hcov, hdis⟩ := hs
  have c1 : Q1.Congruent Q0 :=
    SssCongruent.congruent_of_dist_three (by rw [Q1_d01, Q0_d01]) (by rw [Q1_d12, Q0_d12])
      (by rw [Q1_d20, Q0_d20])
  refine ⟨⟨⟨TT2, ![Q0, Q1], ?_, ?_⟩, Q0, ?_⟩, rfl, rfl⟩
  · rw [← hcov]
    ext x
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
    · rintro (h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | exact hdis | exact hdis.symm
  · intro i; fin_cases i
    · exact Tri.Congruent.refl Q0
    · exact c1

theorem TT2_opp0 : TT2.oppLen 0 = Real.sqrt 2 := by
  unfold Tri.oppLen
  simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl]
  apply dist_eq_of_sq (by positivity)
  show dist (mkPt 2 0) (mkPt 1 1) ^ 2 = Real.sqrt 2 ^ 2
  rw [dist_sq_mkPt, s2sq]; norm_num
theorem TT2_opp1 : TT2.oppLen 1 = Real.sqrt 2 := by
  unfold Tri.oppLen
  simp only [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl]
  apply dist_eq_of_sq (by positivity)
  show dist (mkPt 1 1) (mkPt 0 0) ^ 2 = Real.sqrt 2 ^ 2
  rw [dist_sq_mkPt, s2sq]; norm_num
theorem TT2_opp2 : TT2.oppLen 2 = 2 := by
  unfold Tri.oppLen
  simp only [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl]
  apply dist_eq_of_sq (by norm_num)
  show dist (mkPt 0 0) (mkPt 2 0) ^ 2 = 2 ^ 2
  rw [dist_sq_mkPt]; norm_num
theorem Q0_opp0 : Q0.oppLen 0 = 1 := by
  unfold Tri.oppLen
  simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl]
  exact Q0_d12
theorem Q0_opp1 : Q0.oppLen 1 = Real.sqrt 2 := by
  unfold Tri.oppLen
  simp only [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl]
  exact Q0_d20
theorem Q0_opp2 : Q0.oppLen 2 = 1 := by
  unfold Tri.oppLen
  simp only [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl]
  exact Q0_d01

theorem D2b_similar (D : CongruentDissection 2) (ht : D.target = TT2) (hm : D.model = Q0) : SimilarTM D := by
  · have h2 := s2sq
    have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    refine ⟨Real.sqrt 2, Equiv.swap 1 2, fun k => ?_⟩
    rw [ht, hm]
    have t0 : (Equiv.swap (1 : Fin 3) 2) 0 = 0 := by decide
    have t1 : (Equiv.swap (1 : Fin 3) 2) 1 = 2 := by decide
    have t2 : (Equiv.swap (1 : Fin 3) 2) 2 = 1 := by decide
    have pos := Tri.oppLen_pos
    fin_cases k
    · refine ⟨?_, ?_⟩
      · show TT2.angleAt 0 = Q0.angleAt (Equiv.swap 1 2 0)
        rw [t0]
        refine Erdos634.Draft.G3CAng.angle_eq_of_cos 0 0 ?_
        rw [Erdos634.Draft.G3CAng.cos_angleAt_opp TT2 0 (pos _ _) (pos _ _),
          Erdos634.Draft.G3CAng.cos_angleAt_opp Q0 0 (pos _ _) (pos _ _)]
        simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl, TT2_opp0,
          TT2_opp1, TT2_opp2, Q0_opp0, Q0_opp1, Q0_opp2]
        field_simp; nlinarith [h2]
      · show TT2.oppLen 0 = _ * Q0.oppLen (Equiv.swap 1 2 0)
        rw [t0, TT2_opp0, Q0_opp0]; ring
    · refine ⟨?_, ?_⟩
      · show TT2.angleAt 1 = Q0.angleAt (Equiv.swap 1 2 1)
        rw [t1]
        refine Erdos634.Draft.G3CAng.angle_eq_of_cos 1 2 ?_
        rw [Erdos634.Draft.G3CAng.cos_angleAt_opp TT2 1 (pos _ _) (pos _ _),
          Erdos634.Draft.G3CAng.cos_angleAt_opp Q0 2 (pos _ _) (pos _ _)]
        simp only [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl,
          show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl, TT2_opp0,
          TT2_opp1, TT2_opp2, Q0_opp0, Q0_opp1, Q0_opp2]
        field_simp; nlinarith [h2]
      · show TT2.oppLen 1 = _ * Q0.oppLen (Equiv.swap 1 2 1)
        rw [t1, TT2_opp1, Q0_opp2]; ring
    · refine ⟨?_, ?_⟩
      · show TT2.angleAt 2 = Q0.angleAt (Equiv.swap 1 2 2)
        rw [t2]
        refine Erdos634.Draft.G3CAng.angle_eq_of_cos 2 1 ?_
        rw [Erdos634.Draft.G3CAng.cos_angleAt_opp TT2 2 (pos _ _) (pos _ _),
          Erdos634.Draft.G3CAng.cos_angleAt_opp Q0 1 (pos _ _) (pos _ _)]
        simp only [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl,
          show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl, TT2_opp0,
          TT2_opp1, TT2_opp2, Q0_opp0, Q0_opp1, Q0_opp2]
        field_simp; nlinarith [h2]
      · show TT2.oppLen 2 = _ * Q0.oppLen (Equiv.swap 1 2 2)
        rw [t2, TT2_opp2, Q0_opp1]; nlinarith [h2]
theorem similar_witness_TT2 : ∃ (N : ℕ) (D : CongruentDissection N), SimilarTM D ∧ ¬ IsSquare N := by
  obtain ⟨D, ht, hm⟩ := exists_D2b
  refine ⟨2, D, D2b_similar D ht hm, ?_⟩
  · rintro ⟨m, hm⟩
    have : m ≤ 1 := by nlinarith
    interval_cases m <;> omega

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.similar_witness_TT2
