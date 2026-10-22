-- Draft/LaczFormalL6Wit2.lean -- WITNESS for `LaczFormalL6Rat.equilateral_tile_ii`: the equilateral triangle cut into
-- three (30,30,120) triangles from its centre (N = 3), with TARGET and TILE angles computed.  The construction
-- is a verbatim copy of `Equilateral3.exists_dissection_3_model` (Draft/Equilateral3.lean) whose statement only
-- exposed the model; here the target is exposed as well.  UNAUDITED.
import Erdos634.Draft.LaczFormalL6Wit1
import Erdos634.Draft.Equilateral3

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.CentroidSplit Erdos634.Draft.SumTwoSquares
  Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.FluxPaperWitness (cornerAngle_mem' dist_eq_of_sq)

namespace Erdos634.Draft.LaczFormal

theorem dT' : det3 0 0 6 0 3 (3 * Real.sqrt 3) ≠ 0 := by
  have h0 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  unfold det3; nlinarith
theorem d0' : det3 0 0 6 0 3 (Real.sqrt 3) ≠ 0 := by
  have h0 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  unfold det3; nlinarith

theorem exists_D3 : ∃ D : CongruentDissection 3,
    D.target = mkTri 0 0 6 0 3 (3 * Real.sqrt 3) dT' ∧ D.model = mkTri 0 0 6 0 3 (Real.sqrt 3) d0' := by
  set r : ℝ := Real.sqrt 3 with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by norm_num)
  have hr2 : r ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have dT : det3 0 0 6 0 3 (3 * r) ≠ 0 := by unfold det3; nlinarith
  have d0 : det3 0 0 6 0 3 r ≠ 0 := by unfold det3; nlinarith
  have d1 : det3 6 0 3 (3 * r) 3 r ≠ 0 := by unfold det3; nlinarith
  have d2 : det3 3 (3 * r) 0 0 3 r ≠ 0 := by unfold det3; nlinarith
  set T : Tri := mkTri 0 0 6 0 3 (3 * r) dT
  set T0 : Tri := mkTri 0 0 6 0 3 r d0
  set T1 : Tri := mkTri 6 0 3 (3 * r) 3 r d1
  set T2 : Tri := mkTri 3 (3 * r) 0 0 3 r d2
  have hG : G T = mkPt 3 r := by
    unfold G
    ext i; fin_cases i <;> simp [T, mkTri, mkPt_zero, mkPt_one] <;> ring
  obtain ⟨hcov, h01, h12, h02⟩ := centroid_split T T0 T1 T2
    (by show mkPt (0 : ℝ) 0 = mkPt 0 0; rfl) (by show mkPt (6 : ℝ) 0 = mkPt 6 0; rfl)
    (by rw [hG]; rfl)
    (by show mkPt (6 : ℝ) 0 = mkPt 6 0; rfl) (by show mkPt (3 : ℝ) (3 * r) = mkPt 3 (3 * r); rfl)
    (by rw [hG]; rfl)
    (by show mkPt (3 : ℝ) (3 * r) = mkPt 3 (3 * r); rfl) (by show mkPt (0 : ℝ) 0 = mkPt 0 0; rfl)
    (by rw [hG]; rfl)
  have s36 : dist (mkPt (0 : ℝ) 0) (mkPt 6 0) = 6 := dsq _ _ _ _ _ (by norm_num) (by norm_num)
  have c1 : T1.Congruent T0 := by
    refine SssCongruent.congruent_of_dist_three ?_ ?_ ?_
    · show dist (mkPt (6 : ℝ) 0) (mkPt 3 (3 * r)) = dist (mkPt (0 : ℝ) 0) (mkPt 6 0)
      rw [s36]; exact dsq _ _ _ _ _ (by norm_num) (by nlinarith)
    · show dist (mkPt (3 : ℝ) (3 * r)) (mkPt 3 r) = dist (mkPt (6 : ℝ) 0) (mkPt 3 r)
      exact eqsq dist_nonneg dist_nonneg (by rw [dist_sq_mkPt, dist_sq_mkPt]; nlinarith)
    · show dist (mkPt (3 : ℝ) r) (mkPt 6 0) = dist (mkPt (3 : ℝ) r) (mkPt 0 0)
      exact eqsq dist_nonneg dist_nonneg (by rw [dist_sq_mkPt, dist_sq_mkPt]; nlinarith)
  have c2 : T2.Congruent T0 := by
    refine SssCongruent.congruent_of_dist_three ?_ ?_ ?_
    · show dist (mkPt (3 : ℝ) (3 * r)) (mkPt 0 0) = dist (mkPt (0 : ℝ) 0) (mkPt 6 0)
      rw [s36]; exact dsq _ _ _ _ _ (by norm_num) (by nlinarith)
    · show dist (mkPt (0 : ℝ) 0) (mkPt 3 r) = dist (mkPt (6 : ℝ) 0) (mkPt 3 r)
      exact eqsq dist_nonneg dist_nonneg (by rw [dist_sq_mkPt, dist_sq_mkPt]; nlinarith)
    · show dist (mkPt (3 : ℝ) r) (mkPt 3 (3 * r)) = dist (mkPt (3 : ℝ) r) (mkPt 0 0)
      exact eqsq dist_nonneg dist_nonneg (by rw [dist_sq_mkPt, dist_sq_mkPt]; nlinarith)
  refine ⟨⟨⟨T, ![T0, T1, T2], ?_, ?_⟩, T0, ?_⟩, rfl, rfl⟩
  · rw [← hcov]
    ext x
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl (Or.inl hi)
      · exact Or.inl (Or.inr hi)
      · exact Or.inr hi
    · rintro ((h | h) | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | exact h01 | exact h01.symm | exact h12 | exact h12.symm | exact h02 | exact h02.symm
  · intro i; fin_cases i
    · exact Tri.Congruent.refl T0
    · exact c1
    · exact c2

theorem angleAt_of_cos (T : Tri) (k : Fin 3) (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ Real.pi)
    (h : Real.cos (T.angleAt k) = Real.cos x) : T.angleAt k = x :=
  Real.injOn_cos (cornerAngle_mem' _ _ _) ⟨h0, h1⟩ h

noncomputable abbrev TT3 : Tri := mkTri 0 0 6 0 3 (3 * Real.sqrt 3) dT'
noncomputable abbrev TM3 : Tri := mkTri 0 0 6 0 3 (Real.sqrt 3) d0'

theorem TT3_opp (k : Fin 3) : TT3.oppLen k = 6 := by
  have h3 := s3sq
  unfold Tri.oppLen
  fin_cases k
  · simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl]
    apply dist_eq_of_sq (by norm_num)
    show dist (mkPt 6 0) (mkPt 3 (3 * Real.sqrt 3)) ^ 2 = 6 ^ 2
    rw [dist_sq_mkPt]; nlinarith [h3]
  · simp only [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl]
    apply dist_eq_of_sq (by norm_num)
    show dist (mkPt 3 (3 * Real.sqrt 3)) (mkPt 0 0) ^ 2 = 6 ^ 2
    rw [dist_sq_mkPt]; nlinarith [h3]
  · simp only [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl]
    apply dist_eq_of_sq (by norm_num)
    show dist (mkPt 0 0) (mkPt 6 0) ^ 2 = 6 ^ 2
    rw [dist_sq_mkPt]; norm_num

theorem TM3_opp0 : TM3.oppLen 0 = 2 * Real.sqrt 3 := by
  have h3 := s3sq
  unfold Tri.oppLen
  simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl]
  apply dist_eq_of_sq (by positivity)
  show dist (mkPt 6 0) (mkPt 3 (Real.sqrt 3)) ^ 2 = (2 * Real.sqrt 3) ^ 2
  rw [dist_sq_mkPt]; nlinarith [h3]

theorem TM3_opp1 : TM3.oppLen 1 = 2 * Real.sqrt 3 := by
  have h3 := s3sq
  unfold Tri.oppLen
  simp only [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl]
  apply dist_eq_of_sq (by positivity)
  show dist (mkPt 3 (Real.sqrt 3)) (mkPt 0 0) ^ 2 = (2 * Real.sqrt 3) ^ 2
  rw [dist_sq_mkPt]; nlinarith [h3]

theorem TM3_opp2 : TM3.oppLen 2 = 6 := by
  unfold Tri.oppLen
  simp only [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl]
  apply dist_eq_of_sq (by norm_num)
  show dist (mkPt 0 0) (mkPt 6 0) ^ 2 = 6 ^ 2
  rw [dist_sq_mkPt]; norm_num

theorem TM3_angles : TM3.angleAt 0 = Real.pi / 6 ∧ TM3.angleAt 1 = Real.pi / 6 ∧
    TM3.angleAt 2 = 2 * Real.pi / 3 := by
  have h3 := s3sq
  have hp : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hpi := Real.pi_pos
  have e0 := TM3_opp0
  have e1 := TM3_opp1
  have e2 := TM3_opp2
  refine ⟨?_, ?_, ?_⟩
  · apply angleAt_of_cos TM3 0 _ (by positivity) (by linarith)
    rw [Erdos634.Draft.G3CAng.cos_angleAt_opp TM3 0 (by rw [show (0 : Fin 3) + 1 = 1 from rfl, e1]; positivity)
      (by rw [show (0 : Fin 3) + 2 = 2 from rfl, e2]; norm_num)]
    simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl, e0, e1, e2]
    rw [Real.cos_pi_div_six]
    field_simp; nlinarith [h3]
  · apply angleAt_of_cos TM3 1 _ (by positivity) (by linarith)
    rw [Erdos634.Draft.G3CAng.cos_angleAt_opp TM3 1 (by rw [show (1 : Fin 3) + 1 = 2 from rfl, e2]; norm_num)
      (by rw [show (1 : Fin 3) + 2 = 0 from rfl, e0]; positivity)]
    simp only [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl, e0, e1, e2]
    rw [Real.cos_pi_div_six]
    field_simp; nlinarith [h3]
  · apply angleAt_of_cos TM3 2 _ (by positivity) (by linarith)
    rw [Erdos634.Draft.G3CAng.cos_angleAt_opp TM3 2 (by rw [show (2 : Fin 3) + 1 = 0 from rfl, e0]; positivity)
      (by rw [show (2 : Fin 3) + 2 = 1 from rfl, e1]; positivity)]
    simp only [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl, e0, e1, e2]
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
    field_simp; nlinarith [h3]

/-- **Witness (ii)**: the centroid split of an equilateral triangle, `N = 3`, tile `(π/6,π/6,2π/3)`. -/
theorem equilateral_tile_ii_witness :
    ∃ (N : ℕ) (D : CongruentDissection N), Equilateral D ∧
      TileAngles D (Real.pi / 6) (Real.pi / 6) (2 * Real.pi / 3) := by
  obtain ⟨D, ht, hm⟩ := exists_D3
  refine ⟨3, D, fun k => ?_, ⟨1, ?_⟩⟩
  · rw [ht]; exact angles_third_of_sides TT3 6 (by norm_num) TT3_opp k
  · rw [hm]; exact ⟨TM3_angles.1, TM3_angles.2.1, TM3_angles.2.2⟩


end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.equilateral_tile_ii_witness
