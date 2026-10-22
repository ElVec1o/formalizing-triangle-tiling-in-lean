-- Draft/LaczFormalL6Wit3.lean -- WITNESS for `LaczFormalL6Rat.equilateral_tile_iii`: the equilateral triangle cut by an
-- altitude into TWO congruent (30,60,90) triangles (N = 2 = 2*1^2), a real `CongruentDissection 2`.  (The earlier
-- thought that N = 2 is impossible for an equilateral target was wrong.)  Midpoint-split lemma `halve_split` is
-- modelled on `CentroidSplit.centroid_split`.  UNAUDITED.
import Erdos634.Draft.LaczFormalL6Wit2

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.CentroidSplit Erdos634.Draft.SumTwoSquares
  Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional Erdos634.Draft.LemmaCFinal
open Erdos634.Draft.FluxPaperWitness (cornerAngle_mem' dist_eq_of_sq)

namespace Erdos634.Draft.LaczFormal

/-- The midpoint of the side `pts 0 pts 1`. -/
noncomputable def Mid (T : Tri) : Plane := (1 / 2 : ℝ) • (T.pts 0 + T.pts 1)

theorem coord_Mid (T : Tri) (i : Fin 3) :
    T.basis.coord i (Mid T) = if i = 2 then 0 else 1 / 2 := by
  have := Erdos634.Subdivision.Tri.coord_eq_of_combo T (Mid T) ![1 / 2, 1 / 2, 0] (by simp; norm_num)
    (by unfold Mid; simp [smul_add]) i
  fin_cases i <;> simpa using this

theorem halve_split (T T0 T1 : Tri)
    (a0 : T0.pts 0 = T.pts 0) (a1 : T0.pts 1 = Mid T) (a2 : T0.pts 2 = T.pts 2)
    (b0 : T1.pts 0 = T.pts 1) (b1 : T1.pts 1 = Mid T) (b2 : T1.pts 2 = T.pts 2) :
    (T0.carrier ∪ T1.carrier = T.carrier) ∧
    Disjoint (interior T0.carrier) (interior T1.carrier) := by
  have hcoordT : ∀ i j, T.basis.coord i (T.pts j) = if i = j then 1 else 0 := coord_pts T
  have hMmem : Mid T ∈ T.carrier := by
    rw [T.carrier_eq_nonneg_coord]; intro k; show 0 ≤ T.basis.coord k (Mid T)
    rw [coord_Mid]; split_ifs <;> norm_num
  have hvert : ∀ k, T.pts k ∈ T.carrier := fun k => subset_convexHull ℝ _ ⟨k, rfl⟩
  have hconv := T.convex
  have sub : ∀ S : Tri, (∀ k, S.pts k ∈ T.carrier) → S.carrier ⊆ T.carrier := fun S h =>
    convexHull_min (by rintro _ ⟨k, rfl⟩; exact h k) hconv
  have s0 : T0.carrier ⊆ T.carrier := sub T0 (fun k => by
    fin_cases k
    · show T0.pts 0 ∈ _; rw [a0]; exact hvert 0
    · show T0.pts 1 ∈ _; rw [a1]; exact hMmem
    · show T0.pts 2 ∈ _; rw [a2]; exact hvert 2)
  have s1 : T1.carrier ⊆ T.carrier := sub T1 (fun k => by
    fin_cases k
    · show T1.pts 0 ∈ _; rw [b0]; exact hvert 1
    · show T1.pts 1 ∈ _; rw [b1]; exact hMmem
    · show T1.pts 2 ∈ _; rw [b2]; exact hvert 2)
  refine ⟨Set.Subset.antisymm (Set.union_subset s0 s1) ?_, ?_⟩
  · intro x hx
    rw [T.carrier_eq_nonneg_coord] at hx
    have hx' : ∀ i, 0 ≤ T.basis.coord i x := hx
    set u0 := T.basis.coord 0 x with hu0
    set u1 := T.basis.coord 1 x with hu1
    set u2 := T.basis.coord 2 x with hu2
    have hsum : u0 + u1 + u2 = 1 := by
      have := T.basis.sum_coord_apply_eq_one x; rwa [Fin.sum_univ_three] at this
    have hxeq : x = u0 • T.pts 0 + u1 • T.pts 1 + u2 • T.pts 2 := by
      have := T.basis.linear_combination_coord_eq_self x
      rw [Fin.sum_univ_three] at this; exact this.symm
    have h0 := hx' 0; have h1 := hx' 1; have h2 := hx' 2
    by_cases m : u1 ≤ u0
    · left
      refine Erdos634.CertGeom.mem_carrier_of_combo T0 x ![u0 - u1, 2 * u1, u2]
        (by simp; linarith) (by intro k; fin_cases k <;> simp <;> linarith) ?_
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons]
      rw [a0, a1, a2, hxeq]; unfold Mid; module
    · right
      push Not at m
      refine Erdos634.CertGeom.mem_carrier_of_combo T1 x ![u1 - u0, 2 * u0, u2]
        (by simp; linarith) (by intro k; fin_cases k <;> simp <;> linarith) ?_
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons]
      rw [b0, b1, b2, hxeq]; unfold Mid; module
  · refine sep_lemma T T0 T1 0 1 (by decide) ?_ ?_ <;> intro k <;> fin_cases k <;>
      simp [a0, a1, a2, b0, b1, b2, hcoordT, coord_Mid]

theorem dT6 : det3 0 0 6 0 3 (3 * Real.sqrt 3) ≠ 0 := dT'
theorem dP0 : det3 0 0 3 0 3 (3 * Real.sqrt 3) ≠ 0 := by
  have h0 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  unfold det3; nlinarith
theorem dP1 : det3 6 0 3 0 3 (3 * Real.sqrt 3) ≠ 0 := by
  have h0 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  unfold det3; nlinarith

noncomputable abbrev P0 : Tri := mkTri 0 0 3 0 3 (3 * Real.sqrt 3) dP0
noncomputable abbrev P1 : Tri := mkTri 6 0 3 0 3 (3 * Real.sqrt 3) dP1

theorem mid_eq : Mid TT3 = mkPt 3 0 := by
  unfold Mid
  ext i; fin_cases i <;> simp [mkPt_zero, mkPt_one] <;> norm_num

theorem P0_d01 : dist (P0.pts 0) (P0.pts 1) = 3 := by
  apply dist_eq_of_sq (by norm_num)
  show dist (mkPt 0 0) (mkPt 3 0) ^ 2 = 3 ^ 2
  rw [dist_sq_mkPt]; norm_num
theorem P0_d12 : dist (P0.pts 1) (P0.pts 2) = 3 * Real.sqrt 3 := by
  have h3 := s3sq
  apply dist_eq_of_sq (by positivity)
  show dist (mkPt 3 0) (mkPt 3 (3 * Real.sqrt 3)) ^ 2 = (3 * Real.sqrt 3) ^ 2
  rw [dist_sq_mkPt]; nlinarith [h3]
theorem P0_d20 : dist (P0.pts 2) (P0.pts 0) = 6 := by
  have h3 := s3sq
  apply dist_eq_of_sq (by norm_num)
  show dist (mkPt 3 (3 * Real.sqrt 3)) (mkPt 0 0) ^ 2 = 6 ^ 2
  rw [dist_sq_mkPt]; nlinarith [h3]
theorem P1_d01 : dist (P1.pts 0) (P1.pts 1) = 3 := by
  apply dist_eq_of_sq (by norm_num)
  show dist (mkPt 6 0) (mkPt 3 0) ^ 2 = 3 ^ 2
  rw [dist_sq_mkPt]; norm_num
theorem P1_d12 : dist (P1.pts 1) (P1.pts 2) = 3 * Real.sqrt 3 := by
  have h3 := s3sq
  apply dist_eq_of_sq (by positivity)
  show dist (mkPt 3 0) (mkPt 3 (3 * Real.sqrt 3)) ^ 2 = (3 * Real.sqrt 3) ^ 2
  rw [dist_sq_mkPt]; nlinarith [h3]
theorem P1_d20 : dist (P1.pts 2) (P1.pts 0) = 6 := by
  have h3 := s3sq
  apply dist_eq_of_sq (by norm_num)
  show dist (mkPt 3 (3 * Real.sqrt 3)) (mkPt 6 0) ^ 2 = 6 ^ 2
  rw [dist_sq_mkPt]; nlinarith [h3]

theorem exists_D2 : ∃ D : CongruentDissection 2,
    D.target = TT3 ∧ D.model = P0 := by
  have hs := halve_split TT3 P0 P1
    (by show mkPt (0 : ℝ) 0 = mkPt 0 0; rfl) (by rw [mid_eq]; rfl)
    (by show mkPt (3 : ℝ) (3 * Real.sqrt 3) = mkPt 3 (3 * Real.sqrt 3); rfl)
    (by show mkPt (6 : ℝ) 0 = mkPt 6 0; rfl) (by rw [mid_eq]; rfl)
    (by show mkPt (3 : ℝ) (3 * Real.sqrt 3) = mkPt 3 (3 * Real.sqrt 3); rfl)
  obtain ⟨hcov, hdis⟩ := hs
  have c1 : P1.Congruent P0 :=
    SssCongruent.congruent_of_dist_three (by rw [P1_d01, P0_d01]) (by rw [P1_d12, P0_d12])
      (by rw [P1_d20, P0_d20])
  refine ⟨⟨⟨TT3, ![P0, P1], ?_, ?_⟩, P0, ?_⟩, rfl, rfl⟩
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
    · exact Tri.Congruent.refl P0
    · exact c1

theorem P0_opp0 : P0.oppLen 0 = 3 * Real.sqrt 3 := by
  unfold Tri.oppLen
  simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl]
  exact P0_d12
theorem P0_opp1 : P0.oppLen 1 = 6 := by
  unfold Tri.oppLen
  simp only [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl]
  exact P0_d20
theorem P0_opp2 : P0.oppLen 2 = 3 := by
  unfold Tri.oppLen
  simp only [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl]
  exact P0_d01

theorem P0_angles : P0.angleAt 0 = Real.pi / 3 ∧ P0.angleAt 1 = Real.pi / 2 ∧
    P0.angleAt 2 = Real.pi / 6 := by
  have h3 := s3sq
  have hp : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hpi := Real.pi_pos
  have e0 := P0_opp0
  have e1 := P0_opp1
  have e2 := P0_opp2
  refine ⟨?_, ?_, ?_⟩
  · apply angleAt_of_cos P0 0 _ (by positivity) (by linarith)
    rw [Erdos634.Draft.G3CAng.cos_angleAt_opp P0 0 (by rw [show (0 : Fin 3) + 1 = 1 from rfl, e1]; norm_num)
      (by rw [show (0 : Fin 3) + 2 = 2 from rfl, e2]; norm_num)]
    simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl, e0, e1, e2]
    rw [Real.cos_pi_div_three]
    field_simp; nlinarith [h3]
  · apply angleAt_of_cos P0 1 _ (by positivity) (by linarith)
    rw [Erdos634.Draft.G3CAng.cos_angleAt_opp P0 1 (by rw [show (1 : Fin 3) + 1 = 2 from rfl, e2]; norm_num)
      (by rw [show (1 : Fin 3) + 2 = 0 from rfl, e0]; positivity)]
    simp only [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl, e0, e1, e2]
    rw [Real.cos_pi_div_two]
    have : (3 : ℝ) ^ 2 + (3 * Real.sqrt 3) ^ 2 - 6 ^ 2 = 0 := by nlinarith [h3]
    rw [this]; simp
  · apply angleAt_of_cos P0 2 _ (by positivity) (by linarith)
    rw [Erdos634.Draft.G3CAng.cos_angleAt_opp P0 2 (by rw [show (2 : Fin 3) + 1 = 0 from rfl, e0]; positivity)
      (by rw [show (2 : Fin 3) + 2 = 1 from rfl, e1]; norm_num)]
    simp only [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl, e0, e1, e2]
    rw [Real.cos_pi_div_six]
    field_simp; nlinarith [h3]

/-- **Witness (iii)**: the altitude split of an equilateral triangle, `N = 2`, tile `(π/6, π/3, π/2)`. -/
theorem equilateral_tile_iii_witness :
    ∃ (N : ℕ) (D : CongruentDissection N), Equilateral D ∧
      TileAngles D (Real.pi / 6) (Real.pi / 3) (Real.pi / 2) := by
  obtain ⟨D, ht, hm⟩ := exists_D2
  refine ⟨2, D, fun k => ?_, ?_⟩
  · rw [ht]; exact angles_third_of_sides TT3 6 (by norm_num) TT3_opp k
  · refine ⟨permOf 2 0 1 (by decide) (by decide) (by decide), ?_, ?_, ?_⟩
    · rw [permOf_0, hm]; exact P0_angles.2.2
    · rw [permOf_1, hm]; exact P0_angles.1
    · rw [permOf_2, hm]; exact P0_angles.2.1

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.equilateral_tile_iii_witness
