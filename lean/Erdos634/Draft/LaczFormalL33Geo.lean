import Erdos634.Draft.LaczFormalL30Geo

/-!
# Laczkovich Theorem 2.5, triple `(α+β, α+β, α+β)` (Fig. 7, fifth picture): the plane geometry

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.5, Fig. 7), Beeson, Beeson-Zhang, Zhang.

PRINT GAP: "Similar constructions apply for the other triples listed in (2); see Fig. 7."  Decoded from the fifth picture (an
equilateral triangle, apex split `α | β`, left angle split `β | α`, three `γ` around the inner point `O`, a horizontal segment
`N Q` parallel to the base): the equilateral triangle `E = (A, V, R)` is the union of three tiles `A V O` (scale `1`),
`A O Q` (scale `k = b/a`), `O N Q` (scale `k²`), and the trapezoid `N V R Q` (angles `α` at `V`, `α+β = π/3` at `R`,
`γ` at `Q`, `β + γ` at `N`; Lemma 2.2 (ii) with `α` and `β` exchanged).  Each piece size is determined by the picture
(`s_b = (b/a) s_a`, `s_c = (b/a) s_b`).  In the chart of `LaczFormalL30Geo` (`O` origin, `w = V - O`, `d = Q'`, `|w| = |d| = a`,
`⟨w,d⟩ = -a²/2`, `k = b/a`):
`A = (-k,-k)`, `V = (1,0)`, `R = (1-k,1)`, `O = (0,0)`, `Q = (0,k²)`, `N = (k³,0)`; the side of `E` is `c`.
RANGE: `0 < k < 1`, i.e. `b < a` (for `a < b` exchange `α` and `β`; `a = b` is impossible for a rational tile).
This file: the real geometry for `0 < k < 1`.
-/

namespace Erdos634.LaczL33

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL24 MeasureTheory
open Erdos634.LaczL27 (carrier_eq_of_range range_mk3)
open Erdos634.LaczL30 (sepAB)

private theorem htri : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide

section geo

variable {k : ℝ}

theorem det_E : det3 (-k) (-k) 1 0 (1 - k) 1 = k ^ 2 + k + 1 := by unfold det3; ring
theorem det_Pa : det3 (-k) (-k) 1 0 0 0 = k := by unfold det3; ring
theorem det_Pb : det3 (-k) (-k) 0 0 0 (k ^ 2) = k ^ 3 := by unfold det3; ring
theorem det_Pc : det3 0 0 (k ^ 3) 0 0 (k ^ 2) = k ^ 5 := by unfold det3; ring
theorem det_U1 : det3 (k ^ 3) 0 1 0 (1 - k) 1 = 1 - k ^ 3 := by unfold det3; ring
theorem det_U2 : det3 (k ^ 3) 0 (1 - k) 1 0 (k ^ 2) = k ^ 2 * (1 - k ^ 3) := by unfold det3; ring

theorem k3_lt (hk0 : 0 < k) (hk1 : k < 1) : k ^ 3 < 1 := pow_lt_one₀ hk0.le hk1 (by norm_num)
theorem k5_le_k2 (hk0 : 0 < k) (hk1 : k < 1) : k ^ 5 ≤ k ^ 2 := pow_le_pow_of_le_one hk0.le hk1.le (by norm_num)
theorem k3_le_k2 (hk0 : 0 < k) (hk1 : k < 1) : k ^ 3 ≤ k ^ 2 := pow_le_pow_of_le_one hk0.le hk1.le (by norm_num)

theorem detpos_E (hk0 : 0 < k) (hk1 : k < 1) : 0 < det3 (-k) (-k) 1 0 (1 - k) 1 := by
  rw [det_E]; positivity

/-- the equilateral triangle `A V R`. -/
noncomputable def tE (hk0 : 0 < k) (hk1 : k < 1) : Tri := mkTri (-k) (-k) 1 0 (1 - k) 1 (detpos_E hk0 hk1).ne'
/-- tile `A V O` (scale `1`). -/
noncomputable def tPa (hk0 : 0 < k) (hk1 : k < 1) : Tri := mkTri (-k) (-k) 1 0 0 0 (by rw [det_Pa]; exact hk0.ne')
/-- tile `Q A O`-vertices `(A, O, Q)` (scale `k`). -/
noncomputable def tPb (hk0 : 0 < k) (hk1 : k < 1) : Tri :=
  mkTri (-k) (-k) 0 0 0 (k ^ 2) (by rw [det_Pb]; positivity)
/-- tile with vertices `(O, N, Q)` (scale `k²`). -/
noncomputable def tPc (hk0 : 0 < k) (hk1 : k < 1) : Tri :=
  mkTri 0 0 (k ^ 3) 0 0 (k ^ 2) (by rw [det_Pc]; positivity)
/-- half `N V R` of the trapezoid. -/
noncomputable def tU1 (hk0 : 0 < k) (hk1 : k < 1) : Tri :=
  mkTri (k ^ 3) 0 1 0 (1 - k) 1 (by rw [det_U1]; have := k3_lt hk0 hk1; linarith)
/-- half `N R Q` of the trapezoid. -/
noncomputable def tU2 (hk0 : 0 < k) (hk1 : k < 1) : Tri :=
  mkTri (k ^ 3) 0 (1 - k) 1 0 (k ^ 2) (by
    rw [det_U2]; have := k3_lt hk0 hk1; have : 0 < 1 - k ^ 3 := by linarith
    positivity)

theorem memO (hk0 : 0 < k) (hk1 : k < 1) : mkPt 0 0 ∈ (tE hk0 hk1).carrier :=
  mem_carrier_of_dets (detpos_E hk0 hk1)
    (by have e : det3 0 0 1 0 (1 - k) 1 = 1 := by unfold det3; ring
        rw [e]; norm_num)
    (by have e : det3 (-k) (-k) 0 0 (1 - k) 1 = k ^ 2 := by unfold det3; ring
        rw [e]; positivity)
    (by have e : det3 (-k) (-k) 1 0 0 0 = k := by unfold det3; ring
        rw [e]; exact hk0.le)

theorem memQ (hk0 : 0 < k) (hk1 : k < 1) : mkPt 0 (k ^ 2) ∈ (tE hk0 hk1).carrier :=
  mem_carrier_of_dets (detpos_E hk0 hk1)
    (by have e : det3 0 (k ^ 2) 1 0 (1 - k) 1 = (1 - k) * (k ^ 2 + k + 1) := by unfold det3; ring
        rw [e]; have : 0 < 1 - k := by linarith
        positivity)
    (by have e : det3 (-k) (-k) 0 (k ^ 2) (1 - k) 1 = 0 := by unfold det3; ring
        rw [e])
    (by have e : det3 (-k) (-k) 1 0 0 (k ^ 2) = k * (k ^ 2 + k + 1) := by unfold det3; ring
        rw [e]; positivity)

theorem memN (hk0 : 0 < k) (hk1 : k < 1) : mkPt (k ^ 3) 0 ∈ (tE hk0 hk1).carrier :=
  mem_carrier_of_dets (detpos_E hk0 hk1)
    (by have e : det3 (k ^ 3) 0 1 0 (1 - k) 1 = (1 - k) * (k ^ 2 + k + 1) := by unfold det3; ring
        rw [e]; have : 0 < 1 - k := by linarith
        positivity)
    (by have e : det3 (-k) (-k) (k ^ 3) 0 (1 - k) 1 = k ^ 2 * (k ^ 2 + k + 1) := by unfold det3; ring
        rw [e]; positivity)
    (by have e : det3 (-k) (-k) 1 0 (k ^ 3) 0 = k * (1 - k) * (k ^ 2 + k + 1) := by unfold det3; ring
        rw [e]; have : 0 < 1 - k := by linarith
        positivity)

theorem memA (hk0 : 0 < k) (hk1 : k < 1) : mkPt (-k) (-k) ∈ (tE hk0 hk1).carrier := by
  show (tE hk0 hk1).pts 0 ∈ _
  exact subset_convexHull ℝ _ (Set.mem_range_self 0)

theorem memV (hk0 : 0 < k) (hk1 : k < 1) : mkPt 1 0 ∈ (tE hk0 hk1).carrier := by
  show (tE hk0 hk1).pts 1 ∈ _
  exact subset_convexHull ℝ _ (Set.mem_range_self 1)

theorem memR (hk0 : 0 < k) (hk1 : k < 1) : mkPt (1 - k) 1 ∈ (tE hk0 hk1).carrier := by
  show (tE hk0 hk1).pts 2 ∈ _
  exact subset_convexHull ℝ _ (Set.mem_range_self 2)

theorem sub_Pa (hk0 : 0 < k) (hk1 : k < 1) : (tPa hk0 hk1).carrier ⊆ (tE hk0 hk1).carrier :=
  convexHull_min (Set.range_subset_iff.mpr (fun i => by
    rcases htri i with rfl | rfl | rfl
    · exact memA hk0 hk1
    · exact memV hk0 hk1
    · exact memO hk0 hk1)) (convex_convexHull ℝ _)

theorem sub_Pb (hk0 : 0 < k) (hk1 : k < 1) : (tPb hk0 hk1).carrier ⊆ (tE hk0 hk1).carrier :=
  convexHull_min (Set.range_subset_iff.mpr (fun i => by
    rcases htri i with rfl | rfl | rfl
    · exact memA hk0 hk1
    · exact memO hk0 hk1
    · exact memQ hk0 hk1)) (convex_convexHull ℝ _)

theorem sub_Pc (hk0 : 0 < k) (hk1 : k < 1) : (tPc hk0 hk1).carrier ⊆ (tE hk0 hk1).carrier :=
  convexHull_min (Set.range_subset_iff.mpr (fun i => by
    rcases htri i with rfl | rfl | rfl
    · exact memO hk0 hk1
    · exact memN hk0 hk1
    · exact memQ hk0 hk1)) (convex_convexHull ℝ _)

theorem sub_U1 (hk0 : 0 < k) (hk1 : k < 1) : (tU1 hk0 hk1).carrier ⊆ (tE hk0 hk1).carrier :=
  convexHull_min (Set.range_subset_iff.mpr (fun i => by
    rcases htri i with rfl | rfl | rfl
    · exact memN hk0 hk1
    · exact memV hk0 hk1
    · exact memR hk0 hk1)) (convex_convexHull ℝ _)

theorem sub_U2 (hk0 : 0 < k) (hk1 : k < 1) : (tU2 hk0 hk1).carrier ⊆ (tE hk0 hk1).carrier :=
  convexHull_min (Set.range_subset_iff.mpr (fun i => by
    rcases htri i with rfl | rfl | rfl
    · exact memN hk0 hk1
    · exact memR hk0 hk1
    · exact memQ hk0 hk1)) (convex_convexHull ℝ _)

end geo

section disj

variable {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1)

private theorem pw (hk0 : 0 < k) : 0 < k ^ 2 ∧ 0 < k ^ 3 ∧ 0 < k ^ 5 := ⟨by positivity, by positivity, by positivity⟩

theorem d_Pa_Pb : Disjoint (interior (tPa hk0 hk1).carrier) (interior (tPb hk0 hk1).carrier) := by
  have := pw hk0
  exact sepAB _ _ (-1) 1 0 (Or.inl (by norm_num))
    (fun i => by rcases htri i with rfl | rfl | rfl <;> simp [tPa, mkPt_zero, mkPt_one])
    (fun i => by rcases htri i with rfl | rfl | rfl <;> simp [tPb, mkPt_zero, mkPt_one, this.1.le])

theorem d_Pa_Pc : Disjoint (interior (tPa hk0 hk1).carrier) (interior (tPc hk0 hk1).carrier) := by
  have := pw hk0
  exact sepAB _ _ 0 1 0 (Or.inr one_ne_zero)
    (fun i => by rcases htri i with rfl | rfl | rfl <;> simp [tPa, mkPt_zero, mkPt_one, hk0.le])
    (fun i => by rcases htri i with rfl | rfl | rfl <;> simp [tPc, mkPt_zero, mkPt_one, this.1.le])

theorem d_Pa_U1 : Disjoint (interior (tPa hk0 hk1).carrier) (interior (tU1 hk0 hk1).carrier) :=
  sepAB _ _ 0 1 0 (Or.inr one_ne_zero)
    (fun i => by rcases htri i with rfl | rfl | rfl <;> simp [tPa, mkPt_zero, mkPt_one, hk0.le])
    (fun i => by rcases htri i with rfl | rfl | rfl <;> simp [tU1, mkPt_zero, mkPt_one])

theorem d_Pa_U2 : Disjoint (interior (tPa hk0 hk1).carrier) (interior (tU2 hk0 hk1).carrier) := by
  have := pw hk0
  exact sepAB _ _ 0 1 0 (Or.inr one_ne_zero)
    (fun i => by rcases htri i with rfl | rfl | rfl <;> simp [tPa, mkPt_zero, mkPt_one, hk0.le])
    (fun i => by rcases htri i with rfl | rfl | rfl <;> simp [tU2, mkPt_zero, mkPt_one, this.1.le])

theorem d_Pb_Pc : Disjoint (interior (tPb hk0 hk1).carrier) (interior (tPc hk0 hk1).carrier) := by
  have := pw hk0
  exact sepAB _ _ 1 0 0 (Or.inl one_ne_zero)
    (fun i => by rcases htri i with rfl | rfl | rfl <;> simp [tPb, mkPt_zero, mkPt_one, hk0.le])
    (fun i => by rcases htri i with rfl | rfl | rfl <;> simp [tPc, mkPt_zero, mkPt_one, this.2.1.le])

theorem d_Pb_U1 : Disjoint (interior (tPb hk0 hk1).carrier) (interior (tU1 hk0 hk1).carrier) := by
  have := pw hk0
  have h1 : 0 < 1 - k := by linarith
  exact sepAB _ _ 1 0 0 (Or.inl one_ne_zero)
    (fun i => by rcases htri i with rfl | rfl | rfl <;> simp [tPb, mkPt_zero, mkPt_one, hk0.le])
    (fun i => by rcases htri i with rfl | rfl | rfl <;> simp [tU1, mkPt_zero, mkPt_one, this.2.1.le, h1.le])

theorem d_Pb_U2 : Disjoint (interior (tPb hk0 hk1).carrier) (interior (tU2 hk0 hk1).carrier) := by
  have := pw hk0
  have h1 : 0 < 1 - k := by linarith
  exact sepAB _ _ 1 0 0 (Or.inl one_ne_zero)
    (fun i => by rcases htri i with rfl | rfl | rfl <;> simp [tPb, mkPt_zero, mkPt_one, hk0.le])
    (fun i => by rcases htri i with rfl | rfl | rfl <;> simp [tU2, mkPt_zero, mkPt_one, this.2.1.le, h1.le])

theorem d_Pc_U1 : Disjoint (interior (tPc hk0 hk1).carrier) (interior (tU1 hk0 hk1).carrier) := by
  have := pw hk0
  have h25 := k5_le_k2 hk0 hk1
  have h1 : 0 < 1 - k := by linarith
  refine sepAB _ _ (k ^ 2) (k ^ 3) (k ^ 5) (Or.inl this.1.ne') ?_ ?_
  · intro i; rcases htri i with rfl | rfl | rfl <;> simp [tPc, mkPt_zero, mkPt_one] <;> nlinarith [this.1, this.2.1, this.2.2]
  · intro i; rcases htri i with rfl | rfl | rfl <;> simp [tU1, mkPt_zero, mkPt_one] <;> nlinarith [this.1, this.2.1, this.2.2]

theorem d_Pc_U2 : Disjoint (interior (tPc hk0 hk1).carrier) (interior (tU2 hk0 hk1).carrier) := by
  have := pw hk0
  have h25 := k5_le_k2 hk0 hk1
  have h1 : 0 < 1 - k := by linarith
  refine sepAB _ _ (k ^ 2) (k ^ 3) (k ^ 5) (Or.inl this.1.ne') ?_ ?_
  · intro i; rcases htri i with rfl | rfl | rfl <;> simp [tPc, mkPt_zero, mkPt_one] <;> nlinarith [this.1, this.2.1, this.2.2]
  · intro i; rcases htri i with rfl | rfl | rfl <;> simp [tU2, mkPt_zero, mkPt_one] <;> nlinarith [this.1, this.2.1, this.2.2]

theorem d_U2_U1 : Disjoint (interior (tU2 hk0 hk1).carrier) (interior (tU1 hk0 hk1).carrier) := by
  have := pw hk0
  have h25 := k5_le_k2 hk0 hk1
  have h1 : 0 < 1 - k := by linarith
  have h3 := k3_lt hk0 hk1
  refine sepAB _ _ 1 (-(1 - k - k ^ 3)) (k ^ 3) (Or.inl one_ne_zero) ?_ ?_
  · intro i; rcases htri i with rfl | rfl | rfl <;> simp [tU2, mkPt_zero, mkPt_one] <;> nlinarith [this.1, this.2.1, this.2.2]
  · intro i; rcases htri i with rfl | rfl | rfl <;> simp [tU1, mkPt_zero, mkPt_one] <;> nlinarith [this.1, this.2.1, this.2.2]

end disj

section cover

variable {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1)

/-- the five pieces `A V O`, `A O Q`, `O N Q`, `N V R`, `N R Q`. -/
noncomputable def pieces : Fin 5 → Tri :=
  ![tPa hk0 hk1, tPb hk0 hk1, tPc hk0 hk1, tU1 hk0 hk1, tU2 hk0 hk1]

theorem cover5 : (⋃ i, (pieces hk0 hk1 i).carrier) = (tE hk0 hk1).carrier := by
  refine covers_of_volume_tri (tE hk0 hk1) (pieces hk0 hk1) ?_ ?_ ?_
  · intro i; fin_cases i
    exacts [sub_Pa hk0 hk1, sub_Pb hk0 hk1, sub_Pc hk0 hk1, sub_U1 hk0 hk1, sub_U2 hk0 hk1]
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact d_Pa_Pb hk0 hk1
    · exact d_Pa_Pc hk0 hk1
    · exact d_Pa_U1 hk0 hk1
    · exact d_Pa_U2 hk0 hk1
    · exact (d_Pa_Pb hk0 hk1).symm
    · exact absurd rfl hij
    · exact d_Pb_Pc hk0 hk1
    · exact d_Pb_U1 hk0 hk1
    · exact d_Pb_U2 hk0 hk1
    · exact (d_Pa_Pc hk0 hk1).symm
    · exact (d_Pb_Pc hk0 hk1).symm
    · exact absurd rfl hij
    · exact d_Pc_U1 hk0 hk1
    · exact d_Pc_U2 hk0 hk1
    · exact (d_Pa_U1 hk0 hk1).symm
    · exact (d_Pb_U1 hk0 hk1).symm
    · exact (d_Pc_U1 hk0 hk1).symm
    · exact absurd rfl hij
    · exact (d_U2_U1 hk0 hk1).symm
    · exact (d_Pa_U2 hk0 hk1).symm
    · exact (d_Pb_U2 hk0 hk1).symm
    · exact (d_Pc_U2 hk0 hk1).symm
    · exact d_U2_U1 hk0 hk1
    · exact absurd rfl hij
  · refine Erdos634.AreaDet.area_identity_of_det _ _ ?_
    have h3 := k3_lt hk0 hk1
    have h1 : 0 < 1 - k ^ 3 := by linarith
    rw [Fin.sum_univ_five]
    show |Erdos634.AreaDet.detTri (tPa hk0 hk1)| + |Erdos634.AreaDet.detTri (tPb hk0 hk1)|
      + |Erdos634.AreaDet.detTri (tPc hk0 hk1)| + |Erdos634.AreaDet.detTri (tU1 hk0 hk1)|
      + |Erdos634.AreaDet.detTri (tU2 hk0 hk1)| = |Erdos634.AreaDet.detTri (tE hk0 hk1)|
    simp only [tPa, tPb, tPc, tU1, tU2, tE, detTri_mkTri]
    rw [det_Pa, det_Pb, det_Pc, det_U1, det_U2, det_E, abs_of_pos hk0, abs_of_pos (by positivity),
      abs_of_pos (by positivity), abs_of_pos h1, abs_of_pos (by positivity), abs_of_pos (by positivity)]
    ring

end cover

end Erdos634.LaczL33
