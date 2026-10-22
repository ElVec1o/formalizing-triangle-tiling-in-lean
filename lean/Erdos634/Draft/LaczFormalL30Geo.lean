import Erdos634.Draft.LaczFormalL27Std
import Erdos634.Draft.LaczFormalL24Geo
import Erdos634.CoversGeneral

/-!
# Laczkovich Theorem 2.5, triple `(2α, 2β, α+β)` (Fig. 7, second picture): the plane geometry

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.5, Fig. 7), Beeson, Beeson-Zhang, Zhang.

PRINT GAP: "Similar constructions apply for the other triples listed in (2); see Fig. 7."  Decoded from the picture (labels
`α α` at the apex, `β β` at the left vertex, `α+β` at the right vertex, three `γ` around the inner point `O`):
the triangle `Θ = A L V` is the union of the tiles `A O M`, `A V O` (both of scale `1`, mirror images over `A O`), the tile
`V L O'` (scale `ν`), and the trapezoid `M L O' O` (angles `β` at `L`, `α+β` at `O'`, `γ` at `O`, `α+γ` at `M`, the
trapezoid of Lemma 2.2 (ii)); `O'` lies on `O V`, `M` on `A L`.

All piece sizes are determined by the picture.  In the chart with origin `O` and basis `w = V - O`, `d = M - O`
(`|w| = |d| = a`, `⟨w,d⟩ = -a²/2`, `k = b/a`):
`A = (-k,-k)`, `M = (0,1)`, `O = (0,0)`, `V = (1,0)`, `O' = (θ,0)`, `L = (θ,ν)`, `θ = (1-k)/(2+k)`, `ν = (1+2k)/(k(2+k))`.
RANGE: `0 < k < 1`, i.e. `b < a` (`α > β`); for `a < b` swap the roles of `α` and `β` (the shape `(2α,2β,α+β)` is
symmetric), for `a = b` the triangle is equilateral (three tiles).
This file: the real geometry (cover, disjointness) for `0 < k < 1`.
-/

namespace Erdos634.LaczL30

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL24 MeasureTheory
open Erdos634.LaczL27 (carrier_eq_of_range range_mk3)

noncomputable def th (k : ℝ) : ℝ := (1 - k) / (2 + k)
noncomputable def nu (k : ℝ) : ℝ := (1 + 2 * k) / (k * (2 + k))

private theorem htri : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide

section geo

variable {k : ℝ}

theorem th_pos (hk0 : 0 < k) (hk1 : k < 1) : 0 < th k := by unfold th; apply div_pos <;> linarith
theorem nu_pos (hk0 : 0 < k) (hk1 : k < 1) : 0 < nu k := by unfold nu; positivity
theorem th_lt_one (hk0 : 0 < k) (hk1 : k < 1) : th k < 1 := by
  unfold th; rw [div_lt_one (by linarith)]; linarith

/-! ### determinants -/

theorem det_Th (hk0 : 0 < k) (hk1 : k < 1) : det3 (-k) (-k) 1 0 (th k) (nu k) = (2 * k + 1) * (k ^ 2 + k + 1) / (k * (k + 2)) := by
  have : k ≠ 0 := hk0.ne'
  have : k + 2 ≠ 0 := by linarith
  have : 2 + k ≠ 0 := by linarith
  unfold det3 th nu; field_simp; ring

theorem det_P1 : det3 (-k) (-k) 0 0 0 1 = k := by unfold det3; ring
theorem det_P2 : det3 (-k) (-k) 1 0 0 0 = k := by unfold det3; ring
theorem det_S1 : det3 0 0 (th k) 0 0 1 = th k := by unfold det3; ring
theorem det_S2 : det3 (th k) 0 (th k) (nu k) 0 1 = nu k * th k := by unfold det3; ring
theorem det_P3 : det3 1 0 (th k) (nu k) (th k) 0 = (1 - th k) * nu k := by unfold det3; ring

theorem detpos_Th (hk0 : 0 < k) (hk1 : k < 1) : 0 < det3 (-k) (-k) 1 0 (th k) (nu k) := by
  rw [det_Th hk0 hk1]; positivity

/-! ### the triangles (counter-clockwise, `det3 > 0`) -/

/-- `Θ = A V L` (`A = (-k,-k)`, `V = (1,0)`, `L = (θ,ν)`): apex angle `2α` at `A`, `α+β` at `V`, `2β` at `L`. -/
noncomputable def tTh (hk0 : 0 < k) (hk1 : k < 1) : Tri := mkTri (-k) (-k) 1 0 (th k) (nu k) (detpos_Th hk0 hk1).ne'
/-- tile `A O M` (`α` at `A`, `γ` at `O`, `β` at `M`). -/
noncomputable def tP1 (hk0 : 0 < k) (hk1 : k < 1) : Tri := mkTri (-k) (-k) 0 0 0 1 (by rw [det_P1]; exact hk0.ne')
/-- tile `A V O` (`α` at `A`, `β` at `V`, `γ` at `O`). -/
noncomputable def tP2 (hk0 : 0 < k) (hk1 : k < 1) : Tri := mkTri (-k) (-k) 1 0 0 0 (by rw [det_P2]; exact hk0.ne')
/-- half `O O' M` of the trapezoid. -/
noncomputable def tS1 (hk0 : 0 < k) (hk1 : k < 1) : Tri := mkTri 0 0 (th k) 0 0 1 (by rw [det_S1]; exact (th_pos hk0 hk1).ne')
/-- half `O' L M` of the trapezoid. -/
noncomputable def tS2 (hk0 : 0 < k) (hk1 : k < 1) : Tri := mkTri (th k) 0 (th k) (nu k) 0 1 (by
  rw [det_S2]; exact (mul_pos (nu_pos hk0 hk1) (th_pos hk0 hk1)).ne')
/-- tile `V L O'` (`α` at `V`, `β` at `L`, `γ` at `O'`), scale `ν`. -/
noncomputable def tP3 (hk0 : 0 < k) (hk1 : k < 1) : Tri := mkTri 1 0 (th k) (nu k) (th k) 0 (by
  rw [det_P3]; exact (mul_pos (sub_pos.mpr (th_lt_one hk0 hk1)) (nu_pos hk0 hk1)).ne')

/-! ### vertices of the pieces lie in `Θ` -/

theorem memM (hk0 : 0 < k) (hk1 : k < 1) : mkPt 0 1 ∈ (tTh hk0 hk1).carrier := by
  have : k ≠ 0 := hk0.ne'
  have : k + 2 ≠ 0 := by linarith
  have : 2 + k ≠ 0 := by linarith
  have h1k : 0 < 1 - k := by linarith
  exact mem_carrier_of_dets (detpos_Th hk0 hk1)
    (by
      have e : det3 0 1 1 0 (th k) (nu k) = (1 - k) * (2 * k + 1) / (k * (k + 2)) := by
        unfold det3 th nu; field_simp; ring
      rw [e]; positivity)
    (by
      have e : det3 (-k) (-k) 0 1 (th k) (nu k) = 0 := by
        unfold det3 th nu; field_simp; ring
      rw [e])
    (by
      have e : det3 (-k) (-k) 1 0 0 1 = 2 * k + 1 := by unfold det3; ring
      rw [e]; linarith)

theorem memO (hk0 : 0 < k) (hk1 : k < 1) : mkPt 0 0 ∈ (tTh hk0 hk1).carrier := by
  have : k ≠ 0 := hk0.ne'
  have : k + 2 ≠ 0 := by linarith
  have : 2 + k ≠ 0 := by linarith
  exact mem_carrier_of_dets (detpos_Th hk0 hk1)
    (by
      have e : det3 0 0 1 0 (th k) (nu k) = (2 * k + 1) / (k * (k + 2)) := by
        unfold det3 th nu; field_simp; ring
      rw [e]; positivity)
    (by
      have e : det3 (-k) (-k) 0 0 (th k) (nu k) = (k ^ 2 + k + 1) / (k + 2) := by
        unfold det3 th nu; field_simp; ring
      rw [e]; positivity)
    (by
      have e : det3 (-k) (-k) 1 0 0 0 = k := by unfold det3; ring
      rw [e]; exact hk0.le)

theorem memOp (hk0 : 0 < k) (hk1 : k < 1) : mkPt (th k) 0 ∈ (tTh hk0 hk1).carrier := by
  have : k ≠ 0 := hk0.ne'
  have : k + 2 ≠ 0 := by linarith
  have : 2 + k ≠ 0 := by linarith
  exact mem_carrier_of_dets (detpos_Th hk0 hk1)
    (by
      have e : det3 (th k) 0 1 0 (th k) (nu k) = (2 * k + 1) ^ 2 / (k * (k + 2) ^ 2) := by
        unfold det3 th nu; field_simp; ring
      rw [e]; positivity)
    (by
      have e : det3 (-k) (-k) (th k) 0 (th k) (nu k) = (2 * k + 1) * (k ^ 2 + k + 1) / (k * (k + 2) ^ 2) := by
        unfold det3 th nu; field_simp; ring
      rw [e]; positivity)
    (by
      have e : det3 (-k) (-k) 1 0 (th k) 0 = k * (2 * k + 1) / (k + 2) := by
        unfold det3 th; field_simp; ring
      rw [e]; positivity)

theorem memA (hk0 : 0 < k) (hk1 : k < 1) : mkPt (-k) (-k) ∈ (tTh hk0 hk1).carrier := by
  show (tTh hk0 hk1).pts 0 ∈ _
  exact subset_convexHull ℝ _ (Set.mem_range_self 0)

theorem memV (hk0 : 0 < k) (hk1 : k < 1) : mkPt 1 0 ∈ (tTh hk0 hk1).carrier := by
  show (tTh hk0 hk1).pts 1 ∈ _
  exact subset_convexHull ℝ _ (Set.mem_range_self 1)

theorem memL (hk0 : 0 < k) (hk1 : k < 1) : mkPt (th k) (nu k) ∈ (tTh hk0 hk1).carrier := by
  show (tTh hk0 hk1).pts 2 ∈ _
  exact subset_convexHull ℝ _ (Set.mem_range_self 2)

theorem sub_P1 (hk0 : 0 < k) (hk1 : k < 1) : (tP1 hk0 hk1).carrier ⊆ (tTh hk0 hk1).carrier :=
  convexHull_min (Set.range_subset_iff.mpr (fun i => by
    rcases htri i with rfl | rfl | rfl
    · exact memA hk0 hk1
    · exact memO hk0 hk1
    · exact memM hk0 hk1)) (convex_convexHull ℝ _)

theorem sub_P2 (hk0 : 0 < k) (hk1 : k < 1) : (tP2 hk0 hk1).carrier ⊆ (tTh hk0 hk1).carrier :=
  convexHull_min (Set.range_subset_iff.mpr (fun i => by
    rcases htri i with rfl | rfl | rfl
    · exact memA hk0 hk1
    · exact memV hk0 hk1
    · exact memO hk0 hk1)) (convex_convexHull ℝ _)

theorem sub_S1 (hk0 : 0 < k) (hk1 : k < 1) : (tS1 hk0 hk1).carrier ⊆ (tTh hk0 hk1).carrier :=
  convexHull_min (Set.range_subset_iff.mpr (fun i => by
    rcases htri i with rfl | rfl | rfl
    · exact memO hk0 hk1
    · exact memOp hk0 hk1
    · exact memM hk0 hk1)) (convex_convexHull ℝ _)

theorem sub_S2 (hk0 : 0 < k) (hk1 : k < 1) : (tS2 hk0 hk1).carrier ⊆ (tTh hk0 hk1).carrier :=
  convexHull_min (Set.range_subset_iff.mpr (fun i => by
    rcases htri i with rfl | rfl | rfl
    · exact memOp hk0 hk1
    · exact memL hk0 hk1
    · exact memM hk0 hk1)) (convex_convexHull ℝ _)

theorem sub_P3 (hk0 : 0 < k) (hk1 : k < 1) : (tP3 hk0 hk1).carrier ⊆ (tTh hk0 hk1).carrier :=
  convexHull_min (Set.range_subset_iff.mpr (fun i => by
    rcases htri i with rfl | rfl | rfl
    · exact memV hk0 hk1
    · exact memL hk0 hk1
    · exact memOp hk0 hk1)) (convex_convexHull ℝ _)

end geo

/-! ### separation, area, cover -/

theorem sepAB (T U : Tri) (a b c : ℝ) (hab : a ≠ 0 ∨ b ≠ 0)
    (h1 : ∀ i, a * (T.pts i) 0 + b * (T.pts i) 1 ≤ c) (h2 : ∀ i, c ≤ a * (U.pts i) 0 + b * (U.pts i) 1) :
    Disjoint (interior T.carrier) (interior U.carrier) :=
  sep_tri (coordFun a b 0) (coordFun_linear_ne_zero 0 hab) c (fun i => by simpa using h1 i)
    (fun i => by simpa using h2 i)

section disj

variable {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1)

theorem d_P1_P2 : Disjoint (interior (tP1 hk0 hk1).carrier) (interior (tP2 hk0 hk1).carrier) :=
  sepAB _ _ 1 (-1) 0 (Or.inl one_ne_zero)
    (fun i => by rcases htri i with rfl | rfl | rfl <;> simp [tP1, mkPt_zero, mkPt_one])
    (fun i => by rcases htri i with rfl | rfl | rfl <;> simp [tP2, mkPt_zero, mkPt_one])

theorem d_P1_S1 : Disjoint (interior (tP1 hk0 hk1).carrier) (interior (tS1 hk0 hk1).carrier) :=
  sepAB _ _ 1 0 0 (Or.inl one_ne_zero)
    (fun i => by rcases htri i with rfl | rfl | rfl <;> simp [tP1, mkPt_zero, mkPt_one, hk0.le])
    (fun i => by rcases htri i with rfl | rfl | rfl <;> simp [tS1, mkPt_zero, mkPt_one, (th_pos hk0 hk1).le])

theorem d_P1_S2 : Disjoint (interior (tP1 hk0 hk1).carrier) (interior (tS2 hk0 hk1).carrier) :=
  sepAB _ _ 1 0 0 (Or.inl one_ne_zero)
    (fun i => by rcases htri i with rfl | rfl | rfl <;> simp [tP1, mkPt_zero, mkPt_one, hk0.le])
    (fun i => by rcases htri i with rfl | rfl | rfl <;> simp [tS2, mkPt_zero, mkPt_one, (th_pos hk0 hk1).le])

theorem d_P1_P3 : Disjoint (interior (tP1 hk0 hk1).carrier) (interior (tP3 hk0 hk1).carrier) :=
  sepAB _ _ 1 0 0 (Or.inl one_ne_zero)
    (fun i => by rcases htri i with rfl | rfl | rfl <;> simp [tP1, mkPt_zero, mkPt_one, hk0.le])
    (fun i => by rcases htri i with rfl | rfl | rfl <;> simp [tP3, mkPt_zero, mkPt_one, (th_pos hk0 hk1).le])

theorem d_P2_S1 : Disjoint (interior (tP2 hk0 hk1).carrier) (interior (tS1 hk0 hk1).carrier) :=
  sepAB _ _ 0 1 0 (Or.inr one_ne_zero)
    (fun i => by rcases htri i with rfl | rfl | rfl <;> simp [tP2, mkPt_zero, mkPt_one, hk0.le])
    (fun i => by rcases htri i with rfl | rfl | rfl <;> simp [tS1, mkPt_zero, mkPt_one])

theorem d_P2_S2 : Disjoint (interior (tP2 hk0 hk1).carrier) (interior (tS2 hk0 hk1).carrier) :=
  sepAB _ _ 0 1 0 (Or.inr one_ne_zero)
    (fun i => by rcases htri i with rfl | rfl | rfl <;> simp [tP2, mkPt_zero, mkPt_one, hk0.le])
    (fun i => by rcases htri i with rfl | rfl | rfl <;> simp [tS2, mkPt_zero, mkPt_one, (nu_pos hk0 hk1).le])

theorem d_P2_P3 : Disjoint (interior (tP2 hk0 hk1).carrier) (interior (tP3 hk0 hk1).carrier) :=
  sepAB _ _ 0 1 0 (Or.inr one_ne_zero)
    (fun i => by rcases htri i with rfl | rfl | rfl <;> simp [tP2, mkPt_zero, mkPt_one, hk0.le])
    (fun i => by rcases htri i with rfl | rfl | rfl <;> simp [tP3, mkPt_zero, mkPt_one, (nu_pos hk0 hk1).le])

theorem d_S1_S2 : Disjoint (interior (tS1 hk0 hk1).carrier) (interior (tS2 hk0 hk1).carrier) := by
  have ht := th_pos hk0 hk1
  have hn := nu_pos hk0 hk1
  refine sepAB _ _ 1 (th k) (th k) (Or.inl one_ne_zero) ?_ ?_
  · intro i; rcases htri i with rfl | rfl | rfl <;> simp [tS1, mkPt_zero, mkPt_one] <;> nlinarith
  · intro i; rcases htri i with rfl | rfl | rfl <;> simp [tS2, mkPt_zero, mkPt_one] <;> nlinarith [mul_pos ht hn]

theorem d_S1_P3 : Disjoint (interior (tS1 hk0 hk1).carrier) (interior (tP3 hk0 hk1).carrier) := by
  have ht := th_pos hk0 hk1
  have h1 := th_lt_one hk0 hk1
  refine sepAB _ _ 1 0 (th k) (Or.inl one_ne_zero) ?_ ?_
  · intro i; rcases htri i with rfl | rfl | rfl <;> simp [tS1, mkPt_zero, mkPt_one] <;> linarith
  · intro i; rcases htri i with rfl | rfl | rfl <;> simp [tP3, mkPt_zero, mkPt_one] <;> linarith

theorem d_S2_P3 : Disjoint (interior (tS2 hk0 hk1).carrier) (interior (tP3 hk0 hk1).carrier) := by
  have ht := th_pos hk0 hk1
  have h1 := th_lt_one hk0 hk1
  refine sepAB _ _ 1 0 (th k) (Or.inl one_ne_zero) ?_ ?_
  · intro i; rcases htri i with rfl | rfl | rfl <;> simp [tS2, mkPt_zero, mkPt_one] <;> linarith
  · intro i; rcases htri i with rfl | rfl | rfl <;> simp [tP3, mkPt_zero, mkPt_one] <;> linarith

end disj



section cover

variable {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1)

/-- the five pieces `A O M`, `A V O`, `O O' M`, `O' L M`, `V L O'`. -/
noncomputable def pieces : Fin 5 → Tri :=
  ![tP1 hk0 hk1, tP2 hk0 hk1, tS1 hk0 hk1, tS2 hk0 hk1, tP3 hk0 hk1]

theorem cover5 : (⋃ i, (pieces hk0 hk1 i).carrier) = (tTh hk0 hk1).carrier := by
  refine covers_of_volume_tri (tTh hk0 hk1) (pieces hk0 hk1) ?_ ?_ ?_
  · intro i; fin_cases i
    exacts [sub_P1 hk0 hk1, sub_P2 hk0 hk1, sub_S1 hk0 hk1, sub_S2 hk0 hk1, sub_P3 hk0 hk1]
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact d_P1_P2 hk0 hk1
    · exact d_P1_S1 hk0 hk1
    · exact d_P1_S2 hk0 hk1
    · exact d_P1_P3 hk0 hk1
    · exact (d_P1_P2 hk0 hk1).symm
    · exact absurd rfl hij
    · exact d_P2_S1 hk0 hk1
    · exact d_P2_S2 hk0 hk1
    · exact d_P2_P3 hk0 hk1
    · exact (d_P1_S1 hk0 hk1).symm
    · exact (d_P2_S1 hk0 hk1).symm
    · exact absurd rfl hij
    · exact d_S1_S2 hk0 hk1
    · exact d_S1_P3 hk0 hk1
    · exact (d_P1_S2 hk0 hk1).symm
    · exact (d_P2_S2 hk0 hk1).symm
    · exact (d_S1_S2 hk0 hk1).symm
    · exact absurd rfl hij
    · exact d_S2_P3 hk0 hk1
    · exact (d_P1_P3 hk0 hk1).symm
    · exact (d_P2_P3 hk0 hk1).symm
    · exact (d_S1_P3 hk0 hk1).symm
    · exact (d_S2_P3 hk0 hk1).symm
    · exact absurd rfl hij
  · refine Erdos634.AreaDet.area_identity_of_det _ _ ?_
    have ht := th_pos hk0 hk1
    have hn := nu_pos hk0 hk1
    have h1 := th_lt_one hk0 hk1
    rw [Fin.sum_univ_five]
    show |Erdos634.AreaDet.detTri (tP1 hk0 hk1)| + |Erdos634.AreaDet.detTri (tP2 hk0 hk1)|
      + |Erdos634.AreaDet.detTri (tS1 hk0 hk1)| + |Erdos634.AreaDet.detTri (tS2 hk0 hk1)|
      + |Erdos634.AreaDet.detTri (tP3 hk0 hk1)| = |Erdos634.AreaDet.detTri (tTh hk0 hk1)|
    simp only [tP1, tP2, tS1, tS2, tP3, tTh, detTri_mkTri]
    rw [det_P1, det_P2, det_S1, det_S2, det_P3, det_Th hk0 hk1,
      abs_of_pos hk0, abs_of_pos ht, abs_of_pos (mul_pos hn ht),
      abs_of_pos (mul_pos (sub_pos.mpr h1) hn), abs_of_pos (by have := detpos_Th hk0 hk1; rwa [det_Th hk0 hk1] at this)]
    have : k ≠ 0 := hk0.ne'
    have : k + 2 ≠ 0 := by linarith
    have : 2 + k ≠ 0 := by linarith
    unfold th nu; field_simp; ring

end cover

end Erdos634.LaczL30
