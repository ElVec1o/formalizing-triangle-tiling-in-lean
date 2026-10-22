import Erdos634.Draft.LaczFormalL24Geo

/-!
# Theorem 2.4, first triple: covering of the target `GBE` by the five pieces of Fig. 4

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.4, Fig. 4), Beeson, Beeson-Zhang, Zhang.
-/

namespace Erdos634.LaczL24

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22

def inT1 (a : ℝ) (z : Plane) : Prop := 0 ≤ z 0 ∧ 0 ≤ z 1 ∧ gE a * z 0 + z 1 ≤ gE a

theorem convex_inT1 (a : ℝ) : Convex ℝ {z : Plane | inT1 a z} := by
  intro x hx y hy p q hp hq hpq
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  simp only [inT1, Set.mem_setOf_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  obtain rfl : q = 1 - p := by linarith
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [mul_nonneg hp hx1, mul_nonneg hq hy1]
  · nlinarith [mul_nonneg hp hx2, mul_nonneg hq hy2]
  · nlinarith [mul_nonneg hp (sub_nonneg.2 hx3), mul_nonneg hq (sub_nonneg.2 hy3)]

section cover
variable {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)

private theorem htri3'' : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide

theorem T1_carrier :
    (triT1 a ha0 ha1).carrier = {z : Plane | inT1 a z} := by
  have he := gE_gt ha0 ha1
  have hd1 := gDel_gt ha0 ha1
  apply Set.Subset.antisymm
  · refine convexHull_min (Set.range_subset_iff.mpr ?_) (convex_inT1 a)
    intro k
    rcases htri3'' k with rfl | rfl | rfl
    · show inT1 a (mkPt 0 0); simp [inT1]; linarith
    · show inT1 a (mkPt 1 0); simp [inT1]
    · show inT1 a (mkPt 0 (gE a)); simp [inT1]; linarith
  · intro z hz
    obtain ⟨hs, ht, hh⟩ := hz
    have hepos : 0 < gE a := by linarith
    rw [← mkPt_self z]
    refine mem_mkTri_of_dets (x0 := 0) (y0 := 0) (x1 := 1) (y1 := 0) (x2 := 0) (y2 := gE a) _ ?_ ?_ ?_
    · simp only [det3]; apply div_nonneg <;> nlinarith
    · simp only [det3]; apply div_nonneg <;> nlinarith
    · simp only [det3]; apply div_nonneg <;> nlinarith


/-- Vertices of the pieces lie in the target. -/
theorem pieces_sub_T1 :
    (trapSet (gTau a) ∪ (triBCA a ha0 ha1).carrier ∪ (triACD a ha0 ha1).carrier
      ∪ (triADE a ha0 ha1).carrier ∪ (triCDF a ha0 ha1).carrier) ⊆ {z : Plane | inT1 a z} := by
  have he := gE_gt ha0 ha1
  have hd1 := gDel_gt ha0 ha1
  have hb := gb_pos ha0 ha1
  have hτ0 := gTau_pos ha0 ha1
  have hτ1 := gTau_lt_one ha0 ha1
  have hAe := gAe ha0 ha1
  have hepos : 0 < gE a := by linarith
  have hsub : ∀ T : Tri, (∀ k, inT1 a (T.pts k)) → T.carrier ⊆ {z : Plane | inT1 a z} := fun T hT =>
    convexHull_min (Set.range_subset_iff.mpr hT) (convex_inT1 a)
  intro z hz
  rcases hz with (((hz | hz) | hz) | hz) | hz
  · obtain ⟨h1, h2, h3, h4⟩ := hz
    refine ⟨h3, h1, ?_⟩
    have e1 : gE a * z 0 ≤ gE a * (1 + (gTau a - 1) * z 1) := mul_le_mul_of_nonneg_left h4 hepos.le
    calc gE a * z 0 + z 1 ≤ gE a * (1 + (gTau a - 1) * z 1) + z 1 := by linarith
      _ = gE a + z 1 * (1 - gE a * (1 - gTau a)) := by ring
      _ = gE a + z 1 * (1 - (2 - a ^ 2)) := by rw [hAe]
      _ ≤ gE a := by nlinarith [mul_nonneg h1 hb.le]
  · refine hsub _ ?_ hz
    intro k
    rcases htri3'' k with rfl | rfl | rfl
    · show inT1 a (mkPt 1 0); simp [inT1]
    · show inT1 a (mkPt (gTau a) 1); simp [inT1]; refine ⟨hτ0.le, ?_⟩; nlinarith
    · show inT1 a (mkPt (gTau a) (2 - a ^ 2)); simp [inT1]; refine ⟨hτ0.le, by nlinarith, ?_⟩; nlinarith
  · refine hsub _ ?_ hz
    intro k
    rcases htri3'' k with rfl | rfl | rfl
    · show inT1 a (mkPt (gTau a) (2 - a ^ 2)); simp [inT1]; refine ⟨hτ0.le, by nlinarith, ?_⟩; nlinarith
    · show inT1 a (mkPt (gTau a) 1); simp [inT1]; refine ⟨hτ0.le, ?_⟩; nlinarith
    · show inT1 a (mkPt 0 (gDel a)); simp [inT1]; constructor <;> linarith [gE_gt ha0 ha1]
  · refine hsub _ ?_ hz
    intro k
    rcases htri3'' k with rfl | rfl | rfl
    · show inT1 a (mkPt (gTau a) (2 - a ^ 2)); simp [inT1]; refine ⟨hτ0.le, by nlinarith, ?_⟩; nlinarith
    · show inT1 a (mkPt 0 (gDel a)); simp [inT1]; constructor <;> linarith [gE_gt ha0 ha1]
    · show inT1 a (mkPt 0 (gE a)); simp [inT1]; linarith
  · refine hsub _ ?_ hz
    intro k
    rcases htri3'' k with rfl | rfl | rfl
    · show inT1 a (mkPt (gTau a) 1); simp [inT1]; refine ⟨hτ0.le, ?_⟩; nlinarith
    · show inT1 a (mkPt 0 (gDel a)); simp [inT1]; constructor <;> linarith [gE_gt ha0 ha1]
    · show inT1 a (mkPt 0 1); simp [inT1]; linarith


set_option maxHeartbeats 400000 in
theorem mem_BCA (z : Plane) (hτs : gTau a ≤ z 0) (h2 : (gTau a - 1) * z 1 - z 0 + 1 ≤ 0)
    (hh : gE a * z 0 + z 1 ≤ gE a) : z ∈ (triBCA a ha0 ha1).carrier := by
  have hb := gb_pos ha0 ha1
  have hτ1 := gTau_lt_one ha0 ha1
  have hAe := gAe ha0 ha1
  rw [← mkPt_self z]
  unfold triBCA
  have hD : det3 1 0 (gTau a) 1 (gTau a) (2 - a ^ 2) = (gTau a - 1) * (1 - a ^ 2) := by
    simp only [det3]; ring
  have hDn : (gTau a - 1) * (1 - a ^ 2) < 0 := mul_neg_of_neg_of_pos (by linarith) hb
  refine mem_mkTri_of_dets _ ?_ ?_ ?_
  · apply div_nonneg_of_nonpos
    · have : det3 (z 0) (z 1) (gTau a) 1 (gTau a) (2 - a ^ 2) = (gTau a - z 0) * (1 - a ^ 2) := by
        simp only [det3]; ring
      rw [this]; nlinarith
    · rw [hD]; exact hDn.le
  · apply div_nonneg_of_nonpos
    · have : det3 1 0 (z 0) (z 1) (gTau a) (2 - a ^ 2)
          = (1 - gTau a) * (gE a * z 0 + z 1 - gE a) := by
        simp only [det3]; rw [← hAe]; ring
      rw [this]; nlinarith
    · rw [hD]; exact hDn.le
  · apply div_nonneg_of_nonpos
    · have : det3 1 0 (gTau a) 1 (z 0) (z 1) = (gTau a - 1) * z 1 - z 0 + 1 := by
        simp only [det3]; ring
      rw [this]; exact h2
    · rw [hD]; exact hDn.le

set_option maxHeartbeats 400000 in
theorem mem_CDF (z : Plane) (hs : 0 ≤ z 0) (ht : 1 ≤ z 1)
    (hcd : (gDel a - 1) * z 0 + gTau a * z 1 - gTau a * gDel a ≤ 0) :
    z ∈ (triCDF a ha0 ha1).carrier := by
  have hτ0 := gTau_pos ha0 ha1
  have hd1 := gDel_gt ha0 ha1
  rw [← mkPt_self z]
  unfold triCDF
  have hD : det3 (gTau a) 1 0 (gDel a) 0 1 = gTau a * (gDel a - 1) := by
    simp only [det3]; ring
  have hDp : 0 < gTau a * (gDel a - 1) := mul_pos hτ0 (by linarith)
  refine mem_mkTri_of_dets _ ?_ ?_ ?_
  · apply div_nonneg
    · have : det3 (z 0) (z 1) 0 (gDel a) 0 1 = z 0 * (gDel a - 1) := by
        simp only [det3]; ring
      rw [this]; exact mul_nonneg hs (by linarith)
    · rw [hD]; exact hDp.le
  · apply div_nonneg
    · have : det3 (gTau a) 1 (z 0) (z 1) 0 1 = gTau a * (z 1 - 1) := by
        simp only [det3]; ring
      rw [this]; exact mul_nonneg hτ0.le (by linarith)
    · rw [hD]; exact hDp.le
  · apply div_nonneg
    · have : det3 (gTau a) 1 0 (gDel a) (z 0) (z 1)
          = -((gDel a - 1) * z 0 + gTau a * z 1 - gTau a * gDel a) := by
        simp only [det3]; ring
      rw [this]; linarith
    · rw [hD]; exact hDp.le

set_option maxHeartbeats 400000 in
theorem mem_ACD (z : Plane) (hsτ : z 0 ≤ gTau a)
    (hcd : 0 ≤ (gDel a - 1) * z 0 + gTau a * z 1 - gTau a * gDel a)
    (had : (gDel a - 1 - (1 - a ^ 2)) * z 0 + gTau a * z 1 - gTau a * gDel a ≤ 0) :
    z ∈ (triACD a ha0 ha1).carrier := by
  have hb := gb_pos ha0 ha1
  have hτ0 := gTau_pos ha0 ha1
  rw [← mkPt_self z]
  unfold triACD
  have hD : det3 (gTau a) (2 - a ^ 2) (gTau a) 1 0 (gDel a) = -(gTau a * (1 - a ^ 2)) := by
    simp only [det3]; ring
  have hDn : -(gTau a * (1 - a ^ 2)) < 0 := by
    have := mul_pos hτ0 hb; linarith
  refine mem_mkTri_of_dets _ ?_ ?_ ?_
  · apply div_nonneg_of_nonpos
    · have : det3 (z 0) (z 1) (gTau a) 1 0 (gDel a)
          = -((gDel a - 1) * z 0 + gTau a * z 1 - gTau a * gDel a) := by
        simp only [det3]; ring
      rw [this]; linarith
    · rw [hD]; exact hDn.le
  · apply div_nonneg_of_nonpos
    · have : det3 (gTau a) (2 - a ^ 2) (z 0) (z 1) 0 (gDel a)
          = (gDel a - 1 - (1 - a ^ 2)) * z 0 + gTau a * z 1 - gTau a * gDel a := by
        simp only [det3]; ring
      rw [this]; exact had
    · rw [hD]; exact hDn.le
  · apply div_nonneg_of_nonpos
    · have : det3 (gTau a) (2 - a ^ 2) (gTau a) 1 (z 0) (z 1) = (z 0 - gTau a) * (1 - a ^ 2) := by
        simp only [det3]; ring
      rw [this]; nlinarith
    · rw [hD]; exact hDn.le

set_option maxHeartbeats 400000 in
theorem mem_ADE (z : Plane) (hs : 0 ≤ z 0)
    (had : 0 ≤ (gDel a - 1 - (1 - a ^ 2)) * z 0 + gTau a * z 1 - gTau a * gDel a)
    (hh : gE a * z 0 + z 1 ≤ gE a) : z ∈ (triADE a ha0 ha1).carrier := by
  have hτ0 := gTau_pos ha0 ha1
  have hed := sub_pos.2 (gE_gt ha0 ha1)
  have hAe := gAe ha0 ha1
  rw [← mkPt_self z]
  unfold triADE
  have hD : det3 (gTau a) (2 - a ^ 2) 0 (gDel a) 0 (gE a) = -(gTau a * (gE a - gDel a)) := by
    simp only [det3]; ring
  have hDn : -(gTau a * (gE a - gDel a)) < 0 := by
    have := mul_pos hτ0 hed; linarith
  refine mem_mkTri_of_dets _ ?_ ?_ ?_
  · apply div_nonneg_of_nonpos
    · have : det3 (z 0) (z 1) 0 (gDel a) 0 (gE a) = -(z 0 * (gE a - gDel a)) := by
        simp only [det3]; ring
      rw [this]; have := mul_nonneg hs hed.le; linarith
    · rw [hD]; exact hDn.le
  · apply div_nonneg_of_nonpos
    · have : det3 (gTau a) (2 - a ^ 2) (z 0) (z 1) 0 (gE a)
          = gTau a * (gE a * z 0 + z 1 - gE a) := by
        have h2 : gE a - (2 - a ^ 2) = gE a * gTau a := by linarith [hAe]
        simp only [det3]
        have : (gE a - (2 - a ^ 2)) = gE a * gTau a := h2
        calc (z 0 - gTau a) * (gE a - (2 - a ^ 2)) - (0 - gTau a) * (z 1 - (2 - a ^ 2))
            = (z 0 - gTau a) * (gE a * gTau a) - (0 - gTau a) * (z 1 - (2 - a ^ 2)) := by rw [h2]
          _ = gTau a * (gE a * z 0 + z 1 - gE a * gTau a - (2 - a ^ 2)) := by ring
          _ = gTau a * (gE a * z 0 + z 1 - gE a) := by
              have : gE a * gTau a + (2 - a ^ 2) = gE a := by linarith [hAe]
              rw [show gE a * z 0 + z 1 - gE a * gTau a - (2 - a ^ 2)
                = gE a * z 0 + z 1 - (gE a * gTau a + (2 - a ^ 2)) by ring, this]
      rw [this]; exact mul_nonpos_of_nonneg_of_nonpos hτ0.le (by linarith)
    · rw [hD]; exact hDn.le
  · apply div_nonneg_of_nonpos
    · have : det3 (gTau a) (2 - a ^ 2) 0 (gDel a) (z 0) (z 1)
          = -((gDel a - 1 - (1 - a ^ 2)) * z 0 + gTau a * z 1 - gTau a * gDel a) := by
        simp only [det3]; ring
      rw [this]; linarith
    · rw [hD]; exact hDn.le

/-- Every point of the target lies in one of the pieces. -/
theorem T1_sub_pieces :
    {z : Plane | inT1 a z} ⊆ (trapSet (gTau a) ∪ (triBCA a ha0 ha1).carrier ∪ (triACD a ha0 ha1).carrier
      ∪ (triADE a ha0 ha1).carrier ∪ (triCDF a ha0 ha1).carrier) := by
  have he := gE_gt ha0 ha1
  have hd1 := gDel_gt ha0 ha1
  have hb := gb_pos ha0 ha1
  have hτ0 := gTau_pos ha0 ha1
  have hτ1 := gTau_lt_one ha0 ha1
  have hAe := gAe ha0 ha1
  intro z hz
  obtain ⟨hs, ht, hh⟩ := hz
  by_cases ht1 : z 1 ≤ 1
  · by_cases hbc : z 0 ≤ 1 + (gTau a - 1) * z 1
    · left; left; left; left
      exact ⟨ht, ht1, hs, hbc⟩
    · push Not at hbc
      have hsτ : gTau a ≤ z 0 := by
        nlinarith [mul_nonneg (sub_nonneg.2 hτ1.le) (sub_nonneg.2 ht1)]
      left; left; left; right
      exact mem_BCA ha0 ha1 z hsτ (by linarith) hh
  · push Not at ht1
    by_cases hsτ : gTau a ≤ z 0
    · left; left; left; right
      refine mem_BCA ha0 ha1 z hsτ ?_ hh
      nlinarith [mul_nonneg (sub_nonneg.2 hτ1.le) (sub_nonneg.2 ht1.le)]
    · push Not at hsτ
      by_cases hcd : (gDel a - 1) * z 0 + gTau a * z 1 - gTau a * gDel a ≤ 0
      · right
        exact mem_CDF ha0 ha1 z hs ht1.le hcd
      · push Not at hcd
        by_cases had : (gDel a - 1 - (1 - a ^ 2)) * z 0 + gTau a * z 1 - gTau a * gDel a ≤ 0
        · left; left; right
          exact mem_ACD ha0 ha1 z hsτ.le hcd.le had
        · push Not at had
          left; right
          exact mem_ADE ha0 ha1 z hs had.le hh

end cover

end Erdos634.LaczL24
