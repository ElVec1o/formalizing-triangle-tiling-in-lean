import Erdos634.Draft.LaczFormalL26Thm

/-!
# Laczkovich Theorem 2.4, triples 2, 3, 5 of (1): generic fans in a chart

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.4, Fig. 5), Beeson, Beeson-Zhang, Zhang.

A *fan* with apex `P = (p,q)` over the line `x ↦ B + x e` is the triangle `P, B + x e, B + y e`.  Containment, interior
disjointness and the area identity are proved once, for any apex, any base line (`κ = (b-p) × e > 0`).  The constructions
for Fig. 5 (second, third, fifth triple) are fans of tiles and of the fourth-triple triangle.
-/

namespace Erdos634.LaczL27

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL24 Erdos634.LaczL26

section fan

variable (p q b1 b2 e1 e2 : ℝ)

/-- the cross product `κ = (B - P) × e`. -/
def kap : ℝ := (b1 - p) * e2 - (b2 - q) * e1

theorem fan_det (x y : ℝ) :
    det3 p q (b1 + x * e1) (b2 + x * e2) (b1 + y * e1) (b2 + y * e2) = (y - x) * kap p q b1 b2 e1 e2 := by
  unfold det3 kap; ring

theorem fan_det_ne (hκ : kap p q b1 b2 e1 e2 ≠ 0) {x y : ℝ} (hxy : x ≠ y) :
    det3 p q (b1 + x * e1) (b2 + x * e2) (b1 + y * e1) (b2 + y * e2) ≠ 0 := by
  rw [fan_det]; exact mul_ne_zero (sub_ne_zero.mpr hxy.symm) hκ

/-- the fan triangle `P, B + x e, B + y e`. -/
noncomputable def fanTri (hκ : kap p q b1 b2 e1 e2 ≠ 0) {x y : ℝ} (hxy : x ≠ y) : Tri :=
  mkTri p q (b1 + x * e1) (b2 + x * e2) (b1 + y * e1) (b2 + y * e2) (fan_det_ne p q b1 b2 e1 e2 hκ hxy)

variable {p q b1 b2 e1 e2}

private theorem htri : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide

theorem fan_memP (hκ : 0 < kap p q b1 b2 e1 e2) {u0 u1 : ℝ} (h01 : u0 < u1) (hne : kap p q b1 b2 e1 e2 ≠ 0) :
    mkPt p q ∈ (fanTri p q b1 b2 e1 e2 hne (ne_of_lt h01)).carrier := by
  have hD : 0 < det3 p q (b1 + u0 * e1) (b2 + u0 * e2) (b1 + u1 * e1) (b2 + u1 * e2) := by
    rw [fan_det]; exact mul_pos (by linarith) hκ
  exact mem_carrier_of_dets hD (by rw [fan_det]; exact mul_nonneg (by linarith) hκ.le)
    (by unfold det3; ring_nf; exact le_refl _) (by unfold det3; ring_nf; exact le_refl _)

theorem fan_memB (hκ : 0 < kap p q b1 b2 e1 e2) {u0 u1 : ℝ} (h01 : u0 < u1) (hne : kap p q b1 b2 e1 e2 ≠ 0)
    {z : ℝ} (hz0 : u0 ≤ z) (hz1 : z ≤ u1) :
    mkPt (b1 + z * e1) (b2 + z * e2) ∈ (fanTri p q b1 b2 e1 e2 hne (ne_of_lt h01)).carrier := by
  have hD : 0 < det3 p q (b1 + u0 * e1) (b2 + u0 * e2) (b1 + u1 * e1) (b2 + u1 * e2) := by
    rw [fan_det]; exact mul_pos (by linarith) hκ
  refine mem_carrier_of_dets hD ?_ ?_ ?_
  · have : det3 (b1 + z * e1) (b2 + z * e2) (b1 + u0 * e1) (b2 + u0 * e2) (b1 + u1 * e1) (b2 + u1 * e2) = 0 := by
      unfold det3; ring
    rw [this]
  · have : det3 p q (b1 + z * e1) (b2 + z * e2) (b1 + u1 * e1) (b2 + u1 * e2) = (u1 - z) * kap p q b1 b2 e1 e2 :=
      fan_det p q b1 b2 e1 e2 z u1
    rw [this]; exact mul_nonneg (by linarith) hκ.le
  · have : det3 p q (b1 + u0 * e1) (b2 + u0 * e2) (b1 + z * e1) (b2 + z * e2) = (z - u0) * kap p q b1 b2 e1 e2 :=
      fan_det p q b1 b2 e1 e2 u0 z
    rw [this]; exact mul_nonneg (by linarith) hκ.le

/-- A fan over a sub-interval lies in the fan over the interval. -/
theorem fan_sub (hκ : 0 < kap p q b1 b2 e1 e2) (hne : kap p q b1 b2 e1 e2 ≠ 0) {u0 u1 x y : ℝ}
    (h01 : u0 < u1) (hxy : x ≠ y) (hx0 : u0 ≤ x) (hx1 : x ≤ u1) (hy0 : u0 ≤ y) (hy1 : y ≤ u1) :
    (fanTri p q b1 b2 e1 e2 hne hxy).carrier ⊆ (fanTri p q b1 b2 e1 e2 hne (ne_of_lt h01)).carrier :=
  convexHull_min (Set.range_subset_iff.mpr (fun k => by
    rcases htri k with rfl | rfl | rfl
    · exact fan_memP hκ h01 hne
    · exact fan_memB hκ h01 hne hx0 hx1
    · exact fan_memB hκ h01 hne hy0 hy1)) (convex_convexHull ℝ _)

theorem fan_lineF_ne (hne : kap p q b1 b2 e1 e2 ≠ 0) (m : ℝ) :
    (lineF p q (b1 + m * e1) (b2 + m * e2)).linear ≠ 0 := by
  unfold lineF
  refine coordFun_linear_ne_zero _ ?_
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  apply hne
  unfold kap
  have h1' : b2 + m * e2 - q = 0 := by linarith
  have h2' : b1 + m * e1 - p = 0 := h2
  have hb1 : b1 - p = -(m * e1) := by linarith
  have hb2 : b2 - q = -(m * e2) := by linarith
  rw [hb1, hb2]; ring

theorem fan_lineF_val (z m : ℝ) :
    lineF p q (b1 + m * e1) (b2 + m * e2) (mkPt (b1 + z * e1) (b2 + z * e2)) = (z - m) * kap p q b1 b2 e1 e2 := by
  rw [lineF_apply]; unfold kap; ring

theorem fan_lineF_P (m : ℝ) :
    lineF p q (b1 + m * e1) (b2 + m * e2) (mkPt p q) = 0 := by
  rw [lineF_apply]; ring

/-- Fans over intervals separated at `m` have disjoint interiors. -/
theorem fan_disj (hκ : 0 < kap p q b1 b2 e1 e2) (hne : kap p q b1 b2 e1 e2 ≠ 0) {x y x' y' m : ℝ}
    (hxy : x ≠ y) (hxy' : x' ≠ y') (hx : x ≤ m) (hy : y ≤ m) (hx' : m ≤ x') (hy' : m ≤ y') :
    Disjoint (interior (fanTri p q b1 b2 e1 e2 hne hxy).carrier)
      (interior (fanTri p q b1 b2 e1 e2 hne hxy').carrier) := by
  refine sep_tri (lineF p q (b1 + m * e1) (b2 + m * e2)) (fan_lineF_ne hne m) 0 ?_ ?_
  · intro k
    rcases htri k with rfl | rfl | rfl
    · show lineF _ _ _ _ (mkPt p q) ≤ 0
      rw [fan_lineF_P]
    · show lineF _ _ _ _ (mkPt (b1 + x * e1) (b2 + x * e2)) ≤ 0
      rw [fan_lineF_val]; exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hκ.le
    · show lineF _ _ _ _ (mkPt (b1 + y * e1) (b2 + y * e2)) ≤ 0
      rw [fan_lineF_val]; exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hκ.le
  · intro k
    rcases htri k with rfl | rfl | rfl
    · show 0 ≤ lineF _ _ _ _ (mkPt p q)
      rw [fan_lineF_P]
    · show 0 ≤ lineF _ _ _ _ (mkPt (b1 + x' * e1) (b2 + x' * e2))
      rw [fan_lineF_val]; exact mul_nonneg (by linarith) hκ.le
    · show 0 ≤ lineF _ _ _ _ (mkPt (b1 + y' * e1) (b2 + y' * e2))
      rw [fan_lineF_val]; exact mul_nonneg (by linarith) hκ.le

theorem fan_absdet (hκ : 0 < kap p q b1 b2 e1 e2) (hne : kap p q b1 b2 e1 e2 ≠ 0) {x y : ℝ} (hxy : x ≠ y) :
    |Erdos634.AreaDet.detTri (fanTri p q b1 b2 e1 e2 hne hxy)| = |y - x| * kap p q b1 b2 e1 e2 := by
  unfold fanTri
  rw [detTri_mkTri, fan_det, abs_mul, abs_of_pos hκ]

/-- Two consecutive fans cover the fan over the union interval. -/
theorem fan_cover2 (hκ : 0 < kap p q b1 b2 e1 e2) (hne : kap p q b1 b2 e1 e2 ≠ 0) {u0 u1 u2 : ℝ}
    (h01 : u0 < u1) (h12 : u1 < u2) :
    (fanTri p q b1 b2 e1 e2 hne (ne_of_lt h01)).carrier ∪ (fanTri p q b1 b2 e1 e2 hne (ne_of_lt h12)).carrier
      = (fanTri p q b1 b2 e1 e2 hne (ne_of_lt (h01.trans h12))).carrier := by
  have h := covers_of_volume_tri (fanTri p q b1 b2 e1 e2 hne (ne_of_lt (h01.trans h12)))
    (![fanTri p q b1 b2 e1 e2 hne (ne_of_lt h01), fanTri p q b1 b2 e1 e2 hne (ne_of_lt h12)] : Fin 2 → Tri)
    (by
      intro i; fin_cases i
      · exact fan_sub hκ hne (h01.trans h12) (ne_of_lt h01) (by linarith) (by linarith) (by linarith) (by linarith)
      · exact fan_sub hκ hne (h01.trans h12) (ne_of_lt h12) (by linarith) (by linarith) (by linarith) (by linarith))
    (by
      intro i j hij
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact fan_disj hκ hne (m := u1) (ne_of_lt h01) (ne_of_lt h12) (by linarith) (le_refl _) (le_refl _) (by linarith)
      · exact (fan_disj hκ hne (m := u1) (ne_of_lt h01) (ne_of_lt h12) (by linarith) (le_refl _) (le_refl _) (by linarith)).symm
      · exact absurd rfl hij)
    (Erdos634.AreaDet.area_identity_of_det _ _ (by
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [fan_absdet hκ hne, fan_absdet hκ hne, fan_absdet hκ hne,
        abs_of_pos (by linarith : (0 : ℝ) < u1 - u0), abs_of_pos (by linarith : (0 : ℝ) < u2 - u1),
        abs_of_pos (by linarith : (0 : ℝ) < u2 - u0)]
      ring))
  rw [← h]
  ext z; simp [Fin.exists_fin_succ]

end fan

end Erdos634.LaczL27
