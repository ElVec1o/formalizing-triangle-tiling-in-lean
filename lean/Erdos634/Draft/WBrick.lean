-- Draft/WBrick.lean — step (a) of the 7m² plan: in the W-frame, the parallelogram
-- Φ[0,A]×[0,B] is two triangles cut along its diagonal.  Generic in (A,B); the (3,2) and (2,3)
-- bricks (tile (16,24,32), diagonal 32) are the instances.  UNAUDITED.  Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.Draft.WFrame
import Erdos634.SssCongruent
import Erdos634.Draft.SumTwoSquares

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (s15 s15_pos s15_sq Sh Tset Rect)

namespace Erdos634.Draft.WBrick
open Erdos634.Draft.WFrame Erdos634.Draft.RegionTiling

/-- Separation by a line `a s + b t = c`, `a ≠ 0` (shear to a vertical line). -/
noncomputable def shearH (a b : ℝ) (ha : a ≠ 0) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun p := (a * p.1 + b * p.2, p.2)
  invFun q := ((q.1 - b * q.2) / a, q.2)
  left_inv p := by ext <;> simp <;> field_simp <;> ring
  right_inv q := by ext <;> simp; field_simp; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem interior_disj_lin {A B : Set (ℝ × ℝ)} (a b c : ℝ) (ha : a ≠ 0)
    (hA : ∀ p ∈ A, a * p.1 + b * p.2 ≤ c) (hB : ∀ p ∈ B, c ≤ a * p.1 + b * p.2) :
    Disjoint (interior A) (interior B) := by
  have h := Erdos634.Draft.CollarParam.interior_disj_fst (A := shearH a b ha '' A)
    (B := shearH a b ha '' B) c (by rintro _ ⟨p, hp, rfl⟩; exact hA p hp)
    (by rintro _ ⟨p, hp, rfl⟩; exact hB p hp)
  rw [← (shearH a b ha).image_interior, ← (shearH a b ha).image_interior] at h
  exact (Set.disjoint_image_iff (shearH a b ha).injective).mp h

/-- Squared length of `Φ(Δs,Δt)`. -/
theorem sq_Phi (a b : ℝ × ℝ) :
    dist (Phi a) (Phi b) ^ 2
      = 64 * (a.1 - b.1) ^ 2 + 32 * ((a.1 - b.1) * (a.2 - b.2)) + 64 * (a.2 - b.2) ^ 2 := by
  have e : ∀ c : ℝ × ℝ, Phi c = mkPt (8 * c.1 + 2 * c.2) (2 * s15 * c.2) := fun c => by
    ext i; fin_cases i <;> simp [Phi_apply0, Phi_apply1]
  rw [e a, e b, dist_sq_mkPt]
  have := s15_sq
  nlinarith [this]

theorem det_Phi (a b c : ℝ × ℝ) :
    det3 (Phi a 0) (Phi a 1) (Phi b 0) (Phi b 1) (Phi c 0) (Phi c 1)
      = 16 * s15 * ((b.1 - a.1) * (c.2 - a.2) - (c.1 - a.1) * (b.2 - a.2)) := by
  unfold det3; simp only [Phi_apply0, Phi_apply1]; ring

/-- The triangle with skew-coordinate vertices `a b c`. -/
noncomputable def triC (a b c : ℝ × ℝ)
    (h : (b.1 - a.1) * (c.2 - a.2) - (c.1 - a.1) * (b.2 - a.2) ≠ 0) : Tri :=
  mkTri (Phi a 0) (Phi a 1) (Phi b 0) (Phi b 1) (Phi c 0) (Phi c 1) (by
    rw [det_Phi]; exact mul_ne_zero (mul_ne_zero (by norm_num) s15_pos.ne') h)

theorem mkPt_Phi (a : ℝ × ℝ) : mkPt (Phi a 0) (Phi a 1) = Phi a := by
  ext i; fin_cases i <;> simp

theorem triC_pts (a b c : ℝ × ℝ) (h) : (triC a b c h).pts = ![Phi a, Phi b, Phi c] := by
  simp only [triC, mkTri_pts, mkPt_Phi]

noncomputable def PhiL : (ℝ × ℝ) →ₗ[ℝ] Plane :=
  (LinearMap.fst ℝ ℝ ℝ).smulRight g1 + (LinearMap.snd ℝ ℝ ℝ).smulRight g2

theorem PhiL_eq (p : ℝ × ℝ) : PhiL p = Phi p := rfl

theorem carrier_triC (a b c : ℝ × ℝ) (h) :
    (triC a b c h).carrier = Phi '' convexHull ℝ {a, b, c} := by
  have : Set.range (triC a b c h).pts = Phi '' {a, b, c} := by
    rw [triC_pts]
    ext x
    simp only [Set.mem_range, Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, rfl⟩; fin_cases k <;> simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  rw [Tri.carrier, this]
  have := PhiL.image_convexHull ({a, b, c} : Set (ℝ × ℝ))
  simp only [PhiL_eq] at this
  rw [← this]

/-- Lower triangle of the coordinate rectangle: `(0,0),(A,0),(A,B)`. -/
def LT (A B : ℝ) : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ A ∧ 0 ≤ p.2 ∧ p.2 * A ≤ p.1 * B}
/-- Upper triangle: `(0,0),(0,B),(A,B)`. -/
def UT (A B : ℝ) : Set (ℝ × ℝ) := {p | 0 ≤ p.2 ∧ p.2 ≤ B ∧ 0 ≤ p.1 ∧ p.1 * B ≤ p.2 * A}

theorem LT_convex (A B : ℝ) (hA : 0 < A) (hB : 0 < B) : Convex ℝ (LT A B) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨x1, x2, x3, x4⟩ := hx
  obtain ⟨y1, y2, y3, y4⟩ := hy
  simp only [LT, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  refine ⟨by positivity, ?_, by positivity, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left x2 ha, mul_le_mul_of_nonneg_left y2 hb]
  · nlinarith [mul_le_mul_of_nonneg_left x4 ha, mul_le_mul_of_nonneg_left y4 hb]

theorem UT_convex (A B : ℝ) (hA : 0 < A) (hB : 0 < B) : Convex ℝ (UT A B) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨x1, x2, x3, x4⟩ := hx
  obtain ⟨y1, y2, y3, y4⟩ := hy
  simp only [UT, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  refine ⟨by positivity, ?_, by positivity, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left x2 ha, mul_le_mul_of_nonneg_left y2 hb]
  · nlinarith [mul_le_mul_of_nonneg_left x4 ha, mul_le_mul_of_nonneg_left y4 hb]

theorem hull_LT (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    convexHull ℝ {((0 : ℝ), (0 : ℝ)), (A, 0), (A, B)} = LT A B := by
  apply Set.Subset.antisymm
  · refine convexHull_min ?_ (LT_convex A B hA hB)
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨le_refl _, hA.le, le_refl _, by simp⟩
    · exact ⟨hA.le, le_refl _, le_refl _, by simpa using mul_nonneg hA.le hB.le⟩
    · exact ⟨hA.le, le_refl _, hB.le, by show B * A ≤ A * B; linarith [mul_comm A B]⟩
  · intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hp
    have hc := convex_convexHull ℝ ({((0 : ℝ), (0 : ℝ)), (A, 0), (A, B)} : Set (ℝ × ℝ))
    have := hc.sum_mem (t := (Finset.univ : Finset (Fin 3)))
      (w := ![1 - p.1 / A, p.1 / A - p.2 / B, p.2 / B])
      (z := ![((0 : ℝ), (0 : ℝ)), (A, 0), (A, B)])
      (by
        intro i _
        fin_cases i <;> simp
        · rw [div_le_one hA]; exact h2
        · rw [div_le_div_iff₀ hB hA]; linarith
        · exact div_nonneg h3 hB.le)
      (by simp [Fin.sum_univ_three] <;> ring)
      (by intro i _; fin_cases i <;> exact subset_convexHull ℝ _ (by simp))
    convert this using 1
    ext <;> simp [Fin.sum_univ_three] <;> field_simp <;> ring

theorem hull_UT (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    convexHull ℝ {((0 : ℝ), (0 : ℝ)), (0, B), (A, B)} = UT A B := by
  apply Set.Subset.antisymm
  · refine convexHull_min ?_ (UT_convex A B hA hB)
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨le_refl _, hB.le, le_refl _, by simp⟩
    · exact ⟨hB.le, le_refl _, le_refl _, by simpa using mul_nonneg hB.le hA.le⟩
    · exact ⟨hB.le, le_refl _, hA.le, by show A * B ≤ B * A; linarith [mul_comm A B]⟩
  · intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hp
    have hc := convex_convexHull ℝ ({((0 : ℝ), (0 : ℝ)), (0, B), (A, B)} : Set (ℝ × ℝ))
    have := hc.sum_mem (t := (Finset.univ : Finset (Fin 3)))
      (w := ![1 - p.2 / B, p.2 / B - p.1 / A, p.1 / A])
      (z := ![((0 : ℝ), (0 : ℝ)), (0, B), (A, B)])
      (by
        intro i _
        fin_cases i <;> simp
        · rw [div_le_one hB]; exact h2
        · rw [div_le_div_iff₀ hA hB]; linarith
        · exact div_nonneg h3 hA.le)
      (by simp [Fin.sum_univ_three] <;> ring)
      (by intro i _; fin_cases i <;> exact subset_convexHull ℝ _ (by simp))
    convert this using 1
    ext <;> simp [Fin.sum_univ_three] <;> field_simp <;> ring

theorem LT_union_UT (A B : ℝ) (hA : 0 < A) (hB : 0 < B) : LT A B ∪ UT A B = Rect 0 A 0 B := by
  ext p
  simp only [LT, UT, Rect, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (⟨a, b, c, d⟩ | ⟨a, b, c, d⟩)
    · refine ⟨a, b, c, ?_⟩
      by_contra hh; push Not at hh
      nlinarith
    · refine ⟨c, ?_, a, b⟩
      by_contra hh; push Not at hh
      nlinarith
  · rintro ⟨a, b, c, d⟩
    rcases le_total (p.2 * A) (p.1 * B) with h | h
    · exact Or.inl ⟨a, b, c, h⟩
    · exact Or.inr ⟨c, d, a, h⟩

noncomputable def brickL (A B : ℝ) (hA : 0 < A) (hB : 0 < B) : Tri :=
  triC (0, 0) (A, 0) (A, B) (by intro h; nlinarith [mul_pos hA hB])

noncomputable def brickU (A B : ℝ) (hA : 0 < A) (hB : 0 < B) : Tri :=
  triC (0, 0) (0, B) (A, B) (by intro h; nlinarith [mul_pos hA hB])

theorem carrier_brickL (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    (brickL A B hA hB).carrier = Phi '' LT A B := by
  rw [brickL, carrier_triC, hull_LT A B hA hB]

theorem carrier_brickU (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    (brickU A B hA hB).carrier = Phi '' UT A B := by
  rw [brickU, carrier_triC, hull_UT A B hA hB]

theorem disj_LU (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    Disjoint (interior (Phi '' LT A B)) (interior (Phi '' UT A B)) :=
  disjoint_image (interior_disj_lin (-B) A 0 (by linarith)
    (by rintro p ⟨_, _, _, h⟩; linarith) (by rintro p ⟨_, _, _, h⟩; linarith))

/-- **Step (a):** the coordinate parallelogram `Φ[0,A]×[0,B]` is tiled by its two diagonal halves,
given both are congruent to the model. -/
noncomputable def brick_rt (A B : ℝ) (hA : 0 < A) (hB : 0 < B) (M : Tri)
    (c1 : (brickL A B hA hB).Congruent M) (c2 : (brickU A B hA hB).Congruent M) :
    RTiling (Phi '' Rect 0 A 0 B) M 2 where
  tile := ![brickL A B hA hB, brickU A B hA hB]
  covers := by
    rw [← LT_union_UT A B hA hB, Set.image_union]
    ext x
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · left; simpa [carrier_brickL] using hi
      · right; simpa [carrier_brickU] using hi
    · rintro (h | h)
      · exact ⟨0, by simpa [carrier_brickL] using h⟩
      · exact ⟨1, by simpa [carrier_brickU] using h⟩
  disj := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simpa [carrier_brickL, carrier_brickU] using disj_LU A B hA hB
    · simpa [carrier_brickL, carrier_brickU] using (disj_LU A B hA hB).symm
    · exact absurd rfl hij
  cong := by
    intro i; fin_cases i
    · exact c1
    · exact c2

/-- The model tile: sides `(24, 16, 32)` = `8·(3,2,4)`; the (3,2) brick's lower half. -/
noncomputable def MW : Tri := brickL 3 2 (by norm_num) (by norm_num)

theorem dPhi (a b c d : ℝ × ℝ) (h : dist (Phi a) (Phi b) ^ 2 = dist (Phi c) (Phi d) ^ 2) :
    dist (Phi a) (Phi b) = dist (Phi c) (Phi d) :=
  Erdos634.Draft.SumTwoSquares.eqsq dist_nonneg dist_nonneg h

theorem cong_U32 : (brickU 3 2 (by norm_num) (by norm_num)).Congruent MW := by
  refine ((brickU 3 2 (by norm_num) (by norm_num)).congruent_relabel (Equiv.swap (0 : Fin 3) 2)).trans ?_
  refine Erdos634.SssCongruent.congruent_of_dist_three ?_ ?_ ?_ <;>
    simp only [Tri.relabel, MW, brickL, brickU, triC_pts] <;>
    (refine dPhi _ _ _ _ ?_; rw [sq_Phi, sq_Phi]; norm_num)

theorem cong_L23 : (brickL 2 3 (by norm_num) (by norm_num)).Congruent MW := by
  refine ((brickL 2 3 (by norm_num) (by norm_num)).congruent_relabel (Equiv.swap (0 : Fin 3) 2)).trans ?_
  refine Erdos634.SssCongruent.congruent_of_dist_three ?_ ?_ ?_ <;>
    simp only [Tri.relabel, MW, brickL, brickU, triC_pts] <;>
    (refine dPhi _ _ _ _ ?_; rw [sq_Phi, sq_Phi]; norm_num)

theorem cong_U23 : (brickU 2 3 (by norm_num) (by norm_num)).Congruent MW := by
  refine Erdos634.SssCongruent.congruent_of_dist_three ?_ ?_ ?_ <;>
    simp only [MW, brickL, brickU, triC_pts] <;>
    (refine dPhi _ _ _ _ ?_; rw [sq_Phi, sq_Phi]; norm_num)

noncomputable def brick32 : RTiling (Phi '' Rect 0 3 0 2) MW 2 :=
  brick_rt 3 2 (by norm_num) (by norm_num) MW (Tri.Congruent.refl MW) cong_U32

noncomputable def brick23 : RTiling (Phi '' Rect 0 2 0 3) MW 2 :=
  brick_rt 2 3 (by norm_num) (by norm_num) MW cong_L23 cong_U23

#print axioms Erdos634.Draft.WBrick.brick32
#print axioms Erdos634.Draft.WBrick.brick23

end Erdos634.Draft.WBrick
