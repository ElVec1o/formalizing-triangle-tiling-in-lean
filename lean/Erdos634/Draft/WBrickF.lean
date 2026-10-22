-- Draft/WBrickF.lean — L2 of (private working notes, not included) §3: general-f W-brick.  In the frame Phi_f, the
-- parallelogram Phi_f[0,A]x[0,B] is two triangles cut along its diagonal; the bricks (f²-1, f) and
-- (f, f²-1) (diagonal f²) are congruent to the model tile (f, f²-1, f²) by SSS.  Mirrors WBrick.lean
-- with |g|=1 (f=2: model (3,2,4) = (1/8)·(24,16,32)).  UNAUDITED.  Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.Draft.WFrameF
import Erdos634.SssCongruent
import Erdos634.Draft.SumTwoSquares

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Tset Rect)

namespace Erdos634.Draft.WBrickF
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling

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

theorem det_Phi (f : ℝ) (a b c : ℝ × ℝ) :
    det3 (Phi f a 0) (Phi f a 1) (Phi f b 0) (Phi f b 1) (Phi f c 0) (Phi f c 1)
      = (sD f / (2 * f)) * ((b.1 - a.1) * (c.2 - a.2) - (c.1 - a.1) * (b.2 - a.2)) := by
  unfold det3; simp only [Phi_apply0, Phi_apply1]; ring

/-- The triangle with skew-coordinate vertices `a b c`. -/
noncomputable def triC (f : ℝ) (hf : 1 < f) (a b c : ℝ × ℝ)
    (h : (b.1 - a.1) * (c.2 - a.2) - (c.1 - a.1) * (b.2 - a.2) ≠ 0) : Tri :=
  mkTri (Phi f a 0) (Phi f a 1) (Phi f b 0) (Phi f b 1) (Phi f c 0) (Phi f c 1) (by
    rw [det_Phi]; exact mul_ne_zero (div_ne_zero (sD_pos hf).ne' (by positivity)) h)

theorem mkPt_Phi (f : ℝ) (a : ℝ × ℝ) : mkPt (Phi f a 0) (Phi f a 1) = Phi f a := by
  ext i; fin_cases i <;> simp

theorem triC_pts (f : ℝ) (hf : 1 < f) (a b c : ℝ × ℝ) (h) : (triC f hf a b c h).pts = ![Phi f a, Phi f b, Phi f c] := by
  simp only [triC, mkTri_pts, mkPt_Phi]

noncomputable def PhiL (f : ℝ) : (ℝ × ℝ) →ₗ[ℝ] Plane :=
  (LinearMap.fst ℝ ℝ ℝ).smulRight g1 + (LinearMap.snd ℝ ℝ ℝ).smulRight (g2 f)

theorem PhiL_eq (f : ℝ) (p : ℝ × ℝ) : PhiL f p = Phi f p := rfl

theorem carrier_triC (f : ℝ) (hf : 1 < f) (a b c : ℝ × ℝ) (h) :
    (triC f hf a b c h).carrier = Phi f '' convexHull ℝ {a, b, c} := by
  have : Set.range (triC f hf a b c h).pts = Phi f '' {a, b, c} := by
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
  have := (PhiL f).image_convexHull ({a, b, c} : Set (ℝ × ℝ))
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

noncomputable def brickL (f : ℝ) (hf : 1 < f) (A B : ℝ) (hA : 0 < A) (hB : 0 < B) : Tri :=
  triC f hf (0, 0) (A, 0) (A, B) (by intro h; nlinarith [mul_pos hA hB])

noncomputable def brickU (f : ℝ) (hf : 1 < f) (A B : ℝ) (hA : 0 < A) (hB : 0 < B) : Tri :=
  triC f hf (0, 0) (0, B) (A, B) (by intro h; nlinarith [mul_pos hA hB])

theorem carrier_brickL (f : ℝ) (hf : 1 < f) (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    (brickL f hf A B hA hB).carrier = Phi f '' LT A B := by
  rw [brickL, carrier_triC, hull_LT A B hA hB]

theorem carrier_brickU (f : ℝ) (hf : 1 < f) (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    (brickU f hf A B hA hB).carrier = Phi f '' UT A B := by
  rw [brickU, carrier_triC, hull_UT A B hA hB]

theorem disj_LU (f : ℝ) (hf : 1 < f) (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    Disjoint (interior (Phi f '' LT A B)) (interior (Phi f '' UT A B)) :=
  disjoint_image hf (interior_disj_lin (-B) A 0 (by linarith)
    (by rintro p ⟨_, _, _, h⟩; linarith) (by rintro p ⟨_, _, _, h⟩; linarith))

/-- The coordinate parallelogram `Φ_f[0,A]×[0,B]` is tiled by its two diagonal halves,
given both are congruent to the model. -/
noncomputable def brick_rt (f : ℝ) (hf : 1 < f) (A B : ℝ) (hA : 0 < A) (hB : 0 < B) (M : Tri)
    (c1 : (brickL f hf A B hA hB).Congruent M) (c2 : (brickU f hf A B hA hB).Congruent M) :
    RTiling (Phi f '' Rect 0 A 0 B) M 2 where
  tile := ![brickL f hf A B hA hB, brickU f hf A B hA hB]
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
    · simpa [carrier_brickL, carrier_brickU] using disj_LU f hf A B hA hB
    · simpa [carrier_brickL, carrier_brickU] using (disj_LU f hf A B hA hB).symm
    · exact absurd rfl hij
  cong := by
    intro i; fin_cases i
    · exact c1
    · exact c2

/-- Positivity of the brick sides `f²-1` and `f`. -/
theorem hA_pos {f : ℝ} (hf : 1 < f) : 0 < f ^ 2 - 1 := by nlinarith
theorem hf_pos {f : ℝ} (hf : 1 < f) : 0 < f := by linarith

/-- Model tile `(f, f²-1, f²)`: the lower half of the `(f²-1, f)` brick. -/
noncomputable def MF (f : ℝ) (hf : 1 < f) : Tri := brickL f hf (f ^ 2 - 1) f (hA_pos hf) (hf_pos hf)

theorem dPhi {f : ℝ} (a b c d : ℝ × ℝ)
    (h : dist (Phi f a) (Phi f b) ^ 2 = dist (Phi f c) (Phi f d) ^ 2) :
    dist (Phi f a) (Phi f b) = dist (Phi f c) (Phi f d) :=
  Erdos634.Draft.SumTwoSquares.eqsq dist_nonneg dist_nonneg h

/-- Diagonal identity: `(f²-1)² + f² + (f²-1) f / f = f⁴`; i.e. `a²+b²+ab/f = f⁴` at `(a,b)=(f²-1,f)`. -/
theorem diag_id {f : ℝ} (hf : 1 < f) :
    (f ^ 2 - 1) ^ 2 + f ^ 2 + (f ^ 2 - 1) * f / f = (f ^ 2) ^ 2 := by
  have : f ≠ 0 := (hf_pos hf).ne'
  field_simp; ring

theorem cong_U {f : ℝ} (hf : 1 < f) :
    (brickU f hf (f ^ 2 - 1) f (hA_pos hf) (hf_pos hf)).Congruent (MF f hf) := by
  have h0 : f ≠ 0 := (hf_pos hf).ne'
  refine ((brickU f hf _ _ (hA_pos hf) (hf_pos hf)).congruent_relabel (Equiv.swap (0 : Fin 3) 2)).trans ?_
  refine Erdos634.SssCongruent.congruent_of_dist_three ?_ ?_ ?_ <;>
    simp only [Tri.relabel, MF, brickL, brickU, triC_pts] <;>
    (refine dPhi _ _ _ _ ?_; rw [sq_Phi hf, sq_Phi hf]; field_simp; ring)

theorem cong_L' {f : ℝ} (hf : 1 < f) :
    (brickL f hf f (f ^ 2 - 1) (hf_pos hf) (hA_pos hf)).Congruent (MF f hf) := by
  have h0 : f ≠ 0 := (hf_pos hf).ne'
  refine ((brickL f hf _ _ (hf_pos hf) (hA_pos hf)).congruent_relabel (Equiv.swap (0 : Fin 3) 2)).trans ?_
  refine Erdos634.SssCongruent.congruent_of_dist_three ?_ ?_ ?_ <;>
    simp only [Tri.relabel, MF, brickL, brickU, triC_pts] <;>
    (refine dPhi _ _ _ _ ?_; rw [sq_Phi hf, sq_Phi hf]; field_simp; ring)

theorem cong_U' {f : ℝ} (hf : 1 < f) :
    (brickU f hf f (f ^ 2 - 1) (hf_pos hf) (hA_pos hf)).Congruent (MF f hf) := by
  have h0 : f ≠ 0 := (hf_pos hf).ne'
  refine Erdos634.SssCongruent.congruent_of_dist_three ?_ ?_ ?_ <;>
    simp only [MF, brickL, brickU, triC_pts] <;>
    (refine dPhi _ _ _ _ ?_; rw [sq_Phi hf, sq_Phi hf]; field_simp; ring)

/-- The `(f²-1) × f` brick (old `brick32` at `f=2`). -/
noncomputable def brickA (f : ℝ) (hf : 1 < f) : RTiling (Phi f '' Rect 0 (f ^ 2 - 1) 0 f) (MF f hf) 2 :=
  brick_rt f hf _ _ (hA_pos hf) (hf_pos hf) _ (Tri.Congruent.refl _) (cong_U hf)

/-- The `f × (f²-1)` brick (old `brick23` at `f=2`). -/
noncomputable def brickB (f : ℝ) (hf : 1 < f) : RTiling (Phi f '' Rect 0 f 0 (f ^ 2 - 1)) (MF f hf) 2 :=
  brick_rt f hf _ _ (hf_pos hf) (hA_pos hf) _ (cong_L' hf) (cong_U' hf)

/-- f = 2 sanity: the model is the `(3,2)` brick and `brickA 2` tiles `Φ_2[0,3]×[0,2]`. -/
noncomputable example : RTiling (Phi 2 '' Rect 0 (2 ^ 2 - 1) 0 2) (MF 2 (by norm_num)) 2 := brickA 2 (by norm_num)

end Erdos634.Draft.WBrickF

#print axioms Erdos634.Draft.WBrickF.brickA
#print axioms Erdos634.Draft.WBrickF.brickB
