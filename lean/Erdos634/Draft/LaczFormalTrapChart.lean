import Erdos634.Draft.LaczFormalL37Plane

/-!
# Laczkovich Lemma 2.2 (ii), (iii): a trapezoid GIVEN BY ITS FOUR VERTICES (vertex form)

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Lemma 2.2), Beeson, Beeson-Zhang, Zhang.

`LaczFormalL37Plane` proves Lemma 2.2 (ii), (iii) for the plane set `trapPlane A w d τ` (data form).  The missing conversion
(recorded there as a gap): a trapezoid given by four vertices `A, B, C, D` (`AB ∥ DC`, `AB` the base) is `trapPlane A (B-A) (D-A) τ`
with `C - D = τ • (B - A)`.

* `trapPlane_eq_hull`: for `τ > 0` the convex hull of `{A, B, C, D}` with `C - D = τ • (B - A)` equals `trapPlane A (B-A) (D-A) τ`
  (no independence of `B - A`, `D - A` is needed for this set identity);
* `lemma22_ii_vert`, `lemma22_iii_vert`: the lemmas for the trapezoid given by its four vertices, hypotheses `‖B - A‖ = W`,
  `‖D - A‖ = D` rational, `∠ B A D = vang Δ 1` (the base angle at `A`), `C - D = τ (B - A)` with the forced `τ`.
The angles at the other three vertices are consequences of these data (parallelism and the lengths), so they need not be hypotheses.
-/

namespace Erdos634.LaczTrapChart

open Erdos634 Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL24 Erdos634.LaczL35 Erdos634.LaczL37
  EuclideanGeometry

theorem trapPlane_convex (A w d : Plane) (τ : ℝ) : Convex ℝ (trapPlane A w d τ) := by
  rintro x ⟨s, t, ht0, ht1, hs0, hs1, rfl⟩ y ⟨s', t', ht0', ht1', hs0', hs1', rfl⟩ a b ha hb hab
  refine ⟨a * s + b * s', a * t + b * t', by positivity, ?_, by positivity, ?_, ?_⟩
  · nlinarith
  · have h1 := mul_le_mul_of_nonneg_left hs1 ha
    have h2 := mul_le_mul_of_nonneg_left hs1' hb
    nlinarith
  · have hb' : b = 1 - a := by linarith
    subst hb'
    module

/-- **Vertex form of the trapezoid.**  `AB ∥ DC` is `C - D = τ (B - A)`, `τ > 0`. -/
theorem trapPlane_eq_hull (A B C D : Plane) (τ : ℝ) (hτ : 0 < τ) (hC : C - D = τ • (B - A)) :
    trapPlane A (B - A) (D - A) τ = convexHull ℝ {A, B, C, D} := by
  have hCe : C = A + τ • (B - A) + (D - A) := by
    have : C = D + τ • (B - A) := by rw [← hC]; abel
    rw [this]; abel
  apply Set.Subset.antisymm
  · rintro x ⟨s, t, ht0, ht1, hs0, hs1, rfl⟩
    set H := convexHull ℝ ({A, B, C, D} : Set Plane) with hH
    have hAm : A ∈ H := subset_convexHull ℝ _ (by simp)
    have hBm : B ∈ H := subset_convexHull ℝ _ (by simp)
    have hCm : C ∈ H := subset_convexHull ℝ _ (by simp)
    have hDm : D ∈ H := subset_convexHull ℝ _ (by simp)
    have hconv : Convex ℝ H := convex_convexHull ℝ _
    have hpos : 0 < 1 + (τ - 1) * t := by
      rcases le_total τ 1 with h | h
      · nlinarith [mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr ht1)]
      · nlinarith
    set L : ℝ := 1 + (τ - 1) * t with hL
    set l : ℝ := s / L with hl
    have hl0 : 0 ≤ l := div_nonneg hs0 hpos.le
    have hl1 : l ≤ 1 := (div_le_one hpos).mpr hs1
    have hP1 : (1 - t) • A + t • D ∈ H := hconv hAm hDm (by linarith) ht0 (by ring)
    have hP2 : (1 - t) • B + t • C ∈ H := hconv hBm hCm (by linarith) ht0 (by ring)
    have hx := hconv hP1 hP2 (show 0 ≤ 1 - l by linarith) hl0 (by ring)
    convert hx using 1
    have hs : s = l * L := by rw [hl]; field_simp
    rw [hCe, hs]
    simp only [smul_add, smul_sub, smul_smul, hL, add_smul, sub_smul, one_smul]
    module
  · apply convexHull_min _ (trapPlane_convex A _ _ τ)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨0, 0, le_rfl, zero_le_one, le_rfl, by linarith, by simp⟩
    · exact ⟨1, 0, le_rfl, zero_le_one, zero_le_one, by linarith, by simp⟩
    · exact ⟨τ, 1, zero_le_one, le_rfl, hτ.le, by linarith, by rw [hCe]; simp⟩
    · exact ⟨0, 1, zero_le_one, le_rfl, le_rfl, by linarith, by simp⟩

/-- The base angle at `A` of the vertex-form trapezoid is the angle of the two sides `AB`, `AD`. -/
theorem angle_vert (A B D : Plane) : ∠ B A D = InnerProductGeometry.angle (B - A) (D - A) := rfl

/-- **Lemma 2.2 (ii), vertex form.**  Trapezoid `ABCD`, `AB ∥ DC`, with base `‖AB‖ = W`, leg `‖AD‖ = D` rational, base angle
`∠ B A D = ` the angle of `Δ` at vertex 1, and `C - D = τ (B - A)` with `τ = tTau a b c W D > 0`. -/
theorem lemma22_ii_vert (R : RTri) (A B C D : Plane) (W Dd : ℚ) (hW : 0 < W) (hD : 0 < Dd)
    (hwn : ‖B - A‖ = W) (hdn : ‖D - A‖ = Dd) (hang : ∠ B A D = vang R.Δ 1)
    (τq : ℚ) (hτ : τq = tTau R.a R.b R.c W Dd) (hτpos : 0 < τq) (hC : C - D = (τq : ℝ) • (B - A)) :
    RatSimDiss R.Δ (convexHull ℝ {A, B, C, D}) := by
  rw [← trapPlane_eq_hull A B C D (τq : ℝ) (by exact_mod_cast hτpos) hC]
  exact lemma22_ii_plane R A (B - A) (D - A) W Dd hW hD hwn hdn hang τq hτ hτpos

/-- **Lemma 2.2 (iii), vertex form** (isosceles trapezoid, top ratio `tTauI a b c W D > 0`). -/
theorem lemma22_iii_vert (R : RTri) (A B C D : Plane) (W Dd : ℚ) (hW : 0 < W) (hD : 0 < Dd)
    (hwn : ‖B - A‖ = W) (hdn : ‖D - A‖ = Dd) (hang : ∠ B A D = vang R.Δ 1)
    (hτpos : 0 < tTauI R.a R.b R.c W Dd) (hC : C - D = ((tTauI R.a R.b R.c W Dd : ℚ) : ℝ) • (B - A)) :
    RatSimDiss R.Δ (convexHull ℝ {A, B, C, D}) := by
  rw [← trapPlane_eq_hull A B C D _ (by exact_mod_cast hτpos) hC]
  exact lemma22_iii_plane R A (B - A) (D - A) W Dd hW hD hwn hdn hang hτpos

#print axioms trapPlane_eq_hull
#print axioms lemma22_ii_vert
#print axioms lemma22_iii_vert

end Erdos634.LaczTrapChart
