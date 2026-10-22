import Erdos634.Draft.LaczFormalL35Print
import Erdos634.Draft.LaczFormalL22Iso
import Erdos634.Draft.LaczFormalL24Main
import Erdos634.Draft.LaczFormalL24Wit

/-!
# Laczkovich Lemma 2.2 (ii), (iii) in ACTUAL-PLANE form (rational trapezoids with prescribed angle)

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Lemma 2.2), Beeson, Beeson-Zhang, Zhang.

`lemma22_i` (`LaczFormalL22Par`) is already in actual-plane form.  Here (ii) and (iii) are stated for the plane
trapezoid `trapPlane A w d τ = {A + s w + t d : 0 ≤ t ≤ 1, 0 ≤ s ≤ 1 + (τ-1) t}` (vertices `A, A+w, A+τw+d, A+d`), for ARBITRARY
`A`, `w`, `d` with rational lengths `‖w‖ = W`, `‖d‖ = D` and `∠(w,d)` the angle `β` of the tile at vertex 1: the trapezoid with
base `W`, top `τ W`, base angle `β`.  The top ratio `τ` is the one forced by the tile: `tTau` (case (ii): angles
`(β, α+β, γ, α+γ)`, the trapezoid dissected through the strip construction) or `tTauI` (case (iii), isosceles trapezoid with
angles `(β, β, α+γ, α+γ)`).  The conclusion is `RatSimDiss R.Δ`: a union of finitely many rational triangles similar to `Δ`
with disjoint interiors.
Gap (not formalized): a trapezoid GIVEN BY ITS VERTICES AND ANGLES is not converted here into the `(A, w, d, τ)` data
(the vertex-and-angle form needs the extraction of `w, d, τ` from the four vertices); the data form IS a general plane trapezoid.
-/

namespace Erdos634.LaczL37

open Erdos634 Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL24 Erdos634.LaczL35 EuclideanGeometry

/-- The plane trapezoid `{A + s w + t d : 0 ≤ t ≤ 1, 0 ≤ s ≤ 1 + (τ-1) t}`. -/
def trapPlane (A w d : Plane) (τ : ℝ) : Set Plane :=
  {x | ∃ s t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ 0 ≤ s ∧ s ≤ 1 + (τ - 1) * t ∧ x = A + s • w + t • d}

theorem chart_image_trap (A w d : Plane) (h : w 0 * d 1 - w 1 * d 0 ≠ 0) (τ : ℝ) :
    chartEquiv A w d h '' trapSet τ = trapPlane A w d τ := by
  ext x
  constructor
  · rintro ⟨z, ⟨h1, h2, h3, h4⟩, rfl⟩
    exact ⟨z 0, z 1, h1, h2, h3, h4, chartEquiv_apply A w d h z⟩
  · rintro ⟨s, t, h1, h2, h3, h4, rfl⟩
    refine ⟨mkPt s t, ⟨by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4⟩, ?_⟩
    rw [chartEquiv_apply]; simp

/-- Gram data from the angle at vertex 1 of the tile. -/
theorem gram_of_angle1 (R : RTri) (w d : Plane) (W Dd : ℚ) (hW : 0 < W) (hD : 0 < Dd)
    (hwn : ‖w‖ = W) (hdn : ‖d‖ = Dd) (hang : InnerProductGeometry.angle w d = vang R.Δ 1) :
    inner ℝ w d = (W : ℝ) * Dd * (R.cos1 : ℝ) := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hD' : (0 : ℝ) < Dd := by exact_mod_cast hD
  have hcos : Real.cos (InnerProductGeometry.angle w d) = inner ℝ w d / (W * Dd) := by
    rw [InnerProductGeometry.cos_angle, hwn, hdn]
  rw [hang, RTri.cos_vang1] at hcos
  have hc1 : (R.cos1 : ℝ) = ((R.a : ℝ) ^ 2 + R.c ^ 2 - R.b ^ 2) / (2 * R.a * R.c) := by
    have ha : (R.a : ℝ) ≠ 0 := by exact_mod_cast R.pa.ne'
    have hc : (R.c : ℝ) ≠ 0 := by exact_mod_cast R.pc.ne'
    simp only [RTri.cos1]; push_cast; ring
  rw [hc1, hcos]
  field_simp

theorem hdet_of_angle1 (R : RTri) (w d : Plane) (W Dd : ℚ) (hW : 0 < W) (hD : 0 < Dd)
    (hwn : ‖w‖ = W) (hdn : ‖d‖ = Dd) (hang : InnerProductGeometry.angle w d = vang R.Δ 1) :
    w 0 * d 1 - w 1 * d 0 ≠ 0 := by
  have hwd := gram_of_angle1 R w d W Dd hW hD hwn hdn hang
  have hw : inner ℝ w w = (W : ℝ) ^ 2 := by rw [real_inner_self_eq_norm_sq, hwn]
  have hd : inner ℝ d d = (Dd : ℝ) ^ 2 := by rw [real_inner_self_eq_norm_sq, hdn]
  intro h0
  have ewd : inner ℝ w d = w 0 * d 0 + w 1 * d 1 := by
    simp [PiLp.inner_apply, Fin.sum_univ_two]; ring
  have eww : inner ℝ w w = w 0 * w 0 + w 1 * w 1 := by
    rw [PiLp.inner_apply, Fin.sum_univ_two]; simp; ring
  have edd : inner ℝ d d = d 0 * d 0 + d 1 * d 1 := by
    rw [PiLp.inner_apply, Fin.sum_univ_two]; simp; ring
  have hlag : (w 0 * d 1 - w 1 * d 0) ^ 2 + (inner ℝ w d) ^ 2 = inner ℝ w w * inner ℝ d d := by
    rw [ewd, eww, edd]; ring
  rw [h0, hwd, hw, hd] at hlag
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hD' : (0 : ℝ) < Dd := by exact_mod_cast hD
  have hlt : (R.cos1 : ℝ) ^ 2 < 1 := by rw [← RTri.rot_cos0]; exact R.rot.cos0_sq_lt
  nlinarith [mul_pos hW' hD', sq_pos_of_pos (mul_pos hW' hD')]

/-- **Lemma 2.2 (ii), actual-plane form.**  For any `A, w, d` with rational lengths `W = ‖w‖`, `D = ‖d‖` and
`∠(w,d) =` the angle of `Δ` at vertex 1, the trapezoid of top ratio `τ = tTau a b c W D > 0` is a union of finitely many
rational triangles similar to `Δ` (disjoint interiors). -/
theorem lemma22_ii_plane (R : RTri) (A w d : Plane) (W Dd : ℚ) (hW : 0 < W) (hD : 0 < Dd)
    (hwn : ‖w‖ = W) (hdn : ‖d‖ = Dd) (hang : InnerProductGeometry.angle w d = vang R.Δ 1)
    (τq : ℚ) (hτ : τq = tTau R.a R.b R.c W Dd) (hτpos : 0 < τq) :
    RatSimDiss R.Δ (trapPlane A w d (τq : ℝ)) := by
  have hdet := hdet_of_angle1 R w d W Dd hW hD hwn hdn hang
  have hw : inner ℝ w w = (W : ℝ) ^ 2 := by rw [real_inner_self_eq_norm_sq, hwn]
  have hd : inner ℝ d d = (Dd : ℝ) ^ 2 := by rw [real_inner_self_eq_norm_sq, hdn]
  have key := trap_ii R A w d hdet W Dd hW hD hw hd (gram_of_angle1 R w d W Dd hW hD hwn hdn hang) τq hτ hτpos
  unfold ChartRSD at key
  rwa [chart_image_trap] at key

/-- **Lemma 2.2 (iii), actual-plane form** (isosceles trapezoid, top ratio `tTauI a b c W D > 0`). -/
theorem lemma22_iii_plane (R : RTri) (A w d : Plane) (W Dd : ℚ) (hW : 0 < W) (hD : 0 < Dd)
    (hwn : ‖w‖ = W) (hdn : ‖d‖ = Dd) (hang : InnerProductGeometry.angle w d = vang R.Δ 1)
    (hτpos : 0 < tTauI R.a R.b R.c W Dd) :
    RatSimDiss R.Δ (trapPlane A w d ((tTauI R.a R.b R.c W Dd : ℚ) : ℝ)) := by
  have hdet := hdet_of_angle1 R w d W Dd hW hD hwn hdn hang
  have hw : inner ℝ w w = (W : ℝ) ^ 2 := by rw [real_inner_self_eq_norm_sq, hwn]
  have hd : inner ℝ d d = (Dd : ℝ) ^ 2 := by rw [real_inner_self_eq_norm_sq, hdn]
  have key := trap_iii R A w d hdet W Dd hW hD hw hd (gram_of_angle1 R w d W Dd hW hD hwn hdn hang) hτpos
  unfold ChartRSD at key
  rwa [chart_image_trap] at key

/-! ### witnesses: tile `(2,3,4)`, `W = 4`, `D = 1` (`τ = tTau 2 3 4 4 1 = 1 + (9-16)/(4·2·4) = 25/32 > 0`) -/

theorem wit_ii_plane :
    ∃ (A w d : Plane) (τ : ℚ), ‖w‖ = ((4 : ℚ) : ℝ) ∧ ‖d‖ = ((1 : ℚ) : ℝ) ∧ 0 < τ ∧
      RatSimDiss R234.Δ (trapPlane A w d (τ : ℝ)) := by
  have hc1 : R234.cos1 = 11 / 16 := by simp [RTri.cos1, R234]; norm_num
  obtain ⟨w, d, hw, hd, hwd, hdet⟩ := exists_gram_chart 4 1 ((11 / 16 : ℚ) : ℝ) (by norm_num) (by norm_num)
    (by norm_num)
  have hwn : ‖w‖ = ((4 : ℚ) : ℝ) := by
    have : ‖w‖ ^ 2 = ((4 : ℚ) : ℝ) ^ 2 := by rw [← real_inner_self_eq_norm_sq]; simpa using hw
    exact (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp this
  have hdn : ‖d‖ = ((1 : ℚ) : ℝ) := by
    have : ‖d‖ ^ 2 = ((1 : ℚ) : ℝ) ^ 2 := by rw [← real_inner_self_eq_norm_sq]; simpa using hd
    exact (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp this
  have hang : InnerProductGeometry.angle w d = vang R234.Δ 1 := by
    apply angle_eq_of_cos (InnerProductGeometry.angle_nonneg _ _) (InnerProductGeometry.angle_le_pi _ _)
      (angle_nonneg _ _ _) (angle_le_pi _ _ _)
    rw [InnerProductGeometry.cos_angle]
    show _ = Real.cos (vang R234.Δ 1)
    rw [RTri.cos_vang1, hwn, hdn]
    have : inner ℝ w d = (4 : ℝ) * 1 * (11 / 16) := by simpa using hwd
    rw [this]
    simp [R234]; norm_num
  have hτ : (0 : ℚ) < tTau R234.a R234.b R234.c 4 1 := by simp [tTau, R234]; norm_num
  exact ⟨0, w, d, tTau R234.a R234.b R234.c 4 1, hwn, hdn, hτ,
    lemma22_ii_plane R234 0 w d 4 1 (by norm_num) (by norm_num) hwn hdn hang _ rfl hτ⟩

#print axioms lemma22_ii_plane
#print axioms lemma22_iii_plane
#print axioms wit_ii_plane

end Erdos634.LaczL37
