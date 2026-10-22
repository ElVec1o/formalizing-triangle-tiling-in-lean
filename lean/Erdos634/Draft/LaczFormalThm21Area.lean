-- Draft/LaczFormalThm21Area.lean -- Laczkovich DCG 48 (2012), Lemma 4.1 (parallelogram + area), first brick of Theorem 2.1.
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Lemma 4.1; Combinatorica 10 (1990); Discrete Math 140 (1995)), Beeson, Beeson-Zhang.
import Erdos634.AreaDet
import Erdos634.CongruentArea
import Erdos634.TriLawSin
import Erdos634.RegionDissection
import Erdos634.MarchFlank
import Erdos634.RouteOneVertexKill

open MeasureTheory Erdos634.Geometry Erdos634.AreaDet Erdos634.RegionDissection Erdos634.TilePlacement
open scoped ENNReal

namespace Erdos634.Draft.LaczFormal.Thm21

/-- Planar cross product (determinant). -/
def cross2 (u w : Plane) : ℝ := u 0 * w 1 - u 1 * w 0

theorem norm_sq_plane (u : Plane) : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_two]

theorem inner_plane (u w : Plane) : inner ℝ u w = u 0 * w 0 + u 1 * w 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

/-- **|det| = |u| |w| sin(angle).** -/
theorem abs_cross2 (u w : Plane) :
    |cross2 u w| = ‖u‖ * ‖w‖ * Real.sin (InnerProductGeometry.angle u w) := by
  have hs : 0 ≤ Real.sin (InnerProductGeometry.angle u w) := InnerProductGeometry.sin_angle_nonneg u w
  have h1 : cross2 u w ^ 2 = (‖u‖ * ‖w‖ * Real.sin (InnerProductGeometry.angle u w)) ^ 2 := by
    have hc := InnerProductGeometry.cos_angle_mul_norm_mul_norm u w
    have hsc := Real.sin_sq_add_cos_sq (InnerProductGeometry.angle u w)
    have e1 : cross2 u w ^ 2 + (inner ℝ u w) ^ 2 = ‖u‖ ^ 2 * ‖w‖ ^ 2 := by
      rw [inner_plane, norm_sq_plane, norm_sq_plane]; unfold cross2; ring
    by_cases hu : u = 0
    · subst hu; simp [cross2]
    by_cases hw : w = 0
    · subst hw; simp [cross2]
    have hn : ‖u‖ * ‖w‖ ≠ 0 := mul_ne_zero (norm_ne_zero_iff.mpr hu) (norm_ne_zero_iff.mpr hw)
    rw [← hc] at e1
    have : (‖u‖ * ‖w‖) ^ 2 * (Real.sin (InnerProductGeometry.angle u w) ^ 2 + Real.cos (InnerProductGeometry.angle u w) ^ 2) = ‖u‖ ^ 2 * ‖w‖ ^ 2 := by
      rw [hsc]; ring
    nlinarith [this, e1]
  have h2 : 0 ≤ ‖u‖ * ‖w‖ * Real.sin (InnerProductGeometry.angle u w) := by positivity
  rw [← abs_of_nonneg h2]
  exact sq_eq_sq_iff_abs_eq_abs _ _ |>.mp h1

/-- The linear map `x ↦ x 0 • u + x 1 • w`. -/
noncomputable def pgMap (u w : Plane) : Plane →ₗ[ℝ] Plane := pb.constr ℝ ![u, w]

theorem pgMap_apply (u w x : Plane) : pgMap u w x = x 0 • u + x 1 • w := by
  have hx : x = x 0 • pb 0 + x 1 • pb 1 := by
    ext i; fin_cases i <;> simp [pb_apply_self]
  conv_lhs => rw [hx]
  simp [pgMap, map_add, map_smul]

theorem det_pgMap (u w : Plane) : LinearMap.det (pgMap u w) = cross2 u w := by
  rw [← LinearMap.det_toMatrix pb, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, pgMap_apply, pb_repr, cross2, pb_apply_self]
  ring

/-- The parallelogram with vertex `O` and edge vectors `u, w`. -/
def pgramSet (O u w : Plane) : Set Plane := {x | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, x = O + s • u + t • w}

theorem pgramSet_eq (O u w : Plane) : pgramSet O u w = (fun x : Plane => O + pgMap u w x) '' stdSquare := by
  ext x
  simp only [pgramSet, Set.mem_setOf_eq, Set.mem_image, stdSquare]
  constructor
  · rintro ⟨s, hs, t, ht, rfl⟩
    refine ⟨(EuclideanSpace.single 0 s + EuclideanSpace.single 1 t : Plane), ⟨?_, ?_⟩, ?_⟩
    · simpa using hs
    · simpa using ht
    · rw [pgMap_apply]; simp [add_assoc]
  · rintro ⟨y, ⟨hy0, hy1⟩, rfl⟩
    exact ⟨y 0, hy0, y 1, hy1, by rw [pgMap_apply]; simp [add_assoc]⟩

/-- **Area of a parallelogram = |det|.** -/
theorem volume_pgramSet (O u w : Plane) : volume (pgramSet O u w) = ENNReal.ofReal |cross2 u w| := by
  rw [pgramSet_eq]
  have hpre : (fun x : Plane => O + pgMap u w x) '' stdSquare
      = (fun h : Plane => (-O) + h) ⁻¹' (pgMap u w '' stdSquare) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, by simp⟩
    · rintro ⟨x, hx, hxy⟩; exact ⟨x, hx, by simp only at hxy ⊢; rw [hxy]; abel⟩
  rw [hpre, measure_preimage_add, Measure.addHaar_image_linearMap, det_pgMap, volume_stdSquare, mul_one]

/-- **Area additivity for a region dissection.** -/
theorem volume_region_eq {N : ℕ} (R : RegionDissection N) :
    volume R.region = ∑ i, volume (R.tile i).carrier := by
  have hae : ∀ {i j : Fin N}, i ≠ j → AEDisjoint volume (R.tile i).carrier (R.tile j).carrier := by
    intro i j hij
    have hsub : (R.tile i).carrier ∩ (R.tile j).carrier ⊆
        frontier (R.tile i).carrier ∪ frontier (R.tile j).carrier := by
      rintro x ⟨hxi, hxj⟩
      by_cases h1 : x ∈ interior (R.tile i).carrier
      · by_cases h2 : x ∈ interior (R.tile j).carrier
        · exact absurd h2 (Set.disjoint_left.mp (R.interiors_disjoint hij) h1)
        · exact Or.inr ⟨subset_closure hxj, h2⟩
      · exact Or.inl ⟨subset_closure hxi, h1⟩
    exact measure_mono_null hsub (measure_union_null (R.tile i).volume_frontier (R.tile j).volume_frontier)
  have h := measure_biUnion_finset₀ (μ := volume) (s := (Finset.univ : Finset (Fin N)))
    (f := fun i => (R.tile i).carrier) (fun _ _ _ _ hij => hae hij) (fun i _ => (R.tile i).nullMeasurableSet)
  have hU : (⋃ i ∈ (Finset.univ : Finset (Fin N)), (R.tile i).carrier) = R.region := by
    rw [← R.covers]; simp
  rw [hU] at h; exact h

/-- Area of a tile: `|det| / 2`. -/
theorem volume_tri_eq (T : Tri) : volume T.carrier = ENNReal.ofReal (|detTri T| / 2) := by
  rw [volume_eq_det_mul, volume_stdCarrier_half,
    show (1/2 : ℝ≥0∞) = ENNReal.ofReal (1/2) by rw [ENNReal.ofReal_div_of_pos two_pos]; simp,
    ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1; ring

/-- `|det T| = |p1-p0| |p2-p0| sin (angle at 0)`. -/
theorem abs_detTri_vertex0 (T : Tri) :
    |detTri T| = sideOpp T 2 * sideOpp T 1 * Real.sin (angleAt T 0) := by
  have h : detTri T = cross2 (T.pts 1 - T.pts 0) (T.pts 2 - T.pts 0) := by
    rw [detTri_eq]; unfold cross2; ring
  rw [h, abs_cross2]
  have e1 : ‖T.pts 1 - T.pts 0‖ = sideOpp T 2 := by
    rw [← dist_eq_norm]; unfold sideOpp; show dist (T.pts 1) (T.pts 0) = dist (T.pts (2+1)) (T.pts (2+2)); 
    have : (2 + 1 : Fin 3) = 0 := rfl
    have h2 : (2 + 2 : Fin 3) = 1 := rfl
    rw [this, h2, dist_comm]
  have e2 : ‖T.pts 2 - T.pts 0‖ = sideOpp T 1 := by
    rw [← dist_eq_norm]; unfold sideOpp
    have : (1 + 1 : Fin 3) = 2 := rfl
    have h2 : (1 + 2 : Fin 3) = 0 := rfl
    rw [this, h2]
  rw [e1, e2]
  congr 2

/-- `|det T| = a b sin γ` (area `½ a b sin γ`), `a = sideOpp 0`, `b = sideOpp 1`, `γ` the angle at vertex `2`. -/
theorem abs_detTri_ab (T : Tri) :
    |detTri T| = sideOpp T 0 * sideOpp T 1 * Real.sin (angleAt T 2) := by
  rw [abs_detTri_vertex0]
  have h := Erdos634.TriLawSin.sin_angleAt_mul_sideOpp T 2
  have e : (2 + 1 : Fin 3) = 0 := rfl
  rw [e] at h
  calc sideOpp T 2 * sideOpp T 1 * Real.sin (angleAt T 0)
      = sideOpp T 1 * (Real.sin (angleAt T 0) * sideOpp T 2) := by ring
    _ = sideOpp T 1 * (Real.sin (angleAt T 2) * sideOpp T 0) := by rw [← h]
    _ = _ := by ring

/-- **The area equation of a congruent dissection of a parallelogram:** `t · a b = 2 |u| |w|`
(`t` = number of tiles, `a, b` = the model sides opposite `α, β`, `γ` = the model angle at vertex 2;
the parallelogram has angles `γ`, `π - γ`, so `sin ∠(u,w) = sin γ`). -/
theorem pgram_area_eq {N : ℕ} (C : CongruentRegionDissection N) (O u w : Plane)
    (hreg : C.region = pgramSet O u w)
    (hang : Real.sin (InnerProductGeometry.angle u w) = Real.sin (angleAt C.model 2)) :
    (N : ℝ) * (sideOpp C.model 0 * sideOpp C.model 1) = 2 * (‖u‖ * ‖w‖) := by
  have h1 : volume C.region = (N : ℝ≥0∞) * volume C.model.carrier := by
    rw [volume_region_eq C.toRegionDissection]
    simp only [fun i => Erdos634.CongruentArea.volume_congruent (C.tiles_congruent i)]
    simp
  rw [hreg, volume_pgramSet, volume_tri_eq] at h1
  have hpos : 0 < |detTri C.model| := by
    have := C.model.volume_pos
    rw [volume_tri_eq] at this
    have := (ENNReal.ofReal_pos.mp this)
    linarith
  rw [abs_detTri_ab] at hpos
  have hsin : Real.sin (angleAt C.model 2) ≠ 0 := by
    intro h; rw [h] at hpos; simp at hpos
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_eq_ofReal_iff (abs_nonneg _) (by positivity)] at h1
  rw [abs_cross2, hang, abs_detTri_ab] at h1
  have : (‖u‖ * ‖w‖) * Real.sin (angleAt C.model 2) =
      ((N : ℝ) * (sideOpp C.model 0 * sideOpp C.model 1) / 2) * Real.sin (angleAt C.model 2) := by
    rw [h1]; ring
  have := mul_right_cancel₀ hsin this
  linarith

theorem sideOpp_pos_aux (T : Tri) (m : Fin 3) : 0 < sideOpp T m := by
  unfold sideOpp
  exact dist_pos.mpr (T.indep.injective.ne ((by decide : ∀ m : Fin 3, m + 1 ≠ m + 2) m))

theorem sin_angleAt_pos (T : Tri) (j : Fin 3) : 0 < Real.sin (angleAt T j) :=
  Real.sin_pos_of_pos_of_lt_pi (MarchFlank.cornerAngle_pos T j) (Erdos634.RouteOneVertexKill.cornerAngle_lt_pi T j)

/-- `a / b = sin α / sin β` (law of sines, model vertices 0, 1). -/
theorem side_ratio_eq_sin (T : Tri) :
    sideOpp T 0 / sideOpp T 1 = Real.sin (angleAt T 0) / Real.sin (angleAt T 1) := by
  have h := Erdos634.TriLawSin.sin_angleAt_mul_sideOpp T 0
  have e : (0 + 1 : Fin 3) = 1 := rfl
  rw [e] at h
  have hb := sideOpp_pos_aux T 1
  have hs := sin_angleAt_pos T 1
  rw [div_eq_div_iff hb.ne' hs.ne']
  linarith

theorem ratio_of_area {N k : ℕ} {a b x y : ℝ} (ha : 0 < a) (hb : 0 < b) (hk : 0 < k)
    (harea : (N : ℝ) * (a * b) = 2 * (x * y)) (hx : x = k * a) :
    x / y = ((2 * (k : ℚ) ^ 2 / N : ℚ) : ℝ) * (a / b) := by
  by_cases hN : N = 0
  · subst hN
    have : x * y = 0 := by simpa using harea.symm
    have hx0 : x ≠ 0 := by rw [hx]; positivity
    have hy0 : y = 0 := (mul_eq_zero.mp this).resolve_left hx0
    simp [hy0]
  · have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    subst hx
    have hy : y = N * b / (2 * k) := by
      field_simp at harea ⊢
      nlinarith [harea]
    rw [hy]
    push_cast
    field_simp

/-- **Laczkovich, DCG 48 (2012), Lemma 4.1.**  `C` is a dissection of the parallelogram `O + [0,1]u + [0,1]w`
(angle `γ` or `π - γ` between `u` and `w`) into congruent copies of a triangle of angles `α, β, γ` (model vertices
0, 1, 2) and sides `a, b, c`.  If `|u| = k a` with `k` a positive integer, then `|u| / |w|` is a rational multiple of
`sin α / sin β`. -/
theorem lemma41 {N : ℕ} (C : CongruentRegionDissection N) (O u w : Plane)
    (hreg : C.region = pgramSet O u w)
    (hang : Real.sin (InnerProductGeometry.angle u w) = Real.sin (angleAt C.model 2))
    (k : ℕ) (hk : 0 < k) (hu : ‖u‖ = k * sideOpp C.model 0) :
    ∃ q : ℚ, ‖u‖ / ‖w‖ = q * (Real.sin (angleAt C.model 0) / Real.sin (angleAt C.model 1)) := by
  refine ⟨2 * (k : ℚ) ^ 2 / N, ?_⟩
  rw [← side_ratio_eq_sin]
  exact ratio_of_area (sideOpp_pos_aux _ 0) (sideOpp_pos_aux _ 1) hk (pgram_area_eq C O u w hreg hang) hu

/-- The same for the other edge: `|w| = k a` gives `|w| / |u|`. -/
theorem lemma41' {N : ℕ} (C : CongruentRegionDissection N) (O u w : Plane)
    (hreg : C.region = pgramSet O u w)
    (hang : Real.sin (InnerProductGeometry.angle u w) = Real.sin (angleAt C.model 2))
    (k : ℕ) (hk : 0 < k) (hw : ‖w‖ = k * sideOpp C.model 0) :
    ∃ q : ℚ, ‖w‖ / ‖u‖ = q * (Real.sin (angleAt C.model 0) / Real.sin (angleAt C.model 1)) := by
  refine ⟨2 * (k : ℚ) ^ 2 / N, ?_⟩
  rw [← side_ratio_eq_sin]
  have h := pgram_area_eq C O u w hreg hang
  rw [mul_comm ‖u‖ ‖w‖] at h
  exact ratio_of_area (sideOpp_pos_aux _ 0) (sideOpp_pos_aux _ 1) hk h hw

end Erdos634.Draft.LaczFormal.Thm21
