-- Draft/CollarInputs.lean — instantiating the collar induction: unit square from `PgramTiling22`,
-- `Δ₂` from `Tiling44Bridge`, `Δ₃` from `Tiling99Bridge` (halved), common model.
-- Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.Draft.CollarParam
import Erdos634.PgramTiling22Bridge
import Erdos634.Tiling44Bridge
import Erdos634.Tiling99Bridge
import Erdos634.Realizable

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.RegionTiling Erdos634.Draft.CollarParam

namespace Erdos634.Draft.CollarInputs

/-- `Phi` as a linear map. -/
noncomputable def PhiL : (ℝ × ℝ) →ₗ[ℝ] Plane :=
  (LinearMap.fst ℝ ℝ ℝ).smulRight e1 + (LinearMap.snd ℝ ℝ ℝ).smulRight e2

theorem PhiL_eq (p : ℝ × ℝ) : PhiL p = Phi p := rfl

theorem Tset_convex (m : ℝ) : Convex ℝ (Tset m) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  show 0 ≤ (a • x + b • y).1 ∧ 0 ≤ (a • x + b • y).2 ∧ (a • x + b • y).1 + (a • x + b • y).2 ≤ m
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  refine ⟨by positivity, by positivity, ?_⟩
  nlinarith

theorem Tset_eq_hull (m : ℝ) (hm : 0 ≤ m) :
    Tset m = convexHull ℝ {((0 : ℝ), (0 : ℝ)), (m, 0), (0, m)} := by
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨h1, h2, h3⟩ := hp
    have hc := convex_convexHull ℝ ({((0 : ℝ), (0 : ℝ)), (m, 0), (0, m)} : Set (ℝ × ℝ))
    have v0 : ((0 : ℝ), (0 : ℝ)) ∈ convexHull ℝ ({((0 : ℝ), (0 : ℝ)), (m, 0), (0, m)} : Set (ℝ × ℝ)) :=
      subset_convexHull ℝ _ (by simp)
    have v1 : (m, (0 : ℝ)) ∈ convexHull ℝ ({((0 : ℝ), (0 : ℝ)), (m, 0), (0, m)} : Set (ℝ × ℝ)) :=
      subset_convexHull ℝ _ (by simp)
    have v2 : ((0 : ℝ), m) ∈ convexHull ℝ ({((0 : ℝ), (0 : ℝ)), (m, 0), (0, m)} : Set (ℝ × ℝ)) :=
      subset_convexHull ℝ _ (by simp)
    rcases eq_or_lt_of_le hm with h0 | hpos
    · have : p = (0, 0) := by
        ext <;> simp <;> linarith
      rw [this]; exact v0
    · have := hc.sum_mem (t := (Finset.univ : Finset (Fin 3)))
        (w := ![(m - p.1 - p.2) / m, p.1 / m, p.2 / m])
        (z := ![((0 : ℝ), (0 : ℝ)), (m, 0), (0, m)])
        (by intro i _; fin_cases i <;> simp <;> [exact div_nonneg (by linarith) hm; exact div_nonneg h1 hm; exact div_nonneg h2 hm])
        (by simp [Fin.sum_univ_three]; field_simp; ring)
        (by intro i _; fin_cases i <;> simpa using ‹_›)
      convert this using 1
      ext <;> simp [Fin.sum_univ_three] <;> field_simp
  · refine convexHull_min ?_ (Tset_convex m)
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨le_refl _, le_refl _, by simpa using hm⟩
    · exact ⟨hm, le_refl _, by simp⟩
    · exact ⟨le_refl _, hm, by simp⟩

theorem tri_carrier_eq (T : Tri) (m : ℝ) (hm : 0 ≤ m) (h0 : T.pts 0 = Phi (0, 0))
    (h1 : T.pts 1 = Phi (m, 0)) (h2 : T.pts 2 = Phi (0, m)) :
    T.carrier = Phi '' Tset m := by
  rw [Tset_eq_hull m hm]
  have : Set.range T.pts = Phi '' {((0 : ℝ), (0 : ℝ)), (m, 0), (0, m)} := by
    ext x
    simp only [Set.mem_range, Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, rfl⟩
      fin_cases k
      · left; exact h0
      · right; left; exact h1
      · right; right; exact h2
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, h0⟩
      · exact ⟨1, h1⟩
      · exact ⟨2, h2⟩
  rw [Tri.carrier, this]
  have := PhiL.image_convexHull ({((0 : ℝ), (0 : ℝ)), (m, 0), (0, m)} : Set (ℝ × ℝ))
  simp only [PhiL_eq] at this
  rw [← this]

open Erdos634.Z15Real Erdos634.Realizable

/-- Transport of a region tiling by a homothety (a similarity: the model is mapped too). -/
noncomputable def mapHom {S : Set Plane} {M : Tri} {N : ℕ} (R : RTiling S M N) (p : Plane) (r : ℝ)
    (hr : r ≠ 0) : RTiling ((homothetyEquiv p r hr) '' S)
      (Erdos634.DissectionMap.mapTri (homothetyEquiv p r hr) M) N where
  tile := fun i => Erdos634.DissectionMap.mapTri (homothetyEquiv p r hr) (R.tile i)
  covers := by
    simp only [Erdos634.DissectionMap.mapTri_carrier]
    rw [← Set.image_iUnion, R.covers]
  disj := fun i j hij =>
    Erdos634.DissectionMap.mapTri_interiors_disjoint (homothetyEquiv p r hr) (R.disj hij)
  cong := fun i => Erdos634.Realizable.mapTri_congruent p r hr (R.cong i)

theorem v1_eq : PgramTiling22Bridge.v1 = mkPt 0 0 := by
  simp [PgramTiling22Bridge.v1, PgramTiling22Bridge.toZPt, zx, zy, PgramTiling22.q1, toR]

theorem v2_eq : PgramTiling22Bridge.v2 = mkPt 44 0 := by
  simp [PgramTiling22Bridge.v2, PgramTiling22Bridge.toZPt, zx, zy, PgramTiling22.q2, toR]

theorem v4_eq : PgramTiling22Bridge.v4 = mkPt 22 (6 * s15) := by
  simp [PgramTiling22Bridge.v4, PgramTiling22Bridge.toZPt, zx, zy, PgramTiling22.q4, toR, s15]

theorem mkPt_zero_vec : (mkPt 0 0 : Plane) = 0 := by
  ext i; fin_cases i <;> simp

theorem hom2_paramMap (u v : ℝ) :
    homothetyEquiv (0 : Plane) 2 (by norm_num) (PgramTiling22Bridge.paramMap (u, v)) = Phi (u, v) := by
  rw [homothetyEquiv_apply]
  simp only [PgramTiling22Bridge.paramMap, AffineMap.coe_mk, v1_eq, v2_eq, v4_eq,
    AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, sub_zero, add_zero]
  ext i
  fin_cases i
  · simp [Phi_apply0, mkPt_zero]; ring
  · simp [Phi_apply1, mkPt_one]; ring

theorem pgram_region :
    (homothetyEquiv (0 : Plane) 2 (by norm_num)) '' PgramTiling22Bridge.carrier
      = Phi '' Rect 0 1 0 1 := by
  rw [PgramTiling22Bridge.carrier_eq_image, ← Set.image_comp]
  ext x
  constructor
  · rintro ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩
    refine ⟨(u, v), ⟨hu.1, hu.2, hv.1, hv.2⟩, ?_⟩
    simp only [Function.comp_apply]
    rw [hom2_paramMap]
  · rintro ⟨⟨u, v⟩, ⟨h1, h2, h3, h4⟩, rfl⟩
    refine ⟨(u, v), ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, ?_⟩
    simp only [Function.comp_apply]
    rw [hom2_paramMap]

/-- The 22 pieces as a region tiling of the raw parallelogram. -/
noncomputable def pgramRT : RTiling PgramTiling22Bridge.carrier
    (PgramTiling22Bridge.pieceTri PgramTiling22Bridge.headI_mem_tiles) PgramTiling22.tiles.length where
  tile := PgramTiling22Bridge.pieceAt
  covers := PgramTiling22Bridge.pgram22_covers
  disj := fun i j hij => PgramTiling22Bridge.pieces_interiors_disjoint
    (List.getElem_mem i.isLt) (List.getElem_mem j.isLt) (PgramTiling22Bridge.tiles_getElem_inj i j hij)
  cong := fun i => PgramTiling22Bridge.pieceTri_congruent (List.getElem_mem i.isLt)

theorem eq_of_sq_eq {d v : ℝ} (hd : 0 ≤ d) (hv : 0 ≤ v) (h : d ^ 2 = v ^ 2) : d = v := by
  nlinarith [sq_nonneg (d - v), sq_nonneg (d + v)]

theorem cong_of_scaled {r : ℝ} (hr : 0 < r) (M0 M1 : Tri)
    (h01 : dist (M1.pts 0) (M1.pts 1) ^ 2 = (r * dist (M0.pts 0) (M0.pts 1)) ^ 2)
    (h12 : dist (M1.pts 1) (M1.pts 2) ^ 2 = (r * dist (M0.pts 1) (M0.pts 2)) ^ 2)
    (h20 : dist (M1.pts 2) (M1.pts 0) ^ 2 = (r * dist (M0.pts 2) (M0.pts 0)) ^ 2) :
    (Erdos634.DissectionMap.mapTri (homothetyEquiv (0 : Plane) r hr.ne') M0).Congruent M1 := by
  have hd : ∀ i j : Fin 3, dist ((Erdos634.DissectionMap.mapTri (homothetyEquiv (0 : Plane) r hr.ne') M0).pts i)
      ((Erdos634.DissectionMap.mapTri (homothetyEquiv (0 : Plane) r hr.ne') M0).pts j)
      = r * dist (M0.pts i) (M0.pts j) := by
    intro i j
    show dist (homothetyEquiv 0 r hr.ne' (M0.pts i)) (homothetyEquiv 0 r hr.ne' (M0.pts j)) = _
    rw [homothetyEquiv_dist, abs_of_pos hr]
  refine SssCongruent.congruent_of_dist_three ?_ ?_ ?_
  · rw [hd]; exact (eq_of_sq_eq dist_nonneg (by positivity) h01).symm
  · rw [hd]; exact (eq_of_sq_eq dist_nonneg (by positivity) h12).symm
  · rw [hd]; exact (eq_of_sq_eq dist_nonneg (by positivity) h20).symm

/-- The common model: the certified 44-tiling's tile, sides `(16, 24, 32)`. -/
noncomputable abbrev M44 : Tri := Erdos634.Tiling44Bridge.dissection.model

theorem M44_sq :
    dist (M44.pts 0) (M44.pts 1) ^ 2 = 256 ∧ dist (M44.pts 1) (M44.pts 2) ^ 2 = 576 ∧
      dist (M44.pts 2) (M44.pts 0) ^ 2 = 1024 := by
  have e01 : Tiling44.dist2 (Erdos634.Tiling44Bridge.vertexOf Tiling44.tiles.headI 0)
      (Erdos634.Tiling44Bridge.vertexOf Tiling44.tiles.headI 1) = ((256:ℤ),(0:ℤ)) := by decide
  have e12 : Tiling44.dist2 (Erdos634.Tiling44Bridge.vertexOf Tiling44.tiles.headI 1)
      (Erdos634.Tiling44Bridge.vertexOf Tiling44.tiles.headI 2) = ((576:ℤ),(0:ℤ)) := by decide
  have e20 : Tiling44.dist2 (Erdos634.Tiling44Bridge.vertexOf Tiling44.tiles.headI 2)
      (Erdos634.Tiling44Bridge.vertexOf Tiling44.tiles.headI 0) = ((1024:ℤ),(0:ℤ)) := by decide
  refine ⟨?_, ?_, ?_⟩
  · show dist ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 0)
      ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 1) ^ 2 = 256
    rw [Erdos634.Tiling44Bridge.pieceTri_dist_sq _ Erdos634.Tiling44Bridge.headI_mem_tiles 0 1, e01]
    simp [toR]
  · show dist ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 1)
      ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 2) ^ 2 = 576
    rw [Erdos634.Tiling44Bridge.pieceTri_dist_sq _ Erdos634.Tiling44Bridge.headI_mem_tiles 1 2, e12]
    simp [toR]
  · show dist ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 2)
      ((Erdos634.Tiling44Bridge.pieceTri Erdos634.Tiling44Bridge.headI_mem_tiles).pts 0) ^ 2 = 1024
    rw [Erdos634.Tiling44Bridge.pieceTri_dist_sq _ Erdos634.Tiling44Bridge.headI_mem_tiles 2 0, e20]
    simp [toR]

/-- The unit parallelogram (`Φ[0,1]²`) tiled by 22 copies of the model. -/
noncomputable def unitSquare : RTiling (Phi '' Rect 0 1 0 1) M44 22 := by
  have h := mapHom pgramRT (0 : Plane) 2 (by norm_num)
  have hc : (Erdos634.DissectionMap.mapTri (homothetyEquiv (0 : Plane) 2 (by norm_num))
      (PgramTiling22Bridge.pieceTri PgramTiling22Bridge.headI_mem_tiles)).Congruent M44 := by
    have m22 := PgramTiling22Bridge.model_sides
    have m44 := M44_sq
    refine cong_of_scaled (by norm_num) _ _ ?_ ?_ ?_
    · rw [m44.1, mul_pow, m22.1]; norm_num
    · rw [m44.2.1, mul_pow, m22.2.1]; norm_num
    · rw [m44.2.2, mul_pow, m22.2.2]; norm_num
  have h2 := (Erdos634.Draft.RegionTiling.remodel h hc)
  have h3 : RTiling (Phi '' Rect 0 1 0 1) M44 PgramTiling22.tiles.length :=
    RTiling.cast pgram_region h2
  exact RTiling.castN (by decide) h3

theorem targetTri44_pts :
    Erdos634.Tiling44Bridge.targetTri.pts 0 = Phi (0, 0) ∧
    Erdos634.Tiling44Bridge.targetTri.pts 1 = Phi (2, 0) ∧
    Erdos634.Tiling44Bridge.targetTri.pts 2 = Phi (0, 2) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [Erdos634.Tiling44Bridge.targetTri_pts_eq]
    ext i; fin_cases i <;>
      simp [Phi_apply0, Phi_apply1, mkPt_zero, mkPt_one, Tiling44.target, Tiling44.t1, Tiling44.t2,
        Tiling44.t3, Erdos634.Tiling44Bridge.toZPt, zx, zy, toR, s15] <;> (try norm_num) <;> (try ring)

/-- `Δ₂` tiled by the certified 44 pieces, in skew coordinates. -/
noncomputable def delta2 : RTiling (Phi '' Tset 2) M44 44 := by
  have h := ofCD Erdos634.Tiling44Bridge.dissection
  have hr : Erdos634.Tiling44Bridge.dissection.target.carrier = Phi '' Tset 2 :=
    tri_carrier_eq _ 2 (by norm_num) targetTri44_pts.1 targetTri44_pts.2.1 targetTri44_pts.2.2
  exact RTiling.castN (by decide) (RTiling.cast hr h)

noncomputable abbrev M99 : Tri := Erdos634.Tiling99Bridge.dissection.model

theorem M99_sq :
    dist (M99.pts 0) (M99.pts 1) ^ 2 = 1024 ∧ dist (M99.pts 1) (M99.pts 2) ^ 2 = 2304 ∧
      dist (M99.pts 2) (M99.pts 0) ^ 2 = 4096 := by
  have e01 : Tiling99.dist2 (Erdos634.Tiling99Bridge.vertexOf Tiling99.tiles.headI 0)
      (Erdos634.Tiling99Bridge.vertexOf Tiling99.tiles.headI 1) = ((1024:ℤ),(0:ℤ)) := by decide
  have e12 : Tiling99.dist2 (Erdos634.Tiling99Bridge.vertexOf Tiling99.tiles.headI 1)
      (Erdos634.Tiling99Bridge.vertexOf Tiling99.tiles.headI 2) = ((2304:ℤ),(0:ℤ)) := by decide
  have e20 : Tiling99.dist2 (Erdos634.Tiling99Bridge.vertexOf Tiling99.tiles.headI 2)
      (Erdos634.Tiling99Bridge.vertexOf Tiling99.tiles.headI 0) = ((4096:ℤ),(0:ℤ)) := by decide
  refine ⟨?_, ?_, ?_⟩
  · show dist ((Erdos634.Tiling99Bridge.pieceTri Erdos634.Tiling99Bridge.headI_mem_tiles).pts 0)
      ((Erdos634.Tiling99Bridge.pieceTri Erdos634.Tiling99Bridge.headI_mem_tiles).pts 1) ^ 2 = 1024
    rw [Erdos634.Tiling99Bridge.pieceTri_dist_sq _ Erdos634.Tiling99Bridge.headI_mem_tiles 0 1, e01]
    norm_num [toR]
  · show dist ((Erdos634.Tiling99Bridge.pieceTri Erdos634.Tiling99Bridge.headI_mem_tiles).pts 1)
      ((Erdos634.Tiling99Bridge.pieceTri Erdos634.Tiling99Bridge.headI_mem_tiles).pts 2) ^ 2 = 2304
    rw [Erdos634.Tiling99Bridge.pieceTri_dist_sq _ Erdos634.Tiling99Bridge.headI_mem_tiles 1 2, e12]
    norm_num [toR]
  · show dist ((Erdos634.Tiling99Bridge.pieceTri Erdos634.Tiling99Bridge.headI_mem_tiles).pts 2)
      ((Erdos634.Tiling99Bridge.pieceTri Erdos634.Tiling99Bridge.headI_mem_tiles).pts 0) ^ 2 = 4096
    rw [Erdos634.Tiling99Bridge.pieceTri_dist_sq _ Erdos634.Tiling99Bridge.headI_mem_tiles 2 0, e20]
    norm_num [toR]

theorem targetTri99_pts :
    (Erdos634.DissectionMap.mapTri (homothetyEquiv (0 : Plane) (1 / 2) (by norm_num))
      Erdos634.Tiling99Bridge.targetTri).pts 0 = Phi (0, 0) ∧
    (Erdos634.DissectionMap.mapTri (homothetyEquiv (0 : Plane) (1 / 2) (by norm_num))
      Erdos634.Tiling99Bridge.targetTri).pts 1 = Phi (3, 0) ∧
    (Erdos634.DissectionMap.mapTri (homothetyEquiv (0 : Plane) (1 / 2) (by norm_num))
      Erdos634.Tiling99Bridge.targetTri).pts 2 = Phi (0, 3) := by
  have key : ∀ k, Erdos634.Tiling99Bridge.targetTri.pts k = mkPt
      (toR (zx (Erdos634.Tiling99Bridge.toZPt (![Tiling99.t1 Tiling99.target, Tiling99.t2 Tiling99.target,
        Tiling99.t3 Tiling99.target] k))))
      (toR (zy (Erdos634.Tiling99Bridge.toZPt (![Tiling99.t1 Tiling99.target, Tiling99.t2 Tiling99.target,
        Tiling99.t3 Tiling99.target] k)))) := by
    intro k; fin_cases k <;> rfl
  refine ⟨?_, ?_, ?_⟩ <;>
  · show homothetyEquiv (0 : Plane) (1 / 2) (by norm_num) (Erdos634.Tiling99Bridge.targetTri.pts _) = _
    rw [homothetyEquiv_apply, key]
    ext i; fin_cases i <;>
      simp [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, sub_zero, add_zero, Phi_apply0, Phi_apply1, mkPt_zero, mkPt_one, Tiling99.target, Tiling99.t1, Tiling99.t2,
        Tiling99.t3, Erdos634.Tiling99Bridge.toZPt, zx, zy, toR, s15] <;> (try norm_num) <;> (try ring)

/-- `Δ₃` tiled by the certified 99 pieces, halved into the common scale. -/
noncomputable def delta3 : RTiling (Phi '' Tset 3) M44 99 := by
  have h := mapHom (ofCD Erdos634.Tiling99Bridge.dissection) (0 : Plane) (1 / 2) (by norm_num)
  have hc : (Erdos634.DissectionMap.mapTri (homothetyEquiv (0 : Plane) (1 / 2) (by norm_num)) M99).Congruent
      M44 := by
    have m99 := M99_sq
    have m44 := M44_sq
    refine cong_of_scaled (by norm_num) _ _ ?_ ?_ ?_
    · rw [m44.1, mul_pow, m99.1]; norm_num
    · rw [m44.2.1, mul_pow, m99.2.1]; norm_num
    · rw [m44.2.2, mul_pow, m99.2.2]; norm_num
  have h2 := Erdos634.Draft.RegionTiling.remodel h hc
  have hr : (homothetyEquiv (0 : Plane) (1 / 2) (by norm_num)) ''
      Erdos634.Tiling99Bridge.dissection.target.carrier = Phi '' Tset 3 := by
    rw [← Erdos634.DissectionMap.mapTri_carrier]
    exact tri_carrier_eq _ 3 (by norm_num) targetTri99_pts.1 targetTri99_pts.2.1 targetTri99_pts.2.2
  exact RTiling.castN (by decide) (RTiling.cast hr h2)

/-- **The `(1,2)` spectrum, existence half, in region form:** every `Δ_m`, `m ≥ 2`, is tiled by `11m²`
copies of the tile `(16,24,32)`. -/
theorem realize12_region (m : ℕ) (hm : 2 ≤ m) :
    Nonempty (RTiling (Phi '' Tset (m : ℝ)) M44 (11 * (m * m))) :=
  realize_all unitSquare delta2 delta3 m hm

theorem det_delta (m : ℝ) (hm : 0 < m) : det3 0 0 (88 * m) 0 (44 * m) (12 * s15 * m) ≠ 0 := by
  unfold det3
  have := s15_pos
  nlinarith [mul_pos (mul_pos hm hm) this]

/-- The triangle `Δ_m` with vertices `Φ(0,0), Φ(m,0), Φ(0,m)`. -/
noncomputable def deltaTri (m : ℝ) (hm : 0 < m) : Tri :=
  mkTri 0 0 (88 * m) 0 (44 * m) (12 * s15 * m) (det_delta m hm)

theorem deltaTri_carrier (m : ℝ) (hm : 0 < m) : (deltaTri m hm).carrier = Phi '' Tset m := by
  refine tri_carrier_eq _ m hm.le ?_ ?_ ?_
  · ext i; fin_cases i <;> simp [deltaTri, mkTri, Phi_apply0, Phi_apply1, mkPt_zero, mkPt_one]
  · ext i; fin_cases i <;> simp [deltaTri, mkTri, Phi_apply0, Phi_apply1, mkPt_zero, mkPt_one]
  · ext i; fin_cases i <;> simp [deltaTri, mkTri, Phi_apply0, Phi_apply1, mkPt_zero, mkPt_one] <;> ring

/-- **Existence half of `thm:realize12` (member `(1,2)`), as a `CongruentDissection`:** for every
`m ≥ 2` the triangle `Δ_m` (base `88m`, apex `(44m, 12√15 m)`) is dissected into `11 m²` copies of the
tile `(16,24,32)`. -/
theorem realize12 (m : ℕ) (hm : 2 ≤ m) :
    ∃ D : CongruentDissection (11 * (m * m)), D.model = M44 := by
  obtain ⟨R⟩ := realize12_region m hm
  have hpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have R' : RTiling (deltaTri (m : ℝ) hpos).carrier M44 (11 * (m * m)) :=
    RTiling.cast (deltaTri_carrier _ hpos).symm R
  exact ⟨toCD R', rfl⟩

end Erdos634.Draft.CollarInputs

#print axioms Erdos634.Draft.CollarInputs.realize12
