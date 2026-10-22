import Erdos634.Draft.LaczFormalThm21Area
import Erdos634.Draft.ZhangSporadic
import Erdos634.CertGeom
import Erdos634.CoversGeneral

/-!
# Beeson (arXiv 1206.2229v4) Fig. 27: the geometry of the assembly for Corollary 6

NOTE, UNAUDITED.  Credit: Beeson (arXiv 1206.2229, Sect. 13.4, Fig. 27, adapted from Laczkovich), Beeson-Zhang, Zhang.

Tile `(a,b,c)` with `a^2 + c b = c^2`, realised as `T0 = (0,0), (c,0), (w,h)`, `w = b(b+c)/(2c)`, `w^2 + h^2 = b^2`.
Skew coordinates `(x,y) |-> (c x + w y, h y)` (`B = origin`, `u = (c,0)`, `v = (w,h)`; `u.v = b(b+c)/2`).  With `p > 0`:

  `B = (0,0)`, `C = ((b+c)p, 0)`, `F = (0, (b+c)p)`, `A = (0, (b+2c)p)`, `G = (bp, cp)`.

`ABC` has angles `(2 alpha, alpha, 2 beta)`: `|AC| = c^2 p`, `|AB| = b(b+2c)p`, `|BC| = c(b+c)p`.  Pieces: `T1 = BCF`
(similar to the tile, ratio `(b+c)p`), `T2 = ACG` (ratio `c p`), `T3 = AFG` (isosceles, legs `bcp`, base `abp`).
Proved here: squared sides (via the quadratic form), containment, equal volumes sum, separating lines, the exact cover
`T1 ∪ (T2 ∪ T3) = ABC`.  (The dissections are glued in `BeesonCor6`.)
-/

namespace Erdos634.BeesonCor6Geom

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom MeasureTheory
open scoped ENNReal

structure Cfg where
  b : ℝ
  c : ℝ
  p : ℝ
  w : ℝ
  h : ℝ
  hb : 0 < b
  hc : 0 < c
  hp : 0 < p
  hh : 0 < h
  hw : w * (2 * c) = b * (b + c)
  hwh : w ^ 2 + h ^ 2 = b ^ 2

namespace Cfg
variable (K : Cfg)

/-- point with skew coordinates `(x,y)` -/
noncomputable def pt (x y : ℝ) : Plane := mkPt (K.c * x + K.w * y) (K.h * y)

theorem det3_aff (x0 y0 x1 y1 x2 y2 : ℝ) :
    det3 (K.c * x0 + K.w * y0) (K.h * y0) (K.c * x1 + K.w * y1) (K.h * y1) (K.c * x2 + K.w * y2) (K.h * y2)
      = K.c * K.h * det3 x0 y0 x1 y1 x2 y2 := by
  unfold det3; ring

theorem ch_pos : 0 < K.c * K.h := mul_pos K.hc K.hh

/-- triangle with skew-coordinate vertices -/
noncomputable def tri (x0 y0 x1 y1 x2 y2 : ℝ) (hd : det3 x0 y0 x1 y1 x2 y2 ≠ 0) : Tri :=
  mkTri (K.c * x0 + K.w * y0) (K.h * y0) (K.c * x1 + K.w * y1) (K.h * y1) (K.c * x2 + K.w * y2) (K.h * y2)
    (by rw [K.det3_aff]; exact mul_ne_zero K.ch_pos.ne' hd)

theorem tri_pts (x0 y0 x1 y1 x2 y2 : ℝ) (hd : det3 x0 y0 x1 y1 x2 y2 ≠ 0) :
    (K.tri x0 y0 x1 y1 x2 y2 hd).pts = ![K.pt x0 y0, K.pt x1 y1, K.pt x2 y2] := rfl

/-- the squared distance is the quadratic form of the Gram matrix of `(u,v)` -/
theorem dist_sq_pt (x1 y1 x2 y2 : ℝ) :
    dist (K.pt x1 y1) (K.pt x2 y2) ^ 2
      = K.c ^ 2 * (x1 - x2) ^ 2 + K.b * (K.b + K.c) * ((x1 - x2) * (y1 - y2)) + K.b ^ 2 * (y1 - y2) ^ 2 := by
  unfold pt
  rw [dist_sq_mkPt]
  have h1 := K.hw
  have h2 := K.hwh
  have : (K.c * x1 + K.w * y1 - (K.c * x2 + K.w * y2)) ^ 2 + (K.h * y1 - K.h * y2) ^ 2
      = K.c ^ 2 * (x1 - x2) ^ 2 + (K.w * (2 * K.c)) * ((x1 - x2) * (y1 - y2)) + (K.w ^ 2 + K.h ^ 2) * (y1 - y2) ^ 2 := by
    ring
  rw [this, h1, h2]

/-- the model tile `T0`: sides `c, b, a` -/
noncomputable def T0 : Tri := K.tri 0 0 1 0 0 1 (by unfold det3; norm_num)

/-- the pieces and the whole triangle -/
noncomputable def T1 : Tri :=
  K.tri 0 0 ((K.b + K.c) * K.p) 0 0 ((K.b + K.c) * K.p)
    (by
      have : det3 0 0 ((K.b + K.c) * K.p) 0 0 ((K.b + K.c) * K.p) = ((K.b + K.c) * K.p) ^ 2 := by
        unfold det3; ring
      rw [this]; have := K.hb; have := K.hc; have := K.hp; positivity)
noncomputable def T2 : Tri :=
  K.tri 0 ((K.b + 2 * K.c) * K.p) ((K.b + K.c) * K.p) 0 (K.b * K.p) (K.c * K.p)
    (by
      have : det3 0 ((K.b + 2 * K.c) * K.p) ((K.b + K.c) * K.p) 0 (K.b * K.p) (K.c * K.p) = -(K.c ^ 2 * K.p ^ 2) := by
        unfold det3; ring
      rw [this]; have := K.hc; have := K.hp; simp only [ne_eq, neg_eq_zero]; positivity)
noncomputable def T3 : Tri :=
  K.tri 0 ((K.b + K.c) * K.p) (K.b * K.p) (K.c * K.p) 0 ((K.b + 2 * K.c) * K.p)
    (by
      have : det3 0 ((K.b + K.c) * K.p) (K.b * K.p) (K.c * K.p) 0 ((K.b + 2 * K.c) * K.p) = K.b * K.c * K.p ^ 2 := by
        unfold det3; ring
      rw [this]; have := K.hb; have := K.hc; have := K.hp; positivity)
noncomputable def TT : Tri :=
  K.tri 0 ((K.b + 2 * K.c) * K.p) ((K.b + K.c) * K.p) 0 0 0
    (by
      have : det3 0 ((K.b + 2 * K.c) * K.p) ((K.b + K.c) * K.p) 0 0 0
          = -((K.b + K.c) * K.p * ((K.b + 2 * K.c) * K.p)) := by
        unfold det3; ring
      rw [this]; have := K.hb; have := K.hc; have := K.hp; simp only [ne_eq, neg_eq_zero]; positivity)

theorem sqeq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ^ 2 = y ^ 2) : x = y := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]

theorem dist_scale (T U : Tri) (k : ℝ) (hk : 0 ≤ k)
    (h01 : dist (U.pts 0) (U.pts 1) ^ 2 = k ^ 2 * dist (T.pts 0) (T.pts 1) ^ 2)
    (h02 : dist (U.pts 0) (U.pts 2) ^ 2 = k ^ 2 * dist (T.pts 0) (T.pts 2) ^ 2)
    (h12 : dist (U.pts 1) (U.pts 2) ^ 2 = k ^ 2 * dist (T.pts 1) (T.pts 2) ^ 2) :
    ∀ x y, dist (U.pts x) (U.pts y) = k * dist (T.pts x) (T.pts y) := by
  have e01 : dist (U.pts 0) (U.pts 1) = k * dist (T.pts 0) (T.pts 1) :=
    sqeq dist_nonneg (by positivity) (by rw [h01]; ring)
  have e02 : dist (U.pts 0) (U.pts 2) = k * dist (T.pts 0) (T.pts 2) :=
    sqeq dist_nonneg (by positivity) (by rw [h02]; ring)
  have e12 : dist (U.pts 1) (U.pts 2) = k * dist (T.pts 1) (T.pts 2) :=
    sqeq dist_nonneg (by positivity) (by rw [h12]; ring)
  have e10 : dist (U.pts 1) (U.pts 0) = k * dist (T.pts 1) (T.pts 0) := by
    rw [dist_comm, e01, dist_comm (T.pts 1)]
  have e20 : dist (U.pts 2) (U.pts 0) = k * dist (T.pts 2) (T.pts 0) := by
    rw [dist_comm, e02, dist_comm (T.pts 2)]
  have e21 : dist (U.pts 2) (U.pts 1) = k * dist (T.pts 2) (T.pts 1) := by
    rw [dist_comm, e12, dist_comm (T.pts 2)]
  intro x y
  fin_cases x <;> fin_cases y <;> simp [e01, e02, e12, e10, e20, e21]

/-! ### squared sides -/

theorem T0_01 : dist (K.T0.pts 0) (K.T0.pts 1) ^ 2 = K.c ^ 2 := by
  show dist (K.pt 0 0) (K.pt 1 0) ^ 2 = _
  rw [dist_sq_pt]; ring
theorem T0_02 : dist (K.T0.pts 0) (K.T0.pts 2) ^ 2 = K.b ^ 2 := by
  show dist (K.pt 0 0) (K.pt 0 1) ^ 2 = _
  rw [dist_sq_pt]; ring
theorem T0_12 : dist (K.T0.pts 1) (K.T0.pts 2) ^ 2 = K.c ^ 2 - K.b * K.c := by
  show dist (K.pt 1 0) (K.pt 0 1) ^ 2 = _
  rw [dist_sq_pt]; ring

theorem T1_dist : ∀ x y, dist (K.T1.pts x) (K.T1.pts y) = ((K.b + K.c) * K.p) * dist (K.T0.pts x) (K.T0.pts y) := by
  have hk : 0 ≤ (K.b + K.c) * K.p := by have := K.hb; have := K.hc; have := K.hp; positivity
  refine dist_scale _ _ _ hk ?_ ?_ ?_
  · show dist (K.pt 0 0) (K.pt ((K.b + K.c) * K.p) 0) ^ 2 = _
    rw [K.T0_01, dist_sq_pt]; ring
  · show dist (K.pt 0 0) (K.pt 0 ((K.b + K.c) * K.p)) ^ 2 = _
    rw [K.T0_02, dist_sq_pt]; ring
  · show dist (K.pt ((K.b + K.c) * K.p) 0) (K.pt 0 ((K.b + K.c) * K.p)) ^ 2 = _
    rw [K.T0_12, dist_sq_pt]; ring

theorem T2_dist : ∀ x y, dist (K.T2.pts x) (K.T2.pts y) = (K.c * K.p) * dist (K.T0.pts x) (K.T0.pts y) := by
  have hk : 0 ≤ K.c * K.p := by have := K.hc; have := K.hp; positivity
  refine dist_scale _ _ _ hk ?_ ?_ ?_
  · show dist (K.pt 0 ((K.b + 2 * K.c) * K.p)) (K.pt ((K.b + K.c) * K.p) 0) ^ 2 = _
    rw [K.T0_01, dist_sq_pt]; ring
  · show dist (K.pt 0 ((K.b + 2 * K.c) * K.p)) (K.pt (K.b * K.p) (K.c * K.p)) ^ 2 = _
    rw [K.T0_02, dist_sq_pt]; ring
  · show dist (K.pt ((K.b + K.c) * K.p) 0) (K.pt (K.b * K.p) (K.c * K.p)) ^ 2 = _
    rw [K.T0_12, dist_sq_pt]; ring

theorem T3_01 : dist (K.T3.pts 0) (K.T3.pts 1) ^ 2 = (K.c ^ 2 - K.b * K.c) * (K.b * K.p) ^ 2 := by
  show dist (K.pt 0 ((K.b + K.c) * K.p)) (K.pt (K.b * K.p) (K.c * K.p)) ^ 2 = _
  rw [dist_sq_pt]; ring
theorem T3_02 : dist (K.T3.pts 0) (K.T3.pts 2) ^ 2 = (K.b * K.c * K.p) ^ 2 := by
  show dist (K.pt 0 ((K.b + K.c) * K.p)) (K.pt 0 ((K.b + 2 * K.c) * K.p)) ^ 2 = _
  rw [dist_sq_pt]; ring
theorem T3_12 : dist (K.T3.pts 1) (K.T3.pts 2) ^ 2 = (K.b * K.c * K.p) ^ 2 := by
  show dist (K.pt (K.b * K.p) (K.c * K.p)) (K.pt 0 ((K.b + 2 * K.c) * K.p)) ^ 2 = _
  rw [dist_sq_pt]; ring

theorem TT_01 : dist (K.TT.pts 0) (K.TT.pts 1) ^ 2 = (K.c ^ 2 * K.p) ^ 2 := by
  show dist (K.pt 0 ((K.b + 2 * K.c) * K.p)) (K.pt ((K.b + K.c) * K.p) 0) ^ 2 = _
  rw [dist_sq_pt]; ring
theorem TT_02 : dist (K.TT.pts 0) (K.TT.pts 2) ^ 2 = (K.b * (K.b + 2 * K.c) * K.p) ^ 2 := by
  show dist (K.pt 0 ((K.b + 2 * K.c) * K.p)) (K.pt 0 0) ^ 2 = _
  rw [dist_sq_pt]; ring
theorem TT_12 : dist (K.TT.pts 1) (K.TT.pts 2) ^ 2 = (K.c * (K.b + K.c) * K.p) ^ 2 := by
  show dist (K.pt ((K.b + K.c) * K.p) 0) (K.pt 0 0) ^ 2 = _
  rw [dist_sq_pt]; ring

/-! ### volumes -/

theorem vol_tri (x0 y0 x1 y1 x2 y2 : ℝ) (hd : det3 x0 y0 x1 y1 x2 y2 ≠ 0) :
    volume (K.tri x0 y0 x1 y1 x2 y2 hd).carrier
      = ENNReal.ofReal (K.c * K.h * |det3 x0 y0 x1 y1 x2 y2| / 2) := by
  rw [Erdos634.Draft.LaczFormal.Thm21.volume_tri_eq]
  have : Erdos634.AreaDet.detTri (K.tri x0 y0 x1 y1 x2 y2 hd) = K.c * K.h * det3 x0 y0 x1 y1 x2 y2 := by
    unfold tri; rw [detTri_mkTri, det3_aff]
  rw [this, abs_mul, abs_of_pos K.ch_pos]

theorem vol_T0 : volume K.T0.carrier = ENNReal.ofReal (K.c * K.h / 2) := by
  unfold T0; rw [vol_tri]
  congr 1
  have : det3 0 0 1 0 0 1 = 1 := by unfold det3; norm_num
  rw [this]; simp

theorem vol_T1 : volume K.T1.carrier = ENNReal.ofReal (K.c * K.h * ((K.b + K.c) * K.p) ^ 2 / 2) := by
  unfold T1; rw [vol_tri]
  congr 1
  have : det3 0 0 ((K.b + K.c) * K.p) 0 0 ((K.b + K.c) * K.p) = ((K.b + K.c) * K.p) ^ 2 := by
    unfold det3; ring
  rw [this, abs_of_nonneg (sq_nonneg _)]

theorem vol_T2 : volume K.T2.carrier = ENNReal.ofReal (K.c * K.h * (K.c * K.p) ^ 2 / 2) := by
  unfold T2; rw [vol_tri]
  congr 1
  have : det3 0 ((K.b + 2 * K.c) * K.p) ((K.b + K.c) * K.p) 0 (K.b * K.p) (K.c * K.p) = -((K.c * K.p) ^ 2) := by
    unfold det3; ring
  rw [this, abs_neg, abs_of_nonneg (sq_nonneg _)]

theorem vol_T3 : volume K.T3.carrier = ENNReal.ofReal (K.c * K.h * (K.b * K.c * K.p ^ 2) / 2) := by
  unfold T3; rw [vol_tri]
  congr 1
  have : det3 0 ((K.b + K.c) * K.p) (K.b * K.p) (K.c * K.p) 0 ((K.b + 2 * K.c) * K.p) = K.b * K.c * K.p ^ 2 := by
    unfold det3; ring
  rw [this, abs_of_nonneg (by have := K.hb; have := K.hc; positivity)]

theorem vol_TT : volume K.TT.carrier
    = ENNReal.ofReal (K.c * K.h * (((K.b + K.c) * K.p) * ((K.b + 2 * K.c) * K.p)) / 2) := by
  unfold TT; rw [vol_tri]
  congr 1
  have : det3 0 ((K.b + 2 * K.c) * K.p) ((K.b + K.c) * K.p) 0 0 0
      = -(((K.b + K.c) * K.p) * ((K.b + 2 * K.c) * K.p)) := by
    unfold det3; ring
  rw [this, abs_neg, abs_of_nonneg (by have := K.hb; have := K.hc; have := K.hp; positivity)]

theorem vol_sum : volume K.T1.carrier + volume K.T2.carrier + volume K.T3.carrier = volume K.TT.carrier := by
  rw [K.vol_T1, K.vol_T2, K.vol_T3, K.vol_TT]
  have hb := K.hb; have hc := K.hc; have hp := K.hp; have hh := K.hh
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

theorem vol_T3_eq : volume K.T3.carrier = ENNReal.ofReal (K.b * K.c * K.p ^ 2) * volume K.T0.carrier := by
  rw [K.vol_T3, K.vol_T0, ← ENNReal.ofReal_mul (by have := K.hb; have := K.hc; have := K.hp; positivity)]
  congr 1; ring

/-! ### separating lines -/

noncomputable def lf (x0 y0 x1 y1 : ℝ) : Plane →ᵃ[ℝ] ℝ :=
  lineFun (K.c * x0 + K.w * y0) (K.h * y0) (K.c * x1 + K.w * y1) (K.h * y1)

theorem lf_pt (x0 y0 x1 y1 x y : ℝ) : K.lf x0 y0 x1 y1 (K.pt x y) = K.c * K.h * det3 x0 y0 x1 y1 x y := by
  unfold lf pt
  rw [lineFun_apply]
  simp only [mkPt_zero, mkPt_one]
  unfold det3; ring

theorem forall_fin3 (P : Fin 3 → Prop) : (∀ k, P k) ↔ P 0 ∧ P 1 ∧ P 2 :=
  ⟨fun h => ⟨h 0, h 1, h 2⟩, fun ⟨a, b, c⟩ k => by fin_cases k <;> assumption⟩

theorem ge_of_pts {t : Tri} (f : Plane →ᵃ[ℝ] ℝ) {c : ℝ} (h : ∀ k, c ≤ f (t.pts k)) :
    ∀ x ∈ t.carrier, c ≤ f x := by
  have hconv : Convex ℝ (f ⁻¹' Set.Ici c) := (convex_Ici c).affine_preimage f
  have hsub : t.carrier ⊆ f ⁻¹' Set.Ici c :=
    convexHull_min (Set.range_subset_iff.mpr h) hconv
  exact fun x hx => hsub hx

theorem interiors_disjoint_sets {S U : Set Plane} (f : Plane →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0)
    (c : ℝ) (h1 : ∀ x ∈ S, f x ≤ c) (h2 : ∀ x ∈ U, c ≤ f x) :
    Disjoint (interior S) (interior U) := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  have hxt : x ∈ S := interior_subset hx1
  have hxu : x ∈ U := interior_subset hx2
  have hxc : f x = c := le_antisymm (h1 x hxt) (h2 x hxu)
  set g : Plane →ᵃ[ℝ] ℝ := AffineMap.const ℝ Plane c - f with hg
  have hglin : g.linear ≠ 0 := by
    intro hcon
    apply hf
    have : (AffineMap.const ℝ Plane c).linear - f.linear = 0 := hcon
    have hzero : (AffineMap.const ℝ Plane c).linear = 0 := rfl
    rw [hzero, zero_sub, neg_eq_zero] at this
    exact this
  have hgx : g x = 0 := by simp [hg, hxc]
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx1)
  obtain ⟨y, hy, hyneg⟩ := Erdos634.Geometry.exists_neg_near_of_affine_zero g hglin hgx hr
  have hyt : y ∈ S := hball hy
  have : c < f y := by
    have hgy : g y = c - f y := rfl
    rw [hgy] at hyneg
    linarith
  exact absurd (h1 y hyt) (not_le.mpr this)


/-! ### containment, separation, exact cover -/

theorem pt_combo (a b d x0 y0 x1 y1 x2 y2 : ℝ) :
    a • K.pt x0 y0 + b • K.pt x1 y1 + d • K.pt x2 y2
      = K.pt (a * x0 + b * x1 + d * x2) (a * y0 + b * y1 + d * y2) := by
  unfold pt
  ext i
  fin_cases i
  · simp [mkPt_zero]; ring
  · simp [mkPt_one]; ring

theorem vtx (T : Tri) (k : Fin 3) : T.pts k ∈ T.carrier := subset_convexHull ℝ _ ⟨k, rfl⟩

theorem sub_of_pts (T U : Tri) (h : ∀ k, T.pts k ∈ U.carrier) : T.carrier ⊆ U.carrier :=
  convexHull_min (Set.range_subset_iff.mpr h) (convex_convexHull ℝ _)

theorem F_mem : K.pt 0 ((K.b + K.c) * K.p) ∈ K.TT.carrier := by
  have hb := K.hb; have hc := K.hc; have hp := K.hp
  refine mem_carrier_of_combo K.TT _ ![(K.b + K.c) / (K.b + 2 * K.c), 0, K.c / (K.b + 2 * K.c)] ?_ ?_ ?_
  · simp; field_simp; ring
  · intro k; fin_cases k <;> simp <;> positivity
  · show _ = ((K.b + K.c) / (K.b + 2 * K.c)) • K.pt _ _ + (0 : ℝ) • K.pt _ _ + (K.c / (K.b + 2 * K.c)) • K.pt 0 0
    rw [K.pt_combo]
    congr 1
    · ring
    · field_simp; ring

theorem G_mem : K.pt (K.b * K.p) (K.c * K.p) ∈ K.TT.carrier := by
  have hb := K.hb; have hc := K.hc; have hp := K.hp
  refine mem_carrier_of_combo K.TT _
    ![K.c / (K.b + 2 * K.c), K.b / (K.b + K.c), K.c ^ 2 / ((K.b + K.c) * (K.b + 2 * K.c))] ?_ ?_ ?_
  · simp; field_simp; ring
  · intro k; fin_cases k <;> simp <;> positivity
  · show _ = (K.c / (K.b + 2 * K.c)) • K.pt _ _ + (K.b / (K.b + K.c)) • K.pt _ _
      + (K.c ^ 2 / ((K.b + K.c) * (K.b + 2 * K.c))) • K.pt 0 0
    rw [K.pt_combo]
    congr 1
    · field_simp; ring
    · field_simp; ring

theorem sub1 : K.T1.carrier ⊆ K.TT.carrier := by
  refine sub_of_pts _ _ ((forall_fin3 _).mpr ⟨?_, ?_, ?_⟩)
  · exact vtx K.TT 2
  · exact vtx K.TT 1
  · exact K.F_mem

theorem sub2 : K.T2.carrier ⊆ K.TT.carrier := by
  refine sub_of_pts _ _ ((forall_fin3 _).mpr ⟨?_, ?_, ?_⟩)
  · exact vtx K.TT 0
  · exact vtx K.TT 1
  · exact K.G_mem

theorem sub3 : K.T3.carrier ⊆ K.TT.carrier := by
  refine sub_of_pts _ _ ((forall_fin3 _).mpr ⟨?_, ?_, ?_⟩)
  · exact K.F_mem
  · exact K.G_mem
  · exact vtx K.TT 0

/-- the line `C F` : `T1` on the positive side, `T2 ∪ T3` on the nonpositive side -/
noncomputable def f1 : Plane →ᵃ[ℝ] ℝ := K.lf ((K.b + K.c) * K.p) 0 0 ((K.b + K.c) * K.p)
/-- the line `A G` : `T2` positive side, `T3` nonpositive -/
noncomputable def f2 : Plane →ᵃ[ℝ] ℝ := K.lf 0 ((K.b + 2 * K.c) * K.p) (K.b * K.p) (K.c * K.p)

theorem f1_lin : K.f1.linear ≠ 0 := by
  have hb := K.hb; have hc := K.hc; have hp := K.hp; have hh := K.hh
  unfold f1 lf
  apply lineFun_linear_ne_zero
  right
  have : K.h * 0 ≠ K.h * ((K.b + K.c) * K.p) := by
    intro h; have : K.h * ((K.b + K.c) * K.p) = 0 := by linarith
    have : 0 < K.h * ((K.b + K.c) * K.p) := by positivity
    linarith
  exact this

theorem f2_lin : K.f2.linear ≠ 0 := by
  have hb := K.hb; have hc := K.hc; have hp := K.hp; have hh := K.hh
  unfold f2 lf
  apply lineFun_linear_ne_zero
  right
  intro h
  have : K.h * ((K.b + 2 * K.c) * K.p) - K.h * (K.c * K.p) = 0 := by linarith
  have : 0 < K.h * ((K.b + 2 * K.c) * K.p) - K.h * (K.c * K.p) := by nlinarith [mul_pos hh hp, mul_pos (mul_pos hh hp) hb, mul_pos hh hc]
  linarith

theorem T1_f1 : ∀ x ∈ K.T1.carrier, 0 ≤ K.f1 x := by
  have := K.ch_pos
  have hs : 0 ≤ ((K.b + K.c) * K.p) ^ 2 := sq_nonneg _
  refine ge_of_pts K.f1 ((forall_fin3 _).mpr ⟨?_, ?_, ?_⟩)
  · show 0 ≤ K.lf _ _ _ _ (K.pt 0 0)
    rw [lf_pt]
    have : det3 ((K.b + K.c) * K.p) 0 0 ((K.b + K.c) * K.p) 0 0 = ((K.b + K.c) * K.p) ^ 2 := by unfold det3; ring
    rw [this]; positivity
  · show 0 ≤ K.lf _ _ _ _ (K.pt ((K.b + K.c) * K.p) 0)
    rw [lf_pt]
    have : det3 ((K.b + K.c) * K.p) 0 0 ((K.b + K.c) * K.p) ((K.b + K.c) * K.p) 0 = 0 := by unfold det3; ring
    rw [this]; simp
  · show 0 ≤ K.lf _ _ _ _ (K.pt 0 ((K.b + K.c) * K.p))
    rw [lf_pt]
    have : det3 ((K.b + K.c) * K.p) 0 0 ((K.b + K.c) * K.p) 0 ((K.b + K.c) * K.p) = 0 := by unfold det3; ring
    rw [this]; simp

theorem T2_f1 : ∀ x ∈ K.T2.carrier, K.f1 x ≤ 0 := by
  have := K.ch_pos
  have hb := K.hb; have hc := K.hc; have hp := K.hp
  refine le_of_forall_pts_le K.f1 ((forall_fin3 _).mpr ⟨?_, ?_, ?_⟩)
  · show K.lf _ _ _ _ (K.pt 0 ((K.b + 2 * K.c) * K.p)) ≤ 0
    rw [lf_pt]
    have : det3 ((K.b + K.c) * K.p) 0 0 ((K.b + K.c) * K.p) 0 ((K.b + 2 * K.c) * K.p)
        = -(((K.b + K.c) * K.p) * (K.c * K.p)) := by unfold det3; ring
    rw [this]
    have : 0 < K.c * K.h * (((K.b + K.c) * K.p) * (K.c * K.p)) := by positivity
    nlinarith
  · show K.lf _ _ _ _ (K.pt ((K.b + K.c) * K.p) 0) ≤ 0
    rw [lf_pt]
    have : det3 ((K.b + K.c) * K.p) 0 0 ((K.b + K.c) * K.p) ((K.b + K.c) * K.p) 0 = 0 := by unfold det3; ring
    rw [this]; simp
  · show K.lf _ _ _ _ (K.pt (K.b * K.p) (K.c * K.p)) ≤ 0
    rw [lf_pt]
    have : det3 ((K.b + K.c) * K.p) 0 0 ((K.b + K.c) * K.p) (K.b * K.p) (K.c * K.p) = 0 := by unfold det3; ring
    rw [this]; simp

theorem T3_f1 : ∀ x ∈ K.T3.carrier, K.f1 x ≤ 0 := by
  have := K.ch_pos
  have hb := K.hb; have hc := K.hc; have hp := K.hp
  refine le_of_forall_pts_le K.f1 ((forall_fin3 _).mpr ⟨?_, ?_, ?_⟩)
  · show K.lf _ _ _ _ (K.pt 0 ((K.b + K.c) * K.p)) ≤ 0
    rw [lf_pt]
    have : det3 ((K.b + K.c) * K.p) 0 0 ((K.b + K.c) * K.p) 0 ((K.b + K.c) * K.p) = 0 := by unfold det3; ring
    rw [this]; simp
  · show K.lf _ _ _ _ (K.pt (K.b * K.p) (K.c * K.p)) ≤ 0
    rw [lf_pt]
    have : det3 ((K.b + K.c) * K.p) 0 0 ((K.b + K.c) * K.p) (K.b * K.p) (K.c * K.p) = 0 := by unfold det3; ring
    rw [this]; simp
  · show K.lf _ _ _ _ (K.pt 0 ((K.b + 2 * K.c) * K.p)) ≤ 0
    rw [lf_pt]
    have : det3 ((K.b + K.c) * K.p) 0 0 ((K.b + K.c) * K.p) 0 ((K.b + 2 * K.c) * K.p)
        = -(((K.b + K.c) * K.p) * (K.c * K.p)) := by unfold det3; ring
    rw [this]
    have : 0 < K.c * K.h * (((K.b + K.c) * K.p) * (K.c * K.p)) := by positivity
    nlinarith

theorem T3_f2 : ∀ x ∈ K.T3.carrier, K.f2 x ≤ 0 := by
  have := K.ch_pos
  have hb := K.hb; have hc := K.hc; have hp := K.hp
  refine le_of_forall_pts_le K.f2 ((forall_fin3 _).mpr ⟨?_, ?_, ?_⟩)
  · show K.lf _ _ _ _ (K.pt 0 ((K.b + K.c) * K.p)) ≤ 0
    rw [lf_pt]
    have : det3 0 ((K.b + 2 * K.c) * K.p) (K.b * K.p) (K.c * K.p) 0 ((K.b + K.c) * K.p)
        = -(K.b * K.c * K.p ^ 2) := by unfold det3; ring
    rw [this]
    have : 0 < K.c * K.h * (K.b * K.c * K.p ^ 2) := by positivity
    nlinarith
  · show K.lf _ _ _ _ (K.pt (K.b * K.p) (K.c * K.p)) ≤ 0
    rw [lf_pt]
    have : det3 0 ((K.b + 2 * K.c) * K.p) (K.b * K.p) (K.c * K.p) (K.b * K.p) (K.c * K.p) = 0 := by unfold det3; ring
    rw [this]; simp
  · show K.lf _ _ _ _ (K.pt 0 ((K.b + 2 * K.c) * K.p)) ≤ 0
    rw [lf_pt]
    have : det3 0 ((K.b + 2 * K.c) * K.p) (K.b * K.p) (K.c * K.p) 0 ((K.b + 2 * K.c) * K.p) = 0 := by unfold det3; ring
    rw [this]; simp

theorem T2_f2 : ∀ x ∈ K.T2.carrier, 0 ≤ K.f2 x := by
  have := K.ch_pos
  have hb := K.hb; have hc := K.hc; have hp := K.hp
  refine ge_of_pts K.f2 ((forall_fin3 _).mpr ⟨?_, ?_, ?_⟩)
  · show 0 ≤ K.lf _ _ _ _ (K.pt 0 ((K.b + 2 * K.c) * K.p))
    rw [lf_pt]
    have : det3 0 ((K.b + 2 * K.c) * K.p) (K.b * K.p) (K.c * K.p) 0 ((K.b + 2 * K.c) * K.p) = 0 := by unfold det3; ring
    rw [this]; simp
  · show 0 ≤ K.lf _ _ _ _ (K.pt ((K.b + K.c) * K.p) 0)
    rw [lf_pt]
    have : det3 0 ((K.b + 2 * K.c) * K.p) (K.b * K.p) (K.c * K.p) ((K.b + K.c) * K.p) 0 = K.c ^ 2 * K.p ^ 2 := by
      unfold det3; ring
    rw [this]; positivity
  · show 0 ≤ K.lf _ _ _ _ (K.pt (K.b * K.p) (K.c * K.p))
    rw [lf_pt]
    have : det3 0 ((K.b + 2 * K.c) * K.p) (K.b * K.p) (K.c * K.p) (K.b * K.p) (K.c * K.p) = 0 := by unfold det3; ring
    rw [this]; simp

theorem disj_1_23 : Disjoint (interior K.T1.carrier) (interior (K.T2.carrier ∪ K.T3.carrier)) := by
  refine (interiors_disjoint_sets (S := K.T2.carrier ∪ K.T3.carrier) (U := K.T1.carrier) K.f1 K.f1_lin 0 ?_ K.T1_f1).symm
  rintro x (hx | hx)
  · exact K.T2_f1 x hx
  · exact K.T3_f1 x hx

theorem disj_23 : Disjoint (interior K.T2.carrier) (interior K.T3.carrier) :=
  (interiors_disjoint_sets (S := K.T3.carrier) (U := K.T2.carrier) K.f2 K.f2_lin 0 K.T3_f2 K.T2_f2).symm

theorem cover : K.T1.carrier ∪ (K.T2.carrier ∪ K.T3.carrier) = K.TT.carrier := by
  have d12 : Disjoint (interior K.T1.carrier) (interior K.T2.carrier) :=
    K.disj_1_23.mono_right (interior_mono Set.subset_union_left)
  have d13 : Disjoint (interior K.T1.carrier) (interior K.T3.carrier) :=
    K.disj_1_23.mono_right (interior_mono Set.subset_union_right)
  have hpw : Pairwise fun i j : Fin 3 => Disjoint (interior (![K.T1, K.T2, K.T3] i).carrier)
      (interior (![K.T1, K.T2, K.T3] j).carrier) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact d12
    · exact d13
    · exact d12.symm
    · exact absurd rfl hij
    · exact K.disj_23
    · exact d13.symm
    · exact K.disj_23.symm
    · exact absurd rfl hij
  have hsub : ∀ i, (![K.T1, K.T2, K.T3] i).carrier ⊆ K.TT.carrier := by
    intro i; fin_cases i
    · exact K.sub1
    · exact K.sub2
    · exact K.sub3
  have hv : ∑ i, volume (![K.T1, K.T2, K.T3] i).carrier = volume K.TT.carrier := by
    simp [Fin.sum_univ_three]; exact K.vol_sum
  have h := covers_of_volume_tri K.TT ![K.T1, K.T2, K.T3] hsub hpw hv
  rw [← h]
  ext x
  simp [Fin.exists_fin_succ, or_assoc]

end Cfg
end Erdos634.BeesonCor6Geom
