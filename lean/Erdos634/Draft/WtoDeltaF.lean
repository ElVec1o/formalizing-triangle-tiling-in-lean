-- Draft/WtoDeltaF.lean — L7 of (private working notes, not included) §3: W_m  ->  Delta_m for general f.  UNAUDITED.
-- Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
--
-- FRAME AND DEFINITION OF Delta_m (worked out here; differs from the scope-plan sketch).
--   Phi_f(s,t) = s g1 + t g2, |g1|=|g2|=1, g1.g2 = 1/(2f);  A = f(f^2-1), B = 2f^2-1, C = 3f^2-1.
--   W_m = Phi_f(Wt A B m) has vertices P=(Am,0), Q=(Am,Bm), R=(0,Bm)   (legs Bm, Am; hyp PR = f^3 m).
--   The scale-(fm) copy of the model tile (f, f^2-1, f^2) has sides (f^2, f(f^2-1), f^3)·m.  It is glued
--   to W_m along the side QR (length Am = f(f^2-1)m), on the far side from P, with its OBTUSE vertex
--   (cos = -1/(2f)) at Q — NOT along the hypotenuse PR.  The obtuse angle at Q is supplementary to
--   the W-angle at Q (cos 1/(2f)), so the tile's f^2 m side continues the line P-Q to T=(Am,Cm).
--   Delta_m := Phi_f(hull{P,T,R}), P=(Am,0), T=(Am,Cm), R=(0,Bm): the isosceles triangle with base
--   PT = (3f^2-1)m and legs PR = RT = f^3 m (f=2: base 11m, legs 8m; count 11 m^2 = `tileCount_eleven_sq`).
--   Delta_m = W_m  U  Q_m,   Q_m = Phi_f(hull{R,Q,T}) = scale (fm) tile, (fm)^2 tiles (ladder).
--   Count (2f^2-1)m^2 + f^2 m^2 = (3f^2-1) m^2.
-- PROVED HERE: WClosed f hf m  ->  Nonempty (RTiling (DeltaTri f hf m).carrier (MF f) ((3f^2-1)m^2)),
-- with the congruent-dissection form.  The Delta-additivity Delta m1 -> Delta m2 -> Delta (m1+m2) is NOT
-- proved here (it needs the parallelogram P_1, L8/L9).
import Erdos634.Draft.WAddF
import Erdos634.CellCoord

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Tset Rect RTiling.cast RTiling.castN interior_disj_fst interior_disj_snd)

namespace Erdos634.Draft.WtoDeltaF
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF
  Erdos634.Draft.WPgramF Erdos634.Draft.WGridF Erdos634.Draft.WAddF

/-! ## Region identities in skew coordinates -/

/-- `Delta` region, vertices `(u,0),(u,w),(0,v)`. -/
def DS (u v w : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ≤ u ∧ u * v ≤ v * p.1 + u * p.2 ∧ u * (p.2 - v) ≤ (w - v) * p.1}

/-- `Q` region, vertices `(0,v),(u,v),(u,w)`. -/
def QS (u v w : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ≤ u ∧ v ≤ p.2 ∧ u * (p.2 - v) ≤ (w - v) * p.1}

/-- `W` region in `(u,v)` form. -/
def WS (u v : ℝ) : Set (ℝ × ℝ) := {p | p.1 ≤ u ∧ p.2 ≤ v ∧ u * v ≤ v * p.1 + u * p.2}

theorem DS_convex (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hvw : v < w) : Convex ℝ (DS u v w) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨x1, x2, x3⟩ := hx
  obtain ⟨y1, y2, y3⟩ := hy
  have hb' : b = 1 - a := by linarith
  subst hb'
  simp only [DS, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left x1 ha, mul_le_mul_of_nonneg_left y1 hb]
  · nlinarith [mul_le_mul_of_nonneg_left x2 ha, mul_le_mul_of_nonneg_left y2 hb]
  · nlinarith [mul_le_mul_of_nonneg_left x3 ha, mul_le_mul_of_nonneg_left y3 hb]

theorem QS_convex (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hvw : v < w) : Convex ℝ (QS u v w) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨x1, x2, x3⟩ := hx
  obtain ⟨y1, y2, y3⟩ := hy
  have hb' : b = 1 - a := by linarith
  subst hb'
  simp only [QS, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left x1 ha, mul_le_mul_of_nonneg_left y1 hb]
  · nlinarith [mul_le_mul_of_nonneg_left x2 ha, mul_le_mul_of_nonneg_left y2 hb]
  · nlinarith [mul_le_mul_of_nonneg_left x3 ha, mul_le_mul_of_nonneg_left y3 hb]

theorem hull_DS (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hvw : v < w) :
    convexHull ℝ {((u : ℝ), (0 : ℝ)), (u, w), (0, v)} = DS u v w := by
  have hw : 0 < w := by linarith
  apply Set.Subset.antisymm
  · refine convexHull_min ?_ (DS_convex u v w hu hv hvw)
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨le_refl _, by simp; nlinarith, by simp; nlinarith⟩
    · exact ⟨le_refl _, by simp; nlinarith, by simp; nlinarith⟩
    · exact ⟨by simp; linarith, by simp, by simp⟩
  · intro p hp
    obtain ⟨h1, h2, h3⟩ := hp
    have hc := convex_convexHull ℝ ({((u : ℝ), (0 : ℝ)), (u, w), (0, v)} : Set (ℝ × ℝ))
    have hT : 0 ≤ (p.2 - v + v * p.1 / u) / w := by
      apply div_nonneg _ hw.le
      have : 0 ≤ v * p.1 / u + p.2 - v := by
        have : 0 ≤ (v * p.1 + u * p.2 - u * v) / u := div_nonneg (by linarith) hu.le
        have e : (v * p.1 + u * p.2 - u * v) / u = v * p.1 / u + p.2 - v := by field_simp
        linarith
      linarith
    have hP : 0 ≤ p.1 / u - (p.2 - v + v * p.1 / u) / w := by
      have : 0 ≤ ((w - v) * p.1 - u * (p.2 - v)) / (u * w) :=
        div_nonneg (by linarith) (by positivity)
      have e : ((w - v) * p.1 - u * (p.2 - v)) / (u * w)
          = p.1 / u - (p.2 - v + v * p.1 / u) / w := by field_simp; ring
      linarith
    have hR : 0 ≤ 1 - p.1 / u := by
      rw [sub_nonneg, div_le_one hu]; exact h1
    have := hc.sum_mem (t := (Finset.univ : Finset (Fin 3)))
      (w := ![p.1 / u - (p.2 - v + v * p.1 / u) / w, (p.2 - v + v * p.1 / u) / w, 1 - p.1 / u])
      (z := ![((u : ℝ), (0 : ℝ)), (u, w), (0, v)])
      (by intro i _; fin_cases i <;> simp [hP, hT, hR])
      (by simp [Fin.sum_univ_three])
      (by intro i _; fin_cases i <;> exact subset_convexHull ℝ _ (by simp))
    convert this using 1
    ext <;> simp [Fin.sum_univ_three] <;> field_simp <;> ring

theorem hull_QS (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hvw : v < w) :
    convexHull ℝ {((0 : ℝ), (v : ℝ)), (u, v), (u, w)} = QS u v w := by
  apply Set.Subset.antisymm
  · refine convexHull_min ?_ (QS_convex u v w hu hv hvw)
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨by simp; linarith, by simp, by simp⟩
    · exact ⟨le_refl _, by simp, by simp; nlinarith [mul_pos hu (sub_pos.mpr hvw)]⟩
    · exact ⟨le_refl _, by simp; linarith, by simp; nlinarith [mul_pos hu (sub_pos.mpr hvw)]⟩
  · intro p hp
    obtain ⟨h1, h2, h3⟩ := hp
    have hc := convex_convexHull ℝ ({((0 : ℝ), (v : ℝ)), (u, v), (u, w)} : Set (ℝ × ℝ))
    have hwv : 0 < w - v := by linarith
    have hT : 0 ≤ (p.2 - v) / (w - v) := div_nonneg (by linarith) hwv.le
    have hQ : 0 ≤ p.1 / u - (p.2 - v) / (w - v) := by
      have : 0 ≤ ((w - v) * p.1 - u * (p.2 - v)) / (u * (w - v)) :=
        div_nonneg (by linarith) (by positivity)
      have e : ((w - v) * p.1 - u * (p.2 - v)) / (u * (w - v))
          = p.1 / u - (p.2 - v) / (w - v) := by field_simp
      linarith
    have hR : 0 ≤ 1 - p.1 / u := by
      rw [sub_nonneg, div_le_one hu]; exact h1
    have := hc.sum_mem (t := (Finset.univ : Finset (Fin 3)))
      (w := ![1 - p.1 / u, p.1 / u - (p.2 - v) / (w - v), (p.2 - v) / (w - v)])
      (z := ![((0 : ℝ), (v : ℝ)), (u, v), (u, w)])
      (by intro i _; fin_cases i <;> simp [hQ, hT, hR])
      (by simp [Fin.sum_univ_three])
      (by intro i _; fin_cases i <;> exact subset_convexHull ℝ _ (by simp))
    convert this using 1
    ext <;> simp [Fin.sum_univ_three] <;> field_simp <;> ring

theorem DS_eq (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hvw : v < w) :
    DS u v w = WS u v ∪ QS u v w := by
  have hwv : 0 < w - v := by linarith
  ext p
  simp only [DS, WS, QS, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, b, c⟩
    by_cases hp : p.2 ≤ v
    · left; exact ⟨a, hp, b⟩
    · right; exact ⟨a, by linarith, c⟩
  · rintro (⟨a, b, c⟩ | ⟨a, b, c⟩)
    · have hp1 : 0 ≤ p.1 := by
        by_contra hneg
        push_neg at hneg
        nlinarith [mul_nonneg hu.le (sub_nonneg.mpr b), mul_pos hv (neg_pos.mpr hneg)]
      refine ⟨a, c, ?_⟩
      nlinarith [mul_nonneg hwv.le hp1, mul_nonneg hu.le (sub_nonneg.mpr b)]
    · have hp1 : 0 ≤ p.1 := by
        by_contra hneg
        push_neg at hneg
        nlinarith [mul_nonneg hu.le (sub_nonneg.mpr b), mul_pos hwv (neg_pos.mpr hneg)]
      refine ⟨a, ?_, c⟩
      nlinarith [mul_nonneg hv.le hp1, mul_nonneg hu.le (sub_nonneg.mpr b)]

/-! ## The two triangles -/

/-- `Delta`: `Phi_F hull{(u,0),(u,w),(0,v)}`. -/
noncomputable def DTriR (F : ℝ) (hF1 : 1 < F) (u v w : ℝ) (hu : 0 < u) (hw : 0 < w) : Tri :=
  triC F hF1 (u, 0) (u, w) (0, v) (by
    intro h; simp only [sub_self, zero_mul, sub_zero, zero_sub, neg_mul, neg_neg, zero_sub] at h
    nlinarith [mul_pos hu hw])

/-- `Q`: `Phi_F hull{(0,v),(u,v),(u,w)}`, vertices in the order R, Q, T. -/
noncomputable def QTriR (F : ℝ) (hF1 : 1 < F) (u v w : ℝ) (hu : 0 < u) (hvw : v < w) : Tri :=
  triC F hF1 (0, v) (u, v) (u, w) (by
    intro h; simp only [sub_zero, sub_self, mul_zero] at h
    nlinarith [mul_pos hu (sub_pos.mpr hvw)])

theorem carrier_DTriR (F : ℝ) (hF1 : 1 < F) (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hvw : v < w) :
    (DTriR F hF1 u v w hu (by linarith)).carrier = Phi F '' DS u v w := by
  rw [DTriR, carrier_triC, hull_DS u v w hu hv hvw]

theorem carrier_QTriR (F : ℝ) (hF1 : 1 < F) (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hvw : v < w) :
    (QTriR F hF1 u v w hu hvw).carrier = Phi F '' QS u v w := by
  rw [QTriR, carrier_triC, hull_QS u v w hu hv hvw]

/-! ## Ladder: the scale-`k` copy of a tile, as a `CongruentDissection` -/

open Erdos634.Subdivision in
theorem big_d01 (A B C : Plane) (h : AffineIndependent ℝ ![A, B, C]) (k : ℕ) (hk : 0 < k) :
    dist ((bigTri A B C h k hk).pts 0) ((bigTri A B C h k hk).pts 1) = k * dist A B := by
  rw [bigTri_pts0, bigTri_pts1, dist_eq_norm, dist_eq_norm]
  have : A - P A B C k 0 = (k : ℝ) • (A - B) := by simp only [P]; push_cast; module
  rw [this, norm_smul, Real.norm_natCast]

open Erdos634.Subdivision in
theorem big_d12 (A B C : Plane) (h : AffineIndependent ℝ ![A, B, C]) (k : ℕ) (hk : 0 < k) :
    dist ((bigTri A B C h k hk).pts 1) ((bigTri A B C h k hk).pts 2) = k * dist B C := by
  rw [bigTri_pts1, bigTri_pts2, dist_eq_norm, dist_eq_norm]
  have : P A B C k 0 - P A B C 0 k = (k : ℝ) • (B - C) := by simp only [P]; push_cast; module
  rw [this, norm_smul, Real.norm_natCast]

open Erdos634.Subdivision in
theorem big_d20 (A B C : Plane) (h : AffineIndependent ℝ ![A, B, C]) (k : ℕ) (hk : 0 < k) :
    dist ((bigTri A B C h k hk).pts 2) ((bigTri A B C h k hk).pts 0) = k * dist C A := by
  rw [bigTri_pts2, bigTri_pts0, dist_eq_norm, dist_eq_norm]
  have : P A B C 0 k - A = (k : ℝ) • (C - A) := by simp only [P]; push_cast; module
  rw [this, norm_smul, Real.norm_natCast]

theorem tri_eta (T : Tri) (h : AffineIndependent ℝ ![T.pts 0, T.pts 1, T.pts 2]) :
    (⟨![T.pts 0, T.pts 1, T.pts 2], h⟩ : Tri) = T := by
  cases T with
  | mk p ip => congr 1; funext i; fin_cases i <;> rfl

theorem indep_eta (T : Tri) : AffineIndependent ℝ ![T.pts 0, T.pts 1, T.pts 2] := by
  have := T.indep
  convert this using 1; funext i; fin_cases i <;> rfl

/-- `kT` is cut into `k²` copies of `T`. -/
noncomputable def ladderCD (T : Tri) (k : ℕ) (hk : 0 < k) : CongruentDissection (k * k) where
  toDissection := Erdos634.Subdivision.ladderDissection (T.pts 0) (T.pts 1) (T.pts 2)
    (indep_eta T) k hk
  model := T
  tiles_congruent := fun n => by
    have := Erdos634.Subdivision.ladderDissection_congruent (T.pts 0) (T.pts 1) (T.pts 2)
      (indep_eta T) k hk n
    rw [tri_eta T (indep_eta T)] at this
    exact this.symm

/-- Transport a `CongruentDissection` onto a congruent triangle's carrier (copy of
`WSeed.seed_of_cd`, to avoid importing the f = 2 certificate bridges). -/
theorem seed_of_cd {N : ℕ} (D : CongruentDissection N) (T : Tri) (M : Tri)
    (hT : D.target.Congruent T) (hM : D.model.Congruent M) : Nonempty (RTiling T.carrier M N) := by
  obtain ⟨g, σ, hg⟩ := hT
  have hcar : g '' D.target.carrier = T.carrier := by
    have h1 := Erdos634.DissectionMap.mapTri_carrier (Erdos634.Ladder.isoAff g) D.target
    simp only [Erdos634.Ladder.isoAff_coe] at h1
    rw [← h1]
    simp only [Tri.carrier]
    congr 1
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨σ k, by simp [Erdos634.DissectionMap.mapTri, Erdos634.Ladder.isoAff_coe, hg]⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨k, rfl⟩ := σ.surjective j
      exact ⟨k, by simp [Erdos634.DissectionMap.mapTri, Erdos634.Ladder.isoAff_coe, hg]⟩
  exact ⟨Erdos634.Draft.RegionTiling.remodel
    (RTiling.cast hcar (Erdos634.Draft.RegionTiling.map (ofCD D) g)) hM⟩

/-! ## General `f`: SSS for the scale-`(fm)` tile -/

theorem MF_pts (F : ℝ) (hF1 : 1 < F) :
    (MF F hF1).pts = ![Phi F (0, 0), Phi F (F ^ 2 - 1, 0), Phi F (F ^ 2 - 1, F)] := by
  simp only [MF, brickL, triC_pts]

theorem C_gt_B (f : ℕ) (hf : 2 ≤ f) :
    2 * (f : ℝ) ^ 2 - 1 < 3 * (f : ℝ) ^ 2 - 1 := by
  have := hF f hf; nlinarith

theorem hC_pos (f : ℕ) (hf : 2 ≤ f) : 0 < 3 * (f : ℝ) ^ 2 - 1 := by
  have := B_pos f hf; have := C_gt_B f hf; linarith

/-- **`Delta_m`** in the general-`f` frame: `Phi_f hull{(Am,0),(Am,Cm),(0,Bm)}`,
`A = f(f²-1)`, `B = 2f²-1`, `C = 3f²-1`. -/
noncomputable def DeltaTri (f : ℕ) (hf : 2 ≤ f) (m : ℕ) (hm : 0 < m) : Tri :=
  DTriR (f : ℝ) (hF f hf) ((f : ℝ) * ((f : ℝ) ^ 2 - 1) * m) ((2 * (f : ℝ) ^ 2 - 1) * m)
    ((3 * (f : ℝ) ^ 2 - 1) * m)
    (mul_pos (A_pos f hf) (by exact_mod_cast hm)) (mul_pos (hC_pos f hf) (by exact_mod_cast hm))

/-- The `Q` triangle `Phi_f hull{R,Q,T}`: the scale-`(fm)` model tile. -/
noncomputable def QTri (f : ℕ) (hf : 2 ≤ f) (m : ℕ) (hm : 0 < m) : Tri :=
  QTriR (f : ℝ) (hF f hf) ((f : ℝ) * ((f : ℝ) ^ 2 - 1) * m) ((2 * (f : ℝ) ^ 2 - 1) * m)
    ((3 * (f : ℝ) ^ 2 - 1) * m)
    (mul_pos (A_pos f hf) (by exact_mod_cast hm))
    (mul_lt_mul_of_pos_right (C_gt_B f hf) (by exact_mod_cast hm))

/-- `QTri` has the sides of `(fm)·MF`: it is congruent to the scale-`(fm)` ladder triangle. -/
theorem QTri_congruent (f : ℕ) (hf : 2 ≤ f) (m : ℕ) (hm : 0 < m) :
    ((ladderCD (MF (f : ℝ) (hF f hf)) (f * m) (Nat.mul_pos (by omega) hm)).target).Congruent
      (QTri f hf m hm) := by
  have h1 := hF f hf
  have hf0 : (f : ℝ) ≠ 0 := by positivity
  have hm0 : (m : ℝ) ≠ 0 := by have : (0 : ℝ) < m := by exact_mod_cast hm
                               exact this.ne'
  have tg : (ladderCD (MF (f : ℝ) h1) (f * m) (Nat.mul_pos (by omega) hm)).target
      = Erdos634.Subdivision.bigTri _ _ _ (indep_eta (MF (f : ℝ) h1)) (f * m)
          (Nat.mul_pos (by omega) hm) := rfl
  rw [tg]
  refine Erdos634.SssCongruent.congruent_of_dist_three ?_ ?_ ?_
  · rw [big_d01]
    refine Erdos634.Draft.SumTwoSquares.eqsq (by positivity) dist_nonneg ?_
    simp only [QTri, QTriR, triC_pts, MF_pts, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [mul_pow, sq_Phi h1, sq_Phi h1]
    push_cast
    field_simp; ring
  · rw [big_d12]
    refine Erdos634.Draft.SumTwoSquares.eqsq (by positivity) dist_nonneg ?_
    simp only [QTri, QTriR, triC_pts, MF_pts, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [mul_pow, sq_Phi h1, sq_Phi h1]
    push_cast
    field_simp; ring
  · rw [big_d20]
    refine Erdos634.Draft.SumTwoSquares.eqsq (by positivity) dist_nonneg ?_
    simp only [QTri, QTriR, triC_pts, MF_pts, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [mul_pow, sq_Phi h1, sq_Phi h1]
    push_cast
    field_simp; ring

theorem carrier_DeltaTri (f : ℕ) (hf : 2 ≤ f) (m : ℕ) (hm : 0 < m) :
    (DeltaTri f hf m hm).carrier = Phi (f : ℝ) '' DS ((f : ℝ) * ((f : ℝ) ^ 2 - 1) * m)
      ((2 * (f : ℝ) ^ 2 - 1) * m) ((3 * (f : ℝ) ^ 2 - 1) * m) :=
  carrier_DTriR _ _ _ _ _ (mul_pos (A_pos f hf) (by exact_mod_cast hm)) (mul_pos (B_pos f hf) (by exact_mod_cast hm))
    (mul_lt_mul_of_pos_right (C_gt_B f hf) (by exact_mod_cast hm))

theorem carrier_QTri (f : ℕ) (hf : 2 ≤ f) (m : ℕ) (hm : 0 < m) :
    (QTri f hf m hm).carrier = Phi (f : ℝ) '' QS ((f : ℝ) * ((f : ℝ) ^ 2 - 1) * m)
      ((2 * (f : ℝ) ^ 2 - 1) * m) ((3 * (f : ℝ) ^ 2 - 1) * m) :=
  carrier_QTriR _ _ _ _ _ (mul_pos (A_pos f hf) (by exact_mod_cast hm)) (mul_pos (B_pos f hf) (by exact_mod_cast hm))
    (mul_lt_mul_of_pos_right (C_gt_B f hf) (by exact_mod_cast hm))

/-- `WS` in `(Am, Bm)` form is `WAddF.Wt A B m`. -/
theorem WS_eq (A B m : ℝ) (hm : 0 < m) : WS (A * m) (B * m) = Wt A B m := by
  ext p
  simp only [WS, Wt, Set.mem_setOf_eq]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · intro h
    refine le_of_mul_le_mul_left ?_ hm
    nlinarith
  · intro h
    nlinarith [mul_le_mul_of_nonneg_left h hm.le]

/-- **The scale-`(fm)` model tile tiles `Q_m`** by `(fm)²` tiles (thm:ladder). -/
theorem Q_tiling (f : ℕ) (hf : 2 ≤ f) (m : ℕ) (hm : 0 < m) :
    Nonempty (RTiling (Phi (f : ℝ) '' QS ((f : ℝ) * ((f : ℝ) ^ 2 - 1) * m)
      ((2 * (f : ℝ) ^ 2 - 1) * m) ((3 * (f : ℝ) ^ 2 - 1) * m))
      (MF (f : ℝ) (hF f hf)) (f * m * (f * m))) := by
  have hk : 0 < f * m := Nat.mul_pos (by omega) hm
  have := seed_of_cd (ladderCD (MF (f : ℝ) (hF f hf)) (f * m) hk) (QTri f hf m hm)
    (MF (f : ℝ) (hF f hf)) (QTri_congruent f hf m hm) (Tri.Congruent.refl _)
  obtain ⟨R⟩ := this
  exact ⟨RTiling.cast (carrier_QTri f hf m hm) R⟩

/-- **L7.**  For `f ≥ 2`, `m ≥ 1`: a tiling of `W_m` by `(2f²-1)m²` copies of the model tile
`MF f` (= `(f, f²-1, f²)`) yields a tiling of `Delta_m` (`DeltaTri`) by `(3f²-1)m²` copies. -/
theorem delta_of_W (f : ℕ) (hf : 2 ≤ f) (m : ℕ) (hm : 1 ≤ m) (hW : WClosed f hf m) :
    Nonempty (RTiling (DeltaTri f hf m hm).carrier (MF (f : ℝ) (hF f hf))
      ((3 * f ^ 2 - 1) * m ^ 2)) := by
  have hm' : 0 < m := hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm'
  obtain ⟨RW⟩ := hW
  obtain ⟨RQ⟩ := Q_tiling f hf m hm'
  have hu : 0 < (f : ℝ) * ((f : ℝ) ^ 2 - 1) * m := mul_pos (A_pos f hf) hmR
  have hv : 0 < (2 * (f : ℝ) ^ 2 - 1) * m := mul_pos (B_pos f hf) hmR
  have hvw : (2 * (f : ℝ) ^ 2 - 1) * m < (3 * (f : ℝ) ^ 2 - 1) * m :=
    mul_lt_mul_of_pos_right (C_gt_B f hf) hmR
  have RW' : RTiling (Phi (f : ℝ) '' WS ((f : ℝ) * ((f : ℝ) ^ 2 - 1) * m)
      ((2 * (f : ℝ) ^ 2 - 1) * m)) (MF (f : ℝ) (hF f hf)) ((2 * f ^ 2 - 1) * m ^ 2) :=
    RTiling.cast (by rw [WS_eq _ _ _ hmR]) RW
  have hd : Disjoint (interior (Phi (f : ℝ) '' WS ((f : ℝ) * ((f : ℝ) ^ 2 - 1) * m)
        ((2 * (f : ℝ) ^ 2 - 1) * m)))
      (interior (Phi (f : ℝ) '' QS ((f : ℝ) * ((f : ℝ) ^ 2 - 1) * m)
        ((2 * (f : ℝ) ^ 2 - 1) * m) ((3 * (f : ℝ) ^ 2 - 1) * m))) :=
    disjoint_image (hF f hf) (interior_disj_snd ((2 * (f : ℝ) ^ 2 - 1) * m)
      (by rintro p ⟨_, b, _⟩; exact b) (by rintro p ⟨_, b, _⟩; exact b))
  have U := union RW' RQ hd
  refine ⟨RTiling.castN ?_ (RTiling.cast ?_ U)⟩
  · have h1 : 1 ≤ f ^ 2 := by nlinarith
    have h2 : 1 ≤ 2 * f ^ 2 := by omega
    have h3 : 1 ≤ 3 * f ^ 2 := by omega
    zify [h1, h2, h3]; ring
  · rw [← Set.image_union, carrier_DeltaTri, ← DS_eq _ _ _ hu hv hvw]

/-- Congruent-dissection form: `Delta_m` is the target of a `CongruentDissection` with `(3f²-1)m²`
tiles and model `MF f`. -/
theorem delta_cd_of_W (f : ℕ) (hf : 2 ≤ f) (m : ℕ) (hm : 1 ≤ m) (hW : WClosed f hf m) :
    ∃ D : CongruentDissection ((3 * f ^ 2 - 1) * m ^ 2),
      D.target = DeltaTri f hf m hm ∧ D.model = MF (f : ℝ) (hF f hf) := by
  obtain ⟨R⟩ := delta_of_W f hf m hm hW
  exact ⟨toCD R, rfl, rfl⟩

end Erdos634.Draft.WtoDeltaF

#print axioms Erdos634.Draft.WtoDeltaF.hull_DS
#print axioms Erdos634.Draft.WtoDeltaF.QTri_congruent
#print axioms Erdos634.Draft.WtoDeltaF.Q_tiling
#print axioms Erdos634.Draft.WtoDeltaF.delta_of_W
#print axioms Erdos634.Draft.WtoDeltaF.delta_cd_of_W
