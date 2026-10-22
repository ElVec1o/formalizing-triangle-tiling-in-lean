import Erdos634.Draft.ZhangThm7

/-!
# Beeson Theorem 14 (arXiv 1206.2229v4, Fig. 17 pattern), instance tile `(2,3,4)`

Tiling of the triangle with angles `(2 alpha, alpha, 2 beta)`, base `AC = l*c`, by the tile `(2,3,4)`,
`N = 77` tiles.  Coordinates `(x, w)` stand for the point `(x, sqrt 15 * w)`.  Generated from the
pattern of `BeesonFig17.lean` (same proofs, new numerals).  Credit Beeson (arXiv 1206.2229), Beeson-Zhang,
Zhang (arXiv 2512.22696), Laczkovich.  UNAUDITED.
-/
namespace Erdos634.BeesonT14.I_2_3_4

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.GlueCut Erdos634.SssCongruent Erdos634.ZhangL1 Erdos634.ZhangPara
  Erdos634.ZhangSporadic Erdos634.ZhangThm4

noncomputable def rt : ℝ := Real.sqrt 15
theorem rt_sq : rt * rt = 15 := Real.mul_self_sqrt (by norm_num)
theorem rt_pos : 0 < rt := Real.sqrt_pos.mpr (by norm_num)

/-- rational determinant -/
noncomputable def detR (x0 w0 x1 w1 x2 w2 : ℝ) : ℝ := (x1 - x0) * (w2 - w0) - (x2 - x0) * (w1 - w0)

theorem det3_rt (x0 w0 x1 w1 x2 w2 : ℝ) :
    det3 x0 (rt * w0) x1 (rt * w1) x2 (rt * w2) = rt * detR x0 w0 x1 w1 x2 w2 := by
  simp only [det3, detR]; ring

/-- points of the plane whose rational coordinates `(q 0, q 1 / sqrt 2)` satisfy `p`. -/
def RS (p : ℝ → ℝ → Prop) : Set Plane := {q | p (q 0) (q 1 / rt)}

theorem q1_eq (q : Plane) : rt * (q 1 / rt) = q 1 := by
  have := rt_pos.ne'; field_simp

theorem det3_q (q : Plane) (x1 w1 x2 w2 : ℝ) :
    det3 (q 0) (q 1) x1 (rt * w1) x2 (rt * w2) = rt * detR (q 0) (q 1 / rt) x1 w1 x2 w2 := by
  have := det3_rt (q 0) (q 1 / rt) x1 w1 x2 w2
  rwa [q1_eq] at this

theorem det3_q2 (q : Plane) (x0 w0 x2 w2 : ℝ) :
    det3 x0 (rt * w0) (q 0) (q 1) x2 (rt * w2) = rt * detR x0 w0 (q 0) (q 1 / rt) x2 w2 := by
  have := det3_rt x0 w0 (q 0) (q 1 / rt) x2 w2
  rwa [q1_eq] at this

theorem det3_q3 (q : Plane) (x0 w0 x1 w1 : ℝ) :
    det3 x0 (rt * w0) x1 (rt * w1) (q 0) (q 1) = rt * detR x0 w0 x1 w1 (q 0) (q 1 / rt) := by
  have := det3_rt x0 w0 x1 w1 (q 0) (q 1 / rt)
  rwa [q1_eq] at this

theorem TriSet_RS (x0 w0 x1 w1 x2 w2 : ℝ) :
    TriSet x0 (rt * w0) x1 (rt * w1) x2 (rt * w2) =
      RS (fun X W => 0 ≤ detR X W x1 w1 x2 w2 ∧ 0 ≤ detR x0 w0 X W x2 w2 ∧
        0 ≤ detR x0 w0 x1 w1 X W) := by
  ext q
  simp only [TriSet, RS, Set.mem_setOf_eq]
  rw [det3_q, det3_q2, det3_q3, mul_nonneg_iff_of_pos_left rt_pos,
    mul_nonneg_iff_of_pos_left rt_pos, mul_nonneg_iff_of_pos_left rt_pos]

theorem Dis_of_congr {R : Tri} {n : ℕ} (x0 y0 x1 y1 x2 y2 u0 v0 u1 v1 u2 v2 : ℝ)
    (hP : 0 < det3 x0 y0 x1 y1 x2 y2) (hQ : 0 < det3 u0 v0 u1 v1 u2 v2)
    (hc : (mkTri x0 y0 x1 y1 x2 y2 hP.ne').Congruent (mkTri u0 v0 u1 v1 u2 v2 hQ.ne'))
    (h : Dis R (TriSet x0 y0 x1 y1 x2 y2) n) : Dis R (TriSet u0 v0 u1 v1 u2 v2) n := by
  obtain ⟨C, hr, hm⟩ := h
  have hr' : C.region = (mkTri _ _ _ _ _ _ hP.ne').carrier := by
    rw [hr]; exact TriSet_eq_carrier hP
  obtain ⟨E, hE, hEm⟩ := Erdos634.Draft.CVCCevianCut.transport (C.toCongruentDissection _ hr') _ hc
  refine ⟨E.toRegion, ?_, hEm.trans hm⟩
  show E.target.carrier = _
  rw [hE]
  exact (TriSet_eq_carrier hQ).symm

/-! ### The tile and scaled copies -/

theorem hdet0 : 0 < det3 0 0 4 0 (21 / 8) ((3 / 8) * rt) := by
  have := rt_pos
  simp only [det3]; nlinarith

noncomputable def T0 : Tri := mkTri 0 0 4 0 (21 / 8) ((3 / 8) * rt) hdet0.ne'

/-- squared side table of the tile: `Dt i j` -/
noncomputable def Dt : Fin 3 → Fin 3 → ℝ := ![![0, 16, 9], ![16, 0, 4], ![9, 4, 0]]

theorem Dt_diag (i : Fin 3) : Dt i i = 0 := by fin_cases i <;> rfl
theorem Dt_symm (i j : Fin 3) : Dt i j = Dt j i := by fin_cases i <;> fin_cases j <;> rfl

theorem tile_scaled (m : ℕ) (hm : 0 < m) :
    Dis T0 (TriSet 0 0 (0 + m * (4 - 0)) (0 + m * (0 - 0)) (0 + m * ((21 / 8) - 0))
      (0 + m * ((3 / 8) * rt - 0))) (m * m) :=
  Dis_scaled 0 0 4 0 (21 / 8) ((3 / 8) * rt) hdet0 (Tri.Congruent.refl _) m hm _ _ _ _
    rfl rfl rfl rfl

theorem tile_scaled_dist (m : ℕ) (hdet : 0 < det3 0 0 (0 + m * (4 - 0)) (0 + m * (0 - 0))
      (0 + m * ((21 / 8) - 0)) (0 + m * ((3 / 8) * rt - 0))) (i j : Fin 3) :
    dist ((mkTri 0 0 (0 + m * (4 - 0)) (0 + m * (0 - 0)) (0 + m * ((21 / 8) - 0))
      (0 + m * ((3 / 8) * rt - 0)) hdet.ne').pts i)
      ((mkTri 0 0 (0 + m * (4 - 0)) (0 + m * (0 - 0)) (0 + m * ((21 / 8) - 0))
      (0 + m * ((3 / 8) * rt - 0)) hdet.ne').pts j) ^ 2 = m * m * Dt i j := by
  have hs := rt_sq
  fin_cases i <;> fin_cases j <;> simp [mkTri, dist_sq_mkPt, Dt] <;> nlinarith [hs]

theorem dsq (x0 w0 x1 w1 : ℝ) :
    (x0 - x1) ^ 2 + (rt * w0 - rt * w1) ^ 2 = (x1 - x0) ^ 2 + 15 * (w1 - w0) ^ 2 := by
  have hs := rt_sq
  linear_combination ((w0 - w1) ^ 2) * hs

set_option maxHeartbeats 1000000 in
theorem Dis_piece (m : ℕ) (hm : 0 < m) (σ : Equiv.Perm (Fin 3)) (x0 w0 x1 w1 x2 w2 : ℝ)
    (hdet : 0 < detR x0 w0 x1 w1 x2 w2)
    (h01 : (x1 - x0) ^ 2 + 15 * (w1 - w0) ^ 2 = m * m * Dt (σ 0) (σ 1))
    (h02 : (x2 - x0) ^ 2 + 15 * (w2 - w0) ^ 2 = m * m * Dt (σ 0) (σ 2))
    (h12 : (x2 - x1) ^ 2 + 15 * (w2 - w1) ^ 2 = m * m * Dt (σ 1) (σ 2)) :
    Dis T0 (TriSet x0 (rt * w0) x1 (rt * w1) x2 (rt * w2)) (m * m) := by
  have hs := rt_sq
  have hrt := rt_pos
  have hdP : 0 < det3 x0 (rt * w0) x1 (rt * w1) x2 (rt * w2) := by
    rw [det3_rt]; positivity
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hdQ : 0 < det3 0 0 (0 + m * (4 - 0)) (0 + m * (0 - 0)) (0 + m * ((21 / 8) - 0))
      (0 + m * ((3 / 8) * rt - 0)) := by
    simp only [det3]; nlinarith [mul_pos hm' hm', mul_pos (mul_pos hm' hm') hrt]
  refine Dis_of_congr _ _ _ _ _ _ _ _ _ _ _ _ hdQ hdP ?_ (tile_scaled m hm)
  refine congruent_of_sq_dist_perm σ.symm ?_
  intro i j
  have e := tile_scaled_dist m hdQ i j
  rw [e]
  have P0 : (mkTri x0 (rt * w0) x1 (rt * w1) x2 (rt * w2) hdP.ne').pts 0 = mkPt x0 (rt * w0) := rfl
  have P1 : (mkTri x0 (rt * w0) x1 (rt * w1) x2 (rt * w2) hdP.ne').pts 1 = mkPt x1 (rt * w1) := rfl
  have P2 : (mkTri x0 (rt * w0) x1 (rt * w1) x2 (rt * w2) hdP.ne').pts 2 = mkPt x2 (rt * w2) := rfl
  have d01 : dist (mkPt x0 (rt * w0)) (mkPt x1 (rt * w1)) ^ 2 = m * m * Dt (σ 0) (σ 1) := by
    rw [dist_sq_mkPt, dsq]; exact h01
  have d02 : dist (mkPt x0 (rt * w0)) (mkPt x2 (rt * w2)) ^ 2 = m * m * Dt (σ 0) (σ 2) := by
    rw [dist_sq_mkPt, dsq]; exact h02
  have d12 : dist (mkPt x1 (rt * w1)) (mkPt x2 (rt * w2)) ^ 2 = m * m * Dt (σ 1) (σ 2) := by
    rw [dist_sq_mkPt, dsq]; exact h12
  have d10 : dist (mkPt x1 (rt * w1)) (mkPt x0 (rt * w0)) ^ 2 = m * m * Dt (σ 1) (σ 0) := by
    rw [dist_comm, Dt_symm]; exact d01
  have d20 : dist (mkPt x2 (rt * w2)) (mkPt x0 (rt * w0)) ^ 2 = m * m * Dt (σ 2) (σ 0) := by
    rw [dist_comm, Dt_symm]; exact d02
  have d21 : dist (mkPt x2 (rt * w2)) (mkPt x1 (rt * w1)) ^ 2 = m * m * Dt (σ 2) (σ 1) := by
    rw [dist_comm, Dt_symm]; exact d12
  have d00 : dist (mkPt x0 (rt * w0)) (mkPt x0 (rt * w0)) ^ 2 = m * m * Dt (σ 0) (σ 0) := by
    rw [Dt_diag]; simp
  have d11 : dist (mkPt x1 (rt * w1)) (mkPt x1 (rt * w1)) ^ 2 = m * m * Dt (σ 1) (σ 1) := by
    rw [Dt_diag]; simp
  have d22 : dist (mkPt x2 (rt * w2)) (mkPt x2 (rt * w2)) ^ 2 = m * m * Dt (σ 2) (σ 2) := by
    rw [Dt_diag]; simp
  have key : ∀ a b : Fin 3, dist ((mkTri x0 (rt * w0) x1 (rt * w1) x2 (rt * w2) hdP.ne').pts a)
      ((mkTri x0 (rt * w0) x1 (rt * w1) x2 (rt * w2) hdP.ne').pts b) ^ 2
      = m * m * Dt (σ a) (σ b) := by
    intro a b
    match a, b with
    | 0, 0 => exact d00
    | 0, 1 => exact d01
    | 0, 2 => exact d02
    | 1, 0 => exact d10
    | 1, 1 => exact d11
    | 1, 2 => exact d12
    | 2, 0 => exact d20
    | 2, 1 => exact d21
    | 2, 2 => exact d22
  rw [key, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-! ### Gluing in rational coordinates -/

/-- line functional in rational coordinates -/
noncomputable def lnR (px pw qx qw X W : ℝ) : ℝ := (qx - px) * (W - pw) - (X - px) * (qw - pw)

theorem lineFun_rt (px pw qx qw : ℝ) (q : Plane) :
    lineFun px (rt * pw) qx (rt * qw) q = rt * lnR px pw qx qw (q 0) (q 1 / rt) := by
  obtain ⟨W, hW⟩ : ∃ W, W = q 1 / rt := ⟨_, rfl⟩
  have hq1 : q 1 = rt * W := by rw [hW]; have := rt_pos.ne'; field_simp
  rw [← hW, lineFun_apply, hq1]
  simp only [lnR]; ring

theorem glueR {R : Tri} {p1 p2 : ℝ → ℝ → Prop} {n1 n2 : ℕ} (h1 : Dis R (RS p1) n1)
    (h2 : Dis R (RS p2) n2) (px pw qx qw : ℝ) (hne : px ≠ qx ∨ pw ≠ qw)
    (hS1 : ∀ X W, p1 X W → lnR px pw qx qw X W ≤ 0)
    (hS2 : ∀ X W, p2 X W → 0 ≤ lnR px pw qx qw X W) :
    Dis R (RS (fun X W => p1 X W ∨ p2 X W)) (n1 + n2) := by
  have hrt := rt_pos
  have hne' : px ≠ qx ∨ rt * pw ≠ rt * qw := by
    rcases hne with h | h
    · exact Or.inl h
    · right; intro e; exact h (mul_left_cancel₀ hrt.ne' e)
  refine (Dis.glue_line h1 h2 px (rt * pw) qx (rt * qw) hne' ?_ ?_).congr ?_ rfl
  · intro q hq
    rw [lineFun_rt]
    have := hS1 _ _ hq
    nlinarith
  · intro q hq
    rw [lineFun_rt]
    have := hS2 _ _ hq
    nlinarith
  · ext q; rfl

theorem glueR_quad {R : Tri} {p1 p2 : ℝ → ℝ → Prop} {n1 n2 : ℕ} (h1 : Dis R (RS p1) n1)
    (h2 : Dis R (RS p2) n2) (px pw qx qw rx rw' sx sw : ℝ)
    (hne : px ≠ qx ∨ pw ≠ qw) (hne2 : rx ≠ sx ∨ rw' ≠ sw)
    (hS1 : ∀ X W, p1 X W → lnR px pw qx qw X W ≤ 0)
    (hS1' : ∀ X W, p1 X W → lnR rx rw' sx sw X W ≤ 0)
    (hS2 : ∀ X W, p2 X W → 0 ≤ lnR px pw qx qw X W ∨ 0 ≤ lnR rx rw' sx sw X W) :
    Dis R (RS (fun X W => p1 X W ∨ p2 X W)) (n1 + n2) := by
  have hrt := rt_pos
  have hne' : px ≠ qx ∨ rt * pw ≠ rt * qw := by
    rcases hne with h | h
    · exact Or.inl h
    · right; intro e; exact h (mul_left_cancel₀ hrt.ne' e)
  have hne2' : rx ≠ sx ∨ rt * rw' ≠ rt * sw := by
    rcases hne2 with h | h
    · exact Or.inl h
    · right; intro e; exact h (mul_left_cancel₀ hrt.ne' e)
  have hd : Disjoint (interior (RS p1)) (interior (RS p2)) := by
    refine (disjoint_quadrant (S := RS p2) (T := RS p1)
      (lineFun px (rt * pw) qx (rt * qw)) (lineFun rx (rt * rw') sx (rt * sw))
      (lineFun_linear_ne_zero hne') (lineFun_linear_ne_zero hne2') ?_ ?_ ?_).symm
    · intro q hq; rw [lineFun_rt]; have := hS1 _ _ hq; nlinarith
    · intro q hq; rw [lineFun_rt]; have := hS1' _ _ hq; nlinarith
    · intro q hq
      rcases hS2 _ _ hq with h | h
      · left; rw [lineFun_rt]; nlinarith
      · right; rw [lineFun_rt]; nlinarith
  refine (Dis.glue_disj h1 h2 hd).congr ?_ rfl
  ext q; rfl

/-! ### The parallelogram: `ja x (k-ja)` cells of two tiles each
Cell vectors `u = ((33 / 16), (-9 / 16))` (length `b`), `v = ((17 / 16), (7 / 16))` (length `a`), `|u-v| = c`, `det(u,v) = (3 / 2)`. -/

noncomputable def cxf (Ox Ow X W : ℝ) : ℝ := (X - Ox) * (7 / 16) - (W - Ow) * (17 / 16)
noncomputable def cyf (Ox Ow X W : ℝ) : ℝ := (33 / 16) * (W - Ow) - (-9 / 16) * (X - Ox)
def PgP (Ox Ow m n : ℝ) (X W : ℝ) : Prop :=
  0 ≤ cxf Ox Ow X W ∧ cxf Ox Ow X W ≤ (3 / 2) * m ∧ 0 ≤ cyf Ox Ow X W ∧ cyf Ox Ow X W ≤ (3 / 2) * n

def sg1 : Equiv.Perm (Fin 3) := ⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩
def sg2 : Equiv.Perm (Fin 3) := ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩

theorem cell_dis (Ox Ow : ℝ) : Dis T0 (RS (PgP Ox Ow 1 1)) 2 := by
  have t1 := Dis_piece 1 one_pos sg1 Ox Ow (Ox + (33 / 16)) (Ow + (-9 / 16)) (Ox + (17 / 16))
    (Ow + (7 / 16))
    (by simp only [detR]; nlinarith)
    (by simp [sg1, Dt]; ring) (by simp [sg1, Dt]; ring) (by simp [sg1, Dt]; ring)
  have t2 := Dis_piece 1 one_pos sg2 (Ox + (33 / 16)) (Ow + (-9 / 16)) (Ox + (33 / 16) + (17 / 16))
    (Ow + (-9 / 16) + (7 / 16)) (Ox + (17 / 16)) (Ow + (7 / 16))
    (by simp only [detR]; nlinarith)
    (by simp [sg2, Dt]; ring) (by simp [sg2, Dt]; ring) (by simp [sg2, Dt]; ring)
  rw [TriSet_RS] at t1 t2
  have g := glueR t2 t1 (Ox + (33 / 16)) (Ow + (-9 / 16)) (Ox + (17 / 16)) (Ow + (7 / 16))
    (Or.inl (by intro h; linarith))
    (fun X W h => by obtain ⟨a1, a2, a3⟩ := h; simp only [detR, lnR] at *; linarith)
    (fun X W h => by obtain ⟨a1, a2, a3⟩ := h; simp only [detR, lnR] at *; linarith)
  refine g.congr ?_ (by norm_num)
  ext q
  simp only [RS, Set.mem_setOf_eq]
  constructor
  · rintro (⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩) <;> simp only [detR, PgP, cxf, cyf] at * <;>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · intro h
    simp only [PgP, cxf, cyf] at h
    rcases le_total (((q 0 - Ox) * (7 / 16) - (q 1 / rt - Ow) * (17 / 16)) +
        ((33 / 16) * (q 1 / rt - Ow) - (-9 / 16) * (q 0 - Ox))) (3 / 2) with h' | h'
    · right; simp only [detR]; refine ⟨?_, ?_, ?_⟩ <;> linarith [h.1, h.2.2.1]
    · left; simp only [detR]; refine ⟨?_, ?_, ?_⟩ <;> linarith [h.2.1, h.2.2.2]

theorem strip_dis (n : ℕ) : ∀ Ox Ow : ℝ,
    Dis T0 (RS (PgP Ox Ow 1 ((n + 1 : ℕ) : ℝ))) (2 * (n + 1)) := by
  induction n with
  | zero => intro Ox Ow; exact (cell_dis Ox Ow).congr (by simp) (by norm_num)
  | succ n ih =>
    intro Ox Ow
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have g := glueR (ih Ox Ow)
      (cell_dis (Ox + ((n + 1 : ℕ) : ℝ) * (17 / 16)) (Ow + ((n + 1 : ℕ) : ℝ) * (7 / 16)))
      (Ox + ((n + 1 : ℕ) : ℝ) * (17 / 16)) (Ow + ((n + 1 : ℕ) : ℝ) * (7 / 16))
      (Ox + ((n + 1 : ℕ) : ℝ) * (17 / 16) + (33 / 16))
      (Ow + ((n + 1 : ℕ) : ℝ) * (7 / 16) + (-9 / 16))
      (Or.inl (by intro h; linarith))
      (fun X W h => by
        obtain ⟨a1, a2, a3, a4⟩ := h
        simp only [PgP, cxf, cyf, lnR] at *; push_cast at *; linarith)
      (fun X W h => by
        obtain ⟨a1, a2, a3, a4⟩ := h
        simp only [PgP, cxf, cyf, lnR] at *; push_cast at *; linarith)
    refine g.congr ?_ (by push_cast; ring)
    ext q
    simp only [RS, Set.mem_setOf_eq]
    constructor
    · rintro (h | h) <;> simp only [PgP, cxf, cyf] at * <;> push_cast at * <;>
        refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]
    · intro h
      simp only [PgP, cxf, cyf] at h
      push_cast at h
      rcases le_total ((33 / 16) * (q 1 / rt - Ow) - (-9 / 16) * (q 0 - Ox))
        ((3 / 2) * ((n : ℝ) + 1)) with h' | h'
      · left; simp only [PgP, cxf, cyf]; push_cast
        refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]
      · right; simp only [PgP, cxf, cyf]; push_cast
        refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]

theorem grid_dis (n m : ℕ) : ∀ Ox Ow : ℝ,
    Dis T0 (RS (PgP Ox Ow ((m + 1 : ℕ) : ℝ) ((n + 1 : ℕ) : ℝ))) (2 * (m + 1) * (n + 1)) := by
  induction m with
  | zero => intro Ox Ow; exact (strip_dis n Ox Ow).congr (by simp) (by ring)
  | succ m ih =>
    intro Ox Ow
    have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have g := glueR (strip_dis n (Ox + ((m + 1 : ℕ) : ℝ) * (33 / 16))
        (Ow + ((m + 1 : ℕ) : ℝ) * (-9 / 16))) (ih Ox Ow)
      (Ox + ((m + 1 : ℕ) : ℝ) * (33 / 16)) (Ow + ((m + 1 : ℕ) : ℝ) * (-9 / 16))
      (Ox + ((m + 1 : ℕ) : ℝ) * (33 / 16) + (17 / 16))
      (Ow + ((m + 1 : ℕ) : ℝ) * (-9 / 16) + (7 / 16))
      (Or.inl (by intro h; linarith))
      (fun X W h => by
        obtain ⟨a1, a2, a3, a4⟩ := h
        simp only [PgP, cxf, cyf, lnR] at *; push_cast at *; linarith)
      (fun X W h => by
        obtain ⟨a1, a2, a3, a4⟩ := h
        simp only [PgP, cxf, cyf, lnR] at *; push_cast at *; linarith)
    refine g.congr ?_ (by push_cast; ring)
    ext q
    simp only [RS, Set.mem_setOf_eq]
    constructor
    · rintro (h | h) <;> simp only [PgP, cxf, cyf] at * <;> push_cast at * <;>
        refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]
    · intro h
      simp only [PgP, cxf, cyf] at h
      push_cast at h
      rcases le_total ((q 0 - Ox) * (7 / 16) - (q 1 / rt - Ow) * (17 / 16))
        ((3 / 2) * ((m : ℝ) + 1)) with h' | h'
      · right; simp only [PgP, cxf, cyf]; push_cast
        refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]
      · left; simp only [PgP, cxf, cyf]; push_cast
        refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]

/-! ### The seven pieces and the assembly -/

noncomputable def TriR (x0 w0 x1 w1 x2 w2 : ℝ) : ℝ → ℝ → Prop := fun X W =>
  0 ≤ detR X W x1 w1 x2 w2 ∧ 0 ≤ detR x0 w0 X W x2 w2 ∧ 0 ≤ detR x0 w0 x1 w1 X W

def sg0 : Equiv.Perm (Fin 3) := ⟨![0, 1, 2], ![0, 1, 2], by decide, by decide⟩
def sg3 : Equiv.Perm (Fin 3) := ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩
def sg4 : Equiv.Perm (Fin 3) := ⟨![0, 2, 1], ![0, 2, 1], by decide, by decide⟩
def sg5 : Equiv.Perm (Fin 3) := ⟨![2, 1, 0], ![2, 1, 0], by decide, by decide⟩

theorem Dis_pieceR (m : ℕ) (hm : 0 < m) (σ : Equiv.Perm (Fin 3)) (x0 w0 x1 w1 x2 w2 : ℝ)
    (hdet : 0 < detR x0 w0 x1 w1 x2 w2)
    (h01 : (x1 - x0) ^ 2 + 15 * (w1 - w0) ^ 2 = m * m * Dt (σ 0) (σ 1))
    (h02 : (x2 - x0) ^ 2 + 15 * (w2 - w0) ^ 2 = m * m * Dt (σ 0) (σ 2))
    (h12 : (x2 - x1) ^ 2 + 15 * (w2 - w1) ^ 2 = m * m * Dt (σ 1) (σ 2)) :
    Dis T0 (RS (TriR x0 w0 x1 w1 x2 w2)) (m * m) :=
  (Dis_piece m hm σ x0 w0 x1 w1 x2 w2 hdet h01 h02 h12).congr (TriSet_RS _ _ _ _ _ _) rfl

theorem blue_dis : Dis T0 (RS (TriR 0 0 16 0 (21 / 2) (3 / 2))) (4 * 4) :=
  Dis_pieceR 4 (by norm_num) sg0 _ _ _ _ _ _ (by simp only [detR]; norm_num)
    (by simp [sg0, Dt]; norm_num) (by simp [sg0, Dt]; norm_num) (by simp [sg0, Dt]; norm_num)

theorem pink_dis : Dis T0 (RS (TriR 16 0 (135 / 8) (33 / 8) (21 / 2) (3 / 2))) (4 * 4) :=
  Dis_pieceR 4 (by norm_num) sg3 _ _ _ _ _ _ (by simp only [detR]; norm_num)
    (by simp [sg3, Dt]; norm_num) (by simp [sg3, Dt]; norm_num) (by simp [sg3, Dt]; norm_num)

theorem green_dis : Dis T0 (RS (TriR 0 0 (21 / 2) (3 / 2) (17 / 2) (7 / 2))) (4 * 4) :=
  Dis_pieceR 4 (by norm_num) sg4 _ _ _ _ _ _ (by simp only [detR]; norm_num)
    (by simp [sg4, Dt]; norm_num) (by simp [sg4, Dt]; norm_num) (by simp [sg4, Dt]; norm_num)

theorem yellow_dis : Dis T0 (RS (TriR (21 / 2) (3 / 2) (101 / 8) (19 / 8) (17 / 2) (7 / 2))) (2 * 2) :=
  Dis_pieceR 2 (by norm_num) sg2 _ _ _ _ _ _ (by simp only [detR]; norm_num)
    (by simp [sg2, Dt]; norm_num) (by simp [sg2, Dt]; norm_num) (by simp [sg2, Dt]; norm_num)

theorem top_dis : Dis T0 (RS (TriR (51 / 4) (21 / 4) (135 / 8) (33 / 8) (561 / 32) (231 / 32))) (3 * 3) :=
  Dis_pieceR 3 (by norm_num) sg5 _ _ _ _ _ _ (by simp only [detR]; norm_num)
    (by simp [sg5, Dt]; norm_num) (by simp [sg5, Dt]; norm_num) (by simp [sg5, Dt]; norm_num)

theorem orange_dis : Dis T0 (RS (PgP (17 / 2) (7 / 2) 2 4)) 16 :=
  (grid_dis 3 1 (17 / 2) (7 / 2)).congr (by norm_num) (by norm_num)

noncomputable def G1 : ℝ → ℝ → Prop := fun X W =>
  PgP (17 / 2) (7 / 2) 2 4 X W ∨ TriR (51 / 4) (21 / 4) (135 / 8) (33 / 8) (561 / 32) (231 / 32) X W
noncomputable def G2 : ℝ → ℝ → Prop := fun X W =>
  TriR (21 / 2) (3 / 2) (101 / 8) (19 / 8) (17 / 2) (7 / 2) X W ∨ G1 X W
noncomputable def G3 : ℝ → ℝ → Prop := fun X W => G2 X W ∨ TriR 0 0 (21 / 2) (3 / 2) (17 / 2) (7 / 2) X W
noncomputable def G4 : ℝ → ℝ → Prop := fun X W =>
  TriR 16 0 (135 / 8) (33 / 8) (21 / 2) (3 / 2) X W ∨ G3 X W
noncomputable def G5 : ℝ → ℝ → Prop := fun X W => TriR 0 0 16 0 (21 / 2) (3 / 2) X W ∨ G4 X W

theorem g1_dis : Dis T0 (RS G1) (16 + 3 * 3) :=
  glueR orange_dis top_dis (51 / 4) (21 / 4) (135 / 8) (33 / 8) (Or.inl (by norm_num))
    (by rintro X W ⟨a1, a2, a3, a4⟩; simp only [lnR, PgP, cxf, cyf] at *; linarith)
    (by rintro X W ⟨a1, a2, a3⟩; simp only [lnR, detR] at *; linarith)

theorem g2_dis : Dis T0 (RS G2) (2 * 2 + (16 + 3 * 3)) :=
  glueR yellow_dis g1_dis (17 / 2) (7 / 2) (101 / 8) (19 / 8) (Or.inl (by norm_num))
    (by rintro X W ⟨a1, a2, a3⟩; simp only [lnR, detR] at *; linarith)
    (by
      rintro X W (⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3⟩) <;> simp only [lnR, detR, PgP, cxf, cyf] at * <;>
        linarith)

theorem g3_dis : Dis T0 (RS G3) (2 * 2 + (16 + 3 * 3) + 4 * 4) :=
  glueR g2_dis green_dis (21 / 2) (3 / 2) (17 / 2) (7 / 2) (Or.inl (by norm_num))
    (by
      rintro X W (⟨a1, a2, a3⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3⟩) <;>
        simp only [lnR, detR, PgP, cxf, cyf] at * <;> linarith)
    (by rintro X W ⟨a1, a2, a3⟩; simp only [lnR, detR] at *; linarith)

theorem g4_dis : Dis T0 (RS G4) (4 * 4 + (2 * 2 + (16 + 3 * 3) + 4 * 4)) :=
  glueR pink_dis g3_dis (21 / 2) (3 / 2) (135 / 8) (33 / 8) (Or.inl (by norm_num))
    (by rintro X W ⟨a1, a2, a3⟩; simp only [lnR, detR] at *; linarith)
    (by
      rintro X W ((⟨a1, a2, a3⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3⟩) | ⟨a1, a2, a3⟩) <;>
        simp only [lnR, detR, PgP, cxf, cyf] at * <;> linarith)

theorem g5_dis : Dis T0 (RS G5) (4 * 4 + (4 * 4 + (2 * 2 + (16 + 3 * 3) + 4 * 4))) := by
  refine glueR_quad blue_dis g4_dis 0 0 (21 / 2) (3 / 2) (21 / 2) (3 / 2) 16 0 (Or.inl (by norm_num))
    (Or.inl (by norm_num)) ?_ ?_ ?_
  · rintro X W ⟨a1, a2, a3⟩; simp only [lnR, detR] at *; linarith
  · rintro X W ⟨a1, a2, a3⟩; simp only [lnR, detR] at *; linarith
  · rintro X W (⟨a1, a2, a3⟩ | (⟨a1, a2, a3⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3⟩) | ⟨a1, a2, a3⟩) <;>
      simp only [lnR, detR, PgP, cxf, cyf] at * <;> first | (left; linarith) | (right; linarith)

set_option maxHeartbeats 8000000 in
theorem G5_iff (X W : ℝ) : G5 X W ↔ TriR 0 0 16 0 (561 / 32) (231 / 32) X W := by
  constructor
  · rintro (⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ((⟨a1, a2, a3⟩ | (⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3⟩)) | ⟨a1, a2, a3⟩))
    all_goals
      simp only [TriR, detR, PgP, cxf, cyf] at *
      refine ⟨?_, ?_, ?_⟩ <;> linarith
  · intro h
    simp only [TriR, detR] at h
    obtain ⟨h1, h2, h3⟩ := h
    rcases le_total 0 (lnR 0 0 (21 / 2) (3 / 2) X W) with f1 | f1 <;>
    rcases le_total 0 (lnR (21 / 2) (3 / 2) 16 0 X W) with f2 | f2 <;>
    rcases le_total 0 (lnR (21 / 2) (3 / 2) (17 / 2) (7 / 2) X W) with f3 | f3 <;>
    rcases le_total 0 (lnR (21 / 2) (3 / 2) (135 / 8) (33 / 8) X W) with f4 | f4 <;>
    rcases le_total 0 (lnR (17 / 2) (7 / 2) (101 / 8) (19 / 8) X W) with f5 | f5 <;>
    rcases le_total 0 (lnR (51 / 4) (21 / 4) (135 / 8) (33 / 8) X W) with f6 | f6 <;>
    simp only [G5, G4, G3, G2, G1, TriR, PgP, cxf, cyf, detR, lnR] at * <;>
    first
    | (left; refine ⟨?_, ?_, ?_⟩ <;> linarith)
    | (right; left; refine ⟨?_, ?_, ?_⟩ <;> linarith)
    | (right; right; right; refine ⟨?_, ?_, ?_⟩ <;> linarith)
    | (right; right; left; left; refine ⟨?_, ?_, ?_⟩ <;> linarith)
    | (right; right; left; right; left; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith)
    | (right; right; left; right; right; refine ⟨?_, ?_, ?_⟩ <;> linarith)
    | (exfalso; linarith)

/-- **Beeson Theorem 14, instance `(2,3,4)` (UNAUDITED):** the triangle
`A = (0,0)`, `C = (16,0)`, `B = ((561 / 32), sqrt 15 * (231 / 32))` (angles `(2 alpha, alpha, 2 beta)` at `A, B, C`,
`|AB| = 33`) is tiled by `77` copies of the tile `(2,3,4)`:
`3*4^2 + 2^2 + 3^2 + 2*4*2`. -/
theorem beeson_t14_2_3_4 :
    Dis T0 (TriSet 0 (rt * 0) 16 (rt * 0) (561 / 32) (rt * (231 / 32))) 77 := by
  have h := g5_dis
  rw [TriSet_RS]
  refine h.congr ?_ (by norm_num)
  ext q
  exact G5_iff _ _

end Erdos634.BeesonT14.I_2_3_4
