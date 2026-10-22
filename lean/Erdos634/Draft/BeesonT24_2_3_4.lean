import Erdos634.Draft.ZhangThm7

/-!
# Beeson Theorem 24 (arXiv 1206.2229v4), instance tile `(2,3,4)`, `lambda = 1`, `rho = 2`

An isosceles triangle with base angles `alpha + beta` (base `72`, legs `144`) tiled by `1728` copies of the
tile `(2,3,4)` (`3 alpha + 2 beta = pi`), by the construction in the proof of Theorem 24:
green `T(p)`, blue `T(q)`, yellow `T(u)`, red `T(t)` and pink `T(v)` triangles, the parallelogram `P C R Q`
(`t x r` cells) and the parallelogram `G R L V` (`x` strips).  Coordinates `(x, w)` stand for the point
`(x, sqrt 15 * w)`.  Same machinery as `BeesonFig17.lean` plus the multi-line gluing `glueM`.
Credit Beeson (arXiv 1206.2229), Beeson-Zhang, Zhang (arXiv 2512.22696), Laczkovich.  UNAUDITED.
-/
namespace Erdos634.BeesonT24.I_2_3_4

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


theorem glueM {R : Tri} {p1 p2 : ℝ → ℝ → Prop} {n1 n2 : ℕ} (h1 : Dis R (RS p1) n1)
    (h2 : Dis R (RS p2) n2) (ls : List (ℝ × ℝ × ℝ × ℝ))
    (hne : ∀ l ∈ ls, l.1 ≠ l.2.2.1 ∨ l.2.1 ≠ l.2.2.2)
    (hS1 : ∀ X W, p1 X W → ∃ l ∈ ls, lnR l.1 l.2.1 l.2.2.1 l.2.2.2 X W ≤ 0)
    (hS2 : ∀ X W, p2 X W → ∀ l ∈ ls, 0 ≤ lnR l.1 l.2.1 l.2.2.1 l.2.2.2 X W) :
    Dis R (RS (fun X W => p1 X W ∨ p2 X W)) (n1 + n2) := by
  have hrt := rt_pos
  have hd : Disjoint (interior (RS p1)) (interior (RS p2)) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    have key : ∀ l ∈ ls, 0 < lnR l.1 l.2.1 l.2.2.1 l.2.2.2 (x 0) (x 1 / rt) := by
      intro l hl
      have hne' : l.2.2.1 ≠ l.1 ∨ rt * l.2.2.2 ≠ rt * l.2.1 := by
        rcases hne l hl with h | h
        · exact Or.inl (Ne.symm h)
        · right; intro e; exact h (mul_left_cancel₀ hrt.ne' e).symm
      have hf := lineFun_linear_ne_zero (px := l.2.2.1) (py := rt * l.2.2.2) (qx := l.1)
        (qy := rt * l.2.1) hne'
      have := lt_of_mem_interior (lineFun l.2.2.1 (rt * l.2.2.2) l.1 (rt * l.2.1)) hf
        (T := RS p2) (fun y hy => by
          rw [lineFun_rt]
          have := hS2 _ _ hy l hl
          have e : lnR l.2.2.1 l.2.2.2 l.1 l.2.1 (y 0) (y 1 / rt)
              = - lnR l.1 l.2.1 l.2.2.1 l.2.2.2 (y 0) (y 1 / rt) := by simp only [lnR]; ring
          rw [e]; nlinarith) hx2
      rw [lineFun_rt] at this
      have e : lnR l.2.2.1 l.2.2.2 l.1 l.2.1 (x 0) (x 1 / rt)
          = - lnR l.1 l.2.1 l.2.2.1 l.2.2.2 (x 0) (x 1 / rt) := by simp only [lnR]; ring
      rw [e] at this
      nlinarith
    have hx1a : x ∈ RS p1 := interior_subset hx1
    have hx1' : p1 (x 0) (x 1 / rt) := hx1a
    obtain ⟨l, hl, hle⟩ := hS1 _ _ hx1'
    have := key l hl
    linarith
  refine (Dis.glue_disj h1 h2 hd).congr ?_ rfl
  ext q; rfl

def sg_012 : Equiv.Perm (Fin 3) := ⟨![0, 1, 2], ![0, 1, 2], by decide, by decide⟩
def sg_120 : Equiv.Perm (Fin 3) := ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩
def sg_210 : Equiv.Perm (Fin 3) := ⟨![2, 1, 0], ![2, 1, 0], by decide, by decide⟩
def sg_021 : Equiv.Perm (Fin 3) := ⟨![0, 2, 1], ![0, 2, 1], by decide, by decide⟩
def sg_201 : Equiv.Perm (Fin 3) := ⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩

/-! ### The parallelogram: `ja x (k-ja)` cells of two tiles each
Cell vectors `u = (2, 0)` (length `b`), `v = ((-3 / 4), (3 / 4))` (length `a`), `|u-v| = c`, `det(u,v) = (3 / 2)`. -/

noncomputable def cxf1 (Ox Ow X W : ℝ) : ℝ := (X - Ox) * (3 / 4) - (W - Ow) * (-3 / 4)
noncomputable def cyf1 (Ox Ow X W : ℝ) : ℝ := 2 * (W - Ow) - 0 * (X - Ox)
def PgP1 (Ox Ow m n : ℝ) (X W : ℝ) : Prop :=
  0 ≤ cxf1 Ox Ow X W ∧ cxf1 Ox Ow X W ≤ (3 / 2) * m ∧ 0 ≤ cyf1 Ox Ow X W ∧ cyf1 Ox Ow X W ≤ (3 / 2) * n


theorem cell_dis1 (Ox Ow : ℝ) : Dis T0 (RS (PgP1 Ox Ow 1 1)) 2 := by
  have t1 := Dis_piece 1 one_pos sg_210 Ox Ow (Ox + 2) (Ow + 0) (Ox + (-3 / 4))
    (Ow + (3 / 4))
    (by simp only [detR]; nlinarith)
    (by simp [sg_210, Dt]; ring) (by simp [sg_210, Dt]; ring) (by simp [sg_210, Dt]; ring)
  have t2 := Dis_piece 1 one_pos sg_021 (Ox + 2) (Ow + 0) (Ox + 2 + (-3 / 4))
    (Ow + 0 + (3 / 4)) (Ox + (-3 / 4)) (Ow + (3 / 4))
    (by simp only [detR]; nlinarith)
    (by simp [sg_021, Dt]; ring) (by simp [sg_021, Dt]; ring) (by simp [sg_021, Dt]; ring)
  rw [TriSet_RS] at t1 t2
  have g := glueR t2 t1 (Ox + 2) (Ow + 0) (Ox + (-3 / 4)) (Ow + (3 / 4))
    (Or.inl (by intro h; linarith))
    (fun X W h => by obtain ⟨a1, a2, a3⟩ := h; simp only [detR, lnR] at *; linarith)
    (fun X W h => by obtain ⟨a1, a2, a3⟩ := h; simp only [detR, lnR] at *; linarith)
  refine g.congr ?_ (by norm_num)
  ext q
  simp only [RS, Set.mem_setOf_eq]
  constructor
  · rintro (⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩) <;> simp only [detR, PgP1, cxf1, cyf1] at * <;>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · intro h
    simp only [PgP1, cxf1, cyf1] at h
    rcases le_total (((q 0 - Ox) * (3 / 4) - (q 1 / rt - Ow) * (-3 / 4)) +
        (2 * (q 1 / rt - Ow) - 0 * (q 0 - Ox))) (3 / 2) with h' | h'
    · right; simp only [detR]; refine ⟨?_, ?_, ?_⟩ <;> linarith [h.1, h.2.2.1]
    · left; simp only [detR]; refine ⟨?_, ?_, ?_⟩ <;> linarith [h.2.1, h.2.2.2]

theorem strip_dis1 (n : ℕ) : ∀ Ox Ow : ℝ,
    Dis T0 (RS (PgP1 Ox Ow 1 ((n + 1 : ℕ) : ℝ))) (2 * (n + 1)) := by
  induction n with
  | zero => intro Ox Ow; exact (cell_dis1 Ox Ow).congr (by simp) (by norm_num)
  | succ n ih =>
    intro Ox Ow
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have g := glueR (ih Ox Ow)
      (cell_dis1 (Ox + ((n + 1 : ℕ) : ℝ) * (-3 / 4)) (Ow + ((n + 1 : ℕ) : ℝ) * (3 / 4)))
      (Ox + ((n + 1 : ℕ) : ℝ) * (-3 / 4)) (Ow + ((n + 1 : ℕ) : ℝ) * (3 / 4))
      (Ox + ((n + 1 : ℕ) : ℝ) * (-3 / 4) + 2)
      (Ow + ((n + 1 : ℕ) : ℝ) * (3 / 4) + 0)
      (Or.inl (by intro h; linarith))
      (fun X W h => by
        obtain ⟨a1, a2, a3, a4⟩ := h
        simp only [PgP1, cxf1, cyf1, lnR] at *; push_cast at *; linarith)
      (fun X W h => by
        obtain ⟨a1, a2, a3, a4⟩ := h
        simp only [PgP1, cxf1, cyf1, lnR] at *; push_cast at *; linarith)
    refine g.congr ?_ (by push_cast; ring)
    ext q
    simp only [RS, Set.mem_setOf_eq]
    constructor
    · rintro (h | h) <;> simp only [PgP1, cxf1, cyf1] at * <;> push_cast at * <;>
        refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]
    · intro h
      simp only [PgP1, cxf1, cyf1] at h
      push_cast at h
      rcases le_total (2 * (q 1 / rt - Ow) - 0 * (q 0 - Ox))
        ((3 / 2) * ((n : ℝ) + 1)) with h' | h'
      · left; simp only [PgP1, cxf1, cyf1]; push_cast
        refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]
      · right; simp only [PgP1, cxf1, cyf1]; push_cast
        refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]

theorem grid_dis1 (n m : ℕ) : ∀ Ox Ow : ℝ,
    Dis T0 (RS (PgP1 Ox Ow ((m + 1 : ℕ) : ℝ) ((n + 1 : ℕ) : ℝ))) (2 * (m + 1) * (n + 1)) := by
  induction m with
  | zero => intro Ox Ow; exact (strip_dis1 n Ox Ow).congr (by simp) (by ring)
  | succ m ih =>
    intro Ox Ow
    have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have g := glueR (strip_dis1 n (Ox + ((m + 1 : ℕ) : ℝ) * 2)
        (Ow + ((m + 1 : ℕ) : ℝ) * 0)) (ih Ox Ow)
      (Ox + ((m + 1 : ℕ) : ℝ) * 2) (Ow + ((m + 1 : ℕ) : ℝ) * 0)
      (Ox + ((m + 1 : ℕ) : ℝ) * 2 + (-3 / 4))
      (Ow + ((m + 1 : ℕ) : ℝ) * 0 + (3 / 4))
      (Or.inl (by intro h; linarith))
      (fun X W h => by
        obtain ⟨a1, a2, a3, a4⟩ := h
        simp only [PgP1, cxf1, cyf1, lnR] at *; push_cast at *; linarith)
      (fun X W h => by
        obtain ⟨a1, a2, a3, a4⟩ := h
        simp only [PgP1, cxf1, cyf1, lnR] at *; push_cast at *; linarith)
    refine g.congr ?_ (by push_cast; ring)
    ext q
    simp only [RS, Set.mem_setOf_eq]
    constructor
    · rintro (h | h) <;> simp only [PgP1, cxf1, cyf1] at * <;> push_cast at * <;>
        refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]
    · intro h
      simp only [PgP1, cxf1, cyf1] at h
      push_cast at h
      rcases le_total ((q 0 - Ox) * (3 / 4) - (q 1 / rt - Ow) * (-3 / 4))
        ((3 / 2) * ((m : ℝ) + 1)) with h' | h'
      · right; simp only [PgP1, cxf1, cyf1]; push_cast
        refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]
      · left; simp only [PgP1, cxf1, cyf1]; push_cast
        refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]


/-! ### The parallelogram: `ja x (k-ja)` cells of two tiles each
Cell vectors `u = (3, 0)` (length `b`), `v = ((-1 / 2), (1 / 2))` (length `a`), `|u-v| = c`, `det(u,v) = (3 / 2)`. -/

noncomputable def cxf2 (Ox Ow X W : ℝ) : ℝ := (X - Ox) * (1 / 2) - (W - Ow) * (-1 / 2)
noncomputable def cyf2 (Ox Ow X W : ℝ) : ℝ := 3 * (W - Ow) - 0 * (X - Ox)
def PgP2 (Ox Ow m n : ℝ) (X W : ℝ) : Prop :=
  0 ≤ cxf2 Ox Ow X W ∧ cxf2 Ox Ow X W ≤ (3 / 2) * m ∧ 0 ≤ cyf2 Ox Ow X W ∧ cyf2 Ox Ow X W ≤ (3 / 2) * n


theorem cell_dis2 (Ox Ow : ℝ) : Dis T0 (RS (PgP2 Ox Ow 1 1)) 2 := by
  have t1 := Dis_piece 1 one_pos sg_201 Ox Ow (Ox + 3) (Ow + 0) (Ox + (-1 / 2))
    (Ow + (1 / 2))
    (by simp only [detR]; nlinarith)
    (by simp [sg_201, Dt]; ring) (by simp [sg_201, Dt]; ring) (by simp [sg_201, Dt]; ring)
  have t2 := Dis_piece 1 one_pos sg_120 (Ox + 3) (Ow + 0) (Ox + 3 + (-1 / 2))
    (Ow + 0 + (1 / 2)) (Ox + (-1 / 2)) (Ow + (1 / 2))
    (by simp only [detR]; nlinarith)
    (by simp [sg_120, Dt]; ring) (by simp [sg_120, Dt]; ring) (by simp [sg_120, Dt]; ring)
  rw [TriSet_RS] at t1 t2
  have g := glueR t2 t1 (Ox + 3) (Ow + 0) (Ox + (-1 / 2)) (Ow + (1 / 2))
    (Or.inl (by intro h; linarith))
    (fun X W h => by obtain ⟨a1, a2, a3⟩ := h; simp only [detR, lnR] at *; linarith)
    (fun X W h => by obtain ⟨a1, a2, a3⟩ := h; simp only [detR, lnR] at *; linarith)
  refine g.congr ?_ (by norm_num)
  ext q
  simp only [RS, Set.mem_setOf_eq]
  constructor
  · rintro (⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩) <;> simp only [detR, PgP2, cxf2, cyf2] at * <;>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · intro h
    simp only [PgP2, cxf2, cyf2] at h
    rcases le_total (((q 0 - Ox) * (1 / 2) - (q 1 / rt - Ow) * (-1 / 2)) +
        (3 * (q 1 / rt - Ow) - 0 * (q 0 - Ox))) (3 / 2) with h' | h'
    · right; simp only [detR]; refine ⟨?_, ?_, ?_⟩ <;> linarith [h.1, h.2.2.1]
    · left; simp only [detR]; refine ⟨?_, ?_, ?_⟩ <;> linarith [h.2.1, h.2.2.2]

theorem strip_dis2 (n : ℕ) : ∀ Ox Ow : ℝ,
    Dis T0 (RS (PgP2 Ox Ow 1 ((n + 1 : ℕ) : ℝ))) (2 * (n + 1)) := by
  induction n with
  | zero => intro Ox Ow; exact (cell_dis2 Ox Ow).congr (by simp) (by norm_num)
  | succ n ih =>
    intro Ox Ow
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have g := glueR (ih Ox Ow)
      (cell_dis2 (Ox + ((n + 1 : ℕ) : ℝ) * (-1 / 2)) (Ow + ((n + 1 : ℕ) : ℝ) * (1 / 2)))
      (Ox + ((n + 1 : ℕ) : ℝ) * (-1 / 2)) (Ow + ((n + 1 : ℕ) : ℝ) * (1 / 2))
      (Ox + ((n + 1 : ℕ) : ℝ) * (-1 / 2) + 3)
      (Ow + ((n + 1 : ℕ) : ℝ) * (1 / 2) + 0)
      (Or.inl (by intro h; linarith))
      (fun X W h => by
        obtain ⟨a1, a2, a3, a4⟩ := h
        simp only [PgP2, cxf2, cyf2, lnR] at *; push_cast at *; linarith)
      (fun X W h => by
        obtain ⟨a1, a2, a3, a4⟩ := h
        simp only [PgP2, cxf2, cyf2, lnR] at *; push_cast at *; linarith)
    refine g.congr ?_ (by push_cast; ring)
    ext q
    simp only [RS, Set.mem_setOf_eq]
    constructor
    · rintro (h | h) <;> simp only [PgP2, cxf2, cyf2] at * <;> push_cast at * <;>
        refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]
    · intro h
      simp only [PgP2, cxf2, cyf2] at h
      push_cast at h
      rcases le_total (3 * (q 1 / rt - Ow) - 0 * (q 0 - Ox))
        ((3 / 2) * ((n : ℝ) + 1)) with h' | h'
      · left; simp only [PgP2, cxf2, cyf2]; push_cast
        refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]
      · right; simp only [PgP2, cxf2, cyf2]; push_cast
        refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]

theorem grid_dis2 (n m : ℕ) : ∀ Ox Ow : ℝ,
    Dis T0 (RS (PgP2 Ox Ow ((m + 1 : ℕ) : ℝ) ((n + 1 : ℕ) : ℝ))) (2 * (m + 1) * (n + 1)) := by
  induction m with
  | zero => intro Ox Ow; exact (strip_dis2 n Ox Ow).congr (by simp) (by ring)
  | succ m ih =>
    intro Ox Ow
    have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have g := glueR (strip_dis2 n (Ox + ((m + 1 : ℕ) : ℝ) * 3)
        (Ow + ((m + 1 : ℕ) : ℝ) * 0)) (ih Ox Ow)
      (Ox + ((m + 1 : ℕ) : ℝ) * 3) (Ow + ((m + 1 : ℕ) : ℝ) * 0)
      (Ox + ((m + 1 : ℕ) : ℝ) * 3 + (-1 / 2))
      (Ow + ((m + 1 : ℕ) : ℝ) * 0 + (1 / 2))
      (Or.inl (by intro h; linarith))
      (fun X W h => by
        obtain ⟨a1, a2, a3, a4⟩ := h
        simp only [PgP2, cxf2, cyf2, lnR] at *; push_cast at *; linarith)
      (fun X W h => by
        obtain ⟨a1, a2, a3, a4⟩ := h
        simp only [PgP2, cxf2, cyf2, lnR] at *; push_cast at *; linarith)
    refine g.congr ?_ (by push_cast; ring)
    ext q
    simp only [RS, Set.mem_setOf_eq]
    constructor
    · rintro (h | h) <;> simp only [PgP2, cxf2, cyf2] at * <;> push_cast at * <;>
        refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]
    · intro h
      simp only [PgP2, cxf2, cyf2] at h
      push_cast at h
      rcases le_total ((q 0 - Ox) * (1 / 2) - (q 1 / rt - Ow) * (-1 / 2))
        ((3 / 2) * ((m : ℝ) + 1)) with h' | h'
      · right; simp only [PgP2, cxf2, cyf2]; push_cast
        refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]
      · left; simp only [PgP2, cxf2, cyf2]; push_cast
        refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]


/-! ### The pieces -/

noncomputable def TriR (x0 w0 x1 w1 x2 w2 : ℝ) : ℝ → ℝ → Prop := fun X W =>
  0 ≤ detR X W x1 w1 x2 w2 ∧ 0 ≤ detR x0 w0 X W x2 w2 ∧ 0 ≤ detR x0 w0 x1 w1 X W

theorem Dis_pieceR (m : ℕ) (hm : 0 < m) (σ : Equiv.Perm (Fin 3)) (x0 w0 x1 w1 x2 w2 : ℝ)
    (hdet : 0 < detR x0 w0 x1 w1 x2 w2)
    (h01 : (x1 - x0) ^ 2 + 15 * (w1 - w0) ^ 2 = m * m * Dt (σ 0) (σ 1))
    (h02 : (x2 - x0) ^ 2 + 15 * (w2 - w0) ^ 2 = m * m * Dt (σ 0) (σ 2))
    (h12 : (x2 - x1) ^ 2 + 15 * (w2 - w1) ^ 2 = m * m * Dt (σ 1) (σ 2)) :
    Dis T0 (RS (TriR x0 w0 x1 w1 x2 w2)) (m * m) :=
  (Dis_piece m hm σ x0 w0 x1 w1 x2 w2 hdet h01 h02 h12).congr (TriSet_RS _ _ _ _ _ _) rfl


theorem green_dis : Dis T0 (RS (TriR 0 0 64 0 42 6)) (16 * 16) :=
  Dis_pieceR 16 (by norm_num) sg_012 _ _ _ _ _ _ (by simp only [detR]; norm_num)
    (by simp [sg_012, Dt]; norm_num) (by simp [sg_012, Dt]; norm_num) (by simp [sg_012, Dt]; norm_num)


theorem blue_dis : Dis T0 (RS (TriR 0 0 42 6 24 24)) (24 * 24) :=
  Dis_pieceR 24 (by norm_num) sg_120 _ _ _ _ _ _ (by simp only [detR]; norm_num)
    (by simp [sg_120, Dt]; norm_num) (by simp [sg_120, Dt]; norm_num) (by simp [sg_120, Dt]; norm_num)


theorem red_dis : Dis T0 (RS (TriR 64 0 58 6 42 6)) (8 * 8) :=
  Dis_pieceR 8 (by norm_num) sg_021 _ _ _ _ _ _ (by simp only [detR]; norm_num)
    (by simp [sg_021, Dt]; norm_num) (by simp [sg_021, Dt]; norm_num) (by simp [sg_021, Dt]; norm_num)


theorem pcrq_dis : Dis T0 (RS (PgP1 64 0 4 8)) 64 :=
  (grid_dis1 7 3 64 0).congr (by norm_num) (by norm_num)


theorem grlv_dis : Dis T0 (RS (PgP2 42 6 8 28)) 448 :=
  (grid_dis2 27 7 42 6).congr (by norm_num) (by norm_num)


theorem pink_dis : Dis T0 (RS (TriR 24 24 28 20 52 20)) (8 * 8) :=
  Dis_pieceR 8 (by norm_num) sg_120 _ _ _ _ _ _ (by simp only [detR]; norm_num)
    (by simp [sg_120, Dt]; norm_num) (by simp [sg_120, Dt]; norm_num) (by simp [sg_120, Dt]; norm_num)


theorem yellow_dis : Dis T0 (RS (TriR 24 24 52 20 36 36)) (16 * 16) :=
  Dis_pieceR 16 (by norm_num) sg_210 _ _ _ _ _ _ (by simp only [detR]; norm_num)
    (by simp [sg_210, Dt]; norm_num) (by simp [sg_210, Dt]; norm_num) (by simp [sg_210, Dt]; norm_num)


noncomputable def G1 : ℝ → ℝ → Prop := fun X W => TriR 0 0 64 0 42 6 X W
noncomputable def G2 : ℝ → ℝ → Prop := fun X W =>
  G1 X W ∨ TriR 0 0 42 6 24 24 X W
noncomputable def G3 : ℝ → ℝ → Prop := fun X W =>
  G2 X W ∨ TriR 64 0 58 6 42 6 X W
noncomputable def G4 : ℝ → ℝ → Prop := fun X W =>
  G3 X W ∨ PgP1 64 0 4 8 X W
noncomputable def G5 : ℝ → ℝ → Prop := fun X W =>
  G4 X W ∨ PgP2 42 6 8 28 X W
noncomputable def G6 : ℝ → ℝ → Prop := fun X W =>
  G5 X W ∨ TriR 24 24 28 20 52 20 X W
noncomputable def G7 : ℝ → ℝ → Prop := fun X W =>
  G6 X W ∨ TriR 24 24 52 20 36 36 X W


theorem g2_dis : Dis T0 (RS G2) ((16 * 16) + (24 * 24)) :=
  glueM green_dis blue_dis [(0, 0, 42, 6)]
    (by intro l hl; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
        rcases hl with rfl <;> norm_num)
    (by
      intro X W h
      simp only [G1] at h
      rcases h with ⟨a1, a2, a3⟩
      · exact ⟨(0, 0, 42, 6), by simp, by
          show lnR 0 0 42 6 X W ≤ 0
          simp only [detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *; linarith⟩)
    (by
      intro X W h l hl
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
      rcases hl with rfl <;>
      · simp only [detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *; obtain ⟨b1, b2, b3⟩ := h; linarith)

theorem g3_dis : Dis T0 (RS G3) ((16 * 16) + (24 * 24) + (8 * 8)) :=
  glueM g2_dis red_dis [(42, 6, 64, 0), (42, 6, 0, 0)]
    (by intro l hl; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl <;> norm_num)
    (by
      intro X W h
      simp only [G2, G1] at h
      rcases h with (⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩)
      · exact ⟨(42, 6, 64, 0), by simp, by
          show lnR 42 6 64 0 X W ≤ 0
          simp only [detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *; linarith⟩
      · exact ⟨(42, 6, 0, 0), by simp, by
          show lnR 42 6 0 0 X W ≤ 0
          simp only [detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *; linarith⟩)
    (by
      intro X W h l hl
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;>
      · simp only [detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *; obtain ⟨b1, b2, b3⟩ := h; linarith)

theorem g4_dis : Dis T0 (RS G4) ((16 * 16) + (24 * 24) + (8 * 8) + (64)) :=
  glueM g3_dis pcrq_dis [(42, 6, 64, 0), (42, 6, 0, 0), (58, 6, 64, 0)]
    (by intro l hl; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl <;> norm_num)
    (by
      intro X W h
      simp only [G3, G2, G1] at h
      rcases h with ((⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩) | ⟨a1, a2, a3⟩)
      · exact ⟨(42, 6, 64, 0), by simp, by
          show lnR 42 6 64 0 X W ≤ 0
          simp only [detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *; linarith⟩
      · exact ⟨(42, 6, 0, 0), by simp, by
          show lnR 42 6 0 0 X W ≤ 0
          simp only [detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *; linarith⟩
      · exact ⟨(58, 6, 64, 0), by simp, by
          show lnR 58 6 64 0 X W ≤ 0
          simp only [detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *; linarith⟩)
    (by
      intro X W h l hl
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl <;>
      · simp only [detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *; obtain ⟨b1, b2, b3, b4⟩ := h; linarith)

theorem g5_dis : Dis T0 (RS G5) ((16 * 16) + (24 * 24) + (8 * 8) + (64) + (448)) :=
  glueM g4_dis grlv_dis [(42, 6, 64, 0), (24, 24, 42, 6), (42, 6, 58, 6), (58, 6, 66, 6)]
    (by intro l hl; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl | rfl <;> norm_num)
    (by
      intro X W h
      simp only [G4, G3, G2, G1] at h
      rcases h with (((⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩) | ⟨a1, a2, a3⟩) | ⟨a1, a2, a3, a4⟩)
      · exact ⟨(42, 6, 64, 0), by simp, by
          show lnR 42 6 64 0 X W ≤ 0
          simp only [detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *; linarith⟩
      · exact ⟨(24, 24, 42, 6), by simp, by
          show lnR 24 24 42 6 X W ≤ 0
          simp only [detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *; linarith⟩
      · exact ⟨(42, 6, 58, 6), by simp, by
          show lnR 42 6 58 6 X W ≤ 0
          simp only [detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *; linarith⟩
      · exact ⟨(58, 6, 66, 6), by simp, by
          show lnR 58 6 66 6 X W ≤ 0
          simp only [detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *; linarith⟩)
    (by
      intro X W h l hl
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl | rfl <;>
      · simp only [detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *; obtain ⟨b1, b2, b3, b4⟩ := h; linarith)

theorem g6_dis : Dis T0 (RS G6) ((16 * 16) + (24 * 24) + (8 * 8) + (64) + (448) + (8 * 8)) :=
  glueM g5_dis pink_dis [(42, 6, 64, 0), (24, 24, 42, 6), (42, 6, 58, 6), (58, 6, 66, 6), (28, 20, 52, 20)]
    (by intro l hl; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl | rfl | rfl <;> norm_num)
    (by
      intro X W h
      simp only [G5, G4, G3, G2, G1] at h
      rcases h with ((((⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩) | ⟨a1, a2, a3⟩) | ⟨a1, a2, a3, a4⟩) | ⟨a1, a2, a3, a4⟩)
      · exact ⟨(42, 6, 64, 0), by simp, by
          show lnR 42 6 64 0 X W ≤ 0
          simp only [detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *; linarith⟩
      · exact ⟨(24, 24, 42, 6), by simp, by
          show lnR 24 24 42 6 X W ≤ 0
          simp only [detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *; linarith⟩
      · exact ⟨(42, 6, 58, 6), by simp, by
          show lnR 42 6 58 6 X W ≤ 0
          simp only [detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *; linarith⟩
      · exact ⟨(58, 6, 66, 6), by simp, by
          show lnR 58 6 66 6 X W ≤ 0
          simp only [detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *; linarith⟩
      · exact ⟨(28, 20, 52, 20), by simp, by
          show lnR 28 20 52 20 X W ≤ 0
          simp only [detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *; linarith⟩)
    (by
      intro X W h l hl
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl | rfl | rfl <;>
      · simp only [detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *; obtain ⟨b1, b2, b3⟩ := h; linarith)

theorem g7_dis : Dis T0 (RS G7) ((16 * 16) + (24 * 24) + (8 * 8) + (64) + (448) + (8 * 8) + (16 * 16)) :=
  glueM g6_dis yellow_dis [(42, 6, 64, 0), (24, 24, 42, 6), (42, 6, 58, 6), (58, 6, 66, 6), (28, 20, 52, 20), (24, 24, 52, 20)]
    (by intro l hl; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num)
    (by
      intro X W h
      simp only [G6, G5, G4, G3, G2, G1] at h
      rcases h with (((((⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩) | ⟨a1, a2, a3⟩) | ⟨a1, a2, a3, a4⟩) | ⟨a1, a2, a3, a4⟩) | ⟨a1, a2, a3⟩)
      · exact ⟨(42, 6, 64, 0), by simp, by
          show lnR 42 6 64 0 X W ≤ 0
          simp only [detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *; linarith⟩
      · exact ⟨(24, 24, 42, 6), by simp, by
          show lnR 24 24 42 6 X W ≤ 0
          simp only [detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *; linarith⟩
      · exact ⟨(42, 6, 58, 6), by simp, by
          show lnR 42 6 58 6 X W ≤ 0
          simp only [detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *; linarith⟩
      · exact ⟨(58, 6, 66, 6), by simp, by
          show lnR 58 6 66 6 X W ≤ 0
          simp only [detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *; linarith⟩
      · exact ⟨(28, 20, 52, 20), by simp, by
          show lnR 28 20 52 20 X W ≤ 0
          simp only [detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *; linarith⟩
      · exact ⟨(24, 24, 52, 20), by simp, by
          show lnR 24 24 52 20 X W ≤ 0
          simp only [detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *; linarith⟩)
    (by
      intro X W h l hl
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;>
      · simp only [detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *; obtain ⟨b1, b2, b3⟩ := h; linarith)


set_option maxHeartbeats 8000000 in
theorem G_iff (X W : ℝ) : G7 X W ↔ TriR 0 0 72 0 36 36 X W := by
  constructor
  · intro h
    simp only [G7,G6,G5,G4,G3,G2,G1] at h
    rcases h with ((((((⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩) | ⟨a1, a2, a3⟩) | ⟨a1, a2, a3, a4⟩) | ⟨a1, a2, a3, a4⟩) | ⟨a1, a2, a3⟩) | ⟨a1, a2, a3⟩)
    all_goals
      simp only [detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *
      refine ⟨?_, ?_, ?_⟩ <;> linarith
  · intro h
    simp only [TriR, detR] at h
    obtain ⟨h1, h2, h3⟩ := h
    rcases le_total 0 (lnR 0 0 42 6 X W) with f4 | f4
    · rcases le_total 0 (lnR 24 24 28 20 X W) with f6 | f6
      · rcases le_total 0 (lnR 24 24 52 20 X W) with f8 | f8
        · simp only [G7,G6,G5,G4,G3,G2,G1, detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *
          refine (Or.inr ?_)
          refine ⟨?_, ?_, ?_⟩ <;> linarith
        · rcases le_total 0 (lnR 28 20 52 20 X W) with f10 | f10
          · simp only [G7,G6,G5,G4,G3,G2,G1, detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *
            refine (Or.inl (Or.inr ?_))
            refine ⟨?_, ?_, ?_⟩ <;> linarith
          · simp only [G7,G6,G5,G4,G3,G2,G1, detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *
            refine (Or.inl (Or.inl (Or.inr ?_)))
            refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
      · simp only [G7,G6,G5,G4,G3,G2,G1, detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *
        refine (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ?_))))))
        refine ⟨?_, ?_, ?_⟩ <;> linarith
    · rcases le_total 0 (lnR 42 6 64 0 X W) with f6 | f6
      · rcases le_total 0 (lnR 42 6 66 6 X W) with f8 | f8
        · simp only [G7,G6,G5,G4,G3,G2,G1, detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *
          refine (Or.inl (Or.inl (Or.inr ?_)))
          refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
        · rcases le_total 0 (lnR 58 6 64 0 X W) with f10 | f10
          · simp only [G7,G6,G5,G4,G3,G2,G1, detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *
            refine (Or.inl (Or.inl (Or.inl (Or.inr ?_))))
            refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
          · simp only [G7,G6,G5,G4,G3,G2,G1, detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *
            refine (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ?_)))))
            refine ⟨?_, ?_, ?_⟩ <;> linarith
      · simp only [G7,G6,G5,G4,G3,G2,G1, detR, lnR, TriR, PgP1, cxf1, cyf1, PgP2, cxf2, cyf2] at *
        refine (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ?_))))))
        refine ⟨?_, ?_, ?_⟩ <;> linarith


/-- **Beeson Theorem 24, instance `(2,3,4)`, `lambda = 1`, `rho = 2` (UNAUDITED).**  The isosceles triangle
`A = (0,0)`, `C = (72, 0)`, `B = (36, sqrt 15 * 36)` (base `72`, legs `144`, base angles `alpha + beta`)
is tiled by `1728` copies of the tile `(2,3,4)`. -/
theorem beeson_t24_2_3_4 :
    Dis T0 (TriSet 0 (rt * 0) 72 (rt * 0) 36 (rt * 36)) 1728 := by
  have h := g7_dis
  rw [TriSet_RS]
  refine h.congr ?_ (by norm_num)
  ext q
  exact G_iff _ _

end Erdos634.BeesonT24.I_2_3_4
