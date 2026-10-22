import Erdos634.Draft.ZhangLemma1

/-!
# Zhang Lemma 2 (arXiv 2512.22696v4): parallelograms with sides `x` and `a b` are tiled by `(a,b,c)`

Frame.  `Plane` carries the lattice frame `e₁ = (1,0)`, `e₂ = (1/2, √3/2)` at an origin `(px,py)`:
`uu px py q`, `vv px py q` are the coordinates of `q` in that frame (`q = p + u e₁ + v e₂`).  Then
* `Qs px py s t = {q | 0 ≤ u ≤ s, 0 ≤ v ≤ t}`: the parallelogram with vertices `p, p+s e₁, p+s e₁+t e₂, p+t e₂`
  (angles `π/3, 2π/3, π/3, 2π/3`; sides `s` along `e₁`, `t` along `e₂`);
* `Tz px py x y = {q | 0 ≤ u, 0 ≤ v ≤ y, u+v ≤ x+y}`: the isosceles trapezoid with `π/3` base angles,
  vertices `p, p+(x+y)e₁, p+x e₁+y e₂, p+y e₂` (short side `x`, legs `y`, long base `x+y`);
* `Tri3 px py X = {q | 0 ≤ u, 0 ≤ v, u+v ≤ X}`: the equilateral triangle `p, p+X e₁, p+X e₂`.

`Dis R S n` : `S` carries a `CongruentRegionDissection n` with model `R`.

Statement `zhang_lemma2` (this file): for naturals `a,b,c` with `c² = a²+b²+ab`, `gcd(a,b)=1`, and
`x > 0`, `a b < x + a + b` (i.e. `x > ab − a − b`), the parallelogram `Qs px py x (a b)` carries
`2x` tiles congruent to `Rmodel`.  Zhang's Lemma 2 hypothesis `gcd(a,b)=1` is implicit in his use of
Prop. 2 (Frobenius); `x > 0` is also implicit (a degenerate `x = 0` is not a parallelogram).
UNAUDITED.  Credit Zhang (arXiv 2512.22696), Beeson, Beeson-Rosu, Laczkovich.
-/

namespace Erdos634.ZhangPara

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.GlueCut Erdos634.SssCongruent Erdos634.ZhangL1

noncomputable def uu (px py : ℝ) (q : Plane) : ℝ := (q 0 - px) - (q 1 - py) / zs
noncomputable def vv (px py : ℝ) (q : Plane) : ℝ := 2 * (q 1 - py) / zs
noncomputable def shx (px u v : ℝ) : ℝ := px + u + v / 2
noncomputable def shy (py v : ℝ) : ℝ := py + v * zs / 2

theorem uu_sh (px py u v : ℝ) (q : Plane) : uu (shx px u v) (shy py v) q = uu px py q - u := by
  have := zs_pos.ne'
  unfold uu shx shy; field_simp; ring

theorem vv_sh (px py u v : ℝ) (q : Plane) : vv (shx px u v) (shy py v) q = vv px py q - v := by
  have := zs_pos.ne'
  unfold vv shy; field_simp; ring

theorem q0_eq (px py : ℝ) (q : Plane) : q 0 = px + uu px py q + vv px py q / 2 := by
  have := zs_pos.ne'
  unfold uu vv; field_simp; ring

theorem q1_eq (px py : ℝ) (q : Plane) : q 1 = py + vv px py q * zs / 2 := by
  have := zs_pos.ne'
  unfold vv; field_simp; ring

/-- The point `p + u e₁ + v e₂`. -/
noncomputable def ptP (px py u v : ℝ) : Plane := mkPt (shx px u v) (shy py v)

theorem uu_ptP (px py u v : ℝ) : uu px py (ptP px py u v) = u := by
  have := zs_pos.ne'
  unfold uu ptP shx shy; simp only [mkPt_zero, mkPt_one]; field_simp; ring

theorem vv_ptP (px py u v : ℝ) : vv px py (ptP px py u v) = v := by
  have := zs_pos.ne'
  unfold vv ptP shy; simp only [mkPt_one]; field_simp; ring

theorem eq_ptP (px py : ℝ) (q : Plane) : q = ptP px py (uu px py q) (vv px py q) := by
  unfold ptP shx shy
  rw [← q0_eq, ← q1_eq]; exact (mkPt_eta q).symm

/-! ### Sets -/

def Qs (px py s t : ℝ) : Set Plane :=
  {q | 0 ≤ uu px py q ∧ uu px py q ≤ s ∧ 0 ≤ vv px py q ∧ vv px py q ≤ t}

def Tz (px py x y : ℝ) : Set Plane :=
  {q | 0 ≤ uu px py q ∧ 0 ≤ vv px py q ∧ vv px py q ≤ y ∧ uu px py q + vv px py q ≤ x + y}

def Tri3 (px py X : ℝ) : Set Plane :=
  {q | 0 ≤ uu px py q ∧ 0 ≤ vv px py q ∧ uu px py q + vv px py q ≤ X}

/-- `S` carries a dissection into `n` tiles all congruent to the model `R`. -/
def Dis (R : Tri) (S : Set Plane) (n : ℕ) : Prop :=
  ∃ C : CongruentRegionDissection n, C.region = S ∧ C.model = R

theorem Dis.congr {R : Tri} {S S' : Set Plane} {n n' : ℕ} (h : Dis R S n) (hS : S = S')
    (hn : n = n') : Dis R S' n' := by subst hS; subst hn; exact h

/-! ### Gluing along `u = s` and `v = t` -/

theorem lineFun_u (px py s : ℝ) (q : Plane) :
    lineFun (px + s + 1 / 2) (py + zs / 2) (px + s) py q = zs / 2 * (uu px py q - s) := by
  have := zs_pos.ne'
  simp only [lineFun_apply]; unfold uu; field_simp; ring

theorem lineFun_v (px py t : ℝ) (q : Plane) :
    lineFun (px + 0 + t / 2) (py + t * zs / 2) (px + 0 + t / 2 + 1) (py + t * zs / 2) q
      = zs / 2 * (vv px py q - t) := by
  have := zs_pos.ne'
  simp only [lineFun_apply]; unfold vv; field_simp; ring

theorem Dis.glue_u {R : Tri} {S1 S2 : Set Plane} {n1 n2 : ℕ} (h1 : Dis R S1 n1) (h2 : Dis R S2 n2)
    (px py s : ℝ) (hS1 : ∀ q ∈ S1, uu px py q ≤ s) (hS2 : ∀ q ∈ S2, s ≤ uu px py q) :
    Dis R (S1 ∪ S2) (n1 + n2) := by
  obtain ⟨C1, r1, m1⟩ := h1
  obtain ⟨C2, r2, m2⟩ := h2
  have hz := zs_pos
  have hf := lineFun_linear_ne_zero (px := px + s + 1 / 2) (py := py + zs / 2) (qx := px + s)
    (qy := py) (Or.inl (by intro h; linarith))
  refine ⟨glueByLine C1 C2 (m1.trans m2.symm) _ hf ?_ ?_, ?_, ?_⟩
  · intro x hx
    rw [lineFun_u]
    have := hS1 x (by rwa [← r1])
    nlinarith
  · intro x hx
    rw [lineFun_u]
    have := hS2 x (by rwa [← r2])
    nlinarith
  · simp [r1, r2]
  · simp [m1]

theorem Dis.glue_v {R : Tri} {S1 S2 : Set Plane} {n1 n2 : ℕ} (h1 : Dis R S1 n1) (h2 : Dis R S2 n2)
    (px py t : ℝ) (hS1 : ∀ q ∈ S1, vv px py q ≤ t) (hS2 : ∀ q ∈ S2, t ≤ vv px py q) :
    Dis R (S1 ∪ S2) (n1 + n2) := by
  obtain ⟨C1, r1, m1⟩ := h1
  obtain ⟨C2, r2, m2⟩ := h2
  have hz := zs_pos
  have hf := lineFun_linear_ne_zero (px := px + 0 + t / 2) (py := py + t * zs / 2)
    (qx := px + 0 + t / 2 + 1) (qy := py + t * zs / 2) (Or.inl (by intro h; linarith))
  refine ⟨glueByLine C1 C2 (m1.trans m2.symm) _ hf ?_ ?_, ?_, ?_⟩
  · intro x hx
    rw [lineFun_v]
    have := hS1 x (by rwa [← r1])
    nlinarith
  · intro x hx
    rw [lineFun_v]
    have := hS2 x (by rwa [← r2])
    nlinarith
  · simp [r1, r2]
  · simp [m1]

/-! ### Coordinate triangles in the frame -/

theorem det_raw (px py u0 v0 u1 v1 u2 v2 : ℝ) :
    det3 (shx px u0 v0) (shy py v0) (shx px u1 v1) (shy py v1) (shx px u2 v2) (shy py v2)
      = zs / 2 * det3 u0 v0 u1 v1 u2 v2 := by
  unfold det3 shx shy; ring

theorem det_raw_pos (px py u0 v0 u1 v1 u2 v2 : ℝ) (h : 0 < det3 u0 v0 u1 v1 u2 v2) :
    0 < det3 (shx px u0 v0) (shy py v0) (shx px u1 v1) (shy py v1) (shx px u2 v2) (shy py v2) := by
  rw [det_raw]; have := zs_pos; positivity

noncomputable def triUV (px py u0 v0 u1 v1 u2 v2 : ℝ) (h : 0 < det3 u0 v0 u1 v1 u2 v2) : Tri :=
  mkTri (shx px u0 v0) (shy py v0) (shx px u1 v1) (shy py v1) (shx px u2 v2) (shy py v2)
    (det_raw_pos px py u0 v0 u1 v1 u2 v2 h).ne'

theorem mem_triUV (px py u0 v0 u1 v1 u2 v2 : ℝ) (h : 0 < det3 u0 v0 u1 v1 u2 v2) (q : Plane) :
    q ∈ (triUV px py u0 v0 u1 v1 u2 v2 h).carrier ↔
      0 ≤ det3 (uu px py q) (vv px py q) u1 v1 u2 v2 ∧
      0 ≤ det3 u0 v0 (uu px py q) (vv px py q) u2 v2 ∧
      0 ≤ det3 u0 v0 u1 v1 (uu px py q) (vv px py q) := by
  unfold triUV
  rw [mem_carrier_mkTri_iff (det_raw_pos px py u0 v0 u1 v1 u2 v2 h) q]
  have hq0 := q0_eq px py q
  have hq1 := q1_eq px py q
  have e1 : det3 (q 0) (q 1) (shx px u1 v1) (shy py v1) (shx px u2 v2) (shy py v2)
      = zs / 2 * det3 (uu px py q) (vv px py q) u1 v1 u2 v2 := by
    rw [hq0, hq1]; unfold det3 shx shy; ring
  have e2 : det3 (shx px u0 v0) (shy py v0) (q 0) (q 1) (shx px u2 v2) (shy py v2)
      = zs / 2 * det3 u0 v0 (uu px py q) (vv px py q) u2 v2 := by
    rw [hq0, hq1]; unfold det3 shx shy; ring
  have e3 : det3 (shx px u0 v0) (shy py v0) (shx px u1 v1) (shy py v1) (q 0) (q 1)
      = zs / 2 * det3 u0 v0 u1 v1 (uu px py q) (vv px py q) := by
    rw [hq0, hq1]; unfold det3 shx shy; ring
  have hz : 0 < zs / 2 := by have := zs_pos; positivity
  rw [e1, e2, e3, mul_nonneg_iff_of_pos_left hz, mul_nonneg_iff_of_pos_left hz,
    mul_nonneg_iff_of_pos_left hz]

theorem dist_sq_sh (px py u v u' v' : ℝ) :
    dist (mkPt (shx px u v) (shy py v)) (mkPt (shx px u' v') (shy py v')) ^ 2
      = (u - u') ^ 2 + (u - u') * (v - v') + (v - v') ^ 2 := by
  rw [dist_sq_mkPt]; unfold shx shy
  have hs := zs_sq
  linear_combination ((v - v') ^ 2 / 4) * hs

/-- One tile. -/
theorem Dis_tri (T R : Tri) (h : T.Congruent R) : Dis R T.carrier 1 := by
  obtain ⟨C, hr, hm⟩ := scaledPiece T R T h 1 one_pos rfl (by simp) (by simp)
  exact ⟨C, hr, hm⟩

/-! ### The basic parallelogram: two tiles -/

theorem cong_of_three {T U : Tri} (σ : Equiv.Perm (Fin 3))
    (h01 : dist (T.pts 0) (T.pts 1) ^ 2 = dist (U.pts (σ 0)) (U.pts (σ 1)) ^ 2)
    (h12 : dist (T.pts 1) (T.pts 2) ^ 2 = dist (U.pts (σ 1)) (U.pts (σ 2)) ^ 2)
    (h02 : dist (T.pts 0) (T.pts 2) ^ 2 = dist (U.pts (σ 0)) (U.pts (σ 2)) ^ 2) :
    T.Congruent U := by
  refine congruent_of_sq_dist_perm σ ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    first
    | (simp; done)
    | exact h01 | exact h12 | exact h02
    | (rw [dist_comm, dist_comm (U.pts _)]; first | exact h01 | exact h12 | exact h02)

section base
variable {a b c : ℝ}

theorem R_d01 (ha : 0 < a) (hb : 0 < b) (hc2 : c ^ 2 = a ^ 2 + b ^ 2 + a * b) :
    dist ((Rmodel ha hb).pts 0) ((Rmodel ha hb).pts 1) ^ 2 = c ^ 2 := by
  have hS := zs_sq
  simp only [Rmodel, mkTri]
  show dist (mkPt 0 0) (mkPt (b / 2 + a) (b * zs / 2)) ^ 2 = _
  rw [dist_sq_mkPt]; nlinarith [hS, hc2]

theorem R_d12 (ha : 0 < a) (hb : 0 < b) :
    dist ((Rmodel ha hb).pts 1) ((Rmodel ha hb).pts 2) ^ 2 = a ^ 2 := by
  have hS := zs_sq
  simp only [Rmodel, mkTri]
  show dist (mkPt (b / 2 + a) (b * zs / 2)) (mkPt (b / 2) (b * zs / 2)) ^ 2 = _
  rw [dist_sq_mkPt]; nlinarith [hS]

theorem R_d02 (ha : 0 < a) (hb : 0 < b) :
    dist ((Rmodel ha hb).pts 0) ((Rmodel ha hb).pts 2) ^ 2 = b ^ 2 := by
  have hS := zs_sq
  simp only [Rmodel, mkTri]
  show dist (mkPt 0 0) (mkPt (b / 2) (b * zs / 2)) ^ 2 = _
  rw [dist_sq_mkPt]; nlinarith [hS]

theorem Dis_Qs_two (ha : 0 < a) (hb : 0 < b) (hc2 : c ^ 2 = a ^ 2 + b ^ 2 + a * b) (s t : ℝ)
    (hst : (s = a ∧ t = b) ∨ (s = b ∧ t = a)) (px py : ℝ) :
    Dis (Rmodel ha hb) (Qs px py s t) 2 := by
  have hs0 : 0 < s := by rcases hst with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> assumption
  have ht0 : 0 < t := by rcases hst with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> assumption
  have d1 : 0 < det3 0 0 s 0 s t := by simp only [det3]; nlinarith
  have d2 : 0 < det3 0 0 s t 0 t := by simp only [det3]; nlinarith
  have r01 := R_d01 ha hb hc2
  have r12 := R_d12 ha hb
  have r02 := R_d02 ha hb
  have cong1 : (triUV px py 0 0 s 0 s t d1).Congruent (Rmodel ha hb) := by
    have e01 : dist ((triUV px py 0 0 s 0 s t d1).pts 0) ((triUV px py 0 0 s 0 s t d1).pts 1) ^ 2
        = s ^ 2 := by
      have := dist_sq_sh px py 0 0 s 0; rw [show (0:ℝ) - s = -s by ring] at this
      exact this.trans (by ring)
    have e12 : dist ((triUV px py 0 0 s 0 s t d1).pts 1) ((triUV px py 0 0 s 0 s t d1).pts 2) ^ 2
        = t ^ 2 := by
      have := dist_sq_sh px py s 0 s t
      exact this.trans (by ring)
    have e02 : dist ((triUV px py 0 0 s 0 s t d1).pts 0) ((triUV px py 0 0 s 0 s t d1).pts 2) ^ 2
        = s ^ 2 + s * t + t ^ 2 := by
      have := dist_sq_sh px py 0 0 s t
      exact this.trans (by ring)
    rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine cong_of_three ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩ ?_ ?_ ?_
      · show _ = dist ((Rmodel ha hb).pts 1) ((Rmodel ha hb).pts 2) ^ 2
        rw [e01, r12]
      · show _ = dist ((Rmodel ha hb).pts 2) ((Rmodel ha hb).pts 0) ^ 2
        rw [e12, dist_comm, r02]
      · show _ = dist ((Rmodel ha hb).pts 1) ((Rmodel ha hb).pts 0) ^ 2
        rw [e02, dist_comm, r01]; nlinarith
    · refine cong_of_three ⟨![0, 2, 1], ![0, 2, 1], by decide, by decide⟩ ?_ ?_ ?_
      · show _ = dist ((Rmodel ha hb).pts 0) ((Rmodel ha hb).pts 2) ^ 2
        rw [e01, r02]
      · show _ = dist ((Rmodel ha hb).pts 2) ((Rmodel ha hb).pts 1) ^ 2
        rw [e12, dist_comm, r12]
      · show _ = dist ((Rmodel ha hb).pts 0) ((Rmodel ha hb).pts 1) ^ 2
        rw [e02, r01]; nlinarith
  have cong2 : (triUV px py 0 0 s t 0 t d2).Congruent (Rmodel ha hb) := by
    have e01 : dist ((triUV px py 0 0 s t 0 t d2).pts 0) ((triUV px py 0 0 s t 0 t d2).pts 1) ^ 2
        = s ^ 2 + s * t + t ^ 2 := by
      have := dist_sq_sh px py 0 0 s t
      exact this.trans (by ring)
    have e12 : dist ((triUV px py 0 0 s t 0 t d2).pts 1) ((triUV px py 0 0 s t 0 t d2).pts 2) ^ 2
        = s ^ 2 := by
      have := dist_sq_sh px py s t 0 t
      exact this.trans (by ring)
    have e02 : dist ((triUV px py 0 0 s t 0 t d2).pts 0) ((triUV px py 0 0 s t 0 t d2).pts 2) ^ 2
        = t ^ 2 := by
      have := dist_sq_sh px py 0 0 0 t
      exact this.trans (by ring)
    rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine cong_of_three ⟨![0, 1, 2], ![0, 1, 2], by decide, by decide⟩ ?_ ?_ ?_
      · show _ = dist ((Rmodel ha hb).pts 0) ((Rmodel ha hb).pts 1) ^ 2
        rw [e01, r01]; nlinarith
      · show _ = dist ((Rmodel ha hb).pts 1) ((Rmodel ha hb).pts 2) ^ 2
        rw [e12, r12]
      · show _ = dist ((Rmodel ha hb).pts 0) ((Rmodel ha hb).pts 2) ^ 2
        rw [e02, r02]
    · refine cong_of_three ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩ ?_ ?_ ?_
      · show _ = dist ((Rmodel ha hb).pts 1) ((Rmodel ha hb).pts 0) ^ 2
        rw [e01, dist_comm, r01]; nlinarith
      · show _ = dist ((Rmodel ha hb).pts 0) ((Rmodel ha hb).pts 2) ^ 2
        rw [e12, r02]
      · show _ = dist ((Rmodel ha hb).pts 1) ((Rmodel ha hb).pts 2) ^ 2
        rw [e02, r12]
  obtain ⟨C1, r1, m1⟩ := Dis_tri _ _ cong1
  obtain ⟨C2, r2, m2⟩ := Dis_tri _ _ cong2
  have hz := zs_pos
  have hdiag : ∀ q : Plane, lineFun px py (shx px s t) (shy py t) q
      = zs / 2 * (s * vv px py q - t * uu px py q) := by
    intro q
    have := zs_pos.ne'
    simp only [lineFun_apply, shx, shy]; unfold uu vv; field_simp; ring
  have hf := lineFun_linear_ne_zero (px := px) (py := py) (qx := shx px s t) (qy := shy py t)
    (Or.inr (by unfold shy; intro h; nlinarith))
  refine ⟨glueByLine C1 C2 (m1.trans m2.symm) _ hf ?_ ?_, ?_, ?_⟩
  · intro x hx
    rw [hdiag]
    have hx' : x ∈ (triUV px py 0 0 s 0 s t d1).carrier := by rwa [← r1]
    rw [mem_triUV] at hx'
    obtain ⟨_, h2, _⟩ := hx'
    simp only [det3] at h2
    nlinarith
  · intro x hx
    rw [hdiag]
    have hx' : x ∈ (triUV px py 0 0 s t 0 t d2).carrier := by rwa [← r2]
    rw [mem_triUV] at hx'
    obtain ⟨_, _, h3⟩ := hx'
    simp only [det3] at h3
    nlinarith
  · rw [glueByLine_region, r1, r2]
    ext q
    simp only [Set.mem_union, mem_triUV, Qs, Set.mem_setOf_eq, det3]
    constructor
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
      · refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
      · refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
    · rintro ⟨h1, h2, h3, h4⟩
      rcases le_total (s * vv px py q) (t * uu px py q) with h | h
      · left; refine ⟨?_, ?_, ?_⟩ <;> nlinarith
      · right; refine ⟨?_, ?_, ?_⟩ <;> nlinarith
  · simp [m1]

end base

/-! ### Rows and columns of parallelograms -/

theorem Qs_row (px py s s' t : ℝ) (hs : 0 ≤ s) (hs' : 0 ≤ s') :
    Qs px py (s + s') t = Qs px py s t ∪ Qs (shx px s 0) (shy py 0) s' t := by
  ext q
  simp only [Qs, Set.mem_union, Set.mem_setOf_eq, uu_sh, vv_sh, sub_zero]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    rcases le_total (uu px py q) s with h | h
    · exact Or.inl ⟨h1, h, h3, h4⟩
    · exact Or.inr ⟨by linarith, by linarith, h3, h4⟩
  · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
    · exact ⟨h1, by linarith, h3, h4⟩
    · exact ⟨by linarith, by linarith, h3, h4⟩

theorem Qs_col (px py s t t' : ℝ) (ht : 0 ≤ t) (ht' : 0 ≤ t') :
    Qs px py s (t + t') = Qs px py s t ∪ Qs (shx px 0 t) (shy py t) s t' := by
  ext q
  simp only [Qs, Set.mem_union, Set.mem_setOf_eq, uu_sh, vv_sh, sub_zero]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    rcases le_total (vv px py q) t with h | h
    · exact Or.inl ⟨h1, h2, h3, h⟩
    · exact Or.inr ⟨h1, h2, by linarith, by linarith⟩
  · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
    · exact ⟨h1, h2, h3, by linarith⟩
    · exact ⟨h1, h2, by linarith, by linarith⟩

theorem Dis.row {R : Tri} {px py s s' t : ℝ} {n m : ℕ} (hs : 0 ≤ s) (hs' : 0 ≤ s')
    (h1 : Dis R (Qs px py s t) n) (h2 : Dis R (Qs (shx px s 0) (shy py 0) s' t) m) :
    Dis R (Qs px py (s + s') t) (n + m) := by
  refine (Dis.glue_u h1 h2 px py s ?_ ?_).congr (Qs_row px py s s' t hs hs').symm rfl
  · intro q hq; exact hq.2.1
  · intro q hq
    have := hq.1; rw [uu_sh] at this; linarith

theorem Dis.col {R : Tri} {px py s t t' : ℝ} {n m : ℕ} (ht : 0 ≤ t) (ht' : 0 ≤ t')
    (h1 : Dis R (Qs px py s t) n) (h2 : Dis R (Qs (shx px 0 t) (shy py t) s t') m) :
    Dis R (Qs px py s (t + t')) (n + m) := by
  refine (Dis.glue_v h1 h2 px py t ?_ ?_).congr (Qs_col px py s t t' ht ht').symm rfl
  · intro q hq; exact hq.2.2.2
  · intro q hq
    have := hq.2.2.1; rw [vv_sh] at this; linarith

theorem Dis.colN {R : Tri} {s t : ℝ} {n : ℕ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (h : ∀ px py, Dis R (Qs px py s t) n) :
    ∀ (m : ℕ), 0 < m → ∀ px py, Dis R (Qs px py s (m * t)) (m * n) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => intro px py; exact (h px py).congr (by simp) (by simp)
  | succ m hm ih =>
    intro px py
    have hm0 : (0:ℝ) ≤ m * t := by positivity
    exact (Dis.col hm0 ht (ih px py) (h _ _)).congr (by push_cast; ring_nf) (by ring)

theorem Dis.rowN {R : Tri} {s t : ℝ} {n : ℕ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (h : ∀ px py, Dis R (Qs px py s t) n) :
    ∀ (m : ℕ), 0 < m → ∀ px py, Dis R (Qs px py (m * s) t) (m * n) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => intro px py; exact (h px py).congr (by simp) (by simp)
  | succ m hm ih =>
    intro px py
    have hm0 : (0:ℝ) ≤ m * s := by positivity
    exact (Dis.row hm0 hs (ih px py) (h _ _)).congr (by push_cast; ring_nf) (by ring)

/-- Mixed row of two kinds of pieces: `i` of width `s₁` and `j` of width `s₂`. -/
theorem Dis.rowMix {R : Tri} {s₁ s₂ t : ℝ} {n₁ n₂ : ℕ} (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) (ht : 0 ≤ t)
    (h₁ : ∀ px py, Dis R (Qs px py s₁ t) n₁) (h₂ : ∀ px py, Dis R (Qs px py s₂ t) n₂)
    (i j : ℕ) (hij : 0 < i + j) (px py : ℝ) :
    Dis R (Qs px py (i * s₁ + j * s₂) t) (i * n₁ + j * n₂) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have hj : 0 < j := by omega
    exact (Dis.rowN hs₂.le ht h₂ j hj px py).congr (by simp) (by simp)
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · exact (Dis.rowN hs₁.le ht h₁ i hi px py).congr (by simp) (by simp)
  have hi' : (0:ℝ) ≤ i * s₁ := by positivity
  have hj' : (0:ℝ) ≤ j * s₂ := by positivity
  exact Dis.row hi' hj' (Dis.rowN hs₁.le ht h₁ i hi px py)
    (Dis.rowN hs₂.le ht h₂ j hj _ _)

/-! ### Frobenius for two coprime naturals (Zhang's Proposition 2, elementary proof) -/

theorem frob (a b x : ℕ) (hcop : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    (hx : a * b < x + a + b) : ∃ i j : ℕ, x = i * a + j * b := by
  rcases Nat.lt_or_ge 1 a with h1 | h1
  · obtain ⟨j, hja, hmod⟩ := Nat.exists_mul_mod_eq_of_coprime x hcop.symm ha.ne'
    have hmod : b * j ≡ x [MOD a] := hmod
    have hle : b * j ≤ x := by
      by_contra hlt
      replace hlt := not_le.mp hlt
      have hd := (Nat.modEq_iff_dvd' hlt.le).mp hmod.symm
      have hpos : 0 < b * j - x := by omega
      have := Nat.le_of_dvd hpos hd
      have hbj : b * j ≤ b * (a - 1) := Nat.mul_le_mul_left b (by omega)
      have hab : b * (a - 1) + b = a * b := by
        obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
        simp [Nat.mul_comm]; ring
      omega
    obtain ⟨i, hi⟩ := (Nat.modEq_iff_dvd' hle).mp hmod
    exact ⟨i, j, by rw [Nat.mul_comm i a, Nat.mul_comm j b]; omega⟩
  · have : a = 1 := by omega
    subst this
    exact ⟨x, 0, by simp⟩

/-! ### Lemma 2 -/

/-- **Zhang's Lemma 2 (UNAUDITED).**  For naturals with `c² = a²+b²+ab`, `gcd(a,b)=1`, `x > 0` and
`x > ab − a − b` (stated `ab < x+a+b`), the parallelogram `Qs px py x (a b)` (sides `x` and `ab`,
angles `π/3, 2π/3`) carries `2x` tiles, each congruent to `Rmodel` (sides `c, a, b`, angle `2π/3`
between `a` and `b`). -/
theorem zhang_lemma2 (a b c x : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hcab : c * c = a * a + b * b + a * b) (hcop : Nat.Coprime a b) (hx0 : 0 < x)
    (hx : a * b < x + a + b) (px py : ℝ) :
    Dis (Rmodel (Nat.cast_pos.mpr ha : (0:ℝ) < a) (Nat.cast_pos.mpr hb : (0:ℝ) < b))
      (Qs px py (x : ℝ) ((a : ℝ) * b)) (2 * x) := by
  have ha' : (0:ℝ) < a := Nat.cast_pos.mpr ha
  have hb' : (0:ℝ) < b := Nat.cast_pos.mpr hb
  have hc2 : ((c:ℕ):ℝ) ^ 2 = (a:ℝ) ^ 2 + (b:ℝ) ^ 2 + a * b := by
    exact_mod_cast (by nlinarith [hcab] : c ^ 2 = a ^ 2 + b ^ 2 + a * b)
  obtain ⟨i, j, hij⟩ := frob a b x hcop ha hb hx
  -- pieces `Q(a, ab)` (a stacked copies of `Q(a,b)`) and `Q(b, ab)`
  have hA : ∀ px py, Dis (Rmodel ha' hb') (Qs px py (a:ℝ) ((a:ℝ) * b)) (a * 2) := fun px py =>
    Dis.colN ha'.le hb'.le (fun px py => Dis_Qs_two ha' hb' hc2 a b (Or.inl ⟨rfl, rfl⟩) px py)
      a ha px py
  have hB : ∀ px py, Dis (Rmodel ha' hb') (Qs px py (b:ℝ) ((a:ℝ) * b)) (b * 2) := fun px py =>
    (Dis.colN hb'.le ha'.le (fun px py => Dis_Qs_two ha' hb' hc2 b a (Or.inr ⟨rfl, rfl⟩) px py)
      b hb px py).congr (by rw [mul_comm (b:ℝ) (a:ℝ)]) rfl
  have key := Dis.rowMix ha' hb' (mul_pos ha' hb').le hA hB i j (by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp at hij; omega
      · omega
    · omega) px py
  refine key.congr ?_ ?_
  · congr 1
    have : (x:ℝ) = i * a + j * b := by exact_mod_cast hij
    rw [this]
  · rw [hij]; ring

/-- Witness `(3,5,7)`, `x = 9`: `2x = 18` tiles; areas `9·15·√3/2 = 18 · 15·√3/4`. -/
theorem zhang_lemma2_357 (px py : ℝ) : ∃ n : ℕ, n = 18 ∧ ∃ C : CongruentRegionDissection n,
    C.region = Qs px py (9 : ℕ) (((3:ℕ):ℝ) * ((5:ℕ):ℝ)) := by
  obtain ⟨C, hr, -⟩ := zhang_lemma2 3 5 7 9 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) px py
  exact ⟨2 * 9, by norm_num, C, hr⟩

/-- Witness `(8,7,13)`, `x = 42`: `84` tiles; `42·56·√3/2 = 84 · 56·√3/4`. -/
theorem zhang_lemma2_8_7_13 (px py : ℝ) : ∃ n : ℕ, n = 84 ∧ ∃ C : CongruentRegionDissection n,
    C.region = Qs px py (42 : ℕ) (((8:ℕ):ℝ) * ((7:ℕ):ℝ)) := by
  obtain ⟨C, hr, -⟩ := zhang_lemma2 8 7 13 42 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) px py
  exact ⟨2 * 42, by norm_num, C, hr⟩

end Erdos634.ZhangPara
