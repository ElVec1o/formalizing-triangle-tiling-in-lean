import Erdos634.Draft.ZhangThm4

/-!
# Zhang (arXiv 2512.22696v4) Section 5: triangles from an equiconstructible equilateral triangle

Toolkit: `TriSet` (the triangle as three half-plane conditions, no side conditions), cevian
splitting `Dis_cevian`, unit-tile scalings `Dis_scaled`, mirror `Dis_swap`.

Core constructions (reals `a b`, natural scale `k`, equilateral side `X = k a`, hypothesis
`Dis (Rmodel a b) (Tri3 0 0 X) n0`):

* `core9`:  tile at the left (`120°` at `O=(0,0)`, scale `k`) + equilateral: the triangle
  `E=(X/2, X√3/2), S=(-k b, 0), Q=(X,0)` carries `k² + n0` tiles (Zhang Prop 9).
* `core8`:  a second tile at the right: triangle `E, S, (X + k b, 0)` carries `2k² + n0` (Prop 8).
* `core10`: Prop 9 triangle + a tile of scale `K` below (`120°` at `Q`) (Prop 10).

The theorems `zhang_prop8/9/10` are stated for naturals `a b m` with `X = m a b` and
`EquiConstr a b (m a b) (m² a b)`; the (2) halves are the (1) halves with `a`,`b` exchanged and
the model replaced by its mirror (`Dis_swap`).  Credit Zhang (arXiv 2512.22696), Beeson,
Beeson-Rosu, Laczkovich.  UNAUDITED.
-/

namespace Erdos634.ZhangSporadic

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.GlueCut Erdos634.SssCongruent Erdos634.ZhangL1 Erdos634.ZhangPara
  Erdos634.ZhangProp3 Erdos634.ZhangThm4

/-! ### Triangles as sets -/

/-- The triangle `(x0,y0),(x1,y1),(x2,y2)` (counterclockwise) as three half-planes. -/
def TriSet (x0 y0 x1 y1 x2 y2 : ℝ) : Set Plane :=
  {p | 0 ≤ det3 (p 0) (p 1) x1 y1 x2 y2 ∧ 0 ≤ det3 x0 y0 (p 0) (p 1) x2 y2 ∧
    0 ≤ det3 x0 y0 x1 y1 (p 0) (p 1)}

theorem TriSet_eq_carrier {x0 y0 x1 y1 x2 y2 : ℝ} (h : 0 < det3 x0 y0 x1 y1 x2 y2) :
    TriSet x0 y0 x1 y1 x2 y2 = (mkTri x0 y0 x1 y1 x2 y2 h.ne').carrier := by
  ext p
  rw [mem_carrier_mkTri_iff h]
  rfl

theorem TriSet_rot (x0 y0 x1 y1 x2 y2 : ℝ) :
    TriSet x1 y1 x2 y2 x0 y0 = TriSet x0 y0 x1 y1 x2 y2 := by
  ext p
  simp only [TriSet, Set.mem_setOf_eq, det3]
  constructor <;> rintro ⟨e1, e2, e3⟩ <;> refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem Dis_rot {R : Tri} {n : ℕ} (x0 y0 x1 y1 x2 y2 : ℝ)
    (h : Dis R (TriSet x0 y0 x1 y1 x2 y2) n) : Dis R (TriSet x1 y1 x2 y2 x0 y0) n :=
  h.congr (TriSet_rot x0 y0 x1 y1 x2 y2).symm rfl

theorem nn_of_mul {t x : ℝ} (ht : 0 < t) (h : 0 ≤ t * x) : 0 ≤ x := by
  by_contra hx; push_neg at hx; nlinarith [mul_pos ht (neg_pos.mpr hx)]

theorem aux_cev (t d1 d2 d3 : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    (0 ≤ d1 ∧ 0 ≤ d2 ∧ 0 ≤ d3) ↔
      ((0 ≤ t * d1 ∧ 0 ≤ -(1 - t) * d3 + t * d2 ∧ 0 ≤ d3) ∨
        (0 ≤ (1 - t) * d1 ∧ 0 ≤ d2 ∧ 0 ≤ (1 - t) * d3 - t * d2)) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    by_cases hc : 0 ≤ (1 - t) * d3 - t * d2
    · right; exact ⟨mul_nonneg (by linarith) h1, h2, hc⟩
    · left; push_neg at hc; exact ⟨mul_nonneg ht0.le h1, by linarith, h3⟩
  · rintro (⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩)
    · refine ⟨nn_of_mul ht0 e1, nn_of_mul ht0 ?_, e3⟩
      nlinarith [mul_nonneg (sub_nonneg.mpr ht1.le) e3]
    · refine ⟨nn_of_mul (sub_pos.mpr ht1) e1, e2, nn_of_mul (sub_pos.mpr ht1) ?_⟩
      nlinarith [mul_nonneg ht0.le e2]

theorem TriSet_cevian (Ax Ay Bx By Cx Cy Dx Dy t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (hDx : Dx = (1 - t) * Bx + t * Cx) (hDy : Dy = (1 - t) * By + t * Cy) :
    TriSet Ax Ay Bx By Cx Cy = TriSet Ax Ay Bx By Dx Dy ∪ TriSet Ax Ay Dx Dy Cx Cy := by
  subst hDx hDy
  ext p
  simp only [TriSet, Set.mem_union, Set.mem_setOf_eq]
  have i1 : det3 (p 0) (p 1) Bx By ((1 - t) * Bx + t * Cx) ((1 - t) * By + t * Cy)
      = t * det3 (p 0) (p 1) Bx By Cx Cy := by simp only [det3]; ring
  have i2 : det3 Ax Ay (p 0) (p 1) ((1 - t) * Bx + t * Cx) ((1 - t) * By + t * Cy)
      = -(1 - t) * det3 Ax Ay Bx By (p 0) (p 1) + t * det3 Ax Ay (p 0) (p 1) Cx Cy := by
    simp only [det3]; ring
  have i3 : det3 (p 0) (p 1) ((1 - t) * Bx + t * Cx) ((1 - t) * By + t * Cy) Cx Cy
      = (1 - t) * det3 (p 0) (p 1) Bx By Cx Cy := by simp only [det3]; ring
  have i4 : det3 Ax Ay ((1 - t) * Bx + t * Cx) ((1 - t) * By + t * Cy) (p 0) (p 1)
      = (1 - t) * det3 Ax Ay Bx By (p 0) (p 1) - t * det3 Ax Ay (p 0) (p 1) Cx Cy := by
    simp only [det3]; ring
  rw [i1, i2, i3, i4]
  exact aux_cev t _ _ _ ht0 ht1

theorem Dis.glue_line {R : Tri} {S1 S2 : Set Plane} {n1 n2 : ℕ} (h1 : Dis R S1 n1)
    (h2 : Dis R S2 n2) (px py qx qy : ℝ) (hne : px ≠ qx ∨ py ≠ qy)
    (hS1 : ∀ q ∈ S1, lineFun px py qx qy q ≤ 0) (hS2 : ∀ q ∈ S2, 0 ≤ lineFun px py qx qy q) :
    Dis R (S1 ∪ S2) (n1 + n2) := by
  obtain ⟨C1, r1, m1⟩ := h1
  obtain ⟨C2, r2, m2⟩ := h2
  refine ⟨glueByLine C1 C2 (m1.trans m2.symm) (lineFun px py qx qy)
    (lineFun_linear_ne_zero hne) (fun x hx => hS1 x (by rwa [← r1]))
    (fun x hx => hS2 x (by rwa [← r2])), ?_, ?_⟩
  · simp [r1, r2]
  · simp [m1]

/-- **Cevian gluing.**  `D = (1-t) B + t C`; the triangle `ABC` is `ABD ∪ ADC`. -/
theorem Dis_cevian {R : Tri} {n1 n2 : ℕ} (Ax Ay Bx By Cx Cy Dx Dy t : ℝ) (ht0 : 0 < t)
    (ht1 : t < 1) (hDx : Dx = (1 - t) * Bx + t * Cx) (hDy : Dy = (1 - t) * By + t * Cy)
    (h2 : 0 < det3 Ax Ay Dx Dy Cx Cy)
    (hA : Dis R (TriSet Ax Ay Bx By Dx Dy) n1) (hB : Dis R (TriSet Ax Ay Dx Dy Cx Cy) n2) :
    Dis R (TriSet Ax Ay Bx By Cx Cy) (n1 + n2) := by
  have hne : Ax ≠ Dx ∨ Ay ≠ Dy := by
    by_contra h
    push_neg at h
    obtain ⟨e1, e2⟩ := h
    have : det3 Ax Ay Dx Dy Cx Cy = 0 := by simp only [det3]; rw [← e1, ← e2]; ring
    linarith
  refine (Dis.glue_line hA hB Ax Ay Dx Dy hne ?_ ?_).congr
    (TriSet_cevian Ax Ay Bx By Cx Cy Dx Dy t ht0 ht1 hDx hDy).symm rfl
  · intro q hq
    have := hq.2.1
    simp only [det3] at this
    simp only [lineFun_apply]
    linarith
  · intro q hq
    have := hq.2.2
    simp only [det3] at this
    simp only [lineFun_apply]
    linarith

/-! ### The equilateral triangle -/

theorem tri3_eq_triset (X : ℝ) (hX : 0 < X) :
    Tri3 0 0 X = TriSet 0 0 X 0 (X / 2) (X * zs / 2) := by
  have hz := zs_pos
  have hp : 0 < X * zs / 2 := by positivity
  ext p
  simp only [Tri3, TriSet, Set.mem_setOf_eq]
  have f1 : det3 (p 0) (p 1) X 0 (X / 2) (X * zs / 2)
      = (X * zs / 2) * (X - (uu 0 0 p + vv 0 0 p)) := by
    simp only [det3, uu, vv]; field_simp; ring
  have f2 : det3 0 0 (p 0) (p 1) (X / 2) (X * zs / 2) = (X * zs / 2) * uu 0 0 p := by
    simp only [det3, uu]; field_simp; ring
  have f3 : det3 0 0 X 0 (p 0) (p 1) = (X * zs / 2) * vv 0 0 p := by
    simp only [det3, vv]; field_simp; ring
  rw [f1, f2, f3, mul_nonneg_iff_of_pos_left hp, mul_nonneg_iff_of_pos_left hp,
    mul_nonneg_iff_of_pos_left hp]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨by linarith, h1, h2⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h3, by linarith⟩

/-! ### Unit tiles and scaling -/

theorem Dis_scaled {R : Tri} (x0 y0 x1 y1 x2 y2 : ℝ) (hU : 0 < det3 x0 y0 x1 y1 x2 y2)
    (hUR : (mkTri x0 y0 x1 y1 x2 y2 hU.ne').Congruent R) (k : ℕ) (hk : 0 < k)
    (X1 Y1 X2 Y2 : ℝ) (hX1 : X1 = x0 + k * (x1 - x0)) (hY1 : Y1 = y0 + k * (y1 - y0))
    (hX2 : X2 = x0 + k * (x2 - x0)) (hY2 : Y2 = y0 + k * (y2 - y0)) :
    Dis R (TriSet x0 y0 X1 Y1 X2 Y2) (k * k) := by
  have hT : 0 < det3 x0 y0 X1 Y1 X2 Y2 := by
    have : det3 x0 y0 X1 Y1 X2 Y2 = (k : ℝ) ^ 2 * det3 x0 y0 x1 y1 x2 y2 := by
      subst hX1 hY1 hX2 hY2; simp only [det3]; ring
    rw [this]
    have : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    positivity
  subst hX1 hY1 hX2 hY2
  obtain ⟨C, hr, hm⟩ := scaledPiece (mkTri x0 y0 x1 y1 x2 y2 hU.ne') R
    (mkTri x0 y0 (x0 + k * (x1 - x0)) (y0 + k * (y1 - y0)) (x0 + k * (x2 - x0))
      (y0 + k * (y2 - y0)) hT.ne') hUR k hk (by simp [mkTri])
    (by simp [mkTri, mkPt_sub, mkPt_smul, mkPt_add])
    (by simp [mkTri, mkPt_sub, mkPt_smul, mkPt_add])
  rw [← TriSet_eq_carrier hT] at hr
  exact Dis.congr (show Dis R _ (k * k * 1) from ⟨C, hr, hm⟩) rfl (by ring)

section cong
variable {a b : ℝ}

/-- A triangle with `|01|² = a²`, `|02|² = b²`, `|12|² = a²+b²+ab` is congruent to `Rmodel`. -/
theorem unit_cong1 (ha : 0 < a) (hb : 0 < b) (x0 y0 x1 y1 x2 y2 : ℝ)
    (hU : 0 < det3 x0 y0 x1 y1 x2 y2)
    (h01 : (x1 - x0) ^ 2 + (y1 - y0) ^ 2 = a ^ 2) (h02 : (x2 - x0) ^ 2 + (y2 - y0) ^ 2 = b ^ 2)
    (h12 : (x2 - x1) ^ 2 + (y2 - y1) ^ 2 = a ^ 2 + b ^ 2 + a * b) :
    (mkTri x0 y0 x1 y1 x2 y2 hU.ne').Congruent (Rmodel ha hb) := by
  have hs := zs_sq
  refine congruent_of_sq_dist_perm ⟨![2, 1, 0], ![2, 1, 0], by decide, by decide⟩ ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Rmodel, mkTri, dist_sq_mkPt] <;> nlinarith [hs, h01, h02, h12]

/-- A triangle with `|01|² = b²`, `|02|² = a²`, `|12|² = a²+b²+ab` is congruent to `Rmodel`. -/
theorem unit_cong2 (ha : 0 < a) (hb : 0 < b) (x0 y0 x1 y1 x2 y2 : ℝ)
    (hU : 0 < det3 x0 y0 x1 y1 x2 y2)
    (h01 : (x1 - x0) ^ 2 + (y1 - y0) ^ 2 = b ^ 2) (h02 : (x2 - x0) ^ 2 + (y2 - y0) ^ 2 = a ^ 2)
    (h12 : (x2 - x1) ^ 2 + (y2 - y1) ^ 2 = a ^ 2 + b ^ 2 + a * b) :
    (mkTri x0 y0 x1 y1 x2 y2 hU.ne').Congruent (Rmodel ha hb) := by
  have hs := zs_sq
  refine congruent_of_sq_dist_perm ⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩ ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Rmodel, mkTri, dist_sq_mkPt] <;> nlinarith [hs, h01, h02, h12]

theorem Rmodel_swap (ha : 0 < a) (hb : 0 < b) : (Rmodel ha hb).Congruent (Rmodel hb ha) := by
  have hs := zs_sq
  refine congruent_of_sq_dist_perm ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩ ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Rmodel, mkTri, dist_sq_mkPt] <;> nlinarith [hs]

theorem Dis_swap {S : Set Plane} {n : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : Dis (Rmodel ha hb) S n) : Dis (Rmodel hb ha) S n := by
  obtain ⟨C, hr, hm⟩ := h
  refine ⟨{ C with model := Rmodel hb ha
                   tiles_congruent := fun i => by
                     have := C.tiles_congruent i
                     rw [hm] at this
                     exact this.trans (Rmodel_swap ha hb) }, hr, rfl⟩

end cong

/-! ### Core constructions -/

section cores
variable {a b : ℝ}

/-- **Zhang Prop. 9 core.**  Tile of scale `k` (`120°` at `O`) glued to the equilateral triangle of
side `X = k a` along `O E`; the union is the triangle `E, S=(-k b,0), Q=(X,0)`
(angles `α, 60°, α+2β` in Zhang's notation), `k² + n0` tiles. -/
theorem core9 (ha : 0 < a) (hb : 0 < b) (k : ℕ) (hk : 0 < k) (X : ℝ) (hX : X = k * a) {n0 : ℕ}
    (hE : Dis (Rmodel ha hb) (Tri3 0 0 X) n0) :
    Dis (Rmodel ha hb) (TriSet (X / 2) (X * zs / 2) (-(k * b)) 0 X 0) (k * k + n0) := by
  have hz := zs_pos
  have hs := zs_sq
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hX0 : 0 < X := by rw [hX]; positivity
  have hU : 0 < det3 0 0 (a / 2) (a * zs / 2) (-b) 0 := by
    have : det3 0 0 (a / 2) (a * zs / 2) (-b) 0 = a * b * zs / 2 := by simp only [det3]; ring
    rw [this]; positivity
  have hUR := unit_cong1 ha hb 0 0 (a / 2) (a * zs / 2) (-b) 0 hU
    (by linear_combination (a ^ 2 / 4) * hs) (by ring)
    (by linear_combination (a ^ 2 / 4) * hs)
  have htile := Dis_scaled 0 0 (a / 2) (a * zs / 2) (-b) 0 hU hUR k hk (X / 2) (X * zs / 2)
    (-(k * b)) 0 (by rw [hX]; ring) (by rw [hX]; ring) (by ring) (by ring)
  have htile' := Dis_rot _ _ _ _ _ _ htile
  have hEq := Dis_rot _ _ _ _ _ _ (Dis_rot _ _ _ _ _ _ (hE.congr (tri3_eq_triset X hX0) rfl))
  have hkb : 0 < (k : ℝ) * b := by positivity
  have hXkb : 0 < (k : ℝ) * b + X := by positivity
  refine Dis_cevian (X / 2) (X * zs / 2) (-(k * b)) 0 X 0 0 0 (k * b / (k * b + X)) ?_ ?_ ?_ ?_ ?_
    htile' hEq
  · positivity
  · rw [div_lt_one hXkb]; linarith
  · field_simp; ring
  · ring
  · have : det3 (X / 2) (X * zs / 2) 0 0 X 0 = X ^ 2 * zs / 2 := by simp only [det3]; ring
    rw [this]; positivity

/-- **Zhang Prop. 8 core.**  A second tile at the right: the isosceles triangle
`E, S=(-k b,0), Q2=(X+k b,0)`, `2 k² + n0` tiles. -/
theorem core8 (ha : 0 < a) (hb : 0 < b) (k : ℕ) (hk : 0 < k) (X : ℝ) (hX : X = k * a) {n0 : ℕ}
    (hE : Dis (Rmodel ha hb) (Tri3 0 0 X) n0) :
    Dis (Rmodel ha hb) (TriSet (X / 2) (X * zs / 2) (-(k * b)) 0 (X + k * b) 0)
      (k * k + n0 + k * k) := by
  have hz := zs_pos
  have hs := zs_sq
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hX0 : 0 < X := by rw [hX]; positivity
  have h9 := core9 ha hb k hk X hX hE
  have hU : 0 < det3 X 0 (X + b) 0 (X - a / 2) (a * zs / 2) := by
    have : det3 X 0 (X + b) 0 (X - a / 2) (a * zs / 2) = a * b * zs / 2 := by
      simp only [det3]; ring
    rw [this]; positivity
  have hUR := unit_cong2 ha hb X 0 (X + b) 0 (X - a / 2) (a * zs / 2) hU
    (by ring) (by linear_combination (a ^ 2 / 4) * hs)
    (by linear_combination (a ^ 2 / 4) * hs)
  have htile := Dis_scaled X 0 (X + b) 0 (X - a / 2) (a * zs / 2) hU hUR k hk (X + k * b) 0
    (X / 2) (X * zs / 2) (by ring) (by ring) (by rw [hX]; ring) (by rw [hX]; ring)
  have htile' := Dis_rot _ _ _ _ _ _ (Dis_rot _ _ _ _ _ _ htile)
  have hkb : 0 < (k : ℝ) * b := by positivity
  have hD : 0 < X + 2 * (k * b) := by positivity
  refine Dis_cevian (X / 2) (X * zs / 2) (-(k * b)) 0 (X + k * b) 0 X 0
    ((X + k * b) / (X + 2 * (k * b))) ?_ ?_ ?_ ?_ ?_ h9 htile'
  · positivity
  · rw [div_lt_one hD]; linarith
  · field_simp; ring
  · ring
  · have : det3 (X / 2) (X * zs / 2) X 0 (X + k * b) 0 = (X * zs / 2) * (k * b) := by
      simp only [det3]; ring
    rw [this]; positivity

/-- **Zhang Prop. 10 core.**  The Prop. 9 triangle plus a tile of scale `K` below, `120°` at `Q`,
with `K b = k (a+b)`: the triangle `S, C=(X + K a/2, -K a √3/2), E`. -/
theorem core10 (ha : 0 < a) (hb : 0 < b) (k K : ℕ) (hk : 0 < k) (hK : 0 < K) (X : ℝ)
    (hX : X = k * a) (hKb : (K : ℝ) * b = k * (a + b)) {n0 : ℕ}
    (hE : Dis (Rmodel ha hb) (Tri3 0 0 X) n0) :
    Dis (Rmodel ha hb)
      (TriSet (-(k * b)) 0 (X + K * a / 2) (-(K * a * zs / 2)) (X / 2) (X * zs / 2))
      (K * K + (k * k + n0)) := by
  have hz := zs_pos
  have hs := zs_sq
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hK' : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hX0 : 0 < X := by rw [hX]; positivity
  have h9 := Dis_rot _ _ _ _ _ _ (core9 ha hb k hk X hX hE)
  have hU : 0 < det3 X 0 (X - b) 0 (X + a / 2) (-(a * zs / 2)) := by
    have : det3 X 0 (X - b) 0 (X + a / 2) (-(a * zs / 2)) = a * b * zs / 2 := by
      simp only [det3]; ring
    rw [this]; positivity
  have hUR := unit_cong2 ha hb X 0 (X - b) 0 (X + a / 2) (-(a * zs / 2)) hU
    (by ring) (by linear_combination (a ^ 2 / 4) * hs)
    (by linear_combination (a ^ 2 / 4) * hs)
  have htile := Dis_scaled X 0 (X - b) 0 (X + a / 2) (-(a * zs / 2)) hU hUR K hK
    (-(k * b)) 0 (X + K * a / 2) (-(K * a * zs / 2))
    (by rw [hX]; linear_combination hKb) (by ring) (by ring) (by ring)
  have htile' := Dis_rot _ _ _ _ _ _ htile
  have hkK : 0 < (k : ℝ) + K := by positivity
  refine Dis_cevian (-(k * b)) 0 (X + K * a / 2) (-(K * a * zs / 2)) (X / 2) (X * zs / 2) X 0
    ((K : ℝ) / (K + k)) ?_ ?_ ?_ ?_ ?_ htile' h9
  · positivity
  · rw [div_lt_one (by positivity)]; linarith
  · field_simp; rw [hX]; ring
  · field_simp; rw [hX]; ring
  · have hb' : 0 < (k : ℝ) * b := by positivity
    have : det3 (-(k * b)) 0 X 0 (X / 2) (X * zs / 2) = (X + k * b) * (X * zs / 2) := by
      simp only [det3]; ring
    rw [this]; positivity

end cores

/-! ### Zhang Propositions 8, 9, 10 for natural `a b m` -/

/-- The tile `(a,b,c)`, `c² = a²+b²+ab`, for natural `a b` (as in `EquiConstr`). -/
noncomputable abbrev RM (a b : ℕ) (ha : 0 < a) (hb : 0 < b) : Tri :=
  Rmodel (Nat.cast_pos.mpr ha : (0 : ℝ) < a) (Nat.cast_pos.mpr hb : (0 : ℝ) < b)

section props
variable (a b m : ℕ) (ha : 0 < a) (hb : 0 < b) (hm : 0 < m)
include hm

/-- **Zhang Prop. 9 (1).**  If `m a b` is equiconstructible (`m² a b` tiles) then the triangle with
vertices `E = (X/2, X√3/2)`, `S = (-m b², 0)`, `Q = (X, 0)`, `X = m a b` (sides `mab, mbc, mb(a+b)`,
angles `α, α+β, α+2β`) carries `m² b (a+b)` tiles.  Area check: `(X + m b²) X √3/4 = m² b(a+b) ·
ab√3/4`. -/
theorem zhang_prop9_1
    (hE : EquiConstr a b ha hb ((m : ℝ) * ((a : ℝ) * b)) (m * m * (a * b))) :
    Dis (RM a b ha hb)
      (TriSet (((m : ℝ) * ((a : ℝ) * b)) / 2) (((m : ℝ) * ((a : ℝ) * b)) * zs / 2)
        (-((m : ℝ) * b * b)) 0 ((m : ℝ) * ((a : ℝ) * b)) 0) (m * m * (b * (a + b))) := by
  have := core9 (Nat.cast_pos.mpr ha) (Nat.cast_pos.mpr hb) (m * b) (Nat.mul_pos hm hb) _
    (by push_cast; ring) hE
  exact this.congr (by simp only [Nat.cast_mul]) (by ring)

/-- **Zhang Prop. 9 (2)** (`a`,`b` exchanged): vertices `E`, `S = (-m a², 0)`, `Q = (X, 0)`;
sides `mab, mac, ma(a+b)`; `m² a (a+b)` tiles. -/
theorem zhang_prop9_2
    (hE : EquiConstr a b ha hb ((m : ℝ) * ((a : ℝ) * b)) (m * m * (a * b))) :
    Dis (RM a b ha hb)
      (TriSet (((m : ℝ) * ((a : ℝ) * b)) / 2) (((m : ℝ) * ((a : ℝ) * b)) * zs / 2)
        (-((m : ℝ) * a * a)) 0 ((m : ℝ) * ((a : ℝ) * b)) 0) (m * m * (a * (a + b))) := by
  have ha' : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have hb' : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have hE' := Dis_swap ha' hb' hE
  have := core9 hb' ha' (m * a) (Nat.mul_pos hm ha) _ (by push_cast; ring) hE'
  have h2 := Dis_swap hb' ha' this
  exact h2.congr (by simp only [Nat.cast_mul]) (by ring)

/-- **Zhang Prop. 8 (1).**  Isosceles triangle `E, S = (-m b², 0), (X + m b², 0)` (sides
`mbc, mbc, mb(a+2b)`, base angles `α`), `m² b (a+2b)` tiles. -/
theorem zhang_prop8_1
    (hE : EquiConstr a b ha hb ((m : ℝ) * ((a : ℝ) * b)) (m * m * (a * b))) :
    Dis (RM a b ha hb)
      (TriSet (((m : ℝ) * ((a : ℝ) * b)) / 2) (((m : ℝ) * ((a : ℝ) * b)) * zs / 2)
        (-((m : ℝ) * b * b)) 0 (((m : ℝ) * ((a : ℝ) * b)) + (m : ℝ) * b * b) 0)
      (m * m * (b * (a + 2 * b))) := by
  have := core8 (Nat.cast_pos.mpr ha) (Nat.cast_pos.mpr hb) (m * b) (Nat.mul_pos hm hb) _
    (by push_cast; ring) hE
  exact this.congr (by simp only [Nat.cast_mul]) (by ring)

/-- **Zhang Prop. 8 (2)**: sides `mac, mac, ma(b+2a)`, `m² a (b+2a)` tiles. -/
theorem zhang_prop8_2
    (hE : EquiConstr a b ha hb ((m : ℝ) * ((a : ℝ) * b)) (m * m * (a * b))) :
    Dis (RM a b ha hb)
      (TriSet (((m : ℝ) * ((a : ℝ) * b)) / 2) (((m : ℝ) * ((a : ℝ) * b)) * zs / 2)
        (-((m : ℝ) * a * a)) 0 (((m : ℝ) * ((a : ℝ) * b)) + (m : ℝ) * a * a) 0)
      (m * m * (a * (b + 2 * a))) := by
  have ha' : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have hb' : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have hE' := Dis_swap ha' hb' hE
  have := core8 hb' ha' (m * a) (Nat.mul_pos hm ha) _ (by push_cast; ring) hE'
  have h2 := Dis_swap hb' ha' this
  exact h2.congr (by simp only [Nat.cast_mul]) (by ring)

/-- **Zhang Prop. 10 (1).**  The triangle `S=(-m a²,0), C, E` (sides `mac, (b+2a)mb, (a+b)cm`,
angles `α, 2β, 2α+β`), `C = (X + m(a+b) b/2, -m(a+b) b √3/2)`, carries `m² (a+b)(2a+b)` tiles. -/
theorem zhang_prop10_1
    (hE : EquiConstr a b ha hb ((m : ℝ) * ((a : ℝ) * b)) (m * m * (a * b))) :
    Dis (RM a b ha hb)
      (TriSet (-((m : ℝ) * a * a)) 0
        (((m : ℝ) * ((a : ℝ) * b)) + (m : ℝ) * (a + b) * b / 2)
        (-((m : ℝ) * (a + b) * b * zs / 2))
        (((m : ℝ) * ((a : ℝ) * b)) / 2) (((m : ℝ) * ((a : ℝ) * b)) * zs / 2))
      (m * m * ((a + b) * (2 * a + b))) := by
  have ha' : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have hb' : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have hE' := Dis_swap ha' hb' hE
  have := core10 hb' ha' (m * a) (m * (a + b)) (Nat.mul_pos hm ha) (Nat.mul_pos hm (by omega)) _
    (by push_cast; ring) (by push_cast; ring) hE'
  have h2 := Dis_swap hb' ha' this
  exact h2.congr (by simp only [Nat.cast_mul, Nat.cast_add]) (by ring)

/-- **Zhang Prop. 10 (2)**: triangle `S=(-m b²,0), C, E` (sides `mbc, (a+2b)ma, (a+b)cm`),
`C = (X + m(a+b) a/2, -m(a+b) a √3/2)`, `m² (a+b)(a+2b)` tiles. -/
theorem zhang_prop10_2
    (hE : EquiConstr a b ha hb ((m : ℝ) * ((a : ℝ) * b)) (m * m * (a * b))) :
    Dis (RM a b ha hb)
      (TriSet (-((m : ℝ) * b * b)) 0
        (((m : ℝ) * ((a : ℝ) * b)) + (m : ℝ) * (a + b) * a / 2)
        (-((m : ℝ) * (a + b) * a * zs / 2))
        (((m : ℝ) * ((a : ℝ) * b)) / 2) (((m : ℝ) * ((a : ℝ) * b)) * zs / 2))
      (m * m * ((a + b) * (a + 2 * b))) := by
  have := core10 (Nat.cast_pos.mpr ha) (Nat.cast_pos.mpr hb) (m * b) (m * (a + b))
    (Nat.mul_pos hm hb) (Nat.mul_pos hm (by omega)) _
    (by push_cast; ring) (by push_cast; ring) hE
  exact this.congr (by simp only [Nat.cast_mul, Nat.cast_add]) (by ring)

end props

/-! ### Witnesses `(a,b,c) = (3,5,7)`, `m = 9` (so `X = 135`, hypothesis from `zhang_thm4`) -/

theorem hE357 : EquiConstr 3 5 (by norm_num) (by norm_num)
    (((9 : ℕ) : ℝ) * (((3 : ℕ) : ℝ) * ((5 : ℕ) : ℝ))) (9 * 9 * (3 * 5)) :=
  zhang_thm4 3 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 9
    (by norm_num)

/-- Prop 9(1) witness: triangle `(135/2, 135√3/2), (-225,0), (135,0)`, `3240` tiles
(area `(360)(135)√3/4 = 12150√3 = 3240 · 15√3/4`). -/
theorem zhang_prop9_1_357 :
    Dis (RM 3 5 (by norm_num) (by norm_num))
      (TriSet (135 / 2) (135 * zs / 2) (-225) 0 135 0) 3240 :=
  (zhang_prop9_1 3 5 9 (by norm_num) (by norm_num) (by norm_num) hE357).congr
    (by norm_num) (by norm_num)

/-- Prop 9(2) witness: `(135/2, 135√3/2), (-81,0), (135,0)`, `9·9·3·8 = 1944` tiles
(area `(216)(135)√3/4 = 7290√3 = 1944 · 15√3/4`). -/
theorem zhang_prop9_2_357 :
    Dis (RM 3 5 (by norm_num) (by norm_num))
      (TriSet (135 / 2) (135 * zs / 2) (-81) 0 135 0) 1944 :=
  (zhang_prop9_2 3 5 9 (by norm_num) (by norm_num) (by norm_num) hE357).congr
    (by norm_num) (by norm_num)

/-- Prop 8(1) witness: isosceles `(135/2, 135√3/2), (-225,0), (360,0)`, `81·5·13 = 5265` tiles
(area `585·135√3/4 = 19743.75√3 = 5265 · 15√3/4`). -/
theorem zhang_prop8_1_357 :
    Dis (RM 3 5 (by norm_num) (by norm_num))
      (TriSet (135 / 2) (135 * zs / 2) (-225) 0 360 0) 5265 :=
  (zhang_prop8_1 3 5 9 (by norm_num) (by norm_num) (by norm_num) hE357).congr
    (by norm_num) (by norm_num)

/-- Prop 8(2) witness: `(135/2, 135√3/2), (-81,0), (216,0)`, `81·3·11 = 2673` tiles. -/
theorem zhang_prop8_2_357 :
    Dis (RM 3 5 (by norm_num) (by norm_num))
      (TriSet (135 / 2) (135 * zs / 2) (-81) 0 216 0) 2673 :=
  (zhang_prop8_2 3 5 9 (by norm_num) (by norm_num) (by norm_num) hE357).congr
    (by norm_num) (by norm_num)

/-- Prop 10(1) witness: `S=(-81,0)`, `C=(135+9·8·5/2, -9·8·5√3/2) = (315, -180√3)`, `E`;
`81·8·11 = 7128` tiles. -/
theorem zhang_prop10_1_357 :
    Dis (RM 3 5 (by norm_num) (by norm_num))
      (TriSet (-81) 0 315 (-(180 * zs)) (135 / 2) (135 * zs / 2)) 7128 :=
  (zhang_prop10_1 3 5 9 (by norm_num) (by norm_num) (by norm_num) hE357).congr
    (by norm_num; ring_nf) (by norm_num)

/-- Prop 10(2) witness: `S=(-225,0)`, `C=(135+9·8·3/2, -9·8·3√3/2) = (243, -108√3)`, `E`;
`81·8·13 = 8424` tiles. -/
theorem zhang_prop10_2_357 :
    Dis (RM 3 5 (by norm_num) (by norm_num))
      (TriSet (-225) 0 243 (-(108 * zs)) (135 / 2) (135 * zs / 2)) 8424 :=
  (zhang_prop10_2 3 5 9 (by norm_num) (by norm_num) (by norm_num) hE357).congr
    (by norm_num; ring_nf) (by norm_num)

end Erdos634.ZhangSporadic
