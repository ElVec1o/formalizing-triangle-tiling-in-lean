import Erdos634.Draft.ZhangRat4Prop11Derived

/-!
# Zhang Prop 11: the "angles" clause as a separate statement

arXiv 2512.22696v4, Prop. 11 (1): the triangle with sides `(c^2 m, (a+2b) m c, 3(a+b) m b)` has angles
`(alpha, 2 alpha, 3 beta)`; (2): sides `(c^2 m, (b+2a) m c, 3(a+b) m a)`, angles `(beta, 2 beta, 3 alpha)`
(angle opposite each listed side, in that order).  Here, for points `A B C` with
`|AB| = c^2 m`, `|AC| = (p+2q) m c`, `|BC| = 3(p+q) q m` (`c^2 = p^2+pq+q^2`): the angle at `C`
(opposite `AB`) is `arccos((p+2q)/(2c))`, the angle at `B` (opposite `AC`) is twice that, the angle at
`A` (opposite `BC`) is `3 arccos((2p+q)/(2c))`.  With `(p,q) = (a,b)` and the tile `T=(a,b,c)`
(`angleAt T 0 = alpha`, `angleAt T 1 = beta`) this is part (1); with `(p,q) = (b,a)` part (2).
UNAUDITED.  Credit Zhang (arXiv 2512.22696v4), Beeson, Beeson-Zhang, Laczkovich.
-/

namespace Erdos634.ZhangRat4

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.ZhangRat3 Erdos634.TilePlacement

theorem cosang (X V Y : Plane) {u w s : ℝ} (hu : dist X V = u) (hw : dist Y V = w) (hs : dist X Y = s)
    (hu0 : 0 < u) (hw0 : 0 < w) :
    Real.cos (EuclideanGeometry.angle X V Y) = (u ^ 2 + w ^ 2 - s ^ 2) / (2 * u * w) := by
  have h := EuclideanGeometry.law_cos X V Y
  rw [hu, hw, hs] at h
  field_simp
  nlinarith [h]

theorem angle_eq_arccos (X V Y : Plane) {x : ℝ} (h : Real.cos (EuclideanGeometry.angle X V Y) = x) :
    EuclideanGeometry.angle X V Y = Real.arccos x := by
  rw [← h, Real.arccos_cos (EuclideanGeometry.angle_nonneg _ _ _) (EuclideanGeometry.angle_le_pi _ _ _)]

theorem tri_angles (A B C : Plane) (p q c m : ℝ) (hp : 0 < p) (hq : 0 < q) (hc0 : 0 < c) (hm : 0 < m)
    (hc : c ^ 2 = p ^ 2 + p * q + q ^ 2)
    (hAB : dist A B = c ^ 2 * m) (hAC : dist A C = (p + 2 * q) * m * c)
    (hBC : dist B C = 3 * (p + q) * q * m) :
    EuclideanGeometry.angle A C B = Real.arccos ((p + 2 * q) / (2 * c)) ∧
    EuclideanGeometry.angle C B A = 2 * Real.arccos ((p + 2 * q) / (2 * c)) ∧
    EuclideanGeometry.angle B A C = 3 * Real.arccos ((2 * p + q) / (2 * c)) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hCA : dist C A = (p + 2 * q) * m * c := (dist_comm C A).trans hAC
  have hBA : dist B A = c ^ 2 * m := (dist_comm B A).trans hAB
  have hCB : dist C B = 3 * (p + q) * q * m := (dist_comm C B).trans hBC
  set x : ℝ := (p + 2 * q) / (2 * c) with hx
  set y : ℝ := (2 * p + q) / (2 * c) with hy
  have hxpos : 0 < x := by positivity
  have hypos : 0 < y := by positivity
  have hy1 : y ≤ 1 := by
    rw [hy, div_le_one (by positivity)]
    nlinarith [sq_nonneg (c - (2 * p + q)), mul_pos hp hq]
  have hy2 : 1 / 2 ≤ y := by
    rw [hy, le_div_iff₀ (by positivity)]
    nlinarith [mul_pos hp hq, sq_nonneg (c - (2 * p + q)), mul_pos hp hp]
  -- angle at C
  have hCcos : Real.cos (EuclideanGeometry.angle A C B) = x := by
    rw [cosang A C B (u := (p + 2 * q) * m * c) (w := 3 * (p + q) * q * m) (s := c ^ 2 * m)
      hAC hBC hAB (by positivity) (by positivity)]
    rw [hx, div_eq_div_iff (by positivity) (by positivity)]
    have : c ^ 2 = c ^ 2 := rfl
    have e : ((p + 2 * q) * m * c) ^ 2 + (3 * (p + q) * q * m) ^ 2 - (c ^ 2 * m) ^ 2
        = 3 * (p + 2 * q) ^ 2 * (p + q) * q * m ^ 2 := by
      linear_combination m ^ 2 * ((p + 2 * q) ^ 2 - (c ^ 2 + (p ^ 2 + p * q + q ^ 2))) * hc
    rw [e]; ring
  have hθ : EuclideanGeometry.angle A C B = Real.arccos x := angle_eq_arccos _ _ _ hCcos
  have hθ0 := EuclideanGeometry.angle_nonneg A C B
  have hθ1 := EuclideanGeometry.angle_le_pi A C B
  have hθhalf : EuclideanGeometry.angle A C B ≤ Real.pi / 2 := by
    by_contra hcon
    push Not at hcon
    have := Real.cos_neg_of_pi_div_two_lt_of_lt hcon (by linarith [Real.pi_pos])
    linarith
  -- angle at B
  have hBcos : Real.cos (EuclideanGeometry.angle C B A) = 2 * x ^ 2 - 1 := by
    rw [cosang C B A (u := 3 * (p + q) * q * m) (w := c ^ 2 * m) (s := (p + 2 * q) * m * c)
      hCB hAB hCA
      (by positivity) (by positivity)]
    rw [hx, div_eq_iff (by positivity)]
    have e : (3 * (p + q) * q * m) ^ 2 + (c ^ 2 * m) ^ 2 - ((p + 2 * q) * m * c) ^ 2
        = 3 * (p + q) * q * m ^ 2 * ((p + 2 * q) ^ 2 - 2 * c ^ 2) := by
      linear_combination m ^ 2 * (c ^ 2 + (p ^ 2 + p * q + q ^ 2) - (p + 2 * q) ^ 2 + 6 * (p + q) * q) * hc
    rw [e]
    field_simp
    try ring
  have hB2 : EuclideanGeometry.angle C B A = 2 * EuclideanGeometry.angle A C B := by
    apply Real.injOn_cos ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
      ⟨by linarith, by linarith⟩
    rw [hBcos, Real.cos_two_mul, hCcos]
  -- angle at A
  have hφ : Real.cos (Real.arccos y) = y := Real.cos_arccos (by linarith) hy1
  have hφ0 : 0 ≤ Real.arccos y := Real.arccos_nonneg y
  have hφ3 : Real.arccos y ≤ Real.pi / 3 := by
    by_contra hcon
    push Not at hcon
    have h1 := Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith [Real.pi_pos]) (Real.arccos_le_pi y) hcon
    rw [Real.cos_pi_div_three, hφ] at h1
    linarith
  have hAcos : Real.cos (EuclideanGeometry.angle B A C) = 4 * y ^ 3 - 3 * y := by
    rw [cosang B A C (u := c ^ 2 * m) (w := (p + 2 * q) * m * c) (s := 3 * (p + q) * q * m)
      hBA hCA hBC (by positivity) (by positivity)]
    rw [hy, div_eq_iff (by positivity)]
    have e : (c ^ 2 * m) ^ 2 + ((p + 2 * q) * m * c) ^ 2 - (3 * (p + q) * q * m) ^ 2
        = (p + 2 * q) * (2 * p + q) * ((2 * p + q) ^ 2 - 3 * c ^ 2) * m ^ 2 := by
      linear_combination m ^ 2 * (c ^ 2 + (p ^ 2 + p * q + q ^ 2) + (p + 2 * q) ^ 2
        + 3 * (p + 2 * q) * (2 * p + q)) * hc
    rw [e]
    field_simp
    try ring
  have hA3 : EuclideanGeometry.angle B A C = 3 * Real.arccos y := by
    apply Real.injOn_cos ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
      ⟨by linarith, by linarith [Real.pi_pos]⟩
    rw [hAcos, Real.cos_three_mul, hφ]
  exact ⟨hθ, by rw [hB2, hθ], hA3⟩

section tile
variable (R : RTri) (hrel : R.c ^ 2 = R.a ^ 2 + R.b ^ 2 + R.a * R.b)
include hrel

theorem tile_angle0 : angleAt R.Δ 0 = Real.arccos (((R.a : ℝ) + 2 * R.b) / (2 * R.c)) := by
  have hcR : (R.c : ℝ) ^ 2 = (R.a : ℝ) ^ 2 + (R.b : ℝ) ^ 2 + R.a * R.b := by exact_mod_cast hrel
  have h := cosang (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) (u := (R.c : ℝ)) (w := (R.b : ℝ)) (s := (R.a : ℝ))
    (by rw [dist_comm]; exact R.hc) R.hb R.ha
    (by exact_mod_cast R.pc) (by exact_mod_cast R.pb)
  have hb0 : (0 : ℝ) < R.b := by exact_mod_cast R.pb
  have hc0 : (0 : ℝ) < R.c := by exact_mod_cast R.pc
  unfold angleAt cornerAngle
  refine angle_eq_arccos _ _ _ ?_
  rw [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl]
  rw [h, div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (2 * (R.c : ℝ)) * hcR

theorem tile_angle1 : angleAt R.Δ 1 = Real.arccos ((2 * (R.a : ℝ) + R.b) / (2 * R.c)) := by
  have hcR : (R.c : ℝ) ^ 2 = (R.a : ℝ) ^ 2 + (R.b : ℝ) ^ 2 + R.a * R.b := by exact_mod_cast hrel
  have h := cosang (R.Δ.pts 2) (R.Δ.pts 1) (R.Δ.pts 0) (u := (R.a : ℝ)) (w := (R.c : ℝ)) (s := (R.b : ℝ))
    (by rw [dist_comm]; exact R.ha) R.hc R.hb
    (by exact_mod_cast R.pa) (by exact_mod_cast R.pc)
  have ha0 : (0 : ℝ) < R.a := by exact_mod_cast R.pa
  have hc0 : (0 : ℝ) < R.c := by exact_mod_cast R.pc
  unfold angleAt cornerAngle
  refine angle_eq_arccos _ _ _ ?_
  rw [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl]
  rw [h, div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (2 * (R.c : ℝ)) * hcR

/-- **Zhang Prop 11 (1), angles clause**: triangle `(c^2 m, (a+2b) m c, 3(a+b) m b)` has angles
`(alpha, 2 alpha, 3 beta)` (opposite `AB`, `AC`, `BC`). -/
theorem prop11_1_angles (A B C : Plane) (m : ℝ) (hm : 0 < m)
    (hAB : dist A B = (R.c : ℝ) ^ 2 * m) (hAC : dist A C = ((R.a : ℝ) + 2 * R.b) * m * R.c)
    (hBC : dist B C = 3 * ((R.a : ℝ) + R.b) * R.b * m) :
    EuclideanGeometry.angle A C B = angleAt R.Δ 0 ∧ EuclideanGeometry.angle C B A = 2 * angleAt R.Δ 0 ∧
      EuclideanGeometry.angle B A C = 3 * angleAt R.Δ 1 := by
  have hcR : (R.c : ℝ) ^ 2 = (R.a : ℝ) ^ 2 + (R.b : ℝ) ^ 2 + R.a * R.b := by exact_mod_cast hrel
  have := tri_angles A B C R.a R.b R.c m (by exact_mod_cast R.pa) (by exact_mod_cast R.pb)
    (by exact_mod_cast R.pc) hm (by rw [hcR]; ring) hAB hAC hBC
  rw [tile_angle0 R hrel, tile_angle1 R hrel]
  exact this

/-- **Zhang Prop 11 (2), angles clause**: triangle `(c^2 m, (b+2a) m c, 3(a+b) m a)` has angles
`(beta, 2 beta, 3 alpha)`. -/
theorem prop11_2_angles (A B C : Plane) (m : ℝ) (hm : 0 < m)
    (hAB : dist A B = (R.c : ℝ) ^ 2 * m) (hAC : dist A C = ((R.b : ℝ) + 2 * R.a) * m * R.c)
    (hBC : dist B C = 3 * ((R.a : ℝ) + R.b) * R.a * m) :
    EuclideanGeometry.angle A C B = angleAt R.Δ 1 ∧ EuclideanGeometry.angle C B A = 2 * angleAt R.Δ 1 ∧
      EuclideanGeometry.angle B A C = 3 * angleAt R.Δ 0 := by
  have hcR : (R.c : ℝ) ^ 2 = (R.a : ℝ) ^ 2 + (R.b : ℝ) ^ 2 + R.a * R.b := by exact_mod_cast hrel
  have hcR' : (R.c : ℝ) ^ 2 = (R.b : ℝ) ^ 2 + (R.b : ℝ) * R.a + (R.a : ℝ) ^ 2 := by rw [hcR]; ring
  have := tri_angles A B C R.b R.a R.c m (by exact_mod_cast R.pb) (by exact_mod_cast R.pa)
    (by exact_mod_cast R.pc) hm hcR' hAB hAC (by rw [hBC]; ring)
  rw [tile_angle0 R hrel, tile_angle1 R hrel]
  have e1 : ((R.b : ℝ) + 2 * R.a) = 2 * R.a + R.b := by ring
  have e2 : (2 * (R.b : ℝ) + R.a) = R.a + 2 * R.b := by ring
  rw [e1, e2] at this
  exact this

end tile

end Erdos634.ZhangRat4

#print axioms Erdos634.ZhangRat4.tri_angles
#print axioms Erdos634.ZhangRat4.prop11_1_angles
#print axioms Erdos634.ZhangRat4.prop11_2_angles
