import Erdos634.Draft.LaczFormalThm33iii3
import Erdos634.Draft.LaczFormalL33Equi
import Erdos634.Draft.LaczFormalL35Print

/-!
# Laczkovich DCG 48 (2012) Thm 3.3, "if" direction, module 1 of 4: rational tile from commensurable sines; `γ = 2π/3`

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Thm 3.1, Lemma 2.1; DCG 48 (2012) 330-372, Thm 3.3),
Beeson, Beeson-Zhang, Zhang.

* `Thm33If x y z`          : an equilateral triangle is dissected into congruent copies of a tile with angles `(x, y, z)`
                             (`Equilateral D`, `TileAngles D x y z`, any `N`).
* `rtri_of_sines`          : angles `x + y + z = π` of a triangle with `sin x = p sin z`, `sin y = q sin z` (`p, q` rational)
                             are the angles of a rational triangle `R` (`vang R.Δ i`), via `2 sin y sin z cos x = sin²y + sin²z - sin²x`.
* `thm33_if_of_equi`       : a `RatSimDiss` equilateral `T` yields `Thm33If` (Lemma 2.1 `toCongruent`, exit map).
* `thm33_if_2pi3`          : clause (iii) with `z = 2π/3` (Laczkovich Thm 2.5, triple `(α+β, α+β, α+β)`: `LaczL33.equi_all`).
-/

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
  Erdos634.Draft.LaczFormal Erdos634.LaczL35 Erdos634.LaczL22 Erdos634.CertCoord

namespace Erdos634.LaczThm33If

/-- The printed conclusion: an equilateral triangle IS tiled by the tile with angles `(x, y, z)`. -/
def Thm33If (x y z : ℝ) : Prop :=
  ∃ (N : ℕ) (D : CongruentDissection N), Equilateral D ∧ TileAngles D x y z

theorem cos_lt_one' (y : ℝ) (hy : 0 < y) (hyp : y < Real.pi) : Real.cos y < 1 := by
  have sy := Real.sin_pos_of_pos_of_lt_pi hy hyp
  have := Real.sin_sq_add_cos_sq y
  nlinarith [mul_pos sy sy, Real.cos_le_one y]

theorem sin_lt_add (x y z : ℝ) (hy : 0 < y) (hz : 0 < z) (hsum : x + y + z = Real.pi) (hx : 0 < x) :
    Real.sin x < Real.sin y + Real.sin z := by
  have hx' : x = Real.pi - (y + z) := by linarith
  have e : Real.sin x = Real.sin y * Real.cos z + Real.cos y * Real.sin z := by
    rw [hx', Real.sin_pi_sub, Real.sin_add]
  have sy := Real.sin_pos_of_pos_of_lt_pi hy (by linarith)
  have sz := Real.sin_pos_of_pos_of_lt_pi hz (by linarith)
  have cy := cos_lt_one' y hy (by linarith)
  have cz := cos_lt_one' z hz (by linarith)
  rw [e]; nlinarith [mul_pos sy (sub_pos.mpr cz), mul_pos sz (sub_pos.mpr cy)]

/-- `2 sin y sin z cos x = sin² y + sin² z - sin² x` for `x + y + z = π`. -/
theorem sine_rule_cos (x y z : ℝ) (hsum : x + y + z = Real.pi) :
    2 * Real.sin y * Real.sin z * Real.cos x = Real.sin y ^ 2 + Real.sin z ^ 2 - Real.sin x ^ 2 := by
  have hx' : x = Real.pi - (y + z) := by linarith
  have e1 : Real.sin x = Real.sin y * Real.cos z + Real.cos y * Real.sin z := by
    rw [hx', Real.sin_pi_sub, Real.sin_add]
  have e2 : Real.cos x = -(Real.cos y * Real.cos z - Real.sin y * Real.sin z) := by
    rw [hx', Real.cos_pi_sub, Real.cos_add]
  rw [e1, e2]
  have h1 := Real.sin_sq_add_cos_sq y
  have h2 := Real.sin_sq_add_cos_sq z
  linear_combination ((Real.sin y) ^ 2) * h2 + ((Real.sin z) ^ 2) * h1

theorem cos_vang2 (R : RTri) :
    Real.cos (vang R.Δ 2) = ((R.a : ℝ) ^ 2 + R.b ^ 2 - R.c ^ 2) / (2 * R.a * R.b) := by
  have ha : (R.a : ℝ) ≠ 0 := by exact_mod_cast R.pa.ne'
  have hb : (R.b : ℝ) ≠ 0 := by exact_mod_cast R.pb.ne'
  have h := EuclideanGeometry.law_cos (R.Δ.pts 0) (R.Δ.pts 2) (R.Δ.pts 1)
  have e1 : dist (R.Δ.pts 0) (R.Δ.pts 2) = R.b := by rw [dist_comm]; exact R.hb
  have e2 : dist (R.Δ.pts 1) (R.Δ.pts 2) = R.a := R.ha
  have e3 : dist (R.Δ.pts 0) (R.Δ.pts 1) = R.c := R.hc
  rw [e1, e2, e3, ← vang2] at h
  field_simp
  nlinarith [h]

/-- **A rational tile from commensurable sines.** -/
theorem rtri_of_sines (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hsum : x + y + z = Real.pi)
    (p q : ℚ) (hp : 0 < p) (hq : 0 < q) (hsx : Real.sin x = p * Real.sin z) (hsy : Real.sin y = q * Real.sin z) :
    ∃ R : RTri, vang R.Δ 0 = x ∧ vang R.Δ 1 = y ∧ vang R.Δ 2 = z := by
  have sx := Real.sin_pos_of_pos_of_lt_pi hx (by linarith)
  have sz := Real.sin_pos_of_pos_of_lt_pi hz (by linarith)
  have sy := Real.sin_pos_of_pos_of_lt_pi hy (by linarith)
  have t1 := sin_lt_add x y z hy hz hsum hx
  have t2 := sin_lt_add y x z hx hz (by linarith) hy
  have t3 := sin_lt_add z x y hx hy (by linarith) hz
  rw [hsx, hsy] at t1 t2 t3
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have i1 : p < q + 1 := by
    have : (p : ℝ) < q + 1 := by nlinarith
    exact_mod_cast this
  have i2 : q < p + 1 := by
    have : (q : ℝ) < p + 1 := by nlinarith
    exact_mod_cast this
  have i3 : (1 : ℚ) < p + q := by
    have : (1 : ℝ) < p + q := by nlinarith
    exact_mod_cast this
  obtain ⟨R, ra, rb, rc⟩ := exists_RTri_rat p q 1 hp hq one_pos i1 i2 i3
  have c0 : Real.cos (vang R.Δ 0) = Real.cos x := by
    rw [RTri.cos_vang0, ra, rb, rc]
    have h := sine_rule_cos x y z hsum
    rw [hsx, hsy] at h
    push_cast
    field_simp
    nlinarith [h, sz, mul_pos sz sz]
  have c1 : Real.cos (vang R.Δ 1) = Real.cos y := by
    rw [RTri.cos_vang1, ra, rb, rc]
    have h := sine_rule_cos y x z (by linarith)
    rw [hsx, hsy] at h
    push_cast
    field_simp
    nlinarith [h, sz, mul_pos sz sz]
  have hs := vang_sum R.Δ
  have b0 : vang R.Δ 0 = x := angle_eq_of_cos (EuclideanGeometry.angle_nonneg _ _ _) (EuclideanGeometry.angle_le_pi _ _ _)
    hx.le (by linarith) c0
  have b1 : vang R.Δ 1 = y := angle_eq_of_cos (EuclideanGeometry.angle_nonneg _ _ _) (EuclideanGeometry.angle_le_pi _ _ _)
    hy.le (by linarith) c1
  refine ⟨R, ?_, ?_, ?_⟩
  · exact b0
  · exact b1
  · linarith [b0, b1]

/-- A `RatSimDiss` equilateral triangle gives the printed conclusion for the tile `R`. -/
theorem thm33_if_of_equi (R : RTri) (T : Tri) (h : RatSimDiss R.Δ T.carrier)
    (a0 : cornerAngle (T.pts 1) (T.pts 0) (T.pts 2) = Real.pi / 3)
    (a1 : cornerAngle (T.pts 2) (T.pts 1) (T.pts 0) = Real.pi / 3)
    (a2 : cornerAngle (T.pts 0) (T.pts 2) (T.pts 1) = Real.pi / 3) :
    Thm33If (vang R.Δ 0) (vang R.Δ 1) (vang R.Δ 2) := by
  obtain ⟨q, hq, M, C, hC1, hC2⟩ := RatSimDiss.toCongruent R.rational h
  refine ⟨M, C.toCongruentDissection T hC1, ?_, ?_⟩
  · intro k
    have htri : ∀ y : Fin 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide
    rcases htri k with rfl | rfl | rfl
    · exact a0
    · exact a1
    · exact a2
  · refine ⟨Equiv.refl _, ?_, ?_, ?_⟩
    all_goals
      show cornerAngle _ _ _ = _
      simp only [CongruentRegionDissection.toCongruentDissection, hC2]
    · exact Erdos634.BeesonCor5.angle_scale R.Δ _ (one_div_pos.mpr (Nat.cast_pos.mpr hq)) 1 0 2 (by decide) (by decide)
    · exact Erdos634.BeesonCor5.angle_scale R.Δ _ (one_div_pos.mpr (Nat.cast_pos.mpr hq)) 2 1 0 (by decide) (by decide)
    · exact Erdos634.BeesonCor5.angle_scale R.Δ _ (one_div_pos.mpr (Nat.cast_pos.mpr hq)) 0 2 1 (by decide) (by decide)

/-- **Clause (iii), `z = 2π/3`.**  A rational tile with angle `2π/3` at vertex 2 tiles an equilateral triangle. -/
theorem thm33_if_rtri_2pi3 (R : RTri) (hz : vang R.Δ 2 = 2 * Real.pi / 3) :
    Thm33If (vang R.Δ 0) (vang R.Δ 1) (vang R.Δ 2) := by
  have hc := cos_vang2 R
  rw [hz] at hc
  have hcos : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num
  rw [hcos] at hc
  have ha : (R.a : ℝ) ≠ 0 := by exact_mod_cast R.pa.ne'
  have hb : (R.b : ℝ) ≠ 0 := by exact_mod_cast R.pb.ne'
  have hq : R.a ^ 2 + R.a * R.b + R.b ^ 2 = R.c ^ 2 := by
    have : (R.a : ℝ) ^ 2 + R.a * R.b + R.b ^ 2 = R.c ^ 2 := by
      field_simp at hc; nlinarith [hc]
    exact_mod_cast this
  obtain ⟨T, h1, -, a0, a1, a2⟩ := Erdos634.LaczL33.equi_all R hq
  exact thm33_if_of_equi R T h1 a0 a1 a2

theorem thm33_if_2pi3 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hsum : x + y + z = Real.pi)
    (hz3 : z = 2 * Real.pi / 3) (p q : ℚ) (hp : 0 < p) (hq : 0 < q) (hsx : Real.sin x = p * Real.sin z)
    (hsy : Real.sin y = q * Real.sin z) : Thm33If x y z := by
  obtain ⟨R, r0, r1, r2⟩ := rtri_of_sines x y z hx hy hz hsum p q hp hq hsx hsy
  have := thm33_if_rtri_2pi3 R (by rw [r2, hz3])
  rwa [r0, r1, r2] at this

#print axioms Erdos634.LaczThm33If.rtri_of_sines
#print axioms Erdos634.LaczThm33If.thm33_if_2pi3

end Erdos634.LaczThm33If
