import Erdos634.Draft.LaczFormalL30Geo
import Erdos634.Draft.LaczFormalL25Thm

/-!
# Laczkovich Theorem 2.5, triple `(2α, 2β, α+β)`: the three tiles in the Gram chart

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.5, Fig. 7), Beeson, Beeson-Zhang, Zhang.

`R` a rational tile with `γ = 2π/3` (`c² = a² + ab + b²`) and `b < a`.  Chart `(O; w, d)`, `|w| = |d| = a`,
`⟨w, d⟩ = -a²/2`, `k = b/a`.  The tiles `A O M`, `A V O` (scale `1`) and `V L O'` (scale `ν`) of `LaczFormalL30Geo`.
-/

namespace Erdos634.LaczL30

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL21 Erdos634.LaczL24 Erdos634.Realizable
open Erdos634.LaczL27 (carrier_eq_of_range range_mk3)

/-- `k = b / a`. -/
noncomputable def kq (R : RTri) : ℚ := R.b / R.a

theorem kq_pos (R : RTri) : 0 < kq R := by have := R.pa; have := R.pb; unfold kq; positivity

theorem kq_lt_one (R : RTri) (hab : R.b < R.a) : kq R < 1 := by
  have := R.pa; unfold kq; rw [div_lt_one this]; exact hab

theorem hK0 (R : RTri) : (0 : ℝ) < ((kq R : ℚ) : ℝ) := by exact_mod_cast kq_pos R

theorem hK1 (R : RTri) (hab : R.b < R.a) : ((kq R : ℚ) : ℝ) < 1 := by exact_mod_cast kq_lt_one R hab

/-- the scale `ν = a (a + 2b) / (b (2a + b))` of the tile `V L O'`. -/
noncomputable def nuq (R : RTri) : ℚ := R.a * (R.a + 2 * R.b) / (R.b * (2 * R.a + R.b))

theorem nuq_pos (R : RTri) : 0 < nuq R := by
  have := R.pa; have := R.pb; unfold nuq; positivity

theorem nuq_cast (R : RTri) : ((nuq R : ℚ) : ℝ) = nu ((kq R : ℚ) : ℝ) := by
  have ha : (0 : ℝ) < R.a := by exact_mod_cast R.pa
  have hb : (0 : ℝ) < R.b := by exact_mod_cast R.pb
  have h2 : (0 : ℝ) < 2 * R.a + R.b := by linarith
  unfold nuq nu kq
  push_cast
  field_simp

section chart

variable (R : RTri) (hγ : R.a ^ 2 + R.a * R.b + R.b ^ 2 = R.c ^ 2) (hab : R.b < R.a)
  (w d : Plane) (hdet : w 0 * d 1 - w 1 * d 0 ≠ 0)
  (hw : inner ℝ w w = (R.a : ℝ) ^ 2) (hd : inner ℝ d d = (R.a : ℝ) ^ 2)
  (hwd : inner ℝ w d = (R.a : ℝ) * (R.a : ℝ) * (-1 / 2))

include hγ

theorem real_facts :
    (R.b : ℝ) = ((kq R : ℚ) : ℝ) * (R.a : ℝ) ∧
    (R.c : ℝ) ^ 2 = (R.a : ℝ) ^ 2 * (1 + ((kq R : ℚ) : ℝ) + ((kq R : ℚ) : ℝ) ^ 2) := by
  have ha := R.pa
  have ha' : (R.a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hγR : (R.a : ℝ) ^ 2 + R.a * R.b + R.b ^ 2 = (R.c : ℝ) ^ 2 := by exact_mod_cast hγ
  have hb : (R.b : ℝ) = ((kq R : ℚ) : ℝ) * (R.a : ℝ) := by
    unfold kq; push_cast; field_simp
  refine ⟨hb, ?_⟩
  rw [← hγR, hb]; ring

omit hγ

/-- `(σ 0, σ 1, σ 2)` for the swap of `1` and `2`. -/
theorem swap12 : (Equiv.swap (1 : Fin 3) 2) 0 = 0 ∧ (Equiv.swap (1 : Fin 3) 2) 1 = 2 ∧ (Equiv.swap (1 : Fin 3) 2) 2 = 1 := by
  decide

include hγ hab hdet hw hd hwd

theorem chart_P1 :
    ChartRSD R 0 w d hdet (tP1 (hK0 R) (hK1 R hab)).carrier := by
  obtain ⟨hb, hc2⟩ := real_facts R hγ
  have hk0 := hK0 R
  have ha := R.pa
  have ha' : (0 : ℝ) < (R.a : ℝ) := by exact_mod_cast ha
  obtain ⟨s0, s1, s2⟩ := swap12
  refine chart_single (R := R) (A := 0) (w := w) (d := d) (h := hdet) _
    (chart_tile R 0 w d hdet R.a R.a hw hd ((R.a : ℝ) * (R.a : ℝ) * (-1 / 2)) hwd (-((kq R : ℚ) : ℝ))
      (-((kq R : ℚ) : ℝ)) 0 0 0 1 (by rw [det_P1]; exact hk0.ne') (Equiv.swap 1 2) 1 one_pos ?_ ?_ ?_)
  · rw [s0, s1]; rw [dist_comm, R.hb]; simp only [Rat.cast_one]; rw [hb]; ring
  · rw [s1, s2]; rw [dist_comm, R.ha]; simp only [Rat.cast_one]; ring
  · rw [s2, s0]; rw [dist_comm, R.hc]; simp only [Rat.cast_one]
    rw [hc2]; ring


theorem chart_P2 : ChartRSD R 0 w d hdet (tP2 (hK0 R) (hK1 R hab)).carrier := by
  obtain ⟨hb, hc2⟩ := real_facts R hγ
  have hk0 := hK0 R
  refine chart_single (R := R) (A := 0) (w := w) (d := d) (h := hdet) _
    (chart_tile R 0 w d hdet R.a R.a hw hd ((R.a : ℝ) * (R.a : ℝ) * (-1 / 2)) hwd (-((kq R : ℚ) : ℝ))
      (-((kq R : ℚ) : ℝ)) 1 0 0 0 (by rw [det_P2]; exact hk0.ne') 1 1 one_pos ?_ ?_ ?_)
  · simp only [Equiv.Perm.coe_one, id_eq, Rat.cast_one]; rw [R.hc, hc2]; ring
  · simp only [Equiv.Perm.coe_one, id_eq, Rat.cast_one]; rw [R.ha]; ring
  · simp only [Equiv.Perm.coe_one, id_eq, Rat.cast_one]; rw [R.hb, hb]; ring

theorem chart_P3 : ChartRSD R 0 w d hdet (tP3 (hK0 R) (hK1 R hab)).carrier := by
  obtain ⟨hb, hc2⟩ := real_facts R hγ
  have hk0 := hK0 R
  have hk1 := hK1 R hab
  have hn := nu_pos hk0 hk1
  have ht := th_pos hk0 hk1
  have h1t := th_lt_one hk0 hk1
  have h1 : ((kq R : ℚ) : ℝ) ≠ 0 := hk0.ne'
  have h2 : (2 : ℝ) + ((kq R : ℚ) : ℝ) ≠ 0 := by linarith
  have hnc := nuq_cast R
  refine chart_single (R := R) (A := 0) (w := w) (d := d) (h := hdet) _
    (chart_tile R 0 w d hdet R.a R.a hw hd ((R.a : ℝ) * (R.a : ℝ) * (-1 / 2)) hwd 1 0 (th ((kq R : ℚ) : ℝ))
      (nu ((kq R : ℚ) : ℝ)) (th ((kq R : ℚ) : ℝ)) 0
      (by rw [det_P3]; exact (mul_pos (sub_pos.mpr h1t) hn).ne') 1 (nuq R) (nuq_pos R) ?_ ?_ ?_)
  · simp only [Equiv.Perm.coe_one, id_eq]; rw [R.hc, hc2, hnc]; unfold th nu; field_simp; ring
  · simp only [Equiv.Perm.coe_one, id_eq]; rw [R.ha, hnc]; ring
  · simp only [Equiv.Perm.coe_one, id_eq]; rw [R.hb, hb, hnc]; unfold th nu; field_simp; ring

end chart

end Erdos634.LaczL30
