import Erdos634.Draft.LaczFormalL33Geo
import Erdos634.Draft.LaczFormalL30All

/-!
# Laczkovich Theorem 2.5, triple `(α+β, α+β, α+β)`: the equilateral triangle is a rational similar dissection

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.5, Fig. 7), Beeson, Beeson-Zhang, Zhang.

Chart `(O; w, d)` of `LaczFormalL30Chart` (`|w| = |d| = a`, `⟨w,d⟩ = -a²/2`), `k = b/a < 1`.  Tiles `A V O` (scale `1`,
`chart_P2`), `A O Q` (scale `k`), `O N Q` (scale `k²`); the trapezoid `N V R Q` has angle `α` at `V` and `α+β` at `R`, so
`trap_ii` is applied to the tile with `α` and `β` exchanged (`RTri.sw01`) in the sub-chart `(V; R - V, N - V)` with
`W = c`, `Dd = a (1 - k³)`, `τ = k²`.
-/

namespace Erdos634.LaczL33

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL21 Erdos634.LaczL24 Erdos634.Realizable
  Erdos634.DissectionMap Erdos634.LaczL30
open Erdos634.LaczL27 (carrier_eq_of_range range_mk3)

private theorem htri' : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide

/-- the leg `Dd = a (1 - k³)` of the trapezoid. -/
noncomputable def Ddq2 (R : RTri) : ℚ := R.a * (1 - kq R ^ 3)

theorem Ddq2_pos (R : RTri) (hab : R.b < R.a) : 0 < Ddq2 R := by
  have h0 := kq_pos R
  have h1 := kq_lt_one R hab
  have : kq R ^ 3 < 1 := pow_lt_one₀ h0.le h1 (by norm_num)
  have := R.pa
  unfold Ddq2; have : 0 < 1 - kq R ^ 3 := by linarith
  positivity

theorem tTau2 (R : RTri) (hγ : R.a ^ 2 + R.a * R.b + R.b ^ 2 = R.c ^ 2) :
    tTau R.sw01.a R.sw01.b R.sw01.c R.c (Ddq2 R) = kq R ^ 2 := by
  have ha := R.pa; have hb := R.pb; have hc := R.pc
  have e : R.a ^ 2 - R.c ^ 2 = -(R.b * (R.a + R.b)) := by linear_combination hγ
  have e2 : R.c * R.b * R.c = R.b * (R.a ^ 2 + R.a * R.b + R.b ^ 2) := by rw [hγ]; ring
  simp only [tTau, RTri.sw01]
  rw [e, e2]
  unfold Ddq2 kq
  field_simp
  ring

theorem cos1_sw01 (R : RTri) : R.sw01.cos1 = (R.b ^ 2 + R.c ^ 2 - R.a ^ 2) / (2 * R.b * R.c) := by
  simp only [RTri.cos1, RTri.sw01]

section chart

variable (R : RTri) (hγ : R.a ^ 2 + R.a * R.b + R.b ^ 2 = R.c ^ 2) (hab : R.b < R.a)
  (w d : Plane) (hdet : w 0 * d 1 - w 1 * d 0 ≠ 0)
  (hw : inner ℝ w w = (R.a : ℝ) ^ 2) (hd : inner ℝ d d = (R.a : ℝ) ^ 2)
  (hwd : inner ℝ w d = (R.a : ℝ) * (R.a : ℝ) * (-1 / 2))

include hγ hab hdet hw hd hwd

theorem chart_Pb : ChartRSD R 0 w d hdet (tPb (hK0 R) (hK1 R hab)).carrier := by
  obtain ⟨hb, hc2⟩ := real_facts R hγ
  have hk0 := hK0 R
  have hk1 := hK1 R hab
  have f0 : (finRotate 3 : Equiv.Perm (Fin 3)) 0 = 1 := by decide
  have f1 : (finRotate 3 : Equiv.Perm (Fin 3)) 1 = 2 := by decide
  have f2 : (finRotate 3 : Equiv.Perm (Fin 3)) 2 = 0 := by decide
  have hks : (0 : ℝ) < ((kq R : ℚ) : ℝ) ^ 2 := by positivity
  have hdetb : det3 (-((kq R : ℚ) : ℝ)) (-((kq R : ℚ) : ℝ)) 0 0 0 (((kq R : ℚ) : ℝ) ^ 2) ≠ 0 := by
    rw [det_Pb]; positivity
  refine chart_single (R := R) (A := 0) (w := w) (d := d) (h := hdet) _
    (chart_tile R 0 w d hdet R.a R.a hw hd ((R.a : ℝ) * (R.a : ℝ) * (-1 / 2)) hwd (-((kq R : ℚ) : ℝ))
      (-((kq R : ℚ) : ℝ)) 0 0 0 (((kq R : ℚ) : ℝ) ^ 2) hdetb (finRotate 3) (kq R) (kq_pos R) ?_ ?_ ?_)
  · rw [f0, f1, R.ha]; ring
  · rw [f1, f2, R.hb, hb]; ring
  · rw [f2, f0, R.hc, hc2]; ring

theorem chart_Pc : ChartRSD R 0 w d hdet (tPc (hK0 R) (hK1 R hab)).carrier := by
  obtain ⟨hb, hc2⟩ := real_facts R hγ
  have hk0 := hK0 R
  have hk1 := hK1 R hab
  have f0 : ((finRotate 3 : Equiv.Perm (Fin 3)).symm) 0 = 2 := by decide
  have f1 : ((finRotate 3 : Equiv.Perm (Fin 3)).symm) 1 = 0 := by decide
  have f2 : ((finRotate 3 : Equiv.Perm (Fin 3)).symm) 2 = 1 := by decide
  have hdetc : det3 0 0 (((kq R : ℚ) : ℝ) ^ 3) 0 0 (((kq R : ℚ) : ℝ) ^ 2) ≠ 0 := by
    rw [det_Pc]; positivity
  refine chart_single (R := R) (A := 0) (w := w) (d := d) (h := hdet) _
    (chart_tile R 0 w d hdet R.a R.a hw hd ((R.a : ℝ) * (R.a : ℝ) * (-1 / 2)) hwd 0 0 (((kq R : ℚ) : ℝ) ^ 3) 0 0
      (((kq R : ℚ) : ℝ) ^ 2) hdetc (finRotate 3).symm (kq R ^ 2) (by have := kq_pos R; positivity) ?_ ?_ ?_)
  · rw [f0, f1, R.hb, hb]; push_cast; ring
  · rw [f1, f2, R.hc, hc2]; push_cast; ring
  · rw [f2, f0, R.ha]; push_cast; ring

end chart

#print axioms chart_Pb
#print axioms chart_Pc

end Erdos634.LaczL33
