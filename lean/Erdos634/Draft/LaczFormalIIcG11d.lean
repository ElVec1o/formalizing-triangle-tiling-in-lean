-- Draft/LaczFormalIIcG11d.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3 / Thm 2.1 (v), G11: an interior point of the polygon lies strictly left of every directed edge (`c_pos_of_interior`).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcL8s

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.Draft.LaczFormal.Thm21

namespace Erdos634.Draft.LaczFormal.RG

variable {M : ℕ} [NeZero M]

theorem c_pos_of_interior (P : ConvPoly M) {x : Plane} (hx : x ∈ interior P.carrier) (j : Fin M) : 0 < P.c j x := by
  have hM := P.three_le
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior _ hx
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := ConvPoly.fin_facts hM j
  have hxc : x ∈ P.carrier := interior_subset hx
  have h0 : 0 ≤ P.c j x := hxc j
  by_contra hneg
  have hz : P.c j x = 0 := le_antisymm (not_lt.mp hneg) h0
  set w := x - P.v (j + 2) with hw
  have hpos : 0 < P.c j (P.v (j + 2)) := P.c_vertex_pos f2 f3
  set t : ℝ := ε / (2 * (‖w‖ + 1)) with ht
  have ht0 : 0 < t := by positivity
  set y : Plane := (1 - (-t)) • x + (-t) • P.v (j + 2) with hy
  have hyb : y ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    have : y - x = t • w := by rw [hy, hw]; module
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos ht0, ht]
    have : ε / (2 * (‖w‖ + 1)) * ‖w‖ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith [norm_nonneg w]
    exact this
  have hyc : y ∈ P.carrier := interior_subset (hball hyb)
  have h1 := hyc j
  have hcy : P.c j y = - t * P.c j (P.v (j + 2)) := by
    rw [hy, P.c_comb, hz]; ring
  have : 0 ≤ P.c j y := h1
  rw [hcy] at this
  nlinarith

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.c_pos_of_interior
