-- Draft/LaczFormalIIcWN1.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, Lemma 6.2 (`IIcNoKites`, generic angles): Route B, winding-number layer, item B1.
-- B1: the winding number of a closed polygon is integer-valued and locally constant off the polygon.  Pure Mathlib; vertices are complex numbers (bridge to `Plane` later).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2/6.3, "C-degree"), Beeson, Beeson-Zhang.
--
-- DESIGN NOTES (exact Lean statements of the highest-risk steps, written BEFORE the easy parts; none is proved here, all are comments, no `sorry`):
--
-- (R1) u = v + N via Umlaufsatz.   `turnNum p` := (1/2pi) * sum_i arg ((p(i+1)-p i)/(p i - p(i-1)))   (integer by the same telescoping as `wind_int`),
--      `SimplePoly p` := injective vertices and edges meet only in shared endpoints (consecutive) with no collinear overlap.
--      theorem umlauf (p) (hs : SimplePoly p) : (turnNum p = 1 ∨ turnNum p = -1) ∧
--         (∀ z ∉ edgeSet p, wind p z = 0 ∨ wind p z = turnNum p) ∧ (∃ z ∉ edgeSet p, wind p z = turnNum p).
--      Route: B2 (jump of wind by +-1 across an edge, sign by side), B3 (wind = 0 for |z| large), then induct on a "polygon with an ear" (n >= 4: a convex vertex
--      whose triangle meets no other vertex; delete it; turnNum unchanged, wind changes by the triangle indicator).  RISK: existence of an ear (two-ears theorem) is
--      itself a Jordan-type argument; alternative: take the lexicographically smallest vertex (strictly convex, interior angle < pi) and sweep -- cheaper, B4.
-- (R2) convexity of the innermost cycle.   For a Gamma_kite cycle family (C_i) of simple polygons with interior angles in {a+b, a+b+2g} all < pi when a+b+2g < pi:
--      theorem innermost_convex (C : Fin K → Fin (n _) → ℂ) (hs : ∀ i, SimplePoly (C i)) (hnest : ∀ i j, i ≠ j → Disjoint (edgeSet (C i)) (edgeSet (C j)))
--         (hang : ∀ i k, intAngle (C i) k < π) : ∃ i, ConvexPoly (C i) ∧ ∀ j ≠ i, ∀ z ∈ edgeSet (C j), wind (C i) z ≠ 0.
--      Route: pick i with wind(C i) support minimal (finite, nested by (R3)); all angles < pi plus turnNum = 1 gives convex via B4.  RISK: needs (R3) first.
-- (R3) nesting of disjoint cycles (adjacency of W_i on C1).   Disjoint simple polygons P, Q:  (∀ z ∈ edgeSet Q, wind P z ≠ 0) ∨ (∀ z ∈ edgeSet Q, wind P z = 0), by `wind`
--      locally constant (THIS FILE, `wind_locallyConstant`) plus connectedness of edgeSet Q (needs `edge_connected`, B5, easy: a closed chain of segments).
--      Adjacency of W_i on C1:  for E in the C1-degree, the spoke arrival order around E is the cyclic order of C1:
--      theorem spoke_adjacent (C1 : cycle) (W : Fin K → ℂ) (hW : ∀ i, W i ∈ edgeSet C1 ∨ ...)  -- exact form fixed only after B2-B4 (needs wind-sign test on vertex wedges).
--      RISK: highest; the printed argument (Laczkovich l.1370-1470) uses Fig. 7/8 pictorially.

import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.MetricSpace.Pseudo.Basic

open scoped Classical Fin.NatCast
open Complex

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

/-- The closed polygonal curve through `p 0, p 1, ..., p (n-1), p 0`. -/
def edgeSet (p : Fin n → ℂ) : Set ℂ := ⋃ i : Fin n, segment ℝ (p i) (p (i + 1))

/-- Angle subtended at `z` by the edge `p i -> p (i+1)` (principal value in `(-pi, pi]`). -/
noncomputable def angStep (p : Fin n → ℂ) (z : ℂ) (i : Fin n) : ℝ := Complex.arg ((p (i + 1) - z) / (p i - z))

/-- Total angle swept, `2 pi` times the winding number. -/
noncomputable def turnSum (p : Fin n → ℂ) (z : ℂ) : ℝ := ∑ i : Fin n, angStep p z i

/-- Winding number of the closed polygon `p` about `z` (real-valued; integer off the polygon by `wind_int`). -/
noncomputable def wind (p : Fin n → ℂ) (z : ℂ) : ℝ := turnSum p z / (2 * Real.pi)

theorem vertex_mem_edgeSet (p : Fin n → ℂ) (i : Fin n) : p i ∈ edgeSet p :=
  Set.mem_iUnion.2 ⟨i, left_mem_segment ℝ _ _⟩

theorem sub_ne_zero_of_not_mem {p : Fin n → ℂ} {z : ℂ} (hz : z ∉ edgeSet p) (i : Fin n) : p i - z ≠ 0 := by
  intro h
  exact hz (by rw [← sub_eq_zero.1 h]; exact vertex_mem_edgeSet p i)

theorem prod_ratio (p : Fin n → ℂ) (z : ℂ) (hz : z ∉ edgeSet p) :
    ∏ i : Fin n, (p (i + 1) - z) / (p i - z) = 1 := by
  rw [Finset.prod_div_distrib]
  have : ∏ i : Fin n, (p (i + 1) - z) = ∏ i : Fin n, (p i - z) :=
    Fintype.prod_equiv (Equiv.addRight (1 : Fin n)) _ _ (fun i => rfl)
  rw [this]
  exact div_self (Finset.prod_ne_zero_iff.2 fun i _ => sub_ne_zero_of_not_mem hz i)

theorem prod_ratio_norm (p : Fin n → ℂ) (z : ℂ) (hz : z ∉ edgeSet p) :
    ∏ i : Fin n, ‖(p (i + 1) - z) / (p i - z)‖ = 1 := by
  rw [← norm_prod, prod_ratio p z hz]; simp

/-- **B1 (integrality).**  Off the polygon the winding number is an integer. -/
theorem wind_int (p : Fin n → ℂ) (z : ℂ) (hz : z ∉ edgeSet p) : ∃ k : ℤ, wind p z = k := by
  have hne : ∀ i : Fin n, (p (i + 1) - z) / (p i - z) ≠ 0 := fun i =>
    div_ne_zero (sub_ne_zero_of_not_mem hz (i + 1)) (sub_ne_zero_of_not_mem hz i)
  have hexp : Complex.exp (((turnSum p z : ℝ) : ℂ) * I) = 1 := by
    have h1 : Complex.exp (((turnSum p z : ℝ) : ℂ) * I) = ∏ i : Fin n, Complex.exp ((angStep p z i : ℂ) * I) := by
      rw [turnSum, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
    rw [h1]
    have h2 : ∀ i : Fin n, Complex.exp ((angStep p z i : ℂ) * I) =
        ((p (i + 1) - z) / (p i - z)) / (‖(p (i + 1) - z) / (p i - z)‖ : ℂ) := by
      intro i
      have hn : (‖(p (i + 1) - z) / (p i - z)‖ : ℂ) ≠ 0 := by
        exact_mod_cast norm_ne_zero_iff.2 (hne i)
      rw [eq_div_iff hn, mul_comm]
      exact Complex.norm_mul_exp_arg_mul_I _
    simp_rw [h2]
    rw [Finset.prod_div_distrib, prod_ratio p z hz, ← Complex.ofReal_prod, prod_ratio_norm p z hz]
    simp
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 (by simpa [mul_comm] using hexp : Complex.exp (I * ((turnSum p z : ℝ) : ℂ)) = 1)
  refine ⟨k, ?_⟩
  have hI := congrArg Complex.im hk
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hI' : turnSum p z = k * (2 * Real.pi) := by
    have := congrArg Complex.im (show I * ((turnSum p z : ℝ) : ℂ) = k * (2 * Real.pi * I) from hk)
    simpa using this
  rw [wind, hI']
  field_simp

/-- The ratio `(p(i+1)-z)/(p i-z)` lies in the slit plane when `z` is not on the edge. -/
theorem ratio_mem_slitPlane {a b z : ℂ} (hz : z ∉ segment ℝ a b) :
    (b - z) / (a - z) ∈ Complex.slitPlane := by
  have ha : a - z ≠ 0 := fun h => hz (by rw [← sub_eq_zero.1 h]; exact left_mem_segment ℝ _ _)
  have hb : b - z ≠ 0 := fun h => hz (by rw [← sub_eq_zero.1 h]; exact right_mem_segment ℝ _ _)
  by_contra hns
  rw [Complex.mem_slitPlane_iff] at hns
  push_neg at hns
  obtain ⟨hre, him⟩ := hns
  set w := (b - z) / (a - z) with hw
  have hwne : w ≠ 0 := div_ne_zero hb ha
  have hwr : w = (w.re : ℂ) := Complex.ext (by simp) (by simpa using him)
  have hr : w.re < 0 := lt_of_le_of_ne hre (fun h => hwne (by rw [hwr, h]; simp))
  have hbw : b - z = (w.re : ℂ) * (a - z) := by
    rw [← hwr, hw]; field_simp
  apply hz
  rw [segment_eq_image]
  refine ⟨1 / (1 - w.re), ⟨by positivity [sub_pos.2 (hr.trans zero_lt_one)], ?_⟩, ?_⟩
  · rw [div_le_one (by linarith)]; linarith
  · -- z = a + t (b - a) with t = 1/(1-r):  (1-r) z = (1-r) a + (b - a)  <=>  b - z = r (a - z)
    have h1r : (1 - (w.re : ℂ)) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have : (1 - (w.re : ℂ)) * z = (1 - (w.re : ℂ)) * a + (b - a) := by linear_combination (-1 : ℂ) * hbw
    have ht : ((1 / (1 - w.re) : ℝ) : ℂ) * (1 - (w.re : ℂ)) = 1 := by
      have : (1 - w.re : ℝ) ≠ 0 := by linarith
      have h2 : (1 / (1 - w.re) : ℝ) * (1 - w.re) = 1 := by field_simp
      exact_mod_cast h2
    simp only [Complex.real_smul]
    push_cast at ht ⊢
    linear_combination (-((1 / (1 - (w.re : ℂ)) : ℂ))) * this + (-(a - z)) * ht

theorem isClosed_segment' (a b : ℂ) : IsClosed (segment ℝ a b) := by
  rw [segment_eq_image]
  exact (isCompact_Icc.image (by fun_prop)).isClosed

theorem isClosed_edgeSet (p : Fin n → ℂ) : IsClosed (edgeSet p) :=
  isClosed_iUnion_of_finite fun i => isClosed_segment' _ _

/-- The winding number is continuous off the polygon. -/
theorem wind_continuousAt (p : Fin n → ℂ) (z : ℂ) (hz : z ∉ edgeSet p) : ContinuousAt (wind p) z := by
  unfold wind turnSum angStep
  refine ContinuousAt.div_const (tendsto_finsetSum _ fun i _ => ?_) _
  have hzi : z ∉ segment ℝ (p i) (p (i + 1)) := fun h => hz (Set.mem_iUnion.2 ⟨i, h⟩)
  have hcont : ContinuousAt (fun w : ℂ => (p (i + 1) - w) / (p i - w)) z :=
    (continuousAt_const.sub continuousAt_id).div (continuousAt_const.sub continuousAt_id) (sub_ne_zero_of_not_mem hz i)
  exact ContinuousAt.comp (f := fun w : ℂ => (p (i + 1) - w) / (p i - w)) (Complex.continuousAt_arg (ratio_mem_slitPlane hzi)) hcont

/-- **B1 (local constancy).**  The winding number is constant on a neighbourhood of every point off the polygon. -/
theorem wind_locallyConstant (p : Fin n → ℂ) (z : ℂ) (hz : z ∉ edgeSet p) :
    ∃ ε > 0, ∀ z', dist z' z < ε → z' ∉ edgeSet p ∧ wind p z' = wind p z := by
  obtain ⟨δ1, hδ1, hball⟩ := Metric.isOpen_iff.1 (isClosed_edgeSet p).isOpen_compl z hz
  obtain ⟨δ2, hδ2, hc⟩ := Metric.continuousAt_iff.1 (wind_continuousAt p z hz) 1 one_pos
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun z' hd => ?_⟩
  have hz' : z' ∉ edgeSet p := hball (Metric.mem_ball.2 (lt_of_lt_of_le hd (min_le_left _ _)))
  refine ⟨hz', ?_⟩
  obtain ⟨k, hk⟩ := wind_int p z hz
  obtain ⟨k', hk'⟩ := wind_int p z' hz'
  have hlt := hc (lt_of_lt_of_le hd (min_le_right _ _))
  rw [Real.dist_eq, hk, hk'] at hlt
  have : |(k' - k : ℤ)| < 1 := by exact_mod_cast (by simpa [abs_sub_comm] using hlt : |((k' : ℝ) - k)| < 1)
  have hkk : k' = k := by have := Int.abs_lt_one_iff.1 this; omega
  rw [hk, hk', hkk]

end Erdos634.Draft.LaczFormal.WN
