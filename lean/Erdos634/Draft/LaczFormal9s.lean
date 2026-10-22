import Erdos634.Draft.LaczFormal9r
import Erdos634.Draft.LaczFormalL24Main

/-!
# Laczkovich DM 140 (1995), Theorem 2.3: the trapezoid (Lemma 2.2 (iii)) and the chart assembly of Fig. 3

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.3, Fig. 3, Lemma 2.2 (iii)), Beeson, Beeson-Zhang, Zhang.
Formalization debt, not /goal progress.
-/

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL24 Erdos634.LaczL21 Erdos634.Realizable
  Erdos634.Laczkovich9n Erdos634.Laczkovich9o Erdos634.Laczkovich9p Erdos634.Laczkovich9q Erdos634.Laczkovich9r

namespace Erdos634.Laczkovich9s

section assembly
variable (R : RTri) (k : ℚ) (hk : (1 : ℚ) / 2 < k)
  (hB : R.b = 2 * k * R.a) (hC : R.c = (4 * k ^ 2 - 1) * R.a)
  (A w d : Plane) (h : w 0 * d 1 - w 1 * d 0 ≠ 0)
  (hw : inner ℝ w w = ((qW R.a k : ℚ) : ℝ) ^ 2) (hd : inner ℝ d d = ((qD R.a k : ℚ) : ℝ) ^ 2)
  (hwd : inner ℝ w d = ((qG R.a k : ℚ) : ℝ))

include hk hB hC hw hd hwd

theorem trap_chart : ChartRSD R A w d h (trapSet (wt (cR k))) := by
  have hcp := cR_pos hk
  have hcq : (0 : ℚ) < 4 * k ^ 2 - 1 := by nlinarith
  have hkq : (0 : ℚ) < k := by linarith
  have hra : (0 : ℚ) < R.a := R.pa
  have hcq' : (4 * k ^ 2 - 1) ≠ 0 := hcq.ne'
  have hkq' : k ≠ 0 := hkq.ne'
  have hra' : R.a ≠ 0 := hra.ne'
  have hWpos : 0 < qW R.a k := by unfold qW; positivity
  have hDpos : 0 < qD R.a k := by unfold qD; positivity
  have hcos : R.sw01.cos1 = k := by
    set cc : ℚ := 4 * k ^ 2 - 1 with hccdef
    have hccpos : 0 < cc := hcq
    simp only [RTri.cos1, RTri.sw01, hB, hC]
    rw [div_eq_iff (by positivity)]
    rw [hccdef]; ring
  have hwd' : inner ℝ w d = ((qW R.a k : ℚ) : ℝ) * ((qD R.a k : ℚ) : ℝ) * (R.sw01.cos1 : ℝ) := by
    rw [hwd, hcos]; unfold qG; push_cast; ring
  have hτ : tTauI R.sw01.a R.sw01.b R.sw01.c (qW R.a k) (qD R.a k)
      = (4 * k ^ 2 - 1) ^ 2 / ((4 * k ^ 2 - 1) ^ 2 + 1) := by
    set cc : ℚ := 4 * k ^ 2 - 1 with hccdef
    have hccpos : 0 < cc := hcq
    have hccne : cc ≠ 0 := hccpos.ne'
    simp only [tTauI, RTri.sw01, hB, hC, qW, qD, ← hccdef]
    field_simp
    rw [hccdef]; ring
  have hτpos : 0 < tTauI R.sw01.a R.sw01.b R.sw01.c (qW R.a k) (qD R.a k) := by
    rw [hτ]; positivity
  have key := trap_iii R.sw01 A w d h (qW R.a k) (qD R.a k) hWpos hDpos hw hd hwd' hτpos
  have e : ((tTauI R.sw01.a R.sw01.b R.sw01.c (qW R.a k) (qD R.a k) : ℚ) : ℝ) = wt (cR k) := by
    rw [hτ]; unfold wt cR; push_cast; ring
  rw [e] at key
  exact RatSimDiss.relabel (Δ := R.Δ) (Equiv.swap 0 1) key

theorem tgt_chart : ChartRSD R A w d h (triT (cR k) (cR_pos hk)).carrier := by
  have hcp := cR_pos hk
  have hcT : ∀ T : Tri, IsClosed T.carrier := fun T => T.isCompact.isClosed
  have c1 := trap_chart R k hk hB hC A w d h hw hd hwd
  have c2 := chart_single (R := R) (A := A) (w := w) (d := d) (h := h) _ (tile_ABC R k hk hB hC A w d h hw hd hwd)
  have c3 := chart_single (R := R) (A := A) (w := w) (d := d) (h := h) _ (tile_BCD R k hk hB hC A w d h hw hd hwd)
  have c4 := chart_single (R := R) (A := A) (w := w) (d := d) (h := h) _ (tile_BDE R k hk hB hC A w d h hw hd hwd)
  have c5 := chart_single (R := R) (A := A) (w := w) (d := d) (h := h) _ (tile_DEF R k hk hB hC A w d h hw hd hwd)
  have hcl1 := isClosed_trapSet (wt (cR k))
  have hcl2 := hcl1.union (hcT (triABC (cR k) hcp))
  have hcl3 := hcl2.union (hcT (triBCD (cR k) hcp))
  have u2 := chart_union c1 c2 (d_tr_P1 hcp)
  have d3 := disjoint_interior_union hcl1 (d_tr_P2 hcp) (d_P1_P2 hcp).symm
  have u3 := chart_union u2 c3 d3
  have d4 := disjoint_interior_union hcl2
    (disjoint_interior_union hcl1 (d_tr_P3 hcp) (d_P1_P3 hcp).symm) (d_P2_P3 hcp).symm
  have u4 := chart_union u3 c4 d4
  have d5 := disjoint_interior_union hcl3
    (disjoint_interior_union hcl2 (disjoint_interior_union hcl1 (d_tr_P4 hcp) (d_P1_P4 hcp).symm)
      (d_P2_P4 hcp).symm) (d_P3_P4 hcp)
  have u5 := chart_union u4 c5 d5
  exact chart_mono_eq u5 (Set.Subset.antisymm (pieces_sub hcp) (cover hcp))

end assembly

end Erdos634.Laczkovich9s

#print axioms Erdos634.Laczkovich9s.tgt_chart
#print axioms Erdos634.Laczkovich9r.tile_BDE
