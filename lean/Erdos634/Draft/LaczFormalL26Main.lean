import Erdos634.Draft.LaczFormalL26Tiles

/-!
# Laczkovich Theorem 2.4, fourth triple: the trapezoid and the assembly

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.4, Fig. 5), Beeson (arXiv 1206.2229,
Sect. 13.3, Theorem 23), Beeson-Zhang, Zhang.

`chart_FG`: the trapezoid `L R Q S` (Lemma 2.2 (ii), `trap_ii` for the swapped triangle `R.sw01`, scaled chart
`(a²K w₁, N d₁)`).  `fourth_chart`: the whole target triangle in the chart.
-/

namespace Erdos634.LaczL26

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL21 Erdos634.LaczL24

section trap

variable (R : RTri) (a0 : ℚ) (ha0 : 0 < a0) (ha1 : a0 < 1)
  (hA : R.a = a0 * R.c) (hB : R.b = (1 - a0 ^ 2) * R.c)
  (hN : 0 < a0 ^ 4 - (1 - a0 ^ 2) ^ 3) (w1 d1 : Plane) (hdet : w1 0 * d1 1 - w1 1 * d1 0 ≠ 0)
  (hw : inner ℝ w1 w1 = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2)
  (hd : inner ℝ d1 d1 = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2)
  (hwd : inner ℝ w1 d1 = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2 * (2 - (a0 : ℝ) ^ 2) / 2)

include ha0 ha1 hA hB hN hdet hw hd hwd

set_option maxHeartbeats 1600000 in
theorem chart_FG :
    ChartRSD R 0 w1 d1 hdet ((triF (hyp_of_q a0 ha0 ha1 hN)).carrier ∪ (triG (hyp_of_q a0 ha0 ha1 hN)).carrier) := by
  have hyp := hyp_of_q a0 ha0 ha1 hN
  have hc := R.pc
  have hb0q : (0 : ℚ) < 1 - a0 ^ 2 := by nlinarith
  have hKq : (0 : ℚ) < a0 ^ 2 + (1 - a0 ^ 2) ^ 2 := by positivity
  have hsR : 0 < sR (a0 : ℝ) := by unfold sR gK; have := hyp.ha; positivity
  have hgN : 0 < gN (a0 : ℝ) := hyp.hN
  rw [← trap_poly (hyp_of_q a0 ha0 ha1 hN)]
  obtain ⟨Wq, hWq⟩ : ∃ Wq : ℚ, Wq = R.c * a0 * (a0 ^ 2 + (1 - a0 ^ 2) ^ 2) / (1 - a0 ^ 2) := ⟨_, rfl⟩
  obtain ⟨mq, hmq⟩ : ∃ mq : ℚ, mq = R.c * (a0 ^ 4 - (1 - a0 ^ 2) ^ 3) / (a0 * (1 - a0 ^ 2)) := ⟨_, rfl⟩
  obtain ⟨τq, hτq⟩ : ∃ τq : ℚ, τq = (1 - a0 ^ 2) ^ 2 / (a0 ^ 2 * (a0 ^ 2 + (1 - a0 ^ 2) ^ 2)) := ⟨_, rfl⟩
  have hWpos : 0 < Wq := by rw [hWq]; positivity
  have hmpos : 0 < mq := by rw [hmq]; positivity
  have hτpos : 0 < τq := by rw [hτq]; positivity
  have hWr : (Wq : ℝ) = sR (a0 : ℝ) * (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) := by
    rw [hWq]; unfold sR gK; push_cast; field_simp
  have hmr : (mq : ℝ) = gN (a0 : ℝ) * (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) := by
    rw [hmq]; unfold gN; push_cast; field_simp
  obtain ⟨wT, hwTdef⟩ : ∃ wT : Plane, wT = (sR (a0 : ℝ)) • w1 := ⟨_, rfl⟩
  obtain ⟨dT, hdTdef⟩ : ∃ dT : Plane, dT = (gN (a0 : ℝ)) • d1 := ⟨_, rfl⟩
  have hdetT : wT 0 * dT 1 - wT 1 * dT 0 ≠ 0 := by
    have e : wT 0 * dT 1 - wT 1 * dT 0 = (sR (a0 : ℝ) * gN (a0 : ℝ)) * (w1 0 * d1 1 - w1 1 * d1 0) := by
      simp only [hwTdef, hdTdef, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e]; exact mul_ne_zero (mul_pos hsR hgN).ne' hdet
  have hwT : inner ℝ wT wT = (Wq : ℝ) ^ 2 := by
    rw [hwTdef, gram_smul_self, hw, hWr]; ring
  have hdT : inner ℝ dT dT = (mq : ℝ) ^ 2 := by
    rw [hdTdef, gram_smul_self, hd, hmr]; ring
  have hcos : R.sw01.cos1 = (2 - a0 ^ 2) / 2 := by
    simp only [RTri.cos1, RTri.sw01, hA, hB]
    have : R.c ≠ 0 := hc.ne'
    have : (1 - a0 ^ 2) ≠ 0 := hb0q.ne'
    field_simp; ring
  have hwdT : inner ℝ wT dT = (Wq : ℝ) * (mq : ℝ) * (R.sw01.cos1 : ℝ) := by
    rw [hwTdef, hdTdef, gram_smul, hwd, hWr, hmr, hcos]; push_cast; ring
  have hτ : τq = tTau R.sw01.a R.sw01.b R.sw01.c Wq mq := by
    simp only [tTau, RTri.sw01, hA, hB]
    rw [hWq, hmq, hτq]
    have : R.c ≠ 0 := hc.ne'
    have : (1 - a0 ^ 2) ≠ 0 := hb0q.ne'
    have : a0 ≠ 0 := ha0.ne'
    have : (a0 ^ 2 + (1 - a0 ^ 2) ^ 2) ≠ 0 := hKq.ne'
    have : (a0 ^ 4 - (1 - a0 ^ 2) ^ 3) ≠ 0 := hN.ne'
    field_simp; ring
  have key := RatSimDiss.relabel (Δ := R.Δ) (Equiv.swap 0 1)
    (trap_ii R.sw01 0 wT dT hdetT Wq mq hWpos hmpos hwT hdT hwdT τq hτ hτpos)
  have hτr : (τq : ℝ) = sQ (a0 : ℝ) / sR (a0 : ℝ) := by
    rw [hτq]; unfold sQ sR gb gK; push_cast; field_simp
  unfold ChartRSD
  rw [Set.image_image]
  have hfun : ∀ x : Plane, chartEquiv 0 w1 d1 hdet (mkPt (sR (a0 : ℝ) * x 0) (tQ (a0 : ℝ) * x 1))
      = chartEquiv 0 wT dT hdetT x := by
    intro x
    rw [chartEquiv_apply, chartEquiv_apply]
    simp only [mkPt_zero, mkPt_one, hwTdef, hdTdef, tQ]
    module
  simp only [hfun]
  rw [← hτr]
  exact key

set_option maxHeartbeats 1600000 in
theorem fourth_chart :
    ChartRSD R 0 w1 d1 hdet (triT (hyp_of_q a0 ha0 ha1 hN)).carrier := by
  have hyp := hyp_of_q a0 ha0 ha1 hN
  let S : Fin 6 → Set Plane := ![(triA hyp).carrier, (triB hyp).carrier, (triC hyp).carrier,
    (triD hyp).carrier, (triE hyp).carrier, (triF hyp).carrier ∪ (triG hyp).carrier]
  have hSr : ∀ i, ChartRSD R 0 w1 d1 hdet (S i) := by
    intro i; fin_cases i
    exacts [chart_A R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd, chart_B R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd,
      chart_C R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd, chart_D R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd,
      chart_E R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd, chart_FG R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd]
  have hScl : ∀ i, IsClosed (S i) := by
    intro i; fin_cases i
    · exact (triA hyp).isCompact.isClosed
    · exact (triB hyp).isCompact.isClosed
    · exact (triC hyp).isCompact.isClosed
    · exact (triD hyp).isCompact.isClosed
    · exact (triE hyp).isCompact.isClosed
    · exact ((triF hyp).isCompact.isClosed).union (triG hyp).isCompact.isClosed
  have hSd : Pairwise fun i j => Disjoint (interior (S i)) (interior (S j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact d_AB hyp
    · exact d_AC hyp
    · exact d_AD hyp
    · exact d_AE hyp
    · exact (disjoint_interior_union (triF hyp).isCompact.isClosed (d_AF hyp).symm (d_AG hyp).symm).symm
    · exact (d_AB hyp).symm
    · exact absurd rfl hij
    · exact d_BC hyp
    · exact d_BD hyp
    · exact d_BE hyp
    · exact (disjoint_interior_union (triF hyp).isCompact.isClosed (d_BF hyp).symm (d_BG hyp).symm).symm
    · exact (d_AC hyp).symm
    · exact (d_BC hyp).symm
    · exact absurd rfl hij
    · exact d_CD hyp
    · exact d_CE hyp
    · exact (disjoint_interior_union (triF hyp).isCompact.isClosed (d_CF hyp).symm (d_CG hyp).symm).symm
    · exact (d_AD hyp).symm
    · exact (d_BD hyp).symm
    · exact (d_CD hyp).symm
    · exact absurd rfl hij
    · exact d_DE hyp
    · exact (disjoint_interior_union (triF hyp).isCompact.isClosed (d_DF hyp).symm (d_DG hyp).symm).symm
    · exact (d_AE hyp).symm
    · exact (d_BE hyp).symm
    · exact (d_CE hyp).symm
    · exact (d_DE hyp).symm
    · exact absurd rfl hij
    · exact (disjoint_interior_union (triF hyp).isCompact.isClosed (d_EF hyp).symm (d_EG hyp).symm).symm
    · exact disjoint_interior_union (triF hyp).isCompact.isClosed (d_AF hyp).symm (d_AG hyp).symm
    · exact disjoint_interior_union (triF hyp).isCompact.isClosed (d_BF hyp).symm (d_BG hyp).symm
    · exact disjoint_interior_union (triF hyp).isCompact.isClosed (d_CF hyp).symm (d_CG hyp).symm
    · exact disjoint_interior_union (triF hyp).isCompact.isClosed (d_DF hyp).symm (d_DG hyp).symm
    · exact disjoint_interior_union (triF hyp).isCompact.isClosed (d_EF hyp).symm (d_EG hyp).symm
    · exact absurd rfl hij
  have hU := chart_iUnion (R := R) (A := 0) (w := w1) (d := d1) (h := hdet) S hSr hScl hSd
  have hcover : (⋃ i, S i) = (triT hyp).carrier := by
    rw [← tile_cover hyp]
    ext z
    simp only [Set.mem_iUnion, Fin.exists_fin_succ, S, tile, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Set.mem_union, IsEmpty.exists_iff, or_false, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    try tauto
  rw [hcover] at hU
  exact hU

end trap

end Erdos634.LaczL26
