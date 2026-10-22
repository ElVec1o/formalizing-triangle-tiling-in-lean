import Erdos634.Draft.LaczFormalL27Std

/-!
# Laczkovich Theorem 2.4, triples 2 and 5 of (1): chart dissections

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.4, Fig. 5), Beeson, Beeson-Zhang, Zhang.

`fifth_chart`: the triangle `P X R` (angles `β` at `X`, `2α` at `P`, `α+β` at `R`) is tile `P X L` plus `T`.
`second_chart`: the triangle `P X Y` (angles `β, β, 3α`) adds the mirror tile `P R Y`.
-/

namespace Erdos634.LaczL27

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL24 Erdos634.LaczL26

theorem chart_union2 {R : RTri} {A w d : Plane} {h : w 0 * d 1 - w 1 * d 0 ≠ 0} {S₁ S₂ : Set Plane}
    (h1 : ChartRSD R A w d h S₁) (h2 : ChartRSD R A w d h S₂) (c1 : IsClosed S₁) (c2 : IsClosed S₂)
    (hd : Disjoint (interior S₁) (interior S₂)) : ChartRSD R A w d h (S₁ ∪ S₂) := by
  have := chart_iUnion (R := R) (A := A) (w := w) (d := d) (h := h) (ι := Fin 2) ![S₁, S₂]
    (by intro i; fin_cases i; exacts [h1, h2]) (by intro i; fin_cases i; exacts [c1, c2])
    (by
      intro i j hij; fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hd
      · exact hd.symm
      · exact absurd rfl hij)
  have e : (⋃ i, (![S₁, S₂] : Fin 2 → Set Plane) i) = S₁ ∪ S₂ := by
    ext z; simp [Fin.exists_fin_two]
  rwa [e] at this

theorem fan_tile (R : RTri) (a0 : ℚ) (ha0 : 0 < a0) (ha1 : a0 < 1)
    (hA : R.a = a0 * R.c) (hB : R.b = (1 - a0 ^ 2) * R.c) (w d : Plane)
    (hdet : w 0 * d 1 - w 1 * d 0 ≠ 0)
    (hw : inner ℝ w w = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2)
    (hd : inner ℝ d d = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2)
    (hwd : inner ℝ w d = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2 * (2 - (a0 : ℝ) ^ 2) / 2)
    (p q : ℝ) (hq : 0 < q) {u v : ℝ} (huv : u ≠ v) (k : ℚ) (hk : 0 < k) (kr : ℝ) (hkr : (k : ℝ) = kr)
    (h01 : Qf (a0 : ℝ) (p - (0 + u * 1)) (q - (0 + u * 0)) = kr ^ 2 * (a0 : ℝ) ^ 2 * (1 - (a0 : ℝ) ^ 2) ^ 2)
    (h12 : Qf (a0 : ℝ) ((0 + u * 1) - (0 + v * 1)) ((0 + u * 0) - (0 + v * 0))
      = kr ^ 2 * (a0 : ℝ) ^ 4 * (1 - (a0 : ℝ) ^ 2) ^ 2)
    (h20 : Qf (a0 : ℝ) ((0 + v * 1) - p) ((0 + v * 0) - q) = kr ^ 2 * (a0 : ℝ) ^ 2 * (1 - (a0 : ℝ) ^ 2) ^ 4) :
    ChartRSD R 0 w d hdet (hfan p q hq huv).carrier :=
  chart_single (R := R) (A := 0) (w := w) (d := d) (h := hdet) (hfan p q hq huv)
    (tile_ok R a0 ha0 ha1 hA hB w d hdet hw hd hwd p q (0 + u * 1) (0 + u * 0) (0 + v * 1) (0 + v * 0)
      (fan_det_ne p q 0 0 1 0 (kap_h_ne hq) huv) k hk kr hkr h01 h12 h20)

theorem tile_rat (a0 : ℚ) (ha0 : 0 < a0) (ha1 : a0 < 1) : ∃ k : ℚ, 0 < k ∧ (k : ℝ) = kk (a0 : ℝ) := by
  have hb0q : (0 : ℚ) < 1 - a0 ^ 2 := by nlinarith
  refine ⟨(a0 ^ 2 + (1 - a0 ^ 2) ^ 2) / (1 - a0 ^ 2) ^ 2, by positivity, ?_⟩
  unfold kk gK gb; push_cast; ring

section main

variable (R : RTri) (a0 : ℚ) (ha0 : 0 < a0) (ha1 : a0 < 1)
  (hA : R.a = a0 * R.c) (hB : R.b = (1 - a0 ^ 2) * R.c)
  (hN : T4RSD R a0 ha0 ha1) (w1 d1 : Plane) (hdet : w1 0 * d1 1 - w1 1 * d1 0 ≠ 0)
  (hw : inner ℝ w1 w1 = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2)
  (hd : inner ℝ d1 d1 = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2)
  (hwd : inner ℝ w1 d1 = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2 * (2 - (a0 : ℝ) ^ 2) / 2)

include ha0 ha1 hA hB hN hdet hw hd hwd

/-- positivity facts of the interval endpoints. -/
theorem pts_facts : xL (a0 : ℝ) < 0 ∧ 0 < sR (a0 : ℝ) ∧ sR (a0 : ℝ) < xY (a0 : ℝ) := by
  have hyp := hyp0_of_q a0 ha0 ha1
  have h1 := hyp.ha; have h2 := hyp.hb; have h3 := hyp.hK
  refine ⟨?_, ?_, ?_⟩
  · unfold xL; have : 0 < (a0 : ℝ) ^ 2 * gK (a0 : ℝ) / gb (a0 : ℝ) := by positivity
    linarith
  · unfold sR; positivity
  · unfold xY sR; have : 0 < (a0 : ℝ) ^ 2 * gK (a0 : ℝ) / gb (a0 : ℝ) := by positivity
    linarith

theorem chart_tileL :
    ChartRSD R 0 w1 d1 hdet (hfan (sP (a0 : ℝ)) (tP (a0 : ℝ)) (hyp0_of_q a0 ha0 ha1).hK
      (pts_facts R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd).1.ne).carrier := by
  have hyp := hyp0_of_q a0 ha0 ha1
  obtain ⟨k, hk, hkr⟩ := tile_rat a0 ha0 ha1
  have hb : gb (a0 : ℝ) ≠ 0 := hyp.hb.ne'
  have hh : gb (a0 : ℝ) = 1 - (a0 : ℝ) ^ 2 := rfl
  exact fan_tile R a0 ha0 ha1 hA hB w1 d1 hdet hw hd hwd _ _ _ _ k hk _ hkr
    (id_L01 hb) (id_L12 hb) (id_L20 hb)

theorem chart_tileRt :
    ChartRSD R 0 w1 d1 hdet (hfan (sP (a0 : ℝ)) (tP (a0 : ℝ)) (hyp0_of_q a0 ha0 ha1).hK
      (pts_facts R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd).2.2.ne').carrier := by
  have hyp := hyp0_of_q a0 ha0 ha1
  obtain ⟨k, hk, hkr⟩ := tile_rat a0 ha0 ha1
  have hb : gb (a0 : ℝ) ≠ 0 := hyp.hb.ne'
  exact fan_tile R a0 ha0 ha1 hA hB w1 d1 hdet hw hd hwd _ _ _ _ k hk _ hkr
    (id_R01 hb) (id_R12 hb) (id_R20 hb)

theorem chart_T4 :
    ChartRSD R 0 w1 d1 hdet (hfan (sP (a0 : ℝ)) (tP (a0 : ℝ)) (hyp0_of_q a0 ha0 ha1).hK
      (pts_facts R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd).2.1.ne).carrier := by
  exact hN w1 d1 hdet hw hd hwd

/-- **Fifth triple in the chart**: `hfan P xL sR` is tile + `T`. -/
theorem fifth_chart :
    ChartRSD R 0 w1 d1 hdet (hfan (sP (a0 : ℝ)) (tP (a0 : ℝ)) (hyp0_of_q a0 ha0 ha1).hK
      ((pts_facts R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd).1.trans
        (pts_facts R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd).2.1).ne).carrier := by
  have hyp := hyp0_of_q a0 ha0 ha1
  obtain ⟨h1, h2, h3⟩ := pts_facts R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd
  have hκ : 0 < kap (sP (a0 : ℝ)) (tP (a0 : ℝ)) 0 0 1 0 := by rw [kap_h]; exact hyp.hK
  have hcov := fan_cover2 hκ (kap_h_ne hyp.hK) h1 h2
  have e : (hfan (sP (a0 : ℝ)) (tP (a0 : ℝ)) hyp.hK (h1.trans h2).ne).carrier
      = (hfan (sP (a0 : ℝ)) (tP (a0 : ℝ)) hyp.hK h1.ne).carrier
        ∪ (hfan (sP (a0 : ℝ)) (tP (a0 : ℝ)) hyp.hK h2.ne).carrier := hcov.symm
  rw [e]
  exact chart_union2 (chart_tileL R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd)
    (chart_T4 R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd) (Tri.isCompact _).isClosed (Tri.isCompact _).isClosed
    (fan_disj hκ (kap_h_ne hyp.hK) (m := 0) h1.ne _ h1.le (le_refl _) (le_refl _) h2.le)

/-- **Second triple in the chart**: `hfan P xL xY` is tile + `T` + mirror tile. -/
theorem second_chart :
    ChartRSD R 0 w1 d1 hdet (hfan (sP (a0 : ℝ)) (tP (a0 : ℝ)) (hyp0_of_q a0 ha0 ha1).hK
      (((pts_facts R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd).1.trans
        (pts_facts R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd).2.1).trans
        (pts_facts R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd).2.2).ne).carrier := by
  have hyp := hyp0_of_q a0 ha0 ha1
  obtain ⟨h1, h2, h3⟩ := pts_facts R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd
  have hκ : 0 < kap (sP (a0 : ℝ)) (tP (a0 : ℝ)) 0 0 1 0 := by rw [kap_h]; exact hyp.hK
  have hcov := fan_cover2 (u0 := xL (a0 : ℝ)) (u1 := sR (a0 : ℝ)) (u2 := xY (a0 : ℝ)) hκ (kap_h_ne hyp.hK)
    (h1.trans h2) h3
  have e : (hfan (sP (a0 : ℝ)) (tP (a0 : ℝ)) hyp.hK ((h1.trans h2).trans h3).ne).carrier
      = (hfan (sP (a0 : ℝ)) (tP (a0 : ℝ)) hyp.hK (h1.trans h2).ne).carrier
        ∪ (hfan (sP (a0 : ℝ)) (tP (a0 : ℝ)) hyp.hK h3.ne).carrier := hcov.symm
  rw [e]
  have hR : ChartRSD R 0 w1 d1 hdet (hfan (sP (a0 : ℝ)) (tP (a0 : ℝ)) hyp.hK h3.ne).carrier := by
    rw [hfan_swap]
    exact chart_tileRt R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd
  exact chart_union2 (fifth_chart R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd) hR
    (Tri.isCompact _).isClosed (Tri.isCompact _).isClosed
    (fan_disj hκ (kap_h_ne hyp.hK) (m := sR (a0 : ℝ)) (h1.trans h2).ne h3.ne (h1.trans h2).le (le_refl _) (le_refl _) h3.le)

end main

/-- For `N(a₀) > 0` the input `T4RSD` is `fourth_chart` (Laczkovich's first picture of Fig. 5). -/
theorem T4RSD_of_N (R : RTri) (a0 : ℚ) (ha0 : 0 < a0) (ha1 : a0 < 1)
    (hA : R.a = a0 * R.c) (hB : R.b = (1 - a0 ^ 2) * R.c) (hN : 0 < a0 ^ 4 - (1 - a0 ^ 2) ^ 3) :
    T4RSD R a0 ha0 ha1 := by
  intro w d hdet hw hd hwd
  have hyp := hyp_of_q a0 ha0 ha1 hN
  have key := fourth_chart R a0 ha0 ha1 hA hB hN w d hdet hw hd hwd
  rw [T4_eq hyp] at key
  exact key

end Erdos634.LaczL27
