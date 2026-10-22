import Erdos634.Draft.LaczFormalL27Chart

/-!
# Laczkovich Theorem 2.4, third triple `(α, 2α, 2β)`: the chart dissection

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.4, Fig. 5, fourth picture), Beeson, Beeson-Zhang, Zhang.

Fig. 5, fourth picture: apex `A` (angle `2β = β + β`), left vertex `V` (angle `α`), right vertex `P` (angle `2α = α + α`).
The cevian `A F` (`F = L`) cuts it into the tile `V A L` (angles `α, β, γ`) and the triangle `L A P` (angles `α+β, β, 2α`,
which is the fifth-triple shape); the segment `P R` (`R` on `L A`) cuts `L A P` into `T = L R P` (the fourth-triple triangle,
apex `P`) and the tile `P A R`.  In the standard chart: `A = (xY, 0)`, `V = ((2-a²)·b·K, -(2-a²)·K)`, tile scales `K/b²` and
`K(2-a²)/b²`; all sizes are determined by the picture.  Range: `N(a₀) > 0` (that of `T`).
-/

namespace Erdos634.LaczL27

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL24 Erdos634.LaczL26

noncomputable def vX (a : ℝ) : ℝ := (1 + gb a) * gb a * gK a
noncomputable def vY (a : ℝ) : ℝ := -((1 + gb a) * gK a)
noncomputable def cL (a : ℝ) : ℝ := (1 + gb a) * gK a
noncomputable def k1 (a : ℝ) : ℝ := gK a * (1 + gb a) / gb a ^ 2

variable {a : ℝ}

theorem id_V01 (hb : gb a ≠ 0) :
    Qf a (vX a - xY a) (vY a - 0) = k1 a ^ 2 * a ^ 2 * (1 - a ^ 2) ^ 2 := by
  unfold Qf vX vY xY k1 gb gK at *; field_simp; ring
theorem id_V12 (hb : gb a ≠ 0) :
    Qf a (xY a - 0) (0 - 0) = k1 a ^ 2 * a ^ 4 * (1 - a ^ 2) ^ 2 := by
  unfold Qf xY k1 gb gK at *; field_simp; ring
theorem id_V20 (hb : gb a ≠ 0) :
    Qf a (0 - vX a) (0 - vY a) = k1 a ^ 2 * a ^ 2 * (1 - a ^ 2) ^ 4 := by
  unfold Qf vX vY k1 gb gK at *; field_simp; ring

theorem det_V (h : Hyp0 a) : det3 (vX a) (vY a) (xY a) 0 0 0 ≠ 0 := by
  have h1 := h.ha; have h2 := h.hb; have h3 := h.hK
  have e : det3 (vX a) (vY a) (xY a) 0 0 0 = (1 + gb a) * gK a * xY a := by
    unfold det3 vY; ring
  rw [e]
  have : 0 < xY a := by unfold xY; have : 0 < gb a := h2; unfold gb at *; unfold gK at *; positivity
  have : 0 < 1 + gb a := by linarith
  positivity

theorem kapA (h : Hyp0 a) : kap (xY a) 0 0 0 (gb a) (-1) = xY a := by unfold kap; ring

theorem xY_pos (h : Hyp0 a) : 0 < xY a := by
  have h1 := h.ha; have h2 := h.hb; have h3 := h.hK
  unfold xY; have : 0 < gb a := h2; unfold gb at *; unfold gK at *; positivity


/-- the fan from `A` over the line `x ↦ x (b, -1)` through `L`. -/
noncomputable def fA (h : Hyp0 a) {x y : ℝ} (hxy : x ≠ y) : Tri :=
  fanTri (xY a) 0 0 0 (gb a) (-1) (by rw [kapA h]; exact (xY_pos h).ne') hxy

theorem fA_range (h : Hyp0 a) {x y : ℝ} (hxy : x ≠ y) :
    Set.range (fA h hxy).pts = {mkPt (xY a) 0, mkPt (0 + x * gb a) (0 + x * (-1)), mkPt (0 + y * gb a) (0 + y * (-1))} := by
  unfold fA fanTri
  rw [mkTri_pts, range_mk3]

theorem fA_left (h : Hyp0 a) :
    (fA h (show -gK a ≠ 0 from (by have := h.hK; linarith : -gK a < 0).ne)).carrier
      = (hfan (sP a) (tP a) h.hK (show (0 : ℝ) ≠ xY a from (xY_pos h).ne)).carrier := by
  refine carrier_eq_of_range ?_
  rw [fA_range, hfan_range]
  have e1 : mkPt (0 + -gK a * gb a) (0 + -gK a * -1) = mkPt (sP a) (tP a) := by
    congr 1 <;> (try simp only [sP, tP]) <;> ring
  have e2 : mkPt (0 + 0 * gb a) (0 + 0 * (-1)) = mkPt 0 0 := by congr 1 <;> ring
  rw [e1, e2]
  ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

theorem fA_right (h : Hyp0 a) :
    (fA h (show (0 : ℝ) ≠ cL a from (by have := h.hK; have := h.hb; unfold cL; unfold gb at *; unfold gK at *; positivity : 0 < cL a).ne)).carrier
      = (mkTri (vX a) (vY a) (xY a) 0 0 0 (det_V h)).carrier := by
  refine carrier_eq_of_range ?_
  rw [fA_range, mkTri_pts, range_mk3]
  have e1 : mkPt (0 + 0 * gb a) (0 + 0 * (-1)) = mkPt 0 0 := by congr 1 <;> ring
  have e2 : mkPt (0 + cL a * gb a) (0 + cL a * (-1)) = mkPt (vX a) (vY a) := by
    congr 1 <;> (try simp only [cL, vX, vY]) <;> ring
  rw [e1, e2]
  ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto


theorem tile_rat1 (a0 : ℚ) (ha0 : 0 < a0) (ha1 : a0 < 1) : ∃ k : ℚ, 0 < k ∧ (k : ℝ) = k1 (a0 : ℝ) := by
  have hb0q : (0 : ℚ) < 1 - a0 ^ 2 := by nlinarith
  refine ⟨(a0 ^ 2 + (1 - a0 ^ 2) ^ 2) * (1 + (1 - a0 ^ 2)) / (1 - a0 ^ 2) ^ 2, by positivity, ?_⟩
  unfold k1 gK gb; push_cast; ring

section main

variable (R : RTri) (a0 : ℚ) (ha0 : 0 < a0) (ha1 : a0 < 1)
  (hA : R.a = a0 * R.c) (hB : R.b = (1 - a0 ^ 2) * R.c)
  (hN : T4RSD R a0 ha0 ha1) (w1 d1 : Plane) (hdet : w1 0 * d1 1 - w1 1 * d1 0 ≠ 0)
  (hw : inner ℝ w1 w1 = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2)
  (hd : inner ℝ d1 d1 = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2)
  (hwd : inner ℝ w1 d1 = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2 * (2 - (a0 : ℝ) ^ 2) / 2)

include ha0 ha1 hA hB hN hdet hw hd hwd

theorem chart_tile1 :
    ChartRSD R 0 w1 d1 hdet (mkTri (vX (a0 : ℝ)) (vY (a0 : ℝ)) (xY (a0 : ℝ)) 0 0 0
      (det_V (hyp0_of_q a0 ha0 ha1))).carrier := by
  have hyp := hyp0_of_q a0 ha0 ha1
  obtain ⟨k, hk, hkr⟩ := tile_rat1 a0 ha0 ha1
  have hb : gb (a0 : ℝ) ≠ 0 := hyp.hb.ne'
  exact chart_single (R := R) (A := 0) (w := w1) (d := d1) (h := hdet) _
    (tile_ok R a0 ha0 ha1 hA hB w1 d1 hdet hw hd hwd (vX (a0 : ℝ)) (vY (a0 : ℝ)) (xY (a0 : ℝ)) 0 0 0
      (det_V hyp) k hk _ hkr (id_V01 hb) (id_V12 hb) (id_V20 hb))

theorem lower_chart :
    ChartRSD R 0 w1 d1 hdet (hfan (sP (a0 : ℝ)) (tP (a0 : ℝ)) (hyp0_of_q a0 ha0 ha1).hK
      (show (0 : ℝ) ≠ xY (a0 : ℝ) from (xY_pos (hyp0_of_q a0 ha0 ha1)).ne)).carrier := by
  have hyp := hyp0_of_q a0 ha0 ha1
  obtain ⟨h1, h2, h3⟩ := pts_facts R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd
  have hκ : 0 < kap (sP (a0 : ℝ)) (tP (a0 : ℝ)) 0 0 1 0 := by rw [kap_h]; exact hyp.hK
  have hcov := fan_cover2 (u0 := 0) (u1 := sR (a0 : ℝ)) (u2 := xY (a0 : ℝ)) hκ (kap_h_ne hyp.hK) h2 h3
  have e : (hfan (sP (a0 : ℝ)) (tP (a0 : ℝ)) hyp.hK (h2.trans h3).ne).carrier
      = (hfan (sP (a0 : ℝ)) (tP (a0 : ℝ)) hyp.hK h2.ne).carrier
        ∪ (hfan (sP (a0 : ℝ)) (tP (a0 : ℝ)) hyp.hK h3.ne).carrier := hcov.symm
  rw [e]
  have hR : ChartRSD R 0 w1 d1 hdet (hfan (sP (a0 : ℝ)) (tP (a0 : ℝ)) hyp.hK h3.ne).carrier := by
    rw [hfan_swap]
    exact chart_tileRt R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd
  exact chart_union2 (chart_T4 R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd) hR
    (Tri.isCompact _).isClosed (Tri.isCompact _).isClosed
    (fan_disj hκ (kap_h_ne hyp.hK) (m := sR (a0 : ℝ)) h2.ne h3.ne h2.le (le_refl _) (le_refl _) h3.le)

/-- **Third triple in the chart**: the fan from `A` over `P, L, V` is tile `V A L` + (`T` + tile `P A R`). -/
theorem third_chart :
    ChartRSD R 0 w1 d1 hdet (fA (hyp0_of_q a0 ha0 ha1)
      (show -gK (a0 : ℝ) ≠ cL (a0 : ℝ) from (by
        have := (hyp0_of_q a0 ha0 ha1).hK; have := (hyp0_of_q a0 ha0 ha1).hb
        unfold cL; unfold gb at *; unfold gK at *; nlinarith [sq_nonneg (a0 : ℝ)] : -gK (a0 : ℝ) < cL (a0 : ℝ)).ne)).carrier := by
  have hyp := hyp0_of_q a0 ha0 ha1
  have hK := hyp.hK
  have hcpos : 0 < cL (a0 : ℝ) := by
    have := hyp.hb; unfold cL; unfold gb at *; unfold gK at *; positivity
  have hκ : 0 < kap (xY (a0 : ℝ)) 0 0 0 (gb (a0 : ℝ)) (-1) := by rw [kapA hyp]; exact xY_pos hyp
  have hne : kap (xY (a0 : ℝ)) 0 0 0 (gb (a0 : ℝ)) (-1) ≠ 0 := hκ.ne'
  have h01 : -gK (a0 : ℝ) < 0 := by linarith
  have hcov := fan_cover2 hκ hne h01 hcpos
  have e : (fA hyp (show -gK (a0 : ℝ) ≠ cL (a0 : ℝ) from (h01.trans hcpos).ne)).carrier
      = (fA hyp h01.ne).carrier ∪ (fA hyp hcpos.ne).carrier := hcov.symm
  rw [e]
  have hL : ChartRSD R 0 w1 d1 hdet (fA hyp h01.ne).carrier := by
    rw [fA_left hyp]
    exact lower_chart R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd
  have hRr : ChartRSD R 0 w1 d1 hdet (fA hyp hcpos.ne).carrier := by
    rw [fA_right hyp]
    exact chart_tile1 R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd
  exact chart_union2 hL hRr (Tri.isCompact _).isClosed (Tri.isCompact _).isClosed
    (fan_disj hκ hne (m := 0) h01.ne hcpos.ne h01.le (le_refl _) (le_refl _) hcpos.le)

end main

end Erdos634.LaczL27
