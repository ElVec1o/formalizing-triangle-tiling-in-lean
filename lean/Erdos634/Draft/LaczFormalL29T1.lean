import Erdos634.Draft.LaczFormalL25Thm
import Erdos634.Draft.LaczFormalL27Std

/-!
# Laczkovich Theorem 2.5, triple `(α, α, π - 2α)` (Fig. 7, first picture)

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.5, Fig. 6 and Fig. 7), Beeson,
Beeson-Zhang, Zhang.

PRINT GAP: the paper says only "Similar constructions apply for the other triples listed in (2); see Fig. 7."
Decoded from Fig. 7 (first picture, by its angle labels): the isosceles triangle with base angles `α` is the tile
`(L, B, E)` (angles `α` at `L`, `β` at `B`, `γ = 2π/3` at `E`) glued to the triangle `D E B` of Fig. 6 (`thm25_first`,
angles `α` at `D`, `α+β = π/3` at `E`, `α+2β` at `B`) along `E B`, `L` on the line `D E` beyond `E`.  The size of the tile
is determined: `E B = 2a` forces the tile scale `2`, so `E L = 2b` and in the Gram chart of Fig. 6 (`D = (0,0)`,
`F = (1,0)`, `A = (0,1)`) the whole triangle is `D = (0,0)`, `L = (2,0)`, `B = (0,2)`.  No range condition.
-/

namespace Erdos634.LaczL29

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL21 Erdos634.LaczL24 Erdos634.LaczL25
  Erdos634.Realizable
open Erdos634.LaczL27 (hfan hfan_range carrier_eq_of_range range_mk3 fan_cover2 fan_disj kap_h kap_h_ne)

set_option maxHeartbeats 4000000 in
/-- **Laczkovich Theorem 2.5, triple `(α, α, π - 2α)`.**  `Δ` a rational tile with `γ = 2π/3` (`c² = a² + ab + b²`).  The
triangle `D B L` (`D = T₀`, apex `B = T₁`, `L = T₂`; angle `α` at `D`, isosceles at `B`) is a union of finitely many
congruent triangles similar to `Δ`. -/
theorem thm25_t1 (R : RTri) (hγ : R.a ^ 2 + R.a * R.b + R.b ^ 2 = R.c ^ 2) :
    ∃ (T : Tri) (q : ℕ) (hq : 0 < q) (M : ℕ)
      (C : Erdos634.RegionDissection.CongruentRegionDissection M),
      C.region = T.carrier ∧
      C.model = scaleTri (1 / (q : ℝ)) (one_div_pos.mpr (Nat.cast_pos.mpr hq)).ne' R.Δ ∧
      dist (T.pts 1) (T.pts 0) = dist (T.pts 1) (T.pts 2) ∧
      cornerAngle (T.pts 1) (T.pts 0) (T.pts 2)
        = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) := by
  have ha := R.pa
  have hb := R.pb
  have hc := R.pc
  obtain ⟨W, hWdef⟩ : ∃ W : ℚ, W = R.a + 2 * R.b := ⟨_, rfl⟩
  have hW : 0 < W := by rw [hWdef]; positivity
  obtain ⟨τq, hτdef⟩ : ∃ τq : ℚ, τq = R.b / W := ⟨_, rfl⟩
  have hτW : τq * W = R.b := by rw [hτdef]; field_simp
  have hτ0 : 0 < τq := by rw [hτdef]; positivity
  have hτ1 : τq < 1 / 2 := by
    rw [hτdef, div_lt_div_iff₀ hW (by norm_num), hWdef]; linarith
  have hρW : (1 - τq) * W = R.a + R.b := by rw [sub_mul, one_mul, hτW, hWdef]; ring
  have Iw : (1 - τq) ^ 2 * W ^ 2 - (1 - τq) * W ^ 2 + R.c ^ 2 = R.a ^ 2 := by
    have e : (1 - τq) ^ 2 * W ^ 2 - (1 - τq) * W ^ 2 + R.c ^ 2
        = ((1 - τq) * W) ^ 2 - ((1 - τq) * W) * W + R.c ^ 2 := by ring
    rw [e, hρW, hWdef]; nlinarith [hγ]
  have hcos2 : (W / (2 * R.c)) ^ 2 < 1 := by
    rw [div_pow, div_lt_one (by positivity), hWdef]; nlinarith [hγ, sq_pos_of_pos ha]
  obtain ⟨w, d, hw, hd, hwd0, hdet⟩ := exists_gram_chart (W : ℝ) (R.c : ℝ) ((W / (2 * R.c) : ℚ) : ℝ)
    (by exact_mod_cast hW) (by exact_mod_cast hc) (by exact_mod_cast hcos2)
  have hwd : inner ℝ w d = (W : ℝ) ^ 2 / 2 := by
    rw [hwd0]; push_cast
    have : (R.c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
    field_simp
  have hτ0' : (0 : ℝ) < τq := by exact_mod_cast hτ0
  have hτ1' : (τq : ℝ) < 1 / 2 := by
    have h := (Rat.cast_lt (K := ℝ)).2 hτ1; push_cast at h; exact h
  have hρpos : (0 : ℝ) < 1 - (τq : ℝ) := by linarith
  have hγR : (R.a : ℝ) ^ 2 + R.a * R.b + R.b ^ 2 = (R.c : ℝ) ^ 2 := by exact_mod_cast hγ
  have hWr : (W : ℝ) = R.a + 2 * R.b := by exact_mod_cast hWdef
  have hτWr : (τq : ℝ) * W = R.b := by exact_mod_cast hτW
  have hρWr : (1 - (τq : ℝ)) * W = R.a + R.b := by exact_mod_cast hρW
  have Iwr : (1 - (τq : ℝ)) ^ 2 * (W : ℝ) ^ 2 - (1 - (τq : ℝ)) * (W : ℝ) ^ 2 + (R.c : ℝ) ^ 2
      = (R.a : ℝ) ^ 2 := by exact_mod_cast Iw
  -- the triangle of Fig. 6 as a fan over the x-axis with apex B = (0, 2)
  have cST := chart_ST R hγ W τq hWdef hτdef w d hdet hw hd hwd
  have hκ : 0 < Erdos634.LaczL27.kap 0 2 0 0 1 0 := by rw [kap_h]; norm_num
  have hq2 : (0 : ℝ) < 2 := by norm_num
  have hne : Erdos634.LaczL27.kap 0 2 0 0 1 0 ≠ 0 := hκ.ne'
  have h01 : (0 : ℝ) < 2 * (1 - (τq : ℝ)) := by linarith
  have h12 : 2 * (1 - (τq : ℝ)) < 2 := by linarith
  have cF1 : ChartRSD R 0 w d hdet (hfan 0 2 hq2 (x := 0) (y := 2 * (1 - (τq : ℝ))) h01.ne).carrier := by
    have e : (hfan 0 2 hq2 (x := 0) (y := 2 * (1 - (τq : ℝ))) h01.ne).carrier = ST (τq : ℝ) := by
      rw [← triTT_carrier hτ0' hτ1']
      refine carrier_eq_of_range ?_
      rw [hfan_range]; unfold triTT; rw [mkTri_pts, range_mk3]
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [e]; exact cST
  -- the tile L B E with L = (2,0), B = (0,2), E = (2ρ, 0), scale 2
  have hdetT : det3 2 0 0 2 (2 * (1 - (τq : ℝ))) 0 ≠ 0 := by
    simp only [det3]; nlinarith
  have cT2 : ChartRSD R 0 w d hdet (hfan 0 2 hq2 (x := 2 * (1 - (τq : ℝ))) (y := 2) h12.ne).carrier := by
    have e : (hfan 0 2 hq2 (x := 2 * (1 - (τq : ℝ))) (y := 2) h12.ne).carrier
        = (mkTri 2 0 0 2 (2 * (1 - (τq : ℝ))) 0 hdetT).carrier := by
      refine carrier_eq_of_range ?_
      rw [hfan_range, mkTri_pts, range_mk3]
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [e]
    refine chart_single (R := R) (A := 0) (w := w) (d := d) (h := hdet) _ ?_
    refine chart_tile R 0 w d hdet W R.c hw hd ((W : ℝ) ^ 2 / 2) hwd 2 0 0 2 (2 * (1 - (τq : ℝ))) 0 hdetT 1 2 two_pos
      ?_ ?_ ?_
    · simp only [Equiv.Perm.coe_one, id_eq, Rat.cast_ofNat]
      rw [R.hc]; ring
    · simp only [Equiv.Perm.coe_one, id_eq, Rat.cast_ofNat]
      rw [R.ha]; linear_combination 4 * Iwr
    · simp only [Equiv.Perm.coe_one, id_eq, Rat.cast_ofNat]
      rw [R.hb]; linear_combination (4 * ((τq : ℝ) * W + R.b)) * hτWr
  have cBig : ChartRSD R 0 w d hdet (hfan 0 2 hq2 (x := 0) (y := 2) (by norm_num)).carrier := by
    have hcov := fan_cover2 (u0 := 0) (u1 := 2 * (1 - (τq : ℝ))) (u2 := 2) hκ hne h01 h12
    have e : (hfan 0 2 hq2 (x := 0) (y := 2) (by norm_num)).carrier
        = (hfan 0 2 hq2 (x := 0) (y := 2 * (1 - (τq : ℝ))) h01.ne).carrier
          ∪ (hfan 0 2 hq2 (x := 2 * (1 - (τq : ℝ))) (y := 2) h12.ne).carrier := hcov.symm
    rw [e]
    exact chart_union cF1 cT2
      (fan_disj hκ hne (m := 2 * (1 - (τq : ℝ))) h01.ne h12.ne h01.le (le_refl _) (le_refl _) h12.le)
  have key : RatSimDiss R.Δ (chartEquiv 0 w d hdet '' (hfan 0 2 hq2 (x := 0) (y := 2) (by norm_num)).carrier) := cBig
  obtain ⟨q, hq, M, C, hC1, hC2⟩ := RatSimDiss.toCongruent R.rational key
  have hdetD : det3 0 0 0 2 2 0 ≠ 0 := by simp only [det3]; norm_num
  have eT : (hfan 0 2 hq2 (x := 0) (y := 2) (by norm_num)).carrier = (mkTri 0 0 0 2 2 0 hdetD).carrier := by
    refine carrier_eq_of_range ?_
    rw [hfan_range, mkTri_pts, range_mk3]
    ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hwn : ‖w‖ = (W : ℝ) := by
    refine eq_of_sq_eq' (norm_nonneg _) (by exact_mod_cast hW.le) ?_
    rw [← real_inner_self_eq_norm_sq]; exact hw
  have hdn : ‖d‖ = (R.c : ℝ) := by
    refine eq_of_sq_eq' (norm_nonneg _) (by exact_mod_cast hc.le) ?_
    rw [← real_inner_self_eq_norm_sq]; exact hd
  refine ⟨Erdos634.DissectionMap.mapTri (chartEquiv 0 w d hdet) (mkTri 0 0 0 2 2 0 hdetD), q, hq, M, C, ?_, hC2, ?_, ?_⟩
  · rw [hC1, Erdos634.DissectionMap.mapTri_carrier, ← eT]
  · -- isosceles at B: both legs are 2c
    have gw : ∀ x y : ℝ, dist (chartEquiv 0 w d hdet (mkPt 0 2)) (chartEquiv 0 w d hdet (mkPt x y)) ^ 2
        = (0 - x) ^ 2 * (W : ℝ) ^ 2 + 2 * ((0 - x) * (2 - y)) * ((W : ℝ) ^ 2 / 2) + (2 - y) ^ 2 * (R.c : ℝ) ^ 2 := by
      intro x y
      rw [dist_chart_sq, hw, hd, hwd]; simp only [mkPt_zero, mkPt_one]
    refine eq_of_sq_eq' dist_nonneg dist_nonneg ?_
    show dist (chartEquiv 0 w d hdet (mkPt 0 2)) (chartEquiv 0 w d hdet (mkPt 0 0)) ^ 2
      = dist (chartEquiv 0 w d hdet (mkPt 0 2)) (chartEquiv 0 w d hdet (mkPt 2 0)) ^ 2
    rw [gw, gw]; ring
  · -- the angle at D
    have e1 : chartEquiv 0 w d hdet (mkPt 2 0) - chartEquiv 0 w d hdet (mkPt 0 0) = (2 : ℝ) • w := by
      rw [chartEquiv_apply, chartEquiv_apply]; simp only [mkPt_zero, mkPt_one]; module
    have e2 : chartEquiv 0 w d hdet (mkPt 0 2) - chartEquiv 0 w d hdet (mkPt 0 0) = (2 : ℝ) • d := by
      rw [chartEquiv_apply, chartEquiv_apply]; simp only [mkPt_zero, mkPt_one]; module
    have h1 : ‖R.Δ.pts 1 - R.Δ.pts 0‖ = R.c := by rw [← dist_eq_norm, dist_comm]; exact R.hc
    have h2 : ‖R.Δ.pts 2 - R.Δ.pts 0‖ = R.b := by rw [← dist_eq_norm]; exact R.hb
    show EuclideanGeometry.angle (chartEquiv 0 w d hdet (mkPt 0 2)) (chartEquiv 0 w d hdet (mkPt 0 0))
        (chartEquiv 0 w d hdet (mkPt 2 0))
      = EuclideanGeometry.angle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2)
    rw [EuclideanGeometry.angle_comm (chartEquiv 0 w d hdet (mkPt 0 2)) (chartEquiv 0 w d hdet (mkPt 0 0))
      (chartEquiv 0 w d hdet (mkPt 2 0))]
    unfold EuclideanGeometry.angle
    simp only [vsub_eq_sub]
    rw [e1, e2, InnerProductGeometry.angle_smul_left_of_pos _ _ two_pos,
      InnerProductGeometry.angle_smul_right_of_pos _ _ two_pos]
    unfold InnerProductGeometry.angle
    rw [R.inner_uv, h1, h2, hwd, hwn, hdn]
    congr 1
    have hW0 : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
    have hc0 : (R.c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
    have hb0 : (R.b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
    field_simp
    rw [hWr]
    nlinarith [hγR]

#print axioms thm25_t1

end Erdos634.LaczL29
