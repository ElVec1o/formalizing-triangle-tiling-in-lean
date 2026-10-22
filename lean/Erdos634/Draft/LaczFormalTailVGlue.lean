-- Draft/LaczFormalTailVGlue.lean -- tail case (v) of Laczkovich 1995 Thm 5.3 (pp. 93-94): congruent tiles with angles (pi/10, 3pi/10, 6pi/10)
-- cannot dissect a triangle with angles (3pi/10, 3pi/10, 4pi/10).  Geometric glue (relabelling, law of sines, area identity
-- `abs_det_target`, side words `sideCountT_sum`) turning a hypothetical dissection into the hypotheses of `tail_v_arith`.  UNAUDITED.
-- Credit: Laczkovich (1995).
import Erdos634.Draft.LaczFormalTailV
import Erdos634.Draft.LaczFormalTailIV

open scoped Classical

namespace Erdos634.Draft.LaczFormal

open Real Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
  Erdos634.Draft.LemmaCFinal

set_option maxHeartbeats 3200000 in
/-- **Tail case (v).** -/
theorem tail_v {N : ℕ} (D : CongruentDissection N)
    (hM : TileAngles D (π / 10) (3 * π / 10) (6 * π / 10))
    (hT : TgtAngles D (3 * π / 10) (3 * π / 10) (4 * π / 10)) : False := by
  obtain ⟨σm, m0, m1, m2⟩ := hM
  obtain ⟨σt, t0, t1, t2⟩ := hT
  let D' : CongruentDissection N :=
    { toDissection := Erdos634.NormalPosition.relabelTarget D.toDissection σt
      model := D.model.relabel σm
      tiles_congruent := fun i => (D.tiles_congruent i).relabel σm }
  have hTa := Row2.angleAt_comp D.target D'.target σt (fun k => rfl)
  have hMa := Row2.angleAt_comp D.model D'.model σm (fun k => rfl)
  have a0 : D'.model.angleAt 0 = π / 10 := by rw [(hMa 0).1]; exact m0
  have a1 : D'.model.angleAt 1 = 3 * π / 10 := by rw [(hMa 1).1]; exact m1
  have a2 : D'.model.angleAt 2 = 6 * π / 10 := by rw [(hMa 2).1]; exact m2
  have b0 : D'.target.angleAt 0 = 3 * π / 10 := by rw [(hTa 0).1]; exact t0
  have b1 : D'.target.angleAt 1 = 3 * π / 10 := by rw [(hTa 1).1]; exact t1
  have b2 : D'.target.angleAt 2 = 4 * π / 10 := by rw [(hTa 2).1]; exact t2
  have hpi := Real.pi_pos
  have s5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs5 : 2 < Real.sqrt 5 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  -- the three sines
  have sa : Real.sin (π / 10) = (Real.sqrt 5 - 1) / 4 := by
    rw [← Real.cos_pi_div_two_sub, show π / 2 - π / 10 = 2 * π / 5 by ring]; exact cos_two_pi_div_five
  have sb : Real.sin (3 * π / 10) = (Real.sqrt 5 + 1) / 4 := by
    rw [← Real.cos_pi_div_two_sub, show π / 2 - 3 * π / 10 = π / 5 by ring, Real.cos_pi_div_five]; ring
  set sc := Real.sin (4 * π / 10) with hsc
  have sc6 : Real.sin (6 * π / 10) = sc := by
    rw [hsc, show 6 * π / 10 = π - 4 * π / 10 by ring, Real.sin_pi_sub]
  have scpos : 0 < sc := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  have sc2 : sc ^ 2 = (5 + Real.sqrt 5) / 8 := by
    have h1 := Real.sin_sq_add_cos_sq (4 * π / 10)
    have h2 : Real.cos (4 * π / 10) = (Real.sqrt 5 - 1) / 4 := by
      rw [show 4 * π / 10 = 2 * π / 5 by ring]; exact cos_two_pi_div_five
    rw [h2] at h1; rw [hsc]; nlinarith [s5]
  have hapos : 0 < (Real.sqrt 5 - 1) / 4 := by linarith
  have hbpos : 0 < (Real.sqrt 5 + 1) / 4 := by linarith
  set A := (Real.sqrt 5 - 1) / 4 with hA
  set B := (Real.sqrt 5 + 1) / 4 with hB
  -- model sides: v_k = t * (A, B, sc)
  have hv0 := D'.model.oppLen_pos 0
  have hw0 := D'.target.oppLen_pos 0
  set t := D'.model.oppLen 0 / A with ht
  have htpos : 0 < t := div_pos hv0 hapos
  have v0e : D'.model.oppLen 0 = t * A := by rw [ht]; field_simp
  have v1e : D'.model.oppLen 1 = t * B := by
    have h := D'.model.lawSin 0 1
    rw [a0, a1, sa, sb, v0e] at h
    apply mul_left_cancel₀ hapos.ne'
    linarith
  have v2e : D'.model.oppLen 2 = t * sc := by
    have h := D'.model.lawSin 0 2
    rw [a0, a2, sa, sc6, v0e] at h
    apply mul_left_cancel₀ hapos.ne'
    linarith
  -- target sides: w_k = s * (B, B, sc)
  set s := D'.target.oppLen 0 / B with hs
  have hspos : 0 < s := div_pos hw0 hbpos
  have w0e : D'.target.oppLen 0 = s * B := by rw [hs]; field_simp
  have w1e : D'.target.oppLen 1 = s * B := by
    have h := D'.target.lawSin 0 1
    rw [b0, b1] at h
    have hsin : 0 < Real.sin (3 * π / 10) := by rw [sb]; exact hbpos
    have := mul_left_cancel₀ hsin.ne' (by linarith : Real.sin (3 * π / 10) * D'.target.oppLen 1 =
      Real.sin (3 * π / 10) * D'.target.oppLen 0)
    rw [this, w0e]
  have w2e : D'.target.oppLen 2 = s * sc := by
    have h := D'.target.lawSin 0 2
    rw [b0, b2, sb] at h
    apply mul_left_cancel₀ hbpos.ne'
    rw [w0e] at h
    linarith
  -- area
  have harea := Row3.RP.abs_det_target D'
  rw [Row3.RP.abs_det_eq, Row3.RP.abs_det_eq, b0, a0, sb, sa, w1e, w2e, v1e, v2e] at harea
  set ρ := s / t with hρ
  have hρpos : 0 < ρ := div_pos hspos htpos
  have hN0 : 0 < N := D'.pos
  have h0 : ρ ^ 2 * B = N * A := by
    have key : s ^ 2 * B = N * t ^ 2 * A := by
      have hBsc : 0 < B * sc := mul_pos hbpos scpos
      apply mul_left_cancel₀ hBsc.ne'
      linear_combination harea
    rw [hρ]; field_simp; linear_combination key
  -- side equations
  have r0 := D'.sideCountT_sum 0
  have r2 := D'.sideCountT_sum 2
  rw [Fin.sum_univ_three, v0e, v1e, v2e, w0e] at r0
  rw [Fin.sum_univ_three, v0e, v1e, v2e, w2e] at r2
  have h1 : ρ * B = (D'.sideCountT 0 0 : ℝ) * A + (D'.sideCountT 0 1 : ℝ) * B + (D'.sideCountT 0 2 : ℝ) * sc := by
    have : t * (ρ * B) = t * ((D'.sideCountT 0 0 : ℝ) * A + (D'.sideCountT 0 1 : ℝ) * B + (D'.sideCountT 0 2 : ℝ) * sc) := by
      have e : t * ρ = s := by rw [hρ]; field_simp
      linear_combination (B) * e + (-1 : ℝ) * r0
    exact mul_left_cancel₀ htpos.ne' this
  have h2 : ρ * sc = (D'.sideCountT 2 0 : ℝ) * A + (D'.sideCountT 2 1 : ℝ) * B + (D'.sideCountT 2 2 : ℝ) * sc := by
    have : t * (ρ * sc) = t * ((D'.sideCountT 2 0 : ℝ) * A + (D'.sideCountT 2 1 : ℝ) * B + (D'.sideCountT 2 2 : ℝ) * sc) := by
      have e : t * ρ = s := by rw [hρ]; field_simp
      linear_combination (sc) * e + (-1 : ℝ) * r2
    exact mul_left_cancel₀ htpos.ne' this
  exact tail_v_arith hN0 hρpos scpos sc2 h0 h1 h2

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.tail_v
