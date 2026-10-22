-- Draft/LaczFormalVii.lean -- GEOMETRIC EXTRACTION for the isosceles-right target (Laczkovich 1995, Thm 5.1 case (vii); Thm 5.3 "similar arguments", p. 94):
-- for a congruent dissection of a (pi/4, pi/4, pi/2) triangle by tiles with angles x, y, z, with rho = (target leg)/(tile scale t):
--     rho * (sqrt2/2) = X0 sin x + X1 sin y + X2 sin z   (leg is packed by tile sides),
--     rho            = Z0 sin x + Z1 sin y + Z2 sin z    (hypotenuse),
--     rho^2          = 2 N sin x sin y sin z             (area identity).
-- Then the three (vii) triples are killed by arithmetic in `LaczFormalViiArith`.  UNAUDITED.  Credit: Laczkovich (1995).
import Erdos634.Draft.LaczFormalCaseVI

open scoped Classical

namespace Erdos634.Draft.LaczFormal

open Real Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional

theorem iso_right_extract {N : ℕ} (D : CongruentDissection N) {x y z : ℝ}
    (hM : TileAngles D x y z) (hT : TgtAngles D (π / 4) (π / 4) (π / 2))
    (hsx : 0 < Real.sin x) :
    ∃ (ρ : ℝ) (X Z : Fin 3 → ℕ), 0 < ρ ∧ 0 < N ∧
      ρ * (Real.sqrt 2 / 2) = X 0 * Real.sin x + X 1 * Real.sin y + X 2 * Real.sin z ∧
      ρ = Z 0 * Real.sin x + Z 1 * Real.sin y + Z 2 * Real.sin z ∧
      ρ ^ 2 = 2 * N * (Real.sin x * Real.sin y * Real.sin z) := by
  obtain ⟨σm, m0, m1, m2⟩ := hM
  obtain ⟨σt, t0, t1, t2⟩ := hT
  let D' : CongruentDissection N :=
    { toDissection := Erdos634.NormalPosition.relabelTarget D.toDissection σt
      model := D.model.relabel σm
      tiles_congruent := fun i => (D.tiles_congruent i).relabel σm }
  have hTa := Row2.angleAt_comp D.target D'.target σt (fun k => rfl)
  have hMa := Row2.angleAt_comp D.model D'.model σm (fun k => rfl)
  have a0 : D'.model.angleAt 0 = x := by rw [(hMa 0).1]; exact m0
  have a1 : D'.model.angleAt 1 = y := by rw [(hMa 1).1]; exact m1
  have a2 : D'.model.angleAt 2 = z := by rw [(hMa 2).1]; exact m2
  have b0 : D'.target.angleAt 0 = π / 4 := by rw [(hTa 0).1]; exact t0
  have b1 : D'.target.angleAt 1 = π / 4 := by rw [(hTa 1).1]; exact t1
  have b2 : D'.target.angleAt 2 = π / 2 := by rw [(hTa 2).1]; exact t2
  have hpi := Real.pi_pos
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have sq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have sp4 : Real.sin (π / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
  have sp2 : Real.sin (π / 2) = 1 := Real.sin_pi_div_two
  have hsp : 0 < Real.sin (π / 4) := by rw [sp4]; positivity
  have hv0 := D'.model.oppLen_pos 0
  have hw0 := D'.target.oppLen_pos 0
  set t := D'.model.oppLen 0 / Real.sin x with ht
  have htpos : 0 < t := div_pos hv0 hsx
  have v0e : D'.model.oppLen 0 = t * Real.sin x := by rw [ht]; field_simp
  have v1e : D'.model.oppLen 1 = t * Real.sin y := by
    have h := D'.model.lawSin 0 1
    rw [a0, a1, v0e] at h
    apply mul_left_cancel₀ hsx.ne'
    linarith
  have v2e : D'.model.oppLen 2 = t * Real.sin z := by
    have h := D'.model.lawSin 0 2
    rw [a0, a2, v0e] at h
    apply mul_left_cancel₀ hsx.ne'
    linarith
  set s := D'.target.oppLen 0 / Real.sin (π / 4) with hs
  have hspos : 0 < s := div_pos hw0 hsp
  have w0e : D'.target.oppLen 0 = s * Real.sin (π / 4) := by rw [hs]; field_simp
  have w1e : D'.target.oppLen 1 = s * Real.sin (π / 4) := by
    have h := D'.target.lawSin 0 1
    rw [b0, b1] at h
    have := mul_left_cancel₀ hsp.ne' (by linarith : Real.sin (π / 4) * D'.target.oppLen 1 =
      Real.sin (π / 4) * D'.target.oppLen 0)
    rw [this, w0e]
  have w2e : D'.target.oppLen 2 = s := by
    have h := D'.target.lawSin 0 2
    rw [b0, b2, sp2, w0e] at h
    apply mul_left_cancel₀ hsp.ne'
    linarith
  have harea := Row3.RP.abs_det_target D'
  rw [Row3.RP.abs_det_eq, Row3.RP.abs_det_eq, b0, a0, w1e, w2e, v1e, v2e] at harea
  set ρ := s / t with hρ
  have hρpos : 0 < ρ := div_pos hspos htpos
  have hN0 : 0 < N := D'.pos
  have et : t * ρ = s := by rw [hρ]; field_simp
  have r0 := D'.sideCountT_sum 0
  have r2 := D'.sideCountT_sum 2
  rw [Fin.sum_univ_three, v0e, v1e, v2e, w0e] at r0
  rw [Fin.sum_univ_three, v0e, v1e, v2e, w2e] at r2
  refine ⟨ρ, fun k => D'.sideCountT 0 k, fun k => D'.sideCountT 2 k, hρpos, hN0, ?_, ?_, ?_⟩
  · have : t * (ρ * (Real.sqrt 2 / 2)) = t * ((D'.sideCountT 0 0 : ℝ) * Real.sin x +
        (D'.sideCountT 0 1 : ℝ) * Real.sin y + (D'.sideCountT 0 2 : ℝ) * Real.sin z) := by
      rw [sp4] at r0
      linear_combination (Real.sqrt 2 / 2) * et + (-1 : ℝ) * r0
    exact mul_left_cancel₀ htpos.ne' this
  · have : t * ρ = t * ((D'.sideCountT 2 0 : ℝ) * Real.sin x +
        (D'.sideCountT 2 1 : ℝ) * Real.sin y + (D'.sideCountT 2 2 : ℝ) * Real.sin z) := by
      linear_combination et + (-1 : ℝ) * r2
    exact mul_left_cancel₀ htpos.ne' this
  · have key : s ^ 2 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) =
        N * t ^ 2 * (Real.sin y * Real.sin z * Real.sin x) := by
      rw [sp4] at harea
      linear_combination harea
    have e : Real.sqrt 2 / 2 * (Real.sqrt 2 / 2) = 1 / 2 := by linear_combination (1 / 4 : ℝ) * sq2
    have h2 : s ^ 2 = 2 * N * t ^ 2 * (Real.sin x * Real.sin y * Real.sin z) := by
      linear_combination 2 * key - 2 * s ^ 2 * e
    rw [hρ]
    field_simp
    linear_combination h2

end Erdos634.Draft.LaczFormal
