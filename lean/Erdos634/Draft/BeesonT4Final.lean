import Erdos634.Draft.BeesonT4M2T5
import Erdos634.Draft.FluxFRow15Setup

/-!
# Beeson (arXiv 1206.2229v4) Theorem 4: `M2` for the last two rows, and the closing sentence

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Thm 4), Laczkovich (DCG 48 (2012)), Beeson-Zhang.
Formalization debt, not progress on the /goal outcomes.

`Row15.setup` / `Row14.setup` (committed, not edited) keep only the `chi_-` flux integer.  The `chi_+` flux
(`chiAt ... 0`, the Phi_2 of the printed text; project `S_+ ` with `S_+ (a - b - c) = Phi_2`) is obtained here directly
from `CongruentDissection.triangle_boundary_anchor` in the same way as `Row11.boundary_baseAlpha`.
Rows `(2alpha,alpha,2beta)`: `M2 = -Lambda s (2-s)(1+s)`;  `(2alpha,beta,alpha+beta)`: `M2 = Lambda s`.
`t4_final` collects all five printed rows with `M1 != 0`, `M2 != 0` and `Lambda = M1 / s` for the triquadratic row
`(2alpha,beta,alpha+beta)`.  Project hypothesis (H1) `alpha notin Q*pi` replaces Beeson's Lemma 1.
-/

open scoped Classical

namespace Erdos634.BeesonColoring

open Erdos634.Geometry
open Erdos634.Geometry.A1Field

variable {N : ℕ}

theorem t4_aux {α β a b c : ℝ} {N : ℕ} (D : CongruentDissection N) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) :
    0 < circD D.target / circD D.model ∧ 0 < a / c ∧ a / c < 1 := by
  obtain ⟨ha, hb, hc, hαpos, hβpos⟩ := model_abc_pos h
  obtain ⟨s, hs0, hs1, sA, sB, sG, s2A, sAB, s3A, s2B⟩ := sin_table hrel hαpos hβpos
  have hsδ : 0 < Real.sin (α + β) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  have ea : a = circD D.model * Real.sin α := by rw [← o0, oppLen_eq, h0]
  have ec : c = circD D.model * Real.sin (α + β) := by rw [← o2, oppLen_eq, h2, sG]
  have hD : 0 < circD D.model := circD_pos _
  have hsa : a / c = s := by rw [ea, ec, sA]; field_simp
  exact ⟨div_pos (circD_pos _) hD, hsa ▸ hs0, hsa ▸ hs1⟩

set_option maxHeartbeats 1000000 in
theorem t4_M2_rows45 (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) :
    ((D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = 2 * β) →
      ∃ M1 M2 : ℤ, (M1 : ℝ) = (circD D.target / circD D.model) * ((a / c) * (1 - a / c) * (2 + a / c)) ∧
        (M2 : ℝ) = -((circD D.target / circD D.model) * ((a / c) * (2 - a / c) * (1 + a / c)))) ∧
    ((D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = α + β) →
      ∃ M1 M2 : ℤ, (M1 : ℝ) = (circD D.target / circD D.model) * (a / c) ∧
        (M2 : ℝ) = (circD D.target / circD D.model) * (a / c)) := by
  obtain ⟨ha, hb, hc, hαpos, hβpos⟩ := model_abc_pos h
  obtain ⟨s, hs0, hs1, sA, sB, sG, s2A, sAB, s3A, s2B⟩ := sin_table hrel hαpos hβpos
  have hsδ : 0 < Real.sin (α + β) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hfull := h
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  have ea : a = circD D.model * Real.sin α := by rw [← o0, oppLen_eq, h0]
  have eb : b = circD D.model * Real.sin β := by rw [← o1, oppLen_eq, h1]
  have ec : c = circD D.model * Real.sin (α + β) := by rw [← o2, oppLen_eq, h2, sG]
  have hD : 0 < circD D.model := circD_pos _
  have hDne := hD.ne'
  have hsδne := hsδ.ne'
  have hsa : a / c = s := by rw [ea, ec, sA]; field_simp
  have hcs : a = s * c := by rw [← hsa]; field_simp
  have hbs : b = (1 - s ^ 2) * c := by rw [eb, ec, sB]; ring
  have hDt : circD D.target = (circD D.target / circD D.model) * circD D.model := by field_simp
  set Λ := circD D.target / circD D.model with hΛ
  have side : ∀ (k : Fin 3) (x : ℝ), Real.sin (D.target.angleAt k) = x * Real.sin (α + β) →
      D.target.oppLen k = Λ * c * x := by
    intro k x hx
    rw [oppLen_eq, hx, hDt, ec]; ring
  have hpos2 : 0 < c * ((1 - s) * (2 + s)) := mul_pos hc (mul_pos (by linarith) (by linarith))
  have hcb : c + b - a = c * ((1 - s) * (2 + s)) := by rw [hcs, hbs]; ring
  have hmodel0 : ∀ k, ((D.model.angleAt k : ℝ) : Real.Angle) ∈ (chiAt α hα 0 (D.target.leftUnit 0).angle).L :=
    D.model.threeAlpha_angles_mem hα hrel hfull 0
  have hMp : (chiAt α hα 0 (D.target.leftUnit 0).angle).paperK D.model = -(c + b - a) := by
    rw [← GridChar.tileValue_eq_paperK _ (chiAt_sq _ _ _ _) _ hmodel0, chiAt_tileValue]
    exact threeAlpha_tileValue_plus D.model hα hrel hfull
  rw [hsa]
  refine ⟨?_, ?_⟩
  · rintro ⟨hP0, hP1, hP2⟩
    set anc := (D.target.leftUnit 0).angle with hancdef
    have e2α : ((2 * α : ℝ) : Real.Angle)
        = ((((-2 : ℤ) : ℝ) * Real.pi + ((4 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) : ℝ) : Real.Angle) := by
      congr 1; push_cast; ring
    have eα : ((α : ℝ) : Real.Angle)
        = ((((-1 : ℤ) : ℝ) * Real.pi + ((2 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) : ℝ) : Real.Angle) := by
      congr 1; push_cast; ring
    have e2β : ((2 * β : ℝ) : Real.Angle)
        = ((((4 : ℤ) : ℝ) * Real.pi + ((-6 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) : ℝ) : Real.Angle) := by
      congr 1; push_cast; linarith
    have htarget : ∀ k, ((D.target.angleAt k : ℝ) : Real.Angle) ∈ (chiAt α hα 0 anc).L := by
      intro k
      fin_cases k
      · show ((D.target.angleAt 0 : ℝ) : Real.Angle) ∈ _
        rw [hP0, e2α]; exact chiAt_mem _ _ _ _ _ _
      · show ((D.target.angleAt 1 : ℝ) : Real.Angle) ∈ _
        rw [hP1, eα]; exact chiAt_mem _ _ _ _ _ _
      · show ((D.target.angleAt 2 : ℝ) : Real.Angle) ∈ _
        rw [hP2, e2β]; exact chiAt_mem _ _ _ _ _ _
    have hc2α : (chiAt α hα 0 anc).chi ((2 * α : ℝ) : Real.Angle) = 1 := by
      rw [e2α, chiAt_chi, if_pos (by decide)]
    have hcα : (chiAt α hα 0 anc).chi ((α : ℝ) : Real.Angle) = -1 := by
      rw [eα, chiAt_chi, if_neg (by decide)]
    have hc2β : (chiAt α hα 0 anc).chi ((2 * β : ℝ) : Real.Angle) = 1 := by
      rw [e2β, chiAt_chi, if_pos (by decide)]
    have hPK : (chiAt α hα 0 anc).paperK D.target
        = -(D.target.oppLen 0 - D.target.oppLen 1 + D.target.oppLen 2) := by
      unfold GridChar.paperK
      rw [Fin.sum_univ_three, hP0, hP1, hP2, hc2α, hcα, hc2β]
      ring
    obtain ⟨S, -, -, hSe⟩ := D.triangle_boundary_anchor (chiAt α hα 0 anc)
      (chiAt_sq _ _ _ _) hmodel0 htarget 0 rfl
    have hchi2 : (chiAt α hα 0 anc).chi ((D.target.angleAt (0 + 2) : ℝ) : Real.Angle) = 1 := by
      rw [show (0 : Fin 3) + 2 = 2 from rfl, hP2, hc2β]
    rw [hMp, hchi2, hPK] at hSe
    rw [side 0 (s * (2 - s ^ 2)) (by rw [hP0, s2A]), side 1 s (by rw [hP1, sA]),
      side 2 (s * (1 - s ^ 2) * (3 - s ^ 2)) (by rw [hP2, s2B])] at hSe
    rw [hcb] at hSe
    obtain ⟨M, hMp1, hM⟩ := (t4_M1 D hα hrel hfull).2.2.2.1 ⟨hP0, hP1, hP2⟩
    refine ⟨M, S, ?_, ?_⟩
    · rw [hsa] at hM; exact hM
    · refine mul_right_cancel₀ hpos2.ne' ?_
      linear_combination (-1 : ℝ) * hSe
  · rintro ⟨hP0, hP1, hP2⟩
    set anc := (D.target.leftUnit 0).angle with hancdef
    have e2α : ((2 * α : ℝ) : Real.Angle)
        = ((((-2 : ℤ) : ℝ) * Real.pi + ((4 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) : ℝ) : Real.Angle) := by
      congr 1; push_cast; ring
    have eβ : ((β : ℝ) : Real.Angle)
        = ((((2 : ℤ) : ℝ) * Real.pi + ((-3 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) : ℝ) : Real.Angle) := by
      congr 1; push_cast; linarith
    have eAB : ((α + β : ℝ) : Real.Angle)
        = ((((1 : ℤ) : ℝ) * Real.pi + ((-1 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) : ℝ) : Real.Angle) := by
      congr 1; push_cast; linarith
    have htarget : ∀ k, ((D.target.angleAt k : ℝ) : Real.Angle) ∈ (chiAt α hα 0 anc).L := by
      intro k
      fin_cases k
      · show ((D.target.angleAt 0 : ℝ) : Real.Angle) ∈ _
        rw [hP0, e2α]; exact chiAt_mem _ _ _ _ _ _
      · show ((D.target.angleAt 1 : ℝ) : Real.Angle) ∈ _
        rw [hP1, eβ]; exact chiAt_mem _ _ _ _ _ _
      · show ((D.target.angleAt 2 : ℝ) : Real.Angle) ∈ _
        rw [hP2, eAB]; exact chiAt_mem _ _ _ _ _ _
    have hc2α : (chiAt α hα 0 anc).chi ((2 * α : ℝ) : Real.Angle) = 1 := by
      rw [e2α, chiAt_chi, if_pos (by decide)]
    have hcβ : (chiAt α hα 0 anc).chi ((β : ℝ) : Real.Angle) = 1 := by
      rw [eβ, chiAt_chi, if_pos (by decide)]
    have hcAB : (chiAt α hα 0 anc).chi ((α + β : ℝ) : Real.Angle) = -1 := by
      rw [eAB, chiAt_chi, if_neg (by decide)]
    have hPK : (chiAt α hα 0 anc).paperK D.target
        = -(D.target.oppLen 0 + D.target.oppLen 1 - D.target.oppLen 2) := by
      unfold GridChar.paperK
      rw [Fin.sum_univ_three, hP0, hP1, hP2, hc2α, hcβ, hcAB]
      ring
    obtain ⟨S, -, -, hSe⟩ := D.triangle_boundary_anchor (chiAt α hα 0 anc)
      (chiAt_sq _ _ _ _) hmodel0 htarget 0 rfl
    have hchi2 : (chiAt α hα 0 anc).chi ((D.target.angleAt (0 + 2) : ℝ) : Real.Angle) = -1 := by
      rw [show (0 : Fin 3) + 2 = 2 from rfl, hP2, hcAB]
    rw [hMp, hchi2, hPK] at hSe
    rw [side 0 (s * (2 - s ^ 2)) (by rw [hP0, s2A]), side 1 (1 - s ^ 2) (by rw [hP1, sB]),
      side 2 1 (by rw [hP2]; ring)] at hSe
    rw [hcb] at hSe
    obtain ⟨M, hMp1, hM⟩ := (t4_M1 D hα hrel hfull).2.2.2.2 ⟨hP0, hP1, hP2⟩
    refine ⟨M, S, ?_, ?_⟩
    · rw [hsa] at hM; exact hM
    · refine mul_right_cancel₀ hpos2.ne' ?_
      linear_combination (-1 : ℝ) * hSe

/-- all positivity facts for `0 < s < 1`, `0 < Λ` -/
theorem t4_pos (Λ s : ℝ) (hΛ : 0 < Λ) (h0 : 0 < s) (h1 : s < 1) :
    0 < Λ * (s * (2 + s) / (1 + s)) ∧ 0 < Λ * (s * (2 - s) / (1 - s)) ∧
    0 < Λ * ((1 - s) * (1 + s) ^ 2) ∧ 0 < Λ * ((1 - s) ^ 2 * (1 + s)) ∧
    0 < Λ * (1 / (1 + s)) ∧ 0 < Λ * (1 / (1 - s)) ∧
    0 < Λ * (s * (1 - s) * (2 + s)) ∧ 0 < Λ * (s * (2 - s) * (1 + s)) ∧ 0 < Λ * s := by
  have a1 : 0 < 1 - s := by linarith
  have a2 : 0 < 1 + s := by linarith
  have a3 : 0 < 2 + s := by linarith
  have a4 : 0 < 2 - s := by linarith
  refine ⟨mul_pos hΛ (div_pos (mul_pos h0 a3) a2), mul_pos hΛ (div_pos (mul_pos h0 a4) a1),
    mul_pos hΛ (mul_pos a1 (pow_pos a2 2)), mul_pos hΛ (mul_pos (pow_pos a1 2) a2),
    mul_pos hΛ (one_div_pos.mpr a2), mul_pos hΛ (one_div_pos.mpr a1),
    mul_pos hΛ (mul_pos (mul_pos h0 a1) a3), mul_pos hΛ (mul_pos (mul_pos h0 a4) a2),
    mul_pos hΛ h0⟩

/-- **Beeson Theorem 4, closing sentence** (UNAUDITED; (H1)): for all five shapes the integers `M1, M2` of the printed
table exist with the printed values, `M1 != 0`, `M2 != 0`, and in the shape `(2alpha, beta, alpha+beta)`
`Lambda = M1 / s`.  `Lambda = circD target / circD model`, `s = a / c`. -/
theorem t4_final (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) :
    ((D.target.angleAt 0 = α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + 2 * β) →
      ∃ M1 M2 : ℤ, (M1 : ℝ) = (circD D.target / circD D.model) * ((a / c) * (2 + a / c) / (1 + a / c)) ∧
        (M2 : ℝ) = -((circD D.target / circD D.model) * ((a / c) * (2 - a / c) / (1 - a / c))) ∧
        M1 ≠ 0 ∧ M2 ≠ 0) ∧
    ((D.target.angleAt 0 = β ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = 3 * α) →
      ∃ M1 M2 : ℤ, (M1 : ℝ) = (circD D.target / circD D.model) * ((1 - a / c) * (1 + a / c) ^ 2) ∧
        (M2 : ℝ) = -((circD D.target / circD D.model) * ((1 - a / c) ^ 2 * (1 + a / c))) ∧
        M1 ≠ 0 ∧ M2 ≠ 0) ∧
    ((D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α + β ∧ D.target.angleAt 2 = α) →
      ∃ M1 M2 : ℤ, (M1 : ℝ) = (circD D.target / circD D.model) * (1 / (1 + a / c)) ∧
        (M2 : ℝ) = -((circD D.target / circD D.model) * (1 / (1 - a / c))) ∧ M1 ≠ 0 ∧ M2 ≠ 0) ∧
    ((D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = 2 * β) →
      ∃ M1 M2 : ℤ, (M1 : ℝ) = (circD D.target / circD D.model) * ((a / c) * (1 - a / c) * (2 + a / c)) ∧
        (M2 : ℝ) = -((circD D.target / circD D.model) * ((a / c) * (2 - a / c) * (1 + a / c))) ∧
        M1 ≠ 0 ∧ M2 ≠ 0) ∧
    ((D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = α + β) →
      ∃ M1 M2 : ℤ, (M1 : ℝ) = (circD D.target / circD D.model) * (a / c) ∧
        (M2 : ℝ) = (circD D.target / circD D.model) * (a / c) ∧ M1 ≠ 0 ∧ M2 ≠ 0 ∧
        circD D.target / circD D.model = (M1 : ℝ) / (a / c)) := by
  obtain ⟨hΛ, hs0, hs1⟩ := t4_aux D hrel h
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := t4_pos _ _ hΛ hs0 hs1
  obtain ⟨T1, T2, T3⟩ := t4_M2_T5 D hα hrel h
  obtain ⟨R4, R5⟩ := t4_M2_rows45 D hα hrel h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e
    obtain ⟨M1, M2, h1, h2⟩ := T1 e
    refine ⟨M1, M2, h1, h2, ?_, ?_⟩
    · intro z; rw [z] at h1; simp only [Int.cast_zero] at h1; linarith
    · intro z; rw [z] at h2; simp only [Int.cast_zero] at h2; linarith
  · intro e
    obtain ⟨M1, M2, h1, h2, -⟩ := T2 e
    refine ⟨M1, M2, h1, h2, ?_, ?_⟩
    · intro z; rw [z] at h1; simp only [Int.cast_zero] at h1; linarith
    · intro z; rw [z] at h2; simp only [Int.cast_zero] at h2; linarith
  · intro e
    obtain ⟨M1, M2, h1, h2, -⟩ := T3 e
    refine ⟨M1, M2, h1, h2, ?_, ?_⟩
    · intro z; rw [z] at h1; simp only [Int.cast_zero] at h1; linarith
    · intro z; rw [z] at h2; simp only [Int.cast_zero] at h2; linarith
  · intro e
    obtain ⟨M1, M2, h1, h2⟩ := R4 e
    refine ⟨M1, M2, h1, h2, ?_, ?_⟩
    · intro z; rw [z] at h1; simp only [Int.cast_zero] at h1; linarith
    · intro z; rw [z] at h2; simp only [Int.cast_zero] at h2; linarith
  · intro e
    obtain ⟨M1, M2, h1, h2⟩ := R5 e
    refine ⟨M1, M2, h1, h2, ?_, ?_, ?_⟩
    · intro z; rw [z] at h1; simp only [Int.cast_zero] at h1; linarith
    · intro z; rw [z] at h2; simp only [Int.cast_zero] at h2; linarith
    · rw [h1]; exact (mul_div_cancel_right₀ _ hs0.ne').symm

end Erdos634.BeesonColoring

#print axioms Erdos634.BeesonColoring.t4_M2_rows45
#print axioms Erdos634.BeesonColoring.t4_final
