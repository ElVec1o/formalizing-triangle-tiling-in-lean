-- Draft/ThmIsoShBridge.lean — two helper lemmas bridging `TwoPiThreeData` to `BaseAlphaData`
-- for the C10 (thm:iso) proof:
--   (1) `cos_alpha_of_TwoPiThree`: derives cos(α) = (a+2b)/(2c) and side positivity.
--   (2) `base_alpha_of_isoTP`: from model TwoPiThreeData and an isosceles base-α TgtAngles,
--       constructs BaseAlphaData on the target with an explicit scale μ.
-- Formalization debt; NOT /goal progress.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.Draft.FluxE2Pi3Row9
import Erdos634.Draft.FluxCRow5
import Erdos634.Draft.A1FieldClause
import Erdos634.Draft.TheoremPConditional

open scoped Classical

namespace Erdos634.Geometry

open Erdos634.Draft.TheoremPConditional
open A1Field (sin_angle_pos)

/-- **Lemma 1** (`cos_alpha_of_TwoPiThree`): For a `2π/3` tile with data `(α, a, b, c)`,
    `Real.cos α = (a + 2 * b) / (2 * c)`, and `0 < c`, `0 < a`, `0 < b`. -/
theorem cos_alpha_of_TwoPiThree (T : Tri) {α a b c : ℝ}
    (h : T.TwoPiThreeData α a b c) :
    Real.cos α = (a + 2 * b) / (2 * c) ∧ 0 < c ∧ 0 < a ∧ 0 < b := by
  obtain ⟨σ, hα0, ha, hα1, hb, hγ, hc⟩ := h
  have ha0 : 0 < a := ha ▸ T.oppLen_pos (σ 0)
  have hb0 : 0 < b := hb ▸ T.oppLen_pos (σ 1)
  have hc0 : 0 < c := hc ▸ T.oppLen_pos (σ 2)
  -- Law of cosines at angle 2π/3 (vertex σ 2): c² = a² + ab + b²
  have hlc : c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
    have hl := T.lawCos_perm σ
    rw [ha, hb, hc, hγ,
        show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
        Real.cos_pi_sub, Real.cos_pi_div_three] at hl
    linarith
  -- Side sums at vertex σ 0 (used to identify the two remaining sides as b, c)
  have hsum1 : T.oppLen (σ 0 + 1) + T.oppLen (σ 0 + 2) = b + c := by
    have s1 := T.sum_rot 1 (σ 0)
    have s2 := T.sum_perm 1 σ
    simp only [pow_one] at s1 s2
    rw [ha, hb, hc] at s2
    rw [ha] at s1
    linarith
  have hsum2 : T.oppLen (σ 0 + 1) ^ 2 + T.oppLen (σ 0 + 2) ^ 2 = b ^ 2 + c ^ 2 := by
    have s1 := T.sum_rot 2 (σ 0)
    have s2 := T.sum_perm 2 σ
    rw [ha, hb, hc] at s2
    rw [ha] at s1
    linarith
  -- The product of the two remaining sides equals bc
  have hprod : T.oppLen (σ 0 + 1) * T.oppLen (σ 0 + 2) = b * c := by
    nlinarith [sq_nonneg (T.oppLen (σ 0 + 1) - T.oppLen (σ 0 + 2)),
               T.oppLen_pos (σ 0 + 1), T.oppLen_pos (σ 0 + 2)]
  -- Law of cosines at angle α (vertex σ 0): a² = b² + c² − 2bc·cos(α)
  have hla : a ^ 2 = b ^ 2 + c ^ 2 - 2 * b * c * Real.cos α := by
    have hl := T.lawCos (σ 0)
    rw [ha, hα0] at hl
    linear_combination hl + hsum2 - 2 * Real.cos α * hprod
  -- Derive cos(α) = (a + 2b) / (2c)
  have h_rhs : b ^ 2 + c ^ 2 - a ^ 2 = b * (a + 2 * b) := by linear_combination hlc
  have h1 : 2 * b * c * Real.cos α = b * (a + 2 * b) := by linarith [hla, h_rhs]
  refine ⟨?_, hc0, ha0, hb0⟩
  rw [eq_div_iff (by positivity : (2 : ℝ) * c ≠ 0)]
  exact mul_left_cancel₀ hb0.ne'
    (show b * (Real.cos α * (2 * c)) = b * (a + 2 * b) by linear_combination h1)

/-- **Lemma 2** (`base_alpha_of_isoTP`): From `TwoPiThreeData` on the model and `TgtAngles`
    giving an isosceles base-α target (both base angles `α`, apex angle `α + 3*(π/3 − α)`),
    construct `BaseAlphaData` on the target with explicit scale `μ > 0`. -/
theorem base_alpha_of_isoTP {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : TgtAngles D α α (α + 3 * (Real.pi / 3 - α))) :
    ∃ μ > 0, D.target.BaseAlphaData α a b c μ := by
  obtain ⟨cos_eq, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  obtain ⟨σ, htα0, htα1, htα2⟩ := ht
  -- sin(α) > 0, since it equals sin of an interior angle of D.target
  have hsin_α_pos : 0 < Real.sin α := by
    have := sin_angle_pos D.target (σ 0)
    rwa [htα0] at this
  -- Law of sines at σ0 vs σ1 (equal angles α → equal opposite sides)
  have hls01 := D.target.lawSin (σ 0) (σ 1)
  rw [htα0, htα1] at hls01
  have hoppL01 : D.target.oppLen (σ 1) = D.target.oppLen (σ 0) :=
    mul_left_cancel₀ hsin_α_pos.ne' hls01
  -- Angle at σ2 equals π − 2α (= α + 3*(π/3 − α) by ring)
  have hangle2 : D.target.angleAt (σ 2) = Real.pi - 2 * α := by rw [htα2]; ring
  -- sin(π − 2α) = 2 sin α cos α
  have hsin2 : Real.sin (D.target.angleAt (σ 2)) = 2 * Real.sin α * Real.cos α := by
    rw [hangle2, Real.sin_pi_sub, Real.sin_two_mul]
  -- Law of sines at σ0 vs σ2
  have hls02 := D.target.lawSin (σ 0) (σ 2)
  rw [htα0, hsin2] at hls02
  -- oppLen(σ2) = 2 cos α * oppLen(σ0)
  have hoppL2 : D.target.oppLen (σ 2) = 2 * Real.cos α * D.target.oppLen (σ 0) :=
    mul_left_cancel₀ hsin_α_pos.ne' (by linear_combination hls02)
  -- The scale μ = oppLen(σ0) / c
  have hoppL0_pos : 0 < D.target.oppLen (σ 0) := D.target.oppLen_pos (σ 0)
  have hμ_pos : 0 < D.target.oppLen (σ 0) / c := div_pos hoppL0_pos hc0
  -- The key side equalities
  have hside0 : D.target.oppLen (σ 0) = D.target.oppLen (σ 0) / c * c :=
    (div_mul_cancel₀ (D.target.oppLen (σ 0)) hc0.ne').symm
  have hside1 : D.target.oppLen (σ 1) = D.target.oppLen (σ 0) / c * c := by
    rw [hoppL01]; exact hside0
  have hside2 : D.target.oppLen (σ 2) = D.target.oppLen (σ 0) / c * (a + 2 * b) := by
    rw [hoppL2, cos_eq]
    field_simp [hc0.ne']
  -- Assemble BaseAlphaData = 0 < μ ∧ GridTriData α 0 1 0 1 3 (-2) (μc) (μc) (μ(a+2b))
  refine ⟨D.target.oppLen (σ 0) / c, hμ_pos, ?_⟩
  constructor
  · exact hμ_pos
  · -- GridTriData: exhibit σ with the six angle/side requirements
    exact ⟨σ,
      by rw [htα0]; push_cast; ring,
      hside0,
      by rw [htα1]; push_cast; ring,
      hside1,
      by rw [htα2]; push_cast; ring,
      hside2⟩

end Erdos634.Geometry
