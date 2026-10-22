-- Draft/FDCScaleReduce.lean — the paper's normalization "after scaling the tile has integer sides",
-- made a theorem: `conicform_paper` for tiles with *commensurable* sides.
-- A homothety (`Realizable.scaleDissection`) preserves every angle and scales every length by `|r|`
-- (`homothetyEquiv_dist`), so a dissection whose tile sides are `μ·(a',b',c')`, `a',b',c' ∈ ℤ`, scales
-- by `μ⁻¹` to a dissection of the same size `N` with integer tile sides; the integer-side theorems
-- (`FDCConicFormPi3`) then apply.  This removes the "scaling reduction not formalized" caveat recorded
-- by the independent audit of `prop:conicform`.
-- Written 2026-10-05.  UNAUDITED.
import Erdos634.Realizable
import Erdos634.Draft.FDCConicFormPi3

namespace Erdos634.Draft.FDCScaleReduce

open Erdos634.Geometry Erdos634.Realizable Erdos634.Draft.FDCConicFormPi3

/-- A homothety preserves the unoriented angle at a vertex. -/
theorem homothetyEquiv_cornerAngle (p : Plane) (r : ℝ) (hr : r ≠ 0) (a b c : Plane) :
    cornerAngle (homothetyEquiv p r hr a) (homothetyEquiv p r hr b) (homothetyEquiv p r hr c)
      = cornerAngle a b c := by
  unfold cornerAngle EuclideanGeometry.angle
  simp only [homothetyEquiv_apply, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
  have h1 : (r • (a - p) + p) - (r • (b - p) + p) = r • (a - b) := by
    simp only [smul_sub]; abel
  have h2 : (r • (c - p) + p) - (r • (b - p) + p) = r • (c - b) := by
    simp only [smul_sub]; abel
  rw [h1, h2]
  exact InnerProductGeometry.angle_smul_smul hr _ _

theorem scale_model_angleAt {N : ℕ} (p : Plane) (r : ℝ) (hr : r ≠ 0) (D : CongruentDissection N)
    (k : Fin 3) : (scaleDissection p r hr D).model.angleAt k = D.model.angleAt k := by
  simp only [Tri.angleAt, scaleDissection_model_pts]
  exact homothetyEquiv_cornerAngle p r hr _ _ _

theorem scale_target_angleAt {N : ℕ} (p : Plane) (r : ℝ) (hr : r ≠ 0) (D : CongruentDissection N)
    (k : Fin 3) : (scaleDissection p r hr D).target.angleAt k = D.target.angleAt k := by
  simp only [Tri.angleAt, scaleDissection_target_pts]
  exact homothetyEquiv_cornerAngle p r hr _ _ _

theorem scale_model_oppLen {N : ℕ} (p : Plane) (r : ℝ) (hr : r ≠ 0) (D : CongruentDissection N)
    (k : Fin 3) : (scaleDissection p r hr D).model.oppLen k = |r| * D.model.oppLen k := by
  simp only [Tri.oppLen, scaleDissection_model_pts]
  exact homothetyEquiv_dist p r hr _ _

theorem scale_target_oppLen {N : ℕ} (p : Plane) (r : ℝ) (hr : r ≠ 0) (D : CongruentDissection N)
    (k : Fin 3) : (scaleDissection p r hr D).target.oppLen k = |r| * D.target.oppLen k := by
  simp only [Tri.oppLen, scaleDissection_target_pts]
  exact homothetyEquiv_dist p r hr _ _

/-- **`prop:conicform`, 2π/3 clause, for a tile with commensurable sides** (sides `μ·(a',b',c')`,
`a',b',c'` integers): scale to integer sides, then apply `conicform_2pi3_of_tiling_full`. -/
theorem conicform_2pi3_commensurable {N : ℕ} (D : CongruentDissection N) {α a b c S : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoPiThreeData α a b c)
    (hcomm : ∃ μ : ℝ, 0 < μ ∧ ∃ a' b' c' : ℤ,
      a = μ * a' ∧ b = μ * b' ∧ c = μ * c')
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) (hS : ∀ k, D.target.oppLen k = S) :
    ∃ u v : ℤ, u * v = 16 * (N : ℤ) ^ 2 ∧ (2 : ℤ) ∣ (u + v) ∧
      ∃ s : ℤ, (u + v) / 2 - 5 * (N : ℤ) = s ^ 2 ∧ s ∣ 3 * (N : ℤ) ∧
        (2 : ℤ) ∣ s - N ∧ (2 : ℤ) ∣ 3 * (N : ℤ) / s - N := by
  obtain ⟨μ, hμ, a', b', c', ha, hb, hc⟩ := hcomm
  have hr : μ⁻¹ ≠ 0 := inv_ne_zero hμ.ne'
  have hpos : |μ⁻¹| = μ⁻¹ := abs_of_pos (inv_pos.mpr hμ)
  have hmodel : (scaleDissection 0 μ⁻¹ hr D).model.TwoPiThreeData α a' b' c' := by
    obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
    refine ⟨σ, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [scale_model_angleAt]; exact h0
    · rw [scale_model_oppLen, hpos, o0, ha]; field_simp
    · rw [scale_model_angleAt]; exact h1
    · rw [scale_model_oppLen, hpos, o1, hb]; field_simp
    · rw [scale_model_angleAt]; exact h2
    · rw [scale_model_oppLen, hpos, o2, hc]; field_simp
  exact conicform_2pi3_of_tiling_full (scaleDissection 0 μ⁻¹ hr D) hα hmodel
    ⟨a', b', c', rfl, rfl, rfl⟩ (fun k => by rw [scale_target_angleAt]; exact hP k)
    (S := μ⁻¹ * S) (fun k => by rw [scale_target_oppLen, hpos, hS k])

/-- **`prop:conicform`, π/3 clause, for a tile with commensurable sides.** -/
theorem conicform_pi3_commensurable {N : ℕ} (D : CongruentDissection N) {α a b c S : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.SixtyData α a b c)
    (hcomm : ∃ μ : ℝ, 0 < μ ∧ ∃ a' b' c' : ℤ,
      a = μ * a' ∧ b = μ * b' ∧ c = μ * c')
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) (hS : ∀ k, D.target.oppLen k = S) :
    ∃ u v M : ℤ, u * v = 16 * (N : ℤ) ^ 2 ∧ (2 : ℤ) ∣ (u + v) ∧
      (u + v) / 2 = 5 * (N : ℤ) - M ^ 2 ∧ 0 < M ∧ (M : ℝ) < Real.sqrt N ∧ (2 : ℤ) ∣ M - N := by
  obtain ⟨μ, hμ, a', b', c', ha, hb, hc⟩ := hcomm
  have hr : μ⁻¹ ≠ 0 := inv_ne_zero hμ.ne'
  have hpos : |μ⁻¹| = μ⁻¹ := abs_of_pos (inv_pos.mpr hμ)
  have hmodel : (scaleDissection 0 μ⁻¹ hr D).model.SixtyData α a' b' c' := by
    obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
    refine ⟨σ, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [scale_model_angleAt]; exact h0
    · rw [scale_model_oppLen, hpos, o0, ha]; field_simp
    · rw [scale_model_angleAt]; exact h1
    · rw [scale_model_oppLen, hpos, o1, hb]; field_simp
    · rw [scale_model_angleAt]; exact h2
    · rw [scale_model_oppLen, hpos, o2, hc]; field_simp
  exact conicform_pi3_of_tiling (scaleDissection 0 μ⁻¹ hr D) hα hmodel
    ⟨a', b', c', rfl, rfl, rfl⟩ (fun k => by rw [scale_target_angleAt]; exact hP k)
    (S := μ⁻¹ * S) (fun k => by rw [scale_target_oppLen, hpos, hS k])

/-- **`prop:conicform`, both clauses, scale-free**: for a tile with commensurable sides (the paper's
"after scaling, integer sides"), the conic form of the paper. -/
theorem conicform_paper_scaled (N : ℕ) :
    (∀ (D : CongruentDissection N) (α a b c S : ℝ), (¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) →
      D.model.TwoPiThreeData α a b c →
      (∃ μ : ℝ, 0 < μ ∧ ∃ a' b' c' : ℤ, a = μ * a' ∧ b = μ * b' ∧ c = μ * c') →
      (∀ k, D.target.angleAt k = Real.pi / 3) → (∀ k, D.target.oppLen k = S) →
      ∃ u v : ℤ, u * v = 16 * (N : ℤ) ^ 2 ∧ (2 : ℤ) ∣ (u + v) ∧
        ∃ s : ℤ, (u + v) / 2 - 5 * (N : ℤ) = s ^ 2 ∧ s ∣ 3 * (N : ℤ) ∧
          (2 : ℤ) ∣ s - N ∧ (2 : ℤ) ∣ 3 * (N : ℤ) / s - N) ∧
    (∀ (D : CongruentDissection N) (α a b c S : ℝ), (¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) →
      D.model.SixtyData α a b c →
      (∃ μ : ℝ, 0 < μ ∧ ∃ a' b' c' : ℤ, a = μ * a' ∧ b = μ * b' ∧ c = μ * c') →
      (∀ k, D.target.angleAt k = Real.pi / 3) → (∀ k, D.target.oppLen k = S) →
      ∃ u v M : ℤ, u * v = 16 * (N : ℤ) ^ 2 ∧ (2 : ℤ) ∣ (u + v) ∧
        (u + v) / 2 = 5 * (N : ℤ) - M ^ 2 ∧ 0 < M ∧ (M : ℝ) < Real.sqrt N ∧ (2 : ℤ) ∣ M - N) :=
  ⟨fun D _ _ _ _ _ hα h hcomm hP hS => conicform_2pi3_commensurable D hα h hcomm hP hS,
   fun D _ _ _ _ _ hα h hcomm hP hS => conicform_pi3_commensurable D hα h hcomm hP hS⟩

end Erdos634.Draft.FDCScaleReduce

#print axioms Erdos634.Draft.FDCScaleReduce.conicform_paper_scaled
