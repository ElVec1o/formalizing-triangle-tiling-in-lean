-- Draft/KMomentDet.lean — CASE A, node A3 (Lemma K, K2 half), route (b) "moments", step 3:
-- MOMENT DETERMINACY for finite signed combinations of indicators of compact sets in the plane.
--
--   If  Σ_k c_k ∫_{U_k} x₀^i x₁^j = 0  for all i, j,  then  Σ_k c_k 1_{U_k} = 0  almost everywhere.
--
-- Route: polynomials are dense in C(K) on a closed ball K ⊇ ⋃ U_k (Stone–Weierstrass,
-- `ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints`, subalgebra = range of
-- `MvPolynomial.aeval` at the two coordinates), so the combination integrates every continuous
-- function to 0; conclude with `ae_eq_zero_of_integral_contDiff_smul_eq_zero`.
-- Formalization debt on a paper-level PROVED node; NOT /goal progress.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
-- H59: no parameter pair (e, f) is evaluated here.
import Erdos634.Draft.KMomentTri
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

open MeasureTheory Set MvPolynomial

namespace Erdos634.KMoment

open Erdos634.Geometry

variable {ι : Type*} [Fintype ι] {U : ι → Set Plane} (c : ι → ℝ)

/-- The signed combination `Σ c_k 1_{U_k}`. -/
noncomputable def comb (U : ι → Set Plane) (x : Plane) : ℝ := ∑ k, c k * (U k).indicator 1 x

theorem mul_comb (h : Plane → ℝ) (x : Plane) :
    h x * comb c U x = ∑ k, c k * (U k).indicator h x := by
  rw [comb, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases hx : x ∈ U k
  · simp [indicator_of_mem hx]; ring
  · simp [indicator_of_notMem hx]

theorem integrable_mul_comb (hU : ∀ k, IsCompact (U k)) {h : Plane → ℝ} (hh : Continuous h) :
    Integrable (fun x => h x * comb c U x) := by
  simp_rw [mul_comb]
  refine integrable_finsetSum _ (fun k _ => ?_)
  exact ((integrable_indicator_iff (hU k).measurableSet).mpr
    (hh.continuousOn.integrableOn_compact (hU k))).const_mul _

theorem integral_mul_comb (hU : ∀ k, IsCompact (U k)) {h : Plane → ℝ} (hh : Continuous h) :
    ∫ x, h x * comb c U x = ∑ k, c k * ∫ x in U k, h x := by
  simp_rw [mul_comb]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [integral_const_mul, integral_indicator (hU k).measurableSet]
  · intro k _
    exact ((integrable_indicator_iff (hU k).measurableSet).mpr
      (hh.continuousOn.integrableOn_compact (hU k))).const_mul _

theorem cont_coord (v : Fin 2) : Continuous (fun x : Plane => x v) := PiLp.continuous_apply 2 _ v

theorem cont_eval (P : MvPolynomial (Fin 2) ℝ) : Continuous (fun x : Plane => eval (fun v => x v) P) := by
  simp_rw [eval_eq']
  exact continuous_finsetSum _ (fun m _ => continuous_const.mul
    (continuous_finsetProd _ (fun v _ => (cont_coord v).pow _)))

/-- Polynomial moments vanish once monomial moments do. -/
theorem poly_moment (hU : ∀ k, IsCompact (U k))
    (hmom : ∀ i j : ℕ, ∑ k, c k * ∫ x in U k, (x 0) ^ i * (x 1) ^ j = 0)
    (P : MvPolynomial (Fin 2) ℝ) : ∫ x, eval (fun v => x v) P * comb c U x = 0 := by
  rw [integral_mul_comb c hU (cont_eval P)]
  simp_rw [eval_eq', Fin.prod_univ_two]
  have : ∀ k, ∫ x in U k, ∑ m ∈ P.support, coeff m P * ((x 0) ^ m 0 * (x 1) ^ m 1)
      = ∑ m ∈ P.support, coeff m P * ∫ x in U k, (x 0) ^ m 0 * (x 1) ^ m 1 := by
    intro k
    rw [integral_finsetSum]
    · simp_rw [integral_const_mul]
    · intro m _
      exact (continuous_const.mul (((cont_coord 0).pow _).mul ((cont_coord 1).pow _))).continuousOn
        |>.integrableOn_compact (hU k)
  simp_rw [this, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun m _ => ?_)
  have h := hmom (m 0) (m 1)
  calc ∑ k, c k * (coeff m P * ∫ x in U k, (x 0) ^ m 0 * (x 1) ^ m 1)
      = coeff m P * ∑ k, c k * ∫ x in U k, (x 0) ^ m 0 * (x 1) ^ m 1 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun k _ => by ring)
    _ = 0 := by rw [h, mul_zero]

/-! ## Stone–Weierstrass on a closed ball -/

section SW

variable (R : ℝ)

/-- The closed ball as a compact space. -/
abbrev Kb := Metric.closedBall (0 : Plane) R

instance : CompactSpace (Kb R) := isCompact_iff_compactSpace.mp (isCompact_closedBall 0 R)

/-- Coordinate functions on the ball. -/
def crd (v : Fin 2) : C(Kb R, ℝ) := ⟨fun x => (x : Plane) v, (cont_coord v).comp continuous_subtype_val⟩

/-- The polynomial subalgebra. -/
noncomputable def polyA : Subalgebra ℝ C(Kb R, ℝ) := (aeval (crd R)).range

theorem aeval_apply (P : MvPolynomial (Fin 2) ℝ) (x : Kb R) :
    (aeval (crd R) P) x = eval (fun v => (x : Plane) v) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [_root_.algebraMap_apply]
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp => simp [hp, crd]

theorem polyA_sep : (polyA R).SeparatesPoints := by
  intro x y hxy
  have : ∃ v, (x : Plane) v ≠ (y : Plane) v := by
    by_contra h; push Not at h
    exact hxy (Subtype.ext (PiLp.ext h))
  obtain ⟨v, hv⟩ := this
  exact ⟨crd R v, ⟨crd R v, ⟨X v, by simp⟩, rfl⟩, hv⟩

end SW

/-- **Moment determinacy.** -/
theorem ae_zero_of_moments (hU : ∀ k, IsCompact (U k))
    (hmom : ∀ i j : ℕ, ∑ k, c k * ∫ x in U k, (x 0) ^ i * (x 1) ^ j = 0) :
    ∀ᵐ x, comb c U x = 0 := by
  have hint : Integrable (comb c U) := by
    have := integrable_mul_comb c hU (h := fun _ => (1 : ℝ)) continuous_const
    simpa using this
  obtain ⟨R, hR⟩ := (isCompact_iUnion hU).isBounded.subset_closedBall (0 : Plane)
  have hsupp : ∀ x, x ∉ Metric.closedBall (0 : Plane) R → comb c U x = 0 := by
    intro x hx
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [indicator_of_notMem (fun h => hx (hR (mem_iUnion.mpr ⟨k, h⟩))), mul_zero]
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hint.locallyIntegrable
  intro g hg _
  have hgc : Continuous g := hg.continuous
  simp only [smul_eq_mul]
  set C := ∫ x, |comb c U x|
  have key : ∀ ε > 0, |∫ x, g x * comb c U x| ≤ ε * C := by
    intro ε hε
    let gK : C(Kb R, ℝ) := ⟨fun x => g x, hgc.comp continuous_subtype_val⟩
    obtain ⟨⟨p, hpA⟩, hp⟩ :=
      ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints (polyA R)
        (polyA_sep R) gK ε hε
    obtain ⟨P, rfl⟩ := hpA
    have hP := poly_moment c hU hmom P
    have hdiff : ∫ x, g x * comb c U x
        = ∫ x, (g x - eval (fun v => x v) P) * comb c U x := by
      simp_rw [sub_mul]
      rw [integral_sub (integrable_mul_comb c hU hgc) (integrable_mul_comb c hU (cont_eval P)), hP,
        sub_zero]
    rw [hdiff, ← Real.norm_eq_abs]
    have hb : ∀ x, ‖(g x - eval (fun v => x v) P) * comb c U x‖ ≤ ε * |comb c U x| := by
      intro x
      by_cases hx : x ∈ Metric.closedBall (0 : Plane) R
      · rw [norm_mul, Real.norm_eq_abs]
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        have h1 := ContinuousMap.norm_coe_le_norm ((aeval (crd R)) P - gK) ⟨x, hx⟩
        rw [ContinuousMap.sub_apply, aeval_apply, Real.norm_eq_abs] at h1
        have h2 : |g x - eval (fun v => x v) P| = |eval (fun v => x v) P - g x| := abs_sub_comm _ _
        rw [h2]; exact (h1.trans hp.le)
      · rw [hsupp x hx]; simp
    calc ‖∫ x, (g x - eval (fun v => x v) P) * comb c U x‖
        ≤ ∫ x, ε * |comb c U x| :=
          norm_integral_le_of_norm_le (hint.abs.const_mul ε) (Filter.Eventually.of_forall hb)
      _ = ε * C := integral_const_mul _ _
  have hC : 0 ≤ C := integral_nonneg (fun x => abs_nonneg _)
  have : |∫ x, g x * comb c U x| ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    have := key (δ / (C + 1)) (div_pos hδ (by linarith))
    calc _ ≤ δ / (C + 1) * C := this
      _ ≤ 0 + δ := by
        rw [zero_add, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith
  exact abs_nonpos_iff.mp this

end Erdos634.KMoment

#print axioms Erdos634.KMoment.ae_zero_of_moments
