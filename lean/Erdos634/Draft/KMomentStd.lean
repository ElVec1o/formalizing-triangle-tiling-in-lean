-- Draft/KMomentStd.lean — CASE A, node A3 (Lemma K, K2 half), route (b) "moments", step 1:
-- the monomial moments of the reference triangle `AreaDet.stdCarrier` are RATIONAL:
--
--   ∫_{stdCarrier} x₀^i x₁^j = qstd i j ∈ ℚ,   qstd i j = Σ_{l ≤ j+1} C(j+1,l)(−1)^l / ((j+1)(i+l+1)).
--
-- Rationality is exactly what lets the moment identity of a dissection be moved by a field
-- embedding σ of ℚ(ζ_{4n}) (Draft/KMomentTri.lean, Draft/KConjTransfer.lean).
-- Formalization debt on a paper-level PROVED node; NOT /goal progress.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
-- H59: no parameter pair (e, f) is evaluated here.
import Erdos634.AreaDet
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory Set

namespace Erdos634.KMoment

open Erdos634.Geometry Erdos634.AreaDet

/-- The rational value of `∫_{stdCarrier} x₀^i x₁^j`. -/
def qstd (i j : ℕ) : ℚ :=
  ∑ l ∈ Finset.range (j + 2), ((j + 1).choose l : ℚ) * (-1) ^ l / (((j : ℚ) + 1) * ((i : ℚ) + l + 1))

/-- The plane as `ℝ × ℝ`, measure-preservingly. -/
noncomputable def E2 : Plane ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

theorem E2_mp : MeasurePreserving E2 volume volume :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).trans
    (volume_preserving_finTwoArrow ℝ)

theorem E2_apply (x : Plane) : E2 x = (x 0, x 1) := rfl

/-- The reference triangle in `ℝ × ℝ`. -/
def Tset : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}

theorem stdCarrier_eq : stdCarrier = E2 ⁻¹' Tset := by
  ext x; rw [mem_stdCarrier_iff]; rfl

theorem Tset_closed : IsClosed Tset := by
  apply IsClosed.inter (isClosed_le continuous_const continuous_fst)
  apply IsClosed.inter (isClosed_le continuous_const continuous_snd)
  exact isClosed_le (continuous_fst.add continuous_snd) continuous_const

theorem Tset_compact : IsCompact Tset := by
  apply ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod
    (isCompact_Icc (a := (0 : ℝ)) (b := 1))).of_isClosed_subset Tset_closed
  rintro ⟨x, y⟩ ⟨h1, h2, h3⟩
  simp only at h1 h2 h3
  exact ⟨⟨h1, by linarith⟩, ⟨h2, by linarith⟩⟩

/-- The inner (y) integral. -/
theorem inner_int (i j : ℕ) (x : ℝ) :
    ∫ y, Tset.indicator (fun p : ℝ × ℝ => p.1 ^ i * p.2 ^ j) (x, y)
      = (Icc (0 : ℝ) 1).indicator (fun x => x ^ i * ((1 - x) ^ (j + 1) / (j + 1))) x := by
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · rw [indicator_of_mem hx]
    have e : (fun y => Tset.indicator (fun p : ℝ × ℝ => p.1 ^ i * p.2 ^ j) (x, y))
        = (Icc (0 : ℝ) (1 - x)).indicator (fun y => x ^ i * y ^ j) := by
      funext y
      by_cases hy : y ∈ Icc (0 : ℝ) (1 - x)
      · rw [indicator_of_mem hy, indicator_of_mem]
        exact ⟨hx.1, hy.1, by linarith [hy.2]⟩
      · rw [indicator_of_notMem hy, indicator_of_notMem]
        rintro ⟨_, h2, h3⟩; exact hy ⟨h2, by simp only at h3; linarith⟩
    rw [e, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith [hx.2]), intervalIntegral.integral_const_mul,
      integral_pow]
    congr 1; ring
  · rw [indicator_of_notMem hx]
    have e : (fun y => Tset.indicator (fun p : ℝ × ℝ => p.1 ^ i * p.2 ^ j) (x, y)) = fun _ => 0 := by
      funext y
      rw [indicator_of_notMem]
      rintro ⟨h1, h2, h3⟩; exact hx ⟨h1, by simp only at h2 h3; linarith⟩
    rw [e, integral_zero]

theorem outer_int (i j : ℕ) :
    ∫ x in (0 : ℝ)..1, x ^ i * ((1 - x) ^ (j + 1) / (j + 1)) = (qstd i j : ℝ) := by
  have hexp : ∀ x : ℝ, x ^ i * ((1 - x) ^ (j + 1) / (j + 1))
      = ∑ l ∈ Finset.range (j + 2),
          (((j + 1).choose l : ℝ) * (-1) ^ l / ((j : ℝ) + 1)) * x ^ (i + l) := by
    intro x
    have hb : (1 - x) ^ (j + 1) = ∑ l ∈ Finset.range (j + 1 + 1),
        (-x) ^ l * 1 ^ (j + 1 - l) * ((j + 1).choose l : ℝ) := by
      rw [← add_pow]; ring
    rw [hb, Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [neg_pow, one_pow, pow_add]; ring
  simp_rw [hexp]
  rw [intervalIntegral.integral_finsetSum (fun l _ => by
    exact (continuous_const.mul (continuous_pow _)).intervalIntegrable _ _)]
  unfold qstd; push_cast
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [intervalIntegral.integral_const_mul, integral_pow]
  push_cast
  have h1 : (j : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (i : ℝ) + l + 1 ≠ 0 := by positivity
  field_simp
  simp

/-- **Monomial moments of the reference triangle are rational.** -/
theorem integral_std (i j : ℕ) :
    ∫ x in stdCarrier, (x 0) ^ i * (x 1) ^ j = (qstd i j : ℝ) := by
  rw [stdCarrier_eq]
  have h := E2_mp.setIntegral_preimage_emb E2.measurableEmbedding
    (fun p : ℝ × ℝ => p.1 ^ i * p.2 ^ j) Tset
  simp only [E2_apply] at h
  rw [h, ← integral_indicator Tset_closed.measurableSet]
  have hint : Integrable (Tset.indicator (fun p : ℝ × ℝ => p.1 ^ i * p.2 ^ j)) volume := by
    rw [integrable_indicator_iff Tset_closed.measurableSet]
    exact ((continuous_fst.pow i).mul (continuous_snd.pow j)).continuousOn.integrableOn_compact
      Tset_compact
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [integral_prod _ hint]
  simp_rw [inner_int]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one, outer_int]

end Erdos634.KMoment

#print axioms Erdos634.KMoment.integral_std
