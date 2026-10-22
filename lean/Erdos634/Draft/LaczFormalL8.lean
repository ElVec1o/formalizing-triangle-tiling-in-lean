-- Draft/LaczFormalL8.lean -- atom L8, the elementary corner of the reptile theorem (Snover-Waiveris-Williams 1991;
-- Beeson-Rosu Thm 5): if the target is similar to the tile with ratio mu, then N = mu^2 (area), mu = sqrt N, and
-- mu is rational iff N is a perfect square.  Any N, any similarity (vertex correspondence free).
-- NOT the reptile theorem: the content "N non-square => N = M^2 + K^2 (right triangle, legs M/K) or N = 3 M^2
-- (30-60-90)" is NOT here (atom L8 stays PARTIAL).  UNAUDITED.  Credit: SWW, Beeson, Beeson-Rosu.
import Erdos634.Draft.LaczFormalL6Wit1
import Erdos634.Draft.FluxERow2S

open scoped Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional Erdos634.CertCoord
  Erdos634.Subdivision

namespace Erdos634.Draft.LaczFormal

/-- Same vertex labels: `N = μ²`. -/
theorem similar_ratio_sq {N : ℕ} (D : CongruentDissection N) (μ : ℝ)
    (hsim : ∀ k, D.target.angleAt k = D.model.angleAt k ∧
      D.target.oppLen k = μ * D.model.oppLen k) : 0 < μ ∧ (N : ℝ) = μ ^ 2 := by
  have h1 := D.target.oppLen_pos 0
  have h2 := D.model.oppLen_pos 0
  have hpos : 0 < μ := by
    by_contra hc; push Not at hc
    have := (hsim 0).2
    nlinarith
  refine ⟨hpos, ?_⟩
  have ha := Row3.RP.abs_det_target D
  rw [Row3.RP.abs_det_eq, Row3.RP.abs_det_eq, (hsim 1).2, (hsim 2).2, (hsim 0).1] at ha
  have hs : 0 < Real.sin (D.model.angleAt 0) :=
    Real.sin_pos_of_pos_of_lt_pi (Erdos634.MarchFlank.cornerAngle_pos D.model 0)
      (Erdos634.RouteOneVertexKill.cornerAngle_lt_pi D.model 0)
  have hp : 0 < D.model.oppLen 1 * D.model.oppLen 2 * Real.sin (D.model.angleAt 0) :=
    mul_pos (mul_pos (D.model.oppLen_pos 1) (D.model.oppLen_pos 2)) hs
  refine mul_right_cancel₀ hp.ne' ?_
  linear_combination -ha

/-- Any vertex correspondence `τ`. -/
theorem similar_ratio_sq_perm {N : ℕ} (D : CongruentDissection N) (μ : ℝ) (τ : Equiv.Perm (Fin 3))
    (hsim : ∀ k, D.target.angleAt k = D.model.angleAt (τ k) ∧
      D.target.oppLen k = μ * D.model.oppLen (τ k)) : 0 < μ ∧ (N : ℝ) = μ ^ 2 := by
  have hMa := Row2.angleAt_comp D.model (D.relabelModel τ).model τ (fun k => rfl)
  refine similar_ratio_sq (D.relabelModel τ) μ (fun k => ?_)
  rw [(hMa k).1, (hMa k).2]
  exact hsim k

/-- **Elementary corner of the reptile theorem.**  If the target is similar to the tile, the ratio is `√N`,
and it is rational exactly when `N` is a perfect square. -/
theorem similar_dichotomy {N : ℕ} (D : CongruentDissection N) (hs : SimilarTM D) :
    ∃ μ : ℝ, 0 < μ ∧ (N : ℝ) = μ ^ 2 ∧ μ = Real.sqrt N ∧ (Irrational μ ↔ ¬ IsSquare N) := by
  obtain ⟨μ, τ, h⟩ := hs
  obtain ⟨hpos, hN⟩ := similar_ratio_sq_perm D μ τ h
  have hμ : μ = Real.sqrt N := by
    rw [hN, Real.sqrt_sq hpos.le]
  exact ⟨μ, hpos, hN, hμ, by rw [hμ]; exact irrational_sqrt_natCast_iff⟩

/-- A similar target whose ratio is rational (the ratio is `√N` by `similar_dichotomy`) forces `N` square. -/
theorem similar_rational_square {N : ℕ} (D : CongruentDissection N) (hs : SimilarTM D)
    {μ : ℝ} (hμ : 0 < μ) (hN : (N : ℝ) = μ ^ 2) (hq : ∃ q : ℚ, (q : ℝ) = μ) : IsSquare N := by
  obtain ⟨μ', -, hN', hμ', hirr⟩ := similar_dichotomy D hs
  have : μ = μ' := by
    have h := hN.symm.trans hN'
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with e | e
    · exact e
    · have := Real.sqrt_nonneg (N : ℝ); rw [← hμ'] at this; linarith
  by_contra hn
  exact (hirr.mpr hn) (this ▸ hq)

/-- Non-vacuity: the scale-2 ladder of the equilateral tile (`D_i`, `N = 2*2`) is similar to its tile. -/
theorem D_i_similar : SimilarTM D_i := by
  refine ⟨2, 1, fun k => ⟨?_, ?_⟩⟩
  · show (bigTri (mkPt 0 0) (mkPt 2 0) (mkPt 1 (Real.sqrt 3)) TE.indep 2 (by norm_num)).angleAt k = _
    rw [bigTri_angleAt]; rfl
  · show (bigTri (mkPt 0 0) (mkPt 2 0) (mkPt 1 (Real.sqrt 3)) TE.indep 2 (by norm_num)).oppLen k = _
    rw [bigTri_oppLen]; norm_num; rfl

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.similar_dichotomy
#print axioms Erdos634.Draft.LaczFormal.D_i_similar
