-- Draft/LaczFormalL8Gen.lean -- atom L8 GENERAL, stages (a)+(b-lite): the reduction of the reptile theorem
-- (Snover-Waiveris-Williams 1991; Beeson-Rosu Thm 5) for ANY N, assembled from the Row2 lemmas that do NOT use
-- primality: for a dissection whose target is similar to the tile (ratio mu, same labels) and N NOT a perfect square,
--   (1) mu^2 = N and mu is irrational                         (area; Row2.mu_irrational)
--   (2) pi is in 2*Lambda, Lambda = <theta0, theta1, pi>       (Row2.lemmaW, contrapositive: else mu in Z, N square)
--   (3) side matrix D_ik in N (typed side counts) with D v = mu v, v = model sides > 0   (S1, any model)
--   (4) a/c, b/c are not both rational, all cos(theta_k) lie in Q(mu)                  (Row2.lemmaK_general)
-- What this does NOT contain (the exact blocker, see PLAN.md "L8 general"): Lemma E for general N, i.e. the
-- classification of the model when all angles are rational and cos in Q(sqrt N) (N=2M^2, 3M^2, 5M^2 families:
-- denominators q in {2,3,4,5,6} of the angles theta in (pi/q)Z), which Row2 handles only for N prime = 3 mod 4,
-- p >= 7 (Lemma Q), and the corner/side-word analysis of the non-scalene and rational-angle models.
-- UNAUDITED.  Credit: Snover-Waiveris-Williams, Beeson (Triangle tiling I), Beeson-Rosu.
import Erdos634.Draft.LaczFormalL8
import Erdos634.Draft.FluxERow2E

open scoped Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional

namespace Erdos634.Draft.LaczFormal

/-- **Reduction of the reptile theorem, any N.** -/
theorem similar_reduction {N : ℕ} (D : CongruentDissection N) (μ : ℝ)
    (hsim : ∀ k, D.target.angleAt k = D.model.angleAt k ∧
      D.target.oppLen k = μ * D.model.oppLen k) (hN : ¬ IsSquare N) :
    ((N : ℝ) = μ ^ 2 ∧ ¬ ∃ r : ℚ, μ = r) ∧
    (∃ y ∈ AddSubgroup.closure ({D.model.angleAt 0, D.model.angleAt 1, Real.pi} : Set ℝ),
      Real.pi = 2 * y) ∧
    (∀ i, ∑ j, (D.sideCountT i j : ℝ) * D.model.oppLen j = μ * D.model.oppLen i) ∧
    (¬ ((∃ r : ℚ, D.model.oppLen 0 = r * D.model.oppLen 2) ∧
        (∃ r : ℚ, D.model.oppLen 1 = r * D.model.oppLen 2))) ∧
    (∀ k, Row2.QMu μ (Real.cos (D.model.angleAt k))) := by
  have hside : ∀ k, D.target.oppLen k = μ * D.model.oppLen k := fun k => (hsim k).2
  obtain ⟨hμq, -⟩ := Row2.mu_irrational D μ hside hN
  obtain ⟨-, hnot, hcos⟩ := Row2.lemmaK_general D μ hside hN
  refine ⟨⟨(similar_ratio_sq D μ hsim).2, hμq⟩, ?_, Row2.sideCountT_eigen D μ hside, hnot, hcos⟩
  by_contra hc
  push Not at hc
  obtain ⟨S, hS, -⟩ := Row2.lemmaW D μ hsim hc
  apply hN
  have hsq := (similar_ratio_sq D μ hsim).2
  rw [hS] at hsq
  have : (N : ℤ) = S ^ 2 := by exact_mod_cast hsq
  have hN' : N = S.natAbs ^ 2 := by
    have := congrArg Int.natAbs this
    simpa [Int.natAbs_pow] using this
  exact ⟨S.natAbs, by rw [hN']; ring⟩

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.similar_reduction
