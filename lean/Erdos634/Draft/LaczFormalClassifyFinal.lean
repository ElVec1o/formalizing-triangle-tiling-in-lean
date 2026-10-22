-- Draft/LaczFormalClassifyFinal.lean -- CLASSIFICATION with the three open equilateral shapes excluded.
--   `classify_commensurable_final`: for tile angles a_k pi/n (gcd 1, `Covered n`) the conclusion is SimilarTM, or the right-tile/isosceles-target shape,
--   or `ExcPair3 D`: one of the THREE valid n = 6 shapes.  The tiles (pi/12,7pi/12,pi/3), (pi/30,19pi/30,pi/3), (7pi/30,13pi/30,pi/3) with an
--   equilateral target are excluded by `Graph.no_tiling_12/30a/30b`.
-- UNAUDITED (NOTE).  Credit: Laczkovich (DCG 48 (2012), Thm 3.3 (5) Subcase IVa; Combinatorica 1990; DCG 1998; Discrete Math 140 (1995)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalClassifyAll
import Erdos634.Draft.LaczFormalGraphFinal

open scoped BigOperators Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional

namespace Erdos634.Draft.LaczFormal

variable {N : ℕ}

/-- The three valid exceptional shapes (all at `n = 6`). -/
def ExcPair3 (D : CongruentDissection N) : Prop :=
  (TileAngles D (1 * Real.pi / 6) (1 * Real.pi / 6) (4 * Real.pi / 6) ∧
    TgtAngles D (2 * Real.pi / 6) (2 * Real.pi / 6) (2 * Real.pi / 6))
  ∨ (TileAngles D (1 * Real.pi / 6) (2 * Real.pi / 6) (3 * Real.pi / 6) ∧
    TgtAngles D (1 * Real.pi / 6) (1 * Real.pi / 6) (4 * Real.pi / 6))
  ∨ (TileAngles D (1 * Real.pi / 6) (2 * Real.pi / 6) (3 * Real.pi / 6) ∧
    TgtAngles D (2 * Real.pi / 6) (2 * Real.pi / 6) (2 * Real.pi / 6))

theorem tileAngles_swap12 {D : CongruentDissection N} {x y z : ℝ} (h : TileAngles D x y z) :
    TileAngles D x z y := by
  have := TileAngles.reorder h (Equiv.swap 1 2)
  simpa [Equiv.swap_apply_of_ne_of_ne] using this

theorem excPair_reduce (D : CongruentDissection N) (h : ExcPair D) : ExcPair3 D := by
  rcases h with h | h | h | ⟨hT, hG⟩ | ⟨hT, hG⟩ | ⟨hT, hG⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact (Graph.no_tiling_12 D (tileAngles_swap12 hT) hG).elim
  · exact (Graph.no_tiling_30a D (tileAngles_swap12 hT) hG).elim
  · exact (Graph.no_tiling_30b D (tileAngles_swap12 hT) hG).elim

/-- **Classification of commensurable tiles (covered denominators), equilateral shapes excluded.** -/
theorem classify_commensurable_final (D : CongruentDissection N) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) (hcov : Covered n) :
    SimilarTM D ∨ (∃ k l : Fin 3, l ≠ k ∧ D.model.angleAt k = Real.pi / 2 ∧
        ∃ j₁ j₂ : Fin 3, j₁ ≠ j₂ ∧ D.target.angleAt j₁ = D.model.angleAt l ∧
          D.target.angleAt j₂ = D.model.angleAt l) ∨ ExcPair3 D := by
  rcases classify_commensurable D hn a ha hgcd hcov with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (excPair_reduce D h))

/-- Non-vacuity: the hypotheses are witnessed (ladder dissection, `n = 6`). -/
theorem classify_final_hyps_witness :
    ∃ (N : ℕ) (D : CongruentDissection N) (a : Fin 3 → ℕ),
      (∀ k, D.model.angleAt k = a k * Real.pi / (6 : ℕ)) ∧
      Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 ∧ Covered 6 :=
  classify_commensurable_hyps_witness

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.classify_commensurable_final
