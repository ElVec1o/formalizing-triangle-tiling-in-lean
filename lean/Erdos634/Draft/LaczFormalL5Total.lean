-- Draft/LaczFormalL5Total.lean -- atom L5, COMMENSURABLE half, ALL denominators n (Table 3 lines 1-2 of Beeson-Rosu / Beeson, from Laczkovich 1995 Thm 5.3), via `classify_total`.
-- A congruent dissection (any N, reflections) of a NON-EQUILATERAL triangle by a tile with angles a_k pi/n (gcd 1, any n): similar, or tile `(alpha, beta, pi/2)` with target `(beta, beta, 2 alpha)`.
-- UNAUDITED (NOTE).  Credit: Laczkovich (Discrete Math 140 (1995) Thm 5.1/5.3; DCG 48 (2012)), Beeson-Rosu, Beeson.
import Erdos634.Draft.LaczFormalL5Comm
import Erdos634.Draft.LaczFormalUnifC

open scoped BigOperators Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional

namespace Erdos634.Draft.LaczFormal

variable {N : ℕ}

theorem table3_comm_total (D : CongruentDissection N) (hne : ¬ Equilateral D) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) :
    SimilarTM D ∨ ∃ α β : ℝ, TileAngles D α β (Real.pi / 2) ∧ TgtAngles D β β (2 * α) := by
  have hpi := Real.pi_pos
  have hEq : ∀ {x : ℝ}, TgtAngles D x x x → x = Real.pi / 3 → False := by
    intro x hG hx
    apply hne
    intro j
    rw [Graph.tgt_all D hG j, hx]
  rcases classify_total D hn a ha hgcd with h | h | h
  · exact Or.inl h
  · right
    obtain ⟨k, l, hlk, hk, j₁, j₂, hj, h1, h2⟩ := h
    refine ⟨Real.pi - Real.pi / 2 - D.model.angleAt l, D.model.angleAt l, ?_, ?_⟩
    · exact (((tile_of_two D k l hlk.symm (Real.pi / 2) _ hk rfl).swap).swap23).swap
    · exact tgt_congr3 (tgt_of_two D j₁ j₂ hj _ h1 h2) (by ring)
  · right
    rcases h with ⟨hT, hG⟩ | ⟨hT, hG⟩ | ⟨hT, hG⟩
    · exact (hEq (tgt_cast3 hG rfl rfl rfl) (by ring)).elim
    · refine ⟨Real.pi / 3, Real.pi / 6, ?_, ?_⟩
      · exact (hT.cast (by ring) (by ring) (by ring)).swap
      · exact tgt_cast3 hG (by ring) (by ring) (by ring)
    · exact (hEq (tgt_cast3 hG rfl rfl rfl) (by ring)).elim

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.table3_comm_total
