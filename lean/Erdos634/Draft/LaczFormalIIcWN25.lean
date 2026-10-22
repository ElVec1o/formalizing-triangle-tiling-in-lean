-- Draft/LaczFormalIIcWN25.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2/6.3, Lemma 6.2 (`IIcNoKites`), step (c) `u = v + N`:
-- NON-VACUITY witness and axiom check for `exterior_angle_sum` / `interior_angle_sum` (WN24): the triangle 0, 1, I satisfies every hypothesis
-- (SimplePoly, injective, 3 <= n), and the conclusion is the nontrivial `sum of 3 interior angles = pi`.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2/6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN24
import Erdos634.Draft.LaczFormalIIcWN12

open scoped Classical Fin.NatCast
open Complex

namespace Erdos634.Draft.LaczFormal.WN

theorem interior_angle_sum_witness :
    SimplePoly tri ∧ Function.Injective tri ∧ 3 ≤ 3 ∧
    ∃ ρ : ℝ, (ρ = 1 ∨ ρ = -1) ∧
      (∀ k : Fin 3, 0 < Real.pi - ρ * extAng tri k ∧ Real.pi - ρ * extAng tri k < 2 * Real.pi) ∧
      ∑ k : Fin 3, (Real.pi - ρ * extAng tri k) = Real.pi := by
  refine ⟨tri_simple, tri_injective, le_rfl, ?_⟩
  obtain ⟨ρ, h1, h2, h3⟩ := interior_angle_sum tri_simple tri_injective (le_refl 3)
  refine ⟨ρ, h1, h2, ?_⟩
  rw [h3]; norm_num

#print axioms exterior_angle_sum
#print axioms interior_angle_sum
#print axioms hopf_core
#print axioms interior_angle_sum_witness

end Erdos634.Draft.LaczFormal.WN
