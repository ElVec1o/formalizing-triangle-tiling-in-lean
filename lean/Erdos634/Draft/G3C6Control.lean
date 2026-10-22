-- Draft/G3C6Control.lean — G3C6 (UNAUDITED). No sorry/native_decide. Formalization debt, not /goal progress.
-- PCP node C6 (Theorem R4, gamma = 2 alpha): LITERAL application of `Row4.not_prime_any_label` to the REAL certified
-- 1125-tiling (isosceles (150,150,225)*16 by tile (4,5,6)*16) `G3GControl.D`.  The theorem has NO primality hypothesis
-- (its conclusion is `¬ N.Prime`), so every premise (IrrPi alpha, TwoAlphaData, i ≠ j, both target angles = alpha) is met.
import Erdos634.Draft.G3GControl
import Erdos634.Draft.FluxDRow4AnyLabel

open scoped Classical

namespace Erdos634.Draft.G3C6Control

open Erdos634.Geometry Erdos634.Draft.G3GControl

/-- the literal theorem, joint premises met on the real tiling; conclusion `¬ Prime` on the tiling's tile count -/
theorem row4_literal : ¬ (Erdos634.Draft.G3GTiling1125.cert.leaves.length).Prime :=
  Row4.not_prime_any_label D α_irr data (i := 0) (j := 1) (by decide) t_ang0 t_ang1

theorem row4_1125 : ¬ Nat.Prime 1125 := by
  have h := row4_literal
  rwa [Erdos634.Draft.G3GTiling1125.cert_len] at h

/-- all four premise groups jointly (including both orders / another pair is not claimed) plus tile count 1125 -/
theorem joint_premises :
    (¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) ∧ D.model.TwoAlphaData α 64 80 96 ∧ (0 : Fin 3) ≠ 1 ∧
      D.target.angleAt 0 = α ∧ D.target.angleAt 1 = α ∧ Erdos634.Draft.G3GTiling1125.cert.leaves.length = 1125 :=
  ⟨α_irr, data, by decide, t_ang0, t_ang1, Erdos634.Draft.G3GTiling1125.cert_len⟩

/-- the same pair swapped (any-label content): distinct pair (1,0) also works -/
theorem row4_swapped : ¬ (Erdos634.Draft.G3GTiling1125.cert.leaves.length).Prime :=
  Row4.not_prime_any_label D α_irr data (i := 1) (j := 0) (by decide) t_ang1 t_ang0

end Erdos634.Draft.G3C6Control

#print axioms Erdos634.Draft.G3C6Control.row4_literal
#print axioms Erdos634.Draft.G3C6Control.row4_1125
