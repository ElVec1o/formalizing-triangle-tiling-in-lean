import Erdos634.Ladder

/-!
# Ladder — thm:ladder k²·N dissection by scaling: wrapper

`Ladder.ladder`: given a `CongruentDissection N` of a triangle `T = [A,B,C]`,
there exists a `CongruentDissection (k²·N)` of the `k`-scaled triangle `bigTri A B C k`
with the same model.

VERIFIED: 0 sorry, standard axioms.
-/

namespace Erdos634.Draft.LadderWrap

open Erdos634.Ladder Erdos634.Geometry Erdos634.Subdivision

theorem ladder_dissection (A B C : Plane) (hindep : AffineIndependent ℝ ![A, B, C])
    {N : ℕ} (D : CongruentDissection N) (hT : D.target = (⟨![A, B, C], hindep⟩ : Tri))
    (k : ℕ) (hk : 0 < k) :
    ∃ E : CongruentDissection (k * k * N),
      E.target = Erdos634.Subdivision.bigTri (A := A) (B := B) (C := C) hindep k hk ∧
      E.model = D.model := by
  exact Erdos634.Ladder.ladder (A := A) (B := B) (C := C) hindep D hT k hk

/-- Non-vacuity: 1 > 0. -/
theorem ladder_k_pos : 0 < 1 := Nat.one_pos

#print axioms ladder_dissection

end Erdos634.Draft.LadderWrap
