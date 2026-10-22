/-
Draft/CompositeFinal10.lean — γ = 2α closed for SQUAREFREE N (`G2AFinal.Row4.not_squarefree`, any-label form `caseG_of_squarefree`),
hence `GammaTwoAlphaClosed N` at N = 39, 51, 87, and the final chains:
  N = 35, 55 :  hypothesis-free (as `CompositeFinal9`).
  N = 39, 51 :  `chain_N_final'` has NO residual hypothesis.
  N = 87     :  residual `E60Pair 87 29 9` only.
*** UNAUDITED.  Formalization debt, NOT /goal progress. ***  `Row4.not_squarefree` is conditional at the geometric level as
`Row4.not_prime` (no Lean witness tiling of the base-α target).  No sorry, no native_decide.
-/
import Erdos634.Draft.G2AFinal

open scoped Classical

namespace Erdos634.Draft.CompositeFinal10

open Erdos634.Geometry Erdos634.Draft.ChainComposite Erdos634.Draft.CompositeFinal6 Erdos634.Draft.CompositeFinal9
open Erdos634.Draft.CompositeE5Gen

private theorem cA3 (p q r : Plane) : cornerAngle p q r = cornerAngle r q p :=
  EuclideanGeometry.angle_comm (V := Plane) p q r

/-- **`γ = 2α` for squarefree `N`, any-label form** (`CaseGClosed N`). -/
theorem caseG_of_squarefree (N : ℕ) (hsq : Squarefree N) : CaseGClosed N := by
  intro D α a b c hα h i j hij hi hj
  have key : ∀ σ : Equiv.Perm (Fin 3),
      (D.relabelTarget' σ).target.angleAt 0 = α → (D.relabelTarget' σ).target.angleAt 1 = α → False :=
    fun σ h0 h1 => Row4.not_squarefree (D.relabelTarget' σ) hα h h0 h1 hsq
  have p01 : D.target.angleAt 0 = α → D.target.angleAt 1 = α → False := fun h0 h1 =>
    key 1 (by simpa [CongruentDissection.relabelTarget', Erdos634.NormalPosition.relabelTri,
        Tri.angleAt] using h0)
      (by simpa [CongruentDissection.relabelTarget', Erdos634.NormalPosition.relabelTri,
        Tri.angleAt] using h1)
  have p02 : D.target.angleAt 0 = α → D.target.angleAt 2 = α → False := fun h0 h2 =>
    key (Equiv.swap 1 2)
      (by
        have := h0; simp only [Tri.angleAt] at this ⊢
        simp [CongruentDissection.relabelTarget', Erdos634.NormalPosition.relabelTri,
          Equiv.swap_apply_of_ne_of_ne] at this ⊢
        rw [cA3]; simpa using this)
      (by
        have := h2; simp only [Tri.angleAt] at this ⊢
        simp [CongruentDissection.relabelTarget', Erdos634.NormalPosition.relabelTri,
          Equiv.swap_apply_of_ne_of_ne] at this ⊢
        rw [cA3]; simpa using this)
  have p12 : D.target.angleAt 1 = α → D.target.angleAt 2 = α → False := fun h1 h2 =>
    key (Equiv.swap 0 2)
      (by
        have := h2; simp only [Tri.angleAt] at this ⊢
        simp [CongruentDissection.relabelTarget', Erdos634.NormalPosition.relabelTri,
          Equiv.swap_apply_of_ne_of_ne] at this ⊢
        rw [cA3]; simpa using this)
      (by
        have := h1; simp only [Tri.angleAt] at this ⊢
        simp [CongruentDissection.relabelTarget', Erdos634.NormalPosition.relabelTri,
          Equiv.swap_apply_of_ne_of_ne] at this ⊢
        rw [cA3]; simpa using this)
  fin_cases i <;> fin_cases j <;> simp at hij
  all_goals first
    | exact p01 hi hj | exact p01 hj hi | exact p02 hi hj | exact p02 hj hi
    | exact p12 hi hj | exact p12 hj hi

theorem gamma_39 : GammaTwoAlphaClosed 39 := caseG_of_squarefree 39 sqfree_39
theorem gamma_51 : GammaTwoAlphaClosed 51 := caseG_of_squarefree 51 sqfree_51
theorem gamma_87 : GammaTwoAlphaClosed 87 := caseG_of_squarefree 87 sqfree_87

/-- **N = 39: no residual hypothesis.** -/
theorem chain_39_final' (D : CongruentDissection 39) : False := chain_39_final gamma_39 D
/-- **N = 51: no residual hypothesis.** -/
theorem chain_51_final' (D : CongruentDissection 51) : False := chain_51_final gamma_51 D
/-- **N = 87, modulo `E60Pair 87 29 9` only.** -/
theorem chain_87_final' (gx : E60Pair 87 29 9) (D : CongruentDissection 87) : False :=
  chain_87_final gamma_87 gx D

end Erdos634.Draft.CompositeFinal10

#print axioms Erdos634.Draft.CompositeFinal10.caseG_of_squarefree
#print axioms Erdos634.Draft.CompositeFinal10.chain_39_final'
#print axioms Erdos634.Draft.CompositeFinal10.chain_51_final'
#print axioms Erdos634.Draft.CompositeFinal10.chain_87_final'
