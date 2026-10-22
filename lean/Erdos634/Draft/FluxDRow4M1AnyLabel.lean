-- Draft/FluxDRow4M1AnyLabel.lean — any-label version of `Row4.not_M1` (γ=2α, `M1Div N` in place of primality).
-- UNAUDITED.  Room ALLN campaign.
import Erdos634.Draft.FluxDRow4M1
import Erdos634.Draft.FluxDRow4AnyLabel

open scoped Classical

namespace Erdos634.Geometry

private theorem cA' (p q r : Plane) : cornerAngle p q r = cornerAngle r q p :=
  EuclideanGeometry.angle_comm (V := Plane) p q r

theorem Row4.not_M1_any_label {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    {i j : Fin 3} (hij : i ≠ j) (hi : D.target.angleAt i = α) (hj : D.target.angleAt j = α) :
    ¬ M1Div N := by
  have key : ∀ σ : Equiv.Perm (Fin 3),
      (D.relabelTarget' σ).target.angleAt 0 = α → (D.relabelTarget' σ).target.angleAt 1 = α →
      ¬ M1Div N := fun σ h0 h1 => Row4.not_M1 (D.relabelTarget' σ) hα h h0 h1
  -- the three unordered positions of the α-pair
  have p01 : D.target.angleAt 0 = α → D.target.angleAt 1 = α → ¬ M1Div N := fun h0 h1 =>
    key 1 (by simpa [CongruentDissection.relabelTarget', Erdos634.NormalPosition.relabelTri,
        Tri.angleAt] using h0)
      (by simpa [CongruentDissection.relabelTarget', Erdos634.NormalPosition.relabelTri,
        Tri.angleAt] using h1)
  have p02 : D.target.angleAt 0 = α → D.target.angleAt 2 = α → ¬ M1Div N := fun h0 h2 =>
    key (Equiv.swap 1 2)
      (by
        have := h0; simp only [Tri.angleAt] at this ⊢
        simp [CongruentDissection.relabelTarget', Erdos634.NormalPosition.relabelTri,
          Equiv.swap_apply_of_ne_of_ne] at this ⊢
        rw [cA']; simpa using this)
      (by
        have := h2; simp only [Tri.angleAt] at this ⊢
        simp [CongruentDissection.relabelTarget', Erdos634.NormalPosition.relabelTri,
          Equiv.swap_apply_of_ne_of_ne] at this ⊢
        rw [cA']; simpa using this)
  have p12 : D.target.angleAt 1 = α → D.target.angleAt 2 = α → ¬ M1Div N := fun h1 h2 =>
    key (Equiv.swap 0 2)
      (by
        have := h2; simp only [Tri.angleAt] at this ⊢
        simp [CongruentDissection.relabelTarget', Erdos634.NormalPosition.relabelTri,
          Equiv.swap_apply_of_ne_of_ne] at this ⊢
        rw [cA']; simpa using this)
      (by
        have := h1; simp only [Tri.angleAt] at this ⊢
        simp [CongruentDissection.relabelTarget', Erdos634.NormalPosition.relabelTri,
          Equiv.swap_apply_of_ne_of_ne] at this ⊢
        rw [cA']; simpa using this)
  fin_cases i <;> fin_cases j <;> simp at hij
  all_goals first
    | exact p01 hi hj | exact p01 hj hi | exact p02 hi hj | exact p02 hj hi
    | exact p12 hi hj | exact p12 hj hi

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row4.not_M1_any_label
