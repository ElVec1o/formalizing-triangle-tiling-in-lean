-- Draft/LaczFormalBZ9.lean -- Laczkovich's Theorem 2.1, Case III (gamma = 2 pi/3), TRIANGLE targets, COMPLETE: every regular tiling of a triangle by a tile with gamma = 2 pi/3 satisfies a conclusion of Theorem 2.1.
--   alpha not in Q pi : `caseIII_tri_irr` (Beeson-Zhang Thm 5.2: conclusion (iv));
--   alpha in Q pi     : the equilateral classification (LaczFormalL56Final.equilateral_classification, any N, reflections allowed) forces the tile (pi/6, pi/6, 2 pi/3): conclusion (viii).
-- UNAUDITED.  Credit: Beeson-Zhang (arXiv 2604.01314v1), Laczkovich (DCG 48 (2012), Thm 2.1, Thm 3.3).
import Erdos634.Draft.LaczFormalBZ8
import Erdos634.Draft.LaczFormalL56Final

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

theorem triDissection_angle (T : PolyTiling N 3) (i : Fin 3) : (triDissection T).target.angleAt i = T.P.angle i := by
  unfold Tri.angleAt ConvPoly.angle cornerAngle
  have e : i - 1 = i + 2 := by fin_cases i <;> decide
  rw [e, EuclideanGeometry.angle_comm]
  have hp : ∀ j : Fin 3, (triDissection T).target.pts j = T.P.v j := by intro j; fin_cases j <;> rfl
  rw [hp, hp, hp]

/-- **Theorem 2.1, Case III (`γ = 2π/3`), triangle targets: the conclusion holds** (no hypothesis on `α`, beyond regularity and `γ = 2π/3`). -/
theorem caseIII_tri_all (T : PolyTiling N 3) (hreg : RegularPQ T.C) (hγ : angleAt T.C.model 2 = 2 * Real.pi / 3) : Thm21Concl T.C T.P := by
  classical
  by_cases hα : ∃ r : ℚ, angleAt T.C.model 0 = (r : ℝ) * Real.pi
  · -- rational `α`: the equilateral classification
    obtain ⟨idx, hA, hcnt⟩ := hreg
    have hall := tri_corners T hγ idx hA hcnt
    have hEq : Equilateral (triDissection T) := fun k => by rw [triDissection_angle]; exact hall.1 k
    have hαβ : T.C.model.angleAt 0 + T.C.model.angleAt 1 = Real.pi / 3 := by
      have := Erdos634.Draft.LaczFormal.angleAt_sum T.C.model
      have hγ' : T.C.model.angleAt 2 = 2 * Real.pi / 3 := hγ
      linarith
    have hγ' : T.C.model.angleAt 2 = 2 * Real.pi / 3 := hγ
    have hpi := Real.pi_pos
    have hpos0 := Erdos634.MarchFlank.cornerAngle_pos T.C.model 0
    have hpos1 := Erdos634.MarchFlank.cornerAngle_pos T.C.model 1
    have hpos0' : 0 < T.C.model.angleAt 0 := hpos0
    have hpos1' : 0 < T.C.model.angleAt 1 := hpos1
    have hrat : ∀ k : Fin 3, ¬ IrrPi ((triDissection T).model.angleAt k) := by
      intro k hk
      obtain ⟨r, hr⟩ := hα
      have hr' : T.C.model.angleAt 0 = (r : ℝ) * Real.pi := hr
      fin_cases k
      · exact hk ⟨r, hr'⟩
      · exact hk ⟨1 / 3 - r, by
          show T.C.model.angleAt 1 = _
          push_cast; linarith⟩
      · exact hk ⟨2 / 3, by
          show T.C.model.angleAt 2 = _
          push_cast; linarith⟩
    rcases Erdos634.Draft.LaczFormal.equilateral_classification (triDissection T) hEq with ⟨x, hx, σ, h0, -⟩ | ⟨x, hx, σ, h0, -⟩ | ⟨σ, h0, h1, h2⟩ | ⟨σ, h0, h1, h2⟩ | ⟨σ, h0, h1, h2⟩
    · exact absurd hx (by rw [← h0]; exact hrat _)
    · exact absurd hx (by rw [← h0]; exact hrat _)
    · exfalso
      -- the model has all angles π/3 (every vertex is some σ j); but angle 2 = 2π/3
      have hall3 : ∀ k : Fin 3, T.C.model.angleAt k = Real.pi / 3 := by
        intro k
        obtain ⟨j, rfl⟩ := σ.surjective k
        fin_cases j
        · exact h0
        · exact h1
        · exact h2
      have := hall3 2
      linarith
    · -- the tile `(π/6, π/6, 2π/3)`
      have hv : ∀ k : Fin 3, T.C.model.angleAt k = Real.pi / 6 ∨ T.C.model.angleAt k = 2 * Real.pi / 3 := by
        intro k
        obtain ⟨j, rfl⟩ := σ.surjective k
        fin_cases j
        · exact Or.inl h0
        · exact Or.inl h1
        · exact Or.inr h2
      have h0' : T.C.model.angleAt 0 = Real.pi / 6 := by
        rcases hv 0 with h | h
        · exact h
        · exfalso; linarith
      have h1' : T.C.model.angleAt 1 = Real.pi / 6 := by linarith
      have hC8 : Concl8 T.C T.P := by
        refine ⟨?_, by norm_num, fun i => Or.inl (hall.1 i), h0', h1', hγ'⟩
        intro i j
        have hs := triangle_equilateral T.P hall.1
        unfold ConvPoly.side at hs
        exact ⟨1, 1, one_pos, one_pos, by simp [ConvPoly.side]; rw [hs i, hs j]⟩
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hC8)))))))
    · exfalso
      have hv : ∀ k : Fin 3, T.C.model.angleAt k = Real.pi / 6 ∨ T.C.model.angleAt k = Real.pi / 3 ∨ T.C.model.angleAt k = Real.pi / 2 := by
        intro k
        obtain ⟨j, rfl⟩ := σ.surjective k
        fin_cases j
        · exact Or.inl h0
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr h2)
      rcases hv 2 with h | h | h <;> linarith
  · exact caseIII_tri_irr T hreg hγ hα

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.caseIII_tri_all
