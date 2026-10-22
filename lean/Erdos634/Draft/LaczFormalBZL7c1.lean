-- Draft/LaczFormalBZL7c1.lean -- Beeson-Zhang (arXiv 2604.01314v1) Sect. 2.2 / Table 2, extended to polygon CORNERS of angle 2*alpha or 2*beta (target (2 alpha, pi/3, 2 beta), Thm 5.3 row).
--   `corner_arith_a`, `corner_arith_b`: c0 alpha + c1 beta + c2 gamma = 2 alpha (resp. 2 beta), alpha not in Q pi  =>  (c0,c1,c2) = (2,0,0) (resp. (0,2,0)).
--   `vertex_type_gen`: like `vertex_type` (LaczFormalBZ2) with the hypothesis "all polygon angles are pi/3" weakened to "pi/3, 2 alpha or 2 beta": at every tiling vertex
--   either the regular types of Table 2, or a polygon vertex with no gamma corner.
-- NOTE, UNAUDITED.  Hypotheses are those of `vertex_type`; the equilateral case (all angles pi/3) is a special case of the new hypothesis.
-- Credit: Beeson-Zhang (arXiv 2604.01314v1, Sect. 2.2, Table 2, Thm 5.3), Laczkovich (DCG 48 (2012), Sect. 7), Beeson.
import Erdos634.Draft.LaczFormalBZ2

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- Irrationality of `α/π` in the form `A α = B π/3` with integer `A, B` forces `A = B = 0`. -/
theorem irr_coeff {α : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (A B : ℤ)
    (h : (A : ℝ) * α = (B : ℝ) * (Real.pi / 3)) : A = 0 ∧ B = 0 := by
  have hpi := Real.pi_pos
  by_cases hA : A = 0
  · subst hA
    refine ⟨rfl, ?_⟩
    have : (B : ℝ) * (Real.pi / 3) = 0 := by rw [← h]; simp
    rcases mul_eq_zero.mp this with h1 | h1
    · exact_mod_cast h1
    · exfalso; linarith
  · exfalso
    apply hα
    have hA' : (A : ℝ) ≠ 0 := by exact_mod_cast hA
    refine ⟨(B : ℚ) / (3 * (A : ℚ)), ?_⟩
    push_cast
    field_simp
    linarith

theorem corner_arith_a {α β γ : ℝ} (hαβ : α + β = Real.pi / 3) (hγ : γ = 2 * Real.pi / 3)
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (c0 c1 c2 : ℕ)
    (h : (c0 : ℝ) * α + c1 * β + c2 * γ = 2 * α) : c0 = 2 ∧ c1 = 0 ∧ c2 = 0 := by
  have hβ : β = Real.pi / 3 - α := by linarith
  subst hγ; subst hβ
  have := irr_coeff hα ((c0 : ℤ) - c1 - 2) (-((c1 : ℤ) + 2 * c2)) (by push_cast; linear_combination h)
  omega

theorem corner_arith_b {α β γ : ℝ} (hαβ : α + β = Real.pi / 3) (hγ : γ = 2 * Real.pi / 3)
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (c0 c1 c2 : ℕ)
    (h : (c0 : ℝ) * α + c1 * β + c2 * γ = 2 * β) : c0 = 0 ∧ c1 = 2 ∧ c2 = 0 := by
  have hβ : β = Real.pi / 3 - α := by linarith
  subst hγ; subst hβ
  have := irr_coeff hα ((c0 : ℤ) - c1 + 2) (2 - (c1 : ℤ) - 2 * c2) (by push_cast; linear_combination h)
  omega

/-- **Table 2 of Beeson-Zhang for a convex polygon whose angles are `π/3`, `2α`, `2β`.** -/
theorem vertex_type_gen (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hγ : D.model.angleAt 2 = 2 * Real.pi / 3) (hαβ : D.model.angleAt 0 + D.model.angleAt 1 = Real.pi / 3)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi)
    (hPang : ∀ i, P.angle i = Real.pi / 3 ∨ P.angle i = 2 * D.model.angleAt 0 ∨ P.angle i = 2 * D.model.angleAt 1) {X : Plane}
    (hvert : ∃ j k, (D.tile j).pts k = X) :
    (cnt D idx X 0 = cnt D idx X 1 ∧
      ((X ∈ interior D.region ∧ cnt D idx X 0 + 2 * cnt D idx X 2 = 6) ∨ cnt D idx X 0 + 2 * cnt D idx X 2 = 3 ∨
        (X ∉ interior D.region ∧ cnt D idx X 0 + 2 * cnt D idx X 2 = 1 ∧ ∃ k : Fin M, X = P.v (k + 1)))) ∨
    (cnt D idx X 2 = 0 ∧ ∃ k : Fin M, X = P.v (k + 1)) := by
  have hAexp : Asum D idx X = (cnt D idx X 0 : ℝ) * D.model.angleAt 0 + (cnt D idx X 1 : ℝ) * D.model.angleAt 1 + (cnt D idx X 2 : ℝ) * D.model.angleAt 2 := by
    unfold Asum; rw [Fin.sum_univ_three]
  have hpi := Real.pi_pos
  have key : ∀ m : ℕ, Asum D idx X = m * (Real.pi / 3) → cnt D idx X 0 = cnt D idx X 1 ∧ cnt D idx X 0 + 2 * cnt D idx X 2 = m := by
    intro m hm
    exact type_arith hαβ hγ hα _ _ _ m (by rw [← hAexp]; exact hm)
  rcases vertex_A D P hreg idx hidxA hvert with ⟨hi, h2 | h1⟩ | ⟨hni, h1 | ⟨k, hXk, hk⟩⟩
  · have := key 6 (by rw [h2]; push_cast; ring)
    exact Or.inl ⟨this.1, Or.inl ⟨hi, this.2⟩⟩
  · have := key 3 (by rw [h1]; push_cast; ring)
    exact Or.inl ⟨this.1, Or.inr (Or.inl this.2)⟩
  · have := key 3 (by rw [h1]; push_cast; ring)
    exact Or.inl ⟨this.1, Or.inr (Or.inl this.2)⟩
  · rcases hPang (k + 1) with hp | hp | hp
    · have := key 1 (by rw [hk, hp]; push_cast; ring)
      exact Or.inl ⟨this.1, Or.inr (Or.inr ⟨hni, this.2, k, hXk⟩)⟩
    · have := corner_arith_a hαβ hγ hα _ _ _ (by rw [← hAexp, hk, hp])
      exact Or.inr ⟨this.2.2, k, hXk⟩
    · have := corner_arith_b hαβ hγ hα _ _ _ (by rw [← hAexp, hk, hp])
      exact Or.inr ⟨this.2.2, k, hXk⟩

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.corner_arith_a
#print axioms Erdos634.Draft.LaczFormal.RG.corner_arith_b
#print axioms Erdos634.Draft.LaczFormal.RG.vertex_type_gen
