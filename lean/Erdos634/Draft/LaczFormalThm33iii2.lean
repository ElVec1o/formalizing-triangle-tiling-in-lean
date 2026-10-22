-- Draft/LaczFormalThm33iii2.lean -- Laczkovich DCG 48 (2012) Thm 3.3, clause (iii), module 2 of 3.
--   `type_arith_pi3`     : c0 a + c1 b + c2 (pi/3) = m (pi/3), a + b = 2pi/3, a not in Q pi  =>  c0 = c1;
--   `regular_of_irr_pi3` : PolyTiling of an equilateral triangle (all polygon angles pi/3), gamma = pi/3, alpha not in Q pi  =>  RegularPQ
--                          (analogue of BZ8.regular_of_irr for the gamma = 2pi/3 tile; no Lemma 3.2 needed);
--   `polyTilingOf`       : a CongruentDissection of an equilateral triangle, relabelled by sigma, as a PolyTiling.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson-Zhang (Table 2 pattern), Beeson.
import Erdos634.Draft.LaczFormalThm33iii1

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

theorem type_arith_pi3 {α β γ : ℝ} (hαβ : α + β = 2 * Real.pi / 3) (hγ : γ = Real.pi / 3)
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (c0 c1 c2 m : ℕ)
    (h : (c0 : ℝ) * α + c1 * β + c2 * γ = m * (Real.pi / 3)) : c0 = c1 := by
  have hpi := Real.pi_pos
  have hβ : β = 2 * Real.pi / 3 - α := by linarith
  subst hγ
  subst hβ
  have e : ((c0 : ℝ) - c1) * α = ((m : ℝ) - 2 * c1 - c2) * (Real.pi / 3) := by linear_combination h
  by_contra hne
  apply hα
  have hd : ((c0 : ℝ) - c1) ≠ 0 := by
    intro h0
    apply hne
    have : (c0 : ℝ) = c1 := by linarith
    exact_mod_cast this
  refine ⟨((m : ℚ) - 2 * c1 - c2) / (3 * ((c0 : ℚ) - c1)), ?_⟩
  push_cast
  field_simp
  linarith

theorem regular_of_irr_pi3 (T : PolyTiling N 3) (hγ : angleAt T.C.model 2 = Real.pi / 3)
    (hα : ¬ ∃ r : ℚ, angleAt T.C.model 0 = (r : ℝ) * Real.pi) (hPang : ∀ i, T.P.angle i = Real.pi / 3) : RegularPQ T.C := by
  classical
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  obtain ⟨idx, hidx, hidxA⟩ := exists_idx_both T.C
  refine ⟨idx, hidxA, fun X => ?_⟩
  have hαβ : T.C.model.angleAt 0 + T.C.model.angleAt 1 = 2 * Real.pi / 3 := by
    have := Erdos634.Draft.LaczFormal.angleAt_sum T.C.model
    have hγ' : T.C.model.angleAt 2 = Real.pi / 3 := hγ
    linarith
  have hγ' : T.C.model.angleAt 2 = Real.pi / 3 := hγ
  have hα' : ¬ ∃ r : ℚ, T.C.model.angleAt 0 = (r : ℝ) * Real.pi := hα
  by_cases hvert : ∃ j k, (T.C.tile j).pts k = X
  · have hAexp : Asum T.C idx X = (cnt T.C idx X 0 : ℝ) * T.C.model.angleAt 0 + (cnt T.C idx X 1 : ℝ) * T.C.model.angleAt 1 +
        (cnt T.C idx X 2 : ℝ) * T.C.model.angleAt 2 := by
      unfold Asum; rw [Fin.sum_univ_three]
    have key : ∀ m : ℕ, Asum T.C idx X = m * (Real.pi / 3) → cnt T.C idx X 0 = cnt T.C idx X 1 := by
      intro m hm
      exact type_arith_pi3 hαβ hγ' hα' _ _ _ m (by rw [← hAexp]; exact hm)
    rcases vertex_A T.C T.P T.region_eq idx hidxA hvert with ⟨hi, h2 | h1⟩ | ⟨hni, h1 | ⟨k, hXk, hk⟩⟩
    · exact key 6 (by rw [h2]; push_cast; ring)
    · exact key 3 (by rw [h1]; push_cast; ring)
    · exact key 3 (by rw [h1]; push_cast; ring)
    · exact key 1 (by rw [hk, hPang]; push_cast; ring)
  · show cnt T.C idx X 0 = cnt T.C idx X 1
    rw [cnt_zero_of_not_vertex' T.C idx hvert 0, cnt_zero_of_not_vertex' T.C idx hvert 1]

/-- A congruent dissection of an equilateral triangle as a `PolyTiling`, the model relabelled by `σ`. -/
noncomputable def polyTilingOf (D : CongruentDissection N) (σ : Equiv.Perm (Fin 3))
    (heq : ∀ j : Fin 3, dist (D.target.pts j) (D.target.pts (j + 1)) = dist (D.target.pts 0) (D.target.pts 1)) : PolyTiling N 3 :=
  have hP := Classical.choose_spec (exists_convpoly_of_equilateral D.target heq)
  { C := relabel D.toRegion σ
    P := Classical.choose (exists_convpoly_of_equilateral D.target heq)
    region_eq := by rw [hP.1]; rfl }

theorem polyTilingOf_angles (D : CongruentDissection N) (σ : Equiv.Perm (Fin 3))
    (heq : ∀ j : Fin 3, dist (D.target.pts j) (D.target.pts (j + 1)) = dist (D.target.pts 0) (D.target.pts 1)) :
    (∀ j, angleAt (polyTilingOf D σ heq).C.model j = D.model.angleAt (σ j)) ∧ (∀ i, (polyTilingOf D σ heq).P.angle i = Real.pi / 3) := by
  have hP := Classical.choose_spec (exists_convpoly_of_equilateral D.target heq)
  refine ⟨fun j => ?_, hP.2⟩
  show angleAt (relabel D.toRegion σ).model j = _
  rw [relabel_angleAt]; rfl

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.regular_of_irr_pi3
#print axioms Erdos634.Draft.LaczFormal.RG.polyTilingOf_angles
