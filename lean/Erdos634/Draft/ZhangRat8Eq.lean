import Erdos634.Draft.LaczFormalThm33iii3
import Erdos634.Draft.FluxCRow5
import Erdos634.Draft.LaczFormalBZL7a

/-!
# Zhang (arXiv 2512.22696v4) Theorem 1, row "equilateral target, tile with an angle `pi/3`" (Laczkovich [4], Lemma 3.2 / Thm 3.3)

Statement as printed: an equilateral triangle tiled by congruent triangles with angles `(alpha, 2pi/3 - alpha, pi/3)`,
`alpha` not a rational multiple of `pi`, forces the tile's sides to be pairwise commensurable.  Proved from
`sincomm_irr_family` (Laczkovich Thm 3.3 (iii), unconditional) and the law of sines (`comm_sides_of_sinComm`).
Witness: `G3CSixtyControl.lemmaP_premises_satisfied` (certified dissection by the tile `3360 (5,8,7)`).
NOTE, UNAUDITED.  Credit: Zhang (arXiv 2512.22696v4, Thm 1), Beeson-Zhang, Laczkovich (DCG 48 (2012), Thm 3.3; Discrete Math 140 (1995)).
-/

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement
open Erdos634.Draft.TheoremPConditional

namespace Erdos634.Draft.ZhangRat8Eq
open Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

theorem zhang_thm1_equilateral_pi3 (D : CongruentDissection N) (hEq : Equilateral D) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.SixtyData α a b c) :
    Comm a b ∧ Comm a c := by
  obtain ⟨σ, h0, ha, h1, hb, h2, hc⟩ := h
  have hs := sincomm_irr_family D hEq hα (Or.inl rfl) ⟨σ, h0, h1, h2⟩
  -- sines of the model angles at 0,1,2 pairwise commensurable
  have key : ∀ x y : Fin 3, Comm (Real.sin (D.model.angleAt (σ x))) (Real.sin (D.model.angleAt (σ y))) := by
    obtain ⟨s01, s12, s02⟩ := hs
    intro x y
    have t01 := Erdos634.Draft.LaczFormal.RG.comm_symm' s01
    have t12 := Erdos634.Draft.LaczFormal.RG.comm_symm' s12
    have t02 := Erdos634.Draft.LaczFormal.RG.comm_symm' s02
    fin_cases x <;> fin_cases y <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, h0, h1, h2]
    all_goals first
      | assumption
      | exact Erdos634.Draft.LaczFormal.RG.comm_refl' _
  have sc : ∀ i j : Fin 3, Comm (Real.sin (D.model.angleAt i)) (Real.sin (D.model.angleAt j)) := by
    intro i j
    have := key (σ.symm i) (σ.symm j)
    simpa using this
  have hSC : SinComm D.toRegion := ⟨sc 0 1, sc 1 2, sc 0 2⟩
  obtain ⟨c01, c02⟩ := comm_sides_of_sinComm D.toRegion hSC
  have c12 := Erdos634.Draft.LaczFormal.RG.comm_trans' (Erdos634.Draft.LaczFormal.RG.comm_symm' c01) c02
  have sl : ∀ i j : Fin 3, Comm (slen D.toRegion i) (slen D.toRegion j) := by
    intro i j
    have c10 := Erdos634.Draft.LaczFormal.RG.comm_symm' c01
    have c20 := Erdos634.Draft.LaczFormal.RG.comm_symm' c02
    have c21 := Erdos634.Draft.LaczFormal.RG.comm_symm' c12
    fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    all_goals first
      | assumption
      | exact Erdos634.Draft.LaczFormal.RG.comm_refl' _
  have ea : a = slen D.toRegion (σ 0) := ha.symm
  have eb : b = slen D.toRegion (σ 1) := hb.symm
  have ec : c = slen D.toRegion (σ 2) := hc.symm
  exact ⟨by rw [ea, eb]; exact sl _ _, by rw [ea, ec]; exact sl _ _⟩

end Erdos634.Draft.ZhangRat8Eq

#print axioms Erdos634.Draft.ZhangRat8Eq.zhang_thm1_equilateral_pi3
