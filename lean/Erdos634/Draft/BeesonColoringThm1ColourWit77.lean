import Erdos634.Draft.BeesonColoringThm1Colour
import Erdos634.Draft.BeesonColoringWitness77

/-!
# Witness for `Beeson.thm1_colouring`: Beeson's 77-tiling, blacks minus whites `= 5 = M`

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Fig. 15, Lemma 12, Thm 1), Beeson-Zhang, Laczkovich.
The 77-tiling of `(2 alpha, alpha, 2 beta)` by the tile `(2,3,4)` (`W77.exists_D77`, the same construction repeated with
the target side lengths exported: `X_0, X_1, X_2 = 28, 16, 33`).  All hypotheses of `thm1_colouring` hold (H1 is
`alpha44_irr`); the equation reads `M * 9 = 28 - 16 + 33 = 45`, so `M = 5` is the number of black tiles minus the
number of white tiles of a proper 2-colouring.  NOT witnessed: an explicit adjacent pair of tiles of this tiling (the
tiles are hidden behind the existential of `beeson_t14_2_3_4`); the definition `Dissection.Adj` is therefore not
shown non-vacuous on this tiling here.
-/

open scoped Classical

namespace Erdos634.BeesonColoring.W77

open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.ZhangSporadic
  Erdos634.BeesonT14.I_2_3_4 Erdos634.Draft.FluxGridWitness

theorem exists_D77' : ∃ D : CongruentDissection 77,
    D.model.ThreeAlphaData α44 β44 2 3 4 ∧ D.target.angleAt 0 = 2 * α44 ∧
      D.target.angleAt 1 = α44 ∧ D.target.angleAt 2 = 2 * β44 ∧
      D.target.oppLen 0 = 28 ∧ D.target.oppLen 1 = 16 ∧ D.target.oppLen 2 = 33 := by
  obtain ⟨C, hreg, hm⟩ := beeson_t14_2_3_4
  set D0 : CongruentDissection 77 :=
    C.toCongruentDissection TP (hreg.trans (TriSet_eq_carrier hdetP)) with hD0
  have hmod : D0.model = T0 := hm
  have hTt : D0.target = TP := rfl
  set D := D0.relabelTarget' swp with hD
  have hT : ∀ k, D.target.pts k = D0.target.pts (swp k) := fun k => rfl
  have o0 : D.target.oppLen 0 = 28 := by
    unfold Tri.oppLen
    simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl]
    rw [hT 1, hT 2, swp1, swp2, hTt, dist_comm]; exact t_d12
  have o1 : D.target.oppLen 1 = 16 := by
    unfold Tri.oppLen
    simp only [show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl]
    rw [hT 2, hT 0, swp2, swp0, hTt, dist_comm]; exact t_d01
  have o2 : D.target.oppLen 2 = 33 := by
    unfold Tri.oppLen
    simp only [show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
    rw [hT 0, hT 1, swp0, swp1, hTt]; exact t_d02
  refine ⟨D, ?_, ?_, ?_, ?_, o0, o1, o2⟩
  · show D0.model.ThreeAlphaData α44 β44 2 3 4
    rw [hmod]; exact data77
  · rw [Row14AnyLabel.angleAt_of_pts swp hT, swp0, hTt]; exact t_angle0
  · rw [Row14AnyLabel.angleAt_of_pts swp hT, swp1, hTt]; exact t_angle2
  · rw [Row14AnyLabel.angleAt_of_pts swp hT, swp2, hTt]; exact t_angle1

/-- **Blacks minus whites of the 77-tiling is 5.** -/
theorem colouring_at_77 : ∃ D : CongruentDissection 77, ∃ ε : Fin 77 → ℤ,
    D.toDissection.ProperColouring ε ∧
      ((Finset.univ.filter fun i => ε i = 1).card : ℤ)
        - ((Finset.univ.filter fun i => ε i = -1).card : ℤ) = 5 := by
  obtain ⟨D, h, e0, e1, e2, o0, o1, o2⟩ := exists_D77'
  obtain ⟨-, -, -, h4, -⟩ := thm1_colouring D α44_irr three_α_two_β h
  obtain ⟨ε, hε, M, hM, hMpos, hMeq⟩ := h4 ⟨e0, e1, e2⟩
  refine ⟨D, ε, hε, ?_⟩
  rw [← hM]
  rw [o0, o1, o2] at hMeq
  norm_num at hMeq
  have h5 : (M : ℝ) = 5 := by linarith
  exact_mod_cast h5

end Erdos634.BeesonColoring.W77

#print axioms Erdos634.BeesonColoring.W77.colouring_at_77
