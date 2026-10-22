import Erdos634.Draft.ZhangRat8Tri
import Erdos634.Draft.LaczFormalBZL7h17
import Erdos634.Draft.ZhangThm1Full

/-!
# Witness for `ZhangRat8Tri.beeson_thm107_tri` (closes note M2 "no witness")

The certified 1125-tiling (`G3GControl.D`; Herdt / Beeson Fig. 23): an isosceles TRIANGLE target with side lengths `(2400, 2400, 3600)` (angles `alpha, alpha, pi - 2 alpha`,
`cos alpha = 3/4`, alpha irrational) tiled by the tile `(64, 80, 96)` (angles `alpha, pi - 3 alpha, 2 alpha` after relabelling the model).  After `relabelModel sigma`
every hypothesis of `beeson_thm107_tri` holds, so the row "(a,a,pi-2a) / gamma = 2a" of Zhang Table 1 is NOT vacuous.
NOTE, UNAUDITED.  Credit: Herdt and Zhang (the 1125-tiling), Beeson (arXiv 1206.1974v7, Thm 10.7), Beeson-Zhang, Laczkovich.
-/

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional

namespace Erdos634.Draft.ZhangRat10Wit107
open Erdos634.Draft.LaczFormal.RG Erdos634.Geometry.Row14AnyLabel

set_option maxHeartbeats 3200000 in
theorem beeson_thm107_tri_wit : ∃ (N : ℕ) (D : CongruentDissection N),
    D.model.angleAt 1 = Real.pi - 3 * D.model.angleAt 0 ∧ D.model.angleAt 2 = 2 * D.model.angleAt 0 ∧
    (¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi) ∧
    TgtAngles D (D.model.angleAt 0) (D.model.angleAt 0) (Real.pi - 2 * D.model.angleAt 0) ∧
    ∃ r s : ℚ, slen D.toRegion 0 = (r : ℝ) * slen D.toRegion 1 ∧ slen D.toRegion 2 = (s : ℝ) * slen D.toRegion 0 := by
  open Erdos634.Draft.G3GControl in
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := data
  open Erdos634.Draft.G3GControl in
  set D' := D.relabelModel σ with hD'
  have hM : ∀ k, D'.model.pts k = D.model.pts (σ k) := fun k => rfl
  open Erdos634.Draft.G3GControl in
  have a0 : D'.model.angleAt 0 = α := by rw [angleAt_of_pts σ hM]; exact h0
  open Erdos634.Draft.G3GControl in
  have a1 : D'.model.angleAt 1 = Real.pi - 3 * D'.model.angleAt 0 := by
    rw [a0, angleAt_of_pts σ hM]; exact h1
  open Erdos634.Draft.G3GControl in
  have a2 : D'.model.angleAt 2 = 2 * D'.model.angleAt 0 := by
    rw [a0, angleAt_of_pts σ hM]; exact h2
  open Erdos634.Draft.G3GControl in
  have hα : ¬ ∃ r : ℚ, D'.model.angleAt 0 = (r : ℝ) * Real.pi := by rw [a0]; exact α_irr
  open Erdos634.Draft.G3GControl in
  have hT : TgtAngles D' (D'.model.angleAt 0) (D'.model.angleAt 0) (Real.pi - 2 * D'.model.angleAt 0) := by
    have hsum := Erdos634.Draft.LaczFormal.angleAt_sum D.target
    refine ⟨Equiv.refl _, ?_, ?_, ?_⟩
    · show D.target.angleAt 0 = _
      rw [a0]; exact t_ang0
    · show D.target.angleAt 1 = _
      rw [a0]; exact t_ang1
    · show D.target.angleAt 2 = _
      rw [a0]; linarith [t_ang0, t_ang1, hsum]
  exact ⟨_, D', a1, a2, hα, hT, ZhangRat8Tri.beeson_thm107_tri D' a1 a2 hα hT⟩

end Erdos634.Draft.ZhangRat10Wit107
#print axioms Erdos634.Draft.ZhangRat10Wit107.beeson_thm107_tri_wit
