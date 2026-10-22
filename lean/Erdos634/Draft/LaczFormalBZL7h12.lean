-- Draft/LaczFormalBZL7h12.lean -- Beeson (arXiv 1206.1974v7) Lemmas 10.5/10.6: `g5c_of_corner`, the hypothesis G5c of `Thm107Open` PROVED from the existence of a polygon corner of angle alpha.
-- NOTE, UNAUDITED.  Credit: Beeson (arXiv 1206.1974v7, Lemmas 10.5, 10.6), Laczkovich (DCG 48 (2012), Sect. 4), Herdt, Zhang, Beeson-Zhang.
import Erdos634.Draft.LaczFormalBZL7h11

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- **G5c.**  `NotComb c a b` and a polygon corner of angle `alpha` give a boundary vertex with an outgoing `Gamma_c` edge. -/
theorem g5c_of_corner (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hβ : D.model.angleAt 1 = Real.pi - 3 * D.model.angleAt 0) (hγ : D.model.angleAt 2 = 2 * D.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi)
    (hPang : ∀ k : Fin M, P.angle (k + 1) = D.model.angleAt 0 ∨ P.angle (k + 1) = Real.pi - 2 * D.model.angleAt 0)
    (hnc : NotComb (slen D 2) (slen D 0) (slen D 1)) (kA : Fin M) (hkA : P.angle (kA + 1) = D.model.angleAt 0) :
    ∃ Q, Q ∉ interior D.region ∧ ∃ H, GaEdge D.toRegionDissection (slen D 2) Q H := by
  classical
  have hne12 : slen D 2 ≠ slen D 1 := by intro e; exact hnc 1 0 1 one_pos (by simp [e])
  obtain ⟨Lm, Wm⟩ := side_walk_exists_poly D.toRegionDissection P hreg (kA + 1)
  obtain ⟨Lk, Wk⟩ := side_walk_exists_poly D.toRegionDissection P hreg kA
  obtain ⟨em, hem, hemno⟩ := side_has_c_step D P hreg idx hidxA hβ hγ hα hPang (kA + 1) Wm
  obtain ⟨ek, hek, hekno⟩ := side_has_c_step D P hreg idx hidxA hβ hγ hα hPang kA Wk
  have hcm : dist em.2.1 em.2.2 = slen D 2 := cstep_dist D idx hidx (walkT_mem_step Wm em hem) hemno
  have hck : dist ek.2.1 ek.2.2 = slen D 2 := cstep_dist D idx hidx (walkT_mem_step Wk ek hek) hekno
  obtain ⟨e1, L', hLe, he1, hS1⟩ := walkT_head_h10 Wm (walk_ne_nil D.toRegionDissection P (kA + 1) Wm)
  obtain ⟨i2, U2, hmem2, hS2⟩ := walkT_last Wk (walk_ne_nil D.toRegionDissection P kA Wk)
  have hS1' : TriStep (D.tile e1.1) (toV2 (P.e (kA + 1))) (P.v (kA + 1)) e1.2.2 := by rw [← he1]; exact hS1
  by_cases hfirst : dist (P.v (kA + 1)) e1.2.2 = slen D 2
  · have hlast : dist U2 (P.v (kA + 1)) ≠ slen D 2 := fun h => corner_not_both_c D P hreg idx hidx hidxA hβ hγ hα hne12 kA hkA hS1' hS2 ⟨hfirst, h⟩
    exact g5_of_steps D P hreg idx hidx hidxA hβ hγ hα hnc kA Wk ⟨ek, hek, hck⟩ ⟨(i2, U2, P.v (kA + 1)), hmem2, hlast⟩
  · have hn : dist e1.2.1 e1.2.2 ≠ slen D 2 := by rw [he1]; exact hfirst
    exact g5_of_steps D P hreg idx hidx hidxA hβ hγ hα hnc (kA + 1) Wm ⟨em, hem, hcm⟩ ⟨e1, by rw [hLe]; exact List.mem_cons_self .., hn⟩

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.g5c_of_corner
