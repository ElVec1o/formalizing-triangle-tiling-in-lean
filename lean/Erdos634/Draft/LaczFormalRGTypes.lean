-- Draft/LaczFormalRGTypes.lean -- S3 of PLAN_THM21: port of LaczFormalGraphTypes to `RegionDissection` (dissection-dependent declarations only; the rest is used
-- from the original module).  UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 4), Beeson, Beeson-Zhang; port of the project's LaczFormalGraphTypes.
import Erdos634.Draft.LaczFormalRGEnds
import Erdos634.Draft.LaczFormalGraphTypes

open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}


/-- The model side opposite the vertex of type `t`. -/
noncomputable def slen (D : CongruentRegionDissection N) (t : Fin 3) : ℝ := dist (D.model.pts (t + 1)) (D.model.pts (t + 2))


theorem exists_idx_len (D : CongruentRegionDissection N) :
    ∃ idx : Fin N → Equiv.Perm (Fin 3), ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') =
      dist (D.model.pts (idx i k)) (D.model.pts (idx i k')) := by
  choose f σ hf using fun i => D.tiles_congruent i
  exact ⟨σ, fun i k k' => by rw [← hf i k, ← hf i k', (f i).dist_eq]⟩


/-- The tile side from `pts k` to `pts (k+1)` has the length of the model side opposite type `idx (k+2)`. -/
theorem side_len_01 (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (i : Fin N) (k : Fin 3) :
    dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = slen D (idx i (k + 2)) := by
  rw [hidx]
  unfold slen
  rcases perm_opp (idx i) k with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, dist_comm]
  · rw [h1, h2, dist_comm]


/-- The tile side from `pts k` to `pts (k+2)` has the length of the model side opposite type `idx (k+1)`. -/
theorem side_len_02 (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (i : Fin N) (k : Fin 3) :
    dist ((D.tile i).pts k) ((D.tile i).pts (k + 2)) = slen D (idx i (k + 1)) := by
  have := side_len_01 D idx hidx i (k + 2)
  rw [fin3_p2p1, fin3_p2p2] at this
  rw [dist_comm]; exact this


/-- **A vertex correspondence matching both all distances and all corner angles.** -/
theorem exists_idx_both (D : CongruentRegionDissection N) :
    ∃ idx : Fin N → Equiv.Perm (Fin 3),
      (∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k'))) ∧
      (∀ i v, TilePlacement.angleAt D.model (idx i v) = TilePlacement.angleAt (D.tile i) v) := by
  choose f σ hf using fun i => D.tiles_congruent i
  refine ⟨σ, fun i k k' => by rw [← hf i k, ← hf i k', (f i).dist_eq], fun i v => ?_⟩
  unfold TilePlacement.angleAt cornerAngle
  have hmap : EuclideanGeometry.angle ((D.tile i).pts (v + 1)) ((D.tile i).pts v) ((D.tile i).pts (v + 2))
      = EuclideanGeometry.angle (D.model.pts (σ i (v + 1))) (D.model.pts (σ i v)) (D.model.pts (σ i (v + 2))) := by
    rw [← hf i (v + 1), ← hf i v, ← hf i (v + 2)]
    have := (f i).toRealAffineIsometryEquiv.toAffineIsometry.angle_map ((D.tile i).pts (v + 1)) ((D.tile i).pts v) ((D.tile i).pts (v + 2))
    simpa using this.symm
  rw [hmap]
  rcases perm_adj (σ i) v with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, EuclideanGeometry.angle_comm]



end Erdos634.Draft.LaczFormal.RG
