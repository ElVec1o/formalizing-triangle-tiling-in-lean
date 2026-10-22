-- Draft/LaczFormalGraphTypes.lean -- D0 (part 8): TYPES and LENGTHS.  For a congruent dissection, a vertex correspondence `idx i : Perm (Fin 3)` (tile `i`
-- to the model) matching ALL pairwise distances (hence side lengths) and corner angles.  With it:
--   * the length of the tile side from the corner `pts k` to `pts (k+1)` is `slen (idx (k+2))`, the model side opposite the vertex of type `idx (k+2)`;
--   * for the real fan, `nsq (p s) = (slen (tW code))^2`, `nsq (q s) = (slen (tU code))^2` (code = `codeOf`): "the side along the previous (next)
--     ray joins the types `t, u` (`t, w`) and is opposite `w` (`u`)", the convention of `LaczFormalRegFan`.
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 4: sides a, b, c opposite alpha, beta, gamma).
import Erdos634.Draft.LaczFormalGraphCodes

open Erdos634.Geometry

namespace Erdos634.Draft.LaczFormal.Graph

variable {N : ℕ}

/-- The model side opposite the vertex of type `t`. -/
noncomputable def slen (D : CongruentDissection N) (t : Fin 3) : ℝ := dist (D.model.pts (t + 1)) (D.model.pts (t + 2))

theorem exists_idx_len (D : CongruentDissection N) :
    ∃ idx : Fin N → Equiv.Perm (Fin 3), ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') =
      dist (D.model.pts (idx i k)) (D.model.pts (idx i k')) := by
  choose f σ hf using fun i => D.tiles_congruent i
  exact ⟨σ, fun i k k' => by rw [← hf i k, ← hf i k', (f i).dist_eq]⟩

theorem perm_opp (σ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (σ (k + 2) + 1 = σ k ∧ σ (k + 2) + 2 = σ (k + 1)) ∨ (σ (k + 2) + 1 = σ (k + 1) ∧ σ (k + 2) + 2 = σ k) := by
  revert σ k; decide

theorem fin3_p2p1 (k : Fin 3) : k + 2 + 1 = k := by revert k; decide
theorem fin3_p2p2 (k : Fin 3) : k + 2 + 2 = k + 1 := by revert k; decide

/-- The tile side from `pts k` to `pts (k+1)` has the length of the model side opposite type `idx (k+2)`. -/
theorem side_len_01 (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (i : Fin N) (k : Fin 3) :
    dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = slen D (idx i (k + 2)) := by
  rw [hidx]
  unfold slen
  rcases perm_opp (idx i) k with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, dist_comm]
  · rw [h1, h2, dist_comm]

/-- The tile side from `pts k` to `pts (k+2)` has the length of the model side opposite type `idx (k+1)`. -/
theorem side_len_02 (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (i : Fin N) (k : Fin 3) :
    dist ((D.tile i).pts k) ((D.tile i).pts (k + 2)) = slen D (idx i (k + 1)) := by
  have := side_len_01 D idx hidx i (k + 2)
  rw [fin3_p2p1, fin3_p2p2] at this
  rw [dist_comm]; exact this

theorem nsq_toV2_sub (x y : Plane) : nsq (toV2 (x - y)) = dist x y ^ 2 := by
  rw [nsq_toV2, ← dist_eq_norm]

theorem perm_adj (σ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (σ (k + 1) = σ k + 1 ∧ σ (k + 2) = σ k + 2) ∨ (σ (k + 1) = σ k + 2 ∧ σ (k + 2) = σ k + 1) := by
  revert σ k; decide

/-- **A vertex correspondence matching both all distances and all corner angles.** -/
theorem exists_idx_both (D : CongruentDissection N) :
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

end Erdos634.Draft.LaczFormal.Graph
