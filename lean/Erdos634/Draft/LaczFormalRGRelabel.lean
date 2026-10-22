-- Draft/LaczFormalRGRelabel.lean -- S5 of PLAN_THM21: RELABELING the model of a congruent region dissection by a permutation of its vertices.  Used to transfer the `Gamma_a` results to `Gamma_b`
-- (swap 0 1) and `Gamma_c` (swap 0 2): Laczkovich's "the same argument applies if b is not a linear combination ..." and Sects. 4.4-4.5.
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sects. 4, 9: Gamma_c defined "the same way as Gamma_a, replacing a by c"), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRGCaseV2

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

/-- The model with its vertices permuted by `σ`. -/
noncomputable def Tri.relabel (M : Tri) (σ : Equiv.Perm (Fin 3)) : Tri where
  pts := fun k => M.pts (σ k)
  indep := M.indep.comp_embedding σ.toEmbedding

/-- **Relabel the model of a congruent dissection.** -/
noncomputable def relabel (D : CongruentRegionDissection N) (σ : Equiv.Perm (Fin 3)) : CongruentRegionDissection N where
  toRegionDissection := D.toRegionDissection
  model := Tri.relabel D.model σ
  tiles_congruent := by
    intro i
    obtain ⟨f, τ, hf⟩ := D.tiles_congruent i
    exact ⟨f, τ.trans σ.symm, fun k => by
      show f ((D.tile i).pts k) = D.model.pts (σ (σ.symm (τ k)))
      rw [Equiv.apply_symm_apply]; exact hf k⟩

theorem relabel_tile (D : CongruentRegionDissection N) (σ : Equiv.Perm (Fin 3)) (i : Fin N) : (relabel D σ).tile i = D.tile i := rfl

theorem relabel_region (D : CongruentRegionDissection N) (σ : Equiv.Perm (Fin 3)) : (relabel D σ).region = D.region := rfl

theorem relabel_model_pts (D : CongruentRegionDissection N) (σ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (relabel D σ).model.pts k = D.model.pts (σ k) := rfl

theorem relabel_slen (D : CongruentRegionDissection N) (σ : Equiv.Perm (Fin 3)) (t : Fin 3) :
    slen (relabel D σ) t = slen D (σ t) := by
  unfold slen
  show dist (D.model.pts (σ (t + 1))) (D.model.pts (σ (t + 2))) = dist (D.model.pts (σ t + 1)) (D.model.pts (σ t + 2))
  rcases perm_adj σ t with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, dist_comm]

theorem relabel_angleAt (D : CongruentRegionDissection N) (σ : Equiv.Perm (Fin 3)) (j : Fin 3) :
    angleAt (relabel D σ).model j = angleAt D.model (σ j) := by
  unfold angleAt cornerAngle
  show EuclideanGeometry.angle (D.model.pts (σ (j + 1))) (D.model.pts (σ j)) (D.model.pts (σ (j + 2))) = _
  rcases perm_adj σ j with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, EuclideanGeometry.angle_comm]

/-- The vertex correspondence for the relabeled dissection. -/
def relabelIdx (idx : Fin N → Equiv.Perm (Fin 3)) (σ : Equiv.Perm (Fin 3)) : Fin N → Equiv.Perm (Fin 3) :=
  fun i => (idx i).trans σ.symm

theorem relabelIdx_apply (idx : Fin N → Equiv.Perm (Fin 3)) (σ : Equiv.Perm (Fin 3)) (i : Fin N) (k : Fin 3) :
    relabelIdx idx σ i k = σ.symm (idx i k) := rfl

theorem relabel_cnt (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (σ : Equiv.Perm (Fin 3)) (X : Plane) (l : Fin 3) :
    cnt (relabel D σ) (relabelIdx idx σ) X l = cnt D idx X (σ l) := by
  unfold cnt
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, relabel_tile, relabelIdx_apply]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [← h2]; simp⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h2]; simp⟩

theorem relabel_hidx (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (σ : Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k'))) :
    ∀ i k k', dist (((relabel D σ).tile i).pts k) (((relabel D σ).tile i).pts k') =
      dist ((relabel D σ).model.pts (relabelIdx idx σ i k)) ((relabel D σ).model.pts (relabelIdx idx σ i k')) := by
  intro i k k'
  rw [relabel_model_pts, relabel_model_pts, relabelIdx_apply, relabelIdx_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact hidx i k k'

theorem relabel_hidxA (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (σ : Equiv.Perm (Fin 3))
    (hA : ∀ i v, angleAt D.model (idx i v) = angleAt (D.tile i) v) :
    ∀ i v, angleAt (relabel D σ).model (relabelIdx idx σ i v) = angleAt ((relabel D σ).tile i) v := by
  intro i v
  rw [relabel_angleAt, relabelIdx_apply, Equiv.apply_symm_apply]
  exact hA i v

end Erdos634.Draft.LaczFormal.RG
