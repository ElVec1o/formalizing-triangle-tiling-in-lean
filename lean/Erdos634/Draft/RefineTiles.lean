-- Draft/RefineTiles.lean — refine every tile of a CongruentDissection by the same congruent
-- dissection: if D has N tiles congruent to D.model, and E has M tiles with D.model ≅ E.target,
-- then there is a CongruentDissection (N*M) of D.target with model E.model.
-- (cevian split lemma: E = a 2-tile dissection of D.model.)  UNAUDITED.  NOT in All.lean.
import Erdos634.Compose
import Erdos634.DissectionMap
import Erdos634.Congruence
import Mathlib.Analysis.Normed.Affine.MazurUlam

namespace Erdos634.Draft.RefineTiles
open Erdos634.Geometry Erdos634.DissectionMap

noncomputable def isoAff (h : Plane ≃ᵢ Plane) : Plane ≃ᵃ[ℝ] Plane :=
  h.toRealAffineIsometryEquiv.toAffineEquiv

theorem isoAff_apply (h : Plane ≃ᵢ Plane) (x : Plane) : isoAff h x = h x := by
  simp [isoAff]

theorem refine_congruent {N M : ℕ} (D : CongruentDissection N) (E : CongruentDissection M)
    (hE : D.model.Congruent E.target) :
    ∃ F : CongruentDissection (N * M), F.model = E.model := by
  classical
  have hex : ∀ i : Fin N, ∃ (h : Plane ≃ᵢ Plane) (σ : Equiv.Perm (Fin 3)),
      ∀ k, h ((D.tile i).pts k) = E.target.pts (σ k) := fun i =>
    ((D.tiles_congruent i).trans hE)
  choose h σ hh using hex
  let inner : Fin N → Dissection M := fun i => mapDissection (isoAff (h i).symm) E.toDissection
  have hpts : ∀ i k, isoAff (h i).symm (E.target.pts (σ i k)) = (D.tile i).pts k := by
    intro i k
    rw [isoAff_apply, ← hh i k]; exact (h i).symm_apply_apply _
  have hin : ∀ i, ((inner i).target).carrier = (D.tile i).carrier := by
    intro i
    show (mapTri (isoAff (h i).symm) E.target).carrier = _
    simp only [mapTri, Tri.carrier]
    congr 1
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      obtain ⟨k, rfl⟩ := (σ i).surjective j
      exact ⟨k, (hpts i k).symm⟩
    · rintro ⟨k, rfl⟩
      exact ⟨σ i k, hpts i k⟩
  refine ⟨{ toDissection := Erdos634.Compose.compose D.toDissection inner hin
            model := E.model
            tiles_congruent := fun n => ?_ }, rfl⟩
  rw [Erdos634.Compose.compose_tile]
  refine Tri.Congruent.trans (U := E.tile (finProdFinEquiv.symm n).2) ?_ (E.tiles_congruent _)
  exact ⟨h (finProdFinEquiv.symm n).1, 1, fun k => by simp [inner, mapTri, mapDissection, isoAff_apply]⟩

end Erdos634.Draft.RefineTiles

#print axioms Erdos634.Draft.RefineTiles.refine_congruent
