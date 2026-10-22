-- Draft/RWGlue.lean — gluing two `CongruentDissection`s along a cevian cut (prop:cevianatom /
-- Lemma G of the R-W and R-A proofs).  Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.Draft.CutGen
import Erdos634.UnionDissection
import Erdos634.Ladder
import Erdos634.CongruentArea

open scoped Classical
open Erdos634.Geometry Erdos634.Draft.CutGen

namespace Erdos634.Draft.RWGlue

/-- Transport a `CongruentDissection` to any congruent target. -/
theorem transport_cd {N : ℕ} (D : CongruentDissection N) (U : Tri) (h : D.target.Congruent U) :
    ∃ D' : CongruentDissection N, D'.target.carrier = U.carrier ∧ D'.model = D.model := by
  obtain ⟨f, σ, hf⟩ := h
  refine ⟨{ Erdos634.DissectionMap.mapDissection (Erdos634.Ladder.isoAff f) D.toDissection with
    model := D.model
    tiles_congruent := fun i => ?_ }, ?_, rfl⟩
  · show Tri.Congruent (Erdos634.DissectionMap.mapTri (Erdos634.Ladder.isoAff f) (D.tile i)) D.model
    exact (Erdos634.Ladder.congruent_mapTri f (D.tile i)).symm.trans (D.tiles_congruent i)
  · show (Erdos634.DissectionMap.mapTri (Erdos634.Ladder.isoAff f) D.target).carrier = U.carrier
    rw [Erdos634.DissectionMap.mapTri_carrier, Erdos634.Ladder.isoAff_coe]
    exact Erdos634.CongruentArea.image_carrier_of_congruent hf

/-- Replace the model by a congruent one. -/
noncomputable def remodel {N : ℕ} (D : CongruentDissection N) (M : Tri) (h : D.model.Congruent M) :
    CongruentDissection N :=
  { D with model := M, tiles_congruent := fun i => (D.tiles_congruent i).trans h }

/-- **Gluing along a cevian cut.**  Two dissections by tiles of congruent models, of triangles
congruent to the two pieces `T1 = (A,B,P)`, `T2 = (A,P,C)` of `T = (A,B,C)`, glue to a
dissection of `T` itself, with `N₁ + N₂` tiles and the model of the first. -/
theorem glue_two {N₁ N₂ : ℕ} (T T1 T2 : Tri) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (h1 : T1.pts 0 = T.pts 0) (h2 : T1.pts 1 = T.pts 1)
    (h3 : T1.pts 2 = AffineMap.lineMap (T.pts 1) (T.pts 2) t)
    (g1 : T2.pts 0 = T.pts 0) (g2 : T2.pts 1 = AffineMap.lineMap (T.pts 1) (T.pts 2) t)
    (g3 : T2.pts 2 = T.pts 2)
    (D1 : CongruentDissection N₁) (D2 : CongruentDissection N₂)
    (hm : D2.model.Congruent D1.model)
    (hD1 : D1.target.Congruent T1) (hD2 : D2.target.Congruent T2) :
    ∃ D : CongruentDissection (N₁ + N₂), D.target = T ∧ D.model = D1.model := by
  obtain ⟨D1', hc1, hm1⟩ := transport_cd D1 T1 hD1
  obtain ⟨D2', hc2, hm2⟩ := transport_cd D2 T2 hD2
  have hm2' : D2'.model.Congruent D1'.model := by rw [hm1, hm2]; exact hm
  set D2'' := remodel D2' D1'.model hm2' with hD2''
  have hcut := cut_carrier T T1 T2 t ht0 ht1 h1 h2 h3 g1 g2 g3
  have hc2'' : D2''.target.carrier = T2.carrier := hc2
  have hcov : D1'.target.carrier ∪ D2''.target.carrier = T.carrier := by
    rw [hc1, hc2'']; exact hcut.1
  have hdisj : Disjoint (interior D1'.target.carrier) (interior D2''.target.carrier) := by
    rw [hc1, hc2'']; exact hcut.2
  refine ⟨unionCongruentDissection T D1' D2'' rfl hcov hdisj, rfl, ?_⟩
  show D1'.model = D1.model
  exact hm1

end Erdos634.Draft.RWGlue

#print axioms Erdos634.Draft.RWGlue.glue_two
