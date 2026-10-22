-- Draft/RegionTiling.lean — tilings of arbitrary closed regions by congruent triangles, with union
-- and transport.  The collar induction (thm:realize12) glues non-triangular pieces (parallelogram
-- columns), which `Dissection` (triangle targets only) cannot express.  Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.Draft.RWGlue

open scoped Classical
open Erdos634.Geometry

namespace Erdos634.Draft.RegionTiling

/-- A tiling of the region `S` by `N` triangles congruent to the model `M`. -/
structure RTiling (S : Set Plane) (M : Tri) (N : ℕ) where
  tile : Fin N → Tri
  covers : (⋃ i, (tile i).carrier) = S
  disj : Pairwise fun i j => Disjoint (interior (tile i).carrier) (interior (tile j).carrier)
  cong : ∀ i, (tile i).Congruent M

/-- A `CongruentDissection` is a tiling of its target's carrier. -/
def ofCD {N : ℕ} (D : CongruentDissection N) : RTiling D.target.carrier D.model N where
  tile := D.tile
  covers := D.covers
  disj := D.interiors_disjoint
  cong := D.tiles_congruent

/-- A tiling of a triangle's carrier is a `CongruentDissection`. -/
def toCD {N : ℕ} {T M : Tri} (R : RTiling T.carrier M N) : CongruentDissection N where
  target := T
  tile := R.tile
  covers := R.covers
  interiors_disjoint := R.disj
  model := M
  tiles_congruent := R.cong

/-- Region tilings of regions with disjoint interiors union. -/
noncomputable def union {S₁ S₂ : Set Plane} {M : Tri} {N₁ N₂ : ℕ}
    (R₁ : RTiling S₁ M N₁) (R₂ : RTiling S₂ M N₂)
    (hd : Disjoint (interior S₁) (interior S₂)) : RTiling (S₁ ∪ S₂) M (N₁ + N₂) where
  tile := Fin.append R₁.tile R₂.tile
  covers := by
    have h1 : ∀ x, x ∈ S₁ ↔ ∃ i, x ∈ (R₁.tile i).carrier := fun x => by
      have := Set.ext_iff.mp R₁.covers x
      simp only [Set.mem_iUnion] at this; exact this.symm
    have h2 : ∀ x, x ∈ S₂ ↔ ∃ i, x ∈ (R₂.tile i).carrier := fun x => by
      have := Set.ext_iff.mp R₂.covers x
      simp only [Set.mem_iUnion] at this; exact this.symm
    ext x
    simp only [Set.mem_iUnion, Set.mem_union, h1, h2]
    constructor
    · rintro ⟨i, hi⟩
      induction i using Fin.addCases with
      | left j => left; exact ⟨j, by rwa [Fin.append_left] at hi⟩
      | right j => right; exact ⟨j, by rwa [Fin.append_right] at hi⟩
    · rintro (⟨j, hj⟩ | ⟨j, hj⟩)
      · exact ⟨Fin.castAdd N₂ j, by rwa [Fin.append_left]⟩
      · exact ⟨Fin.natAdd N₁ j, by rwa [Fin.append_right]⟩
  disj := by
    have sub1 : ∀ i, interior (R₁.tile i).carrier ⊆ interior S₁ := fun i =>
      interior_mono (fun x hx => (Set.ext_iff.mp R₁.covers x).mp (Set.mem_iUnion.mpr ⟨i, hx⟩))
    have sub2 : ∀ i, interior (R₂.tile i).carrier ⊆ interior S₂ := fun i =>
      interior_mono (fun x hx => (Set.ext_iff.mp R₂.covers x).mp (Set.mem_iUnion.mpr ⟨i, hx⟩))
    intro i j hij
    induction i using Fin.addCases with
    | left i' =>
      induction j using Fin.addCases with
      | left j' =>
        simp only [Fin.append_left]
        exact R₁.disj (by simpa using hij)
      | right j' =>
        simp only [Fin.append_left, Fin.append_right]
        exact hd.mono (sub1 i') (sub2 j')
    | right i' =>
      induction j using Fin.addCases with
      | left j' =>
        simp only [Fin.append_left, Fin.append_right]
        exact (hd.mono (sub1 j') (sub2 i')).symm
      | right j' =>
        simp only [Fin.append_right]
        exact R₂.disj (by simpa using hij)
  cong := by
    intro i
    induction i using Fin.addCases with
    | left i' => simp only [Fin.append_left]; exact R₁.cong i'
    | right i' => simp only [Fin.append_right]; exact R₂.cong i'

/-- Transport by an isometry: the image region is tiled by images of the tiles. -/
noncomputable def map {S : Set Plane} {M : Tri} {N : ℕ} (R : RTiling S M N)
    (g : Plane ≃ᵢ Plane) : RTiling (g '' S) M N where
  tile := fun i => Erdos634.DissectionMap.mapTri (Erdos634.Ladder.isoAff g) (R.tile i)
  covers := by
    simp only [Erdos634.DissectionMap.mapTri_carrier, Erdos634.Ladder.isoAff_coe]
    rw [← Set.image_iUnion, R.covers]
  disj := by
    intro i j hij
    exact Erdos634.DissectionMap.mapTri_interiors_disjoint (Erdos634.Ladder.isoAff g) (R.disj hij)
  cong := fun i => ((Erdos634.Ladder.congruent_mapTri g (R.tile i)).symm).trans (R.cong i)

/-- Re-model by a congruent tile. -/
def remodel {S : Set Plane} {M M' : Tri} {N : ℕ} (R : RTiling S M N) (h : M.Congruent M') :
    RTiling S M' N :=
  { R with cong := fun i => (R.cong i).trans h }

end Erdos634.Draft.RegionTiling
