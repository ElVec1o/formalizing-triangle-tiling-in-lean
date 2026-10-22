-- Draft/LaczFormal32e2.lean -- Laczkovich DCG 48 (2012) Lemma 3.2 for a CongruentDissection of a TRIANGLE (the form used by the project's dissections):
-- every `CongruentDissection N` of a triangle is a `PolyTiling N 3` (`polyTilingOfTri`), and `lemma32_tri` is `lemma32_tiling` for it.
-- Conclusion: each tile angle is in the Q-span of the three target angles.  NOTE, UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012) Lemma 3.2; DCG 19 (1998) Lemma 10), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormal32e1
import Erdos634.Draft.LaczFormalBZL7d5b

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

/-- A `CongruentDissection` of a triangle, viewed as a tiling of a convex 3-gon. -/
noncomputable def polyTilingOfTri (D : CongruentDissection N) : PolyTiling N 3 where
  C := D.toRegion
  P := (exists_convpoly_of_tri' D.target).choose
  region_eq := by rw [(exists_convpoly_of_tri' D.target).choose_spec.1]; rfl

theorem lemma32_tri (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidxA : ∀ i v, angleAt D.model (idx i v) = angleAt (D.tile i) v) (hirr : IrregularIdx D.toRegion idx) :
    ∀ l : Fin 3, angleAt D.model l ∈ Submodule.span ℚ (Set.range D.target.angleAt) := by
  intro l
  have h := lemma32_tiling (polyTilingOfTri D) idx hidxA hirr l
  refine Submodule.span_mono ?_ h
  obtain ⟨-, τ, hτ, -⟩ := (exists_convpoly_of_tri' D.target).choose_spec
  rintro _ ⟨i, rfl⟩
  exact ⟨τ i, (hτ i).symm⟩

#print axioms lemma32_tri

end Erdos634.Draft.LaczFormal.RG
