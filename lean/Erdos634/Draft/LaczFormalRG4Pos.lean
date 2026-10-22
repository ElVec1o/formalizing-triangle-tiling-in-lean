-- Draft/LaczFormalRG4Pos.lean -- Case IV: the position of a tiling vertex in a dissection of a convex polygon: interior, interior point of an edge, or a vertex of the polygon.
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 4), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG4Arith

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem poly_c_continuous (P : ConvPoly M) (i : Fin M) : Continuous (fun x : Plane => P.c i x) := by
  unfold ConvPoly.c cross2
  fun_prop

/-- A point of the polygon at which all edge functions are positive is an interior point. -/
theorem interior_of_c_pos (P : ConvPoly M) {X : Plane} (h : ∀ i, 0 < P.c i X) : X ∈ interior P.carrier := by
  rw [mem_interior]
  refine ⟨{x | ∀ i, 0 < P.c i x}, fun x hx i => (hx i).le, ?_, h⟩
  have : {x : Plane | ∀ i, 0 < P.c i x} = ⋂ i, {x : Plane | 0 < P.c i x} := by ext x; simp
  rw [this]
  exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (poly_c_continuous P i))

/-- **Position of a tiling vertex.** -/
theorem point_cases (D : RegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier) {X : Plane}
    (hvert : ∃ j k, (D.tile j).pts k = X) :
    X ∈ interior D.region ∨ (∃ (i : Fin M) (t : ℝ), 0 < t ∧ t < 1 ∧ X = (1 - t) • P.v i + t • P.v (i + 1)) ∨
      (∃ k : Fin M, X = P.v (k + 1)) := by
  classical
  have hXP : X ∈ P.carrier := by
    obtain ⟨j, k, hjk⟩ := hvert
    rw [← hreg, ← D.covers]
    exact Set.mem_iUnion.mpr ⟨j, hjk ▸ subset_convexHull ℝ _ ⟨k, rfl⟩⟩
  by_cases hall : ∀ i, 0 < P.c i X
  · left; rw [hreg]; exact interior_of_c_pos P hall
  · right
    push Not at hall
    obtain ⟨i, hi⟩ := hall
    have h0 : P.c i X = 0 := le_antisymm hi (hXP i)
    have hline : crs (toV2 (P.e i)) (toV2 (X - P.v i)) = 0 := h0
    obtain ⟨t, ht, hXt⟩ := vertex_on_edge D P hreg i hvert hline
    rcases ht.1.eq_or_lt with h0t | h0t
    · right
      refine ⟨i - 1, ?_⟩
      rw [(ConvPoly.fin_facts P.three_le i).2.2.2.2.1, hXt, ← h0t]; simp
    · rcases ht.2.eq_or_lt with h1t | h1t
      · right
        refine ⟨i, ?_⟩
        rw [hXt, h1t]; simp
      · left; exact ⟨i, t, h0t, h1t, hXt⟩

end Erdos634.Draft.LaczFormal.RG
