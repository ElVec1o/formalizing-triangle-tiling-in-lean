-- Draft/BeesonCol4L40.lean -- Beeson (arXiv 1206.2229 v4) Lemma 40, the passage "We will rule out (6, 0, 1): then there would be 7 tiles with an edge on AB, and at least six
--   'in-betweens' with a vertex on the boundary, making 13 tiles touching AB, plus four on AC, with no double-counting at vertex A ..., At C there is an alpha+beta angle,
--   hence at least one more tile, making 18."  Applied to the edge-level layer of BeesonCol4Walk/Side/Count.
-- WHAT IS PROVED: (1) `bdyGe3_of_3a2b`: for the tile (alpha, beta, 2 alpha + beta), 3 alpha + 2 beta = pi, every boundary non-corner vertex carries >= 3 tile corners;
--   (2) `l40_601_AB_touching`: a 17-tiling whose side AB is divided into 7 tile edges has >= 13 tiles touching AB (the printed "7 + at least six in-betweens");
--   (3) `l40_601_contradiction`: the printed count 13 + 4 + 1 = 18 > 17, CONDITIONAL on the two named steps NOT derived here:
--   GAP A (quoted): "with no double-counting at vertex A as the tiles touching the two tiles at A are white and black, and so not identical"  (hypothesis `hdisj`);
--   GAP B (quoted): "At C there is an alpha + beta angle, hence at least one more tile"  (hypothesis `hC`: a tile touching neither AB nor having an edge on AC).
--   Neither hypothesis can be witnessed (they are the negation of the lemma's conclusion in the (6,0,1) case); the theorem is a conditional skeleton, NOT a proof of Lemma 40.
-- NOTE, UNAUDITED.  Credit: Beeson (arXiv 1206.2229 v4, Lemma 40), Beeson-Rosu, Laczkovich, Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.
import Erdos634.Draft.BeesonCol4Count

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {M : ℕ} [NeZero M]

/-- Beeson's tile with `3 alpha + 2 beta = pi` (angles `alpha, beta, 2 alpha + beta`, `alpha, beta > 0`): boundary non-corner vertices carry >= 3 corners. -/
theorem bdyGe3_of_3a2b {N : ℕ} (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (ha : 0 < D.model.angleAt 0) (hb : 0 < D.model.angleAt 1) (hc : D.model.angleAt 2 = 2 * D.model.angleAt 0 + D.model.angleAt 1)
    (h : 3 * D.model.angleAt 0 + 2 * D.model.angleAt 1 = Real.pi) : BdyGe3 D P := by
  obtain ⟨hlt, hpair⟩ := pairs_of_3a2b ha hb hc h (fun x => D.model.angleAt x) rfl rfl rfl
  exact bdyGe3_of_pairs D P hreg idx hidxA hlt hpair

/-- The printed count on AB: a side divided into 7 tile edges is touched by at least 13 tiles (7 step tiles and at least 6 in-betweens). -/
theorem l40_601_AB_touching {N : ℕ} (D : CongruentRegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier) (h3 : BdyGe3 D P) (i : Fin M)
    {L : List (Fin N × Plane × Plane)} (W : WalkT D.toRegionDissection (toV2 (P.e i)) (P.v i) (P.v (i + 1)) L) (h7 : L.length = 7) :
    13 ≤ (Finset.univ.filter (fun q : Fin N => (∃ e ∈ L, e.1 = q) ∨
        ∃ e ∈ L, e.2.1 ≠ P.v i ∧ ∃ k, (D.tile q).pts k = e.2.1)).card :=
  seven_edges_thirteen_tiles D P hreg h3 i W h7

/-- **Skeleton of the Lemma 40 count (CONDITIONAL; see GAP A, GAP B in the header).**  A 17-tiling of the polygon `P`: side `iAB` is divided into 7 tile edges, side `iAC` into 4;
the tiles touching `iAB` (>= 13) and the 4 tiles with an edge on `iAC` are disjoint (GAP A), and some further tile touches neither (GAP B).  Then 13 + 4 + 1 = 18 > 17. -/
theorem l40_601_contradiction (D : CongruentRegionDissection 17) (P : ConvPoly M) (hreg : D.region = P.carrier) (h3 : BdyGe3 D P) (iAB iAC : Fin M)
    {LAB LAC : List (Fin 17 × Plane × Plane)}
    (WAB : WalkT D.toRegionDissection (toV2 (P.e iAB)) (P.v iAB) (P.v (iAB + 1)) LAB) (h7 : LAB.length = 7)
    (WAC : WalkT D.toRegionDissection (toV2 (P.e iAC)) (P.v iAC) (P.v (iAC + 1)) LAC) (h4 : LAC.length = 4)
    (hdisj : Disjoint
      (Finset.univ.filter (fun q : Fin 17 => (∃ e ∈ LAB, e.1 = q) ∨ ∃ e ∈ LAB, e.2.1 ≠ P.v iAB ∧ ∃ k, (D.tile q).pts k = e.2.1))
      (LAC.map fun e => e.1).toFinset)
    (hC : ∃ q : Fin 17, q ∉ (Finset.univ.filter (fun q : Fin 17 => (∃ e ∈ LAB, e.1 = q) ∨ ∃ e ∈ LAB, e.2.1 ≠ P.v iAB ∧ ∃ k, (D.tile q).pts k = e.2.1)) ∧
      q ∉ (LAC.map fun e => e.1).toFinset) : False := by
  set T := Finset.univ.filter (fun q : Fin 17 => (∃ e ∈ LAB, e.1 = q) ∨ ∃ e ∈ LAB, e.2.1 ≠ P.v iAB ∧ ∃ k, (D.tile q).pts k = e.2.1) with hT
  set E := (LAC.map fun e => e.1).toFinset with hE
  have h13 : 13 ≤ T.card := l40_601_AB_touching D P hreg h3 iAB WAB h7
  have hEc : E.card = 4 := by
    rw [hE, List.toFinset_card_of_nodup (walk_tiles_nodup WAC), List.length_map, h4]
  obtain ⟨q, hqT, hqE⟩ := hC
  have hU : (insert q (T ∪ E)).card = T.card + E.card + 1 := by
    rw [Finset.card_insert_of_notMem, Finset.card_union_of_disjoint hdisj]
    simp [hqT, hqE]
  have hle : (insert q (T ∪ E)).card ≤ 17 := by
    have := Finset.card_le_univ (insert q (T ∪ E))
    simpa using this
  omega

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.bdyGe3_of_3a2b
#print axioms Erdos634.Draft.LaczFormal.RG.l40_601_contradiction
