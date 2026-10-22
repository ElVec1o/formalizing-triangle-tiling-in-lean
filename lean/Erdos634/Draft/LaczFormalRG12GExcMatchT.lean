-- Draft/LaczFormalRG12GExcMatchT.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2, blueprint L10 (A.2) CORRECTED for exceptional points inside a tile side: the matching of `LaczFormalRG12GExcMatch` WITHOUT `hStrn`.
-- With `S = 2 * sum_E |Strn E|` (twice the number of straight tiles at exceptional points; `S = 0` iff no exceptional point lies inside a tile side), the exact matching M1-M3 degrades to the inequality
--     sum_{Y in KB} (1 - indeg Y) + sum_{X not in PV u KB} outdeg X <= S,
-- i.e. at most `S` vertices of `KB` receive no edge and at most `S` edges start outside the polygon corners and `KB` (together).  Also `indeg Y <= 1` on `KB` and the capacity `indeg E + cnt alpha <= cnt gamma + 2 |Strn E|` at exceptional points.
-- By hand (NOT formalised): a straight tile at E forces Asum E = pi, so cnt gamma = N/2, and |Strn E| = 1, so at most two such points, S <= 4 (the capacity constant 2 is not sharp: the true gain is 1 per such point).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12GExcMatch
import Erdos634.Draft.LaczFormalRG12GExcCapT3

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

set_option maxHeartbeats 12800000 in
/-- **L10 corrected: the matching inequality for Gamma_except (no `hStrn`).** -/
theorem gexc_matching_T [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0)
    :
    (∀ Y ∈ kiteB D idx, ((vtxSet D.toRegionDissection).filter (fun X => GExc D idx X Y)).card ≤ 1) ∧
    (∀ E ∈ excVerts2 D idx P, ((vtxSet D.toRegionDissection).filter (fun X => GExc D idx X E)).card + cnt D idx E 0 ≤
        cnt D idx E 2 + 2 * (Strn D.toRegionDissection E).card) ∧
    (∑ Y ∈ kiteB D idx, (1 - ((vtxSet D.toRegionDissection).filter (fun X => GExc D idx X Y)).card) +
        ∑ X ∈ vtxSet D.toRegionDissection \ (polyVerts P ∪ kiteB D idx), ((vtxSet D.toRegionDissection).filter (fun Y => GExc D idx X Y)).card ≤
      2 * ∑ E ∈ excVerts2 D idx P, (Strn D.toRegionDissection E).card) := by
  classical
  set V := vtxSet D.toRegionDissection with hV
  set KB := kiteB D idx with hKB
  set Ex := excVerts2 D idx P with hEx
  set PV := polyVerts P with hPV
  set out : Plane → ℕ := fun X => (V.filter (fun Y => GExc D idx X Y)).card with hout
  set ind : Plane → ℕ := fun Y => (V.filter (fun X => GExc D idx X Y)).card with hind
  have hcomm : ∑ X ∈ V, out X = ∑ Y ∈ V, ind Y :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := V) (t := V) (GExc D idx)
  -- containments and disjointness
  have hKBV : KB ⊆ V := fun Y hY => (Finset.mem_filter.mp hY).1
  have hExV : Ex ⊆ V := fun Y hY => (Finset.mem_sdiff.mp (Finset.mem_filter.mp hY).1).1
  have hPVV : PV ⊆ V := by
    intro X hX
    obtain ⟨k, rfl⟩ := mem_polyVerts.mp hX
    exact mem_vtxSet.mpr (poly_vertex_is_tile_vertex D.toRegionDissection P hreg (k + 1))
  have hKBEx : Disjoint KB Ex := by
    rw [Finset.disjoint_left]
    intro Y hK hE
    have := kiteB_counts D P hreg idx hC h1 h3 hK
    simp only [hEx, excVerts2, Finset.mem_filter] at hE
    omega
  have hPVKB : Disjoint PV KB := by
    rw [Finset.disjoint_left]
    intro Y hP hK
    have := kiteB_counts D P hreg idx hC h1 h3 hK
    obtain ⟨k, rfl⟩ := mem_polyVerts.mp hP
    have := (hcor (k + 1)).2.2
    omega
  -- indegrees
  have hind0 : ∀ Y ∈ V, Y ∉ KB ∪ Ex → ind Y = 0 := by
    intro Y hY hn
    simp only [hind, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro X hX hE
    rcases gexc_end_cls D P hreg idx hC hab hac h1 h3 G hcor hE with h | h
    · exact hn (Finset.mem_union_left _ h)
    · exact hn (Finset.mem_union_right _ h)
  have hindKB : ∀ Y ∈ KB, ind Y ≤ 1 := by
    intro Y hY
    obtain ⟨Z, hYZ⟩ := (Finset.mem_filter.mp hY).2.1
    simp only [hind]
    apply Finset.card_le_one.mpr
    intro X hX X' hX'
    exact gexc_arrive_kite_unique D P hreg idx hC h1 h3 G hYZ (Finset.mem_filter.mp hX).2 (Finset.mem_filter.mp hX').2
  have hindEx : ∀ E ∈ Ex, ind E ≤ (cnt D idx E 2 - cnt D idx E 0) + 2 * (Strn D.toRegionDissection E).card := by
    intro E hE
    have h2 : ind E + cnt D idx E 0 ≤ cnt D idx E 2 + 2 * (Strn D.toRegionDissection E).card := exc_capacity_T D P hreg idx hC h1 h3 hE
    omega
  have hcensus : ∑ E ∈ Ex, (cnt D idx E 2 - cnt D idx E 0) = M := exc_census D P hreg idx hC h1 h3 hcor
  have hsumind : ∑ Y ∈ V, ind Y = ∑ Y ∈ KB, ind Y + ∑ Y ∈ Ex, ind Y := by
    rw [← Finset.sum_union hKBEx]
    symm
    apply Finset.sum_subset (Finset.union_subset hKBV hExV)
    intro Y hY hn
    exact hind0 Y hY hn
  have hsumKB : ∑ Y ∈ KB, ind Y ≤ KB.card := by
    calc ∑ Y ∈ KB, ind Y ≤ ∑ _Y ∈ KB, 1 := Finset.sum_le_sum hindKB
      _ = KB.card := by simp
  have hsumEx : ∑ Y ∈ Ex, ind Y ≤ M + 2 * ∑ E ∈ Ex, (Strn D.toRegionDissection E).card := by
    calc ∑ Y ∈ Ex, ind Y ≤ ∑ E ∈ Ex, ((cnt D idx E 2 - cnt D idx E 0) + 2 * (Strn D.toRegionDissection E).card) := Finset.sum_le_sum hindEx
      _ = M + 2 * ∑ E ∈ Ex, (Strn D.toRegionDissection E).card := by
        rw [Finset.sum_add_distrib, hcensus, ← Finset.mul_sum]
  -- outdegrees of the sources
  have hout1 : ∀ X ∈ PV ∪ KB, 1 ≤ out X := by
    intro X hX
    have hXV : X ∈ V := by
      rcases Finset.mem_union.mp hX with h | h
      · exact hPVV h
      · exact hKBV h
    obtain ⟨W, hW⟩ : ∃ W, GExc D idx X W := by
      rcases Finset.mem_union.mp hX with h | h
      · obtain ⟨k, rfl⟩ := mem_polyVerts.mp h
        exact gexc_start_of_corner D P hreg idx hC h1 h3 hcor (k + 1)
      · simp only [hKB, kiteB, Finset.mem_filter] at h
        obtain ⟨-, ⟨Z, hXZ⟩, hB⟩ := h
        obtain ⟨Z0, hZ0, -⟩ := gkite_pred_unique D P hreg idx hC hab hac h1 h3 hXZ
        exact gexc_start_of_kite D P hreg idx hC h1 h3 G hZ0 hXZ hB
    simp only [hout]
    exact Finset.card_pos.mpr ⟨W, Finset.mem_filter.mpr ⟨mem_vtxSet.mpr (gexc_end_vertex D idx hW), hW⟩⟩
  have hSV : PV ∪ KB ⊆ V := Finset.union_subset hPVV hKBV
  have hScard : (PV ∪ KB).card = M + KB.card := by
    rw [Finset.card_union_of_disjoint hPVKB, hPV, polyVerts_card]
  have hSout : M + KB.card ≤ ∑ X ∈ PV ∪ KB, out X := by
    calc M + KB.card = ∑ _X ∈ PV ∪ KB, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one, hScard]
      _ ≤ ∑ X ∈ PV ∪ KB, out X := Finset.sum_le_sum hout1
  have hVsplit : ∑ X ∈ V \ (PV ∪ KB), out X + ∑ X ∈ PV ∪ KB, out X = ∑ X ∈ V, out X := Finset.sum_sdiff hSV
  have hsplit : ∑ Y ∈ KB, (1 - ind Y) + ∑ Y ∈ KB, ind Y = KB.card := by
    rw [← Finset.sum_add_distrib]
    calc ∑ Y ∈ KB, ((1 - ind Y) + ind Y) = ∑ _Y ∈ KB, 1 := Finset.sum_congr rfl (fun Y hY => by have := hindKB Y hY; omega)
      _ = KB.card := by simp
  refine ⟨hindKB, ?_, ?_⟩
  · intro E hE
    have := hindEx E hE
    show ind E + cnt D idx E 0 ≤ cnt D idx E 2 + 2 * (Strn D.toRegionDissection E).card
    have hlt := (Finset.mem_filter.mp hE).2
    omega
  · rw [hcomm, hsumind] at hVsplit
    show ∑ Y ∈ KB, (1 - ind Y) + ∑ X ∈ V \ (PV ∪ KB), out X ≤ 2 * ∑ E ∈ Ex, (Strn D.toRegionDissection E).card
    omega

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.gexc_matching_T
