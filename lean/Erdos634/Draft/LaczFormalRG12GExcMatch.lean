-- Draft/LaczFormalRG12GExcMatch.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2, blueprint L10 (A.2, the GLOBAL MATCHING for Gamma_except), assembled from L1-L4, L7, L9 by double counting.
-- Sources: the `M` corners of the polygon (L4) and the type-(B) vertices `KB` of Gamma_kite (L1); every end of an edge is a vertex of `KB` (L7, L3) or an exceptional point (L7); at most one edge arrives at a vertex of `KB` (L2), at most
-- `cnt gamma - cnt alpha` at an exceptional point `E` (L9), and `sum_E (cnt gamma - cnt alpha) = M` (`exc_census`, balance of the corner counts, polygon corners having counts `(1,1,0)`).  Hence
--     M + |KB| <= #edges <= |KB| + M,
-- so (a) every vertex of `KB` receives EXACTLY one edge, (b) every exceptional point receives exactly `cnt gamma - cnt alpha` edges, (c) every edge starts at a polygon corner or at a vertex of `KB`.
-- HYPOTHESES (named): `CaseC`, `HasFansC`, `D.region = P.carrier`, `a,b` commensurable, `a,c` not, gamma < pi/2, != pi/3, `AngGen`, `hcor` (the branch `P = N`: polygon corners have counts `(1,1,0)`), and `hStrn`: NO exceptional point has a straight tile
-- (the interior T-junction exceptional points are NOT covered: see the PRINT GAP in `LaczFormalRG12GExcCap`).  NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12GExcCapMain
import Erdos634.Draft.LaczFormalRG12GExcCorner
import Erdos634.Draft.LaczFormalRG12GExcFanA
import Erdos634.Draft.LaczFormalBZ4b

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

/-- The vertices of Gamma_kite of type (B): vertices of the tiling that start a kite edge and carry no straight line of tile sides. -/
noncomputable def kiteB (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) : Finset Plane :=
  (vtxSet D.toRegionDissection).filter (fun Y => (∃ Z, GKite D idx Y Z) ∧ ¬ StraightAt D Y)

theorem gexc_end_vertex (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) {X Y : Plane} (h : GExc D idx X Y) :
    ∃ j k, (D.tile j).pts k = Y := by
  obtain ⟨d, hd, EL, ER, hrun⟩ := gexc_end_split D idx h
  rcases hrun with ⟨⟨iL, A, hL, hLg⟩, -⟩ | ⟨⟨iR, A, hR, hRg⟩, -⟩
  · obtain ⟨k, hk, -⟩ := hLg; exact ⟨iL, k, hk⟩
  · obtain ⟨k, hk, -⟩ := hRg; exact ⟨iR, k, hk⟩

/-- Every end of an edge of Gamma_except is a vertex of `KB` or an exceptional point. -/
theorem gexc_end_cls [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0) {X Y : Plane} (hE : GExc D idx X Y) :
    Y ∈ kiteB D idx ∨ Y ∈ excVerts2 D idx P := by
  rcases gexc_end_kite_or_exc D P hreg idx hC hab hac h1 h3 G hcor hE with ⟨Z, hYZ⟩ | hexc
  · left
    simp only [kiteB, Finset.mem_filter]
    refine ⟨mem_vtxSet.mpr (gexc_end_vertex D idx hE), ⟨Z, hYZ⟩, ?_⟩
    intro hS
    obtain ⟨W, hW, -⟩ := gkite_pred_unique D P hreg idx hC hab hac h1 h3 hYZ
    exact gexc_not_arrive_of_straight D P hreg idx hC h1 h3 G hW hYZ hS hE
  · right; exact hexc

/-- **Census**: the deficits of the exceptional points add up to the number of polygon corners. -/
theorem exc_census [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3)
    (hcor : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0) :
    ∑ E ∈ excVerts2 D idx P, (cnt D idx E 2 - cnt D idx E 0) = M := by
  classical
  have hdef0 := caseI_deficit_sum D P hreg idx
  have hP0 : cntP0 D idx P = M := by
    unfold cntP0
    rw [Finset.sum_congr rfl (fun k _ => (hcor (k + 1)).1)]
    simp
  have hR2 : cntR2 D idx P = 0 := by
    unfold cntR2
    exact Finset.sum_eq_zero (fun k _ => (hcor (k + 1)).2.2)
  rw [hP0, hR2] at hdef0
  have hnp : ∀ X ∈ vtxSet D.toRegionDissection \ polyVerts P, cnt D idx X 0 ≤ cnt D idx X 2 := by
    intro X hX
    rw [Finset.mem_sdiff] at hX
    have hnc : ∀ k : Fin M, X ≠ P.v (k + 1) := fun k hk => hX.2 (mem_polyVerts.mpr ⟨k, hk⟩)
    obtain ⟨a, -, -⟩ := caseII_nonpoly D P hreg idx hC.hidxA hC.hregc h1 h3 (mem_vtxSet.mp hX.1) hnc
    exact a
  have hsplit : ∑ X ∈ vtxSet D.toRegionDissection \ polyVerts P, ((cnt D idx X 2 : ℤ) - cnt D idx X 0) =
      ∑ X ∈ excVerts2 D idx P, ((cnt D idx X 2 : ℤ) - cnt D idx X 0) := by
    unfold excVerts2
    rw [← Finset.sum_filter_add_sum_filter_not (vtxSet D.toRegionDissection \ polyVerts P) (fun X => cnt D idx X 0 < cnt D idx X 2)]
    have : ∑ X ∈ (vtxSet D.toRegionDissection \ polyVerts P).filter (fun X => ¬ cnt D idx X 0 < cnt D idx X 2), ((cnt D idx X 2 : ℤ) - cnt D idx X 0) = 0 := by
      apply Finset.sum_eq_zero
      intro X hX
      simp only [Finset.mem_filter] at hX
      have := hnp X hX.1
      have : cnt D idx X 2 = cnt D idx X 0 := by omega
      omega
    rw [this, add_zero]
  have hsum : ∑ X ∈ excVerts2 D idx P, ((cnt D idx X 2 : ℤ) - cnt D idx X 0) = (M : ℤ) := by
    rw [← hsplit]
    have : ∑ X ∈ vtxSet D.toRegionDissection \ polyVerts P, ((cnt D idx X 2 : ℤ) - cnt D idx X 0) =
        -∑ X ∈ vtxSet D.toRegionDissection \ polyVerts P, ((cnt D idx X 0 : ℤ) - cnt D idx X 2) := by
      rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro X _; ring
    rw [this, hdef0]; push_cast; ring
  have hnat : ∀ X ∈ excVerts2 D idx P, ((cnt D idx X 2 - cnt D idx X 0 : ℕ) : ℤ) = (cnt D idx X 2 : ℤ) - cnt D idx X 0 := by
    intro X hX
    unfold excVerts2 at hX
    simp only [Finset.mem_filter] at hX
    rw [Nat.cast_sub hX.2.le]
  have : ((∑ E ∈ excVerts2 D idx P, (cnt D idx E 2 - cnt D idx E 0) : ℕ) : ℤ) = (M : ℤ) := by
    rw [Nat.cast_sum, Finset.sum_congr rfl hnat, hsum]
  exact_mod_cast this

theorem polyVerts_card [NeZero M] (P : ConvPoly M) : (polyVerts P).card = M := by
  unfold polyVerts
  rw [Finset.card_image_of_injective]
  · simp
  · intro a b h
    have := polyV_injective P h
    simpa using this

/-- Corner counts of a vertex of `KB`: `(2,2,2)`. -/
theorem kiteB_counts [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) {Y : Plane}
    (hY : Y ∈ kiteB D idx) : cnt D idx Y 0 = 2 ∧ cnt D idx Y 2 = 2 := by
  simp only [kiteB, Finset.mem_filter] at hY
  obtain ⟨-, ⟨Z, hYZ⟩, -⟩ := hY
  obtain ⟨-, ⟨-, c0, -, c2⟩⟩ := gkite_vertex_type D P hreg idx hC.hidxA hC.hregc h1 h3 hYZ
  exact ⟨c0, c2⟩

set_option maxHeartbeats 12800000 in
/-- **L10: the global matching of Gamma_except.** -/
theorem gexc_matching [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0)
    (hStrn : ∀ E ∈ excVerts2 D idx P, Strn D.toRegionDissection E = ∅) :
    (∀ Y ∈ kiteB D idx, ((vtxSet D.toRegionDissection).filter (fun X => GExc D idx X Y)).card = 1) ∧
    (∀ E ∈ excVerts2 D idx P, ((vtxSet D.toRegionDissection).filter (fun X => GExc D idx X E)).card = cnt D idx E 2 - cnt D idx E 0) ∧
    (∀ X Y : Plane, GExc D idx X Y → X ∈ polyVerts P ∨ X ∈ kiteB D idx) := by
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
  have hindEx : ∀ E ∈ Ex, ind E ≤ cnt D idx E 2 - cnt D idx E 0 := by
    intro E hE
    have h2 : ind E + cnt D idx E 0 ≤ cnt D idx E 2 := exc_capacity D P hreg idx hC h1 h3 hE (hStrn E hE)
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
  have hsumEx : ∑ Y ∈ Ex, ind Y ≤ M := by
    calc ∑ Y ∈ Ex, ind Y ≤ ∑ E ∈ Ex, (cnt D idx E 2 - cnt D idx E 0) := Finset.sum_le_sum hindEx
      _ = M := hcensus
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
  have htot : ∑ X ∈ V, out X ≤ KB.card + M := by
    rw [hcomm, hsumind]; omega
  have hrest : ∑ X ∈ V \ (PV ∪ KB), out X = 0 := by omega
  have hSeq : ∑ X ∈ PV ∪ KB, out X = M + KB.card := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro Y hY
    by_contra hne
    have hne' : ind Y ≠ 1 := hne
    have hlt : ∑ Y ∈ KB, ind Y < ∑ _Y ∈ KB, 1 := by
      apply Finset.sum_lt_sum hindKB
      exact ⟨Y, hY, by have := hindKB Y hY; omega⟩
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at hlt
    omega
  · intro E hE
    by_contra hne
    have hne' : ind E ≠ cnt D idx E 2 - cnt D idx E 0 := hne
    have hlt : ∑ Y ∈ Ex, ind Y < ∑ E ∈ Ex, (cnt D idx E 2 - cnt D idx E 0) := by
      apply Finset.sum_lt_sum hindEx
      exact ⟨E, hE, by have := hindEx E hE; omega⟩
    omega
  · intro X Y hXY
    by_contra hnot
    have hXV : X ∈ V := mem_vtxSet.mpr (gexc_start_vertex D idx hXY)
    have hYV : Y ∈ V := mem_vtxSet.mpr (gexc_end_vertex D idx hXY)
    have hXn : X ∈ V \ (PV ∪ KB) := by
      rw [Finset.mem_sdiff]
      refine ⟨hXV, fun h => ?_⟩
      rcases Finset.mem_union.mp h with h | h
      · exact hnot (Or.inl h)
      · exact hnot (Or.inr h)
    have hz : out X = 0 := (Finset.sum_eq_zero_iff.mp hrest) X hXn
    have : 0 < out X := Finset.card_pos.mpr ⟨Y, Finset.mem_filter.mpr ⟨hYV, hXY⟩⟩
    omega

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.gexc_matching
