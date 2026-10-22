-- Draft/LaczFormalBZBridge.lean -- Laczkovich DCG 48 (2012) Thm 2.1, Cases IIIa/IIIb (polygon targets, gamma = 2 pi/3): the BRIDGE between the defect inequality `caseIII_defects` (LaczFormalBZDefects)
-- and the corner-side closure `caseIII_concl1` (LaczFormalIIIaCornerClose), and the two assembled cases.
--   * `nonclean_le_defects`: #(non-clean sides) <= s_b + B.  PRECISE form of "one defect spoils only one side": a side i is non-clean iff some tiling vertex V in the relative interior of side i has counts != (1,1,1)
--     or has an out-edge of Gamma_a; such V is a non-corner boundary vertex (`openSide_ne_vertex`, `not_interior_of_c_zero`) and then, by `poly_noncorner_boundary_type`, a boundary star (counted in s_b) or has
--     gaOut >= 1 (counted in B, whose second sum runs over non-corner boundary vertices).  Distinct sides have disjoint relative interiors (`openSide_unique`), so the choice side -> vertex is injective.
--     (Corner out-edges are in B too but are NOT used: a non-clean side is witnessed by an OPEN-interior vertex only, so no double counting issue arises.)
--   * `caseIII_hdef`: 3 #(non-clean) + P <= R, using the unit sum  P + 2R = 3 (M-2)  (`corner_data`).
--   * `caseIIIa_repaired`: regular PolyTiling, gamma = 2 pi/3, NotComb a b c  ==>  Concl1.   `caseIIIb_repaired`: NotComb b a c ==> Concl1 (relabelling alpha <-> beta, as `caseIII_count'`).
-- NOTE, UNAUDITED.  Non-vacuity: NO tiling with NotComb data and M >= 4 is known in the corpus (the theorem says there is none outside Concl1); the hypotheses regular/gamma = 2pi/3/NotComb are
-- satisfiable abstractly (a, b, c with a not a nonneg. rational combination of b, c) but no polygon tiling witnessing them is exhibited: honest statement, as in LaczFormalIIIcGlue for the IIIc side.
-- Credit: Laczkovich (DCG 48 (2012), Sect. 4, 7), Beeson-Zhang (arXiv 2604.01314), Beeson.
import Erdos634.Draft.LaczFormalBZDefects
import Erdos634.Draft.LaczFormalBZ7
import Erdos634.Draft.LaczFormalIIIaCornerClose
import Erdos634.Draft.LaczFormalRGRelabel
import Erdos634.Draft.LaczFormalRG9Sides

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem gaOut_pos_of_edge (D : CongruentRegionDissection N) {v H : Plane} (hH : GaEdge D.toRegionDissection (slen D 0) v H) : 0 < gaOut D v := by
  have hmem : (v, H) ∈ (gaEdgeSet D).filter (fun e => e.1 = v) := by
    have := ga_edge_endpoints D.toRegionDissection (slen D 0) hH
    simp only [gaEdgeSet, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨⟨mem_vtxSet.mpr this.1, mem_vtxSet.mpr this.2⟩, hH⟩, trivial⟩
  exact Finset.card_pos.mpr ⟨_, hmem⟩

set_option maxHeartbeats 3200000 in
/-- **A non-clean side contains a defect vertex in its relative interior; distinct sides get distinct vertices.** -/
theorem nonclean_le_defects (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hγ : D.model.angleAt 2 = 2 * Real.pi / 3) (hαβ : D.model.angleAt 0 + D.model.angleAt 1 = Real.pi / 3)
    (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1) :
    (Finset.univ.filter (fun i : Fin M => ¬ (NormSide D idx P i ∧ NoEdgeSide D P i))).card ≤ defSb D idx P + defB D P := by
  classical
  set V0 := vtxSet D.toRegionDissection with hV0
  set Tset := V0.filter (fun v => IsNonCorner P v ∧ v ∉ interior D.region ∧ ((cnt D idx v 0 = 3 ∧ cnt D idx v 2 = 0) ∨ 0 < gaOut D v)) with hT
  set S := Finset.univ.filter (fun i : Fin M => ¬ (NormSide D idx P i ∧ NoEdgeSide D P i)) with hS
  have hex : ∀ i : Fin M, i ∈ S → ∃ V, V ∈ Tset ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧ V = (1 - t) • P.v i + t • P.v (i + 1) := by
    intro i hi
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hcase : ∃ V, (∃ j k, (D.tile j).pts k = V) ∧ (∃ t : ℝ, 0 < t ∧ t < 1 ∧ V = (1 - t) • P.v i + t • P.v (i + 1)) ∧
        (¬ (cnt D idx V 0 = 1 ∧ cnt D idx V 1 = 1 ∧ cnt D idx V 2 = 1) ∨ ∃ H', GaEdge D.toRegionDissection (slen D 0) V H') := by
      by_contra hcon
      apply hi
      refine ⟨fun V hv ht => ?_, fun V hv ht H' hH' => ?_⟩
      · by_contra hc; exact hcon ⟨V, hv, ht, Or.inl hc⟩
      · exact hcon ⟨V, hv, ht, Or.inr ⟨H', hH'⟩⟩
    obtain ⟨V, hv, ⟨t, ht0, ht1, hVt⟩, hc⟩ := hcase
    have hvv : V ∈ V0 := mem_vtxSet.mpr hv
    have hnk : IsNonCorner P V := fun k => by rw [hVt]; exact openSide_ne_vertex P ht0 ht1 (k + 1)
    have hni : V ∉ interior D.region := by rw [hreg, hVt]; exact not_interior_of_c_zero P (c_on_edge P i t)
    refine ⟨V, Finset.mem_filter.mpr ⟨hvv, hnk, hni, ?_⟩, t, ht0, ht1, hVt⟩
    rcases hc with hc | ⟨H', hH'⟩
    · left
      rcases poly_noncorner_boundary_type D P hreg idx hidxA hγ hαβ hregc hvv hnk hni with ⟨h0, -, h2⟩ | h
      · exact ⟨h0, h2⟩
      · exact absurd h hc
    · right; exact gaOut_pos_of_edge D hH'
  choose! W hW using hex
  have hinj : Set.InjOn W (S : Set (Fin M)) := by
    intro i hi j hj hij
    obtain ⟨-, t, ht0, ht1, hVt⟩ := hW i hi
    obtain ⟨-, t', ht0', ht1', hVt'⟩ := hW j hj
    rw [hij] at hVt
    exact openSide_unique P ht0 ht1 ht0' ht1' (hVt.symm.trans hVt')
  have h1 : S.card ≤ Tset.card := Finset.card_le_card_of_injOn W (fun i hi => (hW i hi).1) hinj
  set F := V0.filter (fun v => IsNonCorner P v ∧ v ∉ interior D.region) with hF
  set Gs := V0.filter (fun v => IsNonCorner P v ∧ v ∉ interior D.region ∧ 0 < gaOut D v) with hGs
  set Sb := V0.filter (fun v => IsNonCorner P v ∧ v ∉ interior D.region ∧ cnt D idx v 0 = 3 ∧ cnt D idx v 2 = 0) with hSb
  have hsub : Tset ⊆ Sb ∪ Gs := by
    intro v hv
    simp only [hT, hSb, hGs, Finset.mem_filter, Finset.mem_union] at hv ⊢
    rcases hv with ⟨hv1, hv2, hv3, hv4 | hv4⟩
    · exact Or.inl ⟨hv1, hv2, hv3, hv4⟩
    · exact Or.inr ⟨hv1, hv2, hv3, hv4⟩
  have h2 : Tset.card ≤ Sb.card + Gs.card := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hGF : Gs ⊆ F := by
    intro v hv
    simp only [hGs, hF, Finset.mem_filter] at hv ⊢
    exact ⟨hv.1, hv.2.1, hv.2.2.1⟩
  have h3 : Gs.card ≤ ∑ v ∈ F, gaOut D v := by
    calc Gs.card = ∑ _v ∈ Gs, 1 := by simp
      _ ≤ ∑ v ∈ Gs, gaOut D v := Finset.sum_le_sum (fun v hv => by
          simp only [hGs, Finset.mem_filter] at hv; exact hv.2.2.2)
      _ ≤ ∑ v ∈ F, gaOut D v := Finset.sum_le_sum_of_subset hGF
  have h4 : defSb D idx P = Sb.card := rfl
  have h5 : ∑ v ∈ F, gaOut D v ≤ defB D P := by
    unfold defB; exact Nat.le_add_left _ _
  omega

/-- **The defect bound `hdef` of `caseIII_close`**, proved from `caseIII_defects` (`P + 2R = 3 (M-2)`). -/
theorem caseIII_hdef (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2))
    (hγ : D.model.angleAt 2 = 2 * Real.pi / 3) (hαβ : D.model.angleAt 0 + D.model.angleAt 1 = Real.pi / 3)
    (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1) (hPang : ∀ i, P.angle i = Real.pi / 3 ∨ P.angle i = 2 * Real.pi / 3) :
    3 * (Finset.univ.filter (fun i : Fin M => ¬ (NormSide D idx P i ∧ NoEdgeSide D P i))).card + ∑ k : Fin M, cnt D idx (P.v (k + 1)) 0
      ≤ ∑ k : Fin M, cnt D idx (P.v (k + 1)) 2 := by
  classical
  have hd := caseIII_defects D P hreg idx hidx hidxA hnc hγ hαβ hregc hPang
  have hnl := nonclean_le_defects D P hreg idx hidxA hγ hαβ hregc
  obtain ⟨-, hsum⟩ := corner_data D P hreg idx hidxA hγ hαβ hregc
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hc : (∑ k : Fin M, (cnt D idx (P.v (k + 1)) 2 : ℤ)) = ((∑ k : Fin M, cnt D idx (P.v (k + 1)) 2 : ℕ) : ℤ) := by rw [Nat.cast_sum]
  rw [hc] at hd
  have hM3 : 3 ≤ M := P.three_le
  omega

/-- **Case IIIa, repaired** (polygon target `M ≥ 3`, `γ = 2π/3`, `a` not a nonnegative rational combination of `b, c`): Conclusion (i) of Theorem 2.1. -/
theorem caseIIIa_repaired (T : PolyTiling N M) (hreg : RegularPQ T.C) (hγ : angleAt T.C.model 2 = 2 * Real.pi / 3)
    (hnc : NotComb (slen T.C 0) (slen T.C 1) (slen T.C 2)) : Concl1 T.C T.P := by
  classical
  obtain ⟨idx, hA, hcnt⟩ := hreg
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hidx := idx_dist_of_angle T.C idx hA
  have hαβ : T.C.model.angleAt 0 + T.C.model.angleAt 1 = Real.pi / 3 := by
    have := Erdos634.Draft.LaczFormal.angleAt_sum T.C.model
    have hγ'' : T.C.model.angleAt 2 = 2 * Real.pi / 3 := hγ
    linarith
  have hall := poly_angles_2pi3 T hγ idx hA hcnt
  have hdef := caseIII_hdef T.C T.P T.region_eq idx hidx hA hnc hγ hαβ (fun X => hcnt X) hall
  exact caseIII_concl1 T idx hA hcnt hγ hnc hdef

/-- `Concl1` is invariant under exchanging the model vertices `0, 1` (the third disjunct is symmetric: `q ≠ 0` since the sides are positive). -/
theorem concl1_swap (D D' : CongruentRegionDissection N) (P : ConvPoly M) (hD : D'.region = D.region)
    (h2 : angleAt D'.model 2 = angleAt D.model 2) (h0 : angleAt D'.model 0 = angleAt D.model 1) (h1 : angleAt D'.model 1 = angleAt D.model 0)
    (h : Concl1 D' P) (hP : ∀ i, 0 < P.side i) : Concl1 D P := by
  obtain ⟨hq, hang, hr⟩ := h
  refine ⟨hq, ?_, ?_⟩
  · rw [h2] at hang; exact hang
  · have hs0 := hP 0
    have hs1 := hP 1
    rw [h0, h1] at hr
    have hs := Real.sin_pos_of_pos_of_lt_pi (D.model.angleAt_pos' 0) (by have := angleAt_sum D.model; have := D.model.angleAt_pos' 1; have := D.model.angleAt_pos' 2; linarith)
    have hs' := Real.sin_pos_of_pos_of_lt_pi (D.model.angleAt_pos' 1) (by have := angleAt_sum D.model; have := D.model.angleAt_pos' 0; have := D.model.angleAt_pos' 2; linarith)
    rcases hr with ⟨q, hq⟩ | ⟨q, hq⟩
    · right
      have hqne : q ≠ 0 := by
        rintro rfl
        have : P.side 0 / P.side 1 = 0 := by rw [hq]; simp
        have := div_pos hs0 hs1; linarith
      refine ⟨q⁻¹, ?_⟩
      have e : P.side 1 / P.side 0 = (P.side 0 / P.side 1)⁻¹ := by rw [inv_div]
      rw [e, hq]; push_cast
      field_simp
    · left
      have hqne : q ≠ 0 := by
        rintro rfl
        have : P.side 1 / P.side 0 = 0 := by rw [hq]; simp
        have := div_pos hs1 hs0; linarith
      refine ⟨q⁻¹, ?_⟩
      have e : P.side 0 / P.side 1 = (P.side 1 / P.side 0)⁻¹ := by rw [inv_div]
      rw [e, hq]; push_cast
      field_simp

/-- **Case IIIb, repaired** (`b` not a nonnegative rational combination of `a, c`): Conclusion (i), by the relabelling `α ↔ β` of `caseIII_count'`. -/
theorem caseIIIb_repaired (T : PolyTiling N M) (hreg : RegularPQ T.C) (hγ : angleAt T.C.model 2 = 2 * Real.pi / 3)
    (hnc : NotComb (slen T.C 1) (slen T.C 0) (slen T.C 2)) : Concl1 T.C T.P := by
  classical
  obtain ⟨idx, hA, hcnt⟩ := hreg
  set σ : Equiv.Perm (Fin 3) := Equiv.swap 0 1 with hσ
  set Dr := relabel T.C σ with hDr
  have hs0 : σ 0 = 1 := by decide
  have hs1 : σ 1 = 0 := by decide
  have hs2 : σ 2 = 2 := by decide
  have hang : ∀ j, Dr.model.angleAt j = T.C.model.angleAt (σ j) := fun j => relabel_angleAt T.C σ j
  have hsl : ∀ t, slen Dr t = slen T.C (σ t) := fun t => relabel_slen T.C σ t
  have hreg' : Dr.region = T.P.carrier := T.region_eq
  set T' : PolyTiling N M := ⟨Dr, T.P, hreg'⟩ with hT'
  set idx' := relabelIdx idx σ with hidx'
  have hA' : ∀ i v, angleAt T'.C.model (idx' i v) = angleAt (T'.C.tile i) v := relabel_hidxA T.C idx σ hA
  have hγ' : angleAt T'.C.model 2 = 2 * Real.pi / 3 := by
    show Dr.model.angleAt 2 = _
    rw [hang, hs2]; exact hγ
  have hcnt' : ∀ X, cnt T'.C idx' X 0 = cnt T'.C idx' X 1 := by
    intro X
    show cnt Dr idx' X 0 = cnt Dr idx' X 1
    rw [relabel_cnt, relabel_cnt, hs0, hs1]
    exact (hcnt X).symm
  have hnc' : NotComb (slen T'.C 0) (slen T'.C 1) (slen T'.C 2) := by
    show NotComb (slen Dr 0) (slen Dr 1) (slen Dr 2)
    rw [hsl, hsl, hsl, hs0, hs1, hs2]; exact hnc
  have hc1 : Concl1 T'.C T'.P := by
    haveI : HasFansC T'.C.toRegionDissection := hasFansC_poly _ T'.P T'.region_eq
    have hidx := idx_dist_of_angle T'.C idx' hA'
    have hαβ : T'.C.model.angleAt 0 + T'.C.model.angleAt 1 = Real.pi / 3 := by
      have := Erdos634.Draft.LaczFormal.angleAt_sum T'.C.model
      have hγ'' : T'.C.model.angleAt 2 = 2 * Real.pi / 3 := hγ'
      linarith
    have hall := poly_angles_2pi3 T' hγ' idx' hA' hcnt'
    have hdef := caseIII_hdef T'.C T'.P T'.region_eq idx' hidx hA' hnc' hγ' hαβ hcnt' hall
    exact caseIII_concl1 T' idx' hA' hcnt' hγ' hnc' hdef
  have hside : ∀ i, 0 < T.P.side i := fun i => by
    unfold ConvPoly.side
    exact dist_pos.mpr (fun h => by
      have := T.P.three_le
      have hf := ConvPoly.fin_facts this i
      exact hf.1 (polyV_injective T.P h.symm))
  exact concl1_swap T.C Dr T.P rfl ((hang 2).trans (congrArg _ hs2)) ((hang 0).trans (congrArg _ hs0)) ((hang 1).trans (congrArg _ hs1)) hc1 hside

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.nonclean_le_defects
#print axioms Erdos634.Draft.LaczFormal.RG.caseIII_hdef
#print axioms Erdos634.Draft.LaczFormal.RG.caseIIIa_repaired
#print axioms Erdos634.Draft.LaczFormal.RG.caseIIIb_repaired
