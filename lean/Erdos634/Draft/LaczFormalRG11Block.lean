-- Draft/LaczFormalRG11Block.lean -- Laczkovich DCG 48 (2012), Sect. 6.1 (Case II, Subcase IIa, `Gamma_a`), the blocked-side count.  Unlike Case I (where Lemma 4.3 (i) only constrains the INTERIOR vertices of a side),
-- Lemma 4.3 (iii) also needs "no edge of `Gamma_a` starts from `X` or `Y`", so a polygon vertex with an outgoing edge blocks both adjacent sides.  `blocked_card`: the number of sides that carry an exceptional vertex
-- (`SideBad2`) or a boundary vertex with an outgoing edge (`ZSide`) in the relative interior, or have an end with an outgoing edge, is at most `eb + 2 ei` (`eb`, `ei` = boundary / interior exceptional vertices).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 4, 6.1), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG11Count
import Erdos634.Draft.LaczFormalRG9Ia3

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- **Normal vertices on a side without exceptional vertex** (Case II). -/
theorem caseII_normal_side (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1)
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) {i : Fin M} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {X : Plane}
    (hX : X = (1 - t) • P.v i + t • P.v (i + 1)) (hvert : ∃ j k, (D.tile j).pts k = X) (hne : X ∉ excVerts2 D idx P) :
    cnt D idx X 0 = 1 ∧ cnt D idx X 1 = 1 ∧ cnt D idx X 2 = 1 := by
  have hnc : ∀ k : Fin M, X ≠ P.v (k + 1) := fun k => by rw [hX]; exact openSide_ne_vertex P ht0 ht1 (k + 1)
  have hni : X ∉ interior D.region := by
    rw [hreg, hX]; exact not_interior_of_c_zero P (c_on_edge P i t)
  obtain ⟨hle, -, hn⟩ := caseII_nonpoly D P hreg idx hidxA hregc h1 h3 hvert hnc
  have hnex : ¬ cnt D idx X 0 < cnt D idx X 2 := by
    intro hlt
    apply hne
    unfold excVerts2
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    exact ⟨⟨mem_vtxSet.mpr hvert, fun hp => by obtain ⟨k, hk⟩ := mem_polyVerts.mp hp; exact hnc k hk⟩, hlt⟩
  have heq : cnt D idx X 2 = cnt D idx X 0 := by omega
  have h0 := hn heq hni
  refine ⟨h0, ?_, by omega⟩
  rw [← hregc X]; exact h0

/-- The side `i` carries an exceptional vertex (Case II) in its relative interior. -/
def SideBad2 (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (P : ConvPoly M) (i : Fin M) : Prop :=
  ∃ X ∈ excVerts2 D idx P, ∃ t : ℝ, 0 < t ∧ t < 1 ∧ X = (1 - t) • P.v i + t • P.v (i + 1)

theorem sideBad2_card_b (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (P : ConvPoly M) (hreg : D.region = P.carrier) :
    (Finset.univ.filter (SideBad2 D idx P)).card ≤ ((excVerts2 D idx P).filter (fun v => v ∉ interior D.region)).card := by
  classical
  let g : Fin M → Plane := fun i => if h : SideBad2 D idx P i then Classical.choose h else 0
  apply Finset.card_le_card_of_injOn g
  · intro i hi
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi
    simp only [Finset.coe_filter, g, dif_pos hi, Set.mem_setOf_eq]
    obtain ⟨hex, t, ht0, ht1, hX⟩ := Classical.choose_spec hi
    refine ⟨hex, ?_⟩
    rw [hreg, hX]
    exact not_interior_of_c_zero P (c_on_edge P i t)
  · intro i hi j hj hij
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi hj
    simp only [g, dif_pos hi, dif_pos hj] at hij
    obtain ⟨-, t, ht0, ht1, hX⟩ := Classical.choose_spec hi
    obtain ⟨-, t', ht0', ht1', hX'⟩ := Classical.choose_spec hj
    rw [hij] at hX
    exact openSide_unique P ht0 ht1 ht0' ht1' (hX.symm.trans hX')

/-- **Heads without outgoing edge are interior exceptional vertices** (Case II). -/
theorem gaDf_subset_exc2 (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseA D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) :
    ∀ v ∈ gaDf D, v ∈ excVerts2 D idx P ∧ v ∈ interior D.region := by
  intro v hv
  simp only [gaDf, Finset.mem_filter] at hv
  obtain ⟨hvV, ⟨X, hX⟩, hno⟩ := hv
  have hint : v ∈ interior D.region := ga_head_interior D idx h.hidx h.hnc hX
  have hnc : ∀ k : Fin M, v ≠ P.v (k + 1) := by
    intro k hk
    rw [hreg] at hint
    exact polyVertex_not_interior P (k + 1) (hk ▸ hint)
  have hvert := mem_vtxSet.mp hvV
  have hpar : ¬ (∑ l, (cnt D idx v l : ℝ) * D.model.angleAt l = Real.pi → (cnt D idx v 1 + cnt D idx v 2) % 2 = 0) := by
    intro hp
    exact hno (ga_head_out_loc D idx h.hidx h.hidxA h.hnc h.hab h.hac hX hp)
  have hodd : (cnt D idx v 1 + cnt D idx v 2) % 2 ≠ 0 := fun e => hpar (fun _ => e)
  obtain ⟨hle, -, -⟩ := caseII_nonpoly D P hreg idx h.hidxA h.hregc h1 h3 hvert hnc
  have hne : cnt D idx v 2 ≠ cnt D idx v 0 := by
    intro e
    apply hodd
    rw [← h.hregc v, e]
    omega
  refine ⟨?_, hint⟩
  unfold excVerts2
  simp only [Finset.mem_filter, Finset.mem_sdiff]
  exact ⟨⟨hvV, fun hp => by obtain ⟨k, hk⟩ := mem_polyVerts.mp hp; exact hnc k hk⟩, by omega⟩

theorem side_hyps2 (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseA D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3)
    (i : Fin M) (hb : ¬ (SideBad2 D idx P i ∨ ZSide D P i)) : NormSide D idx P i ∧ NoEdgeSide D P i := by
  refine ⟨?_, ?_⟩
  · intro V hv ⟨t, ht0, ht1, hVt⟩
    have hne : V ∉ excVerts2 D idx P := fun hex => hb (Or.inl ⟨V, hex, t, ht0, ht1, hVt⟩)
    exact caseII_normal_side D P hreg idx h.hidxA h.hregc h1 h3 ht0 ht1 hVt hv hne
  · intro V hv ⟨t, ht0, ht1, hVt⟩ H' hH'
    apply hb
    right
    refine ⟨V, ?_, t, ht0, ht1, hVt⟩
    simp only [gaZ, Finset.mem_filter]
    refine ⟨mem_vtxSet.mpr hv, ?_, H', hH'⟩
    rw [hreg, hVt]
    exact not_interior_of_c_zero P (c_on_edge P i t)

/-- A polygon vertex with an outgoing edge of `Γ_a`. -/
def PEdge (D : CongruentRegionDissection N) (P : ConvPoly M) (k : Fin M) : Prop :=
  ∃ H, GaEdge D.toRegionDissection (slen D 0) (P.v k) H

/-- A side is blocked: it carries in its relative interior an exceptional vertex or a boundary vertex with an outgoing edge, or one of its ends has an outgoing edge. -/
def Blocked (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (P : ConvPoly M) (i : Fin M) : Prop :=
  SideBad2 D idx P i ∨ ZSide D P i ∨ PEdge D P i ∨ PEdge D P (i + 1)

/-- **Blocked sides, Case II**: at most `eb + 2 ei`. -/
theorem blocked_card (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseA D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) :
    (Finset.univ.filter (Blocked D idx P)).card ≤
      ((excVerts2 D idx P).filter (fun v => v ∉ interior D.region)).card + 2 * ((excVerts2 D idx P).filter (fun v => v ∈ interior D.region)).card := by
  classical
  set A : Finset Plane := (gaZ D).filter (fun v => v ∈ polyVerts P) with hA
  set B : Finset Plane := (gaZ D).filter (fun v => v ∉ polyVerts P) with hB
  have hAB : A.card + B.card = (gaZ D).card := Finset.filter_card_add_filter_neg_card_eq_card (s := gaZ D) (fun v => v ∈ polyVerts P)
  have hpolyz : ∀ k : Fin M, PEdge D P k → P.v k ∈ A := by
    intro k hk
    rw [hA]
    simp only [Finset.mem_filter, gaZ]
    obtain ⟨H, hH⟩ := hk
    refine ⟨⟨mem_vtxSet.mpr ?_, ?_, H, hH⟩, mem_polyVerts.mpr ⟨k - 1, by rw [sub_add_cancel]⟩⟩
    · have := poly_vertex_is_tile_vertex D.toRegionDissection P hreg (k - 1 + 1)
      rwa [sub_add_cancel] at this
    · rw [hreg]; exact polyVertex_not_interior P k
  have hS3 : (Finset.univ.filter (fun i => PEdge D P i)).card ≤ A.card := by
    apply Finset.card_le_card_of_injOn (fun i => P.v i)
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi
      exact hpolyz i hi
    · intro i _ j _ hij
      exact polyV_injective P hij
  have hS4 : (Finset.univ.filter (fun i => PEdge D P (i + 1))).card ≤ A.card := by
    apply Finset.card_le_card_of_injOn (fun i => P.v (i + 1))
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi
      exact hpolyz (i + 1) hi
    · intro i _ j _ hij
      exact add_right_cancel (polyV_injective P hij)
  have hS2 : (Finset.univ.filter (ZSide D P)).card ≤ B.card := by
    classical
    let g : Fin M → Plane := fun i => if h : ZSide D P i then Classical.choose h else 0
    apply Finset.card_le_card_of_injOn g
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi
      simp only [g, dif_pos hi]
      obtain ⟨hz, t, ht0, ht1, hX⟩ := Classical.choose_spec hi
      rw [hB]
      simp only [Finset.coe_filter, Finset.mem_filter, Set.mem_setOf_eq]
      refine ⟨hz, fun hp => ?_⟩
      obtain ⟨k, hk⟩ := mem_polyVerts.mp hp
      exact openSide_ne_vertex P ht0 ht1 (k + 1) (hX.symm.trans hk)
    · intro i hi j hj hij
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi hj
      simp only [g, dif_pos hi, dif_pos hj] at hij
      obtain ⟨-, t, ht0, ht1, hX⟩ := Classical.choose_spec hi
      obtain ⟨-, t', ht0', ht1', hX'⟩ := Classical.choose_spec hj
      rw [hij] at hX
      exact openSide_unique P ht0 ht1 ht0' ht1' (hX.symm.trans hX')
  have hS1 := sideBad2_card_b D idx P hreg
  have hsub : Finset.univ.filter (Blocked D idx P) ⊆
      (Finset.univ.filter (SideBad2 D idx P) ∪ Finset.univ.filter (ZSide D P)) ∪
        (Finset.univ.filter (fun i => PEdge D P i) ∪ Finset.univ.filter (fun i => PEdge D P (i + 1))) := by
    intro i hi
    simp only [Blocked, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hi ⊢
    tauto
  have c1 := Finset.card_le_card hsub
  have c2 := Finset.card_union_le (Finset.univ.filter (SideBad2 D idx P) ∪ Finset.univ.filter (ZSide D P)) (Finset.univ.filter (fun i => PEdge D P i) ∪ Finset.univ.filter (fun i => PEdge D P (i + 1)))
  have c3 := Finset.card_union_le (Finset.univ.filter (SideBad2 D idx P)) (Finset.univ.filter (ZSide D P))
  have c4 := Finset.card_union_le (Finset.univ.filter (fun i => PEdge D P i)) (Finset.univ.filter (fun i => PEdge D P (i + 1)))
  have hZD := ga_Z_le_Df D idx h
  have h6 : (gaDf D).card ≤ ((excVerts2 D idx P).filter (fun v => v ∈ interior D.region)).card := by
    apply Finset.card_le_card
    intro v hv
    have := gaDf_subset_exc2 D P hreg idx h h1 h3 v hv
    simp only [Finset.mem_filter]
    exact this
  omega

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.blocked_card
