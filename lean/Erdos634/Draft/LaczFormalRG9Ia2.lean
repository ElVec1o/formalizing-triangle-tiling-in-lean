-- Draft/LaczFormalRG9Ia2.lean -- Case I, Subcase Ia (Laczkovich DCG 48 (2012), Sect. 5.1), counting part: the heads of `Gamma_a` without outgoing edge are interior exceptional vertices (`gaDf_subset_exc`);
-- the number of sides of the polygon that carry an exceptional vertex or a boundary vertex with an outgoing edge in their relative interior is at most the number of exceptional vertices (`blk_card`).  UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Sect. 5.1), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG9Flow
import Erdos634.Draft.LaczFormalRG9Ia1

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- A polygon vertex is not an interior point. -/
theorem polyVertex_not_interior (P : ConvPoly M) (k : Fin M) : P.v k ∉ interior P.carrier :=
  not_interior_of_c_zero P (i := k) (ConvPoly.c_self P k)

/-- **Heads without outgoing edge are interior exceptional vertices** (Case I). -/
theorem gaDf_subset_exc (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseA D idx) (h1 : Real.pi / 2 < D.model.angleAt 2) (h3 : D.model.angleAt 2 ≠ 2 * Real.pi / 3) :
    ∀ v ∈ gaDf D, v ∈ excVerts D idx P ∧ v ∈ interior D.region := by
  intro v hv
  simp only [gaDf, Finset.mem_filter] at hv
  obtain ⟨hvV, ⟨X, hX⟩, hno⟩ := hv
  have hint : v ∈ interior D.region := ga_head_interior D idx h.hidx h.hnc hX
  have hnc : ∀ k : Fin M, v ≠ P.v (k + 1) := by
    intro k hk
    rw [hreg] at hint
    exact polyVertex_not_interior P (k + 1) (hk ▸ hint)
  have hvert := mem_vtxSet.mp hvV
  -- the parity condition must fail at `v`
  have hpar : ¬ (∑ l, (cnt D idx v l : ℝ) * D.model.angleAt l = Real.pi → (cnt D idx v 1 + cnt D idx v 2) % 2 = 0) := by
    intro hp
    exact hno (ga_head_out_loc D idx h.hidx h.hidxA h.hnc h.hab h.hac hX hp)
  have hodd : (cnt D idx v 1 + cnt D idx v 2) % 2 ≠ 0 := fun e => hpar (fun _ => e)
  obtain ⟨hle, -, -⟩ := caseI_nonpoly D P hreg idx h.hidxA h.hregc h1 h3 hvert hnc
  have hne : cnt D idx v 2 ≠ cnt D idx v 0 := by
    intro e
    apply hodd
    rw [← h.hregc v, e]
    omega
  refine ⟨?_, hint⟩
  unfold excVerts
  simp only [Finset.mem_filter, Finset.mem_sdiff]
  exact ⟨⟨hvV, fun hp => by obtain ⟨k, hk⟩ := mem_polyVerts.mp hp; exact hnc k hk⟩, by omega⟩

/-- The side `i` carries, in its relative interior, a boundary vertex of the tiling with an outgoing `Γ_a` edge. -/
def ZSide (D : CongruentRegionDissection N) (P : ConvPoly M) (i : Fin M) : Prop :=
  ∃ z ∈ gaZ D, ∃ t : ℝ, 0 < t ∧ t < 1 ∧ z = (1 - t) • P.v i + t • P.v (i + 1)

theorem zSide_card (D : CongruentRegionDissection N) (P : ConvPoly M) :
    (Finset.univ.filter (ZSide D P)).card ≤ (gaZ D).card := by
  classical
  let g : Fin M → Plane := fun i => if h : ZSide D P i then Classical.choose h else 0
  apply Finset.card_le_card_of_injOn g
  · intro i hi
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi
    simp only [g, dif_pos hi]
    exact (Classical.choose_spec hi).1
  · intro i hi j hj hij
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi hj
    simp only [g, dif_pos hi, dif_pos hj] at hij
    obtain ⟨-, t, ht0, ht1, hX⟩ := Classical.choose_spec hi
    obtain ⟨-, t', ht0', ht1', hX'⟩ := Classical.choose_spec hj
    rw [hij] at hX
    exact openSide_unique P ht0 ht1 ht0' ht1' (hX.symm.trans hX')

/-- Sides carrying an exceptional vertex lie in bijection-bounded number with the boundary exceptional vertices. -/
theorem sideBad_card_b (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (P : ConvPoly M) (hreg : D.region = P.carrier) :
    (Finset.univ.filter (SideBad D idx P)).card ≤ ((excVerts D idx P).filter (fun v => v ∉ interior D.region)).card := by
  classical
  let g : Fin M → Plane := fun i => if h : SideBad D idx P i then Classical.choose h else 0
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

/-- **Blocked sides** (Case I, `Γ_a`): at most as many sides carry an exceptional vertex or a boundary vertex with an outgoing edge as there are exceptional vertices. -/
theorem blk_card (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseA D idx) (h1 : Real.pi / 2 < D.model.angleAt 2) (h3 : D.model.angleAt 2 ≠ 2 * Real.pi / 3) :
    (Finset.univ.filter (fun i => SideBad D idx P i ∨ ZSide D P i)).card ≤ (excVerts D idx P).card := by
  classical
  have hsub : Finset.univ.filter (fun i => SideBad D idx P i ∨ ZSide D P i) ⊆
      Finset.univ.filter (SideBad D idx P) ∪ Finset.univ.filter (ZSide D P) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hi ⊢
    exact hi
  have h1' := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (Finset.univ.filter (SideBad D idx P)) (Finset.univ.filter (ZSide D P))
  have h3' := sideBad_card_b D idx P hreg
  have h4 := zSide_card D P
  have h5 := ga_Z_le_Df D idx h
  have h6 : (gaDf D).card ≤ ((excVerts D idx P).filter (fun v => v ∈ interior D.region)).card := by
    apply Finset.card_le_card
    intro v hv
    have := gaDf_subset_exc D P hreg idx h h1 h3 v hv
    simp only [Finset.mem_filter]
    exact this
  have h7 := Finset.filter_card_add_filter_neg_card_eq_card (s := excVerts D idx P) (fun v => v ∈ interior D.region)
  have h8 : ((excVerts D idx P).filter (fun v => v ∉ interior D.region)).card = ((excVerts D idx P).filter (fun v => ¬ v ∈ interior D.region)).card := rfl
  omega

end Erdos634.Draft.LaczFormal.RG
