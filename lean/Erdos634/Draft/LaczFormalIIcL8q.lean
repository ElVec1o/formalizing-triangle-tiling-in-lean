-- Draft/LaczFormalIIcL8q.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, L8 `gexc_disjoint`, step 10: the capacity of an exceptional point for ANY finite family of starts with arrival-type data (`exc_capacity_gen`),
-- and `thru_arr_or_lineD`: an edge `X -> Y` through an exceptional point `E` (inner point) has arrival-type data at `E`.
-- `exc_capacity_gen` is the body of `exc_capacity_sharp` / `exc_capacity` with `{X | GExc X E}` replaced by an arbitrary finite set `S` of points each of which has `ArrData` or `LineD` at `E`.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcL8p
import Erdos634.Draft.LaczFormalIIcL8m
import Erdos634.Draft.LaczFormalIIcSharp5

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

theorem thru_arr_or_lineD (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1) (h1 : D.model.angleAt 2 < Real.pi / 2)
    {E : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection E κ) (hlt : cnt D idx E 0 < cnt D idx E 2) {X Y : Plane}
    (h : GExc D idx X Y) (hE : E ∈ openSegment ℝ X Y) : (∃ aL aR : AtV D.toRegionDissection E, ArrData D idx F X aL aR) ∨ LineD D idx X E := by
  obtain ⟨d, hd, nb, -, -, EL, ER, WL, WR⟩ := gexc_inner_split D idx h hE
  rcases WL with ⟨P, hP, hPne⟩ | ⟨iL, A, B, hS, hin⟩
  · exact arrData_or_lineD_of_split D idx F hd nb ⟨true, P, hP, hPne⟩ EL ER
  · rcases WR with ⟨P, hP, hPne⟩ | ⟨iR, A', B', hS', hin'⟩
    · exact arrData_or_lineD_of_split D idx F hd nb ⟨false, P, hP, hPne⟩ EL ER
    · exfalso
      have hne : iL ≠ iR := by
        intro e; subst e
        exact not_both_inner (D.tile iL) hd hS hS' hin hin'
      have hcard := strn_card_le_one D idx hidxA hregc h1 F hlt
      have m1 := strn_of_inner hS hin
      have m2 := strn_of_inner hS' (by rw [openSegment_symm]; exact hin')
      exact hne (Finset.card_le_one.mp hcard iL m1 iR m2)

set_option maxHeartbeats 6400000 in
/-- **Capacity for an arbitrary family of arrival-type starts.** -/
theorem exc_capacity_gen [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3)
    {E : Plane} (hE : E ∈ excVerts2 D idx P) {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection E κ) (S : Finset Plane)
    (hS : ∀ X ∈ S, (∃ aL aR : AtV D.toRegionDissection E, ArrData D idx F X aL aR) ∨ LineD D idx X E) :
    S.card + cnt D idx E 0 ≤ cnt D idx E 2 := by
  classical
  unfold excVerts2 at hE
  simp only [Finset.mem_filter, Finset.mem_sdiff] at hE
  obtain ⟨⟨hEv, hEp⟩, hlt⟩ := hE
  have hvert := mem_vtxSet.mp hEv
  have hnc : ∀ k : Fin M, E ≠ P.v (k + 1) := fun k hk => hEp (mem_polyVerts.mpr ⟨k, hk⟩)
  have hp1 := exc_cnt0_le_one D P hreg idx hC.hidxA hC.hregc h1 h3 hvert hnc hlt
  obtain ⟨j0, k0, hk0⟩ := hvert
  haveI : Nonempty (AtV D.toRegionDissection E) := ⟨⟨j0, hk0 ▸ tile_pt_mem _ k0⟩⟩
  set Γ : Finset (AtV D.toRegionDissection E) := Finset.univ.filter (fun a => IsGam D idx a) with hΓ
  have hΓcard : Γ.card ≤ cnt D idx E 2 := gamma_card_le_cnt D idx Γ (fun a ha => (Finset.mem_filter.mp ha).2)
  by_cases hSt : Strn D.toRegionDissection E = ∅
  · -- no straight tile: all starts have ArrData
    have hAD : ∀ X ∈ S, ∃ aL aR : AtV D.toRegionDissection E, ArrData D idx F X aL aR := by
      intro X hX
      rcases hS X hX with h | h
      · exact h
      · exfalso
        obtain ⟨d, bl, P', i, A, B, a, b', -, -, -, -, hi, -⟩ := h
        rw [hSt] at hi; exact absurd hi (Finset.notMem_empty _)
    by_cases hA0 : S.card = 0
    · rw [hA0]; omega
    obtain ⟨X0, hX0⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hA0)
    choose! aL aR hAD' using hAD
    have hsub : ∀ X ∈ S, aR X ∈ Γ := by
      intro X hX
      obtain ⟨-, -, -, -, -, -, -, hg⟩ := hAD' X hX
      simp only [hΓ, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hg
    have hinj : Set.InjOn aR S := by
      intro X hX X' hX' h
      exact (arrData_inj_R D idx F (hAD' X hX) (hAD' X' hX') h).symm
    have hle : S.card ≤ Γ.card := Finset.card_le_card_of_injOn aR (fun X hX => hsub X hX) hinj
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hp1 with hp0 | hp1'
    · rw [hp0]; omega
    · rw [hp1']
      have hlt' : S.card < Γ.card := by
        by_contra hnl
        push Not at hnl
        have himg : S.image aR = Γ := by
          apply Finset.eq_of_subset_of_card_le
          · intro g hg
            obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hg
            exact hsub X hX
          · rw [Finset.card_image_of_injOn hinj]; exact hnl
        have hcl : ∀ g ∈ (Γ : Set (AtV D.toRegionDissection E)), ∃ a ∈ (Γ : Set (AtV D.toRegionDissection E)), Par (F.q a) (F.p g) := by
          intro g hg
          have hg' : g ∈ S.image aR := by rw [himg]; exact hg
          obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hg'
          obtain ⟨d, hd, hnb, hw, hq, hp, hgL, hgR⟩ := hAD' X hX
          refine ⟨aL X, ?_, hq.trans hp.symm⟩
          simp only [hΓ, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
          exact hgL
        have hg0 : aR X0 ∈ (Γ : Set (AtV D.toRegionDissection E)) := hsub X0 hX0
        have hall := fan_closed F (Γ : Set (AtV D.toRegionDissection E)) hg0 hcl
        have hpos : 0 < cnt D idx E 0 := by omega
        unfold cnt at hpos
        obtain ⟨⟨i, k⟩, hik⟩ := Finset.card_pos.mp hpos
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hik
        obtain ⟨hik1, hik2⟩ := hik
        have hmem : E ∈ (D.tile i).carrier := hik1 ▸ tile_pt_mem _ k
        obtain ⟨a, ha, hea⟩ := hall (Sum.inl ⟨i, hmem⟩)
        have haeq : a = ⟨i, hmem⟩ := (Sum.inl_injective hea).symm
        subst haeq
        have ha' : IsGam D idx ⟨i, hmem⟩ := by
          have := Finset.mem_coe.mp ha
          simpa [hΓ, IsGam] using this
        obtain ⟨k', hk'1, hk'2⟩ := ha'
        have : k' = k := (D.tile i).indep.injective (hk'1.trans hik1.symm)
        rw [this, hik2] at hk'2
        exact absurd hk'2 (by decide)
      omega
  · -- a straight tile: `p = 0`, at most one `LineD` start, the others inject into `Gamma` minus the straight sector
    have hSne : (Strn D.toRegionDissection E).Nonempty := Finset.nonempty_iff_ne_empty.mpr hSt
    have hp0 := exc_p_zero_of_strn D idx hC.hidxA hC.hregc F hSne hlt
    have hcard := strn_card_le_one D idx hC.hidxA hC.hregc h1 F hlt
    rw [hp0, add_zero]
    set Aln := S.filter (fun X => LineD D idx X E) with hAln
    set Anl := S.filter (fun X => ¬ LineD D idx X E) with hAnl
    have hsplit : Aln.card + Anl.card = S.card := Finset.card_filter_add_card_filter_not _
    have hln1 : Aln.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro X hX X' hX'
      exact (lineD_unique D idx hcard (Finset.mem_filter.mp hX).2 (Finset.mem_filter.mp hX').2).symm
    by_cases hA0 : Anl.card = 0
    · omega
    obtain ⟨X0, hX0⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hA0)
    have hAD : ∀ X ∈ Anl, ∃ aL aR : AtV D.toRegionDissection E, ArrData D idx F X aL aR := by
      intro X hX
      have hX' := Finset.mem_filter.mp hX
      exact (hS X hX'.1).resolve_right hX'.2
    choose! aL aR hAD' using hAD
    have hsub : ∀ X ∈ Anl, aR X ∈ Γ := by
      intro X hX
      obtain ⟨-, -, -, -, -, -, -, hg⟩ := hAD' X hX
      simp only [hΓ, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hg
    have hinj : Set.InjOn aR Anl := by
      intro X hX X' hX' h
      exact (arrData_inj_R D idx F (hAD' X hX) (hAD' X' hX') h).symm
    have hle : Anl.card ≤ Γ.card := Finset.card_le_card_of_injOn aR (fun X hX => hsub X hX) hinj
    have hlt' : Anl.card < Γ.card := by
      by_contra hnl
      push Not at hnl
      have himg : Anl.image aR = Γ := by
        apply Finset.eq_of_subset_of_card_le
        · intro g hg
          obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hg
          exact hsub X hX
        · rw [Finset.card_image_of_injOn hinj]; exact hnl
      have hcl : ∀ g ∈ (Γ : Set (AtV D.toRegionDissection E)), ∃ a ∈ (Γ : Set (AtV D.toRegionDissection E)), Par (F.q a) (F.p g) := by
        intro g hg
        have hg' : g ∈ Anl.image aR := by rw [himg]; exact hg
        obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hg'
        obtain ⟨d, hd, hnb, hw, hq, hp, hgL, hgR⟩ := hAD' X hX
        refine ⟨aL X, ?_, hq.trans hp.symm⟩
        simp only [hΓ, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
        exact hgL
      have hg0 : aR X0 ∈ (Γ : Set (AtV D.toRegionDissection E)) := hsub X0 hX0
      have hall := fan_closed F (Γ : Set (AtV D.toRegionDissection E)) hg0 hcl
      obtain ⟨S0, hSS⟩ := hSne
      have hmem : E ∈ (D.tile S0).carrier := (Finset.mem_filter.mp hSS).2.1
      obtain ⟨a, ha, hea⟩ := hall (Sum.inl ⟨S0, hmem⟩)
      have haeq : a = ⟨S0, hmem⟩ := (Sum.inl_injective hea).symm
      subst haeq
      have ha' : IsGam D idx ⟨S0, hmem⟩ := by
        have := Finset.mem_coe.mp ha
        simpa [hΓ, IsGam] using this
      exact isGam_not_strn D idx ha' hSS
    omega

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.exc_capacity_gen
#print axioms Erdos634.Draft.LaczFormal.RG.thru_arr_or_lineD
