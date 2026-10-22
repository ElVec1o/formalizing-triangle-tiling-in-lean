-- Draft/LaczFormalIIcSharp4.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2-6.3, repair of the hStrn gap (AI assistant plan IIC_STRN.md, S4): the SHARP capacity `exc_capacity_sharp`, with or without straight tiles:
--     (#edges of Gamma_except arriving at an exceptional point E) + cnt alpha <= cnt gamma.
-- Route: `Strn E = empty`: `exc_capacity`.  Else `cnt alpha = 0` and `|Strn E| <= 1`; arrivals split into `LineD` (at most one, S3) and the others (`ArrData`: injection `aR` into the `gamma` sectors `Gamma`, as in L9);
-- if the others filled `Gamma`, `Gamma` would be closed under predecessor (`fan_closed`), hence contain the straight sector of the tile in `Strn E`, which is not a `gamma` sector.  So the others number `<= |Gamma| - 1`, total `<= |Gamma| <= cnt gamma`.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2-6.3, Lemmas 4.4-4.8), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcSharp3

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

set_option maxHeartbeats 6400000 in
/-- **S4: sharp capacity of an exceptional point** (no `hStrn`). -/
theorem exc_capacity_sharp [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3)
    {E : Plane} (hE : E ∈ excVerts2 D idx P) :
    ((vtxSet D.toRegionDissection).filter (fun X => GExc D idx X E)).card + cnt D idx E 0 ≤ cnt D idx E 2 := by
  classical
  by_cases hS : Strn D.toRegionDissection E = ∅
  · exact exc_capacity D P hreg idx hC h1 h3 hE hS
  have hSne : (Strn D.toRegionDissection E).Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
  unfold excVerts2 at hE
  simp only [Finset.mem_filter, Finset.mem_sdiff] at hE
  obtain ⟨⟨hEv, hEp⟩, hlt⟩ := hE
  have hvert := mem_vtxSet.mp hEv
  obtain ⟨κ, _, ⟨F⟩⟩ := HasFansC.fans (D := D.toRegionDissection) E hvert
  obtain ⟨j0, k0, hk0⟩ := hvert
  haveI : Nonempty (AtV D.toRegionDissection E) := ⟨⟨j0, hk0 ▸ tile_pt_mem _ k0⟩⟩
  have hp0 := exc_p_zero_of_strn D idx hC.hidxA hC.hregc F hSne hlt
  have hcard := strn_card_le_one D idx hC.hidxA hC.hregc h1 F hlt
  rw [hp0, add_zero]
  set Aset := (vtxSet D.toRegionDissection).filter (fun X => GExc D idx X E) with hAset
  set Aln := Aset.filter (fun X => LineD D idx X E) with hAln
  set Anl := Aset.filter (fun X => ¬ LineD D idx X E) with hAnl
  have hsplit : Aln.card + Anl.card = Aset.card := Finset.card_filter_add_card_filter_not _
  have hln1 : Aln.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro X hX X' hX'
    exact (lineD_unique D idx hcard (Finset.mem_filter.mp hX).2 (Finset.mem_filter.mp hX').2).symm
  set Γ : Finset (AtV D.toRegionDissection E) := Finset.univ.filter (fun a => IsGam D idx a) with hΓ
  have hΓcard : Γ.card ≤ cnt D idx E 2 := by
    unfold cnt
    apply Finset.card_le_card_of_injOn (fun a : AtV D.toRegionDissection E => (a.1, if h : ∃ k, (D.tile a.1).pts k = E ∧ idx a.1 k = 2 then h.choose else 0))
    · intro a ha
      have hg : ∃ k, (D.tile a.1).pts k = E ∧ idx a.1 k = 2 := by
        have := Finset.mem_coe.mp ha
        simpa [hΓ, IsGam] using this
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, dif_pos hg]
      exact hg.choose_spec
    · intro a _ a' _ h
      exact Subtype.ext (congrArg Prod.fst h)
  by_cases hA0 : Anl.card = 0
  · omega
  obtain ⟨X0, hX0⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hA0)
  have hAD : ∀ X ∈ Anl, ∃ aL aR : AtV D.toRegionDissection E, ArrData D idx F X aL aR := by
    intro X hX
    have hX' := Finset.mem_filter.mp hX
    exact (arrData_or_lineD D idx F (Finset.mem_filter.mp hX'.1).2).resolve_right hX'.2
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
    obtain ⟨S, hSS⟩ := hSne
    have hmem : E ∈ (D.tile S).carrier := (Finset.mem_filter.mp hSS).2.1
    obtain ⟨a, ha, hea⟩ := hall (Sum.inl ⟨S, hmem⟩)
    have haeq : a = ⟨S, hmem⟩ := (Sum.inl_injective hea).symm
    subst haeq
    have ha' : IsGam D idx ⟨S, hmem⟩ := by
      have := Finset.mem_coe.mp ha
      simpa [hΓ, IsGam] using this
    exact isGam_not_strn D idx ha' hSS
  omega

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.exc_capacity_sharp
