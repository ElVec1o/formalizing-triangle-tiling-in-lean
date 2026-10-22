-- Draft/LaczFormalRG12GExcCapMain.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2, lemma L9 `exc_capacity`: the number of edges of Gamma_except arriving at an exceptional point `E` with no straight tile at `E` is at most `cnt gamma - cnt alpha`.
-- See `LaczFormalRG12GExcCap` for the route and the NAMED PRINT GAP (interior T-junction exceptional points).  NOTE, UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Sect. 6.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12GExcCap

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

set_option maxHeartbeats 6400000 in
/-- **L9: capacity of an exceptional point.**  Arrivals at `E` number at most `cnt gamma - cnt alpha` (`r - p`). -/
theorem exc_capacity [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3)
    {E : Plane} (hE : E ∈ excVerts2 D idx P) (hStrn : Strn D.toRegionDissection E = ∅) :
    ((vtxSet D.toRegionDissection).filter (fun X => GExc D idx X E)).card + cnt D idx E 0 ≤ cnt D idx E 2 := by
  classical
  unfold excVerts2 at hE
  simp only [Finset.mem_filter, Finset.mem_sdiff] at hE
  obtain ⟨⟨hEv, hEp⟩, hlt⟩ := hE
  have hvert := mem_vtxSet.mp hEv
  have hnc : ∀ k : Fin M, E ≠ P.v (k + 1) := fun k hk => hEp (mem_polyVerts.mpr ⟨k, hk⟩)
  have hp1 := exc_cnt0_le_one D P hreg idx hC.hidxA hC.hregc h1 h3 hvert hnc hlt
  obtain ⟨κ, _, ⟨F⟩⟩ := HasFansC.fans (D := D.toRegionDissection) E hvert
  obtain ⟨j0, k0, hk0⟩ := hvert
  haveI : Nonempty (AtV D.toRegionDissection E) := ⟨⟨j0, hk0 ▸ tile_pt_mem _ k0⟩⟩
  set Aset := (vtxSet D.toRegionDissection).filter (fun X => GExc D idx X E) with hAset
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
  by_cases hA0 : Aset.card = 0
  · rw [hA0]; omega
  obtain ⟨X0, hX0⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hA0)
  have hAD : ∀ X ∈ Aset, ∃ aL aR : AtV D.toRegionDissection E, ArrData D idx F X aL aR :=
    fun X hX => arrData_exists D idx F hStrn (Finset.mem_filter.mp hX).2
  choose! aL aR hAD' using hAD
  have hsub : ∀ X ∈ Aset, aR X ∈ Γ := by
    intro X hX
    obtain ⟨-, -, -, -, -, -, -, hg⟩ := hAD' X hX
    simp only [hΓ, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hg
  have hinj : Set.InjOn aR Aset := by
    intro X hX X' hX' h
    exact (arrData_inj_R D idx F (hAD' X hX) (hAD' X' hX') h).symm
  have hle : Aset.card ≤ Γ.card := Finset.card_le_card_of_injOn aR (fun X hX => hsub X hX) hinj
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hp1 with hp0 | hp1'
  · rw [hp0]; omega
  · rw [hp1']
    have hlt' : Aset.card < Γ.card := by
      by_contra hnl
      push Not at hnl
      have himg : Aset.image aR = Γ := by
        apply Finset.eq_of_subset_of_card_le
        · intro g hg
          obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hg
          exact hsub X hX
        · rw [Finset.card_image_of_injOn hinj]; exact hnl
      have hcl : ∀ g ∈ (Γ : Set (AtV D.toRegionDissection E)), ∃ a ∈ (Γ : Set (AtV D.toRegionDissection E)), Par (F.q a) (F.p g) := by
        intro g hg
        have hg' : g ∈ Aset.image aR := by rw [himg]; exact hg
        obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hg'
        obtain ⟨d, hd, hnb, hw, hq, hp, hgL, hgR⟩ := hAD' X hX
        refine ⟨aL X, ?_, hq.trans hp.symm⟩
        simp only [hΓ, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
        exact hgL
      have hg0 : aR X0 ∈ (Γ : Set (AtV D.toRegionDissection E)) := hsub X0 hX0
      have hall := fan_closed F (Γ : Set (AtV D.toRegionDissection E)) hg0 hcl
      -- an alpha corner at E
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

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.exc_capacity
