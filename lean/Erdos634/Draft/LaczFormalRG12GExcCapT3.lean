-- Draft/LaczFormalRG12GExcCapT3.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2, L9 with straight tiles: `exc_capacity_T`, see `LaczFormalRG12GExcCapT2` for the route and the (non-sharp) constant.  NOTE, UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Sect. 6.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12GExcCapT2

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

theorem isGam_not_strn (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {E : Plane} {a : AtV D.toRegionDissection E}
    (h : IsGam D idx a) : a.1 ∉ Strn D.toRegionDissection E := by
  obtain ⟨k, hk, -⟩ := h
  intro hs
  simp only [Strn, Finset.mem_filter, Finset.mem_univ, true_and] at hs
  exact hs.2 k hk

set_option maxHeartbeats 6400000 in
/-- **L9 with straight tiles**: arrivals at an exceptional point `E` number at most `cnt gamma - cnt alpha + 2 |Strn E|` (the sharp form for `Strn E = empty` is `exc_capacity`). -/
theorem exc_capacity_T [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3)
    {E : Plane} (hE : E ∈ excVerts2 D idx P) :
    ((vtxSet D.toRegionDissection).filter (fun X => GExc D idx X E)).card + cnt D idx E 0 ≤
      cnt D idx E 2 + 2 * (Strn D.toRegionDissection E).card := by
  classical
  by_cases hS : Strn D.toRegionDissection E = ∅
  · have := exc_capacity D P hreg idx hC h1 h3 hE hS
    rw [hS]; simpa using this
  have hSne : (Strn D.toRegionDissection E).Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
  unfold excVerts2 at hE
  simp only [Finset.mem_filter, Finset.mem_sdiff] at hE
  obtain ⟨⟨hEv, hEp⟩, hlt⟩ := hE
  have hvert := mem_vtxSet.mp hEv
  obtain ⟨κ, _, ⟨F⟩⟩ := HasFansC.fans (D := D.toRegionDissection) E hvert
  obtain ⟨j0, k0, hk0⟩ := hvert
  haveI : Nonempty (AtV D.toRegionDissection E) := ⟨⟨j0, hk0 ▸ tile_pt_mem _ k0⟩⟩
  have hp0 := exc_p_zero_of_strn D idx hC.hidxA hC.hregc F hSne hlt
  rw [hp0, add_zero]
  set Aset := (vtxSet D.toRegionDissection).filter (fun X => GExc D idx X E) with hAset
  have hAD : ∀ X ∈ Aset, ∃ (aR : AtV D.toRegionDissection E) (d : V2), ArrR D idx F X aR d :=
    fun X hX => arrR_exists D idx F (Finset.mem_filter.mp hX).2
  choose! aR dd hAD' using hAD
  set Γ : Finset (AtV D.toRegionDissection E) := Finset.univ.filter (fun a => IsGam D idx a) with hΓ
  set SS : Finset (AtV D.toRegionDissection E) := Finset.univ.filter (fun a => a.1 ∈ Strn D.toRegionDissection E) with hSS
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
  have hSScard : SS.card ≤ (Strn D.toRegionDissection E).card := by
    apply Finset.card_le_card_of_injOn (fun a : AtV D.toRegionDissection E => a.1)
    · intro a ha
      simpa [hSS] using ha
    · intro a _ a' _ h
      exact Subtype.ext h
  let ψ : Plane → AtV D.toRegionDissection E × Bool := fun X =>
    (aR X, if IsGam D idx (aR X) then false else if Par (F.p (aR X)) (neg2 (dd X)) then false else true)
  have hmap : ∀ X ∈ Aset, ψ X ∈ (Γ ×ˢ ({false} : Finset Bool)) ∪ (SS ×ˢ (Finset.univ : Finset Bool)) := by
    intro X hX
    obtain ⟨-, -, -, hcls⟩ := hAD' X hX
    by_cases hg : IsGam D idx (aR X)
    · simp only [ψ, hg, if_true, Finset.mem_union, Finset.mem_product, Finset.mem_singleton, and_true]
      left; simpa [hΓ] using hg
    · simp only [ψ, Finset.mem_union, Finset.mem_product, Finset.mem_univ, and_true]
      right
      rcases hcls with ⟨-, hg'⟩ | ⟨hs, -⟩
      · exact absurd hg' hg
      · simpa [hSS] using hs
  have hinj : Set.InjOn ψ Aset := by
    intro X hX X' hX' hψ
    have hX1 := hAD' X hX
    have hX2 := hAD' X' hX'
    simp only [ψ, Prod.mk.injEq] at hψ
    obtain ⟨heq, hbit⟩ := hψ
    have hX2' : ArrR D idx F X' (aR X) (dd X') := by rw [heq]; exact hX2
    by_cases hg : IsGam D idx (aR X)
    · have hl : Par (F.p (aR X)) (neg2 (dd X)) := by
        rcases hX1.2.2.2 with ⟨h, -⟩ | ⟨hs, -⟩
        · exact h
        · exact absurd hs (isGam_not_strn D idx hg)
      have hl' : Par (F.p (aR X)) (neg2 (dd X')) := by
        rcases hX2'.2.2.2 with ⟨h, -⟩ | ⟨hs, -⟩
        · exact h
        · exact absurd hs (isGam_not_strn D idx hg)
      exact (arrR_unique D idx F hX1 hX2' hl hl').symm
    · have hg' : ¬ IsGam D idx (aR X') := by rw [← heq]; exact hg
      simp only [hg, hg', if_false, if_true] at hbit
      have hsX : Par (F.p (aR X)) (neg2 (dd X)) ∨ Par (F.q (aR X)) (neg2 (dd X)) := by
        rcases hX1.2.2.2 with ⟨-, h⟩ | ⟨-, h⟩
        · exact absurd h hg
        · exact h
      have hsX' : Par (F.p (aR X)) (neg2 (dd X')) ∨ Par (F.q (aR X)) (neg2 (dd X')) := by
        rcases hX2'.2.2.2 with ⟨-, h⟩ | ⟨-, h⟩
        · exact absurd h hg
        · exact h
      by_cases c : Par (F.p (aR X)) (neg2 (dd X)) <;> by_cases c' : Par (F.p (aR X')) (neg2 (dd X'))
      · have c'' : Par (F.p (aR X)) (neg2 (dd X')) := by rw [heq]; exact c'
        exact (arrR_unique D idx F hX1 hX2' c c'').symm
      · simp [c, c'] at hbit
      · simp [c, c'] at hbit
      · have hq : Par (F.q (aR X)) (neg2 (dd X)) := hsX.resolve_left c
        have c'' : ¬ Par (F.p (aR X)) (neg2 (dd X')) := by rw [heq]; exact c'
        have hq' : Par (F.q (aR X)) (neg2 (dd X')) := hsX'.resolve_left c''
        exact (arrR_unique D idx F hX1 hX2' hq hq').symm
  have hle := Finset.card_le_card_of_injOn ψ (fun X hX => hmap X hX) hinj
  have hT : ((Γ ×ˢ ({false} : Finset Bool)) ∪ (SS ×ˢ (Finset.univ : Finset Bool))).card ≤ Γ.card + 2 * SS.card := by
    refine (Finset.card_union_le _ _).trans ?_
    simp [Finset.card_product]
    omega
  omega

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.exc_capacity_T
