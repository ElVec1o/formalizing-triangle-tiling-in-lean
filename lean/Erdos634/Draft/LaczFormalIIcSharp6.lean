-- Draft/LaczFormalIIcSharp6.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2-6.3, repair of the hStrn gap (AI assistant plan IIC_STRN.md, S6): BOUNDARY capacity.  An exceptional point `E` that is not an interior point of the region (so it lies in the open
-- side of the polygon) has `Strn E = empty` (`Asum + pi |Strn| = pi`, `Asum > 0`), `cnt alpha = 0`, and (#arrivals) + cnt alpha + 1 <= cnt gamma: the fan from `fan_open_edge` has the virtual exterior sector, which a predecessor-closed `Gamma` cannot contain (`fan_closed`).
-- So at a boundary exceptional point the capacity is `k - 1` (AI assistant Sect. 2.4 / step 6 of Lemma 6.3: both exceptional points are INTERIOR once each receives `k` arrivals).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2-6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcSharp4
import Erdos634.Draft.LaczFormalRGBdy2
import Erdos634.Draft.LaczFormalBZ1

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

set_option maxHeartbeats 6400000 in
/-- **S6: boundary capacity of an exceptional point** (an exceptional point of the region's boundary receives at most `cnt gamma - 1` edges). -/
theorem exc_capacity_boundary [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3)
    {E : Plane} (hE : E ∈ excVerts2 D idx P) (hb : E ∉ interior D.region) :
    ((vtxSet D.toRegionDissection).filter (fun X => GExc D idx X E)).card + cnt D idx E 0 + 1 ≤ cnt D idx E 2 := by
  classical
  have hE0 := hE
  unfold excVerts2 at hE
  simp only [Finset.mem_filter, Finset.mem_sdiff] at hE
  obtain ⟨⟨hEv, hEp⟩, hlt⟩ := hE
  have hvert := mem_vtxSet.mp hEv
  have hnc : ∀ k : Fin M, E ≠ P.v (k + 1) := fun k hk => hEp (mem_polyVerts.mpr ⟨k, hk⟩)
  rcases point_cases D.toRegionDissection P hreg hvert with h | ⟨i, t, ht0, ht1, hXt⟩ | ⟨k, hXk⟩
  · exact absurd h hb
  swap
  · exact absurd hXk (hnc k)
  subst hXt
  set E : Plane := (1 - t) • P.v i + t • P.v (i + 1) with hEdef
  have hApos := Asum_pos D idx hvert
  obtain ⟨pT, F, hpd, hpe, hqe, hTgt⟩ := fan_open_edge D.toRegionDissection P hreg i ht0 ht1 hvert
  obtain ⟨j0, k0, hk0⟩ := id hvert
  haveI : Nonempty (AtV D.toRegionDissection E) := ⟨⟨j0, hk0 ▸ tile_pt_mem _ k0⟩⟩
  have hpT : pT ≠ 0 := hpd.ne_left
  have hang := head_angle_sum_gen D idx hC.hidxA F
  have hvirt : ∑ j : Unit, wd (F.pe j) (F.qe j) = Real.pi := by
    rw [Fintype.sum_unique]
    show wd (F.pe ()) (F.qe ()) = Real.pi
    rw [hpe, hqe, wd_ext hpT]
  rw [hvirt] at hang
  have hpi := Real.pi_pos
  have hAe : Asum D idx E + Real.pi * ((Strn D.toRegionDissection E).card : ℝ) = Real.pi := by
    unfold Asum; linarith
  have hStrn : Strn D.toRegionDissection E = ∅ := by
    rcases Nat.eq_zero_or_pos (Strn D.toRegionDissection E).card with h0 | h0
    · exact Finset.card_eq_zero.mp h0
    · exfalso
      have : (1 : ℝ) ≤ (Strn D.toRegionDissection E).card := by exact_mod_cast h0
      nlinarith
  rw [hStrn] at hAe
  simp only [Finset.card_empty, Nat.cast_zero, mul_zero, add_zero] at hAe
  -- cnt alpha = 0
  have hγ := model_angle_pos' D 2
  have hAs : Asum D idx E = (cnt D idx E 0 : ℝ) * (Real.pi - D.model.angleAt 2) + (cnt D idx E 2 : ℝ) * D.model.angleAt 2 := Asum_eq D idx hC.hregc E
  have hlt' : (cnt D idx E 0 : ℝ) + 1 ≤ cnt D idx E 2 := by exact_mod_cast hlt
  have hp0 : cnt D idx E 0 = 0 := by
    by_contra hne
    have h1' : (1 : ℝ) ≤ cnt D idx E 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
    nlinarith
  rw [hp0, add_zero]
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
  have hcpos : 1 ≤ cnt D idx E 2 := by omega
  by_cases hA0 : Aset.card = 0
  · omega
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
  have hlt2 : Aset.card < Γ.card := by
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
    obtain ⟨a, -, hea⟩ := hall (Sum.inr ())
    exact Sum.inr_ne_inl hea
  omega

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.exc_capacity_boundary
