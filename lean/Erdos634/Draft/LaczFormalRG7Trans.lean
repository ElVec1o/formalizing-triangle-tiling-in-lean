-- Draft/LaczFormalRG7Trans.lean -- Laczkovich DCG 48 (2012), Sect. 4, the transition lemma (the "Lemma 4.5" of the paper, polygon version, parity form):
-- two tiles on the same side of a line with a common vertex `H` on the line, `H` an inner point of a side of a tile on the other side, such that exactly one of the two sides on the line has
-- length `a`  ==>  an edge of `Gamma_a` starts at `H` (no hypothesis that `H` is the head of an edge).  Four variants (both tiles left / right of the line; order `a, not a` or `not a, a`)
-- are covered by two lemmas (`trans_left`, `trans_right`), each with the hypothesis `(a, not a) or (not a, a)`.  Then the `Gamma_c` form (`gc_transition_*`).
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Lemmas 4.2, 4.5), Beeson, Beeson-Zhang; the proof reuses the project's `ga_head_sectors_*`, `head_cfg_edge`.
import Erdos634.Draft.LaczFormalRG5GammaC

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

/-- A head configuration at `H` with an even number of non-`alpha` corners gives an edge (the `key` of `ga_head_out_half`, for `CaseG`). -/
theorem headcfg_edge_half (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) (hG : CaseG D idx)
    {H : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection H κ) {e : V2} {u v s : AtV D.toRegionDissection H}
    (hc : HeadCfg D F e u v s) : ∃ H', GaEdge D.toRegionDissection (slen D 0) H H' := by
  have hc' := hc
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩ := hc'
  have hcyc := F.head_cyc u v s hc1 hc2 hc3 hc4 hc5 hc6
  obtain ⟨hS1, hsum, hcard⟩ := head_counts D idx hG.hidxA F hcyc.1 hc6 hc1
  exact head_cfg_edge D idx hG.hidx hG.hnc hG.hab hG.hac F hc (hG.hhp H hsum)

/-- **Transition lemma, both tiles to the left of the line.**  Tiles `iA` (side `HA -> H`) and `iB` (side `H -> HB`) lie to the left of the direction `d` and have the common vertex `H` on the line;
`H` is an inner point of a side `V' -> V` of the tile `iS` on the other side.  If exactly one of the two sides has length `a`, an edge of `Γ_a` starts at `H`. -/
theorem trans_left (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) (hG : CaseG D idx)
    {d : V2} {HA H HB V V' : Plane} {iA iB iS : Fin N} {σ : ℝ}
    (hSA : TriStep (D.tile iA) d HA H) (hSB : TriStep (D.tile iB) d H HB) (hSS : TriStep (D.tile iS) (neg2 d) V' V)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hHV : H = V + σ • (V' - V))
    (hord : (dist HA H = slen D 0 ∧ dist H HB ≠ slen D 0) ∨ (dist HA H ≠ slen D 0 ∧ dist H HB = slen D 0)) :
    ∃ H', GaEdge D.toRegionDissection (slen D 0) H H' := by
  classical
  have hvert : ∃ j k, (D.tile j).pts k = H := by
    obtain ⟨kk, f, g, hk, hf, -⟩ := id hSB
    exact ⟨iB, kk, hk⟩
  obtain ⟨κ, _, ⟨F⟩⟩ := HasFansC.fans (D := D.toRegionDissection) H hvert
  have hmemA : H ∈ (D.tile iA).carrier := by
    obtain ⟨kk, f, g, hk, hf, -⟩ := id hSA
    rw [← hf]; exact subset_convexHull ℝ _ ⟨f, rfl⟩
  have hmemB : H ∈ (D.tile iB).carrier := by
    obtain ⟨kk, f, g, hk, hf, -⟩ := id hSB
    rw [← hk]; exact subset_convexHull ℝ _ ⟨kk, rfl⟩
  obtain ⟨hmemS, hnvS, hlineS⟩ := step_interior_pt hSS (σ := 1 - σ) (by linarith) (by linarith)
  have hHS : V' + (1 - σ) • (V - V') = H := by rw [hHV]; ext i; simp; ring
  rw [hHS] at hmemS hnvS hlineS
  set a : AtV D.toRegionDissection H := ⟨iA, hmemA⟩
  set b : AtV D.toRegionDissection H := ⟨iB, hmemB⟩
  set s : AtV D.toRegionDissection H := ⟨iS, hmemS⟩
  obtain ⟨kkA, fA, gA, hkA, hfA, hfkA, hgkA, hgfA, hparA, hleftA⟩ := id hSA
  obtain ⟨kk', fl', hk', hp, hq⟩ := spec_corner_data (F.hspec a) ⟨fA, hfA⟩
  have hqa : Par (F.q a) (neg2 d) := triStep_end hSA kk' fl' hk' hp hq (F.hok a)
  have hca : 0 < crs (F.p a) (F.q a) := crs_pos_of_corner (F.hok a) (F.hspec a) ⟨kk', hk'⟩
  have hkkA : kk' = fA := (D.tile iA).indep.injective (hk'.trans hfA.symm)
  have hnA : nsq (F.q a) = dist HA H ^ 2 := by
    have hq' : Par (toV2 ((D.tile iA).pts (armQ kk' fl') - H)) (neg2 d) := hq ▸ hqa
    have hHA : Par (toV2 (HA - H)) (neg2 d) := par_neg_arm hparA
    have := qarm_eq (T := D.tile iA) fl' hk' (W := HA) (w := kkA) hkA (by rw [hkkA]; exact hfkA.symm) hq' hHA
    rw [hq, nsq_toV2_sub, this]
  obtain ⟨kkB, fB, gB, hkB, hfB, hfkB, hgkB, hgfB, hparB, hleftB⟩ := id hSB
  obtain ⟨kk2, fl2, hk2, hp2, hq2⟩ := spec_corner_data (F.hspec b) ⟨kkB, hkB⟩
  have hpb : Par (F.p b) d := triStep_start hSB kk2 fl2 hk2 hp2 hq2 (F.hok b)
  have hcb : 0 < crs (F.p b) (F.q b) := crs_pos_of_corner (F.hok b) (F.hspec b) ⟨kk2, hk2⟩
  have hkkB : kk2 = kkB := (D.tile iB).indep.injective (hk2.trans hkB.symm)
  have hnB : nsq (F.p b) = dist H HB ^ 2 := by
    have hp' : Par (toV2 ((D.tile iB).pts (armP kk2 fl2) - H)) d := hp2 ▸ hpb
    have := parm_eq (T := D.tile iB) fl2 hk2 (W := HB) (w := fB) hfB (by rw [hkkB]; exact hfkB) hp' hparB
    rw [hp2, nsq_toV2_sub, this, dist_comm]
  obtain ⟨hpS, hqS⟩ := straight_dir s (F.hok s) (F.hloc s) (F.hspec s) hnvS hSS hlineS
  have ha2 : 0 ≤ slen D 0 := (slen_pos D 0).le
  have hcfg : HeadCfg D F d a b s := by
    refine ⟨hca, hqa, hcb, hpb, hpS, hqS, ?_⟩
    rcases hord with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨by rw [hnA, h1], by rw [hnB]; exact sq_ne_of_ne dist_nonneg ha2 h2⟩
    · right; exact ⟨by rw [hnA]; exact sq_ne_of_ne dist_nonneg ha2 h1, by rw [hnB, h2]⟩
  exact headcfg_edge_half D idx hG F hcfg

/-- **Transition lemma, both tiles to the right of the line** (steps along `-d`: `iA : H -> HA`, `iB : HB -> H`; `iS` on the left, `V -> V'` along `d`). -/
theorem trans_right (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) (hG : CaseG D idx)
    {d : V2} {HA H HB V V' : Plane} {iA iB iS : Fin N} {σ : ℝ}
    (hSA : TriStep (D.tile iA) (neg2 d) H HA) (hSB : TriStep (D.tile iB) (neg2 d) HB H) (hSS : TriStep (D.tile iS) d V V')
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hHV : H = V + σ • (V' - V))
    (hord : (dist HA H = slen D 0 ∧ dist H HB ≠ slen D 0) ∨ (dist HA H ≠ slen D 0 ∧ dist H HB = slen D 0)) :
    ∃ H', GaEdge D.toRegionDissection (slen D 0) H H' := by
  classical
  have hvert : ∃ j k, (D.tile j).pts k = H := by
    obtain ⟨kk, f, g, hk, hf, -⟩ := id hSA
    exact ⟨iA, kk, hk⟩
  obtain ⟨κ, _, ⟨F⟩⟩ := HasFansC.fans (D := D.toRegionDissection) H hvert
  have hmemA : H ∈ (D.tile iA).carrier := by
    obtain ⟨kk, f, g, hk, hf, -⟩ := id hSA
    rw [← hk]; exact subset_convexHull ℝ _ ⟨kk, rfl⟩
  have hmemB : H ∈ (D.tile iB).carrier := by
    obtain ⟨kk, f, g, hk, hf, -⟩ := id hSB
    rw [← hf]; exact subset_convexHull ℝ _ ⟨f, rfl⟩
  obtain ⟨hmemS, hnvS, hlineS⟩ := step_interior_pt hSS hσ0 hσ1
  rw [← hHV] at hmemS hnvS hlineS
  set a : AtV D.toRegionDissection H := ⟨iA, hmemA⟩
  set b : AtV D.toRegionDissection H := ⟨iB, hmemB⟩
  set s : AtV D.toRegionDissection H := ⟨iS, hmemS⟩
  obtain ⟨kkA, fA, gA, hkA, hfA, hfkA, hgkA, hgfA, hparA, hleftA⟩ := id hSA
  obtain ⟨kk', fl', hk', hp, hq⟩ := spec_corner_data (F.hspec a) ⟨kkA, hkA⟩
  have hpa : Par (F.p a) (neg2 d) := triStep_start hSA kk' fl' hk' hp hq (F.hok a)
  have hca : 0 < crs (F.p a) (F.q a) := crs_pos_of_corner (F.hok a) (F.hspec a) ⟨kk', hk'⟩
  have hkkA : kk' = kkA := (D.tile iA).indep.injective (hk'.trans hkA.symm)
  have hnA : nsq (F.p a) = dist HA H ^ 2 := by
    have hp' : Par (toV2 ((D.tile iA).pts (armP kk' fl') - H)) (neg2 d) := hp ▸ hpa
    have := parm_eq (T := D.tile iA) fl' hk' (W := HA) (w := fA) hfA (by rw [hkkA]; exact hfkA) hp' hparA
    rw [hp, nsq_toV2_sub, this, dist_comm]
  obtain ⟨kkB, fB, gB, hkB, hfB, hfkB, hgkB, hgfB, hparB, hleftB⟩ := id hSB
  obtain ⟨kk2, fl2, hk2, hp2, hq2⟩ := spec_corner_data (F.hspec b) ⟨fB, hfB⟩
  have hqb0 : Par (F.q b) (-(neg2 d).1, -(neg2 d).2) := triStep_end hSB kk2 fl2 hk2 hp2 hq2 (F.hok b)
  have hqb : Par (F.q b) d := by rw [neg2_neg2] at hqb0; exact hqb0
  have hcb : 0 < crs (F.p b) (F.q b) := crs_pos_of_corner (F.hok b) (F.hspec b) ⟨kk2, hk2⟩
  have hkkB : kk2 = fB := (D.tile iB).indep.injective (hk2.trans hfB.symm)
  have hnB : nsq (F.q b) = dist H HB ^ 2 := by
    have hq' : Par (toV2 ((D.tile iB).pts (armQ kk2 fl2) - H)) d := hq2 ▸ hqb
    have hHB : Par (toV2 (HB - H)) d := par_arm_neg hparB
    have := qarm_eq (T := D.tile iB) fl2 hk2 (W := HB) (w := kkB) hkB (by rw [hkkB]; exact Ne.symm hfkB) hq' hHB
    rw [hq2, nsq_toV2_sub, this, dist_comm]
  obtain ⟨hpS, hqS⟩ := straight_dir s (F.hok s) (F.hloc s) (F.hspec s) hnvS hSS hlineS
  have ha2 : 0 ≤ slen D 0 := (slen_pos D 0).le
  have hcfg : HeadCfg D F (neg2 d) b a s := by
    refine ⟨hcb, ?_, hca, hpa, ?_, hqS, ?_⟩
    · rw [neg2_neg2']; exact hqb
    · rw [neg2_neg2']; exact hpS
    · rcases hord with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right; exact ⟨by rw [hnB]; exact sq_ne_of_ne dist_nonneg ha2 h2, by rw [hnA, h1]⟩
      · left; exact ⟨by rw [hnB, h2], by rw [hnA]; exact sq_ne_of_ne dist_nonneg ha2 h1⟩
  exact headcfg_edge_half D idx hG F hcfg

/-- **Transition lemma for `Γ_c`, tiles to the left** (Laczkovich Lemma 4.5, polygon version, in the form used in Lemma 4.6). -/
theorem gc_trans_left (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx)
    {d : V2} {HA H HB V V' : Plane} {iA iB iS : Fin N} {σ : ℝ}
    (hSA : TriStep (D.tile iA) d HA H) (hSB : TriStep (D.tile iB) d H HB) (hSS : TriStep (D.tile iS) (neg2 d) V' V)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hHV : H = V + σ • (V' - V))
    (hord : (dist HA H = slen D 2 ∧ dist H HB ≠ slen D 2) ∨ (dist HA H ≠ slen D 2 ∧ dist H HB = slen D 2)) :
    ∃ H', GcEdge D H H' := by
  haveI : HasFansC (relabelC D).toRegionDissection := (inferInstance : HasFansC D.toRegionDissection)
  rw [← relabelC_slen0 D] at hord
  obtain ⟨H', hH'⟩ := trans_left (relabelC D) (relabelCIdx idx) h.caseG hSA hSB hSS hσ0 hσ1 hHV hord
  exact ⟨H', (gcEdge_iff D H H').mpr hH'⟩

/-- **Transition lemma for `Γ_c`, tiles to the right.** -/
theorem gc_trans_right (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx)
    {d : V2} {HA H HB V V' : Plane} {iA iB iS : Fin N} {σ : ℝ}
    (hSA : TriStep (D.tile iA) (neg2 d) H HA) (hSB : TriStep (D.tile iB) (neg2 d) HB H) (hSS : TriStep (D.tile iS) d V V')
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hHV : H = V + σ • (V' - V))
    (hord : (dist HA H = slen D 2 ∧ dist H HB ≠ slen D 2) ∨ (dist HA H ≠ slen D 2 ∧ dist H HB = slen D 2)) :
    ∃ H', GcEdge D H H' := by
  haveI : HasFansC (relabelC D).toRegionDissection := (inferInstance : HasFansC D.toRegionDissection)
  rw [← relabelC_slen0 D] at hord
  obtain ⟨H', hH'⟩ := trans_right (relabelC D) (relabelCIdx idx) h.caseG hSA hSB hSS hσ0 hσ1 hHV hord
  exact ⟨H', (gcEdge_iff D H H').mpr hH'⟩

end Erdos634.Draft.LaczFormal.RG
