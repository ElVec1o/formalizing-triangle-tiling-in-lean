-- Draft/LaczFormalIIcSpoke2.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, step 3 (`spokes_angle`), items (a)+(b): the TWO-SECTOR DATA of a (1,1,0) polygon corner, exported as a standalone lemma `corner_sector_data`.
-- At the corner V = P.v (k+1) with counts (1,1,0) the fan has exactly two tile sectors x (starting along the outgoing side e_{k+1}) and y (ending along the incoming side); r is their common inner ray.  Exported: the two tiles with
-- their boundary TriSteps, corner labels (both in {0,1}, distinct), the sector widths (= model angles) in the form `wd (outgoing side) r`, `wd r (incoming side reversed)`, positivity of the crosses, and (b): ANY direction d along
-- which a maximal-segment division has a tile on BOTH sides at V is parallel to r (so a `GExc` edge at a (1,1,0) corner leaves along the inner ray).  The preamble is a copy of `gexc_start_corner_A` (hypotheses `hout`, `hin` not needed).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2-6.3, Fig. 6), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12GExcCornerA

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

theorem wd_par_left {a b : V2} (h : Par a b) (z : V2) : wd a z = wd b z := by
  obtain ⟨c, hc, rfl⟩ := h.smul
  unfold wd
  have : (⟨dt (c * b.1, c * b.2) z, crs (c * b.1, c * b.2) z⟩ : ℂ) = (c : ℂ) * ⟨dt b z, crs b z⟩ := by
    apply Complex.ext <;> simp [dt, crs] <;> ring
  rw [this, Complex.arg_real_mul _ hc]

theorem wd_par_right {a b : V2} (h : Par a b) (z : V2) : wd z a = wd z b := by
  obtain ⟨c, hc, rfl⟩ := h.smul
  unfold wd
  have : (⟨dt z (c * b.1, c * b.2), crs z (c * b.1, c * b.2)⟩ : ℂ) = (c : ℂ) * ⟨dt z b, crs z b⟩ := by
    apply Complex.ext <;> simp [dt, crs] <;> ring
  rw [this, Complex.arg_real_mul _ hc]

theorem crs_pos_par_left {a b : V2} (h : Par a b) {z : V2} (hz : 0 < crs a z) : 0 < crs b z := by
  obtain ⟨c, hc, rfl⟩ := h.smul
  have : crs (c * b.1, c * b.2) z = c * crs b z := by unfold crs; ring
  rw [this] at hz
  exact (mul_pos_iff_of_pos_left hc).mp hz

theorem crs_pos_par_right {a b : V2} (h : Par a b) {z : V2} (hz : 0 < crs z a) : 0 < crs z b := by
  obtain ⟨c, hc, rfl⟩ := h.smul
  have : crs z (c * b.1, c * b.2) = c * crs z b := by unfold crs; ring
  rw [this] at hz
  exact (mul_pos_iff_of_pos_left hc).mp hz

theorem crs_zero_of_par_par {a b d : V2} (h1 : Par a d) (h2 : Par b d) : crs a b = 0 := by
  obtain ⟨c, hc, rfl⟩ := h1.smul
  obtain ⟨c', hc', rfl⟩ := h2.smul
  unfold crs; ring

set_option maxHeartbeats 12800000 in
/-- **(a)+(b): the two-sector data of a (1,1,0) polygon corner.** -/
theorem corner_sector_data [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (k : Fin M)
    (hc0 : cnt D idx (P.v (k + 1)) 0 = 1) (hc1 : cnt D idx (P.v (k + 1)) 1 = 1) (hc2 : cnt D idx (P.v (k + 1)) 2 = 0) :
    ∃ (r : V2) (jx jy : Fin N) (kx ky : Fin 3) (Uo Ui : Plane),
      r ≠ 0 ∧ TriStep (D.tile jx) (toV2 (P.e (k + 1))) (P.v (k + 1)) Uo ∧ TriStep (D.tile jy) (toV2 (P.e k)) Ui (P.v (k + 1)) ∧
      (D.tile jx).pts kx = P.v (k + 1) ∧ (D.tile jy).pts ky = P.v (k + 1) ∧
      idx jx kx ≠ 2 ∧ idx jy ky ≠ 2 ∧ idx jx kx ≠ idx jy ky ∧
      0 < crs (toV2 (P.e (k + 1))) r ∧ wd (toV2 (P.e (k + 1))) r = D.model.angleAt (idx jx kx) ∧
      0 < crs r (toV2 (P.v k - P.v (k + 1))) ∧ wd r (toV2 (P.v k - P.v (k + 1))) = D.model.angleAt (idx jy ky) ∧
      (∀ d : V2, (∃ i U, TriStep (D.tile i) d (P.v (k + 1)) U) → (∃ i U, TriStep (D.tile i) (neg2 d) U (P.v (k + 1))) → Par r d) := by
  classical
  set V := P.v (k + 1) with hVdef
  have hvert : ∃ j k', (D.tile j).pts k' = V := poly_vertex_is_tile_vertex D.toRegionDissection P hreg (k + 1)
  obtain ⟨pT, qT, F, hpd, hqd, hcr, h1, h2', h3, h4, h5⟩ := fan_vertex_poly D.toRegionDissection P hreg k hvert
  obtain ⟨i0, k0, hk0⟩ := hvert
  have hmem0 : V ∈ (D.tile i0).carrier := hk0 ▸ subset_convexHull ℝ _ ⟨k0, rfl⟩
  have hAt : 0 < Fintype.card (AtV D.toRegionDissection V) := Fintype.card_pos_iff.mpr ⟨⟨i0, hmem0⟩⟩
  obtain ⟨c, hc1', hcn, hadj, hsurjc, hinjc⟩ := corner_chain F hcr h1 h2' h3 h4 h5 hAt
  set n := Fintype.card (AtV D.toRegionDissection V) with hn
  have hsumT := corner_tile_sum D.toRegionDissection F hcr h1 h2' h3 h4
  have hwlt := wd_lt_pi_of_crs_pos hcr
  have hwpos := wd_pos (Or.inl hcr : SecOK pT qT)
  have hnostr : ∀ x : AtV D.toRegionDissection V, ∃ kb, (D.tile x.1).pts kb = V := by
    intro x
    rcases F.hspec x with ⟨kb, hk, -⟩ | ⟨hnv, m', -, -, hq, -⟩
    · exact ⟨kb, hk⟩
    · exfalso
      have hw : wd (F.p x) (F.q x) = Real.pi := by rw [hq]; exact wd_straight (F.hok x).ne_p
      have hle : wd (F.p x) (F.q x) ≤ ∑ y : AtV D.toRegionDissection V, wd (F.p y) (F.q y) :=
        Finset.single_le_sum (f := fun y => wd (F.p y) (F.q y)) (fun y _ => (wd_pos (F.hok y)).le) (Finset.mem_univ x)
      linarith
  have hcrall : ∀ x : AtV D.toRegionDissection V, 0 < crs (F.p x) (F.q x) :=
    fun x => crs_pos_of_corner (F.hok x) (F.hspec x) (hnostr x)
  -- labels of the corner tiles: never gamma
  have hlab_ne2 : ∀ (x : AtV D.toRegionDissection V) (kx : Fin 3), (D.tile x.1).pts kx = V → idx x.1 kx ≠ 2 := by
    intro x kx hkx he
    have := cnt_one D idx 2 hkx he
    omega
  -- n = 2
  have hn2 : n = 2 := by
    have hge : 2 ≤ n := by
      have h0 : 0 < cnt D idx V 0 := by omega
      have h1' : 0 < cnt D idx V 1 := by omega
      unfold cnt at h0 h1'
      obtain ⟨⟨t, a⟩, hta⟩ := Finset.card_pos.mp h0
      obtain ⟨⟨t', a'⟩, hta'⟩ := Finset.card_pos.mp h1'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hta hta'
      have hne : t ≠ t' := by
        rintro rfl
        have : a = a' := (D.tile t).indep.injective (hta.1.trans hta'.1.symm)
        subst this
        have := hta.2.symm.trans hta'.2
        exact absurd this (by decide)
      have hmem : V ∈ (D.tile t).carrier := hta.1 ▸ subset_convexHull ℝ _ ⟨a, rfl⟩
      have hmem' : V ∈ (D.tile t').carrier := hta'.1 ▸ subset_convexHull ℝ _ ⟨a', rfl⟩
      exact Nat.succ_le_of_lt (Fintype.one_lt_card_iff.mpr ⟨⟨t, hmem⟩, ⟨t', hmem'⟩, fun h => hne (congrArg Subtype.val h)⟩)
    have hle : n ≤ 2 := by
      by_contra hgt
      push Not at hgt
      obtain ⟨u, v, w, huv, huw, hvw⟩ := Fintype.two_lt_card_iff.mp hgt
      choose kk hkk using hnostr
      have hl2 : ∀ x, (idx x.1 (kk x)).val ≤ 1 := by
        intro x
        have := hlab_ne2 x (kk x) (hkk x)
        have h2 : (idx x.1 (kk x)).val < 3 := (idx x.1 (kk x)).isLt
        have h3' : (idx x.1 (kk x)).val ≠ 2 := fun e => this (Fin.ext e)
        omega
      have key : ∀ x y : AtV D.toRegionDissection V, x ≠ y → idx x.1 (kk x) = idx y.1 (kk y) → False := by
        intro x y hxy he
        have h2c := cnt_two D idx (idx x.1 (kk x)) (fun e => hxy (Subtype.ext e)) (hkk x) (hkk y) rfl he.symm
        have hlx := hl2 x
        have h01 : idx x.1 (kk x) = 0 ∨ idx x.1 (kk x) = 1 := by
          generalize idx x.1 (kk x) = z at hlx ⊢
          revert z; decide
        rcases h01 with e | e
        · rw [e] at h2c; omega
        · rw [e] at h2c; omega
      have hl : ∀ x, idx x.1 (kk x) = 0 ∨ idx x.1 (kk x) = 1 := by
        intro x
        have hlx := hl2 x
        generalize idx x.1 (kk x) = z at hlx ⊢
        revert z; decide
      rcases hl u with e1 | e1 <;> rcases hl v with e2 | e2 <;> rcases hl w with e3 | e3
      all_goals first
        | exact key u v huv (e1.trans e2.symm)
        | exact key u w huw (e1.trans e3.symm)
        | exact key v w hvw (e2.trans e3.symm)
    omega
  have hc1c : 1 ≤ n := by omega
  set x := c 1 with hx
  set y := c 2 with hy
  have hxy : Par (F.p y) (F.q x) := hadj 1 le_rfl (by omega)
  have hd : F.q x ≠ 0 := (F.hok x).ne_q
  have hnb : NoBack D.toRegionDissection (F.q x) V := noBack_corner F hcr h5 (tile_ray_mem F x).2 hd
  have hcy2 : Par qT (F.q y) := by rw [hy]; have := hcn; rw [hn2] at this; exact this
  obtain ⟨kx, flx, hkx, hpx, hqx⟩ := spec_corner_data (F.hspec x) (hnostr x)
  obtain ⟨ky, fly, hky, hpy, hqy⟩ := spec_corner_data (F.hspec y) (hnostr y)
  have hcx := hcrall x
  have hcy := hcrall y
  -- the two boundary steps
  have hSo : TriStep (D.tile x.1) (toV2 (P.e (k + 1))) V ((D.tile x.1).pts (armP kx flx)) :=
    triStep_of_start kx flx hkx hpx hqx hcx (hc1'.trans hpd)
  have hqe' : Par qT (neg2 (toV2 (P.e k))) := by
    have e : toV2 (P.v k - P.v (k + 1)) = neg2 (toV2 (P.e k)) := by
      unfold neg2 toV2 ConvPoly.e; ext <;> simp
    rw [e] at hqd; exact hqd
  have hSi : TriStep (D.tile y.1) (toV2 (P.e k)) ((D.tile y.1).pts (armQ ky fly)) V := by
    have := triStep_of_end (T := D.tile y.1) (d := neg2 (toV2 (P.e k))) ky fly hky hpy hqy hcy (hcy2.symm.trans hqe')
    rwa [neg2_neg2'] at this
  -- export
  have hxne : x ≠ y := by
    intro h
    have := hinjc 1 2 le_rfl (by omega) (by omega) (by omega) h
    omega
  have hpe : Par (F.p x) (toV2 (P.e (k + 1))) := hc1'.trans hpd
  have hqe2 : Par (F.q y) (toV2 (P.v k - P.v (k + 1))) := hcy2.symm.trans hqd
  have hlx := hlab_ne2 x kx hkx
  have hly := hlab_ne2 y ky hky
  have hnex : idx x.1 kx ≠ idx y.1 ky := by
    intro he
    have h2c := cnt_two D idx (idx x.1 kx) (fun e => hxne (Subtype.ext e)) hkx hky rfl he.symm
    have h0' : cnt D idx V 0 = 1 := hc0
    have h1' : cnt D idx V 1 = 1 := hc1
    have hl : ∀ z : Fin 3, z ≠ 2 → z = 0 ∨ z = 1 := by decide
    rcases hl _ hlx with e | e
    · rw [e, h0'] at h2c; omega
    · rw [e, h1'] at h2c; omega
  have hangx : wd (F.p x) (F.q x) = D.model.angleAt (idx x.1 kx) := by
    rw [F.hwd x, hC.hidxA]
    have e := Tri.localAngle_vertex (D.tile x.1) kx
    rw [hkx] at e
    have e2 : (D.tile x.1).angleAt kx = cornerAngle ((D.tile x.1).pts (kx + 1)) V ((D.tile x.1).pts (kx + 2)) := by
      unfold Tri.angleAt; rw [hkx]
    rw [e2]; exact e
  have hangy : wd (F.p y) (F.q y) = D.model.angleAt (idx y.1 ky) := by
    rw [F.hwd y, hC.hidxA]
    have e := Tri.localAngle_vertex (D.tile y.1) ky
    rw [hky] at e
    have e2 : (D.tile y.1).angleAt ky = cornerAngle ((D.tile y.1).pts (ky + 1)) V ((D.tile y.1).pts (ky + 2)) := by
      unfold Tri.angleAt; rw [hky]
    rw [e2]; exact e
  refine ⟨F.q x, x.1, y.1, kx, ky, _, _, hd, hSo, hSi, hkx, hky, hlx, hly, hnex, crs_pos_par_left hpe hcx, ?_, ?_, ?_, ?_⟩
  · rw [← wd_par_left hpe, hangx]
  · exact crs_pos_par_right hqe2 (crs_pos_par_left hxy hcy)
  · rw [← wd_par_right hqe2, ← wd_par_left hxy, hangy]
  · rintro d ⟨i, U, hT⟩ ⟨i', U', hR⟩
    obtain ⟨x', -, hx'p⟩ := sec_start F hT
    obtain ⟨x'', -, hx''q⟩ := sec_end F hR
    obtain ⟨l, hl1, hl2, hlx'⟩ := hsurjc x'
    have hl : l = 1 ∨ l = 2 := by omega
    rcases hl with rfl | rfl
    · -- x' = x
      rw [← hlx'] at hx'p
      obtain ⟨l2, hl21, hl22, hlx''⟩ := hsurjc x''
      have hl' : l2 = 1 ∨ l2 = 2 := by omega
      rcases hl' with rfl | rfl
      · rw [← hlx'', neg2_neg2'] at hx''q
        have := crs_zero_of_par_par hx'p hx''q
        linarith
      · rw [← hlx'', neg2_neg2'] at hx''q
        have h1 : Par pT d := hc1'.symm.trans hx'p
        have h2 : Par qT d := hcy2.trans hx''q
        have := crs_zero_of_par_par h1 h2
        linarith
    · rw [← hlx'] at hx'p
      exact hxy.symm.trans hx'p

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.corner_sector_data
