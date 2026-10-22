-- Draft/LaczFormalIIcIsoG.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2, Case IIc with alpha = beta: the end of an edge of Gamma_except.
--  `sc1_core_iso`/`sc1_wrap_iso` : an interior (2,2,2) vertex that is the head of a left and a right gamma tile and ends the gamma run is IMPOSSIBLE for alpha = beta (False): the window (gamma, alpha, alpha)
--     after the adjacent gamma pair is straight (`straight_of_run_iso`), and the printed branch "a tile along the straight line has gamma at its far end, contradicting the maximality of the run" applies without the
--     case split l(m+1) = l(m+2) of the generic `sc1_core`.
--  `gexc_end_kite_or_exc_iso` : the end of every Gamma_except edge is an exceptional point (`excVerts2`);  `gexc_end_cls_iso` : same conclusion shape as `gexc_end_cls` (Or.inr).
-- Bodies are those of `sc1_core`, `sc1_wrap`, `gexc_end_kite_or_exc` with `AngGen` replaced by `AngGenI` and the kite branch removed.  Originals NOT edited.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2-6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcIsoF

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

set_option maxHeartbeats 6400000 in
/-- **Statement (ii), the case of two `gamma` heads at an interior (2,2,2) vertex.** -/
theorem sc1_core_iso [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGenI (fun l => D.model.angleAt l))
    {Y : Plane} {d : V2} (hYi : Y ∈ interior D.region)
    (c0 : cnt D idx Y 0 = 2) (c1 : cnt D idx Y 1 = 2) (c2 : cnt D idx Y 2 = 2)
    {iL iR : Fin N} {A A' : Plane} (hL : TriStep (D.tile iL) d A Y) (hLg : ∃ k, (D.tile iL).pts k = Y ∧ idx iL k = 2)
    (hR : TriStep (D.tile iR) (neg2 d) Y A') (hRg : ∃ k, (D.tile iR).pts k = Y ∧ idx iR k = 2)
    (hcont : (∀ i U', TriStep (D.tile i) d Y U' → ¬ ∃ k, (D.tile i).pts k = U' ∧ idx i k = 2) ∨
      (∀ i U', TriStep (D.tile i) (neg2 d) U' Y → ¬ ∃ k, (D.tile i).pts k = U' ∧ idx i k = 2)) :
    False := by
  classical
  obtain ⟨F, s, ℓ, hF, hlab, hsurj, hperS⟩ := fan222_tile_iso D idx hC.hidxA hYi c0 c1 c2 G
  have hpar : ∀ j, Par (F.p (s (j + 1))) (F.q (s j)) := fun j => hF.hpar j
  have hperL : ∀ n, ℓ (n + 6) = ℓ n := by
    intro n
    obtain ⟨k, hk, -⟩ := hlab n
    have hk' : (D.tile (s (n + 6)).1).pts k = Y := by rw [hperS n]; exact hk
    have h1' := label_eq hlab (j := n + 6) rfl hk'
    have h2' := label_eq hlab (j := n) rfl hk
    rw [← h1', ← h2', hperS n]
  obtain ⟨pf, qf, kk, fl, S⟩ := secData_exists D idx F s ℓ hlab
  have hp0 : ∀ m, F.p (s m) ≠ 0 := fun m => (F.hok (s m)).ne_p
  have hq0 : ∀ m, F.q (s m) ≠ 0 := fun m => (F.hok (s m)).ne_q
  -- the two adjacent gamma sectors
  obtain ⟨x1, hx1i, hx1q⟩ := sec_end F hL
  obtain ⟨x2, hx2i, hx2p⟩ := sec_start F hR
  obtain ⟨a, -, hsa⟩ := hsurj x1
  have hx2 : x2 = s (a + 1) := next_sector F s hpar (j := a) (r := neg2 d) (by rw [hsa]; exact hx1q) hx2p
  have hia : (s a).1 = iL := by rw [hsa]; exact hx1i
  have hia1 : (s (a + 1)).1 = iR := by rw [← hx2]; exact hx2i
  obtain ⟨kL, hkL, hkL2⟩ := hLg
  obtain ⟨kR, hkR, hkR2⟩ := hRg
  have hla : ℓ a = 2 := (label_eq hlab (j := a) hia hkL).symm.trans hkL2
  have hla1 : ℓ (a + 1) = 2 := (label_eq hlab (j := a + 1) hia1 hkR).symm.trans hkR2
  have hps : Par (F.p (s (a + 1))) (neg2 d) := by rw [← hx2]; exact hx2p
  have h5 : ℓ (a + 1 + 5) = 2 := by rw [show a + 1 + 5 = a + 6 by ring, hperL a]; exact hla
  have hcnt : ((Finset.range 6).filter (fun i => ℓ (a + 1 + i) = 2)).card = 2 := hF.hcnt (a + 1) 2
  have hM : ∀ n, (ℓ n ≠ 2 ∧ qf n ≠ 2) ↔ (ℓ (n + 1) ≠ 2 ∧ pf (n + 1) ≠ 2) := fun n =>
    fan_match D P hreg idx hC hab hac hYi F s hpar S n
  obtain ⟨l1, l2, l3, hq1, hp2, hq2, hpf3⟩ := sc1_comb ℓ pf qf (a + 1) (fun n => S.perm n) hcnt hla1 h5 (hM (a + 1)) (hM (a + 1 + 1)) (hM (a + 1 + 2))
  set m := a + 1 with hm
  -- alpha = beta: the window (gamma, alpha, alpha) at `m` is straight whatever the labels `m+1, m+2` are
  have hwin : (Finset.range 3).filter (fun i => ℓ (m + i) = 2) = {0} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hi, h⟩
      interval_cases i
      · rfl
      · exact absurd h l1
      · exact absurd h l2
    · rintro rfl
      exact ⟨by norm_num, by simpa using hla1⟩
  have hcard : ((Finset.range 3).filter (fun i => ℓ (m + i) = 2)).card = 1 := by rw [hwin]; rfl
  have hopp := straight_of_run_iso G.toAngGen' G.eq01 hF m hcard
  have hpd : Par (F.p (s (m + 3))) d := by
    have := par_neg hps
    rw [neg2_neg2] at this
    exact hopp.trans this
  have hl3 : TriStep (D.tile (s (m + 3)).1) d Y ((D.tile (s (m + 3)).1).pts (armP (kk (m + 3)) (fl (m + 3)))) :=
    triStep_of_start (kk (m + 3)) (fl (m + 3)) (S.hk (m + 3)) (S.hp (m + 3)) (S.hq (m + 3)) (S.crs_pos (m + 3)) hpd
  have hqd : Par (F.q (s (m + 2))) d := (hpar (m + 2)).symm.trans hpd
  have hr2 : TriStep (D.tile (s (m + 2)).1) (neg2 d) ((D.tile (s (m + 2)).1).pts (armQ (kk (m + 2)) (fl (m + 2)))) Y :=
    triStep_of_end (kk (m + 2)) (fl (m + 2)) (S.hk (m + 2)) (S.hp (m + 2)) (S.hq (m + 2)) (S.crs_pos (m + 2)) hqd
  exfalso
  rcases hcont with hc | hc
  · exact hc _ _ hl3 ⟨armP (kk (m + 3)) (fl (m + 3)), rfl, by rw [S.hpf]; exact hpf3⟩
  · exact hc _ _ hr2 ⟨armQ (kk (m + 2)) (fl (m + 2)), rfl, by rw [S.hqf]; exact hq2⟩

set_option maxHeartbeats 6400000 in
/-- **The case of two `gamma` heads**: `Y` interior (2,2,2) and `sc1_core_iso`. -/
theorem sc1_wrap_iso [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGenI (fun l => D.model.angleAt l))
    {Y : Plane} {d : V2} (hvert : ∃ j k, (D.tile j).pts k = Y) (hnc : ∀ k : Fin M, Y ≠ P.v (k + 1)) (hnorm : cnt D idx Y 0 = cnt D idx Y 2)
    {iL iR : Fin N} {A A' : Plane} (hL : TriStep (D.tile iL) d A Y) (hLg : ∃ k, (D.tile iL).pts k = Y ∧ idx iL k = 2)
    (hR : TriStep (D.tile iR) (neg2 d) Y A') (hRg : ∃ k, (D.tile iR).pts k = Y ∧ idx iR k = 2)
    (hcont : (∀ i U', TriStep (D.tile i) d Y U' → ¬ ∃ k, (D.tile i).pts k = U' ∧ idx i k = 2) ∨
      (∀ i U', TriStep (D.tile i) (neg2 d) U' Y → ¬ ∃ k, (D.tile i).pts k = U' ∧ idx i k = 2)) :
    False := by
  classical
  have hij : iL ≠ iR := fun h => by subst h; exact triStep_lr_false hL hR
  obtain ⟨kL, hkL, hkL2⟩ := hLg
  obtain ⟨kR, hkR, hkR2⟩ := hRg
  have h2c : 2 ≤ cnt D idx Y 2 := two_le_cnt hij hkL hkL2 hkR hkR2
  obtain ⟨-, -, hn⟩ := caseII_nonpoly D P hreg idx hC.hidxA hC.hregc h1 h3 hvert hnc
  have hint : Y ∈ interior D.region := by
    by_contra hni
    have := hn hnorm.symm hni
    omega
  obtain ⟨F⟩ := extFan_interior D.toRegionDissection Y hvert hint
  have hang := head_angle_sum D idx hC.hidxA F inferInstance
  rw [Fin.sum_univ_three, hnorm, ← hC.hregc Y, hnorm] at hang
  have hs := G.sum
  have hp := Real.pi_pos
  simp only at hs
  have h2R : (2 : ℝ) ≤ (cnt D idx Y 2 : ℝ) := by exact_mod_cast h2c
  have hk0 : (0 : ℝ) ≤ ((Strn D.toRegionDissection Y).card : ℝ) := Nat.cast_nonneg _
  have hle : (cnt D idx Y 2 : ℝ) ≤ 2 := by nlinarith
  have hc2 : cnt D idx Y 2 = 2 := by
    have : cnt D idx Y 2 ≤ 2 := by exact_mod_cast hle
    omega
  have c0 : cnt D idx Y 0 = 2 := by rw [hnorm]; exact hc2
  have c1 : cnt D idx Y 1 = 2 := by rw [← hC.hregc Y]; exact c0
  exact sc1_core_iso D P hreg idx hC hab hac h1 h3 G hint c0 c1 hc2 hL ⟨kL, hkL, hkL2⟩ hR ⟨kR, hkR, hkR2⟩ hcont

/-- **L7: statement (ii) of Lemma 6.2 for `Gamma_except`.** -/
theorem gexc_end_kite_or_exc_iso [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGenI (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0) {X Y : Plane} (hE : GExc D idx X Y) :
    Y ∈ excVerts2 D idx P := by
  classical
  obtain ⟨d, hd, EL, ER, hrun⟩ := gexc_end_split D idx hE
  -- a gamma corner at Y
  obtain ⟨i0, k0, hk0, hk02⟩ : ∃ i k, (D.tile i).pts k = Y ∧ idx i k = 2 := by
    rcases hrun with ⟨⟨iL, A, hL, hLg⟩, -⟩ | ⟨⟨iR, A, hR, hRg⟩, -⟩
    · exact ⟨iL, hLg.choose, hLg.choose_spec⟩
    · exact ⟨iR, hRg.choose, hRg.choose_spec⟩
  have hvert : ∃ j k, (D.tile j).pts k = Y := ⟨i0, k0, hk0⟩
  have hcnt2 : 0 < cnt D idx Y 2 := cnt_pos_of_corner hk0 hk02
  have hnc : ∀ k : Fin M, Y ≠ P.v (k + 1) := by
    intro k hk
    have := (hcor (k + 1)).2.2
    rw [← hk] at this
    omega
  obtain ⟨hle, -, -⟩ := caseII_nonpoly D P hreg idx hC.hidxA hC.hregc h1 h3 hvert hnc
  by_cases hlt : cnt D idx Y 0 < cnt D idx Y 2
  · unfold excVerts2
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    exact ⟨⟨mem_vtxSet.mpr hvert, fun hp => by obtain ⟨k, hk⟩ := mem_polyVerts.mp hp; exact hnc k hk⟩, hlt⟩
  · exfalso
    have hnorm : cnt D idx Y 0 = cnt D idx Y 2 := by omega
    rcases hrun with ⟨⟨iL0, A0, hL0, hLg0⟩, hcL⟩ | ⟨⟨iR0, A0, hR0, hRg0⟩, hcR⟩
    · obtain ⟨iR, A', B', hR, hcase⟩ := ER
      rcases hcase with ⟨hYB, hRg⟩ | hin
      · rw [← hYB] at hR
        exact sc1_wrap_iso D P hreg idx hC hab hac h1 h3 G hvert hnc hnorm hL0 hLg0 hR hRg (Or.inl hcL)
      · exact (sc2_left_iso D P hreg idx hC hab hac G hnorm hL0 hLg0 hR hin hcL).elim
    · obtain ⟨iL, A', B', hL, hcase⟩ := EL
      rcases hcase with ⟨hYB, hLg⟩ | hin
      · rw [← hYB] at hL
        exact sc1_wrap_iso D P hreg idx hC hab hac h1 h3 G hvert hnc hnorm hL hLg hR0 hRg0 (Or.inr hcR)
      · exact (sc2_right_iso D P hreg idx hC hab hac G hnorm hR0 hRg0 hL hin hcR).elim

/-- **Every end of an edge of Gamma_except is exceptional (alpha = beta)**; conclusion in the shape of `gexc_end_cls`. -/
theorem gexc_end_cls_iso [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGenI (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0) {X Y : Plane} (hE : GExc D idx X Y) :
    Y ∈ kiteB D idx ∨ Y ∈ excVerts2 D idx P :=
  Or.inr (gexc_end_kite_or_exc_iso D P hreg idx hC hab hac h1 h3 G hcor hE)

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.sc1_core_iso
#print axioms Erdos634.Draft.LaczFormal.RG.sc1_wrap_iso
#print axioms Erdos634.Draft.LaczFormal.RG.gexc_end_kite_or_exc_iso
#print axioms Erdos634.Draft.LaczFormal.RG.gexc_end_cls_iso
