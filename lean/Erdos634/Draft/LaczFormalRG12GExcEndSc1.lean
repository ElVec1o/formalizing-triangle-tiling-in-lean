-- Draft/LaczFormalRG12GExcEndSc1.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2, Gamma_except, lemma L7 (statement (ii)), STEP 3: the case where `Y` is the head of a left AND a right tile with `gamma` at `Y` (the paper's "second case"),
-- at an interior (2,2,2) vertex.  The two `gamma` sectors are adjacent (common ray `-d`).  `sc1_comb` is the pure label combinatorics (Lemma 4.8 on the four rays after the `gamma` pair); `sc1_core` concludes that either the next
-- ray is a straight line and a tile starting along it has `gamma` at its far end (contradicting the maximality of the run), or the next pair is a kite and `Y` is a vertex of Gamma_kite.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12GExcEndFan

namespace Erdos634.Draft.LaczFormal.RG

set_option synthInstance.maxSize 4000 in
theorem fin3_other_two : ∀ a b c : Fin 3, a ≠ b → a ≠ c → b ≠ c → a ≠ 2 → b ≠ 2 → c = 2 := by decide
set_option synthInstance.maxSize 4000 in
theorem fin3_other_not_two : ∀ a b c : Fin 3, a ≠ b → a ≠ c → b ≠ c → b = 2 → c ≠ 2 := by decide
set_option synthInstance.maxSize 4000 in
theorem fin3_01 : ∀ a b : Fin 3, a ≠ b → a ≠ 2 → b ≠ 2 → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by decide

end Erdos634.Draft.LaczFormal.RG

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

/-- **Label combinatorics after an adjacent `gamma` pair** (pure): the four sectors `m+1, .., m+4` are not `gamma`; `m+1` has its `p`-side not `c`, so its `q`-side is `c`, matched by the `p`-side of `m+2`, whose `q`-side is not `c`,
so the `p`-side of `m+3` is not `c`. -/
theorem sc1_comb (ℓ pf qf : ℕ → Fin 3) (m : ℕ) (hperm : ∀ n, ℓ n ≠ pf n ∧ ℓ n ≠ qf n ∧ pf n ≠ qf n)
    (hcnt : ((Finset.range 6).filter (fun i => ℓ (m + i) = 2)).card = 2) (h0 : ℓ m = 2) (h5 : ℓ (m + 5) = 2)
    (M0 : (ℓ m ≠ 2 ∧ qf m ≠ 2) ↔ (ℓ (m + 1) ≠ 2 ∧ pf (m + 1) ≠ 2))
    (M1 : (ℓ (m + 1) ≠ 2 ∧ qf (m + 1) ≠ 2) ↔ (ℓ (m + 2) ≠ 2 ∧ pf (m + 2) ≠ 2))
    (M2 : (ℓ (m + 2) ≠ 2 ∧ qf (m + 2) ≠ 2) ↔ (ℓ (m + 3) ≠ 2 ∧ pf (m + 3) ≠ 2)) :
    ℓ (m + 1) ≠ 2 ∧ ℓ (m + 2) ≠ 2 ∧ ℓ (m + 3) ≠ 2 ∧ qf (m + 1) ≠ 2 ∧ pf (m + 2) ≠ 2 ∧ qf (m + 2) = 2 ∧ pf (m + 3) = 2 := by
  have hne : ∀ i, 1 ≤ i → i ≤ 4 → ℓ (m + i) ≠ 2 := by
    intro i hi1 hi4 h2
    have hsub : ({0, 5, i} : Finset ℕ) ⊆ (Finset.range 6).filter (fun i => ℓ (m + i) = 2) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_filter, Finset.mem_range]
      rcases hx with rfl | rfl | rfl
      · exact ⟨by omega, by simpa using h0⟩
      · exact ⟨by omega, h5⟩
      · exact ⟨by omega, h2⟩
    have := Finset.card_le_card hsub
    rw [hcnt] at this
    have hc : ({0, 5, i} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp; omega
      · simp; omega
    omega
  have l1 := hne 1 (by omega) (by omega)
  have l2 := hne 2 (by omega) (by omega)
  have l3 := hne 3 (by omega) (by omega)
  have hpf1 : pf (m + 1) = 2 := by
    by_contra hh
    have : ℓ m ≠ 2 ∧ qf m ≠ 2 := M0.2 ⟨l1, hh⟩
    exact this.1 h0
  obtain ⟨a1, b1, c1⟩ := hperm (m + 1)
  have hq1 : qf (m + 1) ≠ 2 := fin3_other_not_two _ _ _ a1 b1 c1 hpf1
  have hp2 := (M1.1 ⟨l1, hq1⟩).2
  obtain ⟨a2, b2, c2⟩ := hperm (m + 2)
  have hq2 : qf (m + 2) = 2 := fin3_other_two _ _ _ a2 b2 c2 l2 hp2
  have hpf3 : pf (m + 3) = 2 := by
    by_contra hh
    have := M2.2 ⟨l3, hh⟩
    exact this.2 hq2
  exact ⟨l1, l2, l3, hq1, hp2, hq2, hpf3⟩

set_option maxHeartbeats 6400000 in
/-- **Statement (ii), the case of two `gamma` heads at an interior (2,2,2) vertex.** -/
theorem sc1_core [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    {Y : Plane} {d : V2} (hYi : Y ∈ interior D.region)
    (c0 : cnt D idx Y 0 = 2) (c1 : cnt D idx Y 1 = 2) (c2 : cnt D idx Y 2 = 2)
    {iL iR : Fin N} {A A' : Plane} (hL : TriStep (D.tile iL) d A Y) (hLg : ∃ k, (D.tile iL).pts k = Y ∧ idx iL k = 2)
    (hR : TriStep (D.tile iR) (neg2 d) Y A') (hRg : ∃ k, (D.tile iR).pts k = Y ∧ idx iR k = 2)
    (hcont : (∀ i U', TriStep (D.tile i) d Y U' → ¬ ∃ k, (D.tile i).pts k = U' ∧ idx i k = 2) ∨
      (∀ i U', TriStep (D.tile i) (neg2 d) U' Y → ¬ ∃ k, (D.tile i).pts k = U' ∧ idx i k = 2)) :
    ∃ Z, GKite D idx Y Z := by
  classical
  obtain ⟨F, s, ℓ, hF, hlab, hsurj, hperS⟩ := fan222_tile D idx hC.hidxA hYi c0 c1 c2 G
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
  by_cases hkite : ℓ (m + 1) = ℓ (m + 2)
  · -- a kite pair: Y is a vertex of Gamma_kite
    set iT := (s (m + 2)).1 with hiT
    set r := F.p (s (m + 2)) with hr
    have hS : TriStep (D.tile iT) r Y ((D.tile iT).pts (armP (kk (m + 2)) (fl (m + 2)))) :=
      triStep_of_start (kk (m + 2)) (fl (m + 2)) (S.hk (m + 2)) (S.hp (m + 2)) (S.hq (m + 2)) (S.crs_pos (m + 2)) (par_refl (hp0 (m + 2)))
    set V := (D.tile iT).pts (armP (kk (m + 2)) (fl (m + 2))) with hV
    have hdist : dist Y V = slen D 2 := by
      rw [← S.hk (m + 2)]
      exact step_dist_c D idx hC.hidx (armP_ne (kk (m + 2)) (fl (m + 2))).symm (by rw [S.hl]; exact l2) (by rw [S.hpf]; exact hp2)
    obtain ⟨hmo, hmi⟩ := interior_openSeg D P hreg hYi (tile_sub_region D.toRegionDissection iT (tile_pt_mem _ (armP (kk (m + 2)) (fl (m + 2)))))
    have hmo' : ((1 / 2 : ℝ) • V + (1 / 2 : ℝ) • Y) ∈ openSegment ℝ Y V := by rw [openSegment_symm]; exact hmo
    obtain ⟨jj, hjji, hSj, kk0, f0, kk', f', hk0, hf0, hk', hf', hcase⟩ := pair_partner D P hreg idx hC hab hac hS hdist hmo' hmi
    obtain ⟨x, hxj, hxq⟩ := sec_end F hSj
    rw [neg2_neg2'] at hxq
    have hx : x = s (m + 1) := prev_sector F s (j := m + 1) (r := r) (hpar (m + 1)).symm hxq
    have hjj : (s (m + 1)).1 = jj := by rw [← hx]; exact hxj
    have e0 : idx iT kk0 = ℓ (m + 2) := label_eq hlab (j := m + 2) rfl hk0
    have ef0 : f0 = armP (kk (m + 2)) (fl (m + 2)) := (D.tile iT).indep.injective hf0
    have e1' : idx iT f0 = pf (m + 2) := by rw [ef0, S.hpf]
    have e2' : idx jj f' = ℓ (m + 1) := label_eq hlab (j := m + 1) hjj hf'
    obtain ⟨hp2a, hp2b, hp2c⟩ := S.perm (m + 2)
    have hcase1 : idx jj f' = idx iT kk0 ∧ idx jj kk' = idx iT f0 := by
      rcases hcase with hc | hc
      · exact hc
      · exact absurd (hkite.symm.trans (e2'.symm.trans (hc.1.trans e1'))) hp2a
    rcases fin3_01 _ _ hp2a l2 hp2 with ⟨hlam, hplam⟩ | ⟨hlam, hplam⟩
    · -- an alpha pair: `GKite Y V`
      exact ⟨V, iT, jj, r, kk0, f0, kk', f', hjji.symm, hS, hSj, hk0, hf0, by rw [e0]; exact hlam, by rw [e1']; exact hplam, hk', hf',
        by rw [hcase1.2, e1']; exact hplam, by rw [hcase1.1, e0]; exact hlam⟩
    · -- a beta pair: `GKite V Y`, then the successor edge
      have hK : GKite D idx V Y :=
        ⟨jj, iT, neg2 r, kk', f', kk0, f0, hjji, hSj, by rw [neg2_neg2']; exact hS, hk', hf', by rw [hcase1.2, e1']; exact hplam,
          by rw [hcase1.1, e0]; exact hlam, hk0, hf0, by rw [e0]; exact hlam, by rw [e1']; exact hplam⟩
      exact gkite_succ_exists D P hreg idx hC hab hac h1 h3 hK
  · -- a straight line: a tile starting along it has gamma at its far end
    have h01 : ℓ m ≠ ℓ (m + 1) := by rw [hla1]; exact fun h => l1 h.symm
    have h02 : ℓ m ≠ ℓ (m + 2) := by rw [hla1]; exact fun h => l2 h.symm
    have hopp := straight_of_triple G hF m h01 h02 hkite
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

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.sc1_core
