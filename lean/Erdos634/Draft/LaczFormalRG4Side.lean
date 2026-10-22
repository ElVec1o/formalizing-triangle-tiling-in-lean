-- Draft/LaczFormalRG4Side.lean -- Case IV (gamma = pi/3): the fan at a vertex in the relative interior of an edge of the polygon, the "side normal" data (three corner tiles with distinct types
-- and no differing first sides on the inner rays) when no edge of `Gamma_a u Gamma_k` starts there (Lemma 8.1 (iii)), packaged for the local step lemmas (`side_step`).
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Lemma 8.1 (iii), Lemma 4.3), Beeson, Beeson-Zhang; ports of LaczFormalGraphBdy, LaczFormalGraphWalk.
import Erdos634.Draft.LaczFormalRG4Bal
import Erdos634.Draft.LaczFormalGraphBdy

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem cnt_two (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {H : Plane} (l : Fin 3) {t1 t2 : Fin N} {k1 k2 : Fin 3}
    (hne : t1 ≠ t2) (h1 : (D.tile t1).pts k1 = H) (h2 : (D.tile t2).pts k2 = H) (e1 : idx t1 k1 = l) (e2 : idx t2 k2 = l) :
    2 ≤ cnt D idx H l := by
  classical
  unfold cnt
  have : ({(t1, k1), (t2, k2)} : Finset (Fin N × Fin 3)) ⊆ Finset.univ.filter (fun p : Fin N × Fin 3 => (D.tile p.1).pts p.2 = H ∧ idx p.1 p.2 = l) := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> simp [*]
  have h3 := Finset.card_le_card this
  rw [Finset.card_pair (fun e => hne (congrArg Prod.fst e))] at h3
  exact h3

theorem cnt_one (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {H : Plane} (l : Fin 3) {t : Fin N} {k : Fin 3}
    (h1 : (D.tile t).pts k = H) (e1 : idx t k = l) : 1 ≤ cnt D idx H l := by
  classical
  unfold cnt
  exact Finset.card_pos.mpr ⟨(t, k), by simp [h1, e1]⟩

theorem idx_two_of_cnt (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {H : Plane}
    (c0 : cnt D idx H 0 = 0) (c1 : cnt D idx H 1 = 0) {t : Fin N} {k : Fin 3} (h : (D.tile t).pts k = H) : idx t k = 2 := by
  by_contra hne
  have : idx t k = 0 ∨ idx t k = 1 := by
    generalize idx t k = z at hne
    revert z; decide
  rcases this with e | e
  · have := cnt_one D idx 0 h e; omega
  · have := cnt_one D idx 1 h e; omega


/-- The tile with a left side along `d` starting at `V` is the first tile of the side fan. -/
theorem fan_start_unique {D : RegionDissection N} {V : Plane} {pT : V2} {p q : AtV D V → V2} {s1 s2 s3 : AtV D V}
    (hF : SideFan3 D V pT p q s1 s2 s3) {d : V2} (hd : Par pT d) {i : Fin N} {U' : Plane}
    (hS : TriStep (D.tile i) d V U') (hi : V ∈ (D.tile i).carrier) : (⟨i, hi⟩ : AtV D V) = s1 := by
  classical
  set s : AtV D V := ⟨i, hi⟩ with hs
  obtain ⟨kk, f, g, hk, -⟩ := id hS
  obtain ⟨kk', fl, hk', hp, hq⟩ := spec_corner_data (hF.spec s) ⟨kk, hk⟩
  have hstart : Par (p s) d := triStep_start hS kk' fl hk' hp hq (hF.ok s)
  have hdis := tiles_disjoint D V p q hF.loc
  have hsp : Par (p s) pT := hstart.trans hd.symm
  rcases hF.all s with h | h | h
  · exact h
  · exfalso
    rw [h] at hsp
    have h1 : Par (q s1) pT := hF.r2.symm.trans hsp
    exact par_not_secok (hF.ok s1) (h1.trans hF.r1.symm)
  · exfalso
    rw [h] at hsp
    exact start_inj p q hF.ok hdis hF.d13 (hsp.trans hF.r1.symm)

/-- The tile with a left side along `d` ending at `V` is the last tile of the side fan. -/
theorem fan_end_unique {D : RegionDissection N} {V : Plane} {pT : V2} {p q : AtV D V → V2} {s1 s2 s3 : AtV D V}
    (hF : SideFan3 D V pT p q s1 s2 s3) {d : V2} (hd : Par pT d) {i : Fin N} {U : Plane}
    (hS : TriStep (D.tile i) d U V) (hi : V ∈ (D.tile i).carrier) : (⟨i, hi⟩ : AtV D V) = s3 := by
  classical
  set s : AtV D V := ⟨i, hi⟩ with hs
  obtain ⟨kk, f, g, hk, hf, -⟩ := id hS
  obtain ⟨kk', fl, hk', hp, hq⟩ := spec_corner_data (hF.spec s) ⟨f, hf⟩
  have hend : Par (q s) (-d.1, -d.2) := triStep_end hS kk' fl hk' hp hq (hF.ok s)
  have hdis := tiles_disjoint D V p q hF.loc
  have hsq : Par (q s) (-pT.1, -pT.2) := hend.trans (par_neg hd).symm
  rcases hF.all s with h | h | h
  · exfalso
    rw [h] at hsq
    exact end_inj' p q hF.ok hdis (Ne.symm hF.d13) (hsq.trans hF.r4)
  · exfalso
    rw [h] at hsq
    exact end_inj' p q hF.ok hdis (Ne.symm hF.d23) (hsq.trans hF.r4)
  · exact h



/-- **A three-tile fan at an edge point, in order.** -/
theorem unit_fan3 (D : RegionDissection N) {V : Plane} (pT : V2) (F : ExtFan D V Unit) (hpT : pT ≠ 0)
    (hpe : F.pe () = (-pT.1, -pT.2)) (hqe : F.qe () = pT) (hcard : Fintype.card (AtV D V) = 3) :
    ∃ s1 s2 s3 : AtV D V, SideFan3 D V pT F.p F.q s1 s2 s3 := by
  classical
  have hk4 : Fintype.card (AtV D V ⊕ Unit) = 4 := by rw [Fintype.card_sum, hcard]; simp
  have hper := F.hper
  have hinj := F.hinj
  have hsurj := F.hsurj
  rw [hk4] at hper hinj hsurj
  have hmod := cyc_mod F.e 4 hper
  obtain ⟨j0, hj0, hnone⟩ := hsurj (Sum.inr ())
  have hne : ∀ i, 1 ≤ i → i ≤ 3 → F.e (j0 + i) ≠ Sum.inr () := by
    intro i hi1 hi3 h
    rw [hmod (j0 + i)] at h
    have := hinj (Set.mem_Iio.mpr (Nat.mod_lt _ (by norm_num))) (Set.mem_Iio.mpr hj0) (h.trans hnone.symm)
    omega
  have hex : ∀ i, 1 ≤ i → i ≤ 3 → ∃ s, F.e (j0 + i) = Sum.inl s := by
    intro i hi1 hi3
    rcases hx : F.e (j0 + i) with s | u
    · exact ⟨s, rfl⟩
    · exfalso
      apply hne i hi1 hi3
      rw [hx]
  obtain ⟨s1, hs1⟩ := hex 1 (by norm_num) (by norm_num)
  obtain ⟨s2, hs2⟩ := hex 2 (by norm_num) (by norm_num)
  obtain ⟨s3, hs3⟩ := hex 3 (by norm_num) (by norm_num)
  have hdist : ∀ i i', i ≤ 3 → i' ≤ 3 → 1 ≤ i → 1 ≤ i' → i ≠ i' → F.e (j0 + i) ≠ F.e (j0 + i') := by
    intro i i' h1 h2 h3 h4 hne' h
    rw [hmod (j0 + i), hmod (j0 + i')] at h
    have := hinj (Set.mem_Iio.mpr (Nat.mod_lt _ (by norm_num))) (Set.mem_Iio.mpr (Nat.mod_lt _ (by norm_num))) h
    omega
  have hP0 := F.hP j0
  have hP1 := F.hP (j0 + 1)
  have hP2 := F.hP (j0 + 2)
  have hP3 := F.hP (j0 + 3)
  rw [hnone, show j0 + 1 = j0 + 1 from rfl, hs1] at hP0
  rw [show j0 + 1 + 1 = j0 + 2 from rfl, hs2, hs1] at hP1
  rw [show j0 + 2 + 1 = j0 + 3 from rfl, hs3, hs2] at hP2
  have he4 : F.e (j0 + 3 + 1) = Sum.inr () := by
    rw [show j0 + 3 + 1 = j0 + 4 from rfl, hper j0, hnone]
  rw [he4, hs3] at hP3
  simp only [Sum.elim_inl, Sum.elim_inr, hpe, hqe] at hP0 hP1 hP2 hP3
  refine ⟨s1, s2, s3, ⟨hpT, F.hok, F.hloc, F.hspec, ?_, ?_, ?_, ?_, hP0, hP1, hP2, hP3⟩⟩
  · intro h; apply hdist 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rw [hs1, hs2, h]
  · intro h; apply hdist 1 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rw [hs1, hs3, h]
  · intro h; apply hdist 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rw [hs2, hs3, h]
  · intro s
    obtain ⟨j, hj, hjs⟩ := hsurj (Sum.inl s)
    have hjne : j ≠ j0 := by
      intro h; rw [h, hnone] at hjs; exact absurd hjs (by simp)
    have hcases : j = (j0 + 1) % 4 ∨ j = (j0 + 2) % 4 ∨ j = (j0 + 3) % 4 := by omega
    rcases hcases with h | h | h
    · left
      have : F.e (j0 + 1) = Sum.inl s := by rw [hmod (j0 + 1), ← h]; exact hjs
      rw [hs1] at this; exact (Sum.inl.inj this).symm
    · right; left
      have : F.e (j0 + 2) = Sum.inl s := by rw [hmod (j0 + 2), ← h]; exact hjs
      rw [hs2] at this; exact (Sum.inl.inj this).symm
    · right; right
      have : F.e (j0 + 3) = Sum.inl s := by rw [hmod (j0 + 3), ← h]; exact hjs
      rw [hs3] at this; exact (Sum.inl.inj this).symm


/-- **The fan at a tiling vertex in the relative interior of an edge** (`γ = π/3`): one straight virtual sector, three corner tiles with counts `(0,0,3)` or `(1,1,1)`, no tile with the vertex inside a side. -/
theorem edge_fan_counts (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseIV D idx) (i : Fin M) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {V : Plane}
    (hV : V = (1 - t) • P.v i + t • P.v (i + 1)) (hvert : ∃ j k, (D.tile j).pts k = V) :
    ∃ (pT : V2) (F : ExtFan D.toRegionDissection V Unit), Par pT (toV2 (P.e i)) ∧ F.pe () = (-pT.1, -pT.2) ∧ F.qe () = pT ∧
      (∀ x : AtV D.toRegionDissection V, 0 < crs (F.p x) (F.q x)) ∧
      ((cnt D idx V 0 = 0 ∧ cnt D idx V 1 = 0 ∧ cnt D idx V 2 = 3) ∨ (cnt D idx V 0 = 1 ∧ cnt D idx V 1 = 1 ∧ cnt D idx V 2 = 1)) ∧
      Fintype.card (AtV D.toRegionDissection V) = 3 := by
  classical
  subst hV
  obtain ⟨pT, F, hpd, hpe, hqe, hTgt⟩ := fan_open_edge D.toRegionDissection P hreg i ht0 ht1 hvert
  have hpT : pT ≠ 0 := hpd.ne_left
  have hang := head_angle_sum_gen D idx h.hidxA F
  have hvirt : ∑ j : Unit, wd (F.pe j) (F.qe j) = Real.pi := by
    rw [Fintype.sum_unique]
    show wd (F.pe ()) (F.qe ()) = Real.pi
    rw [hpe, hqe, wd_ext hpT]
  rw [hvirt] at hang
  have hcorn : 0 < (Corn D.toRegionDissection ((1 - t) • P.v i + t • P.v (i + 1))).card := by
    obtain ⟨j, k, hk⟩ := hvert
    exact Finset.card_pos.mpr ⟨j, by simp [Corn]; exact ⟨k, hk⟩⟩
  rw [card_corn D idx ((1 - t) • P.v i + t • P.v (i + 1)), Fin.sum_univ_three] at hcorn
  have hA0 := model_angle_pos' D 0
  have hA1 := model_angle_pos' D 1
  have hA2 := model_angle_pos' D 2
  have hpi := Real.pi_pos
  rw [Fin.sum_univ_three] at hang
  have hSpos : 0 < (cnt D idx ((1 - t) • P.v i + t • P.v (i + 1)) 0 : ℝ) * D.model.angleAt 0 + cnt D idx ((1 - t) • P.v i + t • P.v (i + 1)) 1 * D.model.angleAt 1 + cnt D idx ((1 - t) • P.v i + t • P.v (i + 1)) 2 * D.model.angleAt 2 := by
    by_cases h0' : 0 < cnt D idx ((1 - t) • P.v i + t • P.v (i + 1)) 0
    · have : (0:ℝ) < cnt D idx ((1 - t) • P.v i + t • P.v (i + 1)) 0 := by exact_mod_cast h0'
      have := mul_pos this hA0
      have := mul_nonneg (Nat.cast_nonneg (cnt D idx ((1 - t) • P.v i + t • P.v (i + 1)) 1) : (0:ℝ) ≤ _) hA1.le
      have := mul_nonneg (Nat.cast_nonneg (cnt D idx ((1 - t) • P.v i + t • P.v (i + 1)) 2) : (0:ℝ) ≤ _) hA2.le
      linarith
    · by_cases h1' : 0 < cnt D idx ((1 - t) • P.v i + t • P.v (i + 1)) 1
      · have : (0:ℝ) < cnt D idx ((1 - t) • P.v i + t • P.v (i + 1)) 1 := by exact_mod_cast h1'
        have := mul_pos this hA1
        have := mul_nonneg (Nat.cast_nonneg (cnt D idx ((1 - t) • P.v i + t • P.v (i + 1)) 0) : (0:ℝ) ≤ _) hA0.le
        have := mul_nonneg (Nat.cast_nonneg (cnt D idx ((1 - t) • P.v i + t • P.v (i + 1)) 2) : (0:ℝ) ≤ _) hA2.le
        linarith
      · have h2' : 0 < cnt D idx ((1 - t) • P.v i + t • P.v (i + 1)) 2 := by omega
        have : (0:ℝ) < cnt D idx ((1 - t) • P.v i + t • P.v (i + 1)) 2 := by exact_mod_cast h2'
        have := mul_pos this hA2
        have := mul_nonneg (Nat.cast_nonneg (cnt D idx ((1 - t) • P.v i + t • P.v (i + 1)) 0) : (0:ℝ) ≤ _) hA0.le
        have := mul_nonneg (Nat.cast_nonneg (cnt D idx ((1 - t) • P.v i + t • P.v (i + 1)) 1) : (0:ℝ) ≤ _) hA1.le
        linarith
  have hStr : (Strn D.toRegionDissection ((1 - t) • P.v i + t • P.v (i + 1))).card = 0 := by
    by_contra hne
    have : (1 : ℝ) ≤ (Strn D.toRegionDissection ((1 - t) • P.v i + t • P.v (i + 1))).card := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
    nlinarith
  rw [hStr] at hang
  have hS : (cnt D idx ((1 - t) • P.v i + t • P.v (i + 1)) 0 : ℝ) * D.model.angleAt 0 + cnt D idx ((1 - t) • P.v i + t • P.v (i + 1)) 1 * D.model.angleAt 1 + cnt D idx ((1 - t) • P.v i + t • P.v (i + 1)) 2 * D.model.angleAt 2 = Real.pi := by
    simp only [Nat.cast_zero, mul_zero, add_zero] at hang
    linarith
  have hcls := h.harith _ _ _ hS (h.hregc ((1 - t) • P.v i + t • P.v (i + 1)))
  have hcorner : ∀ x : AtV D.toRegionDissection ((1 - t) • P.v i + t • P.v (i + 1)), 0 < crs (F.p x) (F.q x) := by
    intro x
    rcases F.hspec x with ⟨k, hk, -⟩ | ⟨hnv, -⟩
    · exact crs_pos_of_corner (F.hok x) (F.hspec x) ⟨k, hk⟩
    · exfalso
      have : x.1 ∈ Strn D.toRegionDissection ((1 - t) • P.v i + t • P.v (i + 1)) := by
        simp only [Strn, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨x.2, hnv⟩
      have := Finset.card_pos.mpr ⟨x.1, this⟩
      omega
  have hcard : Fintype.card (AtV D.toRegionDissection ((1 - t) • P.v i + t • P.v (i + 1))) = 3 := by
    rw [card_atV, card_corn D idx ((1 - t) • P.v i + t • P.v (i + 1)), hStr, Fin.sum_univ_three]
    rcases hcls with ⟨h0', h2'⟩ | ⟨h0', h2'⟩
    · have := h.hregc ((1 - t) • P.v i + t • P.v (i + 1)); omega
    · have := h.hregc ((1 - t) • P.v i + t • P.v (i + 1)); omega
  refine ⟨pT, F, hpd, hpe, hqe, hcorner, ?_, hcard⟩
  have hr := h.hregc ((1 - t) • P.v i + t • P.v (i + 1))
  rcases hcls with ⟨h0', h2'⟩ | ⟨h0', h2'⟩
  · left; exact ⟨h0', by omega, h2'⟩
  · right; exact ⟨h0', by omega, h2'⟩


/-- **Lemma 8.1 (iii) for a polygon edge.**  A tiling vertex in the relative interior of an edge, from which no edge of `Γ_a ∪ Γ_k` starts, has a three-tile fan with distinct types
at the vertex and no differing first sides on the two inner rays. -/
theorem edge_vertex_data (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseIV D idx) (i : Fin M) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {V : Plane}
    (hV : V = (1 - t) • P.v i + t • P.v (i + 1)) (hvert : ∃ j k, (D.tile j).pts k = V)
    (hnoGa : ∀ H', ¬ GaEdge D.toRegionDissection (slen D 0) V H') (hnoGk : ∀ Z, ¬ GkEdge D.toRegionDissection idx V Z) :
    ∃ (pT : V2) (F : ExtFan D.toRegionDissection V Unit) (s1 s2 s3 : AtV D.toRegionDissection V),
      Par pT (toV2 (P.e i)) ∧ SideFan3 D.toRegionDissection V pT F.p F.q s1 s2 s3 ∧
      (∃ k, (D.tile s2.1).pts k = V) ∧
      (∀ k1 k2 k3, (D.tile s1.1).pts k1 = V → (D.tile s2.1).pts k2 = V → (D.tile s3.1).pts k3 = V →
        idx s1.1 k1 ≠ idx s2.1 k2 ∧ idx s1.1 k1 ≠ idx s3.1 k3 ∧ idx s2.1 k2 ≠ idx s3.1 k3) ∧
      (nsq (F.q s1) = slen D 0 ^ 2 ↔ nsq (F.p s2) = slen D 0 ^ 2) ∧ (nsq (F.q s2) = slen D 0 ^ 2 ↔ nsq (F.p s3) = slen D 0 ^ 2) := by
  classical
  obtain ⟨pT, F, hpd, hpe, hqe, hcr, hcls, hcard⟩ := edge_fan_counts D P hreg idx h i ht0 ht1 hV hvert
  have hpT : pT ≠ 0 := hpd.ne_left
  obtain ⟨s1, s2, s3, hF⟩ := unit_fan3 D.toRegionDissection pT F hpT hpe hqe hcard
  refine ⟨pT, F, s1, s2, s3, hpd, hF, ?_⟩
  have hcorner : ∀ x : AtV D.toRegionDissection V, ∃ k, (D.tile x.1).pts k = V := fun x => ExtFan.corner_of_crs F x (hcr x)
  have c1 : 0 < crs pT (F.q s1) := by
    obtain ⟨a, ha, hap⟩ := hF.r1.smul
    have hh := hcr s1
    rw [hap] at hh; unfold crs at hh ⊢; try simp only at hh ⊢
    by_contra hX; push Not at hX
    nlinarith [mul_nonneg ha.le (neg_nonneg.mpr hX)]
  have c2 : 0 < crs pT (F.p s2) := ExtFan.crs_pos_of_par hF.r2 c1
  have c3p : 0 < crs pT (F.p s3) := by
    obtain ⟨b, hb, hbq⟩ := hF.r4.symm.smul
    have hh := hcr s3
    rw [hbq] at hh; unfold crs at hh ⊢; try simp only at hh ⊢
    by_contra hX; push Not at hX
    nlinarith [mul_nonneg hb.le (neg_nonneg.mpr hX)]
  have c3 : 0 < crs pT (F.q s2) := by
    obtain ⟨c, hc, hcp⟩ := hF.r3.smul
    rw [hcp] at c3p; unfold crs at c3p ⊢; try simp only at c3p ⊢
    by_contra hX; push Not at hX
    nlinarith [mul_nonneg hc.le (neg_nonneg.mpr hX)]
  have arm_nonneg : ∀ x : AtV D.toRegionDissection V, 0 ≤ crs pT (F.p x) ∧ 0 ≤ crs pT (F.q x) := by
    intro x
    rcases hF.all x with rfl | rfl | rfl
    · refine ⟨(ExtFan.crs_zero_of_par hF.r1 (by unfold crs; ring)).ge, c1.le⟩
    · exact ⟨c2.le, c3.le⟩
    · exact ⟨c3p.le, (ExtFan.crs_zero_of_par hF.r4.symm (by unfold crs; ring)).ge⟩
  have nbray : ∀ ρ : V2, 0 < crs pT ρ → NoBack D.toRegionDissection ρ V := by
    intro ρ hρ
    apply ExtFan.noBack_of_none F
    intro x
    obtain ⟨h1, h2⟩ := arm_nonneg x
    refine ⟨fun h' => ?_, fun h' => ?_⟩
    · have := ExtFan.crs_neg_of_par h' hρ; linarith
    · have := ExtFan.crs_neg_of_par h' hρ; linarith
  have nb1 := nbray _ c1
  have nb2 := nbray _ c3
  have iff1 : (nsq (F.q s1) = slen D 0 ^ 2 ↔ nsq (F.p s2) = slen D 0 ^ 2) := by
    by_contra hn
    have hx : (nsq (F.q s1) = slen D 0 ^ 2 ∧ nsq (F.p s2) ≠ slen D 0 ^ 2) ∨ (nsq (F.q s1) ≠ slen D 0 ^ 2 ∧ nsq (F.p s2) = slen D 0 ^ 2) := by tauto
    obtain ⟨H', hH'⟩ := ga_edge_of_ray D idx h.hidx h.hnc F s1 s2 (hcr s1) (hcr s2) hF.r2 nb1 hx
    exact hnoGa H' hH'
  have iff2 : (nsq (F.q s2) = slen D 0 ^ 2 ↔ nsq (F.p s3) = slen D 0 ^ 2) := by
    by_contra hn
    have hx : (nsq (F.q s2) = slen D 0 ^ 2 ∧ nsq (F.p s3) ≠ slen D 0 ^ 2) ∨ (nsq (F.q s2) ≠ slen D 0 ^ 2 ∧ nsq (F.p s3) = slen D 0 ^ 2) := by tauto
    obtain ⟨H', hH'⟩ := ga_edge_of_ray D idx h.hidx h.hnc F s2 s3 (hcr s2) (hcr s3) hF.r3 nb2 hx
    exact hnoGa H' hH'
  refine ⟨hcorner s2, ?_, iff1, iff2⟩
  intro k1 k2 k3 hk1 hk2 hk3
  rcases hcls with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩
  · exfalso
    obtain ⟨kk1, fl1, hkk1, hp1, hq1⟩ := spec_corner_data (F.hspec s1) (hcorner s1)
    obtain ⟨kk2, fl2, hkk2, hp2, hq2⟩ := spec_corner_data (F.hspec s2) (hcorner s2)
    obtain ⟨kk3, fl3, hkk3, hp3, hq3⟩ := spec_corner_data (F.hspec s3) (hcorner s3)
    have g1 := idx_two_of_cnt D idx e0 e1 hkk1
    have g2 := idx_two_of_cnt D idx e0 e1 hkk2
    have g3 := idx_two_of_cnt D idx e0 e1 hkk3
    have u1 := arms_01 (idx s1.1) kk1 fl1 g1
    have u2 := arms_01 (idx s2.1) kk2 fl2 g2
    have u3 := arms_01 (idx s3.1) kk3 fl3 g3
    have f1 := (nsq_q_iff D idx h.hidx h.hab h.hac fl1 hkk1 hq1)
    have f2 := (nsq_p_iff D idx h.hidx h.hab h.hac fl2 hkk2 hp2)
    have f3 := (nsq_q_iff D idx h.hidx h.hab h.hac fl2 hkk2 hq2)
    have f4 := (nsq_p_iff D idx h.hidx h.hab h.hac fl3 hkk3 hp3)
    have k1' : ¬ (idx s1.1 (armQ kk1 fl1) = 1 ∧ idx s2.1 (armP kk2 fl2) = 1) := by
      rintro ⟨t1x, t1y⟩
      obtain ⟨Z, hZ⟩ := gk_of_ray D idx h.hidx h.hab h.hac F s1 s2 hF.r2 hF.d12 hkk1 hkk2 hp1 hq1 hp2 hq2 g1 t1x g2 t1y
      exact hnoGk Z hZ
    have k2' : ¬ (idx s2.1 (armQ kk2 fl2) = 1 ∧ idx s3.1 (armP kk3 fl3) = 1) := by
      rintro ⟨t1x, t1y⟩
      obtain ⟨Z, hZ⟩ := gk_of_ray D idx h.hidx h.hab h.hac F s2 s3 hF.r3 hF.d23 hkk2 hkk3 hp2 hq2 hp3 hq3 g2 t1x g3 t1y
      exact hnoGk Z hZ
    exact no_contra_003 _ _ _ _ _ _ u1 u2 u3 (by rw [← f1, ← f2]; exact iff1) (by rw [← f3, ← f4]; exact iff2) k1' k2'
  · have hk : ∀ (t : Fin N) (k : Fin 3), (D.tile t).pts k = V → ∀ l : Fin 3, idx t k = l → cnt D idx V l = 1 := by
      intro t k hk l hl
      have := cnt_one D idx l hk hl
      fin_cases l <;> simp_all
    refine ⟨?_, ?_, ?_⟩
    · intro e
      have := cnt_two D idx (idx s1.1 k1) (fun h' => hF.d12 (Subtype.ext h')) hk1 hk2 rfl e.symm
      have := hk _ _ hk1 _ rfl
      omega
    · intro e
      have := cnt_two D idx (idx s1.1 k1) (fun h' => hF.d13 (Subtype.ext h')) hk1 hk3 rfl e.symm
      have := hk _ _ hk1 _ rfl
      omega
    · intro e
      have := cnt_two D idx (idx s2.1 k2) (fun h' => hF.d23 (Subtype.ext h')) hk2 hk3 rfl e.symm
      have := hk _ _ hk2 _ rfl
      omega


/-- **The local step at a normal side vertex, three conclusions** (Laczkovich Lemma 4.3 / Fig. 3): with the tile `s3` ending at `V` along the line (tail vertex `fL`, head `kL`) and `s1`
starting at `V` (tail `kR`, head `fR`): (βγ) a `{β,γ}` pair is copied by the next tile; (α) `α` at the tail of the left tile gives `α` at the tail of the right tile; (α') `α` at the
head of the right tile gives `α` at the head of the left tile. -/
theorem side_step_all (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (V : Plane) {pT : V2} {p q : AtV D.toRegionDissection V → V2} {s1 s2 s3 : AtV D.toRegionDissection V}
    (hF : SideFan3 D.toRegionDissection V pT p q s1 s2 s3)
    (hcorner2 : ∃ k, (D.tile s2.1).pts k = V)
    (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    (hnorm : ∀ k1 k2 k3, (D.tile s1.1).pts k1 = V → (D.tile s2.1).pts k2 = V → (D.tile s3.1).pts k3 = V →
      idx s1.1 k1 ≠ idx s2.1 k2 ∧ idx s1.1 k1 ≠ idx s3.1 k3 ∧ idx s2.1 k2 ≠ idx s3.1 k3)
    (hno1 : nsq (q s1) = slen D 0 ^ 2 ↔ nsq (p s2) = slen D 0 ^ 2)
    (hno2 : nsq (q s2) = slen D 0 ^ 2 ↔ nsq (p s3) = slen D 0 ^ 2)
    (kR fR kL fL : Fin 3) (hR1 : (D.tile s1.1).pts kR = V)
    (hR2 : Par (toV2 ((D.tile s1.1).pts fR - V)) pT)
    (hL1 : (D.tile s3.1).pts kL = V)
    (hL2 : Par (toV2 ((D.tile s3.1).pts fL - V)) (-pT.1, -pT.2))
    : ((idx s3.1 fL = 1 ∧ idx s3.1 kL = 2) ∨ (idx s3.1 fL = 2 ∧ idx s3.1 kL = 1) → idx s1.1 kR = idx s3.1 fL ∧ idx s1.1 fR = idx s3.1 kL) ∧
      (idx s3.1 fL = 0 → idx s1.1 kR = 0) ∧ (idx s1.1 fR = 0 → idx s3.1 kL = 0) ∧
      ((idx s1.1 kR = 1 ∧ idx s1.1 fR = 2) ∨ (idx s1.1 kR = 2 ∧ idx s1.1 fR = 1) → idx s1.1 kR = idx s3.1 fL ∧ idx s1.1 fR = idx s3.1 kL) := by
  classical
  obtain ⟨kk1, fl1, hk1, hp1, hq1⟩ := spec_corner_data (hF.spec s1) ⟨kR, hR1⟩
  obtain ⟨kk2, fl2, hk2, hp2, hq2⟩ := spec_corner_data (hF.spec s2) hcorner2
  obtain ⟨kk3, fl3, hk3, hp3, hq3⟩ := spec_corner_data (hF.spec s3) ⟨kL, hL1⟩
  have e1 : kR = kk1 := (D.tile s1.1).indep.injective (hR1.trans hk1.symm)
  have e3 : kL = kk3 := (D.tile s3.1).indep.injective (hL1.trans hk3.symm)
  subst e1 e3
  -- the far vertices
  have hfR : fR = armP kR fl1 := by
    refine arm_unique (D.tile s1.1) V kR hR1 fR (armP kR fl1) ?_ (armP_ne kR fl1) pT hR2 ?_
    · intro h
      have := hR2.ne_left
      apply this
      rw [h, hR1]; simp [toV2]
    · have := hF.r1; rw [hp1] at this; exact this
  have hfL : fL = armQ kL fl3 := by
    refine arm_unique (D.tile s3.1) V kL hL1 fL (armQ kL fl3) ?_ (armQ_ne kL fl3) (-pT.1, -pT.2) hL2 ?_
    · intro h
      have := hL2.ne_left
      apply this
      rw [h, hL1]; simp [toV2]
    · have := hF.r4; rw [hq3] at this; exact this.symm
  subst hfR hfL
  -- codes
  set c1 := codeOf (idx s1.1) kR fl1 with hc1
  set c2 := codeOf (idx s2.1) kk2 fl2 with hc2
  set c3 := codeOf (idx s3.1) kL fl3 with hc3
  obtain ⟨t1, u1, w1, l1⟩ := codeOf_spec' (idx s1.1) kR fl1
  obtain ⟨t2, u2, w2, l2⟩ := codeOf_spec' (idx s2.1) kk2 fl2
  obtain ⟨t3, u3, w3, l3⟩ := codeOf_spec' (idx s3.1) kL fl3
  rw [← hc1] at t1 u1 w1 l1
  rw [← hc2] at t2 u2 w2 l2
  rw [← hc3] at t3 u3 w3 l3
  have hnm := hnorm kR kk2 kL hR1 hk2 hL1
  -- lengths in terms of types
  have hlen1 := arm_lens D idx hidx s1.1 kR fl1
  have hlen2 := arm_lens D idx hidx s2.1 kk2 fl2
  have hlen3 := arm_lens D idx hidx s3.1 kL fl3
  rw [hk1] at hlen1; rw [hk2] at hlen2; rw [hk3] at hlen3
  rw [← hp1, ← hq1] at hlen1
  rw [← hp2, ← hq2] at hlen2
  rw [← hp3, ← hq3] at hlen3
  have hs := slen_sq_eq_iff D hab hac
  -- no differing first sides
  have g1 : (RegFan.tU c1 == 0) = (RegFan.tW c2 == 0) := by
    have h := hno1
    rw [hlen1.2, hlen2.1, hs, hs] at h
    have e1' : (RegFan.tU c1 = 0) ↔ (idx s1.1 (armP kR fl1) = 0) := by
      rw [u1]
      constructor
      · intro h'; exact Fin.ext (by simpa using h')
      · intro h'; rw [h']; rfl
    have e2' : (RegFan.tW c2 = 0) ↔ (idx s2.1 (armQ kk2 fl2) = 0) := by
      rw [w2]
      constructor
      · intro h'; exact Fin.ext (by simpa using h')
      · intro h'; rw [h']; rfl
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq]
    exact e1'.trans (h.trans e2'.symm)
  have g2 : (RegFan.tU c2 == 0) = (RegFan.tW c3 == 0) := by
    have h := hno2
    rw [hlen2.2, hlen3.1, hs, hs] at h
    have e1' : (RegFan.tU c2 = 0) ↔ (idx s2.1 (armP kk2 fl2) = 0) := by
      rw [u2]
      constructor
      · intro h'; exact Fin.ext (by simpa using h')
      · intro h'; rw [h']; rfl
    have e2' : (RegFan.tW c3 = 0) ↔ (idx s3.1 (armQ kL fl3) = 0) := by
      rw [w3]
      constructor
      · intro h'; exact Fin.ext (by simpa using h')
      · intro h'; rw [h']; rfl
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq]
    exact e1'.trans (h.trans e2'.symm)
  set l : List ℕ := [c1, c2, c3] with hl
  have hlen : l.length = 3 := rfl
  have hlt : ∀ x ∈ l, x < 6 := by
    intro x hx
    simp only [hl, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hc : ∀ j : Fin 3, RegFan.cnt l j = 1 := by
    intro j
    rw [hl, cnt3_eq, t1, t2, t3]
    exact perm3_cnt (idx s1.1 kR) (idx s2.1 kk2) (idx s3.1 kL) hnm.1 hnm.2.1 hnm.2.2 j
  have hga1 : RegFan.gaEdge l 1 = false := by
    simp only [RegFan.gaEdge, RegFan.Lc, RegFan.Rc, hl, hlen]
    simp [g1]
  have hga2 : RegFan.gaEdge l 2 = false := by
    simp only [RegFan.gaEdge, RegFan.Lc, RegFan.Rc, hl, hlen]
    simp [g2]
  have hstep : RegFan.stepHyp l = true := by
    have h0 := hc 0
    have h1 := hc 1
    have h2 := hc 2
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at h0 h1 h2
    unfold RegFan.stepHyp
    simp [h0, h1, h2, hga1, hga2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hβγ
    have hline : RegFan.line12' l = true := by
      show ((RegFan.tT c3 == 1 && RegFan.tW c3 == 2) || (RegFan.tT c3 == 2 && RegFan.tW c3 == 1)) = true
      rw [t3, w3]
      rcases hβγ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp [h1, h2]
      · simp [h1, h2]
    have htr := RegFan.boundary_step_beta_gamma' l hlen hlt hstep hline
    have htr' : c3 = RegFan.code (RegFan.tU c1) (RegFan.tW c1) (RegFan.tT c1) := beq_iff_eq.mp htr
    rw [t1, u1, w1] at htr'
    have hd1 : idx s1.1 (armP kR fl1) ≠ idx s1.1 (armQ kR fl1) := (idx s1.1).injective.ne (armPQ_ne kR fl1)
    have hd2 : idx s1.1 (armP kR fl1) ≠ idx s1.1 kR := (idx s1.1).injective.ne (armP_ne kR fl1)
    have hd3 : idx s1.1 (armQ kR fl1) ≠ idx s1.1 kR := (idx s1.1).injective.ne (armQ_ne kR fl1)
    obtain ⟨A, B, C, -⟩ := code_spec (idx s1.1 (armP kR fl1)) (idx s1.1 (armQ kR fl1)) (idx s1.1 kR) hd1 hd2 hd3
    have x1 : RegFan.tT c3 = idx s1.1 (armP kR fl1) := by rw [htr']; exact A
    have x2 : RegFan.tW c3 = idx s1.1 kR := by rw [htr']; exact C
    refine ⟨?_, ?_⟩
    · apply Fin.ext
      rw [← x2, w3]
    · apply Fin.ext
      rw [← x1, t3]
  · intro hα
    have hw : RegFan.tW (l.getD 2 0) = 0 := by
      show RegFan.tW c3 = 0
      rw [w3]; simp [hα]
    have := RegFan.boundary_step_alpha l hlen hlt hstep hw
    have h0 : RegFan.tT c1 = 0 := this
    rw [t1] at h0
    exact Fin.ext (by simpa using h0)
  · intro hα
    have hw : RegFan.tU (l.getD 0 0) = 0 := by
      show RegFan.tU c1 = 0
      rw [u1]; simp [hα]
    have := RegFan.boundary_step_alpha' l hlen hlt hstep hw
    have h0 : RegFan.tT c3 = 0 := this
    rw [t3] at h0
    exact Fin.ext (by simpa using h0)
  · intro hβγ'
    have hline : RegFan.line12 l = true := by
      show ((RegFan.tT c1 == 1 && RegFan.tU c1 == 2) || (RegFan.tT c1 == 2 && RegFan.tU c1 == 1)) = true
      rw [t1, u1]
      rcases hβγ' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp [h1, h2]
      · simp [h1, h2]
    have htr := RegFan.boundary_step_beta_gamma l hlen hlt hstep hline
    have htr' : c3 = RegFan.code (RegFan.tU c1) (RegFan.tW c1) (RegFan.tT c1) := beq_iff_eq.mp htr
    rw [t1, u1, w1] at htr'
    have hd1 : idx s1.1 (armP kR fl1) ≠ idx s1.1 (armQ kR fl1) := (idx s1.1).injective.ne (armPQ_ne kR fl1)
    have hd2 : idx s1.1 (armP kR fl1) ≠ idx s1.1 kR := (idx s1.1).injective.ne (armP_ne kR fl1)
    have hd3 : idx s1.1 (armQ kR fl1) ≠ idx s1.1 kR := (idx s1.1).injective.ne (armQ_ne kR fl1)
    obtain ⟨A, B, C, -⟩ := code_spec (idx s1.1 (armP kR fl1)) (idx s1.1 (armQ kR fl1)) (idx s1.1 kR) hd1 hd2 hd3
    have x1 : RegFan.tT c3 = idx s1.1 (armP kR fl1) := by rw [htr']; exact A
    have x2 : RegFan.tW c3 = idx s1.1 kR := by rw [htr']; exact C
    refine ⟨?_, ?_⟩
    · apply Fin.ext
      rw [← x2, w3]
    · apply Fin.ext
      rw [← x1, t3]


theorem c_on_edge (P : ConvPoly M) (i : Fin M) (t : ℝ) : P.c i ((1 - t) • P.v i + t • P.v (i + 1)) = 0 := by
  have e1 : (1 - t) • P.v i + t • P.v (i + 1) - P.v i = t • P.e i := by
    unfold ConvPoly.e; module
  unfold ConvPoly.c
  rw [e1, cross2_smul_right, cross2_self]; ring

/-- **The local step along a polygon edge** (Laczkovich Lemma 4.3, local content, with Lemma 8.1 (ii),(iii)): two consecutive tiles `j1` (ending at `V`) and `j2` (starting at `V`) of the walk along the
edge `i`, `V` in the relative interior of the edge. (βγ) a `{β,γ}` pair of the tile `j1` is copied by `j2`; (α) `α` at the tail of `j1` gives `α` at the tail of `j2`; (α') `α` at the head of `j2`
gives `α` at the head of `j1`. -/
theorem edge_consec (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseIV D idx) (i : Fin M) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {V : Plane}
    (hV : V = (1 - t) • P.v i + t • P.v (i + 1)) {U U'' : Plane} {j1 j2 : Fin N}
    (h1 : TriStep (D.tile j1) (toV2 (P.e i)) U V) (h2 : TriStep (D.tile j2) (toV2 (P.e i)) V U'')
    (kR fR kL fL : Fin 3) (hR1 : (D.tile j2).pts kR = V) (hR2 : (D.tile j2).pts fR = U'')
    (hL1 : (D.tile j1).pts kL = V) (hL2 : (D.tile j1).pts fL = U) :
    (((idx j1 fL = 1 ∧ idx j1 kL = 2) ∨ (idx j1 fL = 2 ∧ idx j1 kL = 1)) → idx j2 kR = idx j1 fL ∧ idx j2 fR = idx j1 kL) ∧
    (idx j1 fL = 0 → idx j2 kR = 0) ∧ (idx j2 fR = 0 → idx j1 kL = 0) ∧
    (((idx j2 kR = 1 ∧ idx j2 fR = 2) ∨ (idx j2 kR = 2 ∧ idx j2 fR = 1)) → idx j2 kR = idx j1 fL ∧ idx j2 fR = idx j1 kL) := by
  classical
  have hvert : ∃ j k, (D.tile j).pts k = V := ⟨j2, kR, hR1⟩
  have hnot : V ∉ interior D.region := by
    rw [hreg]
    exact not_interior_of_c_zero P (i := i) (by rw [hV]; exact c_on_edge P i t)
  have hnoGa : ∀ H', ¬ GaEdge D.toRegionDissection (slen D 0) V H' := fun H' hH' => lemma81_ii' D P hreg idx h hnot (Or.inl hH')
  have hnoGk : ∀ Z, ¬ GkEdge D.toRegionDissection idx V Z := fun Z hZ => lemma81_ii' D P hreg idx h hnot (Or.inr hZ)
  obtain ⟨pT, F, s1, s2, s3, hpd, hF, hc2, hnorm, hno1, hno2⟩ := edge_vertex_data D P hreg idx h i ht0 ht1 hV hvert hnoGa hnoGk
  have hi : V ∈ (D.tile j1).carrier := hL1 ▸ subset_convexHull ℝ _ ⟨kL, rfl⟩
  have hi2 : V ∈ (D.tile j2).carrier := hR1 ▸ subset_convexHull ℝ _ ⟨kR, rfl⟩
  have e1 := fan_start_unique hF hpd h2 hi2
  have e3 := fan_end_unique hF hpd h1 hi
  have hj2 : s1.1 = j2 := by rw [← e1]
  have hj1 : s3.1 = j1 := by rw [← e3]
  have hR2' : Par (toV2 ((D.tile s1.1).pts fR - V)) pT := by
    rw [hj2, hR2]
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := h2
    exact hpar.trans hpd.symm
  have hL2' : Par (toV2 ((D.tile s3.1).pts fL - V)) (-pT.1, -pT.2) := by
    rw [hj1, hL2]
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := h1
    have hneg : toV2 (U - V) = (-(toV2 (V - U)).1, -(toV2 (V - U)).2) := by
      unfold toV2; ext <;> simp
    rw [hneg]
    exact (par_neg hpar).trans (par_neg hpd).symm
  have := side_step_all D idx h.hidx V hF hc2 h.hab h.hac hnorm hno1 hno2 kR fR kL fL (by rw [hj2]; exact hR1) hR2'
    (by rw [hj1]; exact hL1) hL2'
  rw [hj2, hj1] at this
  exact this


end Erdos634.Draft.LaczFormal.RG
