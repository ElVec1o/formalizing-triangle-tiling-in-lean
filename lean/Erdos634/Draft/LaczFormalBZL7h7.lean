-- Draft/LaczFormalBZL7h7.lean -- Beeson (arXiv 1206.1974v7) Lemma 10.5 (G5), the JUNCTION: at a vertex `Q` in the relative interior of a side of the polygon where the tile step `U -> Q` and the next tile step `Q -> U'` along the side
-- differ in whether their length is `a`, and the number of non-alpha corners at `Q` is even, an edge of Gamma_a (here: of the relabelled tile, Gamma_c) STARTS at `Q`.  Proof: the fan at `Q` with ONE virtual straight sector (exterior), the half-fan lemma.
-- NOTE, UNAUDITED.  Credit: Beeson (arXiv 1206.1974v7, Lemma 10.5), Laczkovich (DCG 48 (2012), Lemmas 4.2, 4.5: half-fan lemma), Beeson-Zhang.
import Erdos634.Draft.LaczFormalBZL7h6

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem end_inj_sum' {D : RegionDissection N} {V : Plane} {κ : Type} [Fintype κ] (F : ExtFan D V κ) {o o' : AtV D V ⊕ κ} (h : o ≠ o') :
    ¬ Par (Sum.elim F.q F.qe o') (Sum.elim F.q F.qe o) :=
  end_inj' (Sum.elim F.p F.pe) (Sum.elim F.q F.qe) (fun o => by rcases o with s | j; exact F.hok s; exact F.hokE j)
    (fun s t hst z => F.disj_all hst z) h

/-- The number of sectors that are tile corners of non-alpha type equals `cnt 1 + cnt 2` (no condition on the other sectors). -/
theorem corner_count_atv (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {H : Plane} (x0 : AtV D.toRegionDissection H) :
    (Finset.univ.filter (fun x : AtV D.toRegionDissection H => ∃ k : Fin 3, (D.tile x.1).pts k = H ∧ idx x.1 k ≠ 0)).card = cnt D idx H 1 + cnt D idx H 2 := by
  classical
  rw [cnt_nonzero]
  refine Finset.card_nbij' (fun x => (x.1, if h : ∃ k, (D.tile x.1).pts k = H ∧ idx x.1 k ≠ 0 then h.choose else 0))
    (fun p => if h : (D.tile p.1).pts p.2 = H then (⟨p.1, h ▸ subset_convexHull ℝ _ ⟨p.2, rfl⟩⟩ : AtV D.toRegionDissection H)
      else x0) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, dif_pos hx]
    exact hx.choose_spec
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hp
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, dif_pos hp.1]
    exact ⟨p.2, hp.1, hp.2⟩
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx
    beta_reduce
    split_ifs with h1
    · rfl
    · exact absurd (by simpa [dif_pos hx] using hx.choose_spec.1) h1
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hp
    obtain ⟨h1, h2⟩ := hp
    simp only [dif_pos h1]
    have hex : ∃ k, (D.tile p.1).pts k = H ∧ idx p.1 k ≠ 0 := ⟨p.2, h1, h2⟩
    simp only [dif_pos hex]
    have : hex.choose = p.2 := by
      have := hex.choose_spec
      exact (D.tile p.1).indep.injective (this.1.trans h1.symm)
    rw [this]

/-- **The junction lemma (Beeson L10.5 via the half-fan lemma).** -/
theorem junction_edge (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) (P : ConvPoly M) (hreg : D.region = P.carrier) (i : Fin M) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {ju jv : Fin N} {U Q U' : Plane} (hQ : Q = (1 - t) • P.v i + t • P.v (i + 1))
    (hu : TriStep (D.tile ju) (toV2 (P.e i)) U Q) (hv : TriStep (D.tile jv) (toV2 (P.e i)) Q U')
    (hdiff : ¬ (dist Q U' = slen D 0 ↔ dist U Q = slen D 0))
    (hev : (cnt D idx Q 1 + cnt D idx Q 2) % 2 = 0) :
    ∃ H', GaEdge D.toRegionDissection (slen D 0) Q H' := by
  classical
  subst hQ
  set Q : Plane := (1 - t) • P.v i + t • P.v (i + 1) with hQd
  have hab := notComb_ne01 hnc
  have hac := notComb_ne02 hnc
  have hvert : ∃ j k, (D.tile j).pts k = (1 - t) • P.v i + t • P.v (i + 1) := by
    obtain ⟨kk, f, g, hk, -⟩ := hv
    exact ⟨jv, kk, hk⟩
  obtain ⟨pT, F, hpd, hpe, hqe, hTgt⟩ := fan_open_edge D.toRegionDissection P hreg i ht0 ht1 hvert
  have hpT : pT ≠ 0 := hpd.ne_left
  obtain ⟨su, hsu1, hsu_q, hsu_c, hsu_arm⟩ := step_end_sector F hu
  obtain ⟨sv, hsv1, hsv_p, hsv_c, hsv_arm⟩ := step_start_sector F hv
  have hne : su ≠ sv := by
    intro h
    have hj : ju = jv := by rw [← hsu1, ← hsv1, h]
    subst hj
    exact no_through_step hu hv
  obtain ⟨j0, hj0, hej0⟩ := F.hsurj (Sum.inr ())
  set L := Fintype.card (AtV D.toRegionDissection Q ⊕ Unit) with hLdef
  have hLcard : L = Fintype.card (AtV D.toRegionDissection Q) + 1 := by rw [hLdef, Fintype.card_sum]; simp
  have hAt2 : 2 ≤ Fintype.card (AtV D.toRegionDissection Q) := by
    have h2 : ({su, sv} : Finset (AtV D.toRegionDissection Q)).card = 2 := Finset.card_pair hne
    have := Finset.card_le_card (Finset.subset_univ ({su, sv} : Finset (AtV D.toRegionDissection Q)))
    rw [h2] at this
    simpa using this
  have hL3 : 3 ≤ L := by omega
  have hvirt : ∑ j : Unit, wd (F.pe j) (F.qe j) = Real.pi := by
    rw [Fintype.sum_unique]
    show wd (F.pe ()) (F.qe ()) = Real.pi
    rw [hpe, hqe, wd_ext hpT]
  have hreal : ∑ s : AtV D.toRegionDissection Q, wd (F.p s) (F.q s) = Real.pi := by
    have := F.hsum
    linarith
  have hcrs : ∀ x : AtV D.toRegionDissection Q, 0 < crs (F.p x) (F.q x) := by
    intro x
    rcases F.hspec x with ⟨k, hk, -⟩ | ⟨-, m', -, -, hq, -⟩
    · exact crs_pos_of_corner (F.hok x) (F.hspec x) ⟨k, hk⟩
    · exfalso
      have hxw : wd (F.p x) (F.q x) = Real.pi := by rw [hq]; exact wd_straight (F.hok x).ne_p
      have hx_ne : x ≠ su := by
        intro h
        subst h
        have := hsu_c
        rw [hq] at this; unfold crs at this; simp at this; linarith
      have hpair : ∑ s ∈ ({x, su} : Finset (AtV D.toRegionDissection Q)), wd (F.p s) (F.q s) ≤ ∑ s : AtV D.toRegionDissection Q, wd (F.p s) (F.q s) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun s _ _ => (wd_pos (F.hok s)).le)
      rw [Finset.sum_pair hx_ne, hxw, hreal] at hpair
      have := wd_pos (F.hok su)
      linarith
  have hstr : sq' F (F.e j0) = (-(sp F (F.e j0)).1, -(sp F (F.e j0)).2) := by
    rw [hej0]
    simp only [sq', sp, Sum.elim_inr]
    rw [hpe, hqe]; simp
  have hcorn : ∀ m, 1 ≤ m → m < L → ∃ x : AtV D.toRegionDissection Q, F.e (j0 + m) = Sum.inl x ∧ 0 < crs (F.p x) (F.q x) := by
    intro m h1 h2
    rcases hm : F.e (j0 + m) with x | j
    · exact ⟨x, rfl, hcrs x⟩
    · exfalso
      have h' : F.e (j0 + m) = F.e (j0 + 0) := by rw [hm, add_zero, hej0]
      have := e_inj_shift F j0 h2 (by omega : 0 < L) h'
      omega
  have hxor : ∀ b a : AtV D.toRegionDissection Q, F.e (j0 + 1) = Sum.inl b → F.e (j0 + (L - 1)) = Sum.inl a →
      ¬ (nsq (F.p b) = slen D 0 ^ 2 ↔ nsq (F.q a) = slen D 0 ^ 2) := by
    intro b a hb ha
    have hpb : Par (F.p b) (toV2 (P.e i)) := by
      have := F.hP j0
      rw [hb, hej0] at this
      simp only [Sum.elim_inl, Sum.elim_inr] at this
      rw [hqe] at this
      exact this.trans hpd
    have hbsv : b = sv := corner_start_unique F (hcrs b) hsv_c (hpb.trans hsv_p.symm)
    have hqa : Par (F.q a) (-(toV2 (P.e i)).1, -(toV2 (P.e i)).2) := by
      have := F.hP (j0 + (L - 1))
      have hE : F.e (j0 + L) = Sum.inr () := by rw [hLdef]; exact (F.hper j0).trans hej0
      rw [show j0 + (L - 1) + 1 = j0 + L by omega, hE, ha] at this
      simp only [Sum.elim_inl, Sum.elim_inr] at this
      rw [hpe] at this
      exact this.symm.trans (par_neg_neg hpd)
    have hasu : a = su := by
      by_contra hne'
      exact end_inj_sum' F (o := Sum.inl su) (o' := Sum.inl a) (fun h => hne' (Sum.inl_injective h).symm)
        (by simpa using hqa.trans hsu_q.symm)
    subst hbsv; subst hasu
    rw [hsv_arm, hsu_arm, nsq_toV2_sub, nsq_toV2_sub, dist_comm U' _]
    have ha0 : 0 < slen D 0 := slen_pos D 0
    have key : ∀ x : ℝ, 0 ≤ x → (x ^ 2 = slen D 0 ^ 2 ↔ x = slen D 0) := fun x hx => pow_left_inj₀ hx ha0.le two_ne_zero
    rw [key _ dist_nonneg, key _ dist_nonneg]
    exact hdiff
  have hpar : (Finset.univ.filter (fun x : AtV D.toRegionDissection Q =>
      (Sum.inl x : AtV D.toRegionDissection Q ⊕ Unit) ≠ F.e j0 ∧ ∃ k : Fin 3, (D.tile x.1).pts k = Q ∧ idx x.1 k ≠ 0)).card % 2 = 0 := by
    have : (Finset.univ.filter (fun x : AtV D.toRegionDissection Q =>
        (Sum.inl x : AtV D.toRegionDissection Q ⊕ Unit) ≠ F.e j0 ∧ ∃ k : Fin 3, (D.tile x.1).pts k = Q ∧ idx x.1 k ≠ 0)) =
        Finset.univ.filter (fun x : AtV D.toRegionDissection Q => ∃ k : Fin 3, (D.tile x.1).pts k = Q ∧ idx x.1 k ≠ 0) := by
      apply Finset.filter_congr
      intro x _
      rw [hej0]
      simp
    rw [this, corner_count_atv D idx su]
    exact hev
  exact half_fan_edge D idx hidx hnc hab hac F j0 hstr hL3 hcorn hxor (by convert hpar)

end Erdos634.Draft.LaczFormal.RG
