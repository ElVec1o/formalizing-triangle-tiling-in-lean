-- Draft/LaczFormalRGBdy4.lean -- S4 of PLAN_THM21: at a vertex `U` in the relative interior of an edge of the polygon, the two tile sides of the walk along the edge that meet at `U`
-- are both of length `a` or both not (Laczkovich Lemma 9.1 (iii), the argument "an edge of Gamma_a must start from U_i"), for `gamma = pi/2`.
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Lemma 9.1 (iii)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRGWalk2
import Erdos634.Draft.LaczFormalRGBal

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- A point on the line of an edge is not an interior point of the polygon. -/
theorem not_interior_of_c_zero (P : ConvPoly M) {U : Plane} {i : Fin M} (h : P.c i U = 0) : U ∉ interior P.carrier := by
  intro hint
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior U hint
  have hE := P.e_ne_zero P.three_le i
  have hn : 0 < (P.e i 0) ^ 2 + (P.e i 1) ^ 2 := by
    by_contra hh
    apply hE
    have h0 : P.e i 0 = 0 := by nlinarith [sq_nonneg (P.e i 0), sq_nonneg (P.e i 1)]
    have h1 : P.e i 1 = 0 := by nlinarith [sq_nonneg (P.e i 0), sq_nonneg (P.e i 1)]
    ext j; fin_cases j <;> simp [h0, h1]
  set nrm : Plane := Erdos634.CertCoord.mkPt (P.e i 1) (-(P.e i 0)) with hnrm
  set ε : ℝ := r / (2 * (‖nrm‖ + 1)) with hε
  have hεpos : 0 < ε := by positivity
  have hdist : dist (U + ε • nrm) U < r := by
    rw [dist_eq_norm]
    have : U + ε • nrm - U = ε • nrm := by abel
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos hεpos, hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    have := norm_nonneg nrm
    nlinarith
  have hmem := interior_subset (hball (Metric.mem_ball.mpr hdist))
  have hci := hmem i
  have hc : P.c i (U + ε • nrm) = - (ε * ((P.e i 0) ^ 2 + (P.e i 1) ^ 2)) := by
    have e1 : U + ε • nrm - P.v i = (U - P.v i) + ε • nrm := by abel
    unfold ConvPoly.c at h ⊢
    rw [e1, cross2_add_right, cross2_smul_right, h]
    unfold cross2
    simp [hnrm, Erdos634.CertCoord.mkPt]
    ring
  have : P.c i (U + ε • nrm) < 0 := by rw [hc]; have := mul_pos hεpos hn; linarith
  exact absurd hci (not_le.mpr this)

/-- `cnt 1 + cnt 2` is the number of tiles through `H` having a non-`α` vertex at `H` (`x0` is any tile through `H`, used as a default). -/
theorem corner_tile_count (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (H : Plane)
    (x0 : AtV D.toRegionDissection H) :
    (Finset.univ.filter (fun x : AtV D.toRegionDissection H => ∃ k : Fin 3, (D.tile x.1).pts k = H ∧ idx x.1 k ≠ 0)).card =
      cnt D idx H 1 + cnt D idx H 2 := by
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

set_option maxHeartbeats 1600000 in
/-- **Lemma 9.1 (iii), the step argument.**  Let `U` be a vertex of the tiling in the relative interior of the edge `i` of the polygon, `j1` the tile of the walk arriving at `U`
and `j2` the tile of the walk leaving it.  Then their sides on the edge are both of length `a` or both not: otherwise an edge of `Γ_a` would start at the boundary point `U`. -/
theorem bdy_step_status (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    (hhp : HalfPar D idx)
    (i : Fin M) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {U1 U2 : Plane} {j1 j2 : Fin N}
    (h1 : TriStep (D.tile j1) (toV2 (P.e i)) U1 ((1 - t) • P.v i + t • P.v (i + 1)))
    (h2 : TriStep (D.tile j2) (toV2 (P.e i)) ((1 - t) • P.v i + t • P.v (i + 1)) U2) :
    (dist U1 ((1 - t) • P.v i + t • P.v (i + 1)) = slen D 0 ↔ dist ((1 - t) • P.v i + t • P.v (i + 1)) U2 = slen D 0) := by
  classical
  set U : Plane := (1 - t) • P.v i + t • P.v (i + 1) with hU
  set d := toV2 (P.e i) with hd
  by_contra hxor
  obtain ⟨kk2, f2, g2, hk2, hf2, hfk2, hgk2, hgf2, hpar2, hleft2⟩ := id h2
  obtain ⟨kk1, f1, g1, hk1, hf1, hfk1, hgk1, hgf1, hpar1, hleft1⟩ := id h1
  have hvert : ∃ j k, (D.tile j).pts k = U := ⟨j2, kk2, hk2⟩
  obtain ⟨pT, F, hpd, hpe, hqe, hTgt⟩ := fan_open_edge D.toRegionDissection P hreg i ht0 ht1 hvert
  have hpT : pT ≠ 0 := hpd.ne_left
  have hdis := tiles_disjoint D.toRegionDissection U F.p F.q F.hloc
  -- the sectors of the two walk tiles
  have hmem2 : U ∈ (D.tile j2).carrier := hk2 ▸ subset_convexHull ℝ _ ⟨kk2, rfl⟩
  have hmem1 : U ∈ (D.tile j1).carrier := hf1 ▸ subset_convexHull ℝ _ ⟨f1, rfl⟩
  set x2 : AtV D.toRegionDissection U := ⟨j2, hmem2⟩ with hx2
  set x1 : AtV D.toRegionDissection U := ⟨j1, hmem1⟩ with hx1
  have hc2 : ∃ k, (D.tile x2.1).pts k = U := ⟨kk2, hk2⟩
  have hc1 : ∃ k, (D.tile x1.1).pts k = U := ⟨f1, hf1⟩
  obtain ⟨kk2', fl2, hk2', hp2, hq2⟩ := spec_corner_data (F.hspec x2) hc2
  obtain ⟨kk1', fl1, hk1', hp1, hq1⟩ := spec_corner_data (F.hspec x1) hc1
  have hcr2 := crs_pos_of_corner (F.hok x2) (F.hspec x2) hc2
  have hcr1 := crs_pos_of_corner (F.hok x1) (F.hspec x1) hc1
  have hkk2 : kk2' = kk2 := (D.tile j2).indep.injective (hk2'.trans hk2.symm)
  have hkk1 : kk1' = f1 := (D.tile j1).indep.injective (hk1'.trans hf1.symm)
  have hP2 : Par (F.p x2) d := triStep_start h2 kk2' fl2 hk2' hp2 hq2 (F.hok x2)
  have hQ1 : Par (F.q x1) (neg2 d) := triStep_end h1 kk1' fl1 hk1' hp1 hq1 (F.hok x1)
  -- lengths
  have hn2 : nsq (F.p x2) = dist U U2 ^ 2 := by
    have hq' : Par (toV2 ((D.tile j2).pts (armP kk2' fl2) - U)) d := hp2 ▸ hP2
    have := parm_eq (T := D.tile j2) fl2 hk2' (W := U2) (w := f2) hf2 (by rw [hkk2]; exact hfk2) hq' hpar2
    rw [hp2, nsq_toV2_sub, this, dist_comm]
  have hn1 : nsq (F.q x1) = dist U1 U ^ 2 := by
    have hq' : Par (toV2 ((D.tile j1).pts (armQ kk1' fl1) - U)) (neg2 d) := hq1 ▸ hQ1
    have hW : Par (toV2 (U1 - U)) (neg2 d) := par_neg_arm hpar1
    have := qarm_eq (T := D.tile j1) fl1 hk1' (W := U1) (w := kk1) hk1 (by rw [hkk1]; exact hfk1.symm) hq' hW
    rw [hq1, nsq_toV2_sub, this]
  -- x1 ≠ x2
  have hx12 : x1 ≠ x2 := by
    intro h
    rw [h] at hQ1
    obtain ⟨c1, hc1', hcp⟩ := hP2.smul
    obtain ⟨c2, hc2', hcq⟩ := hQ1.smul
    have : crs (F.p x2) (F.q x2) = 0 := by
      rw [hcp, hcq]; unfold crs neg2; simp only; ring
    linarith
  -- sector sum
  have hsumT : ∑ x : AtV D.toRegionDissection U, wd (F.p x) (F.q x) ≤ Real.pi := by
    have hv : ∑ j : Unit, wd (F.pe j) (F.qe j) = Real.pi := by
      rw [Fintype.sum_unique]
      show wd (F.pe ()) (F.qe ()) = Real.pi
      rw [hpe, hqe, wd_ext hpT]
    have := F.hsum
    linarith
  -- no straight tile
  have hnostr : ∀ x : AtV D.toRegionDissection U, ∃ k, (D.tile x.1).pts k = U := by
    intro x
    rcases F.hspec x with ⟨k, hk, -⟩ | ⟨hnv, m', -, -, hq, -⟩
    · exact ⟨k, hk⟩
    · exfalso
      have hw : wd (F.p x) (F.q x) = Real.pi := by rw [hq]; exact wd_straight (F.hok x).ne_p
      have hne : x ≠ x2 := by
        intro h; subst h; exact hnv kk2 hk2
      exact no_straight_of_sum F.p F.q F.hok hne hw hsumT
  have hcrall : ∀ x : AtV D.toRegionDissection U, 0 < crs (F.p x) (F.q x) := fun x => crs_pos_of_corner (F.hok x) (F.hspec x) (hnostr x)
  -- counts
  have hStrn : Strn D.toRegionDissection U = ∅ := by
    ext j
    simp only [Strn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_and, not_forall, not_not]
    intro hj
    exact hnostr ⟨j, hj⟩
  have hang := head_angle_sum_gen D idx hidxA F
  have hvirt : ∑ j : Unit, wd (F.pe j) (F.qe j) = Real.pi := by
    rw [Fintype.sum_unique]
    show wd (F.pe ()) (F.qe ()) = Real.pi
    rw [hpe, hqe, wd_ext hpT]
  rw [hStrn, hvirt] at hang
  simp only [Finset.card_empty, Nat.cast_zero, mul_zero, add_zero] at hang
  rw [Fin.sum_univ_three] at hang
  have hsum' : ∑ l, (cnt D idx U l : ℝ) * D.model.angleAt l = Real.pi := by
    rw [Fin.sum_univ_three]
    linarith
  have h3 := hhp U hsum'
  -- the half-fan lemma
  obtain ⟨j0, hj0, hej0⟩ := F.hsurj (Sum.inr ())
  have hLcard : Fintype.card (AtV D.toRegionDissection U ⊕ Unit) = Fintype.card (AtV D.toRegionDissection U) + 1 := by
    rw [Fintype.card_sum]; simp
  have hAt2 : 2 ≤ Fintype.card (AtV D.toRegionDissection U) := by
    have : ({x1, x2} : Finset (AtV D.toRegionDissection U)).card = 2 := Finset.card_pair hx12
    have h := Finset.card_le_card (Finset.subset_univ ({x1, x2} : Finset (AtV D.toRegionDissection U)))
    rw [this] at h
    simpa using h
  have hedge : ∃ H', GaEdge D.toRegionDissection (slen D 0) U H' := by
    refine half_fan_edge D idx hidx hnc hab hac F j0 ?_ (by omega) ?_ ?_ ?_
    · rw [hej0]
      show F.qe () = (-(F.pe ()).1, -(F.pe ()).2)
      rw [hpe, hqe]; simp
    · intro m hm1 hm2
      have : ∃ x : AtV D.toRegionDissection U, F.e (j0 + m) = Sum.inl x := by
        rcases hx : F.e (j0 + m) with x | u
        · exact ⟨x, rfl⟩
        · exfalso
          have h' : F.e (j0 + m) = F.e (j0 + 0) := by
            show F.e (j0 + m) = F.e j0
            rw [hx, hej0]
          have := e_inj_shift F j0 hm2 (by omega) h'
          omega
      obtain ⟨x, hx⟩ := this
      exact ⟨x, hx, hcrall x⟩
    · intro b a hb ha
      have hPb : Par (F.p b) pT := by
        have := F.hP j0
        rw [hej0, hb] at this
        simpa [hqe] using this
      have hb2 : b = x2 := by
        by_contra hne
        have hpp : Par (F.p x2) (F.p b) := hP2.trans (hpd.symm.trans hPb.symm)
        exact start_inj F.p F.q F.hok hdis hne hpp
      have hQa : Par (-pT.1, -pT.2) (F.q a) := by
        have := F.hP (j0 + (Fintype.card (AtV D.toRegionDissection U ⊕ Unit) - 1))
        rw [show j0 + (Fintype.card (AtV D.toRegionDissection U ⊕ Unit) - 1) + 1 = j0 + Fintype.card (AtV D.toRegionDissection U ⊕ Unit) by omega,
          F.hper j0, hej0, ha] at this
        simpa [hpe] using this
      have ha1 : a = x1 := by
        by_contra hne
        have hdn : Par (F.q x1) (-pT.1, -pT.2) := hQ1.trans (by
          have := par_neg hpd
          exact this.symm)
        have hqq : Par (F.q x1) (F.q a) := hdn.trans hQa
        exact end_inj' F.p F.q F.hok hdis (Ne.symm hne) hqq.symm
      rw [hb2, ha1, hn2, hn1]
      intro hiff
      apply hxor
      have e1 : dist U1 U = slen D 0 ↔ dist U1 U ^ 2 = slen D 0 ^ 2 :=
        (pow_left_inj₀ dist_nonneg (slen_pos D 0).le two_ne_zero).symm
      have e2 : dist U U2 = slen D 0 ↔ dist U U2 ^ 2 = slen D 0 ^ 2 :=
        (pow_left_inj₀ dist_nonneg (slen_pos D 0).le two_ne_zero).symm
      rw [e1, e2]
      exact hiff.symm
    · have hc := corner_tile_count D idx U x2
      refine Eq.trans (congrArg (· % 2) ?_) h3
      rw [← hc]
      apply congrArg Finset.card
      ext x
      simp [hej0]
  obtain ⟨H', hH'⟩ := hedge
  have hci : P.c i U = 0 := by
    rw [hU, ConvPoly.c_comb, P.c_self, P.c_next]; simp
  exact lemma91_ii D idx hidx hidxA hnc hab hac hhp (by rw [hreg]; exact not_interior_of_c_zero P hci) hH'

end Erdos634.Draft.LaczFormal.RG
