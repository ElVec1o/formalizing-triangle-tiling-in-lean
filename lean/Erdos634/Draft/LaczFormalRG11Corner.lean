-- Draft/LaczFormalRG11Corner.lean -- Laczkovich DCG 48 (2012), Lemma 4.3 (iii) for polygon sides (Case II, `Gamma_a`, general gamma): a polygon vertex of type `alpha+beta` (cnt = (1,1,0)) from which no edge of `Gamma_a`
-- starts has its two corner tiles classified (the tile with `beta` at the vertex has `gamma` at its other end of the polygon side), and `side_no_ab_a`: a side whose both ends are of type `alpha+beta` with no edge of
-- `Gamma_a` starting at either end (and normal, edge-free interior vertices) is impossible.  The corner classification follows `RG4Corner.vertex_class` (two-corner `alpha,beta` branch) with CaseA hypotheses.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Lemma 4.3 (iii) and its proof, Fig. 3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG9Ia1
import Erdos634.Draft.LaczFormalRG4Corner

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

set_option maxHeartbeats 6400000 in
/-- **Corner classification, type `alpha+beta`, no `Gamma_a` edge** (Case II). -/
theorem corner_ab_class (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseA D idx) (k : Fin M)
    (hA0 : cnt D idx (P.v (k + 1)) 0 = 1) (hA1 : cnt D idx (P.v (k + 1)) 1 = 1) (hA2 : cnt D idx (P.v (k + 1)) 2 = 0)
    (hnoGaV : ∀ H', ¬ GaEdge D.toRegionDissection (slen D 0) (P.v (k + 1)) H') :
    ∀ (jo : Fin N) (Uo : Plane) (ji : Fin N) (Ui : Plane),
      TriStep (D.tile jo) (toV2 (P.e (k + 1))) (P.v (k + 1)) Uo → TriStep (D.tile ji) (toV2 (P.e k)) Ui (P.v (k + 1)) →
        ((TyAt D idx jo (P.v (k + 1)) 0 ∧ TyAt D idx ji (P.v (k + 1)) 1 ∧ TyAt D idx ji Ui 2) ∨
         (TyAt D idx jo (P.v (k + 1)) 1 ∧ TyAt D idx jo Uo 2 ∧ TyAt D idx ji (P.v (k + 1)) 0)) := by
  classical
  intro jo Uo ji Ui hSo hSi
  set V := P.v (k + 1) with hVdef
  have hvert : ∃ j k', (D.tile j).pts k' = V := poly_vertex_is_tile_vertex D.toRegionDissection P hreg (k + 1)
  obtain ⟨pT, qT, F, hpd, hqd, hcr, h1, h2, h3, h4, h5⟩ := fan_vertex_poly D.toRegionDissection P hreg k hvert
  have hqT : qT ≠ 0 := by intro h; rw [h] at hcr; unfold crs at hcr; simp at hcr
  have hpT : pT ≠ 0 := hpd.ne_left
  obtain ⟨i0, k0, hk0⟩ := hvert
  have hmem0 : V ∈ (D.tile i0).carrier := hk0 ▸ subset_convexHull ℝ _ ⟨k0, rfl⟩
  have hAt : 0 < Fintype.card (AtV D.toRegionDissection V) := Fintype.card_pos_iff.mpr ⟨⟨i0, hmem0⟩⟩
  obtain ⟨c, hc1, hcn, hadj, hsurjc, hinjc⟩ := corner_chain F hcr h1 h2 h3 h4 h5 hAt
  set n := Fintype.card (AtV D.toRegionDissection V) with hn
  have hsumT := corner_tile_sum D.toRegionDissection F hcr h1 h2 h3 h4
  have hwlt := wd_lt_pi_of_crs_pos hcr
  have hwpos := wd_pos (Or.inl hcr : SecOK pT qT)
  have hnostr : ∀ x : AtV D.toRegionDissection V, ∃ k, (D.tile x.1).pts k = V := by
    intro x
    rcases F.hspec x with ⟨k, hk, -⟩ | ⟨hnv, m', -, -, hq, -⟩
    · exact ⟨k, hk⟩
    · exfalso
      have hw : wd (F.p x) (F.q x) = Real.pi := by rw [hq]; exact wd_straight (F.hok x).ne_p
      have hle : wd (F.p x) (F.q x) ≤ ∑ y : AtV D.toRegionDissection V, wd (F.p y) (F.q y) :=
        Finset.single_le_sum (f := fun y => wd (F.p y) (F.q y)) (fun y _ => (wd_pos (F.hok y)).le) (Finset.mem_univ x)
      linarith
  have hcrall : ∀ x : AtV D.toRegionDissection V, 0 < crs (F.p x) (F.q x) :=
    fun x => crs_pos_of_corner (F.hok x) (F.hspec x) (hnostr x)
  have hStrn : Strn D.toRegionDissection V = ∅ := by
    ext j
    simp only [Strn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_and, not_forall, not_not]
    intro hj
    exact hnostr ⟨j, hj⟩
  have hnN : n = 2 := by
    rw [hn, card_atV, card_corn D idx V, hStrn]
    simp only [Finset.card_empty, add_zero, Fin.sum_univ_three]
    omega
  have hn2 : n = 2 := hnN
  have hdis := tiles_disjoint D.toRegionDissection V F.p F.q F.hloc
  have hd1 : Par (toV2 (P.e (k + 1))) pT := hpd.symm
  have hqe' : Par qT (neg2 (toV2 (P.e k))) := by
    have e : toV2 (P.v k - P.v (k + 1)) = neg2 (toV2 (P.e k)) := by
      unfold neg2 toV2 ConvPoly.e; ext <;> simp
    rw [e] at hqd; exact hqd
  -- the out tile
  obtain ⟨kko, fo, go, hko, hfo, hfko, hgko, hgfo, hparo, hlefto⟩ := id hSo
  have hmemo : V ∈ (D.tile jo).carrier := hko ▸ subset_convexHull ℝ _ ⟨kko, rfl⟩
  set xo : AtV D.toRegionDissection V := ⟨jo, hmemo⟩ with hxo
  obtain ⟨kko', flo, hko', hpo, hqo⟩ := spec_corner_data (F.hspec xo) ⟨kko, hko⟩
  have hkko : kko' = kko := (D.tile jo).indep.injective (hko'.trans hko.symm)
  have hPxo : Par (F.p xo) (toV2 (P.e (k + 1))) := triStep_start hSo kko' flo hko' hpo hqo (F.hok xo)
  have hxo1 : xo = c 1 := by
    by_contra hne
    exact start_inj F.p F.q F.hok hdis (Ne.symm hne) (hPxo.trans (hd1.trans hc1.symm))
  have hqo' : Par (toV2 ((D.tile jo).pts (armP kko' flo) - V)) (toV2 (P.e (k + 1))) := hpo ▸ hPxo
  have harmo : (D.tile jo).pts (armP kko' flo) = Uo :=
    parm_eq (T := D.tile jo) flo hko' (W := Uo) (w := fo) hfo (by rw [hkko]; exact hfko) hqo' hparo
  -- the in tile
  obtain ⟨kki, fi, gi, hki, hfi, hfki, hgki, hgfi, hpari, hlefti⟩ := id hSi
  have hmemi : V ∈ (D.tile ji).carrier := hfi ▸ subset_convexHull ℝ _ ⟨fi, rfl⟩
  set xi : AtV D.toRegionDissection V := ⟨ji, hmemi⟩ with hxi
  obtain ⟨kki', fli, hki', hpi, hqi⟩ := spec_corner_data (F.hspec xi) ⟨fi, hfi⟩
  have hkki : kki' = fi := (D.tile ji).indep.injective (hki'.trans hfi.symm)
  have hQxi : Par (F.q xi) (neg2 (toV2 (P.e k))) := triStep_end hSi kki' fli hki' hpi hqi (F.hok xi)
  have hxin : xi = c n := by
    by_contra hne
    exact end_inj' F.p F.q F.hok hdis (Ne.symm hne) (hQxi.trans (hqe'.symm.trans hcn))
  have hqi' : Par (toV2 ((D.tile ji).pts (armQ kki' fli) - V)) (neg2 (toV2 (P.e k))) := hqi ▸ hQxi
  have hW : Par (toV2 (Ui - V)) (neg2 (toV2 (P.e k))) := par_neg_arm hpari
  have harmi : (D.tile ji).pts (armQ kki' fli) = Ui :=
    qarm_eq (T := D.tile ji) fli hki' (W := Ui) (w := kki) hki (by rw [hkki]; exact hfki.symm) hqi' hW
  -- types of the arms
  have hab := h.hab
  have hac := h.hac
  have sqo : nsq (F.q xo) = slen D 0 ^ 2 ↔ idx jo (armP kko' flo) = 0 := nsq_q_iff D idx h.hidx hab hac flo hko' hqo
  have spo : nsq (F.p xo) = slen D 0 ^ 2 ↔ idx jo (armQ kko' flo) = 0 := nsq_p_iff D idx h.hidx hab hac flo hko' hpo
  have sqi : nsq (F.q xi) = slen D 0 ^ 2 ↔ idx ji (armP kki' fli) = 0 := nsq_q_iff D idx h.hidx hab hac fli hki' hqi
  have spi : nsq (F.p xi) = slen D 0 ^ 2 ↔ idx ji (armQ kki' fli) = 0 := nsq_p_iff D idx h.hidx hab hac fli hki' hpi
  have do1 : idx jo kko' ≠ idx jo (armP kko' flo) := fun e => armP_ne kko' flo ((idx jo).injective e).symm
  have do2 : idx jo kko' ≠ idx jo (armQ kko' flo) := fun e => armQ_ne kko' flo ((idx jo).injective e).symm
  have do3 : idx jo (armP kko' flo) ≠ idx jo (armQ kko' flo) := fun e => armPQ_ne kko' flo ((idx jo).injective e)
  have di1 : idx ji kki' ≠ idx ji (armP kki' fli) := fun e => armP_ne kki' fli ((idx ji).injective e).symm
  have di2 : idx ji kki' ≠ idx ji (armQ kki' fli) := fun e => armQ_ne kki' fli ((idx ji).injective e).symm
  have di3 : idx ji (armP kki' fli) ≠ idx ji (armQ kki' fli) := fun e => armPQ_ne kki' fli ((idx ji).injective e)
  have hnoGa : ∀ H', ¬ GaEdge D.toRegionDissection (slen D 0) V H' := hnoGaV
  have tyo : ∀ t, TyAt D idx jo V t ↔ idx jo kko' = t := fun t => tyAt_iff hko' t
  have tyoU : ∀ t, TyAt D idx jo Uo t ↔ idx jo (armP kko' flo) = t := fun t => tyAt_iff harmo t
  have tyi : ∀ t, TyAt D idx ji V t ↔ idx ji kki' = t := fun t => tyAt_iff hki' t
  have tyiU : ∀ t, TyAt D idx ji Ui t ↔ idx ji (armQ kki' fli) = t := fun t => tyAt_iff harmi t
  · -- two corners
    have hxin2 : xi = c 2 := by rw [hxin, hn2]
    have hne12 : xo ≠ xi := by
      intro e
      rw [hxo1, hxin2] at e
      have := hinjc 1 2 (by norm_num) (by omega) (by norm_num) (by omega) e
      omega
    have hjne : jo ≠ ji := fun e => hne12 (Subtype.ext e)
    have hxy : Par (F.p xi) (F.q xo) := by rw [hxo1, hxin2]; exact hadj 1 le_rfl (by omega)
    have hnb1 : NoBack D.toRegionDissection (F.q xo) V := by
      rw [hxo1]; exact noBack_corner F hcr h5 (tile_ray_mem F (c 1)).2 (F.hok (c 1)).ne_q
    have hjunc : (nsq (F.q xo) = slen D 0 ^ 2 ↔ nsq (F.p xi) = slen D 0 ^ 2) := by
      by_contra hn
      have hx : (nsq (F.q xo) = slen D 0 ^ 2 ∧ nsq (F.p xi) ≠ slen D 0 ^ 2) ∨ (nsq (F.q xo) ≠ slen D 0 ^ 2 ∧ nsq (F.p xi) = slen D 0 ^ 2) := by tauto
      obtain ⟨H', hH'⟩ := ga_edge_of_ray D idx h.hidx h.hnc F xo xi (hcrall xo) (hcrall xi) hxy hnb1 hx
      exact hnoGa H' hH'
    obtain ⟨e1, e2⟩ : cnt D idx V 1 = 1 ∧ cnt D idx V 2 = 0 := ⟨hA1, hA2⟩
    · -- one `α` corner and one `β` corner
      have hc0 : cnt D idx V 0 = 1 := hA0
      have hle : ∀ l : Fin 3, cnt D idx V l ≤ 1 := by
        intro l; fin_cases l <;> simp <;> omega
      have hto2 : idx jo kko' ≠ 2 := by
        intro e; have : 1 ≤ cnt D idx V 2 := cnt_one D idx 2 hko' e; omega
      have hti2 : idx ji kki' ≠ 2 := by
        intro e; have : 1 ≤ cnt D idx V 2 := cnt_one D idx 2 hki' e; omega
      have htne : idx jo kko' ≠ idx ji kki' := by
        intro e
        have h2c : 2 ≤ cnt D idx V (idx jo kko') := cnt_two D idx (idx jo kko') hjne hko' hki' rfl e.symm
        have h1c := hle (idx jo kko')
        omega
      have hcases : ∀ t t' : Fin 3, t ≠ 2 → t' ≠ 2 → t ≠ t' → (t = 0 ∧ t' = 1) ∨ (t = 1 ∧ t' = 0) := by decide
      rcases hcases _ _ hto2 hti2 htne with ⟨ea, eb⟩ | ⟨ea, eb⟩
      · -- jo has `α`, ji has `β`
        left
        have hq1 : ¬ nsq (F.q xo) = slen D 0 ^ 2 := fun hh => do1 (by rw [ea]; exact (sqo.mp hh).symm)
        have hq2 : ¬ nsq (F.p xi) = slen D 0 ^ 2 := fun hh => hq1 (hjunc.mpr hh)
        have hw0 : ¬ idx ji (armQ kki' fli) = 0 := fun hh => hq2 (spi.mpr hh)
        have hw1 : idx ji (armQ kki' fli) ≠ idx ji kki' := fun e => di2 e.symm
        have hfin : ∀ w t : Fin 3, w ≠ 0 → w ≠ t → t = 1 → w = 2 := by decide
        exact ⟨(tyo 0).mpr ea, (tyi 1).mpr eb, (tyiU 2).mpr (hfin _ _ hw0 hw1 eb)⟩
      · -- jo has `β`, ji has `α`
        right
        have hq2 : ¬ nsq (F.p xi) = slen D 0 ^ 2 := fun hh => di2 (by rw [eb]; exact (spi.mp hh).symm)
        have hq1 : ¬ nsq (F.q xo) = slen D 0 ^ 2 := fun hh => hq2 (hjunc.mp hh)
        have hu0 : ¬ idx jo (armP kko' flo) = 0 := fun hh => hq1 (sqo.mpr hh)
        have hu1 : idx jo (armP kko' flo) ≠ idx jo kko' := fun e => do1 e.symm
        have hfin : ∀ w t : Fin 3, w ≠ 0 → w ≠ t → t = 1 → w = 2 := by decide
        exact ⟨(tyo 1).mpr ea, (tyoU 2).mpr (hfin _ _ hu0 hu1 ea), (tyi 0).mpr eb⟩

set_option maxHeartbeats 3200000 in
/-- **Lemma 4.3 (iii), polygon side, `Γ_a`** (general `γ`): the side `i` has normal interior vertices without outgoing `Γ_a` edge; both ends are of type `α+β` (cnt = (1,1,0)) and no edge of `Γ_a` starts at
either end.  Impossible.  (Equivalently: of two adjacent polygon vertices of type `α+β`, one has an outgoing `Γ_a` edge.) -/
theorem side_no_ab_a (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseA D idx) (i : Fin M)
    (hnormv : ∀ V : Plane, (∃ j k, (D.tile j).pts k = V) → (∃ t : ℝ, 0 < t ∧ t < 1 ∧ V = (1 - t) • P.v i + t • P.v (i + 1)) →
      cnt D idx V 0 = 1 ∧ cnt D idx V 1 = 1 ∧ cnt D idx V 2 = 1)
    (hno : ∀ V : Plane, (∃ j k, (D.tile j).pts k = V) → (∃ t : ℝ, 0 < t ∧ t < 1 ∧ V = (1 - t) • P.v i + t • P.v (i + 1)) →
      ∀ H', ¬ GaEdge D.toRegionDissection (slen D 0) V H')
    (hX0 : cnt D idx (P.v i) 0 = 1) (hX1 : cnt D idx (P.v i) 1 = 1) (hX2 : cnt D idx (P.v i) 2 = 0)
    (hY0 : cnt D idx (P.v (i + 1)) 0 = 1) (hY1 : cnt D idx (P.v (i + 1)) 1 = 1) (hY2 : cnt D idx (P.v (i + 1)) 2 = 0)
    (hnoX : ∀ H', ¬ GaEdge D.toRegionDissection (slen D 0) (P.v i) H') (hnoY : ∀ H', ¬ GaEdge D.toRegionDissection (slen D 0) (P.v (i + 1)) H') : False := by
  classical
  obtain ⟨L, e0, el, hW, hh, hl, hs1, hs2, hT0, hT1⟩ := edge_data D P hreg i
  obtain ⟨L', e0', el', hW', hh', hl', hs1', hs2', hT0', hT1'⟩ := edge_data D P hreg (i - 1)
  obtain ⟨L'', e0'', el'', hW'', hh'', hl'', hs1'', hs2'', hT0'', hT1''⟩ := edge_data D P hreg (i + 1)
  have hT0x : TriStep (D.tile e0.1) (toV2 (P.e i)) (P.v i) e0.2.2 := by rw [← hs1]; exact hT0
  have hT1x : TriStep (D.tile el.1) (toV2 (P.e i)) el.2.1 (P.v (i + 1)) := by rw [← hs2]; exact hT1
  have hs2'x : el'.2.2 = P.v i := by rw [hs2']; simp
  have hT1'x : TriStep (D.tile el'.1) (toV2 (P.e (i - 1))) el'.2.1 (P.v (i - 1 + 1)) := by rw [← hs2']; exact hT1'
  have hT0''x : TriStep (D.tile e0''.1) (toV2 (P.e (i + 1))) (P.v (i + 1)) e0''.2.2 := by rw [← hs1'']; exact hT0''
  have cX := corner_ab_class D P hreg idx h (i - 1) (by simpa using hX0) (by simpa using hX1) (by simpa using hX2) (by simpa using hnoX)
    e0.1 e0.2.2 el'.1 el'.2.1 (by simpa using hT0x) hT1'x
  have cY := corner_ab_class D P hreg idx h i hY0 hY1 hY2 hnoY e0''.1 e0''.2.2 el.1 el.2.1 hT0''x hT1x
  simp only [sub_add_cancel] at cX
  have hR := walk_rules_a D P hreg idx h i hnormv hno hW hh hl
  obtain ⟨kk, f, g, hk, hf, hfk, -⟩ := id hT1
  have hhead : ∀ t : Fin 3, TyAt D idx el.1 el.2.2 t ↔ idx el.1 f = t := fun t => tyAt_iff hf t
  have htail : ∀ t : Fin 3, TyAt D idx el.1 el.2.1 t ↔ idx el.1 kk = t := fun t => tyAt_iff hk t
  have hne : idx el.1 f ≠ idx el.1 kk := fun e => hfk ((idx el.1).injective e)
  have hYh : ∀ t : Fin 3, TyAt D idx el.1 (P.v (i + 1)) t ↔ idx el.1 f = t := fun t => by rw [← hs2]; exact hhead t
  rcases cX with ⟨a1, -, -⟩ | ⟨b1, b2, -⟩
  · -- tail of the first tile is `α`
    have t0 := hR.2.1 (by rw [hs1]; exact a1)
    have e0' := (htail 0).mp t0
    rcases cY with ⟨-, c2, c3⟩ | ⟨-, -, c3⟩
    · have := (htail 2).mp c3
      rw [e0'] at this; exact absurd this (by decide)
    · have := (hYh 0).mp c3
      exact hne (this.trans e0'.symm)
  · -- `β` at the tail and `γ` at the head of the first tile
    have t1 := (hR.1 1 2 (Or.inl ⟨rfl, rfl⟩)).mp ⟨by rw [hs1]; exact b1, b2⟩
    have e2 := (hhead 2).mp t1.2
    rcases cY with ⟨-, c2, -⟩ | ⟨-, -, c3⟩
    · have := (hYh 1).mp c2
      rw [e2] at this; exact absurd this (by decide)
    · have := (hYh 0).mp c3
      rw [e2] at this; exact absurd this (by decide)

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.corner_ab_class
#print axioms Erdos634.Draft.LaczFormal.RG.side_no_ab_a
