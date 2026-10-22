-- Draft/LaczFormalRG4Corner.lean -- Case IV (gamma = pi/3): classification of the corner of the polygon at a vertex `v_{k+1}`.  The polygon angle is `pi/3` (one `gamma` tile, "E1") or `2 pi/3`
-- (tiles `alpha, beta`, "E2a", or `gamma, gamma`, "E2b"); the types at the vertex and at the far ends of the first tile `jo` of the walk along the outgoing edge `e_{k+1}` and of the last
-- tile `ji` of the walk along the incoming edge `e_k` are determined (Laczkovich, proof of Lemma 8.1 / Sect. 8.1, with Lemma 8.1 (ii): no edge of `Gamma_a u Gamma_k` starts on the boundary).
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.1), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG4Walk

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

set_option maxHeartbeats 6400000 in
/-- **Corner classification (Case IV).** -/
theorem vertex_class (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseIV D idx) (k : Fin M) :
    ∀ (jo : Fin N) (Uo : Plane) (ji : Fin N) (Ui : Plane),
      TriStep (D.tile jo) (toV2 (P.e (k + 1))) (P.v (k + 1)) Uo → TriStep (D.tile ji) (toV2 (P.e k)) Ui (P.v (k + 1)) →
      (P.angle (k + 1) = Real.pi / 3 ∧
        ((TyAt D idx jo (P.v (k + 1)) 2 ∧ TyAt D idx jo Uo 1 ∧ TyAt D idx ji (P.v (k + 1)) 2 ∧ TyAt D idx ji Ui 0) ∨
         (TyAt D idx jo (P.v (k + 1)) 2 ∧ TyAt D idx jo Uo 0 ∧ TyAt D idx ji (P.v (k + 1)) 2 ∧ TyAt D idx ji Ui 1))) ∨
      (P.angle (k + 1) = 2 * Real.pi / 3 ∧
        ((TyAt D idx jo (P.v (k + 1)) 0 ∧ TyAt D idx ji (P.v (k + 1)) 1 ∧ TyAt D idx ji Ui 2) ∨
         (TyAt D idx jo (P.v (k + 1)) 1 ∧ TyAt D idx jo Uo 2 ∧ TyAt D idx ji (P.v (k + 1)) 0) ∨
         (TyAt D idx jo (P.v (k + 1)) 2 ∧ TyAt D idx jo Uo 1 ∧ TyAt D idx ji (P.v (k + 1)) 2 ∧ TyAt D idx ji Ui 1))) := by
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
  have hang := head_angle_sum_gen D idx h.hidxA F
  have hvirt : ∑ j : Bool, wd (F.pe j) (F.qe j) = Real.pi + (Real.pi - wd pT qT) := by
    rw [Fintype.sum_bool, h1, h2, h3, h4, wd_straight hqT, wd_neg_left hcr]; ring
  rw [hStrn, hvirt] at hang
  simp only [Finset.card_empty, Nat.cast_zero, mul_zero, add_zero] at hang
  rw [Fin.sum_univ_three] at hang
  have hsum' : ((cnt D idx V 0 : ℕ) : ℝ) * D.model.angleAt 0 + (cnt D idx V 1 : ℕ) * D.model.angleAt 1 + (cnt D idx V 2 : ℕ) * D.model.angleAt 2 = wd pT qT := by
    linarith
  -- the polygon angle
  have hθ : P.angle (k + 1) = wd pT qT := by
    obtain ⟨ρ, hρ, hiff⟩ := P.vertex_local_T P.three_le k
    have hN : 0 < N := Fin.pos i0
    have hT1 : (P.locTri P.three_le k).pts 1 = V := rfl
    have hiffD : ∀ y, dist y ((P.locTri P.three_le k).pts 1) < ρ → (y ∈ D.region ↔ y ∈ (P.locTri P.three_le k).carrier) := by
      intro y hy; rw [hreg]; exact hiff y hy
    have hs := sum_localAngle_tri D.toRegionDissection hN (P.locTri P.three_le k) hρ hiffD
    have hwdt := tiles_angle_sum D.toRegionDissection V F.p F.q F.hwd
    have hwdT : wd pT qT = (P.locTri P.three_le k).localAngle V := by
      rw [← hsumT, hwdt]; exact hs
    have hloc : (P.locTri P.three_le k).localAngle V = P.angle (k + 1) := by
      have := Tri.localAngle_vertex (P.locTri P.three_le k) 1
      rw [hT1] at this
      rw [this]
      unfold ConvPoly.angle cornerAngle
      have e1 : k + 1 - 1 = k := by simp
      have e2 : k + 1 + 1 = k + 2 := (ConvPoly.fin_facts P.three_le k).2.2.2.2.2
      rw [e1, e2, EuclideanGeometry.angle_comm (P.v k)]
      rfl
    rw [← hloc, hwdT]
  -- counts
  have hpi := Real.pi_pos
  have hr : ((cnt D idx V 0 : ℕ) : ℝ) = (cnt D idx V 1 : ℕ) := by exact_mod_cast h.hregc V
  have hN2 : ((2 * cnt D idx V 1 + cnt D idx V 2 : ℕ) : ℝ) * (Real.pi / 3) = wd pT qT := by
    rw [← hsum', hr, h.hγ]
    have := h.hαβ
    push_cast
    nlinarith [this]
  have hN2pos : 0 < 2 * cnt D idx V 1 + cnt D idx V 2 := by
    by_contra hz
    have : 2 * cnt D idx V 1 + cnt D idx V 2 = 0 := by omega
    rw [this] at hN2
    simp at hN2; linarith
  have hN2lt : 2 * cnt D idx V 1 + cnt D idx V 2 < 3 := by
    by_contra hz
    push Not at hz
    have : (3 : ℝ) ≤ ((2 * cnt D idx V 1 + cnt D idx V 2 : ℕ) : ℝ) := by exact_mod_cast hz
    nlinarith
  have hnN : n = 2 * cnt D idx V 1 + cnt D idx V 2 := by
    rw [hn, card_atV, card_corn D idx V, hStrn]
    simp only [Finset.card_empty, add_zero, Fin.sum_univ_three]
    have := h.hregc V
    omega
  have hn12 : n = 1 ∨ n = 2 := by omega
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
  have hci : P.c (k + 1) V = 0 := by rw [hVdef]; exact P.c_self _
  have hbd : V ∉ interior D.region := by rw [hreg]; exact not_interior_of_c_zero P hci
  have hnoGa : ∀ H', ¬ GaEdge D.toRegionDissection (slen D 0) V H' := fun H' hH' => lemma81_ii' D P hreg idx h hbd (Or.inl hH')
  have hnoGk : ∀ Z, ¬ GkEdge D.toRegionDissection idx V Z := fun Z hZ => lemma81_ii' D P hreg idx h hbd (Or.inr hZ)
  have tyo : ∀ t, TyAt D idx jo V t ↔ idx jo kko' = t := fun t => tyAt_iff hko' t
  have tyoU : ∀ t, TyAt D idx jo Uo t ↔ idx jo (armP kko' flo) = t := fun t => tyAt_iff harmo t
  have tyi : ∀ t, TyAt D idx ji V t ↔ idx ji kki' = t := fun t => tyAt_iff hki' t
  have tyiU : ∀ t, TyAt D idx ji Ui t ↔ idx ji (armQ kki' fli) = t := fun t => tyAt_iff harmi t
  have hang3 : P.angle (k + 1) = ((2 * cnt D idx V 1 + cnt D idx V 2 : ℕ) : ℝ) * (Real.pi / 3) := by rw [hθ, hN2]
  rcases hn12 with hn1 | hn2
  · -- one corner: a single `γ` tile
    have hc1c : cnt D idx V 1 = 0 ∧ cnt D idx V 2 = 1 := by omega
    have hc0c : cnt D idx V 0 = 0 := by have := h.hregc V; omega
    have hto : idx jo kko' = 2 := idx_two_of_cnt D idx hc0c hc1c.1 hko'
    have hti : idx ji kki' = 2 := idx_two_of_cnt D idx hc0c hc1c.1 hki'
    have hxx : xo = xi := by rw [hxo1, hxin, hn1]
    have hjj : jo = ji := congrArg Subtype.val hxx
    have hUne : Uo ≠ Ui := by
      intro hU
      have hP : F.p xo = F.q xi := by
        rw [hpo, hqi, harmo, harmi, hU]
      rw [← hxx] at hP
      have h0 : crs (F.p xo) (F.q xo) = 0 := by rw [hP]; unfold crs; ring
      have := hcrall xo
      linarith
    subst hjj
    have hidxne : idx jo (armP kko' flo) ≠ idx jo (armQ kki' fli) := by
      intro e
      have e' : armP kko' flo = armQ kki' fli := (idx jo).injective e
      apply hUne
      rw [← harmo, ← harmi, e']
    have hu2 : idx jo (armP kko' flo) ≠ 2 := by rw [← hto]; exact fun e => do1 e.symm
    have hw2 : idx jo (armQ kki' fli) ≠ 2 := by rw [← hti]; exact fun e => di2 e.symm
    have hcases : ∀ u w : Fin 3, u ≠ w → u ≠ 2 → w ≠ 2 → (u = 1 ∧ w = 0) ∨ (u = 0 ∧ w = 1) := by decide
    have hang1 : P.angle (k + 1) = Real.pi / 3 := by
      rw [hang3, hc1c.1, hc1c.2]; push_cast; ring
    left
    refine ⟨hang1, ?_⟩
    rcases hcases _ _ hidxne hu2 hw2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · left; exact ⟨(tyo 2).mpr hto, (tyoU 1).mpr e1, (tyi 2).mpr hti, (tyiU 0).mpr e2⟩
    · right; exact ⟨(tyo 2).mpr hto, (tyoU 0).mpr e1, (tyi 2).mpr hti, (tyiU 1).mpr e2⟩
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
    have hcnts : (cnt D idx V 1 = 1 ∧ cnt D idx V 2 = 0) ∨ (cnt D idx V 1 = 0 ∧ cnt D idx V 2 = 2) := by omega
    have hang2 : P.angle (k + 1) = 2 * Real.pi / 3 := by
      rw [hang3]
      rcases hcnts with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> (rw [e1, e2]; push_cast; ring)
    right
    refine ⟨hang2, ?_⟩
    rcases hcnts with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · -- one `α` corner and one `β` corner
      have hc0 : cnt D idx V 0 = 1 := by have := h.hregc V; omega
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
        right; left
        have hq2 : ¬ nsq (F.p xi) = slen D 0 ^ 2 := fun hh => di2 (by rw [eb]; exact (spi.mp hh).symm)
        have hq1 : ¬ nsq (F.q xo) = slen D 0 ^ 2 := fun hh => hq2 (hjunc.mp hh)
        have hu0 : ¬ idx jo (armP kko' flo) = 0 := fun hh => hq1 (sqo.mpr hh)
        have hu1 : idx jo (armP kko' flo) ≠ idx jo kko' := fun e => do1 e.symm
        have hfin : ∀ w t : Fin 3, w ≠ 0 → w ≠ t → t = 1 → w = 2 := by decide
        exact ⟨(tyo 1).mpr ea, (tyoU 2).mpr (hfin _ _ hu0 hu1 ea), (tyi 0).mpr eb⟩
    · -- two `γ` corners
      have hc0 : cnt D idx V 0 = 0 := by have := h.hregc V; omega
      have hto : idx jo kko' = 2 := idx_two_of_cnt D idx hc0 e1 hko'
      have hti : idx ji kki' = 2 := idx_two_of_cnt D idx hc0 e1 hki'
      have hex : ¬ (idx jo (armQ kko' flo) = 1 ∧ idx ji (armP kki' fli) = 1) := by
        rintro ⟨t1x, t1y⟩
        obtain ⟨Z, hZ⟩ := gk_of_ray D idx h.hidx hab hac F xo xi hxy hne12 hko' hki' hpo hqo hpi hqi hto t1x hti t1y
        exact hnoGk Z hZ
      have hj2 : (idx jo (armP kko' flo) = 0 ↔ idx ji (armQ kki' fli) = 0) := by
        rw [← sqo, ← spi]; exact hjunc
      have hu2 : idx jo (armP kko' flo) ≠ 2 := by rw [← hto]; exact fun e => do1 e.symm
      have hw2 : idx jo (armQ kko' flo) ≠ 2 := by rw [← hto]; exact fun e => do2 e.symm
      have hu2' : idx ji (armP kki' fli) ≠ 2 := by rw [← hti]; exact fun e => di1 e.symm
      have hw2' : idx ji (armQ kki' fli) ≠ 2 := by rw [← hti]; exact fun e => di2 e.symm
      have hfin : ∀ uo wo ui wi : Fin 3, uo ≠ wo → ui ≠ wi → uo ≠ 2 → wo ≠ 2 → ui ≠ 2 → wi ≠ 2 → (uo = 0 ↔ wi = 0) →
          ¬ (wo = 1 ∧ ui = 1) → uo = 1 ∧ wi = 1 := by decide
      obtain ⟨f1, f2⟩ := hfin _ _ _ _ do3 di3 hu2 hw2 hu2' hw2' hj2 hex
      right; right
      exact ⟨(tyo 2).mpr hto, (tyoU 1).mpr f1, (tyi 2).mpr hti, (tyiU 1).mpr f2⟩

end Erdos634.Draft.LaczFormal.RG
