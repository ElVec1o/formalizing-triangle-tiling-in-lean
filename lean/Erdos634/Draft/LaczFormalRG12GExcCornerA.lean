-- Draft/LaczFormalRG12GExcCornerA.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2, Gamma_except, lemma L4 (part 1) `gexc_start_corner_A` (FABLE_THM21_FINISH blueprint, A.2 sources, Fig. 6 (A)): at a vertex `V = v_{k+1}` of the polygon
-- of type `alpha + beta` (counts `(1,1,0)`) whose two tiles have their `c`-side on the boundary (Fig. 6 (A)), an edge of Gamma_except STARTS at `V`.
-- Route: the corner fan has exactly two tiles `x` (starting along the outgoing side) and `y` (ending along the incoming side), both with a corner label `alpha` or `beta` (`n = 2` by pigeonhole on the labels, `cnt = (1,1,0)`);
-- the boundary arm of each is a side of length `c`, so (no `gamma` corner on a side of length `c`) its far end is not `gamma`, hence the OTHER arm (the common inner ray `d`) has far end `gamma` (`fin3_sum3`).
-- The inner ray starts a maximal segment (`noBack_corner`, `exists_maxseg`); both first tiles have `gamma` at their far end (`left_step_unique`/`right_step_unique`), so both divisions have a `gamma`-run (`grunEnd_exists`).
-- Hypotheses: `CaseC`, `HasFansC`, `D.region = P.carrier`, the counts `(1,1,0)` at `V`, and the `c`-length of the outgoing and incoming boundary steps (`hout`, `hin`; derived in `LaczFormalRG12GExcCorner` from Lemma 4.7).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2, Fig. 6), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12GExcHelp
import Erdos634.Draft.LaczFormalRG12CornerSeg
import Erdos634.Draft.LaczFormalRG12L61Prop

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

set_option maxHeartbeats 12800000 in
/-- **L4, part 1: Fig. 6 (A) starts an edge of Gamma_except.** -/
theorem gexc_start_corner_A [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (k : Fin M)
    (hc0 : cnt D idx (P.v (k + 1)) 0 = 1) (hc1 : cnt D idx (P.v (k + 1)) 1 = 1) (hc2 : cnt D idx (P.v (k + 1)) 2 = 0)
    (hout : ∀ (jo : Fin N) (Uo : Plane), TriStep (D.tile jo) (toV2 (P.e (k + 1))) (P.v (k + 1)) Uo → dist (P.v (k + 1)) Uo = slen D 2)
    (hin : ∀ (ji : Fin N) (Ui : Plane), TriStep (D.tile ji) (toV2 (P.e k)) Ui (P.v (k + 1)) → dist Ui (P.v (k + 1)) = slen D 2) :
    ∃ W, GExc D idx (P.v (k + 1)) W := by
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
  have hdo := hout _ _ hSo
  have hdi := hin _ _ hSi
  have hsum : ∀ (i : Fin N) (kk : Fin 3) (fl : Bool), (idx i kk).val + (idx i (armP kk fl)).val + (idx i (armQ kk fl)).val = 3 := fun i kk fl =>
    fin3_sum3 (fun h => armP_ne kk fl ((idx i).injective h).symm) (fun h => armQ_ne kk fl ((idx i).injective h).symm)
      (fun h => armPQ_ne kk fl ((idx i).injective h))
  -- far labels
  have hxq : idx x.1 (armQ kx flx) = 2 := by
    have hn1 : idx x.1 (armP kx flx) ≠ 2 := by
      intro e
      apply step_dist_ne_c D idx hC (p := kx) (q := armP kx flx) (Ne.symm (armP_ne kx flx)) (Or.inr e)
      rw [hkx]; exact hdo
    have hn0 := hlab_ne2 x kx hkx
    have := hsum x.1 kx flx
    apply Fin.ext
    have a1 : (idx x.1 kx).val ≠ 2 := fun e => hn0 (Fin.ext e)
    have a2 : (idx x.1 (armP kx flx)).val ≠ 2 := fun e => hn1 (Fin.ext e)
    have a3 := (idx x.1 kx).isLt
    have a4 := (idx x.1 (armP kx flx)).isLt
    have a5 : (idx x.1 kx).val ≠ (idx x.1 (armP kx flx)).val := fun e => armP_ne kx flx ((idx x.1).injective (Fin.ext e)).symm
    simp
    omega
  have hyp : idx y.1 (armP ky fly) = 2 := by
    have hn1 : idx y.1 (armQ ky fly) ≠ 2 := by
      intro e
      apply step_dist_ne_c D idx hC (p := armQ ky fly) (q := ky) (armQ_ne ky fly) (Or.inl e)
      rw [hky]; exact hdi
    have hn0 := hlab_ne2 y ky hky
    have := hsum y.1 ky fly
    apply Fin.ext
    have a1 : (idx y.1 ky).val ≠ 2 := fun e => hn0 (Fin.ext e)
    have a2 : (idx y.1 (armQ ky fly)).val ≠ 2 := fun e => hn1 (Fin.ext e)
    have a3 := (idx y.1 ky).isLt
    have a4 := (idx y.1 (armQ ky fly)).isLt
    have a5 : (idx y.1 ky).val ≠ (idx y.1 (armQ ky fly)).val := fun e => armQ_ne ky fly ((idx y.1).injective (Fin.ext e)).symm
    simp
    omega
  -- the maximal segment along the inner ray
  have hl0 : TriStep (D.tile y.1) (F.q x) V ((D.tile y.1).pts (armP ky fly)) := triStep_of_start ky fly hky hpy hqy hcy hxy
  have hr0 : TriStep (D.tile x.1) (neg2 (F.q x)) ((D.tile x.1).pts (armQ kx flx)) V := triStep_of_end kx flx hkx hpx hqx hcx (par_refl hd)
  have hX : ∃ j kb, (D.tile j).pts kb = V := ⟨y.1, ky, hky⟩
  obtain ⟨Z', L1, L2, W1, W2, hL1, hL2, hno1, hno2⟩ := exists_maxseg D.toRegionDissection hd hX ⟨_, _, hl0⟩ ⟨_, _, hr0⟩
  obtain ⟨e1, L1', hL1e, hS1, he1X⟩ : ∃ e1 L1', L1 = e1 :: L1' ∧ TriStep (D.tile e1.1) (F.q x) e1.2.1 e1.2.2 ∧ e1.2.1 = V := by
    cases W1 with
    | nil => exact absurd rfl hL1
    | cons hS W' => exact ⟨_, _, rfl, hS, rfl⟩
  obtain ⟨e2, L2', hL2e, hS2, he2X⟩ : ∃ e2 L2', L2 = e2 :: L2' ∧ TriStep (D.tile e2.1) (neg2 (F.q x)) e2.2.2 e2.2.1 ∧ e2.2.1 = V := by
    cases W2 with
    | nil => exact absurd rfl hL2
    | cons hS W' => exact ⟨_, _, rfl, hS, rfl⟩
  rw [he1X] at hS1
  rw [he2X] at hS2
  obtain ⟨hi1, hU1⟩ := left_step_unique D.toRegionDissection hS1 hl0
  obtain ⟨hi2, hU2⟩ := right_step_unique D.toRegionDissection hS2 hr0
  have hg1 : GammaHead D idx e1 := ⟨armP ky fly, by rw [hU1, hi1], by rw [hi1]; exact hyp⟩
  have hg2 : GammaHead D idx e2 := ⟨armQ kx flx, by rw [hU2, hi2], by rw [hi2]; exact hxq⟩
  obtain ⟨H1, hr1⟩ := grunEnd_exists D idx hL1 (by rw [hL1e]; intro z hz; simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hz; rw [← hz]; exact hg1)
  obtain ⟨H2, hr2⟩ := grunEnd_exists D idx hL2 (by rw [hL2e]; intro z hz; simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hz; rw [← hz]; exact hg2)
  rcases le_total (dist V H1) (dist V H2) with hle | hle
  · exact ⟨H1, F.q x, Z', L1, L2, H1, H2, hd, hnb, W1, W2, hL1, hL2, hno1, hno2, hr1, hr2, Or.inl ⟨rfl, hle⟩⟩
  · exact ⟨H2, F.q x, Z', L1, L2, H1, H2, hd, hnb, W1, W2, hL1, hL2, hno1, hno2, hr1, hr2, Or.inr ⟨rfl, hle⟩⟩

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.gexc_start_corner_A
