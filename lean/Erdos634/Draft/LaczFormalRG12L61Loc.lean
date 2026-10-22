-- Draft/LaczFormalRG12L61Loc.lean -- Laczkovich DCG 48 (2012), Lemma 6.1 (Subcase IIc), local part: along a polygon side with normal interior vertices, in Case C (`Gamma_c` empty), the four propagation rules for the type `gamma`:
-- forward tail (`edge_step_n`, already in RG9Side), backward head, FORWARD HEAD (`edge_step_head_f`) and BACKWARD TAIL (`edge_step_tail_b`), the last two from the pair rule at a normal vertex.  Whole-side versions
-- `walk_head_fwd`, `walk_head_bwd`, `walk_tail_bwd`.  Copies of `edge_vertex_data_n` (normal branch only), `edge_step_n`, `walk_gamma_n` of RG9Side.  NOTE, UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Lemmas 4.4, 6.1), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG9SideC2

namespace Erdos634.Draft.LaczFormal.RG

/-- the type swap `α ↔ γ`. -/
def sw : Fin 3 → Fin 3 | 0 => 2 | 1 => 1 | 2 => 0

theorem swap_symm_eq_sw (x : Fin 3) : (Equiv.swap (0 : Fin 3) 2).symm x = sw x := by
  revert x; decide

/-- Pure finite check: the six local rules on the four types `a = idx j1 fL` (tail of `j1`), `b = idx j1 kL` (head of `j1`, at `V`), `c = idx j2 kR` (tail of `j2`, at `V`), `d = idx j2 fR` (head of `j2`). -/
theorem loc_decide : ∀ a b c d : Fin 3, c ≠ b → a ≠ b → c ≠ d →
    (((sw a = 1 ∧ sw b = 2) ∨ (sw a = 2 ∧ sw b = 1)) →
      sw c = sw a ∧ sw d = sw b) →
    (sw a = 0 → sw c = 0) →
    (sw d = 0 → sw b = 0) →
    (((sw c = 1 ∧ sw d = 2) ∨ (sw c = 2 ∧ sw d = 1)) →
      sw c = sw a ∧ sw d = sw b) →
    ((a = 2 → c = 2) ∧ (d = 2 → b = 2) ∧ (((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)) → c = a ∧ d = b) ∧
      (((c = 0 ∧ d = 1) ∨ (c = 1 ∧ d = 0)) → c = a ∧ d = b) ∧ (b = 2 → d = 2) ∧ (c = 2 → a = 2)) := by
  intro a b c d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp [sw]

end Erdos634.Draft.LaczFormal.RG

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]


/-- **The local data at a side vertex, `Γ_c` version.**  `V` in the relative interior of the edge `i` (`γ = π/3`, no edge of `Γ_c` starts at `V` because `V` is a boundary point):
a three-tile fan; either the three types at `V` are distinct, or all three corners at `V` are `γ` (the exceptional vertex `3γ = π`); the first sides on the two inner rays have the
same `c`-status. -/
theorem edge_vertex_data_n2 (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx) (i : Fin M) (hnorm : ∀ V : Plane, (∃ j k, (D.tile j).pts k = V) → (∃ t : ℝ, 0 < t ∧ t < 1 ∧ V = (1 - t) • P.v i + t • P.v (i + 1)) → cnt D idx V 0 = 1 ∧ cnt D idx V 1 = 1 ∧ cnt D idx V 2 = 1) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {V : Plane}
    (hV : V = (1 - t) • P.v i + t • P.v (i + 1)) (hvert : ∃ j k, (D.tile j).pts k = V) :
    ∃ (pT : V2) (F : ExtFan D.toRegionDissection V Unit) (s1 s2 s3 : AtV D.toRegionDissection V),
      Par pT (toV2 (P.e i)) ∧ SideFan3 D.toRegionDissection V pT F.p F.q s1 s2 s3 ∧
      (∃ k, (D.tile s2.1).pts k = V) ∧
      (∀ k1 k2 k3, (D.tile s1.1).pts k1 = V → (D.tile s2.1).pts k2 = V → (D.tile s3.1).pts k3 = V →
        idx s1.1 k1 ≠ idx s2.1 k2 ∧ idx s1.1 k1 ≠ idx s3.1 k3 ∧ idx s2.1 k2 ≠ idx s3.1 k3) ∧
      (nsq (F.q s1) = slen D 2 ^ 2 ↔ nsq (F.p s2) = slen D 2 ^ 2) ∧ (nsq (F.q s2) = slen D 2 ^ 2 ↔ nsq (F.p s3) = slen D 2 ^ 2) := by
  classical
  have hG := h.caseG
  have hs0 : slen (relabelC D) 0 = slen D 2 := relabelC_slen0 D
  haveI : HasFansC (relabelC D).toRegionDissection := (inferInstance : HasFansC D.toRegionDissection)
  have hbd : V ∉ interior D.region := by
    rw [hreg]; exact not_interior_of_c_zero P (i := i) (by rw [hV]; exact c_on_edge P i t)
  obtain ⟨pT, F, hpd, hpe, hqe, hcr, hcls, hcard⟩ := edge_fan_counts_n D P hreg idx h.hidxA h.hregc i hnorm ht0 ht1 hV hvert
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
  have iff1 : (nsq (F.q s1) = slen D 2 ^ 2 ↔ nsq (F.p s2) = slen D 2 ^ 2) := by
    by_contra hn
    have hx : (nsq (F.q s1) = slen (relabelC D) 0 ^ 2 ∧ nsq (F.p s2) ≠ slen (relabelC D) 0 ^ 2) ∨
        (nsq (F.q s1) ≠ slen (relabelC D) 0 ^ 2 ∧ nsq (F.p s2) = slen (relabelC D) 0 ^ 2) := by rw [hs0]; tauto
    obtain ⟨H', hH'⟩ := ga_edge_of_ray (relabelC D) (relabelCIdx idx) hG.hidx hG.hnc F s1 s2 (hcr s1) (hcr s2) hF.r2 nb1 hx
    exact gc_no_boundary D idx h hbd ((gcEdge_iff D V H').mpr hH')
  have iff2 : (nsq (F.q s2) = slen D 2 ^ 2 ↔ nsq (F.p s3) = slen D 2 ^ 2) := by
    by_contra hn
    have hx : (nsq (F.q s2) = slen (relabelC D) 0 ^ 2 ∧ nsq (F.p s3) ≠ slen (relabelC D) 0 ^ 2) ∨
        (nsq (F.q s2) ≠ slen (relabelC D) 0 ^ 2 ∧ nsq (F.p s3) = slen (relabelC D) 0 ^ 2) := by rw [hs0]; tauto
    obtain ⟨H', hH'⟩ := ga_edge_of_ray (relabelC D) (relabelCIdx idx) hG.hidx hG.hnc F s2 s3 (hcr s2) (hcr s3) hF.r3 nb2 hx
    exact gc_no_boundary D idx h hbd ((gcEdge_iff D V H').mpr hH')
  refine ⟨hcorner s2, ?_, iff1, iff2⟩
  have hn1 := (hnorm V hvert ⟨t, ht0, ht1, hV⟩).1
  rcases hcls with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩
  · exfalso; omega
  · 
    have hk : ∀ (t : Fin N) (k : Fin 3), (D.tile t).pts k = V → ∀ l : Fin 3, idx t k = l → cnt D idx V l = 1 := by
      intro t k hk l hl
      have := cnt_one D idx l hk hl
      fin_cases l <;> simp_all
    refine fun k1 k2 k3 hk1 hk2 hk3 => ⟨?_, ?_, ?_⟩
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


set_option maxHeartbeats 3200000 in
/-- **The local rules at a normal side vertex** (Case C, original types `α = 0, β = 1, γ = 2`): two consecutive tiles `j1` (ending at `V`) and `j2` (starting at `V`) of the walk along the edge `i`, `V` in the relative
interior and normal.  With `a, b` the types of `j1` at its tail, head and `c, d` those of `j2`: tail `γ` forward, head `γ` backward, the `{α,β}` pair forward and backward, and (from normality) head `γ` forward and tail `γ`
backward. -/
theorem edge_local_rules (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx) (i : Fin M) (hnorm : ∀ V : Plane, (∃ j k, (D.tile j).pts k = V) → (∃ t : ℝ, 0 < t ∧ t < 1 ∧ V = (1 - t) • P.v i + t • P.v (i + 1)) → cnt D idx V 0 = 1 ∧ cnt D idx V 1 = 1 ∧ cnt D idx V 2 = 1) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {V : Plane} (hV : V = (1 - t) • P.v i + t • P.v (i + 1)) {U U'' : Plane} {j1 j2 : Fin N}
    (h1 : TriStep (D.tile j1) (toV2 (P.e i)) U V) (h2 : TriStep (D.tile j2) (toV2 (P.e i)) V U'')
    (kR fR kL fL : Fin 3) (hR1 : (D.tile j2).pts kR = V) (hR2 : (D.tile j2).pts fR = U'')
    (hL1 : (D.tile j1).pts kL = V) (hL2 : (D.tile j1).pts fL = U) :
    ((idx j1 fL = 2 → idx j2 kR = 2) ∧ (idx j2 fR = 2 → idx j1 kL = 2) ∧
      (((idx j1 fL = 0 ∧ idx j1 kL = 1) ∨ (idx j1 fL = 1 ∧ idx j1 kL = 0)) → idx j2 kR = idx j1 fL ∧ idx j2 fR = idx j1 kL) ∧
      (((idx j2 kR = 0 ∧ idx j2 fR = 1) ∨ (idx j2 kR = 1 ∧ idx j2 fR = 0)) → idx j2 kR = idx j1 fL ∧ idx j2 fR = idx j1 kL) ∧
      (idx j1 kL = 2 → idx j2 fR = 2) ∧ (idx j2 kR = 2 → idx j1 fL = 2)) := by
  classical
  have hG := h.caseG
  haveI : HasFansC (relabelC D).toRegionDissection := (inferInstance : HasFansC D.toRegionDissection)
  have hvert : ∃ j k, (D.tile j).pts k = V := ⟨j2, kR, hR1⟩
  obtain ⟨pT, F, s1, s2, s3, hpd, hF, hc2, hcls, hno1, hno2⟩ := edge_vertex_data_n2 D P hreg idx h i hnorm ht0 ht1 hV hvert
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
  have hnorm' : ∀ k1 k2 k3, (D.tile s1.1).pts k1 = V → (D.tile s2.1).pts k2 = V → (D.tile s3.1).pts k3 = V →
      relabelCIdx idx s1.1 k1 ≠ relabelCIdx idx s2.1 k2 ∧ relabelCIdx idx s1.1 k1 ≠ relabelCIdx idx s3.1 k3 ∧
      relabelCIdx idx s2.1 k2 ≠ relabelCIdx idx s3.1 k3 := by
    intro k1 k2 k3 a1 a2 a3
    obtain ⟨n1, n2, n3⟩ := hcls k1 k2 k3 a1 a2 a3
    have inj : ∀ (a b : Fin N) (k k' : Fin 3), relabelCIdx idx a k = relabelCIdx idx b k' → idx a k = idx b k' := by
      intro a b k k' e
      unfold relabelCIdx at e
      rw [relabelIdx_apply, relabelIdx_apply] at e
      exact Equiv.injective _ e
    exact ⟨fun e => n1 (inj _ _ _ _ e), fun e => n2 (inj _ _ _ _ e), fun e => n3 (inj _ _ _ _ e)⟩
  have hs0 : slen (relabelC D) 0 = slen D 2 := relabelC_slen0 D
  have hss := side_step_all (relabelC D) (relabelCIdx idx) hG.hidx V hF hc2 hG.hab hG.hac hnorm' (by rw [hs0]; exact hno1) (by rw [hs0]; exact hno2)
    kR fR kL fL (by rw [hj2]; exact hR1) hR2' (by rw [hj1]; exact hL1) hL2'
  rw [hj2, hj1] at hss
  obtain ⟨k2, hk2⟩ := hc2
  have hcn := (hcls kR k2 kL (by rw [hj2]; exact hR1) hk2 (by rw [hj1]; exact hL1)).2.1
  rw [hj2, hj1] at hcn
  have hab : idx j1 fL ≠ idx j1 kL := by
    intro e
    have hkf : fL = kL := (idx j1).injective e
    apply hL2'.ne_left
    rw [hj1, hkf, hL1]
    unfold toV2; ext <;> simp
  have hcd : idx j2 kR ≠ idx j2 fR := by
    intro e
    have hkf : kR = fR := (idx j2).injective e
    apply hR2'.ne_left
    rw [hj2, ← hkf, hR1]
    unfold toV2; ext <;> simp
  have hr : ∀ a k, relabelCIdx idx a k = sw (idx a k) := fun a k => by unfold relabelCIdx; rw [relabelIdx_apply, swap_symm_eq_sw]
  simp only [hr] at hss
  obtain ⟨s_1, s_2, s_3, s_4⟩ := hss
  exact loc_decide _ _ _ _ hcn hab hcd s_1 s_2 s_3 s_4

/-- Head `γ` forward along a normal side vertex. -/
theorem edge_step_head_f (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx) (i : Fin M) (hnorm : ∀ V : Plane, (∃ j k, (D.tile j).pts k = V) → (∃ t : ℝ, 0 < t ∧ t < 1 ∧ V = (1 - t) • P.v i + t • P.v (i + 1)) → cnt D idx V 0 = 1 ∧ cnt D idx V 1 = 1 ∧ cnt D idx V 2 = 1) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {V : Plane} (hV : V = (1 - t) • P.v i + t • P.v (i + 1)) {U U'' : Plane} {j1 j2 : Fin N}
    (h1 : TriStep (D.tile j1) (toV2 (P.e i)) U V) (h2 : TriStep (D.tile j2) (toV2 (P.e i)) V U'')
    (kR fR kL fL : Fin 3) (hR1 : (D.tile j2).pts kR = V) (hR2 : (D.tile j2).pts fR = U'')
    (hL1 : (D.tile j1).pts kL = V) (hL2 : (D.tile j1).pts fL = U) : idx j1 kL = 2 → idx j2 fR = 2 :=
  (edge_local_rules D P hreg idx h i hnorm ht0 ht1 hV h1 h2 kR fR kL fL hR1 hR2 hL1 hL2).2.2.2.2.1

/-- Tail `γ` backward along a normal side vertex. -/
theorem edge_step_tail_b (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx) (i : Fin M) (hnorm : ∀ V : Plane, (∃ j k, (D.tile j).pts k = V) → (∃ t : ℝ, 0 < t ∧ t < 1 ∧ V = (1 - t) • P.v i + t • P.v (i + 1)) → cnt D idx V 0 = 1 ∧ cnt D idx V 1 = 1 ∧ cnt D idx V 2 = 1) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {V : Plane} (hV : V = (1 - t) • P.v i + t • P.v (i + 1)) {U U'' : Plane} {j1 j2 : Fin N}
    (h1 : TriStep (D.tile j1) (toV2 (P.e i)) U V) (h2 : TriStep (D.tile j2) (toV2 (P.e i)) V U'')
    (kR fR kL fL : Fin 3) (hR1 : (D.tile j2).pts kR = V) (hR2 : (D.tile j2).pts fR = U'')
    (hL1 : (D.tile j1).pts kL = V) (hL2 : (D.tile j1).pts fL = U) : idx j2 kR = 2 → idx j1 fL = 2 :=
  (edge_local_rules D P hreg idx h i hnorm ht0 ht1 hV h1 h2 kR fR kL fL hR1 hR2 hL1 hL2).2.2.2.2.2

/-- Head `γ` backward along a normal side vertex. -/
theorem edge_step_head_b (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx) (i : Fin M) (hnorm : ∀ V : Plane, (∃ j k, (D.tile j).pts k = V) → (∃ t : ℝ, 0 < t ∧ t < 1 ∧ V = (1 - t) • P.v i + t • P.v (i + 1)) → cnt D idx V 0 = 1 ∧ cnt D idx V 1 = 1 ∧ cnt D idx V 2 = 1) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {V : Plane} (hV : V = (1 - t) • P.v i + t • P.v (i + 1)) {U U'' : Plane} {j1 j2 : Fin N}
    (h1 : TriStep (D.tile j1) (toV2 (P.e i)) U V) (h2 : TriStep (D.tile j2) (toV2 (P.e i)) V U'')
    (kR fR kL fL : Fin 3) (hR1 : (D.tile j2).pts kR = V) (hR2 : (D.tile j2).pts fR = U'')
    (hL1 : (D.tile j1).pts kL = V) (hL2 : (D.tile j1).pts fL = U) : idx j2 fR = 2 → idx j1 kL = 2 :=
  (edge_local_rules D P hreg idx h i hnorm ht0 ht1 hV h1 h2 kR fR kL fL hR1 hR2 hL1 hL2).2.1

/-- Tail `γ` forward along a normal side vertex (restated from the local rules). -/
theorem edge_step_tail_f (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx) (i : Fin M) (hnorm : ∀ V : Plane, (∃ j k, (D.tile j).pts k = V) → (∃ t : ℝ, 0 < t ∧ t < 1 ∧ V = (1 - t) • P.v i + t • P.v (i + 1)) → cnt D idx V 0 = 1 ∧ cnt D idx V 1 = 1 ∧ cnt D idx V 2 = 1) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {V : Plane} (hV : V = (1 - t) • P.v i + t • P.v (i + 1)) {U U'' : Plane} {j1 j2 : Fin N}
    (h1 : TriStep (D.tile j1) (toV2 (P.e i)) U V) (h2 : TriStep (D.tile j2) (toV2 (P.e i)) V U'')
    (kR fR kL fL : Fin 3) (hR1 : (D.tile j2).pts kR = V) (hR2 : (D.tile j2).pts fR = U'')
    (hL1 : (D.tile j1).pts kL = V) (hL2 : (D.tile j1).pts fL = U) : idx j1 fL = 2 → idx j2 kR = 2 :=
  (edge_local_rules D P hreg idx h i hnorm ht0 ht1 hV h1 h2 kR fR kL fL hR1 hR2 hL1 hL2).1

end Erdos634.Draft.LaczFormal.RG
