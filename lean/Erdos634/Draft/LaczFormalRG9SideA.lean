-- Draft/LaczFormalRG9SideA.lean -- Laczkovich DCG 48 (2012), Lemma 4.3 (local content) for a polygon side, GENERAL gamma, `Gamma_a` version: under the hypotheses that every tiling vertex in the relative interior of the side is
-- NORMAL (one corner of each type) and no edge of `Gamma_a` starts there.  Copies of `RG4Side.edge_vertex_data`/`edge_consec` (Case IV, gamma = pi/3) without the `Gamma_k` part and with the normality and no-edge
-- hypotheses supplied.  UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Lemma 4.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG9Side
import Erdos634.Draft.LaczFormalRG4Walk

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- Hypotheses of Case I for `Γ_a`: vertex correspondence, regular counts, `a` not a nonnegative rational combination of `b, c`. -/
structure CaseA (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) : Prop where
  hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k'))
  hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v
  hnc : NotComb (slen D 0) (slen D 1) (slen D 2)
  hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1

theorem CaseA.hab {D : CongruentRegionDissection N} {idx : Fin N → Equiv.Perm (Fin 3)} (h : CaseA D idx) : slen D 0 ≠ slen D 1 := by
  intro e
  have := h.hnc 1 1 0 one_pos
  apply this; rw [e]; simp

theorem CaseA.hac {D : CongruentRegionDissection N} {idx : Fin N → Equiv.Perm (Fin 3)} (h : CaseA D idx) : slen D 0 ≠ slen D 2 := by
  intro e
  have := h.hnc 1 0 1 one_pos
  apply this; rw [e]; simp

/-- **The local data at a side vertex, `Γ_c` version.**  `V` in the relative interior of the edge `i` (`γ = π/3`, no edge of `Γ_c` starts at `V` because `V` is a boundary point):
a three-tile fan; either the three types at `V` are distinct, or all three corners at `V` are `γ` (the exceptional vertex `3γ = π`); the first sides on the two inner rays have the
same `c`-status. -/
theorem edge_vertex_data_a (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseA D idx) (i : Fin M) (hnormv : ∀ V : Plane, (∃ j k, (D.tile j).pts k = V) → (∃ t : ℝ, 0 < t ∧ t < 1 ∧ V = (1 - t) • P.v i + t • P.v (i + 1)) → cnt D idx V 0 = 1 ∧ cnt D idx V 1 = 1 ∧ cnt D idx V 2 = 1) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {V : Plane}
    (hV : V = (1 - t) • P.v i + t • P.v (i + 1)) (hvert : ∃ j k, (D.tile j).pts k = V)
    (hno : ∀ H', ¬ GaEdge D.toRegionDissection (slen D 0) V H') :
    ∃ (pT : V2) (F : ExtFan D.toRegionDissection V Unit) (s1 s2 s3 : AtV D.toRegionDissection V),
      Par pT (toV2 (P.e i)) ∧ SideFan3 D.toRegionDissection V pT F.p F.q s1 s2 s3 ∧
      (∃ k, (D.tile s2.1).pts k = V) ∧
      (∀ k1 k2 k3, (D.tile s1.1).pts k1 = V → (D.tile s2.1).pts k2 = V → (D.tile s3.1).pts k3 = V →
        idx s1.1 k1 ≠ idx s2.1 k2 ∧ idx s1.1 k1 ≠ idx s3.1 k3 ∧ idx s2.1 k2 ≠ idx s3.1 k3) ∧
      (nsq (F.q s1) = slen D 0 ^ 2 ↔ nsq (F.p s2) = slen D 0 ^ 2) ∧ (nsq (F.q s2) = slen D 0 ^ 2 ↔ nsq (F.p s3) = slen D 0 ^ 2) := by
  classical
  have hbd : V ∉ interior D.region := by
    rw [hreg]; exact not_interior_of_c_zero P (i := i) (by rw [hV]; exact c_on_edge P i t)
  obtain ⟨pT, F, hpd, hpe, hqe, hcr, hcls, hcard⟩ := edge_fan_counts_n D P hreg idx h.hidxA h.hregc i hnormv ht0 ht1 hV hvert
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
    exact hno H' hH'
  have iff2 : (nsq (F.q s2) = slen D 0 ^ 2 ↔ nsq (F.p s3) = slen D 0 ^ 2) := by
    by_contra hn
    have hx : (nsq (F.q s2) = slen D 0 ^ 2 ∧ nsq (F.p s3) ≠ slen D 0 ^ 2) ∨ (nsq (F.q s2) ≠ slen D 0 ^ 2 ∧ nsq (F.p s3) = slen D 0 ^ 2) := by tauto
    obtain ⟨H', hH'⟩ := ga_edge_of_ray D idx h.hidx h.hnc F s2 s3 (hcr s2) (hcr s3) hF.r3 nb2 hx
    exact hno H' hH'
  refine ⟨hcorner s2, ?_, iff1, iff2⟩
  have hn0 := (hnormv V hvert (by subst hV; exact ⟨t, ht0, ht1, rfl⟩)).1
  rcases hcls with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩
  · exfalso; omega
  · have hk : ∀ (t : Fin N) (k : Fin 3), (D.tile t).pts k = V → ∀ l : Fin 3, idx t k = l → cnt D idx V l = 1 := by
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

/-- **The local step along a polygon edge** (Laczkovich Lemma 4.3, local content, with Lemma 8.1 (ii),(iii)): two consecutive tiles `j1` (ending at `V`) and `j2` (starting at `V`) of the walk along the
edge `i`, `V` in the relative interior of the edge. (βγ) a `{β,γ}` pair of the tile `j1` is copied by `j2`; (α) `α` at the tail of `j1` gives `α` at the tail of `j2`; (α') `α` at the head of `j2`
gives `α` at the head of `j1`. -/
theorem edge_consec_a (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseA D idx) (i : Fin M) (hnormv : ∀ V : Plane, (∃ j k, (D.tile j).pts k = V) → (∃ t : ℝ, 0 < t ∧ t < 1 ∧ V = (1 - t) • P.v i + t • P.v (i + 1)) → cnt D idx V 0 = 1 ∧ cnt D idx V 1 = 1 ∧ cnt D idx V 2 = 1)
    (hno : ∀ V : Plane, (∃ j k, (D.tile j).pts k = V) → (∃ t : ℝ, 0 < t ∧ t < 1 ∧ V = (1 - t) • P.v i + t • P.v (i + 1)) → ∀ H', ¬ GaEdge D.toRegionDissection (slen D 0) V H') {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {V : Plane}
    (hV : V = (1 - t) • P.v i + t • P.v (i + 1)) {U U'' : Plane} {j1 j2 : Fin N}
    (h1 : TriStep (D.tile j1) (toV2 (P.e i)) U V) (h2 : TriStep (D.tile j2) (toV2 (P.e i)) V U'')
    (kR fR kL fL : Fin 3) (hR1 : (D.tile j2).pts kR = V) (hR2 : (D.tile j2).pts fR = U'')
    (hL1 : (D.tile j1).pts kL = V) (hL2 : (D.tile j1).pts fL = U) :
    (((idx j1 fL = 1 ∧ idx j1 kL = 2) ∨ (idx j1 fL = 2 ∧ idx j1 kL = 1)) → idx j2 kR = idx j1 fL ∧ idx j2 fR = idx j1 kL) ∧
    (idx j1 fL = 0 → idx j2 kR = 0) ∧ (idx j2 fR = 0 → idx j1 kL = 0) ∧
    (((idx j2 kR = 1 ∧ idx j2 fR = 2) ∨ (idx j2 kR = 2 ∧ idx j2 fR = 1)) → idx j2 kR = idx j1 fL ∧ idx j2 fR = idx j1 kL) := by
  classical
  have hvert : ∃ j k, (D.tile j).pts k = V := ⟨j2, kR, hR1⟩
  obtain ⟨pT, F, s1, s2, s3, hpd, hF, hc2, hnorm, hno1, hno2⟩ := edge_vertex_data_a D P hreg idx h i hnormv ht0 ht1 hV hvert (hno V hvert ⟨t, ht0, ht1, hV⟩)
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
