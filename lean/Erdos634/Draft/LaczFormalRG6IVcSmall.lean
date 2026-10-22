-- Draft/LaczFormalRG6IVcSmall.lean -- Theorem 2.1, Case IV (gamma = pi/3), Subcase IVc (a, b commensurable, c not a rational multiple of a), POLYGONS WITH AT MOST FOUR SIDES.
-- Laczkovich Sect. 8.3, first part: if two consecutive corners of `A` equal `pi/3` (so `A` is a triangle or a trapezoid), contradiction.  The proof of the paper uses Lemma 4.4 (i) and
-- "Gamma_c is empty" (Lemma 4.6); here only the weaker fact "no edge of Gamma_c starts on the boundary" (`gc_no_boundary`, a consequence of balance) is used, together with the local
-- step along a side in the relabeled model (`side_step_all` for `alpha <-> gamma`), the 3 gamma vertex (all three corners gamma) treated directly.
-- A quadrilateral with no two adjacent corners `pi/3` is a parallelogram and then conclusion (i) holds (rational polygon, `sin alpha / sin beta = a/b`).
-- NOT done here: Lemma 4.6, Lemma 4.8, the Phi/chi argument for N >= 5 (hexagons), the case alpha rational.  UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Sect. 4 and 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG5GammaC
import Erdos634.Draft.LaczFormalRG4Walk
import Erdos634.Draft.LaczFormalRG4Side
import Erdos634.Draft.LaczFormalRG4CaseIV

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- The half-plane arithmetic for `γ = π/3` (the proof of `CaseIV.harith`, without `NotComb`). -/
theorem halfPlaneArith_pi3 (D : CongruentRegionDissection N) (hγ : D.model.angleAt 2 = Real.pi / 3) : HalfPlaneArith D := by
  have hαβ : D.model.angleAt 0 + D.model.angleAt 1 = 2 * Real.pi / 3 := by
    have := Erdos634.Draft.LaczFormal.angleAt_sum D.model
    linarith
  intro n0 n1 n2 hs hn
  subst hn
  have hp := Real.pi_pos
  rw [hγ] at hs
  have e1 : (n0 : ℝ) * (2 * Real.pi / 3) + n2 * (Real.pi / 3) = Real.pi := by nlinarith [hs, hαβ]
  have e2 : ((2 * n0 + n2 : ℕ) : ℝ) = 3 := by
    push_cast
    have : ((2 : ℝ) * n0 + n2) * (Real.pi / 3) = 3 * (Real.pi / 3) := by nlinarith [e1]
    exact mul_right_cancel₀ (by positivity) this
  have e3 : 2 * n0 + n2 = 3 := by exact_mod_cast e2
  omega


/-- **The fan at a tiling vertex in the relative interior of an edge** (`γ = π/3`): one straight virtual sector, three corner tiles with counts `(0,0,3)` or `(1,1,1)`, no tile with the vertex inside a side. -/
theorem edge_fan_counts_c (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (hγ : D.model.angleAt 2 = Real.pi / 3) (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1) (i : Fin M) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {V : Plane}
    (hV : V = (1 - t) • P.v i + t • P.v (i + 1)) (hvert : ∃ j k, (D.tile j).pts k = V) :
    ∃ (pT : V2) (F : ExtFan D.toRegionDissection V Unit), Par pT (toV2 (P.e i)) ∧ F.pe () = (-pT.1, -pT.2) ∧ F.qe () = pT ∧
      (∀ x : AtV D.toRegionDissection V, 0 < crs (F.p x) (F.q x)) ∧
      ((cnt D idx V 0 = 0 ∧ cnt D idx V 1 = 0 ∧ cnt D idx V 2 = 3) ∨ (cnt D idx V 0 = 1 ∧ cnt D idx V 1 = 1 ∧ cnt D idx V 2 = 1)) ∧
      Fintype.card (AtV D.toRegionDissection V) = 3 := by
  classical
  subst hV
  obtain ⟨pT, F, hpd, hpe, hqe, hTgt⟩ := fan_open_edge D.toRegionDissection P hreg i ht0 ht1 hvert
  have hpT : pT ≠ 0 := hpd.ne_left
  have hang := head_angle_sum_gen D idx hidxA F
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
  have hcls := (halfPlaneArith_pi3 D hγ) _ _ _ hS (hregc ((1 - t) • P.v i + t • P.v (i + 1)))
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
    · have := hregc ((1 - t) • P.v i + t • P.v (i + 1)); omega
    · have := hregc ((1 - t) • P.v i + t • P.v (i + 1)); omega
  refine ⟨pT, F, hpd, hpe, hqe, hcorner, ?_, hcard⟩
  have hr := hregc ((1 - t) • P.v i + t • P.v (i + 1))
  rcases hcls with ⟨h0', h2'⟩ | ⟨h0', h2'⟩
  · left; exact ⟨h0', by omega, h2'⟩
  · right; exact ⟨h0', by omega, h2'⟩


/-- **The local data at a side vertex, `Γ_c` version.**  `V` in the relative interior of the edge `i` (`γ = π/3`, no edge of `Γ_c` starts at `V` because `V` is a boundary point):
a three-tile fan; either the three types at `V` are distinct, or all three corners at `V` are `γ` (the exceptional vertex `3γ = π`); the first sides on the two inner rays have the
same `c`-status. -/
theorem edge_vertex_data_c (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx) (hγ : D.model.angleAt 2 = Real.pi / 3) (i : Fin M) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {V : Plane}
    (hV : V = (1 - t) • P.v i + t • P.v (i + 1)) (hvert : ∃ j k, (D.tile j).pts k = V) :
    ∃ (pT : V2) (F : ExtFan D.toRegionDissection V Unit) (s1 s2 s3 : AtV D.toRegionDissection V),
      Par pT (toV2 (P.e i)) ∧ SideFan3 D.toRegionDissection V pT F.p F.q s1 s2 s3 ∧
      (∃ k, (D.tile s2.1).pts k = V) ∧
      ((∀ k1 k2 k3, (D.tile s1.1).pts k1 = V → (D.tile s2.1).pts k2 = V → (D.tile s3.1).pts k3 = V →
        idx s1.1 k1 ≠ idx s2.1 k2 ∧ idx s1.1 k1 ≠ idx s3.1 k3 ∧ idx s2.1 k2 ≠ idx s3.1 k3) ∨
       (∀ k3, (D.tile s3.1).pts k3 = V → idx s3.1 k3 = 2)) ∧
      (nsq (F.q s1) = slen D 2 ^ 2 ↔ nsq (F.p s2) = slen D 2 ^ 2) ∧ (nsq (F.q s2) = slen D 2 ^ 2 ↔ nsq (F.p s3) = slen D 2 ^ 2) := by
  classical
  have hG := h.caseG
  have hs0 : slen (relabelC D) 0 = slen D 2 := relabelC_slen0 D
  haveI : HasFansC (relabelC D).toRegionDissection := (inferInstance : HasFansC D.toRegionDissection)
  have hbd : V ∉ interior D.region := by
    rw [hreg]; exact not_interior_of_c_zero P (i := i) (by rw [hV]; exact c_on_edge P i t)
  obtain ⟨pT, F, hpd, hpe, hqe, hcr, hcls, hcard⟩ := edge_fan_counts_c D P hreg idx h.hidxA hγ h.hregc i ht0 ht1 hV hvert
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
  rcases hcls with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩
  · right
    intro k3 hk3
    exact idx_two_of_cnt D idx e0 e1 hk3
  · left
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

theorem swap02_symm_zero_iff (x : Fin 3) : (Equiv.swap (0 : Fin 3) 2).symm x = 0 ↔ x = 2 := by
  revert x; decide

set_option maxHeartbeats 3200000 in
/-- **The `γ` rule along a side** (Laczkovich Lemma 4.4, local content): two consecutive tiles `j1` (ending at `V`) and `j2` (starting at `V`) of the walk along the edge `i`, `V` in the relative
interior of the edge.  If `j1` has `γ` at its tail then `j2` has `γ` at its tail `V`. -/
theorem edge_step_c (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx) (hγ : D.model.angleAt 2 = Real.pi / 3) (i : Fin M) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {V : Plane} (hV : V = (1 - t) • P.v i + t • P.v (i + 1)) {U U'' : Plane} {j1 j2 : Fin N}
    (h1 : TriStep (D.tile j1) (toV2 (P.e i)) U V) (h2 : TriStep (D.tile j2) (toV2 (P.e i)) V U'')
    (kR fR kL fL : Fin 3) (hR1 : (D.tile j2).pts kR = V) (hR2 : (D.tile j2).pts fR = U'')
    (hL1 : (D.tile j1).pts kL = V) (hL2 : (D.tile j1).pts fL = U) :
    idx j1 fL = 2 → idx j2 kR = 2 := by
  classical
  intro hg
  have hG := h.caseG
  haveI : HasFansC (relabelC D).toRegionDissection := (inferInstance : HasFansC D.toRegionDissection)
  have hvert : ∃ j k, (D.tile j).pts k = V := ⟨j2, kR, hR1⟩
  obtain ⟨pT, F, s1, s2, s3, hpd, hF, hc2, hcls, hno1, hno2⟩ := edge_vertex_data_c D P hreg idx h hγ i ht0 ht1 hV hvert
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
  rcases hcls with hnorm | hall
  · have hnorm' : ∀ k1 k2 k3, (D.tile s1.1).pts k1 = V → (D.tile s2.1).pts k2 = V → (D.tile s3.1).pts k3 = V →
        relabelCIdx idx s1.1 k1 ≠ relabelCIdx idx s2.1 k2 ∧ relabelCIdx idx s1.1 k1 ≠ relabelCIdx idx s3.1 k3 ∧
        relabelCIdx idx s2.1 k2 ≠ relabelCIdx idx s3.1 k3 := by
      intro k1 k2 k3 a1 a2 a3
      obtain ⟨n1, n2, n3⟩ := hnorm k1 k2 k3 a1 a2 a3
      have inj : ∀ (a b : Fin N) (k k' : Fin 3), relabelCIdx idx a k = relabelCIdx idx b k' → idx a k = idx b k' := by
        intro a b k k' e
        unfold relabelCIdx at e
        rw [relabelIdx_apply, relabelIdx_apply] at e
        exact Equiv.injective _ e
      exact ⟨fun e => n1 (inj _ _ _ _ e), fun e => n2 (inj _ _ _ _ e), fun e => n3 (inj _ _ _ _ e)⟩
    have hs0 : slen (relabelC D) 0 = slen D 2 := relabelC_slen0 D
    have := side_step_all (relabelC D) (relabelCIdx idx) hG.hidx V hF hc2 hG.hab hG.hac hnorm' (by rw [hs0]; exact hno1) (by rw [hs0]; exact hno2)
      kR fR kL fL (by rw [hj2]; exact hR1) hR2' (by rw [hj1]; exact hL1) hL2'
    rw [hj2, hj1] at this
    have h3 := this.2.1
    show idx j2 kR = 2
    unfold relabelCIdx at h3
    rw [relabelIdx_apply, relabelIdx_apply] at h3
    exact (swap02_symm_zero_iff _).mp (h3 ((swap02_symm_zero_iff _).mpr hg))
  · exfalso
    have hk := hall kL (by rw [hj1]; exact hL1)
    rw [hj1] at hk
    have hkf : kL = fL := (idx j1).injective (hk.trans hg.symm)
    have hne := hL2'.ne_left
    apply hne
    rw [hj1, ← hkf, hL1]
    unfold toV2; ext <;> simp


set_option maxHeartbeats 3200000 in
/-- **The `γ` rule along the whole edge** (Laczkovich Lemma 4.4 (i), proof): `γ` at the tail of the first tile of the walk gives `γ` at the tail of the last tile. -/
theorem walk_gamma (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx) (hγ : D.model.angleAt 2 = Real.pi / 3) (i : Fin M) {L : List (Fin N × Plane × Plane)}
    (W : WalkT D.toRegionDissection (toV2 (P.e i)) (P.v i) (P.v (i + 1)) L) {e0 el : Fin N × Plane × Plane}
    (hf : L.head? = some e0) (hl : L.getLast? = some el) :
    TyAt D idx e0.1 e0.2.1 2 → TyAt D idx el.1 el.2.1 2 := by
  classical
  have hU : ∃ s : ℝ, 0 ≤ s ∧ toV2 (P.v i - P.v i) = (s * (toV2 (P.e i)).1, s * (toV2 (P.e i)).2) :=
    ⟨0, le_rfl, by unfold toV2; ext <;> simp⟩
  have hL : ∃ L0, L = e0 :: L0 := by
    cases L with
    | nil => simp at hf
    | cons x L0 => simp at hf; exact ⟨L0, by rw [hf]⟩
  obtain ⟨L0, hL0⟩ := hL
  have hel_mem : el ∈ L := List.mem_of_getLast? hl
  intro hR
  refine walk_prop_forward D.toRegionDissection P hreg i (fun e => TyAt D idx e.1 e.2.1 2) ?_ rfl W hU e0 L0 hL0 hR el hel_mem
  intro e e2 t ht0 ht1 hVt hX2 hS1 hS2 hRe
  obtain ⟨kk1, f1, hk1, hf1⟩ := step_idx hS1
  obtain ⟨kk2, f2, hk2, hf2⟩ := step_idx hS2
  have := edge_step_c D P hreg idx h hγ i ht0 ht1 hVt (U := e.2.1) (U'' := e2.2.2) (j1 := e.1) (j2 := e2.1) hS1 (by rw [← hX2]; exact hS2)
    kk2 f2 f1 kk1 (by rw [← hX2, ← hk2]) (by rw [hf2]) hf1 hk1 ((tyAt_iff hk1 2).mp hRe)
  exact (tyAt_iff hk2 2).mpr this

set_option maxHeartbeats 3200000 in
/-- **A corner of the polygon equal to `π/3` is a single `γ` corner**: every tile with a corner at `v_{k+1}` has type `γ` there. -/
theorem corner_pi3_types (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (hγ : D.model.angleAt 2 = Real.pi / 3)
    (hαβ : D.model.angleAt 0 + D.model.angleAt 1 = 2 * Real.pi / 3) (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1) (k : Fin M)
    (hkang : P.angle (k + 1) = Real.pi / 3) :
    ∀ (j : Fin N) (kk : Fin 3), (D.tile j).pts kk = P.v (k + 1) → idx j kk = 2 := by
  classical
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
  have hang := head_angle_sum_gen D idx hidxA F
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
  have hr : ((cnt D idx V 0 : ℕ) : ℝ) = (cnt D idx V 1 : ℕ) := by exact_mod_cast hregc V
  have hN2 : ((2 * cnt D idx V 1 + cnt D idx V 2 : ℕ) : ℝ) * (Real.pi / 3) = wd pT qT := by
    rw [← hsum', hr, hγ]
    have := hαβ
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
    have := hregc V
    omega
  have hang3 : P.angle (k + 1) = ((2 * cnt D idx V 1 + cnt D idx V 2 : ℕ) : ℝ) * (Real.pi / 3) := by rw [hθ, hN2]

  have hc : 2 * cnt D idx V 1 + cnt D idx V 2 = 1 := by
    have h1 : ((2 * cnt D idx V 1 + cnt D idx V 2 : ℕ) : ℝ) * (Real.pi / 3) = 1 * (Real.pi / 3) := by
      rw [← hang3, hkang]; ring
    have h2 : ((2 * cnt D idx V 1 + cnt D idx V 2 : ℕ) : ℝ) = 1 := mul_right_cancel₀ (by positivity) h1
    exact_mod_cast h2
  have hc1 : cnt D idx V 1 = 0 := by omega
  have hc0 : cnt D idx V 0 = 0 := by have := hregc V; omega
  intro j kk hjk
  exact idx_two_of_cnt D idx hc0 hc1 hjk

set_option maxHeartbeats 3200000 in
/-- **No two consecutive corners of the polygon equal `π/3`** (Subcase IVc with `N ≤ 4`: a triangle or a trapezoid is impossible).  `γ = π/3`, regular counts, `c` not a nonnegative
rational combination of `a, b`.  Proof: the first tile of the walk along the edge has `γ` at its tail (corner `π/3`), so by the `γ` rule (`walk_gamma`) the last tile has `γ` at its tail;
it also has `γ` at its head (corner `π/3`): two `γ` corners in one tile. -/
theorem no_adjacent_pi3 (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx) (hγ : D.model.angleAt 2 = Real.pi / 3) (k : Fin M)
    (hk1 : P.angle (k + 1) = Real.pi / 3) (hk2 : P.angle (k + 1 + 1) = Real.pi / 3) : False := by
  classical
  have hαβ : D.model.angleAt 0 + D.model.angleAt 1 = 2 * Real.pi / 3 := by
    have := Erdos634.Draft.LaczFormal.angleAt_sum D.model
    linarith
  obtain ⟨L, e0, el, hW, hh, hl, hs1, hs2, hT0, hT1⟩ := edge_data D P hreg (k + 1)
  have c1 := corner_pi3_types D P hreg idx h.hidxA hγ hαβ h.hregc k hk1
  have c2 := corner_pi3_types D P hreg idx h.hidxA hγ hαβ h.hregc (k + 1) hk2
  have t0 : TyAt D idx e0.1 e0.2.1 2 := by
    intro kk hkk
    exact c1 e0.1 kk (hkk.trans hs1)
  have t1 : TyAt D idx el.1 el.2.2 2 := by
    intro kk hkk
    exact c2 el.1 kk (hkk.trans hs2)
  have t2 := walk_gamma D P hreg idx h hγ (k + 1) hW hh hl t0
  obtain ⟨kk, f, g, hk, hf, hfk, -⟩ := hT1
  have a1 := (tyAt_iff hk 2).mp t2
  have a2 := (tyAt_iff hf 2).mp t1
  exact hfk ((idx el.1).injective (a2.trans a1.symm))


theorem no_adjacent_pi3' (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx) (hγ : D.model.angleAt 2 = Real.pi / 3) (i : Fin M)
    (hi : P.angle i = Real.pi / 3) (hj : P.angle (i + 1) = Real.pi / 3) : False := by
  have e : i - 1 + 1 = i := sub_add_cancel i 1
  exact no_adjacent_pi3 D P hreg idx h hγ (i - 1) (by rw [e]; exact hi) (by rw [e]; exact hj)

/-- `sin α / sin β = a / b` for the model triangle. -/
theorem sin_ratio_eq (D : CongruentRegionDissection N) :
    Real.sin (D.model.angleAt 0) / Real.sin (D.model.angleAt 1) = slen D 0 / slen D 1 := by
  obtain ⟨h1, -⟩ := slen_sin_rel' D
  have hb : 0 < slen D 1 := slen_pos D 1
  have hsum := Erdos634.Draft.LaczFormal.angleAt_sum D.model
  have p0 := model_angle_pos' D 0
  have p1 := model_angle_pos' D 1
  have p2 := model_angle_pos' D 2
  have s1 : 0 < Real.sin (D.model.angleAt 1) := Real.sin_pos_of_pos_of_lt_pi p1 (by linarith)
  rw [div_eq_div_iff s1.ne' hb.ne']
  linarith

set_option maxHeartbeats 6400000 in
/-- **Subcase IVc, `N ≤ 4`.**  `γ = π/3`, regular tiling of a convex `M`-gon, `M ≤ 4`, `a, b` commensurable, `c` not commensurable with `a`: the polygon is a parallelogram of angles `γ, π - γ` whose sides have
rational ratio times `sin α / sin β` (conclusion (i) of Theorem 2.1); triangles and trapezoids are impossible. -/
theorem caseIVc_small {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) (hγ : angleAt T.C.model 2 = Real.pi / 3)
    (hab : Comm (slen T.C 0) (slen T.C 1)) (hac : ¬ Comm (slen T.C 0) (slen T.C 2)) (hM : M ≤ 4) : Concl1 T.C T.P := by
  classical
  have hRat := polytiling_rational T hreg hab hac
  obtain ⟨idx, hA, hcnt⟩ := hreg
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hC : CaseC T.C idx := ⟨idx_dist_of_angle T.C idx hA, hA, fun X => hcnt X, notComb_c_of_comm (slen_pos T.C 2) hab hac⟩
  have hγ' : T.C.model.angleAt 2 = Real.pi / 3 := hγ
  have hαβ : T.C.model.angleAt 0 + T.C.model.angleAt 1 = 2 * Real.pi / 3 := by
    have := Erdos634.Draft.LaczFormal.angleAt_sum T.C.model
    linarith
  have hall : ∀ i : Fin M, T.P.angle i = Real.pi / 3 ∨ T.P.angle i = 2 * Real.pi / 3 := by
    intro i
    have := polygon_angle_pi3 T.C T.P T.region_eq idx hA hγ' hαβ (fun X => hcnt X) (i - 1)
    rwa [sub_add_cancel] at this
  have hsum := poly_angle_sum T.P
  have hpi := Real.pi_pos
  have hM3 : 3 ≤ M := T.P.three_le
  have adj : ∀ i : Fin M, T.P.angle i = Real.pi / 3 → T.P.angle (i + 1) = Real.pi / 3 → False :=
    fun i h1 h2 => no_adjacent_pi3' T.C T.P T.region_eq idx hC hγ' i h1 h2
  -- the ratio of the first two sides
  have hratio : ∃ q : ℚ, T.P.side 0 / T.P.side 1 = q * (Real.sin (angleAt T.C.model 0) / Real.sin (angleAt T.C.model 1)) := by
    obtain ⟨m1, n1, hm1, hn1, e1⟩ := hRat 0 1
    obtain ⟨m2, n2, hm2, hn2, e2⟩ := hab
    have hs1 : 0 < T.P.side 1 := side_pos T.P 1
    have hsb : 0 < slen T.C 1 := slen_pos T.C 1
    refine ⟨((n1 * m2 : ℕ) : ℚ) / ((m1 * n2 : ℕ) : ℚ), ?_⟩
    have hsr : Real.sin (angleAt T.C.model 0) / Real.sin (angleAt T.C.model 1) = slen T.C 0 / slen T.C 1 := sin_ratio_eq T.C
    rw [hsr]
    have hm1' : (m1 : ℝ) ≠ 0 := by positivity
    have hn2' : (n2 : ℝ) ≠ 0 := by positivity
    have hm2' : (m2 : ℝ) ≠ 0 := by positivity
    push_cast
    rw [div_eq_iff hs1.ne']
    field_simp
    linear_combination ((n2 : ℝ) * slen T.C 1) * e1 - ((n1 : ℝ) * T.P.side 1) * e2
  by_cases hM4 : M = 4
  · subst hM4
    have hsum4 : ∑ i : Fin 4, T.P.angle i = 2 * Real.pi := by rw [hsum]; norm_num
    rw [Fin.sum_univ_four] at hsum4
    have n01 : ¬ (T.P.angle 0 = Real.pi / 3 ∧ T.P.angle 1 = Real.pi / 3) := fun ⟨a, b⟩ => adj 0 a (by simpa using b)
    have n12 : ¬ (T.P.angle 1 = Real.pi / 3 ∧ T.P.angle 2 = Real.pi / 3) := fun ⟨a, b⟩ =>
      adj 1 a (by have e : (1 : Fin 4) + 1 = 2 := by decide
                  rw [e]; exact b)
    have n23 : ¬ (T.P.angle 2 = Real.pi / 3 ∧ T.P.angle 3 = Real.pi / 3) := fun ⟨a, b⟩ =>
      adj 2 a (by have e : (2 : Fin 4) + 1 = 3 := by decide
                  rw [e]; exact b)
    have n30 : ¬ (T.P.angle 3 = Real.pi / 3 ∧ T.P.angle 0 = Real.pi / 3) := fun ⟨a, b⟩ =>
      adj 3 a (by have e : (3 : Fin 4) + 1 = 0 := by decide
                  rw [e]; exact b)
    have par : (T.P.angle 0 = Real.pi / 3 ∧ T.P.angle 1 = 2 * Real.pi / 3 ∧ T.P.angle 2 = Real.pi / 3 ∧ T.P.angle 3 = 2 * Real.pi / 3) ∨
        (T.P.angle 0 = 2 * Real.pi / 3 ∧ T.P.angle 1 = Real.pi / 3 ∧ T.P.angle 2 = 2 * Real.pi / 3 ∧ T.P.angle 3 = Real.pi / 3) := by
      rcases hall 0 with h0 | h0 <;> rcases hall 1 with h1 | h1 <;> rcases hall 2 with h2 | h2 <;> rcases hall 3 with h3 | h3 <;>
        first
        | (exfalso; linarith)
        | (exfalso; exact n01 ⟨h0, h1⟩)
        | (exfalso; exact n12 ⟨h1, h2⟩)
        | (exfalso; exact n23 ⟨h2, h3⟩)
        | (exfalso; exact n30 ⟨h3, h0⟩)
        | (left; exact ⟨h0, h1, h2, h3⟩)
        | (right; exact ⟨h0, h1, h2, h3⟩)
    have hpg : ∀ i : Fin 4, T.P.v i + T.P.v (i + 2) = T.P.v (i + 1) + T.P.v (i + 3) := by
      rcases par with ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩
      · exact par_all T.P 0 (quad_parallelogram T.P 0 (by simpa using h1) (by simpa using h2) (by simpa using h3))
      · have e1 : (3 : Fin 4) + 1 = 0 := by decide
        have e2 : (3 : Fin 4) + 2 = 1 := by decide
        have e3 : (3 : Fin 4) + 3 = 2 := by decide
        exact par_all T.P 3 (quad_parallelogram T.P 3 (by rw [e1]; exact h0) (by rw [e2]; exact h1) (by rw [e3]; exact h2))
    have hex : ∃ i : Fin 4, T.P.angle i = angleAt T.C.model 2 := by
      rcases par with ⟨h0, -⟩ | ⟨-, h1, -⟩
      · exact ⟨0, by rw [h0]; exact hγ.symm⟩
      · exact ⟨1, by rw [h1]; exact hγ.symm⟩
    exact ⟨⟨rfl, hpg⟩, hex, Or.inl hratio⟩
  · exfalso
    have hM3' : M = 3 := by omega
    subst hM3'
    have hsum3 : ∑ i : Fin 3, T.P.angle i = Real.pi := by rw [hsum]; norm_num
    rw [Fin.sum_univ_three] at hsum3
    have a1 : T.P.angle 1 = Real.pi / 3 := by
      rcases hall 0 with h0 | h0 <;> rcases hall 1 with h1 | h1 <;> rcases hall 2 with h2 | h2 <;> first | exact h1 | (exfalso; linarith)
    have a2 : T.P.angle 2 = Real.pi / 3 := by
      rcases hall 0 with h0 | h0 <;> rcases hall 1 with h1 | h1 <;> rcases hall 2 with h2 | h2 <;> first | exact h2 | (exfalso; linarith)
    exact adj 1 a1 (by have e : (1 : Fin 3) + 1 = 2 := by decide
                       rw [e]; exact a2)

end Erdos634.Draft.LaczFormal.RG
