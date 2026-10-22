import Erdos634.Draft.BeesonIso3g

/-!
# Beeson, "Tilings of an isosceles triangle" (arXiv 1206.1974 v7), Lemma 11.8: the north side of a chord supports at least TWO tiles

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.1974 v7, Lemma 11.8; arXiv 1206.2229), Laczkovich (DCG 48 (2012), Sect. 4), Beeson-Zhang, Herdt, Zhang.
Formalization debt, not progress on the /goal outcomes.

Printed: "Consider the triangle BEF.  Since it has the same angle at B as ABC, namely alpha + beta, its angles at E and F must each be alpha.  Then the north side of EF cannot be
covered by a single tile, since if it were, that tile would have two alpha angles, one at E and another at F."
* `poly_angle_wd`: the interior angle at `v_{k+1}` is the width of the sector `(e_{k+1}, -e_k)`.
* `single_step_false`: if the chord `E F` (adjacent open sides, interior angle at `B` equal to `alpha + beta = pi - 2 alpha`) is a single right step `F -> E` of a tile, contradiction:
  the widths of the chains at `E`, `F` between the chord and the side `B` add up to `2 alpha` (triangle `BEF`), so by `north_arith` each is one tile with angle `alpha`; that tile would have `alpha` at
  the two distinct vertices `E`, `F`.
-/

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem poly_angle_wd (P : ConvPoly M) (k : Fin M) :
    P.angle (k + 1) = wd (toV2 (P.e (k + 1))) (-(toV2 (P.e k)).1, -(toV2 (P.e k)).2) := by
  have hu : P.e (k + 1) ≠ 0 := P.e_ne_zero P.three_le _
  have hw : -P.e k ≠ 0 := neg_ne_zero.mpr (P.e_ne_zero P.three_le _)
  have hc : 0 ≤ cross (P.e (k + 1)) (-P.e k) := by
    have := crs_consecutive_pos P k
    have e : cross (P.e (k + 1)) (-P.e k) = crs (toV2 (P.e k)) (toV2 (P.e (k + 1))) := by
      rw [← crs_toV2]; unfold crs toV2; simp; ring
    rw [e]; exact this.le
  have e1 : toV2 (-P.e k) = (-(toV2 (P.e k)).1, -(toV2 (P.e k)).2) := by unfold toV2; simp
  rw [← e1, wd_eq_angle hu hw hc]
  unfold ConvPoly.angle cornerAngle EuclideanGeometry.angle
  rw [add_sub_cancel_right, InnerProductGeometry.angle_comm]
  congr 1
  unfold ConvPoly.e; simp

/-- Sums over `Finset.Ico 1 (m+1)` of the chain widths in terms of model angles of chosen corner labels. -/
theorem chain_labels (C : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidxA : ∀ i v, C.model.angleAt (idx i v) = (C.tile i).angleAt v) {Q : Plane} {pT : V2} (Ch : OpenChain C.toRegionDissection Q pT) :
    ∃ (l : ℕ → Fin 3) (kc : ℕ → Fin 3), ∀ j, 1 ≤ j → j < Ch.L →
      (C.tile (Ch.c j).1).pts (kc j) = Q ∧ idx (Ch.c j).1 (kc j) = l j ∧
      wd (Ch.F.p (Ch.c j)) (Ch.F.q (Ch.c j)) = C.model.angleAt (l j) := by
  have hex : ∀ j, ∃ k : Fin 3, (1 ≤ j ∧ j < Ch.L) → (C.tile (Ch.c j).1).pts k = Q := by
    intro j
    by_cases h : 1 ≤ j ∧ j < Ch.L
    · obtain ⟨k, hk⟩ := corner_of_crs_pos Ch.F (Ch.c j) (Ch.hcrs j h.1 h.2)
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose kc hkc using hex
  refine ⟨fun j => idx (Ch.c j).1 (kc j), kc, fun j h1 h2 => ?_⟩
  have hk := hkc j ⟨h1, h2⟩
  exact ⟨hk, rfl, sector_angle C idx hidxA Ch.F (Ch.c j) hk⟩

theorem single_step_false (C : CongruentRegionDissection N) [HasFansC C.toRegionDissection] (P : ConvPoly M) (hreg : C.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, C.model.angleAt (idx i v) = (C.tile i).angleAt v)
    (hβ : C.model.angleAt 1 = Real.pi - 3 * C.model.angleAt 0) (hγ : C.model.angleAt 2 = 2 * C.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, C.model.angleAt 0 = (r : ℝ) * Real.pi)
    (i : Fin M) {t t' : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (ht0' : 0 < t') (ht1' : t' < 1)
    {E F : Plane} (hE : E = (1 - t) • P.v i + t • P.v (i + 1)) (hF : F = (1 - t') • P.v (i + 1) + t' • P.v (i + 1 + 1)) (hEF : E ≠ F)
    (hB : P.angle (i + 1) = Real.pi - 2 * C.model.angleAt 0)
    (hvE : ∃ j k, (C.tile j).pts k = E) (hvF : ∃ j k, (C.tile j).pts k = F)
    {jt : Fin N} (hS : TriStep (C.tile jt) (neg2 (toV2 (F - E))) F E) : False := by
  obtain ⟨hg1, hg2, hg3⟩ := chord_geo P i ht1 ht0' hE hF
  obtain ⟨pE, hpE, ⟨CE⟩⟩ := chain_at C.toRegionDissection P hreg i ht0 ht1 hE hvE
  obtain ⟨pF, hpF, ⟨CF⟩⟩ := chain_at C.toRegionDissection P hreg (i + 1) ht0' ht1' hF hvF
  set d := toV2 (F - E) with hd
  set eI := toV2 (P.e i) with heI
  set eJ := toV2 (P.e (i + 1)) with heJ
  have hdE : 0 < crs pE d := crs_pos_par_left hpE.symm hg1
  have hndF : 0 < crs eJ (neg2 d) := by
    have : crs eJ (neg2 d) = crs d eJ := by unfold crs neg2; simp only; ring
    rw [this]; exact hg2
  have hdF : 0 < crs pF (neg2 d) := crs_pos_par_left hpF.symm hndF
  -- the sector at E
  obtain ⟨s, hs1, hsq, hsc, -⟩ := step_end_sector CE.F hS
  rw [neg2_neg2] at hsq
  obtain ⟨m, hm1, hmL, hms⟩ := CE.hsurj s
  have hqm : Par (CE.F.q (CE.c m)) d := by rw [hms]; exact hsq
  have hxs : ∑ j ∈ Finset.Ico 1 (m + 1), wd (CE.F.p (CE.c j)) (CE.F.q (CE.c j)) = wd eI d := by
    rw [← CE.wd_partial hpE.ne_left m hm1 hmL, wd_par_right hqm, wd_par_left hpE]
  -- the sector at F
  obtain ⟨s', hs'1, hs'p, hs'c, -⟩ := step_start_sector CF.F hS
  obtain ⟨m', hm'1, hm'L, hm's⟩ := CF.hsurj s'
  have hpm : Par (CF.F.p (CF.c m')) (neg2 d) := by rw [hm's]; exact hs'p
  have hm'2 : 2 ≤ m' := by
    by_contra hh
    have h1 : m' = 1 := by omega
    have h2 : Par (CF.F.p (CF.c m')) pF := by rw [h1]; exact CF.hfirst
    have := par_par_crs h2 hpm
    linarith
  have hqprev : Par (CF.F.q (CF.c (m' - 1))) (neg2 d) := by
    have h := CF.hadj (m' - 1) (by omega) (by omega)
    rw [show m' - 1 + 1 = m' by omega] at h
    exact h.symm.trans hpm
  have hys0 : ∑ j ∈ Finset.Ico 1 m', wd (CF.F.p (CF.c j)) (CF.F.q (CF.c j)) = wd pF (neg2 d) := by
    have := CF.wd_partial hpF.ne_left (m' - 1) (by omega) (by omega)
    rw [show m' - 1 + 1 = m' by omega] at this
    rw [← this, wd_par_right hqprev]
  have htot : ∑ j ∈ Finset.Ico 1 m', wd (CF.F.p (CF.c j)) (CF.F.q (CF.c j)) +
      ∑ j ∈ Finset.Ico m' CF.L, wd (CF.F.p (CF.c j)) (CF.F.q (CF.c j)) = Real.pi := by
    rw [← CF.hsum]
    exact Finset.sum_Ico_consecutive (fun j => wd (CF.F.p (CF.c j)) (CF.F.q (CF.c j))) (show 1 ≤ m' by omega) (show m' ≤ CF.L by omega)
  have hwdF : wd pF (neg2 d) = Real.pi - wd d eJ := by
    have e1 := wd_neg_neg eJ (neg2 d)
    rw [neg2_neg2] at e1
    have e2 := wd_neg_left hg2
    rw [wd_par_left hpF, ← e1, e2]
  have hys : ∑ j ∈ Finset.Ico m' CF.L, wd (CF.F.p (CF.c j)) (CF.F.q (CF.c j)) = wd d eJ := by
    linarith
  -- the triangle
  have htri := wd_triangle hg1 hg2 hg3
  have hBw : wd eJ (-eI.1, -eI.2) = Real.pi - 2 * C.model.angleAt 0 := by
    rw [← hB]; exact (poly_angle_wd P i).symm
  have hsum2 : wd eI d + wd d eJ = 2 * C.model.angleAt 0 := by linarith
  -- labels
  obtain ⟨lE, kcE, hlE⟩ := chain_labels C idx hidxA CE
  obtain ⟨lF, kcF, hlF⟩ := chain_labels C idx hidxA CF
  have sE : ∑ j ∈ Finset.Ico 1 (m + 1), C.model.angleAt (lE j) = wd eI d := by
    rw [← hxs]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_Ico] at hj
    exact ((hlE j hj.1 (by omega)).2.2).symm
  have sF : ∑ j ∈ Finset.Ico m' CF.L, C.model.angleAt (lF j) = wd d eJ := by
    rw [← hys]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_Ico] at hj
    exact ((hlF j (by omega) hj.2).2.2).symm
  obtain ⟨hc1, hc2, hl1, hl2⟩ := north_arith hα C.model.angleAt rfl hβ hγ (Finset.Ico 1 (m + 1)) (Finset.Ico m' CF.L) lE lF
    ⟨1, by simp; omega⟩ ⟨m', by simp; omega⟩ (by rw [sE, sF]; exact hsum2)
  have hmem1 : m ∈ Finset.Ico 1 (m + 1) := by simp; omega
  have hmem2 : m' ∈ Finset.Ico m' CF.L := by simp; omega
  have h1 := hl1 m hmem1
  have h2 := hl2 m' hmem2
  obtain ⟨hk1, hid1, -⟩ := hlE m hm1 hmL
  obtain ⟨hk2, hid2, -⟩ := hlF m' (by omega) hm'L
  have ht1' : (CE.c m).1 = jt := by rw [hms]; exact hs1
  have ht2' : (CF.c m').1 = jt := by rw [hm's]; exact hs'1
  rw [ht1'] at hk1 hid1
  rw [ht2'] at hk2 hid2
  have hkk : kcE m = kcF m' := (idx jt).injective (hid1.trans (h1.trans (hid2.trans h2).symm))
  apply hEF
  rw [← hk1, ← hk2, hkk]

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.single_step_false
