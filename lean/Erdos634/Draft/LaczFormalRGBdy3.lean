-- Draft/LaczFormalRGBdy3.lean -- S4 of PLAN_THM21: first tile steps along a boundary line of a dissection of a region: from the fan with the virtual straight sector (open edge) or the
-- two virtual sectors (corner), the tile sector that follows the virtual one starts along the boundary direction `d`, hence is a left step `TriStep` from the vertex.
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 4, Lemma 4.3 proof: the division X = U_0, U_1, .., U_k = Y of the side XY), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRGBdy2
import Erdos634.Draft.LaczFormalGraphWalk

open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

/-- The tile sector after the straight virtual sector of an open-edge vertex gives a left step along `d` from the vertex. -/
theorem first_step_open (D : RegionDissection N) {V : Plane} (F : ExtFan D V Unit) {pT d : V2}
    (hpe : F.pe () = (-pT.1, -pT.2)) (hqe : F.qe () = pT) (hpd : Par pT d)
    (hvert : ∃ i k, (D.tile i).pts k = V) : ∃ i U', TriStep (D.tile i) d V U' := by
  classical
  have hpT : pT ≠ 0 := hpd.ne_left
  obtain ⟨j0, hj0, hej0⟩ := F.hsurj (Sum.inr ())
  obtain ⟨i0, k0, hk0⟩ := hvert
  have hmem0 : V ∈ (D.tile i0).carrier := hk0 ▸ subset_convexHull ℝ _ ⟨k0, rfl⟩
  have hLcard : Fintype.card (AtV D V ⊕ Unit) = Fintype.card (AtV D V) + 1 := by
    rw [Fintype.card_sum]; simp
  have hAtV : 0 < Fintype.card (AtV D V) := Fintype.card_pos_iff.mpr ⟨⟨i0, hmem0⟩⟩
  have hP0 := F.hP j0
  rw [hej0] at hP0
  simp only [Sum.elim_inr] at hP0
  rw [hqe] at hP0
  rcases hnext : F.e (j0 + 1) with s | u
  · rw [hnext] at hP0
    simp only [Sum.elim_inl] at hP0
    have hsp : Par (F.p s) d := hP0.trans hpd
    have hsum : ∑ x : AtV D V, wd (F.p x) (F.q x) ≤ Real.pi := by
      have hv : ∑ j : Unit, wd (F.pe j) (F.qe j) = Real.pi := by
        rw [Fintype.sum_unique]
        show wd (F.pe ()) (F.qe ()) = Real.pi
        rw [hpe, hqe, wd_ext hpT]
      have := F.hsum
      linarith
    have hcorner : ∃ k, (D.tile s.1).pts k = V := by
      rcases F.hspec s with ⟨k, hk, -⟩ | ⟨hnv, m', -, -, hq, -⟩
      · exact ⟨k, hk⟩
      · exfalso
        have ht : (⟨i0, hmem0⟩ : AtV D V) ≠ s := by
          intro h
          have := congrArg Subtype.val h
          simp only at this
          rw [this] at hk0
          exact hnv k0 hk0
        refine no_straight_of_sum F.p F.q F.hok (Ne.symm ht) ?_ hsum
        rw [hq]; exact wd_straight (F.hok s).ne_p
    obtain ⟨kk, fl, hk, hp', hq'⟩ := spec_corner_data (F.hspec s) hcorner
    have hcrs := crs_pos_of_corner (F.hok s) (F.hspec s) hcorner
    exact ⟨s.1, (D.tile s.1).pts (armP kk fl), triStep_of_start kk fl hk hp' hq' hcrs hsp⟩
  · exfalso
    have h1 : F.e (j0 + 1) = F.e (j0 + 0) := by
      show F.e (j0 + 1) = F.e j0
      rw [hnext, hej0]
    have := e_inj_shift F j0 (by omega) (by omega) h1
    omega

theorem wd_lt_pi_of_crs_pos {p q : V2} (h : 0 < crs p q) : wd p q < Real.pi := by
  unfold wd
  rw [Complex.arg_lt_pi_iff]
  right
  simpa using h.ne'

/-- At a corner fan the tiles' widths add up to the width of the target cone. -/
theorem corner_tile_sum (D : RegionDissection N) {V : Plane} (F : ExtFan D V Bool) {pT qT : V2} (hcr : 0 < crs pT qT)
    (h1 : F.pe true = (-qT.1, -qT.2)) (h2 : F.qe true = pT) (h3 : F.pe false = qT) (h4 : F.qe false = (-qT.1, -qT.2)) :
    ∑ x : AtV D V, wd (F.p x) (F.q x) = wd pT qT := by
  have hqT : qT ≠ 0 := by
    intro h; rw [h] at hcr; unfold crs at hcr; simp at hcr
  have := F.hsum
  rw [Fintype.sum_bool, h1, h2, h3, h4, wd_straight hqT, wd_neg_left hcr] at this
  linarith

/-- The tile sector after the virtual sector `(-qT, pT)` of a corner fan gives a left step along `d` from the corner. -/
theorem first_step_corner (D : RegionDissection N) {V : Plane} (F : ExtFan D V Bool) {pT qT d : V2} (hcr : 0 < crs pT qT)
    (h1 : F.pe true = (-qT.1, -qT.2)) (h2 : F.qe true = pT) (h3 : F.pe false = qT) (h4 : F.qe false = (-qT.1, -qT.2))
    (hpd : Par pT d) (hvert : ∃ i k, (D.tile i).pts k = V) : ∃ i U', TriStep (D.tile i) d V U' := by
  classical
  obtain ⟨j0, hj0, hej0⟩ := F.hsurj (Sum.inr true)
  obtain ⟨i0, k0, hk0⟩ := hvert
  have hmem0 : V ∈ (D.tile i0).carrier := hk0 ▸ subset_convexHull ℝ _ ⟨k0, rfl⟩
  have hsumT := corner_tile_sum D F hcr h1 h2 h3 h4
  have hP0 := F.hP j0
  rw [hej0] at hP0
  simp only [Sum.elim_inr] at hP0
  rw [h2] at hP0
  rcases hnext : F.e (j0 + 1) with s | b
  · rw [hnext] at hP0
    simp only [Sum.elim_inl] at hP0
    have hsp : Par (F.p s) d := hP0.trans hpd
    have hcorner : ∃ k, (D.tile s.1).pts k = V := by
      rcases F.hspec s with ⟨k, hk, -⟩ | ⟨hnv, m', -, -, hq, -⟩
      · exact ⟨k, hk⟩
      · exfalso
        have hw : wd (F.p s) (F.q s) = Real.pi := by rw [hq]; exact wd_straight (F.hok s).ne_p
        have hle : wd (F.p s) (F.q s) ≤ ∑ x : AtV D V, wd (F.p x) (F.q x) :=
          Finset.single_le_sum (f := fun x => wd (F.p x) (F.q x)) (fun x _ => (wd_pos (F.hok x)).le) (Finset.mem_univ s)
        have := wd_lt_pi_of_crs_pos hcr
        linarith
    obtain ⟨kk, fl, hk, hp', hq'⟩ := spec_corner_data (F.hspec s) hcorner
    have hcrs := crs_pos_of_corner (F.hok s) (F.hspec s) hcorner
    exact ⟨s.1, (D.tile s.1).pts (armP kk fl), triStep_of_start kk fl hk hp' hq' hcrs hsp⟩
  · exfalso
    rw [hnext] at hP0
    simp only [Sum.elim_inr] at hP0
    cases b
    · simp only [h3] at hP0
      have := hP0.1
      unfold crs at this hcr
      nlinarith
    · have h5 : F.e (j0 + 1) = F.e (j0 + 0) := by
        show F.e (j0 + 1) = F.e j0
        rw [hnext, hej0]
      have := e_inj_shift F j0 (by
        have : 2 ≤ Fintype.card (AtV D V ⊕ Bool) := by
          rw [Fintype.card_sum]; simp
        omega) (by
        have := hj0; omega) h5
      omega

/-- The tile sector before the virtual sector `(qT, -qT)` of a corner fan gives a left step along `dd` ENDING at the corner, where `qT` points along `-dd`. -/
theorem last_step_corner (D : RegionDissection N) {V : Plane} (F : ExtFan D V Bool) {pT qT dd : V2} (hcr : 0 < crs pT qT)
    (h1 : F.pe true = (-qT.1, -qT.2)) (h2 : F.qe true = pT) (h3 : F.pe false = qT) (h4 : F.qe false = (-qT.1, -qT.2))
    (hqd : Par qT (neg2 dd)) (hvert : ∃ i k, (D.tile i).pts k = V) : ∃ i U'', TriStep (D.tile i) dd U'' V := by
  classical
  set L := Fintype.card (AtV D V ⊕ Bool) with hL
  obtain ⟨j0, hj0, hej0⟩ := F.hsurj (Sum.inr false)
  have hsumT := corner_tile_sum D F hcr h1 h2 h3 h4
  have hL2 : 2 ≤ L := by rw [hL, Fintype.card_sum]; simp
  have hP0 := F.hP (j0 + (L - 1))
  rw [show j0 + (L - 1) + 1 = j0 + L by omega, F.hper j0, hej0] at hP0
  simp only [Sum.elim_inr] at hP0
  rw [h3] at hP0
  rcases hprev : F.e (j0 + (L - 1)) with s | b
  · rw [hprev] at hP0
    simp only [Sum.elim_inl] at hP0
    have hcorner : ∃ k, (D.tile s.1).pts k = V := by
      rcases F.hspec s with ⟨k, hk, -⟩ | ⟨hnv, m', -, -, hq, -⟩
      · exact ⟨k, hk⟩
      · exfalso
        have hw : wd (F.p s) (F.q s) = Real.pi := by rw [hq]; exact wd_straight (F.hok s).ne_p
        have hle : wd (F.p s) (F.q s) ≤ ∑ x : AtV D V, wd (F.p x) (F.q x) :=
          Finset.single_le_sum (f := fun x => wd (F.p x) (F.q x)) (fun x _ => (wd_pos (F.hok x)).le) (Finset.mem_univ s)
        have := wd_lt_pi_of_crs_pos hcr
        linarith
    obtain ⟨kk, fl, hk, hp', hq'⟩ := spec_corner_data (F.hspec s) hcorner
    have hcrs := crs_pos_of_corner (F.hok s) (F.hspec s) hcorner
    have hqs : Par (F.q s) qT := hP0.symm
    have hst := triStep_of_end (T := D.tile s.1) (d := qT) kk fl hk hp' hq' hcrs hqs
    have hneg : Par dd (neg2 qT) := by
      have := par_neg hqd
      unfold neg2 at this ⊢
      simp only [neg_neg] at this
      exact this.symm
    exact ⟨s.1, _, TriStep.of_par hneg hst⟩
  · exfalso
    rw [hprev] at hP0
    simp only [Sum.elim_inr] at hP0
    cases b
    · have h5 : F.e (j0 + (L - 1)) = F.e (j0 + 0) := by
        show F.e (j0 + (L - 1)) = F.e j0
        rw [hprev, hej0]
      have := e_inj_shift F j0 (by omega) (by omega) h5
      omega
    · simp only [h2] at hP0
      have := hP0.1
      unfold crs at this hcr
      nlinarith

end Erdos634.Draft.LaczFormal.RG
