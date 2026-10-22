-- Draft/LaczFormalIIcWN17.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2, step (a): a relative interior point of an edge of Gamma_kite lies on no other edge of Gamma_kite.
-- Cases: T-junction (`tjunction`), transversal crossing (four half-discs), collinear overlap with the same / opposite orientation (labels alpha, beta).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN16

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord Filter Topology

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

theorem v2_sq_pos {d : V2} (hd : d ≠ 0) : 0 < d.1 ^ 2 + d.2 ^ 2 := by
  by_contra hh
  apply hd
  have a : d.1 = 0 := by nlinarith [sq_nonneg d.1, sq_nonneg d.2]
  have b : d.2 = 0 := by nlinarith [sq_nonneg d.1, sq_nonneg d.2]
  exact Prod.ext a b

set_option maxHeartbeats 1000000 in
theorem gkite_open_not_meet [NeZero N] (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {X Y X' Y' : Plane}
    (h : GKite D idx X Y) (h' : GKite D idx X' Y') (hne : ¬ (X = X' ∧ Y = Y')) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hz' : X + t • (Y - X) ∈ segment ℝ X' Y') : False := by
  obtain ⟨i, j, d, kk, f, kk2, f2, hij, hi, hj, hk, hf, hl1, hl2, hk2, hf2, hl3, hl4⟩ := h
  obtain ⟨i', j', d', kkp, fp, kk2p, f2p, hij', hi', hj', hkp, hfp, hl1p, hl2p, hk2p, hf2p, hl3p, hl4p⟩ := h'
  rw [segment_eq_image'] at hz'
  obtain ⟨t', ⟨ht'0, ht'1⟩, hzt⟩ := hz'
  have hD := D.toRegionDissection
  rcases ht'0.lt_or_eq with ht'0' | ht'0'
  · rcases ht'1.lt_or_eq with ht'1' | ht'1'
    · ----------------------------------------------------------------------------------------------- interior of both
      set z : Plane := X + t • (Y - X) with hzdef
      have hzt' : X' + t' • (Y' - X') = z := hzt
      have hz3 : Y' + (1 - t') • (X' - Y') = z := by
        rw [← hzt']; ext m; simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; ring
      obtain ⟨ri, hri, hi1⟩ := halfdisc (D.tile i) hi ht0 ht1
      obtain ⟨ri', hri', hi1'⟩ := halfdisc (D.tile i') hi' ht'0' ht'1'
      obtain ⟨rj', hrj', hj1'⟩ := halfdisc (D.tile j') hj' (t := 1 - t') (by linarith) (by linarith)
      rw [hzt'] at hi1'
      rw [hz3] at hj1'
      have hd0 : d ≠ 0 := by
        obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, -⟩ := hi
        exact hpar.ne_right
      have hd0' : d' ≠ 0 := by
        obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, -⟩ := hi'
        exact hpar.ne_right
      by_cases hc : crs d d' = 0
      · ---------------------------------------------------------------------------------------- collinear
        have hrotd : 0 < crs d (-d.2, d.1) := by
          have : crs d (-d.2, d.1) = d.1 ^ 2 + d.2 ^ 2 := by unfold crs; ring
          rw [this]; exact v2_sq_pos hd0
        obtain ⟨ε, hε0, hεd⟩ := exists_eps z (mkPt (-d.2) d.1) (lt_min hri (lt_min hri' hrj'))
        have hwi : z + ε • mkPt (-d.2) d.1 ∈ interior (D.tile i).carrier := by
          refine hi1 _ (lt_of_lt_of_le hεd (min_le_left _ _)) ?_
          rw [crs_shift d z ε (-d.2, d.1)]; exact mul_pos hε0 hrotd
        rcases par_or_neg hd0 hd0' hc with hp | hp
        · have hc' : 0 < crs d' (-d.2, d.1) := by
            have e : crs d' (-d.2, d.1) = dt d d' := by unfold crs dt; ring
            rw [e]; exact hp.2
          have hwi' : z + ε • mkPt (-d.2) d.1 ∈ interior (D.tile i').carrier := by
            refine hi1' _ (lt_of_lt_of_le hεd ((min_le_right _ _).trans (min_le_left _ _))) ?_
            rw [crs_shift d' z ε (-d.2, d.1)]; exact mul_pos hε0 hc'
          have hii : i = i' := by
            by_contra hh
            exact Set.disjoint_left.1 (D.interiors_disjoint hh) hwi hwi'
          subst hii
          have := tri_edges_par_eq (D.tile i) hi (triStep_congr_par' hi' hp.symm)
          exact hne ⟨this.1, this.2⟩
        · have hc' : 0 < crs (neg2 d') (-d.2, d.1) := by
            have e : crs (neg2 d') (-d.2, d.1) = dt d (neg2 d') := by unfold crs dt neg2; ring
            rw [e]; exact hp.2
          have hwj' : z + ε • mkPt (-d.2) d.1 ∈ interior (D.tile j').carrier := by
            refine hj1' _ (lt_of_lt_of_le hεd ((min_le_right _ _).trans (min_le_right _ _))) ?_
            rw [crs_shift (neg2 d') z ε (-d.2, d.1)]; exact mul_pos hε0 hc'
          have hij2 : i = j' := by
            by_contra hh
            exact Set.disjoint_left.1 (D.interiors_disjoint hh) hwi hwj'
          subst hij2
          have := tri_edges_par_eq (D.tile i) hi (triStep_congr_par' hj' hp.symm)
          obtain ⟨e1, e2⟩ := this
          -- labels: the tile i has the vertex X with label 0 and the vertex Y' = X with label 1
          have hinj := (D.tile i).indep.injective
          have : kk = kk2p := hinj (by rw [hk, hk2p, e1])
          rw [this] at hl1
          rw [hl1] at hl3p
          exact absurd hl3p (by decide)
      · ---------------------------------------------------------------------------------------- transversal
        obtain ⟨v1, hv11, hv12⟩ := exists_dir hc 1 1
        obtain ⟨v2, hv21, hv22⟩ := exists_dir hc 1 (-1)
        obtain ⟨ε1, hε10, hε1d⟩ := exists_eps z (mkPt v1.1 v1.2) (lt_min hri hri')
        obtain ⟨ε2, hε20, hε2d⟩ := exists_eps z (mkPt v2.1 v2.2) (lt_min hri hrj')
        have w1i : z + ε1 • mkPt v1.1 v1.2 ∈ interior (D.tile i).carrier := by
          refine hi1 _ (lt_of_lt_of_le hε1d (min_le_left _ _)) ?_
          rw [crs_shift d z ε1 v1, hv11]; linarith
        have w1i' : z + ε1 • mkPt v1.1 v1.2 ∈ interior (D.tile i').carrier := by
          refine hi1' _ (lt_of_lt_of_le hε1d (min_le_right _ _)) ?_
          rw [crs_shift d' z ε1 v1, hv12]; linarith
        have w2i : z + ε2 • mkPt v2.1 v2.2 ∈ interior (D.tile i).carrier := by
          refine hi1 _ (lt_of_lt_of_le hε2d (min_le_left _ _)) ?_
          rw [crs_shift d z ε2 v2, hv21]; linarith
        have w2j : z + ε2 • mkPt v2.1 v2.2 ∈ interior (D.tile j').carrier := by
          refine hj1' _ (lt_of_lt_of_le hε2d (min_le_right _ _)) ?_
          have : crs (neg2 d') v2 = -crs d' v2 := by unfold crs neg2; simp only; ring
          rw [crs_shift (neg2 d') z ε2 v2, this, hv22]; linarith
        have e1 : i = i' := by
          by_contra hh
          exact Set.disjoint_left.1 (D.interiors_disjoint hh) w1i w1i'
        have e2 : i = j' := by
          by_contra hh
          exact Set.disjoint_left.1 (D.interiors_disjoint hh) w2i w2j
        exact hij' (e1.symm.trans e2)
    · ------------------------------------------------------------------------------------------- t' = 1: z = Y'
      refine tjunction D.toRegionDissection (k := i') (k0 := fp) hi hj ht0 ht1 ?_
      rw [hfp, hzt.symm]; rw [ht'1']; ext m; simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; ring
  · ----------------------------------------------------------------------------------------------- t' = 0: z = X'
    refine tjunction D.toRegionDissection (k := i') (k0 := kkp) hi hj ht0 ht1 ?_
    rw [hkp, hzt.symm, ← ht'0']; ext m; simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; ring

end Erdos634.Draft.LaczFormal.RG
