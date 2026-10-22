-- Draft/LaczFormalIIcIsoE.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2, Case IIc with alpha = beta: `straight_two_gamma_iso`, `sc2_left_iso`, `sc2_right_iso` = the lemmas of RG12GExcEndT VERBATIM (they use only `G.sum`),
-- with the interface `AngGenI` in place of `AngGen`.  Originals NOT edited.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12GExcEnd
import Erdos634.Draft.LaczFormalIIcIsoD

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

/-- **Two `gamma` corners and a straight tile at one vertex are impossible when `p = r`** (angle sum). -/
theorem straight_two_gamma_iso (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (G : AngGenI (fun l => D.model.angleAt l))
    (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1) {Y : Plane} (hnorm : cnt D idx Y 0 = cnt D idx Y 2) {κ : Type} [Fintype κ]
    (F : ExtFan D.toRegionDissection Y κ) (hemp : IsEmpty κ) {i j : Fin N} (hij : i ≠ j) {a b : Fin 3} (h1 : (D.tile i).pts a = Y) (h2 : idx i a = 2)
    (h3 : (D.tile j).pts b = Y) (h4 : idx j b = 2) {t : Fin N} (ht : t ∈ Strn D.toRegionDissection Y) : False := by
  have h2c : 2 ≤ cnt D idx Y 2 := two_le_cnt hij h1 h2 h3 h4
  have hang := head_angle_sum D idx hidxA F hemp
  rw [Fin.sum_univ_three, hnorm, ← hregc Y, hnorm] at hang
  have hk : 1 ≤ (Strn D.toRegionDissection Y).card := Finset.card_pos.mpr ⟨t, ht⟩
  have hs := G.sum
  have hp := Real.pi_pos
  simp only at hs
  have hkR : (1 : ℝ) ≤ ((Strn D.toRegionDissection Y).card : ℝ) := by exact_mod_cast hk
  have h2R : (2 : ℝ) ≤ (cnt D idx Y 2 : ℝ) := by exact_mod_cast h2c
  nlinarith

set_option maxHeartbeats 6400000 in
/-- **Statement (ii), first case, left run**: the left run ends at `Y` (a left tile ending at `Y` has `gamma` there, no left tile starting at `Y` along `d` has `gamma` at its far end) while `Y` is an inner point of a side
of a right tile: impossible when `p = r` at `Y`. -/
theorem sc2_left_iso [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (G : AngGenI (fun l => D.model.angleAt l)) {Y : Plane} (hnorm : cnt D idx Y 0 = cnt D idx Y 2) {d : V2}
    {iL : Fin N} {A : Plane} (hL : TriStep (D.tile iL) d A Y) (hLg : ∃ k, (D.tile iL).pts k = Y ∧ idx iL k = 2)
    {iR : Fin N} {A' B' : Plane} (hR : TriStep (D.tile iR) (neg2 d) B' A') (hRin : Y ∈ openSegment ℝ A' B')
    (hc : ∀ i U', TriStep (D.tile i) d Y U' → ¬ ∃ k, (D.tile i).pts k = U' ∧ idx i k = 2) : False := by
  classical
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar0, hleft0⟩ := id hL
  have hvert : ∃ i k, (D.tile i).pts k = Y := ⟨iL, f, hf⟩
  obtain ⟨κ, _, ⟨F⟩⟩ := HasFansC.fans (D := D.toRegionDissection) Y hvert
  have hmemA : Y ∈ (D.tile iL).carrier := hf ▸ tile_pt_mem _ f
  set a : AtV D.toRegionDissection Y := ⟨iL, hmemA⟩ with ha
  obtain ⟨kk', fl', hk', hp, hq⟩ := spec_corner_data (F.hspec a) ⟨f, hf⟩
  have hqa : Par (F.q a) (neg2 d) := triStep_end hL kk' fl' hk' hp hq (F.hok a)
  have hca : 0 < crs (F.p a) (F.q a) := crs_pos_of_corner (F.hok a) (F.hspec a) ⟨kk', hk'⟩
  -- the straight tile
  obtain ⟨σ, hσ0, hσ1, hYσ⟩ := openSegment_param (by rw [openSegment_symm]; exact hRin : Y ∈ openSegment ℝ B' A')
  obtain ⟨hmemS, hnvS, hlineS⟩ := step_interior_pt hR hσ0 hσ1
  rw [← hYσ] at hmemS hnvS hlineS
  set s : AtV D.toRegionDissection Y := ⟨iR, hmemS⟩ with hs
  obtain ⟨hps, hqs⟩ := straight_dir s (F.hok s) (F.hloc s) (F.hspec s) hnvS hR hlineS
  have hqs' : Par (F.q s) d := by
    rw [hqs]
    have := par_neg hps
    rwa [neg2_neg2] at this
  obtain ⟨b, hcb, hpb⟩ := F.ray_left a s hca hqa hqs'
  obtain ⟨hemp, hint, hasn, hbsn, habn, -⟩ := F.head_cyc a b s hca hqa hcb hpb hps hqs
  have hbvert := vertex_of_crs_pos (F.hspec b) hcb
  obtain ⟨kb, flb, hkb, hpb', hqb'⟩ := spec_corner_data (F.hspec b) hbvert
  have hSb : TriStep (D.tile b.1) d Y ((D.tile b.1).pts (armP kb flb)) := triStep_of_start kb flb hkb hpb' hqb' hcb hpb
  have hfar : ¬ idx b.1 (armP kb flb) = 2 := fun h => hc _ _ hSb ⟨_, rfl, h⟩
  have hStrn : iR ∈ Strn D.toRegionDissection Y := by
    simp only [Strn, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hmemS, hnvS⟩
  by_cases hlb : idx b.1 kb = 2
  · obtain ⟨kL, hkL, hkL2⟩ := hLg
    exact straight_two_gamma_iso D idx hC.hidxA G hC.hregc hnorm F hemp (fun h => habn (Subtype.ext h)) hkL hkL2 hkb hlb hStrn
  · have hdist : dist Y ((D.tile b.1).pts (armP kb flb)) = slen D 2 := by
      have := step_dist_c D idx hC.hidx (armP_ne kb flb).symm hlb hfar
      rwa [hkb] at this
    obtain ⟨hm, hmi⟩ := interior_openSeg D P hreg hint (tile_sub_region D.toRegionDissection b.1 (tile_pt_mem _ (armP kb flb)))
    have hm' : ((1 / 2 : ℝ) • ((D.tile b.1).pts (armP kb flb)) + (1 / 2 : ℝ) • Y) ∈ openSegment ℝ Y ((D.tile b.1).pts (armP kb flb)) := by
      rw [openSegment_symm]; exact hm
    obtain ⟨j, -, hSj, -⟩ := pair_partner D P hreg idx hC hab hac hSb hdist hm' hmi
    obtain ⟨x, hxj, hxq⟩ := sec_end F hSj
    rw [neg2_neg2'] at hxq
    have hxs : x = s := by
      by_contra hne
      have hdis := tiles_disjoint D.toRegionDissection Y F.p F.q F.hloc
      exact end_inj' F.p F.q F.hok hdis (Ne.symm hne) (hxq.trans hqs'.symm)
    obtain ⟨kk2, f2, g2, hk2, hf2, -⟩ := id hSj
    have hjR : j = iR := by rw [← hxj, hxs]
    exact hnvS f2 (by rw [← hjR]; exact hf2)

set_option maxHeartbeats 6400000 in
/-- **Statement (ii), first case, right run** (mirror of `sc2_left_iso`). -/
theorem sc2_right_iso [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (G : AngGenI (fun l => D.model.angleAt l)) {Y : Plane} (hnorm : cnt D idx Y 0 = cnt D idx Y 2) {d : V2}
    {iR : Fin N} {A : Plane} (hR : TriStep (D.tile iR) (neg2 d) Y A) (hRg : ∃ k, (D.tile iR).pts k = Y ∧ idx iR k = 2)
    {iL : Fin N} {A' B' : Plane} (hL : TriStep (D.tile iL) d A' B') (hLin : Y ∈ openSegment ℝ A' B')
    (hc : ∀ i U', TriStep (D.tile i) (neg2 d) U' Y → ¬ ∃ k, (D.tile i).pts k = U' ∧ idx i k = 2) : False := by
  classical
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar0, hleft0⟩ := id hR
  have hvert : ∃ i k, (D.tile i).pts k = Y := ⟨iR, kk, hk⟩
  obtain ⟨κ, _, ⟨F⟩⟩ := HasFansC.fans (D := D.toRegionDissection) Y hvert
  have hmemA : Y ∈ (D.tile iR).carrier := hk ▸ tile_pt_mem _ kk
  set a : AtV D.toRegionDissection Y := ⟨iR, hmemA⟩ with ha
  obtain ⟨kk', fl', hk', hp, hq⟩ := spec_corner_data (F.hspec a) ⟨kk, hk⟩
  have hpa : Par (F.p a) (neg2 d) := triStep_start hR kk' fl' hk' hp hq (F.hok a)
  have hca : 0 < crs (F.p a) (F.q a) := crs_pos_of_corner (F.hok a) (F.hspec a) ⟨kk', hk'⟩
  -- the straight tile
  obtain ⟨σ, hσ0, hσ1, hYσ⟩ := openSegment_param hLin
  obtain ⟨hmemS, hnvS, hlineS⟩ := step_interior_pt hL hσ0 hσ1
  rw [← hYσ] at hmemS hnvS hlineS
  set s : AtV D.toRegionDissection Y := ⟨iL, hmemS⟩ with hs
  obtain ⟨hps, hqs⟩ := straight_dir s (F.hok s) (F.hloc s) (F.hspec s) hnvS hL hlineS
  obtain ⟨c, hcc, hqc⟩ := F.ray_right a s hca hpa hps
  have hqc' : Par (F.q c) (neg2 (neg2 d)) := by rw [neg2_neg2']; exact hqc
  have hps' : Par (F.p s) (neg2 (neg2 d)) := by rw [neg2_neg2']; exact hps
  obtain ⟨hemp, hint, hasn, hbsn, hcan, -⟩ := F.head_cyc (d := neg2 d) c a s hcc hqc' hca hpa hps' hqs
  have hcvert := vertex_of_crs_pos (F.hspec c) hcc
  obtain ⟨kc, flc, hkc, hpc', hqc''⟩ := spec_corner_data (F.hspec c) hcvert
  have hSc : TriStep (D.tile c.1) (neg2 d) ((D.tile c.1).pts (armQ kc flc)) Y := triStep_of_end kc flc hkc hpc' hqc'' hcc hqc
  have hfar : ¬ idx c.1 (armQ kc flc) = 2 := fun h => hc _ _ hSc ⟨_, rfl, h⟩
  have hStrn : iL ∈ Strn D.toRegionDissection Y := by
    simp only [Strn, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hmemS, hnvS⟩
  by_cases hlc : idx c.1 kc = 2
  · obtain ⟨kR, hkR, hkR2⟩ := hRg
    exact straight_two_gamma_iso D idx hC.hidxA G hC.hregc hnorm F hemp (fun h => hcan (Subtype.ext h.symm)) hkR hkR2 hkc hlc hStrn
  · have hdist : dist ((D.tile c.1).pts (armQ kc flc)) Y = slen D 2 := by
      have := step_dist_c D idx hC.hidx (armQ_ne kc flc).symm hlc hfar
      rw [hkc] at this
      rwa [dist_comm]
    obtain ⟨hm, hmi⟩ := interior_openSeg D P hreg hint (tile_sub_region D.toRegionDissection c.1 (tile_pt_mem _ (armQ kc flc)))
    obtain ⟨j, -, hSj, -⟩ := pair_partner D P hreg idx hC hab hac hSc hdist hm hmi
    rw [neg2_neg2'] at hSj
    obtain ⟨x, hxj, hxp⟩ := sec_start F hSj
    have hxs : x = s := by
      by_contra hne
      have hdis := tiles_disjoint D.toRegionDissection Y F.p F.q F.hloc
      exact start_inj F.p F.q F.hok hdis (Ne.symm hne) (hxp.trans hps.symm)
    obtain ⟨kk2, f2, g2, hk2, hf2, -⟩ := id hSj
    have hjL : j = iL := by rw [← hxj, hxs]
    exact hnvS kk2 (by rw [← hjL]; exact hk2)

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.straight_two_gamma_iso
#print axioms Erdos634.Draft.LaczFormal.RG.sc2_left_iso
#print axioms Erdos634.Draft.LaczFormal.RG.sc2_right_iso
