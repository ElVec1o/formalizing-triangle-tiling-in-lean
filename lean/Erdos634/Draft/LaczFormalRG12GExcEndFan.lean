-- Draft/LaczFormalRG12GExcEndFan.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2, Gamma_except, lemma L7 (statement (ii)), STEP 2: the fan at an interior (2,2,2) vertex.
-- (a) `SecData`: per-sector corner data (corner index, flip, labels of the corner and of the two far ends) of a fan in which every tile has `Y` as a corner (`secData_exists`).
-- (b) `fan_match` (Lemma 4.8 in fan form): the `q`-side of the sector `s_n` has length `c` iff the `p`-side of the sector `s_{n+1}` has length `c` (both sectors flank one ray; `pair_partner`).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 4, 6.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12GExcEndSplit

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

/-- Per-sector corner data of a fan at `Y` whose sectors are all corners. -/
structure SecData (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {Y : Plane} (F : ExtFan D.toRegionDissection Y Empty)
    (s : ℕ → AtV D.toRegionDissection Y) (ℓ pf qf : ℕ → Fin 3) (kk : ℕ → Fin 3) (fl : ℕ → Bool) : Prop where
  hk : ∀ n, (D.tile (s n).1).pts (kk n) = Y
  hp : ∀ n, F.p (s n) = toV2 ((D.tile (s n).1).pts (armP (kk n) (fl n)) - Y)
  hq : ∀ n, F.q (s n) = toV2 ((D.tile (s n).1).pts (armQ (kk n) (fl n)) - Y)
  hl : ∀ n, idx (s n).1 (kk n) = ℓ n
  hpf : ∀ n, idx (s n).1 (armP (kk n) (fl n)) = pf n
  hqf : ∀ n, idx (s n).1 (armQ (kk n) (fl n)) = qf n

theorem secData_exists (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {Y : Plane} (F : ExtFan D.toRegionDissection Y Empty)
    (s : ℕ → AtV D.toRegionDissection Y) (ℓ : ℕ → Fin 3) (hlab : ∀ j, ∃ k, (D.tile (s j).1).pts k = Y ∧ idx (s j).1 k = ℓ j) :
    ∃ (pf qf : ℕ → Fin 3) (kk : ℕ → Fin 3) (fl : ℕ → Bool), SecData D idx F s ℓ pf qf kk fl := by
  have h : ∀ n, ∃ (kk : Fin 3) (fl : Bool), (D.tile (s n).1).pts kk = Y ∧ F.p (s n) = toV2 ((D.tile (s n).1).pts (armP kk fl) - Y) ∧
      F.q (s n) = toV2 ((D.tile (s n).1).pts (armQ kk fl) - Y) ∧ idx (s n).1 kk = ℓ n := by
    intro n
    obtain ⟨k, hk, hl⟩ := hlab n
    obtain ⟨kk, fl, hkk, hp, hq⟩ := spec_corner_data (F.hspec (s n)) ⟨k, hk⟩
    have : kk = k := (D.tile (s n).1).indep.injective (hkk.trans hk.symm)
    exact ⟨kk, fl, hkk, hp, hq, by rw [this]; exact hl⟩
  choose kk fl hk hp hq hl using h
  exact ⟨fun n => idx (s n).1 (armP (kk n) (fl n)), fun n => idx (s n).1 (armQ (kk n) (fl n)), kk, fl, ⟨hk, hp, hq, hl, fun n => rfl, fun n => rfl⟩⟩

theorem SecData.perm {D : CongruentRegionDissection N} {idx : Fin N → Equiv.Perm (Fin 3)} {Y : Plane} {F : ExtFan D.toRegionDissection Y Empty}
    {s : ℕ → AtV D.toRegionDissection Y} {ℓ pf qf : ℕ → Fin 3} {kk : ℕ → Fin 3} {fl : ℕ → Bool} (S : SecData D idx F s ℓ pf qf kk fl) (n : ℕ) :
    ℓ n ≠ pf n ∧ ℓ n ≠ qf n ∧ pf n ≠ qf n := by
  rw [← S.hl n, ← S.hpf n, ← S.hqf n]
  refine ⟨fun h => armP_ne (kk n) (fl n) ((idx (s n).1).injective h).symm, fun h => armQ_ne (kk n) (fl n) ((idx (s n).1).injective h).symm,
    fun h => armPQ_ne (kk n) (fl n) ((idx (s n).1).injective h)⟩

theorem SecData.crs_pos {D : CongruentRegionDissection N} {idx : Fin N → Equiv.Perm (Fin 3)} {Y : Plane} {F : ExtFan D.toRegionDissection Y Empty}
    {s : ℕ → AtV D.toRegionDissection Y} {ℓ pf qf : ℕ → Fin 3} {kk : ℕ → Fin 3} {fl : ℕ → Bool} (S : SecData D idx F s ℓ pf qf kk fl) (n : ℕ) :
    0 < crs (F.p (s n)) (F.q (s n)) :=
  crs_pos_of_corner (F.hok (s n)) (F.hspec (s n)) ⟨kk n, S.hk n⟩

/-- The unique sector ending along a ray. -/
theorem prev_sector {D : RegionDissection N} {V : Plane} {κ : Type} [Fintype κ] (F : ExtFan D V κ) (s : ℕ → AtV D V) {j : ℕ} {y : AtV D V} {r : V2}
    (hq : Par (F.q (s j)) r) (hy : Par (F.q y) r) : y = s j := by
  by_contra hne
  have hdis := tiles_disjoint D V F.p F.q F.hloc
  exact end_inj' F.p F.q F.hok hdis (Ne.symm hne) (hy.trans hq.symm)

theorem interior_openSeg {M : ℕ} [NeZero M] (D : CongruentRegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier) {Y U : Plane}
    (hYi : Y ∈ interior D.region) (hU : U ∈ D.region) : ((1 / 2 : ℝ) • U + (1 / 2 : ℝ) • Y) ∈ openSegment ℝ U Y ∧
      ((1 / 2 : ℝ) • U + (1 / 2 : ℝ) • Y) ∈ interior D.region := by
  have hconv : Convex ℝ D.region := hreg ▸ convPoly_convex P
  have hseg : openSegment ℝ Y U ⊆ interior D.region := hconv.openSegment_interior_self_subset_interior hYi hU
  have hm : ((1 / 2 : ℝ) • U + (1 / 2 : ℝ) • Y) ∈ openSegment ℝ U Y := ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  refine ⟨hm, hseg ?_⟩
  rw [openSegment_symm]; exact hm

/-- **Lemma 4.8 in fan form**: at an interior vertex whose sectors are all corners, the `q`-side of `s_n` has length `c` iff the `p`-side of `s_{n+1}` does. -/
theorem fan_match [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2)) {Y : Plane}
    (hYi : Y ∈ interior D.region) (F : ExtFan D.toRegionDissection Y Empty) (s : ℕ → AtV D.toRegionDissection Y)
    (hpar : ∀ j, Par (F.p (s (j + 1))) (F.q (s j))) {ℓ pf qf : ℕ → Fin 3} {kk : ℕ → Fin 3} {fl : ℕ → Bool} (S : SecData D idx F s ℓ pf qf kk fl) (n : ℕ) :
    (ℓ n ≠ 2 ∧ qf n ≠ 2) ↔ (ℓ (n + 1) ≠ 2 ∧ pf (n + 1) ≠ 2) := by
  classical
  have hq0 : ∀ m, F.q (s m) ≠ 0 := fun m => (F.hok (s m)).ne_q
  have hp0 : ∀ m, F.p (s m) ≠ 0 := fun m => (F.hok (s m)).ne_p
  constructor
  · rintro ⟨hl, hqn⟩
    set T := D.tile (s n).1 with hT
    have hdist : dist ((T).pts (armQ (kk n) (fl n))) Y = slen D 2 := by
      rw [dist_comm, ← S.hk n]
      exact step_dist_c D idx hC.hidx (armQ_ne (kk n) (fl n)).symm (by rw [S.hl n]; exact hl) (by rw [S.hqf n]; exact hqn)
    have hS : TriStep T (neg2 (F.q (s n))) (T.pts (armQ (kk n) (fl n))) Y :=
      triStep_of_end (kk n) (fl n) (S.hk n) (S.hp n) (S.hq n) (S.crs_pos n) (par_refl (hq0 n))
    obtain ⟨hm, hmi⟩ := interior_openSeg D P hreg hYi (tile_sub_region D.toRegionDissection (s n).1 (tile_pt_mem T (armQ (kk n) (fl n))))
    obtain ⟨j, -, hSj, -⟩ := pair_partner D P hreg idx hC hab hac hS hdist hm hmi
    rw [neg2_neg2'] at hSj
    obtain ⟨x, hxj, hxp⟩ := sec_start F hSj
    have hx : x = s (n + 1) := next_sector F s hpar (j := n) (r := F.q (s n)) (par_refl (hq0 n)) hxp
    subst hxj
    rw [hx] at hSj
    obtain ⟨f, hf, hfe⟩ := arm_start_eq hSj (kk (n + 1)) (fl (n + 1)) (S.hk (n + 1)) (S.hp (n + 1)) (S.hq (n + 1)) (F.hok (s (n + 1)))
    by_contra hcon
    have hg : idx (s (n + 1)).1 (kk (n + 1)) = 2 ∨ idx (s (n + 1)).1 (armP (kk (n + 1)) (fl (n + 1))) = 2 := by
      rw [S.hl, S.hpf]
      by_contra hh
      push Not at hh
      exact hcon ⟨hh.1, hh.2⟩
    have hne := step_dist_ne_c D idx hC (armP_ne (kk (n + 1)) (fl (n + 1))).symm hg
    apply hne
    rw [S.hk (n + 1), ← hfe, hf, dist_comm]
    exact hdist
  · rintro ⟨hl, hpn⟩
    set T := D.tile (s (n + 1)).1 with hT
    have hdist : dist Y (T.pts (armP (kk (n + 1)) (fl (n + 1)))) = slen D 2 := by
      rw [← S.hk (n + 1)]
      exact step_dist_c D idx hC.hidx (armP_ne (kk (n + 1)) (fl (n + 1))).symm (by rw [S.hl]; exact hl) (by rw [S.hpf]; exact hpn)
    have hS : TriStep T (F.p (s (n + 1))) Y (T.pts (armP (kk (n + 1)) (fl (n + 1)))) :=
      triStep_of_start (kk (n + 1)) (fl (n + 1)) (S.hk (n + 1)) (S.hp (n + 1)) (S.hq (n + 1)) (S.crs_pos (n + 1)) (par_refl (hp0 (n + 1)))
    obtain ⟨hm, hmi⟩ := interior_openSeg D P hreg hYi (tile_sub_region D.toRegionDissection (s (n + 1)).1 (tile_pt_mem T (armP (kk (n + 1)) (fl (n + 1)))))
    have hm' : ((1 / 2 : ℝ) • (T.pts (armP (kk (n + 1)) (fl (n + 1)))) + (1 / 2 : ℝ) • Y) ∈ openSegment ℝ Y (T.pts (armP (kk (n + 1)) (fl (n + 1)))) := by
      rw [openSegment_symm]; exact hm
    obtain ⟨j, -, hSj, -⟩ := pair_partner D P hreg idx hC hab hac hS hdist hm' hmi
    obtain ⟨x, hxj, hxq⟩ := sec_end F hSj
    rw [neg2_neg2'] at hxq
    have hx : x = s n := prev_sector F s (j := n) (r := F.p (s (n + 1))) (hpar n).symm (hxq)
    subst hxj
    rw [hx] at hSj
    obtain ⟨k0, hk0, hk0e⟩ := arm_end_eq hSj (kk n) (fl n) (S.hk n) (S.hp n) (S.hq n) (F.hok (s n))
    by_contra hcon
    have hg : idx (s n).1 (kk n) = 2 ∨ idx (s n).1 (armQ (kk n) (fl n)) = 2 := by
      rw [S.hl, S.hqf]
      by_contra hh
      push Not at hh
      exact hcon ⟨hh.1, hh.2⟩
    have hne := step_dist_ne_c D idx hC (armQ_ne (kk n) (fl n)).symm hg
    apply hne
    rw [S.hk n, ← hk0e, hk0]
    exact hdist

end Erdos634.Draft.LaczFormal.RG
