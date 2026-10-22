-- Draft/LaczFormalIIcIsoF.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2-6.3, Case IIc with alpha = beta: at an interior (2,2,2) vertex of the isosceles model there is ALWAYS a straight line of tile sides.
--  `window_one_gamma`        : a cyclic word of six sectors with each label twice has a window of three consecutive sectors containing the label 2 exactly once (c(j) + c(j+3) = 2, steps of size <= 1).
--  `straightAt_of_222_iso`   : hence (`straight_of_run_iso`) an interior vertex with cnt = (2,2,2) satisfies `StraightAt D Y` (the Fig. 5 (A) shape: tiles flanking a ray -d, and a tile starting along d).
--  `kiteB_empty_iso`         : so `kiteB D idx = empty` for alpha = beta (a kiteB vertex is a Gamma_kite vertex = interior (2,2,2) vertex with NO straight line).  This replaces Lemma 6.2 in the isosceles case.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcIsoE
import Erdos634.Draft.LaczFormalRG12GExcMatch

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

/-- **A window with exactly one gamma.** -/
theorem window_one_gamma {ℓ : ℕ → Fin 3} (hcnt : ∀ j l, ((Finset.range 6).filter (fun i => ℓ (j + i) = l)).card = 2) :
    ∃ j, ((Finset.range 3).filter (fun i => ℓ (j + i) = 2)).card = 1 := by
  classical
  by_contra hno
  push Not at hno
  set g : ℕ → ℕ := fun i => if ℓ i = 2 then 1 else 0 with hg
  have g1 : ∀ i, g i ≤ 1 := fun i => by simp only [hg]; split_ifs <;> omega
  have w3 : ∀ j, ((Finset.range 3).filter (fun i => ℓ (j + i) = 2)).card = g j + g (j + 1) + g (j + 2) := by
    intro j
    simp only [Finset.card_filter, Finset.sum_range_succ, Finset.sum_range_zero, hg, add_zero, zero_add]
  have w6 : ∀ j, ((Finset.range 6).filter (fun i => ℓ (j + i) = 2)).card =
      g j + g (j + 1) + g (j + 2) + g (j + 3) + g (j + 4) + g (j + 5) := by
    intro j
    simp only [Finset.card_filter, Finset.sum_range_succ, Finset.sum_range_zero, hg, add_zero, zero_add]
  have h0 := hno 0
  have h1 := hno 1
  have h2 := hno 2
  have h3 := hno 3
  have h4 := hno 4
  have h5 := hno 5
  rw [w3] at h0 h1 h2 h3 h4 h5
  have s0 := hcnt 0 2
  have s1 := hcnt 1 2
  have s2 := hcnt 2 2
  rw [w6] at s0 s1 s2
  have := g1 0
  have := g1 1
  have := g1 2
  have := g1 3
  have := g1 4
  have := g1 5
  have := g1 6
  have := g1 7
  simp only [Nat.reduceAdd, Nat.zero_add] at *
  omega

set_option maxHeartbeats 6400000 in
/-- **Isosceles model: an interior (2,2,2) vertex carries a straight line of tile sides.** -/
theorem straightAt_of_222_iso (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) {Y : Plane} (hint : Y ∈ interior D.region)
    (h0 : cnt D idx Y 0 = 2) (h1 : cnt D idx Y 1 = 2) (h2 : cnt D idx Y 2 = 2) (G : AngGenI (fun l => D.model.angleAt l)) :
    StraightAt D Y := by
  classical
  obtain ⟨F, s, ℓ, hF, hlab, hsurj, hperS⟩ := fan222_tile_iso D idx hidxA hint h0 h1 h2 G
  obtain ⟨pf, qf, kk, fl, S⟩ := secData_exists D idx F s ℓ hlab
  obtain ⟨j, hj⟩ := window_one_gamma hF.hcnt
  have hopp : Par (F.p (s (j + 3))) (-(F.p (s j)).1, -(F.p (s j)).2) :=
    straight_of_run_iso G.toAngGen' G.eq01 hF j hj
  have hp0 : ∀ m, F.p (s m) ≠ 0 := fun m => (F.hok (s m)).ne_p
  have hq0 : ∀ m, F.q (s m) ≠ 0 := fun m => (F.hok (s m)).ne_q
  set r := F.p (s j) with hr
  -- the sector before `s j` ends along `r`
  have hq5 : Par (F.q (s (j + 5))) r := by
    have h6 : s (j + 5 + 1) = s j := hperS j
    have := (hF.hpar (j + 5)).symm
    simp only at this
    rw [h6] at this
    exact this
  have hSi : TriStep (D.tile (s (j + 5)).1) (neg2 r) ((D.tile (s (j + 5)).1).pts (armQ (kk (j + 5)) (fl (j + 5)))) Y := by
    have := triStep_of_end (kk (j + 5)) (fl (j + 5)) (S.hk (j + 5)) (S.hp (j + 5)) (S.hq (j + 5)) (S.crs_pos (j + 5)) hq5
    exact this
  have hSj : TriStep (D.tile (s j).1) (neg2 (neg2 r)) Y ((D.tile (s j).1).pts (armP (kk j) (fl j))) := by
    rw [neg2_neg2']
    exact triStep_of_start (kk j) (fl j) (S.hk j) (S.hp j) (S.hq j) (S.crs_pos j) (par_refl (hp0 j))
  have hSk : TriStep (D.tile (s (j + 3)).1) (neg2 r) Y ((D.tile (s (j + 3)).1).pts (armP (kk (j + 3)) (fl (j + 3)))) :=
    triStep_of_start (kk (j + 3)) (fl (j + 3)) (S.hk (j + 3)) (S.hp (j + 3)) (S.hq (j + 3)) (S.crs_pos (j + 3)) hopp
  exact ⟨neg2 r, _, _, _, _, _, _, hSi, hSj, hSk⟩

set_option maxHeartbeats 6400000 in
/-- **For alpha = beta no vertex of Gamma_kite is of type (B): `kiteB = empty`** (replaces Lemma 6.2 in the isosceles case). -/
theorem kiteB_empty_iso [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3)
    (G : AngGenI (fun l => D.model.angleAt l)) : kiteB D idx = ∅ := by
  classical
  apply Finset.eq_empty_of_forall_notMem
  intro Y hY
  simp only [kiteB, Finset.mem_filter] at hY
  obtain ⟨-, ⟨Z, hYZ⟩, hnS⟩ := hY
  obtain ⟨-, ⟨hint, c0, c1, c2⟩⟩ := gkite_vertex_type D P hreg idx hC.hidxA hC.hregc h1 h3 hYZ
  exact hnS (straightAt_of_222_iso D idx hC.hidxA hint c0 c1 c2 G)

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.window_one_gamma
#print axioms Erdos634.Draft.LaczFormal.RG.straightAt_of_222_iso
#print axioms Erdos634.Draft.LaczFormal.RG.kiteB_empty_iso
