-- Draft/LaczFormalGraphSide.lean -- D0 (part 3): the fan at a vertex ON A SIDE of the target (not a corner).
-- The tiles through `V` fill the half-plane of the target; adding the EXTERIOR half-plane as one virtual straight sector `none`
-- (clockwise ray `-pT`, counterclockwise ray `pT`, where the target is locally `{cross pT z >= 0}`), the family is again a covering,
-- disjoint family of admissible sectors with widths adding up to `2 pi`, so `fan_cycle` lists it cyclically; removing `none` gives the
-- linear fan `h_0 .. h_n` of Laczkovich's Lemma 4.5 proof (the rays `h_0`, `h_n` lie on the side of the polygon).  UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Sect. 4); Beeson (1206.2229, vertex figures at boundary points).
import Erdos634.Draft.LaczFormalGraphLocal

namespace Erdos634.Draft.LaczFormal.Graph

open Erdos634.Geometry

variable {N : ℕ}

/-- A point with exactly one vanishing barycentric coordinate is not a vertex. -/
theorem edge_coords_not_vertex (T : Tri) (m : Fin 3) (V : Plane) (h0 : T.basis.coord m V = 0)
    (hpos : ∀ j, j ≠ m → 0 < T.basis.coord j V) : ∀ k, T.pts k ≠ V := by
  intro k hk
  have h1 : T.basis.coord (k + 1) V = 0 := by rw [← hk]; exact T.basis.coord_apply_ne (fin3_ne_one k)
  have h2 : T.basis.coord (k + 2) V = 0 := by rw [← hk]; exact T.basis.coord_apply_ne (fin3_ne_two k)
  by_cases hm1 : k + 1 = m
  · have hm2 : k + 2 ≠ m := fun h => fin3_add_ne k (hm1.trans h.symm)
    exact absurd h2 (hpos _ hm2).ne'
  · exact absurd h1 (hpos _ hm1).ne'

theorem secOK_ext {a : V2} (ha : a ≠ 0) : SecOK (-a.1, -a.2) a := by
  have hp : ((-a.1, -a.2) : V2) ≠ 0 := by
    intro h; apply ha
    have h1 : -a.1 = 0 := congrArg Prod.fst h
    have h2 : -a.2 = 0 := congrArg Prod.snd h
    exact Prod.ext (show a.1 = 0 by linarith) (show a.2 = 0 by linarith)
  right
  have h1 := crs_straight (-a.1, -a.2)
  have h2 := dt_straight_neg hp
  simp only [neg_neg] at h1 h2
  exact ⟨h1, h2⟩

/-- Sector generators of the family with the exterior half-plane adjoined (`none`). -/
def extP (pT : V2) (p : AtV D V → V2) : Option (AtV D V) → V2
  | none => (-pT.1, -pT.2)
  | some s => p s

def extQ (pT : V2) (q : AtV D V → V2) : Option (AtV D V) → V2
  | none => pT
  | some s => q s

/-- **D0, vertex on a side of the target.**  `V` lies in the relative interior of the target side opposite vertex `m` and is a vertex of
the tiling.  Then the tiles through `V` together with the exterior half-plane form a cyclic fan. -/
theorem vertex_fan_side (D : Dissection N) (V : Plane) (m : Fin 3) (h0 : D.target.basis.coord m V = 0)
    (hpos : ∀ j, j ≠ m → 0 < D.target.basis.coord j V) (hvert : ∃ i k, (D.tile i).pts k = V) :
    ∃ (pT : V2) (p q : AtV D V → V2) (e : ℕ → Option (AtV D V)),
      pT ≠ 0 ∧ LocalCone D.target V pT (-pT.1, -pT.2) ∧
      (∀ s, SecOK (p s) (q s)) ∧ (∀ s, LocalCone (D.tile s.1) V (p s) (q s)) ∧
      (∀ s, wd (p s) (q s) = (D.tile s.1).localAngle V) ∧ (∀ s, SectorSpec (D.tile s.1) V (p s) (q s)) ∧
      (∀ n, Par (extP pT p (e (n + 1))) (extQ pT q (e n))) ∧
      (∀ n, e (n + Fintype.card (Option (AtV D V))) = e n) ∧
      Set.InjOn e (Set.Iio (Fintype.card (Option (AtV D V)))) ∧
      (∀ o, ∃ j < Fintype.card (Option (AtV D V)), e j = o) := by
  classical
  obtain ⟨pT, qT, hokT, hlocT, hwdT, hspecT⟩ := straight_sector D.target m V h0 hpos
  have hqT : qT = (-pT.1, -pT.2) := by
    rcases hspecT with ⟨k, hk, _⟩ | ⟨_, m', _, _, hq, _⟩
    · exact absurd hk (edge_coords_not_vertex D.target m V h0 hpos k)
    · exact hq
  subst hqT
  have hpT : pT ≠ 0 := hokT.ne_p
  have hex : ∀ s : AtV D V, ∃ pq : V2 × V2, SecOK pq.1 pq.2 ∧ LocalCone (D.tile s.1) V pq.1 pq.2 ∧
      wd pq.1 pq.2 = (D.tile s.1).localAngle V ∧ SectorSpec (D.tile s.1) V pq.1 pq.2 := by
    intro s
    obtain ⟨p, q, h1, h2, h3, h4⟩ := local_sector (D.tile s.1) s.2 (not_interior_of_vertex D hvert s.1)
    exact ⟨(p, q), h1, h2, h3, h4⟩
  choose pq hok hloc hwd hspec using hex
  set p : AtV D V → V2 := fun s => (pq s).1
  set q : AtV D V → V2 := fun s => (pq s).2
  obtain ⟨i0, k0, hk0⟩ := hvert
  haveI : Nonempty (AtV D V) := ⟨⟨i0, hk0 ▸ subset_convexHull ℝ _ ⟨k0, rfl⟩⟩⟩
  obtain ⟨R, hR, hRT⟩ := hlocT
  -- target cone and scaling
  have hcover_tiles : ∀ z, inCone pT (-pT.1, -pT.2) z → ∃ s, inCone (p s) (q s) z := by
    intro z hz
    exact tiles_cover D V p q hloc {z | inCone pT (-pT.1, -pT.2) z} R hR
      (fun y hy => by simpa using hRT y hy)
      (fun z hz t ht => (inCone_smul_iff ht).mpr hz) z hz
  have hcrsT : ∀ z, inCone pT (-pT.1, -pT.2) z ↔ 0 ≤ crs pT z := fun z => inCone_straight_iff pT z
  have hok' : AllOK (extP pT p) (extQ pT q) := by
    intro o
    rcases o with _ | s
    · exact secOK_ext hpT
    · exact hok s
  have hcov : Covers (extP pT p) (extQ pT q) := by
    intro z
    by_cases hz : 0 ≤ crs pT z
    · obtain ⟨s, hs⟩ := hcover_tiles z ((hcrsT z).mpr hz)
      exact ⟨some s, hs⟩
    · push_neg at hz
      refine ⟨none, ?_, ?_⟩
      · show 0 ≤ crs (-pT.1, -pT.2) z; unfold crs at hz ⊢; nlinarith
      · show 0 ≤ crs z pT; unfold crs at hz ⊢; nlinarith
  have hext : ∀ (t : AtV D V) (z : V2), inInt (-pT.1, -pT.2) pT z → inInt (p t) (q t) z → False := by
    intro t z hz1 hz2
    have hneg : crs pT z < 0 := by
      have := hz1.1; unfold crs at this ⊢; try dsimp only at this; nlinarith
    obtain ⟨rt, hrt, ht⟩ := hloc t
    obtain ⟨ε, hε, hd⟩ := exists_ptOf_small V z (lt_min hrt hR)
    have hds : dist (ptOf V z ε) V < rt := lt_of_lt_of_le hd (min_le_left _ _)
    have hdR : dist (ptOf V z ε) V < R := lt_of_lt_of_le hd (min_le_right _ _)
    have hz2' := hz2
    rw [← inInt_smul_iff hε, ← toV2_ptOf V z ε] at hz2'
    have h1 := mem_interior_of_inInt ht hds hz2'
    have h2 : ptOf V z ε ∈ D.target.carrier := by
      rw [← D.covers]
      exact Set.mem_iUnion.mpr ⟨t.1, interior_subset h1⟩
    have h3 := (hRT _ hdR).mp h2
    rw [toV2_ptOf, inCone_straight_iff] at h3
    unfold crs at h3 hneg
    try dsimp only at h3 hneg
    nlinarith
  have hdisj : Disjoint' (extP pT p) (extQ pT q) := by
    intro o1 o2 hne z ⟨hz1, hz2⟩
    rcases o1 with _ | s <;> rcases o2 with _ | t
    · exact hne rfl
    · exact hext t z hz1 hz2
    · exact hext s z hz2 hz1
    · exact tiles_disjoint D V p q hloc s t (fun h => hne (by rw [h])) z ⟨hz1, hz2⟩
  have hsum : ∑ o, wd (extP pT p o) (extQ pT q o) = 2 * Real.pi := by
    rw [Fintype.sum_option]
    have e1 : wd (extP pT p none) (extQ pT q none) = Real.pi := wd_ext hpT
    rw [e1]
    have e2 : ∑ s : AtV D V, wd (extP pT p (some s)) (extQ pT q (some s)) = ∑ s : AtV D V, wd (p s) (q s) := rfl
    rw [e2, tiles_angle_sum D V p q hwd, D.sum_localAngle_eq V, localAngle_of_edge_coords D.target m V h0 hpos]
    ring
  haveI : Nonempty (Option (AtV D V)) := ⟨none⟩
  obtain ⟨e, h1, h2, h3, h4⟩ := fan_cycle (extP pT p) (extQ pT q) hok' hcov hdisj hsum
  exact ⟨pT, p, q, e, hpT, ⟨R, hR, hRT⟩, hok, hloc, hwd, hspec, h1, h2, h3, h4⟩

end Erdos634.Draft.LaczFormal.Graph
