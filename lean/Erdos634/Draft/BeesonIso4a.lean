import Erdos634.Draft.BeesonIso3j
import Erdos634.Draft.LaczFormalBZL7h11

/-!
# Beeson, "Tilings of an isosceles triangle" (arXiv 1206.1974 v7), Sect. 11: tools for Lemma 11.10 (corner tiles, ray bound, sides by labels)

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.1974 v7, Lemmas 11.9, 11.10; arXiv 1206.2229), Laczkovich (DCG 48 (2012), Sect. 4), Beeson-Zhang, Herdt, Zhang.
Formalization debt, not progress on the /goal outcomes.

* `tile_dist_third`: the side of a tile between two vertices has the length `slen` of the label of the third vertex.
* `corner_tile_vertices`: at a polygon vertex of angle `alpha` the outgoing and the incoming side steps belong to ONE tile `T`, of label `alpha` there, whose three vertices are the corner and the two
  step ends (the third vertex lies ON the other side).  (Extracted from the proof of `corner_not_both_c`.)
* `ray_bound`: a point `Z` on the ray from `Q` through `R` (`R` on the line of side `j`, `Q` strictly inside) of the polygon satisfies `dist Q Z <= dist Q R`.
-/

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem tile_dist_third (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (j : Fin N) {u v w : Fin 3} (hvu : v ≠ u) (hwu : w ≠ u) (hwv : w ≠ v) :
    dist ((D.tile j).pts u) ((D.tile j).pts v) = slen D (idx j w) := by
  rcases fin3_arm u v hvu with h | h
  · subst h
    rw [side_len_01 D idx hidx, fin3_third_bz7 u w hwu hwv]
  · subst h
    rw [side_len_02 D idx hidx, fin3_third_bz7_bz7b u w hwu hwv]

theorem corner_tile_vertices (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hβ : D.model.angleAt 1 = Real.pi - 3 * D.model.angleAt 0) (hγ : D.model.angleAt 2 = 2 * D.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi)
    (kA : Fin M) (hkA : P.angle (kA + 1) = D.model.angleAt 0)
    {j1 j2 : Fin N} {U1 U2 : Plane}
    (hS1 : TriStep (D.tile j1) (toV2 (P.e (kA + 1))) (P.v (kA + 1)) U1) (hS2 : TriStep (D.tile j2) (toV2 (P.e kA)) U2 (P.v (kA + 1))) :
    j1 = j2 ∧ ∃ k0 k1 k2 : Fin 3, k1 ≠ k0 ∧ k2 ≠ k0 ∧ k2 ≠ k1 ∧ (D.tile j1).pts k0 = P.v (kA + 1) ∧ (D.tile j1).pts k1 = U1 ∧
      (D.tile j1).pts k2 = U2 ∧ idx j1 k0 = 0 := by
  classical
  obtain ⟨hn0, hn1, hn2⟩ := corner_alpha_counts D P hreg idx hidxA hβ hγ hα kA hkA
  set A := P.v (kA + 1) with hA
  obtain ⟨kk1, f1, g1, hk1, hf1, hfk1, hgk1, hgf1, hpar1, hleft1⟩ := id hS1
  obtain ⟨kk2, f2, g2, hk2, hf2, hfk2, hgk2, hgf2, hpar2, hleft2⟩ := id hS2
  have hz : ∀ z : Fin 3, 1 ≤ cnt D idx A z → z = 0 := by
    intro z hz
    fin_cases z
    · rfl
    · simp at hz; omega
    · simp at hz; omega
  have h10 : idx j1 kk1 = 0 := hz _ (cnt_pos_of_corner_h1 D idx hk1 rfl)
  have h20 : idx j2 f2 = 0 := hz _ (cnt_pos_of_corner_h1 D idx hf2 rfl)
  have hj : j1 = j2 := corner_eq_of_cnt_le_one_h1 D idx (l := 0) (by omega) hk1 h10 hf2 h20
  subst hj
  have hkk : kk1 = f2 := (D.tile j1).indep.injective (hk1.trans hf2.symm)
  subst hkk
  have hff : f1 ≠ kk2 := by
    intro hff
    subst hff
    have hU : U1 = U2 := by rw [← hf1, ← hk2]
    subst hU
    obtain ⟨c1, hc1', hc1e⟩ := hpar1.smul
    obtain ⟨c2, hc2', hc2e⟩ := hpar2.smul
    have hneg : toV2 (A - U1) = (-(toV2 (U1 - A)).1, -(toV2 (U1 - A)).2) := by unfold toV2; ext <;> simp
    rw [hc2e, hc1e] at hneg
    have hcr := crs_consecutive_pos P kA
    set dk := toV2 (P.e kA) with hdk
    set dm := toV2 (P.e (kA + 1)) with hdm
    have e1 := congrArg Prod.fst hneg
    have e2 := congrArg Prod.snd hneg
    simp only at e1 e2
    unfold crs at hcr
    have : c2 * (dk.1 * dm.2 - dk.2 * dm.1) = 0 := by linear_combination dm.2 * e1 - dm.1 * e2
    have h0 : (dk.1 * dm.2 - dk.2 * dm.1) = 0 := by
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hc2'.ne'
      · exact h
    linarith
  exact ⟨rfl, kk1, f1, kk2, hfk1, Ne.symm hfk2, Ne.symm hff, hk1, hf1, hk2, h10⟩

/-- A point `Z` of the polygon on the ray from `Q` through `R` (`R` on the line of the side `j`, `Q` strictly inside it) is not beyond `R`. -/
theorem ray_bound (P : ConvPoly M) (j : Fin M) {Q R Z : Plane} (hQ : 0 < P.c j Q) (hR : P.c j R = 0) (hZ : Z ∈ P.carrier)
    {lam : ℝ} (hl : 0 < lam) (hZe : toV2 (Z - Q) = (lam * (toV2 (R - Q)).1, lam * (toV2 (R - Q)).2)) :
    lam ≤ 1 ∧ dist Z Q = lam * dist R Q := by
  have hcc : ∀ y, P.c j y = crs (toV2 (P.e j)) (toV2 (y - P.v j)) := fun y => rfl
  have hdecZ : toV2 (Z - P.v j) = ((toV2 (Z - Q)).1 + (toV2 (Q - P.v j)).1, (toV2 (Z - Q)).2 + (toV2 (Q - P.v j)).2) := by
    unfold toV2; ext <;> simp
  have hdecR : toV2 (R - P.v j) = ((toV2 (R - Q)).1 + (toV2 (Q - P.v j)).1, (toV2 (R - Q)).2 + (toV2 (Q - P.v j)).2) := by
    unfold toV2; ext <;> simp
  have hZ0 : 0 ≤ P.c j Z := hZ j
  rw [hcc, hdecZ, hZe] at hZ0
  rw [hcc, hdecR] at hR
  rw [hcc] at hQ
  have h1 : crs (toV2 (P.e j)) (lam * (toV2 (R - Q)).1 + (toV2 (Q - P.v j)).1, lam * (toV2 (R - Q)).2 + (toV2 (Q - P.v j)).2)
      = lam * crs (toV2 (P.e j)) (toV2 (R - Q)) + crs (toV2 (P.e j)) (toV2 (Q - P.v j)) := by unfold crs; simp only; ring
  have h2 : crs (toV2 (P.e j)) ((toV2 (R - Q)).1 + (toV2 (Q - P.v j)).1, (toV2 (R - Q)).2 + (toV2 (Q - P.v j)).2)
      = crs (toV2 (P.e j)) (toV2 (R - Q)) + crs (toV2 (P.e j)) (toV2 (Q - P.v j)) := by unfold crs; simp only; ring
  rw [h1] at hZ0
  rw [h2] at hR
  refine ⟨?_, ?_⟩
  · by_contra hh; push Not at hh
    nlinarith
  · have d1 := dist_of_toV2 hl.le hZe
    have d2 := dist_of_toV2 (zero_le_one' ℝ) (show toV2 (R - Q) = (1 * (toV2 (R - Q)).1, 1 * (toV2 (R - Q)).2) by simp)
    rw [d1, d2]; ring

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.corner_tile_vertices
#print axioms Erdos634.Draft.LaczFormal.RG.ray_bound
#print axioms Erdos634.Draft.LaczFormal.RG.tile_dist_third
