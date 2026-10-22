-- Draft/LaczFormalRGWalk2.lean -- S4 of PLAN_THM21: the WALK of tiles along an edge of a convex polygon (the division X = U_0, U_1, .., U_k = Y of the side XY into tile sides;
-- Laczkovich DCG 48 (2012), Sect. 4), for a dissection of the polygon: `side_walk_exists_poly`.  Every polygon vertex is a vertex of a tile (`poly_vertex_is_tile_vertex`).
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 4, Lemma 4.3), Beeson, Beeson-Zhang; port of LaczFormalGraphWalk.side_walk_exists.
import Erdos634.Draft.LaczFormalRGBdy3
import Erdos634.Draft.LaczFormalRGWalk
import Erdos634.PinPlumbing

open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- Every vertex of the polygon is the corner of some tile of a dissection of it. -/
theorem poly_vertex_is_tile_vertex (D : RegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier) (m : Fin M) :
    ∃ i k, (D.tile i).pts k = P.v m := by
  classical
  set k1 := m - 1 with hk1
  have hm : k1 + 1 = m := (ConvPoly.fin_facts P.three_le m).2.2.2.2.1
  have hV : P.v m ∈ P.carrier := by
    intro j
    by_cases hj : j = m
    · subst hj; rw [← P.c_self j]; rfl
    · by_cases hj' : j + 1 = m
      · rw [← hj']; exact (P.c_next j).symm ▸ le_rfl
      · exact (P.c_vertex_pos (Ne.symm hj) (Ne.symm hj')).le
  have hcov : P.v m ∈ ⋃ i, (D.tile i).carrier := by rw [D.covers, hreg]; exact hV
  obtain ⟨i0, hi0⟩ := Set.mem_iUnion.mp hcov
  have hN : 0 < N := Fin.pos i0
  obtain ⟨ρ, hρ, hiff⟩ := P.vertex_local_T P.three_le k1
  have hT1 : (P.locTri P.three_le k1).pts 1 = P.v m := by rw [← hm]; rfl
  have hiffD : ∀ y, dist y (P.v m) < ρ → (y ∈ D.region ↔ y ∈ (P.locTri P.three_le k1).carrier) := by
    intro y hy; rw [hreg]; exact hiff y (by rw [hm]; exact hy)
  have hsum := sum_localAngle_tri D hN (P.locTri P.three_le k1) hρ hiffD
  have hT1' : (P.locTri P.three_le k1).localAngle (P.v m) < Real.pi := by
    rw [← hT1, Tri.localAngle_vertex]
    exact Erdos634.RouteOneVertexKill.cornerAngle_lt_pi _ 1
  have hle : (D.tile i0).localAngle (P.v m) ≤ ∑ i', (D.tile i').localAngle (P.v m) :=
    Finset.single_le_sum (f := fun i' => (D.tile i').localAngle (P.v m)) (fun i' _ => (D.tile i').localAngle_nonneg _) (Finset.mem_univ i0)
  rw [hsum] at hle
  rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i0) (P.v m) with ⟨j, hj, -⟩ | h2 | h1 | h0
  · exact ⟨i0, j, hj.symm⟩
  · exfalso; have := Real.pi_pos; linarith
  · exfalso; linarith
  · exact absurd h0 (Erdos634.MarchFlank.localAngle_ne_zero_of_mem _ hi0)

/-- A vertex of the tiling on the line of the edge `i`, in the polygon, lies on the edge. -/
theorem vertex_on_edge (D : RegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier) (i : Fin M) {U : Plane}
    (hU : ∃ j k, (D.tile j).pts k = U) (hline : crs (toV2 (P.e i)) (toV2 (U - P.v i)) = 0) :
    ∃ t ∈ Set.Icc (0:ℝ) 1, U = (1 - t) • P.v i + t • P.v (i + 1) := by
  have hUP : U ∈ P.carrier := by
    obtain ⟨j, k, hjk⟩ := hU
    rw [← hreg, ← D.covers]
    exact Set.mem_iUnion.mpr ⟨j, hjk ▸ subset_convexHull ℝ _ ⟨k, rfl⟩⟩
  have h0 : P.c i U = 0 := by
    have : P.c i U = crs (toV2 (P.e i)) (toV2 (U - P.v i)) := rfl
    rw [this]; exact hline
  exact P.edge_param P.three_le hUP h0

/-- **A left step starts at every vertex of the tiling on the edge `i`, except the last.** -/
theorem step_exists_poly (D : RegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier) (i : Fin M) {U : Plane}
    (hU : ∃ j k, (D.tile j).pts k = U) (hline : crs (toV2 (P.e i)) (toV2 (U - P.v i)) = 0) (hUY : U ≠ P.v (i + 1)) :
    ∃ j U', TriStep (D.tile j) (toV2 (P.e i)) U U' := by
  classical
  obtain ⟨t, ht, hUt⟩ := vertex_on_edge D P hreg i hU hline
  rcases ht.1.eq_or_lt with h0 | h0
  · -- U = v_i
    have hUX : U = P.v i := by rw [hUt, ← h0]; simp
    have hk : i - 1 + 1 = i := (ConvPoly.fin_facts P.three_le i).2.2.2.2.1
    have hvert : ∃ j k, (D.tile j).pts k = P.v (i - 1 + 1) := by rw [hk, ← hUX]; exact hU
    obtain ⟨pT, qT, F, hpd, hqd, hcr, h1, h2, h3, h4, h5⟩ := fan_vertex_poly D P hreg (i - 1) hvert
    rw [hk] at hpd
    obtain ⟨j, U', hS⟩ := first_step_corner D F hcr h1 h2 h3 h4 hpd hvert
    rw [hk] at hS
    rw [hUX]
    exact ⟨j, U', hS⟩
  · have ht1 : t < 1 := by
      rcases ht.2.eq_or_lt with h1 | h1
      · exfalso; apply hUY; rw [hUt, h1]; simp
      · exact h1
    have hvert : ∃ j k, (D.tile j).pts k = (1 - t) • P.v i + t • P.v (i + 1) := by rw [← hUt]; exact hU
    obtain ⟨pT, F, hpd, hpe, hqe, hTgt⟩ := fan_open_edge D P hreg i h0 ht1 hvert
    obtain ⟨j, U', hS⟩ := first_step_open D F hpe hqe hpd hvert
    rw [← hUt] at hS
    exact ⟨j, U', hS⟩

/-- **The walk along an edge exists**: a chain of left tiles from `v_i` to `v_{i+1}` along the edge (the division of the side into tile sides). -/
theorem side_walk_exists_poly (D : RegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier) (i : Fin M) :
    ∃ L, WalkT D (toV2 (P.e i)) (P.v i) (P.v (i + 1)) L := by
  classical
  set d := toV2 (P.e i) with hd
  set X0 := P.v i with hX0
  set Y0 := P.v (i + 1) with hY0
  have hd0 : d ≠ 0 := toV2_ne_zero (P.e_ne_zero P.three_le i)
  have hnd : 0 < nsq d := nsq_pos hd0
  set A : Finset Plane := vtxSet D with hA
  set F : Plane → Finset Plane := fun U => A.filter (fun v => dt d (toV2 (v - X0)) > dt d (toV2 (U - X0))) with hF
  have key : ∀ n : ℕ, ∀ U : Plane, (F U).card = n → (∃ j k, (D.tile j).pts k = U) →
      crs d (toV2 (U - X0)) = 0 → ∃ L, WalkT D d U Y0 L := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro U hcard hvert hline
      by_cases hUY : U = Y0
      · exact ⟨[], hUY ▸ WalkT.nil U⟩
      · have hstep : ∃ j U', TriStep (D.tile j) d U U' := step_exists_poly D P hreg i hvert hline hUY
        obtain ⟨j, U', hS⟩ := hstep
        obtain ⟨kk, f, g, hk, hf, -, -, -, hpar, -⟩ := id hS
        obtain ⟨c, hc, hcw⟩ := hpar.smul
        have hdec : toV2 (U' - X0) = ((toV2 (U' - U)).1 + (toV2 (U - X0)).1, (toV2 (U' - U)).2 + (toV2 (U - X0)).2) := by
          unfold toV2; ext <;> simp
        have hline' : crs d (toV2 (U' - X0)) = 0 := by
          rw [hdec, hcw]
          unfold crs at hline ⊢; simp only at hline ⊢; nlinarith [hline]
        have hdt : dt d (toV2 (U' - X0)) > dt d (toV2 (U - X0)) := by
          rw [hdec, hcw]
          unfold dt nsq at *; simp only; nlinarith [mul_pos hc hnd]
        have hvert' : ∃ j k, (D.tile j).pts k = U' := ⟨j, f, hf⟩
        have hsub : F U' ⊂ F U := by
          refine ⟨?_, ?_⟩
          · intro v hv
            simp only [hF, Finset.mem_filter] at hv ⊢
            exact ⟨hv.1, lt_trans hdt hv.2⟩
          · intro hsub
            have hU'mem : U' ∈ F U := by
              simp only [hF, Finset.mem_filter]
              exact ⟨mem_vtxSet.mpr hvert', hdt⟩
            have := hsub hU'mem
            simp only [hF, Finset.mem_filter] at this
            exact lt_irrefl _ this.2
        have hlt : (F U').card < n := hcard ▸ Finset.card_lt_card hsub
        obtain ⟨L, hL⟩ := ih (F U').card hlt U' rfl hvert' hline'
        exact ⟨(j, U, U') :: L, WalkT.cons hS hL⟩
  have hX0v : ∃ j k, (D.tile j).pts k = X0 := poly_vertex_is_tile_vertex D P hreg i
  exact key _ X0 rfl hX0v (by unfold crs toV2; simp)

end Erdos634.Draft.LaczFormal.RG
