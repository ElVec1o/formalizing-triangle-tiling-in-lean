-- Draft/LaczFormalBZL7d1.lean -- Beeson-Zhang (arXiv 2604.01314v1) Table 2 and LEMMA 3.5 for a convex polygon target of ANY angles that has no gamma corner at a polygon vertex
-- (the printed Lemma 3.5 is for a triangle ABC not similar to the tile; there no corner of ABC carries a gamma, see LaczFormalBZL7d2).
--   `vertex_type_gen2` : Table 2 with the polygon angles arbitrary and `cnt (corner) gamma = 0` as hypothesis;
--   `bz_lemma35_gen2`  : `NotComb a b c` is impossible (weight 6 out - 6 in + #alpha + #beta - 2 #gamma >= 0 everywhere, >= 1 at a polygon vertex, total 0).
-- Generalises LaczFormalBZL7c1/c2 (angles in {pi/3, 2 alpha, 2 beta}).  NOTE, UNAUDITED.
-- Credit: Beeson-Zhang (arXiv 2604.01314v1, Lemma 3.5, Table 2, Table 4), Laczkovich (DCG 48 (2012), Sect. 4, 7), Beeson.
import Erdos634.Draft.LaczFormalBZ4
import Erdos634.Draft.LaczFormalBZL7c1

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- **Table 2 of Beeson-Zhang for a convex polygon with no `γ` corner at any polygon vertex** (any polygon angles). -/
theorem vertex_type_gen2 (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hγ : D.model.angleAt 2 = 2 * Real.pi / 3) (hαβ : D.model.angleAt 0 + D.model.angleAt 1 = Real.pi / 3)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi)
    (hcorn : ∀ k : Fin M, cnt D idx (P.v (k + 1)) 2 = 0) {X : Plane}
    (hvert : ∃ j k, (D.tile j).pts k = X) :
    (cnt D idx X 0 = cnt D idx X 1 ∧
      ((X ∈ interior D.region ∧ cnt D idx X 0 + 2 * cnt D idx X 2 = 6) ∨ cnt D idx X 0 + 2 * cnt D idx X 2 = 3 ∨
        (X ∉ interior D.region ∧ cnt D idx X 0 + 2 * cnt D idx X 2 = 1 ∧ ∃ k : Fin M, X = P.v (k + 1)))) ∨
    (cnt D idx X 2 = 0 ∧ ∃ k : Fin M, X = P.v (k + 1)) := by
  have hAexp : Asum D idx X = (cnt D idx X 0 : ℝ) * D.model.angleAt 0 + (cnt D idx X 1 : ℝ) * D.model.angleAt 1 + (cnt D idx X 2 : ℝ) * D.model.angleAt 2 := by
    unfold Asum; rw [Fin.sum_univ_three]
  have hpi := Real.pi_pos
  have key : ∀ m : ℕ, Asum D idx X = m * (Real.pi / 3) → cnt D idx X 0 = cnt D idx X 1 ∧ cnt D idx X 0 + 2 * cnt D idx X 2 = m := by
    intro m hm
    exact type_arith hαβ hγ hα _ _ _ m (by rw [← hAexp]; exact hm)
  rcases vertex_A D P hreg idx hidxA hvert with ⟨hi, h2 | h1⟩ | ⟨hni, h1 | ⟨k, hXk, hk⟩⟩
  · have := key 6 (by rw [h2]; push_cast; ring)
    exact Or.inl ⟨this.1, Or.inl ⟨hi, this.2⟩⟩
  · have := key 3 (by rw [h1]; push_cast; ring)
    exact Or.inl ⟨this.1, Or.inr (Or.inl this.2)⟩
  · have := key 3 (by rw [h1]; push_cast; ring)
    exact Or.inl ⟨this.1, Or.inr (Or.inl this.2)⟩
  · exact Or.inr ⟨by rw [hXk]; exact hcorn k, k, hXk⟩

/-- **Beeson-Zhang Lemma 3.5** (`NotComb a b c` is impossible) for a dissection of a convex polygon whose angles are `π/3`, `2α` or `2β`. -/
theorem bz_lemma35_gen2 (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2))
    (hγ : D.model.angleAt 2 = 2 * Real.pi / 3) (hαβ : D.model.angleAt 0 + D.model.angleAt 1 = Real.pi / 3)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi)
    (hPlt : ∀ i, P.angle i < Real.pi) (hcorn : ∀ k : Fin M, cnt D idx (P.v (k + 1)) 2 = 0) : False := by
  classical
  have hpi := Real.pi_pos
  have hα0 := model_angle_pos' D 0
  have hβ0 := model_angle_pos' D 1
  have hab : slen D 0 ≠ slen D 1 := by
    intro e
    have := hnc 1 1 0 one_pos
    apply this; rw [e]; simp
  have hac : slen D 0 ≠ slen D 2 := by
    intro e
    have := hnc 1 0 1 one_pos
    apply this; rw [e]; simp
  set V := vtxSet D.toRegionDissection with hVdef
  set E : Finset (Plane × Plane) := (V ×ˢ V).filter (fun e => GaEdge D.toRegionDissection (slen D 0) e.1 e.2) with hE
  let out : Plane → ℕ := fun v => (E.filter (fun e => e.1 = v)).card
  let inn : Plane → ℕ := fun v => (E.filter (fun e => e.2 = v)).card
  have hEmem : ∀ e : Plane × Plane, e ∈ E ↔ GaEdge D.toRegionDissection (slen D 0) e.1 e.2 := by
    intro e
    simp only [hE, Finset.mem_filter, Finset.mem_product]
    constructor
    · exact fun h => h.2
    · intro h
      have := ga_edge_endpoints D.toRegionDissection (slen D 0) h
      exact ⟨⟨mem_vtxSet.mpr this.1, mem_vtxSet.mpr this.2⟩, h⟩
  have hin1 : ∀ v, inn v ≤ 1 := by
    intro v
    simp only [inn]
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    have h1 := (hEmem a).mp ha.1
    have h2 := (hEmem b).mp hb.1
    rw [ha.2] at h1
    rw [hb.2] at h2
    have := ga_indegree D idx hidx hnc h1 h2
    exact Prod.ext this (ha.2.trans hb.2.symm)
  have hbal : ∑ v ∈ V, (out v : ℤ) = ∑ v ∈ V, (inn v : ℤ) := by
    have h1 := Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (s := E) (t := V)
      (fun e he => ((Finset.mem_product.mp (Finset.mem_filter.mp he).1).1))
    have h2 := Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (s := E) (t := V)
      (fun e he => ((Finset.mem_product.mp (Finset.mem_filter.mp he).1).2))
    have : ∑ v ∈ V, out v = ∑ v ∈ V, inn v := by
      simp only [out, inn]; rw [← h1, ← h2]
    exact_mod_cast this
  have hs0 : ∑ v ∈ V, (cnt D idx v 0 : ℤ) = N := by exact_mod_cast sum_cnt_vtx D idx 0
  have hs1 : ∑ v ∈ V, (cnt D idx v 1 : ℤ) = N := by exact_mod_cast sum_cnt_vtx D idx 1
  have hs2 : ∑ v ∈ V, (cnt D idx v 2 : ℤ) = N := by exact_mod_cast sum_cnt_vtx D idx 2
  -- in-degree zero at every vertex of the polygon
  have hin0poly : ∀ k : Fin M, inn (P.v (k + 1)) = 0 := by
    intro k
    by_contra hne
    have hi1 := hin1 (P.v (k + 1))
    have h1 : inn (P.v (k + 1)) = 1 := by omega
    obtain ⟨e, he⟩ := Finset.card_pos.mp (by simp only [inn] at h1 ⊢; omega : 0 < (E.filter (fun e => e.2 = P.v (k + 1))).card)
    simp only [Finset.mem_filter] at he
    have hge := (hEmem e).mp he.1
    rw [he.2] at hge
    obtain ⟨hsum, -⟩ := bz_head_analysis D idx hidx hidxA hnc hab hac hge
    have hv : ∃ j k', (D.tile j).pts k' = P.v (k + 1) := poly_vertex_is_tile_vertex D.toRegionDissection P hreg (k + 1)
    have hcA := corner_A D P hreg idx hidxA k hv
    have hAs : Asum D idx (P.v (k + 1)) = Real.pi := by unfold Asum; exact hsum
    rw [hAs] at hcA
    have := hPlt (k + 1)
    linarith
  have hf : ∀ v ∈ V, 0 ≤ 6 * (out v : ℤ) - 6 * (inn v : ℤ) + (cnt D idx v 0 : ℤ) + (cnt D idx v 1 : ℤ) - 2 * (cnt D idx v 2 : ℤ) := by
    intro v hv
    have hvert : ∃ j k, (D.tile j).pts k = v := mem_vtxSet.mp hv
    rcases vertex_type_gen2 D P hreg idx hidxA hγ hαβ hα hcorn hvert with ⟨hreg', htype⟩ | ⟨hc2, k, hk⟩
    · have F1 : inn v = 1 → cnt D idx v 0 + 2 * cnt D idx v 2 = 3 ∧
          (cnt D idx v 0 = 1 → cnt D idx v 2 = 1 → 1 ≤ out v) := by
        intro h1
        have hne : (E.filter (fun e => e.2 = v)).Nonempty := Finset.card_pos.mp (by simp only [inn] at h1; omega)
        obtain ⟨e, he⟩ := hne
        simp only [Finset.mem_filter] at he
        have hge := (hEmem e).mp he.1
        rw [he.2] at hge
        obtain ⟨hsum, hsimple⟩ := bz_head_analysis D idx hidx hidxA hnc hab hac hge
        have hexp : ∑ l, (cnt D idx v l : ℝ) * D.model.angleAt l = (cnt D idx v 0 : ℝ) * D.model.angleAt 0 + (cnt D idx v 1 : ℝ) * D.model.angleAt 1 + (cnt D idx v 2 : ℝ) * D.model.angleAt 2 := by
          rw [Fin.sum_univ_three]
        have := type_arith hαβ hγ hα (cnt D idx v 0) (cnt D idx v 1) (cnt D idx v 2) 3 (by rw [← hexp, hsum]; push_cast; ring)
        refine ⟨this.2, fun h0 h2 => ?_⟩
        have h1' : cnt D idx v 1 = 1 := by omega
        obtain ⟨H', hH'⟩ := hsimple h0 h1' h2
        have : (v, H') ∈ E.filter (fun e => e.1 = v) := by
          rw [Finset.mem_filter]
          exact ⟨(hEmem (v, H')).mpr hH', rfl⟩
        exact Finset.card_pos.mpr ⟨_, this⟩
      have F2 : cnt D idx v 0 = 0 → cnt D idx v 2 = 3 → 1 ≤ out v := by
        intro h0 h2
        have hint : v ∈ interior D.region := by
          rcases htype with ⟨hi, -⟩ | h | ⟨-, h, -⟩
          · exact hi
          · omega
          · omega
        have h1' : cnt D idx v 1 = 0 := by omega
        obtain ⟨H', hH'⟩ := bz_center_out D idx hidx hidxA hnc hab hac hγ hvert hint h0 h1' h2
        have : (v, H') ∈ E.filter (fun e => e.1 = v) := by
          rw [Finset.mem_filter]
          exact ⟨(hEmem (v, H')).mpr hH', rfl⟩
        exact Finset.card_pos.mpr ⟨_, this⟩
      have hi1 := hin1 v
      rcases Nat.lt_or_ge (inn v) 1 with hlt | hge
      · have hi0 : inn v = 0 := by omega
        rw [hi0]
        by_cases hc3 : cnt D idx v 2 = 3
        · have := F2 (by omega) hc3
          omega
        · omega
      · have hi1' : inn v = 1 := by omega
        obtain ⟨hm3, hsm⟩ := F1 hi1'
        by_cases hc1 : cnt D idx v 2 = 1
        · have := hsm (by omega) hc1
          omega
        · omega
    · have hi0 := hin0poly k
      rw [← hk] at hi0
      rw [hi0, hc2]
      omega
  have hv0 : ∃ j k, (D.tile j).pts k = P.v (0 + 1) := poly_vertex_is_tile_vertex D.toRegionDissection P hreg (0 + 1)
  have hvV : P.v (0 + 1) ∈ V := mem_vtxSet.mpr hv0
  have hcA := corner_A D P hreg idx hidxA 0 hv0
  have hcnt2 : cnt D idx (P.v (0 + 1)) 2 = 0 := hcorn 0
  have hApos := Asum_pos D idx hv0
  have hin0 := hin0poly 0
  have hc01 : 1 ≤ cnt D idx (P.v (0 + 1)) 0 + cnt D idx (P.v (0 + 1)) 1 := by
    by_contra hlt
    have h0 : cnt D idx (P.v (0 + 1)) 0 = 0 := by omega
    have h1 : cnt D idx (P.v (0 + 1)) 1 = 0 := by omega
    have hAexp : Asum D idx (P.v (0 + 1)) = (cnt D idx (P.v (0 + 1)) 0 : ℝ) * D.model.angleAt 0 + (cnt D idx (P.v (0 + 1)) 1 : ℝ) * D.model.angleAt 1 + (cnt D idx (P.v (0 + 1)) 2 : ℝ) * D.model.angleAt 2 := by
      unfold Asum; rw [Fin.sum_univ_three]
    rw [hAexp, h0, h1, hcnt2] at hApos
    simp at hApos
  have hf0 : 1 ≤ 6 * (out (P.v (0 + 1)) : ℤ) - 6 * (inn (P.v (0 + 1)) : ℤ) + (cnt D idx (P.v (0 + 1)) 0 : ℤ) + (cnt D idx (P.v (0 + 1)) 1 : ℤ) - 2 * (cnt D idx (P.v (0 + 1)) 2 : ℤ) := by
    rw [hin0, hcnt2]
    push_cast
    omega
  have hsum0 : ∑ v ∈ V, (6 * (out v : ℤ) - 6 * (inn v : ℤ) + (cnt D idx v 0 : ℤ) + (cnt D idx v 1 : ℤ) - 2 * (cnt D idx v 2 : ℤ)) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      hbal, hs0, hs1, hs2]
    ring
  have hle := Finset.single_le_sum (f := fun v => 6 * (out v : ℤ) - 6 * (inn v : ℤ) + (cnt D idx v 0 : ℤ) + (cnt D idx v 1 : ℤ) - 2 * (cnt D idx v 2 : ℤ)) hf hvV
  simp only at hle
  rw [hsum0] at hle
  omega

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.vertex_type_gen2
#print axioms Erdos634.Draft.LaczFormal.RG.bz_lemma35_gen2
