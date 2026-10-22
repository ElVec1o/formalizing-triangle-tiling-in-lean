-- Draft/LaczFormalBZ4.lean -- Beeson-Zhang (arXiv 2604.01314v1) LEMMA 3.5, formal: a dissection of an equilateral triangle (a convex polygon with all angles pi/3) by the tile (alpha, beta, 2 pi/3),
-- alpha not in Q pi, in which `a` is NOT a nonnegative rational combination of `b, c` does not exist.
-- Proof (Beeson-Zhang, Sect. 3): for the graph Gamma_a let f(v) = out(v) - in(v).  The weight 6 f(v) + (#alpha + #beta - 2 #gamma)(v) is >= 0 at every vertex (centre (0,0,3): out >= 1;
-- star (3,3,0): in <= 1; simple vertex (1,1,1): in = 1 implies out >= 1 by Lemma 3.2; all other types: in = 0 and the corner term is >= 0), and >= 2 at a vertex of the triangle (type (1,1,0), in = 0);
-- but the sum over all vertices is 6 (sum out - sum in) + (N + N - 2N) = 0.  Contradiction.
-- NO balance (out = in at every vertex) is used: that is exactly the claim of Laczkovich's Lemma 7.1 (i) that fails at a 3 alpha + 3 beta = pi vertex (BZFlaw).
-- UNAUDITED.  Credit: Beeson-Zhang (Lemma 3.5), Laczkovich (DCG 48 (2012), Sect. 4, 7).
import Erdos634.Draft.LaczFormalBZ3

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- **Beeson-Zhang Lemma 3.5** (`NotComb a b c` is impossible) for a dissection of a convex polygon with all angles `π/3`. -/
theorem bz_lemma35 (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2))
    (hγ : D.model.angleAt 2 = 2 * Real.pi / 3) (hαβ : D.model.angleAt 0 + D.model.angleAt 1 = Real.pi / 3)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi) (hPang : ∀ i, P.angle i = Real.pi / 3) : False := by
  classical
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
  -- in-degree at most one
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
  -- double counting
  have hbal : ∑ v ∈ V, (out v : ℤ) = ∑ v ∈ V, (inn v : ℤ) := by
    have h1 := Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (s := E) (t := V)
      (fun e he => ((Finset.mem_product.mp (Finset.mem_filter.mp he).1).1))
    have h2 := Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (s := E) (t := V)
      (fun e he => ((Finset.mem_product.mp (Finset.mem_filter.mp he).1).2))
    have : ∑ v ∈ V, out v = ∑ v ∈ V, inn v := by
      simp only [out, inn]; rw [← h1, ← h2]
    exact_mod_cast this
  -- the totals of the counts
  have hs0 : ∑ v ∈ V, (cnt D idx v 0 : ℤ) = N := by exact_mod_cast sum_cnt_vtx D idx 0
  have hs2 : ∑ v ∈ V, (cnt D idx v 2 : ℤ) = N := by exact_mod_cast sum_cnt_vtx D idx 2
  -- the local inequality
  have hf : ∀ v ∈ V, 0 ≤ 6 * (out v : ℤ) - 6 * (inn v : ℤ) + 2 * (cnt D idx v 0 : ℤ) - 2 * (cnt D idx v 2 : ℤ) := by
    intro v hv
    have hvert : ∃ j k, (D.tile j).pts k = v := mem_vtxSet.mp hv
    obtain ⟨hreg', htype⟩ := vertex_type D P hreg idx hidxA hγ hαβ hα hPang hvert
    have hm : cnt D idx v 0 + 2 * cnt D idx v 2 = 6 ∨ cnt D idx v 0 + 2 * cnt D idx v 2 = 3 ∨ cnt D idx v 0 + 2 * cnt D idx v 2 = 1 := by
      rcases htype with ⟨-, h⟩ | h | ⟨-, h, -⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    -- in-degree one: a head
    have F1 : inn v = 1 → cnt D idx v 0 + 2 * cnt D idx v 2 = 3 ∧
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
    -- the centre
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
    have hreg'' := hreg'
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
  -- a vertex of the triangle
  have hv0 : ∃ j k, (D.tile j).pts k = P.v (0 + 1) := poly_vertex_is_tile_vertex D.toRegionDissection P hreg (0 + 1)
  have hvV : P.v (0 + 1) ∈ V := mem_vtxSet.mpr hv0
  have hcA := corner_A D P hreg idx hidxA 0 hv0
  have hcnt : cnt D idx (P.v (0 + 1)) 0 = 1 ∧ cnt D idx (P.v (0 + 1)) 1 = 1 ∧ cnt D idx (P.v (0 + 1)) 2 = 0 := by
    have hexp : Asum D idx (P.v (0 + 1)) = (cnt D idx (P.v (0 + 1)) 0 : ℝ) * D.model.angleAt 0 + (cnt D idx (P.v (0 + 1)) 1 : ℝ) * D.model.angleAt 1 + (cnt D idx (P.v (0 + 1)) 2 : ℝ) * D.model.angleAt 2 := by
      unfold Asum; rw [Fin.sum_univ_three]
    have := type_arith hαβ hγ hα (cnt D idx (P.v (0 + 1)) 0) (cnt D idx (P.v (0 + 1)) 1) (cnt D idx (P.v (0 + 1)) 2) 1
      (by rw [← hexp, hcA, hPang]; push_cast; ring)
    omega
  have hin0 : inn (P.v (0 + 1)) = 0 := by
    by_contra hne
    have hi1 := hin1 (P.v (0 + 1))
    have h1 : inn (P.v (0 + 1)) = 1 := by omega
    obtain ⟨e, he⟩ := Finset.card_pos.mp (by simp only [inn] at h1 ⊢; omega : 0 < (E.filter (fun e => e.2 = P.v (0 + 1))).card)
    simp only [Finset.mem_filter] at he
    have hge := (hEmem e).mp he.1
    rw [he.2] at hge
    obtain ⟨hsum, -⟩ := bz_head_analysis D idx hidx hidxA hnc hab hac hge
    have hexp : ∑ l, (cnt D idx (P.v (0 + 1)) l : ℝ) * D.model.angleAt l = (cnt D idx (P.v (0 + 1)) 0 : ℝ) * D.model.angleAt 0 + (cnt D idx (P.v (0 + 1)) 1 : ℝ) * D.model.angleAt 1 + (cnt D idx (P.v (0 + 1)) 2 : ℝ) * D.model.angleAt 2 := by
      rw [Fin.sum_univ_three]
    have := type_arith hαβ hγ hα (cnt D idx (P.v (0 + 1)) 0) (cnt D idx (P.v (0 + 1)) 1) (cnt D idx (P.v (0 + 1)) 2) 3 (by rw [← hexp, hsum]; push_cast; ring)
    omega
  have hf0 : 2 ≤ 6 * (out (P.v (0 + 1)) : ℤ) - 6 * (inn (P.v (0 + 1)) : ℤ) + 2 * (cnt D idx (P.v (0 + 1)) 0 : ℤ) - 2 * (cnt D idx (P.v (0 + 1)) 2 : ℤ) := by
    rw [hin0, hcnt.1, hcnt.2.2]
    push_cast
    omega
  have hsum0 : ∑ v ∈ V, (6 * (out v : ℤ) - 6 * (inn v : ℤ) + 2 * (cnt D idx v 0 : ℤ) - 2 * (cnt D idx v 2 : ℤ)) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      hbal, hs0, hs2]
    ring
  have hle := Finset.single_le_sum (f := fun v => 6 * (out v : ℤ) - 6 * (inn v : ℤ) + 2 * (cnt D idx v 0 : ℤ) - 2 * (cnt D idx v 2 : ℤ)) hf hvV
  simp only at hle
  rw [hsum0] at hle
  omega

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.bz_lemma35
