-- Draft/LaczFormalBZ4b.lean -- Beeson-Zhang Lemma 3.5, POLYGON version: for a regular tiling of a convex M-gon (corner angles pi/3 or 2 pi/3) by the tile (alpha, beta, 2 pi/3) in which `a` is not a nonnegative
-- rational combination of `b, c`, the number R of tiles whose gamma-corner sits at a vertex of the polygon is at least M - 2.
--   (M = 3: R = 0 < 1, so the hypothesis is absurd: this is `bz_lemma35` without irrationality of alpha, with regularity as hypothesis.  M = 4: both angles 2 pi/3 are single gamma corners; M = 5, 6 likewise.)
-- The proof is the vertex count of LaczFormalBZ4 with the corner terms kept: sum over polygon vertices of (#alpha + #beta - 2 #gamma) = 6 (M - 2 - R) must be <= 0.
-- WHAT THIS DOES NOT DO: exclude R >= M - 2.  Those are the polygons of Theorem 2.1 (ii) (M - 2 angles gamma): there the printed proof (Lemma 7.1 (i)) is not available and this count gives no contradiction.
-- UNAUDITED.  Credit: Beeson-Zhang (Lemma 3.5), Laczkovich (DCG 48 (2012), Sect. 7).
import Erdos634.Draft.LaczFormalBZ4

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem type_arith_reg {α β γ : ℝ} (hαβ : α + β = Real.pi / 3) (hγ : γ = 2 * Real.pi / 3) (c0 c2 m : ℕ)
    (h : (c0 : ℝ) * α + c0 * β + c2 * γ = m * (Real.pi / 3)) : c0 + 2 * c2 = m := by
  have hpi := Real.pi_pos
  have e : ((c0 + 2 * c2 : ℕ) : ℝ) * (Real.pi / 3) = (m : ℝ) * (Real.pi / 3) := by
    push_cast
    rw [hγ] at h
    linear_combination h - (c0 : ℝ) * hαβ
  have := mul_right_cancel₀ (by positivity : (Real.pi / 3) ≠ 0) e
  exact_mod_cast this

theorem polyV_injective (P : ConvPoly M) : Function.Injective P.v := by
  intro i j hij
  by_contra hne
  have hM := P.three_le
  have hfi := ConvPoly.fin_facts hM i
  by_cases hj : j = i + 1
  · -- use the edge `j`, vertex `i`
    have hfj := ConvPoly.fin_facts hM j
    have h1 : i ≠ j := hne
    have h2 : i ≠ j + 1 := by rw [hj, hfi.2.2.2.2.2]; exact hfi.2.1.symm
    have := P.c_vertex_pos h1 h2
    rw [hij, P.c_self] at this
    exact lt_irrefl _ this
  · have h1 : j ≠ i := fun h => hne h.symm
    have := P.c_vertex_pos h1 hj
    rw [← hij, P.c_self] at this
    exact lt_irrefl _ this

/-- Vertex types for a polygon with corner angles `π/3` or `2π/3` and regular counts. -/
theorem vertex_type_poly (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hγ : D.model.angleAt 2 = 2 * Real.pi / 3) (hαβ : D.model.angleAt 0 + D.model.angleAt 1 = Real.pi / 3)
    (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1) {X : Plane}
    (hvert : ∃ j k, (D.tile j).pts k = X) (hnc : ∀ k : Fin M, X ≠ P.v (k + 1)) :
    (X ∈ interior D.region ∧ cnt D idx X 0 + 2 * cnt D idx X 2 = 6) ∨ cnt D idx X 0 + 2 * cnt D idx X 2 = 3 := by
  have hpi := Real.pi_pos
  have hAexp : Asum D idx X = (cnt D idx X 0 : ℝ) * D.model.angleAt 0 + (cnt D idx X 1 : ℝ) * D.model.angleAt 1 + (cnt D idx X 2 : ℝ) * D.model.angleAt 2 := by
    unfold Asum; rw [Fin.sum_univ_three]
  have hr : ((cnt D idx X 0 : ℕ) : ℝ) = (cnt D idx X 1 : ℕ) := by exact_mod_cast hregc X
  have key : ∀ m : ℕ, Asum D idx X = m * (Real.pi / 3) → cnt D idx X 0 + 2 * cnt D idx X 2 = m := by
    intro m hm
    apply type_arith_reg hαβ hγ _ _ m
    rw [← hr] at hAexp
    rw [← hAexp]; exact hm
  rcases vertex_A D P hreg idx hidxA hvert with ⟨hi, h2 | h1⟩ | ⟨hni, h1 | ⟨k, hXk, -⟩⟩
  · exact Or.inl ⟨hi, key 6 (by rw [h2]; push_cast; ring)⟩
  · exact Or.inr (key 3 (by rw [h1]; push_cast; ring))
  · exact Or.inr (key 3 (by rw [h1]; push_cast; ring))
  · exact absurd hXk (hnc k)

/-- **Beeson-Zhang Lemma 3.5, polygon version.**  `NotComb a b c` forces at least `M - 2` tiles to have their `γ`-corner at a vertex of the polygon. -/
theorem bz_count_poly (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2))
    (hγ : D.model.angleAt 2 = 2 * Real.pi / 3) (hαβ : D.model.angleAt 0 + D.model.angleAt 1 = Real.pi / 3)
    (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1) (hPang : ∀ i, P.angle i = Real.pi / 3 ∨ P.angle i = 2 * Real.pi / 3) :
    ((M : ℤ) - 2) ≤ ∑ k : Fin M, (cnt D idx (P.v (k + 1)) 2 : ℤ) := by
  classical
  have hpi := Real.pi_pos
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
  have hs2 : ∑ v ∈ V, (cnt D idx v 2 : ℤ) = N := by exact_mod_cast sum_cnt_vtx D idx 2
  -- the heads
  have F1 : ∀ v ∈ V, inn v = 1 → cnt D idx v 0 + 2 * cnt D idx v 2 = 3 ∧
      (cnt D idx v 0 = 1 → cnt D idx v 2 = 1 → 1 ≤ out v) := by
    intro v hv h1
    have hne : (E.filter (fun e => e.2 = v)).Nonempty := Finset.card_pos.mp (by simp only [inn] at h1; omega)
    obtain ⟨e, he⟩ := hne
    simp only [Finset.mem_filter] at he
    have hge := (hEmem e).mp he.1
    rw [he.2] at hge
    obtain ⟨hsum, hsimple⟩ := bz_head_analysis D idx hidx hidxA hnc hab hac hge
    have hexp : ∑ l, (cnt D idx v l : ℝ) * D.model.angleAt l = (cnt D idx v 0 : ℝ) * D.model.angleAt 0 + (cnt D idx v 1 : ℝ) * D.model.angleAt 1 + (cnt D idx v 2 : ℝ) * D.model.angleAt 2 := by
      rw [Fin.sum_univ_three]
    have hr : ((cnt D idx v 0 : ℕ) : ℝ) = (cnt D idx v 1 : ℕ) := by exact_mod_cast hregc v
    have hm3 : cnt D idx v 0 + 2 * cnt D idx v 2 = 3 := by
      apply type_arith_reg hαβ hγ _ _ 3
      rw [← hr] at hexp
      rw [← hexp, hsum]; push_cast; ring
    refine ⟨hm3, fun h0 h2 => ?_⟩
    have h1' : cnt D idx v 1 = 1 := by rw [← hregc v]; exact h0
    obtain ⟨H', hH'⟩ := hsimple h0 h1' h2
    have : (v, H') ∈ E.filter (fun e => e.1 = v) := by
      rw [Finset.mem_filter]
      exact ⟨(hEmem (v, H')).mpr hH', rfl⟩
    exact Finset.card_pos.mpr ⟨_, this⟩
  -- non-corner vertices
  have hf : ∀ v ∈ V, (∀ k : Fin M, v ≠ P.v (k + 1)) →
      0 ≤ 6 * (out v : ℤ) - 6 * (inn v : ℤ) + 2 * (cnt D idx v 0 : ℤ) - 2 * (cnt D idx v 2 : ℤ) := by
    intro v hv hnk
    have hvert : ∃ j k, (D.tile j).pts k = v := mem_vtxSet.mp hv
    have htype := vertex_type_poly D P hreg idx hidxA hγ hαβ hregc hvert hnk
    have hm : cnt D idx v 0 + 2 * cnt D idx v 2 = 6 ∨ cnt D idx v 0 + 2 * cnt D idx v 2 = 3 := by
      rcases htype with ⟨-, h⟩ | h
      · exact Or.inl h
      · exact Or.inr h
    have F2 : cnt D idx v 0 = 0 → cnt D idx v 2 = 3 → 1 ≤ out v := by
      intro h0 h2
      have hint : v ∈ interior D.region := by
        rcases htype with ⟨hi, -⟩ | h
        · exact hi
        · omega
      have h1' : cnt D idx v 1 = 0 := by rw [← hregc v]; exact h0
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
      obtain ⟨hm3, hsm⟩ := F1 v hv hi1'
      by_cases hc1 : cnt D idx v 2 = 1
      · have := hsm (by omega) hc1
        omega
      · omega
  -- corner vertices: no incoming edge
  have hcorner : ∀ k : Fin M, P.v (k + 1) ∈ V ∧ inn (P.v (k + 1)) = 0 ∧
      ((cnt D idx (P.v (k + 1)) 0 + 2 * cnt D idx (P.v (k + 1)) 2 : ℕ) : ℝ) * (Real.pi / 3) = P.angle (k + 1) := by
    intro k
    have hv0 : ∃ j k', (D.tile j).pts k' = P.v (k + 1) := poly_vertex_is_tile_vertex D.toRegionDissection P hreg (k + 1)
    have hcA := corner_A D P hreg idx hidxA k hv0
    have hexp : Asum D idx (P.v (k + 1)) = (cnt D idx (P.v (k + 1)) 0 : ℝ) * D.model.angleAt 0 + (cnt D idx (P.v (k + 1)) 1 : ℝ) * D.model.angleAt 1 + (cnt D idx (P.v (k + 1)) 2 : ℝ) * D.model.angleAt 2 := by
      unfold Asum; rw [Fin.sum_univ_three]
    have hr : ((cnt D idx (P.v (k + 1)) 0 : ℕ) : ℝ) = (cnt D idx (P.v (k + 1)) 1 : ℕ) := by exact_mod_cast hregc _
    have hmk : ((cnt D idx (P.v (k + 1)) 0 + 2 * cnt D idx (P.v (k + 1)) 2 : ℕ) : ℝ) * (Real.pi / 3) = P.angle (k + 1) := by
      rw [← hcA]
      rw [hexp, ← hr]
      push_cast
      rw [hγ]
      linear_combination (-(cnt D idx (P.v (k + 1)) 0 : ℝ)) * hαβ
    refine ⟨mem_vtxSet.mpr hv0, ?_, hmk⟩
    by_contra hne
    have hi1 := hin1 (P.v (k + 1))
    have h1 : inn (P.v (k + 1)) = 1 := by omega
    obtain ⟨e, he⟩ := Finset.card_pos.mp (by simp only [inn] at h1 ⊢; omega : 0 < (E.filter (fun e => e.2 = P.v (k + 1))).card)
    simp only [Finset.mem_filter] at he
    have hge := (hEmem e).mp he.1
    rw [he.2] at hge
    obtain ⟨hsum, -⟩ := bz_head_analysis D idx hidx hidxA hnc hab hac hge
    have : Asum D idx (P.v (k + 1)) = Real.pi := hsum
    rw [hcA] at this
    rcases hPang (k + 1) with h | h <;> (rw [h] at this; linarith)
  -- the sum over all vertices
  have hsum0 : ∑ v ∈ V, (6 * (out v : ℤ) - 6 * (inn v : ℤ) + 2 * (cnt D idx v 0 : ℤ) - 2 * (cnt D idx v 2 : ℤ)) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      hbal, hs0, hs2]
    ring
  set C : Finset Plane := Finset.univ.image (fun k : Fin M => P.v (k + 1)) with hC
  have hCsub : C ⊆ V := by
    intro v hv
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hv
    exact (hcorner k).1
  have hinj : Function.Injective (fun k : Fin M => P.v (k + 1)) := fun k k' h => by
    have := polyV_injective P h
    simpa using this
  set f : Plane → ℤ := fun v => 6 * (out v : ℤ) - 6 * (inn v : ℤ) + 2 * (cnt D idx v 0 : ℤ) - 2 * (cnt D idx v 2 : ℤ) with hfdef
  have hnonc : ∀ v ∈ V \ C, 0 ≤ f v := by
    intro v hv
    refine hf v (Finset.mem_sdiff.mp hv).1 (fun k hk => (Finset.mem_sdiff.mp hv).2 ?_)
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk.symm⟩
  have hsplit : ∑ v ∈ V \ C, f v + ∑ v ∈ C, f v = ∑ v ∈ V, f v := Finset.sum_sdiff hCsub
  have hge : ∑ v ∈ C, f v ≤ 0 := by
    have h0 : 0 ≤ ∑ v ∈ V \ C, f v := Finset.sum_nonneg hnonc
    have : ∑ v ∈ V, f v = 0 := hsum0
    linarith
  rw [hC, Finset.sum_image (fun k _ k' _ h => hinj h)] at hge
  -- on corners f = 6 out + g >= g
  have hcor : ∀ k : Fin M, 2 * (cnt D idx (P.v (k + 1)) 0 : ℤ) - 2 * (cnt D idx (P.v (k + 1)) 2 : ℤ) ≤ f (P.v (k + 1)) := by
    intro k
    simp only [hfdef]
    rw [(hcorner k).2.1]
    have : (0 : ℤ) ≤ out (P.v (k + 1)) := Nat.cast_nonneg _
    push_cast
    linarith
  have hge2 : ∑ k : Fin M, (2 * (cnt D idx (P.v (k + 1)) 0 : ℤ) - 2 * (cnt D idx (P.v (k + 1)) 2 : ℤ)) ≤ 0 :=
    le_trans (Finset.sum_le_sum fun k _ => hcor k) hge
  -- the polygon angle sum
  have hmsum : ∑ k : Fin M, ((cnt D idx (P.v (k + 1)) 0 + 2 * cnt D idx (P.v (k + 1)) 2 : ℕ) : ℤ) = 3 * ((M : ℤ) - 2) := by
    have hR : ∑ k : Fin M, (((cnt D idx (P.v (k + 1)) 0 + 2 * cnt D idx (P.v (k + 1)) 2 : ℕ) : ℝ) * (Real.pi / 3)) = ((M - 2 : ℕ) : ℝ) * Real.pi := by
      rw [Finset.sum_congr rfl (fun k _ => (hcorner k).2.2)]
      rw [← poly_angle_sum P]
      exact Equiv.sum_comp (Equiv.addRight (1 : Fin M)) (fun i => P.angle i)
    rw [← Finset.sum_mul] at hR
    have hM3 : 3 ≤ M := P.three_le
    have hR2 : (∑ k : Fin M, ((cnt D idx (P.v (k + 1)) 0 + 2 * cnt D idx (P.v (k + 1)) 2 : ℕ) : ℝ)) = 3 * ((M : ℝ) - 2) := by
      have hMr : ((M - 2 : ℕ) : ℝ) = (M : ℝ) - 2 := by rw [Nat.cast_sub (by omega)]; norm_num
      rw [hMr] at hR
      have := mul_right_cancel₀ (by positivity : (Real.pi / 3) ≠ 0) (show (∑ k : Fin M, ((cnt D idx (P.v (k + 1)) 0 + 2 * cnt D idx (P.v (k + 1)) 2 : ℕ) : ℝ)) * (Real.pi / 3) = (3 * ((M : ℝ) - 2)) * (Real.pi / 3) by
        rw [hR]; ring)
      exact this
    have : ((∑ k : Fin M, ((cnt D idx (P.v (k + 1)) 0 + 2 * cnt D idx (P.v (k + 1)) 2 : ℕ) : ℤ) : ℤ) : ℝ) = ((3 * ((M : ℤ) - 2) : ℤ) : ℝ) := by
      push_cast
      push_cast at hR2
      exact hR2
    exact_mod_cast this
  have key : ∑ k : Fin M, (2 * (cnt D idx (P.v (k + 1)) 0 : ℤ) - 2 * (cnt D idx (P.v (k + 1)) 2 : ℤ)) =
      2 * (3 * ((M : ℤ) - 2)) - 6 * ∑ k : Fin M, (cnt D idx (P.v (k + 1)) 2 : ℤ) := by
    rw [← hmsum]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [key] at hge2
  omega

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.bz_count_poly
