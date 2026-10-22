-- Draft/LaczFormalBZDefects.lean -- the DEFECT INEQUALITY for Cases IIIa/IIIb of Laczkovich's Theorem 2.1 (polygon targets, gamma = 2 pi/3), replacing the false printed Lemma 7.1 (i)-(iii).
-- Proposal: (private working notes, not included) Sect. 2 (audited SOUND WITH GAPS, (private working notes, not included)).  This file is the `bz_count_poly` proof with the slack KEPT:
--   f(v) = 6 out(v) - 6 in(v) + 2 #alpha(v) - 2 #gamma(v) is >= 0 at every non-corner vertex, >= 6 at a non-corner boundary vertex that is a star (3,3,0) or has out >= 1 (in = 0 there by `ga_head_interior`),
--   >= 12 at a double star (6,6,0), >= 6 at a gamma-star (4,4,1); at a corner f >= 2p - 2r + 6 out.  Sum f = 0 then gives
--   `caseIII_defects`:  s_b + 2 S2 + G + B  <=  R - (M - 2)      (= (R - P)/3 since P + 2R = 3 (M - 2)),
-- with s_b = non-corner boundary stars, S2 = double stars, G = gamma-stars, B = total out-degree of Gamma_a at boundary points (corners included), R = sum of the gamma-counts at the corners.
-- Consequences: `poly_noncorner_boundary_type` (a non-corner boundary vertex is a star (3,3,0) or normal (1,1,1)); `caseIII_clean_boundary` (R = M - 2: no boundary star, no out-edge at the boundary,
-- every non-corner boundary vertex has counts (1,1,1)) -- the input of Lemma 4.3.
-- NOTE, UNAUDITED.  Hypotheses = those of `bz_count_poly` (witnessed there/in LaczFormalBZWit; R >= M-2 occurs e.g. for the all-gamma polygons).  Credit: Laczkovich (DCG 48 (2012), Sect. 4, 7), Beeson-Zhang (arXiv 2604.01314), Beeson.
import Erdos634.Draft.LaczFormalBZ4b

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- The edge set of `Γ_a` (`a = slen D 0`) on the vertex set, as a finset of pairs of points. -/
noncomputable def gaEdgeSet (D : CongruentRegionDissection N) : Finset (Plane × Plane) :=
  (vtxSet D.toRegionDissection ×ˢ vtxSet D.toRegionDissection).filter (fun e => GaEdge D.toRegionDissection (slen D 0) e.1 e.2)

/-- Out-degree of `Γ_a` at the point `v`. -/
noncomputable def gaOut (D : CongruentRegionDissection N) (v : Plane) : ℕ := ((gaEdgeSet D).filter (fun e => e.1 = v)).card

/-- Not a corner of the polygon. -/
def IsNonCorner (P : ConvPoly M) (v : Plane) : Prop := ∀ k : Fin M, v ≠ P.v (k + 1)

/-- `s_b`: non-corner vertices on the boundary (not interior points of the region) with counts `(3,*,0)`: boundary stars. -/
noncomputable def defSb (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (P : ConvPoly M) : ℕ :=
  ((vtxSet D.toRegionDissection).filter (fun v => IsNonCorner P v ∧ v ∉ interior D.region ∧ cnt D idx v 0 = 3 ∧ cnt D idx v 2 = 0)).card

/-- `S2`: double stars `(6,*,0)` (non-corner). -/
noncomputable def defS2 (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (P : ConvPoly M) : ℕ :=
  ((vtxSet D.toRegionDissection).filter (fun v => IsNonCorner P v ∧ cnt D idx v 0 = 6 ∧ cnt D idx v 2 = 0)).card

/-- `G`: gamma-stars `(4,*,1)` (non-corner). -/
noncomputable def defG (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (P : ConvPoly M) : ℕ :=
  ((vtxSet D.toRegionDissection).filter (fun v => IsNonCorner P v ∧ cnt D idx v 0 = 4 ∧ cnt D idx v 2 = 1)).card

/-- `B`: total out-degree of `Γ_a` at the corners of the polygon plus at the non-corner boundary vertices. -/
noncomputable def defB (D : CongruentRegionDissection N) (P : ConvPoly M) : ℕ :=
  (∑ k : Fin M, gaOut D (P.v (k + 1))) +
    ∑ v ∈ (vtxSet D.toRegionDissection).filter (fun v => IsNonCorner P v ∧ v ∉ interior D.region), gaOut D v

/-- The weight of a vertex in the defect count. -/
noncomputable def defW (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (P : ConvPoly M) (v : Plane) : ℤ :=
  (if IsNonCorner P v ∧ v ∉ interior D.region ∧ cnt D idx v 0 = 3 ∧ cnt D idx v 2 = 0 then 1 else 0)
  + 2 * (if IsNonCorner P v ∧ cnt D idx v 0 = 6 ∧ cnt D idx v 2 = 0 then 1 else 0)
  + (if IsNonCorner P v ∧ cnt D idx v 0 = 4 ∧ cnt D idx v 2 = 1 then 1 else 0)
  + (if IsNonCorner P v ∧ v ∉ interior D.region then (gaOut D v : ℤ) else 0)

/-- **The defect inequality** (Cases IIIa/IIIb, polygon targets, `γ = 2π/3`): `s_b + 2 S2 + G + B ≤ R - (M-2)`.
Same hypotheses as `bz_count_poly`, whose conclusion `0 ≤ R - (M-2)` is the case of all defects dropped. -/
theorem caseIII_defects (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2))
    (hγ : D.model.angleAt 2 = 2 * Real.pi / 3) (hαβ : D.model.angleAt 0 + D.model.angleAt 1 = Real.pi / 3)
    (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1) (hPang : ∀ i, P.angle i = Real.pi / 3 ∨ P.angle i = 2 * Real.pi / 3) :
    ((defSb D idx P : ℕ) : ℤ) + 2 * (defS2 D idx P : ℤ) + (defG D idx P : ℤ) + (defB D P : ℤ)
      ≤ (∑ k : Fin M, (cnt D idx (P.v (k + 1)) 2 : ℤ)) - ((M : ℤ) - 2) := by
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
  set E : Finset (Plane × Plane) := gaEdgeSet D with hE
  let out : Plane → ℕ := fun v => (E.filter (fun e => e.1 = v)).card
  let inn : Plane → ℕ := fun v => (E.filter (fun e => e.2 = v)).card
  have hout : ∀ v, out v = gaOut D v := fun v => rfl
  have hEmem : ∀ e : Plane × Plane, e ∈ E ↔ GaEdge D.toRegionDissection (slen D 0) e.1 e.2 := by
    intro e
    simp only [hE, gaEdgeSet, Finset.mem_filter, Finset.mem_product]
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
  -- a head is an interior point
  have hinnI : ∀ v, v ∉ interior D.region → inn v = 0 := by
    intro v hv
    by_contra hne
    obtain ⟨e, he⟩ := Finset.card_pos.mp (by simp only [inn] at hne ⊢; omega : 0 < (E.filter (fun e => e.2 = v)).card)
    simp only [Finset.mem_filter] at he
    have hge := (hEmem e).mp he.1
    rw [he.2] at hge
    exact hv (ga_head_interior D idx hidx hnc hge)
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
  set f : Plane → ℤ := fun v => 6 * (out v : ℤ) - 6 * (inn v : ℤ) + 2 * (cnt D idx v 0 : ℤ) - 2 * (cnt D idx v 2 : ℤ) with hfdef
  -- the per-vertex bound at non-corner vertices: f >= 6 w
  have hfw : ∀ v ∈ V, IsNonCorner P v → 6 * defW D idx P v ≤ f v := by
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
    have hF1 : inn v = 1 → cnt D idx v 0 + 2 * cnt D idx v 2 = 3 := fun h => (F1 v hv h).1
    have hF1s : inn v = 1 → cnt D idx v 0 = 1 → cnt D idx v 2 = 1 → 1 ≤ out v := fun h => (F1 v hv h).2
    have hov : (out v : ℤ) = (gaOut D v : ℤ) := rfl
    by_cases hI : v ∈ interior D.region
    · simp only [defW, hnk, hI, not_true_eq_false, false_and, true_and, if_false, hfdef]
      split_ifs <;> omega
    · have hin0 := hinnI v hI
      have hm3 : cnt D idx v 0 + 2 * cnt D idx v 2 = 3 := by
        rcases htype with ⟨hi, -⟩ | h
        · exact absurd hi hI
        · exact h
      simp only [defW, hnk, hI, not_false_eq_true, true_and, hfdef]
      split_ifs <;> omega
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
  have hsum0 : ∑ v ∈ V, f v = 0 := by
    simp only [hfdef]
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
  have hwC : ∀ v ∈ C, defW D idx P v = 0 := by
    intro v hv
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hv
    have : ¬ IsNonCorner P (P.v (k + 1)) := fun h => h k rfl
    simp [defW, this]
  set g : Plane → ℤ := fun v => f v - 6 * defW D idx P v with hgdef
  have hnonc : ∀ v ∈ V \ C, 0 ≤ g v := by
    intro v hv
    have hnk : IsNonCorner P v := fun k hk => (Finset.mem_sdiff.mp hv).2 (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk.symm⟩)
    have := hfw v (Finset.mem_sdiff.mp hv).1 hnk
    simp only [hgdef]; linarith
  have hsplit : ∑ v ∈ V \ C, g v + ∑ v ∈ C, g v = ∑ v ∈ V, g v := Finset.sum_sdiff hCsub
  have hsumg : ∑ v ∈ V, g v = - 6 * ∑ v ∈ V, defW D idx P v := by
    simp only [hgdef]
    rw [Finset.sum_sub_distrib, hsum0, ← Finset.mul_sum]; ring
  have hge : ∑ v ∈ C, g v ≤ - 6 * ∑ v ∈ V, defW D idx P v := by
    have h0 : 0 ≤ ∑ v ∈ V \ C, g v := Finset.sum_nonneg hnonc
    linarith
  have hgC : ∑ v ∈ C, g v = ∑ v ∈ C, f v := by
    refine Finset.sum_congr rfl fun v hv => ?_
    simp only [hgdef, hwC v hv]; ring
  rw [hgC, hC, Finset.sum_image (fun k _ k' _ h => hinj h)] at hge
  -- on corners f = 6 out + g >= g
  have hcor : ∀ k : Fin M, 2 * (cnt D idx (P.v (k + 1)) 0 : ℤ) - 2 * (cnt D idx (P.v (k + 1)) 2 : ℤ) + 6 * (gaOut D (P.v (k + 1)) : ℤ) ≤ f (P.v (k + 1)) := by
    intro k
    simp only [hfdef]
    rw [(hcorner k).2.1]
    have hov : (out (P.v (k + 1)) : ℤ) = (gaOut D (P.v (k + 1)) : ℤ) := rfl
    push_cast
    linarith
  have hge2 : ∑ k : Fin M, (2 * (cnt D idx (P.v (k + 1)) 0 : ℤ) - 2 * (cnt D idx (P.v (k + 1)) 2 : ℤ) + 6 * (gaOut D (P.v (k + 1)) : ℤ))
      ≤ - 6 * ∑ v ∈ V, defW D idx P v :=
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
  have key : ∑ k : Fin M, (2 * (cnt D idx (P.v (k + 1)) 0 : ℤ) - 2 * (cnt D idx (P.v (k + 1)) 2 : ℤ) + 6 * (gaOut D (P.v (k + 1)) : ℤ)) =
      2 * (3 * ((M : ℤ) - 2)) - 6 * ∑ k : Fin M, (cnt D idx (P.v (k + 1)) 2 : ℤ) + 6 * ∑ k : Fin M, (gaOut D (P.v (k + 1)) : ℤ) := by
    rw [← hmsum]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  -- the sum of the weights
  have hW : ∑ v ∈ V, defW D idx P v = (defSb D idx P : ℤ) + 2 * (defS2 D idx P : ℤ) + (defG D idx P : ℤ)
      + ∑ v ∈ V.filter (fun v => IsNonCorner P v ∧ v ∉ interior D.region), (gaOut D v : ℤ) := by
    simp only [defW]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_boole, Finset.sum_boole,
      ← Finset.sum_filter]
    simp only [defSb, defS2, defG]
    rfl
  have hB : (defB D P : ℤ) = ∑ k : Fin M, (gaOut D (P.v (k + 1)) : ℤ) + ∑ v ∈ V.filter (fun v => IsNonCorner P v ∧ v ∉ interior D.region), (gaOut D v : ℤ) := by
    simp only [defB]; push_cast; rfl
  rw [key, hW] at hge2
  rw [hB]
  linarith

/-- Gap 3 of the audit: a non-corner BOUNDARY vertex (not an interior point of the region) is a star `(3,3,0)` or normal `(1,1,1)`. -/
theorem poly_noncorner_boundary_type (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hγ : D.model.angleAt 2 = 2 * Real.pi / 3) (hαβ : D.model.angleAt 0 + D.model.angleAt 1 = Real.pi / 3)
    (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1) {v : Plane} (hv : v ∈ vtxSet D.toRegionDissection)
    (hnk : IsNonCorner P v) (hI : v ∉ interior D.region) :
    (cnt D idx v 0 = 3 ∧ cnt D idx v 1 = 3 ∧ cnt D idx v 2 = 0) ∨ (cnt D idx v 0 = 1 ∧ cnt D idx v 1 = 1 ∧ cnt D idx v 2 = 1) := by
  have hvert : ∃ j k, (D.tile j).pts k = v := mem_vtxSet.mp hv
  have htype := vertex_type_poly D P hreg idx hidxA hγ hαβ hregc hvert hnk
  have h1 := hregc v
  rcases htype with ⟨hi, -⟩ | h
  · exact absurd hi hI
  · omega

/-- **Clean boundary** (the input of Lemma 4.3): if `R = M - 2` (the corners carry exactly `M - 2` gamma's; the equality case of `caseIII_defects`), then there is no boundary star, no out-edge of `Γ_a`
at any corner or non-corner boundary vertex, and every non-corner boundary vertex has counts `(1,1,1)`. -/
theorem caseIII_clean_boundary (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2))
    (hγ : D.model.angleAt 2 = 2 * Real.pi / 3) (hαβ : D.model.angleAt 0 + D.model.angleAt 1 = Real.pi / 3)
    (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1) (hPang : ∀ i, P.angle i = Real.pi / 3 ∨ P.angle i = 2 * Real.pi / 3)
    (hR : (∑ k : Fin M, (cnt D idx (P.v (k + 1)) 2 : ℤ)) = (M : ℤ) - 2) :
    (∀ k : Fin M, ¬ ∃ H, GaEdge D.toRegionDissection (slen D 0) (P.v (k + 1)) H) ∧
    (∀ v ∈ vtxSet D.toRegionDissection, IsNonCorner P v → v ∉ interior D.region →
      (¬ ∃ H, GaEdge D.toRegionDissection (slen D 0) v H) ∧ cnt D idx v 0 = 1 ∧ cnt D idx v 1 = 1 ∧ cnt D idx v 2 = 1) := by
  have hd := caseIII_defects D P hreg idx hidx hidxA hnc hγ hαβ hregc hPang
  rw [hR] at hd
  have hS : defSb D idx P = 0 := by omega
  have hB0 : defB D P = 0 := by omega
  have hnoout : ∀ v, gaOut D v = 0 → ¬ ∃ H, GaEdge D.toRegionDissection (slen D 0) v H := by
    intro v h ⟨H, hH⟩
    have hmem : (v, H) ∈ (gaEdgeSet D).filter (fun e => e.1 = v) := by
      have := ga_edge_endpoints D.toRegionDissection (slen D 0) hH
      simp only [gaEdgeSet, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨⟨mem_vtxSet.mpr this.1, mem_vtxSet.mpr this.2⟩, hH⟩, trivial⟩
    have : 0 < gaOut D v := Finset.card_pos.mpr ⟨_, hmem⟩
    omega
  simp only [defB, add_eq_zero, Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies] at hB0
  refine ⟨fun k => hnoout _ (hB0.1 k), fun v hv hnk hI => ?_⟩
  refine ⟨hnoout v (hB0.2 v (Finset.mem_filter.mpr ⟨hv, hnk, hI⟩)), ?_⟩
  have hty := poly_noncorner_boundary_type D P hreg idx hidxA hγ hαβ hregc hv hnk hI
  rcases hty with ⟨h0, -, h2⟩ | h
  · exfalso
    have : v ∈ (vtxSet D.toRegionDissection).filter (fun v => IsNonCorner P v ∧ v ∉ interior D.region ∧ cnt D idx v 0 = 3 ∧ cnt D idx v 2 = 0) :=
      Finset.mem_filter.mpr ⟨hv, hnk, hI, h0, h2⟩
    have : 0 < defSb D idx P := Finset.card_pos.mpr ⟨_, this⟩
    omega
  · exact h

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.caseIII_defects
#print axioms Erdos634.Draft.LaczFormal.RG.poly_noncorner_boundary_type
#print axioms Erdos634.Draft.LaczFormal.RG.caseIII_clean_boundary
