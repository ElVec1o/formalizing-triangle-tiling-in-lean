-- Draft/LaczFormalIVcPhi.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (IVc, alpha/pi irrational): the flux of the polygon vanishes, for the tile (alpha, 2pi/3 - alpha, pi/3).
--   `ivc_interior_pairs_cancel`, `ivc_edge_len_mem`, `ivc_sideEdges_all_or_none`, `ivc_flux_zero` : the IIIc theorems of LaczFormalIIIcPair/Side/Phi redone for IVcData
--   (angle pi/3 at the vertex opposite c; the flux of a tile is weight(c-edge) * (c - a - b), so the final cancellation is (a + b) * kt = 0, no a != b needed).
-- Generated from the IIIc files by textual substitution (TwoPiThreeData -> IVcData, 2pi/3 -> pi/3 at gamma, c + a - b -> c - a - b) and then built.
-- NOTE, UNAUDITED.  Non-vacuity: NAMED only (hypotheses: regular PolyTiling, tile data IVcData with alpha/pi irrational, a,b commensurable, c not).
-- Credit: Laczkovich (DCG 48 (2012), Sect. 8.3, 7.3, Lemmas 4.5-4.8), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIIcPhi
import Erdos634.Draft.LaczFormalIVcData

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.Draft.LaczFormal.RG

namespace Erdos634.Draft.LaczFormal.IIIc

/-- **(d1) Interior c-pairs cancel.**  `Bd i` says the open `c`-side of tile `i` contains no interior point of the polygon.  The sum of all tile fluxes (weight anchored at `θ₀`) equals the
sum over the tiles with `Bd i`: the others come in Lemma-4.8 pairs (an involution), each pair of total flux `0`. -/
theorem ivc_interior_pairs_cancel {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) {α : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hmodel : T.C.model.IVcData α (slen T.C 0) (slen T.C 1) (slen T.C 2))
    (hab : Comm (slen T.C 0) (slen T.C 1)) (hac : ¬ Comm (slen T.C 0) (slen T.C 2)) (θ₀ : Real.Angle)
    (kg : Fin N → Fin 3) (hkg : ∀ i, (T.C.tile i).angleAt (kg i) = Real.pi / 3) :
    ∑ i, (T.C.tile i).flux (fAlphaAt α hα θ₀).weight =
      ∑ i ∈ Finset.univ.filter (fun i => ∀ m ∈ openSegment ℝ (eU (T.C.tile i) (kg i + 1)) (eV (T.C.tile i) (kg i + 1)), m ∉ interior T.C.region),
        (T.C.tile i).flux (fAlphaAt α hα θ₀).weight := by
  classical
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hT : ∀ i, (T.C.tile i).IVcData α (slen T.C 0) (slen T.C 1) (slen T.C 2) :=
    fun i => Tri.IVcData.of_congruent (T.C.tiles_congruent i) hmodel
  have hca : slen T.C 2 ≠ slen T.C 0 := by
    intro h; apply hac; exact ⟨1, 1, one_pos, one_pos, by rw [h]⟩
  have hcb : slen T.C 2 ≠ slen T.C 1 := by
    intro h; apply hac
    obtain ⟨p, q, hp, hq, hpq⟩ := hab
    exact ⟨p, q, hp, hq, by rw [h]; exact hpq⟩
  set Bd : Fin N → Prop := fun i => ∀ m ∈ openSegment ℝ (eU (T.C.tile i) (kg i + 1)) (eV (T.C.tile i) (kg i + 1)), m ∉ interior T.C.region with hBd
  set f : Fin N → ℝ := fun i => (T.C.tile i).flux (fAlphaAt α hα θ₀).weight with hf
  have hdist : ∀ i, dist (eU (T.C.tile i) (kg i + 1)) (eV (T.C.tile i) (kg i + 1)) = slen T.C 2 := by
    intro i; rw [dist_eUV]; exact ivc_cedge_dist hα (hT i) (kg i) (hkg i)
  have hpart : ∀ i, ¬ Bd i → ∃ j, j ≠ i ∧
      TriStep (T.C.tile j) (neg2 (toV2 (eV (T.C.tile i) (kg i + 1) - eU (T.C.tile i) (kg i + 1)))) (eV (T.C.tile i) (kg i + 1)) (eU (T.C.tile i) (kg i + 1)) := by
    intro i hi
    simp only [hBd, not_forall] at hi
    obtain ⟨m, hm, hmi⟩ := hi
    exact polytiling_lemma48 T hreg hab hac (triStep_edge _ _) (hdist i) hm (not_not.mp hmi)
  -- the interior tiles sum to zero
  have hI : ∑ i ∈ Finset.univ.filter (fun i => ¬ Bd i), f i = 0 := by
    refine Finset.sum_involution (fun i hi => Classical.choose (hpart i (Finset.mem_filter.mp hi).2)) ?_ ?_ ?_ ?_
    · intro i hi
      have hs := (Classical.choose_spec (hpart i (Finset.mem_filter.mp hi).2)).2
      exact ivc_pair_flux_zero hα (hT i) (hT _) hca hcb θ₀ (triStep_edge _ _) hs (hdist i)
    · intro i hi _
      exact (Classical.choose_spec (hpart i (Finset.mem_filter.mp hi).2)).1
    · intro i hi
      have hi' := (Finset.mem_filter.mp hi).2
      have hs := (Classical.choose_spec (hpart i hi')).2
      set j := Classical.choose (hpart i hi')
      obtain ⟨h1, h2⟩ := ivc_triStep_cedge hα (hT j) hca hcb (kg j) (hkg j) hs (by rw [dist_comm]; exact hdist i)
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hj => hi' ?_⟩
      intro m hm hmi
      apply hj m _ hmi
      rw [← h1, ← h2, openSegment_symm]; exact hm
    · intro i hi
      have hi' := (Finset.mem_filter.mp hi).2
      have hs := (Classical.choose_spec (hpart i hi')).2
      set j := Classical.choose (hpart i hi') with hjdef
      obtain ⟨h1, h2⟩ := ivc_triStep_cedge hα (hT j) hca hcb (kg j) (hkg j) hs (by rw [dist_comm]; exact hdist i)
      have hj' : ¬ Bd j := by
        intro hj; apply hi'
        intro m hm hmi
        apply hj m _ hmi
        rw [← h1, ← h2, openSegment_symm]; exact hm
      have hs2 := (Classical.choose_spec (hpart j hj')).2
      set k := Classical.choose (hpart j hj')
      rw [← h1, ← h2] at hs2
      have hd : neg2 (toV2 (eU (T.C.tile i) (kg i + 1) - eV (T.C.tile i) (kg i + 1))) = toV2 (eV (T.C.tile i) (kg i + 1) - eU (T.C.tile i) (kg i + 1)) := by
        ext <;> simp [neg2, toV2]
      rw [hd] at hs2
      exact (left_step_unique T.C.toRegionDissection hs2 (triStep_edge (T.C.tile i) (kg i + 1))).1
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ Bd f, hI, add_zero]

/-- Every tile edge of a placement of the tile has length `a`, `b` or `c`. -/
theorem ivc_edge_len_mem {T : Tri} {α a b c : ℝ} (h : T.IVcData α a b c) (k : Fin 3) :
    dist (T.pts k) (T.pts (k + 1)) = a ∨ dist (T.pts k) (T.pts (k + 1)) = b ∨ dist (T.pts k) (T.pts (k + 1)) = c := by
  have e : T.oppLen (k + 2) = dist (T.pts k) (T.pts (k + 1)) := by
    unfold Tri.oppLen
    have e1 : k + 2 + 1 = k := by fin_cases k <;> rfl
    have e2 : k + 2 + 2 = k + 1 := by fin_cases k <;> rfl
    rw [e1, e2]
  rw [← e]
  rcases h.cases (k + 2) with ⟨-, h1⟩ | ⟨-, h2⟩ | ⟨-, h3⟩
  · exact Or.inr (Or.inr h1)
  · exact Or.inl h2
  · exact Or.inr (Or.inl h3)

/-- **(d2) all-or-none on the boundary.**  Either every tile edge on every side of `A` has length `c`, or none has. -/
theorem ivc_sideEdges_all_or_none {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) {α : ℝ}
    (hmodel : T.C.model.IVcData α (slen T.C 0) (slen T.C 1) (slen T.C 2))
    (hab : Comm (slen T.C 0) (slen T.C 1)) (hac : ¬ Comm (slen T.C 0) (slen T.C 2)) :
    (∀ j, ∀ e ∈ T.P.sideEdges T.C.toRegionDissection j, T.C.toRegionDissection.eLen e = slen T.C 2) ∨
    (∀ j, ∀ e ∈ T.P.sideEdges T.C.toRegionDissection j, T.C.toRegionDissection.eLen e ≠ slen T.C 2) := by
  classical
  obtain ⟨idx, hA, hcnt⟩ := hreg
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hC : CaseC T.C idx := ⟨RG.idx_dist_of_angle T.C idx hA, hA, fun X => hcnt X, RG.notComb_c_of_comm (RG.slen_pos T.C 2) hab hac⟩
  have hT : ∀ i, (T.C.tile i).IVcData α (slen T.C 0) (slen T.C 1) (slen T.C 2) :=
    fun i => Tri.IVcData.of_congruent (T.C.tiles_congruent i) hmodel
  have ha := RG.slen_pos T.C 0
  have hb := RG.slen_pos T.C 1
  have hc := RG.slen_pos T.C 2
  have hdec : ∀ j, ∃ (nc : ℕ) (S : ℝ), T.P.side j = nc * slen T.C 2 + S ∧ (S = 0 ∨ (0 < S ∧ Comm S (slen T.C 0))) ∧
      ((∃ e ∈ T.P.sideEdges T.C.toRegionDissection j, T.C.toRegionDissection.eLen e = slen T.C 2) → 0 < nc) ∧
      ((∃ e ∈ T.P.sideEdges T.C.toRegionDissection j, T.C.toRegionDissection.eLen e ≠ slen T.C 2) → 0 < S ∧ Comm S (slen T.C 0)) := by
    intro j
    obtain ⟨nc, S, h1, h2, h3, h4⟩ := iiic_sum_decomp (T.P.sideEdges T.C.toRegionDissection j) T.C.toRegionDissection.eLen ha hb hab
      (fun e _ => ivc_edge_len_mem (hT e.1) e.2)
    exact ⟨nc, S, by rw [← T.P.side_len_sum T.C.toRegionDissection T.region_eq j]; exact h1, h2, h3, h4⟩
  rcases polygon_sides_alike T.C idx hC T.P T.region_eq with hA' | hB'
  · left
    intro j e he
    by_contra hne
    obtain ⟨m, hm, hside⟩ := hA' j
    obtain ⟨nc, S, h1, h2, h3, h4⟩ := hdec j
    obtain ⟨hSpos, hSc⟩ := h4 ⟨e, he, hne⟩
    rw [hside] at h1
    have hmn : nc < m := by
      by_contra hcon
      push Not at hcon
      have : (m : ℝ) ≤ nc := by exact_mod_cast hcon
      nlinarith
    apply hac
    have hS : S = ((m - nc : ℕ) : ℝ) * slen T.C 2 := by
      rw [Nat.cast_sub hmn.le]; linarith
    rw [hS] at hSc
    have := iiic_comm_nsmul (m - nc) (Nat.sub_pos_of_lt hmn) (a := slen T.C 0) hSc
    obtain ⟨p, q, hp, hq, h⟩ := this
    exact ⟨q, p, hq, hp, h.symm⟩
  · right
    intro j e he hec
    obtain ⟨na, nb, hpos, hside⟩ := hB' j
    obtain ⟨nc, S, h1, h2, h3, h4⟩ := hdec j
    have hncpos := h3 ⟨e, he, hec⟩
    have hZc : Comm (T.P.side j) (slen T.C 0) := by rw [hside]; exact comm_comb hab na nb hpos
    have hnc : (0 : ℝ) < nc := by exact_mod_cast hncpos
    have hxy : T.P.side j - S = nc * slen T.C 2 := by linarith
    have hpos' : 0 < T.P.side j - S := by rw [hxy]; positivity
    have hcomm : Comm ((nc : ℝ) * slen T.C 2) (slen T.C 0) := by
      rw [← hxy]
      rcases h2 with h0 | ⟨_, hSc⟩
      · rw [h0, sub_zero]; exact hZc
      · exact iiic_comm_sub ha hZc hSc hpos'
    have := iiic_comm_nsmul nc hncpos hcomm
    obtain ⟨p, q, hp, hq, h⟩ := this
    exact hac ⟨q, p, hq, hp, h.symm⟩

set_option maxHeartbeats 800000 in
/-- **(d2)+(d3a): the polygon flux of the weight anchored at ANY `θ₀` is `0`** (in particular `Phi(A) = 0`, `iiic_phi_zero`). -/
theorem ivc_flux_zero {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) {α : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hmodel : T.C.model.IVcData α (slen T.C 0) (slen T.C 1) (slen T.C 2))
    (hab : Comm (slen T.C 0) (slen T.C 1)) (hac : ¬ Comm (slen T.C 0) (slen T.C 2)) (θ₀ : Real.Angle) :
    T.P.flux (fAlphaAt α hα θ₀).weight = 0 := by
  classical
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hT : ∀ i, (T.C.tile i).IVcData α (slen T.C 0) (slen T.C 1) (slen T.C 2) :=
    fun i => Tri.IVcData.of_congruent (T.C.tiles_congruent i) hmodel
  have hca : slen T.C 2 ≠ slen T.C 0 := by
    intro h; apply hac; exact ⟨1, 1, one_pos, one_pos, by rw [h]⟩
  have hcb : slen T.C 2 ≠ slen T.C 1 := by
    intro h; apply hac
    obtain ⟨p, q, hp, hq, hpq⟩ := hab
    exact ⟨p, q, hp, hq, by rw [h]; exact hpq⟩
  choose kg hkg' using fun i => (hT i).gamma_unique hα
  have hkg : ∀ i, (T.C.tile i).angleAt (kg i) = Real.pi / 3 := fun i => (hkg' i).1
  set R := T.C.toRegionDissection with hR
  set w := (fAlphaAt α hα θ₀).weight with hw
  set K := slen T.C 2 - slen T.C 0 - slen T.C 1 with hK
  have hAdd : ∑ i, (T.C.tile i).flux w = T.P.flux w := T.P.flux_cancel R T.region_eq _ (fAlphaAt α hα θ₀).weight_odd
  have hCancel := ivc_interior_pairs_cancel T hreg hα hmodel hab hac θ₀ kg hkg
  set B := Finset.univ.filter (fun i => ∀ m ∈ openSegment ℝ (eU (T.C.tile i) (kg i + 1)) (eV (T.C.tile i) (kg i + 1)), m ∉ interior T.C.region) with hB
  have hflux : ∀ i, (T.C.tile i).flux w = w (R.eDir (i, kg i + 1)) * K := fun i =>
    (T.C.tile i).flux_cedge_ivc hα (hT i) θ₀ (kg i) (hkg i)
  have hsucc : ∀ j : Fin 3, j ≠ j + 1 := by decide
  -- a boundary c-tile has its c-edge on a side
  have hBside : ∀ i ∈ B, ∃ j, (i, kg i + 1) ∈ T.P.sideEdges R j := by
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    have hpts : (T.C.tile i).pts (kg i + 1) ≠ (T.C.tile i).pts (kg i + 1 + 1) := fun h => hsucc _ ((T.C.tile i).indep.injective h)
    obtain ⟨hxT, hxa, hxb⟩ := mem_ne_ends_of_avg hpts (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
    have hxn : ((1:ℝ)/2) • (T.C.tile i).pts (kg i + 1) + ((1:ℝ)/2) • (T.C.tile i).pts (kg i + 1 + 1) ∉ interior T.P.carrier := by
      rw [← T.region_eq]
      apply hi'
      rw [openSegment_eUV]
      exact ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, rfl⟩
    obtain ⟨j, hj⟩ := T.P.edge_on_side R T.region_eq (i, kg i + 1) hxT hxa hxb hxn
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  have hcl : ∀ i, R.eLen (i, kg i + 1) = slen T.C 2 := fun i => ivc_cedge_dist hα (hT i) (kg i) (hkg i)
  rcases ivc_sideEdges_all_or_none T hreg hmodel hab hac with hall | hnone
  · -- every side edge is a c-edge
    have hE : ∀ j, ∀ e ∈ T.P.sideEdges R j, e.2 = kg e.1 + 1 := by
      intro j e he
      exact ivc_cedge_index hα (hT e.1) hca hcb (kg e.1) (hkg e.1) e.2 (hall j e he)
    have hBmem : ∀ j, ∀ e ∈ T.P.sideEdges R j, e.1 ∈ B := by
      intro j e he
      have hsub : R.eSet e ⊆ T.P.sideSet j := (Finset.mem_filter.mp he).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun m hm hmi => ?_⟩
      rw [openSegment_eUV] at hm
      have hm' : m ∈ R.eSet e := by
        have : e = (e.1, kg e.1 + 1) := Prod.ext rfl (hE j e he)
        rw [this]
        exact openSegment_subset_segment ℝ _ _ hm
      rw [T.region_eq] at hmi
      exact T.P.not_interior_of_sideSet (hsub hm') hmi
    set g : Fin N × Fin 3 → ℝ := fun e => w (R.eDir e) with hg
    have hBE : B.image (fun i => (i, kg i + 1)) = Finset.univ.biUnion (fun j => T.P.sideEdges R j) := by
      ext e
      simp only [Finset.mem_image, Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact hBside i hi
      · rintro ⟨j, hj⟩
        exact ⟨e.1, hBmem j e hj, (Prod.ext rfl (hE j e hj).symm)⟩
    have hinj : Function.Injective (fun i : Fin N => (i, kg i + 1)) := fun i i' h => congrArg Prod.fst h
    have hsumB : ∑ i ∈ B, (T.C.tile i).flux w = K * ∑ j, ((T.P.sideEdges R j).card : ℝ) * w (T.P.sideDir j) := by
      have h1 : ∑ i ∈ B, (T.C.tile i).flux w = ∑ i ∈ B, g (i, kg i + 1) * K := Finset.sum_congr rfl (fun i _ => hflux i)
      rw [h1, ← Finset.sum_mul, ← Finset.sum_image (f := g) (g := fun i => (i, kg i + 1)) (fun x _ y _ h => hinj h), hBE,
        Finset.sum_biUnion (fun j _ j' _ hjj' => T.P.sideEdges_disjoint R hjj')]
      rw [mul_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      have hsc : ∑ e ∈ T.P.sideEdges R j, w (R.eDir e) = ∑ e ∈ T.P.sideEdges R j, w (T.P.sideDir j) :=
        Finset.sum_congr rfl (fun e he => congrArg w (T.P.eDir_of_side R T.region_eq (Finset.mem_filter.mp he).2))
      rw [hsc, Finset.sum_const, nsmul_eq_mul]
    have hside : ∀ j, T.P.side j = ((T.P.sideEdges R j).card : ℝ) * slen T.C 2 := by
      intro j
      rw [← T.P.side_len_sum R T.region_eq j, Finset.sum_congr rfl (fun e he => hall j e he), Finset.sum_const, nsmul_eq_mul]
    have hPhi : T.P.flux w = slen T.C 2 * ∑ j, ((T.P.sideEdges R j).card : ℝ) * w (T.P.sideDir j) := by
      unfold ConvPoly.flux
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [hside j, smul_eq_mul]; ring
    set kt := ∑ j, ((T.P.sideEdges R j).card : ℝ) * w (T.P.sideDir j) with hkt
    have heq : T.P.flux w = K * kt := by rw [← hAdd, hCancel, hsumB]
    have h0 : (slen T.C 0 + slen T.C 1) * kt = 0 := by
      have := hPhi.symm.trans heq
      rw [hK] at this
      linarith
    have hkt0 : kt = 0 := (mul_eq_zero.mp h0).resolve_left (add_pos (RG.slen_pos T.C 0) (RG.slen_pos T.C 1)).ne'
    rw [hPhi, hkt0, mul_zero]
  · -- no side edge is a c-edge: no boundary c-tile
    have hB0 : ∑ i ∈ B, (T.C.tile i).flux w = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      obtain ⟨j, hj⟩ := hBside i hi
      exact absurd (hcl i) (hnone j _ hj)
    rw [← hAdd, hCancel, hB0]


end Erdos634.Draft.LaczFormal.IIIc

#print axioms Erdos634.Draft.LaczFormal.IIIc.ivc_interior_pairs_cancel
#print axioms Erdos634.Draft.LaczFormal.IIIc.ivc_sideEdges_all_or_none
#print axioms Erdos634.Draft.LaczFormal.IIIc.ivc_flux_zero
