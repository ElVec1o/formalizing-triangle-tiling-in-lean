-- Draft/LaczFormalIIIcPair.lean -- Laczkovich DCG 48 (2012), Sect. 7.3 (Subcase IIIc), item (d1): the INTERIOR c-tiles cancel in Phi.
--   `eU`, `eV`, `triStep_edge`  : canonical left-oriented endpoints of tile edge k (tile on the left of eV - eU = leftDir k), and the TriStep they give;
--   `triStep_cedge`             : a TriStep of length c of a placement of the 2pi/3 tile IS its canonical c-edge (kg+1);
--   `iiic_interior_pairs_cancel`: for a regular PolyTiling with a,b commensurable, c not: the sum of the tile fluxes (any anchor) equals the sum over the tiles whose open c-side
--                                 contains NO interior point of the polygon (the involution i -> partner of Lemma 4.8, by `polytiling_lemma48` + `left_step_unique`, and `pair_flux_zero`).
-- This is the printed "Phi(Q_i) = 0 for the pairs", WITHOUT the kite/parallelogram shape and WITHOUT the case split 'Q_i tile A or not': the dichotomy is the filter.
-- NOTE, UNAUDITED.  Non-vacuity: NAMED, not exhibited in Lean: two congruent triangles with irrational alpha, sin(pi/3-alpha)=2 sin alpha (a/b rational, c^2=7a^2/..., c/a=sqrt 7), glued
-- into a parallelogram satisfy every hypothesis; the existing witness vTiling has alpha = pi/6 (rational), so it satisfies the Lemma-4.8 hypotheses but not hα.
-- Credit: Laczkovich (DCG 48 (2012), Sect. 7.3, Lemma 4.8), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIIcFlux
import Erdos634.Draft.LaczFormalRG10Lemma48

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.Draft.LaczFormal.RG

namespace Erdos634.Draft.LaczFormal.IIIc

/-- Start of the left-oriented edge `k`. -/
noncomputable def eU (T : Tri) (k : Fin 3) : Plane := if 0 < T.det then T.pts k else T.pts (k + 1)
/-- End of the left-oriented edge `k`. -/
noncomputable def eV (T : Tri) (k : Fin 3) : Plane := if 0 < T.det then T.pts (k + 1) else T.pts k

theorem eV_sub_eU (T : Tri) (k : Fin 3) : eV T k - eU T k = T.leftDir k := by
  unfold eV eU Tri.leftDir; split_ifs <;> rfl

theorem dist_eUV (T : Tri) (k : Fin 3) : dist (eU T k) (eV T k) = dist (T.pts k) (T.pts (k + 1)) := by
  unfold eU eV; split_ifs
  · rfl
  · exact dist_comm _ _

theorem cross_cyc (T : Tri) (k : Fin 3) :
    (T.pts (k + 1) - T.pts k) 0 * (T.pts (k + 2) - T.pts k) 1 - (T.pts (k + 1) - T.pts k) 1 * (T.pts (k + 2) - T.pts k) 0 = T.det := by
  unfold Tri.det
  fin_cases k <;> simp [Fin.isValue] <;> ring

theorem toV2_ne_zero {w : Plane} (hw : w ≠ 0) : toV2 w ≠ 0 := by
  intro h
  apply hw
  have h0 : w 0 = 0 := congrArg Prod.fst h
  have h1 : w 1 = 0 := congrArg Prod.snd h
  ext i; fin_cases i
  · exact h0
  · exact h1

/-- **The canonical edge step**: tile `T` lies on the left of `eU -> eV` along `eV - eU`. -/
theorem triStep_edge (T : Tri) (k : Fin 3) : TriStep T (toV2 (eV T k - eU T k)) (eU T k) (eV T k) := by
  have hne : toV2 (eV T k - eU T k) ≠ 0 := by
    rw [eV_sub_eU]; exact toV2_ne_zero (T.leftDir_ne_zero k)
  have hpar : Par (toV2 (eV T k - eU T k)) (toV2 (eV T k - eU T k)) :=
    smul_par (c := 1) one_pos hne (Prod.ext (by simp) (by simp))
  by_cases hd : 0 < T.det
  · refine ⟨k, k + 1, k + 2, ?_, ?_, ?_, ?_, ?_, hpar, ?_⟩
    · simp [eU, hd]
    · simp [eV, hd]
    · exact (by decide : ∀ j : Fin 3, j + 1 ≠ j) k
    · exact (by decide : ∀ j : Fin 3, j + 2 ≠ j) k
    · exact (by decide : ∀ j : Fin 3, j + 2 ≠ j + 1) k
    · simp only [eU, eV, if_pos hd]
      simp only [crs, toV2, PiLp.sub_apply]
      have h := cross_cyc T k
      simp only [PiLp.sub_apply] at h
      nlinarith [h]
  · have hdn : T.det < 0 := lt_of_le_of_ne (not_lt.mp hd) T.det_ne_zero
    refine ⟨k + 1, k, k + 2, ?_, ?_, ?_, ?_, ?_, hpar, ?_⟩
    · simp [eU, hd]
    · simp [eV, hd]
    · exact (by decide : ∀ j : Fin 3, j ≠ j + 1) k
    · exact (by decide : ∀ j : Fin 3, j + 2 ≠ j + 1) k
    · exact (by decide : ∀ j : Fin 3, j + 2 ≠ j) k
    · simp only [eU, eV, if_neg hd]
      simp only [crs, toV2, PiLp.sub_apply]
      have h := cross_cyc T k
      simp only [PiLp.sub_apply] at h
      nlinarith [h]

/-- For a placement of the `2pi/3` tile, the `c`-edge `kg+1` has length `c`. -/
theorem cedge_dist {T : Tri} {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) (kg : Fin 3) (hkg : T.angleAt kg = 2 * Real.pi / 3) :
    dist (T.pts (kg + 1)) (T.pts (kg + 1 + 1)) = c := by
  have hr := h.alpha_range
  have hpi := Real.pi_pos
  have ho : T.oppLen kg = c := by
    rcases h.cases kg with ⟨-, h1⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exfalso; rw [hkg] at h1; linarith [hr.1, hr.2]
    · exfalso; rw [hkg] at h1; linarith [hr.1, hr.2]
  have e : kg + 1 + 1 = kg + 2 := by fin_cases kg <;> rfl
  rw [e]; exact ho

/-- **A `TriStep` of length `c` of a placement of the tile is its canonical `c`-edge.** -/
theorem triStep_cedge {T : Tri} {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) (hca : c ≠ a) (hcb : c ≠ b)
    (kg : Fin 3) (hkg : T.angleAt kg = 2 * Real.pi / 3) {d : V2} {U V : Plane} (hS : TriStep T d U V) (hc : dist U V = c) :
    U = eU T (kg + 1) ∧ V = eV T (kg + 1) := by
  obtain ⟨k, hl, hp⟩ := triStep_leftDir hS
  have hdk : dist (T.pts k) (T.pts (k + 1)) = c := by
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact hc
    · rw [h1, h2, dist_comm]; exact hc
  have e := cedge_index h hca hcb kg hkg k hdk
  subst e
  have hv := eV_sub_eU T (kg + 1)
  rw [hl] at hv
  have hsucc : ∀ j : Fin 3, j ≠ j + 1 := by decide
  have hne : T.pts (kg + 1) ≠ T.pts (kg + 1 + 1) := fun h => hsucc _ (T.indep.injective h)
  by_cases hd : 0 < T.det
  · rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by simp [eU, hd, h1], by simp [eV, hd, h2]⟩
    · exfalso
      apply hne
      have h4 : eV T (kg + 1) - eU T (kg + 1) = T.pts (kg + 1 + 1) - T.pts (kg + 1) := by simp [eV, eU, hd]
      have h3 : T.pts (kg + 1 + 1) - T.pts (kg + 1) = T.pts (kg + 1) - T.pts (kg + 1 + 1) :=
        h4.symm.trans (hv.trans (by rw [← h1, ← h2]))
      ext i
      have := congrArg (fun z : Plane => z i) h3
      simp at this
      linarith
  · rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exfalso
      apply hne
      have h4 : eV T (kg + 1) - eU T (kg + 1) = T.pts (kg + 1) - T.pts (kg + 1 + 1) := by simp [eV, eU, hd]
      have h3 : T.pts (kg + 1) - T.pts (kg + 1 + 1) = T.pts (kg + 1 + 1) - T.pts (kg + 1) :=
        h4.symm.trans (hv.trans (by rw [← h1, ← h2]))
      ext i
      have := congrArg (fun z : Plane => z i) h3
      simp at this
      linarith
    · exact ⟨by simp [eU, hd, h2], by simp [eV, hd, h1]⟩

/-- **(d1) Interior c-pairs cancel.**  `Bd i` says the open `c`-side of tile `i` contains no interior point of the polygon.  The sum of all tile fluxes (weight anchored at `θ₀`) equals the
sum over the tiles with `Bd i`: the others come in Lemma-4.8 pairs (an involution), each pair of total flux `0`. -/
theorem iiic_interior_pairs_cancel {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) {α : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hmodel : T.C.model.TwoPiThreeData α (slen T.C 0) (slen T.C 1) (slen T.C 2))
    (hab : Comm (slen T.C 0) (slen T.C 1)) (hac : ¬ Comm (slen T.C 0) (slen T.C 2)) (θ₀ : Real.Angle)
    (kg : Fin N → Fin 3) (hkg : ∀ i, (T.C.tile i).angleAt (kg i) = 2 * Real.pi / 3) :
    ∑ i, (T.C.tile i).flux (fAlphaAt α hα θ₀).weight =
      ∑ i ∈ Finset.univ.filter (fun i => ∀ m ∈ openSegment ℝ (eU (T.C.tile i) (kg i + 1)) (eV (T.C.tile i) (kg i + 1)), m ∉ interior T.C.region),
        (T.C.tile i).flux (fAlphaAt α hα θ₀).weight := by
  classical
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hT : ∀ i, (T.C.tile i).TwoPiThreeData α (slen T.C 0) (slen T.C 1) (slen T.C 2) :=
    fun i => Tri.TwoPiThreeData.of_congruent (T.C.tiles_congruent i) hmodel
  have hca : slen T.C 2 ≠ slen T.C 0 := by
    intro h; apply hac; exact ⟨1, 1, one_pos, one_pos, by rw [h]⟩
  have hcb : slen T.C 2 ≠ slen T.C 1 := by
    intro h; apply hac
    obtain ⟨p, q, hp, hq, hpq⟩ := hab
    exact ⟨p, q, hp, hq, by rw [h]; exact hpq⟩
  set Bd : Fin N → Prop := fun i => ∀ m ∈ openSegment ℝ (eU (T.C.tile i) (kg i + 1)) (eV (T.C.tile i) (kg i + 1)), m ∉ interior T.C.region with hBd
  set f : Fin N → ℝ := fun i => (T.C.tile i).flux (fAlphaAt α hα θ₀).weight with hf
  have hdist : ∀ i, dist (eU (T.C.tile i) (kg i + 1)) (eV (T.C.tile i) (kg i + 1)) = slen T.C 2 := by
    intro i; rw [dist_eUV]; exact cedge_dist (hT i) (kg i) (hkg i)
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
      exact pair_flux_zero hα (hT i) (hT _) hca hcb θ₀ (triStep_edge _ _) hs (hdist i)
    · intro i hi _
      exact (Classical.choose_spec (hpart i (Finset.mem_filter.mp hi).2)).1
    · intro i hi
      have hi' := (Finset.mem_filter.mp hi).2
      have hs := (Classical.choose_spec (hpart i hi')).2
      set j := Classical.choose (hpart i hi')
      obtain ⟨h1, h2⟩ := triStep_cedge (hT j) hca hcb (kg j) (hkg j) hs (by rw [dist_comm]; exact hdist i)
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hj => hi' ?_⟩
      intro m hm hmi
      apply hj m _ hmi
      rw [← h1, ← h2, openSegment_symm]; exact hm
    · intro i hi
      have hi' := (Finset.mem_filter.mp hi).2
      have hs := (Classical.choose_spec (hpart i hi')).2
      set j := Classical.choose (hpart i hi') with hjdef
      obtain ⟨h1, h2⟩ := triStep_cedge (hT j) hca hcb (kg j) (hkg j) hs (by rw [dist_comm]; exact hdist i)
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

end Erdos634.Draft.LaczFormal.IIIc

#print axioms Erdos634.Draft.LaczFormal.IIIc.triStep_edge
#print axioms Erdos634.Draft.LaczFormal.IIIc.triStep_cedge
#print axioms Erdos634.Draft.LaczFormal.IIIc.iiic_interior_pairs_cancel
