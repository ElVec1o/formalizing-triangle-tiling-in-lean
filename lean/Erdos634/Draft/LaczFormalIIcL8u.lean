-- Draft/LaczFormalIIcL8u.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, step 7 (G10) `index_split`: the hypothesis `hI` of `central_symmetry_of_spokes` is DISCHARGED in the two-exceptional-point case.
-- Hypotheses: Case IIc with P = M = 2k, every corner of type (1,1,0), an edge `GExc (P.v j) (W j)` at every corner, `kiteB = empty` (this is the form of `NoKites` used here), and two distinct values of `W`.
-- Route: `W j` is exceptional (`gexc_end_cls`, kiteB empty); at most two exceptional vertices (`caseII_exc_count`); so `W j in {E, F}`; the fibres `I_E = {j | W j = E}` inject into the arrivals at `E`, whose number is `cnt gamma - cnt alpha` (M1)
-- and `sum_E (cnt gamma - cnt alpha) = M` (`exc_census`), hence `|I_E| = cnt gamma - cnt alpha`; the angle relation `(r - p) gamma = (v - p) pi` with `k gamma = pi` puts this in `{k, 2k}`, so it is `k` for both;
-- `spokes_disjoint` (L8) and `spokes_interval` (L8g) make `I_E` a cyclic interval of length `k`.
-- NOTE, UNAUDITED.  CONDITIONAL on `kiteB = empty` (NoKites) and on the Case IIc hypothesis block (witnessed by GenWitK (204-tile octagon, genTiling_thm21) and IsoWitM).  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcL8t
import Erdos634.Draft.LaczFormalIIcL8g
import Erdos634.Draft.LaczFormalIIcSym

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

theorem card_sub_lt {M : ℕ} [NeZero M] (s : Fin M) {j : ℕ} (hj : j ≤ M) : (Finset.univ.filter (fun i : Fin M => (i - s).val < j)).card = j := by
  have himg : (Finset.univ.filter (fun i : Fin M => (i - s).val < j)).image (fun i : Fin M => (i - s).val) = Finset.range j := by
    ext n
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hn
      refine ⟨(n : Fin M) + s, ?_, ?_⟩
      · simp only [add_sub_cancel_right, Fin.val_natCast]; rw [Nat.mod_eq_of_lt (by omega)]; exact hn
      · simp only [add_sub_cancel_right, Fin.val_natCast]; exact Nat.mod_eq_of_lt (by omega)
  have hinj : Function.Injective (fun i : Fin M => (i - s).val) := by
    intro a b h
    have := Fin.ext h
    exact sub_left_injective this
  rw [← Finset.card_image_of_injective _ hinj, himg, Finset.card_range]

set_option maxHeartbeats 12800000 in
/-- **`hI` for Case IIc** (two exceptional points). -/
theorem index_split {k : ℕ} [NeZero (2 * k)] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly (2 * k)) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin (2 * k), cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0)
    (hNK : kiteB D idx = ∅) (W : Fin (2 * k) → Plane) (hW : ∀ j, GExc D idx (P.v j) (W j)) (hdiff : ∃ j, W j ≠ W 0) :
    ∃ E F : Plane, E ≠ F ∧ ∃ s0 : Fin (2 * k), ∀ i : Fin (2 * k), ((i - s0).val < k → W i = E) ∧ (k ≤ (i - s0).val → W i = F) := by
  classical
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exfalso; exact (NeZero.ne (2 * k)) (by simp [h])
    · exact h
  obtain ⟨j0, hj0⟩ := hdiff
  set E := W 0 with hEdef
  set F := W j0 with hFdef
  have hEF : E ≠ F := fun h => hj0 h.symm
  obtain ⟨hKB, hM1, hM3⟩ := gexc_matching' D P hreg idx hC hab hac h1 h3 G hcor
  have hWex : ∀ j, W j ∈ excVerts2 D idx P := by
    intro j
    rcases gexc_end_cls D P hreg idx hC hab hac h1 h3 G hcor (hW j) with h | h
    · rw [hNK] at h; exact absurd h (Finset.notMem_empty _)
    · exact h
  have hP0 : cntP0 D idx P = 2 * k := by
    unfold cntP0
    rw [Finset.sum_congr rfl (fun j _ => (hcor (j + 1)).1)]
    simp
  have hcard2 : (excVerts2 D idx P).card ≤ 2 := by
    obtain ⟨-, -, hc, -⟩ := caseII_exc_count D P hreg idx hC.hidxA hC.hregc h1 h3
    rw [hP0] at hc
    push_cast at hc
    omega
  have hsub : ({E, F} : Finset Plane) ⊆ excVerts2 D idx P := by
    intro Z hZ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hZ
    rcases hZ with rfl | rfl <;> exact hWex _
  have hEx : excVerts2 D idx P = {E, F} := by
    symm
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_pair hEF]; exact hcard2
  have hWEF : ∀ j, W j = E ∨ W j = F := by
    intro j
    have := hWex j
    rw [hEx] at this
    simpa using this
  -- counts
  have hcensus := exc_census D P hreg idx hC h1 h3 hcor
  rw [hEx, Finset.sum_pair hEF] at hcensus
  have hEmem : E ∈ excVerts2 D idx P := by rw [hEx]; simp
  have hFmem : F ∈ excVerts2 D idx P := by rw [hEx]; simp
  have hAE := hM1 E hEmem
  have hAF := hM1 F hFmem
  have hIE : (Finset.univ.filter (fun j => W j = E)).card ≤ cnt D idx E 2 - cnt D idx E 0 := by
    rw [← hAE]
    apply Finset.card_le_card_of_injOn (fun j => P.v j)
    · intro j hj
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hj
      simp only [Finset.coe_filter, Set.mem_setOf_eq]
      refine ⟨mem_vtxSet.mpr ?_, by rw [← hj]; exact hW j⟩
      obtain ⟨i, kk, hik⟩ := poly_vertex_is_tile_vertex D.toRegionDissection P hreg j
      exact ⟨i, kk, hik⟩
    · intro a _ b _ h; exact vtx_inj' P h
  have hIF : (Finset.univ.filter (fun j => W j = F)).card ≤ cnt D idx F 2 - cnt D idx F 0 := by
    rw [← hAF]
    apply Finset.card_le_card_of_injOn (fun j => P.v j)
    · intro j hj
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hj
      simp only [Finset.coe_filter, Set.mem_setOf_eq]
      refine ⟨mem_vtxSet.mpr ?_, by rw [← hj]; exact hW j⟩
      obtain ⟨i, kk, hik⟩ := poly_vertex_is_tile_vertex D.toRegionDissection P hreg j
      exact ⟨i, kk, hik⟩
    · intro a _ b _ h; exact vtx_inj' P h
  have hpart : (Finset.univ.filter (fun j => W j = E)).card + (Finset.univ.filter (fun j => W j = F)).card = 2 * k := by
    have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin (2 * k)))) (t := ({E, F} : Finset Plane)) (f := W)
      (by intro j _; simpa using hWEF j)
    rw [Finset.sum_pair hEF] at this
    simpa using this.symm
  have hIEeq : (Finset.univ.filter (fun j => W j = E)).card = cnt D idx E 2 - cnt D idx E 0 := by omega
  have hIFeq : (Finset.univ.filter (fun j => W j = F)).card = cnt D idx F 2 - cnt D idx F 0 := by omega
  -- the angle relation
  obtain ⟨hang, hMγ⟩ := corner_angles_gamma D P hreg idx hC h1 h3 hcor
  have hpi := Real.pi_pos
  have hγ0 := model_angle_pos' D 2
  have hkγ : (k : ℝ) * D.model.angleAt 2 = Real.pi := by
    have : ((2 * k : ℕ) : ℝ) * D.model.angleAt 2 = 2 * Real.pi := hMγ
    push_cast at this; linarith
  have hval : ∀ Z ∈ excVerts2 D idx P, cnt D idx Z 2 - cnt D idx Z 0 = k ∨ cnt D idx Z 2 - cnt D idx Z 0 = 2 * k := by
    intro Z hZ
    have hZ' := hZ
    unfold excVerts2 at hZ'
    simp only [Finset.mem_filter, Finset.mem_sdiff] at hZ'
    obtain ⟨⟨hZv, hZp⟩, hlt⟩ := hZ'
    have hvert := mem_vtxSet.mp hZv
    have hnc : ∀ kk : Fin (2 * k), Z ≠ P.v (kk + 1) := fun kk hkk => hZp (mem_polyVerts.mpr ⟨kk, hkk⟩)
    obtain ⟨v, hv2, hrel⟩ := vertex_angle_rel D P hreg idx hC.hidxA hC.hregc hvert hnc
    have hp1 := exc_cnt0_le_one D P hreg idx hC.hidxA hC.hregc h1 h3 hvert hnc hlt
    have hr : (cnt D idx Z 2 : ℝ) - cnt D idx Z 0 = ((v : ℝ) - cnt D idx Z 0) * k := by
      have : ((cnt D idx Z 2 : ℝ) - cnt D idx Z 0) * D.model.angleAt 2 = (((v : ℝ) - cnt D idx Z 0) * k) * D.model.angleAt 2 := by
        rw [hrel]; nlinarith [hkγ]
      exact mul_right_cancel₀ hγ0.ne' this
    obtain ⟨a, ha⟩ : ∃ a, a = cnt D idx Z 2 - cnt D idx Z 0 := ⟨_, rfl⟩
    rw [← ha]
    have haR : (a : ℝ) = ((v : ℝ) - cnt D idx Z 0) * k := by rw [ha, Nat.cast_sub hlt.le]; exact hr
    have ha1 : 1 ≤ a := by omega
    have ha1R : (1 : ℝ) ≤ a := by exact_mod_cast ha1
    have hk1R : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    rcases (by omega : cnt D idx Z 0 = 0 ∨ cnt D idx Z 0 = 1) with hp | hp <;>
    rcases (by omega : v = 0 ∨ v = 1 ∨ v = 2) with hv | hv | hv <;>
    · rw [hp, hv] at haR
      simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] at haR
      first
        | (exfalso; nlinarith)
        | (left; exact_mod_cast (by linarith : (a : ℝ) = (k : ℝ)))
        | (right; exact_mod_cast (by push_cast; linarith : (a : ℝ) = ((2 * k : ℕ) : ℝ)))
  have hE' := hval E hEmem
  have hF' := hval F hFmem
  have hIEk : (Finset.univ.filter (fun j => W j = E)).card = k := by omega
  have hEint : E ∈ interior P.carrier := by
    have := (gexc_exc_interior_exact D P hreg idx hC hab hac h1 h3 G hcor E hEmem).1; rwa [hreg] at this
  have hFint : F ∈ interior P.carrier := by
    have := (gexc_exc_interior_exact D P hreg idx hC hab hac h1 h3 G hcor F hFmem).1; rwa [hreg] at this
  have hdis : ∀ i l : Fin (2 * k), W i = E → W l = F → ∀ X, X ∈ segment ℝ (P.v i) E → X ∈ segment ℝ (P.v l) F → False := by
    intro i l hi hl X
    have hil : i ≠ l := by
      intro h; subst h; rw [hi] at hl; exact hEF hl
    have hGi := hW i
    rw [hi] at hGi
    have hGl := hW l
    rw [hl] at hGl
    exact spokes_disjoint D P hreg idx hC hab hac h1 h3 G hcor hEmem hFmem hEF hil hGi hGl X
  obtain ⟨s, j, hj, hiff⟩ := spokes_interval P (interior_subset hEint) (interior_subset hFint) hEF W hWEF hdis
  have hcardj : (Finset.univ.filter (fun i : Fin (2 * k) => W i = E)).card = j := by
    rw [Finset.filter_congr (fun i _ => hiff i)]
    exact card_sub_lt s hj
  have hjk : j = k := by omega
  subst hjk
  refine ⟨E, F, hEF, s, fun i => ⟨fun h => (hiff i).2 h, fun h => ?_⟩⟩
  rcases hWEF i with hi | hi
  · exfalso
    have := (hiff i).1 hi
    omega
  · exact hi

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.index_split
