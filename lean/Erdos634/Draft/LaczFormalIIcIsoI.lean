-- Draft/LaczFormalIIcIsoI.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, Case IIc with alpha = beta: `exc_not_inner_iso`, `spokes_disjoint_iso`, `index_split_iso`, `central_symmetry_two_exc_iso`.
-- Verbatim copies of the originals with `AngGenI` for `AngGen` and the `_iso` chain of IIcIsoG/H.  Originals NOT edited.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcIsoH
import Erdos634.Draft.LaczFormalIIcL8v

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

set_option maxHeartbeats 6400000 in
/-- **(A)** an exceptional vertex is never an inner point of an edge of Gamma_except. -/
theorem exc_not_inner_iso [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGenI (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0)
    {E X Y : Plane} (hE : E ∈ excVerts2 D idx P) (h : GExc D idx X Y) (hin : E ∈ openSegment ℝ X Y) : False := by
  classical
  have hE' := hE
  unfold excVerts2 at hE'
  simp only [Finset.mem_filter, Finset.mem_sdiff] at hE'
  obtain ⟨⟨hEv, hEp⟩, hlt⟩ := hE'
  have hvert := mem_vtxSet.mp hEv
  obtain ⟨κ, _, ⟨F⟩⟩ := HasFansC.fans (D := D.toRegionDissection) E hvert
  set Aset := (vtxSet D.toRegionDissection).filter (fun X' => GExc D idx X' E) with hAset
  obtain ⟨d, hd, nb, par, -⟩ := gexc_inner_split D idx h hin
  have hXY : toV2 (Y - X) ≠ 0 := par.ne_left
  have hXn : X ∉ Aset := by
    intro hX
    have hX' := (Finset.mem_filter.mp hX).2
    have hY := gexc_det D idx h hX' (par_of_openSegment hin hXY)
    subst hY
    obtain ⟨σ, hσ0, hσ1, hEσ⟩ := openSegment_param hin
    have c0 : Y 0 = X 0 + σ * (Y 0 - X 0) := by have := congrArg (fun z : Plane => z 0) hEσ; simpa using this
    have c1 : Y 1 = X 1 + σ * (Y 1 - X 1) := by have := congrArg (fun z : Plane => z 1) hEσ; simpa using this
    have h0 : (1 - σ) * (Y 0 - X 0) = 0 := by linarith
    have h1' : (1 - σ) * (Y 1 - X 1) = 0 := by linarith
    have e0 := (mul_eq_zero.mp h0).resolve_left (by linarith)
    have e1 := (mul_eq_zero.mp h1').resolve_left (by linarith)
    apply hXY
    unfold toV2; ext <;> simp [e0, e1]
  have hS : ∀ X' ∈ insert X Aset, (∃ aL aR : AtV D.toRegionDissection E, ArrData D idx F X' aL aR) ∨ LineD D idx X' E := by
    intro X' hX'
    rcases Finset.mem_insert.mp hX' with rfl | hmem
    · exact thru_arr_or_lineD D idx hC.hidxA hC.hregc h1 F hlt h hin
    · exact arrData_or_lineD D idx F (Finset.mem_filter.mp hmem).2
  have hcap := exc_capacity_gen D P hreg idx hC h1 h3 hE F (insert X Aset) hS
  rw [Finset.card_insert_of_notMem hXn] at hcap
  have hex : Aset.card = cnt D idx E 2 - cnt D idx E 0 := (gexc_exc_interior_exact_iso D P hreg idx hC hab hac h1 h3 G hcor E hE).2
  omega

set_option maxHeartbeats 6400000 in
/-- **L8 `gexc_disjoint`**: spokes from distinct corners to distinct exceptional vertices are disjoint. -/
theorem spokes_disjoint_iso [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGenI (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0)
    {E F : Plane} (hE : E ∈ excVerts2 D idx P) (hF : F ∈ excVerts2 D idx P) (hEF : E ≠ F) {i l : Fin M} (hil : i ≠ l)
    (hi : GExc D idx (P.v i) E) (hl : GExc D idx (P.v l) F) :
    ∀ X, X ∈ segment ℝ (P.v i) E → X ∈ segment ℝ (P.v l) F → False := by
  classical
  intro X hX1 hX2
  have hEint : E ∈ interior P.carrier := by
    have := (gexc_exc_interior_exact_iso D P hreg idx hC hab hac h1 h3 G hcor E hE).1; rwa [hreg] at this
  have hFint : F ∈ interior P.carrier := by
    have := (gexc_exc_interior_exact_iso D P hreg idx hC hab hac h1 h3 G hcor F hF).1; rwa [hreg] at this
  have hAint : P.v i ∉ interior P.carrier := vertex_not_interior P i
  have hBint : P.v l ∉ interior P.carrier := vertex_not_interior P l
  have hAB : P.v i ≠ P.v l := fun h => hil (vtx_inj' P h)
  have hEcar : E ∈ P.carrier := interior_subset hEint
  have hFcar : F ∈ P.carrier := interior_subset hFint
  have hnc : ∀ Z ∈ interior P.carrier, ∀ k : Fin M, Z ≠ P.v (k + 1) := fun Z hZ k hk => vertex_not_interior P (k + 1) (hk ▸ hZ)
  have hAE_int : ∀ Z ∈ openSegment ℝ (P.v i) E, Z ∈ interior P.carrier := fun Z hZ =>
    openSegment_interior_of P hEint (vtx_mem' P i) (by rwa [openSegment_symm] at hZ)
  have hBF_int : ∀ Z ∈ openSegment ℝ (P.v l) F, Z ∈ interior P.carrier := fun Z hZ =>
    openSegment_interior_of P hFint (vtx_mem' P l) (by rwa [openSegment_symm] at hZ)
  have hBE : P.v l ≠ E := fun h => hBint (h ▸ hEint)
  have hAE : P.v i ≠ E := fun h => hAint (h ▸ hEint)
  have hAF : P.v i ≠ F := fun h => hAint (h ▸ hFint)
  have hBF : P.v l ≠ F := fun h => hBint (h ▸ hFint)
  by_cases hXE : X = E
  · subst hXE
    exact exc_not_inner_iso D P hreg idx hC hab hac h1 h3 G hcor hE hl (mem_openSegment_of_ne_left_right hBE hEF.symm hX2)
  by_cases hXF : X = F
  · subst hXF
    exact exc_not_inner_iso D P hreg idx hC hab hac h1 h3 G hcor hF hi (mem_openSegment_of_ne_left_right hAF hEF hX1)
  by_cases hXA : X = P.v i
  · subst hXA
    exact hAint (hBF_int _ (mem_openSegment_of_ne_left_right hAB.symm hAF.symm hX2))
  by_cases hXB : X = P.v l
  · subst hXB
    exact hBint (hAE_int _ (mem_openSegment_of_ne_left_right hAB hBE.symm hX1))
  have hX1' : X ∈ openSegment ℝ (P.v i) E := mem_openSegment_of_ne_left_right (Ne.symm hXA) (Ne.symm hXE) hX1
  have hX2' : X ∈ openSegment ℝ (P.v l) F := mem_openSegment_of_ne_left_right (Ne.symm hXB) (Ne.symm hXF) hX2
  have hXint : X ∈ interior P.carrier := hAE_int X hX1'
  by_cases hpar : crs (toV2 (E - P.v i)) (toV2 (F - P.v l)) = 0
  · -- collinear case
    obtain ⟨σ, hσ0, hσ1, hXσ⟩ := openSegment_param hX1'
    obtain ⟨τ, hτ0, hτ1, hXτ⟩ := openSegment_param hX2'
    set A := P.v i with hA
    set B := P.v l with hB
    have hb : B - A = σ • (E - A) - τ • (F - B) := by
      have h := hXσ.symm.trans hXτ
      calc B - A = (B + τ • (F - B)) - A - τ • (F - B) := by module
        _ = (A + σ • (E - A)) - A - τ • (F - B) := by rw [← h]
        _ = σ • (E - A) - τ • (F - B) := by module
    have hp0 : cross2 (E - A) (F - B) = 0 := by unfold cross2; unfold crs toV2 at hpar; simpa using hpar
    have gE : gl A B E = 0 := by
      unfold gl; rw [hb]; unfold cross2 at hp0 ⊢
      simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hp0 ⊢
      nlinarith [hp0]
    have gF : gl A B F = 0 := by
      unfold gl
      have e : F - A = (F - B) + (B - A) := by abel
      rw [e, hb]; unfold cross2 at hp0 ⊢
      simp only [PiLp.sub_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul] at hp0 ⊢
      nlinarith [hp0]
    have hEs := chord_in_segment P hil hEcar gE
    have hFs := chord_in_segment P hil hFcar gF
    have hEo : E ∈ openSegment ℝ A B := mem_openSegment_of_ne_left_right hAE hBE hEs
    have hFo : F ∈ openSegment ℝ A B := mem_openSegment_of_ne_left_right hAF hBF hFs
    exact exc_not_inner_iso D P hreg idx hC hab hac h1 h3 G hcor hE hl (col_E_in hAB hEo hFo hEF hX1' hX2')
  · have hXexc := cross_exc D P hreg idx hC h1 hi hl hX1' hX2' hpar (hnc X hXint)
    exact exc_not_inner_iso D P hreg idx hC hab hac h1 h3 G hcor hXexc hi hX1'

set_option maxHeartbeats 12800000 in
/-- **`hI` for Case IIc** (two exceptional points). -/
theorem index_split_iso {k : ℕ} [NeZero (2 * k)] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly (2 * k)) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGenI (fun l => D.model.angleAt l))
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
  obtain ⟨hKB, hM1, hM3⟩ := gexc_matching_iso D P hreg idx hC hab hac h1 h3 G hcor
  have hWex : ∀ j, W j ∈ excVerts2 D idx P := by
    intro j
    rcases gexc_end_cls_iso D P hreg idx hC hab hac h1 h3 G hcor (hW j) with h | h
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
    have := (gexc_exc_interior_exact_iso D P hreg idx hC hab hac h1 h3 G hcor E hEmem).1; rwa [hreg] at this
  have hFint : F ∈ interior P.carrier := by
    have := (gexc_exc_interior_exact_iso D P hreg idx hC hab hac h1 h3 G hcor F hFmem).1; rwa [hreg] at this
  have hdis : ∀ i l : Fin (2 * k), W i = E → W l = F → ∀ X, X ∈ segment ℝ (P.v i) E → X ∈ segment ℝ (P.v l) F → False := by
    intro i l hi hl X
    have hil : i ≠ l := by
      intro h; subst h; rw [hi] at hl; exact hEF hl
    have hGi := hW i
    rw [hi] at hGi
    have hGl := hW l
    rw [hl] at hGl
    exact spokes_disjoint_iso D P hreg idx hC hab hac h1 h3 G hcor hEmem hFmem hEF hil hGi hGl X
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

set_option maxHeartbeats 12800000 in
/-- **Central symmetry of the two-exceptional-point polygon**, unconditional on the index split (conditional on `kiteB = empty`). -/
theorem central_symmetry_two_exc_iso {k : ℕ} [NeZero (2 * k)] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly (2 * k)) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGenI (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin (2 * k), cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0)
    (hNK : kiteB D idx = ∅) (W : Fin (2 * k) → Plane) (hW : ∀ j, GExc D idx (P.v j) (W j)) (hdiff : ∃ j, W j ≠ W 0) :
    ∀ i : Fin (2 * k), P.side i = P.side (i + (k : Fin (2 * k))) := by
  obtain ⟨E, F, hEF, hI⟩ := index_split_iso D P hreg idx hC hab hac h1 h3 G hcor hNK W hW hdiff
  obtain ⟨-, hMγ⟩ := corner_angles_gamma D P hreg idx hC h1 h3 hcor
  have hk4 := k_ge_four (model_angle_pos' D 2) h1 h3 hMγ
  have hint : ∀ E ∈ excVerts2 D idx P, E ∈ interior D.region := fun E hE =>
    (gexc_exc_interior_exact_iso D P hreg idx hC hab hac h1 h3 G hcor E hE).1
  exact central_symmetry_of_spokes D P hreg idx hC h1 h3 hcor (by omega) hint W hW E F hI

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.exc_not_inner_iso
#print axioms Erdos634.Draft.LaczFormal.RG.spokes_disjoint_iso
#print axioms Erdos634.Draft.LaczFormal.RG.index_split_iso
#print axioms Erdos634.Draft.LaczFormal.RG.central_symmetry_two_exc_iso
