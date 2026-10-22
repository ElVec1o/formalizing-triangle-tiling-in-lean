-- Draft/LaczFormalIIcIsoJ.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, Case IIc with alpha = beta: `lemma63_one_iso`, `lemma63_two_iso`, `M_even_of_two_iso`, `g11_two_iso`, `lemma63_two_full_iso`, `lemma63_full_iso`: LEMMA 6.3 for alpha = beta (with the hypothesis `kiteB = empty`, proved in IsoF).
-- Verbatim copies of the originals with `AngGenI` for `AngGen` and the `_iso` chain of IIcIsoG/H.  Originals NOT edited.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcIsoI
import Erdos634.Draft.LaczFormalIIcG11g
import Erdos634.Draft.LaczFormalIIcL8ab

open scoped Classical Fin.NatCast
open EuclideanGeometry Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

set_option maxHeartbeats 12800000 in
/-- **Lemma 6.3, one exceptional point** (all corners send their edge to the same point). -/
theorem lemma63_one_iso [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGenI (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0)
    (W : Fin M → Plane) (hW : ∀ j, GExc D idx (P.v j) (W j)) (hsame : ∀ j, W j = W 0) : Concl7 D P := by
  have hint : ∀ E ∈ excVerts2 D idx P, E ∈ interior D.region := fun E hE =>
    (gexc_exc_interior_exact_iso D P hreg idx hC hab hac h1 h3 G hcor E hE).1
  obtain ⟨a, b, hab', hsp⟩ := spokes_angle D P hreg idx hC h1 h3 hcor hint W hW
  obtain ⟨hang, hMγ⟩ := corner_angles_gamma D P hreg idx hC h1 h3 hcor
  have hpi := Real.pi_pos
  have hγ0 := model_angle_pos' D 2
  have hαβγ : D.model.angleAt a + D.model.angleAt b + D.model.angleAt 2 = Real.pi := by
    have := angleAt_sum D.model
    rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact this
    · linarith
  set E := W 0 with hE
  set V : ℕ → Plane := fun n => P.v (n : Fin M) with hV
  have hVs : ∀ n, V (n + 1) = P.v ((n : Fin M) + 1) := fun n => by simp only [hV, Nat.cast_succ]
  have hper : ∀ i, V (i + M) = V i := fun i => by simp [hV, Nat.cast_add]
  have hne : ∀ i, V i ≠ E := fun i => by
    have := gexc_ne D idx (hW (i : Fin M))
    rw [hsame (i : Fin M)] at this
    exact fun h => this h.symm
  have hA : ∀ i, ∠ E (V i) (V (i + 1)) = D.model.angleAt a := by
    intro i
    have := (hsp ((i : Fin M) - 1)).1
    rw [sub_add_cancel, hsame (i : Fin M)] at this
    rw [hVs i, EuclideanGeometry.angle_comm]
    exact this
  have hB : ∀ i, ∠ (V i) (V (i + 1)) E = D.model.angleAt b := by
    intro i
    have := (hsp (i : Fin M)).2
    rw [hsame ((i : Fin M) + 1)] at this
    rw [hVs i]
    exact this
  have hαβlt : D.model.angleAt a + D.model.angleAt b < Real.pi := by linarith
  have hαeqβ := spoke_chain_alpha_eq_beta (n := M) (by have := P.three_le; omega) V E (D.model.angleAt a) (D.model.angleAt b) hper hne hA hB
    (model_angle_pos' D a) (model_angle_pos' D b) hαβlt
  have h01 : D.model.angleAt 0 = D.model.angleAt 1 := by
    rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hαeqβ
    · exact hαeqβ.symm
  have sα : 0 < Real.sin (D.model.angleAt a) := Real.sin_pos_of_pos_of_lt_pi (model_angle_pos' D a) (by linarith)
  have sγ : 0 < Real.sin (D.model.angleAt 2) := Real.sin_pos_of_pos_of_lt_pi hγ0 (by linarith [model_angle_pos' D a, model_angle_pos' D b])
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by have := P.three_le; omega : 0 < M)
  -- the distances to E are constant
  have step : ∀ i, dist (V (i + 1)) E = dist (V i) E := by
    intro i
    have h := EuclideanGeometry.sin_angle_mul_dist_eq_sin_angle_mul_dist (V i) (V (i + 1)) E
    rw [hB i, hA i, dist_comm E (V i), ← hαeqβ] at h
    have := mul_right_cancel₀ sα.ne' (by linarith : dist (V (i + 1)) E * Real.sin (D.model.angleAt a) = dist (V i) E * Real.sin (D.model.angleAt a))
    exact this
  have hr : ∀ i, dist (V i) E = dist (V 0) E := by
    intro i; induction i with
    | zero => rfl
    | succ i ih => rw [step i, ih]
  have hVne : ∀ i, V i ≠ V (i + 1) := by
    intro i h
    rw [hVs i] at h
    have := vtx_inj' P h
    have hf := (ConvPoly.fin_facts P.three_le (i : Fin M)).1
    exact hf this.symm
  -- side length
  have hside : ∀ i : ℕ, P.side (i : Fin M) = Real.sin (D.model.angleAt 2) * dist (V 0) E / Real.sin (D.model.angleAt a) := by
    intro i
    have hsd : P.side (i : Fin M) = dist (V i) (V (i + 1)) := by
      unfold ConvPoly.side; rw [hVs i]
    have hs1 := EuclideanGeometry.angle_add_angle_add_angle_eq_pi (p₁ := V i) (p₂ := V (i + 1)) E (hVne i).symm
    have hl := EuclideanGeometry.law_sin (V i) E (V (i + 1))
    have e1 : ∠ (V (i + 1)) (V i) E = D.model.angleAt a := by rw [EuclideanGeometry.angle_comm]; exact hA i
    have e2 : ∠ (V i) E (V (i + 1)) = D.model.angleAt 2 := by
      rw [EuclideanGeometry.angle_comm]
      have : ∠ (V (i + 1)) E (V i) = Real.pi - D.model.angleAt b - D.model.angleAt a := by
        have hB' := hB i
        have hA' := hA i
        linarith
      rw [this]; linarith
    rw [e1, e2, dist_comm E (V (i + 1)), hr (i + 1)] at hl
    rw [hsd, dist_comm (V i) (V (i + 1))]
    rw [eq_div_iff sα.ne']
    linarith
  have hang0 : ∀ i : Fin M, P.angle i = P.angle 0 := fun i => by rw [hang i, hang 0]
  have hγM : D.model.angleAt 2 = 2 * Real.pi / M := by
    field_simp; linarith
  refine ⟨fun i => ?_, hang0, h01, ?_, hγM⟩
  · have h1' := hside (i.val)
    have h0' := hside 0
    rw [Fin.cast_val_eq_self] at h1'
    simpa using h1'.trans h0'.symm
  · change D.model.angleAt 0 = Real.pi / 2 - Real.pi / M
    have e : 2 * Real.pi / (M : ℝ) = 2 * (Real.pi / M) := by ring
    rw [hγM, e] at hαβγ
    rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith [h01]

set_option maxHeartbeats 12800000 in
/-- **Lemma 6.3, two exceptional points** (conclusion (v) without its printed inequality). -/
theorem lemma63_two_iso {k : ℕ} [NeZero (2 * k)] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly (2 * k)) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGenI (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin (2 * k), cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0)
    (hNK : kiteB D idx = ∅) (W : Fin (2 * k) → Plane) (hW : ∀ j, GExc D idx (P.v j) (W j)) (hdiff : ∃ j, W j ≠ W 0) :
    Concl5Rest D P k ∧ ∃ (s : Fin (2 * k)) (rev : Bool) (a : ℕ → ℝ), Concl5Seq D P k s rev a := by
  obtain ⟨E, F, hEF, hI⟩ := index_split_iso D P hreg idx hC hab hac h1 h3 G hcor hNK W hW hdiff
  obtain ⟨hang, hMγ⟩ := corner_angles_gamma D P hreg idx hC h1 h3 hcor
  have hk4 := k_ge_four (model_angle_pos' D 2) h1 h3 hMγ
  have hint : ∀ E ∈ excVerts2 D idx P, E ∈ interior D.region := fun E hE =>
    (gexc_exc_interior_exact_iso D P hreg idx hC hab hac h1 h3 G hcor E hE).1
  have hsym := central_symmetry_two_exc_iso D P hreg idx hC hab hac h1 h3 G hcor hNK W hW hdiff
  have hαβγ := angleAt_sum D.model
  refine ⟨⟨rfl, hk4, rational_of_caseC D idx hC hab P hreg, fun i => ?_, fun i => ?_⟩, ?_⟩
  · change P.angle i = D.model.angleAt 0 + D.model.angleAt 1
    rw [hang i]; linarith
  · rw [ofNat_cast_fin]; exact hsym i
  obtain ⟨a, b, hab', s0, hrec⟩ := geometric_sides_of_spokes D P hreg idx hC h1 h3 hcor (by omega) hint W hW E F hI
  have hpos0 : 0 < Real.sin (D.model.angleAt 0) := Real.sin_pos_of_pos_of_lt_pi (model_angle_pos' D 0) (by linarith [model_angle_pos' D 1, model_angle_pos' D 2])
  have hpos1 : 0 < Real.sin (D.model.angleAt 1) := Real.sin_pos_of_pos_of_lt_pi (model_angle_pos' D 1) (by linarith [model_angle_pos' D 0, model_angle_pos' D 2])
  rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨s0, false, fun n => P.side (s0 + (Fin.ofNat (2 * k) n)), ⟨fun n => by simp, fun n hn => ?_⟩⟩
    simp only [ofNat_cast_fin]
    show P.side (s0 + ((n + 1 : ℕ) : Fin (2 * k))) = Real.sin (D.model.angleAt 0) / Real.sin (D.model.angleAt 1) * P.side (s0 + (n : Fin (2 * k)))
    have := hrec n hn
    rw [div_mul_eq_mul_div, eq_div_iff hpos1.ne']
    linarith
  · refine ⟨s0 + ((k - 1 : ℕ) : Fin (2 * k)), true, fun n => P.side (s0 + ((k - 1 : ℕ) : Fin (2 * k)) - (Fin.ofNat (2 * k) n) - 1), ⟨fun n => by simp, fun n hn => ?_⟩⟩
    simp only [ofNat_cast_fin]
    have hm := hrec (k - 3 - n) (by omega)
    have e1 : s0 + ((k - 1 : ℕ) : Fin (2 * k)) - ((n + 1 : ℕ) : Fin (2 * k)) - 1 = s0 + ((k - 3 - n : ℕ) : Fin (2 * k)) := by
      have : (k - 3 - n : ℕ) + (n + 1) + 1 = k - 1 := by omega
      have h' : ((k - 1 : ℕ) : Fin (2 * k)) = ((k - 3 - n : ℕ) : Fin (2 * k)) + ((n + 1 : ℕ) : Fin (2 * k)) + 1 := by
        rw [← this]; push_cast; ring
      rw [h']; abel
    have e2 : s0 + ((k - 1 : ℕ) : Fin (2 * k)) - (n : Fin (2 * k)) - 1 = s0 + ((k - 3 - n + 1 : ℕ) : Fin (2 * k)) := by
      have : (k - 3 - n + 1 : ℕ) + n + 1 = k - 1 := by omega
      have h' : ((k - 1 : ℕ) : Fin (2 * k)) = ((k - 3 - n + 1 : ℕ) : Fin (2 * k)) + (n : Fin (2 * k)) + 1 := by
        rw [← this]; push_cast; ring
      rw [h']; abel
    rw [e1, e2]
    show P.side (s0 + ((k - 3 - n : ℕ) : Fin (2 * k))) = Real.sin (D.model.angleAt 0) / Real.sin (D.model.angleAt 1) * P.side (s0 + ((k - 3 - n + 1 : ℕ) : Fin (2 * k)))
    rw [div_mul_eq_mul_div, eq_div_iff hpos1.ne']
    linarith

set_option maxHeartbeats 12800000 in
/-- two distinct values of `W` force `M` even. -/
theorem M_even_of_two_iso [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGenI (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0)
    (hNK : kiteB D idx = ∅) (W : Fin M → Plane) (hW : ∀ j, GExc D idx (P.v j) (W j)) (hdiff : ∃ j, W j ≠ W 0) : ∃ k, M = 2 * k := by
  classical
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
  have hP0 : cntP0 D idx P = M := by
    unfold cntP0
    rw [Finset.sum_congr rfl (fun j _ => (hcor (j + 1)).1)]
    simp
  have hcard2 : (excVerts2 D idx P).card ≤ 2 := by
    obtain ⟨-, -, hc, -⟩ := caseII_exc_count D P hreg idx hC.hidxA hC.hregc h1 h3
    rw [hP0] at hc
    omega
  have hsub : ({E, F} : Finset Plane) ⊆ excVerts2 D idx P := by
    intro Z hZ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hZ
    rcases hZ with rfl | rfl <;> exact hWex _
  have hEx : excVerts2 D idx P = {E, F} := by
    symm
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_pair hEF]; exact hcard2
  have hcensus := exc_census D P hreg idx hC h1 h3 hcor
  rw [hEx, Finset.sum_pair hEF] at hcensus
  have hEmem : E ∈ excVerts2 D idx P := by rw [hEx]; simp
  have hFmem : F ∈ excVerts2 D idx P := by rw [hEx]; simp
  have hpi := Real.pi_pos
  have hγ0 := model_angle_pos' D 2
  obtain ⟨hang, hMγ⟩ := corner_angles_gamma D P hreg idx hC h1 h3 hcor
  have hval : ∀ Z ∈ excVerts2 D idx P, ∃ m : ℕ, m ∈ ({1, 2} : Finset ℕ) ∧ 2 * (cnt D idx Z 2 - cnt D idx Z 0) = m * M := by
    intro Z hZ
    have hZ' := hZ
    unfold excVerts2 at hZ'
    simp only [Finset.mem_filter, Finset.mem_sdiff] at hZ'
    obtain ⟨⟨hZv, hZp⟩, hlt⟩ := hZ'
    have hvert := mem_vtxSet.mp hZv
    have hnc : ∀ kk : Fin M, Z ≠ P.v (kk + 1) := fun kk hkk => hZp (mem_polyVerts.mpr ⟨kk, hkk⟩)
    obtain ⟨v, hv2, hrel⟩ := vertex_angle_rel D P hreg idx hC.hidxA hC.hregc hvert hnc
    have hp1 := exc_cnt0_le_one D P hreg idx hC.hidxA hC.hregc h1 h3 hvert hnc hlt
    obtain ⟨a, ha⟩ : ∃ a, a = cnt D idx Z 2 - cnt D idx Z 0 := ⟨_, rfl⟩
    rw [← ha]
    have haR : (a : ℝ) * D.model.angleAt 2 = ((v : ℝ) - cnt D idx Z 0) * Real.pi := by
      rw [ha, Nat.cast_sub hlt.le]; exact hrel
    have h2a : (2 * a : ℝ) = ((v : ℝ) - cnt D idx Z 0) * M := by
      have : ((2 * a : ℝ)) * D.model.angleAt 2 = (((v : ℝ) - cnt D idx Z 0) * M) * D.model.angleAt 2 := by
        linear_combination 2 * haR - ((v : ℝ) - cnt D idx Z 0) * hMγ
      exact mul_right_cancel₀ hγ0.ne' this
    have ha1 : 1 ≤ a := by omega
    have ha1R : (1 : ℝ) ≤ a := by exact_mod_cast ha1
    have hMR : (3 : ℝ) ≤ M := by exact_mod_cast P.three_le
    rcases (by omega : cnt D idx Z 0 = 0 ∨ cnt D idx Z 0 = 1) with hp | hp <;>
    rcases (by omega : v = 0 ∨ v = 1 ∨ v = 2) with hv | hv | hv <;>
    · rw [hp, hv] at h2a
      simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] at h2a
      first
        | (exfalso; nlinarith)
        | (have h' : (2 * a : ℝ) = ((1 : ℕ) : ℝ) * M := by push_cast; linarith
           exact ⟨1, by simp, by exact_mod_cast h'⟩)
        | (have h' : (2 * a : ℝ) = ((2 : ℕ) : ℝ) * M := by push_cast; linarith
           exact ⟨2, by simp, by exact_mod_cast h'⟩)
  obtain ⟨mE, hmE, hE2⟩ := hval E hEmem
  obtain ⟨mF, hmF, hF2⟩ := hval F hFmem
  have hEpos : 1 ≤ cnt D idx E 2 - cnt D idx E 0 := by
    have h := hEmem; unfold excVerts2 at h
    have := (Finset.mem_filter.mp h).2
    omega
  have hFpos : 1 ≤ cnt D idx F 2 - cnt D idx F 0 := by
    have h := hFmem; unfold excVerts2 at h
    have := (Finset.mem_filter.mp h).2
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmE hmF
  rcases hmE with rfl | rfl <;> rcases hmF with rfl | rfl
  · exact ⟨cnt D idx E 2 - cnt D idx E 0, by omega⟩
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega

set_option maxHeartbeats 25600000 in
theorem g11_two_iso {k : ℕ} [NeZero (2 * k)] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly (2 * k)) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGenI (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin (2 * k), cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0)
    (hNK : kiteB D idx = ∅) (W : Fin (2 * k) → Plane) (hW : ∀ j, GExc D idx (P.v j) (W j)) (hdiff : ∃ j, W j ≠ W 0) :
    ∃ (a b : Fin 3) (s0 : Fin (2 * k)), ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)) ∧
      (∀ n : ℕ, n + 2 < k → P.side (s0 + ((n + 1 : ℕ) : Fin (2 * k))) * Real.sin (D.model.angleAt b) = Real.sin (D.model.angleAt a) * P.side (s0 + ((n : ℕ) : Fin (2 * k)))) ∧
      ((Real.sin (D.model.angleAt a) / Real.sin (D.model.angleAt b)) ^ (k - 1) * P.side s0 ≤ P.side (s0 + ((k - 1 : ℕ) : Fin (2 * k))) ∨
        P.side s0 ≤ (Real.sin (D.model.angleAt a) / Real.sin (D.model.angleAt b)) * P.side (s0 + ((k - 1 : ℕ) : Fin (2 * k)))) := by
  classical
  obtain ⟨E, F, hEF, hI⟩ := index_split_iso D P hreg idx hC hab hac h1 h3 G hcor hNK W hW hdiff
  obtain ⟨hang, hMγ⟩ := corner_angles_gamma D P hreg idx hC h1 h3 hcor
  have hk4 := k_ge_four (model_angle_pos' D 2) h1 h3 hMγ
  have hWex : ∀ j, W j ∈ excVerts2 D idx P := by
    intro j
    rcases gexc_end_cls_iso D P hreg idx hC hab hac h1 h3 G hcor (hW j) with h | h
    · rw [hNK] at h; exact absurd h (Finset.notMem_empty _)
    · exact h
  have hint : ∀ E ∈ excVerts2 D idx P, E ∈ interior D.region := fun E hE =>
    (gexc_exc_interior_exact_iso D P hreg idx hC hab hac h1 h3 G hcor E hE).1
  have hsymm := central_symmetry_two_exc_iso D P hreg idx hC hab hac h1 h3 G hcor hNK W hW hdiff
  obtain ⟨a, b, hab', hsp⟩ := spokes_angle D P hreg idx hC h1 h3 hcor hint W hW
  obtain ⟨s0, hs0⟩ := hI
  have hpi := Real.pi_pos
  have hkγ : (k : ℝ) * D.model.angleAt 2 = Real.pi := by
    have : ((2 * k : ℕ) : ℝ) * D.model.angleAt 2 = 2 * Real.pi := hMγ
    push_cast at this; linarith
  have hγ0 := model_angle_pos' D 2
  have hαβγ : D.model.angleAt a + D.model.angleAt b + D.model.angleAt 2 = Real.pi := by
    have := angleAt_sum D.model
    rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact this
    · linarith
  obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  refine ⟨a, b, s0, hab', ?_⟩
  set ι : ℕ → Fin (2 * k) := fun n => (n : Fin (2 * k)) + s0 with hιdef
  have hι : ∀ n, ι (n + 1) = ι n + 1 := by
    intro n; simp only [hιdef]; rw [Nat.cast_succ, add_right_comm]
  have hι2 : ∀ n, ι (n + 2) = ι n + 2 := by
    intro n
    have h := hι (n + 1); rw [hι n] at h
    show ι (n + 1 + 1) = _
    rw [h, add_assoc, one_add_one_eq_two]
  set V : ℕ → Plane := fun n => P.v (ι n) with hV
  have hV1 : ∀ n, V (n + 1) = P.v (ι n + 1) := fun n => by simp only [hV]; rw [hι n]
  have hV2 : ∀ n, V (n + 2) = P.v (ι n + 2) := fun n => by simp only [hV]; rw [hι2 n]
  have hval : ∀ n, n < 2 * k → ((ι n - s0).val = n) := by
    intro n hn
    simp only [hιdef, add_sub_cancel_right]
    rw [Fin.val_natCast]; exact Nat.mod_eq_of_lt hn
  have hWE : ∀ n, n < k → W (ι n) = E := fun n hn => (hs0 (ι n)).1 (by rw [hval n (by omega)]; exact hn)
  have hWF : ∀ n, k ≤ n → n < 2 * k → W (ι n) = F := fun n h1 h2 => (hs0 (ι n)).2 (by rw [hval n h2]; exact h1)
  have hcr : ∀ n, 0 < cross2 (V (n + 1) - V n) (V (n + 2) - V (n + 1)) := by
    intro n
    have hf := ConvPoly.fin_facts P.three_le (ι n)
    have := P.left (ι n) (ι n + 2) hf.2.1 hf.2.2.1
    rw [hV1 n, hV2 n, cross2_shift]
    exact this
  have hang' : ∀ n, ∠ (V n) (V (n + 1)) (V (n + 2)) = Real.pi - D.model.angleAt 2 := by
    intro n
    have := hang (ι n + 1)
    unfold ConvPoly.angle cornerAngle at this
    rw [add_sub_cancel_right] at this
    have hf := ConvPoly.fin_facts P.three_le (ι n)
    rw [hf.2.2.2.2.2] at this
    rw [hV1 n, hV2 n]
    exact this
  have hEa : ∀ n, n < k → ∠ (V (n + 1)) (V n) E = D.model.angleAt a := by
    intro n hn
    have := (hsp (ι n - 1)).1
    rw [sub_add_cancel] at this
    rw [hWE n hn] at this
    rw [hV1 n]
    exact this
  have hEb : ∀ n, n + 1 < k → ∠ (V n) (V (n + 1)) E = D.model.angleAt b := by
    intro n hn
    have := (hsp (ι n)).2
    have hw : W (ι n + 1) = E := by rw [← hι n]; exact hWE (n + 1) hn
    rw [hw] at this
    rw [hV1 n]
    exact this
  have hFa : ∀ n, k ≤ n → n < 2 * k → ∠ (V (n + 1)) (V n) F = D.model.angleAt a := by
    intro n h1 h2
    have := (hsp (ι n - 1)).1
    rw [sub_add_cancel] at this
    rw [hWF n h1 h2] at this
    rw [hV1 n]
    exact this
  have hFb : ∀ n, k ≤ n → n + 1 < 2 * k → ∠ (V n) (V (n + 1)) F = D.model.angleAt b := by
    intro n h1 h2
    have := (hsp (ι n)).2
    have hw : W (ι n + 1) = F := by rw [← hι n]; exact hWF (n + 1) (by omega) h2
    rw [hw] at this
    rw [hV1 n]
    exact this
  -- exceptional points
  have hEmem : E ∈ excVerts2 D idx P := by have := hWex (ι 0); rwa [hWE 0 (by omega)] at this
  have hFmem : F ∈ excVerts2 D idx P := by have := hWex (ι k); rwa [hWF k le_rfl (by omega)] at this
  have hEint : E ∈ interior P.carrier := by have := hint E hEmem; rwa [hreg] at this
  have hFint : F ∈ interior P.carrier := by have := hint F hFmem; rwa [hreg] at this
  have hEl : ∀ n, n + 1 < k → 0 < cross2 (V (n + 1) - V n) (E - V n) := by
    intro n hn
    have := c_pos_of_interior P hEint (ι n)
    unfold ConvPoly.c ConvPoly.e at this
    rw [hV1 n]; exact this
  have hFl : 0 < cross2 (V (k + 1) - V k) (F - V k) := by
    have := c_pos_of_interior P hFint (ι k)
    unfold ConvPoly.c ConvPoly.e at this
    rw [hV1 k]; exact this
  -- sides
  have hne : ∀ n, V n ≠ V (n + 1) := by
    intro n h
    rw [hV1 n] at h
    have := vtx_inj' P h
    exact (ConvPoly.fin_facts P.three_le (ι n)).1 this.symm
  have hside : ∀ j : ℕ, P.side (s0 + (j : Fin (2 * k))) = dist (V j) (V (j + 1)) := by
    intro j
    have : s0 + (j : Fin (2 * k)) = ι j := add_comm _ _
    rw [this]
    unfold ConvPoly.side
    rw [hV1 j]
  have hsa : 0 < Real.sin (D.model.angleAt a) := Real.sin_pos_of_pos_of_lt_pi (model_angle_pos' D a) (by linarith [model_angle_pos' D b])
  refine ⟨?_, ?_⟩
  · intro n hn
    have key := sine_ratio_step (A := V n) (B := V (n + 1)) (C := V (n + 2)) (E := E) (model_angle_pos' D a) (model_angle_pos' D b) (by linarith)
      (hne n) (hne (n + 1)) (hEa n (by omega)) (hEb n (by omega)) (hEa (n + 1) (by omega)) (hEb (n + 1) (by omega))
    rw [hside (n + 1), hside n]
    exact key
  · have h0 : P.side s0 = dist (V 0) (V (0 + 1)) := by simpa using hside 0
    have hsym : dist (V (m + 1)) (V (m + 1 + 1)) = dist (V 0) (V (0 + 1)) := by
      have e : dist (V k) (V (k + 1)) = dist (V 0) (V (0 + 1)) := by
        rw [← hside k, ← h0]; exact (hsymm s0).symm
      have hk : m + 1 = k := hm.symm
      rw [hk]; exact e
    have hk1 : k - 1 = m := by omega
    have core := g11_core (m := m) (by omega) V E F (D.model.angleAt a) (D.model.angleAt b) (D.model.angleAt 2) hcr hang'
      (model_angle_pos' D a) (model_angle_pos' D b) hαβγ hγ0 (by rw [← hm]; exact hkγ)
      (fun n hn => hEa n (by omega)) (fun n hn => hEb n (by omega)) (fun n hn => hEl n (by omega))
      (by have := hFa k le_rfl (by omega); rw [hm] at this; exact this)
      (by have := hFb k le_rfl (by omega); rw [hm] at this; exact this)
      (by have := hFl; rw [hm] at this; exact this) hsym
    rcases core with c1 | c2 | ⟨X, hX1, hX2⟩
    · left
      rw [hk1, h0, hside m]; exact c1
    · right
      rw [hk1, h0, hside m]; exact c2
    · exfalso
      have hi : GExc D idx (P.v (ι m)) E := by
        have := hW (ι m); rwa [hWE m (by omega)] at this
      have hl : GExc D idx (P.v (ι (m + 1))) F := by
        have := hW (ι (m + 1)); rwa [hWF (m + 1) (by omega) (by omega)] at this
      have hil : ι m ≠ ι (m + 1) := by
        rw [hι m]; exact (ConvPoly.fin_facts P.three_le (ι m)).1.symm
      exact spokes_disjoint_iso D P hreg idx hC hab hac h1 h3 G hcor hEmem hFmem hEF hil hi hl X hX1 hX2

set_option maxHeartbeats 25600000 in
/-- **Lemma 6.3, two exceptional points, with the printed inequality** (conclusion (v) of Theorem 2.1, labels free). -/
theorem lemma63_two_full_iso {k : ℕ} [NeZero (2 * k)] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly (2 * k)) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGenI (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin (2 * k), cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0)
    (hNK : kiteB D idx = ∅) (W : Fin (2 * k) → Plane) (hW : ∀ j, GExc D idx (P.v j) (W j)) (hdiff : ∃ j, W j ≠ W 0) : Concl5 D P := by
  obtain ⟨hrest, -⟩ := lemma63_two_iso D P hreg idx hC hab hac h1 h3 G hcor hNK W hW hdiff
  obtain ⟨a, b, s0, hab', hg, hineq⟩ := g11_two_iso D P hreg idx hC hab hac h1 h3 G hcor hNK W hW hdiff
  have hαβγ := angleAt_sum D.model
  have hp0 := model_angle_pos' D 0
  have hp1 := model_angle_pos' D 1
  have hp2 := model_angle_pos' D 2
  have hsin0 : 0 < Real.sin (D.model.angleAt 0) := Real.sin_pos_of_pos_of_lt_pi hp0 (by linarith)
  have hsin1 : 0 < Real.sin (D.model.angleAt 1) := Real.sin_pos_of_pos_of_lt_pi hp1 (by linarith)
  have hsymm : ∀ i : Fin (2 * k), P.side i = P.side (i + (k : Fin (2 * k))) := fun i => by
    have := hrest.2.2.2.2 i; rwa [ofNat_cast_fin'] at this
  rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨q, hq, s, rev, aa, e1, e2, e3⟩ := reading_exists P hrest.2.1 hsymm _ _ hsin0 hsin1 s0 hg hineq
    exact ⟨k, hrest.1, hrest.2.1, hrest.2.2.1, hrest.2.2.2.1, hrest.2.2.2.2, q, hq, s, rev, aa, e1, e2, e3⟩
  · obtain ⟨q, hq, s, rev, aa, e1, e2, e3⟩ := reading_exists P hrest.2.1 hsymm _ _ hsin1 hsin0 s0 hg hineq
    exact ⟨k, hrest.1, hrest.2.1, hrest.2.2.1, hrest.2.2.2.1, hrest.2.2.2.2, q, hq.symm, s, rev, aa, e1, e2, e3⟩

/-- **Lemma 6.3 with the printed inequality** (conditional on `kiteB = empty`). -/
theorem lemma63_full_iso [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGenI (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0)
    (hNK : kiteB D idx = ∅) (W : Fin M → Plane) (hW : ∀ j, GExc D idx (P.v j) (W j)) :
    Concl7 D P ∨ Concl5 D P := by
  by_cases hdiff : ∃ j, W j ≠ W 0
  · obtain ⟨k, rfl⟩ := M_even_of_two_iso D P hreg idx hC hab hac h1 h3 G hcor hNK W hW hdiff
    exact Or.inr (lemma63_two_full_iso D P hreg idx hC hab hac h1 h3 G hcor hNK W hW hdiff)
  · push Not at hdiff
    exact Or.inl (lemma63_one_iso D P hreg idx hC hab hac h1 h3 G hcor W hW (fun j => hdiff j))

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.lemma63_one_iso
#print axioms Erdos634.Draft.LaczFormal.RG.lemma63_two_iso
#print axioms Erdos634.Draft.LaczFormal.RG.M_even_of_two_iso
#print axioms Erdos634.Draft.LaczFormal.RG.g11_two_iso
#print axioms Erdos634.Draft.LaczFormal.RG.lemma63_two_full_iso
#print axioms Erdos634.Draft.LaczFormal.RG.lemma63_full_iso
