-- Draft/LaczFormalIIIaCornerClose.lean -- Laczkovich DCG 48 (2012) Case IIIa (and IIIb after relabelling), polygon targets, gamma = 2 pi/3: the CORNER-SIDE half of the L71 counting repair
-- (audit (private working notes, not included) gaps 2, 4, 5).  What is proved here, with the DEFECT BOUND as an explicit hypothesis `hdef`:
--   * `corner_units`/`corner_data`: each polygon vertex carries (cnt0, cnt2) in {(1,0),(2,0),(0,1)} (angle pi/3, 2 pi/3, 2 pi/3), and the units sum to 3 (M-2);
--   * `caseIII_close`: if the number of non-clean sides (a side is clean iff `NormSide` and `NoEdgeSide`, the two hypotheses of Lemma 4.3) satisfies  3 * #nonclean + P <= R
--     (P = sum of cnt0, R = sum of cnt2 over the polygon vertices; to be supplied by `caseIII_defects` of another session), then M = 4, the corners are (G, A, G, A), and every side is clean;
--     the pigeonhole of the audit (a clean side with single-gamma corners at both ends) is closed by `side_no_gg_a` (Lemma 4.3 (i)), the `gamma at tail/head` fact is extracted exactly as in `caseI_a`;
--   * `caseIII_concl1`: in that case Conclusion (i) of Theorem 2.1 (Lemma 4.3 (ii) `gamma_vertex_multiple` + Lemma 4.1 `lemma41_poly`, parallelogram via `quad_parallelogram_gen`).
-- The parallelogram identity v0+v2=v1+v3 from the angles was ALREADY `quad_parallelogram_gen` (RG9Geo): audit gap 5 needed no new geometry.
-- NOTE, UNAUDITED.  The defect bound `hdef` is NOT proved here; non-vacuity of the rest: see LaczFormalIIIaCornerComb (arrangements) and the file end (hypothesis shape).
-- Credit: Laczkovich (DCG 48 (2012), Sect. 4, 7, Lemmas 4.1-4.3), Beeson-Zhang (arXiv 2604.01314), Beeson.
import Erdos634.Draft.LaczFormalRG9Ia3
import Erdos634.Draft.LaczFormalRG3Comm
import Erdos634.Draft.LaczFormalIIIaCornerComb

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- **The units at a polygon vertex**: `(cnt0 + 2 cnt2) (π/3)` is the polygon angle (regular tiling, `α+β = π/3`, `γ = 2π/3`). -/
theorem corner_units (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hγ : D.model.angleAt 2 = 2 * Real.pi / 3) (hαβ : D.model.angleAt 0 + D.model.angleAt 1 = Real.pi / 3)
    (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1) (k : Fin M) :
    ((cnt D idx (P.v (k + 1)) 0 + 2 * cnt D idx (P.v (k + 1)) 2 : ℕ) : ℝ) * (Real.pi / 3) = P.angle (k + 1) := by
  have hv0 : ∃ j k', (D.tile j).pts k' = P.v (k + 1) := poly_vertex_is_tile_vertex D.toRegionDissection P hreg (k + 1)
  have hcA := corner_A D P hreg idx hidxA k hv0
  have hexp : Asum D idx (P.v (k + 1)) = (cnt D idx (P.v (k + 1)) 0 : ℝ) * D.model.angleAt 0 + (cnt D idx (P.v (k + 1)) 1 : ℝ) * D.model.angleAt 1 + (cnt D idx (P.v (k + 1)) 2 : ℝ) * D.model.angleAt 2 := by
    unfold Asum; rw [Fin.sum_univ_three]
  have hr : ((cnt D idx (P.v (k + 1)) 0 : ℕ) : ℝ) = (cnt D idx (P.v (k + 1)) 1 : ℕ) := by exact_mod_cast hregc _
  rw [← hcA, hexp, ← hr]
  push_cast
  rw [hγ]
  linear_combination (-(cnt D idx (P.v (k + 1)) 0 : ℝ)) * hαβ

/-- The corner data: types `(1,0), (2,0), (0,1)` and the unit sum `3 (M-2)`. -/
theorem corner_data (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hγ : D.model.angleAt 2 = 2 * Real.pi / 3) (hαβ : D.model.angleAt 0 + D.model.angleAt 1 = Real.pi / 3)
    (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1) :
    (∀ k : Fin M, (cnt D idx (P.v (k + 1)) 0 = 1 ∧ cnt D idx (P.v (k + 1)) 2 = 0) ∨ (cnt D idx (P.v (k + 1)) 0 = 2 ∧ cnt D idx (P.v (k + 1)) 2 = 0) ∨
      (cnt D idx (P.v (k + 1)) 0 = 0 ∧ cnt D idx (P.v (k + 1)) 2 = 1)) ∧
    ∑ k : Fin M, (cnt D idx (P.v (k + 1)) 0 + 2 * cnt D idx (P.v (k + 1)) 2) = 3 * (M - 2) := by
  have hpi := Real.pi_pos
  have hU := corner_units D P hreg idx hidxA hγ hαβ hregc
  have hang := polygon_angle_2pi3 D P hreg idx hidxA hγ hαβ hregc
  have hpi3 : (Real.pi / 3) ≠ 0 := by positivity
  have hty : ∀ k : Fin M, (cnt D idx (P.v (k + 1)) 0 + 2 * cnt D idx (P.v (k + 1)) 2 = 1) ∨ (cnt D idx (P.v (k + 1)) 0 + 2 * cnt D idx (P.v (k + 1)) 2 = 2) := by
    intro k
    have e := hU k
    rcases hang k with h | h
    · left
      rw [h] at e
      have := mul_right_cancel₀ hpi3 (show ((cnt D idx (P.v (k + 1)) 0 + 2 * cnt D idx (P.v (k + 1)) 2 : ℕ) : ℝ) * (Real.pi / 3) = ((1 : ℕ) : ℝ) * (Real.pi / 3) by rw [e]; push_cast; ring)
      exact_mod_cast this
    · right
      rw [h] at e
      have := mul_right_cancel₀ hpi3 (show ((cnt D idx (P.v (k + 1)) 0 + 2 * cnt D idx (P.v (k + 1)) 2 : ℕ) : ℝ) * (Real.pi / 3) = ((2 : ℕ) : ℝ) * (Real.pi / 3) by rw [e]; push_cast; ring)
      exact_mod_cast this
  refine ⟨fun k => by rcases hty k with h | h <;> omega, ?_⟩
  have hR : ∑ k : Fin M, (((cnt D idx (P.v (k + 1)) 0 + 2 * cnt D idx (P.v (k + 1)) 2 : ℕ) : ℝ) * (Real.pi / 3)) = ((M - 2 : ℕ) : ℝ) * Real.pi := by
    rw [Finset.sum_congr rfl (fun k _ => hU k)]
    rw [← poly_angle_sum P]
    exact Equiv.sum_comp (Equiv.addRight (1 : Fin M)) (fun i => P.angle i)
  rw [← Finset.sum_mul] at hR
  have hM3 : 3 ≤ M := P.three_le
  have hMr : ((M - 2 : ℕ) : ℝ) = (M : ℝ) - 2 := by rw [Nat.cast_sub (by omega)]; norm_num
  have := mul_right_cancel₀ hpi3 (show (∑ k : Fin M, ((cnt D idx (P.v (k + 1)) 0 + 2 * cnt D idx (P.v (k + 1)) 2 : ℕ) : ℝ)) * (Real.pi / 3) = (((3 * (M - 2) : ℕ)) : ℝ) * (Real.pi / 3) by
    rw [hR, hMr]; push_cast; rw [Nat.cast_sub (by omega)]; push_cast; ring)
  exact_mod_cast this

theorem fin4_sum_shift (f : Fin 4 → ℕ) (a : Fin 4) : ∑ k, f k = f a + f (a + 1) + f (a + 2) + f (a + 3) := by
  fin_cases a <;> simp [Fin.sum_univ_four] <;> omega

set_option maxHeartbeats 3200000 in
/-- **IIIa/IIIb corner-side closure** (see the file header).  `hdef`: `3 * (#non-clean sides) + P <= R`. -/
theorem caseIII_close (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseA D idx) (hγ : D.model.angleAt 2 = 2 * Real.pi / 3)
    (hdef : 3 * (Finset.univ.filter (fun i : Fin M => ¬ (NormSide D idx P i ∧ NoEdgeSide D P i))).card + ∑ k : Fin M, cnt D idx (P.v (k + 1)) 0
      ≤ ∑ k : Fin M, cnt D idx (P.v (k + 1)) 2) :
    M = 4 ∧ (∃ a : Fin M, P.angle (a + 1) = D.model.angleAt 2 ∧ P.angle (a + 1 + 1) = Real.pi - D.model.angleAt 2 ∧ P.angle (a + 2 + 1) = D.model.angleAt 2 ∧
      cnt D idx (P.v (a + 1)) 0 = 0 ∧ cnt D idx (P.v (a + 1)) 2 = 1) ∧ ∀ i : Fin M, NormSide D idx P i ∧ NoEdgeSide D P i := by
  classical
  have hpi := Real.pi_pos
  have hαβ : D.model.angleAt 0 + D.model.angleAt 1 = Real.pi / 3 := by
    have := Erdos634.Draft.LaczFormal.angleAt_sum D.model
    linarith
  obtain ⟨hty, hsum⟩ := corner_data D P hreg idx h.hidxA hγ hαβ h.hregc
  obtain ⟨-, -, hcomb⟩ := corner_comb P.three_le (fun k => cnt D idx (P.v (k + 1)) 0) (fun k => cnt D idx (P.v (k + 1)) 2) hty hsum
  set S : Finset (Fin M) := Finset.univ.filter (fun i : Fin M => ¬ (NormSide D idx P i ∧ NoEdgeSide D P i)) with hS
  have hU := corner_units D P hreg idx h.hidxA hγ hαβ h.hregc
  rcases hcomb with h1 | h2 | ⟨hM4, a, ha, hb, hc, hd⟩
  · exfalso; omega
  · exfalso
    have hlt : S.card < (Finset.univ.filter (fun i : Fin M => cnt D idx (P.v (i - 1 + 1)) 2 = 1 ∧ cnt D idx (P.v (i + 1)) 2 = 1)).card := by
      omega
    obtain ⟨i, hiG, hiS⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hiG
    have hb : NormSide D idx P i ∧ NoEdgeSide D P i := by
      by_contra hn; exact hiS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)
    obtain ⟨c1, c2⟩ := hiG
    obtain ⟨hn, hno⟩ := hb
    obtain ⟨L, e0, el, hW, hh, hl, hs1, hs2, hT0, hT1⟩ := edge_data D P hreg i
    rw [sub_add_cancel] at c1
    have z1 : cnt D idx (P.v i) 0 = 0 := by
      have := hty (i - 1)
      rw [sub_add_cancel] at this
      omega
    have z2 : cnt D idx (P.v (i + 1)) 0 = 0 := by
      have := hty i
      omega
    have t0 : TyAt D idx e0.1 e0.2.1 2 := fun kk hkk => idx_two_of_cnt D idx z1 (by rw [← h.hregc]; exact z1) (hkk.trans hs1)
    have t1 : TyAt D idx el.1 el.2.2 2 := fun kk hkk => idx_two_of_cnt D idx z2 (by rw [← h.hregc]; exact z2) (hkk.trans hs2)
    exact side_no_gg_a D P hreg idx h i hn hno hW hh hl t0 t1
  · -- the parallelogram pattern (G, A, G, A)
    subst hM4
    have h3 := fin4_sum_shift (fun k => cnt D idx (P.v (k + 1)) 0) a
    have h4 := fin4_sum_shift (fun k => cnt D idx (P.v (k + 1)) 2) a
    have h5 := fin4_sum_shift (fun k => cnt D idx (P.v (k + 1)) 0 + 2 * cnt D idx (P.v (k + 1)) 2) a
    simp only at h3 h4 h5
    have hx3 := hty (a + 3)
    have hxa := hty a
    have hxa1 := hty (a + 1)
    have hxa2 := hty (a + 2)
    have hS0 : S.card = 0 := by omega
    have hall : ∀ i : Fin 4, NormSide D idx P i ∧ NoEdgeSide D P i := by
      intro i
      by_contra hn
      have : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩
      rw [Finset.card_eq_zero] at hS0
      rw [hS0] at this; simp at this
    have e11 : ∀ e : Fin 4, e + 1 + 1 = e + 2 := by decide
    refine ⟨rfl, ⟨a, ?_, ?_, ?_, ?_, ha⟩, hall⟩
    · have := hU a
      rw [hγ]
      have hn0 : cnt D idx (P.v (a + 1)) 0 = 0 := by omega
      rw [← this, hn0, ha]; push_cast; ring
    · have := hU (a + 1)
      have hn0 : cnt D idx (P.v (a + 1 + 1)) 0 = 1 := by omega
      have hn2 : cnt D idx (P.v (a + 1 + 1)) 2 = 0 := by omega
      rw [hγ, ← this, hn0, hn2]; push_cast; ring
    · have := hU (a + 2)
      have hn0 : cnt D idx (P.v (a + 2 + 1)) 0 = 0 := by omega
      have hn2 : cnt D idx (P.v (a + 2 + 1)) 2 = 1 := by omega
      rw [hγ, ← this, hn0, hn2]; push_cast; ring
    · omega

set_option maxHeartbeats 3200000 in
/-- **Conclusion (i) of Theorem 2.1 from the corner-side closure** (Case IIIa; IIIb by the relabelling of `caseIII_count'`, not done here).  Hypothesis `hdef` is the defect bound of the L71 repair
(`3 * #non-clean sides + P <= R`), supplied by another session's `caseIII_defects`; `NotComb a b c` is the IIIa hypothesis. -/
theorem caseIII_concl1 (T : PolyTiling N M) (idx : Fin N → Equiv.Perm (Fin 3)) (hA : ∀ i v, angleAt T.C.model (idx i v) = angleAt (T.C.tile i) v)
    (hcnt : ∀ X, cnt T.C idx X 0 = cnt T.C idx X 1) (hγ : angleAt T.C.model 2 = 2 * Real.pi / 3)
    (hnc : NotComb (slen T.C 0) (slen T.C 1) (slen T.C 2))
    (hdef : 3 * (Finset.univ.filter (fun i : Fin M => ¬ (NormSide T.C idx T.P i ∧ NoEdgeSide T.C T.P i))).card + ∑ k : Fin M, cnt T.C idx (T.P.v (k + 1)) 0
      ≤ ∑ k : Fin M, cnt T.C idx (T.P.v (k + 1)) 2) : Concl1 T.C T.P := by
  classical
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hidx := idx_dist_of_angle T.C idx hA
  have hCA : CaseA T.C idx := ⟨hidx, hA, hnc, hcnt⟩
  obtain ⟨hM4, ⟨a, ang1, ang2, ang3, c0, c2⟩, hall⟩ := caseIII_close T.C T.P T.region_eq idx hCA hγ hdef
  subst hM4
  have e11 : ∀ e : Fin 4, e + 1 + 1 = e + 2 := by decide
  have e21 : ∀ e : Fin 4, e + 2 + 1 = e + 3 := by decide
  rw [e11] at ang2
  rw [e21] at ang3
  have hI := hall a
  have hO := hall (a + 1)
  have hside := gamma_vertex_multiple T.C T.P T.region_eq idx hCA a c0 (by rw [← hcnt]; exact c0) c2 hI.1 hI.2 hO.1 hO.2
  exact concl1_of_gamma_para T a ang1 ang2 ang3 hside

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.caseIII_concl1
