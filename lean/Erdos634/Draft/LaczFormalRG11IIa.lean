-- Draft/LaczFormalRG11IIa.lean -- Laczkovich DCG 48 (2012), Sect. 6.1 (Case II, Subcase IIa: `gamma < pi/2`, `gamma != pi/3`, `a` not a nonnegative rational combination of `b, c`): the cases `P = M-1` and `P = M`
-- (`P` = number of polygon vertices of type `alpha+beta`; the printed text writes `R = N-1`, `R = N`, evidently a misprint for `P`, as the Case II summary at the end of Sect. 6 says) are impossible.
-- Route: counting (`caseII_exc_count`: `#exceptional <= P - M + 2`), blocked sides (`blocked_card`: `<= eb + 2 ei`), `2P - M` sides have both ends of type `alpha+beta`, `M >= 5`, hence an unblocked side with both ends
-- of type `alpha+beta`, which Lemma 4.3 (iii) (`side_no_ab_a`) forbids.  NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.1), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG11Block
import Erdos634.Draft.LaczFormalRG11Corner

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- Each polygon vertex carries at most one pair `α, β`; `P ≤ M`; and `P = #{vertices of type α+β}`. -/
theorem cntP0_eq_card (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1)
    (h1 : D.model.angleAt 2 < Real.pi / 2) :
    cntP0 D idx P = (Finset.univ.filter (fun k : Fin M => cnt D idx (P.v (k + 1)) 0 = 1)).card := by
  rw [Finset.card_filter]
  unfold cntP0
  apply Finset.sum_congr rfl
  intro k _
  rcases caseII_polyvertex D P hreg idx hidxA hregc h1 k with ⟨a, -, -⟩ | ⟨a, -, -⟩
  · simp [a]
  · simp [a]

/-- **Subcase IIa, `P ∈ {M-1, M}` impossible.**  Conclusion: `P = M - 2`. -/
theorem caseIIa_P_eq (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseA D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) :
    (cntP0 D idx P : ℤ) = M - 2 := by
  classical
  have hpi := Real.pi_pos
  have hγ0 := model_angle_pos' D 2
  obtain ⟨hRP, hMP, hexc, hang⟩ := caseII_exc_count D P hreg idx h.hidxA h.hregc h1 h3
  have hcard := cntP0_eq_card D P hreg idx h.hidxA h.hregc h1
  have hPM : cntP0 D idx P ≤ M := by
    rw [hcard]
    calc _ ≤ (Finset.univ : Finset (Fin M)).card := Finset.card_le_univ _
      _ = M := by simp
  have hM3 := ConvPoly.three_le P
  by_contra hne
  have hge : (M : ℤ) - 1 ≤ cntP0 D idx P := by omega
  -- M ≥ 5
  have hM5 : 5 ≤ M := by
    obtain ⟨k, hk⟩ : ∃ k, cntP0 D idx P = k + cntR2 D idx P := ⟨cntP0 D idx P - cntR2 D idx P, by omega⟩
    have hang' : (k : ℝ) * D.model.angleAt 2 = ((cntP0 D idx P : ℝ) - M + 2) * Real.pi := by
      have : ((cntP0 D idx P : ℝ) - cntR2 D idx P) = k := by rw [hk]; push_cast; ring
      rw [← this]; exact hang
    rcases (by omega : cntP0 D idx P = M - 1 ∨ cntP0 D idx P = M) with hc | hc
    · have hj : ((cntP0 D idx P : ℝ) - M + 2) = 1 := by
        have : (cntP0 D idx P : ℝ) = (M : ℝ) - 1 := by
          have := hc; have h' : (cntP0 D idx P : ℤ) = (M : ℤ) - 1 := by omega
          exact_mod_cast h'
        linarith
      rw [hj, one_mul] at hang'
      by_contra hlt
      have hk4 : k ≤ 3 := by omega
      interval_cases k
      · simp at hang'; linarith
      · simp at hang'; linarith
      · norm_num at hang'; linarith
      · apply h3; norm_num at hang'; linarith
    · have hj : ((cntP0 D idx P : ℝ) - M + 2) = 2 := by
        have : (cntP0 D idx P : ℝ) = (M : ℝ) := by exact_mod_cast hc
        linarith
      rw [hj] at hang'
      by_contra hlt
      have hk4 : (k : ℝ) ≤ 4 := by
        have : k ≤ M := by omega
        exact_mod_cast (by omega : k ≤ 4)
      nlinarith
  -- vertices of type `α+β`, sides with both ends of that type
  set T : Finset (Fin M) := Finset.univ.filter (fun k : Fin M => ¬ cnt D idx (P.v (k + 1)) 0 = 1) with hT
  have hTc : T.card + cntP0 D idx P = M := by
    rw [hcard, hT]
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin M))) (fun k : Fin M => cnt D idx (P.v (k + 1)) 0 = 1)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  set G : Finset (Fin M) := Finset.univ.filter (fun i : Fin M => cnt D idx (P.v (i - 1 + 1)) 0 = 1 ∧ cnt D idx (P.v (i + 1)) 0 = 1) with hG
  have hGc : M ≤ G.card + 2 * T.card := by
    have hsub : (Finset.univ : Finset (Fin M)) ⊆ G ∪ (T.image (fun k => k + 1) ∪ T) := by
      intro i _
      by_cases h0 : cnt D idx (P.v (i - 1 + 1)) 0 = 1
      · by_cases h2 : cnt D idx (P.v (i + 1)) 0 = 1
        · refine Finset.mem_union_left _ ?_
          rw [hG]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h0, h2⟩
        · refine Finset.mem_union_right _ (Finset.mem_union_right _ ?_)
          rw [hT]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h2
      · refine Finset.mem_union_right _ (Finset.mem_union_left _ ?_)
        rw [Finset.mem_image]
        refine ⟨i - 1, ?_, by simp⟩
        rw [hT]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h0
    have c1 := Finset.card_le_card hsub
    have c2 := Finset.card_union_le G (T.image (fun k => k + 1) ∪ T)
    have c3 := Finset.card_union_le (T.image (fun k => k + 1)) T
    have c4 : (T.image (fun k => k + 1)).card ≤ T.card := Finset.card_image_le
    simp only [Finset.card_univ, Fintype.card_fin] at c1
    omega
  have hblk := blocked_card D P hreg idx h h1 h3
  have hexc' := Finset.card_filter_add_card_filter_not (s := excVerts2 D idx P) (fun v => v ∈ interior D.region)
  -- an unblocked side with both ends of type `α+β`
  have hex : ∃ i ∈ G, ¬ Blocked D idx P i := by
    by_contra hall
    push Not at hall
    have hsub : G ⊆ Finset.univ.filter (Blocked D idx P) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hall i hi
    have := Finset.card_le_card hsub
    omega
  obtain ⟨i, hiG, hib⟩ := hex
  simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and] at hiG
  obtain ⟨gX, gY⟩ := hiG
  rw [sub_add_cancel] at gX
  have hbl : ¬ (SideBad2 D idx P i ∨ ZSide D P i) := fun hh => hib (by unfold Blocked; tauto)
  obtain ⟨hn, hno⟩ := side_hyps2 D P hreg idx h h1 h3 i hbl
  have hp0 : ¬ PEdge D P i := fun hh => hib (by unfold Blocked; tauto)
  have hp1 : ¬ PEdge D P (i + 1) := fun hh => hib (by unfold Blocked; tauto)
  have c2X : cnt D idx (P.v i) 2 = 0 := by
    have := caseII_polyvertex D P hreg idx h.hidxA h.hregc h1 (i - 1)
    rw [sub_add_cancel] at this
    rcases this with ⟨-, a, -⟩ | ⟨a, -, -⟩
    · exact a
    · omega
  have c2Y : cnt D idx (P.v (i + 1)) 2 = 0 := by
    rcases caseII_polyvertex D P hreg idx h.hidxA h.hregc h1 i with ⟨-, a, -⟩ | ⟨a, -, -⟩
    · exact a
    · omega
  exact side_no_ab_a D P hreg idx h i hn hno gX (by rw [← h.hregc]; exact gX) c2X gY (by rw [← h.hregc]; exact gY) c2Y
    (fun H hH => hp0 ⟨H, hH⟩) (fun H hH => hp1 ⟨H, hH⟩)

/-- **An unblocked side does not have both ends of type `α+β`** (Lemma 4.3 (iii)). -/
theorem no_adj_ab (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseA D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3)
    (i : Fin M) (hib : ¬ Blocked D idx P i) (gX : cnt D idx (P.v (i - 1 + 1)) 0 = 1) (gY : cnt D idx (P.v (i + 1)) 0 = 1) : False := by
  classical
  rw [sub_add_cancel] at gX
  have hbl : ¬ (SideBad2 D idx P i ∨ ZSide D P i) := fun hh => hib (by unfold Blocked; tauto)
  obtain ⟨hn, hno⟩ := side_hyps2 D P hreg idx h h1 h3 i hbl
  have hp0 : ¬ PEdge D P i := fun hh => hib (by unfold Blocked; tauto)
  have hp1 : ¬ PEdge D P (i + 1) := fun hh => hib (by unfold Blocked; tauto)
  have c2X : cnt D idx (P.v i) 2 = 0 := by
    have := caseII_polyvertex D P hreg idx h.hidxA h.hregc h1 (i - 1)
    rw [sub_add_cancel] at this
    rcases this with ⟨-, a, -⟩ | ⟨a, -, -⟩
    · exact a
    · omega
  have c2Y : cnt D idx (P.v (i + 1)) 2 = 0 := by
    rcases caseII_polyvertex D P hreg idx h.hidxA h.hregc h1 i with ⟨-, a, -⟩ | ⟨a, -, -⟩
    · exact a
    · omega
  exact side_no_ab_a D P hreg idx h i hn hno gX (by rw [← h.hregc]; exact gX) c2X gY (by rw [← h.hregc]; exact gY) c2Y
    (fun H hH => hp0 ⟨H, hH⟩) (fun H hH => hp1 ⟨H, hH⟩)

set_option maxHeartbeats 1600000 in
/-- **Subcase IIa, `P = M - 2`: the quadrilateral.**  Given `P = M-2`: `M = 4`, the corners are `α+β, γ, α+β, γ`, every side is unblocked. -/
theorem caseII_core (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseA D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) :
    (∀ i : Fin M, ¬ Blocked D idx P i) ∧ M = 4 ∧ (∃ a : Fin M, P.angle (a + 1) = D.model.angleAt 2 ∧ P.angle (a + 2) = Real.pi - D.model.angleAt 2 ∧
      P.angle (a + 3) = D.model.angleAt 2 ∧ cnt D idx (P.v (a + 1)) 0 = 0 ∧ cnt D idx (P.v (a + 1)) 2 = 1) := by
  classical
  have hpi := Real.pi_pos
  have hγ0 := model_angle_pos' D 2
  have hM3 := ConvPoly.three_le P
  have hP := caseIIa_P_eq D P hreg idx h h1 h3
  obtain ⟨hRP, hMP, hexc, hang⟩ := caseII_exc_count D P hreg idx h.hidxA h.hregc h1 h3
  have hexc0 : (excVerts2 D idx P).card = 0 := by omega
  have hblk := blocked_card D P hreg idx h h1 h3
  have hf1 := Finset.card_filter_le (excVerts2 D idx P) (fun v => v ∉ interior D.region)
  have hf2 := Finset.card_filter_le (excVerts2 D idx P) (fun v => v ∈ interior D.region)
  have hall : ∀ i : Fin M, ¬ Blocked D idx P i := by
    intro i hb
    have hz : (Finset.univ.filter (Blocked D idx P)).card = 0 := by omega
    rw [Finset.card_eq_zero] at hz
    have hmem : i ∈ Finset.univ.filter (Blocked D idx P) := by simp [hb]
    rw [hz] at hmem
    simp at hmem
  have hpoly := caseII_polyvertex D P hreg idx h.hidxA h.hregc h1
  have hadj : ∀ i : Fin M, ¬ (cnt D idx (P.v (i - 1 + 1)) 0 = 1 ∧ cnt D idx (P.v (i + 1)) 0 = 1) :=
    fun i hh => no_adj_ab D P hreg idx h h1 h3 i (hall i) hh.1 hh.2
  have hcard := cntP0_eq_card D P hreg idx h.hidxA h.hregc h1
  set T : Finset (Fin M) := Finset.univ.filter (fun k : Fin M => ¬ cnt D idx (P.v (k + 1)) 0 = 1) with hT
  have hTc : T.card + cntP0 D idx P = M := by
    rw [hcard, hT]
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin M))) (fun k : Fin M => cnt D idx (P.v (k + 1)) 0 = 1)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  have hM2T : M ≤ 2 * T.card := by
    have hsub : (Finset.univ : Finset (Fin M)) ⊆ (T.image (fun k => k + 1) ∪ T) := by
      intro i _
      by_cases h0 : cnt D idx (P.v (i - 1 + 1)) 0 = 1
      · have h2 : ¬ cnt D idx (P.v (i + 1)) 0 = 1 := fun h2 => hadj i ⟨h0, h2⟩
        refine Finset.mem_union_right _ ?_
        rw [hT]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h2
      · refine Finset.mem_union_left _ ?_
        rw [Finset.mem_image]
        refine ⟨i - 1, ?_, by simp⟩
        rw [hT]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h0
    have c1 := Finset.card_le_card hsub
    have c3 := Finset.card_union_le (T.image (fun k => k + 1)) T
    have c4 : (T.image (fun k => k + 1)).card ≤ T.card := Finset.card_image_le
    simp only [Finset.card_univ, Fintype.card_fin] at c1
    omega
  have hR2 : cntR2 D idx P = cntP0 D idx P := by
    have h0 : ((cntP0 D idx P : ℝ) - M + 2) = 0 := by
      have : (cntP0 D idx P : ℤ) = (M : ℤ) - 2 := hP
      have : (cntP0 D idx P : ℝ) = (M : ℝ) - 2 := by exact_mod_cast this
      linarith
    rw [h0, zero_mul] at hang
    rcases mul_eq_zero.mp hang with h0' | h0'
    · have : (cntP0 D idx P : ℝ) = cntR2 D idx P := by linarith
      exact_mod_cast this.symm
    · linarith
  have hsumPR : M ≤ cntP0 D idx P + cntR2 D idx P := by
    unfold cntP0 cntR2
    rw [← Finset.sum_add_distrib]
    have : ∑ _k : Fin M, 1 ≤ ∑ k : Fin M, (cnt D idx (P.v (k + 1)) 0 + cnt D idx (P.v (k + 1)) 2) := by
      apply Finset.sum_le_sum
      intro k _
      rcases hpoly k with ⟨h2, -, -⟩ | ⟨h2, h0, -⟩ <;> omega
    simpa using this
  have hPz : (cntP0 D idx P : ℤ) = (M : ℤ) - 2 := hP
  have hM4 : M = 4 := by omega
  refine ⟨hall, hM4, ?_⟩
  subst hM4
  have hP4 : cntP0 D idx P = 2 := by omega
  have hsumR : ∑ k : Fin 4, cnt D idx (P.v (k + 1)) 2 = 2 := by
    have h' : ∑ k : Fin 4, cnt D idx (P.v (k + 1)) 2 = cntR2 D idx P := rfl
    omega
  have hsumP : ∑ k : Fin 4, cnt D idx (P.v (k + 1)) 0 = 2 := by
    have h' : ∑ k : Fin 4, cnt D idx (P.v (k + 1)) 0 = cntP0 D idx P := rfl
    omega
  rw [Fin.sum_univ_four] at hsumR hsumP
  have a0 := hadj 0
  have a1 := hadj 1
  have a2 := hadj 2
  have a3 := hadj 3
  have e30 : (0 : Fin 4) - 1 + 1 = 0 := by decide
  have e01 : (1 : Fin 4) - 1 + 1 = 1 := by decide
  have e12 : (2 : Fin 4) - 1 + 1 = 2 := by decide
  have e23 : (3 : Fin 4) - 1 + 1 = 3 := by decide
  rw [e30] at a0
  rw [e01] at a1
  rw [e12] at a2
  rw [e23] at a3
  have e3 : (3 : Fin 4) + 1 = 0 := by decide
  have n0 := hpoly 0
  have n1 := hpoly 1
  have n2 := hpoly 2
  have n3 := hpoly 3
  have eA : (0 : Fin 4) + 1 = 1 := by decide
  have eB : (1 : Fin 4) + 1 = 2 := by decide
  have eC : (2 : Fin 4) + 1 = 3 := by decide
  simp only [eA, eB, eC, e3] at n0 n1 n2 n3 a0 a1 a2 a3 hsumR hsumP
  -- the pattern of corners
  have key : (cnt D idx (P.v 0) 0 = 1 ∧ cnt D idx (P.v 2) 0 = 1 ∧ cnt D idx (P.v 1) 0 = 0 ∧ cnt D idx (P.v 3) 0 = 0 ∧ cnt D idx (P.v 1) 2 = 1 ∧ cnt D idx (P.v 3) 2 = 1) ∨
      (cnt D idx (P.v 1) 0 = 1 ∧ cnt D idx (P.v 3) 0 = 1 ∧ cnt D idx (P.v 0) 0 = 0 ∧ cnt D idx (P.v 2) 0 = 0 ∧ cnt D idx (P.v 0) 2 = 1 ∧ cnt D idx (P.v 2) 2 = 1) := by
    rcases n0 with ⟨x0, y0, -⟩ | ⟨x0, y0, -⟩ <;> rcases n1 with ⟨x1, y1, -⟩ | ⟨x1, y1, -⟩ <;> rcases n2 with ⟨x2, y2, -⟩ | ⟨x2, y2, -⟩ <;>
      rcases n3 with ⟨x3, y3, -⟩ | ⟨x3, y3, -⟩ <;> omega
  rcases key with ⟨k0, k2, k1, k3, c1, c3⟩ | ⟨k1, k3, k0, k2, c0, c2⟩
  · refine ⟨0, ?_, ?_, ?_, k1, c1⟩
    · rcases n0 with ⟨x, -, -⟩ | ⟨-, -, ang⟩
      · omega
      · simpa [c1] using ang
    · rcases n1 with ⟨-, -, ang⟩ | ⟨x, -, -⟩
      · simpa using ang
      · omega
    · rcases n2 with ⟨x, -, -⟩ | ⟨-, -, ang⟩
      · omega
      · simpa [c3] using ang
  · refine ⟨3, ?_, ?_, ?_, ?_, ?_⟩
    · rcases n3 with ⟨x, -, -⟩ | ⟨-, -, ang⟩
      · omega
      · simpa [c0] using ang
    · rcases n0 with ⟨-, -, ang⟩ | ⟨x, -, -⟩
      · simpa using ang
      · omega
    · rcases n1 with ⟨x, -, -⟩ | ⟨-, -, ang⟩
      · omega
      · simpa [c2] using ang
    · simpa using k0
    · simpa using c0

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.caseIIa_P_eq
#print axioms Erdos634.Draft.LaczFormal.RG.caseII_core
