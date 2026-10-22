-- Draft/LaczFormalRG12L61Count.lean -- Laczkovich DCG 48 (2012), Lemma 6.1 (Subcase IIc), the counting part.  `lemma61_core`: Case C (`Gamma_c` empty), `gamma < pi/2`, `gamma != pi/3`: either every polygon vertex
-- is of type `alpha+beta` (`P = N`, the paper's remaining case) or `N = 4` with corners `gamma, alpha+beta, gamma, alpha+beta` and each `gamma` corner a single `gamma` (the parallelogram of conclusion (i)).
-- `P = N-1` is impossible: one exceptional point at most (`caseII_exc_count`), so one of the two pairs of sides next to the single `gamma` vertex is free and `gamma_prop_fwd/bwd` produces a second `gamma` vertex.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), proof of Lemma 6.1), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12L61Prop
import Erdos634.Draft.LaczFormalRG11IIa
import Erdos634.Draft.LaczFormalRG9Sides

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- `k γ = π` with `0 < γ < π/2`, `γ ≠ π/3` forces `k ≥ 4`. -/
theorem gamma_mult_ge4 {γ : ℝ} (h0 : 0 < γ) (h1 : γ < Real.pi / 2) (h3 : γ ≠ Real.pi / 3) (k : ℕ) (hk : (k : ℝ) * γ = Real.pi) : 4 ≤ k := by
  have hpi := Real.pi_pos
  by_contra hlt
  push Not at hlt
  interval_cases k
  · simp at hk; linarith
  · simp at hk; linarith
  · norm_num at hk; linarith
  · apply h3; norm_num at hk; linarith

theorem fin_four_facts (hM : 4 ≤ M) (x : Fin M) : x ≠ x - 2 ∧ x ≠ x - 1 ∧ x + 1 ≠ x - 2 ∧ x + 1 ≠ x - 1 := by
  have hM3 : 3 ≤ M := by omega
  have f1 := ConvPoly.fin_facts hM3 (x - 1)
  have f0 := ConvPoly.fin_facts hM3 x
  have hxx : x - 1 + 1 = x := sub_add_cancel x 1
  have hxxx : x - 1 - 1 = x - 2 := by rw [sub_sub, fin_one_add_one]
  refine ⟨?_, ?_, ?_, f0.2.2.2.1⟩
  · have := f1.2.2.2.1
    rw [hxx, hxxx] at this
    exact this
  · have := f1.1
    rw [hxx] at this
    exact this
  · intro hh
    have e : (x + 1) - (x - 2) = 1 + 2 := by abel
    rw [hh, sub_self] at e
    have e2 := congrArg Fin.val e.symm
    rw [Fin.val_add, fin_val_one, fin_val_two, Nat.mod_eq_of_lt (by omega : 1 < M), Nat.mod_eq_of_lt (by omega : 2 < M),
      Nat.mod_eq_of_lt (by omega : 1 + 2 < M), fin_val_zero] at e2
    omega

/-- Each polygon vertex is of type `α+β` (counts `(1,1,0)`) or consists of `γ`'s only (counts `(0,0,r)`, `r ≥ 1`). -/
theorem vtx_dich (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (j : Fin M) :
    (cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0 ∧ P.angle j = Real.pi - D.model.angleAt 2) ∨
    (cnt D idx (P.v j) 0 = 0 ∧ cnt D idx (P.v j) 1 = 0 ∧ 1 ≤ cnt D idx (P.v j) 2 ∧ P.angle j = (cnt D idx (P.v j) 2 : ℝ) * D.model.angleAt 2) := by
  have := caseII_polyvertex D P hreg idx h.hidxA h.hregc h1 (j - 1)
  rw [sub_add_cancel] at this
  have hr := h.hregc (P.v j)
  rcases this with ⟨a, b, c⟩ | ⟨a, b, c⟩
  · exact Or.inl ⟨a, by omega, b, c⟩
  · exact Or.inr ⟨a, by omega, b, c⟩

theorem normSide_of_good (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3)
    (i : Fin M) (hb : ¬ SideBad2 D idx P i) : NormSide D idx P i := by
  intro V hv ⟨t, ht0, ht1, hVt⟩
  have hne : V ∉ excVerts2 D idx P := fun hex => hb ⟨V, hex, t, ht0, ht1, hVt⟩
  exact caseII_normal_side D P hreg idx h.hidxA h.hregc h1 h3 ht0 ht1 hVt hv hne

/-- Two adjacent corners consisting of `γ` only are impossible along a side with normal interior vertices. -/
theorem adj_G (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx) (i : Fin M) (hn : NormSide D idx P i)
    (g1 : cnt D idx (P.v i) 0 = 0) (g2 : cnt D idx (P.v (i + 1)) 0 = 0) : False := by
  have e : i - 1 + 1 = i := sub_add_cancel i 1
  have r1 := h.hregc (P.v i)
  have r2 := h.hregc (P.v (i + 1))
  exact no_adjacent_gamma D P hreg idx h (i - 1) (by rw [e]; exact hn) (by rw [e]; exact ⟨g1, by omega⟩) (by rw [e]; exact ⟨g2, by omega⟩)


set_option maxHeartbeats 6400000 in
/-- **Lemma 6.1, core** (Laczkovich DCG 48 (2012), Sect. 6.3): Case C, `γ < π/2`, `γ ≠ π/3`.  Either every corner of the polygon is of type `α+β` (`P = M`), or `M = 4` with angles `γ, π-γ, γ` at three
consecutive vertices (the parallelogram).  (`P = M-1` is impossible; `P = M-2` gives the parallelogram.) -/
theorem lemma61_core (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) :
    cntP0 D idx P = M ∨ (M = 4 ∧ ∃ a : Fin M, P.angle (a + 1) = D.model.angleAt 2 ∧ P.angle (a + 2) = Real.pi - D.model.angleAt 2 ∧ P.angle (a + 3) = D.model.angleAt 2) := by
  classical
  have hpi := Real.pi_pos
  have hγ0 := model_angle_pos' D 2
  have hM3 := ConvPoly.three_le P
  obtain ⟨hRP, hMP, hexc, hang⟩ := caseII_exc_count D P hreg idx h.hidxA h.hregc h1 h3
  have hd := vtx_dich D P hreg idx h h1
  have hreg0 := h.hregc
  set Gs : Finset (Fin M) := Finset.univ.filter (fun j => cnt D idx (P.v j) 0 = 0) with hGs
  have hmemG : ∀ j, j ∈ Gs ↔ cnt D idx (P.v j) 0 = 0 := fun j => by simp [hGs]
  have hsumP : cntP0 D idx P = ∑ j : Fin M, cnt D idx (P.v j) 0 :=
    Equiv.sum_comp (Equiv.addRight (1 : Fin M)) (fun j => cnt D idx (P.v j) 0)
  have hsumR : cntR2 D idx P = ∑ j : Fin M, cnt D idx (P.v j) 2 :=
    Equiv.sum_comp (Equiv.addRight (1 : Fin M)) (fun j => cnt D idx (P.v j) 2)
  have hPG : cntP0 D idx P + Gs.card = M := by
    have e1 : ∑ j : Fin M, cnt D idx (P.v j) 0 = (Finset.univ.filter (fun j : Fin M => ¬ cnt D idx (P.v j) 0 = 0)).card := by
      rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro j _
      rcases hd j with ⟨a, -⟩ | ⟨a, -⟩ <;> simp [a]
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin M))) (fun j : Fin M => cnt D idx (P.v j) 0 = 0)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    have hGc : Gs.card = (Finset.univ.filter (fun j : Fin M => cnt D idx (P.v j) 0 = 0)).card := rfl
    rw [hsumP, e1]
    omega
  have hcz : ∀ j, ¬ cnt D idx (P.v j) 0 = 0 → cnt D idx (P.v j) 2 = 0 := by
    intro j hj
    rcases hd j with ⟨-, -, a, -⟩ | ⟨a, -⟩
    · exact a
    · exact absurd a hj
  have hbad := sideBad2_card_b D idx P hreg
  have hfl := Finset.card_filter_le (excVerts2 D idx P) (fun v => v ∉ interior D.region)
  rcases (by omega : Gs.card = 0 ∨ Gs.card = 1 ∨ Gs.card = 2) with hs | hs | hs
  · left; omega
  · -- `P = M - 1`: impossible
    exfalso
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hs
    have hGx : ∀ j, cnt D idx (P.v j) 0 = 0 ↔ j = x := fun j => by
      have := Finset.ext_iff.mp hx j
      rw [hmemG, Finset.mem_singleton] at this
      exact this
    have hPeq : cntP0 D idx P + 1 = M := by omega
    -- `M ≥ 5`
    have hM4 : 4 ≤ M := by
      have hkR : ((cntP0 D idx P - cntR2 D idx P : ℕ) : ℝ) * D.model.angleAt 2 = Real.pi := by
        rw [Nat.cast_sub hRP]
        have : ((cntP0 D idx P : ℝ) - M + 2) = 1 := by
          have : (M : ℝ) = (cntP0 D idx P : ℝ) + 1 := by exact_mod_cast hPeq.symm
          linarith
        rw [hang, this, one_mul]
      have := gamma_mult_ge4 hγ0 h1 h3 _ hkR
      omega
    have hbad1 : (Finset.univ.filter (SideBad2 D idx P)).card ≤ 1 := by omega
    have hbad_le : ∀ a b : Fin M, SideBad2 D idx P a → SideBad2 D idx P b → a = b := by
      intro a b ha hb
      by_contra hne
      have hsub : ({a, b} : Finset (Fin M)) ⊆ Finset.univ.filter (SideBad2 D idx P) := by
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hi with rfl | rfl <;> assumption
      have := Finset.card_le_card hsub
      rw [Finset.card_pair hne] at this
      omega
    have hxG : cnt D idx (P.v x) 0 = 0 := (hGx x).mpr rfl
    have hnG : ∀ j, j ≠ x → cnt D idx (P.v j) 2 = 0 := fun j hj => hcz j (fun e => hj ((hGx j).mp e))
    have hf0 := ConvPoly.fin_facts hM3 x
    have f4 := fin_four_facts hM4 x
    have notG : ∀ j, 1 ≤ cnt D idx (P.v j) 2 → j = x := by
      intro j hj
      by_contra hne
      have := hnG j hne
      omega
    by_cases hfw : ¬ SideBad2 D idx P x ∧ ¬ SideBad2 D idx P (x + 1)
    · have hn1 := normSide_of_good D P hreg idx h h1 h3 x hfw.1
      have hn2 := normSide_of_good D P hreg idx h h1 h3 (x + 1) hfw.2
      have := gamma_prop_fwd D P hreg idx h x hn1 hn2 hxG (by rw [← hreg0]; exact hxG) (hnG (x + 1) hf0.1)
      have := notG _ this
      rw [hf0.2.2.2.2.2] at this
      exact hf0.2.1 this
    · by_cases hbw : ¬ SideBad2 D idx P (x - 2) ∧ ¬ SideBad2 D idx P (x - 1)
      · have e1 : x - 2 + 1 = x - 1 := by rw [← fin_one_add_one]; abel
        have e2 : x - 2 + 1 + 1 = x := by rw [e1]; exact sub_add_cancel x 1
        have hn1 := normSide_of_good D P hreg idx h h1 h3 (x - 2) hbw.1
        have hn2 := normSide_of_good D P hreg idx h h1 h3 (x - 2 + 1) (by rw [e1]; exact hbw.2)
        have hY : cnt D idx (P.v (x - 2 + 1)) 2 = 0 := by
          rw [e1]; exact hnG (x - 1) f4.2.1.symm
        have := gamma_prop_bwd D P hreg idx h (x - 2) hn1 hn2 (by rw [e2]; exact hxG) (by rw [e2, ← hreg0]; exact hxG) hY
        have := notG _ this
        exact f4.1 this.symm
      · -- one bad side in each pair: two distinct bad sides
        have hb1 : SideBad2 D idx P x ∨ SideBad2 D idx P (x + 1) := by
          by_contra hh; push Not at hh; exact hfw ⟨hh.1, hh.2⟩
        have hb2 : SideBad2 D idx P (x - 2) ∨ SideBad2 D idx P (x - 1) := by
          by_contra hh; push Not at hh; exact hbw ⟨hh.1, hh.2⟩
        rcases hb1 with b1 | b1 <;> rcases hb2 with b2 | b2
        · exact f4.1 (hbad_le _ _ b1 b2)
        · exact f4.2.1 (hbad_le _ _ b1 b2)
        · exact f4.2.2.1 (hbad_le _ _ b1 b2)
        · exact f4.2.2.2 (hbad_le _ _ b1 b2)
  · -- `P = M - 2`: the parallelogram
    right
    have hPeq : cntP0 D idx P + 2 = M := by omega
    have hexc0 : (excVerts2 D idx P).card = 0 := by omega
    have hgood : ∀ i, ¬ SideBad2 D idx P i := by
      intro i hi
      obtain ⟨X, hX, -⟩ := hi
      have := Finset.card_pos.mpr ⟨X, hX⟩
      omega
    have hN : ∀ i, NormSide D idx P i := fun i => normSide_of_good D P hreg idx h h1 h3 i (hgood i)
    have hstep : ∀ j, cnt D idx (P.v j) 0 = 0 → cnt D idx (P.v (j + 2)) 0 = 0 := by
      intro j hj
      have hf0 := ConvPoly.fin_facts hM3 j
      have hj1 : ¬ cnt D idx (P.v (j + 1)) 0 = 0 := fun hh => adj_G D P hreg idx h j (hN j) hj hh
      have := gamma_prop_fwd D P hreg idx h j (hN j) (hN (j + 1)) hj (by rw [← hreg0]; exact hj) (hcz _ hj1)
      rw [hf0.2.2.2.2.2] at this
      rcases hd (j + 2) with ⟨-, -, a, -⟩ | ⟨a, -⟩
      · omega
      · exact a
    obtain ⟨a0, b0, hab, hGe⟩ := Finset.card_eq_two.mp hs
    have ha0 : cnt D idx (P.v a0) 0 = 0 := (hmemG a0).mp (by rw [hGe]; simp)
    set x := a0 with hxdef
    have hf0 := ConvPoly.fin_facts hM3 x
    have hx2 : cnt D idx (P.v (x + 2)) 0 = 0 := hstep x ha0
    have hGx : Gs = {x, x + 2} := by
      have hmem : x + 2 ∈ Gs := (hmemG _).mpr hx2
      rw [hGe] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with e | e
      · exact absurd e hf0.2.1
      · rw [hGe, e]
    have hf2 := ConvPoly.fin_facts hM3 (x + 2)
    have hx4 : cnt D idx (P.v (x + 2 + 2)) 0 = 0 := hstep _ hx2
    have hx4' : x + 2 + 2 = x := by
      have hmem : x + 2 + 2 ∈ Gs := (hmemG _).mpr hx4
      rw [hGx] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with e | e
      · exact e
      · exact absurd e hf2.2.1
    have h22 : (2 : Fin M) + 2 = 0 := by
      have e : (x + 2 + 2) - x = 2 + 2 := by abel
      rw [hx4', sub_self] at e
      exact e.symm
    have hdvd : M ∣ 4 := by
      have e2 := congrArg Fin.val h22
      rw [Fin.val_add, fin_val_two, Nat.mod_eq_of_lt (by omega : 2 < M), fin_val_zero] at e2
      exact Nat.dvd_of_mod_eq_zero e2
    have hM4 : M = 4 := by
      have := Nat.le_of_dvd (by norm_num) hdvd
      rcases (by omega : M = 3 ∨ M = 4) with e | e
      · exfalso; rw [e] at hdvd; omega
      · exact e
    -- the two `γ` corners are single
    have hRP' : cntR2 D idx P = cntP0 D idx P := by
      have hz : ((cntP0 D idx P : ℝ) - cntR2 D idx P) * D.model.angleAt 2 = 0 := by
        rw [hang]
        have : ((cntP0 D idx P : ℝ) - M + 2) = 0 := by
          have : (M : ℝ) = (cntP0 D idx P : ℝ) + 2 := by exact_mod_cast hPeq.symm
          linarith
        rw [this, zero_mul]
      rcases mul_eq_zero.mp hz with e | e
      · have : (cntP0 D idx P : ℝ) = cntR2 D idx P := by linarith
        exact_mod_cast this.symm
      · linarith
    have hRsum : cntR2 D idx P = cnt D idx (P.v x) 2 + cnt D idx (P.v (x + 2)) 2 := by
      rw [hsumR]
      have hsub : ∑ j ∈ Gs, cnt D idx (P.v j) 2 = ∑ j : Fin M, cnt D idx (P.v j) 2 :=
        Finset.sum_subset (Finset.subset_univ Gs) (fun j _ hj => hcz j (fun e => hj ((hmemG j).mpr e)))
      rw [← hsub, hGx, Finset.sum_pair (Ne.symm hf0.2.1)]
    have hc1 : 1 ≤ cnt D idx (P.v x) 2 := by
      rcases hd x with ⟨a, -⟩ | ⟨-, -, a, -⟩
      · omega
      · exact a
    have hc2 : 1 ≤ cnt D idx (P.v (x + 2)) 2 := by
      rcases hd (x + 2) with ⟨a, -⟩ | ⟨-, -, a, -⟩
      · omega
      · exact a
    have hcnt1 : cnt D idx (P.v x) 2 = 1 := by omega
    have hcnt2 : cnt D idx (P.v (x + 2)) 2 = 1 := by omega
    have hangx : P.angle x = D.model.angleAt 2 := by
      rcases hd x with ⟨a, -⟩ | ⟨-, -, -, a⟩
      · omega
      · rw [a, hcnt1]; simp
    have hangx2 : P.angle (x + 2) = D.model.angleAt 2 := by
      rcases hd (x + 2) with ⟨a, -⟩ | ⟨-, -, -, a⟩
      · omega
      · rw [a, hcnt2]; simp
    have hx1 : cnt D idx (P.v (x + 1)) 0 = 1 := by
      by_contra hne
      have hz : cnt D idx (P.v (x + 1)) 0 = 0 := by
        rcases hd (x + 1) with ⟨a, -⟩ | ⟨a, -⟩
        · exact absurd a hne
        · exact a
      have hmem : x + 1 ∈ Gs := (hmemG _).mpr hz
      rw [hGx] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with e | e
      · exact hf0.1 e
      · exact hf0.2.2.1 e.symm
    have hangx1 : P.angle (x + 1) = Real.pi - D.model.angleAt 2 := by
      rcases hd (x + 1) with ⟨-, -, -, a⟩ | ⟨a, -⟩
      · exact a
      · omega
    subst hM4
    refine ⟨rfl, x - 1, ?_, ?_, ?_⟩
    · have e : x - 1 + 1 = x := sub_add_cancel x 1
      rw [e]; exact hangx
    · have e : ∀ y : Fin 4, y - 1 + 2 = y + 1 := by decide
      rw [e]; exact hangx1
    · have e : ∀ y : Fin 4, y - 1 + 3 = y + 2 := by decide
      rw [e]; exact hangx2

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.lemma61_core
