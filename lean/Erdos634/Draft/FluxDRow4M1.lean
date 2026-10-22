-- Draft/FluxDRow4M1.lean — ROW 4 (γ = 2α tile on the base-α target) with `N.Prime` replaced by the
-- weakest hypothesis the proof uses: `M1Div N` — no divisor m of N with 3 m² < N other than m = 1
-- (forces `M = 1` in `Row4.P5`).  Holds for every prime N and for N = 15.  Copies of `prime_leg_words`,
-- `prime_reduced`, `not_prime` with only that hypothesis changed (room ALLN, SCOPE_N15_L1 leaf G).
-- CONDITIONAL AT THE GEOMETRIC LEVEL exactly as `Row4.not_prime` (no Lean witness tiling).  UNAUDITED.
import Erdos634.Draft.FluxDRow4Bk

open scoped Classical

namespace Erdos634.Geometry

variable {N : ℕ}

/-- No divisor `m > 1` of `N` with `3 m² < N` (so `N = M M'`, `M' > 3M` forces `M = 1`). -/
def M1Div (N : ℕ) : Prop := ∀ m : ℕ, m ∣ N → 3 * (m * m) < N → m = 1

theorem M1Div_prime {N : ℕ} (hN : N.Prime) : M1Div N := by
  intro m hm h3
  rcases (Nat.dvd_prime hN).mp hm with h1 | h1
  · exact h1
  · exfalso; subst h1; nlinarith [hN.two_le]

theorem M1Div_fifteen : M1Div 15 := by
  intro m hm h3
  have : m ≤ 15 := Nat.le_of_dvd (by norm_num) hm
  interval_cases m <;> simp_all <;> omega

theorem Row4.leg_words_M1 (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    (hA : D.target.angleAt 0 = α) (hB : D.target.angleAt 1 = α) (hN : M1Div N) :
    ∃ k : ℕ, 2 ≤ k ∧ N = 2 * k + 1 ∧ D.target.oppLen 0 = a + c ∧
      (k : ℝ) * c = (k + 1) * a ∧ (k : ℝ) ^ 2 * b = N * a ∧
      ∀ p q r : ℕ, D.target.oppLen 0 = p * a + q * b + r * c →
        (p = 0 ∧ q = k ∧ r = 0) ∨ (p = 1 ∧ q = 0 ∧ r = 1) := by
  obtain ⟨M, M', hM0, hM'0, hM, hM', hNM, hM2, -, hlt, -, -, hab⟩ := Row4.P5 D hα h hA hB
  obtain ⟨κ, -, -, ha, -, -, -, -, -⟩ := Row4.sides D h hA hB
  -- C6: `M = 1` (a proper divisor of the prime `N`: `N = M·M′ > M` since `M′ > 3M ≥ 3`)
  have hM1 : M = 1 := by
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hM0.le
    have hmN : (m : ℤ) < N := by
      have := mul_pos hM0 (show (0 : ℤ) < M' - 1 by linarith)
      linarith
    have hdvd : m ∣ N := by
      have : (m : ℤ) ∣ (N : ℤ) := ⟨M', hNM⟩
      exact_mod_cast this
    have h3 : 3 * (m * m) < N := by
      have hMpos : (0 : ℤ) < m := hM0
      have : (3 : ℤ) * ((m : ℤ) * m) < N := by rw [hNM]; nlinarith
      exact_mod_cast this
    have := hN m hdvd h3
    rw [this]; norm_num
  subst hM1
  have hM'N : M' = N := by linarith
  have hN4 : 4 ≤ N := by omega
  obtain ⟨k, hk⟩ : ∃ k, N = 2 * k + 1 := ⟨(N - 1) / 2, by omega⟩
  have hk2 : 2 ≤ k := by omega
  -- the tile, read in `k`
  rw [hM'N] at hM'
  push_cast at hM hM'
  have hkN : (N : ℝ) = 2 * k + 1 := by rw [hk]; push_cast; ring
  have hkc : (k : ℝ) * c = (k + 1) * a := by
    linear_combination (1 / 2 : ℝ) * hM' - (1 / 2 : ℝ) * hM - (1 / 2 : ℝ) * (c - a) * hkN
  have hkb : (k : ℝ) ^ 2 * b = N * a := by
    have e : a * ((k : ℝ) ^ 2 * b - N * a) = 0 := by
      linear_combination (k : ℝ) ^ 2 * hab + ((k : ℝ) * c + (k + 1) * a) * hkc - a ^ 2 * hkN
    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left ha.ne')
  refine ⟨k, hk2, hk, by linear_combination -hM, hkc, hkb, fun p q r hw => ?_⟩
  apply Row4.L7 hk2
  have e : a * ((k : ℝ) * (2 * k + 1) - (p * k ^ 2 + q * (2 * k + 1) + r * (k * (k + 1)))) = 0 := by
    linear_combination (k : ℝ) ^ 2 * hM + (k : ℝ) ^ 2 * hw + ((r : ℝ) * k - k) * hkc
      + (q : ℝ) * hkb + (q : ℝ) * a * hkN
  have e2 := sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left ha.ne')
  exact_mod_cast e2

theorem Row4.reduced_M1 (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    (hA : D.target.angleAt 0 = α) (hC : D.target.angleAt 1 = α) (hN : M1Div N) :
    ∃ j : Fin 3, (j = 1 ∨ j = 2) ∧ ∃ k : ℕ, 2 ≤ k ∧ N = 2 * k + 1 ∧
      ((D.sideEdges j).filter (fun e => D.eLen e = b)).card = k ∧
      ∀ e ∈ D.sideEdges j, D.eLen e = b := by
  obtain ⟨k, hk2, hNk, -, -, -, hwords⟩ := Row4.leg_words_M1 D hα h hA hC hN
  obtain ⟨-, -, -, -, -, -, -, -, hX1⟩ := Row4.sides D h hA hC
  obtain ⟨hab, hac, hbc⟩ := Row4.scalene D hα h
  -- the word of each leg is `(0,k,0)` or `(1,0,1)`
  have hw : ∀ i : Fin 3, (i = 0 ∨ i = 1) →
      (((D.sideEdges (i + 1)).filter (fun e => D.eLen e = a)).card = 0 ∧
        ((D.sideEdges (i + 1)).filter (fun e => D.eLen e = b)).card = k ∧
        ((D.sideEdges (i + 1)).filter (fun e => D.eLen e = c)).card = 0) ∨
      (((D.sideEdges (i + 1)).filter (fun e => D.eLen e = a)).card = 1 ∧
        ((D.sideEdges (i + 1)).filter (fun e => D.eLen e = b)).card = 0 ∧
        ((D.sideEdges (i + 1)).filter (fun e => D.eLen e = c)).card = 1) := by
    intro i hi
    apply hwords
    rw [← Row4.side_word_counts D hα h i]
    rcases hi with rfl | rfl
    · rfl
    · exact hX1.symm
  -- an `(1,0,1)` leg is `{ea, ec}`
  have hstruct : ∀ j : Fin 3,
      ((D.sideEdges j).filter (fun e => D.eLen e = a)).card = 1 →
      ((D.sideEdges j).filter (fun e => D.eLen e = b)).card = 0 →
      ((D.sideEdges j).filter (fun e => D.eLen e = c)).card = 1 →
      ∃ ea ec, D.sideEdges j = {ea, ec} ∧ D.eLen ea = a ∧ D.eLen ec = c := by
    intro j h1 h2 h3
    obtain ⟨ea, hea⟩ := Finset.card_eq_one.mp h1
    obtain ⟨ec, hec⟩ := Finset.card_eq_one.mp h3
    have hmea : ea ∈ (D.sideEdges j).filter (fun e => D.eLen e = a) := by rw [hea]; simp
    have hmec : ec ∈ (D.sideEdges j).filter (fun e => D.eLen e = c) := by rw [hec]; simp
    refine ⟨ea, ec, ?_, (Finset.mem_filter.mp hmea).2, (Finset.mem_filter.mp hmec).2⟩
    ext e
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro he
      rcases Row4.eLen_abc D h e with e1 | e1 | e1
      · left
        have : e ∈ (D.sideEdges j).filter (fun e => D.eLen e = a) := Finset.mem_filter.mpr ⟨he, e1⟩
        rw [hea] at this; simpa using this
      · exfalso
        have : e ∈ (D.sideEdges j).filter (fun e => D.eLen e = b) := Finset.mem_filter.mpr ⟨he, e1⟩
        rw [Finset.card_eq_zero.mp h2] at this; simp at this
      · right
        have : e ∈ (D.sideEdges j).filter (fun e => D.eLen e = c) := Finset.mem_filter.mpr ⟨he, e1⟩
        rw [hec] at this; simpa using this
    · rintro (rfl | rfl)
      · exact (Finset.mem_filter.mp hmea).1
      · exact (Finset.mem_filter.mp hmec).1
  have hbk : ∀ j : Fin 3,
      ((D.sideEdges j).filter (fun e => D.eLen e = a)).card = 0 →
      ((D.sideEdges j).filter (fun e => D.eLen e = c)).card = 0 →
      ∀ e ∈ D.sideEdges j, D.eLen e = b := by
    intro j h1 h3 e he
    rcases Row4.eLen_abc D h e with e1 | e1 | e1
    · exfalso
      have : e ∈ (D.sideEdges j).filter (fun e => D.eLen e = a) := Finset.mem_filter.mpr ⟨he, e1⟩
      rw [Finset.card_eq_zero.mp h1] at this; simp at this
    · exact e1
    · exfalso
      have : e ∈ (D.sideEdges j).filter (fun e => D.eLen e = c) := Finset.mem_filter.mpr ⟨he, e1⟩
      rw [Finset.card_eq_zero.mp h3] at this; simp at this
  rcases hw 0 (Or.inl rfl) with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact ⟨1, Or.inl rfl, k, hk2, hNk, h2, hbk 1 h1 h3⟩
  rcases hw 1 (Or.inr rfl) with ⟨h1', h2', h3'⟩ | ⟨h1', h2', h3'⟩
  · exact ⟨2, Or.inr rfl, k, hk2, hNk, h2', hbk 2 h1' h3'⟩
  exfalso
  obtain ⟨ea₂, ec₂, hs₂, ha₂, hc₂⟩ := hstruct 1 h1 h2 h3
  obtain ⟨ea₁, ec₁, hs₁, ha₁, hc₁⟩ := hstruct 2 h1' h2' h3'
  exact Row4.L8_ac D hα h hA hC hs₁ ha₁ hc₁ hs₂ ha₂ hc₂


theorem Row4.not_M1 (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    (hA : D.target.angleAt 0 = α) (hC : D.target.angleAt 1 = α) : ¬ M1Div N := by
  intro hN
  obtain ⟨j, hj, k, hk2, -, hcard, hall⟩ := Row4.reduced_M1 D hα h hA hC hN
  obtain ⟨hα0, hα3, -⟩ := Row4.model_sides D h
  have hB : D.target.angleAt 2 = Real.pi - 2 * α := by
    have := D.target.angleAt_sum; rw [hA, hC] at this; linarith
  obtain ⟨hBγ, -⟩ := Row4.corner_B D hα h hα0 hα3 hB
  have hne : ∀ i j : Fin 3, i ≠ j → D.target.pts i ≠ D.target.pts j := fun i j hij e =>
    hij (D.target.indep.injective e)
  rcases hj with rfl | rfl
  · -- the leg `CB = [pts 1, pts 2]`
    refine Row4.bk_leg D hα h (hne 1 2 (by decide)) rfl rfl ?_
      (fun i => (Row4.corner_A D hα h hα0 hα3 hC i).2) hBγ hk2 hcard hall
    intro v hv
    have h3 : v = 0 ∨ v = 1 ∨ v = 2 := by fin_cases v <;> simp
    rcases h3 with rfl | rfl | rfl
    · exact absurd hv (Row4.third_not_on_side D.target 1)
    · exact Or.inl rfl
    · exact Or.inr rfl
  · -- the leg `AB = [pts 0, pts 2]`
    have hsAB : D.target.edge 2 = segment ℝ (D.target.pts 0) (D.target.pts 2) := by
      show segment ℝ (D.target.pts 2) (D.target.pts (2 + 1)) = _
      rw [show (2 : Fin 3) + 1 = 0 from rfl, segment_symm]
    refine Row4.bk_leg D hα h (hne 0 2 (by decide)) hsAB (by rw [dist_comm]; rfl) ?_
      (fun i => (Row4.corner_A D hα h hα0 hα3 hA i).2) hBγ hk2 hcard hall
    intro v hv
    have h3 : v = 0 ∨ v = 1 ∨ v = 2 := by fin_cases v <;> simp
    rcases h3 with rfl | rfl | rfl
    · exact Or.inl rfl
    · rw [segment_symm] at hv
      exact absurd hv (Row4.third_not_on_side D.target 2)
    · exact Or.inr rfl


end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row4.not_M1
