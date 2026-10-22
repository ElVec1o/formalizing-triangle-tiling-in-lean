-- Draft/FluxCRow5N15.lean — Theorem E, π/3 branch (equilateral target) at N = 15: the pin `m₁ = N ∧ m₂ = 3`
-- (which the prime chain gets from primality) is derived at N = 15 by a finite check on `m₁ m₂ = 45`
-- plus a real-algebra kill of the (9,5) pair ((a−b)² < 0), and the existing E7b/E8 chain is re-threaded
-- with that pin.  `Row5.theoremE_sixty_full15 : … → N = 15 → False`.  Room ALLN / SCOPE_R8_PI3 §B.
-- Copies of FluxCRow5Complete / FluxCRow5Hr0 lemmas with `N.Prime ∧ 3<N` replaced by `N = 15`.  UNAUDITED.
import Erdos634.Draft.FluxCRow5Hr0

open scoped Classical
open Finset

namespace Erdos634.Geometry

open Row5Hr0

theorem Row5.theoremE_sixty_pin15 (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.SixtyData α a b c)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) (hN15 : N = 15) :
    ∃ m₁ m₂ : ℤ, (2 : ℤ) ∣ m₁ - N ∧ (2 : ℤ) ∣ m₂ - N ∧ 1 ≤ m₁ ∧ m₁ ≤ N ∧ 1 ≤ m₂ ∧ m₂ ≤ N ∧
      (m₁ : ℝ) * (a + b - c) = 3 * D.target.oppLen 0 ∧
      (m₂ : ℝ) * (a + b + c) = 3 * D.target.oppLen 0 ∧
      D.target.oppLen 0 ^ 2 = N * a * b ∧ m₁ * m₂ = 3 * N ∧ m₂ < m₁ ∧ (m₁ = N ∧ m₂ = 3) := by
  obtain ⟨m₁, m₂, hd1, hd2, h1, h1N, h2, h2N, hS1, hS2, har, hprod, hlt, -⟩ :=
    Row5.theoremE_sixty D hα h hP
  refine ⟨m₁, m₂, hd1, hd2, h1, h1N, h2, h2N, hS1, hS2, har, hprod, hlt, ?_⟩
  subst hN15
  have hb1 : m₁ ≤ 15 := by exact_mod_cast h1N
  have hcases : (m₁ = 15 ∧ m₂ = 3) ∨ (m₁ = 9 ∧ m₂ = 5) := by
    have hp : m₁ * m₂ = 45 := by exact_mod_cast hprod
    obtain ⟨d1, hd1'⟩ := hd1
    interval_cases m₁ <;> omega
  rcases hcases with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact ⟨by rw [e1]; norm_num, e2⟩
  · exfalso
    subst e1; subst e2
    obtain ⟨σ, -, oa, -, ob, hγ, oc⟩ := h
    have ha0 : 0 < a := oa ▸ D.model.oppLen_pos (σ 0)
    have hb0 : 0 < b := ob ▸ D.model.oppLen_pos (σ 1)
    have hS0 : 0 < D.target.oppLen 0 := D.target.oppLen_pos 0
    set S := D.target.oppLen 0
    have hS1' : 9 * (a + b - c) = 3 * S := by exact_mod_cast hS1
    have hS2' : 5 * (a + b + c) = 3 * S := by exact_mod_cast hS2
    have har' : S ^ 2 = 15 * a * b := by exact_mod_cast har
    have hc : c = 2 * (a + b) / 7 := by linarith
    have hSab : S = 15 * (a + b) / 7 := by rw [hc] at hS1'; linarith
    rw [hSab] at har'
    nlinarith [sq_nonneg (a - b), mul_pos ha0 hb0]

theorem Row5.sixty_closedForms15 (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.SixtyData α a b c)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) (hN15 : N = 15) :
    2 * (N : ℝ) * (a + b) = D.target.oppLen 0 * ((N : ℝ) + 3) ∧
      2 * (N : ℝ) * c = D.target.oppLen 0 * ((N : ℝ) - 3) ∧
      4 * (N : ℝ) ^ 2 * (a - b) ^ 2
        = D.target.oppLen 0 ^ 2 * ((N : ℝ) - 1) * ((N : ℝ) - 9) := by
  obtain ⟨m₁, m₂, -, -, hm1, hm1N, hm2, hm2N, hSeq1, hSeq2, harea, hprod, hlt, hpin⟩ :=
    Row5.theoremE_sixty_pin15 D hα h hP hN15
  set S := D.target.oppLen 0
  obtain ⟨ha, hb⟩ := hpin
  subst ha; subst hb
  have eq1 : (N : ℝ) * (a + b - c) = 3 * S := by exact_mod_cast hSeq1
  have eq2 : a + b + c = S := by
    have h := hSeq2; push_cast at h; linarith
  have hc2 : 2 * (N : ℝ) * c = S * ((N : ℝ) - 3) := by linear_combination (N : ℝ) * eq2 - eq1
  have hab2 : 2 * (N : ℝ) * (a + b) = S * ((N : ℝ) + 3) := by
    linear_combination 2 * (N : ℝ) * eq2 - hc2
  have hab_sq : 4 * (N : ℝ) ^ 2 * (a + b) ^ 2 = S ^ 2 * ((N : ℝ) + 3) ^ 2 := by
    rw [show (4 * (N : ℝ) ^ 2 * (a + b) ^ 2) = (2 * (N : ℝ) * (a + b)) ^ 2 by ring,
      show S ^ 2 * ((N : ℝ) + 3) ^ 2 = (S * ((N : ℝ) + 3)) ^ 2 by ring, hab2]
  exact ⟨hab2, hc2, by linear_combination hab_sq + 16 * (N : ℝ) * harea⟩

/-- **`π/3` conclusion (AUDIT.md §4, steps 2–4).**  Given the closed forms, `E7b`'s conclusion
`r = 0` (hypothesis `hr0`, see file header), and a side decomposition, `3 < N` is impossible. -/
theorem Row5.sixty_forces_not_gt_three15 {N : ℕ} {a b c S : ℝ} (hN15 : N = 15)
    (hab2 : 2 * (N : ℝ) * (a + b) = S * ((N : ℝ) + 3))
    (hfin2 : 4 * (N : ℝ) ^ 2 * (a - b) ^ 2 = S ^ 2 * ((N : ℝ) - 1) * ((N : ℝ) - 9))
    (hS0 : 0 < S) (p q r : ℤ) (hp0 : 0 ≤ p) (hq0 : 0 ≤ q)
    (hside : S = p * a + q * b + r * c) (hr0 : r = 0) : False := by
  subst hr0
  have hside2 : S = p * a + q * b := by rw [hside]; push_cast; ring
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hSne : S ≠ 0 := ne_of_gt hS0
  -- `(N-1)(N-9) ≥ 0` forces `N ∉ {5,7}`; with primality this forces `N ≥ 11`.
  have hnn : (0 : ℝ) ≤ ((N : ℝ) - 1) * ((N : ℝ) - 9) := by
    have h1 : (0 : ℝ) ≤ 4 * (N : ℝ) ^ 2 * (a - b) ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ S ^ 2 * (((N : ℝ) - 1) * ((N : ℝ) - 9)) := by
      have := hfin2; nlinarith [h1]
    have hS2 : 0 < S ^ 2 := by positivity
    by_contra hcon
    push_neg at hcon
    have : S ^ 2 * (((N : ℝ) - 1) * ((N : ℝ) - 9)) < 0 := mul_neg_of_pos_of_neg hS2 hcon
    linarith
  have hnnZ : (0 : ℤ) ≤ ((N : ℤ) - 1) * ((N : ℤ) - 9) := by exact_mod_cast hnn
  have hN9 : N ≠ 9 := by omega
  have hN10 : N ≠ 10 := by omega
  have hN11 : 11 ≤ N := by omega
  have h1N : (1 : ℕ) ≤ N := by omega
  have h9N : (9 : ℕ) ≤ N := by omega
  -- irrationality of `X' / S`, `X' := 2N(a-b)`
  have hxirr : Irrational (2 * (N : ℝ) * (a - b) / S) := by
    have hcases : ¬ ((N : ℤ) = 1 ∨ (N : ℤ) = 9 ∨ (N : ℤ) = 10) := by omega
    have hnotsq : ¬ IsSquare ((N - 1) * (N - 9)) := by
      rintro ⟨k, hk⟩
      have hZ : ((N : ℤ) - 1) * ((N : ℤ) - 9) = (k : ℤ) ^ 2 := by
        have hk' : (((N - 1) * (N - 9) : ℕ) : ℤ) = (k : ℤ) * (k : ℤ) := by exact_mod_cast hk
        have hNsub : (((N - 1) * (N - 9) : ℕ) : ℤ) = ((N : ℤ) - 1) * ((N : ℤ) - 9) := by
          rw [Nat.cast_mul, Nat.cast_sub h1N, Nat.cast_sub h9N]; push_cast; ring
        rw [← hNsub, hk']; ring
      exact hcases (sq_Nm1Nm9_cases (N : ℤ) (by omega) (k : ℤ) hZ)
    have hirr0 : Irrational (Real.sqrt (((N - 1) * (N - 9) : ℕ) : ℝ)) :=
      irrational_sqrt_natCast_iff.mpr hnotsq
    have hcast : (((N - 1) * (N - 9) : ℕ) : ℝ) = ((N : ℝ) - 1) * ((N : ℝ) - 9) := by
      rw [Nat.cast_mul, Nat.cast_sub h1N, Nat.cast_sub h9N]; push_cast; ring
    have hxsq : (2 * (N : ℝ) * (a - b) / S) ^ 2 = (((N - 1) * (N - 9) : ℕ) : ℝ) := by
      rw [div_pow, div_eq_iff (pow_ne_zero 2 hSne), hcast]
      linear_combination hfin2
    have hxabs : |2 * (N : ℝ) * (a - b) / S| = Real.sqrt (((N - 1) * (N - 9) : ℕ) : ℝ) := by
      rw [← Real.sqrt_sq_eq_abs, hxsq]
    have hxabsirr : Irrational |2 * (N : ℝ) * (a - b) / S| := hxabs ▸ hirr0
    rcases abs_choice (2 * (N : ℝ) * (a - b) / S) with heq | heq
    · rwa [heq] at hxabsirr
    · rw [heq] at hxabsirr
      have hneg := hxabsirr.neg
      simpa using hneg
  -- `(p−q)•X' = S•(4N − (p+q)(N+3))`, so `p = q`.
  set M' : ℤ := 4 * (N : ℤ) - (p + q) * ((N : ℤ) + 3) with hMdef
  have heqM : ((p : ℝ) - q) * (2 * (N : ℝ) * (a - b)) = S * (M' : ℝ) := by
    have hMcast : (M' : ℝ) = 4 * (N : ℝ) - ((p : ℝ) + q) * ((N : ℝ) + 3) := by
      rw [hMdef]; push_cast; ring
    rw [hMcast]
    linear_combination (-4 * (N : ℝ)) * hside2 - ((p : ℝ) + q) * hab2
  have hpq0 : p = q := by
    by_contra hne
    have hnz : ((p : ℝ) - q) ≠ 0 := by
      intro h0
      apply hne
      have hpq : (p : ℝ) = q := by linarith
      exact_mod_cast hpq
    apply hxirr
    refine ⟨(M' : ℚ) / ((p : ℚ) - q), ?_⟩
    push_cast
    rw [div_eq_div_iff hnz hSne]
    linear_combination -heqM
  subst hpq0
  have hM'0 : M' = 0 := by
    have hz : ((p : ℝ) - p) * (2 * (N : ℝ) * (a - b)) = 0 := by ring
    rw [hz] at heqM
    rcases mul_eq_zero.mp heqM.symm with h | h
    · exact absurd h hSne
    · exact_mod_cast h
  have hpN3 : p * ((N : ℤ) + 3) = 2 * (N : ℤ) := by
    have hm : 4 * (N : ℤ) - (p + p) * ((N : ℤ) + 3) = 0 := hMdef ▸ hM'0
    linarith
  have hdvd : ((N : ℤ) + 3) ∣ 6 := ⟨2 - p, by linear_combination hpN3⟩
  have hle : (N : ℤ) + 3 ≤ 6 := Int.le_of_dvd (by norm_num) hdvd
  have hN3le : (N : ℤ) ≤ 3 := by omega
  have hNge : 3 < (N : ℤ) := by omega
  omega

/-- **E7b step 1 (uniform sign), at the level of each tile.**  At prime `N > 3`, every tile's
`w₁`-flux is `+(a + b − c)`. -/
theorem tile_flux_eq15 (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.SixtyData α a b c)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) (hN15 : N = 15) :
    ∀ i, (D.tile i).flux (G1 D α hα).weight = a + b - c := by
  set G := G1 D α hα
  set M := a + b - c with hMdef
  obtain ⟨m₁, m₂, -, -, -, -, -, -, hSeq1, -, -, -, -, hpin⟩ := Row5.theoremE_sixty_pin15 D hα h hP hN15
  obtain ⟨hm1, -⟩ := hpin
  subst hm1
  have hNM : (N : ℝ) * M = 3 * D.target.oppLen 0 := by exact_mod_cast hSeq1
  have hS0 : 0 < D.target.oppLen 0 := D.target.oppLen_pos 0
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hM0 : 0 < M := by
    by_contra hc; push Not at hc
    have : (N : ℝ) * M ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hN0.le hc
    linarith
  have hK : G.tileValue D.model = -M := sixty_tileValue_one D.model hα h
  have hpm : ∀ i, (D.tile i).flux G.weight = M ∨ (D.tile i).flux G.weight = -M := by
    intro i
    have := (D.tile i).flux_grid_pm G (g1_sq D hα) (tile_angles_mem D hα h i)
    rw [G.tileValue_congr (D.tiles_congruent i), hK, neg_neg] at this
    exact this.symm
  let ε : Fin N → ℤ := fun i => if (D.tile i).flux G.weight = M then 1 else -1
  have hε : ∀ i, ε i = 1 ∨ ε i = -1 := by
    intro i; by_cases hi : (D.tile i).flux G.weight = M
    · left; exact if_pos hi
    · right; exact if_neg hi
  have hεv : ∀ i, (D.tile i).flux G.weight = (ε i : ℝ) * M := by
    intro i; by_cases hi : (D.tile i).flux G.weight = M
    · rw [show ε i = 1 from if_pos hi]; push_cast; rw [one_mul, hi]
    · rw [show ε i = -1 from if_neg hi]; push_cast
      rcases hpm i with h1 | h1
      · exact absurd h1 hi
      · rw [h1, neg_one_mul]
  have hsum : (∑ i, (ε i : ℝ)) * M = (N : ℝ) * M := by
    rw [Finset.sum_mul, ← Finset.sum_congr rfl fun i _ => hεv i,
      D.flux_cancel G.weight G.weight_odd, target_flux D hα h hP, hNM]
  have hsumR : (∑ i, (ε i : ℝ)) = (N : ℝ) := mul_right_cancel₀ hM0.ne' hsum
  have hsumZ : ∑ i, ε i = (N : ℤ) := by exact_mod_cast hsumR
  have hall := uniform_sign_pos ε hε hsumZ
  intro i
  rw [hεv i, hall i]; push_cast; ring

/-- **E7b step 2 (sign class), edge level.**  At prime `N > 3`, every edge sign of every tile is
`−1`. -/
theorem edgeSign_eq_neg_one15 (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.SixtyData α a b c)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) (hN15 : N = 15)
    (i : Fin N) (k : Fin 3) : (G1 D α hα).edgeSign (D.tile i) k = -1 := by
  set G := G1 D α hα
  have hf := (D.tile i).flux_eq_edgeSign G (g1_sq D hα) (tile_angles_mem D hα h i) k
  have hK : G.tileValue D.model = -(a + b - c) := sixty_tileValue_one D.model hα h
  rw [G.tileValue_congr (D.tiles_congruent i), hK,
    tile_flux_eq15 D hα h hP hN15 i] at hf
  obtain ⟨m₁, m₂, -, -, -, -, -, -, hSeq1, -, -, -, -, hpin⟩ := Row5.theoremE_sixty_pin15 D hα h hP hN15
  obtain ⟨hm1, -⟩ := hpin
  subst hm1
  have hS0 : 0 < D.target.oppLen 0 := D.target.oppLen_pos 0
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNM : (N : ℝ) * (a + b - c) = 3 * D.target.oppLen 0 := by exact_mod_cast hSeq1
  have hM0 : a + b - c ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hNM; linarith
  have : (G.edgeSign (D.tile i) k + 1) * (a + b - c) = 0 := by linear_combination hf
  rcases mul_eq_zero.mp this with h1 | h1
  · linarith
  · exact absurd h1 hM0

/-- **E7b steps 3–4: no `c`-edge on side `01`.**  Every tile edge lying on target side `01` has
length `a` or `b`. -/
theorem side_edge_len15 (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.SixtyData α a b c)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) (hN15 : N = 15)
    (e : Fin N × Fin 3) (he : e ∈ D.toDissection.sideEdges 0) :
    D.toDissection.eLen e = a ∨ D.toDissection.eLen e = b := by
  set G := G1 D α hα
  have hsub : D.toDissection.eSet e ⊆ D.target.edge 0 := (Finset.mem_filter.mp he).2
  have hdir := D.toDissection.eDir_of_side hsub
  have hw : G.weight ((D.tile e.1).leftUnit e.2) = 1 := by
    have : (D.tile e.1).leftUnit e.2 = D.target.leftUnit 0 := hdir
    unfold GridChar.weight; rw [this]; exact G.val_anchor
  have hs := edgeSign_eq_neg_one15 D hα h hP hN15 e.1 e.2
  unfold GridChar.edgeSign at hs
  rw [hw, mul_one] at hs
  -- the opposite vertex `v = e.2 + 2` and the model vertex it corresponds to
  obtain ⟨σ, hσ⟩ := (D.tiles_congruent e.1).exists_perm
  obtain ⟨τ, h0, o0, h1, o1, h2, o2⟩ := h
  have hlen : D.toDissection.eLen e = (D.tile e.1).oppLen (e.2 + 2) := by
    unfold Dissection.eLen Tri.oppLen
    have k1 : ∀ k : Fin 3, k + 2 + 1 = k := by decide
    have k2 : ∀ k : Fin 3, k + 2 + 2 = k + 1 := by decide
    rw [k1, k2]
  obtain ⟨m, hm⟩ := τ.surjective (σ (e.2 + 2))
  rw [hlen, (hσ _).2, ← hm]
  rw [(hσ _).1, ← hm] at hs
  have hm3 : m = 0 ∨ m = 1 ∨ m = 2 := by fin_cases m <;> simp
  rcases hm3 with rfl | rfl | rfl
  · exact Or.inl o0
  · exact Or.inr o1
  · rw [h2, chi_c] at hs; norm_num at hs

/-- **E8 with E7b: side `01` is `p·a + q·b`, no `c`-term (`r = 0`).** -/
theorem side_decomposition_r0_15 (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.SixtyData α a b c)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) (hN15 : N = 15) :
    ∃ p q : ℕ, dist (D.target.pts 0) (D.target.pts 1) = (p : ℝ) * a + (q : ℝ) * b := by
  set s := D.toDissection.sideEdges 0
  set len := D.toDissection.eLen
  have hsum := D.toDissection.side_len_sum 0
  rw [show (0 : Fin 3) + 1 = 1 from rfl] at hsum
  refine ⟨(s.filter fun e => len e = a).card, (s.filter fun e => ¬ len e = a).card, ?_⟩
  rw [← hsum, ← Finset.sum_filter_add_sum_filter_not s (fun e => len e = a)]
  have hA : ∑ e ∈ s.filter (fun e => len e = a), len e
      = ((s.filter fun e => len e = a).card : ℝ) * a := by
    rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2),
      Finset.sum_const, nsmul_eq_mul]
  have hB : ∑ e ∈ s.filter (fun e => ¬ len e = a), len e
      = ((s.filter fun e => ¬ len e = a).card : ℝ) * b := by
    rw [Finset.sum_congr rfl (fun e he => ?_), Finset.sum_const, nsmul_eq_mul]
    have hm := Finset.mem_filter.mp he
    exact (side_edge_len15 D hα h hP hN15 e hm.1).resolve_left hm.2
  rw [hA, hB]

/-- **Theorem E, `π/3` branch, end to end, with `hr0` DISCHARGED.**  An equilateral target
`N`-tiled by congruent copies of a `(α, 2π/3 − α, π/3)` tile with `α/π ∉ ℚ` (reflections allowed,
not edge-to-edge) has `N` not a prime `> 3`. -/
theorem Row5.theoremE_sixty_full15 (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.SixtyData α a b c)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) (hN15 : N = 15) : False := by
  obtain ⟨hab2, -, hfin2⟩ := Row5.sixty_closedForms15 D hα h hP hN15
  obtain ⟨p, q, hpq⟩ := side_decomposition_r0_15 D hα h hP hN15
  obtain ⟨-, e2, -⟩ := Row5.equilateral_boundary D hα 0
    (fun k => D.model.sixty_angles_mem hα h 0 _ k) hP
  have hd : dist (D.target.pts 0) (D.target.pts 1) = D.target.oppLen 0 := by
    rw [← e2]; unfold Tri.oppLen; rfl
  rw [hd] at hpq
  exact Row5.sixty_forces_not_gt_three15 hN15 hab2 hfin2 (D.target.oppLen_pos 0)
    (p : ℤ) (q : ℤ) 0 (by positivity) (by positivity) (by rw [hpq]; push_cast; ring) rfl

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row5.theoremE_sixty_full15
