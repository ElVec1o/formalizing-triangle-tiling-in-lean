/-
Draft/CompositeE5Gen.lean — Theorem E (equilateral target) at COMPOSITE odd N: the pin `{s,t} = {3,N}` of the prime chain is
replaced by the full list of admissible pairs `(s,t)`, `s t = 3N`, `s,t ≤ N`, `s ≡ t ≡ N (2)`.
(P60) `sixty_side_kill`:  π/3, pair `(m₁,m₂)`: closed forms `2N(a+b) = S(m₁+m₂)`, `2Nc = S(m₁−m₂)`,
      `(2N(a−b))² = S²·D`, `D = (m₁+m₂)² − 16N`; the side decomposition `S = p a + q b + r c` then forces `p = q`
      (else `D` is a perfect square) and `2N = p(m₁+m₂) + r(m₁−m₂)`.
(P120) `twoPiThree_side_kill`: 2π/3, pair `(s,t)`, `D = (t−s)² + 16N`; side decomposition forces `p = q = 0`, `2N = r(s+t)`.
(E7b)  the pair `(m₁,m₂) = (N,3)` (π/3) is closed by the uniform-sign argument (copy of `FluxCRow5N15` with the hypothesis
       `N (a+b−c) = 3S` in place of `N = 15`; gives `r = 0`) and `D = (N−1)(N−9)` non-square for `N ≥ 11`.
Outputs `gapE60_of_pairs`, `gapE120_of_pairs`: `GapE60 N` / `GapE120 N` from a finite arithmetic hypothesis on pairs.
UNAUDITED.  Formalization debt, NOT /goal progress.  No sorry, no native_decide.
-/
import Erdos634.Draft.CompositeFinal7
import Erdos634.Draft.FluxCRow5N15
import Erdos634.Draft.FluxCRow5TwoPiThreeFull

open scoped Classical
open Finset

namespace Erdos634.Draft.CompositeE5Gen

open Erdos634.Geometry Erdos634.Geometry.Row5Hr0 Erdos634.Draft.Chain15 Erdos634.Draft.TheoremPConditional

/-- rational `x` with `x² = D` (`D : ℤ`) forces `D` to be a perfect square. -/
theorem isSquare_of_rat_sq (D K L : ℤ) (hL : L ≠ 0) (h : ((K : ℝ) / (L : ℝ)) ^ 2 = (D : ℝ)) : IsSquare D := by
  have hq : ((K : ℚ) / (L : ℚ)) ^ 2 = (D : ℚ) := by
    have : (((K : ℚ) / (L : ℚ)) ^ 2 : ℚ) = (D : ℚ) := by
      apply Rat.cast_injective (α := ℝ)
      push_cast
      exact h
    exact this
  have hsq : IsSquare ((D : ℤ) : ℚ) := ⟨(K : ℚ) / (L : ℚ), by rw [← hq]; ring⟩
  exact Rat.isSquare_intCast_iff.mp hsq

/-- **2π/3 equilateral, general pair `(s, t)`**: closed forms + irrational-part side matching. -/
theorem twoPiThree_side_kill {N : ℕ} {a b c S : ℝ} (s t : ℤ) (hN : 0 < N)
    (hs : (s : ℝ) * (c + a - b) = 3 * S) (ht : (t : ℝ) * (c + b - a) = 3 * S)
    (harea : S ^ 2 = N * a * b) (hprod : s * t = 3 * (N : ℤ)) (hS0 : 0 < S)
    (p q r : ℤ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hside : S = p * a + q * b + r * c)
    (hD : ¬ IsSquare ((t - s) ^ 2 + 16 * (N : ℤ)))
    (hno : 2 * (N : ℤ) ≠ r * (s + t)) : False := by
  have hprodR : (s : ℝ) * t = 3 * N := by exact_mod_cast hprod
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have e1 : 2 * (N : ℝ) * c = S * (s + t) := by
    have : 3 * ((2 * (N : ℝ) * c) - S * (s + t)) = 0 := by
      linear_combination (t : ℝ) * hs + (s : ℝ) * ht - 2 * c * hprodR
    linarith
  have e2 : 2 * (N : ℝ) * (a - b) = S * (t - s) := by
    have : 3 * ((2 * (N : ℝ) * (a - b)) - S * (t - s)) = 0 := by
      linear_combination (t : ℝ) * hs - (s : ℝ) * ht - 2 * (a - b) * hprodR
    linarith
  have hX : (2 * (N : ℝ) * (a + b)) ^ 2 = S ^ 2 * (((t - s) ^ 2 + 16 * (N : ℤ) : ℤ) : ℝ) := by
    push_cast
    linear_combination (2 * (N : ℝ) * (a - b) + S * (t - s)) * e2 - 16 * (N : ℝ) * harea
  -- (p+q) X = S K
  have hK : ((p : ℝ) + q) * (2 * (N : ℝ) * (a + b)) =
      S * (((4 * (N : ℤ) - (p - q) * (t - s) - 2 * r * (s + t) : ℤ)) : ℝ) := by
    push_cast
    linear_combination (-4 * (N : ℝ)) * hside - ((p : ℝ) - q) * e2 - 2 * (r : ℝ) * e1
  by_cases hpq : p + q = 0
  · have hp0 : p = 0 := by omega
    have hq0 : q = 0 := by omega
    subst hp0; subst hq0
    have h4 : S * (4 * (N : ℝ) - 2 * r * (s + t)) = 0 := by
      push_cast at hK
      linarith
    rcases mul_eq_zero.mp h4 with h | h
    · exact hS0.ne' h
    · apply hno
      have : (2 * (N : ℝ)) = r * (s + t) := by linarith
      exact_mod_cast this
  · apply hD
    have hL : ((p + q : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hpq
    refine isSquare_of_rat_sq _ (4 * (N : ℤ) - (p - q) * (t - s) - 2 * r * (s + t)) (p + q) hpq ?_
    have hS2 : S ^ 2 ≠ 0 := by positivity
    have hX' : 2 * (N : ℝ) * (a + b) =
        S * ((((4 * (N : ℤ) - (p - q) * (t - s) - 2 * r * (s + t) : ℤ)) : ℝ) / ((p + q : ℤ) : ℝ)) := by
      push_cast at hL hK ⊢
      field_simp
      linear_combination hK
    rw [hX'] at hX
    have : S ^ 2 * (((((4 * (N : ℤ) - (p - q) * (t - s) - 2 * r * (s + t) : ℤ)) : ℝ) / ((p + q : ℤ) : ℝ))) ^ 2 =
        S ^ 2 * (((t - s) ^ 2 + 16 * (N : ℤ) : ℤ) : ℝ) := by
      rw [← hX]; ring
    exact mul_left_cancel₀ hS2 this

/-- **π/3 equilateral, general pair `(m₁, m₂)`**: closed forms + irrational-part side matching. -/
theorem sixty_side_kill {N : ℕ} {a b c S : ℝ} (m₁ m₂ : ℤ) (hN : 0 < N)
    (h1 : (m₁ : ℝ) * (a + b - c) = 3 * S) (h2 : (m₂ : ℝ) * (a + b + c) = 3 * S)
    (harea : S ^ 2 = N * a * b) (hprod : m₁ * m₂ = 3 * (N : ℤ)) (hS0 : 0 < S)
    (p q r : ℤ) (hside : S = p * a + q * b + r * c)
    (hD : ¬ IsSquare ((m₁ + m₂) ^ 2 - 16 * (N : ℤ)))
    (hno : 0 ≤ (m₁ + m₂) ^ 2 - 16 * (N : ℤ) → 2 * (N : ℤ) ≠ p * (m₁ + m₂) + r * (m₁ - m₂)) : False := by
  have hprodR : (m₁ : ℝ) * m₂ = 3 * N := by exact_mod_cast hprod
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have e1 : 2 * (N : ℝ) * (a + b) = S * (m₁ + m₂) := by
    have : 3 * ((2 * (N : ℝ) * (a + b)) - S * (m₁ + m₂)) = 0 := by
      linear_combination (m₂ : ℝ) * h1 + (m₁ : ℝ) * h2 - 2 * (a + b) * hprodR
    linarith
  have e2 : 2 * (N : ℝ) * c = S * (m₁ - m₂) := by
    have : 3 * ((2 * (N : ℝ) * c) - S * (m₁ - m₂)) = 0 := by
      linear_combination (m₁ : ℝ) * h2 - (m₂ : ℝ) * h1 - 2 * c * hprodR
    linarith
  have hX : (2 * (N : ℝ) * (a - b)) ^ 2 = S ^ 2 * (((m₁ + m₂) ^ 2 - 16 * (N : ℤ) : ℤ) : ℝ) := by
    push_cast
    linear_combination ((2 * (N : ℝ) * (a + b) + S * (m₁ + m₂))) * e1 + 16 * (N : ℝ) * harea
  have hK : ((p : ℝ) - q) * (2 * (N : ℝ) * (a - b)) =
      S * (((4 * (N : ℤ) - (p + q) * (m₁ + m₂) - 2 * r * (m₁ - m₂) : ℤ)) : ℝ) := by
    push_cast
    linear_combination (-4 * (N : ℝ)) * hside - ((p : ℝ) + q) * e1 - 2 * (r : ℝ) * e2
  by_cases hneg : (m₁ + m₂) ^ 2 - 16 * (N : ℤ) < 0
  · have hnegR : ((((m₁ + m₂) ^ 2 - 16 * (N : ℤ) : ℤ)) : ℝ) < 0 := by exact_mod_cast hneg
    have : S ^ 2 * ((((m₁ + m₂) ^ 2 - 16 * (N : ℤ) : ℤ)) : ℝ) < 0 :=
      mul_neg_of_pos_of_neg (by positivity) hnegR
    nlinarith [sq_nonneg (2 * (N : ℝ) * (a - b))]
  have hno' := hno (not_lt.mp hneg)
  by_cases hpq : p - q = 0
  · have hpq' : p = q := by omega
    subst hpq'
    have h4 : S * (4 * (N : ℝ) - 2 * p * (m₁ + m₂) - 2 * r * (m₁ - m₂)) = 0 := by
      push_cast at hK
      linarith
    rcases mul_eq_zero.mp h4 with h | h
    · exact hS0.ne' h
    · apply hno'
      have : (2 * (N : ℝ)) = p * (m₁ + m₂) + r * (m₁ - m₂) := by linarith
      exact_mod_cast this
  · apply hD
    have hL : ((p - q : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hpq
    refine isSquare_of_rat_sq _ (4 * (N : ℤ) - (p + q) * (m₁ + m₂) - 2 * r * (m₁ - m₂)) (p - q) hpq ?_
    have hS2 : S ^ 2 ≠ 0 := by positivity
    have hX' : 2 * (N : ℝ) * (a - b) =
        S * ((((4 * (N : ℤ) - (p + q) * (m₁ + m₂) - 2 * r * (m₁ - m₂) : ℤ)) : ℝ) / ((p - q : ℤ) : ℝ)) := by
      push_cast at hL hK ⊢
      field_simp
      linear_combination hK
    rw [hX'] at hX
    have : S ^ 2 * (((((4 * (N : ℤ) - (p + q) * (m₁ + m₂) - 2 * r * (m₁ - m₂) : ℤ)) : ℝ) / ((p - q : ℤ) : ℝ))) ^ 2 =
        S ^ 2 * (((m₁ + m₂) ^ 2 - 16 * (N : ℤ) : ℤ) : ℝ) := by
      rw [← hX]; ring
    exact mul_left_cancel₀ hS2 this



/-! ## Geometric layer -/

section Geo

variable {N : ℕ}

/-- **E7b step 1 (uniform sign), at the level of each tile.**  At prime `N > 3`, every tile's
`w₁`-flux is `+(a + b − c)`. -/
theorem tile_flux_eq_pin (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.SixtyData α a b c)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) (hN11 : 11 ≤ N)
    (hNM : (N : ℝ) * (a + b - c) = 3 * D.target.oppLen 0) :
    ∀ i, (D.tile i).flux (G1 D α hα).weight = a + b - c := by
  set G := G1 D α hα
  set M := a + b - c with hMdef
  have hNM2 : (N : ℝ) * M = 3 * D.target.oppLen 0 := hNM
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
theorem edgeSign_eq_neg_one_pin (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.SixtyData α a b c)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) (hN11 : 11 ≤ N)
    (hNM : (N : ℝ) * (a + b - c) = 3 * D.target.oppLen 0)
    (i : Fin N) (k : Fin 3) : (G1 D α hα).edgeSign (D.tile i) k = -1 := by
  set G := G1 D α hα
  have hf := (D.tile i).flux_eq_edgeSign G (g1_sq D hα) (tile_angles_mem D hα h i) k
  have hK : G.tileValue D.model = -(a + b - c) := sixty_tileValue_one D.model hα h
  rw [G.tileValue_congr (D.tiles_congruent i), hK,
    tile_flux_eq_pin D hα h hP hN11 hNM i] at hf
  have hS0 : 0 < D.target.oppLen 0 := D.target.oppLen_pos 0
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hM0 : a + b - c ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hNM; linarith
  have : (G.edgeSign (D.tile i) k + 1) * (a + b - c) = 0 := by linear_combination hf
  rcases mul_eq_zero.mp this with h1 | h1
  · linarith
  · exact absurd h1 hM0

/-- **E7b steps 3–4: no `c`-edge on side `01`.**  Every tile edge lying on target side `01` has
length `a` or `b`. -/
theorem side_edge_len_pin (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.SixtyData α a b c)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) (hN11 : 11 ≤ N)
    (hNM : (N : ℝ) * (a + b - c) = 3 * D.target.oppLen 0)
    (e : Fin N × Fin 3) (he : e ∈ D.toDissection.sideEdges 0) :
    D.toDissection.eLen e = a ∨ D.toDissection.eLen e = b := by
  set G := G1 D α hα
  have hsub : D.toDissection.eSet e ⊆ D.target.edge 0 := (Finset.mem_filter.mp he).2
  have hdir := D.toDissection.eDir_of_side hsub
  have hw : G.weight ((D.tile e.1).leftUnit e.2) = 1 := by
    have : (D.tile e.1).leftUnit e.2 = D.target.leftUnit 0 := hdir
    unfold GridChar.weight; rw [this]; exact G.val_anchor
  have hs := edgeSign_eq_neg_one_pin D hα h hP hN11 hNM e.1 e.2
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
theorem side_decomposition_r0_pin (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.SixtyData α a b c)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) (hN11 : 11 ≤ N)
    (hNM : (N : ℝ) * (a + b - c) = 3 * D.target.oppLen 0) :
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
    exact (side_edge_len_pin D hα h hP hN11 hNM e hm.1).resolve_left hm.2
  rw [hA, hB]


/-- Every tile edge has length `a`, `b` or `c` (π/3 tile). -/
theorem sixty_edge_len (D : CongruentDissection N) {α a b c : ℝ}
    (h : D.model.SixtyData α a b c) (e : Fin N × Fin 3) :
    D.toDissection.eLen e = a ∨ D.toDissection.eLen e = b ∨ D.toDissection.eLen e = c := by
  obtain ⟨σ, hσ⟩ := (D.tiles_congruent e.1).exists_perm
  obtain ⟨τ, -, o0, -, o1, -, o2⟩ := h
  have hlen : D.toDissection.eLen e = (D.tile e.1).oppLen (e.2 + 2) := by
    unfold Dissection.eLen Tri.oppLen
    have k1 : ∀ k : Fin 3, k + 2 + 1 = k := by decide
    have k2 : ∀ k : Fin 3, k + 2 + 2 = k + 1 := by decide
    rw [k1, k2]
  obtain ⟨m, hm⟩ := τ.surjective (σ (e.2 + 2))
  rw [hlen, (hσ _).2, ← hm]
  have hm3 : m = 0 ∨ m = 1 ∨ m = 2 := by fin_cases m <;> simp
  rcases hm3 with rfl | rfl | rfl
  · exact Or.inl o0
  · exact Or.inr (Or.inl o1)
  · exact Or.inr (Or.inr o2)

/-- Side `01` of the target is `p·a + q·b + r·c`, `p, q, r ∈ ℕ` (π/3 tile). -/
theorem sixty_side_decomposition (D : CongruentDissection N) {α a b c : ℝ}
    (h : D.model.SixtyData α a b c) :
    ∃ p q r : ℕ, dist (D.target.pts 0) (D.target.pts 1)
      = (p : ℝ) * a + (q : ℝ) * b + (r : ℝ) * c := by
  set s := D.toDissection.sideEdges 0
  set len := D.toDissection.eLen
  have hsum := D.toDissection.side_len_sum 0
  rw [show (0 : Fin 3) + 1 = 1 from rfl] at hsum
  set s' := s.filter fun e => ¬ len e = a
  refine ⟨(s.filter fun e => len e = a).card, (s'.filter fun e => len e = b).card,
    (s'.filter fun e => ¬ len e = b).card, ?_⟩
  rw [← hsum, ← Finset.sum_filter_add_sum_filter_not s (fun e => len e = a),
    ← Finset.sum_filter_add_sum_filter_not s' (fun e => len e = b)]
  have hA : ∑ e ∈ s.filter (fun e => len e = a), len e
      = ((s.filter fun e => len e = a).card : ℝ) * a := by
    rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2),
      Finset.sum_const, nsmul_eq_mul]
  have hB : ∑ e ∈ s'.filter (fun e => len e = b), len e
      = ((s'.filter fun e => len e = b).card : ℝ) * b := by
    rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2),
      Finset.sum_const, nsmul_eq_mul]
  have hC : ∑ e ∈ s'.filter (fun e => ¬ len e = b), len e
      = ((s'.filter fun e => ¬ len e = b).card : ℝ) * c := by
    rw [Finset.sum_congr rfl (fun e he => ?_), Finset.sum_const, nsmul_eq_mul]
    have hm := Finset.mem_filter.mp he
    have hm' := Finset.mem_filter.mp hm.1
    rcases sixty_edge_len D h e with h1 | h1 | h1
    · exact absurd h1 hm'.2
    · exact absurd h1 hm.2
    · exact h1
  rw [hA, hB, hC]; ring

/-- `(N−1)(N−9)` is not a perfect square for `N ≥ 11`, in the form needed by `sixty_side_kill` at `(N,3)`. -/
theorem nonsq_pin (N : ℕ) (hN : 11 ≤ N) : ¬ IsSquare (((N : ℤ) + 3) ^ 2 - 16 * (N : ℤ)) := by
  rintro ⟨k, hk⟩
  have hZ : ((N : ℤ) - 1) * ((N : ℤ) - 9) = |k| ^ 2 := by
    rw [sq_abs]; nlinarith [hk]
  have := sq_Nm1Nm9_cases (N : ℤ) (by omega) |k| hZ
  omega

/-- **E60 at the pin `(N,3)`**: closed by E7b (`r = 0`) + non-square `D`. -/
theorem sixty_pinned_false (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.SixtyData α a b c)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) (hN11 : 11 ≤ N)
    (hNM : (N : ℝ) * (a + b - c) = 3 * D.target.oppLen 0)
    (h3 : (3 : ℝ) * (a + b + c) = 3 * D.target.oppLen 0)
    (harea : D.target.oppLen 0 ^ 2 = N * a * b) : False := by
  obtain ⟨p, q, hpq⟩ := side_decomposition_r0_pin D hα h hP hN11 hNM
  obtain ⟨-, e2, -⟩ := Row5.equilateral_boundary D hα 0
    (fun k => D.model.sixty_angles_mem hα h 0 _ k) hP
  have hd : dist (D.target.pts 0) (D.target.pts 1) = D.target.oppLen 0 := by
    rw [← e2]; unfold Tri.oppLen; rfl
  rw [hd] at hpq
  refine sixty_side_kill (N := N) (a := a) (b := b) (c := c) (S := D.target.oppLen 0) (N : ℤ) 3 (by omega)
    (by exact_mod_cast hNM) (by exact_mod_cast h3) harea (by push_cast; ring) (D.target.oppLen_pos 0)
    (p : ℤ) (q : ℤ) 0 (by push_cast; rw [hpq]; ring) (nonsq_pin N hN11) ?_
  intro _ hcon
  have hp0 : (0 : ℤ) ≤ p := by positivity
  push_cast at hcon
  rcases Nat.lt_or_ge p 2 with hlt | hge
  · interval_cases p <;> omega
  · nlinarith

end Geo


/-! ## The two leaves from finite arithmetic on pairs -/

/-- **`GapE120 N` from the pair table.**  Hypothesis: every admissible `(s,t)` has non-square `D = (t−s)²+16N`
and `2N ∤`-form `2N ≠ r(s+t)` for all `r ≥ 0`. -/
theorem gapE120_of_pairs (N : ℕ) (hN : 0 < N)
    (hpairs : ∀ s t : ℤ, 1 ≤ s → s ≤ N → 1 ≤ t → t ≤ N → s * t = 3 * (N : ℤ) →
      ¬ IsSquare ((t - s) ^ 2 + 16 * (N : ℤ)) ∧ ∀ r : ℤ, 0 ≤ r → 2 * (N : ℤ) ≠ r * (s + t)) : GapE120 N := by
  intro D α a b c hα h hE
  obtain ⟨s, t, -, -, hs1, hsN, ht1, htN, hS1, hS2, harea, hprod, -⟩ := Row5.theoremE_twoPiThree D hα h hE
  obtain ⟨p, q, r, hpqr⟩ := Row5TwoPiThreeFull.side_decomposition D h
  obtain ⟨-, e2, -⟩ := Row5.equilateral_boundary D hα 0
    (fun k => D.model.data_angles_mem hα h 0 k) hE
  have hd : dist (D.target.pts 0) (D.target.pts 1) = D.target.oppLen 0 := by
    rw [← e2]; unfold Tri.oppLen; rfl
  rw [hd] at hpqr
  obtain ⟨hD, hno⟩ := hpairs s t hs1 hsN ht1 htN hprod
  exact twoPiThree_side_kill (N := N) (a := a) (b := b) (c := c) (S := D.target.oppLen 0) s t hN hS1 hS2 harea hprod
    (D.target.oppLen_pos 0) (p : ℤ) (q : ℤ) (r : ℤ) (by positivity) (by positivity)
    (by rw [hpqr]; push_cast; ring) hD (hno (r : ℤ) (by positivity))

/-- **`GapE60 N` from the pair table.**  Hypothesis: every admissible `(m₁,m₂)` is the pin `(N,3)`, or has non-square
`D = (m₁+m₂)²−16N` and `2N ≠ p(m₁+m₂) + r(m₁−m₂)` for all `p, r ≥ 0`. -/
theorem gapE60_of_pairs (N : ℕ) (hN : 11 ≤ N)
    (hpairs : ∀ m₁ m₂ : ℤ, 1 ≤ m₁ → m₁ ≤ N → 1 ≤ m₂ → m₂ ≤ N → m₁ * m₂ = 3 * (N : ℤ) → m₂ < m₁ →
      (m₁ = N ∧ m₂ = 3) ∨ (¬ IsSquare ((m₁ + m₂) ^ 2 - 16 * (N : ℤ)) ∧
        (0 ≤ (m₁ + m₂) ^ 2 - 16 * (N : ℤ) →
          ∀ p r : ℤ, 0 ≤ p → 0 ≤ r → 2 * (N : ℤ) ≠ p * (m₁ + m₂) + r * (m₁ - m₂)))) : GapE60 N := by
  intro D α a b c hα h hE
  obtain ⟨m₁, m₂, -, -, hm1, hm1N, hm2, hm2N, hS1, hS2, harea, hprod, hlt, -⟩ := Row5.theoremE_sixty D hα h hE
  rcases hpairs m₁ m₂ hm1 hm1N hm2 hm2N hprod hlt with ⟨e1, e2⟩ | ⟨hD, hno⟩
  · subst e1; subst e2
    exact sixty_pinned_false D hα h hE hN (by exact_mod_cast hS1) (by exact_mod_cast hS2) harea
  · obtain ⟨p, q, r, hpqr⟩ := sixty_side_decomposition D h
    obtain ⟨-, e2, -⟩ := Row5.equilateral_boundary D hα 0
      (fun k => D.model.sixty_angles_mem hα h 0 _ k) hE
    have hd : dist (D.target.pts 0) (D.target.pts 1) = D.target.oppLen 0 := by
      rw [← e2]; unfold Tri.oppLen; rfl
    rw [hd] at hpqr
    exact sixty_side_kill (N := N) (a := a) (b := b) (c := c) (S := D.target.oppLen 0) m₁ m₂ (by omega)
      hS1 hS2 harea hprod (D.target.oppLen_pos 0) (p : ℤ) (q : ℤ) (r : ℤ)
      (by rw [hpqr]; push_cast; ring) hD (fun hnn => hno hnn (p : ℤ) (r : ℤ) (by positivity) (by positivity))

/-- **`E60Pair N m₁ m₂`**: no equilateral-target dissection with a π/3 tile whose invariant pair is exactly `(m₁, m₂)`.
Named residual for the single non-pin pair that the irrational-part side matching cannot kill (N = 87, `(29, 9)`). -/
def E60Pair (N : ℕ) (m₁ m₂ : ℤ) : Prop :=
  ∀ (D : CongruentDissection N) (α a b c : ℝ), IrrPi α → D.model.SixtyData α a b c → Equilateral D →
    (m₁ : ℝ) * (a + b - c) = 3 * D.target.oppLen 0 → (m₂ : ℝ) * (a + b + c) = 3 * D.target.oppLen 0 → False

/-- `GapE60 N` from the pair table with ONE exceptional pair `(x, y)` carried as the hypothesis `E60Pair N x y`. -/
theorem gapE60_of_pairs_exc (N : ℕ) (hN : 11 ≤ N) (x y : ℤ) (gx : E60Pair N x y)
    (hpairs : ∀ m₁ m₂ : ℤ, 1 ≤ m₁ → m₁ ≤ N → 1 ≤ m₂ → m₂ ≤ N → m₁ * m₂ = 3 * (N : ℤ) → m₂ < m₁ →
      (m₁ = N ∧ m₂ = 3) ∨ (m₁ = x ∧ m₂ = y) ∨ (¬ IsSquare ((m₁ + m₂) ^ 2 - 16 * (N : ℤ)) ∧
        (0 ≤ (m₁ + m₂) ^ 2 - 16 * (N : ℤ) →
          ∀ p r : ℤ, 0 ≤ p → 0 ≤ r → 2 * (N : ℤ) ≠ p * (m₁ + m₂) + r * (m₁ - m₂)))) : GapE60 N := by
  intro D α a b c hα h hE
  obtain ⟨m₁, m₂, -, -, hm1, hm1N, hm2, hm2N, hS1, hS2, harea, hprod, hlt, -⟩ := Row5.theoremE_sixty D hα h hE
  rcases hpairs m₁ m₂ hm1 hm1N hm2 hm2N hprod hlt with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨hD, hno⟩
  · subst e1; subst e2
    exact sixty_pinned_false D hα h hE hN (by exact_mod_cast hS1) (by exact_mod_cast hS2) harea
  · subst e1; subst e2
    exact gx D α a b c hα h hE hS1 hS2
  · obtain ⟨p, q, r, hpqr⟩ := sixty_side_decomposition D h
    obtain ⟨-, e2, -⟩ := Row5.equilateral_boundary D hα 0
      (fun k => D.model.sixty_angles_mem hα h 0 _ k) hE
    have hd : dist (D.target.pts 0) (D.target.pts 1) = D.target.oppLen 0 := by
      rw [← e2]; unfold Tri.oppLen; rfl
    rw [hd] at hpqr
    exact sixty_side_kill (N := N) (a := a) (b := b) (c := c) (S := D.target.oppLen 0) m₁ m₂ (by omega)
      hS1 hS2 harea hprod (D.target.oppLen_pos 0) (p : ℤ) (q : ℤ) (r : ℤ)
      (by rw [hpqr]; push_cast; ring) hD (fun hnn => hno hnn (p : ℤ) (r : ℤ) (by positivity) (by positivity))

end Erdos634.Draft.CompositeE5Gen

#print axioms Erdos634.Draft.CompositeE5Gen.twoPiThree_side_kill
#print axioms Erdos634.Draft.CompositeE5Gen.sixty_side_kill
#print axioms Erdos634.Draft.CompositeE5Gen.sixty_pinned_false
#print axioms Erdos634.Draft.CompositeE5Gen.gapE120_of_pairs
#print axioms Erdos634.Draft.CompositeE5Gen.gapE60_of_pairs
#print axioms Erdos634.Draft.CompositeE5Gen.gapE60_of_pairs_exc
