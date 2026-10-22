-- STATUS 2026-09-30: NO axiom and NO sorry remain (`f1_free_statement` depends only on standard axioms);
-- the axiom/sorry remarks below are historical.
-- Draft/F1FreeProof.lean — Assembly proof for F1FreeStatement (C8 / prop:F1free).
--
-- Proves:
--   `f1_V1V2_word_count` (ZERO sorry) — exactly one a-edge and one c-edge on the V₁V₂ side
--                                        of an F₁ target (the side of length μ·(a+b)).
--   `f1_free_statement`  (1 axiom)    — complete assembly; one named axiom remains:
--       `f1_Tprime_K2_inputs`         — K₁+K₂ of PROOF_F1free.md: extract T′ (unique a-edge tile
--                                        on V₁V₂ from side_walk partition), show its γ-vertex X
--                                        lies on both V₁V₂ and another target side (b-edge
--                                        boundary counting: N b-edges total, 0 on V₁V₂ → all on
--                                        V₂V₃∪V₃V₁, γ-vertex = shared endpoint of a-edge and
--                                        b-edge ⊆ V₂V₃ or V₃V₁).
--
-- PAPER STATUS: PROVED (prop:F1free, PROOF_F1free.md, two hostile reviews HOLD).
-- LEAN STATUS:  assembly PROVED modulo one named axiom (f1_Tprime_K2_inputs).
--
-- Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).

import Erdos634.Draft.F1AlgebraPin
import Erdos634.Draft.F1BEdgeBoundaryM
import Erdos634.Draft.F1CornerK
import Erdos634.Draft.F1K2Contradiction
import Erdos634.Draft.F1Bridge
import Erdos634.Draft.F1TprimeExtractM
import Erdos634.EdgeChain

open scoped Classical
open Erdos634.Draft.TheoremPConditional

namespace Erdos634.Draft.F1FreeProofM

open Erdos634.Geometry
open Erdos634.Draft.F1BEdgeBoundaryM (f1_V1V2_b_zero)
open Erdos634.Draft.F1TprimeExtractM (f1_Tprime_K2_proved)
open Erdos634.Draft.F1AreaIdentity (F1_area_identity)

private instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp⟩

/-! ## Step 3 arithmetic: V₁V₂ word = (a,c) or (c,a) -/

/-- **F₁ Step 3: V₁V₂ word count.**
On the side of an F₁ target of length μ·(a+b), assuming no b-edges, the edge-count equation
P·a + R·c = μ·(a+b) combined with the pin c·(N−1) = a·(N+1) forces P·(N−1) + R·(N+1) = 2N.
For prime N > 3 this has the unique ℕ solution P = R = 1: exactly one a-edge and one c-edge.

This is Step 3 of PROOF_F1free.md. -/
theorem f1_V1V2_word_count {N : ℕ} (D : CongruentDissection N) {α a b c μ : ℝ}
    (hirr : IrrPi α)
    (hm  : D.model.TwoPiThreeData α a b c)
    (hF1 : D.target.F1Data α a b c μ)
    (hμ  : 0 < μ)
    (hpm : c * ((N : ℝ) - 1) = a * ((N : ℝ) + 1) ∧ μ * (c - a) = b) (h6 : 6 < N) :
    ∃ σ : Equiv.Perm (Fin 3),
      ∀ P R : ℕ,
        (P : ℝ) * a + (R : ℝ) * c =
          dist (D.target.pts (σ 2 + 1)) (D.target.pts (σ 2 + 2)) →
        P = 1 ∧ R = 1 := by
  -- Side positivity
  obtain ⟨-, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  -- Pin + μ-relation
  obtain ⟨hpin, hmu⟩ := id hpm
  -- Area identity N*b = μ²*(a+b)
  have harea : (N : ℝ) * b = μ ^ 2 * (a + b) := F1_area_identity D hm hF1 ha0 hb0 hμ
  have hN1pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  -- μ*(a+b) = 2Nc/(N+1)
  have hmu_ab : μ * (a + b) = 2 * (N : ℝ) * c / ((N : ℝ) + 1) :=
    F1BEdgeBoundaryM.f1_mu_ab_val ha0 hb0 hc0 hμ hpin hmu harea hN1pos
  -- a = c*(N-1)/(N+1)
  have ha_val : a = c * ((N : ℝ) - 1) / ((N : ℝ) + 1) := by
    field_simp [hN1pos.ne']; linarith
  -- From f1_V1V2_b_zero, get σ, side-length fact, and Q = 0 on the V₁V₂ side
  obtain ⟨σ, hside_eq, hQ⟩ := f1_V1V2_b_zero D hirr hm hF1 hμ hpm h6
  refine ⟨σ, fun P R hPR => ?_⟩
  -- hPR : P*a + R*c = dist(σ(2)+1, σ(2)+2) = μ*(a+b)
  -- From P*a + R*c = μ*(a+b) and a = c*(N-1)/(N+1):
  -- P*(N-1) + R*(N+1) = 2N in ℝ
  have hNm2 : (N : ℤ) ≥ 5 := by
    have h4 : N ≠ 4 := by omega
    have : 2 ≤ N := by omega
    omega
  have hcne : c ≠ 0 := hc0.ne'
  have hN1ne : ((N : ℝ) + 1) ≠ 0 := hN1pos.ne'
  have hPR_eq : (P : ℝ) * ((N : ℝ) - 1) + (R : ℝ) * ((N : ℝ) + 1) = 2 * (N : ℝ) := by
    -- hPR : P*a + R*c = dist = μ*(a+b)
    rw [hside_eq, hmu_ab] at hPR  -- now hPR : P*a + R*c = 2Nc/(N+1)
    rw [ha_val] at hPR
    have : c * ((P : ℝ) * ((N : ℝ) - 1) / ((N : ℝ) + 1) + (R : ℝ)) =
           c * (2 * (N : ℝ) / ((N : ℝ) + 1)) := by
      field_simp [hcne, hN1ne] at hPR ⊢; linarith
    have := mul_left_cancel₀ hcne this
    field_simp [hN1ne] at this ⊢
    linarith
  -- Cast to ℕ
  have hN_ge5 : 5 ≤ N := by exact_mod_cast hNm2
  have hN1 : 1 ≤ N := by omega
  have hPR_nat : P * (N - 1) + R * (N + 1) = 2 * N := by
    have hN1cast : (N : ℝ) - 1 = ((N - 1 : ℕ) : ℝ) := by
      rw [← Nat.cast_one (R := ℝ), ← Nat.cast_sub hN1]
    have hN1cast2 : (N : ℝ) + 1 = ((N + 1 : ℕ) : ℝ) := by push_cast; ring
    -- Restate hPR_eq with ℕ-cast subexpressions, then use norm_cast
    have h : (P : ℝ) * ((N - 1 : ℕ) : ℝ) + (R : ℝ) * ((N + 1 : ℕ) : ℝ) = 2 * (N : ℝ) := by
      rw [← hN1cast, ← hN1cast2]; exact hPR_eq
    exact_mod_cast h
  -- Bound R ≤ 1 (since R*(N+1) ≤ 2*N < 2*(N+1)) and P ≤ 2
  have hR_le1 : R ≤ 1 := by nlinarith [Nat.zero_le (P * (N - 1))]
  -- Case split on R = 0 or R = 1, avoiding interval_cases
  rcases Nat.eq_zero_or_pos R with hR0 | hRpos
  · -- R = 0: P*(N-1) = 2*N — impossible: (N-1) | 2 but N-1 ≥ 4
    subst hR0; simp at hPR_nat
    -- Work in ℤ to use dvd_sub cleanly
    have hdvd_2 : (N : ℤ) - 1 ∣ 2 := by
      have heq : ((N : ℤ) - 1) * P = 2 * (N : ℤ) := by
        have : P * (N - 1) = 2 * N := hPR_nat
        exact_mod_cast show (N - 1) * P = 2 * N from by linarith
      have h1 : (N : ℤ) - 1 ∣ ((N : ℤ) - 1) * P := dvd_mul_right _ _
      have h2 : (N : ℤ) - 1 ∣ 2 * ((N : ℤ) - 1) := dvd_mul_left _ _
      have h3 : ((N : ℤ) - 1) * (P : ℤ) - 2 * ((N : ℤ) - 1) = 2 := by linarith
      exact h3 ▸ dvd_sub h1 h2
    have hle : (N : ℤ) - 1 ≤ 2 := Int.le_of_dvd (by omega) hdvd_2
    omega
  · -- R ≥ 1, combined with R ≤ 1: R = 1
    have hR1 : R = 1 := by omega
    subst hR1
    -- P*(N-1) = N-1, so P = 1
    have hPN : P * (N - 1) = N - 1 := by omega
    constructor
    · exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < N - 1)
        (by rw [one_mul]; exact hPN)
    · rfl

-- K₁+K₂ is now proved in F1TprimeExtract.lean (1 sorry remaining: injection argument).
-- The axiom has been replaced by f1_Tprime_K2_proved.

/-! ## Assembly: F1FreeStatement -/

-- Helper: derive hword from hside_eq (from f1_V1V2_b_zero), inlining word_count arithmetic.
private lemma f1_word_from_bzero {N : ℕ} (D : CongruentDissection N) {α a b c μ : ℝ}
    (hirr : IrrPi α) (hm : D.model.TwoPiThreeData α a b c)
    (hF1 : D.target.F1Data α a b c μ) (hμ : 0 < μ) (hpm : c * ((N : ℝ) - 1) = a * ((N : ℝ) + 1) ∧ μ * (c - a) = b) (h6 : 6 < N)
    (σ : Equiv.Perm (Fin 3))
    (hside_eq : dist (D.target.pts (σ 2 + 1)) (D.target.pts (σ 2 + 2)) = μ * (a + b)) :
    ∀ P R : ℕ, (P : ℝ) * a + (R : ℝ) * c =
      dist (D.target.pts (σ 2 + 1)) (D.target.pts (σ 2 + 2)) →
    P = 1 ∧ R = 1 := by
  -- Arithmetic is identical to f1_V1V2_word_count; σ and hside_eq come from the caller.
  obtain ⟨-, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  obtain ⟨hpin, hmu⟩ := id hpm
  have harea : (N : ℝ) * b = μ ^ 2 * (a + b) := F1_area_identity D hm hF1 ha0 hb0 hμ
  have hN1pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hmu_ab : μ * (a + b) = 2 * (N : ℝ) * c / ((N : ℝ) + 1) :=
    F1BEdgeBoundaryM.f1_mu_ab_val ha0 hb0 hc0 hμ hpin hmu harea hN1pos
  have ha_val : a = c * ((N : ℝ) - 1) / ((N : ℝ) + 1) := by
    field_simp [hN1pos.ne']; linarith
  intro P R hPR
  rw [hside_eq, hmu_ab] at hPR
  rw [ha_val] at hPR
  have hNm2 : (N : ℤ) ≥ 5 := by
    omega
  have hcne : c ≠ 0 := hc0.ne'
  have hN1ne : ((N : ℝ) + 1) ≠ 0 := hN1pos.ne'
  have hPR_eq : (P : ℝ) * ((N : ℝ) - 1) + (R : ℝ) * ((N : ℝ) + 1) = 2 * (N : ℝ) := by
    have : c * ((P : ℝ) * ((N : ℝ) - 1) / ((N : ℝ) + 1) + (R : ℝ)) =
           c * (2 * (N : ℝ) / ((N : ℝ) + 1)) := by
      field_simp [hcne, hN1ne] at hPR ⊢; linarith
    have := mul_left_cancel₀ hcne this
    field_simp [hN1ne] at this ⊢; linarith
  have hN_ge5 : 5 ≤ N := by exact_mod_cast hNm2
  have hN1 : 1 ≤ N := by omega
  have hPR_nat : P * (N - 1) + R * (N + 1) = 2 * N := by
    have hN1cast : (N : ℝ) - 1 = ((N - 1 : ℕ) : ℝ) := by
      rw [← Nat.cast_one (R := ℝ), ← Nat.cast_sub hN1]
    have hN1cast2 : (N : ℝ) + 1 = ((N + 1 : ℕ) : ℝ) := by push_cast; ring
    have h : (P : ℝ) * ((N - 1 : ℕ) : ℝ) + (R : ℝ) * ((N + 1 : ℕ) : ℝ) = 2 * (N : ℝ) := by
      rw [← hN1cast, ← hN1cast2]; exact hPR_eq
    exact_mod_cast h
  have hR_le1 : R ≤ 1 := by nlinarith [Nat.zero_le (P * (N - 1))]
  rcases Nat.eq_zero_or_pos R with hR0 | hRpos
  · subst hR0; simp at hPR_nat
    have hdvd_2 : (N : ℤ) - 1 ∣ 2 := by
      have heq : ((N : ℤ) - 1) * P = 2 * (N : ℤ) := by
        have : P * (N - 1) = 2 * N := hPR_nat
        exact_mod_cast show (N - 1) * P = 2 * N from by linarith
      have h1 : (N : ℤ) - 1 ∣ ((N : ℤ) - 1) * P := dvd_mul_right _ _
      have h2 : (N : ℤ) - 1 ∣ 2 * ((N : ℤ) - 1) := dvd_mul_left _ _
      have h3 : ((N : ℤ) - 1) * (P : ℤ) - 2 * ((N : ℤ) - 1) = 2 := by linarith
      exact h3 ▸ dvd_sub h1 h2
    have hle : (N : ℤ) - 1 ≤ 2 := Int.le_of_dvd (by omega) hdvd_2
    omega
  · have hR1 : R = 1 := by omega
    subst hR1
    have hPN : P * (N - 1) = N - 1 := by omega
    constructor
    · exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < N - 1) (by rw [one_mul]; exact hPN)
    · rfl

/-- **F1 free, `Ma = 1` form** (room ALLN GAPF1, 2026-09-30): the F1FreeStatement proof with the primality
input replaced by the pin hypotheses (`Ma = 1` ⇒ `c(N−1) = a(N+1) ∧ μ(c−a) = b`), for any `N > 6`. -/
theorem f1_free_Ma1 {N : ℕ} (D : CongruentDissection N) (h6 : 6 < N) {α a b c : ℝ}
    (hirr : IrrPi α) (hm : D.model.TwoPiThreeData α a b c) (hF1shape : F1Shape D α)
    (hP1 : ∀ μ : ℝ, 0 < μ → D.target.F1Data α a b c μ →
      c * ((N : ℝ) - 1) = a * ((N : ℝ) + 1) ∧ μ * (c - a) = b)
    (hP2 : ∀ μ : ℝ, 0 < μ → D.target.F1Data (Real.pi / 3 - α) b a c μ →
      c * ((N : ℝ) - 1) = b * ((N : ℝ) + 1) ∧ μ * (c - b) = a) : False := by
  rcases f1_data_of_f1shape D hm hF1shape with ⟨μ, hμ, hF1⟩ | ⟨μ, hμ, hF1'⟩
  · have hpm := hP1 μ hμ hF1
    obtain ⟨σ, hside_eq, hQzero⟩ := f1_V1V2_b_zero D hirr hm hF1 hμ hpm h6
    have hword := f1_word_from_bzero D hirr hm hF1 hμ hpm h6 σ hside_eq
    obtain ⟨i', X, hγ, j₂, hj_ne, hX1, hX2⟩ :=
      f1_Tprime_K2_proved D hirr hm hF1 hμ hpm h6 σ hside_eq hQzero hword
    exact f1_k2_contradiction D hirr hm hF1 i' X hγ (σ 2 + 1) j₂ hj_ne.symm hX1 hX2
  · have hirr' : IrrPi (Real.pi / 3 - α) := by
      intro ⟨q, hq⟩; apply hirr; exact ⟨1/3 - q, by push_cast; linarith⟩
    have hm' : D.model.TwoPiThreeData (Real.pi / 3 - α) b a c :=
      Erdos634.Geometry.twoPiThreeData_swap D.model hm
    have hpm := hP2 μ hμ hF1'
    obtain ⟨σ, hside_eq, hQzero⟩ := f1_V1V2_b_zero D hirr' hm' hF1' hμ hpm h6
    have hword := f1_word_from_bzero D hirr' hm' hF1' hμ hpm h6 σ hside_eq
    obtain ⟨i', X, hγ, j₂, hj_ne, hX1, hX2⟩ :=
      f1_Tprime_K2_proved D hirr' hm' hF1' hμ hpm h6 σ hside_eq hQzero hword
    exact f1_k2_contradiction D hirr' hm' hF1' i' X hγ (σ 2 + 1) j₂ hj_ne.symm hX1 hX2

end Erdos634.Draft.F1FreeProofM

#print axioms Erdos634.Draft.F1FreeProofM.f1_free_Ma1
