-- Draft/F1SideWord.lean — Steps 3–4 of prop:F1free (PROOF_F1free.md).
--
-- Main result: `f1_total_b_count`.  For prime N > 3, a 2π/3 model, and an F₁ target,
-- the three side-word decompositions (from `Dissection.side_walk_abc`) satisfy
-- Q₀ + Q₁ + Q₂ = N (total b-edges on the boundary equals the tile count N).
--
-- Proof sketch:
--   • `habc`: every tile edge ∈ {a,b,c} via `CongruentDissection.eLen_mem`.
--   • Apply `side_walk_abc` to sides 0, 1, 2 → P_i,Q_i,R_i with
--         (P_i:ℝ)*a + (Q_i:ℝ)*b + (R_i:ℝ)*c = dist(pts i)(pts i+1).
--   • Sum over i: (ΣP)*a + (ΣQ)*b + (ΣR)*c = perimeter.
--   • From `f1_pin_mu_of_prime`: c*(N-1)=a*(N+1), μ*(c-a)=b.
--   • From `F1_area_identity`: N*b = μ²*(a+b).
--   • F₁ perimeter = μa + μc + μ(a+b) = N*b + 2*N*c/(N+1).
--   • Rearrange to (ΣQ-N)*(b/c) + K = 0, K ∈ ℚ.
--   • `f1_b_over_c_irrational` + `rat_coeff_unique` → ΣQ = N. ✓
--
-- ZERO sorry.  Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).

import Erdos634.Draft.F1AlgebraPin
import Erdos634.Draft.F1IrrationalRatioM
import Erdos634.Draft.F1Bridge
import Erdos634.Draft.FluxDRow2S1
import Erdos634.Draft.F1AreaIdentity
import Erdos634.EdgeChain

open scoped Classical

namespace Erdos634.Draft.F1SideWordM

open Erdos634.Geometry
open Erdos634.Row14 (NotRat rat_coeff_unique)
open Erdos634.Draft.F1IrrationalRatioM (f1_b_over_c_irrational)
open Erdos634.Draft.F1AreaIdentity (F1_area_identity)

/-! ## Helper: every tile edge is in {a, b, c} -/

private lemma tile_edges_abc {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hm : D.model.TwoPiThreeData α a b c) :
    ∀ (j : Fin N) (k : Fin 3),
      dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = a ∨
      dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = b ∨
      dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = c := by
  intro j k
  obtain ⟨m, hm_eq⟩ := D.eLen_mem ⟨j, k⟩
  have hdef : D.eLen ⟨j, k⟩ = dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) := rfl
  rw [← hdef, hm_eq]
  obtain ⟨σ, -, ha_op, -, hb_op, -, hc_op⟩ := hm
  obtain ⟨i, rfl⟩ := σ.surjective m
  fin_cases i
  · exact Or.inl ha_op
  · exact Or.inr (Or.inl hb_op)
  · exact Or.inr (Or.inr hc_op)

/-! ## Helper: F₁ perimeter = N*b + 2*N*c/(N+1) -/

private lemma f1_perimeter {N : ℕ} {a b c μ : ℝ}
    (ha0 : 0 < a) (hb0 : 0 < b) (hc0 : 0 < c) (hμ : 0 < μ)
    (hpin : c * ((N : ℝ) - 1) = a * ((N : ℝ) + 1))
    (hmu  : μ * (c - a) = b)
    (harea : (N : ℝ) * b = μ ^ 2 * (a + b))
    (hN1 : (0 : ℝ) < (N : ℝ) + 1) :
    μ * a + μ * c + μ * (a + b) = (N : ℝ) * b + 2 * (N : ℝ) * c / ((N : ℝ) + 1) := by
  have hmu_a_2 : 2 * (μ * a) = ((N : ℝ) - 1) * b := by nlinarith
  have hmu_c_2 : 2 * (μ * c) = ((N : ℝ) + 1) * b := by nlinarith
  have hmu_ab : μ * (a + b) * ((N : ℝ) + 1) = 2 * (N : ℝ) * c := by
    have h1 : μ * (μ * (a + b)) = (N : ℝ) * b := by nlinarith [sq_nonneg μ, harea]
    have h2 : μ * (a + b) * ((N : ℝ) + 1) * μ = 2 * (N : ℝ) * c * μ := by nlinarith
    exact mul_right_cancel₀ hμ.ne' (by linarith)
  -- μ*a + μ*c = N*b  (from hmu_a_2 + hmu_c_2)
  have hsum_μac : μ * a + μ * c = (N : ℝ) * b := by linarith
  -- μ*(a+b) = 2*N*c/(N+1)
  have hμab_eq : μ * (a + b) = 2 * (N : ℝ) * c / ((N : ℝ) + 1) := by
    rw [eq_div_iff hN1.ne']
    linarith [hmu_ab]
  linarith [hsum_μac, hμab_eq]

/-! ## Helper: target perimeter = sum of oppLen values -/

private lemma sum_oppLen_eq_perimeter (T : Tri) :
    T.oppLen 0 + T.oppLen 1 + T.oppLen 2 =
    dist (T.pts 0) (T.pts 1) + dist (T.pts 1) (T.pts 2) + dist (T.pts 2) (T.pts 0) := by
  unfold Tri.oppLen
  have h00 : (0 : Fin 3) + 1 = 1 := by decide
  have h01 : (0 : Fin 3) + 2 = 2 := by decide
  have h10 : (1 : Fin 3) + 1 = 2 := by decide
  have h11 : (1 : Fin 3) + 2 = 0 := by decide
  have h20 : (2 : Fin 3) + 1 = 0 := by decide
  have h21 : (2 : Fin 3) + 2 = 1 := by decide
  simp only [h00, h01, h10, h11, h20, h21, dist_comm]
  ring

private lemma f1_oppLen_sum {T : Tri} {α a b c μ : ℝ}
    (hF1 : T.F1Data α a b c μ) :
    T.oppLen 0 + T.oppLen 1 + T.oppLen 2 = μ * a + μ * c + μ * (a + b) := by
  obtain ⟨-, hgrid⟩ := hF1
  obtain ⟨σ, -, hs0, -, hs1, -, hs2⟩ := hgrid
  -- ∑ i : Fin 3, T.oppLen (σ i) = ∑ i, T.oppLen i  (Equiv.sum_comp)
  have hperm : T.oppLen 0 + T.oppLen 1 + T.oppLen 2 =
      T.oppLen (σ 0) + T.oppLen (σ 1) + T.oppLen (σ 2) := by
    have h : ∑ i : Fin 3, T.oppLen (σ i) = ∑ i : Fin 3, T.oppLen i :=
      Equiv.sum_comp σ T.oppLen
    simp only [Fin.sum_univ_three] at h
    linarith
  rw [hperm, hs0, hs1, hs2]

/-! ## Main theorem: total b-count = N -/

set_option maxHeartbeats 800000 in
theorem f1_total_b_count {N : ℕ} (D : CongruentDissection N) {α a b c μ : ℝ}
    (hα  : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hm  : D.model.TwoPiThreeData α a b c)
    (hF1 : D.target.F1Data α a b c μ)
    (hμ  : 0 < μ)
    (hpm : c * ((N : ℝ) - 1) = a * ((N : ℝ) + 1) ∧ μ * (c - a) = b)
    (h6  : 6 < N) :
    ∃ P0 Q0 R0 P1 Q1 R1 P2 Q2 R2 : ℕ,
      (P0 : ℝ) * a + (Q0 : ℝ) * b + (R0 : ℝ) * c
        = dist (D.target.pts 0) (D.target.pts 1) ∧
      (P1 : ℝ) * a + (Q1 : ℝ) * b + (R1 : ℝ) * c
        = dist (D.target.pts 1) (D.target.pts 2) ∧
      (P2 : ℝ) * a + (Q2 : ℝ) * b + (R2 : ℝ) * c
        = dist (D.target.pts 2) (D.target.pts (0 : Fin 3)) ∧
      Q0 + Q1 + Q2 = N := by
  obtain ⟨-, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  obtain ⟨hpin, hmu⟩ := id hpm
  have hirr : ¬ ∃ r : ℚ, b = (r : ℝ) * c :=
    f1_b_over_c_irrational D hα hm hF1 hμ hpm h6
  have hbc_notrat : NotRat (b / c) := by
    intro ⟨q, hq⟩
    apply hirr
    exact ⟨q, by rw [div_eq_iff hc0.ne'] at hq; linarith⟩
  have harea : (N : ℝ) * b = μ ^ 2 * (a + b) :=
    F1_area_identity D hm hF1 ha0 hb0 hμ
  have hN1pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  -- Build habc
  have habc : ∀ (j : Fin N) (k : Fin 3),
      dist ((D.toDissection.tile j).pts k) ((D.toDissection.tile j).pts (k + 1)) = a ∨
      dist ((D.toDissection.tile j).pts k) ((D.toDissection.tile j).pts (k + 1)) = b ∨
      dist ((D.toDissection.tile j).pts k) ((D.toDissection.tile j).pts (k + 1)) = c :=
    tile_edges_abc D hm
  -- Apply side_walk_abc to each side
  obtain ⟨P0, Q0, R0, hside0, -⟩ := D.toDissection.side_walk_abc 0 a b c habc
  obtain ⟨P1, Q1, R1, hside1, -⟩ := D.toDissection.side_walk_abc 1 a b c habc
  obtain ⟨P2, Q2, R2, hside2, -⟩ := D.toDissection.side_walk_abc 2 a b c habc
  -- side 2: (2 : Fin 3) + 1 = 0
  have hside2' : (P2 : ℝ) * a + (Q2 : ℝ) * b + (R2 : ℝ) * c =
      dist (D.target.pts 2) (D.target.pts (0 : Fin 3)) := by
    simp only [show (2 : Fin 3) + 1 = (0 : Fin 3) from by decide] at hside2
    exact hside2
  refine ⟨P0, Q0, R0, P1, Q1, R1, P2, Q2, R2, hside0, hside1, hside2', ?_⟩
  -- Rettype side hypotheses to D.target (definitionally equal to D.toDissection.target)
  have hs0 : (P0 : ℝ) * a + (Q0 : ℝ) * b + (R0 : ℝ) * c =
      dist (D.target.pts 0) (D.target.pts 1) := hside0
  have hs1 : (P1 : ℝ) * a + (Q1 : ℝ) * b + (R1 : ℝ) * c =
      dist (D.target.pts 1) (D.target.pts 2) := hside1
  -- Sum the three side equations
  have hsum : ((P0 + P1 + P2 : ℕ) : ℝ) * a + ((Q0 + Q1 + Q2 : ℕ) : ℝ) * b +
      ((R0 + R1 + R2 : ℕ) : ℝ) * c =
      dist (D.target.pts 0) (D.target.pts 1) +
      dist (D.target.pts 1) (D.target.pts 2) +
      dist (D.target.pts 2) (D.target.pts 0) := by
    push_cast
    linear_combination hs0 + hs1 + hside2'
  -- The dist sum = oppLen sum = perimeter value
  have hperim_val : dist (D.target.pts 0) (D.target.pts 1) +
      dist (D.target.pts 1) (D.target.pts 2) +
      dist (D.target.pts 2) (D.target.pts 0) =
      (N : ℝ) * b + 2 * (N : ℝ) * c / ((N : ℝ) + 1) := by
    rw [← sum_oppLen_eq_perimeter]
    exact (f1_oppLen_sum hF1).trans (f1_perimeter ha0 hb0 hc0 hμ hpin hmu harea hN1pos)
  -- Combined equation
  have hcombined : ((P0 + P1 + P2 : ℕ) : ℝ) * a + ((Q0 + Q1 + Q2 : ℕ) : ℝ) * b +
      ((R0 + R1 + R2 : ℕ) : ℝ) * c = (N : ℝ) * b + 2 * (N : ℝ) * c / ((N : ℝ) + 1) :=
    hsum.trans hperim_val
  -- Substitute a = c*(N-1)/(N+1) to get equation in b and c only
  have ha_val : a = c * ((N : ℝ) - 1) / ((N : ℝ) + 1) := by
    field_simp [hN1pos.ne']; linarith
  rw [ha_val] at hcombined
  have hcne : c ≠ 0 := hc0.ne'
  have hcombined2 : ((Q0 + Q1 + Q2 : ℕ) : ℝ) * b +
      (((P0 + P1 + P2 : ℕ) : ℝ) * ((N : ℝ) - 1) / ((N : ℝ) + 1) +
       ((R0 + R1 + R2 : ℕ) : ℝ)) * c = (N : ℝ) * b + 2 * (N : ℝ) / ((N : ℝ) + 1) * c := by
    field_simp [hN1pos.ne'] at hcombined ⊢; linarith
  -- Rearrange to r*(b/c) + c0 = 0
  have heq_bc : (((Q0 + Q1 + Q2 : ℕ) : ℝ) - N) * (b / c) +
      (((P0 + P1 + P2 : ℕ) : ℝ) * ((N : ℝ) - 1) / ((N : ℝ) + 1) +
       ((R0 + R1 + R2 : ℕ) : ℝ) - 2 * (N : ℝ) / ((N : ℝ) + 1)) = 0 := by
    field_simp [hcne, hN1pos.ne'] at hcombined2 ⊢; linarith
  -- Cast rational coefficients to ℚ
  set rQ : ℚ := ((Q0 + Q1 + Q2 : ℕ) : ℚ) - (N : ℚ)
  set c0K : ℚ := ((P0 + P1 + P2 : ℕ) : ℚ) * (((N : ℤ) - 1 : ℤ) : ℚ) / (((N : ℤ) + 1 : ℤ) : ℚ) +
                 ((R0 + R1 + R2 : ℕ) : ℚ) - 2 * (N : ℚ) / (((N : ℤ) + 1 : ℤ) : ℚ)
  have hrQ_cast : (rQ : ℝ) = ((Q0 + Q1 + Q2 : ℕ) : ℝ) - N := by
    simp only [rQ]; push_cast; ring
  have hc0K_cast : (c0K : ℝ) =
      ((P0 + P1 + P2 : ℕ) : ℝ) * ((N : ℝ) - 1) / ((N : ℝ) + 1) +
      ((R0 + R1 + R2 : ℕ) : ℝ) - 2 * (N : ℝ) / ((N : ℝ) + 1) := by
    simp only [c0K]; push_cast; field_simp [hN1pos.ne']
  have heq_rat : (rQ : ℝ) * (b / c) + (c0K : ℝ) = 0 := by
    rw [hrQ_cast, hc0K_cast]; exact heq_bc
  -- rat_coeff_unique: the coefficient of (b/c) must be 0
  obtain ⟨hrQ_zero, -⟩ := rat_coeff_unique hbc_notrat rQ c0K heq_rat
  have hQN_Q : ((Q0 + Q1 + Q2 : ℕ) : ℚ) = (N : ℚ) := by
    have : rQ = 0 := hrQ_zero
    simp [rQ] at this; linarith
  exact_mod_cast hQN_Q

#check @f1_total_b_count
#print axioms f1_total_b_count

end Erdos634.Draft.F1SideWordM
