-- Draft/F1BEdgeBoundary.lean — Step 4 of prop:F1free (PROOF_F1free.md).
--
-- Proves `f1_V1V2_b_zero`:  the side of an F₁ target with length μ·(a+b)
-- (the "V₁V₂ side", opposite the 2π/3−α vertex) carries zero b-edges.
--
-- This is the key irrationality step:  P·a + Q·b + R·c = 2Nc/(N+1) forces Q = 0
-- because b/c ∉ ℚ (proved by `f1_b_over_c_irrational`) while the remaining
-- combination P·(N−1)/(N+1) + R − 2N/(N+1) is rational.
--
-- The full Step 4 conclusion ("every tile has its b-edge on V₂V₃ ∪ V₃V₁") follows
-- from this plus the injection argument (each tile has exactly one b-edge, N boundary
-- b-edges → every tile appears); that injection is BLOCKER for the next file.
--
-- ZERO sorry.  Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).

import Erdos634.Draft.F1AlgebraPin
import Erdos634.Draft.F1IrrationalRatioM
import Erdos634.Draft.F1Bridge
import Erdos634.Draft.FluxDRow2S1
import Erdos634.Draft.F1AreaIdentity
import Erdos634.EdgeChain

open scoped Classical

namespace Erdos634.Draft.F1BEdgeBoundaryM

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

/-! ## Helper: μ·(a+b) = 2·N·c/(N+1) -/

lemma f1_mu_ab_val {N : ℕ} {a b c μ : ℝ}
    (ha0 : 0 < a) (hb0 : 0 < b) (hc0 : 0 < c) (hμ : 0 < μ)
    (hpin : c * ((N : ℝ) - 1) = a * ((N : ℝ) + 1))
    (hmu  : μ * (c - a) = b)
    (harea : (N : ℝ) * b = μ ^ 2 * (a + b))
    (hN1 : (0 : ℝ) < (N : ℝ) + 1) :
    μ * (a + b) = 2 * (N : ℝ) * c / ((N : ℝ) + 1) := by
  have hμne : μ ≠ 0 := hμ.ne'
  -- b*(N+1) = 2μc  from hmu + hpin
  have hb_N1 : b * ((N : ℝ) + 1) = 2 * μ * c := by nlinarith [hpin, hmu]
  -- μ*(a+b)*μ = N*b  from harea
  have hmu_ab_sq : μ * (μ * (a + b)) = (N : ℝ) * b := by nlinarith [harea]
  -- μ*(a+b)*(N+1) = 2Nc  (multiply hmu_ab_sq by (N+1), substitute N*b*(N+1) = N*2μc)
  have hmu_ab_N1 : μ * (a + b) * ((N : ℝ) + 1) = 2 * (N : ℝ) * c := by
    have h1 : (N : ℝ) * b * ((N : ℝ) + 1) = (N : ℝ) * (2 * μ * c) := by nlinarith [hb_N1]
    nlinarith [hmu_ab_sq, h1]
  rw [eq_div_iff hN1.ne']
  linarith [hmu_ab_N1]

/-! ## Main: the V₁V₂ side carries zero b-edges -/

/-- **F₁ Step 4 (irrationality piece).**
For an F₁ CongruentDissection with prime N > 3, the side of length μ·(a+b) — the side
from V₁ = target.pts(σ 0) to V₂ = target.pts(σ 1) — carries zero b-edges. -/
theorem f1_V1V2_b_zero {N : ℕ} (D : CongruentDissection N) {α a b c μ : ℝ}
    (hα  : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hm  : D.model.TwoPiThreeData α a b c)
    (hF1 : D.target.F1Data α a b c μ)
    (hμ  : 0 < μ)
    (hpm : c * ((N : ℝ) - 1) = a * ((N : ℝ) + 1) ∧ μ * (c - a) = b)
    (h6  : 6 < N) :
    ∃ σ : Equiv.Perm (Fin 3),
      dist (D.target.pts (σ 2 + 1)) (D.target.pts (σ 2 + 2)) = μ * (a + b) ∧
      ∀ P Q R : ℕ,
        (P : ℝ) * a + (Q : ℝ) * b + (R : ℝ) * c =
          dist (D.target.pts (σ 2 + 1)) (D.target.pts (σ 2 + 2)) →
        Q = 0 := by
  -- Side positivity
  obtain ⟨-, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  -- Algebraic pin and μ-relation
  obtain ⟨hpin, hmu⟩ := id hpm
  -- Area identity
  have harea : (N : ℝ) * b = μ ^ 2 * (a + b) := F1_area_identity D hm hF1 ha0 hb0 hμ
  have hN1pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  -- b/c is irrational
  have hirr : ¬ ∃ (r : ℚ), b = (r : ℝ) * c := f1_b_over_c_irrational D hα hm hF1 hμ hpm h6
  have hbc_notrat : NotRat (b / c) := by
    intro ⟨q, hq⟩; apply hirr
    exact ⟨q, by rw [div_eq_iff hc0.ne'] at hq; linarith⟩
  -- μ·(a+b) = 2·N·c/(N+1)
  have hmu_ab : μ * (a + b) = 2 * (N : ℝ) * c / ((N : ℝ) + 1) :=
    f1_mu_ab_val ha0 hb0 hc0 hμ hpin hmu harea hN1pos
  -- Extract σ from F1Data
  obtain ⟨-, hgrid⟩ := hF1
  obtain ⟨σ, -, -, -, -, -, hoppLen2⟩ := hgrid
  -- oppLen(σ 2) = dist(pts(σ 2+1))(pts(σ 2+2)) = μ·(a+b)
  have hside_len_mu : dist (D.target.pts (σ 2 + 1)) (D.target.pts (σ 2 + 2)) =
      μ * (a + b) := by
    have : D.target.oppLen (σ 2) = μ * (a + b) := hoppLen2
    simp [Tri.oppLen] at this
    rw [this]
  have hside_len : dist (D.target.pts (σ 2 + 1)) (D.target.pts (σ 2 + 2)) =
      2 * (N : ℝ) * c / ((N : ℝ) + 1) := by rw [hside_len_mu, hmu_ab]
  -- Provide the witness σ
  exact ⟨σ, hside_len_mu, fun P Q R hPQR => by
    -- hPQR: P*a + Q*b + R*c = 2Nc/(N+1)
    -- a = c*(N-1)/(N+1)
    have ha_val : a = c * ((N : ℝ) - 1) / ((N : ℝ) + 1) := by
      field_simp [hN1pos.ne']; linarith
    -- Rewrite hPQR: (Q:ℝ)*b + (P*(N-1)/(N+1) + R - 2N/(N+1))*c = 0
    have hcne : c ≠ 0 := hc0.ne'
    have heq : ((Q : ℝ) - 0) * (b / c) +
        ((P : ℝ) * ((N : ℝ) - 1) / ((N : ℝ) + 1) + (R : ℝ) - 2 * (N : ℝ) / ((N : ℝ) + 1)) = 0 := by
      rw [hside_len] at hPQR
      rw [ha_val] at hPQR
      field_simp [hcne, hN1pos.ne'] at hPQR ⊢
      linarith
    -- Cast to ℚ coefficients
    set rQ : ℚ := (Q : ℚ) - 0
    set c0K : ℚ := (P : ℚ) * (((N : ℤ) - 1 : ℤ) : ℚ) / (((N : ℤ) + 1 : ℤ) : ℚ) +
                   (R : ℚ) - 2 * (N : ℚ) / (((N : ℤ) + 1 : ℤ) : ℚ)
    have hrQ_cast : (rQ : ℝ) = (Q : ℝ) - 0 := by simp [rQ]
    have hc0K_cast : (c0K : ℝ) =
        (P : ℝ) * ((N : ℝ) - 1) / ((N : ℝ) + 1) + (R : ℝ) - 2 * (N : ℝ) / ((N : ℝ) + 1) := by
      simp only [c0K]
      push_cast
      field_simp [hN1pos.ne']
    have heq_rat : (rQ : ℝ) * (b / c) + (c0K : ℝ) = 0 := by
      rw [hrQ_cast, hc0K_cast]; linarith [heq]
    obtain ⟨hrQ_zero, -⟩ := rat_coeff_unique hbc_notrat rQ c0K heq_rat
    have : (Q : ℚ) = 0 := by
      have : rQ = 0 := hrQ_zero
      simp [rQ] at this
      exact_mod_cast this
    exact_mod_cast this⟩

/-! ## Helper: model's b-edge count = 1 -/

/-- The side-length b appears exactly once in the model's side multiset.
Follows from b ≠ a and b ≠ c together with the TwoPiThreeData permutation. -/
private lemma model_b_count_one {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hm : D.model.TwoPiThreeData α a b c)
    (hb_ne_a : b ≠ a) (hb_ne_c : b ≠ c) :
    Multiset.count b ({dist (D.model.pts 0) (D.model.pts 1),
        dist (D.model.pts 2) (D.model.pts 0),
        dist (D.model.pts 1) (D.model.pts 2)} : Multiset ℝ) = 1 := by
  obtain ⟨σ, -, ha_op, -, hb_op, -, hc_op⟩ := hm
  -- Use sideMultiset_shift at σ 1 to get the model sides in the shifted form
  have hshift := Tri.sideMultiset_shift D.model (σ 1)
  -- The third element of the shifted multiset = oppLen(σ1) = b
  have hthird : dist (D.model.pts (σ 1 + 1)) (D.model.pts (σ 1 + 2)) = b := by
    have h := hb_op; simp only [Tri.oppLen] at h; exact h
  -- σ1+1 ≠ σ1 and σ1+2 ≠ σ1 in Fin 3 (true for all k : Fin 3, verified by decide)
  have hne1 : σ 1 + 1 ≠ σ 1 := (show ∀ k : Fin 3, k + 1 ≠ k from by decide) (σ 1)
  have hne2 : σ 1 + 2 ≠ σ 1 := (show ∀ k : Fin 3, k + 2 ≠ k from by decide) (σ 1)
  -- oppLen(σ1+1) ≠ b  (σ1+1 = σ0 or σ2; either way oppLen = a or c)
  have h_ne1 : D.model.oppLen (σ 1 + 1) ≠ b := by
    have h01 : σ 1 + 1 = σ 0 ∨ σ 1 + 1 = σ 1 ∨ σ 1 + 1 = σ 2 := by
      obtain ⟨j, hj⟩ := σ.surjective (σ 1 + 1)
      fin_cases j
      · exact Or.inl hj.symm
      · exact Or.inr (Or.inl hj.symm)
      · exact Or.inr (Or.inr hj.symm)
    rcases h01 with h | h | h
    · rw [h, ha_op]; exact hb_ne_a.symm
    · exact absurd h hne1
    · rw [h, hc_op]; exact hb_ne_c.symm
  -- oppLen(σ1+2) ≠ b
  have h_ne2 : D.model.oppLen (σ 1 + 2) ≠ b := by
    have h02 : σ 1 + 2 = σ 0 ∨ σ 1 + 2 = σ 1 ∨ σ 1 + 2 = σ 2 := by
      obtain ⟨j, hj⟩ := σ.surjective (σ 1 + 2)
      fin_cases j
      · exact Or.inl hj.symm
      · exact Or.inr (Or.inl hj.symm)
      · exact Or.inr (Or.inr hj.symm)
    rcases h02 with h | h | h
    · rw [h, ha_op]; exact hb_ne_a.symm
    · exact absurd h hne2
    · rw [h, hc_op]; exact hb_ne_c.symm
  -- The shifted multiset has first element = oppLen(σ1+2) and second = oppLen(σ1+1)
  have hfirst : dist (D.model.pts (σ 1)) (D.model.pts (σ 1 + 1)) = D.model.oppLen (σ 1 + 2) := by
    simp only [Tri.oppLen]
    have h221 : σ 1 + 2 + 1 = σ 1 :=
      (show ∀ k : Fin 3, k + 2 + 1 = k from by decide) (σ 1)
    have h222 : σ 1 + 2 + 2 = σ 1 + 1 :=
      (show ∀ k : Fin 3, k + 2 + 2 = k + 1 from by decide) (σ 1)
    rw [h221, h222]
  have hsecond : dist (D.model.pts (σ 1 + 2)) (D.model.pts (σ 1)) = D.model.oppLen (σ 1 + 1) := by
    simp only [Tri.oppLen]
    have h121 : σ 1 + 1 + 1 = σ 1 + 2 :=
      (show ∀ k : Fin 3, k + 1 + 1 = k + 2 from by decide) (σ 1)
    have h122 : σ 1 + 1 + 2 = σ 1 :=
      (show ∀ k : Fin 3, k + 1 + 2 = k from by decide) (σ 1)
    rw [h121, h122]
  -- Rewrite model sides via the shift equality
  rw [← hshift, hfirst, hsecond, hthird]
  -- count b {oppLen(σ1+2), oppLen(σ1+1), b} = 1
  simp [h_ne1, h_ne2, h_ne1.symm, h_ne2.symm]

/-! ## (★): each tile has exactly one b-edge -/

/-- **F₁ tile b-edge uniqueness (★).**  For a 2π/3 model with b ≠ a and b ≠ c, each tile of a
congruent dissection has exactly one edge of length b. -/
theorem f1_tile_b_unique {N : ℕ} (D : CongruentDissection N) {α a b c μ : ℝ}
    (hα  : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hm  : D.model.TwoPiThreeData α a b c)
    (hF1 : D.target.F1Data α a b c μ)
    (hμ  : 0 < μ)
    (hpm : c * ((N : ℝ) - 1) = a * ((N : ℝ) + 1) ∧ μ * (c - a) = b)
    (h6  : 6 < N)
    (i   : Fin N) :
    ∃! k : Fin 3, dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = b := by
  -- b ≠ c (b/c ∉ ℚ) and b ≠ a (a/c ∈ ℚ)
  obtain ⟨-, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  obtain ⟨hpin, -⟩ := id hpm
  have hirr : ¬ ∃ r : ℚ, b = (r : ℝ) * c := f1_b_over_c_irrational D hα hm hF1 hμ hpm h6
  have hb_ne_c : b ≠ c := fun h => hirr ⟨1, by push_cast; linarith⟩
  have hb_ne_a : b ≠ a := fun h => hirr ⟨((N : ℤ) - 1 : ℤ) / ((N : ℤ) + 1 : ℤ), by
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    rw [h]; push_cast; field_simp [hN1.ne']; linarith [hpin]⟩
  -- Save model b-count before destructuring hm
  have hcount_model_saved : Multiset.count b ({dist (D.model.pts 0) (D.model.pts 1),
      dist (D.model.pts 2) (D.model.pts 0),
      dist (D.model.pts 1) (D.model.pts 2)} : Multiset ℝ) = 1 :=
    model_b_count_one D hm hb_ne_a hb_ne_c
  -- σ from TwoPiThreeData: model.oppLen(σ 1) = b
  obtain ⟨σ, -, -, -, hb_opp, -, -⟩ := hm
  -- sideMultiset of tile i = sideMultiset of model (by congruence)
  have hmulti := (D.tiles_congruent i).sideMultiset_eq
  -- b belongs to the model's side multiset (via oppLen(σ 1) = b)
  have hb_in_model : b ∈ ({dist (D.model.pts 0) (D.model.pts 1),
      dist (D.model.pts 2) (D.model.pts 0),
      dist (D.model.pts 1) (D.model.pts 2)} : Multiset ℝ) := by
    have hshift := Tri.sideMultiset_shift D.model (σ 1)
    have hmem : dist (D.model.pts (σ 1 + 1)) (D.model.pts (σ 1 + 2)) ∈
        ({dist (D.model.pts (σ 1)) (D.model.pts (σ 1 + 1)),
          dist (D.model.pts (σ 1 + 2)) (D.model.pts (σ 1)),
          dist (D.model.pts (σ 1 + 1)) (D.model.pts (σ 1 + 2))} : Multiset ℝ) := by simp
    rw [hshift] at hmem
    rwa [← hb_opp, Tri.oppLen]
  -- b belongs to the tile's side multiset (via hmulti)
  rw [← hmulti] at hb_in_model
  -- Extract existence: b equals one of the three tile edge distances
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hb_in_model
  -- The three entries of the multiset {d₀, d₁, d₂} correspond to k=0,2,1
  set d₀ := dist ((D.tile i).pts 0) ((D.tile i).pts 1)
  set d₁ := dist ((D.tile i).pts 2) ((D.tile i).pts 0)
  set d₂ := dist ((D.tile i).pts 1) ((D.tile i).pts 2)
  -- d₁ = edge at k=2; d₂ = edge at k=1
  have hd₁_k2 : d₁ = dist ((D.tile i).pts 2) ((D.tile i).pts (2 + 1)) := by
    simp [d₁, show (2 : Fin 3) + 1 = (0 : Fin 3) from by decide]
  have hd₂_k1 : d₂ = dist ((D.tile i).pts 1) ((D.tile i).pts (1 + 1)) := by
    simp [d₂, show (1 : Fin 3) + 1 = (2 : Fin 3) from by decide]
  -- Uniform count helper: {d₀,d₁,d₂} = model sides, so count b = 1.
  have hcount1 : Multiset.count b ({d₀, d₁, d₂} : Multiset ℝ) = 1 :=
    hmulti ▸ hcount_model_saved
  -- Existence + uniqueness in each branch.
  rcases hb_in_model with h | h | h
  · -- b = d₀ = edge at k=0
    refine ⟨0, h.symm, fun k hk => ?_⟩
    -- uniqueness: if some other k has dist = b, count ≥ 2, contradicting hcount1 = 1
    by_contra hne
    have hk_in : k = 1 ∨ k = 2 := by fin_cases k <;> simp_all
    exfalso
    rcases hk_in with rfl | rfl
    · -- k=1: d₂ = b
      have hb_d₂ : d₂ = b := hd₂_k1.trans hk
      have : 2 ≤ Multiset.count b ({d₀, d₁, d₂} : Multiset ℝ) := by
        simp only [show d₀ = b from h.symm, show d₂ = b from hb_d₂,
                   Multiset.insert_eq_cons, Multiset.count_cons,
                   Multiset.count_singleton, Multiset.count_zero, if_pos rfl]
        split_ifs <;> omega
      omega
    · -- k=2: d₁ = b
      have hb_d₁ : d₁ = b := hd₁_k2.trans hk
      have : 2 ≤ Multiset.count b ({d₀, d₁, d₂} : Multiset ℝ) := by
        simp only [show d₀ = b from h.symm, show d₁ = b from hb_d₁,
                   Multiset.insert_eq_cons, Multiset.count_cons,
                   Multiset.count_singleton, Multiset.count_zero, if_pos rfl]
        split_ifs <;> omega
      omega
  · -- b = d₁ = edge at k=2
    refine ⟨2, hd₁_k2.symm.trans h.symm, fun k hk => ?_⟩
    by_contra hne
    have hk_in : k = 0 ∨ k = 1 := by fin_cases k <;> simp_all
    exfalso
    rcases hk_in with rfl | rfl
    · -- k=0: d₀ = b
      have hb_d₀ : d₀ = b := hk
      have : 2 ≤ Multiset.count b ({d₀, d₁, d₂} : Multiset ℝ) := by
        simp only [show d₀ = b from hb_d₀, show d₁ = b from h.symm,
                   Multiset.insert_eq_cons, Multiset.count_cons,
                   Multiset.count_singleton, Multiset.count_zero, if_pos rfl]
        split_ifs <;> omega
      omega
    · -- k=1: d₂ = b
      have hb_d₂ : d₂ = b := hd₂_k1.trans hk
      have : 2 ≤ Multiset.count b ({d₀, d₁, d₂} : Multiset ℝ) := by
        simp only [show d₁ = b from h.symm, show d₂ = b from hb_d₂,
                   Multiset.insert_eq_cons, Multiset.count_cons,
                   Multiset.count_singleton, Multiset.count_zero, if_pos rfl]
        split_ifs <;> omega
      omega
  · -- b = d₂ = edge at k=1
    refine ⟨1, hd₂_k1.symm.trans h.symm, fun k hk => ?_⟩
    by_contra hne
    have hk_in : k = 0 ∨ k = 2 := by fin_cases k <;> simp_all
    exfalso
    rcases hk_in with rfl | rfl
    · -- k=0: d₀ = b
      have hb_d₀ : d₀ = b := hk
      have : 2 ≤ Multiset.count b ({d₀, d₁, d₂} : Multiset ℝ) := by
        simp only [show d₀ = b from hb_d₀, show d₂ = b from h.symm,
                   Multiset.insert_eq_cons, Multiset.count_cons,
                   Multiset.count_singleton, Multiset.count_zero, if_pos rfl]
        split_ifs <;> omega
      omega
    · -- k=2: d₁ = b
      have hb_d₁ : d₁ = b := hd₁_k2.trans hk
      have : 2 ≤ Multiset.count b ({d₀, d₁, d₂} : Multiset ℝ) := by
        simp only [show d₂ = b from h.symm, show d₁ = b from hb_d₁,
                   Multiset.insert_eq_cons, Multiset.count_cons,
                   Multiset.count_singleton, Multiset.count_zero, if_pos rfl]
        split_ifs <;> omega
      omega

#check @f1_V1V2_b_zero
#print axioms f1_V1V2_b_zero

end Erdos634.Draft.F1BEdgeBoundaryM
