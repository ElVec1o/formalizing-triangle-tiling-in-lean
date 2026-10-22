-- Draft/F1TprimeExtract.lean — Proof of K₁+K₂ (replaces axiom f1_Tprime_K2_inputs).
--
-- Takes hside_eq and hQzero explicitly (from f1_V1V2_b_zero, available in caller).
-- PAPER STATUS: PROVED (prop:F1free Steps 4-5, Lemmas K1-K2).
-- LEAN STATUS: ZERO sorry (complete).

import Erdos634.Draft.F1AlgebraPin
import Erdos634.Draft.F1BEdgeBoundaryM
import Erdos634.Draft.F1IrrationalRatioM
import Erdos634.Draft.F1AreaIdentity
import Erdos634.EdgeChain
import Erdos634.Draft.FluxValue
import Erdos634.Draft.F1SideWordM
import Erdos634.Draft.F1BoundaryK2

open scoped Classical
open Erdos634.Geometry
open Erdos634.Draft.TheoremPConditional (IrrPi)
open Erdos634.Draft.F1IrrationalRatioM (f1_b_over_c_irrational)
open Erdos634.Draft.F1BEdgeBoundaryM (f1_tile_b_unique)
open Erdos634.Draft.F1SideWordM (f1_total_b_count)
open Erdos634.Row14 (NotRat rat_coeff_unique)

namespace Erdos634.Draft.F1TprimeExtractM

private instance : Fact (Module.finrank ℝ Plane = 2) := by exact ⟨by simp⟩

private lemma fin3_ne_complement (x y : Fin 3) (h : x ≠ y) : x = y + 1 ∨ x = y + 2 := by
  fin_cases x <;> fin_cases y <;> simp_all (config := { decide := true })

-- Explicit sum decomposition with b-filter (not ¬a∧b-filter).
-- When b ≠ a, the b-filter and ¬a∧b-filter are the same set.
private lemma sum_three_filter {ι : Type*} (s : Finset ι) (len : ι → ℝ) (a b c : ℝ)
    (hab : b ≠ a) (h : ∀ e ∈ s, len e = a ∨ len e = b ∨ len e = c) :
    ((s.filter fun e => len e = a).card : ℝ) * a +
    (s.filter fun e => len e = b).card * b +
    (s.filter fun e => ¬ len e = a ∧ ¬ len e = b).card * c =
    ∑ e ∈ s, len e := by
  -- filter b = filter (¬a ∧ b) because b ≠ a
  have hfilt : s.filter (fun e => len e = b) =
      s.filter (fun e => ¬ len e = a ∧ len e = b) := by
    ext e; simp only [Finset.mem_filter]
    exact ⟨fun ⟨he, hb⟩ => ⟨he, fun ha => hab (ha.symm ▸ hb ▸ rfl), hb⟩,
           fun ⟨he, _, hb⟩ => ⟨he, hb⟩⟩
  rw [hfilt]
  have hsplit1 := Finset.sum_filter_add_sum_filter_not s (fun e => len e = a) len
  have hsplit2 := Finset.sum_filter_add_sum_filter_not
    (s.filter fun e => ¬ len e = a) (fun e => len e = b) len
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit2
  have hA : ∑ e ∈ s.filter (fun e => len e = a), len e =
      ((s.filter fun e => len e = a).card : ℝ) * a := by
    rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2),
        Finset.sum_const, nsmul_eq_mul]
  have hB : ∑ e ∈ s.filter (fun e => ¬ len e = a ∧ len e = b), len e =
      ((s.filter fun e => ¬ len e = a ∧ len e = b).card : ℝ) * b := by
    rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2.2),
        Finset.sum_const, nsmul_eq_mul]
  have hC : ∑ e ∈ s.filter (fun e => ¬ len e = a ∧ ¬ len e = b), len e =
      ((s.filter fun e => ¬ len e = a ∧ ¬ len e = b).card : ℝ) * c := by
    rw [Finset.sum_congr rfl (fun e he => ?_), Finset.sum_const, nsmul_eq_mul]
    rcases h e (Finset.mem_filter.mp he).1 with h' | h' | h'
    · exact absurd h' (Finset.mem_filter.mp he).2.1
    · exact absurd h' (Finset.mem_filter.mp he).2.2
    · exact h'
  linarith [hsplit1, hsplit2, hA, hB, hC]

private lemma f1_b_ne_a {N : ℕ} (D : CongruentDissection N) {α a b c μ : ℝ}
    (hirr : IrrPi α) (hm : D.model.TwoPiThreeData α a b c)
    (hF1 : D.target.F1Data α a b c μ) (hμ : 0 < μ) (hpm : c * ((N : ℝ) - 1) = a * ((N : ℝ) + 1) ∧ μ * (c - a) = b) (h6 : 6 < N) :
    b ≠ a := by
  obtain ⟨-, hc0, ha0, -⟩ := cos_alpha_of_TwoPiThree D.model hm
  obtain ⟨hpin, -⟩ := id hpm
  have hN1pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  intro heq
  exact (f1_b_over_c_irrational D hirr hm hF1 hμ hpm h6) ⟨((N : ℤ) - 1 : ℤ) / ((N : ℤ) + 1 : ℤ), by
    rw [heq]; push_cast; field_simp [hN1pos.ne']; linarith⟩

private lemma f1_a_ne_c {N : ℕ} (D : CongruentDissection N) {α a b c μ : ℝ}
    (hirr : IrrPi α) (hm : D.model.TwoPiThreeData α a b c)
    (hF1 : D.target.F1Data α a b c μ) (hμ : 0 < μ) (hpm : c * ((N : ℝ) - 1) = a * ((N : ℝ) + 1) ∧ μ * (c - a) = b) (h6 : 6 < N) :
    a ≠ c := by
  obtain ⟨-, hc0, ha0, -⟩ := cos_alpha_of_TwoPiThree D.model hm
  obtain ⟨hpin, -⟩ := id hpm
  intro heq
  -- hpin : c*(N-1) = a*(N+1); heq : a = c → a*(N-1) = a*(N+1) → N-1 = N+1
  rw [← heq] at hpin
  have := mul_left_cancel₀ ha0.ne' (by linarith : a * ((N : ℝ) - 1) = a * ((N : ℝ) + 1))
  linarith

private lemma tile_a_edge_unique {N : ℕ} (D : CongruentDissection N) {α a b c μ : ℝ}
    (hirr : IrrPi α) (hm : D.model.TwoPiThreeData α a b c)
    (hF1 : D.target.F1Data α a b c μ) (hμ : 0 < μ) (hpm : c * ((N : ℝ) - 1) = a * ((N : ℝ) + 1) ∧ μ * (c - a) = b) (h6 : 6 < N)
    (i : Fin N) (k₁ k₂ : Fin 3)
    (hk₁ : dist ((D.tile i).pts k₁) ((D.tile i).pts (k₁+1)) = a)
    (hk₂ : dist ((D.tile i).pts k₂) ((D.tile i).pts (k₂+1)) = a) :
    k₁ = k₂ := by
  -- Compute distinctness BEFORE destructuring hm (which consumes it)
  have ha_ne_b : a ≠ b := (f1_b_ne_a D hirr hm hF1 hμ hpm h6).symm
  have ha_ne_c : a ≠ c := f1_a_ne_c D hirr hm hF1 hμ hpm h6
  obtain ⟨σ', hσ'⟩ := (D.tiles_congruent i).exists_perm
  obtain ⟨σ_m, hm0a, hm0s, hm1a, hm1s, hm2a, hm2s⟩ := hm
  -- (D.tile i).oppLen (kⱼ+2) = dist(pts(kⱼ), pts(kⱼ+1)) = a in Fin 3
  have hk1_fin : (k₁ : Fin 3) + 2 + 1 = k₁ := by fin_cases k₁ <;> decide
  have hk1_fin2 : (k₁ : Fin 3) + 2 + 2 = k₁ + 1 := by fin_cases k₁ <;> decide
  have hk2_fin : (k₂ : Fin 3) + 2 + 1 = k₂ := by fin_cases k₂ <;> decide
  have hk2_fin2 : (k₂ : Fin 3) + 2 + 2 = k₂ + 1 := by fin_cases k₂ <;> decide
  have hoppk₁ : (D.tile i).oppLen (k₁ + 2) = a := by
    simp only [Tri.oppLen, hk1_fin, hk1_fin2]; exact hk₁
  have hoppk₂ : (D.tile i).oppLen (k₂ + 2) = a := by
    simp only [Tri.oppLen, hk2_fin, hk2_fin2]; exact hk₂
  have hmodel_k₁ : D.model.oppLen (σ' (k₁ + 2)) = a := by
    rw [← (hσ' (k₁ + 2)).2]; exact hoppk₁
  have hmodel_k₂ : D.model.oppLen (σ' (k₂ + 2)) = a := by
    rw [← (hσ' (k₂ + 2)).2]; exact hoppk₂
  have hσ_k₁ : σ' (k₁ + 2) = σ_m 0 := by
    obtain ⟨j, hj⟩ := σ_m.surjective (σ' (k₁ + 2))
    fin_cases j
    · exact hj.symm
    · exfalso; rw [← hj] at hmodel_k₁; simp only [] at hmodel_k₁
      exact absurd (hm1s.symm.trans hmodel_k₁) ha_ne_b.symm
    · exfalso; rw [← hj] at hmodel_k₁; simp only [] at hmodel_k₁
      exact absurd (hm2s.symm.trans hmodel_k₁) ha_ne_c.symm
  have hσ_k₂ : σ' (k₂ + 2) = σ_m 0 := by
    obtain ⟨j, hj⟩ := σ_m.surjective (σ' (k₂ + 2))
    fin_cases j
    · exact hj.symm
    · exfalso; rw [← hj] at hmodel_k₂; simp only [] at hmodel_k₂
      exact absurd (hm1s.symm.trans hmodel_k₂) ha_ne_b.symm
    · exfalso; rw [← hj] at hmodel_k₂; simp only [] at hmodel_k₂
      exact absurd (hm2s.symm.trans hmodel_k₂) ha_ne_c.symm
  have := σ'.injective (hσ_k₁.trans hσ_k₂.symm)
  fin_cases k₁ <;> fin_cases k₂ <;> simp_all (config := { decide := true })

set_option maxHeartbeats 800000 in
theorem f1_Tprime_K2_proved {N : ℕ} (D : CongruentDissection N) {α a b c μ : ℝ}
    (hirr : IrrPi α) (hm : D.model.TwoPiThreeData α a b c)
    (hF1 : D.target.F1Data α a b c μ) (hμ : 0 < μ) (hpm : c * ((N : ℝ) - 1) = a * ((N : ℝ) + 1) ∧ μ * (c - a) = b) (h6 : 6 < N)
    (σ : Equiv.Perm (Fin 3))
    (hside_eq : dist (D.target.pts (σ 2 + 1)) (D.target.pts (σ 2 + 2)) = μ * (a + b))
    (hQzero : ∀ P Q R : ℕ,
        (P : ℝ) * a + (Q : ℝ) * b + (R : ℝ) * c =
          dist (D.target.pts (σ 2 + 1)) (D.target.pts (σ 2 + 2)) → Q = 0)
    (hword : ∀ P R : ℕ,
        (P : ℝ) * a + (R : ℝ) * c =
          dist (D.target.pts (σ 2 + 1)) (D.target.pts (σ 2 + 2)) →
        P = 1 ∧ R = 1) :
    ∃ (i' : Fin N) (X : Plane),
      (D.tile i').localAngle X = 2 * Real.pi / 3 ∧
      ∃ j₂ : Fin 3, j₂ ≠ σ 2 + 1 ∧
        X ∈ D.target.edge (σ 2 + 1) ∧
        X ∈ D.target.edge j₂ := by
  obtain ⟨-, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  have habc : ∀ (j : Fin N) (k : Fin 3),
      dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = a ∨
      dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = b ∨
      dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = c := by
    intro j k
    obtain ⟨m, hm_eq⟩ := D.eLen_mem ⟨j, k⟩
    have hdef : D.eLen ⟨j, k⟩ = dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) := rfl
    rw [← hdef, hm_eq]
    obtain ⟨σ_m, -, ha_op, -, hb_op, -, hc_op⟩ := hm
    obtain ⟨i, rfl⟩ := σ_m.surjective m
    fin_cases i <;> simp only []
    · exact Or.inl ha_op
    · exact Or.inr (Or.inl hb_op)
    · exact Or.inr (Or.inr hc_op)
  -- Part A: Extract T′
  obtain ⟨partV, hcovV, -, hsumV⟩ := D.toDissection.side_walk (σ 2 + 1)
  obtain ⟨P_V, Q_V, R_V, hPQRV, _⟩ := sum_three_values partV
    (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
    a b c (fun e _ => habc e.1 e.2)
  -- hsumV uses (σ 2+1)+1; show this equals σ 2+2 in Fin 3
  have hfin21 : (σ 2 + 1 : Fin 3) + 1 = σ 2 + 2 :=
    (show ∀ x : Fin 3, (x + 1 : Fin 3) + 1 = x + 2 from by decide) (σ 2)
  have hwordV : (P_V : ℝ) * a + (Q_V : ℝ) * b + (R_V : ℝ) * c =
      dist (D.target.pts (σ 2 + 1)) (D.target.pts (σ 2 + 2)) := by
    rw [← hfin21]; linarith [hPQRV, hsumV]
  have hQV0 : Q_V = 0 := hQzero P_V Q_V R_V hwordV
  have hPR_eq : (P_V : ℝ) * a + (R_V : ℝ) * c =
      dist (D.target.pts (σ 2 + 1)) (D.target.pts (σ 2 + 2)) := by
    have h : (Q_V : ℝ) = 0 := by exact_mod_cast hQV0
    nlinarith [hb0, h ▸ hwordV]
  obtain ⟨hPV1, -⟩ := hword P_V R_V hPR_eq
  -- hPV1 : P_V = 1. Need: the a-filter of partV is nonempty.
  -- sum_three_values sets P_V := (partV.filter (len = a)).card definitionally.
  -- From hPV1: P_V=1. If the a-filter of partV is empty, all elements have len∈{b,c}.
  -- Applying hQzero to the b-count forces b-count=0. Then c-count*c = a + R_V*c.
  -- Since a < c (from hpin, N≥2), this is impossible (cnt-R_V ≥ 1 → a ≥ c, contradiction).
  have hpin : c * ((N : ℝ) - 1) = a * ((N : ℝ) + 1) :=
    (hpm.1)
  have hac_lt : a < c := by
    have hNp1 : (0:ℝ) < (N:ℝ) + 1 := by positivity
    have hmul : c * ((N:ℝ) - 1) < c * ((N:ℝ) + 1) :=
      mul_lt_mul_of_pos_left (by linarith) hc0
    rw [hpin] at hmul
    exact lt_of_mul_lt_mul_right hmul hNp1.le
  have hfiltA_pos : 0 < (partV.filter fun e =>
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = a).card := by
    by_contra h_neg
    push_neg at h_neg
    have h_empty : (partV.filter fun e =>
        dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = a) = ∅ :=
      Finset.card_eq_zero.mp (by omega)
    have h_non_a : ∀ e ∈ partV,
        dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) ≠ a := by
      intro e he heq
      have hpos : 0 < (partV.filter fun e =>
          dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = a).card :=
        Finset.card_pos.mpr ⟨e, by simp only [Finset.mem_filter]; exact ⟨he, heq⟩⟩
      omega
    have h_bc : ∀ e ∈ partV,
        dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b ∨
        dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = c := by
      intro e he
      rcases habc e.1 e.2 with ha | hb | hc
      · exact absurd ha (h_non_a e he)
      · exact Or.inl hb
      · exact Or.inr hc
    -- sum_three_values on partV treating (b, c, c) to get P_n*b + (Q_n+R_n)*c = sum
    obtain ⟨P_n, Q_n, R_n, hsum_n, _⟩ := sum_three_values partV
        (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
        b c c (fun e he => by
          rcases h_bc e he with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h))
    -- hsum_n: P_n*b + Q_n*c + R_n*c = ∑ partV = (P_V*a + Q_V*b + R_V*c) [= a + R_V*c]
    -- Both sum_three_values applications equal ∑ partV
    have hsum_eq : (P_n : ℝ) * b + (Q_n : ℝ) * c + (R_n : ℝ) * c =
        (P_V : ℝ) * a + (Q_V : ℝ) * b + (R_V : ℝ) * c := by
      linarith [hsum_n, hPQRV]
    -- hQzero forces P_n = 0 (the b-coefficient)
    have hPn0 : P_n = 0 := by
      apply hQzero 0 P_n (Q_n + R_n)
      have hPV1' : (P_V:ℝ) = 1 := by exact_mod_cast hPV1
      have hQV0' : (Q_V:ℝ) = 0 := by exact_mod_cast hQV0
      have hbc_eq : (P_n:ℝ)*b + (Q_n:ℝ)*c + (R_n:ℝ)*c = dist (D.target.pts (σ 2 + 1))
          (D.target.pts (σ 2 + 2)) := by linarith [hsum_eq, hPR_eq]
      simp only [Nat.cast_zero, zero_mul, zero_add, Nat.cast_add, add_mul]; linarith
    -- c-count * c = a + R_V*c
    have hcnt_c : ((Q_n + R_n : ℕ) : ℝ) * c = a + (R_V : ℝ) * c := by
      have hPn0' : (P_n:ℝ) = 0 := by exact_mod_cast hPn0
      have hPV1' : (P_V:ℝ) = 1 := by exact_mod_cast hPV1
      have hQV0' : (Q_V:ℝ) = 0 := by exact_mod_cast hQV0
      have hQRc : (Q_n:ℝ)*c + (R_n:ℝ)*c = a + (R_V:ℝ)*c := by
        have h := hsum_eq
        rw [hPn0', zero_mul, zero_add, hPV1', one_mul, hQV0', zero_mul, add_zero] at h
        exact h
      calc ((Q_n + R_n : ℕ) : ℝ) * c
          = (Q_n : ℝ) * c + (R_n : ℝ) * c := by push_cast; ring
        _ = a + (R_V : ℝ) * c := hQRc
    -- Q_n + R_n > R_V as naturals (since a > 0)
    have hcnt_nat : R_V < Q_n + R_n := by
      have : (R_V:ℝ) < ((Q_n + R_n : ℕ) : ℝ) := by nlinarith [ha0, hc0]
      exact_mod_cast this
    -- (Q_n+R_n - R_V : ℝ) ≥ 1
    have hge1 : (1 : ℝ) ≤ ((Q_n + R_n : ℕ) : ℝ) - (R_V : ℝ) := by
      have h := Nat.succ_le_iff.mpr hcnt_nat
      have h' : (R_V : ℝ) + 1 ≤ ((Q_n + R_n : ℕ) : ℝ) := by exact_mod_cast h
      linarith
    -- a = (cnt - R_V)*c ≥ c, contradicting a < c
    nlinarith [mul_le_mul_of_nonneg_right hge1 hc0.le, hcnt_c, hac_lt]
  obtain ⟨⟨i', k_a'⟩, hmem_a'⟩ := Finset.card_pos.mp hfiltA_pos
  have hka_a : dist ((D.tile i').pts k_a') ((D.tile i').pts (k_a' + 1)) = a :=
    (Finset.mem_filter.mp hmem_a').2
  have hka_in_partV : (i', k_a') ∈ partV := (Finset.mem_filter.mp hmem_a').1
  -- Part B: γ-vertex X
  -- Save hm before destructuring (tile_a_edge_unique and f1_tile_b_unique need it)
  have hm_copy := hm
  obtain ⟨σ', hσ'⟩ := (D.tiles_congruent i').exists_perm
  obtain ⟨σ_m, hm0a, hm0s, hm1a, hm1s, hm2a, hm2s⟩ := hm
  let k_γ := σ'.symm (σ_m 2)
  have hangle_γ : (D.tile i').angleAt k_γ = 2 * Real.pi / 3 := by
    have h := (hσ' k_γ).1
    rw [show σ' k_γ = σ_m 2 from by simp [k_γ, Equiv.apply_symm_apply]] at h
    rw [h, hm2a]
  let X := (D.tile i').pts k_γ
  have hlocalAngle : (D.tile i').localAngle X = 2 * Real.pi / 3 := by
    simp only [X, Tri.localAngle_vertex]; exact hangle_γ
  -- Part C: X ∈ target.edge(σ(2)+1)
  let j_a := σ'.symm (σ_m 0)
  have hopp_a : (D.tile i').oppLen j_a = a := by
    have h := (hσ' j_a).2
    rw [show σ' j_a = σ_m 0 from by simp [j_a, Equiv.apply_symm_apply]] at h
    rw [h, hm0s]
  have hka''_a : dist ((D.tile i').pts (j_a+1)) ((D.tile i').pts (j_a+2)) = a := by
    simp only [Tri.oppLen] at hopp_a; exact hopp_a
  have hka_eq : k_a' = j_a + 1 :=
    tile_a_edge_unique D hirr hm_copy hF1 hμ hpm h6 i' k_a' (j_a+1) hka_a
      (by rw [show (j_a + 1 : Fin 3) + 1 = j_a + 2 from
              (show ∀ x : Fin 3, (x + 1) + 1 = x + 2 from by decide) j_a]; exact hka''_a)
  have hjγ_ne_ja : k_γ ≠ j_a := by
    simp only [k_γ, j_a]; intro h
    exact absurd (σ_m.injective (σ'.symm.injective h)) (by decide)
  have hkγ_endpoint_a : k_γ = k_a' ∨ k_γ = k_a' + 1 := by
    rcases fin3_ne_complement k_γ j_a hjγ_ne_ja with h | h
    · left; rw [hka_eq, ← h]
    · right; rw [hka_eq, h]
      exact (show ∀ x : Fin 3, x + 2 = (x + 1) + 1 from by decide) j_a
  have hX_in_edge_a : X ∈ (D.tile i').edge k_a' := by
    rcases hkγ_endpoint_a with h | h
    · have hXeq : X = (D.tile i').pts k_a' := by simp [X, h]
      rw [hXeq]; exact left_mem_segment ℝ _ _
    · have hXeq : X = (D.tile i').pts (k_a' + 1) := by simp [X, h]
      rw [hXeq]; exact right_mem_segment ℝ _ _
  have hX_in_targetV : X ∈ D.target.edge (σ 2 + 1) := by
    apply (hcovV ▸ Set.subset_biUnion_of_mem hka_in_partV)
    exact hX_in_edge_a
  -- Part D: T′'s b-edge on σ(2) or σ(2)+2
  let j_b := σ'.symm (σ_m 1)
  have hopp_b : (D.tile i').oppLen j_b = b := by
    have h := (hσ' j_b).2
    rw [show σ' j_b = σ_m 1 from by simp [j_b, Equiv.apply_symm_apply]] at h
    rw [h, hm1s]
  have hkb''_b : dist ((D.tile i').pts (j_b+1)) ((D.tile i').pts (j_b+2)) = b := by
    simp only [Tri.oppLen] at hopp_b; exact hopp_b
  obtain ⟨k_bU, hkbU_b, hkbU_uniq⟩ := f1_tile_b_unique D hirr hm_copy hF1 hμ hpm h6 i'
  have hkb_eq : j_b + 1 = k_bU :=
    hkbU_uniq (j_b+1) (by
      have hfin : (j_b + 1 : Fin 3) + 1 = j_b + 2 :=
        (show ∀ x : Fin 3, (x + 1) + 1 = x + 2 from by decide) j_b
      simp only [hfin]; exact hkb''_b)
  obtain ⟨partA, hcovA, -, hsumA⟩ := D.toDissection.side_walk (σ 2)
  obtain ⟨partB, hcovB, -, hsumB⟩ := D.toDissection.side_walk (σ 2 + 2)
  -- Part D: T′'s b-edge on σ(2) or σ(2)+2.
  -- Proof: total boundary b-edges = N (f1_total_b_count + hQV0=0);
  -- injection {boundary b-edges} → Fin N; tile i' is in the image.
  have hbedge_located : (i', k_bU) ∈ partA ∨ (i', k_bU) ∈ partB := by
    -- Q-uniqueness via rat_coeff_unique: b/c irrational → b-coefficient in Pa+Qb+Rc=L unique
    have hbci := f1_b_over_c_irrational D hirr hm_copy hF1 hμ hpm h6
    have hbc_notrat : NotRat (b / c) := by
      intro ⟨q, hq⟩; apply hbci
      exact ⟨q, by rw [div_eq_iff hc0.ne'] at hq; linarith⟩
    have hN1pos : (N : ℝ) + 1 ≠ 0 := by positivity
    have ha_val : a = c * ((N : ℝ) - 1) / ((N : ℝ) + 1) := by
      field_simp [hN1pos]; linarith [hpin]
    have hQ_uniq : ∀ (Pq1 Qq1 Rq1 Pq2 Qq2 Rq2 : ℕ) (L : ℝ),
        (Pq1 : ℝ) * a + Qq1 * b + Rq1 * c = L →
        (Pq2 : ℝ) * a + Qq2 * b + Rq2 * c = L → Qq1 = Qq2 := by
      intro Pq1 Qq1 Rq1 Pq2 Qq2 Rq2 L h1 h2
      have hdiff : ((Qq1 : ℝ) - Qq2) * b +
          ((Rq1 : ℝ) - Rq2) * c =
          ((Pq2 : ℝ) - Pq1) * c * ((N : ℝ) - 1) / ((N : ℝ) + 1) := by
        rw [ha_val] at h1 h2; field_simp [hN1pos] at h1 h2 ⊢; linarith
      have hdiv : ((Qq1 : ℝ) - Qq2) * (b / c) =
          ((Pq2 : ℝ) - Pq1) * ((N : ℝ) - 1) / ((N : ℝ) + 1) - ((Rq1 : ℝ) - Rq2) := by
        field_simp [hc0.ne', hN1pos] at hdiff ⊢; linarith
      set rQ : ℚ := (((Qq1 : ℤ) - Qq2 : ℤ) : ℚ)
      set c0K : ℚ := -(((Pq2 : ℤ) - Pq1 : ℤ) : ℚ) * (((N : ℤ) - 1 : ℤ) : ℚ) /
          (((N : ℤ) + 1 : ℤ) : ℚ) + (((Rq1 : ℤ) - Rq2 : ℤ) : ℚ)
      have hrQ_cast : (rQ : ℝ) = ((Qq1 : ℝ) - Qq2) := by
        simp only [rQ]; push_cast; ring
      have hN1ne : ((N : ℝ) + 1) ≠ 0 := by linarith
      have hc0K_cast : (c0K : ℝ) = -((Pq2 : ℝ) - Pq1) * ((N : ℝ) - 1) /
          ((N : ℝ) + 1) + ((Rq1 : ℝ) - Rq2) := by
        simp only [c0K]; push_cast; field_simp [hN1ne]
      have heq_rat : (rQ : ℝ) * (b / c) + (c0K : ℝ) = 0 := by
        rw [hrQ_cast, hc0K_cast]; linear_combination hdiv
      have hrQ_zero := (rat_coeff_unique hbc_notrat rQ c0K heq_rat).1
      have : (Qq1 : ℤ) - Qq2 = 0 := by
        have := hrQ_zero
        simp only [rQ] at this
        exact_mod_cast this
      omega
    -- b-counts for sides A and B via sum_three_values on the same parts
    obtain ⟨PA, QA, RA, hA_eq, _⟩ := sum_three_values partA
        (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) a b c
        (fun e _ => habc e.1 e.2)
    obtain ⟨PB, QB, RB, hB_eq, _⟩ := sum_three_values partB
        (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) a b c
        (fun e _ => habc e.1 e.2)
    have hfin22 : (σ 2 + 2 : Fin 3) + 1 = σ 2 + 3 :=
      (show ∀ x : Fin 3, (x + 2 : Fin 3) + 1 = x + 3 from by decide) (σ 2)
    have hA_side : (PA : ℝ) * a + QA * b + RA * c =
        dist (D.target.pts (σ 2)) (D.target.pts (σ 2 + 1)) := by linarith [hA_eq, hsumA]
    have hB_side : (PB : ℝ) * a + QB * b + RB * c =
        dist (D.target.pts (σ 2 + 2)) (D.target.pts (σ 2 + 3)) := by
      linarith [hB_eq, hfin22 ▸ hsumB]
    -- QA + QB = N via f1_total_b_count + fin_cases on σ 2
    have hQAB : QA + QB = N := by
      obtain ⟨P0, Q0, R0, P1, Q1, R1, P2, Q2, R2, hs0, hs1, hs2, hQtot⟩ :=
        f1_total_b_count D hirr hm_copy hF1 hμ hpm h6
      -- hs2 already has pts (0:Fin 3)
      have hs2' : (P2 : ℝ) * a + Q2 * b + R2 * c =
          dist (D.target.pts 2) (D.target.pts 0) := hs2
      -- split on the value of σ 2 ∈ {0,1,2}
      have h_σ2_cases : σ 2 = 0 ∨ σ 2 = 1 ∨ σ 2 = 2 := by
        have hv : (σ 2).val = 0 ∨ (σ 2).val = 1 ∨ (σ 2).val = 2 := by
          have := (σ 2).isLt; omega
        rcases hv with h | h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Or.inl (Fin.ext h))
        · exact Or.inr (Or.inr (Fin.ext h))
      rcases h_σ2_cases with h_σ2 | h_σ2 | h_σ2
      · -- σ 2 = 0: A=side 0, V=side 1, B=side 2
        have hA0 : (PA : ℝ) * a + QA * b + RA * c =
            dist (D.target.pts 0) (D.target.pts 1) := by
          simp only [h_σ2, show (0 : Fin 3) + 1 = 1 from by decide] at hA_side; exact hA_side
        have hB2 : (PB : ℝ) * a + QB * b + RB * c =
            dist (D.target.pts 2) (D.target.pts 0) := by
          simp only [h_σ2, show (0 : Fin 3) + 2 = 2 from by decide,
                     show (0 : Fin 3) + 2 + 1 = 0 from by decide] at hB_side
          exact hB_side
        have hV1 : (P_V : ℝ) * a + Q_V * b + R_V * c =
            dist (D.target.pts 1) (D.target.pts 2) := by
          simp only [h_σ2, show (0 : Fin 3) + 1 = 1 from by decide,
                     show (0 : Fin 3) + 1 + 1 = 2 from by decide] at hwordV
          exact hwordV
        have hQA0 : QA = Q0 := hQ_uniq PA QA RA P0 Q0 R0 _ hA0 hs0
        have hQB2 : QB = Q2 := hQ_uniq PB QB RB P2 Q2 R2 _ hB2 hs2'
        have hQV1 : Q_V = Q1 := hQ_uniq P_V Q_V R_V P1 Q1 R1 _ hV1 hs1
        omega
      · -- σ 2 = 1: A=side 1, V=side 2, B=side 0
        have hA1 : (PA : ℝ) * a + QA * b + RA * c =
            dist (D.target.pts 1) (D.target.pts 2) := by
          simp only [h_σ2, show (1 : Fin 3) + 1 = 2 from by decide] at hA_side; exact hA_side
        have hB0 : (PB : ℝ) * a + QB * b + RB * c =
            dist (D.target.pts 0) (D.target.pts 1) := by
          simp only [h_σ2, show (1 : Fin 3) + 2 = 0 from by decide,
                     show (1 : Fin 3) + 2 + 1 = 1 from by decide] at hB_side
          exact hB_side
        have hV2 : (P_V : ℝ) * a + Q_V * b + R_V * c =
            dist (D.target.pts 2) (D.target.pts 0) := by
          simp only [h_σ2, show (1 : Fin 3) + 1 = 2 from by decide,
                     show (1 : Fin 3) + 1 + 1 = 0 from by decide] at hwordV
          exact hwordV
        have hQA1 : QA = Q1 := hQ_uniq PA QA RA P1 Q1 R1 _ hA1 hs1
        have hQB0 : QB = Q0 := hQ_uniq PB QB RB P0 Q0 R0 _ hB0 hs0
        have hQV2 : Q_V = Q2 := hQ_uniq P_V Q_V R_V P2 Q2 R2 _ hV2 hs2'
        omega
      · -- σ 2 = 2: A=side 2, V=side 0, B=side 1
        have hA2 : (PA : ℝ) * a + QA * b + RA * c =
            dist (D.target.pts 2) (D.target.pts 0) := by
          simp only [h_σ2, show (2 : Fin 3) + 1 = 0 from by decide] at hA_side; exact hA_side
        have hB1 : (PB : ℝ) * a + QB * b + RB * c =
            dist (D.target.pts 1) (D.target.pts 2) := by
          simp only [h_σ2, show (2 : Fin 3) + 2 = 1 from by decide,
                     show (2 : Fin 3) + 2 + 1 = 2 from by decide] at hB_side
          exact hB_side
        have hV0 : (P_V : ℝ) * a + Q_V * b + R_V * c =
            dist (D.target.pts 0) (D.target.pts 1) := by
          simp only [h_σ2, show (2 : Fin 3) + 1 = 0 from by decide,
                     show (2 : Fin 3) + 1 + 1 = 1 from by decide] at hwordV
          exact hwordV
        have hQA2 : QA = Q2 := hQ_uniq PA QA RA P2 Q2 R2 _ hA2 hs2'
        have hQB1 : QB = Q1 := hQ_uniq PB QB RB P1 Q1 R1 _ hB1 hs1
        have hQV0' : Q_V = Q0 := hQ_uniq P_V Q_V R_V P0 Q0 R0 _ hV0 hs0
        omega
    -- bA and bB: b-filtered boundary subsets
    -- QA = bA.card and QB = bB.card definitionally (sum_three_values witnesses)
    -- b ≠ a: from hbci and hpin
    have hba : b ≠ a := f1_b_ne_a D hirr hm_copy hF1 hμ hpm h6
    -- QA = (partA.filter (dist=b)).card (b≠a → ¬a∧b filter = b filter)
    have hbA_eq : (partA.filter fun e =>
        dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b).card = QA := by
      apply hQ_uniq
          ((partA.filter fun e =>
            dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = a).card)
          ((partA.filter fun e =>
            dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b).card)
          ((partA.filter fun e =>
            ¬ dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = a ∧
            ¬ dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b).card)
          PA QA RA (dist (D.target.pts (σ 2)) (D.target.pts (σ 2 + 1)))
      · linarith [sum_three_filter partA
            (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) a b c
            hba (fun e _ => habc e.1 e.2), hsumA]
      · exact hA_side
    have hbB_eq : (partB.filter fun e =>
        dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b).card = QB := by
      have hsumB' : ∑ e ∈ partB, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) =
          dist (D.target.pts (σ 2 + 2)) (D.target.pts (σ 2 + 3)) := hfin22 ▸ hsumB
      apply hQ_uniq
          ((partB.filter fun e =>
            dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = a).card)
          ((partB.filter fun e =>
            dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b).card)
          ((partB.filter fun e =>
            ¬ dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = a ∧
            ¬ dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b).card)
          PB QB RB (dist (D.target.pts (σ 2 + 2)) (D.target.pts (σ 2 + 3)))
      · linarith [sum_three_filter partB
            (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) a b c
            hba (fun e _ => habc e.1 e.2), hsumB']
      · exact hB_side
    -- Now use counting + injection
    -- Define the combined b-boundary (on sides A and B)
    let bAB := (partA ∪ partB).filter fun e =>
        dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b
    -- bAB.card = QA + QB = N (using hbA_eq + hbB_eq + disjointness of partA ∩ partB)
    -- Each tile has ≤1 element in bAB (f1_tile_b_unique), so bAB.image Prod.fst has N elements
    -- → tile i' appears in bAB.image Prod.fst → (i', k_bU) ∈ bAB
    -- Part D5: injection bAB → Fin N (via Prod.fst, unique b-edge per tile)
    have hinj : ∀ e1 ∈ bAB, ∀ e2 ∈ bAB, e1.1 = e2.1 → e1 = e2 := by
      intro ⟨i1, k1⟩ he1 ⟨i2, k2⟩ he2 heq
      simp only at heq; subst heq
      simp only [Finset.mem_filter, Finset.mem_union, bAB] at he1 he2
      have hb1 : dist ((D.tile i1).pts k1) ((D.tile i1).pts (k1 + 1)) = b := he1.2
      have hb2 : dist ((D.tile i1).pts k2) ((D.tile i1).pts (k2 + 1)) = b := he2.2
      obtain ⟨_, _, huniq⟩ := f1_tile_b_unique D hirr hm_copy hF1 hμ hpm h6 i1
      congr 1; exact (huniq k1 hb1).trans (huniq k2 hb2).symm
    -- Part D6: |bAB| = N
    have hbAB_card : bAB.card = N := by
      -- bAB ⊆ partA ∪ partB, and partA ∩ partB are disjoint (different boundary sides)
      -- so bAB.card = bA.card + bB.card = QA + QB = N
      have hdisj : Disjoint partA partB := by
        rw [Finset.disjoint_left]
        intro e heA heB
        -- Each edge in partA is contained in segment_A (from hcovA union property)
        have hsubA : (D.tile e.1).edge e.2 ⊆
            segment ℝ (D.target.pts (σ 2)) (D.target.pts (σ 2 + 1)) := by
          intro y hy; rw [← hcovA]; exact Set.mem_iUnion₂.mpr ⟨e, heA, hy⟩
        -- Each edge in partB is contained in segment_B (from hcovB union property)
        have hsubB : (D.tile e.1).edge e.2 ⊆
            segment ℝ (D.target.pts (σ 2 + 2)) (D.target.pts ((σ 2 + 2) + 1)) := by
          intro y hy; rw [← hcovB]; exact Set.mem_iUnion₂.mpr ⟨e, heB, hy⟩
        -- (σ 2 + 2 : Fin 3) + 1 = σ 2 in Fin 3 (wraps around)
        have hσ_add3 : (σ 2 + 2 : Fin 3) + 1 = σ 2 :=
          (show ∀ x : Fin 3, (x + 2 : Fin 3) + 1 = x from by decide) (σ 2)
        -- Both endpoints of edge e lie in segment_A and segment_B
        have hpt0_in_A : (D.tile e.1).pts e.2 ∈ D.target.edge (σ 2) :=
          hsubA (left_mem_segment ℝ _ _)
        have hpt0_in_B : (D.tile e.1).pts e.2 ∈ D.target.edge (σ 2 + 2) :=
          hsubB (left_mem_segment ℝ _ _)
        have hpt1_in_A : (D.tile e.1).pts (e.2 + 1) ∈ D.target.edge (σ 2) :=
          hsubA (right_mem_segment ℝ _ _)
        have hpt1_in_B : (D.tile e.1).pts (e.2 + 1) ∈ D.target.edge (σ 2 + 2) :=
          hsubB (right_mem_segment ℝ _ _)
        -- tri_adjacent_edges_inter_vertex T k hek hek1 : X = T.pts (k+1)
        -- With k = σ2+2, result is X = D.target.pts (σ2+2+1).
        -- Need: pts e.2 ∈ edge(σ2+2) AND pts e.2 ∈ edge((σ2+2)+1).
        -- hpt0_in_B : pts e.2 ∈ edge(σ2+2). edge((σ2+2)+1) = edge(σ2) by hσ_add3.
        have hedge_eq : D.target.edge ((σ 2 + 2 : Fin 3) + 1) = D.target.edge (σ 2) := by
          congr 1
        have hpt0_corner : (D.tile e.1).pts e.2 = D.target.pts ((σ 2 + 2 : Fin 3) + 1) := by
          have h0A' : (D.tile e.1).pts e.2 ∈ D.target.edge ((σ 2 + 2 : Fin 3) + 1) := by
            rw [hedge_eq]; exact hpt0_in_A
          exact tri_adjacent_edges_inter_vertex D.target (σ 2 + 2) hpt0_in_B h0A'
        have hpt1_corner : (D.tile e.1).pts (e.2 + 1) = D.target.pts ((σ 2 + 2 : Fin 3) + 1) := by
          have h1A' : (D.tile e.1).pts (e.2 + 1) ∈ D.target.edge ((σ 2 + 2 : Fin 3) + 1) := by
            rw [hedge_eq]; exact hpt1_in_A
          exact tri_adjacent_edges_inter_vertex D.target (σ 2 + 2) hpt1_in_B h1A'
        -- Both endpoints equal → edge has zero length, contradicts positivity
        have hpts_eq : (D.tile e.1).pts e.2 = (D.tile e.1).pts (e.2 + 1) :=
          hpt0_corner.trans hpt1_corner.symm
        have hlen_pos : 0 < dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) := by
          rcases habc e.1 e.2 with h | h | h <;> linarith [ha0, hb0, hc0, h.symm.le]
        exact absurd (hpts_eq ▸ dist_self ((D.tile e.1).pts e.2)) (ne_of_gt hlen_pos)
      have hcard_split : bAB.card = (partA.filter fun e =>
            dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b).card +
          (partB.filter fun e =>
            dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b).card := by
        rw [show bAB = (partA.filter fun e =>
              dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b) ∪
            (partB.filter fun e =>
              dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b) from
          Finset.filter_union _ _ _]
        apply Finset.card_union_of_disjoint
        apply Finset.disjoint_filter_filter
        exact hdisj
      omega
    -- Part D7: bAB.image Prod.fst = Finset.univ
    have himg_full : bAB.image Prod.fst = Finset.univ := by
      apply Finset.eq_univ_of_card
      have hinj_on : Set.InjOn Prod.fst (bAB : Set (Fin N × Fin 3)) :=
        fun e1 he1 e2 he2 h => hinj e1 (Finset.mem_coe.mp he1) e2 (Finset.mem_coe.mp he2) h
      rw [Finset.card_image_of_injOn hinj_on, hbAB_card]
      simp only [Fintype.card_fin]
    -- Part D8: tile i' is covered → (i', k_bU) ∈ bAB
    have hi'_in_img : i' ∈ bAB.image Prod.fst := by
      rw [himg_full]; exact Finset.mem_univ i'
    obtain ⟨⟨itile, ktile⟩, hmem, hitile_eq⟩ := Finset.mem_image.mp hi'_in_img
    have hitile_eq' : itile = i' := hitile_eq
    have hktile_b : dist ((D.tile itile).pts ktile) ((D.tile itile).pts (ktile + 1)) = b :=
      (Finset.mem_filter.mp hmem).2
    have hk''_eq : ktile = k_bU := by
      obtain ⟨_, _, huniq'⟩ := f1_tile_b_unique D hirr hm_copy hF1 hμ hpm h6 itile
      exact (huniq' ktile hktile_b).trans
        (huniq' k_bU (hitile_eq' ▸ hkbU_b)).symm
    rw [hk''_eq] at hmem
    rw [hitile_eq'] at hmem
    rcases Finset.mem_union.mp (Finset.mem_filter.mp hmem).1 with h | h
    · exact Or.inl h
    · exact Or.inr h
  -- Part E: X ∈ target.edge(j₂)
  have hjγ_ne_jb : k_γ ≠ j_b := by
    simp only [k_γ, j_b]; intro h
    exact absurd (σ_m.injective (σ'.symm.injective h)) (by decide)
  have hkγ_endpoint_b : k_γ = k_bU ∨ k_γ = k_bU + 1 := by
    rw [← hkb_eq]
    rcases fin3_ne_complement k_γ j_b hjγ_ne_jb with h | h
    · left; exact h
    · right; rw [h]
      exact (show ∀ x : Fin 3, x + 2 = (x + 1) + 1 from by decide) j_b
  have hX_in_edge_b : X ∈ (D.tile i').edge k_bU := by
    rcases hkγ_endpoint_b with h | h
    · -- k_γ = k_bU, X = pts k_bU = left endpoint of edge k_bU
      have hXval : X = (D.tile i').pts k_bU := congrArg (D.tile i').pts h
      have hedge : (D.tile i').edge k_bU =
          segment ℝ ((D.tile i').pts k_bU) ((D.tile i').pts (k_bU + 1)) := rfl
      exact hXval ▸ hedge.symm ▸ left_mem_segment ℝ _ _
    · -- k_γ = k_bU + 1, X = pts(k_bU+1) = right endpoint of edge k_bU
      have hXval : X = (D.tile i').pts (k_bU + 1) := congrArg (D.tile i').pts h
      have hedge : (D.tile i').edge k_bU =
          segment ℝ ((D.tile i').pts k_bU) ((D.tile i').pts (k_bU + 1)) := rfl
      exact hXval ▸ hedge.symm ▸ right_mem_segment ℝ _ _
  rcases hbedge_located with h | h
  · exact ⟨i', X, hlocalAngle, σ 2,
      (show ∀ x : Fin 3, x ≠ x + 1 from by decide) (σ 2),
      hX_in_targetV, (hcovA ▸ Set.subset_biUnion_of_mem h) hX_in_edge_b⟩
  · exact ⟨i', X, hlocalAngle, σ 2 + 2,
      (show ∀ x : Fin 3, x + 2 ≠ x + 1 from by decide) (σ 2),
      hX_in_targetV, (hcovB ▸ Set.subset_biUnion_of_mem h) hX_in_edge_b⟩

end Erdos634.Draft.F1TprimeExtractM
