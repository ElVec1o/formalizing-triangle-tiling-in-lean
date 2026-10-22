-- Draft/LaczFormalBZL7c7.lean -- Beeson-Zhang (arXiv 2604.01314v1) THEOREM 5.3 / Theorem 1.1, row (2 alpha, pi/3, 2 beta) of Table 5, formal.
--   `bz_c_rational_row` : alpha not in Q pi, a, b commensurable  ==>  c is a rational multiple of a   (target triangle with angles (2 alpha, pi/3, 2 beta) at rho 0, rho 1, rho 2).
--   `bz_thm53`          : a CongruentDissection (any N, reflections allowed, not edge-to-edge) of such a triangle by the tile (alpha, pi/3 - alpha, 2 pi/3), alpha not in Q pi, has pairwise commensurable
--                          sides: Comm a b /\ Comm a c.
-- Route (differs from the printed one): Lemma 3.5/3.6 (`bz_ab_comm_row`, graph Gamma_a counting with polygon corners 2 alpha, 2 beta) gives a/b rational; the flux invariants of f_alpha, f_beta
-- (`bz_phi_gen`, interior c-edges cancelled by a Q-linear functional) and the strict triangle inequality give c rational.  Neither Lemma 3.4, Theorem 3.7 (all boundary c-edges) nor sawtooth tiles are used.
-- NOTE, UNAUDITED.  Credit: Beeson-Zhang (arXiv 2604.01314v1, Lemmas 3.5, 3.6, Thm 5.3), Laczkovich (DCG 48 (2012), p. 351, 365: Phi), Beeson.
import Erdos634.Draft.LaczFormalBZL7c3
import Erdos634.Draft.LaczFormalBZL7c6

open scoped Classical
open Erdos634.Geometry Erdos634.Draft.LaczFormal.Thm21

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

theorem bz_c_rational_row (D : CongruentDissection N) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoPiThreeData α a b c)
    (hab : ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ (p : ℝ) * a = (q : ℝ) * b)
    (ρ : Equiv.Perm (Fin 3)) (h0 : D.target.angleAt (ρ 0) = 2 * α) (h1 : D.target.angleAt (ρ 1) = Real.pi / 3)
    (h2 : D.target.angleAt (ρ 2) = 2 * (Real.pi / 3 - α)) :
    ∃ r : ℚ, c = (r : ℝ) * a := by
  by_contra hc
  have e1 := bz_phi_gen D hα h hab hc (fAlpha α hα) (GridChar.rankn_sq _ _ _ _ _ _ _) (c + a - b)
    (fun T kg hT hkg => T.flux_cedge hα hT kg hkg)
  have e2 := bz_phi_gen D hα h hab hc (fBeta α hα) (GridChar.rankn_sq _ _ _ _ _ _ _) (c + b - a)
    (fun T kg hT hkg => T.flux_cedge_beta hα hT kg hkg)
  obtain ⟨s1, hs1, hsum1⟩ := target_sum D.target hα 0 ρ h0 h1 h2
  obtain ⟨s2, hs2, hsum2⟩ := target_sum D.target hα 1 ρ h0 h1 h2
  set n : Fin 3 → ℝ := fun j => ((((D.sideEdges j).filter (fun e => D.eLen e = c)).card : ℕ) : ℝ) with hn
  set f : Fin 3 → ℝ := fun j => dist (D.target.pts j) (D.target.pts (j + 1)) with hf
  have hfl1 : D.target.flux (fAlpha α hα).weight = ∑ j : Fin 3, f j * (fAlpha α hα).weight (D.target.leftUnit j) := by
    unfold Tri.flux; simp only [smul_eq_mul, hf]
  have hfl2 : D.target.flux (fBeta α hα).weight = ∑ j : Fin 3, f j * (fBeta α hα).weight (D.target.leftUnit j) := by
    unfold Tri.flux; simp only [smul_eq_mul, hf]
  have s1' : ∑ j : Fin 3, n j * (fAlpha α hα).weight (D.target.leftUnit j) = s1 * (n (ρ 1 + 1) - n (ρ 0 + 1) - n (ρ 2 + 1)) := hsum1 n
  have s1f : ∑ j : Fin 3, f j * (fAlpha α hα).weight (D.target.leftUnit j) = s1 * (f (ρ 1 + 1) - f (ρ 0 + 1) - f (ρ 2 + 1)) := hsum1 f
  have s2' : ∑ j : Fin 3, n j * (fBeta α hα).weight (D.target.leftUnit j) = s2 * (n (ρ 1 + 1) - n (ρ 0 + 1) - n (ρ 2 + 1)) := hsum2 n
  have s2f : ∑ j : Fin 3, f j * (fBeta α hα).weight (D.target.leftUnit j) = s2 * (f (ρ 1 + 1) - f (ρ 0 + 1) - f (ρ 2 + 1)) := hsum2 f
  have E1 : (c + a - b) * (s1 * (n (ρ 1 + 1) - n (ρ 0 + 1) - n (ρ 2 + 1))) = s1 * (f (ρ 1 + 1) - f (ρ 0 + 1) - f (ρ 2 + 1)) := by
    rw [← s1', ← s1f, ← hfl1]; exact e1
  have E2 : (c + b - a) * (s2 * (n (ρ 1 + 1) - n (ρ 0 + 1) - n (ρ 2 + 1))) = s2 * (f (ρ 1 + 1) - f (ρ 0 + 1) - f (ρ 2 + 1)) := by
    rw [← s2', ← s2f, ← hfl2]; exact e2
  set M := n (ρ 1 + 1) - n (ρ 0 + 1) - n (ρ 2 + 1) with hM
  set Q := f (ρ 1 + 1) - f (ρ 0 + 1) - f (ρ 2 + 1) with hQ
  have E1' : (c + a - b) * M = Q := by
    apply mul_left_cancel₀ hs1; linear_combination E1
  have E2' : (c + b - a) * M = Q := by
    apply mul_left_cancel₀ hs2; linear_combination E2
  have hab0 : (a - b) * M = 0 := by linarith
  have hM0 : M = 0 := by
    rcases mul_eq_zero.mp hab0 with h3 | h3
    · exact absurd (by linarith) (h.a_ne_b hα)
    · exact h3
  have hQ0 : Q = 0 := by rw [← E1', hM0, mul_zero]
  -- Q = oppLen (rho 1) - oppLen (rho 0) - oppLen (rho 2) < 0
  have hk : ∀ k : Fin 3, f (k + 1) = D.target.oppLen k := by
    intro k
    simp only [hf, Tri.oppLen]
    rw [show k + 1 + 1 = k + 2 from by revert k; decide]
  have hlt := D.target.oppLen_lt_add_perm ρ
  have : Q = D.target.oppLen (ρ 1) - D.target.oppLen (ρ 0) - D.target.oppLen (ρ 2) := by
    rw [hQ, hk, hk, hk]
  linarith

/-- **Beeson-Zhang Theorem 5.3 (Theorem 1.1, row `(2α, 2β, π/3)`).** A congruent dissection (any `N`, reflections allowed, not edge-to-edge) of a triangle whose angles are `2α`, `π/3`, `2β`
(`β = π/3 - α`) at the vertices `ρ 0, ρ 1, ρ 2` by the tile `(α, β, 2π/3)` with `α ∉ ℚπ` has the sides `a, b, c` of the tile pairwise commensurable. -/
theorem bz_thm53 (D : CongruentDissection N) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoPiThreeData α a b c)
    (ρ : Equiv.Perm (Fin 3)) (h0 : D.target.angleAt (ρ 0) = 2 * α) (h1 : D.target.angleAt (ρ 1) = Real.pi / 3)
    (h2 : D.target.angleAt (ρ 2) = 2 * (Real.pi / 3 - α)) :
    Comm a b ∧ Comm a c := by
  have hT : ∀ j, D.target.angleAt j = Real.pi / 3 ∨ D.target.angleAt j = 2 * α ∨ D.target.angleAt j = 2 * (Real.pi / 3 - α) := by
    intro j
    obtain ⟨k, rfl⟩ := ρ.surjective j
    have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
    rcases hk with rfl | rfl | rfl
    · exact Or.inr (Or.inl h0)
    · exact Or.inl h1
    · exact Or.inr (Or.inr h2)
  have hab := bz_ab_comm_row D hα h hT
  refine ⟨hab, ?_⟩
  obtain ⟨r, hr⟩ := bz_c_rational_row D hα h hab ρ h0 h1 h2
  have ha : 0 < a := by
    obtain ⟨σ, -, o0, -⟩ := h
    rw [← o0]; exact D.model.oppLen_pos' _
  have hc : 0 < c := by
    obtain ⟨σ, -, -, -, -, -, o2⟩ := h
    rw [← o2]; exact D.model.oppLen_pos' _
  have hrpos : (0 : ℚ) < r := by
    by_contra hneg
    push Not at hneg
    have : (r : ℝ) ≤ 0 := by exact_mod_cast hneg
    nlinarith
  have hnum : 0 < r.num := Rat.num_pos.mpr hrpos
  refine ⟨r.num.toNat, r.den, ?_, r.den_pos, ?_⟩
  · omega
  · have h1' : ((r.num.toNat : ℕ) : ℝ) = (r.num : ℝ) := by
      have : ((r.num.toNat : ℕ) : ℤ) = r.num := Int.toNat_of_nonneg hnum.le
      exact_mod_cast this
    have h2' : (r : ℝ) * (r.den : ℝ) = (r.num : ℝ) := by
      have := Rat.mul_den_eq_num r
      exact_mod_cast this
    rw [h1', hr, ← h2']
    ring

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.bz_c_rational_row
#print axioms Erdos634.Draft.LaczFormal.RG.bz_thm53
