-- Draft/LaczFormalBZL7c6.lean -- Beeson-Zhang (arXiv 2604.01314v1) Thm 5.3 (row (2 alpha, pi/3, 2 beta)), the Phi-contradiction, formal and WITHOUT Theorem 3.7 / Lemma 3.4 / sawtooth tiles:
--   `target_sum`              : for a triangle whose angles are (2 alpha, pi/3, 2 beta) at the vertices rho 0, rho 1, rho 2, the weights of f_alpha / f_beta on its sides are s * (-1, +1, -1)
--                               on the sides opposite those vertices, s != 0 (BZ: sawtooth rotation factors (+1, +1, -1) up to a global sign);
--   `bz_c_rational_row`       : a, b commensurable and alpha not in Q pi  ==>  c is a rational multiple of a.
-- Proof: bz_phi_gen for f_alpha (K = c+a-b) and f_beta (K = c+b-a) gives K M = Q for both, M = n_B - n_A - n_C (numbers of c-edges on the sides), Q = q - p - r (side lengths);
-- so (a-b) M = 0, a != b, M = 0, Q = 0, contradicting the strict triangle inequality q < p + r.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), p. 351, 365: Phi), Beeson-Zhang (arXiv 2604.01314v1, Lemma 5.1, Thm 5.2, Thm 5.3).
import Erdos634.Draft.LaczFormalBZL7c5

open scoped Classical

namespace Erdos634.Geometry

variable {N : ℕ}

theorem zmod2_signs : (∀ b : ZMod 2, ((3 : ℤ) : ZMod 2) + b * ((-2 : ℤ) : ZMod 2) ≠ 0) ∧
    (∀ b : ZMod 2, ((2 : ℤ) : ZMod 2) + b * ((0 : ℤ) : ZMod 2) = 0) ∧
    (∀ b : ZMod 2, ((1 : ℤ) : ZMod 2) + b * ((2 : ℤ) : ZMod 2) ≠ 0) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem target_sum (T : Tri) {α : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (b' : ZMod 2) (ρ : Equiv.Perm (Fin 3))
    (h0 : T.angleAt (ρ 0) = 2 * α) (h1 : T.angleAt (ρ 1) = Real.pi / 3) (h2 : T.angleAt (ρ 2) = 2 * (Real.pi / 3 - α)) :
    ∃ s : ℝ, s ≠ 0 ∧ ∀ f : Fin 3 → ℝ,
      ∑ j : Fin 3, f j * (GridChar.rankn 3 (by norm_num) (by decide) α hα b' 0).weight (T.leftUnit j)
        = s * (f (ρ 1 + 1) - f (ρ 0 + 1) - f (ρ 2 + 1)) := by
  set G := GridChar.rankn 3 (by norm_num) (by decide) α hα b' 0 with hG
  have hsq := GridChar.rankn_sq 3 (by norm_num) (by decide) α hα b' 0
  have hmem : ∀ j, ((T.angleAt j : ℝ) : Real.Angle) ∈ G.L := by
    intro j
    obtain ⟨k, rfl⟩ := ρ.surjective j
    have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
    rcases hk with rfl | rfl | rfl
    · rw [h0, show 2 * α = ((0 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((2 : ℤ) : ℝ) * α by push_cast; ring]
      exact GridChar.rankn_mem _ _ _ _ _ _ _ _ _
    · rw [h1, show Real.pi / 3 = ((1 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((0 : ℤ) : ℝ) * α by push_cast; ring]
      exact GridChar.rankn_mem _ _ _ _ _ _ _ _ _
    · rw [h2, show 2 * (Real.pi / 3 - α) = ((2 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((-2 : ℤ) : ℝ) * α by push_cast; ring]
      exact GridChar.rankn_mem _ _ _ _ _ _ _ _ _
  obtain ⟨s, hw, -⟩ := T.weight_form G hsq hmem
  have hw1 : ∀ d : Dir, G.weight d * G.weight d = 1 := fun d => G.val_sq hsq _
  have hs : s ≠ 0 := by
    intro hs0
    have := hw1 (T.leftUnit 0)
    rw [hw 0, hs0] at this
    simp at this
  refine ⟨s, hs, fun f => ?_⟩
  obtain ⟨hA, hB, hC⟩ := zmod2_signs
  have c0 : G.chi ((Real.pi - 2 * α : ℝ) : Real.Angle) = -1 := by
    rw [show Real.pi - 2 * α = ((3 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((-2 : ℤ) : ℝ) * α by push_cast; ring, hG, GridChar.rankn_chi, if_neg (hA b')]
  have c1 : G.chi ((Real.pi - Real.pi / 3 : ℝ) : Real.Angle) = 1 := by
    rw [show Real.pi - Real.pi / 3 = ((2 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((0 : ℤ) : ℝ) * α by push_cast; ring, hG, GridChar.rankn_chi, if_pos (hB b')]
  have c2 : G.chi ((Real.pi - 2 * (Real.pi / 3 - α) : ℝ) : Real.Angle) = -1 := by
    rw [show Real.pi - 2 * (Real.pi / 3 - α) = ((1 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((2 : ℤ) : ℝ) * α by push_cast; ring, hG, GridChar.rankn_chi, if_neg (hC b')]
  have hk3 : ∀ k : Fin 3, k + 1 + 2 = k := by decide
  calc ∑ j : Fin 3, f j * G.weight (T.leftUnit j)
      = ∑ k : Fin 3, f (k + 1) * G.weight (T.leftUnit (k + 1)) :=
        (Equiv.sum_comp (Equiv.addRight (1 : Fin 3)) (fun j => f j * G.weight (T.leftUnit j))).symm
    _ = ∑ k : Fin 3, f (k + 1) * (s * G.chi ((Real.pi - T.angleAt k : ℝ) : Real.Angle)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hw (k + 1), hk3]
    _ = ∑ j : Fin 3, f (ρ j + 1) * (s * G.chi ((Real.pi - T.angleAt (ρ j) : ℝ) : Real.Angle)) :=
        (Equiv.sum_comp ρ (fun k => f (k + 1) * (s * G.chi ((Real.pi - T.angleAt k : ℝ) : Real.Angle)))).symm
    _ = s * (f (ρ 1 + 1) - f (ρ 0 + 1) - f (ρ 2 + 1)) := by
        rw [Fin.sum_univ_three, h0, h1, h2, c0, c1, c2]
        ring

end Erdos634.Geometry

#print axioms Erdos634.Geometry.target_sum
