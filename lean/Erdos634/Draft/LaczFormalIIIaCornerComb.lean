-- Draft/LaczFormalIIIaCornerComb.lean -- Laczkovich DCG 48 (2012) Case IIIa/IIIb, polygon targets M >= 4: the FINITE corner combinatorics of the
-- L71 counting repair (audit (private working notes, not included) gap 2).  Pure combinatorics, no geometry.
-- Corner data: `x k` = number of alpha-corners (= number of beta-corners) and `y k` = number of gamma-corners at the polygon vertex k, so (x,y) is (1,0) [angle pi/3],
-- (2,0) or (0,1) [angle 2 pi/3].  Statement: with P = sum x, R = sum y, g = number of cyclically adjacent pairs of single-gamma corners,
--   (a) M <= 6 and P + 2R = 3(M-2) (so 3 | R - P);   (b) R < P, or R < 3 g + P, or M = 4 and the corner pattern is (G, A, G, A).
-- NOTE, UNAUDITED.  Non-vacuity: witnesses at the end (trapezoid, parallelogram, hexagon).  Credit: Laczkovich (DCG 48 (2012), Sect. 4, 7), Beeson-Zhang, Beeson.
import Mathlib

open scoped Fin.NatCast
set_option maxRecDepth 100000

namespace Erdos634.Draft.LaczFormal.RG

/-- coded corner type: 0 = angle pi/3 (1 alpha, 1 beta), 1 = double (2,2,0), 2 = single gamma. -/
def n0c (c : Fin 3) : ℕ := match c with | 0 => 1 | 1 => 2 | 2 => 0
def n2c (c : Fin 3) : ℕ := match c with | 0 => 0 | 1 => 0 | 2 => 1

/-- the finite property for one coded arrangement -/
def CornerGood {M : ℕ} [NeZero M] (t : Fin M → Fin 3) : Prop :=
  ∑ k, n2c (t k) < ∑ k, n0c (t k) ∨
  ∑ k, n2c (t k) < 3 * (Finset.univ.filter (fun i : Fin M => n2c (t (i - 1)) = 1 ∧ n2c (t i) = 1)).card + ∑ k, n0c (t k) ∨
  (M = 4 ∧ ∃ a : Fin M, t a = 2 ∧ t (a + 1) = 0 ∧ t (a + 2) = 2)

instance {M : ℕ} [NeZero M] (t : Fin M → Fin 3) : Decidable (CornerGood t) := by unfold CornerGood; infer_instance

theorem cornerGood3 : ∀ t : Fin 3 → Fin 3, ∑ k, (n0c (t k) + 2 * n2c (t k)) = 3 * (3 - 2) → CornerGood t := by decide
theorem cornerGood4 : ∀ t : Fin 4 → Fin 3, ∑ k, (n0c (t k) + 2 * n2c (t k)) = 3 * (4 - 2) → CornerGood t := by decide
theorem cornerGood5 : ∀ t : Fin 5 → Fin 3, ∑ k, (n0c (t k) + 2 * n2c (t k)) = 3 * (5 - 2) → CornerGood t := by decide
theorem cornerGood6 : ∀ t : Fin 6 → Fin 3, ∑ k, (n0c (t k) + 2 * n2c (t k)) = 3 * (6 - 2) → CornerGood t := by decide

/-- **Corner classification and pigeonhole input.** -/
theorem corner_comb {M : ℕ} [NeZero M] (h3 : 3 ≤ M) (x y : Fin M → ℕ)
    (hty : ∀ k, (x k = 1 ∧ y k = 0) ∨ (x k = 2 ∧ y k = 0) ∨ (x k = 0 ∧ y k = 1))
    (hsum : ∑ k, (x k + 2 * y k) = 3 * (M - 2)) :
    M ≤ 6 ∧ ∑ k, x k + 2 * ∑ k, y k = 3 * (M - 2) ∧
    (∑ k, y k < ∑ k, x k ∨
     ∑ k, y k < 3 * (Finset.univ.filter (fun i : Fin M => y (i - 1) = 1 ∧ y i = 1)).card + ∑ k, x k ∨
     (M = 4 ∧ ∃ a : Fin M, y a = 1 ∧ x (a + 1) = 1 ∧ y (a + 1) = 0 ∧ y (a + 2) = 1)) := by
  have hs2 : ∑ k, x k + 2 * ∑ k, y k = 3 * (M - 2) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]; exact hsum
  -- M <= 6: each corner contributes at least 1 unit, and at most 2
  have hM6 : M ≤ 6 := by
    have h1 : ∑ _k : Fin M, 1 ≤ ∑ k, (x k + 2 * y k) :=
      Finset.sum_le_sum fun k _ => by rcases hty k with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> omega
    have h2 : ∑ k, (x k + 2 * y k) ≤ ∑ _k : Fin M, 2 :=
      Finset.sum_le_sum fun k _ => by rcases hty k with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> omega
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1 h2
    omega
  refine ⟨hM6, hs2, ?_⟩
  obtain ⟨t, hx, hy⟩ : ∃ t : Fin M → Fin 3, x = (fun k => n0c (t k)) ∧ y = (fun k => n2c (t k)) := by
    refine ⟨fun k => if y k = 1 then 2 else if x k = 1 then 0 else 1, ?_, ?_⟩ <;> funext k <;>
      rcases hty k with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> simp [a, b, n0c, n2c]
  subst hx hy
  have hgood : CornerGood t := by
    interval_cases M
    · exact cornerGood3 t hsum
    · exact cornerGood4 t hsum
    · exact cornerGood5 t hsum
    · exact cornerGood6 t hsum
  rcases hgood with h | h | ⟨hM, a, ha, hb, hc⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨hM, a, ?_, ?_, ?_, ?_⟩) <;> simp [ha, hb, hc, n0c, n2c]

/-! ### Non-vacuity: three concrete arrangements satisfying the hypotheses. -/
-- trapezoid (G,G,A,A): M = 4, units 2+2+1+1 = 6
example : ∑ k : Fin 4, (n0c (![2, 2, 0, 0] k) + 2 * n2c (![2, 2, 0, 0] k)) = 3 * (4 - 2) := by decide
-- parallelogram (G,A,G,A): M = 4, and its pattern is the third alternative of the conclusion
example : ∑ k : Fin 4, (n0c (![2, 0, 2, 0] k) + 2 * n2c (![2, 0, 2, 0] k)) = 3 * (4 - 2) := by decide
example : ∃ a : Fin 4, (![2, 0, 2, 0] : Fin 4 → Fin 3) a = 2 ∧ (![2, 0, 2, 0] : Fin 4 → Fin 3) (a + 1) = 0 ∧ (![2, 0, 2, 0] : Fin 4 → Fin 3) (a + 2) = 2 :=
  ⟨0, by decide⟩
-- hexagon with six single-gamma corners: R = 6, P = 0, g = 6
example : ∑ k : Fin 6, (n0c (![2, 2, 2, 2, 2, 2] k) + 2 * n2c (![2, 2, 2, 2, 2, 2] k)) = 3 * (6 - 2) := by decide

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.corner_comb
