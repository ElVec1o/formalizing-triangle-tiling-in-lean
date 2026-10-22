import Mathlib

/-!
# Beeson (arXiv 1206.2229 v4) Lemma 43: no `N`-tiling of `(2 alpha, beta, alpha+beta)` for `N < 28`, from Lemmas 39-42

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Lemmas 39-43, Theorem 10), Beeson-Rosu, Laczkovich, Beeson-Zhang.
Formalization debt, not progress on the /goal outcomes.

Printed proof: "For N < 28, the equation M^2 + N = 2 K^2 has a solution with 0 < M < K only for N = 7, 14, 17, 23 ...
We have ruled each of these out in the previous four lemmas."  This file proves exactly that logical skeleton:

* `lemma43_arith` : the arithmetic fact (finite check).
* `lemma43_of` : with `Tiles N` standing for "a triangle with angles `(2 alpha, beta, alpha+beta)`, `3 alpha + 2 beta = pi`,
  `alpha` not a rational multiple of `pi`, has an `N`-tiling", and the NAMED hypotheses
    - `hT10` : `Tiles N -> exists M K, 0 < M < K, M^2 + N = 2 K^2` (printed Theorem 10, `s = M/K` with `0 < s < 1`),
    - `h39`, `h41`, `h42` : `not Tiles 14, 7, 23` (project: `BeesonSmallN.lemma39/41/42`, stronger form
      `CongruentDissection N -> False`),
    - `h40` : `not Tiles 17` (printed Lemma 40; GAP: no Lean proof; the engine registry row `cevian 1 3 1 17 (3,8,9)` is a
      search result, NO_TILING, 191 nodes; Beeson's proof is the d-matrix / boundary-layer argument of Lemmas 31-38),
  `Tiles N` is false for every `N < 28`.
-/

namespace Erdos634.BeesonCol2L43

theorem lemma43_arith (N : ℕ) (hN : 0 < N) (hN28 : N < 28)
    (h : ∃ M K : ℕ, 0 < M ∧ M < K ∧ M ^ 2 + N = 2 * K ^ 2) :
    N = 7 ∨ N = 14 ∨ N = 17 ∨ N = 23 := by
  obtain ⟨M, K, hM, hMK, he⟩ := h
  have hK : K ≤ 5 := by nlinarith
  have hMK' : M < 5 := by omega
  interval_cases K <;> interval_cases M <;> omega

theorem lemma43_of (Tiles : ℕ → Prop)
    (hT10 : ∀ N, 0 < N → Tiles N → ∃ M K : ℕ, 0 < M ∧ M < K ∧ M ^ 2 + N = 2 * K ^ 2)
    (h7 : ¬ Tiles 7) (h14 : ¬ Tiles 14) (h17 : ¬ Tiles 17) (h23 : ¬ Tiles 23) :
    ∀ N, 0 < N → N < 28 → ¬ Tiles N := by
  intro N hN hlt ht
  rcases lemma43_arith N hN hlt (hT10 N hN ht) with rfl | rfl | rfl | rfl
  exacts [h7 ht, h14 ht, h17 ht, h23 ht]

/-- Witness that the four hypothesised values really are the solutions, with the printed tiles:
`(M,K) = (1,2), (2,3), (1,3), (3,4)` for `N = 7, 14, 17, 23`. -/
theorem lemma43_wit : (1 : ℕ) ^ 2 + 7 = 2 * 2 ^ 2 ∧ 2 ^ 2 + 14 = 2 * 3 ^ 2 ∧ 1 ^ 2 + 17 = 2 * 3 ^ 2 ∧
    3 ^ 2 + 23 = 2 * 4 ^ 2 := by norm_num

end Erdos634.BeesonCol2L43
