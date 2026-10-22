-- Draft/LaczFormalRegArith.lean -- arithmetic layer of Laczkovich's REGULAR-tiling classification (DCG 48 (2012) 330-372, Sects. 4-8):
--  (1) the lists of "exceptional" vertex equations: Lemma 8.1 (gamma = pi/3, quoted list `3g=pi, 6g=2pi, 3a+3b=2pi, a+b+4g=2pi`)
--      and Lemma 7.1 (gamma = 2pi/3, quoted list `3g=2pi, 3a+3b=pi, 4a+4b+g=2pi, 6a+6b=2pi`), as decidable statements about the
--      numbers (p, r, v) of the reduced equation  p(alpha+beta) + r gamma = v pi  (p = common count of alpha and beta);
--  (2) the finite-digraph balance lemma used in Lemma 4.6 / 7.1(i) / 8.1(i): in-degree <= 1 and (in-degree > 0 => out-degree > 0)
--      force out-degree = in-degree at every vertex (hence no outgoing edge from a vertex without incoming edges).
-- Pure arithmetic / finite combinatorics; no geometry.  UNAUDITED.  Credit: Laczkovich (2012, Lemmas 4.6, 7.1, 8.1).
import Mathlib.Tactic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Erdos634.Draft.LaczFormal

/-! ## (1) Exceptional vertex equations -/

/-- **Lemma 8.1, list of exceptional equations (gamma = pi/3, alpha + beta = 2 pi/3).**  In units of `pi/3` the reduced equation
`p (alpha+beta) + r gamma = v pi` reads `2p + r = 3v`.  Exceptional means `p ≠ r` (the vertex is not normal).  With `v ∈ {1,2}`
(`pi` on a tile edge, `2pi` interior) the only solutions are `3γ = π`, `6γ = 2π`, `α+β+4γ = 2π`, `3α+3β = 2π`. -/
theorem caseIV_exceptional_list (p r v : ℕ) (hv : v = 1 ∨ v = 2) (h : 2 * p + r = 3 * v) (hne : p ≠ r) :
    (p = 0 ∧ r = 3 ∧ v = 1) ∨ (p = 0 ∧ r = 6 ∧ v = 2) ∨ (p = 1 ∧ r = 4 ∧ v = 2) ∨ (p = 3 ∧ r = 0 ∧ v = 2) := by
  rcases hv with rfl | rfl <;> omega

/-- Non-vacuity of the Case IV list: each member satisfies the hypotheses, and the normal solutions (`p = r`) are exactly
the ones excluded. -/
theorem caseIV_exceptional_realised :
    (2 * 0 + 3 = 3 * 1 ∧ (0 : ℕ) ≠ 3) ∧ (2 * 0 + 6 = 3 * 2 ∧ (0 : ℕ) ≠ 6) ∧
    (2 * 1 + 4 = 3 * 2 ∧ (1 : ℕ) ≠ 4) ∧ (2 * 3 + 0 = 3 * 2 ∧ (3 : ℕ) ≠ 0) ∧
    (2 * 1 + 1 = 3 * 1 ∧ (1 : ℕ) = 1) ∧ (2 * 2 + 2 = 3 * 2 ∧ (2 : ℕ) = 2) := by
  decide

/-- **Lemma 7.1, list of exceptional equations (gamma = 2pi/3, alpha + beta = pi/3).**  In units of `pi/3`: `p + 2r = 3v`. -/
theorem caseIII_exceptional_list (p r v : ℕ) (hv : v = 1 ∨ v = 2) (h : p + 2 * r = 3 * v) (hne : p ≠ r) :
    (p = 3 ∧ r = 0 ∧ v = 1) ∨ (p = 6 ∧ r = 0 ∧ v = 2) ∨ (p = 4 ∧ r = 1 ∧ v = 2) ∨ (p = 0 ∧ r = 3 ∧ v = 2) := by
  rcases hv with rfl | rfl <;> omega

theorem caseIII_exceptional_realised :
    (3 + 2 * 0 = 3 * 1 ∧ (3 : ℕ) ≠ 0) ∧ (6 + 2 * 0 = 3 * 2 ∧ (6 : ℕ) ≠ 0) ∧
    (4 + 2 * 1 = 3 * 2 ∧ (4 : ℕ) ≠ 1) ∧ (0 + 2 * 3 = 3 * 2 ∧ (0 : ℕ) ≠ 3) ∧
    (1 + 2 * 1 = 3 * 1 ∧ (1 : ℕ) = 1) ∧ (2 + 2 * 2 = 3 * 2 ∧ (2 : ℕ) = 2) := by
  decide

/-! ## (2) Balance of a finite digraph -/

/-- **Digraph balance** (the counting step of Laczkovich Lemma 4.6, 7.1(i), 8.1(i)).  In a finite digraph with in-degree `≤ 1`
at every vertex in which every vertex of positive in-degree has positive out-degree, in-degree = out-degree at every vertex. -/
theorem digraph_balance {V : Type*} [Fintype V] [DecidableEq V] (E : Finset (V × V))
    (hin : ∀ v, (E.filter fun e => e.2 = v).card ≤ 1)
    (hout : ∀ v, 0 < (E.filter fun e => e.2 = v).card → 0 < (E.filter fun e => e.1 = v).card) :
    ∀ v, (E.filter fun e => e.1 = v).card = (E.filter fun e => e.2 = v).card := by
  have hle : ∀ v ∈ (Finset.univ : Finset V),
      (E.filter fun e => e.2 = v).card ≤ (E.filter fun e => e.1 = v).card := by
    intro v _
    by_cases h0 : (E.filter fun e => e.2 = v).card = 0
    · omega
    · have := hout v (Nat.pos_of_ne_zero h0)
      have := hin v
      omega
  have h1 : E.card = ∑ v, (E.filter fun e => e.1 = v).card :=
    Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  have h2 : E.card = ∑ v, (E.filter fun e => e.2 = v).card :=
    Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  have hsum : ∑ v, (E.filter fun e => e.2 = v).card = ∑ v, (E.filter fun e => e.1 = v).card := by
    rw [← h1, ← h2]
  intro v
  exact ((Finset.sum_eq_sum_iff_of_le hle).mp hsum v (Finset.mem_univ v)).symm

/-- Consequence used for "no edge starts on the boundary": a vertex with no incoming edge has no outgoing edge. -/
theorem digraph_no_out_of_no_in {V : Type*} [Fintype V] [DecidableEq V] (E : Finset (V × V))
    (hin : ∀ v, (E.filter fun e => e.2 = v).card ≤ 1)
    (hout : ∀ v, 0 < (E.filter fun e => e.2 = v).card → 0 < (E.filter fun e => e.1 = v).card)
    (v : V) (h0 : (E.filter fun e => e.2 = v).card = 0) : (E.filter fun e => e.1 = v).card = 0 := by
  rw [digraph_balance E hin hout v, h0]

/-- Non-vacuity: the directed triangle on `Fin 3` satisfies both hypotheses. -/
theorem digraph_balance_witness :
    let E : Finset (Fin 3 × Fin 3) := {(0, 1), (1, 2), (2, 0)}
    (∀ v, (E.filter fun e => e.2 = v).card ≤ 1) ∧
    (∀ v, 0 < (E.filter fun e => e.2 = v).card → 0 < (E.filter fun e => e.1 = v).card) := by
  decide

/-- Negative control: the hypothesis "positive in-degree implies positive out-degree" cannot be dropped: the single edge
`0 → 1` has in-degree `≤ 1` everywhere but is unbalanced. -/
theorem digraph_balance_needs_hout :
    let E : Finset (Fin 2 × Fin 2) := {(0, 1)}
    (∀ v, (E.filter fun e => e.2 = v).card ≤ 1) ∧
    ¬ (∀ v, (E.filter fun e => e.1 = v).card = (E.filter fun e => e.2 = v).card) := by
  decide

end Erdos634.Draft.LaczFormal
