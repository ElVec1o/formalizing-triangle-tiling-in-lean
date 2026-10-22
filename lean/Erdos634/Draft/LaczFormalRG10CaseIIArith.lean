-- Draft/LaczFormalRG10CaseIIArith.lean -- Laczkovich DCG 48 (2012), Case II (gamma < pi/2, gamma != pi/3), Subcase IIa, the bookkeeping the printed text leaves implicit ("Repeating the analogous argument of case I, we can also see
-- that the cases R = N-1 and R = N are impossible", Sect. 6.1).  In Case I the side rule is Lemma 4.3 (i), which only constrains INTERIOR vertices of a side; in Case II it is Lemma 4.3 (iii), which in addition needs
-- "no edge of Gamma_a starts from X or from Y", so a boundary vertex with an outgoing edge blocks up to TWO sides instead of one.  The count still closes, because of the numeric facts below.  NOTE, UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Sect. 4, 6), Beeson, Beeson-Zhang.
import Mathlib

namespace Erdos634.Draft.LaczFormal.RG

/-- `P = N-1`: the reduced equation `k gamma = pi` with `k = N-1-R` and a vertex of `A` of type `R gamma` (`R >= 1`) force `N >= 6` (`k >= 4`, as `gamma < pi/2` and `gamma != pi/3`). -/
theorem caseII_PN1_N_ge_six {N R k : ℕ} (hR : 1 ≤ R) (hN : N = k + 1 + R) {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < Real.pi / 2) (hγ3 : γ ≠ Real.pi / 3)
    (hk : (k : ℝ) * γ = Real.pi) : 6 ≤ N := by
  have hpi := Real.pi_pos
  have hk4 : 4 ≤ k := by
    by_contra hlt
    push Not at hlt
    interval_cases k
    · simp at hk; linarith
    · simp at hk; linarith
    · norm_num at hk; linarith
    · apply hγ3; norm_num at hk; linarith
  omega

/-- `P = N`: `N gamma = 2 pi` with `gamma < pi/2` gives `N >= 5` (and `N != 6` from `gamma != pi/3`). -/
theorem caseII_PN_N_ge_five {N : ℕ} {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < Real.pi / 2) (hγ3 : γ ≠ Real.pi / 3) (hN : (N : ℝ) * γ = 2 * Real.pi) :
    5 ≤ N ∧ N ≠ 6 := by
  have hpi := Real.pi_pos
  refine ⟨?_, ?_⟩
  · by_contra hlt
    push Not at hlt
    have : (N : ℝ) ≤ 4 := by exact_mod_cast Nat.lt_succ_iff.mp hlt
    nlinarith
  · rintro rfl
    apply hγ3
    push_cast at hN
    linarith

/-- Blocked sides, `P = N-1`: one exceptional vertex (boundary or interior; interior => at most one boundary vertex `T` with an outgoing edge, which blocks at most two sides), and `N-2` sides have both ends of
type `alpha+beta`; for `N >= 6` a free side remains. -/
theorem caseII_free_side_PN1 {N eb ei Z : ℕ} (hN : 6 ≤ N) (hE : eb + ei ≤ 1) (hZ : Z ≤ ei) : eb + 2 * Z < N - 2 := by omega

/-- Blocked sides, `P = N`: at most two exceptional vertices and deficit at most their number; `N >= 5` sides, each with both ends of type `alpha+beta`; a free side remains. -/
theorem caseII_free_side_PN {N eb ei Z : ℕ} (hN : 5 ≤ N) (hE : eb + ei ≤ 2) (hZ : Z ≤ ei) : eb + 2 * Z < N := by omega

/-- WITNESSES for the hypotheses: `gamma = pi/4`, `k = 4`, `R = 1`, `N = 6` for `P = N-1`; `gamma = 2 pi / 5`, `N = 5` for `P = N`. -/
theorem caseII_arith_witness : 6 ≤ 4 + 1 + 1 ∧ (5 ≤ 5 ∧ (5 : ℕ) ≠ 6) := by
  have hpi := Real.pi_pos
  refine ⟨caseII_PN1_N_ge_six (N := 6) (R := 1) (k := 4) le_rfl rfl (γ := Real.pi / 4) (by positivity) (by linarith) (by intro h; linarith) (by push_cast; ring), ?_⟩
  exact caseII_PN_N_ge_five (N := 5) (γ := 2 * Real.pi / 5) (by positivity) (by linarith) (by intro h; linarith) (by push_cast; ring)

end Erdos634.Draft.LaczFormal.RG
