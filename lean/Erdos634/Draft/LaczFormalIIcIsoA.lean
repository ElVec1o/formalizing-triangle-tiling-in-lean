-- Draft/LaczFormalIIcIsoA.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2-6.3, Case IIc with alpha = beta: the fan ARITHMETIC that replaces `straight_run_arith`.
-- With `omega 0 = omega 1` (isosceles model) a straight line of tile sides through a (2,2,2) vertex still splits the six corners into two runs of THREE sectors, but a run
-- carries the label 2 (gamma) EXACTLY ONCE and two alpha-angles (labels 0/1 in any combination): `straight_run_arith_iso`, `straight_run_labels_iso`.
-- Parallel to `straight_run_arith`/`straight_run_labels` (RG12Fan222), which are NOT edited.  Hypotheses: `AngGen'` plus `omega 0 = omega 1` (witnessed by the regular-polygon model alpha = pi/2 - pi/M, gamma = 2 pi/M, M >= 5, M != 6).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcG11h

open Erdos634.Draft.LaczFormal.Graph

namespace Erdos634.Draft.LaczFormal.RG

/-- **Straight sums, isosceles**: `a alpha + b alpha + c gamma = pi` with `a, b, c <= 2` forces `c = 1` and `a + b = 2`. -/
theorem straight_run_arith_iso {ω : Fin 3 → ℝ} (G : AngGen' ω) (h01 : ω 0 = ω 1) {a b c : ℕ} (ha : a ≤ 2) (hb : b ≤ 2) (hc : c ≤ 2)
    (h : (a : ℝ) * ω 0 + b * ω 1 + c * ω 2 = Real.pi) : c = 1 ∧ a + b = 2 := by
  have p0 := G.pos 0
  have p1 := G.pos 1
  have p2 := G.pos 2
  have hs := G.sum
  have hpi := Real.pi_pos
  rw [← h01] at h hs
  interval_cases a <;> interval_cases b <;> interval_cases c <;> norm_num at h ⊢ <;>
    first
    | (exfalso; linarith)
    | exact (G.ne02 (by linarith)).elim
    | exact (G.r0 (by linarith)).elim
    | exact (G.r2 (by linarith)).elim

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.straight_run_arith_iso
