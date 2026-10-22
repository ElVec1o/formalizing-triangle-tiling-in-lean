import Erdos634.Draft.LaczFormalRGCaseVb
import Erdos634.Draft.LaczFormalRGCaseVc2

/-!
# Theorem 2.1, Case V (gamma = pi/2): the case split  (NOTE / UNAUDITED)

For a regular tiling of a convex quadrilateral by congruent triangles with a right angle
`gamma`, the polygon is a rectangle (conclusion (i)).  Sub-cases (Laczkovich, DCG 48 (2012),
Sect. 9; Beeson, Beeson-Zhang for the Gamma_a edge framework):
* `a, b` incommensurable: `NotComb a b c` (Va) or `NotComb b a c` (Vb); otherwise the two
  relations `r a = p b + q c`, `r' b = p' a + q' c` force `a, b` commensurable.
* `a, b` commensurable: `c` commensurable with `a` (Vc_comm) or not (Vc_c).
-/

namespace Erdos634.Draft.LaczFormal.RG
open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

/-- **Case V, full split** (quadrilateral targets).  NOTE / UNAUDITED. -/
theorem caseV {N : ℕ} (T : PolyTiling N 4) (hreg : RegularPQ T.C)
    (hγ : angleAt T.C.model 2 = Real.pi / 2) : Concl1 T.C T.P := by
  classical
  have ha := slen_pos T.C 0
  have hb := slen_pos T.C 1
  have hc := slen_pos T.C 2
  by_cases hcomm : ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * slen T.C 0 = n * slen T.C 1
  · obtain ⟨m, n, hm, hn, hab⟩ := hcomm
    by_cases hca : ∃ m' n' : ℕ, 0 < m' ∧ 0 < n' ∧ (m' : ℝ) * slen T.C 2 = n' * slen T.C 0
    · obtain ⟨m', n', hm', hn', h⟩ := hca
      exact caseV_Vc_comm T hreg hγ hm hn hm' hn' hab h
    · push_neg at hca
      exact caseV_Vc_c T hreg hγ hm hn hab hca
  · push_neg at hcomm
    by_cases h1 : NotComb (slen T.C 0) (slen T.C 1) (slen T.C 2)
    · exact caseV_Va T hreg hγ h1
    by_cases h2 : NotComb (slen T.C 1) (slen T.C 0) (slen T.C 2)
    · exact caseV_Vb T hreg hγ h2
    exfalso
    unfold NotComb at h1 h2
    push_neg at h1 h2
    obtain ⟨r, p, q, hr, e1⟩ := h1
    obtain ⟨r', p', q', hr', e2⟩ := h2
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq
      have hp : 0 < p := by
        rcases Nat.eq_zero_or_pos p with h0 | h0
        · subst h0
          have e1' : (r:ℝ) * slen T.C 0 = 0 := by rw [e1]; simp
          have : (0:ℝ) < r * slen T.C 0 := mul_pos (by exact_mod_cast hr) ha
          linarith
        · exact h0
      exact hcomm r p hr hp (by simpa using e1) 
    rcases Nat.eq_zero_or_pos q' with hq' | hq'
    · subst hq'
      have hp : 0 < p' := by
        rcases Nat.eq_zero_or_pos p' with h0 | h0
        · subst h0
          have e2' : (r':ℝ) * slen T.C 1 = 0 := by rw [e2]; simp
          have : (0:ℝ) < r' * slen T.C 1 := mul_pos (by exact_mod_cast hr') hb
          linarith
        · exact h0
      exact hcomm p' r' hp hr' (by simpa using e2.symm)
    refine hcomm (q' * r + q * p') (q * r' + q' * p) (Nat.add_pos_left (Nat.mul_pos hq' hr) _)
      (Nat.add_pos_left (Nat.mul_pos hq hr') _) ?_
    push_cast
    linear_combination (q' : ℝ) * e1 - (q : ℝ) * e2

end Erdos634.Draft.LaczFormal.RG
