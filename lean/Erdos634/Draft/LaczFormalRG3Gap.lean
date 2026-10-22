-- Draft/LaczFormalRG3Gap.lean -- THE GAP IN LACZKOVICH'S LEMMA 7.1 (DCG 48 (2012), p. 364), as a decidable local statement (Beeson-Zhang, arXiv 2604.01314, Appendix A).
-- Lemma 7.1 (i) needs: if `X` is the head of an edge of `Gamma_a` and the equation at `X` is `3 alpha + 3 beta = pi` (six corner tiles, three with `beta` and three with `alpha`, on one side of a straight line),
-- then an edge of `Gamma_a` starts from `X` ("Three of the triangles T_i have angle beta at X, and at least two of them are of the same orientation ...").  For `gamma = pi/3` the analogous vertex is `3 gamma = pi`
-- (`RegFan.pi_fan_3gamma`: TRUE, with `Gamma_k` added).  For `gamma = 2 pi/3` the claim is FALSE even locally: `pi330_fails` exhibits a fan of six corners (types `beta, beta, beta, alpha, alpha, alpha`)
-- satisfying the hypotheses (incoming `Gamma_a` edge along the straight line) with NO `Gamma_a` edge along any of the five inner rays.  64 of the 512 admissible fans are such counterexamples (`#eval`, checked 2026-10-21).
-- What the repair must do (not done here): the balance `out-degree = in-degree` of Lemma 7.1 (i) cannot be proved vertex by vertex; either a modified graph (as `Gamma_k` for `gamma = pi/3`) or a global argument
-- is needed, and Laczkovich's own repair (mentioned in Beeson-Zhang, footnote 1) is not available.  Consequently Subcases IIIa/IIIb of Theorem 2.1 are NOT formalized (`RG3Comm.caseIII_reduce`).
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 7), Beeson-Zhang (the gap).
import Erdos634.Draft.LaczFormalRegFan

namespace Erdos634.Draft.LaczFormal.RegFan

/-- Six corner tiles on one side of a straight line through `X`, types `(3,3,0)` (`3α + 3β = π`), with an incoming `Γ_a` edge along the line. -/
def pi330Hyp (l : List ℕ) : Bool := cnt l 0 == 3 && cnt l 1 == 3 && cnt l 2 == 0 && incoming l
/-- An edge of `Γ_a` starts along one of the five inner rays. -/
def pi330Concl (l : List ℕ) : Bool := (List.range 6).any (fun i => 1 ≤ i && gaEdge l i)

/-- **The claim of Lemma 7.1 at a `3α+3β = π` vertex is false locally.** -/
theorem pi330_fails : ¬ ∀ l : List ℕ, l.length = 6 → (∀ x ∈ l, x < 6) → pi330Hyp l = true → pi330Concl l = true := by
  intro h
  have := h [3, 2, 3, 0, 0, 0] (by decide) (by decide) (by decide)
  revert this
  decide

/-- The counterexample fan: hypotheses hold, conclusion fails. -/
theorem pi330_witness : pi330Hyp [3, 2, 3, 0, 0, 0] = true ∧ pi330Concl [3, 2, 3, 0, 0, 0] = false := by decide

/-- NEGATIVE CONTROL: the corresponding statement for `3γ = π` (three `γ` corners) is true once `Γ_k` is added (`pi_fan_3gamma`), and for the normal vertex `α+β+γ = π` it is true (`pi_fan_normal`). -/
theorem pi003_control : (allFans 3).all pi003OK = true := pi003_check

end Erdos634.Draft.LaczFormal.RegFan
