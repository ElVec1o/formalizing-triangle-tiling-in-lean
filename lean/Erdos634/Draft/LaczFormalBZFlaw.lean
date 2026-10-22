-- Draft/LaczFormalBZFlaw.lean -- THE FLAW IN THE PRINTED LEMMA 7.1 (i) OF LACZKOVICH (DCG 48 (2012), p. 364, lines 13-14 of the proof), as a theorem,
-- with its negative controls (Beeson-Zhang, arXiv 2604.01314v1, Appendix A).
--
-- The printed claim, at a vertex X whose equation is 3 alpha + 3 beta = pi (six corner tiles on one side of a straight line, three of angle beta and three of angle alpha),
-- reached by an incoming Gamma_a edge along the line, is: "an edge of Gamma_a starts from X".  Local (fan) form: `PrintedL71_330`.  It is FALSE: `printed_L71_330_false`.
-- Exact size of the failure: of the 512 admissible fans (types (3,3,0) with an incoming a-edge), exactly 64 have no outgoing Gamma_a edge (`pi330_hyp_count`, `pi330_counterexample_count`),
-- the other 448 have one (`pi330_good_count`).  Negative controls (statements of the same shape that ARE true): the normal pi-vertex (1,1,1) (`pi_fan_normal`), the vertex
-- 3 gamma = pi once Gamma_k is added (`pi_fan_3gamma`); and the (3,3,0) vertex with the hypothesis "the number of non-a corners is even" (`parity_control`: the even-parity
-- version of the claim is not violated), which is the mechanism behind Lemma 4.5 for Gamma_c (non-c corners are alpha, beta: equally many, so an even number).
-- What this does NOT show: that the lemma fails in a real tiling (a fan is local data); Beeson-Zhang exhibit the local configuration (their Fig. 4) and say the printed proof does not repair.
-- Consequence recorded in `RG.caseIII_reduce`: Subcases IIIa/IIIb of Thm 2.1 are not supported by the printed argument.
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 7), Beeson-Zhang (the flaw).
import Erdos634.Draft.LaczFormalRG3Gap

namespace Erdos634.Draft.LaczFormal.RegFan

/-- **Laczkovich's printed Lemma 7.1 (i) at a `3α + 3β = π` vertex, local form**: for every fan of six corners (types `(3,3,0)`) with an incoming `Γ_a` edge along the boundary line,
an edge of `Γ_a` starts along one of the five inner rays. -/
def PrintedL71_330 : Prop :=
  ∀ l : List ℕ, l.length = 6 → (∀ x ∈ l, x < 6) → pi330Hyp l = true → pi330Concl l = true

/-- **The printed claim is false** (Beeson-Zhang, Appendix A; local witness: the fan `[3,2,3,0,0,0]` = `β,β,β,α,α,α`). -/
theorem printed_L71_330_false : ¬ PrintedL71_330 := pi330_fails

/-- The number of admissible fans (hypotheses of the printed claim). -/
theorem pi330_hyp_count : ((allFans 6).filter pi330Hyp).length = 512 := by decide +kernel

/-- Exactly 64 of the 512 admissible fans are counterexamples. -/
theorem pi330_counterexample_count : ((allFans 6).filter (fun l => pi330Hyp l && !pi330Concl l)).length = 64 := by decide +kernel

/-- The other 448 satisfy the printed conclusion (so the claim is not false "everywhere": the lemma is true at most fans and false at some). -/
theorem pi330_good_count : ((allFans 6).filter (fun l => pi330Hyp l && pi330Concl l)).length = 448 := by decide +kernel

/-- NEGATIVE CONTROL 1 (same shape, true): the fans `[3,2,2,0,0,0]`, `[3,3,2,0,0,0]`, `[3,3,3,0,0,0]` satisfy the hypotheses AND the conclusion. -/
theorem pi330_control_true :
    pi330Hyp [3, 2, 2, 0, 0, 0] = true ∧ pi330Concl [3, 2, 2, 0, 0, 0] = true ∧
    pi330Hyp [3, 3, 2, 0, 0, 0] = true ∧ pi330Concl [3, 3, 2, 0, 0, 0] = true ∧
    pi330Hyp [3, 3, 3, 0, 0, 0] = true ∧ pi330Concl [3, 3, 3, 0, 0, 0] = true := by decide

/-- NEGATIVE CONTROL 2: the normal `π`-vertex `α+β+γ = π` (Lemma 4.2 local content) is true for every fan, and has a non-vacuous instance. -/
theorem normal_control : (∀ l : List ℕ, l.length = 3 → (∀ x ∈ l, x < 6) → piNormalHyp l = true → piNormalConcl l = true) ∧
    piNormalHyp [0, 2, 4] = true := ⟨fun l h1 h2 h3 => pi_fan_normal l h1 h2 h3, by decide⟩

/-- NEGATIVE CONTROL 3: the counterexample fan has THREE corners that are not `α` (the `β`'s): an odd number.  The parity of the non-`a` corners is what the printed argument misses:
among the 64 counterexamples the number of non-`a` corners is always 3 (odd), whereas for `Γ_c` the non-`c` corners are `α, β` in equal numbers (even), the vertex-local reason
Lemma 4.5 holds for `Γ_c`.  (Statement: the number of non-`α` corners of every fan with the hypotheses is exactly 3, so odd; it is a property of the type `(3,3,0)`, not of the 64.) -/
theorem pi330_nonalpha_odd : ∀ l ∈ (allFans 6).filter pi330Hyp, (l.filter (fun x => tT x != 0)).length = 3 := by decide +kernel

end Erdos634.Draft.LaczFormal.RegFan

#print axioms Erdos634.Draft.LaczFormal.RegFan.printed_L71_330_false
#print axioms Erdos634.Draft.LaczFormal.RegFan.pi330_good_count
#print axioms Erdos634.Draft.LaczFormal.RegFan.normal_control
