# Fidelity of theorem21_unconditional (Laczkovich DCG 48 Thm 2.1)

Labels: every theorem here is NOTE/UNAUDITED by anyone outside the project (see README). Written 2026-10-22; internal working document, lightly cleaned of references to private notes.


# Laczkovich Thm 2.1 (DCG 48 (2012)): statement fidelity of `RG.theorem21_unconditional` -- 2026-10-22
Label: NOTE / UNAUDITED (internal; not audited outside the project). Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
Lean: `Erdos634.Draft.LaczFormal.RG.theorem21_unconditional : Theorem21` (Draft/LaczFormalThm21Final.lean) `= theorem21_of_noKites iicNoKites_proved`.
`#print axioms`: [propext, Classical.choice, Quot.sound] (also for `iic_claim_unconditional : IIcClaim`, `assembly_witness_unc`). Log: (project working notes, not included) (9231 jobs OK).
Scan: a `sorryAx` or `Lean.ofReduceBool` (native_decide) anywhere in the dependency closure would appear in the axioms print; none does. The grep of Draft/LaczFormal*.lean finds `sorry` only in comments ("no sorry").

## Hypothesis block (complete list)
`Theorem21 := forall (N M : N) [NeZero M] (T : PolyTiling N M), RegularPQ T.C -> Thm21Concl T.C T.P`.
* `PolyTiling N M`: a `CongruentRegionDissection N` C, a strictly convex polygon P (M >= 3, vertices ccw, `left` strict), `C.region = P.carrier`.
* `RegularPQ C`: exists `idx` (angle-preserving vertex correspondence) with `cntR C idx X 0 = cntR C idx X 1` at every point X (normalisation p = q of the paper's three alternatives).
No other hypothesis. `IIcNoKites` itself is universally quantified over all N, M, PolyTiling T, idx (`forall N M T idx, CaseC ... -> kiteB = empty`); its hypothesis block is the Case IIc block (CaseC, angle 2 < pi/2, != pi/3, Comm a b, not Comm a c, AngGen, corner counts), which is a case hypothesis, not a residual assumption: IIc is a case of the proof. Non-vacuity: `assembly_witness` on `rTilingSqrt3` (Thm21AssemblyWit) for the non-IIc branch; the IIc block is witnessed for the isosceles case by IsoWitM (8-tile octagon, IsoWitA..M) and for GENERIC angles (AngGen, alpha != beta, CaseC, corner counts, Comm a b, not Comm a c, gamma = pi/4) by GenWitK (204-tile octagon, `genTiling_thm21`, with kiteB = empty proved by genDiss_noGKite). CORRECTION 2026-10-22 (fresh IIc audit): the earlier sentence 'no genuine IIc generic-angle example is known' was stale; the hypothesis block is satisfiable in both subclasses. The chain hypotheses inside the proof (closed injective Gamma_kite chain, kiteB nonempty) are intentionally inconsistent (proof by contradiction, printed Lemma 6.2).

## Table (Lean `Thm21Concl` disjunct; printed paper statement paraphrased from the docstrings of Draft/LaczFormalThm21Def.lean)
| # | Lean | Deviation / note |
|---|---|---|
| i | `Concl1`: `M = 4 /\ forall i, v_i + v_{i+2} = v_{i+1} + v_{i+3}`, `exists i, angle i = gamma`, `(exists q:Q, side0/side1 = q * sin a/sin b) \/ (same with side1/side0)` | Printed: parallelogram, angles gamma and alpha+beta, side ratio rational multiple of sin a/sin b. Either order accepted (accepted because the printed "ratio of the two sides" is order-free). |
| ii | `Concl2`: RationalPoly, M-2 angles = gamma, other two = m(a+b), n(a+b), `SinComm` | match |
| iii | `Concl3`: RationalPoly, M-2 angles = a+b, other two = m gamma, n gamma, `SinComm` | match |
| iv | `Concl4`: M=3, equilateral, gamma in {pi/3, 2pi/3}, `SinComm` | match |
| v | `Concl5`: M = 2k, k >= 4, rational, all angles a+b, `side i = side (i+k)`, `exists q, (q = sin0/sin1 \/ q = sin1/sin0)`, a geometric from some vertex s and direction rev, `q^(k-1) a_0 <= a_(k-1)` | KNOWN DEVIATIONS: (1) q or 1/q (labels 0,1 interchangeable in the paper; Lean first fixed sin0/sin1, strengthened-wrongly, repaired 2026-10-22); (2) start vertex and direction existentially chosen ("in this order"); (3) the inequality is stated as `a_k >= q^(k-1) a_1` verbatim, but its proof for the non-AngGen IIc subclass goes through the G11 repair ((project working notes, not included); (4) `a_i` indexed from 0. |
| vi | `Concl6`: M = 6, rational, `side i = side (i+3)`, all angles 2pi/3, gamma in {pi/3, 2pi/3}, `exists q:Q, sin a/sin b = q` | The paper's (vi) clause is dropped from `lemma63_full` under h3 (gamma != pi/3): in Case IIc the branch producing (vi) needs gamma = pi/3, which h3 excludes, so (vi) is never output by IIc; (vi) arises only in IVc (`caseIVc_concl`). Not a weakening of the theorem. |
| vii | `Concl7`: regular M-gon, a = b = pi/2 - pi/M, gamma = 2pi/M | match |
| viii | `Concl8`: rational, M <= 6, angles in {pi/3, 2pi/3}, a = b = pi/6, gamma = 2pi/3 | match |
| ix | `Concl9`: M = 6, rational, angles 2pi/3, gamma = pi/3, {a,b} = {pi/6, pi/2} | match |
Whole: `Thm21Concl` is the 9-fold disjunction in order i..ix; `RationalPoly P` = sides pairwise `Comm` (positive integer multiples agree), the paper's "rational polygon".

## Printed gaps repaired (the Lean statement is the REPAIRED theorem, not a transcription of the printed proof)
* Lemma 7.1(i) (Case IIIa/IIIb): printed counting false at 3a+3b = pi (`printed_L71_330_false`); Lean uses the Beeson-Zhang repair `caseIIIa_repaired`/`caseIIIb_repaired`; the printed L7.1 is not used.
* Lemma 6.3: printed "at most k" corrected to "at most k-1" (Lean `lemma63` machinery, Sharp5/7).
* "Every vertex on XY is normal" (Lemma 6.2/6.3 setup): not assumed; proved as part of ExcInsideAll / GExc start (`gexc_start_of_corner`).
* A straight vertex on the Gamma_kite cycle: handled explicitly in the Gamma_kite chain argument (WN119-126: convex-vertex chords, nesting).
* Case IVc: boundary c-sides: the printed "repeating IIIc" is not literal (c-edge opposite pi/3; new sign lemma `flux_cedge` for gamma = pi/3, `ivc_final_ge5`, `ivc_rat_final`).
* Lemma 6.2 for isosceles models (alpha = beta) is proved separately (IsoF/IsoG/IsoH-K), with its own G11 (`g11_two_iso`).

## Honest status
Statement as Lean-formalized and proved: yes, standard axioms. Not claimed: that it is the printed theorem verbatim (deviations above), that anyone outside the project has read it, or any consequence for #634 (this is formalization debt, not progress on any open problem).

