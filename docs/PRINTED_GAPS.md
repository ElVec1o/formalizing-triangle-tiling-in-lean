# Printed gaps and slips found while formalizing

Status of every item: **as found in our formalization; not yet communicated to the authors.**
Tone: these are small observations made while turning proofs into Lean. A printed argument that a human expert
fills in without noticing is not an error in the mathematics; where we say "false" we mean the literal printed
sentence, and where the theorem itself survives we say so. Each item is based on the Lean files named, the
exact printed statement paraphrased, and what we needed instead. Our readings of the sources may be wrong;
none of this has been checked by anyone outside the project. All Lean statements are NOTE/UNAUDITED (see README).

## Laczkovich, DCG 48 (2012), "Tilings of convex polygons with congruent triangles"

1. **Lemma 7.1(i) (Cases IIIa/IIIb).** The printed counting step is false in the literal local form at
   3alpha+3beta = pi: `PrintedL71_330` and `printed_L71_330_false` (`LaczFormalBZFlaw`; 512 admissible fans, 64
   counterexamples, checked by the kernel). This was found first by Beeson and Zhang (arXiv 2604.01314, Appendix A).
   Our repair: a defect count `caseIII_defects` (stars, double stars, gamma-stars, out-degree of Gamma_a) giving
   the inequality needed by the endgame; used in `caseIIIa_repaired`, `caseIIIb_repaired`.
2. **Case IVc, boundary c-sides.** The printed "repeating the argument of IIIc" is not literal: the c-edge lies
   opposite pi/3, and a new sign lemma `flux_cedge` was needed (`ivc_final_ge5`, `ivc_rat_final`). Also the
   dichotomy "no tile edge of length c on the boundary, or all of them" is proved at edge level
   (`ivc_rat_boundary_c_dichotomy`).
3. **"Every vertex on XY is normal" (Lemma 6.2/6.3 set-up).** Not assumed in the Lean proof; it is derived
   inside `excInsideAll_proved` / `gexc_start_of_corner`.
4. **Lemma 6.3, the bound at an exceptional point.** The printed bound "at most k-1" (and its justification) is
   not valid in the literal form at an exceptional point inside a tile side (a T-junction): there the end Y of
   an edge of Gamma_except can be an inner point of a step of the other division (arrival along a straight
   line). The sharp bound is k (`exc_capacity_sharp`, files Sharp5 and Sharp7), which is all the argument
   needs; the conclusion of Lemma 6.3 stands.
5. **A straight vertex on the Gamma_kite cycle.** Lemma 6.2's wording "angles alpha+beta or alpha+2 gamma+beta"
   does not list a straight (pi) vertex on the cycle; we handle it explicitly in the chain argument
   (`LaczFormalIIcWN119`-`126`: nesting, convex-vertex chords).
6. **Lemma 6.2, chord and arrival cases.** The printed disjointness of chords skips the endpoint cases (a chord
   at a concave vertex ending at a concave vertex); the Gamma_except ray at a cycle vertex lies in the
   alpha+beta wedge, not between the two gamma tiles. Both are covered by the arrival-direction lemmas
   `chord_wind_ne_near`, `chord_arrival_wind_zero`, `r2c_chord_end`.
7. **Lemma 6.2, labelling.** "angles alpha, beta at V_{i-1}, V_i" is not forced: either labelling occurs
   (`spokes_angle`); we apply `ring_monotone` with swapped arguments.
8. **Section 6.1, "repeating the analogous argument of Case I".** The step hides a counting argument: Case II
   needs Lemma 4.3(iii) (hypothesis "no edge of Gamma_a starts at X or Y"), so a boundary vertex with an outgoing
   edge can block two sides. See `LaczFormalRG10CaseIIArith` and the header of the Case II files.

## Laczkovich, Discrete Math. 140 (1995), "Tilings of triangles"

9. **Theorem 5.3, case (vii) (tile with angles pi/4, pi/8).** We did not find a printed proof of this case in the
   text we used; we prove it from scratch (`lacz53_thm`: side words, law of sines, Heron area in the basis
   1, sqrt2, s, sqrt2 s). Possibly the proof is in a source we did not have; we say only that we could not
   locate it.

## Beeson, arXiv 1206.1974 (isosceles targets)

10. **Lemma 10.4.** (a) The reason "no interior segment passes through an interior star" is not justified for
    a single interior star (4,2,1), which splits as (3,1,0)+(1,1,1), both of angle pi; a straight line can
    pass through it. We replaced the claim by a weighting argument. (b) The existence of a unique outgoing
    b/c or b/a segment is shown by Figures 13-14; we formalized the relation content only (see
    `beeson_thm107_proved`, file `LaczFormalBZL7h16`) and did not formalize the figure case analysis.
11. **Lemma 10.5.** The statement says an "a or b edge on PQ" where QR is meant (typo); we add the side
    condition that an alpha corner exists, which the printed proof uses.
12. **Lemma 11.8.** Literally false at the vertex B and for the corner tiles (a tile at B has vertices on both
    AB and BC); the proof assumes E on AB, F on BC, both different from B ("E on AC" is a typo).
13. **Lemma 11.11.** "By Lemma 11.8 no tile contributes to both n and m" fails for the two tiles at B; the
    bound becomes (N+1)/4. Lemma 11.9: last step (|RP| versus |AR|). Lemma 11.13: the statement concerns the
    legs but the proof the base AC; on a leg the pigeonhole is tight (we proved the base).

## Beeson, arXiv 1206.2229 (tilings of triangles)

14. **Lemma 37.** The printed statement (a solution 0 < M < K of N + M^2 = 2K^2 for every admissible N) fails for
    N = 1 and N = 2 (kernel- and computation-checked up to K = 400); our `lemma37_pos` adds "N not a square and
    not twice a square", which matches exactly the failing cases. The descent unit matters here.
15. **Lemma 46.** "N prime implies N = +-1 mod 8" in the printed form; the argument only needs N odd (and
    0 < m < k only to exclude N = 2): `lemma46`.
## Zhang, arXiv 2512.22696

16. **Proposition 6(2), smaller-side count.** Corollary 1 for (a,b,c) = (3,5,7) uses b^2 = 25 (the larger side
    squared, 3575 = 143 * 25), whereas a literal "a > b, smaller side squared" gives (5,3,7) -> 1287. The
    printed trapezoid y = ab(a-b) is consistent with the larger-side reading only after a relabelling. We read
    it as a convention slip; Lean proves the larger-side statement in both orders (`ZhangRat7Swap`).

## Credit
Laczkovich, Beeson, Beeson-Zhang (2604.01314), Zhang. Beeson and Zhang found item 1 before us.
