# Coverage of Zhang (arXiv 2512.22696)

Labels: every theorem here is NOTE/UNAUDITED by anyone outside the project (see README). Written 2026-10-22; internal working document, lightly cleaned of references to private notes.


# Zhang arXiv 2512.22696v4 -- coverage v5 (2026-10-22, session). NOTE/UNAUDITED. Credit Zhang, Beeson-Zhang (2604.01314), Beeson (1206.2229v4 Thm 9, Lemmas 1, 11; 1206.1974v7 Thm 10.7), Laczkovich (Discrete Math 140 Thms 5.1, 5.3; DCG 48).
New modules (all in AllBeeson, built via the build script, axioms propext/choice/Quot.sound only):
- `Draft/ZhangRat10Thm9.lean`: `beeson_thm9` (printed Thm 9: tile angles (alpha,beta,2alpha+beta), 3a+2b=pi, target not AAA-similar => sides rational) with NO irrationality hypothesis: H1 from `BeesonH1.lemma1_unconditional`
  (Laczkovich 5.1/5.3), five shapes from `lemma11`, sides from Rows 11-15 (`zhang_thm1_beeson3`). `beeson_thm9_printed`: literal form (alpha, beta at some vertices, `not SimilarTM`, all side ratios `Comm`).
  `zhang_thm1_beeson3_unc`: Zhang's Beeson-III rows without `alpha not in Q pi` (needs "not similar" instead; the printed Thm 9 hypothesis).
- `Draft/ZhangRat10Thm9Wit.lean`: witness `beeson_thm9_wit` = certified 44-tiling (target (beta,beta,3alpha), AAA non-similarity proved).
- `Draft/ZhangRat10Wit107.lean`: M2 CLOSED. `beeson_thm107_tri_wit`: the Herdt 1125-tiling (G3GControl.D) is an isosceles TRIANGLE target (angles alpha,alpha,pi-2alpha, cos alpha=3/4), model relabelled to (alpha,pi-3alpha,2alpha); all hypotheses of `beeson_thm107_tri` hold and its conclusion is obtained. Row (a,a,pi-2a)/gamma=2a is NOT vacuous.
- `Draft/ZhangRat10Order.lean`: G2 CLOSED for Lemma 5: `zhang_lemma5_geom_any` (target angles (2a,2b,a+b) at the target vertices in any of the 6 orders, via `relabelTarget'`). Lemma 3 (equilateral target) has no vertex order.

## M1 status
CLOSED in the printed form: Zhang's "Theorem 3 of [2]" = Beeson v4 Thm 9 is now a Lean theorem without the irrationality hypothesis, with the printed hypothesis "not similar". Reading of "T is rational" = all side ratios rational (`Comm`).
Caveat: AAA non-similarity vs. SimilarTM bridged in `notTriple3_of_not_similar`; `beeson_thm9_printed` uses the latter. Beeson's Corollary 2 (rank L = 2) not formalized (not used by Zhang).

## G1 (note, no Lean): Prop 6(2) smaller-side count
Zhang Prop 6 / Thm 7 print the second tiling with m^2(a+b)... counts; Cor 1 for (a,b,c)=(3,5,7) uses b^2=25 (the LARGER side squared, 3575 = 143*25), while a literal "a>b, smaller side squared" gives (5,3,7)->1287. The printed proof's trapezoid y=ab(a-b) (a>b) is consistent with the larger-side reading only under a relabelling. Verdict: almost surely a printed typo/convention slip (Cor 1 and Lean agree on larger side). Lean covers the larger-side statement (ZhangRat7Swap, both orders). Not a missing theorem; the literal smaller-side count is a different, unproved tiling, not claimed.

## G4: Table 1 and Prop 11
Table 1 (paper, Sec. 5) is captioned "Constructions for all the tilings using (a,b,c) = (3,5,7) for all but the last row and (5,8,7) for the last row": a demonstration of the general results for two specific tiles, with counts such as 3m^2(a+2b)(a+b), m in 5N0+7N0, and 1440 "known". "Instance-level" = the table lists these two tiles only; the paper states no general theorem for the rows beyond Props 3, 6, 9 and Thm 7 (in Lean). So the table is not a missing general statement. Prop 11 ("if the ((a+2b)am,(b+2a)bm,c^2m) triangle tiles into (a,b,c) then ...") is general; Lean has its derived form (ZhangRat4Prop11Derived) with the extra hypothesis m' in <max(A,B),C>; that is a (small) mismatch, kept below.

## Final Missing list
1. Prop 11 general form without the semigroup hypothesis `m' in <max(A,B),C>` (ZhangRat4Prop11Derived); check printed proof for whether the hypothesis is implicit.
2. `beeson_thm107_proved` (Beeson Thm 10.7) and Row 11-15 colouring/flux rationality are internally audited only; no outside check. Lemma 1/Thm 9 depend on `lacz51_all`/`lacz53_thm` (project re-proofs of Laczkovich 5.1/5.3; unaudited, no outside check).
3. Beeson Cor 2 (rank L = 2) not formalized (unused by Zhang). Zhang's Conjectures 1-5: open, nothing to prove. Table 1: examples, not a theorem.
4. G1: literal smaller-side count of Prop 6(2): printed typo, unproved as stated.
Closed this pass: M1 (hypothesis-free Thm 9), M2 (witness), G2 (Lemma 5 any order), G1/G4 (notes).

