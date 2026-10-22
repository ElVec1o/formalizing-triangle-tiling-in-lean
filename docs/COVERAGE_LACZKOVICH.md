# Coverage of Laczkovich DM 140 (1995), DCG 19 (1998), DCG 48 (2012), SWW 1991

Labels: every theorem here is NOTE/UNAUDITED by anyone outside the project (see README). Written 2026-10-22; internal working document, lightly cleaned of references to private notes.


# Laczkovich papers -- Lean coverage table v3 (2026-10-22, session: DM 140 Thm 2.3 and Thm 2.6 added; v2 is LACZ_COVERAGE_v2.md, v1 LACZ_COVERAGE.md). NOTE/UNAUDITED. Formalization debt, not progress on any open problem.
Credit: Laczkovich, Beeson, Beeson-Zhang, Snover-Waiveris-Williams, Zhang. Sources: (project working notes, not included) (DCG 48 (2012), DM 140 (1995) `NEW_2026-10-21/..._clean.txt`, DCG 19 (1998), SWW 1991, plus Laczkovich arXiv 2002.12013 (2020) which is also in the room).
Titles (checked from the txt headers): DCG 48 (2012) 330-372 "Tilings of Convex Polygons with Congruent Triangles"; DM 140 (1995) 79-94 "Tilings of triangles"; DCG 19 (1998) 411-425 "Tilings of Polygons with Similar Triangles, II"; SWW, Discrete Math 91 (1991) 193-200 "Rep-tiling for triangles".
All Lean names live in `lean/Erdos634/Draft/` under `Erdos634.Draft.*` (aggregates `AllLacz*.lean`). Axioms of every cited theorem: propext, Classical.choice, Quot.sound only (axiom gate logs `Ax*(project working notes, not included), (project working notes, not included)); no sorry, no native_decide.
Match: F faithful (same statement), S stronger, W weaker, D differs (stated), MISSING = no Lean statement. Audit: "internal" = PAPER_MAP VERIFIED after a statement-match audit inside the project; "NOTE" = NOTE/UNAUDITED. Nothing here was audited outside the project.
Hypotheses are witnessed unless a row says otherwise ("no witness" is stated, never silently skipped).

## A. DCG 48 (2012), "Tilings of Convex Polygons with Congruent Triangles"
| ID | Printed statement (short) | Lean | Match | Witness | Audit |
|---|---|---|---|---|---|
| A-Thm2.1 | regular tiling (p_i = q_i at all vertices) of a convex N-gon by congruent triangles => one of the nine conclusions (i)-(ix) | `RG.theorem21_unconditional : Theorem21` (LaczFormalThm21Final); `Thm21Concl` = 9-fold disjunction `Concl1..Concl9` | F for the REPAIRED theorem: deviations listed in THM21_FIDELITY_2026-10-22_v2.md (printed L7.1(i) false, L6.3 "at most k" -> k-1, (v) q or 1/q and start vertex existential) | `RG.assembly_witness_unc` (rTilingSqrt3); case witnesses `caseIVc_small_witness`, `caseV_Va_witness`, `caseIIIa_witness`, `GenWitK` (IIc generic, 204-tile octagon), `IsoWitM` | NOTE (fresh IIc audit 2026-10-22, fidelity doc; not outside) |
| A-Thm2.1 exist | "each case (i)-(ix) occurs": whenever A and (alpha,beta,gamma) satisfy the conditions, A has a regular tiling (p.334-336; (ix) excepted) | (iv) only via DM140 Thm 3.1 = `thm33_if_rtri_pi3/_2pi3`; (i),(ii),(iii),(v),(vi),(vii),(viii),(ix) MISSING | MISSING for 8 of 9 | -- | -- |
| A-Thm2.2 | non-similar convex non-parallelogram polygons with a regular tiling form a countable set | none | MISSING | -- | -- |
| A-Rem2.3 | irregular tilings: continuum many non-similar convex N-gons (rotated isosceles triangles T_i) | none | MISSING | -- | -- |
| A-Thm2.4 | regular tiling (any of p=q, p=r, q=r) of a convex N-gon by (a,b,c)-triangles => N<=6, or A regular N-gon, or A rational and centrally symmetric, or a,b,c pairwise commensurable | `thm24_2012_csym` (LaczFormal9m; literal `CentSym` = exists c, x in A => 2c-x in A, via `csym_of_equiangular`, LaczFormal9l); earlier weaker `thm24_2012` (LaczFormal9e, central symmetry as side/angle shadow) | F (regular N-gon = all sides and all angles equal; rational = pairwise commensurable sides) | `thm24_witness` (rTilingSqrt3, hypothesis block), `csym_octagon` (regular octagon is `CentSym`), `thm34ii_witness` (octagon tiling) | NOTE |
| A-Thm3.1 | c(A)=infinity iff A is a regular triangle, a parallelogram, or (iii) rational with N-2 angles delta (cos delta rational) and two others integer multiples of pi-delta | none (spectrum cardinality not defined in Lean); ingredient: DM140 Thm 3.1 | MISSING | -- | -- |
| A-Lem3.2 | irregular tiling of convex polygon A by (alpha,beta,gamma) => alpha,beta,gamma in the Q-span of the angles of A | `RG.lemma32_tiling` (PolyTiling, any N, any convex M-gon, reflections), `RG.lemma32_tri` (triangle targets); arithmetic core `lemma32_arith`, `lemma10_min`, `cramer_alpha/beta/gamma`, `lemma32_alg` | F (hypothesis "irregular" = exists idx with p!=q, p!=r, q!=r somewhere) | `witness_lemma32_tri` (isosceles right triangle split by altitude, irregular); `lemma32_alg_witness`; `witness_conclusion` (32d) | NOTE |
| A-Thm3.3 | regular triangle tiled by congruent (a,b,c) iff a permutation satisfies (i) (pi/6,pi/6,2pi/3), (ii) (pi/6,pi/2,pi/3), (iii) gamma in {pi/3,2pi/3} and sines pairwise commensurable | "only if": `thm33_only_if` (Thm33Iii3; uses `equilateral_classification`, `sincomm_irr_family`, `classify_total`, `no_tiling_12/30a/30b`); "if": `thm33_if`, `thm33_iff` (Thm33if5; clause_i, clause_ii, `thm33_if_iii`) | F (both directions, any N, reflections, not edge-to-edge) | clauses (i),(ii) explicit in Thm33if4; N-formula witnesses `equilateral_tile_i/ii/iii_witness`; irrational family `equilateral_tile_irr_witness_60/_120` (N=1440, 1215) | NOTE |
| A-Thm3.4(i) | N not in {3,4,6} => c(R_N) < infinity | none (needs Thm 3.1 + spectrum cardinality) | MISSING | -- | -- |
| A-Thm3.4(ii) | N not in {3,4,6}, regular tiling of R_N => alpha=beta=pi/2-pi/N, gamma=2pi/N | `thm34ii_2012` (LaczFormal9g; from `theorem21_unconditional` + Mathlib `niven` + sine rule; `cos_two_pi_div`, `cos_gamma_rat`, `sin_eq_angle`) | F (R_N = `PolyTiling` with all sides equal and all angles equal; conclusion as `exists sigma, angleAt model (sigma j)`) | `thm34ii_witness`: the real regular octagon `IsoWit.octTiling` (M=8) | NOTE |
| A-Thm3.4(iii) | N>420 and R_N tiled by congruent triangles => angles in list (6) | none (needs [4] forthcoming paper, not in room) | MISSING (cited result [4] not in room) | -- | -- |
| A-Lem3.5 | N not in {3,4,6}: R_N has no tiling by (pi/N,pi/N,pi-2pi/N) | none | MISSING | -- | -- |
| A-Thm3.6 | congruent triangles tile a rectangle => right triangle, side ratio = rational multiple of leg ratio | 'if' half: Draft/LaczFormalCombi1 `thm36_if` (real tilings, witnesses). 'only if' needs [1, Thm 23] (Combinatorica 1990, not in room) | PARTIAL (2026-10-22 Combi1) | -- | -- |
| A-Cor3.7 | square tiled iff gamma=pi/2 and sin alpha/sin beta rational | 'if': Combi1 `cor37_if`; arithmetic of 'only if': Combi2 `cor37_only_if_arith`; geometric 'only if' needs Thm 3.6 (G2) | PARTIAL | -- | -- |
| A-Lem3.8 | rectangle tiled by congruent right triangles => leg ratio rational multiple of side ratio | arithmetic cores cases 2/3, 3/4: Combi2 `lem38_case23`, `lem38_case34`; cases 3/5, 4/5, 4/7 (Niven degrees) and the tiling wiring NOT done; needs Laczkovich Combinatorica 10 (1990) Thm 2 (coordinates in the cot field) -- source not in room; project has `KConj`/`H1gPos.L1` conjugate-dissection machinery for similar purposes | PARTIAL (arithmetic only) | -- | -- |
| A-Lem3.9 | triples (12) (pi/8,5pi/8,pi/4 etc.) cannot tile a rectangle | closing area step only: Combi2 `lem39_area_sqrt2/sqrt3`; coordinates in Q(sqrt2)/Q(sqrt3) + conjugate rectangle tiling need [1, Thm 2] (G1) | PARTIAL (arithmetic only) | -- | -- |
| A-Lem4.1 | parallelogram (gamma, pi-gamma) tiled by (a,b,c)-triangles, one side an integer multiple of a => side ratio rational multiple of sin a/sin b ((i) of Thm 2.1) | `lemma41` (region dissections of `pgramSet`), `lemma41'`, `lemma41_poly` (PolyTiling, M=4) | F | `lemma41_witness`, `lemma41_poly_witness` (unit square) | NOTE |
| A-Lem4.2 | a not a nonneg rational combination of b,c; normal vertex V endpoint of a Gamma_a edge => an edge starts at V | graph layer for real tilings: `Graph.Four` / `RG.Four` ("Lemma 4.2 for real tilings"), `RegFan` local content; consumed by `ga_head_out` | D: no single theorem named `lemma42`; proved as the head/fan analysis for real tilings | no stand-alone witness (exercised inside the Case IVc/V witnesses) | NOTE |
| A-Lem4.3 | (i),(ii),(iii) along a side XY with normal interior vertices and no Gamma_a edge: angle forms, alpha/beta alternation, side multiples | `lemma43_ii` (GraphWalk), `lemma43_back` (GraphBack), `RG` walk rules (R1,R1',R2,R3) + (iii) polygon form (RG11Corner) | F in pieces ((i),(ii),(iii) each stated; (iii) polygon version) | via Thm 2.1 case witnesses | NOTE |
| A-Lem4.4 | Gamma_c analogue of 4.3 (i),(ii) | RG9Side/RG6IVcSmall ("Lemma 4.4 (i), polygon side, Gamma_c", gamma rule along a side) | F in pieces | via case witnesses | NOTE |
| A-Lem4.5 | head of a Gamma_c edge starts an edge (c not a nonneg combination of a,b) | RG5GammaC "Lemma 4.5 real version"; RG7Trans "transition lemma" | F | via case witnesses | NOTE |
| A-Lem4.6 | a,b commensurable, c not rational multiple of a => Gamma_c empty | `RG8Final` (Lemma 4.6, convex polygon, CaseC) | F | the rhombus of `lemma61_witness` (hypotheses of the Case C block) | NOTE |
| A-Lem4.7 | same hypotheses => sides of A pairwise commensurable | RG5GammaC "Lemma 4.7 for a polygon tiling" | F | the rhombus of `lemma61_witness` | NOTE |
| A-Lem4.8 | same hypotheses => c-sides in the interior come in pairs (parallelogram or kite) | `lemma48_pair`, `polytiling_lemma48` (RG10Lemma48), `block_pair` | F | `lemma48_witness` (30-60-90 parallelogram; 2-tile caveat) | NOTE |
| A-Lem6.1 | a,b commensurable, c not: (i) of Thm 2.1 or P=N (all angles alpha+beta) | `RG.lemma61` (RG12L61Final), `lemma61_core` | F | `lemma61_witness` | NOTE |
| A-Lem6.2 | P=N: only parallelograms; no kites unless alpha=beta | `RG.iicNoKites_proved` (WN119-127), isosceles `IIcIso*`, generic `genDiss_noGKite` | F in the IIc setting (hypothesis block = the Case IIc block) | `GenWitK`, `IsoWitM` | NOTE (fresh IIc audit) |
| A-Lem6.3 | P=N => (v), (vi) or (vii) | `lemma63`, `lemma63_one`, `lemma63_two_full`, `lemma63_full` (+ iso versions) | D: "at most k" corrected to k-1; (vi) never output by IIc under h3 (documented) | `lemma63_one_iso_octagon` | NOTE |
| A-Lem7.1 | (i) out-degree = in-degree of Gamma_a, (ii) no edge starts on boundary, (iii) boundary vertices normal (gamma=2pi/3) | printed (i) is FALSE at 3a+3b=pi: `RegFan.printed_L71_330_false`, `BZFlaw`; repaired route `caseIIIa_repaired/_IIIb_repaired` (Beeson-Zhang); equation list `caseIII_exceptional_list` | D (printed claim refuted; repaired theorem proved instead) | counter-instance is the refutation itself | NOTE |
| A-Lem7.2 | Phi(A) = 3d_1 (N=3), 3d_4 (N=4,5), alternating sum (N=6) | FluxPolyPhi3 "Lemma 7.2, N=3/4/5/6" | F | module `LaczFormalFluxPolyPhiWit` | NOTE |
| A-Lem8.1 | (i),(ii),(iii) for Gamma_a u Gamma_k (gamma=pi/3) | `lemma81_i`, `lemma81_ii`, `lemma81_i'`, `lemma81_ii'` (GraphBal/RG), (iii) GraphBdy; weight-free versions | F | no stand-alone witness | NOTE |
| A-Lem9.1 | gamma=pi/2: (i) balance, (ii) no edge from boundary, (iii) a side is an integer multiple of a | `lemma91_i`, `lemma91_ii` (RGBal), (iii) per-edge form RGCorner/RGBdy4 | F for (i),(ii); D for (iii) (per-edge form; the printed "one of the sides" is used inside `thm21_V`) | `caseV_Va_witness` | NOTE |
| A-Sect5-9 | Cases I..V of the proof of Thm 2.1 (Subcases Ia-Id, IIa-IIc, IIIa-c, IVa-c, Va) | `thm21_I`, `caseII_a`, `caseII_b`, `caseII_b_small`, `caseIIIa_repaired`, `caseIIIc_concl`, `caseIII_tri_all`, `caseIV_Va/Vb`, `caseIVc_small`, `caseIVc_concl`, `ivc_rat_final`, `thm21_V` (all sum into Theorem 2.1) | covered by A-Thm2.1 | see A-Thm2.1 | NOTE |

## B. DM 140 (1995), "Tilings of triangles"
| ID | Printed statement (short) | Lean | Match | Witness | Audit |
|---|---|---|---|---|---|
| B-Lem2.1 | Delta rational; polygon dissected into rational triangles similar to Delta => dissected into congruent triangles similar to Delta | `lemma21`, `lemma21_nat`, `lemma21_rat`, `ratio_rat`, `common_denominator` (LaczFormalL21) | S (any region, tiles congruent to scaled Delta) | `lemma21_nat_witness` | NOTE |
| B-Lem2.2(i) | every rational parallelogram (alpha, pi-alpha) is dissected into rational triangles of angles alpha,beta,gamma | `lemma22_i` (RatSimDiss on `parSet`) | F (chart/plane form with rational norms) | none named for (i) (used by `rect_ratSim`) | NOTE |
| B-Lem2.2(ii) | every rational trapezoid with angles beta, alpha+beta, gamma, alpha+beta | `lemma22_ii_plane`, `lemma22_ii_vert` | F (plane and vertex forms) | `wit_ii_plane`, `wit_ii_vert` | NOTE |
| B-Lem2.2(iii) | every rational trapezoid with angles beta,beta,alpha+gamma,alpha+gamma | `lemma22_iii_plane`, `lemma22_iii_vert`, `trap_iii` | F | none named; instance S (beta=pi/3) is `thm31_trapezoid_vert` | NOTE |
| B-Thm2.3 | isosceles (alpha,alpha,pi-2alpha), alpha<pi/3, cos alpha rational => dissected into congruent triangles (alpha,2alpha,pi-3alpha) (Fig. 3) | `thm23_printed` (LaczFormal9u; `HasAngles T alpha alpha (pi-2alpha)` => `PrintedConcl T alpha (2alpha) (pi-3alpha)`), `thm23_any`, `thm23_first` (LaczFormal9t, explicit triangle GFC), `tgt_chart` (9s), `cover` (9o), `tile23` | F (Fig. 3 rendered with pdftoppm from the printed page and read: tiles ABC, BCD, BDE, DEF + isosceles trapezoid GEBA via Lemma 2.2 (iii) + Lemma 2.1; cover is proved by a hull calculus (fan + cevian cuts) in LaczFormal9n, exact for every c=4cos^2 alpha-1>0) | `wit_thm23_first` (k=3/4, tile (4,6,5)) | NOTE |
| B-Thm2.4 | 0<alpha<pi/3, sin(alpha/2) rational, beta=(pi-3alpha)/2, gamma=(pi+alpha)/2; T with angles one of the 5 triples (1) => dissected into congruent triangles (alpha,beta,gamma) | `thm24_printed` (L35Print), `thm24_all_triples`, `thm24_first` (Fig. 4), `thm24_second/third/fourth/fifth(_all, _any)` | F; proof of the 4th triple differs from the printed Fig. 5 (our construction differs from the printed Fig. 5; this is NOT claimed as a printed gap (the point is known from Beeson earlier work)) | `wit24_printed`, `wit_thm24_first_234`, `wit_thm24_first_12716`, `wit_fifth/second/third/fourth_234` | NOTE |
| B-Thm2.5 | alpha<pi/3, sqrt3 sin alpha and cos alpha rational, beta=pi/3-alpha; the 6 triples (2) | `thm25_printed`, `thm25_all_triples`, `thm25_first`, `thm25_t1_any`..`thm25_t6_any` | F | `wit25_printed`, `wit_thm25_first_537/357`, `wit_t1_357`, `wit_t2..t6_*` | NOTE |
| B-Thm2.6 | infinitely many isosceles triangles with c(T) >= 6 | `thm26` (LaczFormal9x): infinite set S of base angles alpha in (0,pi/12) (alpha = 6 arcsin((r^2-3)/(r^2+3)), r rational in (7/4,44/25)), each admitting an isosceles T, and every T with angles (alpha,alpha,pi-2alpha) satisfies `SixShapes T` (`core26`, 9w): six dissections into congruent triangles with the six angle triples (3) of the printed proof (itself, altitude, Thm 2.3, Thm 2.4 (x2: alpha and alpha'=(pi-2alpha)/3), Thm 2.5), pairwise non-permutation (`six_distinct`, 9v) | F for the existence statement (the family is a sub-family of the printed one; c(T)>=6 is stated as six pairwise non-similar shapes, the definition of c(T) of the Introduction; `c(T)` itself as a cardinal is not defined). Difference: pairwise distinctness is proved by comparing the largest entries (needs alpha<pi/12) instead of the irrationality of alpha/pi | `core26` is applied to explicit T from `thm23_first` (inside `thm26`) | NOTE |
| B-Lem3.2 | x,y nonzero rationals, x+2y != 0 != y+2x => a=\|x(x+2y)\|, b=\|y(y+2x)\|, c=x^2+xy+y^2 are the sides of a rational triangle with angle pi/3 or 2pi/3 | `lemma32_dm140` (LaczFormal9a; `RTri` with these sides and `vang R.Delta 2` = pi/3 iff xy(x+2y)(y+2x)>0, 2pi/3 iff <0), `tri_ineq` | F | `lemma32_dm140_witness` (x=-1,y=4: (7,8,13), 2pi/3) | NOTE |
| B-Thm3.1 | rational triangle with an angle pi/3 or 2pi/3 => equilateral triangle dissected into congruent triangles similar to it | `thm33_if_rtri_pi3`, `thm33_if_rtri_2pi3`, `thm31_trapezoid_vert` (the trapezoid S), `thm33_if_of_equi` | F (conclusion as `Thm33If`: equilateral CongruentDissection with the tile's angles) | `thm31_witness_357` (tile (3,5,7), gamma=2pi/3, an equilateral CongruentDissection exists) | NOTE |
| B-Thm3.3 | x,y nonzero integers, x+2y!=0!=y+2x => equilateral triangle dissected into n=\|xy(x+2y)(y+2x)\| k^2 congruent triangles | `dm140_thm33` (LaczFormal9c; via `equi_model`, `equi_n_formula` (side walk + area identity), `dilate_equi`, `heron_rel`): exists k>0, N=\|xy(x+2y)(y+2x)\|*k^2, D : CongruentDissection N equilateral, model sides s(a,b,c) in some order | F | `thm33_witness_11` ((1,1): N=9k^2), `thm33_witness_m14` ((-1,4): (7,8,13)) | NOTE |
| B-Thm3.4 | finite set P of primes => n (count of an equilateral dissection) with every p in P of odd exponent | `dm140_thm34` (LaczFormal9d; x=4q, y=1 as printed; N = 8q(2q+1)(8q+1)k^2) | F | `thm34_witness` (P={2,3}) | NOTE |
| B-Thm4.1 | T dissected into (not nec. congruent) triangles of angles alpha,beta,gamma not all rational multiples of pi => (i)-(vi) | none (needs a vertex-equation layer for non-congruent similar tiles; `RegionDissection` exists, the `cnt`/idx layer is congruent-only) | MISSING | -- | -- |
| B-Thm4.2 | angles of T not all rational multiples of pi => s(T) <= 6 | none | MISSING | -- | -- |
| B-Lem5.2 | 0<a<n, {ka/n}<=1/3 or >=2/3 for all k prime to 2n => n = d n1, n1 in {3,4,6,10} | `lacz_lemma_5_2`, `lacz_lemma_5_2_fract`, `lacz_lemma_5_2_values` | F | `lacz_lemma_5_2_witness` (a=1,n=6) | internal (PAPER_MAP VERIFIED 2026-10-20) |
| B-Thm5.1 | T dissected into triangles (alpha,beta,gamma) rational multiples of pi => (i)-(vii) | congruent-tile version only: `classify_total`, `classify_rational`, `classify_commensurable_final(3)`, `l9_generic`, `l9_uniform`, `table3_comm_total`; kills `tail_iv`, `case_vi`, `case_vii_8`, `case_vii_12_345`, `case_vii_12_138`, `tail_v_arith`; `lacz51_all` (family (alpha,beta,2alpha+beta)), `lacz53_thm` (pi/8 tile) | W: congruent tiles only (Laczkovich's statement is for similar non-congruent pieces) | `classify_final_hyps_witness`, `tail_iv_hyps_individually`, `case_vi_hyps_individually`, `case_vii_hyps_individually` | `tail_iv`, `case_vi`, `lacz_lemma_5_2` internal; rest NOTE |
| B-Thm5.3 | rational angles, T not equilateral => s(T)<=4, c(T)<=2 (c=1 if scalene or isosceles right; c=2 if isosceles neither) | c(T) clause for CONGRUENT tiles: `thm53_c_classify`, `thm53_c_scalene`, `thm53_c_right_isosceles` (LaczFormal9i; from `lemma1b` + `classify_rational`), existence `isosceles_split`, `isosceles_split_tileAngles`, `isosceles_split_not_similar` (altitude split, LaczFormal9j), package `thm53_c_isosceles` (apex-at-2 isosceles, not right, not equilateral: every dissection is by own shape or by the right tile; both occur; not similar) | W: shape/angle form of c(T)=1,2 (no `Set.ncard` of similarity classes; target stated as a `Tri` with apex at vertex 2 for the c=2 clause); the clause s(T)<=4 (non-congruent similar pieces) NOT stated | `thm53_classify_witness`, `thm53_scalene_witness` (one-tile 30-60-90), `thm53_isosceles_witness` (30-30-120 triangle `triso`, base angle pi/6) | NOTE |
| B-Thm5.4 | every dissection of the equilateral triangle into similar triangles has a piece with angle pi/3 or 2pi/3 | `thm54_congruent` (LaczFormal9e): congruent pieces only (from `thm33_only_if`) | W: congruent pieces only (printed: similar, not nec. congruent) | `thm54_witness` (the 4-tile ladder `D_i`) | NOTE |
| B-Intro | s(T), c(T) definitions; simple/abundant; (i) s(T)<=6; (ii) c(T)=6 infinitely often; (iii) c(T)=infinity for equilateral | none (cardinalities) | MISSING | -- | -- |

## C. DCG 19 (1998), "Tilings of Polygons with Similar Triangles, II"
| ID | Printed statement (short) | Lean | Match | Witness | Audit |
|---|---|---|---|---|---|
| C-Prop1 | polygon decomposed into similar symmetric trapezoids => s(A)=infinity | none | MISSING | -- | -- |
| C-Thm2 | s(R_n)=infinity for every n>=3 | none | MISSING | -- | -- |
| C-Thm3 | s_1(A)>0 (regular tiling by some triangle) => an angle delta of A with A decomposed into symmetric trapezoids (delta, pi-delta) | none (Lemmas 6-9, 11-13 missing) | MISSING | -- | -- |
| C-Thm4 | s_2(A) <= c n^6 (irregular tilings) | none | MISSING | -- | -- |
| C-Cor5 | s(A)=infinity => trapezoid decomposition | none | MISSING | -- | -- |
| C-Lem6 | parallelogram (gamma,delta) decomposed into <= 4 trapezoids | none | MISSING | -- | -- |
| C-Lem7 | polygon with angles in {gamma,gamma+pi,delta,delta+pi}, n of each kind => finitely many trapezoids | none | MISSING | -- | -- |
| C-Lem8 | polygon with angles p_i delta + r_i gamma, sum p = sum r => finitely many trapezoids | none (cf. DCG48 Sect. 3 existence use) | MISSING | -- | -- |
| C-Lem9 | at most c n^6 triples (x,y,z) admit a vertex system of the stated form | none | MISSING | -- | -- |
| C-Lem10 | the determinant D_ij is nonzero for some pair (minimal system) | `lemma10_min` (LaczFormal32b, arithmetic form, minimal system, "good" system structure), `coreR0`, `lemma32_arith` (with minimisation) | F in the arithmetic form (hypotheses = the lemma's conditions (i'),(ii),(iii),(iv) as `Good`) | `witness_good` (6-tile split of the equilateral triangle) | NOTE |
| C-Lem11 | i,j>n, min-max/max-min positivity, D_ij=0 => p_i+p_j=q_i+q_j=r_i+r_j | none (needs the minimality-of-N framework) | MISSING | -- | -- |
| C-Lem12 | N>8n+16 and two indices as stated => x,y,z rational, denominator <= max(\|D_ij\|,50) | none | MISSING | -- | -- |
| C-Lem13 | N>120n => x,y,z rational, denominator <= 2100 | none | MISSING | -- | -- |

## D. Snover-Waiveris-Williams, Discrete Math 91 (1991), "Rep-tiling for triangles"
| ID | Printed statement (short) | Lean | Match | Witness | Audit |
|---|---|---|---|---|---|
| D-Lem1 | alpha rational multiple of pi and cos/sin/tan alpha rational => alpha = 0, pi/6, pi/4 or pi/3 mod pi/2 | `sww_lemma1` (LaczFormal9h; `SWWAngle`, via Mathlib `niven`; tan is Lean's sin/cos, junk value 0 at cos=0 is consistent with the conclusion) | F | `sww_lemma1_witness` (pi/3), `sww_control` (arithmetic control only) | NOTE |
| D-Lem2,3 | packing equations: e,i nonzero or f,h nonzero; i=0 => ... | internal to the SWW packing route; Lean uses a different route (Row2 chain + Niven) | D (not stated; not needed) | -- | -- |
| D-Lem4 | n-tiled, x rational => n = k^2 or k^2+l^2 | subsumed by `reptile_SWW` | S-part (the three cases at once) | `sww_*` witnesses | NOTE |
| D-Lem5 | n-tiled, y rational => n = k^2 or 3k^2 | subsumed by `reptile_SWW` | S-part | same | NOTE |
| D-Lem6,7 | n,x,y irrational => n = k^2 (sign pattern of Ra, Ir) | subsumed by `reptile_SWW` (`similar_reptile`, `kill_30_30_120`, `thirty_arith`) | S-part | same | NOTE |
| D-Main (Golomb conjecture) | triangle n-tiled by congruent triangles similar to it => n = k^2, 3k^2 or k^2+l^2 | `LaczFormal.reptile_SWW` (LaczFormalT6): any N, reflections allowed, not edge-to-edge: IsSquare N, or N=A^2+B^2 with right tile legs A:B, or N=3m^2 with the 30-60-90 tile | F (a sharper statement than SWW's list since it gives the tile) | `sww_sumsq_exists` (all A,B), `sww_three_exists`, `sww_sumsq_N5/N13/N10`, `sww_three_N12/N27`, `sww_N5_area`, `D_i_similar` | NOTE (PAPER_MAP "Reptile theorem") |
| D-Cor1 | the set of integers n with no n-tiled triangle is infinite | `sww_cor1` (LaczFormal9h): `Set.Infinite {n \| not exists D : CongruentDissection n, SimilarTM D}`; family n=8m+7 from `reptile_SWW` (printed proof uses Lagrange's three-square theorem) | F (statement); proof differs | follows from `reptile_SWW` witnesses being the only n | NOTE |
| D-Cor2 | (k^2+l^2)-tiled non-square => right triangle | in `reptile_SWW` second alternative | F | `sww_sumsq_N5` | NOTE |
| D-Cor3 | 3k^2-tiled => 30-60-90 | in `reptile_SWW` third alternative | F | `sww_three_N12` | NOTE |
| D-Cor4 | for any n a triangle tiled with n pieces similar to it (not nec. congruent) | none | MISSING | -- | -- |

## E. Cited, not in the room as numbered statements here
| ID | Statement | Lean |
|---|---|---|
| E-Lacz1990 Thm 2 | vertices of a tiling by similar triangles have coordinates in the field generated by the cotangents | not stated; conjugate-dissection machinery `KConj.lemmaK`, `H1gPos.conj_congruentDissection_subfield` (Laczkovich's method) is in Lean for other uses. Source (Combinatorica 10 (1990)) not in the room |
| E-Niven [Irr. Numbers] Cor 3.12, Thm 3.9 | rational cosines; degree of cos(pi/N) | Mathlib `Real.niven` covers 3.12; 3.9 (degree phi(2N)/2) not stated |
| E-Beeson-Zhang, Beeson-Rosu | not Laczkovich; see `BZ_ROWS_2026-10-22.md`, `ZHANG_COVERAGE.md` | -- |

## F. Laczkovich arXiv 2002.12013 (2020), "Irregular tilings of regular polygons with similar triangles" (in the room; not part of the requested three)
| ID | Statement | Lean | Match |
|---|---|---|---|
| F-Thm1 | triangle tiling R_N, N>=25, N!=30,42, rational angles => (i),(ii),(iii) | none | MISSING |
| F-Thm2..6 | vertex counts, equal equations, alpha=delta_N etc. | none (only Condition (E) pieces: `vertex_group`, `sum_cnt`, `exists_idx_general`, `fiber_sum_P`, `conj_interior_sum`, CondE kills) | MISSING (pieces in Lean) |
| F-Thm7, Cor8 | irregular tiling of R_N (N>10) exists iff angles rational; <= 3 triangles for N>42 | none | MISSING |
| F-Lem9 | Condition (K)/(E) for R_N | `KConj.lemmaK` (general), not the R_N form | W |
| F-Lem11..13, Prop14, Lem15 | number-theoretic lemmas (prime-to-nN residues) | none | MISSING |

## Changes since v1 (session, 2026-10-22; files `Draft/LaczFormal9a..9m`, aggregate `Draft/AllLaczCoverage`; commits 6009d1f8 .. d5b917f0)
| module | new theorem(s) | row moved |
|---|---|---|
| 9a | `lemma32_dm140`, `lemma32_dm140_witness`, `thm31_witness_357` | B-Lem3.2 MISSING -> F; B-Thm3.1 gets a witness |
| 9b, 9c | `equi_count`, `equi_model`, `equi_n_formula`, `dilate_equi`, `dm140_thm33` | B-Thm3.3 MISSING -> F |
| 9d | `dm140_thm34` | B-Thm3.4 MISSING -> F |
| 9e | `thm54_congruent`, `thm24_2012` (shadow of central symmetry), `sides_of_sinComm` | B-Thm5.4 MISSING -> W; A-Thm2.4 MISSING -> (superseded by 9m) |
| 9g | `thm34ii_2012`, `cos_two_pi_div`, `cos_gamma_rat`, `sin_eq_angle` | A-Thm3.4(ii) MISSING -> F |
| 9h | `sww_lemma1` (+`swwAngle_*`), `sww_cor1` | D-Lem1, D-Cor1 MISSING -> F |
| 9i, 9j, 9k | `thm53_c_classify`, `thm53_c_scalene`, `thm53_c_right_isosceles`, `isosceles_split(_tileAngles, _angles, _not_similar)`, `thm53_c_isosceles`, witnesses | B-Thm5.3: W (angle/shape form of the c(T) clause) |
| 9l, 9m | `next_edge`, `edge_iter`, `edge_opposite`, `sum_const`, `csym_of_equiangular`, `thm24_2012_csym`, `csym_octagon` | A-Thm2.4 -> F (literal central symmetry) |
| 9f | witnesses `thm54_witness`, `thm33_witness_11/_m14`, `thm34_witness`, `thm24_witness`, `thm34ii_witness` | non-vacuity |
Axioms of all 35 new theorems/witnesses: propext, Classical.choice, Quot.sound only (`AxCoverage_2026-10-22.out.txt`, 35 `#print axioms`, 0 `sorryAx`); no `sorry`, no `native_decide` in `LaczFormal9*.lean`. Builds via (project working notes, not included) (session), `AllLaczCoverage` OK.

## Census v2/v3 (v2 numbers follow; v3 = v2 with B-Thm2.3 and B-Thm2.6 MISSING -> F; claim rows of sections A-D; the aggregate row A-Sect5-9 is counted under A-Thm2.1)
v3 (this file): F 35, S 4, W 3, D 4, MISSING 27. By paper: DCG 48 (2012): F 17, D 3, MISSING 11; DM 140 (1995): F 12, S 1, W 3, MISSING 3; DCG 19 (1998): F 1, MISSING 12; SWW (1991): F 5, S 3, D 1, MISSING 1.
v1 had F 26, S 4, W 2, D 4, MISSING 37 for the same rows (74 rows incl. the aggregate). Nothing here was audited outside the project; "F" means the Lean statement matches the printed statement as read by the author of the file (PAPER_MAP-style internal audit only for the rows marked internal), not that a fresh reader checked it.
Hypothesis witnesses still absent (rows marked "no stand-alone witness"): A-Lem4.2, A-Lem8.1, B-Lem2.2(i),(iii); Thm 3.6-type rows do not exist. The hypotheses of `thm34ii_2012` ARE witnessed (octagon).

## HONEST MISSING LIST (with the exact gap)
A. DCG 48 (2012)
1. Thm 2.1 existence part (i)(ii)(iii)(v)(vi)(vii)(viii)(ix) (p.334-336). Only (iv) (= DM140 Thm 3.1) and the single regular octagon (vii, M=8: `IsoWit.octTiling`) exist. Gap: a `PolyTiling` for each family: (ii)/(iii) use DCG19 Lemma 8 ("rational symmetric trapezoids", MISSING), (vii) needs a `ConvPoly` for every regular M-gon (trig strictness of `left`) plus cover/disjoint proofs of the centre split.
2. Thm 2.2 (countability) and Rem 2.3: no type of similarity classes of convex polygons; Rem 2.3 needs the rotated-isosceles fan to be a convex M-gon.
3. Thm 3.1, Thm 3.4(i),(iii): `c(A)` (cardinality of the spectrum) is not defined in Lean; (iii) cites "[4]" (forthcoming, not in the room).
4. Lemma 3.5: the proof says "By Theorem 3.9 of [5], the degree of cos alpha = cos(pi/N) is phi(2N)/2" (Niven-Zuckerman-Montgomery, not in Mathlib as such).
5. Thm 3.6, Cor 3.7, Lemma 3.8, Lemma 3.9: need Laczkovich Combinatorica 10 (1990) Thm 2, cited as "[1, Theorem 2]: the coordinates of the vertices of the triangles belong to Q(sqrt2)" (source not in the room; the project has the conjugate-dissection machinery `KConj`, not that statement).
B. DM 140 (1995)
6. (CLOSED in v3) Thm 2.3 and Thm 2.6: Fig. 3 was rendered from the page and read; see rows B-Thm2.3, B-Thm2.6.
7. Thm 4.1, Thm 4.2, Thm 5.1 (similar, not nec. congruent, pieces), Thm 5.3 (s(T) <= 4 clause) and the Introduction's s(T), c(T) cardinalities: the vertex-equation layer (`cnt`, `idx`, `KConj`) is for `CongruentRegionDissection`; the proof of Thm 4.1 counts "exactly N alphas, N betas and N gammas" over non-congruent pieces. Needs a similar-pieces dissection layer.
C. DCG 19 (1998)
8. Prop 1, Thm 2, Thm 3, Thm 4, Cor 5, Lemmas 6-9: symmetric trapezoids (not defined in Lean), the trapezoid decompositions, the count c n^6.
9. Lemmas 11-13: arithmetic of the minimal system. Lemma 11's proof ends "...but the value of N is reduced", i.e. it needs N minimal among ALL systems for the triple (x,y,z); `Good` (LaczFormal32b) has no such minimality predicate. Lemma 12, 13: depend on Lemma 11 and 8n+16 / 120n case analyses.
D. SWW (1991)
10. Cor 4 (for any n a triangle tiled by n pieces similar to it, not nec. congruent): needs non-congruent similar pieces (as item 7).
E. 2020 arXiv paper (in the room, not requested): Thm 1-8 and Lemmas 9, 11-13, Prop 14, Lem 15 MISSING except the Condition (E) pieces listed in F of v1.

## Statement-match notes for the new theorems (honest)
* `dm140_thm33`: the printed theorem says the equilateral triangle "can be dissected into n congruent triangles"; Lean also records that the tile is similar to the triangle of Lemma 3.2 (model sides `s(a,b,c)` in some order). `k` is produced, not chosen.
* `thm24_2012_csym`: "regular N-gon" = all sides equal and all interior angles equal (ConvPoly, strictly convex); "rational" = pairwise commensurable sides (Laczkovich's definition); regularity of the tiling is existential over `idx` and the three alternatives.
* `thm34ii_2012`: regular polygon hypothesis as above; conclusion is an unordered triple (`exists sigma`).
* `thm54_congruent`, `thm53_c_*`: congruent tiles only (see B rows).
* `sww_cor1`: n = 8m+7 only (an infinite subset), same statement as the printed corollary.
* Not added to `lean/PAPER_MAP.md` (batch rows pending; the user's ordering was the coverage table and Lean files).

## Changes in v3 (session, 2026-10-22; files `Draft/LaczFormal9n..9x`, aggregate `Draft/AllLaczCoverage` now imports 9u and 9x; commits 1cdbdf90, 5f45c9b6, c6cbef18, 63d47503 and the aggregate commit)
| module | content |
|---|---|
| 9n | hull calculus `H P Q R` (convex combinations of three points): `H_fan` (cut from an interior point), `H_cev` (cut at a side point), `H_sub_convex`, `tri_sub_H` |
| 9o | Fig. 3 in the chart (G; GE, GA): `n=c^2+1`, `h=c^2+c+1`, B=(c^2/n,1), C=(0,h), F=(h/n,0), D=((c+1)/n,c^2), Q=BF cap DE; exact target `{x,y>=0, n x+y<=h}`; `cover` (target = trapezoid + ABC + BCD + BDE + DEF) |
| 9p, 9q | pieces inside the target; exact vertex values on the five separating lines; the ten pairwise interior-disjointness facts |
| 9r | the four tiles are similar to Delta (ratios 1, 1/c, 1/(2kc), 1/(2k), exact `field_simp; ring` identities, `chart_tile`) |
| 9s | trapezoid GEBA = `trap_iii` for `R.sw01`, chart assembly `tgt_chart` (`ChartRSD`) |
| 9t | `thm23_first`: explicit triangle GFC is a `CongruentRegionDissection` into copies of `scaleTri (1/q) Delta`; angles `alpha` at both base vertices |
| 9u | `thm23_any`, `tile23`, `thm23_printed`, `wit_tile_456`, `wit_thm23_first` |
| 9v | `six_distinct` (triples (3) of Thm 2.6 pairwise non-permutations for 0<alpha<pi/12) |
| 9w | `core26`, `SixShapes`, rationality of cos 6x, sin 3x, sin(alpha'/2), sqrt3 sin 6x |
| 9x | `thm26` (infinite family via arcsin of a rational parameter) |
All new theorems depend only on propext, Classical.choice, Quot.sound (`#print axioms` at the end of each file, logs (project working notes, not included)). No `sorry`, no `native_decide`. Builds via (project working notes, not included) (session, one module at a time).

## DCG 48 (2012) rows assigned to this lane and NOT closed (exact gaps; nothing was claimed)
* A-Thm2.1 existence, case by case (printed p.334-336): (i) parallelogram: needs a `PolyTiling` (ConvPoly of the parallelogram, 2pq congruent cells split by a diagonal, `RegularPQ` with the idx counting at every lattice point); pieces exist only as `RatSimDiss` (`lemma22_i`, `rect_ratSim`), not as a `PolyTiling`. (ii)/(iii): the printed proof says "Now it can be shown by induction on N that under these conditions A can be decomposed into finitely many nonoverlapping rational symmetric trapezoids ... (See also Lemma 8 of [3] ...)": DCG19 Lemma 8 is MISSING. (iv) done (DM140 Thm 3.1). (v): the fan from E over the polygon, `W` and `W'`, the parallelogram `W'V0WVk` by (i): needs (i) and general centrally symmetric 2k-gons as `ConvPoly`. (vi): three parallelograms, needs (i). (vii): regular M-gon centre split: only M=8 exists (`IsoWit.octTiling`); general M needs trig strictness of `left` and the sector cover/separation (the plan is in this file's design notes; not built). (viii)/(ix): "A can be decomposed into congruent regular triangles" for rational polygons with angles pi/3, 2pi/3: lattice decomposition not formalized.
* A-Thm2.2: printed proof "the set of non-similar rational triangles is countable ... From this observation it is clear that ..." needs a type of similarity classes of convex polygons and the reconstruction of a polygon from (angles, side ratios); not defined in Lean.
* A-Rem2.3: needs `ConvPoly` of the fan polygon `X, Y_0..Y_{N-2}` (trig strictness), the tiling by the rotated triangles T_i, irregularity of that tiling for all three alternatives (p=q, p=r, q=r) and an injective similarity invariant of the polygons.
* A-Lem3.5: printed proof "However, by Theorem 3.9 of [5], the degree of cos alpha = cos(pi/N) is phi(2N)/2": not in Mathlib; also needs the area comparison for a tiling of R_N.
* A-Thm3.1, A-Thm3.4(i): `c(A)` as a cardinal is not defined; the 'only if' direction of Thm 3.1 uses DCG19 Thm 4 (s_2(A) <= c n^6, row C-Thm4, MISSING) for irregular tilings; 3.4(i) is Thm 3.1 + Niven (cos(2pi/N) rational => N in {3,4,6}) and so is blocked by it.
* A-Thm3.4(iii): "(iii) If N > 420, then c(R_N) = 2" cites "[4]" (forthcoming, not in the room).

