# Beeson-Zhang (arXiv 2604.01314, 2604.03609): row-by-row status

Labels: every theorem here is NOTE/UNAUDITED by anyone outside the project (see README). Written 2026-10-22; internal working document, lightly cleaned of references to private notes.


# Beeson-Zhang Thm 1.1 / 1.2: every row, Lean status (session, 2026-10-22). NOTE, UNAUDITED.
Sources: arXiv 2604.01314v1 (BZ), text at (project working notes, not included) (Thm 1.1 line 42, Thm 1.2 line 89, Table 1 line 57, Table 5 line 716, Thm 3.7 line 431, proof of 1.1 line 694).
Credit: Beeson-Zhang, Laczkovich (DCG 48 (2012); Discrete Math 140 (1995)), Beeson.
(arXiv 2604.03609 = Beeson-Laczkovich-Zhang "Erdos 633"; it contains no row of BZ Thm 1.1/1.2, only uses them.)

## Thm 1.1 (as printed)
Triangle ABC tiled by a tile (a,b,c), angles (alpha,beta,gamma=2pi/3) NONcommensurable (alpha not in Q pi). If ABC is not similar to the tile, a,b,c are pairwise commensurable.
The statement quantifies over ALL triangles ABC. The printed proof is: Thm 3.7 (Lemmas 3.4, 3.5, 3.6) leaves exactly two exceptional targets, equilateral (Thm 5.2) and (2alpha,2beta,pi/3) (Thm 5.3).
Table 1 lists which targets can occur at all (consequence of Laczkovich Thm 4.1 of the 1995 paper); the gamma = 2pi/3 rows are the six below.

| # | target ABC (angles) | tile | BZ citation | Lean status | file / theorem |
|---|---|---|---|---|---|
| 1 | equilateral | gamma=2pi/3 | Thm 5.2 | DONE, any N, reflections, not edge-to-edge | BZ6 `bz_thm52`; BZL7a `bz_L7_triangle` (via thm21_partial4); witness BZL7b/BZWit (N=1215) |
| 2 | (2alpha, 2beta, pi/3) | gamma=2pi/3 | Thm 5.3 | DONE | BZL7c7 `bz_thm53`; witness BZL7c8 `witness_143` |
| 3 | (alpha, alpha, pi-2alpha) | gamma=2pi/3 | Thm 3.7 | DONE (2026-10-22, UNAUDITED), not witnessed (no tiling known) | BZL7d6 `bz_thm11` |
| 4 | (alpha, 2alpha, pi-3alpha) | gamma=2pi/3 | Thm 3.7 | DONE, not witnessed | `bz_thm11` |
| 5 | (alpha, 2beta, 2alpha+beta) | gamma=2pi/3 | Thm 3.7 | DONE, not witnessed | `bz_thm11` |
| 6 | (alpha, alpha+beta, alpha+2beta) | gamma=2pi/3 | Thm 3.7 | DONE, not witnessed | `bz_thm11` |
| 7 | any other ABC not similar to the tile (Thm 1.1 as stated) | gamma=2pi/3 | Thm 3.7 | DONE for every triangle with NotSim (rows 1-7 at once) | BZL7d6 `bz_thm11` (witnesses d7 at rows 1, 2 only) |
| 8 | ABC similar to the tile | | excluded by hypothesis | n/a | |
| 9 | alpha in Q pi (commensurable angles) | | NOT in BZ (they cite Laczkovich 1995 Thms 5.1, 5.3 "mostly settled") | MISSING; L9 blocked on Combinatorica 1990 source, see (project working notes, not included) | |

Lean status of the pieces of Thm 3.7:
| piece | statement | Lean |
|---|---|---|
| Tab. 2 vertex types | inside interior / sides | BZ2 `vertex_type`, BZL7c1 `vertex_type_gen` (corners pi/3, 2alpha, 2beta only) |
| Lemma 3.2, centre case | head analysis, centre out-degree | BZ3 `bz_head_analysis`, `bz_center_out` DONE (any corners) |
| Lemma 3.5 | no NotComb a b c | BZ4 (equilateral), BZL7c2 (special corners), BZL7d1/d3 `bz_lemma35_gen2`, `bz_lemma35_notsim` (ANY triangle not similar): DONE |
| Lemma 3.6 | two combs => Comm a b | BZ5/BZ6 `comm_of_two_combs` DONE; `bz_ab_comm_row` (BZL7c3) for the special corner set |
| Lemma 3.4 | no c-relation => boundary all c | DONE in the form `sides_all_c` (BZL7d4a/d4b); the printed second half (ABC special) is replaced by the flux contradiction `bz_allc_false` (d6), valid for every sign pattern |
| Thm 3.7 / Thm 1.1 | assembly | DONE `bz_thm11` (BZL7d6), UNAUDITED; AllLaczBZL7 aggregates d1-d7 |
| Lemma 3.1 (c-link at pi-vertex) | | not needed by the design below (uses the CaseG uniform-sides lemma instead) |

## Thm 1.2 (Table 5)
R not similar to ABC, not a right triangle, angles not all in Q pi => sides commensurable.
| ABC | tile | cited proof | Lean status |
|---|---|---|---|
| equilateral | alpha=pi/3 | Laczkovich 2012 Lemma 3.2, Thm 3.3 | DONE `E60Irr.sixty_commensurable`; Thm 3.3 iff: Draft/LaczFormalThm33if* (AllLaczThm33) |
| equilateral | gamma=2pi/3 | BZ Thm 1.1 | DONE (row 1) |
| (2alpha,2beta,pi/3) | gamma=2pi/3 | BZ Thm 1.1 | DONE (row 2) |
| (alpha,alpha,pi-2alpha) | gamma=2alpha | Beeson arXiv:1206.1974 Thm 10.5 | MISSING; source not in the room (B3 of (project working notes, not included)) |
| (2alpha,beta,alpha+beta) | 3alpha+2beta=pi | Beeson III (1206.2229) Thm 3 | DONE: Row11-Row15 (FluxDRow11, FluxFRow15AnyLabel, PAPER_MAP rows D2-row15, D3/D5) |
| (2alpha,alpha,2beta) | 3alpha+2beta=pi | same | DONE (Row15) |
| isosceles | 3alpha+2beta=pi | same | DONE (Row11/12/13) |
Note: Table 1 rows (alpha,alpha,pi-2alpha),(alpha,2alpha,pi-3alpha),(alpha,2beta,2alpha+beta),(alpha,alpha+beta,alpha+2beta) with gamma=2pi/3 do not appear in Table 5 (they do not meet "not a right triangle ... " wait they do: they are covered by "Theorem 1.1 of this paper" in the text of the proof but Table 5 prints only the two gamma=2pi/3 rows equilateral and (2alpha,2beta,pi/3); BZ's proof of Thm 1.2 therefore silently uses Thm 3.7 for the other four, or Table 1 is not exhaustive for them. Quoted: Table 5 lists "equilateral gamma=2pi/3" and "(2alpha,2beta,pi/3) gamma=2pi/3" only.)

## Designs for the missing rows (10 lines each)

### D1. Lemma 3.5 + 3.6 for ANY triangle not similar to the tile  => Comm a b  (BZL7d1, d2)
1. Generalise `vertex_type_gen` (BZL7c1) by replacing `hPang` by `hcorn : forall k, cnt D idx (P.v (k+1)) 2 = 0` (no gamma at polygon corners). Non-corner part of the proof is unchanged (vertex_A).
2. Generalise `bz_lemma35_gen` (BZL7c2): in-degree 0 at polygon vertices uses only P.angle < pi (head angle sum = pi); look up the ConvPoly lemma giving angle < pi.
3. The corner term: f(corner) = 6 out + cnt0 + cnt1 >= 1 because Asum > 0 and cnt2 = 0, so some tile angle (alpha or beta) is at the corner. One corner suffices for the strict inequality (sum f = 0 forces all f = 0).
4. Discharge `hcorn` for a triangle target NOT similar to the tile: sum of corner angles = pi => T0 alpha + T1 beta + T2 gamma = pi (T_l = total count of corner type l over the 3 corners) => T0 = T1, T1 + 2 T2 = 3 (irrr_coeff); T2 = 1 forces T=(1,1,1) and (each corner has >= 1 angle) one angle per corner, so ABC has angles {alpha,beta,gamma} = similar. Needs a hypothesis NotSim D.target model.
5. Rewrite `bz_lemma35_row` / `bz_ab_comm_row` (BZL7c3) with `NotSim` in place of hT. Re-use `exists_convpoly_of_tri`, `tpt_swap`, `comm_of_two_combs`.
6. Witness: the 1215-tiling (equilateral, NotSim) and the 143-tiling target (2alpha,pi/3,2beta) (NotSim) both satisfy it; no tiling is known for the other rows, stated as such.

### D2. Lemma 3.4: no c-relation => ABC in {equilateral, (pi/3,2alpha,2beta)}   (BZL7d3-d6)
1. Hypothesis `NotComb c b a` (no c-relation). Build `CaseG (relabelC D) (relabelCIdx idx)` DIRECTLY (not `CaseC`, whose `hregc` fails at non-regular corners): hidx, hidxA, hnc as in CaseC.caseG; HalfPar of the relabelled model only at points of angle sum pi, where alpha irrational gives cnt0 = cnt1 (irr_coeff).
2. Copy the first half of `polygon_sides_alike` (RG5GammaC:194): `walk_status_chain` gives, for each side i of the triangle, every boundary tile edge has the c-status of the first edge (all c or no c per side). No corner step (that is where `corner_c_status` needs regular corners).
3. A side with no c-edge is impossible: each of its n tiles has an a- or b-edge on the side, hence its gamma vertex on that edge; a vertex interior to the side has angle sum pi so at most one gamma; no gamma at a corner (hcorn, step D1.4). n tiles inject into the n-1 interior vertices. Contradiction.
4. So every boundary tile edge of every side is a c-edge. At a corner, the first edge of side i and the last edge of side i-1 are c-edges of two DISTINCT tiles (a tile has one c-edge), so >= 2 tiles per corner; totals T0 = T1 = 3, T2 = 0 force exactly 2 per corner: corner types {2alpha, 2beta, alpha+beta}; counting gives n_ab odd in {1,3}: (pi/3,2alpha,2beta) or equilateral.
5. Output: `bz_lemma34 : NotComb c b a -> (equilateral) \/ (angles (2alpha,pi/3,2beta) at some permutation)`.

### D3. Thm 3.7 and Thm 1.1 for ABC not similar to the tile   (BZL7d7)
1. `Comm a b` from D1.
2. `by_cases NotComb c b a`: if not, c-relation r c = p b + q a (r > 0) with Comm a b gives Comm a c (rational arithmetic, `comm_comb`-style).
3. If NotComb c b a: D2 gives equilateral (-> `bz_thm52`) or the (2alpha,pi/3,2beta) shape (-> `bz_thm53` with the permutation).
4. Statement `bz_thm11`: D : CongruentDissection N, h : TwoPiThreeData alpha a b c, alpha not in Q pi, NotSim target model  ==> Comm a b /\ Comm a c. Covers rows 1-7 at once.
5. Honest limits: rows 3-6 are hypothetically empty (no tiling known); witness only at rows 1, 2.

### D4. Thm 1.2 rows without Lean: (alpha,alpha,pi-2alpha) with gamma=2alpha
Cited proof Beeson arXiv:1206.1974 Thm 10.5 (not in the room). Cannot design from the available sources; needs the source (blocker B3).

### D5. alpha in Q pi (commensurable angles)  - outside BZ. Laczkovich 1995 Thms 5.1, 5.3; blocker as in (project working notes, not included) (Combinatorica 1990 lemmas); Lean has a conjugate-tiling theory (H1hCT) per (project working notes, not included) batch 6 correction; not designed here.

## UPDATE 2026-10-22 (session, later): rows 3-6 are WITNESSED
| 3 | (alpha,alpha,pi-2alpha), gamma=2pi/3 | N = 5265, tile (3,5,7), Zhang Prop 8(1) | BZL7i2 `witness_row3` |
| 4 | (alpha,2alpha,pi-3alpha) | N = 7800, Zhang Prop 11(1) | BZL7i4 `witness_row4` |
| 5 | (alpha,2beta,2alpha+beta) | N = 7128, Zhang Prop 10(1) | BZL7i3 `witness_row5` |
| 6 | (alpha,alpha+beta,alpha+2beta) | N = 3240, Zhang Prop 9(1) | BZL7i2 `witness_row6` |
Row 9 (alpha in Q pi): `bz_rational_classify` (BZL7j3) for Covered3 denominators: alpha = pi/6 and equilateral target; `witness_30_30_120` (BZL7j4): Thm 1.1's conclusion is false there (sides 1,1,sqrt 3), so the hypothesis cannot be dropped.
Polygon targets: BZL7j1/j2 (Comm a b for every convex polygon without gamma corner; balanced corners => Thm 2.1); gap for M >= 4 with unbalanced corners and c incommensurable quoted in the Lean file headers.

