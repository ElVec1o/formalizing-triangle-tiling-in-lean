# Formalizing triangle tiling in Lean

Author: Vico Bonfioli. Version 1.0.

A Lean 4 / Mathlib formalization of results on tilings of polygons and triangles by congruent (and similar)
triangles, mostly from the work of M. Laczkovich, M. Beeson, Beeson–Roșu, Beeson–Zhang, Zhang and
Snover–Waiveris–Williams. It grew out of work on Erdős problem 634 (can a triangle be cut into N congruent
triangles for prime N?), and the repository keeps only what the triangle-tiling theory needs. **The Erdős problem
itself is not claimed solved here.**

## Status: read this first

* Every theorem in this repository is **NOTE/UNAUDITED**: checked by the Lean kernel (axioms `propext`,
  `Classical.choice`, `Quot.sound` only, no `sorry`, no `native_decide`), but **not reviewed by anyone outside the
  project**. A Lean theorem proves what its statement says; whether the statement is the printed theorem is
  exactly what the "match" labels below record (F faithful, S stronger, W weaker, D differs).
* The deposit **has not been rebuilt separately**. The files were extracted from the author's development tree,
  where they were built one module at a time (memory), and they differ from it only in comments (references to
  private working notes removed). A build from this repository has not been checked by the author.
* Beeson's programme (arXiv 1206.2229, 1206.1974) is **partly paused**: of 204 rows, 51 DONE, 15 DONE (depends on
  `lacz51_all`), 31 DONE-WITH-HYPOTHESIS, 54 PARTIAL, 46 NOT FORMALIZED, 7 OUT OF SCOPE.

## Contents

| Path | What |
|---|---|
| `lean/` | 1834 Lean modules (about 21 MB): `Erdos634/Draft/LaczFormal*`, `Beeson*`, `Zhang*` and their full import closure inside `Erdos634` (the aggregates `AllLacz*`, `AllBeeson*`) |
| `lean/Erdos634.lean` | root module (imports the aggregates) |
| `docs/COVERAGE_LACZKOVICH.md` | row-by-row table: Laczkovich DM 140 (1995), DCG 19 (1998), DCG 48 (2012), SWW 1991 |
| `docs/COVERAGE_BEESON.md` | 204 rows: Beeson 1206.2229 / 1206.1974, Beeson–Roșu, Zhang |
| `docs/COVERAGE_BEESON_ZHANG_BZ.md` | Beeson–Zhang (2604.01314, 2604.03609) Thm 1.1/1.2, every row |
| `docs/COVERAGE_ZHANG.md` | Zhang (2512.22696) |
| `docs/THM21_FIDELITY.md` | statement fidelity of `theorem21_unconditional` |
| `docs/PRINTED_GAPS.md` | printed gaps and slips found while formalizing (courtesy notes, not yet sent to the authors) |

## Headline theorems (all in namespace `Erdos634.Draft`; all NOTE/UNAUDITED)

| Source | Lean name (file) | Match |
|---|---|---|
| Laczkovich DCG 48 Thm 2.1 (nine conclusions for regular tilings of a convex polygon) | `LaczFormal.RG.theorem21_unconditional` (`LaczFormalThm21Final`) | F for the repaired theorem (see fidelity doc) |
| Laczkovich DCG 48 Thm 3.3 (equilateral target, iff) | `thm33_iff`, `thm33_only_if` (`LaczFormalThm33if5`, `Thm33Iii3`) | F, both directions |
| Laczkovich DCG 48 Lemma 3.2 | `lemma32_tiling`, `lemma32_tri` (`LaczFormal32e2`) | F |
| Laczkovich DM 140 Thm 5.1 / 5.3 (congruent-tile version) | `lacz51_all`, `lacz53_thm` (`LaczFormal51Gen2`) | W: congruent tiles only |
| Beeson Lemma 1 (H1), unconditional | `lemma1_unconditional` and wrappers (`BeesonCol6L1`, `LaczFormal51Lemma1`) | see map |
| Beeson–Zhang Thm 1.1 (gamma = 2π/3, target not similar) | `bz_thm11` (`LaczFormalBZL7d6`) | F |
| Beeson–Zhang rational case | `bz_rational_all` (`LaczFormalBZL7k1`) | see BZ table |
| Beeson 1206.1974 Thm 10.7 | `beeson_thm107_proved` (`LaczFormalBZL7h16`) | PARTIAL (relation content; figure cases not formalized) |
| Beeson Thm 9 (Zhang's "Theorem 3 of [2]") | `beeson_thm9`, `beeson_thm9_printed` (`ZhangRat10Thm9`) | F (printed hypothesis) |
| Zhang Thm 1 | `zhang_thm1` (`ZhangThm1Full`) | see Zhang table |
| Laczkovich constructions Thm 2.3, 2.4, 2.5, 2.6 | `thm23_printed`, `thm24_printed`, `thm25_first`, `thm26` | see Laczkovich table |

Hypotheses are named in the statements; witnesses (non-vacuity) are listed per row in the coverage tables
(for example `assembly_witness_unc`, `genTiling_thm21`, `witness_143`, `beeson_thm9_wit`, `beeson_thm107_tri_wit`).
Open items are the "Missing" lists at the end of the coverage documents: for Laczkovich DCG 48, the existence
half of Thm 2.1 for 8 of 9 cases, Thms 2.2, 2.3-remark, 3.1, 3.4, Lemma 3.5; Thm 3.6 is partial; see the table.

## Internal audit rounds (all inside the project, none external)

| Round | Subject | Verdict |
|---|---|---|
| Thm 2.1 adversarial | `theorem21_unconditional` statement vs print | FAITHFUL, not vacuous |
| Case IIc, fresh audit | IIc chain / `iicNoKites_proved` (one stale sentence corrected) | no error found |
| Laczkovich 5.1 adversarial | `lacz51_all` | SOUND WITH GAPS (upstream lemmaK, LemmaKStar, `classify_commensurable_final` not re-audited) |
| Trust base | unread groups of the 5.1 closure | G1 SOUND, G2 SOUND WITH GAPS, G3 SOUND |
| H1 unconditional | `lemma1_unconditional` and 12 wrappers | axioms checked, no `sorry`/`native_decide` |
| Beeson Thm 17 / Lemma 37, 46 | algorithm, `lemma49` | SOUND (print-error claims confirmed by computation) |
| IVc rational bridge, corner cone | `ivc_rat_final`, `corner_cone`, `vw_star` | SOUND WITH GAPS (witnesses incomplete; proof bodies not all line-read) |

A statement marked "SOUND WITH GAPS" has named closing tasks; none of these is a claim by any outside reader.

## Printed gaps

`docs/PRINTED_GAPS.md` lists points where a printed argument needed repair when formalized (Laczkovich 2012
Lemma 7.1(i), first found by Beeson–Zhang, arXiv 2604.01314, Appendix A; Lemmas 6.2/6.3; Beeson 1206.1974
Lemmas 10.4, 10.5, 11.8, 11.11; Beeson 1206.2229 Lemmas 37, 46; Zhang Prop. 6). They are stated neutrally, with
what we needed instead. Not yet communicated to the authors.

## How to build

`lean/lean-toolchain`, `lean/lakefile.toml`, `lean/lake-manifest.json` are copied from the development tree
(Lean `leanprover/lean4:v4.30.0`, Mathlib `v4.30.0`). The development builds were done one module at a time in
dependency order, because a parallel build of this size exceeds ordinary memory. The aggregates
`Erdos634.Draft.AllLacz*` and `AllBeeson*` are the intended entry points. The 34 `Refl.*` modules in the closure
are the small checker and the N = 17 certificate used by one lemma (`Refl.DataE120`, 1.3 MB, is the largest);
no large search certificates are included. **This deposit was not rebuilt separately.**

## Credit and disclosure

The mathematics is that of Laczkovich (Discrete Math. 140 (1995); Discrete Comput. Geom. 19 (1998), 48 (2012)),
Beeson (arXiv 1206.2229, 1206.1974), Beeson–Roșu, Beeson–Zhang (2604.01314, 2604.03609), Zhang (2512.22696),
Snover–Waiveris–Williams (Discrete Math. 91 (1991)); thanks also to Paliy and Herdt for related prior work and
examples. AI assistance (Claude, Anthropic) was used in the preparation of the proofs, the Lean files and the text;
the Lean theorems are checked by the Lean kernel, and the author is responsible for the contents.

## License
Text and docs: CC BY 4.0. Lean code: MIT. See `LICENSE`.
