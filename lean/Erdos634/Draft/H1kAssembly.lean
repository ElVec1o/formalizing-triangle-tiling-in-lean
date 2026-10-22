/-
Draft/H1kAssembly.lean — CONDITIONAL assembly of `ChainComposite.H1Right N` from the atoms H1.a, H1.b, H1.d and two
explicit hypothesis Props for the parts that are NOT in Lean:
  * `RightCaseC N` — paper §2 Case C (`a/b ∉ ℚ`, `c ∉ ℚa + ℚb`, `lam ∉ ℚ` is impossible); needs atom H1.c (flux
    coordinates `A_X, B_X, C_X`, from `Row3.RP` / `rightTile_flux_value_c` / `target_flux_general`).
  * `RightCaseD N` — paper §2 Case D (`a/b ∉ ℚ`, `c = r a + s b`, `lam ∉ ℚ` is impossible); needs D4–D9 = atoms
    H1.e (corner geometry CL), H1.f/g (neighbour graph, vertices in K), H1.h (CT), H1.i (SL), H1.j; H1.d (this folder) supplies
    the field `K` and the embedding `σ` with the σ-images of the side words (`caseD_algebra`).
Both hypotheses are quantified over normal-form dissections (`RightNormal`) so assembly can substitute the later proofs.
Theorem: `H1Right N` follows from `RightCaseC N` and `RightCaseD N`.  Nothing else (Case AB, the split, the λ ∈ ℚ branch
and the WLOG normalization are PROVED here / in H1a, H1b, H1d).
*** CONDITIONAL.  UNAUDITED.  Formalization debt, NOT /goal progress.  No sorry. ***
-/
import Erdos634.Draft.H1aSetup
import Erdos634.Draft.H1bCaseAB
import Erdos634.Draft.H1dCaseD
import Erdos634.Draft.ChainComposite

open scoped Classical

namespace Erdos634.Draft.H1k

open Erdos634.Geometry Erdos634.Draft.H1a Erdos634.Draft.ChainComposite

/-- **Case C hypothesis (NOT in Lean).**  In normal form with `M = N/2`, `a = oppLen 0`, `b = oppLen 1`, `c = oppLen 2`
of the model and `lam = target.oppLen 1 / c`: `lam ∉ ℚ`, `a/b ∉ ℚ` and `c ∉ ℚa + ℚb` is contradictory.
Source: paper-level `SCOPE_H1_full.md` §2 Case C (Gaussian flux identity, coefficient separation `A_X = B_X = C_X = 0`). -/
def RightCaseC (N : ℕ) : Prop :=
  ∀ (D : CongruentDissection N) (α : ℝ), RightNormal D α →
    Irrational (D.target.oppLen 1 / D.model.oppLen 2) →
    Irrational (D.model.oppLen 0 / D.model.oppLen 1) →
    ¬ (∃ r s : ℚ, D.model.oppLen 2 = r * D.model.oppLen 0 + s * D.model.oppLen 1) → False

/-- **Case D hypothesis (NOT in Lean).**  Same notation: `lam ∉ ℚ`, `a/b ∉ ℚ`, `c = r a + s b` (`r, s ∈ ℚ`) is
contradictory.  Source: `SCOPE_H1_full.md` §2 Case D, D4–D9 (conjugate dissection CT, sign lemma SL, corners CL). -/
def RightCaseD (N : ℕ) : Prop :=
  ∀ (D : CongruentDissection N) (α : ℝ), RightNormal D α →
    Irrational (D.target.oppLen 1 / D.model.oppLen 2) →
    Irrational (D.model.oppLen 0 / D.model.oppLen 1) →
    (∃ r s : ℚ, D.model.oppLen 2 = r * D.model.oppLen 0 + s * D.model.oppLen 1) → False

/-- **`H1Right N` from Case C and Case D** (Case AB, the exhaustive split and the rational-`lam` branch are proved). -/
theorem h1Right_of_caseC_caseD (N : ℕ) (hC : RightCaseC N) (hD : RightCaseD N) : H1Right N := by
  intro D hR
  obtain ⟨D', α, M, hN, hF⟩ := rightCase_facts hR
  apply h1_of_irrational_case hF
  intro hlam
  have hb0 : D'.model.oppLen 1 ≠ 0 := hF.hb.ne'
  rcases H1d.case_split (c := D'.model.oppLen 2) hb0 with hAB | ⟨hi, hnc⟩ | ⟨hi, hrs⟩
  · exact H1b.caseAB_sumsq hF.ha hF.hb (by linarith [hF.pyth]) hF.hlam hF.hlam2 hlam hAB hF.wAB
  · exact (hC D' α hN hlam hi hnc).elim
  · exact (hD D' α hN hlam hi hrs).elim

end Erdos634.Draft.H1k

#print axioms Erdos634.Draft.H1k.h1Right_of_caseC_caseD
