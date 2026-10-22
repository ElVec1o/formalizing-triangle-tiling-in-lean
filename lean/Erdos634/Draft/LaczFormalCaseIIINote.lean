-- Draft/LaczFormalCaseIIINote.lean -- NOTE (UNAUDITED): the verified repair chain for Laczkovich DCG 48 (2012) Thm 2.1, Cases IIIa/IIIb, plus the relabelling lemma.
-- Credit: Laczkovich (DCG 48 (2012), Sect. 4, 7), Beeson-Zhang (arXiv 2604.01314), Beeson.
--
-- CHAIN (all axioms = propext, Classical.choice, Quot.sound; checked 2026-10-22, (private working notes, not included)):
--  1. `corner_comb` (IIIaCornerComb): corner classification + pigeonhole, by `decide`/finite case work; imported via BZBridge -> IIIaCornerClose.
--  2. `caseIII_defects` (BZDefects): s_b + 2 S2 + G + B <= R - (M-2).  Hypothesis `hPang` (all polygon angles pi/3 or 2pi/3) is NOT extra: it is a
--     THEOREM `poly_angles_2pi3` (BZ7) for any regular PolyTiling with gamma = 2pi/3, applied in `caseIIIa_repaired`.
--  3. `nonclean_le_defects`, `caseIII_hdef` (BZBridge): 3 #(non-clean sides) + P <= R.
--  4. `caseIIIa_repaired` (RegularPQ, gamma = 2pi/3, NotComb a b c  =>  Concl1);  `caseIIIb_repaired` (NotComb b a c => Concl1, by alpha<->beta relabelling).
--  5. Assembly: `thm21_partial3` / `theorem21_of_cases3` (Thm21Partial3); aggregate AllLaczThm21Top3 (closure contains every module above).
-- WITNESS: `caseIIIa_witness` (LaczFormalIIIaWit): non-vacuity of the case-IIIa hypotheses (two-tile parallelogram, tile (1, sqrt2, sqrt(3+sqrt2)), NotComb proved).
-- LABELS: statements UNAUDITED-by-person; automated statement audit passed with notes ((private working notes, not included)).  NO tiling with M >= 4 satisfying IIIa/IIIb data is known (theorem: none outside Concl1).
-- REGULARITY NOTE: `Theorem21` quantifies over `RegularPQ` only (regular pair = model vertices 0,1, i.e. p=q).  The paper's alternatives p=r, q=r are the SAME
-- hypothesis after renaming the angles (the conclusions (i)-(ix) are written in the names alpha,beta,gamma with (alpha,beta) the regular pair).  `regular_relabel` below (any sigma; p=r is swap 1 2, q=r is swap 0 2) proves the renaming is available inside Lean: a tiling regular w.r.t. another pair is a RegularPQ tiling of a relabelled model.
import Erdos634.Draft.LaczFormalThm21Partial3

open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

/-- Regular w.r.t. the angle pair `(σ 0, σ 1)` of the model  <=>  `RegularPQ` for the model relabelled by `σ` (so p=r, q=r reduce to p=q). -/
theorem regular_relabel {N : ℕ} (C : CongruentRegionDissection N) (σ : Equiv.Perm (Fin 3))
    (h : ∃ idx : Fin N → Equiv.Perm (Fin 3), (∀ i v, angleAt C.model (idx i v) = angleAt (C.tile i) v) ∧
      ∀ X, cntR C idx X (σ 0) = cntR C idx X (σ 1)) : RegularPQ (relabel C σ) := by
  obtain ⟨idx, hA, hc⟩ := h
  refine ⟨relabelIdx idx σ, relabel_hidxA C idx σ hA, fun X => ?_⟩
  have e0 := relabel_cnt C idx σ X 0
  have e1 := relabel_cnt C idx σ X 1
  have r0 : cntR (relabel C σ) (relabelIdx idx σ) X 0 = cnt (relabel C σ) (relabelIdx idx σ) X 0 := by
    unfold cntR cnt; congr
  have r1 : cntR (relabel C σ) (relabelIdx idx σ) X 1 = cnt (relabel C σ) (relabelIdx idx σ) X 1 := by
    unfold cntR cnt; congr
  have r2 : cntR C idx X (σ 0) = cnt C idx X (σ 0) := by unfold cntR cnt; congr
  have r3 : cntR C idx X (σ 1) = cnt C idx X (σ 1) := by unfold cntR cnt; congr
  rw [r0, r1, e0, e1, ← r2, ← r3]; exact hc X

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.regular_relabel
