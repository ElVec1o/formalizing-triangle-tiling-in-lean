-- Draft/LaczFormalRG4RegFan.lean -- Case IV (gamma = pi/3): the WEIGHT-FREE version of the vertex-local check behind Lemma 8.1(i) at the heads of `Gamma_k` edges.
-- `colG` replaces the weighted collinearity flag `col`: ray `i` has an opposite ray only if a block of consecutive corners starting at ray `i` has the type counts
-- `(1,1,1)` or `(0,0,3)` (the only blocks of total angle `pi` when `alpha + beta = 2 gamma = 2 pi/3` and `a` is not a rational combination of `b, c`; proved in `RG4Arith.block_eq`).
-- Decided by `decide +kernel` over all `6^6` fans, as the weighted checks of `LaczFormalRegFan`.
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Lemma 8.1), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRegFan

namespace Erdos634.Draft.LaczFormal.RegFan

/-- Number of corners of type `j` among the `m` consecutive corners starting at `l[i]` (cyclic). -/
def blk (l : List ℕ) (i m j : ℕ) : ℕ :=
  ((List.range m).filter (fun s => tT (l.getD ((i + s) % l.length) 0) == j)).length

/-- Ray `i` may have an opposite ray: some block of consecutive corners starting at ray `i` has counts `(1,1,1)` or `(0,0,3)`. -/
def colG (l : List ℕ) (i : ℕ) : Bool :=
  (List.range l.length).any (fun m =>
    (blk l i m 0 == 1 && blk l i m 1 == 1 && blk l i m 2 == 1) || (blk l i m 0 == 0 && blk l i m 1 == 0 && blk l i m 2 == 3))

def fullConclG (l : List ℕ) : Bool :=
  (List.range 6).any (fun i => (!(colG l i) && gaEdge l i) || gkEdge l i)
def fullOKG (l : List ℕ) : Bool :=
  !(fullHyp333 l || fullHyp222 l) || fullConclG l

theorem full_checkG : (allFans 6).all fullOKG = true := by decide +kernel

/-- **Lemma 8.1(i), the `Γ_k`-head vertices, weight-free.** -/
theorem full_fan_gk_headG (l : List ℕ) (hlen : l.length = 6) (hlt : ∀ x ∈ l, x < 6)
    (h : (fullHyp333 l || fullHyp222 l) = true) : fullConclG l = true :=
  impl_of_ok ((List.all_eq_true.mp full_checkG) l (mem_allFans 6 l hlen hlt)) h

/-- Witness of the hypotheses and of the conclusion (type `2α+2β+2γ`), with a `Γ_k` edge only. -/
theorem full_fan_witnessG :
    fullHyp333 [0, 0, 0, 2, 2, 3] = true ∧ fullConclG [0, 0, 0, 2, 2, 3] = true ∧
    fullHyp222 [0, 0, 2, 3, 4, 5] = true ∧ fullConclG [0, 0, 2, 3, 4, 5] = true := by
  decide

/-! ## The alpha-propagation along a side (the proof of Lemma 4.3 / Fig. 3 for the `α` case): in a normal three-tile fan at a side vertex without differing first sides,
if the left tile (last of the line) has `α` at its far end then the right tile has `α` at the vertex; and symmetrically. -/

def alphaStepOK (l : List ℕ) : Bool := !(stepHyp l) || !(tW (l.getD 2 0) == 0) || (tT (l.getD 0 0) == 0)
def alphaStepOK' (l : List ℕ) : Bool := !(stepHyp l) || !(tU (l.getD 0 0) == 0) || (tT (l.getD 2 0) == 0)

theorem alpha_check : (allFans 3).all alphaStepOK = true := by decide +kernel
theorem alpha_check' : (allFans 3).all alphaStepOK' = true := by decide +kernel

theorem boundary_step_alpha (l : List ℕ) (hlen : l.length = 3) (hlt : ∀ x ∈ l, x < 6) (h : stepHyp l = true)
    (hw : tW (l.getD 2 0) = 0) : tT (l.getD 0 0) = 0 := by
  have := (List.all_eq_true.mp alpha_check) l (mem_allFans 3 l hlen hlt)
  simp only [alphaStepOK, h, Bool.not_true, hw, beq_self_eq_true, Bool.or_eq_true, Bool.not_eq_true', Bool.false_or, beq_iff_eq] at this
  simpa using this

theorem boundary_step_alpha' (l : List ℕ) (hlen : l.length = 3) (hlt : ∀ x ∈ l, x < 6) (h : stepHyp l = true)
    (hw : tU (l.getD 0 0) = 0) : tT (l.getD 2 0) = 0 := by
  have := (List.all_eq_true.mp alpha_check') l (mem_allFans 3 l hlen hlt)
  simp only [alphaStepOK', h, Bool.not_true, hw, beq_self_eq_true, Bool.or_eq_true, Bool.not_eq_true', Bool.false_or, beq_iff_eq] at this
  simpa using this

/-- Witness: the hypotheses (`stepHyp`, far end of the left tile is `α`) are satisfiable. -/
theorem alpha_step_witness : stepHyp [0, 2, 5] = true ∧ tW ([0, 2, 5].getD 2 0) = 0 ∧ tT ([0, 2, 5].getD 0 0) = 0 := by decide

end Erdos634.Draft.LaczFormal.RegFan
