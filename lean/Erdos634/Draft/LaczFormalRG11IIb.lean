-- Draft/LaczFormalRG11IIb.lean -- **Theorem 2.1, Case II (gamma < pi/2, gamma != pi/3), Subcase "b not a nonnegative combination of a, c"** (Laczkovich DCG 48 (2012), Sect. 6.1: "symmetric to IIa"): relabel `alpha <-> beta` in `caseII_a`
-- (same proof as `caseI_b` from `caseI_a`).  `caseII_b_small` -> Concl1.  NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG11Final
import Erdos634.Draft.LaczFormalRG9Ib

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

/-- **Subcase IIb'** (Case II, `b` not a nonnegative rational combination of `a, c`): relabel `α ↔ β`. -/
theorem caseII_b_small {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) (h1 : angleAt T.C.model 2 < Real.pi / 2) (h3 : angleAt T.C.model 2 ≠ Real.pi / 3)
    (hnc : NotComb (slen T.C 1) (slen T.C 0) (slen T.C 2)) : Concl1 T.C T.P := by
  set σ : Equiv.Perm (Fin 3) := Equiv.swap 0 1 with hσ
  have s0 : σ 0 = 1 := by simp [hσ]
  have s1 : σ 1 = 0 := by simp [hσ]
  have s2 : σ 2 = 2 := by rw [hσ]; exact Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  let T' : PolyTiling N M := ⟨relabel T.C σ, T.P, T.region_eq⟩
  obtain ⟨idx, hA, hcnt⟩ := hreg
  have hreg' : RegularPQ T'.C := by
    refine ⟨relabelIdx idx σ, relabel_hidxA T.C idx σ hA, fun X => ?_⟩
    have e0 := relabel_cnt T.C idx σ X 0
    have e1 := relabel_cnt T.C idx σ X 1
    rw [s0] at e0; rw [s1] at e1
    show cnt (relabel T.C σ) (relabelIdx idx σ) X 0 = cnt (relabel T.C σ) (relabelIdx idx σ) X 1
    rw [e0, e1]
    exact (hcnt X).symm
  have hγ' : angleAt T'.C.model 2 = angleAt T.C.model 2 := by
    show angleAt (relabel T.C σ).model 2 = _
    rw [relabel_angleAt, s2]
  have hnc' : NotComb (slen T'.C 0) (slen T'.C 1) (slen T'.C 2) := by
    show NotComb (slen (relabel T.C σ) 0) (slen (relabel T.C σ) 1) (slen (relabel T.C σ) 2)
    rw [relabel_slen, relabel_slen, relabel_slen, s0, s1, s2]; exact hnc
  have h := caseII_a T' hreg' (by rw [hγ']; exact h1) (by rw [hγ']; exact h3) hnc'
  obtain ⟨⟨h4, hpar⟩, ⟨i, hi⟩, hratio⟩ := h
  have e2 : angleAt (relabel T.C σ).model 2 = angleAt T.C.model 2 := by rw [relabel_angleAt, s2]
  have e0 : angleAt (relabel T.C σ).model 0 = angleAt T.C.model 1 := by rw [relabel_angleAt, s0]
  have e1 : angleAt (relabel T.C σ).model 1 = angleAt T.C.model 0 := by rw [relabel_angleAt, s1]
  refine ⟨⟨h4, hpar⟩, ⟨i, ?_⟩, ?_⟩
  · rw [← e2]; exact hi
  · have hsA := Erdos634.Draft.LaczFormal.Thm21.sin_angleAt_pos T.C.model 0
    have hsB := Erdos634.Draft.LaczFormal.Thm21.sin_angleAt_pos T.C.model 1
    have p0 := side_pos T.P 0
    have p1 := side_pos T.P 1
    rcases hratio with ⟨q, hq⟩ | ⟨q, hq⟩
    · have hq' : T.P.side 0 / T.P.side 1 = q * (Real.sin (angleAt T.C.model 1) / Real.sin (angleAt T.C.model 0)) := by
        have := hq; simp only [T'] at this; rw [e0, e1] at this; exact this
      obtain ⟨q', hq''⟩ := ratio_flip p0 p1 hsB hsA hq'
      right; exact ⟨q', hq''⟩
    · have hq' : T.P.side 1 / T.P.side 0 = q * (Real.sin (angleAt T.C.model 1) / Real.sin (angleAt T.C.model 0)) := by
        have := hq; simp only [T'] at this; rw [e0, e1] at this; exact this
      obtain ⟨q', hq''⟩ := ratio_flip p1 p0 hsB hsA hq'
      left; exact ⟨q', hq''⟩

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.caseII_b_small
