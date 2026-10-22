-- Draft/LaczFormalRG9Ib.lean -- **Theorem 2.1, Case I (gamma > pi/2, gamma != 2pi/3), COMPLETE** (Laczkovich DCG 48 (2012), Sect. 5): Subcase Ib by relabeling `alpha <-> beta` (as in `caseIV_Vb`), and the combination of
-- Subcases Ia (`caseI_a`), Ib, Ic (`caseI_c`) and the pairwise commensurable branch (`caseI_d`): `RG.thm21_I`.  UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Sect. 5), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG9Ia3
import Erdos634.Draft.LaczFormalRG9Id

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

/-- **Subcase Ib** (`b` not a nonnegative rational combination of `a, c`): relabel `α ↔ β`. -/
theorem caseI_b {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) (h1 : Real.pi / 2 < angleAt T.C.model 2) (h3 : angleAt T.C.model 2 ≠ 2 * Real.pi / 3)
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
  have h := caseI_a T' hreg' (by rw [hγ']; exact h1) (by rw [hγ']; exact h3) hnc'
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

/-- **Theorem 2.1, Case I (`γ > π/2`, `γ ≠ 2π/3`) is a theorem**: every regular tiling of a convex polygon by congruent triangles has one of the shapes of Theorem 2.1 (in fact (i) or (ii)). -/
theorem thm21_I {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) (h1 : Real.pi / 2 < angleAt T.C.model 2) (h3 : angleAt T.C.model 2 ≠ 2 * Real.pi / 3) :
    Thm21Concl T.C T.P := by
  classical
  by_cases hA : NotComb (slen T.C 0) (slen T.C 1) (slen T.C 2)
  · exact Or.inl (caseI_a T hreg h1 h3 hA)
  by_cases hB : NotComb (slen T.C 1) (slen T.C 0) (slen T.C 2)
  · exact Or.inl (caseI_b T hreg h1 h3 hB)
  unfold NotComb at hA hB
  push Not at hA hB
  obtain ⟨r, p, q, hr, e1⟩ := hA
  obtain ⟨r', p', q', hr', e2⟩ := hB
  have hcomm : Comm (slen T.C 0) (slen T.C 1) := comm_of_two_combs (slen_pos T.C 0) (slen_pos T.C 1) hr e1 hr' e2
  by_cases hc : Comm (slen T.C 0) (slen T.C 2)
  · exact Or.inr (Or.inl (caseI_d T hreg h1 h3 hcomm hc))
  · exact Or.inl (caseI_c T hreg h1 h3 hcomm hc)

end Erdos634.Draft.LaczFormal.RG
