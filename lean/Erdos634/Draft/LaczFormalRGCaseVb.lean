-- Draft/LaczFormalRGCaseVb.lean -- Case V, SUBCASE Vb of Laczkovich's Theorem 2.1 ("The same argument applies if b is not a linear combination of a and c"): relabel alpha <-> beta.
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 9.1 end), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRGRelabel

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

theorem ratio_flip {x y s t : ℝ} (hx : 0 < x) (hy : 0 < y) (hs : 0 < s) (ht : 0 < t) {q : ℚ} (h : x / y = q * (s / t)) :
    ∃ q' : ℚ, y / x = q' * (t / s) := by
  have hq : (q : ℝ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h
    exact (div_pos hx hy).ne' h
  refine ⟨q⁻¹, ?_⟩
  push_cast
  field_simp
  field_simp at h
  linarith

theorem side_pos {M : ℕ} [NeZero M] (P : ConvPoly M) (i : Fin M) : 0 < P.side i := by
  unfold ConvPoly.side
  apply dist_pos.mpr
  intro h
  apply P.e_ne_zero P.three_le i
  unfold ConvPoly.e; rw [← h]; simp

/-- **Case V, subcase Vb.** -/
theorem caseV_Vb {N : ℕ} (T : PolyTiling N 4) (hreg : RegularPQ T.C) (hγ : angleAt T.C.model 2 = Real.pi / 2)
    (hnc : NotComb (slen T.C 1) (slen T.C 0) (slen T.C 2)) : Concl1 T.C T.P := by
  set σ : Equiv.Perm (Fin 3) := Equiv.swap 0 1 with hσ
  have s0 : σ 0 = 1 := by simp [hσ]
  have s1 : σ 1 = 0 := by simp [hσ]
  have s2 : σ 2 = 2 := by rw [hσ]; exact Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  let T' : PolyTiling N 4 := ⟨relabel T.C σ, T.P, T.region_eq⟩
  obtain ⟨idx, hA, hcnt⟩ := hreg
  have hreg' : RegularPQ T'.C := by
    refine ⟨relabelIdx idx σ, relabel_hidxA T.C idx σ hA, fun X => ?_⟩
    have e0 := relabel_cnt T.C idx σ X 0
    have e1 := relabel_cnt T.C idx σ X 1
    rw [s0] at e0; rw [s1] at e1
    show cnt (relabel T.C σ) (relabelIdx idx σ) X 0 = cnt (relabel T.C σ) (relabelIdx idx σ) X 1
    rw [e0, e1]
    exact (hcnt X).symm
  have hγ' : angleAt T'.C.model 2 = Real.pi / 2 := by
    show angleAt (relabel T.C σ).model 2 = _
    rw [relabel_angleAt, s2]; exact hγ
  have hnc' : NotComb (slen T'.C 0) (slen T'.C 1) (slen T'.C 2) := by
    show NotComb (slen (relabel T.C σ) 0) (slen (relabel T.C σ) 1) (slen (relabel T.C σ) 2)
    rw [relabel_slen, relabel_slen, relabel_slen, s0, s1, s2]; exact hnc
  have h := caseV_Va T' hreg' hγ' hnc'
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
