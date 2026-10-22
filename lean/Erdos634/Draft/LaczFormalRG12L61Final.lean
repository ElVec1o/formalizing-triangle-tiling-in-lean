-- Draft/LaczFormalRG12L61Final.lean -- **Laczkovich DCG 48 (2012), Lemma 6.1** (Theorem 2.1, Subcase IIc): `a, b` commensurable, `c` not a rational multiple of `a`, `gamma < pi/2`, `gamma != pi/3`, regular tiling of a convex
-- polygon: either conclusion (i) holds, or every angle of the polygon equals `alpha + beta = pi - gamma` (`P = N`).  Route: `lemma61_core` (propagation of `gamma` around a vertex, one exceptional vertex at most) and,
-- for the parallelogram, the assembly of `caseI_c` (rationality of the polygon by Lemma 4.7, `polytiling_rational`).  NOTE, UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Lemma 6.1 and 4.7), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12L61Count
import Erdos634.Draft.LaczFormalRG9Ic

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

/-- **Lemma 6.1.**  Under the hypotheses of Subcase IIc, either conclusion (i) of Theorem 2.1 holds, or every angle of the polygon equals `π - γ = α + β`. -/
theorem lemma61 {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) (h1 : angleAt T.C.model 2 < Real.pi / 2) (h3 : angleAt T.C.model 2 ≠ Real.pi / 3)
    (hab : Comm (slen T.C 0) (slen T.C 1)) (hac : ¬ Comm (slen T.C 0) (slen T.C 2)) :
    Concl1 T.C T.P ∨ ∀ j : Fin M, T.P.angle j = Real.pi - angleAt T.C.model 2 := by
  classical
  have hRat := polytiling_rational T hreg hab hac
  obtain ⟨idx, hA, hcnt⟩ := hreg
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hC : CaseC T.C idx := ⟨idx_dist_of_angle T.C idx hA, hA, fun X => hcnt X, notComb_c_of_comm (slen_pos T.C 2) hab hac⟩
  rcases lemma61_core T.C T.P T.region_eq idx hC h1 h3 with hP | ⟨hM4, a, ha1, ha2, ha3⟩
  · right
    intro j
    have hcard := cntP0_eq_card T.C T.P T.region_eq idx hC.hidxA hC.hregc h1
    rw [hP] at hcard
    have hall : Finset.univ.filter (fun k : Fin M => cnt T.C idx (T.P.v (k + 1)) 0 = 1) = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [← hcard]; simp)
    have hj : cnt T.C idx (T.P.v (j - 1 + 1)) 0 = 1 := by
      have : (j - 1) ∈ Finset.univ.filter (fun k : Fin M => cnt T.C idx (T.P.v (k + 1)) 0 = 1) := by rw [hall]; exact Finset.mem_univ _
      simpa using this
    have := caseII_polyvertex T.C T.P T.region_eq idx hC.hidxA hC.hregc h1 (j - 1)
    rw [sub_add_cancel] at this hj
    rcases this with ⟨-, -, e⟩ | ⟨e, -, -⟩
    · exact e
    · omega
  · left
    have hratio : ∃ q : ℚ, T.P.side 0 / T.P.side 1 = q * (Real.sin (angleAt T.C.model 0) / Real.sin (angleAt T.C.model 1)) := by
      obtain ⟨m1, n1, hm1, hn1, e1⟩ := hRat 0 1
      obtain ⟨m2, n2, hm2, hn2, e2⟩ := hab
      have hs1 : 0 < T.P.side 1 := side_pos T.P 1
      have hsb : 0 < slen T.C 1 := slen_pos T.C 1
      refine ⟨((n1 * m2 : ℕ) : ℚ) / ((m1 * n2 : ℕ) : ℚ), ?_⟩
      have hsr : Real.sin (angleAt T.C.model 0) / Real.sin (angleAt T.C.model 1) = slen T.C 0 / slen T.C 1 := sin_ratio_eq T.C
      rw [hsr]
      have hm1' : (m1 : ℝ) ≠ 0 := by positivity
      have hn2' : (n2 : ℝ) ≠ 0 := by positivity
      have hm2' : (m2 : ℝ) ≠ 0 := by positivity
      push_cast
      rw [div_eq_iff hs1.ne']
      field_simp
      linear_combination ((n2 : ℝ) * slen T.C 1) * e1 - ((n1 : ℝ) * T.P.side 1) * e2
    subst hM4
    have hpg : ∀ i : Fin 4, T.P.v i + T.P.v (i + 2) = T.P.v (i + 1) + T.P.v (i + 3) :=
      par_all T.P a (quad_parallelogram_gen T.P a (angleAt T.C.model 2) ha1 ha2 ha3)
    exact ⟨⟨rfl, hpg⟩, ⟨a + 1, ha1⟩, Or.inl hratio⟩

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.lemma61
