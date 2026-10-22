-- Draft/LaczFormalIVcFinal.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (IVc, alpha/pi irrational, M >= 5): the END of the irrational branch.
--   `ivc_final_ge5`: regular PolyTiling of a convex M-gon, M >= 5, by congruent copies of the tile (alpha, 2pi/3 - alpha, pi/3) at model vertices (0, 1, 2), alpha/pi irrational,
--   a, b commensurable, c not commensurable with a  ==>  Concl6 (centrally symmetric rational hexagon, (vi)).   (M <= 4 is `caseIVc_small`.)
-- Route: the printed 'repeating the argument of IIIc' made explicit: the flux sign lemma is redone for gamma = pi/3 (`Tri.flux_cedge_ivc`, factor c - a - b), `ivc_flux_zero` gives Phi(A) = 0 for
-- every anchor, every angle of A is pi/3 or 2pi/3 (`polygon_angle_pi3`), M <= 6 by angle sum, and the IIIc polygon lemmas (`poly5_kill`, `poly6_sym`, Lemma 7.2, which only see the polygon) finish.
-- NOTE, UNAUDITED.  Non-vacuity of the hypotheses: NAMED only (an irrational-alpha instance with M >= 5 is not exhibited; if none exists the branch is vacuous and the theorem still holds).
-- Credit: Laczkovich (DCG 48 (2012), Sect. 8.3, 7.3, Lemma 7.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcPhi
import Erdos634.Draft.LaczFormalIIIcFinal

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.Draft.LaczFormal.RG

namespace Erdos634.Draft.LaczFormal.IIIc

set_option maxHeartbeats 6400000 in
theorem ivc_final_ge5 {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) {α : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hm0 : angleAt T.C.model 0 = α) (hm1 : angleAt T.C.model 1 = 2 * Real.pi / 3 - α) (hm2 : angleAt T.C.model 2 = Real.pi / 3)
    (hab : Comm (slen T.C 0) (slen T.C 1)) (hac : ¬ Comm (slen T.C 0) (slen T.C 2)) (hM5 : 5 ≤ M) : Concl6 T.C T.P := by
  classical
  have hmodel : T.C.model.IVcData α (slen T.C 0) (slen T.C 1) (slen T.C 2) :=
    ⟨1, by simpa using hm0, rfl, by simpa using hm1, rfl, by simpa using hm2, rfl⟩
  have hRat := polytiling_rational T hreg hab hac
  have hzero : ∀ θ₀ : Real.Angle, T.P.flux (fAlphaAt α hα θ₀).weight = 0 := fun θ₀ => ivc_flux_zero T hreg hα hmodel hab hac θ₀
  obtain ⟨idx, hA, hcnt⟩ := hreg
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hm0' : T.C.model.angleAt 0 = α := hm0
  have hm1' : T.C.model.angleAt 1 = 2 * Real.pi / 3 - α := hm1
  have hm2' : T.C.model.angleAt 2 = Real.pi / 3 := hm2
  have hαβ : T.C.model.angleAt 0 + T.C.model.angleAt 1 = 2 * Real.pi / 3 := by rw [hm0', hm1']; ring
  have hall : ∀ i : Fin M, T.P.angle i = Real.pi / 3 ∨ T.P.angle i = 2 * Real.pi / 3 := by
    intro i
    have := polygon_angle_pi3 T.C T.P T.region_eq idx hA hm2' hαβ (fun X => hcnt X) (i - 1)
    rwa [sub_add_cancel] at this
  have hsum := poly_angle_sum T.P
  have hpi := Real.pi_pos
  have hM3 : 3 ≤ M := T.P.three_le
  have hM6 : M ≤ 6 := by
    have hle1 : ∀ i, T.P.angle i ≤ 2 * Real.pi / 3 := fun i => by rcases hall i with h | h <;> rw [h] <;> linarith
    have hle : ∑ i, T.P.angle i ≤ ∑ _i : Fin M, 2 * Real.pi / 3 := Finset.sum_le_sum (fun i _ => hle1 i)
    rw [hsum] at hle
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hle
    rw [Nat.cast_sub (by omega)] at hle
    have : (M : ℝ) ≤ 6 := by
      by_contra hc
      push Not at hc
      push_cast at hle
      nlinarith
    exact_mod_cast this
  have hratio : ∃ q : ℚ, Real.sin (angleAt T.C.model 0) / Real.sin (angleAt T.C.model 1) = q := by
    obtain ⟨p, q, hp, hq, e⟩ := hab
    refine ⟨(q : ℚ) / (p : ℚ), ?_⟩
    have hsr : Real.sin (angleAt T.C.model 0) / Real.sin (angleAt T.C.model 1) = slen T.C 0 / slen T.C 1 := sin_ratio_eq T.C
    rw [hsr]
    have hb := RG.slen_pos T.C 1
    have hp' : (p : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    linarith
  have hM : M = 5 ∨ M = 6 := by omega
  rcases hM with rfl | rfl
  · exfalso
    have hsum5 : ∑ i : Fin 5, T.P.angle i = 3 * Real.pi := by rw [hsum]; norm_num
    rw [Fin.sum_univ_five] at hsum5
    rcases hall 0 with a0 | a0 <;> rcases hall 1 with a1 | a1 <;> rcases hall 2 with a2 | a2 <;> rcases hall 3 with a3 | a3 <;>
      rcases hall 4 with a4 | a4 <;>
      first
      | (exfalso; linarith)
      | exact poly5_kill T.P hzero 4 (by simpa using a0) (by simpa using a1) (by simpa using a2) (by simpa using a3)
      | exact poly5_kill T.P hzero 0 (by simpa using a1) (by simpa using a2) (by simpa using a3) (by simpa using a4)
      | exact poly5_kill T.P hzero 1 (by simpa using a2) (by simpa using a3) (by simpa using a4) (by simpa using a0)
      | exact poly5_kill T.P hzero 2 (by simpa using a3) (by simpa using a4) (by simpa using a0) (by simpa using a1)
      | exact poly5_kill T.P hzero 3 (by simpa using a4) (by simpa using a0) (by simpa using a1) (by simpa using a2)
  · obtain ⟨hang, hsym⟩ := poly6_sym T.P hzero hall
    exact ⟨rfl, hRat, hsym, hang, Or.inl hm2, hratio⟩

end Erdos634.Draft.LaczFormal.IIIc

#print axioms Erdos634.Draft.LaczFormal.IIIc.ivc_final_ge5
