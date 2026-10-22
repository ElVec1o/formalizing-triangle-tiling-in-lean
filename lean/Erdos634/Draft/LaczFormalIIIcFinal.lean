-- Draft/LaczFormalIIIcFinal.lean -- Laczkovich DCG 48 (2012), Sect. 7.3 (IIIc, alpha/pi irrational): the END of the subcase.
--   `iiic_final`: regular PolyTiling of a convex polygon A by congruent copies of the tile (alpha, pi/3 - alpha, 2pi/3) at model vertices (0, 1, 2), alpha/pi irrational,
--   a, b commensurable, c not commensurable with a  ==>  Concl1 (parallelogram, (i)) OR Concl6 (centrally symmetric rational hexagon, (vi)).
-- Route: every angle of A is pi/3 or 2pi/3 (`polygon_angle_2pi3`); the flux of the weight anchored at ANY side vanishes (`iiic_flux_zero`); the polygon is cyclically re-indexed (`rotP`,
-- the flux does not depend on the indexing) so that Lemma 7.2 (`lemma72_three/four/five`: Phi = 3 d > 0) kills the triangle, the trapezoid (adjacent pi/3 angles) and the pentagon;
-- alternating angles give a parallelogram (`quad_parallelogram`), the hexagon gives d_i = d_{i+3} (`lemma72_six` and Phi = 0).  Sum of angles gives M <= 6.
-- NOTE, UNAUDITED.  Non-vacuity of the hypotheses: NAMED only (irrational-alpha parallelogram of two congruent triangles with sin(pi/3-alpha) = 2 sin alpha; its conclusion is Concl1).
-- Printed gap closed: the printed text says 'we may assume N=4 trapezoid has X0X1 || X2X3 and N=5 has its only acute angle at X1': this is the re-indexing `rotP` (Phi is index-free).
-- Credit: Laczkovich (DCG 48 (2012), Sect. 7.3, Lemma 7.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIIcPhi
import Erdos634.Draft.LaczFormalRG6IVcSmall
import Erdos634.Draft.LaczFormalRG3Comm
import Erdos634.Draft.LaczFormalRG9Geo

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.Draft.LaczFormal.RG

namespace Erdos634.Draft.LaczFormal.IIIc

variable {M : ℕ} [NeZero M]

/-- Cyclic re-indexing of a convex polygon. -/
def rotP (P : ConvPoly M) (s : Fin M) : ConvPoly M where
  v j := P.v (j + s)
  three_le := P.three_le
  left i j hj hj1 := by
    have h := P.left (i + s) (j + s) (fun h => hj (add_right_cancel h)) (fun h => hj1 (add_right_cancel (h.trans (add_right_comm i 1 s).symm)))
    rw [← add_right_comm i 1 s] at h
    exact h

theorem rotP_side (P : ConvPoly M) (s j : Fin M) : (rotP P s).side j = P.side (j + s) := by
  unfold ConvPoly.side
  show dist (P.v (j + s)) (P.v (j + 1 + s)) = dist (P.v (j + s)) (P.v (j + s + 1))
  rw [add_right_comm]

theorem rotP_angle (P : ConvPoly M) (s j : Fin M) : (rotP P s).angle j = P.angle (j + s) := by
  unfold ConvPoly.angle
  show cornerAngle (P.v (j - 1 + s)) (P.v (j + s)) (P.v (j + 1 + s)) = cornerAngle (P.v (j + s - 1)) (P.v (j + s)) (P.v (j + s + 1))
  rw [show j - 1 + s = j + s - 1 by abel, show j + 1 + s = j + s + 1 by abel]

theorem rotP_sideDir (P : ConvPoly M) (s j : Fin M) : (rotP P s).sideDir j = P.sideDir (j + s) := by
  apply Subtype.ext
  have h : (rotP P s).e j = P.e (j + s) := by
    unfold ConvPoly.e
    show P.v (j + 1 + s) - P.v (j + s) = P.v (j + s + 1) - P.v (j + s)
    rw [add_right_comm]
  show ‖(rotP P s).e j‖⁻¹ • (rotP P s).e j = ‖P.e (j + s)‖⁻¹ • P.e (j + s)
  rw [h]

theorem rotP_flux (P : ConvPoly M) (s : Fin M) (f : Dir → ℝ) : (rotP P s).flux f = P.flux f := by
  unfold ConvPoly.flux
  have h := Equiv.sum_comp (Equiv.addRight s) (fun j => P.side j • f (P.sideDir j))
  rw [← h]
  exact Finset.sum_congr rfl (fun j _ => by rw [rotP_side, rotP_sideDir]; rfl)

section PolyLemmas
variable {α : ℝ} {hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi}

theorem poly3_kill (P : ConvPoly 3) (hzero : ∀ θ₀ : Real.Angle, P.flux (fAlphaAt α hα θ₀).weight = 0)
    (hall : ∀ i, P.angle i = Real.pi / 3 ∨ P.angle i = 2 * Real.pi / 3) : False := by
  have hsum : ∑ i : Fin 3, P.angle i = Real.pi := by rw [poly_angle_sum]; norm_num
  rw [Fin.sum_univ_three] at hsum
  have hA : ∀ i, P.angle i = Real.pi / 3 := by
    have hpi := Real.pi_pos
    rcases hall 0 with h0 | h0 <;> rcases hall 1 with h1 | h1 <;> rcases hall 2 with h2 | h2 <;>
      first | (exfalso; linarith) | (intro i; fin_cases i <;> assumption)
  obtain ⟨-, -, hP⟩ := lemma72_three α hα P hA
  have h0 : P.Phi α hα = 0 := hzero _
  have := side_pos P 0
  linarith

theorem poly4_trap_kill (P : ConvPoly 4) (hzero : ∀ θ₀ : Real.Angle, P.flux (fAlphaAt α hα θ₀).weight = 0) (s : Fin 4)
    (h1 : P.angle (1 + s) = Real.pi / 3) (h2 : P.angle (2 + s) = 2 * Real.pi / 3) (h3 : P.angle (3 + s) = 2 * Real.pi / 3) : False := by
  obtain ⟨-, -, hP⟩ := lemma72_four α hα (rotP P s) (by rw [rotP_angle]; exact h1) (by rw [rotP_angle]; exact h2) (by rw [rotP_angle]; exact h3)
  have h0 : (rotP P s).Phi α hα = 0 := by unfold ConvPoly.Phi; rw [rotP_flux]; exact hzero _
  have := side_pos (rotP P s) 3
  linarith

theorem poly5_kill (P : ConvPoly 5) (hzero : ∀ θ₀ : Real.Angle, P.flux (fAlphaAt α hα θ₀).weight = 0) (s : Fin 5)
    (h1 : P.angle (1 + s) = Real.pi / 3) (h2 : P.angle (2 + s) = 2 * Real.pi / 3) (h3 : P.angle (3 + s) = 2 * Real.pi / 3)
    (h4 : P.angle (4 + s) = 2 * Real.pi / 3) : False := by
  obtain ⟨-, -, hP⟩ := lemma72_five α hα (rotP P s) (by rw [rotP_angle]; exact h1) (by rw [rotP_angle]; exact h2) (by rw [rotP_angle]; exact h3)
    (by rw [rotP_angle]; exact h4)
  have h0 : (rotP P s).Phi α hα = 0 := by unfold ConvPoly.Phi; rw [rotP_flux]; exact hzero _
  have := side_pos (rotP P s) 3
  linarith

/-- The hexagon case: all angles `2pi/3` and the sides are centrally symmetric. -/
theorem poly6_sym (P : ConvPoly 6) (hzero : ∀ θ₀ : Real.Angle, P.flux (fAlphaAt α hα θ₀).weight = 0)
    (hall : ∀ i, P.angle i = Real.pi / 3 ∨ P.angle i = 2 * Real.pi / 3) :
    (∀ i, P.angle i = 2 * Real.pi / 3) ∧ ∀ i : Fin 6, P.side i = P.side (i + 3) := by
  have hsum : ∑ i : Fin 6, P.angle i = 4 * Real.pi := by rw [poly_angle_sum]; norm_num
  rw [Fin.sum_univ_six] at hsum
  have hpi := Real.pi_pos
  have hA : ∀ i, P.angle i = 2 * Real.pi / 3 := by
    rcases hall 0 with h0 | h0 <;> rcases hall 1 with h1 | h1 <;> rcases hall 2 with h2 | h2 <;>
    rcases hall 3 with h3 | h3 <;> rcases hall 4 with h4 | h4 <;> rcases hall 5 with h5 | h5 <;>
      first | (exfalso; linarith) | (intro i; fin_cases i <;> assumption)
  refine ⟨hA, ?_⟩
  obtain ⟨e1, e2, hP⟩ := lemma72_six α hα P hA
  have h0 : P.Phi α hα = 0 := hzero _
  intro i
  fin_cases i <;> simp <;> linarith

end PolyLemmas

set_option maxHeartbeats 6400000 in
/-- **IIIc, `alpha/pi` irrational: conclusion (i) or (vi) of Theorem 2.1.** -/
theorem iiic_final {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) {α : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hm0 : angleAt T.C.model 0 = α) (hm1 : angleAt T.C.model 1 = Real.pi / 3 - α) (hm2 : angleAt T.C.model 2 = 2 * Real.pi / 3)
    (hab : Comm (slen T.C 0) (slen T.C 1)) (hac : ¬ Comm (slen T.C 0) (slen T.C 2)) : Concl1 T.C T.P ∨ Concl6 T.C T.P := by
  classical
  have hmodel : T.C.model.TwoPiThreeData α (slen T.C 0) (slen T.C 1) (slen T.C 2) :=
    ⟨1, by simpa using hm0, rfl, by simpa using hm1, rfl, by simpa using hm2, rfl⟩
  have hRat := polytiling_rational T hreg hab hac
  have hzero : ∀ θ₀ : Real.Angle, T.P.flux (fAlphaAt α hα θ₀).weight = 0 := fun θ₀ => iiic_flux_zero T hreg hα hmodel hab hac θ₀
  obtain ⟨idx, hA, hcnt⟩ := hreg
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hm0' : T.C.model.angleAt 0 = α := hm0
  have hm1' : T.C.model.angleAt 1 = Real.pi / 3 - α := hm1
  have hm2' : T.C.model.angleAt 2 = 2 * Real.pi / 3 := hm2
  have hαβ : T.C.model.angleAt 0 + T.C.model.angleAt 1 = Real.pi / 3 := by rw [hm0', hm1']; ring
  have hall : ∀ i : Fin M, T.P.angle i = Real.pi / 3 ∨ T.P.angle i = 2 * Real.pi / 3 := by
    intro i
    have := polygon_angle_2pi3 T.C T.P T.region_eq idx hA hm2' hαβ (fun X => hcnt X) (i - 1)
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
  have hM : M = 3 ∨ M = 4 ∨ M = 5 ∨ M = 6 := by omega
  rcases hM with rfl | rfl | rfl | rfl
  · exact absurd (poly3_kill T.P hzero hall) id
  · left
    have hsum4 : ∑ i : Fin 4, T.P.angle i = 2 * Real.pi := by rw [hsum]; norm_num
    rw [Fin.sum_univ_four] at hsum4
    have key : (∀ i : Fin 4, T.P.v i + T.P.v (i + 2) = T.P.v (i + 1) + T.P.v (i + 3)) ∧ (T.P.angle 0 = 2 * Real.pi / 3 ∨ T.P.angle 1 = 2 * Real.pi / 3) := by
      rcases hall 0 with a0 | a0 <;> rcases hall 1 with a1 | a1 <;> rcases hall 2 with a2 | a2 <;> rcases hall 3 with a3 | a3 <;>
        first
        | (exfalso; linarith)
        | (exfalso; exact poly4_trap_kill T.P hzero 0 (by simpa using a1) (by simpa using a2) (by simpa using a3))
        | (exfalso; exact poly4_trap_kill T.P hzero 1 (by simpa using a2) (by simpa using a3) (by simpa using a0))
        | (exfalso; exact poly4_trap_kill T.P hzero 2 (by simpa using a3) (by simpa using a0) (by simpa using a1))
        | (exfalso; exact poly4_trap_kill T.P hzero 3 (by simpa using a0) (by simpa using a1) (by simpa using a2))
        | exact ⟨par_all T.P 0 (quad_parallelogram T.P 0 (by simpa using a1) (by simpa using a2) (by simpa using a3)), Or.inr a1⟩
        | exact ⟨par_all T.P 3 (quad_parallelogram T.P 3 (by simpa using a0) (by simpa using a1) (by simpa using a2)), Or.inl a0⟩
    have hex : ∃ i : Fin 4, T.P.angle i = angleAt T.C.model 2 := by
      rcases key.2 with h | h
      · exact ⟨0, by rw [h, hm2]⟩
      · exact ⟨1, by rw [h, hm2]⟩
    have hratio' : ∃ q : ℚ, T.P.side 0 / T.P.side 1 = q * (Real.sin (angleAt T.C.model 0) / Real.sin (angleAt T.C.model 1)) := by
      obtain ⟨m1, n1, hm1', hn1, e1⟩ := hRat 0 1
      obtain ⟨m2, n2, hm2', hn2, e2⟩ := hab
      have hs1 : 0 < T.P.side 1 := side_pos T.P 1
      have hsb : 0 < slen T.C 1 := RG.slen_pos T.C 1
      refine ⟨((n1 * m2 : ℕ) : ℚ) / ((m1 * n2 : ℕ) : ℚ), ?_⟩
      have hsr : Real.sin (angleAt T.C.model 0) / Real.sin (angleAt T.C.model 1) = slen T.C 0 / slen T.C 1 := sin_ratio_eq T.C
      rw [hsr]
      have hm1'' : (m1 : ℝ) ≠ 0 := by positivity
      have hn2' : (n2 : ℝ) ≠ 0 := by positivity
      have hm2'' : (m2 : ℝ) ≠ 0 := by positivity
      push_cast
      rw [div_eq_iff hs1.ne']
      field_simp
      linear_combination ((n2 : ℝ) * slen T.C 1) * e1 - ((n1 : ℝ) * T.P.side 1) * e2
    exact ⟨⟨rfl, key.1⟩, hex, Or.inl hratio'⟩
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
  · right
    obtain ⟨hang, hsym⟩ := poly6_sym T.P hzero hall
    exact ⟨rfl, hRat, hsym, hang, Or.inr hm2, hratio⟩

end Erdos634.Draft.LaczFormal.IIIc

#print axioms Erdos634.Draft.LaczFormal.IIIc.poly3_kill
#print axioms Erdos634.Draft.LaczFormal.IIIc.poly6_sym
#print axioms Erdos634.Draft.LaczFormal.IIIc.iiic_final
