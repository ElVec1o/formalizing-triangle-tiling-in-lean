-- Draft/LaczFormalCombi4d.lean -- Laczkovich, DCG 48 (2012), Lemma 3.8, IRREGULAR case: the assembled theorem `lem38_irregular`
-- (see Combi4c for the statement, the ingredients and what is NOT covered: the regular case).
-- NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Comput. Geom. 48 (2012), Lemma 3.8; Combinatorica 10 (1990)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalCombi4c

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement
open Erdos634.Draft.LaczFormal.RG

namespace Erdos634.Laczkovich.Combi4

/-- **Lemma 3.8 of Laczkovich (2012), irregular case, for a real tiling.**  `T` a congruent dissection of a rectangle (all angles `pi/2`) whose model has a right angle
at vertex 2, `idx` an angle-preserving vertex correspondence at which the corner counts of types 0 and 1 differ somewhere (irregularity in the pair `(alpha, beta)`):
the ratio of the two sides of the rectangle is a rational multiple of `a/b` (in one of the two orders). -/
theorem lem38_irregular {N : ℕ} (T : PolyTiling N 4) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidxA : ∀ i v, T.C.model.angleAt (idx i v) = (T.C.tile i).angleAt v) (hang : ∀ i, T.P.angle i = Real.pi / 2)
    (hγ : T.C.model.angleAt 2 = Real.pi / 2) (hirr : ∃ X, cnt T.C idx X 0 ≠ cnt T.C idx X 1) :
    (∃ q : ℚ, T.P.side 0 / T.P.side 3 = q * (sideOpp T.C.model 0 / sideOpp T.C.model 1)) ∨
    (∃ q : ℚ, T.P.side 3 / T.P.side 0 = q * (sideOpp T.C.model 0 / sideOpp T.C.model 1)) := by
  classical
  have hpi := Real.pi_pos
  set Mo := T.C.model with hMo
  set a := sideOpp Mo 0 with ha
  set b := sideOpp Mo 1 with hb
  set c := sideOpp Mo 2 with hc
  set α0 := Mo.angleAt 0 with hα0
  set α1 := Mo.angleAt 1 with hα1
  have hsum : α0 + α1 + Mo.angleAt 2 = Real.pi := Erdos634.Draft.LaczFormal.angleAt_sum Mo
  have hsum' : α0 + α1 = Real.pi / 2 := by rw [hγ] at hsum; linarith
  have hp0 : 0 < α0 := model_angle_pos' T.C 0
  have hp1 : 0 < α1 := model_angle_pos' T.C 1
  have hcpos : 0 < c := Erdos634.Draft.LaczFormal.Thm21.sideOpp_pos_aux Mo 2
  -- law of sines
  have los2 := Erdos634.TriLawSin.sin_angleAt_mul_sideOpp Mo 2
  have los1 := Erdos634.TriLawSin.sin_angleAt_mul_sideOpp Mo 1
  have e30 : (2 + 1 : Fin 3) = 0 := by decide
  have e21 : (1 + 1 : Fin 3) = 2 := by decide
  rw [e30] at los2
  rw [e21] at los1
  have hsg : Real.sin (angleAt Mo 2) = 1 := by
    show Real.sin (Mo.angleAt 2) = 1
    rw [hγ]; exact Real.sin_pi_div_two
  have hA : a = Real.sin α0 * c := by
    have := los2; rw [hsg] at this; simp only [one_mul] at this
    show sideOpp Mo 0 = _
    have h' : Real.sin (angleAt Mo 0) * sideOpp Mo 2 = sideOpp Mo 0 := this
    exact h'.symm
  have hB : b = Real.sin α1 * c := by
    have := los1; rw [hsg] at this; simp only [one_mul] at this
    have h' : sideOpp Mo 1 = Real.sin (angleAt Mo 1) * sideOpp Mo 2 := this
    exact h'
  have hα1' : α1 = Real.pi / 2 - α0 := by linarith
  have hsin1 : Real.sin α1 = Real.cos α0 := by rw [hα1', Real.sin_pi_div_two_sub]
  have hsin0 : Real.sin α0 = Real.cos α1 := by rw [hα1', Real.cos_pi_div_two_sub]
  -- sides and area
  have hrect := rect_of_angles T.P hang
  have harea0 := poly4_area T hrect (Or.inl (by rw [hang 0]; exact hγ.symm))
  obtain ⟨x, y, z, hW⟩ := side_comb T 0
  obtain ⟨u, v, w, hH⟩ := side_comb T 3
  have hWp := side_pos T.P 0
  have hHp := side_pos T.P 3
  have hx : x + y + z ≠ 0 := by
    intro h0
    have hx0 : x = 0 := by omega
    have hy0 : y = 0 := by omega
    have hz0 : z = 0 := by omega
    rw [hx0, hy0, hz0] at hW; simp at hW; linarith
  have hu : u + v + w ≠ 0 := by
    intro h0
    have hx0 : u = 0 := by omega
    have hy0 : v = 0 := by omega
    have hz0 : w = 0 := by omega
    rw [hx0, hy0, hz0] at hH; simp at hH; linarith
  have hapos : 0 < a := Erdos634.Draft.LaczFormal.Thm21.sideOpp_pos_aux Mo 0
  have hbpos : 0 < b := Erdos634.Draft.LaczFormal.Thm21.sideOpp_pos_aux Mo 1
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · exfalso
      subst h0
      rw [Nat.cast_zero, zero_mul] at harea0
      nlinarith [mul_pos hWp hHp, mul_pos hapos hbpos]
    · exact h0
  have hWd : T.P.side 0 = x * a + y * b + z * c := hW
  have hHd : T.P.side 3 = u * a + v * b + w * c := hH
  have hAreaD : (N : ℝ) * (a * b) = 2 * (T.P.side 0 * T.P.side 3) := harea0
  -- the vertex relation for a pair of types (l, l') with l' < l at a vertex
  have vrel : ∀ (l l' : Fin 3), l ≠ 2 → l' ≠ 2 → l ≠ l' → (∃ X, cnt T.C idx X l ≠ cnt T.C idx X l') →
      Mo.angleAt l + Mo.angleAt l' = Real.pi / 2 →
      ∃ m s : ℕ, 0 < m ∧ s ≤ 4 ∧ (m : ℝ) * Mo.angleAt l = s * Real.pi / 2 := by
    intro l l' hl hl' hll' hne hsl
    obtain ⟨X, hXv, hXlt⟩ := exists_gt_cnt T.C idx l l' hne
    obtain ⟨e, he, hAs⟩ := Asum_half T idx hidxA hang hXv
    have hAs' : Asum T.C idx X = (cnt T.C idx X 0 : ℝ) * Mo.angleAt 0 + (cnt T.C idx X 1 : ℝ) * Mo.angleAt 1
        + (cnt T.C idx X 2 : ℝ) * Mo.angleAt 2 := by
      unfold Asum; rw [Fin.sum_univ_three]
    have hX : (cnt T.C idx X 0 : ℝ) * Mo.angleAt 0 + (cnt T.C idx X 1 : ℝ) * Mo.angleAt 1
        + (cnt T.C idx X 2 : ℝ) * (Real.pi / 2) = e * (Real.pi / 2) := by
      rw [← hAs, hAs', hγ]
    have hcase : (l = 0 ∧ l' = 1) ∨ (l = 1 ∧ l' = 0) := by
      fin_cases l <;> fin_cases l' <;> simp_all
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine rel_extract (Mo.angleAt 0) (Mo.angleAt 1) hp0 hsl (cnt T.C idx X 0) (cnt T.C idx X 1) (cnt T.C idx X 2) e he hXlt ?_
      linarith
    · refine rel_extract (Mo.angleAt 1) (Mo.angleAt 0) hp1 hsl (cnt T.C idx X 1) (cnt T.C idx X 0) (cnt T.C idx X 2) e he hXlt ?_
      linarith
  rcases lt_trichotomy α0 α1 with hlt | heq | hgt
  · -- alpha0 < alpha1: the big angle is alpha1, legs swapped
    have hθ1 : Real.pi / 4 < α1 := by linarith
    have hθ2 : α1 < Real.pi / 2 := by linarith
    obtain ⟨m, s, hm, hs4, hmα⟩ := vrel 1 0 (by decide) (by decide) (by decide)
      (by obtain ⟨X, hX⟩ := hirr; exact ⟨X, fun h => hX h.symm⟩) (by linarith)
    have hW' : T.P.side 0 = (y : ℝ) * (c * Real.sin α1) + x * (c * Real.cos α1) + z * c := by
      rw [hWd, hA, hB, hsin0]; ring
    have hH' : T.P.side 3 = (v : ℝ) * (c * Real.sin α1) + u * (c * Real.cos α1) + w * c := by
      rw [hHd, hA, hB, hsin0]; ring
    have harea' : (N : ℝ) * ((c * Real.sin α1) * (c * Real.cos α1)) = 2 * (T.P.side 0 * T.P.side 3) := by
      rw [← hAreaD, hA, hB, hsin0]; ring
    have hmain := lem38_rect_arith α1 c hcpos hθ1 hθ2 m s hm hs4 hmα (T.P.side 0) (T.P.side 3) y x z v u w N hNpos hW' hH'
      (by omega) (by omega) harea'
    have hr : (c * Real.sin α1) / (c * Real.cos α1) = b / a := by
      rw [hA, hB, hsin0]; ring
    rw [hr] at hmain
    have hWH : 0 < T.P.side 0 / T.P.side 3 := div_pos hWp hHp
    have hba : 0 < b / a := div_pos hbpos hapos
    rcases hmain with ⟨q, hq⟩ | ⟨q, hq⟩
    · right
      have hq0 : (q : ℝ) ≠ 0 := by
        intro h0; rw [h0, zero_mul] at hq; linarith
      refine ⟨q⁻¹, ?_⟩
      have : T.P.side 3 / T.P.side 0 = (T.P.side 0 / T.P.side 3)⁻¹ := by rw [inv_div]
      rw [this, hq]; push_cast
      field_simp
    · left
      have hq0 : (q : ℝ) ≠ 0 := by
        intro h0; rw [h0, zero_mul] at hq
        have : 0 < T.P.side 3 / T.P.side 0 := div_pos hHp hWp
        linarith
      refine ⟨q⁻¹, ?_⟩
      have : T.P.side 0 / T.P.side 3 = (T.P.side 3 / T.P.side 0)⁻¹ := by rw [inv_div]
      rw [this, hq]; push_cast
      field_simp
  · -- alpha0 = alpha1 = pi/4: isosceles right
    have h4 : α0 = Real.pi / 4 := by linarith
    have hba : b = a := by rw [hA, hB, heq]
    have hsq : Real.sin α0 = Real.sqrt 2 / 2 := by rw [h4]; exact Real.sin_pi_div_four
    have hca : c = a * Real.sqrt 2 := by
      rw [hA, hsq]
      have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
      linear_combination (-(c / 2)) * h2
    have hW' : T.P.side 0 = (x : ℝ) * a + y * a + z * (a * Real.sqrt 2) := by rw [hWd, hba, hca]
    have hH' : T.P.side 3 = (u : ℝ) * a + v * a + w * (a * Real.sqrt 2) := by rw [hHd, hba, hca]
    have harea' : (N : ℝ) * (a * a) = 2 * (T.P.side 0 * T.P.side 3) := by rw [← hAreaD, hba]
    obtain ⟨q, hq⟩ := iso_rect_arith a hapos _ _ x y z u v w N hW' hH' hWp hHp harea'
    left
    refine ⟨q, ?_⟩
    rw [hq, hba]
  · -- alpha0 > alpha1
    have hθ1 : Real.pi / 4 < α0 := by linarith
    have hθ2 : α0 < Real.pi / 2 := by linarith
    obtain ⟨m, s, hm, hs4, hmα⟩ := vrel 0 1 (by decide) (by decide) (by decide) hirr (by linarith)
    have hW' : T.P.side 0 = (x : ℝ) * (c * Real.sin α0) + y * (c * Real.cos α0) + z * c := by
      rw [hWd, hA, hB, hsin1]; ring
    have hH' : T.P.side 3 = (u : ℝ) * (c * Real.sin α0) + v * (c * Real.cos α0) + w * c := by
      rw [hHd, hA, hB, hsin1]; ring
    have harea' : (N : ℝ) * ((c * Real.sin α0) * (c * Real.cos α0)) = 2 * (T.P.side 0 * T.P.side 3) := by
      rw [← hAreaD, hA, hB, hsin1]; ring
    have hmain := lem38_rect_arith α0 c hcpos hθ1 hθ2 m s hm hs4 hmα (T.P.side 0) (T.P.side 3) x y z u v w N hNpos hW' hH'
      hx hu harea'
    have hr : (c * Real.sin α0) / (c * Real.cos α0) = a / b := by
      rw [hA, hB, hsin1]; ring
    rw [hr] at hmain
    exact hmain

end Erdos634.Laczkovich.Combi4
#print axioms Erdos634.Laczkovich.Combi4.lem38_irregular
