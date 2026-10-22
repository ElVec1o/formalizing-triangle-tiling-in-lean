import Erdos634.Draft.BeesonH1
import Erdos634.Draft.LaczFormal53Disp
import Erdos634.Draft.A1FieldClause
import Erdos634.Draft.FluxDSideWord
import Erdos634.ARAGeom

/-!
# Laczkovich Theorem 5.3, the instance Beeson uses (tile `(pi/4, pi/8, 5 pi/8)`): `BeesonH1.Lacz53` is a THEOREM

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Thm 5.1 and 5.3; the printed proof of 5.3 treats the cases
(iv) and (v) and says "similar arguments apply" for (vi), (vii) -- the case used here is (vii), NOT printed), Beeson (arXiv 1206.2229
v4, Lemma 1), Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.

Own proof (no use of Theorem 5.1): the target angle at each vertex is a sum of tile angles (`corner_fig'`, the proof of
`BeesonColoring.corner_fig` with `alpha <> beta` in place of irrationality), so it is `U pi/8`, `U` a positive integer, total 8; not a
permutation of `(2,1,5)` (that is the similar case).  The remaining triples `(1,1,6)`, `(1,3,4)`, `(2,2,4)`, `(2,3,3)` are excluded
by the side words (`side_word_threeAlpha`), the law of sines (`A1Field.oppLen_eq`), and the area relation (`ARA.area_heron`), in the
basis `1, sqrt2, sin(pi/8), sqrt2 sin(pi/8)` (`LaczFormal53Basis`, `LaczFormal53Shapes`, `LaczFormal53Disp`).
-/

namespace Erdos634.Lacz53

open Erdos634 Erdos634.Geometry Erdos634.BeesonColoring E4 Erdos634.Geometry.A1Field

open scoped Classical

/-- `cos (pi/8) = (1 + sqrt2) sin (pi/8)`. -/
theorem cos8_eq : Real.cos (Real.pi / 8) = (1 + Real.sqrt 2) * uu := by
  have hs := s2_sq
  have hu := uu_sq
  have hc : Real.cos (Real.pi / 8) ^ 2 = (2 + Real.sqrt 2) / 4 := by
    rw [Real.cos_pi_div_eight, div_pow, Real.sq_sqrt (by positivity)]; norm_num
  have hpos : 0 < Real.cos (Real.pi / 8) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have h2 : ((1 + Real.sqrt 2) * uu) ^ 2 = (2 + Real.sqrt 2) / 4 := by
    nlinarith [hs, hu]
  have h3 : 0 < (1 + Real.sqrt 2) * uu := mul_pos (by positivity) uu_pos
  exact (sq_eq_sq₀ hpos.le h3.le).1 (by rw [hc, h2])

theorem ev_sE {U : ℕ} (h1 : 1 ≤ U) (h6 : U ≤ 6) : (sE U).ev = Real.sin ((U : ℝ) * (Real.pi / 8)) := by
  have c8 := cos8_eq
  interval_cases U
  · simp [sE, ev_uE, uu]
  · rw [show ((2 : ℕ) : ℝ) * (Real.pi / 8) = Real.pi / 4 by push_cast; ring, Real.sin_pi_div_four]
    simp [sE, ev_wE]
  · rw [show ((3 : ℕ) : ℝ) * (Real.pi / 8) = Real.pi / 2 - Real.pi / 8 by push_cast; ring, Real.sin_pi_div_two_sub, c8]
    simp [sE, ev_vE]
  · rw [show ((4 : ℕ) : ℝ) * (Real.pi / 8) = Real.pi / 2 by push_cast; ring, Real.sin_pi_div_two]
    simp [sE, ev_oneE]
  · rw [show ((5 : ℕ) : ℝ) * (Real.pi / 8) = Real.pi - (Real.pi / 2 - Real.pi / 8) by push_cast; ring, Real.sin_pi_sub,
      Real.sin_pi_div_two_sub, c8]
    simp [sE, ev_vE]
  · rw [show ((6 : ℕ) : ℝ) * (Real.pi / 8) = Real.pi - Real.pi / 4 by push_cast; ring, Real.sin_pi_sub, Real.sin_pi_div_four]
    simp [sE, ev_wE]

theorem hh_tile : hhE wE uE vE = ofQ (1 / 4) := by
  ext <;> simp [hhE, E4.mul, E4.add, E4.smul, E4.sub, wE, uE, vE, ofQ] <;> norm_num

/-- **`corner_fig` without irrationality**: only `alpha <> beta` is used. -/
theorem corner_fig' {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hαβ : α ≠ β) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) (k : Fin 3) :
    vcount D k Real.pi = 0 ∧
    (vcount D k α : ℝ) * α + (vcount D k β : ℝ) * β + (vcount D k (2 * α + β) : ℝ) * (2 * α + β)
      = D.target.angleAt k := by
  obtain ⟨ha, hb, -, hαpos, hβpos⟩ := model_abc_pos h
  have hαπ : α ≠ Real.pi := by intro e; linarith
  have hβπ : β ≠ Real.pi := by intro e; linarith
  have hπ0 : Real.pi ≠ 0 := Real.pi_ne_zero
  have hm := Erdos634.TilePlacement.corner_multiplicities D.toDissection α β (2 * α + β) hαβ
    (by intro e; linarith) hαπ hαpos.ne' (by intro e; linarith) hβπ hβpos.ne'
    (by intro e; linarith) (by intro e; linarith) hπ0 k (fun i => localAngle_mem_3a D h k i)
  have hpos := D.target.angleAt_pos' k
  have hsum := D.target.angleAt_sum
  have hlt : D.target.angleAt k < Real.pi := by
    have := D.target.angleAt_pos' 0
    have := D.target.angleAt_pos' 1
    have := D.target.angleAt_pos' 2
    fin_cases k <;> simp <;> linarith
  have hpi : vcount D k Real.pi = 0 := by
    by_contra hne
    have h1 : (1 : ℝ) ≤ (vcount D k Real.pi : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
    have hp : (vcount D k Real.pi : ℝ) * Real.pi ≥ Real.pi := by nlinarith [Real.pi_pos]
    have := mul_nonneg (Nat.cast_nonneg (vcount D k α) : (0:ℝ) ≤ _) hαpos.le
    have := mul_nonneg (Nat.cast_nonneg (vcount D k β) : (0:ℝ) ≤ _) hβpos.le
    have := mul_nonneg (Nat.cast_nonneg (vcount D k (2 * α + β)) : (0:ℝ) ≤ _) (by linarith : (0:ℝ) ≤ 2 * α + β)
    unfold vcount at *
    change _ = D.target.angleAt k at hm
    linarith
  refine ⟨hpi, ?_⟩
  unfold vcount at hpi ⊢
  have := hm
  rw [hpi] at this
  change _ = D.target.angleAt k at this
  simpa using this

end Erdos634.Lacz53

namespace Erdos634.BeesonH1

open Erdos634 Erdos634.Geometry Erdos634.BeesonColoring Erdos634.Lacz53 Erdos634.Lacz53.E4
  Erdos634.Geometry.A1Field

open scoped Classical

set_option maxHeartbeats 8000000 in
/-- **Laczkovich Theorem 5.3 for the tile `(pi/4, pi/8, 5 pi/8)`** (case (vii)), proved: `Lacz53` holds. -/
theorem lacz53_thm : Lacz53 := by
  intro N D α β a b c h hα hβ hns
  have hpi := Real.pi_pos
  have hrel : 3 * α + 2 * β = Real.pi := by rw [hα, hβ]; ring
  have hαβ : α ≠ β := by intro e; rw [hα, hβ] at e; linarith
  have hγ : 2 * α + β = 5 * (Real.pi / 8) := by rw [hα, hβ]; ring
  obtain ⟨σ, h0, ha, h1, hb, h2, hc⟩ := id h
  have hDm0 : 0 < circD D.model := circD_pos _
  have hDt0 : 0 < circD D.target := circD_pos _
  have hw : Real.sin α = Real.sqrt 2 / 2 := by rw [hα]; exact Real.sin_pi_div_four
  have hu : Real.sin β = uu := by rw [hβ]; rfl
  have hv5 : Real.sin (5 * (Real.pi / 8)) = (1 + Real.sqrt 2) * uu := by
    have := ev_sE (U := 5) (by norm_num) (by norm_num)
    have e : (sE 5).ev = (1 + Real.sqrt 2) * uu := ev_vE
    rw [e] at this; simpa using this.symm
  have hv : Real.sin (2 * α + β) = (1 + Real.sqrt 2) * uu := by rw [hγ]; exact hv5
  have ha' : a = circD D.model * (Real.sqrt 2 / 2) := by rw [← ha, oppLen_eq _ (σ 0), h0, hw]
  have hb' : b = circD D.model * uu := by rw [← hb, oppLen_eq _ (σ 1), h1, hu]
  have hc' : c = circD D.model * ((1 + Real.sqrt 2) * uu) := by rw [← hc, oppLen_eq _ (σ 2), h2, hv]
  choose n m k hw3 using fun j => D.side_word_threeAlpha h j
  have fig : ∀ j : Fin 3, ∃ U : ℕ, D.target.angleAt j = (U : ℝ) * (Real.pi / 8) := by
    intro j
    obtain ⟨-, e⟩ := corner_fig' D hαβ hrel h j
    refine ⟨2 * vcount D j α + vcount D j β + 5 * vcount D j (2 * α + β), ?_⟩
    rw [← e]; push_cast
    linear_combination (vcount D j α : ℝ) * hα + (vcount D j β : ℝ) * hβ +
      (vcount D j (2 * α + β) : ℝ) * (2 * hα + hβ)
  choose U hU using fig
  have hU1 : ∀ j, 1 ≤ U j := by
    intro j
    have h0 := D.target.angleAt_pos' j
    rw [hU j] at h0
    rcases Nat.eq_zero_or_pos (U j) with hz | hz
    · rw [hz] at h0; simp at h0
    · exact hz
  have hsum : U 0 + U 1 + U 2 = 8 := by
    have := D.target.angleAt_sum
    rw [hU 0, hU 1, hU 2] at this
    have hh : ((U 0 : ℝ) + U 1 + U 2) = 8 := by
      have h8 : ((U 0 : ℝ) + U 1 + U 2 - 8) * (Real.pi / 8) = 0 := by linarith
      rcases mul_eq_zero.1 h8 with h | h
      · linarith
      · exfalso; linarith
    exact_mod_cast hh
  have hU6 : ∀ j, U j ≤ 6 := by
    intro j
    have := hU1 0; have := hU1 1; have := hU1 2
    fin_cases j <;> simp <;> omega
  have hT : ∀ j, D.target.oppLen j = circD D.target * Real.sin ((U j : ℝ) * (Real.pi / 8)) := by
    intro j; rw [oppLen_eq _ j, hU j]
  have hLev : ∀ j, D.target.oppLen j = circD D.model * (sideE (n j : ℚ) (m j) (k j)).ev := by
    intro j
    rw [hw3 j, ha', hb', hc', ev_sideE]; push_cast; ring
  have hposN : ∀ j, 0 < n j + m j + k j := by
    intro j
    by_contra hz
    have hz' : n j = 0 ∧ m j = 0 ∧ k j = 0 := by omega
    have := D.target.oppLen_pos j
    rw [hLev j, ev_sideE, hz'.1, hz'.2.1, hz'.2.2] at this
    simp at this
  have prop : ∀ i j : Fin 3, (sideE (n i : ℚ) (m i) (k i)).mul (sE (U j))
      = (sideE (n j : ℚ) (m j) (k j)).mul (sE (U i)) := by
    intro i j
    apply E4.ev_inj
    rw [ev_mul, ev_mul, ev_sE (hU1 j) (hU6 j), ev_sE (hU1 i) (hU6 i)]
    have ei := hLev i; have ej := hLev j
    rw [hT i] at ei; rw [hT j] at ej
    apply mul_left_cancel₀ hDm0.ne'
    linear_combination (-(Real.sin ((U j : ℝ) * (Real.pi / 8)))) * ei +
      Real.sin ((U i : ℝ) * (Real.pi / 8)) * ej
  have hnot : ¬ ((U 0 = 1 ∨ U 1 = 1 ∨ U 2 = 1) ∧ (U 0 = 2 ∨ U 1 = 2 ∨ U 2 = 2) ∧
      (U 0 = 5 ∨ U 1 = 5 ∨ U 2 = 5)) := by
    intro hc
    have h6 : (U 0 = 2 ∧ U 1 = 1 ∧ U 2 = 5) ∨ (U 0 = 2 ∧ U 1 = 5 ∧ U 2 = 1) ∨ (U 0 = 1 ∧ U 1 = 2 ∧ U 2 = 5) ∨
        (U 0 = 1 ∧ U 1 = 5 ∧ U 2 = 2) ∨ (U 0 = 5 ∧ U 1 = 2 ∧ U 2 = 1) ∨ (U 0 = 5 ∧ U 1 = 1 ∧ U 2 = 2) := by
      omega
    refine hns ?_
    simp only [Triple3]
    rw [hU 0, hU 1, hU 2, hγ, hα, hβ]
    rcases h6 with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ <;>
      rw [e0, e1, e2] <;> push_cast <;>
      first
      | exact Or.inl ⟨by ring1, by ring1, by ring1⟩
      | exact Or.inr (Or.inl ⟨by ring1, by ring1, by ring1⟩)
      | exact Or.inr (Or.inr (Or.inl ⟨by ring1, by ring1, by ring1⟩))
      | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by ring1, by ring1, by ring1⟩)))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by ring1, by ring1, by ring1⟩))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by ring1, by ring1, by ring1⟩))))
  -- area
  have hA := Erdos634.ARA.area_heron D
  rw [← Erdos634.ARA.Hh_perm D.model σ, ha, hb, hc, ha', hb', hc', hLev 0, hLev 1, hLev 2] at hA
  have hHt := congrArg E4.ev hh_tile
  rw [ev_hhE, ev_ofQ, ev_wE, ev_uE, ev_vE] at hHt
  push_cast at hHt
  unfold Erdos634.ARA.Hh at hA
  have hDm4 : circD D.model ^ 4 ≠ 0 := by positivity
  have key : (N : ℝ) ^ 2 / 4 = 2 * (sideE (n 0 : ℚ) (m 0) (k 0)).ev ^ 2 * (sideE (n 1 : ℚ) (m 1) (k 1)).ev ^ 2 +
      2 * (sideE (n 1 : ℚ) (m 1) (k 1)).ev ^ 2 * (sideE (n 2 : ℚ) (m 2) (k 2)).ev ^ 2 +
      2 * (sideE (n 2 : ℚ) (m 2) (k 2)).ev ^ 2 * (sideE (n 0 : ℚ) (m 0) (k 0)).ev ^ 2 -
      (sideE (n 0 : ℚ) (m 0) (k 0)).ev ^ 4 - (sideE (n 1 : ℚ) (m 1) (k 1)).ev ^ 4 -
      (sideE (n 2 : ℚ) (m 2) (k 2)).ev ^ 4 := by
    apply mul_left_cancel₀ hDm4
    linear_combination hA + (-((N : ℝ) ^ 2 * circD D.model ^ 4)) * hHt
  have hH0 : hhE (sideE (n 0 : ℚ) (m 0) (k 0)) (sideE (n 1 : ℚ) (m 1) (k 1)) (sideE (n 2 : ℚ) (m 2) (k 2))
      = ofQ ((N : ℚ) ^ 2 / 4) := by
    apply E4.ev_inj
    rw [ev_hhE, ev_ofQ]; push_cast
    linear_combination -key
  exact main_alg (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (by exact_mod_cast hposN 0) (by exact_mod_cast hposN 1) (by exact_mod_cast hposN 2)
    (hU1 0) (hU1 1) (hU1 2) hsum hnot (prop 0 1) (prop 0 2) (prop 1 2) hH0

/-- **Beeson Lemma 1 (H1)** with `Lacz53` discharged: the single remaining hypothesis is `Lacz51` (Laczkovich Thm 5.1). -/
theorem lemma1_of_lacz51 (h51 : Lacz51) {N : ℕ} (D : CongruentDissection N)
    {α β a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) :
    ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi :=
  lemma1_of_laczkovich h51 lacz53_thm D hrel h hns

/-- `lemma6` with `H1` discharged up to `Lacz51`. -/
theorem lemma6_of_lacz51 (h51 : Lacz51) {N : ℕ} (D : CongruentDissection N)
    {α β a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (h : D.model.ThreeAlphaData α β a b c) :
    Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β) ∨
    ((∀ k, vcount D k (2 * α + β) = 0) ∧ (∑ k, vcount D k α) = 3 ∧ (∑ k, vcount D k β) = 2 ∧
      (∑ k, (vcount D k α + vcount D k β)) = 5) :=
  lemma6_of_laczkovich h51 lacz53_thm D hrel h

end Erdos634.BeesonH1

#print axioms Erdos634.BeesonH1.lacz53_thm
#print axioms Erdos634.BeesonH1.lemma1_of_lacz51
#print axioms Erdos634.BeesonH1.lemma6_of_lacz51
