/-
Draft/H1dCaseD.lean — atom H1.d of (private working notes, not included) §2 "Case D" algebra D1–D3.
Setting (all real numbers, no geometry): right-tile sides `a, b, c > 0` with `c² = a² + b²`; `a/b ∉ ℚ`
(`Irrational (a/b)`); `c = r a + s b` with `r, s ∈ ℚ` (Case D); `lam > 0`, `lam² = M ∈ ℕ`, `lam ∉ ℚ`; side words
`lam c = u_a a + u_b b + u_c c` and `2 lam b = w_a a + w_b b + w_c c` (`u_•, w_• ∈ ℕ`).
  * D1 (`d1_quadratic`): `(r²-1)t² + 2rs t + (s²-1) = 0` for `t = a/b`, and `r² ≠ 1`.
  * D2 (`d2_field_eq`): `ℚ⟮lam⟯ = ℚ⟮t⟯`, of degree 2 over ℚ (so `K := ℚ⟮lam⟯` contains `a/b` and `c/b`).
  * D3 (`caseD_algebra`): the nontrivial ℚ-embedding `σ : K →ₐ[ℚ] ℝ`, `σ lam = -lam`, with
    `σ(c/b)² = σ(a/b)² + 1`, `σ(a/b) ≠ 0 ≠ σ(c/b)`, and the σ-images of the two side words:
    `-lam σ(c/b) = u_a σ(a/b) + u_b + u_c σ(c/b)`  (σ|AB|, scaled by 1/b),
    `-2 lam = w_a σ(a/b) + w_b + w_c σ(c/b)`      (σ|BC|, scaled by 1/b).
These are exactly the data D6 of the paper (sign lemma input).  Nothing here uses geometry; D4–D9 (CT, SL, corners) are NOT
here (they are `H1.e–H1.j`).  The four-way split `case_split` of §2 is also proved.
*** UNAUDITED.  Formalization debt, NOT /goal progress.  Pure Mathlib; no cited theorem; no sorry. ***
-/
import Mathlib

open Polynomial

namespace Erdos634.Draft.H1d

/-- `x` irrational root of a quadratic over ℚ with nonzero leading coefficient: integral, degree exactly 2. -/
theorem quad_finrank {x : ℝ} {A B E : ℚ} (hA : A ≠ 0) (hx : Irrational x)
    (h : (A : ℝ) * x ^ 2 + B * x + E = 0) :
    IsIntegral ℚ x ∧ (minpoly ℚ x).natDegree = 2 := by
  set p : ℚ[X] := C A * X ^ 2 + C B * X + C E with hp
  have hdeg : p.natDegree = 2 := Polynomial.natDegree_quadratic hA
  have hp0 : p ≠ 0 := by
    intro h0; rw [h0] at hdeg; simp at hdeg
  have hroot : Polynomial.aeval x p = 0 := by
    simp only [hp, map_add, map_mul, map_pow, aeval_C, aeval_X]; exact_mod_cast h
  have hint : IsIntegral ℚ x := by
    have : IsAlgebraic ℚ x := ⟨p, hp0, hroot⟩
    exact this.isIntegral
  refine ⟨hint, le_antisymm ?_ ?_⟩
  · have h1 := minpoly.degree_le_of_ne_zero (A := ℚ) (x := x) hp0 hroot
    have := Polynomial.natDegree_le_natDegree h1
    omega
  · exact (minpoly.two_le_natDegree_iff hint).mpr (by
      rintro ⟨q, hq⟩
      exact hx ⟨q, hq⟩)

/-- **D1.** For `c = r a + s b`, `c² = a² + b²`: the quadratic relation for `t = a/b` and `r² ≠ 1`
(using `a/b ∉ ℚ`). -/
theorem d1_quadratic {a b c : ℝ} {r s : ℚ} (hb : 0 < b) (hc2 : c ^ 2 = a ^ 2 + b ^ 2)
    (hrs : c = r * a + s * b) (hirr : Irrational (a / b)) :
    ((r : ℝ) ^ 2 - 1) * (a / b) ^ 2 + 2 * r * s * (a / b) + ((s : ℝ) ^ 2 - 1) = 0 ∧ r ^ 2 ≠ 1 := by
  have hb0 : b ≠ 0 := hb.ne'
  have hq : ((r : ℝ) ^ 2 - 1) * (a / b) ^ 2 + 2 * r * s * (a / b) + ((s : ℝ) ^ 2 - 1) = 0 := by
    have h : ((r : ℝ) ^ 2 - 1) * a ^ 2 + 2 * r * s * a * b + ((s : ℝ) ^ 2 - 1) * b ^ 2 = 0 := by
      rw [hrs] at hc2; linear_combination hc2
    field_simp
    linear_combination h
  refine ⟨hq, ?_⟩
  intro hr1
  have hr1' : (r : ℝ) ^ 2 = 1 := by exact_mod_cast hr1
  rw [hr1'] at hq
  by_cases hs : s = 0
  · subst hs; simp at hq
  · apply hirr
    have hrne : r ≠ 0 := by rintro rfl; norm_num at hr1
    refine ⟨(1 - s ^ 2) / (2 * r * s), ?_⟩
    have hrne' : (r : ℝ) ≠ 0 := by exact_mod_cast hrne
    have hsne' : (s : ℝ) ≠ 0 := by exact_mod_cast hs
    push_cast
    rw [div_eq_iff (by positivity)]
    linear_combination -hq

/-- `a/b ∉ ℚ` from "`a ≠ q b` for every rational `q`". -/
theorem irrational_div_of_not_rat {a b : ℝ} (hb : b ≠ 0) (h : ¬ ∃ q : ℚ, a = q * b) :
    Irrational (a / b) := by
  rintro ⟨q, hq⟩
  exact h ⟨q, by rw [hq]; field_simp⟩

/-- **The four-way split of §2** (exhaustive): `(AB)` `a/b ∈ ℚ`; `(C)` `a/b ∉ ℚ`, `c ∉ ℚa + ℚb`; `(D)` `a/b ∉ ℚ`,
`c = r a + s b`. -/
theorem case_split {a b c : ℝ} (hb : b ≠ 0) :
    (∃ q : ℚ, a = q * b) ∨
    (Irrational (a / b) ∧ ¬ ∃ r s : ℚ, c = r * a + s * b) ∨
    (Irrational (a / b) ∧ ∃ r s : ℚ, c = r * a + s * b) := by
  by_cases h1 : ∃ q : ℚ, a = q * b
  · exact Or.inl h1
  · have hi := irrational_div_of_not_rat hb h1
    by_cases h2 : ∃ r s : ℚ, c = r * a + s * b
    · exact Or.inr (Or.inr ⟨hi, h2⟩)
    · exact Or.inr (Or.inl ⟨hi, h2⟩)

/-- **D2.** `ℚ⟮lam⟯ = ℚ⟮t⟯` and both have degree 2. -/
theorem d2_field_eq {a b c lam : ℝ} {r s : ℚ} {M ua ub uc : ℕ} (hb : 0 < b) (hc : 0 < c)
    (hc2 : c ^ 2 = a ^ 2 + b ^ 2) (hrs : c = r * a + s * b) (hirr : Irrational (a / b))
    (hlam2 : lam ^ 2 = M) (hlirr : Irrational lam)
    (hw : lam * c = ua * a + ub * b + uc * c) :
    IntermediateField.adjoin ℚ {lam} = IntermediateField.adjoin ℚ {a / b} ∧
      Module.finrank ℚ (IntermediateField.adjoin ℚ {a / b}) = 2 := by
  obtain ⟨hq, hr⟩ := d1_quadratic hb hc2 hrs hirr
  have hr' : ((r : ℚ) ^ 2 - 1) ≠ 0 := sub_ne_zero.mpr hr
  obtain ⟨hint_t, hdeg_t⟩ := quad_finrank (A := r ^ 2 - 1) (B := 2 * r * s) (E := s ^ 2 - 1) hr' hirr
    (by push_cast; linear_combination hq)
  obtain ⟨hint_l, hdeg_l⟩ := quad_finrank (A := 1) (B := 0) (E := -(M : ℚ)) one_ne_zero hlirr
    (by push_cast; linear_combination hlam2)
  have hfin_t : Module.finrank ℚ (IntermediateField.adjoin ℚ {a / b}) = 2 := by
    rw [IntermediateField.adjoin.finrank hint_t, hdeg_t]
  have hfin_l : Module.finrank ℚ (IntermediateField.adjoin ℚ {lam}) = 2 := by
    rw [IntermediateField.adjoin.finrank hint_l, hdeg_l]
  refine ⟨?_, hfin_t⟩
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {a / b}) :=
    Module.finite_of_finrank_pos (by rw [hfin_t]; norm_num)
  apply IntermediateField.eq_of_le_of_finrank_eq
  · rw [IntermediateField.adjoin_simple_le_iff]
    set E := IntermediateField.adjoin ℚ {a / b} with hE
    have ht : a / b ∈ E := IntermediateField.mem_adjoin_simple_self ℚ (a / b)
    have hct : c / b = r * (a / b) + s := by rw [hrs]; field_simp
    have hct_mem : c / b ∈ E := by
      rw [hct]
      exact E.add_mem (E.mul_mem (E.algebraMap_mem r) ht) (E.algebraMap_mem s)
    have hct0 : c / b ≠ 0 := by positivity
    have hl : lam = (ua * (a / b) + ub + uc * (c / b)) / (c / b) := by
      rw [eq_div_iff hct0]; field_simp; linear_combination hw
    rw [hl]
    refine E.div_mem (E.add_mem (E.add_mem (E.mul_mem ?_ ht) ?_) (E.mul_mem ?_ hct_mem)) hct_mem
    · exact E.natCast_mem ua
    · exact E.natCast_mem ub
    · exact E.natCast_mem uc
  · rw [hfin_l, hfin_t]

/-- **D3 (the algebra of Case D).**  See the file header. -/
theorem caseD_algebra {a b c lam : ℝ} {r s : ℚ} {M ua ub uc wa wb wc : ℕ} (hb : 0 < b) (hc : 0 < c)
    (hc2 : c ^ 2 = a ^ 2 + b ^ 2) (hrs : c = r * a + s * b) (hirr : Irrational (a / b))
    (hlam : 0 < lam) (hlam2 : lam ^ 2 = M) (hlirr : Irrational lam)
    (hw : lam * c = ua * a + ub * b + uc * c) (hw' : 2 * lam * b = wa * a + wb * b + wc * c) :
    ∃ (K : IntermediateField ℚ ℝ) (hl : lam ∈ K) (ht : a / b ∈ K) (hct : c / b ∈ K) (σ : K →ₐ[ℚ] ℝ),
      Module.finrank ℚ K = 2 ∧ σ ⟨lam, hl⟩ = -lam ∧
      (σ ⟨c / b, hct⟩) ^ 2 = (σ ⟨a / b, ht⟩) ^ 2 + 1 ∧
      σ ⟨a / b, ht⟩ ≠ 0 ∧ σ ⟨c / b, hct⟩ ≠ 0 ∧
      σ ⟨c / b, hct⟩ = r * σ ⟨a / b, ht⟩ + s ∧
      -lam * σ ⟨c / b, hct⟩ = ua * σ ⟨a / b, ht⟩ + ub + uc * σ ⟨c / b, hct⟩ ∧
      -(2 * lam) = wa * σ ⟨a / b, ht⟩ + wb + wc * σ ⟨c / b, hct⟩ := by
  obtain ⟨hEq, hfin⟩ := d2_field_eq hb hc hc2 hrs hirr hlam2 hlirr hw
  obtain ⟨hint_l, hdeg_l⟩ := quad_finrank (A := 1) (B := 0) (E := -(M : ℚ)) one_ne_zero hlirr
    (by push_cast; linear_combination hlam2)
  set K := IntermediateField.adjoin ℚ {lam} with hK
  have hl : lam ∈ K := IntermediateField.mem_adjoin_simple_self ℚ lam
  have ht : a / b ∈ K := by
    rw [hEq]; exact IntermediateField.mem_adjoin_simple_self ℚ (a / b)
  have hct_eq : c / b = r * (a / b) + s := by rw [hrs]; field_simp
  have hct : c / b ∈ K := by
    rw [hct_eq]
    exact K.add_mem (K.mul_mem (K.algebraMap_mem r) ht) (K.algebraMap_mem s)
  -- minimal polynomial of lam is X² - M
  have hmin : minpoly ℚ lam = X ^ 2 - C (M : ℚ) := by
    symm
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint_l)
    · exact (monic_X_pow 2).sub_of_left (by rw [degree_X_pow]; exact degree_C_le.trans_lt (by norm_num))
    · apply minpoly.dvd
      simp only [map_sub, map_pow, aeval_X, aeval_C]
      rw [hlam2]; simp
    · rw [hdeg_l, natDegree_sub_C]; simp
  have hroot : -lam ∈ (minpoly ℚ lam).aroots ℝ := by
    rw [Polynomial.mem_aroots]
    refine ⟨minpoly.ne_zero hint_l, ?_⟩
    rw [hmin]
    simp only [map_sub, map_pow, aeval_X, aeval_C]
    rw [neg_sq, hlam2]; simp
  set σ : K →ₐ[ℚ] ℝ := (IntermediateField.algHomAdjoinIntegralEquiv ℚ hint_l).symm ⟨-lam, hroot⟩ with hσ
  have hσl : σ ⟨lam, hl⟩ = -lam :=
    IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hint_l ⟨-lam, hroot⟩
  have hfinK : Module.finrank ℚ K = 2 := by
    rw [hK, IntermediateField.adjoin.finrank hint_l, hdeg_l]
  set A : K := ⟨a / b, ht⟩ with hA
  set Cc : K := ⟨c / b, hct⟩ with hC
  set L : K := ⟨lam, hl⟩ with hL
  have hCeq : Cc = (r : K) * A + (s : K) := by
    apply Subtype.ext
    simp [hC, hA, hct_eq]
  have hCA : Cc ^ 2 = A ^ 2 + 1 := by
    apply Subtype.ext
    simp only [hC, hA]
    push_cast
    field_simp
    linear_combination hc2
  have hAne : A ≠ 0 := by
    intro h0
    have : a / b = 0 := congrArg Subtype.val h0
    exact hirr.ne_zero this
  have hCne : Cc ≠ 0 := by
    intro h0
    have : c / b = 0 := congrArg Subtype.val h0
    have : 0 < c / b := by positivity
    linarith
  have hb0 : b ≠ 0 := hb.ne'
  refine ⟨K, hl, ht, hct, σ, hfinK, hσl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change σ Cc ^ 2 = σ A ^ 2 + 1
    rw [← map_pow, hCA]; simp
  · exact fun h => hAne (σ.toRingHom.injective (by simpa using h))
  · exact fun h => hCne (σ.toRingHom.injective (by simpa using h))
  · change σ Cc = r * σ A + s
    rw [hCeq]; simp
  · have hK1 : L * Cc = (ua : K) * A + (ub : K) + (uc : K) * Cc := by
      apply Subtype.ext
      simp only [hL, hC, hA]
      push_cast
      field_simp
      linear_combination hw
    have := congrArg σ hK1
    simp only [map_mul, map_add, map_natCast, hσl] at this
    simpa using this
  · have hK2 : L + L = (wa : K) * A + (wb : K) + (wc : K) * Cc := by
      apply Subtype.ext
      simp only [hL, hC, hA]
      push_cast
      field_simp
      linear_combination hw'
    have := congrArg σ hK2
    simp only [map_mul, map_add, map_natCast, hσl] at this
    linarith

end Erdos634.Draft.H1d

#print axioms Erdos634.Draft.H1d.d1_quadratic
#print axioms Erdos634.Draft.H1d.case_split
#print axioms Erdos634.Draft.H1d.d2_field_eq
#print axioms Erdos634.Draft.H1d.caseD_algebra
