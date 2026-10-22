-- Draft/CaseALemmaH15Exc.lean — Lemma H at N = 15: the four exceptional cores, the case split, and
-- `lemmaH_15`.  Primality steps replaced by: 2r² ≠ 15 (parity), 3x² ≠ 15 (x² ≠ 5), y² ≠ 10,
-- m² ≠ 30 (all by bounded check).  Formalization debt; NOT /goal progress.
import Erdos634.Draft.CaseALemmaH15

namespace Erdos634.Geometry.CaseA.LemmaH

open Real

/-- θ = π/8: ζ⁴ = i. -/
theorem core15_pi_div_eight : HCore15 (Real.pi / 8) := by
  intro r x y hX0
  have hX := (by exact_mod_cast hX0 : 2 * ((r : ℝ) + x * Real.sin (Real.pi / 8) + y * Real.cos (Real.pi / 8)) ^ 2 = ((15 : ℕ) : ℝ))
  have hprim := prim_of (θ := Real.pi / 8) (j := 1) (M := 16) (by norm_num) (by norm_num)
    (by push_cast; ring)
  have hind := indep4 (ζ := Complex.exp (↑(Real.pi / 8) * Complex.I)) (1 : QI) one_ne_zero
    (by simp) hprim (by norm_num) (by decide)
  have hrel : Complex.exp (↑(Real.pi / 8) * Complex.I) ^ 4 =
      ((⟨Complex.I, I_mem⟩ : QI) : ℂ) + ((0 : QI) : ℂ) * Complex.exp (↑(Real.pi / 8) * Complex.I)
      + ((0 : QI) : ℂ) * Complex.exp (↑(Real.pi / 8) * Complex.I) ^ 2
      + ((0 : QI) : ℂ) * Complex.exp (↑(Real.pi / 8) * Complex.I) ^ 3 := by
    rw [exp_pow_eq, show ((4 : ℕ) : ℝ) * (Real.pi / 8) = Real.pi / 2 by push_cast; ring,
      exp_pi_div_two_I]
    simp
  obtain ⟨e0, e1, e2, -⟩ := four_coeffs (p := 15) hind _ _ _ _ hrel hX
  simp only [IntermediateField.coe_zero, mul_zero, add_zero] at e0 e1 e2
  have r0 := congrArg Complex.re e0; have i0 := congrArg Complex.im e0
  have r1 := congrArg Complex.re e1; have i1 := congrArg Complex.im e1
  have r2 := congrArg Complex.re e2
  simp [sq] at r0 i0 r1 i1 r2
  -- r1 : r = 0 ∨ y = 0, i1 : r = 0 ∨ x = 0; r0 : (y² − x² + 2xy)/4 = 0; r2 : r² + (x²+y²)/2 = p/2
  rcases i1 with hr | hx
  · subst hr
    have hq : ((x : ℤ) - y) ^ 2 = 2 * (y : ℤ) ^ 2 := by
      have : ((x : ℝ) - y) ^ 2 = 2 * (y : ℝ) ^ 2 := by linear_combination (-4) * r0
      exact_mod_cast this
    have hy : (y : ℤ) = 0 := sq_eq_two_sq hq
    have hy' : y = 0 := by exact_mod_cast hy
    subst hy'
    have hx : (x : ℤ) = 0 := by simpa using hq
    have hx' : x = 0 := by exact_mod_cast hx
    subst hx'
    have : (15 : ℝ) = 0 := by simp at r2 <;> linarith
    norm_num at this
  · subst hx
    rcases r1 with hr | hy
    · subst hr
      have : (y : ℝ) = 0 := by simp at r0; nlinarith
      have hy' : y = 0 := by exact_mod_cast this
      subst hy'
      have : (15 : ℝ) = 0 := by simp at r2 <;> linarith
      norm_num at this
    · subst hy
      have : 2 * (r : ℝ) ^ 2 = 15 := by simp at r2; linarith
      have h15 := (by exact_mod_cast this : 2 * r ^ 2 = 15)
      omega

/-- θ = π/12: ζ⁴ = 1 + iζ² (ζ² = e^{iπ/6}). -/
theorem core15_pi_div_twelve : HCore15 (Real.pi / 12) := by
  intro r x y hX0
  have hX := (by exact_mod_cast hX0 : 2 * ((r : ℝ) + x * Real.sin (Real.pi / 12) + y * Real.cos (Real.pi / 12)) ^ 2 = ((15 : ℕ) : ℝ))
  have hprim := prim_of (θ := Real.pi / 12) (j := 1) (M := 24) (by norm_num) (by norm_num)
    (by push_cast; ring)
  have hind := indep4 (ζ := Complex.exp (↑(Real.pi / 12) * Complex.I)) (1 : QI) one_ne_zero
    (by simp) hprim (by norm_num) (by decide)
  have hrel : Complex.exp (↑(Real.pi / 12) * Complex.I) ^ 4 =
      ((1 : QI) : ℂ) + ((0 : QI) : ℂ) * Complex.exp (↑(Real.pi / 12) * Complex.I)
      + ((⟨Complex.I, I_mem⟩ : QI) : ℂ) * Complex.exp (↑(Real.pi / 12) * Complex.I) ^ 2
      + ((0 : QI) : ℂ) * Complex.exp (↑(Real.pi / 12) * Complex.I) ^ 3 := by
    have h4 : Complex.exp (↑(Real.pi / 12) * Complex.I) ^ 4
        = Complex.exp (↑(Real.pi / 3) * Complex.I) := by
      rw [exp_pow_eq]; congr 2; push_cast; ring
    have h2 : Complex.exp (↑(Real.pi / 12) * Complex.I) ^ 2
        = Complex.exp (↑(Real.pi / 6) * Complex.I) := by
      rw [exp_pow_eq]; congr 2; push_cast; ring
    rw [h4, h2, exp_eq_cos_sin (Real.pi / 3), exp_eq_cos_sin (Real.pi / 6),
      Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_six]
    simp only [IntermediateField.coe_one, IntermediateField.coe_zero, zero_mul, add_zero]
    show _ = 1 + Complex.I * _
    push_cast
    linear_combination (-1 / 2 : ℂ) * Complex.I_sq
  obtain ⟨e0, e1, e2, -⟩ := four_coeffs (p := 15) hind _ _ _ _ hrel hX
  simp only [IntermediateField.coe_zero, IntermediateField.coe_one, mul_zero, add_zero,
    mul_one] at e0 e1 e2
  have r0 := congrArg Complex.re e0
  have r1 := congrArg Complex.im e1
  have r2 := congrArg Complex.re e2
  simp [sq] at r0 r1 r2
  rcases r1 with hr | hx
  · subst hr
    have hxy : (x : ℝ) = y := by
      have h0 : ((x : ℝ) - y) * (x + y) = 0 := by linear_combination (-2) * r0
      rcases mul_eq_zero.mp h0 with h | h
      · linarith
      · have : (0 : ℝ) ≤ x := Nat.cast_nonneg x
        have : (0 : ℝ) ≤ y := Nat.cast_nonneg y
        linarith
    have : 3 * (x : ℝ) ^ 2 = 15 := by rw [← hxy] at r2; simp at r2; linarith
    have h15 := (by exact_mod_cast this : 3 * x ^ 2 = 15)
    exact sq_ne_5 x (by omega)
  · subst hx
    have hy' : y = 0 := by
      first
      | exact r0
      | exact_mod_cast (show (y : ℝ) = 0 by nlinarith)
    subst hy'
    have : 2 * (r : ℝ) ^ 2 = 15 := by simp at r2; linarith
    have h15 := (by exact_mod_cast this : 2 * r ^ 2 = 15)
    omega

/-- θ = π/10: ζ⁴ = −1 + iζ + ζ² − iζ³ (from Φ₅(ζ⁴) = 0 and ζ⁵ = i). -/
theorem core15_pi_div_ten : HCore15 (Real.pi / 10) := by
  intro r x y hX0
  have hX := (by exact_mod_cast hX0 : 2 * ((r : ℝ) + x * Real.sin (Real.pi / 10) + y * Real.cos (Real.pi / 10)) ^ 2 = ((15 : ℕ) : ℝ))
  have hprim := prim_of (θ := Real.pi / 10) (j := 1) (M := 20) (by norm_num) (by norm_num)
    (by push_cast; ring)
  have hind := indep4 (ζ := Complex.exp (↑(Real.pi / 10) * Complex.I)) (1 : QI) one_ne_zero
    (by simp) hprim (by norm_num) (by decide)
  have h5 : Complex.exp (↑(Real.pi / 10) * Complex.I) ^ 5 = Complex.I := by
    rw [exp_pow_eq, show ((5 : ℕ) : ℝ) * (Real.pi / 10) = Real.pi / 2 by push_cast; ring,
      exp_pi_div_two_I]
  have hμ : IsPrimitiveRoot (Complex.exp (↑(Real.pi / 10) * Complex.I) ^ 4) 5 := by
    rw [exp_pow_eq]
    exact prim_of (j := 1) (by norm_num) (by norm_num) (by push_cast; ring)
  have hΦ := hμ.geom_sum_eq_zero (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one] at hΦ
  generalize hz : Complex.exp (↑(Real.pi / 10) * Complex.I) = ζ at h5 hΦ
  have hrel : ζ ^ 4 = Subtype.val (-1 : QI) + Subtype.val (⟨Complex.I, I_mem⟩ : QI) * ζ
      + Subtype.val (1 : QI) * ζ ^ 2 + Subtype.val (-(⟨Complex.I, I_mem⟩ : QI)) * ζ ^ 3 := by
    push_cast
    linear_combination hΦ - (ζ * ((ζ ^ 5) ^ 2 + Complex.I * ζ ^ 5 - 1) + ζ ^ 2 * (ζ ^ 5 + Complex.I)
      + ζ ^ 3) * h5 - (ζ ^ 2 + ζ ^ 6) * Complex.I_sq
  subst hz
  obtain ⟨e0, e1, e2, -⟩ := four_coeffs (p := 15) hind (-1) _ 1 _ hrel hX
  push_cast at e0 e1 e2
  have i0 := congrArg Complex.im e0
  have r1 := congrArg Complex.re e1
  have i1 := congrArg Complex.im e1
  have r2 := congrArg Complex.re e2
  simp [sq] at i0 r1 i1 r2
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hy0 : (0 : ℝ) ≤ y := Nat.cast_nonneg y
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hxy : (x : ℝ) * y = 0 := by nlinarith
  rcases mul_eq_zero.mp hxy with hx | hy
  · have hy : (y : ℝ) = 0 := by rw [hx] at i1; nlinarith
    have : 2 * (r : ℝ) ^ 2 = 15 := by rw [hx, hy] at r2; linarith
    have h15 := (by exact_mod_cast this : 2 * r ^ 2 = 15)
    omega
  · rw [hy] at i1 r2
    have hx4 : (x : ℝ) * (4 * r - x) = 0 := by linear_combination 4 * i1
    rcases mul_eq_zero.mp hx4 with hx | hx
    · have : 2 * (r : ℝ) ^ 2 = 15 := by rw [hx] at r2; linarith
      have h15 := (by exact_mod_cast this : 2 * r ^ 2 = 15)
      omega
    · have hx' : (x : ℝ) = 4 * r := by linarith
      have : 2 * ((5 * r ^ 2 : ℕ) : ℝ) = 15 := by push_cast; rw [hx'] at r2; linarith
      have h2 : 2 * (5 * r ^ 2) = 15 := by exact_mod_cast this
      omega

/-- θ = π/5: ζ⁴ = −1 + ζ − ζ² + ζ³ (ζ⁵ = −1, ζ ≠ −1); independence via the primitive 20th root
`i·ζ`. -/
theorem core15_pi_div_five : HCore15 (Real.pi / 5) := by
  intro r x y hX0
  have hX := (by exact_mod_cast hX0 : 2 * ((r : ℝ) + x * Real.sin (Real.pi / 5) + y * Real.cos (Real.pi / 5)) ^ 2 = ((15 : ℕ) : ℝ))
  set ζ := Complex.exp (↑(Real.pi / 5) * Complex.I) with hζ
  have hprim := prim_of (θ := 7 * Real.pi / 10) (j := 7) (M := 20) (by norm_num) (by norm_num)
    (by push_cast; ring)
  have hu : ((⟨Complex.I, I_mem⟩ : QI) : ℂ) * ζ = Complex.exp (↑(7 * Real.pi / 10) * Complex.I) := by
    have e7 : Complex.exp (↑(7 * Real.pi / 10) * Complex.I)
        = Complex.exp (↑(Real.pi / 2) * Complex.I) * Complex.exp (↑(Real.pi / 5) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    show Complex.I * ζ = _
    rw [e7, exp_pi_div_two_I, hζ]
  have hind := indep4 (ζ := ζ) _ iQ_ne hu hprim (by norm_num) (by decide)
  have h5 : ζ ^ 5 = -1 := by
    rw [hζ, exp_pow_eq, show ((5 : ℕ) : ℝ) * (Real.pi / 5) = Real.pi by push_cast; ring]
    exact Complex.exp_pi_mul_I
  have hne : ζ + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [hζ, exp_eq_cos_sin] at this
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.one_re, Complex.zero_re, mul_zero, zero_mul, sub_zero] at this
    have hc : 0 < Real.cos (Real.pi / 5) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],
      by linarith [Real.pi_pos]⟩
    linarith
  have hq : ζ ^ 4 - ζ ^ 3 + ζ ^ 2 - ζ + 1 = 0 := by
    have : (ζ + 1) * (ζ ^ 4 - ζ ^ 3 + ζ ^ 2 - ζ + 1) = 0 := by linear_combination h5
    exact (mul_eq_zero.mp this).resolve_left hne
  have hrel : ζ ^ 4 = ((-1 : QI) : ℂ) + ((1 : QI) : ℂ) * ζ + ((-1 : QI) : ℂ) * ζ ^ 2
      + ((1 : QI) : ℂ) * ζ ^ 3 := by
    push_cast
    linear_combination hq
  obtain ⟨e0, e1, e2, e3⟩ := four_coeffs (p := 15) hind _ _ _ _ hrel hX
  push_cast at e0 e1 e2 e3
  have i0 := congrArg Complex.im e0
  have r1 := congrArg Complex.re e1
  have r2 := congrArg Complex.re e2
  simp [sq] at i0 r1 r2
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hy0 : (0 : ℝ) ≤ y := Nat.cast_nonneg y
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hxy : (x : ℝ) * y = 0 := by nlinarith
  have hx : (x : ℝ) = 0 ∧ (y : ℝ) = 0 := by
    rcases mul_eq_zero.mp hxy with hx | hy
    · rw [hx] at r1; exact ⟨hx, by nlinarith⟩
    · rw [hy] at r1; exact ⟨by nlinarith, hy⟩
  have : 2 * (r : ℝ) ^ 2 = 15 := by rw [hx.1, hx.2] at r2; linarith
  have h15 := (by exact_mod_cast this : 2 * r ^ 2 = 15)
  omega

/-! ## Glue -/

theorem hcore15_of_eq {θ a : ℝ} (h : HCore15 a) (e : θ = a) : HCore15 θ := e ▸ h

/-- Every θ with `θ·n = 2πj`, `0 < 4j < n ≤ 30`, `n` in the exceptional class, is one of the
eleven angles; HCore15 there from the four open cores (`hexc`) and the proved ones. -/
theorem exc_finish15 (hexc : HCore15 (Real.pi / 8) ∧ HCore15 (Real.pi / 12) ∧ HCore15 (Real.pi / 10) ∧
      HCore15 (Real.pi / 5))
    {θ : ℝ} {n j : ℕ} (hn : n ≤ 30) (hj0 : 0 < j) (hj : 4 * j < n)
    (hθ : θ * n = 2 * Real.pi * j) (hP : (4 ∣ n ∧ n.totient ≤ 9) ∨ n.totient ≤ 4) : HCore15 θ := by
  obtain ⟨h8, h12, h10, h5⟩ := hexc
  have c38 := hcore15_compl h8
  have c512 := hcore15_compl h12
  have c25 := hcore15_compl h10
  have c310 := hcore15_compl h5
  have c4 := core15_pi_div_four
  have c6 := core15_pi_div_six
  have c3 := core15_pi_div_three
  have hjn : j < n := by omega
  have hmem := exc_list n hn hP
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases j <;> push_cast at hθ <;> (try omega) <;>
    first
    | exact hcore15_of_eq h8 (by linarith) | exact hcore15_of_eq h12 (by linarith)
    | exact hcore15_of_eq h10 (by linarith) | exact hcore15_of_eq h5 (by linarith)
    | exact hcore15_of_eq c38 (by linarith) | exact hcore15_of_eq c512 (by linarith)
    | exact hcore15_of_eq c25 (by linarith) | exact hcore15_of_eq c310 (by linarith)
    | exact hcore15_of_eq c4 (by linarith) | exact hcore15_of_eq c6 (by linarith)
    | exact hcore15_of_eq c3 (by linarith)

/-- **The case split** (steps 5–6): for θ ∈ ℚπ, 0 < θ < π/2, `HCore15 θ` — generic angles by the
cyclotomic degree bound, the eleven exceptional angles from the cores at π/4, π/6, π/3 (proved) and
the four cores in `hexc` (open). -/
theorem hcore15_rational (hexc : HCore15 (Real.pi / 8) ∧ HCore15 (Real.pi / 12) ∧ HCore15 (Real.pi / 10) ∧
      HCore15 (Real.pi / 5))
    {θ : ℝ} (hq : ∃ q : ℚ, θ = q * Real.pi) (h0 : 0 < θ) (h2 : θ < Real.pi / 2) : HCore15 θ := by
  obtain ⟨hn, j, hj0, hj4, hθ⟩ := theta_form hq h0 h2
  set ζ := Complex.exp (θ * Complex.I)
  set n := orderOf ζ with hn_def
  have hP : IsPrimitiveRoot ζ n := IsPrimitiveRoot.orderOf ζ
  by_cases hdiv : 4 ∣ n
  · by_cases h10 : 10 ≤ n.totient
    · exact hcore15_of_primitive 1 one_ne_zero hn (by simpa using hP) h10
    · exact exc_finish15 hexc (le_30 hn (by omega)) hj0 hj4 hθ (Or.inl ⟨hdiv, by omega⟩)
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | hodd
  · have hmodd : Odd m := by
      rcases Nat.even_or_odd m with ⟨t, ht⟩ | h
      · exact absurd ⟨t, by omega⟩ hdiv
      · exact h
    have hm0 : 0 < m := by omega
    have hneg : orderOf (-ζ) = m := orderOf_neg_of_two_mul hm0 hmodd (by omega)
    have hω : orderOf (Complex.I * ζ) = 4 * m := by
      have e : Complex.I * ζ = (-Complex.I) * (-ζ) := by ring
      rw [e, (Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime, orderOf_negI, hneg]
      rw [orderOf_negI, hneg]
      show Nat.Coprime (2 ^ 2) m
      exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hmodd)
    have hφn : n.totient = m.totient := by
      rw [hm, ← two_mul]; exact Nat.totient_two_mul_of_odd hmodd
    by_cases h10 : 10 ≤ (4 * m).totient
    · have hpr := IsPrimitiveRoot.orderOf (Complex.I * ζ)
      rw [hω] at hpr
      exact hcore15_of_primitive ⟨Complex.I, I_mem⟩ iQ_ne (by omega) hpr h10
    · rw [totient_four_mul hmodd] at h10
      exact exc_finish15 hexc (le_30 hn (by omega)) hj0 hj4 hθ (Or.inr (by omega))
  · have hω : orderOf (Complex.I * ζ) = 4 * n := by
      rw [(Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime, orderOf_I]
      rw [orderOf_I]
      show Nat.Coprime (2 ^ 2) n
      exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd)
    by_cases h10 : 10 ≤ (4 * n).totient
    · have hpr := IsPrimitiveRoot.orderOf (Complex.I * ζ)
      rw [hω] at hpr
      exact hcore15_of_primitive ⟨Complex.I, I_mem⟩ iQ_ne (by omega) hpr h10
    · rw [totient_four_mul hodd] at h10
      exact exc_finish15 hexc (le_30 hn (by omega)) hj0 hj4 hθ (Or.inr (by omega))


/-! ## Lemma H at N = 15 -/

theorem lemmaH_15 {N : ℕ} (D : CongruentDissection N) {θ : ℝ} (hq : ∃ q : ℚ, θ = q * Real.pi)
    (hθ0 : 0 < θ) (hθ2 : θ < Real.pi / 2)
    {p q : Fin 3} (hpq : p ≠ q) (hmp : D.model.angleAt p = θ) (hmq : D.model.angleAt q = Real.pi / 2)
    {i j : Fin 3} (hij : i ≠ j) (hi : D.target.angleAt i = θ) (hj : D.target.angleAt j = θ)
    (hN : N = 15) : False := by
  subst hN
  obtain ⟨r, x, y, h⟩ := count_eq D hθ0 hθ2 hpq hmp hmq hij hi hj
  have hC : HCore15 θ :=
    hcore15_rational ⟨core15_pi_div_eight, core15_pi_div_twelve, core15_pi_div_ten,
      core15_pi_div_five⟩ hq hθ0 hθ2
  exact hC r x y (by rw [← h]; norm_num)

end Erdos634.Geometry.CaseA.LemmaH

#print axioms Erdos634.Geometry.CaseA.LemmaH.core15_pi_div_eight
#print axioms Erdos634.Geometry.CaseA.LemmaH.core15_pi_div_twelve
#print axioms Erdos634.Geometry.CaseA.LemmaH.core15_pi_div_ten
#print axioms Erdos634.Geometry.CaseA.LemmaH.core15_pi_div_five
#print axioms Erdos634.Geometry.CaseA.LemmaH.hcore15_rational
#print axioms Erdos634.Geometry.CaseA.LemmaH.lemmaH_15
