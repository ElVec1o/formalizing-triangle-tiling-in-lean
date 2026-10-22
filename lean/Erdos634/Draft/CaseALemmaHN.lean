-- Draft/CaseALemmaHN.lean — Lemma H (half-isosceles exit of Case A) for ARBITRARY tile count N satisfying six
-- elementary non-solution conditions `HArith N`; generalisation of `CaseALemmaH15{,Exc}` (N = 15) in which every
-- "15" is replaced by N and each arithmetic closer by the corresponding `HArith` field:
--   a1: 2r² ≠ N   a2: t² ≠ N   a3: 3y² ≠ 2N   a4: t² ≠ 2N   a5: 3x² ≠ N   a6: 10r² ≠ N   (pos: 0 < N).
-- No primality, no oddness of N used.  `harith_38`, `harith_86` discharge them by bounded check.  UNAUDITED.
-- Formalization debt on the paper-level Lemma H exit; NOT /goal progress.
import Erdos634.Draft.CaseALemmaH15Exc

namespace Erdos634.Geometry.CaseA.LemmaH

open Real

variable {N : ℕ}

structure HArith (N : ℕ) : Prop where
  pos : 0 < N
  a1 : ∀ r : ℕ, 2 * r ^ 2 ≠ N
  a2 : ∀ t : ℕ, t ^ 2 ≠ N
  a3 : ∀ y : ℕ, 3 * y ^ 2 ≠ 2 * N
  a4 : ∀ t : ℕ, t ^ 2 ≠ 2 * N
  a5 : ∀ x : ℕ, 3 * x ^ 2 ≠ N
  a6 : ∀ r : ℕ, 10 * r ^ 2 ≠ N

/-- The core at θ for tile count N. -/
def HCoreN (N : ℕ) (θ : ℝ) : Prop :=
  ∀ r x y : ℕ, 2 * ((r : ℝ) + x * Real.sin θ + y * Real.cos θ) ^ 2 ≠ N


open Real



theorem hcoreN_compl {θ : ℝ} (h : HCoreN N θ) : HCoreN N (Real.pi / 2 - θ) := by
  intro r x y hX
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub] at hX
  exact h r y x (by linear_combination hX)

/-- generic case, with `p` free and `hne : 2r² ≠ p`. -/
theorem generic_killN (hAr : HArith N) {θ : ℝ} (hind : GenericIndep θ) : HCoreN N θ := by
  intro r x y hX
  set p : ℕ := N with hp15
  set e := Complex.exp (θ * Complex.I) with he_def
  set e' := Complex.exp (-(θ : ℂ) * Complex.I) with he'_def
  have hee : e * e' = 1 := by rw [he_def, he'_def, ← Complex.exp_add]; ring_nf; simp
  have hXc : 2 * ((r : ℂ) + x * Complex.sin θ + y * Complex.cos θ) ^ 2 = p := by
    have := congrArg (fun t : ℝ => (t : ℂ)) hX
    push_cast at this
    simpa [p] using this
  have hsin : Complex.sin θ = (e' - e) * Complex.I / 2 := rfl
  have hcos : Complex.cos θ = (e + e') / 2 := rfl
  rw [hsin, hcos] at hXc
  set Xc := (r : ℂ) + x * ((e' - e) * Complex.I / 2) + y * ((e + e') / 2) with hXc_def
  have hXc' : 2 * Xc ^ 2 = p := hXc
  set iQ : QI := ⟨Complex.I, I_mem⟩
  set A : QI := ((y : QI) - iQ * (x : QI)) / 2
  set B : QI := ((y : QI) + iQ * (x : QI)) / 2
  have hc2 : ((2 : QI) : ℂ) = 2 := by
    rw [show (2 : QI) = ((2 : ℕ) : QI) from (Nat.cast_ofNat).symm]; push_cast; rfl
  have hA : (A : ℂ) = ((y : ℂ) - Complex.I * x) / 2 := by simp [A, iQ, hc2]
  have hB : (B : ℂ) = ((y : ℂ) + Complex.I * x) / 2 := by simp [B, iQ, hc2]
  have hXe : Xc * e = r * e + (A : ℂ) * e ^ 2 + (B : ℂ) := by
    rw [hA, hB, hXc_def]
    linear_combination (↑x * Complex.I / 2 + ↑y / 2) * hee
  set g : Fin 5 → QI := ![B ^ 2, 2 * (r : QI) * B, (r : QI) ^ 2 + 2 * A * B - (p : QI) / 2,
    2 * (r : QI) * A, A ^ 2]
  have hsum : ∑ k, g k • (fun k : Fin 5 => e ^ (k : ℕ)) k = 0 := by
    rw [Fin.sum_univ_five]
    simp only [IntermediateField.smul_def, smul_eq_mul]
    have g0 : g 0 = B ^ 2 := rfl
    have g1 : g 1 = 2 * (r : QI) * B := rfl
    have g2 : g 2 = (r : QI) ^ 2 + 2 * A * B - (p : QI) / 2 := rfl
    have g3 : g 3 = 2 * (r : QI) * A := rfl
    have g4 : g 4 = A ^ 2 := rfl
    have c0 : ((0 : Fin 5) : ℕ) = 0 := rfl
    have c1 : ((1 : Fin 5) : ℕ) = 1 := rfl
    have c2 : ((2 : Fin 5) : ℕ) = 2 := rfl
    have c3 : ((3 : Fin 5) : ℕ) = 3 := rfl
    have c4 : ((4 : Fin 5) : ℕ) = 4 := rfl
    rw [g0, g1, g2, g3, g4, c0, c1, c2, c3, c4]
    push_cast
    simp only [hc2]
    linear_combination (-(Xc * e + (r * e + (A : ℂ) * e ^ 2 + (B : ℂ)))) * hXe
      + (e ^ 2 / 2) * hXc'
  have hg4 := Fintype.linearIndependent_iff.mp hind g hsum 4
  have hA0 : (A : ℂ) = 0 := by
    have : A = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by simpa [g] using hg4)
    simp [this]
  rw [hA] at hA0
  have hre := congrArg Complex.re hA0
  have him := congrArg Complex.im hA0
  simp at hre him
  subst hre; subst him
  have h2 : 2 * (r : ℝ) ^ 2 = N := by simpa using hX
  exact hAr.a1 r (by exact_mod_cast h2)

theorem hcoreN_of_primitive (hAr : HArith N) {θ : ℝ} (u : QI) (hu : u ≠ 0) {M : ℕ} (hM : 0 < M)
    (hω : IsPrimitiveRoot ((u : ℂ) * Complex.exp (θ * Complex.I)) M) (h10 : 10 ≤ M.totient) :
    HCoreN N θ :=
  generic_killN hAr (indep_of_scaled u hu rfl (indep_of_totient hω hM h10))

theorem coreN_pi_div_four (hAr : HArith N) : HCoreN N (Real.pi / 4) := by
  intro r x y hX
  rw [Real.sin_pi_div_four, Real.cos_pi_div_four] at hX
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hkey : (2 * (r : ℝ) ^ 2 + ((x : ℝ) + y) ^ 2 - (N : ℝ)) + 2 * r * (x + y) * Real.sqrt 2 = 0 := by
    linear_combination hX - (((x : ℝ) + y) ^ 2 / 2) * hs
  have hirr : Irrational (Real.sqrt 2) := irrational_sqrt_two
  have hrt : (r : ℝ) * (x + y) = 0 := by
    by_contra hne
    apply hirr
    have hne' : (2 * (r : ℝ) * (x + y)) ≠ 0 := by
      intro h0; apply hne; linarith
    refine ⟨((N : ℚ) - 2 * r ^ 2 - ((x : ℚ) + y) ^ 2) / (2 * r * (x + y)), ?_⟩
    push_cast
    rw [div_eq_iff hne']
    linear_combination -hkey
  rcases mul_eq_zero.mp hrt with h | h
  · have hr : r = 0 := by exact_mod_cast h
    subst hr
    have ht : ((x + y : ℕ) : ℝ) ^ 2 = N := by push_cast; simp at hkey; linarith
    have ht' : (x + y) ^ 2 = N := by exact_mod_cast ht
    exact hAr.a2 _ ht'
  · have ht : 2 * ((r : ℝ)) ^ 2 = N := by
      have : ((x : ℝ) + y) = 0 := h
      linear_combination hkey - (((x : ℝ) + y) + 2 * r * Real.sqrt 2) * this
    have : 2 * r ^ 2 = N := by exact_mod_cast ht
    exact hAr.a1 r this

theorem coreN_pi_div_six (hAr : HArith N) : HCoreN N (Real.pi / 6) := by
  intro r x y hX
  rw [Real.sin_pi_div_six, Real.cos_pi_div_six] at hX
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  set a : ℝ := r + x / 2
  set b : ℝ := y / 2
  have hkey : (2 * a ^ 2 + 6 * b ^ 2 - (N : ℝ)) + 4 * a * b * Real.sqrt 3 = 0 := by
    linear_combination hX - (2 * b ^ 2) * hs
  have hirr : Irrational (Real.sqrt 3) := Nat.prime_three.irrational_sqrt
  have hab : a * b = 0 := by
    by_contra hne
    apply hirr
    have hne' : (4 * a * b) ≠ 0 := by intro h0; apply hne; linarith
    refine ⟨((N : ℚ) - 2 * ((r : ℚ) + x / 2) ^ 2 - 6 * ((y : ℚ) / 2) ^ 2) / (4 * ((r : ℚ) + x / 2) * (y / 2)),
      ?_⟩
    push_cast
    rw [div_eq_iff hne']
    linear_combination -hkey
  rcases mul_eq_zero.mp hab with h | h
  · have hr : (r : ℝ) = 0 := by
      have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      have : (0 : ℝ) ≤ x := Nat.cast_nonneg x
      simp only [a] at h; linarith
    have hx : (x : ℝ) = 0 := by simp only [a] at h; linarith
    have h3 : ((3 * y ^ 2 : ℕ) : ℝ) = ((2 * N : ℕ) : ℝ) := by
      push_cast
      have : (2 : ℝ) * a ^ 2 + 6 * b ^ 2 - N + 4 * a * b * Real.sqrt 3 = 0 := hkey
      rw [h] at this; simp only [b] at this; linarith
    have h3' : 3 * y ^ 2 = 2 * N := by exact_mod_cast h3
    exact hAr.a3 y h3'
  · have h2 : (((2 * r + x) ^ 2 : ℕ) : ℝ) = ((2 * N : ℕ) : ℝ) := by
      push_cast
      have : (2 : ℝ) * a ^ 2 + 6 * b ^ 2 - N + 4 * a * b * Real.sqrt 3 = 0 := hkey
      rw [h] at this; simp only [a] at this; linarith
    exact hAr.a4 _ (by exact_mod_cast h2)

theorem coreN_pi_div_three (hAr : HArith N) : HCoreN N (Real.pi / 3) := by
  have := hcoreN_compl (coreN_pi_div_six hAr)
  rwa [show Real.pi / 2 - Real.pi / 6 = Real.pi / 3 by ring] at this



/-- θ = π/8: ζ⁴ = i. -/
theorem coreN_pi_div_eight (hAr : HArith N) : HCoreN N (Real.pi / 8) := by
  intro r x y hX0
  have hX := (by exact_mod_cast hX0 : 2 * ((r : ℝ) + x * Real.sin (Real.pi / 8) + y * Real.cos (Real.pi / 8)) ^ 2 = (N : ℝ))
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
  obtain ⟨e0, e1, e2, -⟩ := four_coeffs (p := N) hind _ _ _ _ hrel hX
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
    have : (N : ℝ) = 0 := by simp at r2 <;> linarith
    exact absurd this (by exact_mod_cast hAr.pos.ne')
  · subst hx
    rcases r1 with hr | hy
    · subst hr
      have : (y : ℝ) = 0 := by simp at r0; nlinarith
      have hy' : y = 0 := by exact_mod_cast this
      subst hy'
      have : (N : ℝ) = 0 := by simp at r2 <;> linarith
      exact absurd this (by exact_mod_cast hAr.pos.ne')
    · subst hy
      have : 2 * (r : ℝ) ^ 2 = N := by simp at r2; linarith
      have h15 := (by exact_mod_cast this : 2 * r ^ 2 = N)
      exact hAr.a1 r h15

/-- θ = π/12: ζ⁴ = 1 + iζ² (ζ² = e^{iπ/6}). -/
theorem coreN_pi_div_twelve (hAr : HArith N) : HCoreN N (Real.pi / 12) := by
  intro r x y hX0
  have hX := (by exact_mod_cast hX0 : 2 * ((r : ℝ) + x * Real.sin (Real.pi / 12) + y * Real.cos (Real.pi / 12)) ^ 2 = (N : ℝ))
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
  obtain ⟨e0, e1, e2, -⟩ := four_coeffs (p := N) hind _ _ _ _ hrel hX
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
    have : 3 * (x : ℝ) ^ 2 = N := by rw [← hxy] at r2; simp at r2; linarith
    have h15 := (by exact_mod_cast this : 3 * x ^ 2 = N)
    exact hAr.a5 x h15
  · subst hx
    have hy' : y = 0 := by
      first
      | exact r0
      | exact_mod_cast (show (y : ℝ) = 0 by nlinarith)
    subst hy'
    have : 2 * (r : ℝ) ^ 2 = N := by simp at r2; linarith
    have h15 := (by exact_mod_cast this : 2 * r ^ 2 = N)
    exact hAr.a1 r h15

/-- θ = π/10: ζ⁴ = −1 + iζ + ζ² − iζ³ (from Φ₅(ζ⁴) = 0 and ζ⁵ = i). -/
theorem coreN_pi_div_ten (hAr : HArith N) : HCoreN N (Real.pi / 10) := by
  intro r x y hX0
  have hX := (by exact_mod_cast hX0 : 2 * ((r : ℝ) + x * Real.sin (Real.pi / 10) + y * Real.cos (Real.pi / 10)) ^ 2 = (N : ℝ))
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
  obtain ⟨e0, e1, e2, -⟩ := four_coeffs (p := N) hind (-1) _ 1 _ hrel hX
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
    have : 2 * (r : ℝ) ^ 2 = N := by rw [hx, hy] at r2; linarith
    have h15 := (by exact_mod_cast this : 2 * r ^ 2 = N)
    exact hAr.a1 r h15
  · rw [hy] at i1 r2
    have hx4 : (x : ℝ) * (4 * r - x) = 0 := by linear_combination 4 * i1
    rcases mul_eq_zero.mp hx4 with hx | hx
    · have : 2 * (r : ℝ) ^ 2 = N := by rw [hx] at r2; linarith
      have h15 := (by exact_mod_cast this : 2 * r ^ 2 = N)
      exact hAr.a1 r h15
    · have hx' : (x : ℝ) = 4 * r := by linarith
      have : 2 * ((5 * r ^ 2 : ℕ) : ℝ) = N := by push_cast; rw [hx'] at r2; linarith
      have h2 : 2 * (5 * r ^ 2) = N := by exact_mod_cast this
      exact hAr.a6 r (by rw [← h2]; ring)

/-- θ = π/5: ζ⁴ = −1 + ζ − ζ² + ζ³ (ζ⁵ = −1, ζ ≠ −1); independence via the primitive 20th root
`i·ζ`. -/
theorem coreN_pi_div_five (hAr : HArith N) : HCoreN N (Real.pi / 5) := by
  intro r x y hX0
  have hX := (by exact_mod_cast hX0 : 2 * ((r : ℝ) + x * Real.sin (Real.pi / 5) + y * Real.cos (Real.pi / 5)) ^ 2 = (N : ℝ))
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
  obtain ⟨e0, e1, e2, e3⟩ := four_coeffs (p := N) hind _ _ _ _ hrel hX
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
  have : 2 * (r : ℝ) ^ 2 = N := by rw [hx.1, hx.2] at r2; linarith
  have h15 := (by exact_mod_cast this : 2 * r ^ 2 = N)
  exact hAr.a1 r h15

/-! ## Glue -/

theorem hcoreN_of_eq {θ a : ℝ} (h : HCoreN N a) (e : θ = a) : HCoreN N θ := e ▸ h

/-- Every θ with `θ·n = 2πj`, `0 < 4j < n ≤ 30`, `n` in the exceptional class, is one of the
eleven angles; HCoreN N there from the four open cores (`hexc`) and the proved ones. -/
theorem exc_finishN (hAr : HArith N) (hexc : HCoreN N (Real.pi / 8) ∧ HCoreN N (Real.pi / 12) ∧ HCoreN N (Real.pi / 10) ∧
      HCoreN N (Real.pi / 5))
    {θ : ℝ} {n j : ℕ} (hn : n ≤ 30) (hj0 : 0 < j) (hj : 4 * j < n)
    (hθ : θ * n = 2 * Real.pi * j) (hP : (4 ∣ n ∧ n.totient ≤ 9) ∨ n.totient ≤ 4) : HCoreN N θ := by
  obtain ⟨h8, h12, h10, h5⟩ := hexc
  have c38 := hcoreN_compl h8
  have c512 := hcoreN_compl h12
  have c25 := hcoreN_compl h10
  have c310 := hcoreN_compl h5
  have c4 := (coreN_pi_div_four hAr)
  have c6 := (coreN_pi_div_six hAr)
  have c3 := (coreN_pi_div_three hAr)
  have hjn : j < n := by omega
  have hmem := exc_list n hn hP
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases j <;> push_cast at hθ <;> (try omega) <;>
    first
    | exact hcoreN_of_eq h8 (by linarith) | exact hcoreN_of_eq h12 (by linarith)
    | exact hcoreN_of_eq h10 (by linarith) | exact hcoreN_of_eq h5 (by linarith)
    | exact hcoreN_of_eq c38 (by linarith) | exact hcoreN_of_eq c512 (by linarith)
    | exact hcoreN_of_eq c25 (by linarith) | exact hcoreN_of_eq c310 (by linarith)
    | exact hcoreN_of_eq c4 (by linarith) | exact hcoreN_of_eq c6 (by linarith)
    | exact hcoreN_of_eq c3 (by linarith)

/-- **The case split** (steps 5–6): for θ ∈ ℚπ, 0 < θ < π/2, `HCoreN N θ` — generic angles by the
cyclotomic degree bound, the eleven exceptional angles from the cores at π/4, π/6, π/3 (proved) and
the four cores in `hexc` (open). -/
theorem hcoreN_rational (hAr : HArith N) (hexc : HCoreN N (Real.pi / 8) ∧ HCoreN N (Real.pi / 12) ∧ HCoreN N (Real.pi / 10) ∧
      HCoreN N (Real.pi / 5))
    {θ : ℝ} (hq : ∃ q : ℚ, θ = q * Real.pi) (h0 : 0 < θ) (h2 : θ < Real.pi / 2) : HCoreN N θ := by
  obtain ⟨hn, j, hj0, hj4, hθ⟩ := theta_form hq h0 h2
  set ζ := Complex.exp (θ * Complex.I)
  set n := orderOf ζ with hn_def
  have hP : IsPrimitiveRoot ζ n := IsPrimitiveRoot.orderOf ζ
  by_cases hdiv : 4 ∣ n
  · by_cases h10 : 10 ≤ n.totient
    · exact hcoreN_of_primitive hAr 1 one_ne_zero hn (by simpa using hP) h10
    · exact exc_finishN hAr hexc (le_30 hn (by omega)) hj0 hj4 hθ (Or.inl ⟨hdiv, by omega⟩)
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
      exact hcoreN_of_primitive hAr ⟨Complex.I, I_mem⟩ iQ_ne (by omega) hpr h10
    · rw [totient_four_mul hmodd] at h10
      exact exc_finishN hAr hexc (le_30 hn (by omega)) hj0 hj4 hθ (Or.inr (by omega))
  · have hω : orderOf (Complex.I * ζ) = 4 * n := by
      rw [(Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime, orderOf_I]
      rw [orderOf_I]
      show Nat.Coprime (2 ^ 2) n
      exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd)
    by_cases h10 : 10 ≤ (4 * n).totient
    · have hpr := IsPrimitiveRoot.orderOf (Complex.I * ζ)
      rw [hω] at hpr
      exact hcoreN_of_primitive hAr ⟨Complex.I, I_mem⟩ iQ_ne (by omega) hpr h10
    · rw [totient_four_mul hodd] at h10
      exact exc_finishN hAr hexc (le_30 hn (by omega)) hj0 hj4 hθ (Or.inr (by omega))



/-! ## Lemma H at N with `HArith N` -/

theorem lemmaH_N (hAr : HArith N) (D : CongruentDissection N) {θ : ℝ} (hq : ∃ q : ℚ, θ = q * Real.pi)
    (hθ0 : 0 < θ) (hθ2 : θ < Real.pi / 2)
    {p q : Fin 3} (hpq : p ≠ q) (hmp : D.model.angleAt p = θ) (hmq : D.model.angleAt q = Real.pi / 2)
    {i j : Fin 3} (hij : i ≠ j) (hi : D.target.angleAt i = θ) (hj : D.target.angleAt j = θ) : False := by
  obtain ⟨r, x, y, h⟩ := count_eq D hθ0 hθ2 hpq hmp hmq hij hi hj
  have hC : HCoreN N θ :=
    hcoreN_rational hAr ⟨coreN_pi_div_eight hAr, coreN_pi_div_twelve hAr, coreN_pi_div_ten hAr,
      coreN_pi_div_five hAr⟩ hq hθ0 hθ2
  exact hC r x y h.symm

theorem harith_of_bound {N : ℕ} (hN : 0 < N) (hb : N < 400)
    (h1 : ∀ r < 20, 2 * r ^ 2 ≠ N) (h2 : ∀ t < 20, t ^ 2 ≠ N) (h3 : ∀ y < 20, 3 * y ^ 2 ≠ 2 * N)
    (h4 : ∀ t < 30, t ^ 2 ≠ 2 * N) (h5 : ∀ x < 20, 3 * x ^ 2 ≠ N) (h6 : ∀ r < 20, 10 * r ^ 2 ≠ N) :
    HArith N := by
  refine ⟨hN, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r h; exact h1 r (by nlinarith) h
  · intro t h; exact h2 t (by nlinarith) h
  · intro y h; exact h3 y (by nlinarith) h
  · intro t h; exact h4 t (by nlinarith) h
  · intro x h; exact h5 x (by nlinarith) h
  · intro r h; exact h6 r (by nlinarith) h

theorem harith_38 : HArith 38 := harith_of_bound (by norm_num) (by norm_num) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide)

theorem harith_86 : HArith 86 := harith_of_bound (by norm_num) (by norm_num) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide)

end Erdos634.Geometry.CaseA.LemmaH

#print axioms Erdos634.Geometry.CaseA.LemmaH.generic_killN
#print axioms Erdos634.Geometry.CaseA.LemmaH.hcoreN_rational
#print axioms Erdos634.Geometry.CaseA.LemmaH.lemmaH_N
#print axioms Erdos634.Geometry.CaseA.LemmaH.harith_38
#print axioms Erdos634.Geometry.CaseA.LemmaH.harith_86
