-- Draft/CaseALemmaHExc2.lean — CASE A, node A9 (Lemma H): the four remaining exceptional cores
-- π/8, π/12, π/10, π/5, by the SAME cyclotomic method as the generic case, one level down:
-- ζ = e^{iθ} has degree ≥ 4 over ℚ(i) (so 1, ζ, ζ², ζ³ are ℚ(i)-independent), and ζ⁴ is an explicit
-- ℚ(i)-combination of 1, ζ, ζ², ζ³.  Substituting into ζ²(X² − p/2) = 0 gives four coefficient
-- equations in A = (y − ix)/2, B = (y + ix)/2, whose only solutions give 2X² ∈ {2r², 3x², 10r², …},
-- never a prime ≥ 5.  (This replaces LEMMA_H.md step 6's conductor fact / square-class tables.)
-- Then `lemmaH` : Lemma H as written, unconditional.
-- Formalization debt; NOT /goal progress.  Imported into All.lean (All.lean:634); on the theoremP_6 closure (UNAUDITED).  H59: no (e, f) evaluated.
import Erdos634.Draft.CaseALemmaHGlue

namespace Erdos634.Geometry.CaseA.LemmaH

open Real

/-! ## The coefficient identity and the four-coefficient extraction -/

/-- `ζ²(X² − p/2)` expanded: `B² + 2rBζ + Cζ² + 2rAζ³ + A²ζ⁴ = 0`. -/
theorem key_rel {θ : ℝ} {r x y p : ℕ}
    (hX : 2 * ((r : ℝ) + x * Real.sin θ + y * Real.cos θ) ^ 2 = p) :
    let e := Complex.exp (θ * Complex.I)
    let A : ℂ := ((y : ℂ) - Complex.I * x) / 2
    let B : ℂ := ((y : ℂ) + Complex.I * x) / 2
    B ^ 2 + 2 * r * B * e + (r ^ 2 + 2 * A * B - p / 2) * e ^ 2 + 2 * r * A * e ^ 3
      + A ^ 2 * e ^ 4 = 0 := by
  intro e A B
  set e' := Complex.exp (-(θ : ℂ) * Complex.I) with he'_def
  have hee : e * e' = 1 := by
    show Complex.exp (θ * Complex.I) * e' = 1
    rw [he'_def, ← Complex.exp_add]; ring_nf; simp
  have hXc : 2 * ((r : ℂ) + x * Complex.sin θ + y * Complex.cos θ) ^ 2 = p := by
    have := congrArg (fun t : ℝ => (t : ℂ)) hX
    push_cast at this
    exact this
  have hsin : Complex.sin θ = (e' - e) * Complex.I / 2 := rfl
  have hcos : Complex.cos θ = (e + e') / 2 := rfl
  rw [hsin, hcos] at hXc
  set Xc := (r : ℂ) + x * ((e' - e) * Complex.I / 2) + y * ((e + e') / 2) with hXc_def
  have hXe : Xc * e = r * e + A * e ^ 2 + B := by
    rw [hXc_def]
    simp only [A, B]
    linear_combination (↑x * Complex.I / 2 + ↑y / 2) * hee
  linear_combination (-(Xc * e + (r * e + A * e ^ 2 + B))) * hXe + (e ^ 2 / 2) * hXc

/-- Independence of `1, ζ, ζ², ζ³` from a primitive root `u·ζ` of order `M` with φ(M) ≥ 8. -/
theorem indep4 {ζ ω : ℂ} (u : QI) (hu : u ≠ 0) (hωu : (u : ℂ) * ζ = ω) {M : ℕ}
    (hω : IsPrimitiveRoot ω M) (hM : 0 < M) (h8 : 8 ≤ M.totient) :
    LinearIndependent QI (fun k : Fin 4 => ζ ^ (k : ℕ)) := by
  have hd := totient_le_two_mul_deg hω hM
  have h4 : 4 ≤ (minpoly QI ω).natDegree := by omega
  have hI := (linearIndependent_pow (K := QI) ω).comp (Fin.castLE h4) (Fin.castLE_injective h4)
  rw [Fintype.linearIndependent_iff] at hI ⊢
  intro g hg k
  have hu' : (u : ℂ) ≠ 0 := by exact_mod_cast hu
  have := hI (fun k => g k * u⁻¹ ^ (k : ℕ)) (by
    rw [← hg]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [Function.comp_apply, Fin.val_castLE, IntermediateField.smul_def, smul_eq_mul]
    rw [← hωu]
    push_cast
    have e1 : (u : ℂ)⁻¹ ^ (k : ℕ) * ((u : ℂ) * ζ) ^ (k : ℕ) = ζ ^ (k : ℕ) := by
      rw [← mul_pow]; congr 1; field_simp
    rw [mul_assoc, e1]) k
  simpa [hu] using this

/-- **Four-coefficient extraction.**  If `1, ζ, ζ², ζ³` are ℚ(i)-independent and
`ζ⁴ = a₀ + a₁ζ + a₂ζ² + a₃ζ³` with `aₖ ∈ ℚ(i)`, then `2X² = p` forces the four equations
`B² + A²a₀ = 0`, `2rB + A²a₁ = 0`, `C + A²a₂ = 0`, `2rA + A²a₃ = 0`. -/
theorem four_coeffs {θ : ℝ} {r x y p : ℕ}
    (hind : LinearIndependent QI (fun k : Fin 4 => Complex.exp (θ * Complex.I) ^ (k : ℕ)))
    (a0 a1 a2 a3 : QI)
    (hrel : Complex.exp (θ * Complex.I) ^ 4 = a0 + a1 * Complex.exp (θ * Complex.I)
      + a2 * Complex.exp (θ * Complex.I) ^ 2 + a3 * Complex.exp (θ * Complex.I) ^ 3)
    (hX : 2 * ((r : ℝ) + x * Real.sin θ + y * Real.cos θ) ^ 2 = p) :
    let A : ℂ := ((y : ℂ) - Complex.I * x) / 2
    let B : ℂ := ((y : ℂ) + Complex.I * x) / 2
    B ^ 2 + A ^ 2 * a0 = 0 ∧ 2 * r * B + A ^ 2 * a1 = 0 ∧
      (r ^ 2 + 2 * A * B - p / 2) + A ^ 2 * a2 = 0 ∧ 2 * r * A + A ^ 2 * a3 = 0 := by
  intro A B
  have hk := key_rel (r := r) (x := x) (y := y) (p := p) hX
  simp only at hk
  set e := Complex.exp (θ * Complex.I)
  set iQ : QI := ⟨Complex.I, I_mem⟩
  have hc2 : ((2 : QI) : ℂ) = 2 := by
    rw [show (2 : QI) = ((2 : ℕ) : QI) from (Nat.cast_ofNat).symm]; push_cast; rfl
  set A' : QI := ((y : QI) - iQ * (x : QI)) / 2
  set B' : QI := ((y : QI) + iQ * (x : QI)) / 2
  have hA : (A' : ℂ) = A := by simp [A', iQ, hc2, A]
  have hB : (B' : ℂ) = B := by simp [B', iQ, hc2, B]
  set g : Fin 4 → QI := ![B' ^ 2 + A' ^ 2 * a0, 2 * (r : QI) * B' + A' ^ 2 * a1,
    ((r : QI) ^ 2 + 2 * A' * B' - (p : QI) / 2) + A' ^ 2 * a2, 2 * (r : QI) * A' + A' ^ 2 * a3]
  have hsum : ∑ k, g k • (fun k : Fin 4 => e ^ (k : ℕ)) k = 0 := by
    rw [Fin.sum_univ_four]
    simp only [IntermediateField.smul_def, smul_eq_mul]
    have g0 : g 0 = B' ^ 2 + A' ^ 2 * a0 := rfl
    have g1 : g 1 = 2 * (r : QI) * B' + A' ^ 2 * a1 := rfl
    have g2 : g 2 = ((r : QI) ^ 2 + 2 * A' * B' - (p : QI) / 2) + A' ^ 2 * a2 := rfl
    have g3 : g 3 = 2 * (r : QI) * A' + A' ^ 2 * a3 := rfl
    have c0 : ((0 : Fin 4) : ℕ) = 0 := rfl
    have c1 : ((1 : Fin 4) : ℕ) = 1 := rfl
    have c2 : ((2 : Fin 4) : ℕ) = 2 := rfl
    have c3 : ((3 : Fin 4) : ℕ) = 3 := rfl
    rw [g0, g1, g2, g3, c0, c1, c2, c3]
    push_cast
    simp only [hc2, hA, hB]
    linear_combination hk - A ^ 2 * hrel
  have hz := Fintype.linearIndependent_iff.mp hind g hsum
  have z0 := congrArg Subtype.val (hz 0)
  have z1 := congrArg Subtype.val (hz 1)
  have z2 := congrArg Subtype.val (hz 2)
  have z3 := congrArg Subtype.val (hz 3)
  simp only [g, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons] at z0 z1 z2 z3
  push_cast at z0 z1 z2 z3
  simp only [hc2, hA, hB] at z0 z1 z2 z3
  exact ⟨by simpa using z0, by simpa using z1, by simpa using z2, by simpa using z3⟩

/-! ## Elementary number theory -/

/-- `a² = 2b²` in ℤ forces `b = 0` (√2 irrational). -/
theorem sq_eq_two_sq {a b : ℤ} (h : a ^ 2 = 2 * b ^ 2) : b = 0 := by
  by_contra hb
  apply irrational_sqrt_two
  refine ⟨|(a : ℚ)| / |(b : ℚ)|, ?_⟩
  have hb' : (|(b : ℝ)|) ≠ 0 := by simpa using hb
  have hsq : (|(a : ℝ)| / |(b : ℝ)|) ^ 2 = 2 := by
    rw [div_pow, sq_abs, sq_abs]
    have : ((a : ℝ)) ^ 2 = 2 * (b : ℝ) ^ 2 := by exact_mod_cast h
    rw [this]; field_simp
  have := Real.sqrt_sq (show (0 : ℝ) ≤ |(a : ℝ)| / |(b : ℝ)| by positivity)
  rw [hsq] at this
  push_cast
  exact this.symm

theorem three_sq_ne_prime {x p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : 3 * x ^ 2 ≠ p := by
  intro h
  rcases hp.eq_one_or_self_of_dvd 3 ⟨x ^ 2, h.symm⟩ with h1 | h1 <;> omega

/-! ## The four cores -/

theorem exp_pi_div_two_I : Complex.exp (↑(Real.pi / 2) * Complex.I) = Complex.I := by
  rw [Complex.exp_mul_I]; push_cast; rw [Complex.cos_pi_div_two, Complex.sin_pi_div_two]; ring

theorem exp_pow_eq {θ : ℝ} (k : ℕ) :
    Complex.exp (θ * Complex.I) ^ k = Complex.exp (↑(k * θ) * Complex.I) := by
  rw [← Complex.exp_nat_mul]; push_cast; ring_nf

theorem prim_of {θ : ℝ} {j M : ℕ} (hM : M ≠ 0) (hj : j.Coprime M)
    (hθ : θ = 2 * Real.pi * j / M) : IsPrimitiveRoot (Complex.exp (θ * Complex.I)) M := by
  have h := Complex.isPrimitiveRoot_exp_of_coprime j M hM hj
  convert h using 2
  rw [hθ]; push_cast; ring

/-- θ = π/8: ζ⁴ = i. -/
theorem core_pi_div_eight : HCore (Real.pi / 8) := by
  intro r x y p hp hp5 hX
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
  obtain ⟨e0, e1, e2, -⟩ := four_coeffs hind _ _ _ _ hrel hX
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
    have : (p : ℝ) = 0 := by simp at r2; linarith
    have : p = 0 := by exact_mod_cast this
    exact hp.ne_zero this
  · subst hx
    rcases r1 with hr | hy
    · subst hr
      have : (y : ℝ) = 0 := by simp at r0; nlinarith
      have hy' : y = 0 := by exact_mod_cast this
      subst hy'
      have : (p : ℝ) = 0 := by simp at r2; linarith
      have : p = 0 := by exact_mod_cast this
      exact hp.ne_zero this
    · subst hy
      have : 2 * (r : ℝ) ^ 2 = p := by simp at r2; linarith
      exact two_sq_ne_prime hp (by omega) (by exact_mod_cast this)

theorem exp_eq_cos_sin (t : ℝ) :
    Complex.exp (↑t * Complex.I) = (Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- θ = π/12: ζ⁴ = 1 + iζ² (ζ² = e^{iπ/6}). -/
theorem core_pi_div_twelve : HCore (Real.pi / 12) := by
  intro r x y p hp hp5 hX
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
  obtain ⟨e0, e1, e2, -⟩ := four_coeffs hind _ _ _ _ hrel hX
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
    have : 3 * (x : ℝ) ^ 2 = p := by rw [← hxy] at r2; simp at r2; linarith
    exact three_sq_ne_prime hp hp5 (by exact_mod_cast this)
  · subst hx
    have hy' : y = 0 := by
      first
      | exact r0
      | exact_mod_cast (show (y : ℝ) = 0 by nlinarith)
    subst hy'
    have : 2 * (r : ℝ) ^ 2 = p := by simp at r2; linarith
    exact two_sq_ne_prime hp (by omega) (by exact_mod_cast this)

/-- θ = π/10: ζ⁴ = −1 + iζ + ζ² − iζ³ (from Φ₅(ζ⁴) = 0 and ζ⁵ = i). -/
theorem core_pi_div_ten : HCore (Real.pi / 10) := by
  intro r x y p hp hp5 hX
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
  obtain ⟨e0, e1, e2, -⟩ := four_coeffs hind (-1) _ 1 _ hrel hX
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
    have : 2 * (r : ℝ) ^ 2 = p := by rw [hx, hy] at r2; linarith
    exact two_sq_ne_prime hp (by omega) (by exact_mod_cast this)
  · rw [hy] at i1 r2
    have hx4 : (x : ℝ) * (4 * r - x) = 0 := by linear_combination 4 * i1
    rcases mul_eq_zero.mp hx4 with hx | hx
    · have : 2 * (r : ℝ) ^ 2 = p := by rw [hx] at r2; linarith
      exact two_sq_ne_prime hp (by omega) (by exact_mod_cast this)
    · have hx' : (x : ℝ) = 4 * r := by linarith
      have : 2 * ((5 * r ^ 2 : ℕ) : ℝ) = p := by push_cast; rw [hx'] at r2; linarith
      have h2 : 2 * (5 * r ^ 2) = p := by exact_mod_cast this
      rcases hp.eq_one_or_self_of_dvd 2 ⟨_, h2.symm⟩ with h1 | h1 <;> omega

/-- θ = π/5: ζ⁴ = −1 + ζ − ζ² + ζ³ (ζ⁵ = −1, ζ ≠ −1); independence via the primitive 20th root
`i·ζ`. -/
theorem core_pi_div_five : HCore (Real.pi / 5) := by
  intro r x y p hp hp5 hX
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
  obtain ⟨e0, e1, e2, e3⟩ := four_coeffs hind _ _ _ _ hrel hX
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
  have : 2 * (r : ℝ) ^ 2 = p := by rw [hx.1, hx.2] at r2; linarith
  exact two_sq_ne_prime hp (by omega) (by exact_mod_cast this)

/-! ## Lemma H, unconditional -/

/-- **Lemma H** (row 1, `LEMMA_H.md` §1, node A9), as written: let the target of a
`CongruentDissection N` be isosceles with base angle θ ∈ ℚπ, 0 < θ < π/2 (θ at two distinct target
vertices), and let the tile be right with an acute angle θ (any labelling of model and target,
reflections allowed, no edge-to-edge assumption).  Then N is not a prime ≥ 5. -/
theorem lemmaH {N : ℕ} (D : CongruentDissection N) {θ : ℝ} (hq : ∃ q : ℚ, θ = q * Real.pi)
    (hθ0 : 0 < θ) (hθ2 : θ < Real.pi / 2)
    {p q : Fin 3} (hpq : p ≠ q) (hmp : D.model.angleAt p = θ) (hmq : D.model.angleAt q = Real.pi / 2)
    {i j : Fin 3} (hij : i ≠ j) (hi : D.target.angleAt i = θ) (hj : D.target.angleAt j = θ) :
    ¬ (N.Prime ∧ 5 ≤ N) :=
  lemmaH_rational ⟨core_pi_div_eight, core_pi_div_twelve, core_pi_div_ten, core_pi_div_five⟩
    D hq hθ0 hθ2 hpq hmp hmq hij hi hj

/-- The algebraic core alone: for θ ∈ ℚπ, 0 < θ < π/2, `2(r + x sin θ + y cos θ)² ≠ p` for every
prime p ≥ 5 and r, x, y ∈ ℕ. -/
theorem hcore_all {θ : ℝ} (hq : ∃ q : ℚ, θ = q * Real.pi) (hθ0 : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    HCore θ :=
  hcore_rational ⟨core_pi_div_eight, core_pi_div_twelve, core_pi_div_ten, core_pi_div_five⟩
    hq hθ0 hθ2

end Erdos634.Geometry.CaseA.LemmaH

#print axioms Erdos634.Geometry.CaseA.LemmaH.four_coeffs
#print axioms Erdos634.Geometry.CaseA.LemmaH.core_pi_div_eight
#print axioms Erdos634.Geometry.CaseA.LemmaH.core_pi_div_twelve
#print axioms Erdos634.Geometry.CaseA.LemmaH.core_pi_div_ten
#print axioms Erdos634.Geometry.CaseA.LemmaH.core_pi_div_five
#print axioms Erdos634.Geometry.CaseA.LemmaH.hcore_all
#print axioms Erdos634.Geometry.CaseA.LemmaH.lemmaH
