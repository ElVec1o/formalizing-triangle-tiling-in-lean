-- Draft/CaseALemmaVSines.lean — CASE A, node A2 (Lemma V), real-number form, no dissection.
-- Source: (private working notes, not included) §3.2 steps 3–6.
-- The identity (★) is taken in its sine form
--     N · sin α₁ sin α₂ sin α₃ sin A = X² · sin B sin C,   X = Σ c_k sin α_k  (c_k ∈ ℕ),
-- with every angle j·π/n, 0 < j < n.  Conclusion: v_ℓ(N) is even for every prime ℓ ∤ 2n.
-- Route: ζ = e^{2πi/4n}, K = ℚ(ζ) ⊂ ℂ, 2 sin(jπ/n) = ζ^{3n}·ζ^{4n−2j}·(ζ^{4j} − 1) ∈ 𝓞 K,
-- an ℓ-unit (`LemmaV.LUnit.one_sub`), and `LemmaV.even_padicValNat`.
-- Formalization debt; NOT /goal progress.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
-- Hazard H59: no parameter pair (e, f) is evaluated here.
import Erdos634.Draft.CaseALemmaVCore

namespace Erdos634.Geometry.CaseA.LemmaV

open Complex NumberField

/-- `ζ_{4n} = e^{2πi/4n}`. -/
noncomputable def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * I / (4 * n : ℕ))

theorem zeta_prim {n : ℕ} (hn : 0 < n) : IsPrimitiveRoot (zeta n) (4 * n) :=
  Complex.isPrimitiveRoot_exp (4 * n) (by omega)

theorem zeta_pow (n k : ℕ) : zeta n ^ k = Complex.exp (k * (2 * Real.pi * I / (4 * n : ℕ))) := by
  rw [zeta, ← Complex.exp_nat_mul]

theorem zeta_pow_n {n : ℕ} (hn : 0 < n) : zeta n ^ n = I := by
  rw [zeta_pow]
  have : (n : ℂ) * (2 * Real.pi * I / (4 * n : ℕ)) = (Real.pi / 2 : ℝ) * I := by
    have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast; field_simp; ring
  rw [this, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

theorem zeta_pow_two_mul {n : ℕ} (hn : 0 < n) (j : ℕ) :
    zeta n ^ (2 * j) = Complex.exp (((j : ℝ) * Real.pi / n : ℝ) * I) := by
  rw [zeta_pow]; congr 1
  have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast; field_simp; ring

/-- **Step 4, the formula.** `2 sin(jπ/n) = ζ^{3n}·ζ^{4n−2j}·(ζ^{4j} − 1)` for `j ≤ 2n`. -/
theorem two_sin_eq {n : ℕ} (hn : 0 < n) {j : ℕ} (hj : 2 * j ≤ 4 * n) :
    ((2 * Real.sin ((j : ℝ) * Real.pi / n) : ℝ) : ℂ)
      = zeta n ^ (3 * n) * zeta n ^ (4 * n - 2 * j) * (zeta n ^ (4 * j) - 1) := by
  set θ : ℝ := (j : ℝ) * Real.pi / n
  have hE := zeta_pow_two_mul hn j
  have h1 : zeta n ^ (4 * n - 2 * j) * zeta n ^ (2 * j) = 1 := by
    rw [← pow_add, Nat.sub_add_cancel hj]; exact (zeta_prim hn).pow_eq_one
  have hinv : zeta n ^ (4 * n - 2 * j) = Complex.exp (-(θ : ℂ) * I) := by
    have h2 : Complex.exp (-(θ : ℂ) * I) * Complex.exp ((θ : ℂ) * I) = 1 := by
      rw [← Complex.exp_add]; simp
    rw [hE] at h1
    exact mul_right_cancel₀ (Complex.exp_ne_zero _) (h1.trans h2.symm)
  have h3n : zeta n ^ (3 * n) = -I := by
    rw [mul_comm, pow_mul, zeta_pow_n hn]; simp [pow_three, Complex.I_mul_I]
  have h4j : zeta n ^ (4 * j) = Complex.exp ((θ : ℂ) * I) ^ 2 := by
    rw [← hE, ← pow_mul]; ring_nf
  rw [h3n, hinv, h4j]
  push_cast
  rw [Complex.sin]
  have h2 : Complex.exp (-(θ : ℂ) * I) * Complex.exp ((θ : ℂ) * I) = 1 := by
    rw [← Complex.exp_add]; simp
  linear_combination (I * Complex.exp ((θ : ℂ) * I)) * h2

section Field

variable {n : ℕ} [NeZero n]

/-- `K = ℚ(ζ_{4n}) ⊂ ℂ`. -/
noncomputable abbrev Kf (n : ℕ) : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {zeta n}

instance : NeZero (4 * n) := ⟨by have := NeZero.ne n; omega⟩

instance cyc : IsCyclotomicExtension {4 * n} ℚ (Kf n) := by
  have hζ := zeta_prim (Nat.pos_of_ne_zero (NeZero.ne n))
  change IsCyclotomicExtension {4 * n} ℚ (Kf n).toSubalgebra
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    ((hζ.isIntegral (by have := NeZero.ne n; omega)).tower_top.isAlgebraic)]
  exact hζ.adjoin_isCyclotomicExtension ℚ

instance nf : NumberField (Kf n) := IsCyclotomicExtension.numberField {4 * n} ℚ (Kf n)

theorem zetaK_prim : IsPrimitiveRoot (⟨zeta n, IntermediateField.mem_adjoin_simple_self ℚ _⟩ :
    Kf n) (4 * n) := by
  have hζ := zeta_prim (Nat.pos_of_ne_zero (NeZero.ne n))
  exact (IsPrimitiveRoot.coe_submonoidClass_iff).mp hζ

/-- `ζ` in `𝓞 K`. -/
noncomputable def z (n : ℕ) [NeZero n] : 𝓞 (Kf n) := (zetaK_prim (n := n)).toInteger

/-- The embedding `𝓞 K → ℂ`. -/
noncomputable def φ (n : ℕ) : 𝓞 (Kf n) →+* ℂ :=
  (algebraMap (Kf n) ℂ).comp (algebraMap (𝓞 (Kf n)) (Kf n))

omit [NeZero n] in
theorem φ_inj : Function.Injective (φ n) :=
  (algebraMap (Kf n) ℂ).injective.comp RingOfIntegers.coe_injective

theorem φ_z : φ n (z n) = zeta n := rfl

/-- The element `S(jπ/n) = 2 sin(jπ/n)` of `𝓞 K`. -/
noncomputable def Sint (n : ℕ) [NeZero n] (j : ℕ) : 𝓞 (Kf n) :=
  z n ^ (3 * n) * z n ^ (4 * n - 2 * j) * (z n ^ (4 * j) - 1)

theorem φ_Sint {j : ℕ} (hj : 2 * j ≤ 4 * n) :
    φ n (Sint n j) = ((2 * Real.sin ((j : ℝ) * Real.pi / n) : ℝ) : ℂ) := by
  rw [two_sin_eq (Nat.pos_of_ne_zero (NeZero.ne n)) hj, Sint]
  simp [map_mul, map_pow, map_sub, φ_z]

/-- **Step 4, integrality.** `S(jπ/n)` is an ℓ-unit for `0 < j < n`, `ℓ ∤ n`. -/
theorem Sint_lunit {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓn : ¬ ℓ ∣ n) {j : ℕ} (hj0 : 0 < j) (hjn : j < n) :
    LUnit ℓ (Sint n j) := by
  have hz : IsPrimitiveRoot (z n) (4 * n) := (zetaK_prim (n := n)).toInteger_isPrimitiveRoot
  have hzu : IsUnit (z n) := hz.isUnit (by have := NeZero.ne n; omega)
  have hω : (z n ^ (4 * j)) ^ n = 1 := by
    rw [← pow_mul, show 4 * j * n = (4 * n) * j by ring, pow_mul, hz.pow_eq_one, one_pow]
  have hω1 : z n ^ (4 * j) ≠ 1 := hz.pow_ne_one_of_pos_of_lt (by omega) (by omega)
  have h1 := LUnit.one_sub hω hω1 hℓn
  have h2 : z n ^ (4 * j) - 1 = (-1) * (1 - z n ^ (4 * j)) := by ring
  rw [Sint, h2]
  refine ((LUnit.of_isUnit hℓ ((hzu.pow _).mul (hzu.pow _))).mul hℓ
    ((LUnit.of_isUnit hℓ isUnit_one.neg).mul hℓ h1))

end Field

/-- **Lemma V, real form.**  Angles `jπ/n` with `0 < j < n`; if
`N · sin α₀ sin α₁ sin α₂ sin β₀ = X² · sin β₁ sin β₂` with `X = Σ c_k sin α_k`, `c_k ∈ ℕ`,
then `v_ℓ(N)` is even for every prime `ℓ ∤ 2n`. -/
theorem even_of_sine_identity {n : ℕ} (hn : 0 < n) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ¬ ℓ ∣ 2 * n)
    {N : ℕ} (hN : N ≠ 0) (a : Fin 3 → ℕ) (ha0 : ∀ k, 0 < a k) (han : ∀ k, a k < n)
    (b : Fin 3 → ℕ) (hb0 : ∀ k, 0 < b k) (hbn : ∀ k, b k < n) (c : Fin 3 → ℕ)
    (h : (N : ℝ) * Real.sin (a 0 * Real.pi / n) * Real.sin (a 1 * Real.pi / n) *
        Real.sin (a 2 * Real.pi / n) * Real.sin (b 0 * Real.pi / n)
      = (∑ k, (c k : ℝ) * Real.sin (a k * Real.pi / n)) ^ 2 *
        Real.sin (b 1 * Real.pi / n) * Real.sin (b 2 * Real.pi / n)) :
    Even (padicValNat ℓ N) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓn : ¬ ℓ ∣ n := fun hd => hℓ2 (dvd_mul_of_dvd_right hd 2)
  have hℓ4n : ¬ ℓ ∣ 4 * n := by
    intro hd
    rcases (Nat.Prime.dvd_mul hℓ).mp hd with h4 | h4
    · have : ℓ ∣ 2 * 2 := h4
      rcases (Nat.Prime.dvd_mul hℓ).mp this with h2 | h2 <;>
        exact hℓ2 (dvd_mul_of_dvd_left h2 n)
    · exact hℓn h4
  have hle : ∀ j, j < n → 2 * j ≤ 4 * n := fun j hj => by omega
  apply even_padicValNat (K := Kf n) (m := 4 * n) hℓ4n hN
    (A := Sint n (a 0) * Sint n (a 1) * Sint n (a 2) * Sint n (b 0))
    (B := Sint n (b 1) * Sint n (b 2)) (Y := ∑ k, ((c k : ℤ) : 𝓞 (Kf n)) * Sint n (a k))
  · exact (((Sint_lunit hℓ hℓn (ha0 0) (han 0)).mul hℓ (Sint_lunit hℓ hℓn (ha0 1) (han 1))).mul hℓ
      (Sint_lunit hℓ hℓn (ha0 2) (han 2))).mul hℓ (Sint_lunit hℓ hℓn (hb0 0) (hbn 0))
  · exact (Sint_lunit hℓ hℓn (hb0 1) (hbn 1)).mul hℓ (Sint_lunit hℓ hℓn (hb0 2) (hbn 2))
  · apply φ_inj
    simp only [map_mul, map_pow, map_sum, map_intCast]
    rw [φ_Sint (hle _ (han 0)), φ_Sint (hle _ (han 1)), φ_Sint (hle _ (han 2)),
      φ_Sint (hle _ (hbn 0)), φ_Sint (hle _ (hbn 1)), φ_Sint (hle _ (hbn 2))]
    simp only [Fin.sum_univ_three] at h ⊢
    rw [φ_Sint (hle _ (han 0)), φ_Sint (hle _ (han 1)), φ_Sint (hle _ (han 2))]
    have h' := congrArg (fun x : ℝ => ((16 * x : ℝ) : ℂ)) h
    simp only at h'
    push_cast at h' ⊢
    linear_combination h'

/-- Witness (non-vacuity): the equilateral 4-tiling's identity, n = 3, all angles π/3,
X = 2·sin(π/3), ℓ = 5.  Every hypothesis holds (the identity by `ring`). -/
example : Even (padicValNat 5 4) :=
  even_of_sine_identity (n := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ![1, 1, 1] (by decide) (by decide) ![1, 1, 1] (by decide) (by decide) ![2, 0, 0]
    (by simp [Fin.sum_univ_three]; ring)

end Erdos634.Geometry.CaseA.LemmaV

#print axioms Erdos634.Geometry.CaseA.LemmaV.two_sin_eq
#print axioms Erdos634.Geometry.CaseA.LemmaV.even_of_sine_identity
