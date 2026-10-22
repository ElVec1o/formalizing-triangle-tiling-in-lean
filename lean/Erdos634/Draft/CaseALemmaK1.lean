-- Draft/CaseALemmaK1.lean — CASE A, node A3 (Lemma K), the K1 half, on a REAL `CongruentDissection`.
-- Source: (private working notes, not included) §3.3 (K1 = "s_T(k) = s_ABC(k)"), with K1
-- exactly the predicate `LemmaKStar.K1` of Draft/CaseALemmaKStar.lean (VERIFIED Lemma K*).
--
-- ROUTE (no conjugate dissection, no winding numbers — blocker B-K is NOT needed for K1):
--   (★) N·S(α₀)S(α₁)S(α₂)S(B₀) = X²·S(B₁)S(B₂), S = 2 sin, X = Σ c_k S(α_k)  (`LemmaV.star`, an
--   identity with ℕ-coefficients among elements of ℚ(ζ_{4n}));
--   apply ANY ℚ-embedding σ : ℚ(ζ_{4n}) → ℂ, ζ ↦ ζ^{k'} (k' ≡ k mod n, k' odd);
--   σ(S(jπ/n)) = c·S(jk'π/n) with one c ≠ 0, so the same identity holds with conjugated sines, and
--   σ(X) = c·(real) — hence Π_i S(a_i k'π/n)·Π_j S(u_j k'π/n) > 0;
--   the sign of S(mπ/n) is (−1)^⌊m/n⌋, and Σ_i ⌊a_i k'/n⌋ = k' − s_T(k), Σ_j ⌊u_j k'/n⌋ = k' − s_ABC(k);
--   so s_T(k) ≡ s_ABC(k) (mod 2), i.e. K1(k).
-- This is the paper's (ii)+(iii)-consequence "ε = ε_ABC" obtained from the AREA identity alone.
-- K2 is NOT obtained here (it is not an arithmetic consequence of K1; see the final report).
-- Formalization debt on a paper-level PROVED node; NOT /goal progress.  Imported into All.lean (All.lean:671).
-- Hazard H59: no parameter pair (e, f) is evaluated here.
import Erdos634.Draft.CaseALemmaVDissection
import Erdos634.Draft.CaseALemmaKStar

namespace Erdos634.Geometry.CaseA.LemmaK1

open Erdos634.Geometry Complex Erdos634.Geometry.CaseA.LemmaV Erdos634.LemmaKStar

/-! ## §1 The Galois embedding ζ ↦ ζ^k -/

theorem exists_sigma {n : ℕ} (hn : 0 < n) {k : ℕ} (hk : k.Coprime (4 * n)) :
    ∃ σ : Kf n →ₐ[ℚ] ℂ,
      σ (IntermediateField.AdjoinSimple.gen ℚ (zeta n)) = zeta n ^ k := by
  have hζ := zeta_prim hn
  have hint : IsIntegral ℚ (zeta n) := (hζ.isIntegral (by omega)).tower_top
  have hroot : zeta n ^ k ∈ (minpoly ℚ (zeta n)).aroots ℂ := by
    rw [Polynomial.mem_aroots]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hζ (by omega)]
    have h := (Polynomial.isRoot_cyclotomic_iff_charZero (R := ℂ) (by omega : 0 < 4 * n)).mpr
      (hζ.pow_of_coprime k hk)
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact h
  exact ⟨(IntermediateField.algHomAdjoinIntegralEquiv ℚ hint).symm ⟨_, hroot⟩,
    IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hint _⟩

/-! ## §2 Sines as field elements and their conjugates -/

/-- `S(jπ/n) = 2 sin(jπ/n)` as an element of `ℚ(ζ_{4n})`. -/
noncomputable def eS (n j : ℕ) : Kf n :=
  let g := IntermediateField.AdjoinSimple.gen ℚ (zeta n)
  g ^ (3 * n) * g ^ (4 * n - 2 * j) * (g ^ (4 * j) - 1)

theorem coe_eS {n : ℕ} (hn : 0 < n) {j : ℕ} (hj : 2 * j ≤ 4 * n) :
    ((eS n j : Kf n) : ℂ) = ((2 * Real.sin ((j : ℝ) * Real.pi / n) : ℝ) : ℂ) := by
  rw [two_sin_eq hn hj, eS]
  simp

/-- `ζ^k` raised to `4n − 2j`, times `(ζ^k)^{4j} − 1`, is `i·2 sin(jkπ/n)`. -/
theorem conj_core {n : ℕ} (hn : 0 < n) (k : ℕ) {j : ℕ} (hj : 2 * j ≤ 4 * n) :
    (zeta n ^ k) ^ (4 * n - 2 * j) * ((zeta n ^ k) ^ (4 * j) - 1)
      = I * ((2 * Real.sin (((j * k : ℕ) : ℝ) * Real.pi / n) : ℝ) : ℂ) := by
  set θ : ℝ := ((j * k : ℕ) : ℝ) * Real.pi / n
  have hE : (zeta n ^ k) ^ (2 * j) = Complex.exp ((θ : ℂ) * I) := by
    rw [← pow_mul, show k * (2 * j) = 2 * (j * k) by ring, zeta_pow_two_mul hn]
  have h1 : (zeta n ^ k) ^ (4 * n - 2 * j) * (zeta n ^ k) ^ (2 * j) = 1 := by
    rw [← pow_mul, ← pow_mul, ← pow_add, ← mul_add, Nat.sub_add_cancel hj, pow_mul',
      (zeta_prim hn).pow_eq_one, one_pow]
  rw [hE] at h1
  have h4 : (zeta n ^ k) ^ (4 * j) = Complex.exp ((θ : ℂ) * I) ^ 2 := by
    rw [← hE, ← pow_mul]; ring_nf
  have h2 : Complex.exp (-(θ : ℂ) * I) * Complex.exp ((θ : ℂ) * I) = 1 := by
    rw [← Complex.exp_add]; simp
  have hW : (zeta n ^ k) ^ (4 * n - 2 * j) = Complex.exp (-(θ : ℂ) * I) :=
    mul_right_cancel₀ (Complex.exp_ne_zero _) (h1.trans h2.symm)
  rw [h4, hW]
  push_cast
  rw [Complex.sin]
  have hI : I * I = -1 := Complex.I_mul_I
  linear_combination (Complex.exp ((θ : ℂ) * I)) * h2
    + (-(Complex.exp (-(θ : ℂ) * I)) + Complex.exp ((θ : ℂ) * I)) * hI

theorem sigma_eS {n : ℕ} (hn : 0 < n) {k : ℕ} (σ : Kf n →ₐ[ℚ] ℂ)
    (hσ : σ (IntermediateField.AdjoinSimple.gen ℚ (zeta n)) = zeta n ^ k) {j : ℕ}
    (hj : 2 * j ≤ 4 * n) :
    σ (eS n j) = ((zeta n ^ k) ^ (3 * n) * I)
      * ((2 * Real.sin (((j * k : ℕ) : ℝ) * Real.pi / n) : ℝ) : ℂ) := by
  simp only [eS, map_mul, map_pow, map_sub, map_one, hσ]
  rw [mul_assoc, conj_core hn k hj]; ring

/-! ## §3 The (★) expression, transported -/

/-- `Ψ = N·s₀s₁s₂t₀ − (Σ c_k s_k)²·t₁t₂`. -/
def Ψ {R : Type*} [CommRing R] (N : ℕ) (c : Fin 3 → ℕ) (s t : Fin 3 → R) : R :=
  (N : R) * s 0 * s 1 * s 2 * t 0 - (∑ k, (c k : R) * s k) ^ 2 * t 1 * t 2

theorem Ψ_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) (c : Fin 3 → ℕ)
    (s t : Fin 3 → R) : f (Ψ N c s t) = Ψ N c (fun i => f (s i)) (fun i => f (t i)) := by
  simp [Ψ, map_sub, map_mul, map_pow, map_sum, map_natCast]

theorem Ψ_smul {R : Type*} [CommRing R] (N : ℕ) (c : Fin 3 → ℕ) (u : R) (s t : Fin 3 → R) :
    Ψ N c (fun i => u * s i) (fun i => u * t i) = u ^ 4 * Ψ N c s t := by
  simp only [Ψ, Fin.sum_univ_three]; ring

/-- (★) with its sines conjugated: for every `k` coprime to `4n`. -/
theorem conj_star {n : ℕ} (hn : 0 < n) {N : ℕ} (c a b : Fin 3 → ℕ) (ha : ∀ i, a i < n)
    (hb : ∀ i, b i < n)
    (h : (N : ℝ) * Real.sin (a 0 * Real.pi / n) * Real.sin (a 1 * Real.pi / n) *
        Real.sin (a 2 * Real.pi / n) * Real.sin (b 0 * Real.pi / n)
      = (∑ k, (c k : ℝ) * Real.sin (a k * Real.pi / n)) ^ 2 *
        Real.sin (b 1 * Real.pi / n) * Real.sin (b 2 * Real.pi / n))
    {k : ℕ} (hk : k.Coprime (4 * n)) :
    Ψ N c (fun i => 2 * Real.sin (((a i * k : ℕ) : ℝ) * Real.pi / n))
      (fun i => 2 * Real.sin (((b i * k : ℕ) : ℝ) * Real.pi / n)) = 0 := by
  obtain ⟨σ, hσ⟩ := exists_sigma hn hk
  have hle : ∀ {j : ℕ}, j < n → 2 * j ≤ 4 * n := fun h => by omega
  -- the real identity
  have hR : Ψ N c (fun i => 2 * Real.sin ((a i : ℝ) * Real.pi / n))
      (fun i => 2 * Real.sin ((b i : ℝ) * Real.pi / n)) = 0 := by
    simp only [Ψ, Fin.sum_univ_three] at h ⊢
    linear_combination 16 * h
  -- in the field
  have hK : Ψ N c (fun i => eS n (a i)) (fun i => eS n (b i)) = 0 := by
    apply (algebraMap (Kf n) ℂ).injective
    rw [Ψ_map, map_zero]
    have e1 : (fun i => algebraMap (Kf n) ℂ (eS n (a i)))
        = fun i => Complex.ofRealHom (2 * Real.sin ((a i : ℝ) * Real.pi / n)) := by
      funext i; exact coe_eS hn (hle (ha i))
    have e2 : (fun i => algebraMap (Kf n) ℂ (eS n (b i)))
        = fun i => Complex.ofRealHom (2 * Real.sin ((b i : ℝ) * Real.pi / n)) := by
      funext i; exact coe_eS hn (hle (hb i))
    have hm := Ψ_map Complex.ofRealHom N c (fun i => 2 * Real.sin ((a i : ℝ) * Real.pi / n))
      (fun i => 2 * Real.sin ((b i : ℝ) * Real.pi / n))
    rw [e1, e2, ← hm, hR, map_zero]
  have hC := congrArg σ.toRingHom hK
  rw [Ψ_map, map_zero] at hC
  have e3 : (fun i => σ.toRingHom (eS n (a i))) = fun i => ((zeta n ^ k) ^ (3 * n) * I) *
      Complex.ofRealHom (2 * Real.sin (((a i * k : ℕ) : ℝ) * Real.pi / n)) := by
    funext i; exact sigma_eS hn σ hσ (hle (ha i))
  have e4 : (fun i => σ.toRingHom (eS n (b i))) = fun i => ((zeta n ^ k) ^ (3 * n) * I) *
      Complex.ofRealHom (2 * Real.sin (((b i * k : ℕ) : ℝ) * Real.pi / n)) := by
    funext i; exact sigma_eS hn σ hσ (hle (hb i))
  have hm := Ψ_map Complex.ofRealHom N c
    (fun i => 2 * Real.sin (((a i * k : ℕ) : ℝ) * Real.pi / n))
    (fun i => 2 * Real.sin (((b i * k : ℕ) : ℝ) * Real.pi / n))
  rw [e3, e4, Ψ_smul, ← hm] at hC
  have hc : ((zeta n ^ k) ^ (3 * n) * I) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ (Complex.exp_ne_zero _))) Complex.I_ne_zero
  have := (mul_eq_zero.mp hC).resolve_left (pow_ne_zero _ hc)
  exact Complex.ofReal_eq_zero.mp this

/-! ## §4 Signs of sines -/

theorem two_sin_sign {n : ℕ} (hn : 0 < n) (m : ℤ) :
    2 * Real.sin ((m : ℝ) * Real.pi / n)
      = (-1 : ℝ) ^ ⌊((m : ℚ) / n)⌋ * (2 * Real.sin (((Int.fract ((m : ℚ) / n) : ℚ) : ℝ) * Real.pi)) := by
  have hq := Int.fract_add_floor ((m : ℚ) / n)
  have hr : (m : ℝ) / n = ((Int.fract ((m : ℚ) / n) : ℚ) : ℝ) + ((⌊((m : ℚ) / n)⌋ : ℤ) : ℝ) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) hq
    simp only [Rat.cast_add, Rat.cast_intCast, Rat.cast_div, Rat.cast_natCast] at this
    exact this.symm
  have : (m : ℝ) * Real.pi / n = ((Int.fract ((m : ℚ) / n) : ℚ) : ℝ) * Real.pi
      + ((⌊((m : ℚ) / n)⌋ : ℤ) : ℝ) * Real.pi := by
    rw [mul_div_right_comm, hr]; ring
  rw [this, Real.sin_add_int_mul_pi]; ring

theorem sin_fract_pos {q : ℚ} (h : Int.fract q ≠ 0) :
    0 < 2 * Real.sin (((Int.fract q : ℚ) : ℝ) * Real.pi) := by
  have h0 : (0 : ℝ) < ((Int.fract q : ℚ) : ℝ) := by
    exact_mod_cast lt_of_le_of_ne (Int.fract_nonneg q) (Ne.symm h)
  have h1 : ((Int.fract q : ℚ) : ℝ) < 1 := by exact_mod_cast Int.fract_lt_one q
  have := Real.sin_pos_of_pos_of_lt_pi (mul_pos h0 Real.pi_pos) (by nlinarith [Real.pi_pos])
  linarith

/-! ## §5 Arithmetic: the lift and the floor sums -/

variable {n : ℕ} {a : Fin 3 → ℕ}

theorem yv_congr {k k' : ℤ} (h : (n : ℤ) ∣ k' - k) (hn : 0 < n) (i : Fin 3) :
    yv n a k' i = yv n a k i := by
  obtain ⟨t, ht⟩ := h
  unfold yv
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have : (((k' * (a i : ℤ) : ℤ) : ℚ) / n) = (((k * (a i : ℤ) : ℤ) : ℚ) / n) + ((t * a i : ℤ) : ℚ) := by
    have hk' : k' = k + n * t := by linarith
    rw [hk']; push_cast; field_simp
  rw [this, Int.fract_add_intCast]

theorem floor_sum (hsum : ∑ i, a i = n) (hn : 0 < n) (k : ℤ) :
    ((∑ i, ⌊(((k * (a i : ℤ) : ℤ) : ℚ) / n)⌋ : ℤ) : ℚ) = k - sT n a k := by
  have h := sum_raw hsum hn k
  unfold sT yv
  have e : ∀ i, ((⌊(((k * (a i : ℤ) : ℤ) : ℚ) / n)⌋ : ℤ) : ℚ)
      = (((k * (a i : ℤ) : ℤ) : ℚ) / n) - Int.fract ((((k * (a i : ℤ) : ℤ) : ℚ) / n)) :=
    fun i => (Int.self_sub_fract _).symm
  rw [Int.cast_sum, Finset.sum_congr rfl (fun i _ => e i), Finset.sum_sub_distrib, h]

theorem exists_lift (hn : 0 < n) {k : ℤ} (hk : Int.gcd k n = 1) :
    ∃ k' : ℕ, k'.Coprime (4 * n) ∧ (n : ℤ) ∣ (k' : ℤ) - k := by
  classical
  set k0 : ℤ := k + 2 * n * (|k| + 1) + (if Even k then (n : ℤ) else 0) with hk0
  have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have hpos : 0 ≤ k0 := by
    have habs := neg_abs_le k
    have : (0 : ℤ) ≤ (if Even k then (n : ℤ) else 0) := by split_ifs <;> omega
    nlinarith [abs_nonneg k, neg_abs_le k, mul_nonneg (sub_nonneg.mpr hn1) (abs_nonneg k)]
  have hodd : Odd k0 := by
    by_cases he : Even k
    · simp only [hk0, he, if_true]
      have hno : Odd (n : ℤ) := by
        rcases Int.even_or_odd (n : ℤ) with h | h
        · exfalso
          have h2k : (2 : ℤ) ∣ k := he.two_dvd
          have h2n : (2 : ℤ) ∣ (n : ℤ) := h.two_dvd
          have := Int.dvd_gcd h2k h2n
          rw [hk] at this; norm_num at this
        · exact h
      have : Even (k + 2 * n * (|k| + 1)) := he.add (by exact ⟨n * (|k| + 1), by ring⟩)
      exact this.add_odd hno
    · simp only [hk0, he, if_false, add_zero]
      rw [Int.not_even_iff_odd] at he
      exact he.add_even ⟨n * (|k| + 1), by ring⟩
  refine ⟨k0.toNat, ?_, ?_⟩
  · have hc : ((k0.toNat : ℕ) : ℤ) = k0 := Int.toNat_of_nonneg hpos
    have hoddN : Odd k0.toNat := by rw [← Int.odd_coe_nat, hc]; exact hodd
    have h4 : k0.toNat.Coprime 4 := by
      have : k0.toNat.Coprime 2 := Nat.coprime_two_right.mpr hoddN
      simpa using Nat.Coprime.pow_right 2 this
    have hcn : k0.toNat.Coprime n := by
      rw [← Nat.isCoprime_iff_coprime, hc]
      have hcop : IsCoprime k (n : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hk
      have := hcop.add_mul_left_left (2 * (|k| + 1) + (if Even k then 1 else 0))
      convert this using 1
      rw [hk0]; split_ifs <;> ring
    exact Nat.Coprime.mul_right h4 hcn
  · rw [Int.toNat_of_nonneg hpos, hk0]
    refine ⟨2 * (|k| + 1) + (if Even k then 1 else 0), ?_⟩
    split_ifs <;> ring

/-! ## §6 K1 from the conjugated (★) -/

/-- **Arithmetic core of K1.**  If (★) holds for angles `a_iπ/n` (tile) and `b_jπ/n` (target),
both summing to `n`, then for every unit `k` mod `n`: `s_T(k) = s_T^b(k)`. -/
theorem sT_eq_of_star {N : ℕ} (hN : N ≠ 0) (hn : 0 < n) (c b : Fin 3 → ℕ)
    (ha1 : ∀ i, 1 ≤ a i) (hsa : ∑ i, a i = n) (hb1 : ∀ i, 1 ≤ b i) (hsb : ∑ i, b i = n)
    (h : (N : ℝ) * Real.sin (a 0 * Real.pi / n) * Real.sin (a 1 * Real.pi / n) *
        Real.sin (a 2 * Real.pi / n) * Real.sin (b 0 * Real.pi / n)
      = (∑ k, (c k : ℝ) * Real.sin (a k * Real.pi / n)) ^ 2 *
        Real.sin (b 1 * Real.pi / n) * Real.sin (b 2 * Real.pi / n))
    {k : ℤ} (hk : Int.gcd k n = 1) : sT n a k = sT n b k := by
  obtain ⟨k', hk'c, hk'd⟩ := exists_lift hn hk
  have hΨ := conj_star hn c a b (fun i => a_lt hsa ha1 i) (fun i => a_lt hsb hb1 i) h hk'c
  -- sign decomposition of each conjugated sine
  have hcast : ∀ j : ℕ, (((j * k' : ℕ) : ℝ)) = (((k' : ℤ) * (j : ℤ) : ℤ) : ℝ) := by
    intro j; push_cast; ring
  set fa : Fin 3 → ℤ := fun i => ⌊((((k' : ℤ) * (a i : ℤ) : ℤ) : ℚ) / n)⌋
  set fb : Fin 3 → ℤ := fun i => ⌊((((k' : ℤ) * (b i : ℤ) : ℤ) : ℚ) / n)⌋
  set pa : Fin 3 → ℝ := fun i => 2 * Real.sin (((yv n a k i : ℚ) : ℝ) * Real.pi)
  set pb : Fin 3 → ℝ := fun i => 2 * Real.sin (((yv n b k i : ℚ) : ℝ) * Real.pi)
  have hSa : ∀ i, 2 * Real.sin ((((a i * k' : ℕ)) : ℝ) * Real.pi / n) = (-1 : ℝ) ^ fa i * pa i := by
    intro i
    rw [hcast, two_sin_sign hn]
    have h' := yv_congr (a := a) hk'd hn i
    unfold yv at h'
    rw [h']
    rfl
  have hSb : ∀ i, 2 * Real.sin ((((b i * k' : ℕ)) : ℝ) * Real.pi / n) = (-1 : ℝ) ^ fb i * pb i := by
    intro i
    rw [hcast, two_sin_sign hn]
    have h' := yv_congr (a := b) hk'd hn i
    unfold yv at h'
    rw [h']
    rfl
  have hpa : ∀ i, 0 < pa i := fun i => sin_fract_pos (yv_ne hsa ha1 hk i)
  have hpb : ∀ i, 0 < pb i := fun i => sin_fract_pos (yv_ne hsb hb1 hk i)
  unfold Ψ at hΨ
  simp only [hSa, hSb] at hΨ
  -- the product of all six is positive
  set Y := ∑ j, (c j : ℝ) * ((-1 : ℝ) ^ fa j * pa j)
  set sgn : ℝ := (-1 : ℝ) ^ (fa 0 + fa 1 + fa 2 + fb 0 + fb 1 + fb 2) with hsgn_def
  have hsgn : sgn * (pa 0 * pa 1 * pa 2 * pb 0 * pb 1 * pb 2) * N
      = (Y * ((-1 : ℝ) ^ fb 1 * pb 1) * ((-1 : ℝ) ^ fb 2 * pb 2)) ^ 2 := by
    have hz : ∀ x y : ℤ, (-1 : ℝ) ^ (x + y) = (-1 : ℝ) ^ x * (-1 : ℝ) ^ y :=
      fun x y => zpow_add₀ (by norm_num) x y
    rw [hsgn_def]
    simp only [hz]
    linear_combination ((-1 : ℝ) ^ fb 1 * pb 1 * ((-1 : ℝ) ^ fb 2 * pb 2)) * hΨ
  have hP : 0 < pa 0 * pa 1 * pa 2 * pb 0 * pb 1 * pb 2 * N := by
    have : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    have := hpa 0; have := hpa 1; have := hpa 2; have := hpb 0; have := hpb 1; have := hpb 2
    positivity
  have hsgn_nn : 0 ≤ sgn := by
    by_contra hneg; push Not at hneg
    have : sgn * (pa 0 * pa 1 * pa 2 * pb 0 * pb 1 * pb 2 * N) < 0 := mul_neg_of_neg_of_pos hneg hP
    nlinarith [sq_nonneg (Y * ((-1 : ℝ) ^ fb 1 * pb 1) * ((-1 : ℝ) ^ fb 2 * pb 2))]
  -- the floor sums
  have hFa := floor_sum hsa hn (k' : ℤ)
  have hFb := floor_sum hsb hn (k' : ℤ)
  have hTa : sT n a (k' : ℤ) = sT n a k := by
    unfold sT; exact Finset.sum_congr rfl (fun i _ => yv_congr hk'd hn i)
  have hTb : sT n b (k' : ℤ) = sT n b k := by
    unfold sT; exact Finset.sum_congr rfl (fun i _ => yv_congr hk'd hn i)
  rw [hTa] at hFa; rw [hTb] at hFb
  rw [Fin.sum_univ_three] at hFa hFb
  rcases sT_12 hsa ha1 hk with h1 | h1 <;> rcases sT_12 hsb hb1 hk with h2 | h2
  · rw [h1, h2]
  · exfalso
    rw [h1] at hFa; rw [h2] at hFb
    have hA : fa 0 + fa 1 + fa 2 = (k' : ℤ) - 1 := by
      have t : ((fa 0 + fa 1 + fa 2 : ℤ) : ℚ) = ((k' : ℤ) : ℚ) - 1 := hFa
      apply Int.cast_injective (α := ℚ); rw [t]; push_cast; ring
    have hB : fb 0 + fb 1 + fb 2 = (k' : ℤ) - 2 := by
      have t : ((fb 0 + fb 1 + fb 2 : ℤ) : ℚ) = ((k' : ℤ) : ℚ) - 2 := hFb
      apply Int.cast_injective (α := ℚ); rw [t]; push_cast; ring
    have hodd : Odd (fa 0 + fa 1 + fa 2 + fb 0 + fb 1 + fb 2) :=
      ⟨(k' : ℤ) - 2, by linarith⟩
    have : sgn = -1 := hodd.neg_one_zpow
    linarith
  · exfalso
    rw [h1] at hFa; rw [h2] at hFb
    have hA : fa 0 + fa 1 + fa 2 = (k' : ℤ) - 2 := by
      have t : ((fa 0 + fa 1 + fa 2 : ℤ) : ℚ) = ((k' : ℤ) : ℚ) - 2 := hFa
      apply Int.cast_injective (α := ℚ); rw [t]; push_cast; ring
    have hB : fb 0 + fb 1 + fb 2 = (k' : ℤ) - 1 := by
      have t : ((fb 0 + fb 1 + fb 2 : ℤ) : ℚ) = ((k' : ℤ) : ℚ) - 1 := hFb
      apply Int.cast_injective (α := ℚ); rw [t]; push_cast; ring
    have hodd : Odd (fa 0 + fa 1 + fa 2 + fb 0 + fb 1 + fb 2) :=
      ⟨(k' : ℤ) - 2, by linarith⟩
    have : sgn = -1 := hodd.neg_one_zpow
    linarith
  · rw [h1, h2]

/-! ## §7 Lemma K, K1 half, on a real dissection -/

/-- **Lemma K (K1), on a real `CongruentDissection`.**  Model angles `a_iπ/n`; `f` any corner data
with target angle `j` equal to `(f_j · a)π/n` (e.g. the corner figures).  Then for every integer `k`
coprime to `n`, `K1 n a f k`, i.e. `s_T(k) = s_ABC(k)`.  No conjugate dissection is built. -/
theorem lemmaK_K1 {N : ℕ} (D : CongruentDissection N) (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ i, D.model.angleAt i = a i * Real.pi / n) (f : Fin 3 → Fin 3 → ℕ)
    (hf : ∀ j, D.target.angleAt j = (uu a f j : ℕ) * Real.pi / n)
    {k : ℤ} (hk : Int.gcd k n = 1) : K1 n a f k := by
  obtain ⟨c, hc⟩ := star D
  have hN : N ≠ 0 := D.toDissection.pos.ne'
  have hA := fun i => nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)
  have hB := fun j => nat_bounds hn (hf j) (angle_pos _ j) (angle_lt_pi _ j)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have sum_of : ∀ (T : Tri) (b : Fin 3 → ℕ), (∀ i, T.angleAt i = b i * Real.pi / n) →
      ∑ i, b i = n := by
    intro T b hb
    have hs := T.angleAt_sum
    rw [hb 0, hb 1, hb 2] at hs
    have hnn : (n : ℝ) * (Real.pi / n) = Real.pi := by field_simp
    have key : (((b 0 + b 1 + b 2 : ℕ) : ℝ) - n) * (Real.pi / n) = 0 := by
      push_cast; linear_combination hs - hnn
    have hpn : Real.pi / n ≠ 0 := div_ne_zero Real.pi_ne_zero hn'
    have := sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right hpn)
    rw [Fin.sum_univ_three]; exact_mod_cast this
  have hsa := sum_of _ a ha
  have hsb := sum_of _ (uu a f) hf
  simp only [ha, hf] at hc
  exact sT_eq_of_star hN hn c (uu a f) (fun i => (hA i).1) hsa (fun j => (hB j).1) hsb hc hk

end Erdos634.Geometry.CaseA.LemmaK1

#print axioms Erdos634.Geometry.CaseA.LemmaK1.exists_sigma
#print axioms Erdos634.Geometry.CaseA.LemmaK1.conj_star
#print axioms Erdos634.Geometry.CaseA.LemmaK1.sT_eq_of_star
#print axioms Erdos634.Geometry.CaseA.LemmaK1.lemmaK_K1
