-- Draft/CaseALemmaHGlue.lean — CASE A, node A9 (Lemma H): the case split of step 5 / step 6.
-- For θ ∈ ℚπ, 0 < θ < π/2, with n the order of e^{iθ}:
--   * totient bound: φ(n) ≤ 9 ⇒ n ≤ 30 (via n ∣ 5040, prime powers);
--   * generic branch: u·e^{iθ} is a primitive lcm(4,n)-th root (u = 1 or i) with φ ≥ 10
--     unless n ∈ {5, 6, 8, 10, 12, 16, 20, 24}  ⇒ HCore θ by `hcore_of_primitive`;
--   * exceptional branch: θ is one of the eleven angles; HCore there from π/4, π/6, π/3 (proved)
--     and π/8, π/12, π/10, π/5 (HYPOTHESES `hexc`, with their complements via `hcore_compl`).
-- Formalization debt; NOT /goal progress.  Imported into All.lean (All.lean:633).  H59: no (e, f) evaluated.
import Erdos634.Draft.CaseALemmaHExc

namespace Erdos634.Geometry.CaseA.LemmaH

open Real

/-! ## Totient bound -/

theorem pp_dvd : ∀ p v : ℕ, p.Prime → 0 < v → (p ^ v).totient ≤ 9 → p ^ v ∣ 5040 := by
  intro p v hp hv h
  rw [Nat.totient_prime_pow hp hv] at h
  have hp2 := hp.two_le
  have hp1 : p - 1 ≤ 9 := by
    have : 1 ≤ p ^ (v - 1) := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have hpv : p ^ (v - 1) ≤ 9 := by
    have : 1 ≤ p - 1 := by omega
    nlinarith
  have hv4 : v - 1 ≤ 3 := by
    by_contra hc
    have : 2 ^ (v - 1) ≤ p ^ (v - 1) := Nat.pow_le_pow_left hp2 _
    have : 2 ^ 4 ≤ 2 ^ (v - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hp10 : p ≤ 10 := by omega
  obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hv4 hpv h
  interval_cases p <;> norm_num at hp <;> interval_cases w <;> revert hpv h <;> norm_num

theorem dvd_5040 {n : ℕ} (hn : 0 < n) (h : n.totient ≤ 9) : n ∣ 5040 := by
  refine (Nat.factorization_prime_le_iff_dvd hn.ne' (by norm_num)).mp fun p hp => ?_
  set v := n.factorization p
  rcases Nat.eq_zero_or_pos v with hv | hv
  · rw [hv]; exact Nat.zero_le _
  have hd : p ^ v ∣ n := Nat.ordProj_dvd n p
  have ht : (p ^ v).totient ≤ 9 :=
    le_trans (Nat.le_of_dvd (Nat.totient_pos.mpr hn) (Nat.totient_dvd_of_dvd hd)) h
  have h5 := pp_dvd p v hp hv ht
  have := (Nat.factorization_le_iff_dvd (pow_ne_zero _ hp.ne_zero) (by norm_num)).mpr h5 p
  rwa [Nat.Prime.factorization_pow hp, Finsupp.single_eq_same] at this

theorem totient_small : ∀ d ∈ Nat.divisors 5040, d.totient ≤ 9 → d ≤ 30 := by decide +kernel

theorem le_30 {n : ℕ} (hn : 0 < n) (h : n.totient ≤ 9) : n ≤ 30 :=
  totient_small n (Nat.mem_divisors.mpr ⟨dvd_5040 hn h, by norm_num⟩) h

/-! ## Orders -/

theorem orderOf_I : orderOf Complex.I = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := orderOf_eq_prime_pow (x := Complex.I) (p := 2) (n := 1) (by norm_num) (by norm_num)
  simpa using this

theorem orderOf_negI : orderOf (-Complex.I) = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := orderOf_eq_prime_pow (x := -Complex.I) (p := 2) (n := 1) (by norm_num) (by norm_num)
  simpa using this

/-- If `ζ` has order `2m`, `m` odd, then `-ζ` has order `m`. -/
theorem orderOf_neg_of_two_mul {ζ : ℂ} {m : ℕ} (hm : 0 < m) (hodd : Odd m)
    (hζ : orderOf ζ = 2 * m) : orderOf (-ζ) = m := by
  have hP : IsPrimitiveRoot ζ (2 * m) := hζ ▸ IsPrimitiveRoot.orderOf ζ
  have hm1 : ζ ^ m = -1 := (hP.pow (by omega) (by ring)).eq_neg_one_of_two_right
  rw [orderOf_eq_iff hm]
  refine ⟨?_, fun k hk hk0 hk1 => ?_⟩
  · rw [neg_pow, hm1, hodd.neg_one_pow]; ring
  · have h2 : ζ ^ (2 * k) = 1 := by
      have e : (-ζ) ^ (2 * k) = ζ ^ (2 * k) := Even.neg_pow ⟨k, by ring⟩ ζ
      rw [← e, pow_mul', hk1, one_pow]
    obtain ⟨c, hc⟩ := (hP.pow_eq_one_iff_dvd (2 * k)).mp h2
    have : m ∣ k := ⟨c, by rw [mul_assoc] at hc; omega⟩
    exact absurd (Nat.le_of_dvd hk0 this) (by omega)

/-! ## θ ∈ ℚπ: e^{iθ} is a root of unity of order n, θ·n = 2πj, 0 < 4j < n -/

theorem theta_form {θ : ℝ} (hq : ∃ q : ℚ, θ = q * Real.pi) (h0 : 0 < θ) (h2 : θ < Real.pi / 2) :
    0 < orderOf (Complex.exp (θ * Complex.I)) ∧ ∃ j : ℕ, 0 < j ∧
      4 * j < orderOf (Complex.exp (θ * Complex.I)) ∧
      θ * orderOf (Complex.exp (θ * Complex.I)) = 2 * Real.pi * j := by
  obtain ⟨q, rfl⟩ := hq
  set ζ := Complex.exp (((q : ℝ) * Real.pi : ℝ) * Complex.I)
  have hq' : (q : ℂ) * q.den = q.num := by exact_mod_cast Rat.mul_den_eq_num q
  have hpow : ζ ^ (2 * q.den) = 1 := by
    rw [← Complex.exp_nat_mul]
    have : ((2 * q.den : ℕ) : ℂ) * ((((q : ℝ) * Real.pi : ℝ) : ℂ) * Complex.I)
        = (q.num : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast; linear_combination (2 * (Real.pi : ℂ) * Complex.I) * hq'
    rw [this]; exact Complex.exp_int_mul_two_pi_mul_I q.num
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.mpr ⟨2 * q.den, by positivity, hpow⟩
  have hn := hfin.orderOf_pos
  refine ⟨hn, ?_⟩
  set n := orderOf ζ
  have h1 : ζ ^ n = 1 := pow_orderOf_eq_one ζ
  rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff] at h1
  obtain ⟨j, hj⟩ := h1
  have hjr : (q : ℝ) * Real.pi * n = 2 * Real.pi * j := by
    have := congrArg Complex.im hj
    simp at this
    linarith
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hj0 : (0 : ℝ) < j := by
    have : 0 < (q : ℝ) * Real.pi * n := by positivity
    nlinarith [Real.pi_pos]
  have hj4 : (4 : ℝ) * j < n := by
    have : (q : ℝ) * Real.pi * n < Real.pi / 2 * n := by nlinarith
    nlinarith [Real.pi_pos]
  have hjz : (0 : ℤ) < j := by exact_mod_cast hj0
  have hjn : ((j.toNat : ℕ) : ℝ) = j := by exact_mod_cast Int.toNat_of_nonneg hjz.le
  refine ⟨j.toNat, by omega, ?_, ?_⟩
  · have h4 : ((4 * j.toNat : ℕ) : ℝ) < n := by push_cast; rw [hjn]; exact hj4
    exact_mod_cast h4
  · rw [hjn]; exact_mod_cast hjr

/-! ## The exceptional finisher -/

theorem exc_list : ∀ n ≤ 30, ((4 ∣ n ∧ n.totient ≤ 9) ∨ n.totient ≤ 4) →
    n ∈ [0, 1, 2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 24] := by decide +kernel

theorem hcore_of_eq {θ a : ℝ} (h : HCore a) (e : θ = a) : HCore θ := e ▸ h

/-- Every θ with `θ·n = 2πj`, `0 < 4j < n ≤ 30`, `n` in the exceptional class, is one of the
eleven angles; HCore there from the four open cores (`hexc`) and the proved ones. -/
theorem exc_finish (hexc : HCore (Real.pi / 8) ∧ HCore (Real.pi / 12) ∧ HCore (Real.pi / 10) ∧
      HCore (Real.pi / 5))
    {θ : ℝ} {n j : ℕ} (hn : n ≤ 30) (hj0 : 0 < j) (hj : 4 * j < n)
    (hθ : θ * n = 2 * Real.pi * j) (hP : (4 ∣ n ∧ n.totient ≤ 9) ∨ n.totient ≤ 4) : HCore θ := by
  obtain ⟨h8, h12, h10, h5⟩ := hexc
  have c38 := hcore_compl h8
  have c512 := hcore_compl h12
  have c25 := hcore_compl h10
  have c310 := hcore_compl h5
  have c4 := core_pi_div_four
  have c6 := core_pi_div_six
  have c3 := core_pi_div_three
  have hjn : j < n := by omega
  have hmem := exc_list n hn hP
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases j <;> push_cast at hθ <;> (try omega) <;>
    first
    | exact hcore_of_eq h8 (by linarith) | exact hcore_of_eq h12 (by linarith)
    | exact hcore_of_eq h10 (by linarith) | exact hcore_of_eq h5 (by linarith)
    | exact hcore_of_eq c38 (by linarith) | exact hcore_of_eq c512 (by linarith)
    | exact hcore_of_eq c25 (by linarith) | exact hcore_of_eq c310 (by linarith)
    | exact hcore_of_eq c4 (by linarith) | exact hcore_of_eq c6 (by linarith)
    | exact hcore_of_eq c3 (by linarith)

/-! ## Step 5 / step 6 split: HCore at every rational angle, given the four open cores -/

theorem iQ_ne : (⟨Complex.I, I_mem⟩ : QI) ≠ 0 := fun h => Complex.I_ne_zero (congrArg Subtype.val h)

theorem totient_four_mul {m : ℕ} (hm : Odd m) : (4 * m).totient = 2 * m.totient := by
  rw [Nat.totient_mul (by
    show Nat.Coprime (2 ^ 2) m
    exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hm))]
  rfl

/-- **The case split** (steps 5–6): for θ ∈ ℚπ, 0 < θ < π/2, `HCore θ` — generic angles by the
cyclotomic degree bound, the eleven exceptional angles from the cores at π/4, π/6, π/3 (proved) and
the four cores in `hexc` (open). -/
theorem hcore_rational (hexc : HCore (Real.pi / 8) ∧ HCore (Real.pi / 12) ∧ HCore (Real.pi / 10) ∧
      HCore (Real.pi / 5))
    {θ : ℝ} (hq : ∃ q : ℚ, θ = q * Real.pi) (h0 : 0 < θ) (h2 : θ < Real.pi / 2) : HCore θ := by
  obtain ⟨hn, j, hj0, hj4, hθ⟩ := theta_form hq h0 h2
  set ζ := Complex.exp (θ * Complex.I)
  set n := orderOf ζ with hn_def
  have hP : IsPrimitiveRoot ζ n := IsPrimitiveRoot.orderOf ζ
  by_cases hdiv : 4 ∣ n
  · by_cases h10 : 10 ≤ n.totient
    · exact hcore_of_primitive 1 one_ne_zero hn (by simpa using hP) h10
    · exact exc_finish hexc (le_30 hn (by omega)) hj0 hj4 hθ (Or.inl ⟨hdiv, by omega⟩)
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
      exact hcore_of_primitive ⟨Complex.I, I_mem⟩ iQ_ne (by omega) hpr h10
    · rw [totient_four_mul hmodd] at h10
      exact exc_finish hexc (le_30 hn (by omega)) hj0 hj4 hθ (Or.inr (by omega))
  · have hω : orderOf (Complex.I * ζ) = 4 * n := by
      rw [(Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime, orderOf_I]
      rw [orderOf_I]
      show Nat.Coprime (2 ^ 2) n
      exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd)
    by_cases h10 : 10 ≤ (4 * n).totient
    · have hpr := IsPrimitiveRoot.orderOf (Complex.I * ζ)
      rw [hω] at hpr
      exact hcore_of_primitive ⟨Complex.I, I_mem⟩ iQ_ne (by omega) hpr h10
    · rw [totient_four_mul hodd] at h10
      exact exc_finish hexc (le_30 hn (by omega)) hj0 hj4 hθ (Or.inr (by omega))

/-- **Lemma H (row 1, LEMMA_H.md §1), as written, conditional ONLY on the four exceptional cores
at π/8, π/12, π/10, π/5.**  Isosceles target with base angle θ ∈ ℚπ at two distinct vertices,
0 < θ < π/2, tiled by N congruent right tiles with an acute angle θ (any labelling, reflections,
no edge-to-edge) ⇒ N is not a prime ≥ 5. -/
theorem lemmaH_rational (hexc : HCore (Real.pi / 8) ∧ HCore (Real.pi / 12) ∧
      HCore (Real.pi / 10) ∧ HCore (Real.pi / 5))
    {N : ℕ} (D : CongruentDissection N) {θ : ℝ} (hq : ∃ q : ℚ, θ = q * Real.pi) (hθ0 : 0 < θ)
    (hθ2 : θ < Real.pi / 2)
    {p q : Fin 3} (hpq : p ≠ q) (hmp : D.model.angleAt p = θ) (hmq : D.model.angleAt q = Real.pi / 2)
    {i j : Fin 3} (hij : i ≠ j) (hi : D.target.angleAt i = θ) (hj : D.target.angleAt j = θ) :
    ¬ (N.Prime ∧ 5 ≤ N) :=
  lemmaH_conditional D hθ0 hθ2 (Or.inr (hcore_rational hexc hq hθ0 hθ2)) hpq hmp hmq hij hi hj

end Erdos634.Geometry.CaseA.LemmaH

#print axioms Erdos634.Geometry.CaseA.LemmaH.le_30
#print axioms Erdos634.Geometry.CaseA.LemmaH.theta_form
#print axioms Erdos634.Geometry.CaseA.LemmaH.exc_finish
#print axioms Erdos634.Geometry.CaseA.LemmaH.hcore_rational
#print axioms Erdos634.Geometry.CaseA.LemmaH.lemmaH_rational
