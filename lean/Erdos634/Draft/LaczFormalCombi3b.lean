-- Draft/LaczFormalCombi3b.lean -- the Niven-type degree fact behind Laczkovich, DCG 48 (2012), Lemma 3.8, cases 3/5, 4/5, 4/7:
-- `sin theta` is not a rational function of `cos theta` for theta = 2 pi m/N when phi(4n) > phi(N) (n odd, n | N).
-- Proof: if it were, `i` lies in `Q(omega)`, `omega = e^{i theta}`; then `i * omega^(N/n)` is a primitive 4n-th root of unity in
-- `Q(omega)`, so phi(4n) <= [Q(omega):Q] = phi(N).  (The printed proof cites Niven, Irrational Numbers, Thm 3.9.)
-- NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Comput. Geom. 48 (2012), Lemma 3.8; Combinatorica 10 (1990)), Beeson, Beeson-Zhang.
import Mathlib
import Erdos634.Draft.LaczFormalCombi3a

open scoped Classical
open Polynomial IntermediateField

namespace Erdos634.Laczkovich.Combi3

theorem sin_not_ratfn (m N n : ℕ) (hN : 0 < N) (hcop : Nat.Coprime m N) (hn : 0 < n) (hnodd : Odd n) (hnN : n ∣ N)
    (hφ : ¬ ((4 * n).totient ≤ N.totient)) (hsin : Real.sin (2 * m * Real.pi / N) ≠ 0) :
    ¬ ∃ r q : ℚ[X], aeval (Real.cos (2 * m * Real.pi / N)) q ≠ 0 ∧
      Real.sin (2 * m * Real.pi / N) * aeval (Real.cos (2 * m * Real.pi / N)) q = aeval (Real.cos (2 * m * Real.pi / N)) r := by
  rintro ⟨r, q, hq, hrq⟩
  set θ : ℝ := 2 * m * Real.pi / N with hθ
  set ω : ℂ := Complex.exp ((θ : ℂ) * Complex.I) with hωdef
  have hωprim : IsPrimitiveRoot ω N := by
    have := Complex.isPrimitiveRoot_exp_of_coprime m N hN.ne' hcop
    have e : ω = Complex.exp (2 * Real.pi * Complex.I * (m / N)) := by
      rw [hωdef, hθ]; congr 1; push_cast; ring
    rw [e]; exact this
  have hωint : IsIntegral ℚ ω := (hωprim.isIntegral hN).tower_top
  set L : IntermediateField ℚ ℂ := ℚ⟮ω⟯ with hL
  haveI : FiniteDimensional ℚ L := adjoin.finiteDimensional hωint
  have hrank : Module.finrank ℚ L = N.totient := by
    rw [hL, adjoin.finrank hωint, ← Polynomial.cyclotomic_eq_minpoly_rat hωprim hN, Polynomial.natDegree_cyclotomic]
  have hωL : ω ∈ L := mem_adjoin_simple_self ℚ ω
  have hee : ω * Complex.exp (-(θ : ℂ) * Complex.I) = 1 := by
    rw [hωdef, ← Complex.exp_add]; ring_nf; simp
  have hinv : Complex.exp (-(θ : ℂ) * Complex.I) = ω⁻¹ := eq_inv_of_mul_eq_one_right hee
  set cC : ℂ := ((Real.cos θ : ℝ) : ℂ) with hcC
  set sC : ℂ := ((Real.sin θ : ℝ) : ℂ) with hsC
  have hcos : cC = (ω + ω⁻¹) / 2 := by
    rw [hcC, Complex.ofReal_cos, Complex.cos, hωdef, ← hinv]
  have hcL : cC ∈ L := by
    rw [hcos]; exact L.div_mem (L.add_mem hωL (L.inv_mem hωL)) (by simpa using L.natCast_mem 2)
  have hexp : ω = cC + sC * Complex.I := by
    rw [hωdef, Complex.exp_mul_I, hcC, hsC, Complex.ofReal_cos, Complex.ofReal_sin]
  -- complex form of the hypothesis
  have hqC : aeval cC q ≠ 0 := by
    intro h0; apply hq
    have : (algebraMap ℝ ℂ) (aeval (Real.cos θ) q) = 0 := by
      rw [← Polynomial.aeval_algebraMap_apply]; exact h0
    exact (map_eq_zero_iff _ (algebraMap ℝ ℂ).injective).mp this
  have hrqC : sC * aeval cC q = aeval cC r := by
    have := congrArg (algebraMap ℝ ℂ) hrq
    simpa [map_mul, ← Polynomial.aeval_algebraMap_apply, hsC, hcC] using this
  -- membership in L
  have hpolyL : ∀ p : ℚ[X], aeval cC p ∈ L := by
    intro p
    let c' : L := ⟨cC, hcL⟩
    have := Polynomial.aeval_algHom_apply L.val c' p
    have e : aeval cC p = L.val (aeval c' p) := this
    rw [e]; exact (aeval c' p).2
  have hsL : sC ∈ L := by
    have : sC = aeval cC r / aeval cC q := by
      rw [eq_div_iff hqC]; exact hrqC
    rw [this]; exact L.div_mem (hpolyL r) (hpolyL q)
  have hsC0 : sC ≠ 0 := by
    rw [hsC]; exact_mod_cast hsin
  have hIL : Complex.I ∈ L := by
    have : Complex.I = (ω - cC) / sC := by
      rw [eq_div_iff hsC0]; linear_combination -hexp
    rw [this]; exact L.div_mem (L.sub_mem hωL hcL) hsL
  -- the root of unity of order 4n
  have hI4 : IsPrimitiveRoot Complex.I 4 := by
    apply IsPrimitiveRoot.mk_of_lt Complex.I (by norm_num) (by simp [show (4 : ℕ) = 2 * 2 from rfl])
    intro l hl hl0
    interval_cases l <;> simp [pow_succ, Complex.ext_iff] <;> norm_num
  have hn' : n * (N / n) = N := Nat.mul_div_cancel' hnN
  have hNn : N / n ≠ 0 := by
    intro h0; rw [h0] at hn'; omega
  have hξ : IsPrimitiveRoot (ω ^ (N / n)) n := by
    have := hωprim.pow_of_dvd hNn (Nat.div_dvd_of_dvd hnN)
    rwa [Nat.div_div_self hnN hN.ne'] at this
  have hcop4 : Nat.Coprime 4 n := by
    have h2 : Nat.Coprime 2 n := Nat.coprime_two_left.mpr hnodd
    simpa using Nat.Coprime.pow_left 2 h2
  have hord : orderOf (Complex.I * ω ^ (N / n)) = 4 * n := by
    rw [(Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime, hI4.eq_orderOf.symm, hξ.eq_orderOf.symm]
    rw [← hI4.eq_orderOf, ← hξ.eq_orderOf]; exact hcop4
  have hzprim : IsPrimitiveRoot (Complex.I * ω ^ (N / n)) (4 * n) := by
    rw [← hord]; exact IsPrimitiveRoot.orderOf _
  have hzL : Complex.I * ω ^ (N / n) ∈ L := L.mul_mem hIL (L.pow_mem hωL (N / n))
  -- degree bound
  have hzint : IsIntegral ℚ (Complex.I * ω ^ (N / n)) := (hzprim.isIntegral (by omega)).tower_top
  set x : L := ⟨_, hzL⟩
  have hx : (minpoly ℚ x).natDegree ≤ Module.finrank ℚ L := minpoly.natDegree_le x
  have hmx : minpoly ℚ x = minpoly ℚ (Complex.I * ω ^ (N / n)) := by
    rw [← minpoly.algebraMap_eq (algebraMap L ℂ).injective x]; rfl
  have hdeg : (minpoly ℚ (Complex.I * ω ^ (N / n))).natDegree = (4 * n).totient := by
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hzprim (by omega), Polynomial.natDegree_cyclotomic]
  rw [hmx, hdeg, hrank] at hx
  exact hφ hx

end Erdos634.Laczkovich.Combi3
