import Mathlib
import Erdos634.Draft.CaseALemmaHGlue

/-!
# Beeson, "Tilings of an isosceles triangle" (arXiv 1206.1974 v7), Lemma 4.3 (first part)

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.1974 v7, Lemma 4.3; the printed proof cites Niven-type Theorem 3.9 of [12]),
Beeson-Rosu, Beeson-Zhang, Laczkovich.  Formalization debt, not progress on the /goal outcomes.  Pure algebra, no tiling, no H1.

`lemma43_totient`: if `cos(2 m pi / n)` has degree `<= 2` over `Q` (`gcd(m,n)=1`, `n > 0`), then `phi(n) <= 4`; hence
`lemma43_list`: `n` is one of `1,2,3,4,5,6,8,10,12`.  (Proof: `omega = e^{i theta}` is a root of `X^2 - 2 cos(theta) X + 1`
over `Q(cos theta)`, tower law, `Q(omega)` has degree `phi(n)` (cyclotomic irreducibility).)

PRINT ERROR (found here): the printed list `5, 6, 8, 10, 12` omits `n = 1, 2, 3, 4`, where `cos` is rational (degree 1, which the
printed hypothesis "degree 1 or 2" allows): `cos 0 = 1`, `cos pi = -1`, `cos(2 pi / 3) = -1/2`, `cos(pi/2) = 0`
(`print_error_n4`).  The printed second part (both `cos` and `sin` of degree `<= 2` gives `n in {6, 8, 12}`) is NOT formalized here
(blocker: needs the sin-side degree count of [12] Thm 3.9; also `n = 4` has `cos = 0`, `sin = 1`, rational).
-/

namespace Erdos634.Draft.BeesonRow4A

open Polynomial IntermediateField

set_option synthInstance.maxHeartbeats 400000 in
theorem tot_le_of_quad {K : IntermediateField ℚ ℂ} [FiniteDimensional ℚ K] {ω : ℂ} {n : ℕ}
    (hω : IsPrimitiveRoot ω n) (hn : 0 < n) (hq : (minpoly K ω).natDegree ≤ 2) :
    n.totient ≤ Module.finrank ℚ K * 2 := by
  have hωZ : IsIntegral ℚ ω := (hω.isIntegral hn).tower_top
  have hωK : IsIntegral K ω := hωZ.tower_top
  set E : IntermediateField K ℂ := K⟮ω⟯
  haveI : FiniteDimensional K E := adjoin.finiteDimensional hωK
  haveI : FiniteDimensional ℚ E := Module.Finite.trans K E
  have htower := Module.finrank_mul_finrank ℚ K E
  have hE : Module.finrank K E = (minpoly K ω).natDegree := adjoin.finrank hωK
  set x : E := ⟨ω, mem_adjoin_simple_self K ω⟩
  have hx : (minpoly ℚ x).natDegree ≤ Module.finrank ℚ E := minpoly.natDegree_le x
  have hmx : minpoly ℚ x = minpoly ℚ ω := by
    rw [← minpoly.algebraMap_eq (algebraMap E ℂ).injective x]; rfl
  have hdeg : (minpoly ℚ ω).natDegree = n.totient := by
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hω hn, Polynomial.natDegree_cyclotomic]
  rw [hmx, hdeg] at hx
  rw [← htower, hE] at hx
  calc n.totient ≤ Module.finrank ℚ K * (minpoly K ω).natDegree := hx
    _ ≤ Module.finrank ℚ K * 2 := Nat.mul_le_mul_left _ hq

theorem lemma43_totient (m n : ℕ) (hn : 0 < n) (hcop : Nat.Coprime m n)
    (hint : IsIntegral ℚ (Real.cos (2 * m * Real.pi / n)))
    (hdeg : (minpoly ℚ (Real.cos (2 * m * Real.pi / n))).natDegree ≤ 2) : n.totient ≤ 4 := by
  set θ : ℝ := 2 * m * Real.pi / n with hθ
  set c : ℂ := ((Real.cos θ : ℝ) : ℂ) with hc
  set ω : ℂ := Complex.exp ((θ : ℂ) * Complex.I) with hωdef
  have hωprim : IsPrimitiveRoot ω n := by
    have := Complex.isPrimitiveRoot_exp_of_coprime m n hn.ne' hcop
    have e : ω = Complex.exp (2 * Real.pi * Complex.I * (m / n)) := by
      rw [hωdef, hθ]; congr 1; push_cast; ring
    rw [e]; exact this
  have hcint : IsIntegral ℚ c := by
    have := IsIntegral.algebraMap (B := ℂ) hint
    simpa [hc] using this
  have hmin : minpoly ℚ c = minpoly ℚ (Real.cos θ) := by
    have := minpoly.algebraMap_eq (A := ℚ) (B := ℝ) (B' := ℂ) (fun x y h => Complex.ofReal_injective h) (Real.cos θ)
    rw [hc]; exact this
  set K : IntermediateField ℚ ℂ := ℚ⟮c⟯
  haveI : FiniteDimensional ℚ K := adjoin.finiteDimensional hcint
  have hK : Module.finrank ℚ K ≤ 2 := by
    rw [adjoin.finrank hcint, hmin]; exact hdeg
  have hωQ : IsIntegral ℚ ω := (hωprim.isIntegral hn).tower_top
  have hωK : IsIntegral K ω := hωQ.tower_top
  set c' : K := ⟨c, mem_adjoin_simple_self ℚ c⟩
  have hee : ω * Complex.exp (-(θ : ℂ) * Complex.I) = 1 := by
    rw [hωdef, ← Complex.exp_add]; ring_nf; simp
  have hcos : c = (ω + Complex.exp (-(θ : ℂ) * Complex.I)) / 2 := by
    rw [hc, Complex.ofReal_cos, Complex.cos, hωdef]
  set p : K[X] := X ^ 2 - C (2 * c') * X + 1 with hp
  have hpm : p.Monic := by rw [hp]; monicity!
  have hpd : p.natDegree ≤ 2 := by rw [hp]; compute_degree
  have hpa : aeval ω p = 0 := by
    have hc'' : algebraMap K ℂ c' = c := rfl
    simp only [hp, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, map_one, map_ofNat, hc'']
    set e' := Complex.exp (-(θ : ℂ) * Complex.I)
    rw [hcos]
    linear_combination (-1 : ℂ) * hee
  have hq : (minpoly K ω).natDegree ≤ 2 :=
    (natDegree_le_natDegree (minpoly.degree_le_of_ne_zero K ω hpm.ne_zero hpa)).trans hpd
  have := tot_le_of_quad hωprim hn hq
  omega

theorem small_list : ∀ n ≤ 30, 0 < n → n.totient ≤ 4 → n ∈ [1, 2, 3, 4, 5, 6, 8, 10, 12] := by
  decide +kernel

theorem lemma43_list (m n : ℕ) (hn : 0 < n) (hcop : Nat.Coprime m n)
    (hint : IsIntegral ℚ (Real.cos (2 * m * Real.pi / n)))
    (hdeg : (minpoly ℚ (Real.cos (2 * m * Real.pi / n))).natDegree ≤ 2) :
    n ∈ [1, 2, 3, 4, 5, 6, 8, 10, 12] := by
  have h4 := lemma43_totient m n hn hcop hint hdeg
  have h30 := Erdos634.Geometry.CaseA.LemmaH.le_30 hn (by omega)
  exact small_list n h30 hn h4

/-- Print error: `n = 4` (`m = 1`) satisfies the hypotheses (cos = 0, degree 1) yet is outside the printed list. -/
theorem print_error_n4 : Real.cos (2 * (1 : ℕ) * Real.pi / (4 : ℕ)) = 0 ∧ (4 : ℕ) ∉ [5, 6, 8, 10, 12] := by
  refine ⟨?_, by decide⟩
  have : (2 * ((1 : ℕ) : ℝ) * Real.pi / ((4 : ℕ) : ℝ)) = Real.pi / 2 := by push_cast; ring
  rw [this]; exact Real.cos_pi_div_two

#print axioms lemma43_totient
#print axioms lemma43_list
#print axioms print_error_n4

end Erdos634.Draft.BeesonRow4A
