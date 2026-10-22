-- Draft/CaseALemmaHExc.lean — CASE A, node A9 (Lemma H): exceptional angles and a generic witness.
--   * `hcore_compl`: HCore θ ⇒ HCore (π/2 − θ) (sin/cos swap), pairing the eleven angles.
--   * `core_pi_div_six`, `core_pi_div_three`: HCore at π/6, π/3 (square classes {2, 6}).
--   * `core_two_pi_div_eleven`: HCore at 2π/11 through the GENERIC route (primitive 11th root,
--     φ(11) = 10) — a witness that `GenericIndep`'s hypothesis is satisfiable at a real angle.
-- Formalization debt; NOT /goal progress.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).  H59: no (e, f) evaluated.
import Erdos634.Draft.CaseALemmaHDegree

namespace Erdos634.Geometry.CaseA.LemmaH

open Real

theorem hcore_compl {θ : ℝ} (h : HCore θ) : HCore (Real.pi / 2 - θ) := by
  intro r x y p hp hp5 hX
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub] at hX
  exact h r y x p hp hp5 (by linear_combination hX)

/-- `m² = 2p` has no solution with `p` prime ≠ 2. -/
theorem sq_ne_two_prime {m p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : m ^ 2 ≠ 2 * p := by
  intro h
  rcases Nat.even_or_odd m with ⟨t, ht⟩ | ⟨t, ht⟩
  · subst ht
    exact two_sq_ne_prime (r := t) hp hp2 (by nlinarith)
  · subst ht
    rw [show (2 * t + 1) ^ 2 = 2 * (2 * t ^ 2 + 2 * t) + 1 by ring] at h; omega

theorem core_pi_div_six : HCore (Real.pi / 6) := by
  intro r x y p hp hp5 hX
  have hp2 : p ≠ 2 := by omega
  rw [Real.sin_pi_div_six, Real.cos_pi_div_six] at hX
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  set a : ℝ := r + x / 2
  set b : ℝ := y / 2
  have hkey : (2 * a ^ 2 + 6 * b ^ 2 - p) + 4 * a * b * Real.sqrt 3 = 0 := by
    linear_combination hX - (2 * b ^ 2) * hs
  have hirr : Irrational (Real.sqrt 3) := Nat.prime_three.irrational_sqrt
  have hab : a * b = 0 := by
    by_contra hne
    apply hirr
    have hne' : (4 * a * b) ≠ 0 := by intro h0; apply hne; linarith
    refine ⟨(p - 2 * ((r : ℚ) + x / 2) ^ 2 - 6 * ((y : ℚ) / 2) ^ 2) / (4 * ((r : ℚ) + x / 2) * (y / 2)),
      ?_⟩
    push_cast
    rw [div_eq_iff hne']
    linear_combination -hkey
  rcases mul_eq_zero.mp hab with h | h
  · -- r = x = 0, 6b² = p, i.e. 3y² = 2p
    have hr : (r : ℝ) = 0 := by
      have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      have : (0 : ℝ) ≤ x := Nat.cast_nonneg x
      simp only [a] at h; linarith
    have hx : (x : ℝ) = 0 := by simp only [a] at h; linarith
    have h3 : ((3 * y ^ 2 : ℕ) : ℝ) = ((2 * p : ℕ) : ℝ) := by
      push_cast
      have : (2 : ℝ) * a ^ 2 + 6 * b ^ 2 - p + 4 * a * b * Real.sqrt 3 = 0 := hkey
      rw [h] at this; simp only [b] at this; linarith
    have h3' : 3 * y ^ 2 = 2 * p := by exact_mod_cast h3
    have hd : 3 ∣ 2 * p := ⟨y ^ 2, h3'.symm⟩
    rcases (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num : Nat.Coprime 3 2) hd) with ⟨t, ht⟩
    rcases hp.eq_one_or_self_of_dvd 3 ⟨t, ht⟩ with h1 | h1 <;> omega
  · -- y = 0, 2a² = p, i.e. (2r + x)² = 2p
    have h2 : (((2 * r + x) ^ 2 : ℕ) : ℝ) = ((2 * p : ℕ) : ℝ) := by
      push_cast
      have : (2 : ℝ) * a ^ 2 + 6 * b ^ 2 - p + 4 * a * b * Real.sqrt 3 = 0 := hkey
      rw [h] at this; simp only [a] at this; linarith
    exact sq_ne_two_prime hp hp2 (by exact_mod_cast h2)

theorem core_pi_div_three : HCore (Real.pi / 3) := by
  have := hcore_compl core_pi_div_six
  rwa [show Real.pi / 2 - Real.pi / 6 = Real.pi / 3 by ring] at this

theorem core_pi_div_four' : HCore (Real.pi / 4) := core_pi_div_four

/-- **Generic-route witness**: HCore at θ = 2π/11 (e^{iθ} primitive 11th root, φ(11) = 10). -/
theorem core_two_pi_div_eleven : HCore (2 * Real.pi / 11) := by
  refine hcore_of_primitive (M := 11) 1 one_ne_zero (by norm_num) ?_ ?_
  · have h := Complex.isPrimitiveRoot_exp 11 (by norm_num)
    convert h using 1
    push_cast
    ring_nf
  · rw [Nat.totient_prime (by norm_num)]

theorem genericIndep_two_pi_div_eleven : GenericIndep (2 * Real.pi / 11) := by
  have h := Complex.isPrimitiveRoot_exp 11 (by norm_num)
  have he : Complex.exp (((2 * Real.pi / 11 : ℝ) : ℂ) * Complex.I)
      = Complex.exp (2 * Real.pi * Complex.I / ((11 : ℕ) : ℂ)) := by
    congr 1; push_cast; ring
  exact indep_of_scaled (1 : QI) one_ne_zero (by rw [he]; simp)
    (indep_of_totient h (by norm_num) (by rw [Nat.totient_prime (by norm_num)]))

end Erdos634.Geometry.CaseA.LemmaH

#print axioms Erdos634.Geometry.CaseA.LemmaH.hcore_compl
#print axioms Erdos634.Geometry.CaseA.LemmaH.core_pi_div_six
#print axioms Erdos634.Geometry.CaseA.LemmaH.core_pi_div_three
#print axioms Erdos634.Geometry.CaseA.LemmaH.core_two_pi_div_eleven
#print axioms Erdos634.Geometry.CaseA.LemmaH.genericIndep_two_pi_div_eleven
