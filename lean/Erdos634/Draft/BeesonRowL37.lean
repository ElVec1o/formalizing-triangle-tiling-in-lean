import Mathlib

/-!
# Beeson (arXiv 1206.2229 v4), Lemma 37 (converse: the tiling equation N + M^2 = 2K^2 is solvable)

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Lemma 37; the idea of the proof is attributed there to
N. Elkies and W. Jagy), Beeson-Zhang, Laczkovich.  Formalization debt, not progress on the /goal outcomes.
Pure arithmetic: no H1, no tiling.  Map row T-L45 (printed Lemma 37).

* `thue_two`: every prime p = +-1 (mod 8) has `p + a^2 = 2 b^2` (Thue's pigeonhole lemma, replacing the printed citation
  to Theorem 4.23 of [2] on the form x^2 - y^2 of discriminant 8).
* `sol_mul`: solutions multiply (norm form of Z[sqrt 2], times the unit 1+sqrt 2).
* `lemma37_exists`: `N = s^2 q`, all primes of `q` equal to 2 or +-1 mod 8 => `N + M^2 = 2 K^2` has an integer solution.
* `lemma37_pos`: if moreover N is neither a square nor twice a square, there is a solution with `0 < M < K`.

PRINT NOTES (honest).  (1) The printed Lemma 37 asserts a solution with `M < K` for EVERY such N.  False for `N = 1` and
`N = 2`: `1 + M^2 = 2K^2` and `2 + M^2 = 2K^2` force `M >= K` (`no_small_M_one`, `no_small_M_two`).  The printed proof itself
ends in the two exceptional cases (`M = K`: N square; `M' = 0`: N twice a square) and the printed Lemma 36 states the
restriction, so Lemma 37 as printed lacks "not a square or twice a square".  (2) Printed descent uses `(M',K') =
(4K-3M, 3K+2M)`; the solution is `(4K-3M, 3K-2M)` (e.g. N = 7, (M,K) = (5,4) gives (1,2); `3K+2M = 22` fails).
`lemma37_pos` is proved with the corrected unit.
-/

namespace Erdos634.BeesonRow

/-- `N + M^2 = 2K^2` solvable in integers. -/
def Sol (N : ℕ) : Prop := ∃ M K : ℤ, (N : ℤ) + M ^ 2 = 2 * K ^ 2

theorem sq_eq_two_mul_sq_zero (a b : ℤ) (h : a ^ 2 = 2 * b ^ 2) : b = 0 := by
  by_contra hb
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have h2 : (√2 : ℝ) = |(a : ℝ) / b| := by
    rw [← Real.sqrt_sq_eq_abs]
    congr 1
    field_simp
    exact_mod_cast h.symm
  exact irrational_sqrt_two ⟨|(a : ℚ) / b|, by push_cast; exact h2.symm⟩

theorem thue_two (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (h8 : p % 8 = 1 ∨ p % 8 = 7) :
    ∃ a b : ℤ, (p : ℤ) + a ^ 2 = 2 * b ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ : IsSquare (2 : ZMod p) := (ZMod.exists_sq_eq_two_iff hp2).mpr h8
  set r := Nat.sqrt p with hrdef
  have hr1 : r * r ≤ p := Nat.sqrt_le p
  have hr2 : p < (r + 1) * (r + 1) := Nat.lt_succ_sqrt p
  have hr3 : r * r < p := by
    refine lt_of_le_of_ne hr1 (fun h => ?_)
    rcases hp.eq_one_or_self_of_dvd r ⟨r, h.symm⟩ with h1 | h1
    · have : p = 1 := by rw [← h, h1]
      exact hp.one_lt.ne' this
    · rw [h1] at h; nlinarith [hp.two_le]
  let f : Fin (r + 1) × Fin (r + 1) → ZMod p := fun uv => ((uv.1 : ℕ) : ZMod p) - x * ((uv.2 : ℕ) : ZMod p)
  have hcard : Fintype.card (ZMod p) < Fintype.card (Fin (r + 1) × Fin (r + 1)) := by
    simp [ZMod.card]; exact hr2
  obtain ⟨⟨u1, v1⟩, ⟨u2, v2⟩, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  simp only [f] at heq
  set a : ℤ := (u1 : ℕ) - (u2 : ℕ) with ha
  set b : ℤ := (v1 : ℕ) - (v2 : ℕ) with hb
  have hab : (a : ZMod p) = x * (b : ZMod p) := by
    simp only [ha, hb]; push_cast; linear_combination heq
  have hdvd : (p : ℤ) ∣ a ^ 2 - 2 * b ^ 2 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hab, hx]; ring
  obtain ⟨t, ht⟩ := hdvd
  have hu1 := u1.isLt; have hu2 := u2.isLt; have hv1 := v1.isLt; have hv2 := v2.isLt
  have hra : a ^ 2 ≤ (r : ℤ) ^ 2 := by
    have : |a| ≤ r := by rw [abs_le]; constructor <;> simp only [ha] <;> omega
    nlinarith [sq_abs a, abs_nonneg a]
  have hrb : b ^ 2 ≤ (r : ℤ) ^ 2 := by
    have : |b| ≤ r := by rw [abs_le]; constructor <;> simp only [hb] <;> omega
    nlinarith [sq_abs b, abs_nonneg b]
  have hrp : (r : ℤ) ^ 2 < p := by exact_mod_cast (by nlinarith : r ^ 2 < p)
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have ht1 : t < 1 := by
    by_contra hc; push Not at hc
    nlinarith [mul_le_mul_of_nonneg_left hc hp0.le, sq_nonneg b]
  have ht2 : -2 < t := by
    by_contra hc; push Not at hc
    nlinarith [mul_le_mul_of_nonneg_left hc hp0.le, sq_nonneg a]
  have : t = 0 ∨ t = -1 := by omega
  rcases this with h0 | h1
  · exfalso
    rw [h0] at ht
    have hb0 : b = 0 := sq_eq_two_mul_sq_zero a b (by linarith)
    have ha0 : a = 0 := by rw [hb0] at ht; nlinarith
    apply hne
    have e1 : (u1 : ℕ) = u2 := by simp only [ha] at ha0; omega
    have e2 : (v1 : ℕ) = v2 := by simp only [hb] at hb0; omega
    exact Prod.ext (Fin.ext e1) (Fin.ext e2)
  · exact ⟨a, b, by rw [h1] at ht; linarith⟩

theorem sol_mul {N1 N2 : ℕ} (h1 : Sol N1) (h2 : Sol N2) : Sol (N1 * N2) := by
  obtain ⟨M1, K1, e1⟩ := h1
  obtain ⟨M2, K2, e2⟩ := h2
  refine ⟨(M1 * M2 + 2 * K1 * K2) + 2 * (M1 * K2 + K1 * M2), (M1 * M2 + 2 * K1 * K2) + (M1 * K2 + K1 * M2), ?_⟩
  push_cast
  have n1 : (N1 : ℤ) = 2 * K1 ^ 2 - M1 ^ 2 := by linarith
  have n2 : (N2 : ℤ) = 2 * K2 ^ 2 - M2 ^ 2 := by linarith
  rw [n1, n2]; ring

theorem sol_sq (s : ℕ) : Sol (s ^ 2) := ⟨s, s, by push_cast; ring⟩
theorem sol_two : Sol 2 := ⟨4, 3, by norm_num⟩
theorem sol_one : Sol 1 := ⟨1, 1, by norm_num⟩

theorem sol_prime (p : ℕ) (hp : p.Prime) (h : p = 2 ∨ p % 8 = 1 ∨ p % 8 = 7) : Sol p := by
  rcases h with rfl | h
  · exact sol_two
  · have hp2 : p ≠ 2 := by rintro rfl; omega
    obtain ⟨a, b, e⟩ := thue_two p hp hp2 h
    exact ⟨a, b, e⟩

theorem sol_of_primes : ∀ q : ℕ, 0 < q → (∀ p : ℕ, p.Prime → p ∣ q → p = 2 ∨ p % 8 = 1 ∨ p % 8 = 7) → Sol q := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hq hall
    by_cases h1 : q = 1
    · subst h1; exact sol_one
    · have hmp : (Nat.minFac q).Prime := Nat.minFac_prime h1
      obtain ⟨q', hq'⟩ := Nat.minFac_dvd q
      have hq'pos : 0 < q' := by
        rcases Nat.eq_zero_or_pos q' with h | h
        · rw [h] at hq'; omega
        · exact h
      have hlt : q' < q := by
        have := hmp.two_le
        conv_rhs => rw [hq']
        nlinarith
      have h' := ih q' hlt hq'pos (fun p hp hpd => hall p hp (hq' ▸ Dvd.dvd.mul_left hpd _))
      rw [hq']
      exact sol_mul (sol_prime _ hmp (hall _ hmp (Nat.minFac_dvd q))) h'

theorem lemma37_exists (N s q : ℕ) (hq : 0 < q) (hN : N = s ^ 2 * q)
    (hall : ∀ p : ℕ, p.Prime → p ∣ q → p = 2 ∨ p % 8 = 1 ∨ p % 8 = 7) : Sol N := by
  rw [hN]; exact sol_mul (sol_sq s) (sol_of_primes q hq hall)

theorem no_small_M_one : ¬ ∃ M K : ℕ, 0 < M ∧ M < K ∧ 1 + M ^ 2 = 2 * K ^ 2 := by
  rintro ⟨M, K, h0, h1, h⟩; nlinarith
theorem no_small_M_two : ¬ ∃ M K : ℕ, 0 < M ∧ M < K ∧ 2 + M ^ 2 = 2 * K ^ 2 := by
  rintro ⟨M, K, h0, h1, h⟩
  have : M ^ 2 < K ^ 2 := by nlinarith
  nlinarith

theorem lemma37_pos (N : ℕ) (hN : 0 < N) (hs : Sol N) (hsq : ¬ ∃ t : ℕ, N = t ^ 2)
    (h2sq : ¬ ∃ t : ℕ, N = 2 * t ^ 2) :
    ∃ M K : ℕ, 0 < M ∧ M < K ∧ N + M ^ 2 = 2 * K ^ 2 := by
  have hex : ∃ m : ℕ, 0 < m ∧ ∃ k : ℕ, N + m ^ 2 = 2 * k ^ 2 := by
    obtain ⟨M, K, e⟩ := hs
    refine ⟨M.natAbs, ?_, K.natAbs, ?_⟩
    · rcases Nat.eq_zero_or_pos M.natAbs with h | h
      · exfalso; apply h2sq
        have hM : M = 0 := Int.natAbs_eq_zero.mp h
        refine ⟨K.natAbs, ?_⟩
        have : (N : ℤ) = 2 * (K.natAbs : ℤ) ^ 2 := by rw [Int.natAbs_sq]; rw [hM] at e; linarith
        exact_mod_cast this
      · exact h
    · have : (N : ℤ) + (M.natAbs : ℤ) ^ 2 = 2 * (K.natAbs : ℤ) ^ 2 := by
        rw [Int.natAbs_sq, Int.natAbs_sq]; exact e
      exact_mod_cast this
  classical
  obtain ⟨hm0, k0, hk0⟩ := Nat.find_spec hex
  set m0 := Nat.find hex with hm
  have hmin : ∀ m < m0, ¬ (0 < m ∧ ∃ k : ℕ, N + m ^ 2 = 2 * k ^ 2) := fun m hm' => Nat.find_min hex hm'
  have step : ∀ u v : ℤ, (N : ℤ) + u ^ 2 = 2 * v ^ 2 → 0 < u.natAbs → u.natAbs < m0 → False := by
    intro u v e hu hlt
    apply hmin u.natAbs hlt
    refine ⟨hu, v.natAbs, ?_⟩
    have : (N : ℤ) + (u.natAbs : ℤ) ^ 2 = 2 * (v.natAbs : ℤ) ^ 2 := by
      rw [Int.natAbs_sq, Int.natAbs_sq]; exact e
    exact_mod_cast this
  refine ⟨m0, k0, hm0, ?_, hk0⟩
  by_contra hle
  push Not at hle
  have hkM : (k0 : ℤ) ≤ m0 := by exact_mod_cast hle
  have e : (N : ℤ) + (m0 : ℤ) ^ 2 = 2 * (k0 : ℤ) ^ 2 := by exact_mod_cast hk0
  have hNz : (0 : ℤ) < N := by exact_mod_cast hN
  have hm2 : (m0 : ℤ) < 2 * k0 := by nlinarith
  have hk0' : (0 : ℤ) < k0 := by nlinarith
  rcases lt_or_eq_of_le hkM with hlt | heq
  · -- k0 < m0
    have e' : (N : ℤ) + (3 * m0 - 4 * k0) ^ 2 = 2 * (3 * k0 - 2 * m0) ^ 2 := by nlinarith
    rcases lt_trichotomy (3 * (m0 : ℤ) - 4 * k0) 0 with hu | hu | hu
    · apply step _ _ e' (by omega) (by omega)
    · apply h2sq
      rw [hu] at e'
      refine ⟨(3 * k0 - 2 * m0 : ℤ).natAbs, ?_⟩
      have : (N : ℤ) = 2 * ((3 * k0 - 2 * m0 : ℤ).natAbs : ℤ) ^ 2 := by
        rw [Int.natAbs_sq]; linarith
      exact_mod_cast this
    · apply step _ _ e' (by omega) (by omega)
  · apply hsq
    refine ⟨k0, ?_⟩
    have : (N : ℤ) = (k0 : ℤ) ^ 2 := by rw [← heq] at e; nlinarith
    exact_mod_cast this

/-- Witnesses: N = 17 (prime, 1 mod 8): 17 + 1 = 2*9; N = 153 = 9*17: 153 + 9 = 2*81;  N = 7: 7+1 = 2*4, 7 + 25 = 2*16. -/
theorem wit37 : Sol 17 ∧ Sol 153 ∧ Sol 7 := ⟨⟨1, 3, by norm_num⟩, ⟨3, 9, by norm_num⟩, ⟨1, 2, by norm_num⟩⟩

theorem wit37_pos : ∃ M K : ℕ, 0 < M ∧ M < K ∧ 7 + M ^ 2 = 2 * K ^ 2 := ⟨1, 2, by norm_num⟩

end Erdos634.BeesonRow
