import Mathlib

/-!
# Beeson (arXiv 1206.2229 v4), Lemma 36 (necessity half of the tiling equation) and the arithmetic core of Theorem 8

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Lemma 36, Theorem 8), Beeson-Zhang, Laczkovich.
Formalization debt, not progress on the /goal outcomes.  Pure arithmetic: no H1, no tiling.  (This is map row T-L44;
the printed numbering in the repo text (private working notes, not included) is Lemma 36, the map's "L44" is a renumbering.)

Printed Lemma 36: if `N = 2K^2 - M^2` is solvable then `N` is a square times a product of distinct primes, each 2 or
`8n +- 1`.  Printed proof: "WLOG N squarefree; mod 8"; the proof here is by 2-adic-free descent on `p^2 | M, K` and
`ZMod.exists_sq_eq_two_iff` (2 is a square mod p iff p = +-1 mod 8), valid for EVERY prime p = 3, 5 mod 8.

* `lemma36_val`: v_p(N) is even for p = 3, 5 (mod 8).
* `lemma36`: `N = s^2 q`, `q` squarefree, every prime of `q` is 2 or `+-1 mod 8`.
* `thm8_core`: the arithmetic core of printed Theorem 8 (N prime, `K | M^2`, `M^2 < N`, `M > 0` is impossible).
  The printed text "K < M since a/c = K/M" is not needed; Theorem 4's `M^2 < N` suffices.
-/

namespace Erdos634.BeesonRow

theorem lemma36_val (p : ℕ) (hp : p.Prime) (h8 : p % 8 = 3 ∨ p % 8 = 5) :
    ∀ N : ℕ, ∀ M K : ℤ, (N : ℤ) + M ^ 2 = 2 * K ^ 2 → Even (padicValNat p N) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by rintro rfl; omega
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro M K h
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    by_cases hb : (p : ℤ) ∣ M ∧ (p : ℤ) ∣ K
    · obtain ⟨⟨m, rfl⟩, ⟨k, rfl⟩⟩ := hb
      have h2 : (N : ℤ) = (p : ℤ) ^ 2 * (2 * k ^ 2 - m ^ 2) := by linear_combination h
      have hpos : 0 < 2 * k ^ 2 - m ^ 2 := by
        have : (0 : ℤ) < (p : ℤ) ^ 2 := by have := hp.pos; positivity
        have hN' : (0 : ℤ) < N := by exact_mod_cast hN
        by_contra hc
        push Not at hc
        have := mul_nonpos_of_nonneg_of_nonpos this.le hc
        linarith
      obtain ⟨N', hN'⟩ : ∃ N' : ℕ, (N' : ℤ) = 2 * k ^ 2 - m ^ 2 := ⟨(2 * k ^ 2 - m ^ 2).toNat, by omega⟩
      have hNN : N = p ^ 2 * N' := by
        have : (N : ℤ) = ((p ^ 2 * N' : ℕ) : ℤ) := by push_cast; rw [h2, hN']
        exact_mod_cast this
      have hN'pos : 0 < N' := by
        rcases Nat.eq_zero_or_pos N' with h0 | h0
        · rw [h0] at hN'; simp at hN'; omega
        · exact h0
      have hlt : N' < N := by
        rw [hNN]; have := hp.two_le; have h4 : 4 ≤ p ^ 2 := by nlinarith
        nlinarith
      have := ih N' hlt m k (by rw [hN']; ring)
      rw [hNN, padicValNat.mul (pow_pos hp.pos 2).ne' hN'pos.ne', padicValNat.pow _ hp.ne_zero,
        padicValNat.self hp.one_lt]
      rcases this with ⟨r, hr⟩; exact ⟨r + 1, by omega⟩
    · have hnd : ¬ p ∣ N := by
        intro hd
        apply hb
        have hz : ((M : ℤ) : ZMod p) ^ 2 = 2 * ((K : ℤ) : ZMod p) ^ 2 := by
          have := congrArg (fun x : ℤ => (x : ZMod p)) h
          simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_ofNat] at this
          have hN0 : ((N : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff N p).mpr hd
          rw [hN0, zero_add] at this
          exact this
        by_cases hK : ((K : ℤ) : ZMod p) = 0
        · have hM : ((M : ℤ) : ZMod p) = 0 := by
            rw [hK] at hz; simpa using hz
          exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hM, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hK⟩
        · exfalso
          have hsq : IsSquare (2 : ZMod p) := by
            refine ⟨(M : ZMod p) * (K : ZMod p)⁻¹, ?_⟩
            field_simp
            linear_combination (-1 : ZMod p) * hz
          have := (ZMod.exists_sq_eq_two_iff hp2).mp hsq
          omega
      rw [padicValNat.eq_zero_of_not_dvd hnd]; exact ⟨0, rfl⟩

theorem lemma36 (N M K : ℕ) (hN : 0 < N) (h : (N : ℤ) + (M : ℤ) ^ 2 = 2 * (K : ℤ) ^ 2) :
    ∃ s q : ℕ, N = s ^ 2 * q ∧ Squarefree q ∧ ∀ p : ℕ, p.Prime → p ∣ q → p = 2 ∨ p % 8 = 1 ∨ p % 8 = 7 := by
  obtain ⟨a, b, hab, hsf⟩ := Nat.sq_mul_squarefree N
  refine ⟨b, a, hab.symm, hsf, ?_⟩
  intro p hp hpa
  by_contra hne
  push Not at hne
  obtain ⟨h2, h1, h7⟩ := hne
  have h8 : p % 8 = 3 ∨ p % 8 = 5 := by
    have := hp.eq_one_or_self_of_dvd 2
    have hodd : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h | h
      · exact absurd h h2
      · exact h
    omega
  have hev := lemma36_val p hp h8 N M K h
  have ha0 : a ≠ 0 := by rintro rfl; simp at hab; omega
  have hb0 : b ≠ 0 := by rintro rfl; simp at hab; omega
  have hva : padicValNat p a = 1 := by
    have h1' : 1 ≤ padicValNat p a := by
      haveI : Fact p.Prime := ⟨hp⟩
      exact one_le_padicValNat_of_dvd ha0 hpa
    have h2' : ¬ 2 ≤ padicValNat p a := by
      intro h2'
      haveI : Fact p.Prime := ⟨hp⟩
      have : p ^ 2 ∣ a := (padicValNat_dvd_iff_le ha0).mpr h2'
      have : p * p ∣ a := by rwa [← pow_two]
      exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hsf p this))
    omega
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← hab, padicValNat.mul (by positivity) ha0, padicValNat.pow _ hb0, hva] at hev
  obtain ⟨r, hr⟩ := hev
  omega

/-- Arithmetic core of printed Theorem 8: `N` prime, `0 < M`, `M^2 < N`, `K | M^2`, `N + M^2 = 2K^2` is impossible. -/
theorem thm8_core (N M K : ℕ) (hN : N.Prime) (hM : 0 < M) (hlt : M ^ 2 < N) (hK : K ∣ M ^ 2)
    (h : N + M ^ 2 = 2 * K ^ 2) : False := by
  have hKN : K ∣ N := by
    have : K ∣ N + M ^ 2 := by rw [h]; exact Dvd.dvd.mul_left (dvd_pow_self K two_ne_zero) 2
    exact (Nat.dvd_add_left hK).mp this
  rcases (Nat.dvd_prime hN).mp hKN with h1 | h1
  · subst h1; nlinarith [hN.two_le, pow_pos hM 2]
  · subst h1; nlinarith [hN.two_le]

/-- Witnesses: N = 7 (= -1 mod 8) is solvable (7 + 1 = 2*4? no: 7+25 = 2*16), N = 17: 17+1 = 2*9. -/
theorem wit36 : (7 : ℤ) + 5 ^ 2 = 2 * 4 ^ 2 ∧ (17 : ℤ) + 1 ^ 2 = 2 * 3 ^ 2 := by norm_num

end Erdos634.BeesonRow
