/-
Lemma S, node A5: **Iso and Elim in class form** (PROOF_lemmaS.md P1.2 — the reviewed statements).

  For an I-point x put E_x := Σ_{j∈I, x_j = x} e_j, and let d_x be the order of x's m-part.
  Iso: if f(d_x) ∤ d_y for every other I-point y with E_y ≠ 0, then E_x = 0.
  Elim: if E_x = 0 for every full I-point x (f(m) | d_x), then E_x = 0 for every I-point.
(Lemma P's hypothesis; p ≥ 7; m_I = m by P1.3.)

Encoding: x_j = a_j/n with 0 < a_j < n, so x_j = x_k ⟺ a_j = a_k; an I-point is a value y of a with
p ∤ y; E_y = `classSum a e y`. Elim is stated for the tile datum a : Fin 3 → ℕ, Σ a_j = n = p^r m,
gcd(a) = 1. Proof of Elim as in §3.4: a non-full y has a deficiency prime power q^k ∥ f(m) with
q | a_y; q divides no other a (else it divides all three, gcd = 1), so every other point has the full
q^k, hence q^k | f(d_x) ∤ d_y; then Iso at each non-full point.
Formalization debt, not /goal progress.
-/
import Mathlib
import Erdos634.Draft.LemmaSIso

open scoped BigOperators
open Finset

namespace Erdos634.LemmaSElim

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi (dm)
open Erdos634.LemmaSIso (fpc lemmaIso fpc_dvd fpc_mod4 fpc_ne_zero)

/-- E_y = Σ_{j : x_j = y} e_j. -/
def classSum {ι : Type*} [Fintype ι] (a : ι → ℕ) (e : ι → ℚ) (y : ℕ) : ℚ :=
  ∑ j ∈ univ.filter (fun j => a j = y), e j

/-- Every character condition sees e only through the class sums. -/
theorem regroup {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} [NeZero n]
    (χ : DirichletCharacter ℂ n) (a : ι → ℕ) (e : ι → ℚ) :
    ∑ j, (e j : ℂ) * bracket χ (a j) =
      ∑ y : (univ.image a), ((classSum a e y : ℚ) : ℂ) * bracket χ y := by
  rw [sum_coe_sort (univ.image a) (fun y => ((classSum a e y : ℚ) : ℂ) * bracket χ y),
    ← sum_fiberwise_of_maps_to (g := a) (t := univ.image a)
      (fun j _ => mem_image_of_mem a (mem_univ j))]
  refine sum_congr rfl (fun y _ => ?_)
  unfold classSum
  rw [Rat.cast_sum, sum_mul]
  exact sum_congr rfl (fun j hj => by rw [(mem_filter.1 hj).2])

section Cls
variable {p r m : ℕ} [hp : Fact p.Prime] [NeZero m]

/-- **Lemma Iso, class form** (P1.2). -/
theorem lemmaIso_class (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (x : ℕ) (hx : x ∈ univ.image a) (hpx : ¬ p ∣ x)
    (hiso : ∀ y ∈ univ.image a, y ≠ x → ¬ p ∣ y → classSum a e y ≠ 0 →
      ¬ fpc (dm m x) ∣ dm m y) :
    classSum a e x = 0 := by
  have := lemmaIso (p := p) (r := r) (m := m) hp7 hr hpm (ι := univ.image a)
    (fun y => (y : ℕ)) (fun y => classSum a e y)
    (fun χ ho hc => by rw [← regroup χ a e]; exact hP χ ho hc) ⟨x, hx⟩ hpx
    (fun k hk hpk hek => hiso k k.2 (fun h => hk (Subtype.ext h)) hpk hek)
  exact this

/-! ### Prime-power bookkeeping -/

theorem pp_dvd_dm {q k a : ℕ} (hq : q.Prime) (hqm : q ^ k ∣ m) (hqa : ¬ q ∣ a) :
    q ^ k ∣ dm m a := by
  have hc : (q ^ k).Coprime (m.gcd a) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hq).2
      (fun h => hqa (dvd_trans h (Nat.gcd_dvd_right m a))))
  refine hc.dvd_of_dvd_mul_right ?_
  rw [dm, Nat.div_mul_cancel (Nat.gcd_dvd_left m a)]; exact hqm

theorem dvd_fpc {q k d : ℕ} (hqd : q ^ k ∣ d) (h2 : q ≠ 2 ∨ 2 ≤ k) (hq : q.Prime) :
    q ^ k ∣ fpc d := by
  unfold fpc
  split_ifs with h
  · rcases h2 with h2 | h2
    · have hc : (q ^ k).Coprime 2 :=
        Nat.Coprime.pow_left k ((Nat.coprime_primes hq Nat.prime_two).2 h2)
      refine hc.dvd_of_dvd_mul_left ?_
      rwa [Nat.mul_div_cancel' (show 2 ∣ d by omega)]
    · by_cases hq2 : q = 2
      · subst hq2
        have : 4 ∣ d := dvd_trans (by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num]; exact Nat.pow_dvd_pow 2 h2) hqd
        omega
      · have hc : (q ^ k).Coprime 2 :=
          Nat.Coprime.pow_left k ((Nat.coprime_primes hq Nat.prime_two).2 hq2)
        refine hc.dvd_of_dvd_mul_left ?_
        rwa [Nat.mul_div_cancel' (show 2 ∣ d by omega)]
  · exact hqd

/-- A non-full point has a deficiency prime power q^k | f(m), q^k ∤ d_y, and q^k ≠ 2. -/
theorem deficiency {y : ℕ} (hnf : ¬ fpc m ∣ dm m y) :
    ∃ q k : ℕ, q.Prime ∧ 1 ≤ k ∧ q ^ k ∣ fpc m ∧ ¬ q ^ k ∣ dm m y ∧ (q ≠ 2 ∨ 2 ≤ k) := by
  have hm0 : m ≠ 0 := NeZero.ne m
  have hf0 : fpc m ≠ 0 := fpc_ne_zero hm0
  have hd0 : dm m y ≠ 0 := by
    intro h0
    have := Nat.div_mul_cancel (Nat.gcd_dvd_left m y)
    rw [show m / m.gcd y = 0 from h0, zero_mul] at this
    exact hm0 this.symm
  rw [← Nat.factorization_le_iff_dvd hf0 hd0, Finsupp.le_def] at hnf
  push_neg at hnf
  obtain ⟨q, hq⟩ := hnf
  have hqp : q.Prime := by
    by_contra hnp
    simp [Nat.factorization_eq_zero_of_not_prime _ hnp] at hq
  refine ⟨q, (fpc m).factorization q, hqp, by omega, Nat.ordProj_dvd _ _,
    fun h => by rw [hqp.pow_dvd_iff_le_factorization hd0] at h; omega, ?_⟩
  by_cases hq2 : q = 2
  · subst hq2
    right
    have h2 : 2 ∣ fpc m := by
      have := Nat.ordProj_dvd (fpc m) 2
      exact dvd_trans (dvd_pow_self 2 (by omega)) this
    have h4 : 2 ^ 2 ∣ fpc m := by have := fpc_mod4 m; norm_num; omega
    exact (Nat.prime_two.pow_dvd_iff_le_factorization hf0).1 h4
  · exact Or.inl hq2

/-- In a tile datum a prime q | n dividing two of the a_j divides gcd(a) = 1: impossible. -/
theorem not_two_dvd {a : Fin 3 → ℕ} (hgcd : univ.gcd a = 1) {q : ℕ} (hq : q.Prime)
    (hn : q ∣ a 0 + a 1 + a 2) {j k : Fin 3} (hjk : j ≠ k) (hj : q ∣ a j) (hk : q ∣ a k) : False := by
  have H : ∀ t : Fin 3, ((a t : ℕ) : ZMod q) = 0 := by
    have hs : ((a 0 : ZMod q) + a 1 + a 2) = 0 := by
      have := (ZMod.natCast_eq_zero_iff _ _).2 hn; push_cast at this; exact this
    have hj' := (ZMod.natCast_eq_zero_iff _ _).2 hj
    have hk' := (ZMod.natCast_eq_zero_iff _ _).2 hk
    intro t
    fin_cases j <;> fin_cases k <;> fin_cases t <;> simp at hjk hj' hk' ⊢ <;>
      first | exact hj' | exact hk' | linear_combination hs - hj' - hk'
  have : q ∣ univ.gcd a := Finset.dvd_gcd (fun t _ => (ZMod.natCast_eq_zero_iff _ _).1 (H t))
  rw [hgcd] at this
  exact hq.one_lt.ne' (Nat.dvd_one.1 this)

/-- **Lemma Elim, class form** (P1.2), for a tile datum. -/
theorem lemmaElim (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) (a : Fin 3 → ℕ) (e : Fin 3 → ℚ)
    (hsum : a 0 + a 1 + a 2 = p ^ r * m) (hgcd : univ.gcd a = 1)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (hfull : ∀ x ∈ univ.image a, ¬ p ∣ x → fpc m ∣ dm m x → classSum a e x = 0) :
    ∀ x ∈ univ.image a, ¬ p ∣ x → classSum a e x = 0 := by
  intro z hz hpz
  by_cases hzf : fpc m ∣ dm m z
  · exact hfull z hz hpz hzf
  refine lemmaIso_class hp7 hr hpm a e hP z hz hpz (fun y hy hyz hpy hEy hdiv => ?_)
  have hyf : ¬ fpc m ∣ dm m y := fun h => hEy (hfull y hy hpy h)
  obtain ⟨q, k, hq, hk, hqf, hqy, h2⟩ := deficiency hyf
  have hqm : q ^ k ∣ m := dvd_trans hqf (fpc_dvd m)
  have hqa : q ∣ y := by
    by_contra h; exact hqy (pp_dvd_dm hq hqm h)
  have hqz : ¬ q ∣ z := by
    intro h
    obtain ⟨jy, -, rfl⟩ := mem_image.1 hy
    obtain ⟨jz, -, rfl⟩ := mem_image.1 hz
    have hne : jy ≠ jz := fun h' => hyz (by rw [h'])
    have hqn : q ∣ a 0 + a 1 + a 2 := by
      rw [hsum]; exact dvd_mul_of_dvd_right (dvd_trans (dvd_pow_self q (by omega)) hqm) _
    exact not_two_dvd hgcd hq hqn hne hqa h
  have := dvd_fpc (pp_dvd_dm hq hqm hqz) h2 hq
  exact hqy (dvd_trans this hdiv)

end Cls

/-! ## Witness: every hypothesis of `lemmaElim` realised with e ≠ 0 (n = 14, a = (2,5,7),
e = (0,0,1), the right-angle relation; Lemma P's hypothesis via `crit_witness_14`). -/
theorem witness_elim : ∀ x ∈ univ.image (![2, 5, 7] : Fin 3 → ℕ), ¬ 7 ∣ x →
    classSum ![2, 5, 7] ![0, 0, 1] x = 0 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine lemmaElim (p := 7) (r := 1) (m := 2) (by norm_num) le_rfl (by norm_num) _ _
    (by decide) (by decide) ?_ ?_
  · intro χ ho _
    have := Erdos634.LemmaSC.crit_witness_14 χ ho
    simp [Fin.sum_univ_three, this]
  · intro x hx hpx _
    simp only [mem_image, mem_univ, true_and] at hx
    obtain ⟨j, rfl⟩ := hx
    fin_cases j
    · simp [classSum, sum_filter, Fin.sum_univ_three]
    · simp [classSum, sum_filter, Fin.sum_univ_three]
    · exact absurd (by decide) hpx

#print axioms Erdos634.LemmaSElim.lemmaIso_class
#print axioms Erdos634.LemmaSElim.lemmaElim
#print axioms Erdos634.LemmaSElim.witness_elim

end Erdos634.LemmaSElim
