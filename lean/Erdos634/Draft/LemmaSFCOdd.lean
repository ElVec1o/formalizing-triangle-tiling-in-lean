/-
Lemma S, node A5: **FC-odd, assembled** (PROOF_lemmaS.md P2):

  FC-odd (Lemma P's hypothesis; n ≢ 2 (mod 4); n ∉ {21, 28}). E_x = 0 for every full I-point x.
  R1′ and R1F2c are completed by Lemma L. R1F2o is completed by R3, R2b and R2a.

Case split used (class form; m_I = m by P1.3, so "full" = prime to m): for a full I-point x,
* no other full point with E ≠ 0 has β = ±β_x                   → isolation (N(a)/N(b)) [LemmaSFC];
* another full y with β_y = −β_x                                → class R1′ [LemmaSR1p];
* another full y with β_y = β_x, third point l full            → |F| = 3, P1.4 [LemmaSF3];
* another full y with β_y = β_x, third point l not full        → class R1F2 [LemmaSR1F2].
The only exclusion is the paper's own class R2 (p = 7, r = 1, m ∈ {3, 4}, i.e. n ∈ {21, 28}),
and only in its genuinely exceptional configuration: hypothesis `hex` asks for at most two full
I-points there (LemmaSOddAll settles the three-point case by exact computation).
Formalization debt, not /goal progress.
-/
import Mathlib
import Erdos634.Draft.LemmaSR1F2

open scoped BigOperators
open Finset

namespace Erdos634.LemmaSFCOdd

open DirichletCharacter
open Erdos634.LemmaSC (bracket)
open Erdos634.LemmaSElim (classSum)
open Erdos634.LemmaSFC (fullPts)
open Erdos634.LemmaSR3 (kX_ne small_cop)

theorem third (i j : Fin 3) (hij : i ≠ j) :
    ∃ k : Fin 3, (∀ a : Fin 3 → ℕ, a i + a j + a k = a 0 + a 1 + a 2) ∧
      (∀ t : Fin 3, t = i ∨ t = j ∨ t = k) := by
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | exact ⟨0, fun a => by (try simp) <;> ring, by decide⟩
    | exact ⟨1, fun a => by (try simp) <;> ring, by decide⟩
    | exact ⟨2, fun a => by (try simp) <;> ring, by decide⟩

section FC
variable {p r m : ℕ} [hp : Fact p.Prime] [NeZero m]

/-- **FC-odd**, as written (m ≢ 2 mod 4, n ∉ {21, 28}). -/
theorem fcOdd (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) (hm4 : m % 4 ≠ 2)
    (a : Fin 3 → ℕ) (hex : p = 7 → r = 1 → (m = 3 ∨ m = 4) → (fullPts p m a).card ≤ 2)
    (ha : ∀ j, 0 < a j) (hsum : a 0 + a 1 + a 2 = p ^ r * m) (e : Fin 3 → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0) :
    ∀ x ∈ fullPts p m a, classSum a e x = 0 := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  haveI : Fact (1 < p ^ r) := ⟨Nat.one_lt_pow (by omega) (by omega)⟩
  intro x hx
  have hxf := mem_filter.1 hx
  have hX : IsUnit ((x : ℕ) : ZMod (p ^ r)) := (ZMod.isUnit_iff_coprime x _).2
    (Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hxf.2.1).symm)
  have c1 := kX_ne hX 1 (small_cop (by norm_num) (by norm_num) hp7)
  have c2 := kX_ne hX 2 (small_cop (by norm_num) (by norm_num) hp7)
  have c3 := kX_ne hX 3 (small_cop (by norm_num) (by norm_num) hp7)
  push_cast at c1 c2 c3
  by_cases hiso : ∀ y ∈ fullPts p m a, y ≠ x → classSum a e y ≠ 0 →
      (y : ZMod (p ^ r)) ≠ x ∧ (y : ZMod (p ^ r)) ≠ -x
  · refine Erdos634.LemmaSFC.fc_generic hp7 hr hpm hm4 a e hP ?_ x hx hiso
    by_cases h11 : 11 ≤ p
    · exact Or.inl h11
    by_cases hr2 : 2 ≤ r
    · exact Or.inr (Or.inl hr2)
    have hp7' : p = 7 := by
      have hpp := hp.out
      interval_cases p <;> first | rfl | (exfalso; norm_num at hpp)
    have hr1 : r = 1 := by omega
    by_cases h34 : m = 3 ∨ m = 4
    · exact Or.inr (Or.inr (Or.inl (hex hp7' hr1 h34)))
    · push Not at h34
      exact Or.inr (Or.inr (Or.inr ⟨hr1, h34.1, h34.2⟩))
  push Not at hiso
  obtain ⟨y, hy, hyx, hEy, hrel⟩ := hiso
  have hyf := mem_filter.1 hy
  obtain ⟨i, -, rfl⟩ := mem_image.1 hxf.1
  obtain ⟨j, -, rfl⟩ := mem_image.1 hyf.1
  have hij : i ≠ j := fun h => hyx (by rw [h])
  obtain ⟨k, hk, hall⟩ := third i j hij
  have himg : univ.image a = {a i, a j, a k} := by
    ext w; simp only [mem_image, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · rintro ⟨t, rfl⟩; rcases hall t with rfl | rfl | rfl <;> simp
    · rintro (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩
  have hsum' : a i + a j + a k = p ^ r * m := by rw [hk a, hsum]
  have hs0 : ((a i : ℕ) : ZMod (p ^ r)) + (a j : ZMod (p ^ r)) + (a k : ZMod (p ^ r)) = 0 := by
    have : ((a i + a j + a k : ℕ) : ZMod (p ^ r)) = 0 := by
      rw [hsum', Nat.cast_mul, ZMod.natCast_self, zero_mul]
    push_cast at this; exact this
  by_cases hneg : ((a j : ℕ) : ZMod (p ^ r)) = -(a i : ZMod (p ^ r))
  · -- class R1′
    have hpk : p ∣ a k := by
      have hk0 : ((a k : ℕ) : ZMod (p ^ r)) = 0 := by linear_combination hs0 - hneg
      rw [ZMod.natCast_eq_zero_iff] at hk0
      exact dvd_trans (dvd_pow_self p (by omega)) hk0
    exact (Erdos634.LemmaSR1p.lemmaR1prime hp7 hr hpm hm4 a e hP (a i) (a j) (a k) himg hsum' (ha k)
      hxf.2.1 hyf.2.1 hpk hxf.2.2 hyf.2.2 (Ne.symm hyx) hneg).1
  -- same β
  have hsame : ((a j : ℕ) : ZMod (p ^ r)) = (a i : ZMod (p ^ r)) := by
    by_contra h; exact hneg (hrel h)
  have hl : ((a k : ℕ) : ZMod (p ^ r)) = -2 * (a i : ZMod (p ^ r)) := by
    linear_combination hs0 - hsame
  have hpl : ¬ p ∣ a k := by
    intro h
    have hPk : ((a k : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
    have hcast := congrArg (ZMod.castHom (dvd_pow_self p (by omega : r ≠ 0)) (ZMod p)) hl
    rw [map_natCast, map_mul, map_neg, map_ofNat, map_natCast, hPk] at hcast
    have h2x : ((2 * a i : ℕ) : ZMod p) = 0 := by push_cast; linear_combination hcast
    rw [ZMod.natCast_eq_zero_iff] at h2x
    rcases (Nat.Prime.dvd_mul hp.out).1 h2x with h2 | h2
    · exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega)
    · exact hxf.2.1 h2
  by_cases hlc : (a k).Coprime m
  · -- |F| = 3
    have hlfull : a k ∈ fullPts p m a := mem_filter.2 ⟨mem_image_of_mem a (mem_univ k), hpl, hlc⟩
    have hxl : a i ≠ a k := fun h => c3 (by
      have : ((a k : ℕ) : ZMod (p ^ r)) = (a i : ZMod (p ^ r)) := by rw [h]
      linear_combination hl - this)
    have hyl : a j ≠ a k := fun h => c3 (by
      have : ((a k : ℕ) : ZMod (p ^ r)) = (a i : ZMod (p ^ r)) := by rw [← h, hsame]
      linear_combination hl - this)
    exact (Erdos634.LemmaSF3.lemmaF3same hp7 hr hpm hm4 a e hP (a i) (a j) (a k) himg hsum' hx hy
      hlfull (Ne.symm hyx) hxl hyl hsame
      ⟨fun h => c3 (by linear_combination hl - h), fun h => c1 (by linear_combination hl - h)⟩).1
  · -- class R1F2
    exact (Erdos634.LemmaSR1F2.lemmaR1F2 hp7 hr hpm hm4 a e hP (a i) (a j) (a k) himg hsum' hx hy
      hpl hlc (Ne.symm hyx) hsame).1

end FC

/-! ## Instances: n = 105 = 7·15, a = (2, 68, 35) (R1′ route) and n = 35, a = (1, 8, 26)
(|F| = 3 route): every full I-point has E = 0 for every e satisfying Lemma P's hypothesis. -/
theorem instance_105 (e : Fin 3 → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (7 ^ 1 * 15), χ.Odd → 7 ^ 1 ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ ((![2, 68, 35] : Fin 3 → ℕ) j) = 0) :
    ∀ x ∈ fullPts 7 15 (![2, 68, 35] : Fin 3 → ℕ), classSum ![2, 68, 35] e x = 0 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact fcOdd (p := 7) (r := 1) (m := 15) (by norm_num) le_rfl (by norm_num) (by norm_num)
    _ (fun _ _ h => by omega) (by decide) (by decide) e hP

theorem instance_35 (e : Fin 3 → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (7 ^ 1 * 5), χ.Odd → 7 ^ 1 ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ ((![1, 8, 26] : Fin 3 → ℕ) j) = 0) :
    ∀ x ∈ fullPts 7 5 (![1, 8, 26] : Fin 3 → ℕ), classSum ![1, 8, 26] e x = 0 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact fcOdd (p := 7) (r := 1) (m := 5) (by norm_num) le_rfl (by norm_num) (by norm_num)
    _ (fun _ _ h => by omega) (by decide) (by decide) e hP

#print axioms Erdos634.LemmaSFCOdd.fcOdd
#print axioms Erdos634.LemmaSFCOdd.instance_105
#print axioms Erdos634.LemmaSFCOdd.instance_35

end Erdos634.LemmaSFCOdd
