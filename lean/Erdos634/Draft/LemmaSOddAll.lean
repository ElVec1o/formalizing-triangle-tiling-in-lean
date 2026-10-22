/-
Lemma S, node A5: **Lemma S on the whole odd branch** (n ≢ 2 mod 4), with the paper's finite class
R2 (n ∈ {21, 28}) settled by exact computation inside Lean.

  Lemma S: if a prime p ≥ 7 divides n, then R(a) = R₀(a).   [here: n ≢ 2 (mod 4)]

LemmaSOdd.lemmaS_odd needs at most two full I-points when (p, r, m) ∈ {(7,1,3), (7,1,4)}. The
remaining configurations:
* n = 28 (m = 4): three full points would be three odd numbers summing to 28 — impossible.
* n = 21 (m = 3): three full points = three distinct residues prime to 21 summing to 21: exactly
  the ordered tuples of {1, 4, 16} and {2, 8, 11} (the quadratic-residue configuration 1 + 2 + 4 ≡ 0
  mod 7 that §4 calls genuinely exceptional). For those, the three equations at k = 1, 2, 5 have
  nonzero determinant (−5292, −7056), so R(a) = 0 = R₀(a).
Formalization debt, not /goal progress.
-/
import Mathlib
import Erdos634.Draft.LemmaSOdd

open scoped BigOperators
open Finset

namespace Erdos634.LemmaSOddAll

open Erdos634.LemmaS (relSpace trivSpace mem_relSpace_Z sawZ trivSpace_le)
open Erdos634.LemmaSFC (fullPts)

/-- The ordered pairs (a₀, a₁) of the exceptional n = 21 tiles. -/
def L21 : List (ℕ × ℕ) :=
  [(1, 4), (1, 16), (4, 1), (4, 16), (16, 1), (16, 4), (2, 8), (2, 11), (8, 2), (8, 11), (11, 2),
    (11, 8)]

/-- The bounded search as a Boolean. -/
def ok21 (x y : ℕ) : Bool :=
  !(decide (x + y ≤ 21) && x % 3 != 0 && x % 7 != 0 && y % 3 != 0 && y % 7 != 0 &&
    (21 - x - y) % 3 != 0 && (21 - x - y) % 7 != 0 && x != y && x != 21 - x - y && y != 21 - x - y)
  || decide ((x, y) ∈ L21)

/-- The search, checked by kernel evaluation. -/
theorem chk21 : (List.range 22).all (fun x => (List.range 22).all (fun y => ok21 x y)) = true := by
  decide

/-- The n = 21 tuples with three full points. -/
theorem enum21 (x y z : ℕ) (hx : x % 3 ≠ 0 ∧ x % 7 ≠ 0) (hy : y % 3 ≠ 0 ∧ y % 7 ≠ 0)
    (hz : z % 3 ≠ 0 ∧ z % 7 ≠ 0) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hs : x + y + z = 21) : (x, y) ∈ L21 := by
  have hz' : z = 21 - x - y := by omega
  subst hz'
  have h := List.all_eq_true.1 (List.all_eq_true.1 chk21 x (List.mem_range.2 (by omega))) y
    (List.mem_range.2 (by omega))
  simp only [ok21, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  rcases h with h | h
  · exfalso
    simp [hx.1, hx.2, hy.1, hy.2, hz.1, hz.2, hxy, hxz, hyz, show x + y ≤ 21 by omega] at h
  · exact h

/-- For a tuple listed in `L21`, R(a) = 0 = R₀(a) at n = 21. -/
theorem rel21 (a : Fin 3 → ℕ) (h : (a 0, a 1) ∈ L21) (hs : a 0 + a 1 + a 2 = 21) :
    relSpace 21 a = trivSpace 21 a := by
  refine le_antisymm (fun e he => ?_) (trivSpace_le 21 a)
  have h1 := (mem_relSpace_Z (n := 21) (by norm_num)).1 he 1 (by norm_num)
  have h2 := (mem_relSpace_Z (n := 21) (by norm_num)).1 he 2 (by norm_num)
  have h5 := (mem_relSpace_Z (n := 21) (by norm_num)).1 he 5 (by norm_num)
  simp only [L21, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at h
  have hz : e = 0 := by
    rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ |
      ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
    · have hc : a 2 = 21 - a 0 - a 1 := by omega
      rw [ha, hb] at hc
      norm_num at hc
      rw [ha, hb, hc] at h1 h2 h5
      simp only [sawZ] at h1 h2 h5
      norm_num at h1 h2 h5
      funext i
      fin_cases i <;> simp <;> linarith
  rw [hz]; exact zero_mem _

/-- **Lemma S, odd branch, unconditional**: n = p^r m, p ≥ 7 prime, p ∤ m, m ≢ 2 (mod 4). -/
theorem lemmaS_oddAll {p r m : ℕ} [hp : Fact p.Prime] [NeZero m] (hp7 : 7 ≤ p) (hr : 1 ≤ r)
    (hpm : ¬ p ∣ m) (hm4 : m % 4 ≠ 2)
    (a : Fin 3 → ℕ) (hpos : ∀ i, 0 < a i) (hsum : ∑ i, a i = p ^ r * m)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) :
    relSpace (p ^ r * m) a = trivSpace (p ^ r * m) a := by
  by_cases hE : p = 7 ∧ r = 1 ∧ (m = 3 ∨ m = 4) ∧ ¬ (fullPts p m a).card ≤ 2
  · obtain ⟨rfl, rfl, hm34, hc⟩ := hE
    have himg3 : (univ.image a).card ≤ 3 := card_image_le.trans (by simp)
    have hsub : fullPts 7 m a ⊆ univ.image a := filter_subset _ _
    have hfc := card_le_card hsub
    have heq : fullPts 7 m a = univ.image a := eq_of_subset_of_card_le hsub (by omega)
    have hall : ∀ i, a i ∈ fullPts 7 m a := fun i => heq ▸ mem_image_of_mem a (mem_univ i)
    have hinj : Set.InjOn a (univ : Finset (Fin 3)) :=
      card_image_iff.1 (by rw [card_univ, Fintype.card_fin]; omega)
    have hne : ∀ i j : Fin 3, i ≠ j → a i ≠ a j :=
      fun i j hij h => hij (hinj (mem_coe.2 (mem_univ i)) (mem_coe.2 (mem_univ j)) h)
    have hcond : ∀ i, ¬ 7 ∣ a i ∧ (a i).Coprime m := fun i => (mem_filter.1 (hall i)).2
    have hsum3 : a 0 + a 1 + a 2 = 7 ^ 1 * m := by rw [← hsum, Fin.sum_univ_three]
    rcases hm34 with rfl | rfl
    · -- n = 21
      have hmod : ∀ i, a i % 3 ≠ 0 ∧ a i % 7 ≠ 0 := by
        intro i
        obtain ⟨h7, h3⟩ := hcond i
        refine ⟨fun h => ?_, fun h => h7 (Nat.dvd_of_mod_eq_zero h)⟩
        have := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h) (dvd_refl 3)
        rw [h3.gcd_eq_one] at this; omega
      have hs21 : a 0 + a 1 + a 2 = 21 := by rw [hsum3]; norm_num
      have := enum21 (a 0) (a 1) (a 2) (hmod 0) (hmod 1) (hmod 2) (hne 0 1 (by decide))
        (hne 0 2 (by decide)) (hne 1 2 (by decide)) hs21
      show relSpace 21 a = trivSpace 21 a
      exact rel21 a this hs21
    · -- n = 28: three odd numbers cannot sum to 28
      exfalso
      have hodd : ∀ i, a i % 2 = 1 := by
        intro i
        by_contra h
        have h2 : 2 ∣ a i := by omega
        have := Nat.dvd_gcd h2 (show 2 ∣ 4 by norm_num)
        rw [(hcond i).2.gcd_eq_one] at this; omega
      have := hodd 0; have := hodd 1; have := hodd 2
      omega
  · exact Erdos634.LemmaSOdd.lemmaS_odd hp7 hr hpm hm4 a
      (fun h1 h2 h3 => by by_contra hc; exact hE ⟨h1, h2, h3, hc⟩) hpos hsum hgcd

/-! ## Instances: the exceptional tiles themselves, and (2, 8, 11)/21. -/
theorem instance_1_4_16 : relSpace (7 ^ 1 * 3) ![1, 4, 16] = trivSpace (7 ^ 1 * 3) ![1, 4, 16] := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact lemmaS_oddAll (p := 7) (r := 1) (m := 3) (by norm_num) le_rfl (by norm_num) (by norm_num)
    _ (by decide) (by decide) (by decide)

theorem instance_1_4_16_trivial : trivSpace 21 ![1, 4, 16] = ⊥ := by
  rw [eq_bot_iff, trivSpace, Submodule.span_le]
  rintro v (⟨i, j, hij, h, rfl⟩ | ⟨i, h, rfl⟩)
  · fin_cases i <;> fin_cases j <;> simp at hij h
  · fin_cases i <;> simp at h

#print axioms Erdos634.LemmaSOddAll.enum21
#print axioms Erdos634.LemmaSOddAll.rel21
#print axioms Erdos634.LemmaSOddAll.lemmaS_oddAll
#print axioms Erdos634.LemmaSOddAll.instance_1_4_16

end Erdos634.LemmaSOddAll
