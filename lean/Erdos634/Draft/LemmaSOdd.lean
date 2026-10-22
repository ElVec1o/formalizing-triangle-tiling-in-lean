/-
Lemma S, node A5: **Lemma S on the odd branch** (n ≢ 2 mod 4), assembled from
  Lemma C's criterion (LemmaSCCrit.mem_relSpace_iff_odd),
  FC-odd (LemmaSFCOdd.fcOdd), Elim (LemmaSElim.lemmaElim) — together Lemma P's conclusion —
  and Lemma R (LemmaSR.lemmaR: Lemma S ⟸ Lemma P).

  Lemma S: if a prime p ≥ 7 divides n, then R(a) = R₀(a).

Proved here for tile data a (a_j ≥ 1, Σ a_j = n, gcd(a) = 1) with n = p^r m, p ∤ m, r ≥ 1, p ≥ 7, and
  * m ≢ 2 (mod 4)                      [the odd branch; the EVEN branch n ≡ 2 (mod 4) is in LemmaSEven, not here; note 2026-10-03],
  * at (p, r, m) ∈ {(7, 1, 3), (7, 1, 4)} (n ∈ {21, 28}, the paper's class R2) at most two full
    I-points (`hex`); LemmaSOddAll removes this by exact computation.
Formalization debt, not /goal progress.
-/
import Mathlib
import Erdos634.Draft.LemmaSFCOdd
import Erdos634.Draft.LemmaSR

open scoped BigOperators
open Finset

namespace Erdos634.LemmaSOdd

open Erdos634.LemmaS (relSpace trivSpace)
open Erdos634.LemmaSElim (classSum lemmaElim)
open Erdos634.LemmaSFC (fullPts dm_eq_iff)
open Erdos634.LemmaSPhi (dm)
open Erdos634.LemmaSIso (fpc)

/-- **Lemma S, odd branch.** -/
theorem lemmaS_odd {p r m : ℕ} [hp : Fact p.Prime] [NeZero m] (hp7 : 7 ≤ p) (hr : 1 ≤ r)
    (hpm : ¬ p ∣ m) (hm4 : m % 4 ≠ 2)
    (a : Fin 3 → ℕ) (hex : p = 7 → r = 1 → (m = 3 ∨ m = 4) → (fullPts p m a).card ≤ 2) (hpos : ∀ i, 0 < a i) (hsum : ∑ i, a i = p ^ r * m)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) :
    relSpace (p ^ r * m) a = trivSpace (p ^ r * m) a := by
  haveI : NeZero (p ^ r * m) := ⟨Nat.mul_ne_zero (pow_ne_zero _ hp.out.ne_zero) (NeZero.ne m)⟩
  have hsum3 : a 0 + a 1 + a 2 = p ^ r * m := by rw [← hsum, Fin.sum_univ_three]
  have hgcd' : univ.gcd a = 1 := by
    apply Nat.eq_one_of_dvd_one
    rw [← hgcd]
    exact Nat.dvd_gcd (Finset.gcd_dvd (mem_univ 0))
      (Nat.dvd_gcd (Finset.gcd_dvd (mem_univ 1)) (Finset.gcd_dvd (mem_univ 2)))
  refine Erdos634.LemmaSR.lemmaR a hpos hsum hgcd hp.out
    (dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) m) (fun e he j hpj => ?_)
  have hcrit := (Erdos634.LemmaSC.mem_relSpace_iff_odd a e).1 he
  have hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * Erdos634.LemmaSC.bracket χ (a j) = 0 := fun χ ho _ => hcrit χ ho
  have hfpc : fpc m = m := by unfold fpc; rw [if_neg hm4]
  have hall := lemmaElim hp7 hr hpm a e hsum3 hgcd' hP (fun x hx hpx hfull => by
    rw [hfpc] at hfull
    have hdm : dm m x = m := Nat.dvd_antisymm (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left m x)) hfull
    exact Erdos634.LemmaSFCOdd.fcOdd hp7 hr hpm hm4 a hex hpos hsum3 e hP x
      (mem_filter.2 ⟨hx, hpx, (dm_eq_iff x).1 hdm⟩)) (a j) (mem_image_of_mem a (mem_univ j)) hpj
  unfold classSum at hall
  rw [filter_filter]
  rw [← hall]
  refine sum_congr ?_ (fun _ _ => rfl)
  ext k
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨by rw [h]; exact hpj, h⟩

/-! ## Instance: the (1, 8, 26)/35 tile (p = 7, r = 1, m = 5): R(a) = R₀(a). Computed by no
engine — derived from the chain above. -/
theorem instance_35 : relSpace (7 ^ 1 * 5) ![1, 8, 26] = trivSpace (7 ^ 1 * 5) ![1, 8, 26] := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact lemmaS_odd (p := 7) (r := 1) (m := 5) (by norm_num) le_rfl (by norm_num) (by norm_num)
    _ (fun _ _ h => by omega) (by decide) (by decide) (by decide)

#print axioms Erdos634.LemmaSOdd.lemmaS_odd
#print axioms Erdos634.LemmaSOdd.instance_35

end Erdos634.LemmaSOdd
