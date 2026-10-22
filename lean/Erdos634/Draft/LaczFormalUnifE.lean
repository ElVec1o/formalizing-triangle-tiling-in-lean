-- Draft/LaczFormalUnifE.lean -- NEGATIVE CONTROL for the bound `200 < n` of `claimQ` / `no_big` / `shapes_of_K_uniform`:
-- at n = 60 the tile (10,13,37) with corner column sums F = (6,0,0) satisfies the corner equation F . x'(k) = 1 at EVERY unit k
-- (Laczkovich's exceptional n = 60 triples; F_0 a_0 = 60 as required), so the other hypotheses of `claimQ` hold and only `200 < n` fails.
-- UNAUDITED (NOTE).  Credit: Laczkovich (Discrete Math 140 (1995) p. 92), Beeson-Rosu.
import Erdos634.Draft.LaczFormalUnifB

open scoped BigOperators
open Erdos634.LemmaKStar

namespace Erdos634.Draft.LaczFormal

theorem yv_mod (n : ℕ) (a : Fin 3 → ℕ) (hn : 0 < n) (k : ℤ) (i : Fin 3) :
    yv n a k i = yv n a (k % n) i := by
  unfold yv
  rw [Int.fract_div_intCast_eq_div_intCast_mod, Int.fract_div_intCast_eq_div_intCast_mod]
  congr 2
  exact ((Int.mod_modEq k n).mul_right _).symm

theorem sT_mod (n : ℕ) (a : Fin 3 → ℕ) (hn : 0 < n) (k : ℤ) : sT n a k = sT n a (k % n) := by
  unfold sT; exact Finset.sum_congr rfl fun i _ => yv_mod n a hn k i

theorem xp_mod (n : ℕ) (a : Fin 3 → ℕ) (hn : 0 < n) (k : ℤ) (i : Fin 3) : xp n a k i = xp n a (k % n) i := by
  unfold xp; rw [sT_mod n a hn k, yv_mod n a hn k i]

theorem claimQ_control :
    ∀ k : ℤ, Int.gcd k 60 = 1 →
      ∑ l, (((![6, 0, 0] : Fin 3 → ℕ) l : ℕ) : ℚ) * xp 60 ![10, 13, 37] k l = 1 := by
  intro k hk
  rw [Fin.sum_univ_three]
  simp only [xp_mod 60 ![10, 13, 37] (by norm_num) k]
  have hm0 : 0 ≤ k % (60 : ℕ) := Int.emod_nonneg _ (by norm_num)
  have hm1 : k % (60 : ℕ) < 60 := Int.emod_lt_of_pos _ (by norm_num)
  have hg : Int.gcd (k % (60 : ℕ)) 60 = 1 := by
    rw [← hk]; simp [Int.gcd_emod]
  generalize k % (60 : ℕ) = m at hm0 hm1 hg
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hm0
  have hm1' : m < 60 := by exact_mod_cast hm1
  interval_cases m <;> first
    | (exfalso; revert hg; decide)
    | (simp [xp, sT, yv, Fin.sum_univ_three, Int.fract_div_intCast_eq_div_intCast_mod]; norm_num)

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.claimQ_control
