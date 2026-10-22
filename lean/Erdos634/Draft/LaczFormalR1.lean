-- Draft/LaczFormalR1.lean -- stage R1 of the L9 residue plan (PLAN_L9_L7.md): from Lemma K's conjugate-angle equalities K1 and K2 (for one
-- unit k) to Laczkovich's conjugate equation  p x'_0 + q x'_1 + r x'_2 = 1  (p, q, r = the column sums F of the corner figures), i.e. his
-- "p alpha' + q beta' + r gamma' = pi" of Thm 5.1 (p. 91), and the consequence  F_i >= 3  =>  x'_i <= 1/3.
-- Pure arithmetic on `LemmaKStar` data.  UNAUDITED.  Credit: Laczkovich (1995, Thm 5.1 proof).
import Erdos634.Draft.CaseALemmaKStar

open scoped BigOperators
open Erdos634.LemmaKStar

namespace Erdos634.Draft.LaczFormal

variable {n : ℕ} {a : Fin 3 → ℕ} {f : Fin 3 → Fin 3 → ℕ}

theorem yv_lt_one (k : ℤ) (i : Fin 3) (hn : 0 < n) : 0 ≤ yv n a k i ∧ yv n a k i < 1 := by
  unfold yv; exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem yv_pos {k : ℤ} (hk : Int.gcd k n = 1) (hn : 0 < n) (i : Fin 3) (hai : 0 < a i) (hlt : a i < n) :
    0 < yv n a k i := by
  unfold yv
  rcases (Int.fract_nonneg (((k * (a i : ℤ) : ℤ) : ℚ) / n)).lt_or_eq with h | h
  · exact h
  · exfalso
    have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    obtain ⟨m, hm⟩ := Int.fract_eq_zero_iff.mp h.symm
    have h1 : ((k * (a i : ℤ) : ℤ) : ℚ) = (m * n : ℤ) := by
      push_cast; push_cast at hm
      field_simp at hm; linarith
    have h2 : k * (a i : ℤ) = m * n := by exact_mod_cast h1
    have hcop : IsCoprime k (n : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hk
    have hdvd : (n : ℤ) ∣ (a i : ℤ) := by
      have : (n : ℤ) ∣ k * (a i : ℤ) := ⟨m, by rw [h2]; ring⟩
      exact (hcop.symm).dvd_of_dvd_mul_left this
    have := Int.le_of_dvd (by exact_mod_cast hai) hdvd
    omega

theorem sT_eq_one_or_two {k : ℤ} (hk : Int.gcd k n = 1) (hn : 0 < n) (hpos : ∀ i, 1 ≤ a i)
    (hsum : ∑ i, a i = n) : sT n a k = 1 ∨ sT n a k = 2 := by
  have hlt : ∀ i, a i < n := by
    intro i
    rw [← hsum, Fin.sum_univ_three]
    have := hpos 0; have := hpos 1; have := hpos 2
    fin_cases i <;> simp <;> omega
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hint : ∃ m : ℤ, sT n a k = m := by
    refine ⟨k - ∑ i, ⌊((k * (a i : ℤ) : ℤ) : ℚ) / n⌋, ?_⟩
    unfold sT yv
    simp only [Int.fract]
    rw [Finset.sum_sub_distrib]
    have : ∑ i, ((k * (a i : ℤ) : ℤ) : ℚ) / n = k := by
      rw [← Finset.sum_div]
      have : ∑ i, ((k * (a i : ℤ) : ℤ) : ℚ) = k * n := by
        push_cast
        rw [← Finset.mul_sum]
        have : ∑ i, (a i : ℚ) = n := by exact_mod_cast hsum
        rw [this]
      rw [this]; field_simp
    rw [this]; push_cast; ring
  obtain ⟨m, hm⟩ := hint
  have hlo : 0 < sT n a k := by
    unfold sT
    exact Finset.sum_pos (fun i _ => yv_pos hk hn i (hpos i) (hlt i)) ⟨0, Finset.mem_univ _⟩
  have hhi : sT n a k < 3 := by
    unfold sT
    calc ∑ i, yv n a k i < ∑ _i : Fin 3, (1 : ℚ) :=
          Finset.sum_lt_sum (fun i _ => (yv_lt_one k i hn).2.le) ⟨0, Finset.mem_univ _, (yv_lt_one k 0 hn).2⟩
      _ = 3 := by simp
  rw [hm] at hlo hhi ⊢
  have h1 : (0 : ℤ) < m := by exact_mod_cast hlo
  have h2 : m < 3 := by exact_mod_cast hhi
  have : m = 1 ∨ m = 2 := by omega
  rcases this with rfl | rfl
  · left; norm_num
  · right; norm_num

theorem xp_bounds {k : ℤ} (hk : Int.gcd k n = 1) (hn : 0 < n) (hpos : ∀ i, 1 ≤ a i)
    (hsum : ∑ i, a i = n) (i : Fin 3) : 0 ≤ xp n a k i ∧ xp n a k i ≤ 1 := by
  have := yv_lt_one (a := a) k i hn
  unfold xp
  split_ifs
  · exact ⟨this.1, this.2.le⟩
  · constructor <;> linarith [this.2]

/-- **R1.**  K1 and K2 at a unit `k` give Laczkovich's conjugate equation `F · x'(k) = 1`. -/
theorem R1_conj_eq {k : ℤ} (hk : Int.gcd k n = 1) (hn : 0 < n) (hpos : ∀ i, 1 ≤ a i)
    (hsum : ∑ i, a i = n) (hK1 : K1 n a f k) (hK2 : K2 n a f k) :
    ∑ i, (FF f i : ℚ) * xp n a k i = 1 := by
  have hsw : ∑ i, (FF f i : ℚ) * xp n a k i = ∑ j, xpu n a f k j := by
    have : ∑ i, (FF f i : ℚ) * xp n a k i = ∑ j, ∑ i, (f j i : ℚ) * xp n a k i := by
      unfold FF
      push_cast
      simp_rw [Finset.sum_mul]
      exact Finset.sum_comm
    rw [this]
    exact Finset.sum_congr rfl (fun j _ => hK2 j)
  rw [hsw]
  unfold K1 at hK1
  rcases sT_eq_one_or_two hk hn hpos hsum with h1 | h2
  · have : ∑ j, xpu n a f k j = ∑ j, xv n a f k j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      unfold xpu; rw [if_pos h1]
    rw [this]; change sABC n a f k = 1
    rw [← hK1]; exact h1
  · have : ∑ j, xpu n a f k j = ∑ j, (1 - xv n a f k j) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      unfold xpu; rw [if_neg (by rw [h2]; norm_num)]
    rw [this, Finset.sum_sub_distrib]
    have : ∑ j, xv n a f k j = 2 := by
      change sABC n a f k = 2
      rw [← hK1]; exact h2
    rw [this]; simp; norm_num

/-- **R1, bound.**  If the column sum `F_i >= 3` then `x'_i(k) <= 1/3`. -/
theorem R1_bound {k : ℤ} (hk : Int.gcd k n = 1) (hn : 0 < n) (hpos : ∀ i, 1 ≤ a i)
    (hsum : ∑ i, a i = n) (hK1 : K1 n a f k) (hK2 : K2 n a f k) (i : Fin 3) (hF : 3 ≤ FF f i) :
    xp n a k i ≤ 1 / 3 := by
  have h := R1_conj_eq hk hn hpos hsum hK1 hK2
  rw [Fin.sum_univ_three] at h
  have b0 := xp_bounds hk hn hpos hsum 0
  have b1 := xp_bounds hk hn hpos hsum 1
  have b2 := xp_bounds hk hn hpos hsum 2
  have hF' : (3 : ℚ) ≤ FF f i := by exact_mod_cast hF
  have c0 : 0 ≤ (FF f 0 : ℚ) * xp n a k 0 := mul_nonneg (by positivity) b0.1
  have c1 : 0 ≤ (FF f 1 : ℚ) * xp n a k 1 := mul_nonneg (by positivity) b1.1
  have c2 : 0 ≤ (FF f 2 : ℚ) * xp n a k 2 := mul_nonneg (by positivity) b2.1
  have hi : (FF f i : ℚ) * xp n a k i ≤ 1 := by
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by fin_cases i <;> simp) with rfl | rfl | rfl <;> linarith
  have hx := (xp_bounds hk hn hpos hsum i).1
  nlinarith

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.R1_conj_eq
#print axioms Erdos634.Draft.LaczFormal.R1_bound
