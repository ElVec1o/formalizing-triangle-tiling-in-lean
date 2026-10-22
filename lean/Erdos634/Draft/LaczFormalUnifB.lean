-- Draft/LaczFormalUnifB.lean -- UNIFORM arithmetic classification of the corner column sums F (Laczkovich, Discrete Math 140 (1995), Thm 5.1, for n > 200, 5-smooth):
-- from `F . x'(k) = 1` at every unit k (`R1_conj_eq`) and `F . a = n`, with F having a zero entry, F is one of (2,1,0), (1,2,0), (2,2,0) up to order.
-- Route: F_i >= 3 => x'_i <= 1/3 (`R1_bound`) => Lemma 5.2 (`lacz_lemma_5_2_values`) => gcd bookkeeping => either contradiction (F_j >= 1) or F = (p,0,0), p in {3,4,6,10},
-- killed by the explicit unit of `Q_core` (`claimQ`).  No interior-vertex equation and no orientation-sign lemma are needed (K1 replaces them).
-- UNAUDITED (NOTE).  Credit: Laczkovich (Discrete Math 140 (1995) Thm 5.1, Lemma 5.2; DCG 48 (2012)), Beeson-Rosu, Beeson.
import Erdos634.Draft.LaczFormalUnifA
import Erdos634.Draft.LaczFormalR1
import Erdos634.Draft.LaczFormalLem52
import Erdos634.Draft.CaseALemmaF

open scoped BigOperators
open Erdos634.LemmaKStar Erdos634.LemmaF

namespace Erdos634.Draft.LaczFormal

variable {n : ℕ} {a : Fin 3 → ℕ}

theorem fract_of_eq (m c w : ℤ) (n : ℕ) (hn : 0 < n) (hc0 : 0 ≤ c) (hcn : c < n) (hm : m = c + n * w) :
    Int.fract ((m : ℚ) / n) = (c : ℚ) / n := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have : (m : ℚ) / n = (c : ℚ) / n + (w : ℚ) := by
    rw [hm]; push_cast; field_simp
  rw [this, Int.fract_add_intCast]
  apply Int.fract_eq_self.mpr
  constructor
  · positivity
  · rw [div_lt_one (by exact_mod_cast hn)]; exact_mod_cast hcn

/-- `R1_bound` from the equation alone. -/
theorem xp_le_third {F : Fin 3 → ℕ} {k : ℤ} (hk : Int.gcd k n = 1) (hn : 0 < n) (hpos : ∀ i, 1 ≤ a i)
    (hsum : ∑ i, a i = n) (h : ∑ i, (F i : ℚ) * xp n a k i = 1) (i : Fin 3) (hF : 3 ≤ F i) :
    xp n a k i ≤ 1 / 3 := by
  rw [Fin.sum_univ_three] at h
  have b0 := xp_bounds hk hn hpos hsum 0
  have b1 := xp_bounds hk hn hpos hsum 1
  have b2 := xp_bounds hk hn hpos hsum 2
  have hF' : (3 : ℚ) ≤ F i := by exact_mod_cast hF
  have c0 : 0 ≤ (F 0 : ℚ) * xp n a k 0 := mul_nonneg (by positivity) b0.1
  have c1 : 0 ≤ (F 1 : ℚ) * xp n a k 1 := mul_nonneg (by positivity) b1.1
  have c2 : 0 ≤ (F 2 : ℚ) * xp n a k 2 := mul_nonneg (by positivity) b2.1
  have hi : (F i : ℚ) * xp n a k i ≤ 1 := by
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by fin_cases i <;> simp) with rfl | rfl | rfl <;> linarith
  have hx := (xp_bounds hk hn hpos hsum i).1
  nlinarith

/-- **Four values.**  `F_i >= 3` and the equation at every unit force `a_i/n in {1/3, 1/4, 1/6, 1/10, 3/10}`. -/
theorem four_values {F : Fin 3 → ℕ} (hn : 0 < n) (hpos : ∀ i, 1 ≤ a i) (hsum : ∑ i, a i = n)
    (hFa : ∑ l, F l * a l = n) (hR : ∀ k : ℤ, Int.gcd k n = 1 → ∑ l, (F l : ℚ) * xp n a k l = 1)
    (i : Fin 3) (h3 : 3 ≤ F i) :
    n = 3 * a i ∨ n = 4 * a i ∨ n = 6 * a i ∨ n = 10 * a i ∨ 10 * a i = 3 * n := by
  have hle : F i * a i ≤ n := by
    rw [← hFa]
    exact Finset.single_le_sum (f := fun l => F l * a l) (fun l _ => Nat.zero_le _) (Finset.mem_univ i)
  have h3a : 3 * a i ≤ n := le_trans (Nat.mul_le_mul_right _ h3) hle
  have hai := hpos i
  refine lacz_lemma_5_2_values (by omega) (by omega) h3a ?_
  intro k hk
  have hk1 : Nat.Coprime k n := Nat.Coprime.coprime_dvd_right (Dvd.intro_left 2 rfl) hk
  have hkz : Int.gcd (k : ℤ) n = 1 := by rw [Int.gcd_natCast_natCast]; exact hk1
  have hb := xp_le_third hkz hn hpos hsum (hR (k : ℤ) hkz) i h3
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hy : yv n a (k : ℤ) i = (((k * a i) % n : ℕ) : ℚ) / n := by
    unfold yv
    have : (((k : ℤ) * (a i : ℤ) : ℤ) : ℚ) = ((k * a i : ℕ) : ℚ) := by push_cast; ring
    rw [this, Int.fract_div_natCast_eq_div_natCast_mod]
  unfold xp at hb
  split_ifs at hb
  · left
    rw [hy, div_le_iff₀ hn'] at hb
    have : (3 * (((k * a i) % n : ℕ) : ℚ)) ≤ n := by linarith
    exact_mod_cast this
  · right
    rw [hy] at hb
    have : (2 * n : ℚ) ≤ 3 * (((k * a i) % n : ℕ) : ℚ) := by
      have h1 : 2 / 3 ≤ (((k * a i) % n : ℕ) : ℚ) / n := by linarith
      rw [le_div_iff₀ hn'] at h1; linarith
    exact_mod_cast this

/-- If a common divisor divides all three tile angles it is 1. -/
theorem gcd_one_of_all {i j r : Fin 3} (hij : i ≠ j) (hir : i ≠ r) (hjr : j ≠ r)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) {g : ℕ} (hi : g ∣ a i) (hj : g ∣ a j) (hr : g ∣ a r) : g = 1 := by
  have hall : ∀ l, g ∣ a l := by
    intro l
    rcases cover i j r hij hir hjr l with rfl | rfl | rfl <;> assumption
  have : g ∣ Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) :=
    Nat.dvd_gcd (hall 0) (Nat.dvd_gcd (hall 1) (hall 2))
  rw [hgcd] at this
  exact Nat.dvd_one.mp this

/-- **Claim Q.**  `F = (p,0,0)` with `p in {3,4,6,10}`: contradiction for `n > 200` (5-smooth, primitive). -/
theorem claimQ {F : Fin 3 → ℕ} {i j r : Fin 3} (hij : i ≠ j) (hir : i ≠ r) (hjr : j ≠ r)
    (hn : 200 < n) (hsm : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ℓ ≤ 5) (hpos : ∀ l, 1 ≤ a l)
    (hsum : ∑ l, a l = n) (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (hFi : F i * a i = n) (hFj : F j = 0) (hFr : F r = 0) (hp : F i = 3 ∨ F i = 4 ∨ F i = 6 ∨ F i = 10)
    (hR : ∀ k : ℤ, Int.gcd k n = 1 → ∑ l, (F l : ℚ) * xp n a k l = 1) : False := by
  set p := F i with hpdef
  have hp3 : 3 ≤ p := by rcases hp with h | h | h | h <;> omega
  have hp10 : p ≤ 10 := by rcases hp with h | h | h | h <;> omega
  have hai21 : 21 ≤ a i := by
    by_contra hlt
    push_neg at hlt
    have : p * a i ≤ 10 * 20 := Nat.mul_le_mul hp10 (by omega)
    omega
  have hsa : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ a i → ℓ ≤ 5 := fun ℓ hℓ hd =>
    hsm ℓ hℓ (dvd_trans hd (Dvd.intro_left p hFi))
  have hs3 : a i + a j + a r = n := by rw [← hsum]; exact (sum3 a hij hir hjr).symm
  have hain : a i ∣ n := Dvd.intro_left p hFi
  have hcop : Nat.Coprime (a i) (a j) := by
    have hgi : Nat.gcd (a i) (a j) ∣ a i := Nat.gcd_dvd_left _ _
    have hgj : Nat.gcd (a i) (a j) ∣ a j := Nat.gcd_dvd_right _ _
    have hsumij : Nat.gcd (a i) (a j) ∣ a i + a j := dvd_add hgi hgj
    have hn' : Nat.gcd (a i) (a j) ∣ n := dvd_trans hgi hain
    have hgr : Nat.gcd (a i) (a j) ∣ a r := by
      rw [← hs3] at hn'
      exact (Nat.dvd_add_right hsumij).mp (by simpa [add_assoc] using hn')
    exact gcd_one_of_all hij hir hjr hgcd hgi hgj hgr
  obtain ⟨i0, hi1, hi19, hdiv, hi0⟩ := pick_i (p := p) (a := a i) (b := a j) hp hsa hcop
  obtain ⟨k, t, w, hk, hkb, hkc⟩ := Q_core (by omega) (by omega) hcop hdiv hi0
  have hn0 : 0 < n := by omega
  have hcast : ((p * a i : ℕ) : ℤ) = (n : ℤ) := by exact_mod_cast hFi
  rw [hcast] at hkb hkc
  have hkg : Int.gcd k n = 1 := Int.isCoprime_iff_gcd_eq_one.mp hkc
  have hnp' : (p : ℤ) * a i = n := by exact_mod_cast hFi
  have hp3Z : (3 : ℤ) ≤ p := by exact_mod_cast hp3
  have hAZ : (21 : ℤ) ≤ a i := by exact_mod_cast hai21
  have hAn : (a i : ℤ) + 2 * a i ≤ n := by nlinarith
  have h1 : k * (a i : ℤ) = n * t - a i := by rw [hk]; linear_combination t * hnp'
  have h2 : k * (a j : ℤ) = i0 + n * w := hkb
  have hyi : yv n a k i = ((n - a i : ℤ) : ℚ) / n := by
    unfold yv
    refine fract_of_eq _ _ (t - 1) n hn0 (by omega) (by omega) ?_
    rw [h1]; ring
  have hyj : yv n a k j = (i0 : ℚ) / n := by
    unfold yv
    have := fract_of_eq (k * a j) (i0 : ℤ) w n hn0 (by omega) (by omega) h2
    simpa using this
  have har : (a r : ℤ) = n - a i - a j := by omega
  have hyr : yv n a k r = ((a i - i0 : ℤ) : ℚ) / n := by
    unfold yv
    refine fract_of_eq _ _ (k - t - w) n hn0 (by omega) (by omega) ?_
    rw [har]
    calc k * ((n : ℤ) - a i - a j) = n * k - k * a i - k * a j := by ring
      _ = (a i - i0) + n * (k - t - w) := by rw [h1, h2]; ring
  have hsT : sT n a k = 1 := by
    unfold sT
    rw [sum3 (fun l => yv n a k l) hij hir hjr, hyi, hyj, hyr]
    have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn0.ne'
    field_simp
    push_cast
    ring
  have hxp : ∀ l, xp n a k l = yv n a k l := fun l => by unfold xp; rw [if_pos hsT]
  have h := hR k hkg
  rw [sum3 (fun l => (F l : ℚ) * xp n a k l) hij hir hjr, hFj, hFr, hxp i, hyi] at h
  have hnq : (n : ℚ) = p * a i := by exact_mod_cast hFi.symm
  have hai' : (a i : ℚ) ≠ 0 := by exact_mod_cast (by omega : a i ≠ 0)
  have hp3' : (3 : ℚ) ≤ p := by exact_mod_cast hp3
  push_cast at h
  rw [hnq] at h
  field_simp at h
  nlinarith

/-- From `F_i >= 3` (with a zero entry `F_r`): a divisor `D >= n/10` of `a_i` dividing `F_j`. -/
theorem big_div {F : Fin 3 → ℕ} {i j r : Fin 3} (hij : i ≠ j) (hir : i ≠ r) (hjr : j ≠ r)
    (hn : 200 < n) (hpos : ∀ l, 1 ≤ a l) (hsum : ∑ l, a l = n) (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (hFa : ∑ l, F l * a l = n) (hR : ∀ k : ℤ, Int.gcd k n = 1 → ∑ l, (F l : ℚ) * xp n a k l = 1)
    (hFr : F r = 0) (h3 : 3 ≤ F i) : ∃ D, n ≤ 10 * D ∧ D ∣ a i ∧ D ∣ F j := by
  have hn0 : 0 < n := by omega
  have hFa2 : F i * a i + F j * a j = n := by
    rw [sum3 (fun l => F l * a l) hij hir hjr, hFr] at hFa; simpa using hFa
  have hs3 : a i + a j + a r = n := by rw [← hsum]; exact (sum3 a hij hir hjr).symm
  have hv := four_values hn0 hpos hsum hFa hR i h3
  obtain ⟨D, hD10, hDa, hDn⟩ : ∃ D, n ≤ 10 * D ∧ D ∣ a i ∧ D ∣ n := by
    rcases hv with h | h | h | h | h
    · exact ⟨a i, by omega, dvd_refl _, ⟨3, by omega⟩⟩
    · exact ⟨a i, by omega, dvd_refl _, ⟨4, by omega⟩⟩
    · exact ⟨a i, by omega, dvd_refl _, ⟨6, by omega⟩⟩
    · exact ⟨a i, by omega, dvd_refl _, ⟨10, by omega⟩⟩
    · exact ⟨n / 10, by omega, ⟨3, by omega⟩, ⟨10, by omega⟩⟩
  refine ⟨D, hD10, hDa, ?_⟩
  have hDF : D ∣ F j * a j := by
    have h1 : D ∣ F i * a i := Dvd.dvd.mul_left hDa _
    rw [← hFa2] at hDn
    exact (Nat.dvd_add_right h1).mp hDn
  have hcop : Nat.Coprime D (a j) := by
    have hgi : Nat.gcd D (a j) ∣ a i := dvd_trans (Nat.gcd_dvd_left _ _) hDa
    have hgj : Nat.gcd D (a j) ∣ a j := Nat.gcd_dvd_right _ _
    have hn' : Nat.gcd D (a j) ∣ n := dvd_trans (Nat.gcd_dvd_left _ _) hDn
    have hgr : Nat.gcd D (a j) ∣ a r := by
      rw [← hs3] at hn'
      exact (Nat.dvd_add_right (dvd_add hgi hgj)).mp hn'
    exact gcd_one_of_all hij hir hjr hgcd hgi hgj hgr
  exact hcop.dvd_of_dvd_mul_right hDF

/-- **No large corner sum.**  With a zero entry `F_r = 0`, no `F_i >= 3`: contradiction for `n > 200` (5-smooth, primitive). -/
theorem no_big {F : Fin 3 → ℕ} {i j r : Fin 3} (hij : i ≠ j) (hir : i ≠ r) (hjr : j ≠ r)
    (hn : 200 < n) (hsm : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ℓ ≤ 5) (hpos : ∀ l, 1 ≤ a l)
    (hsum : ∑ l, a l = n) (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (hFa : ∑ l, F l * a l = n) (hR : ∀ k : ℤ, Int.gcd k n = 1 → ∑ l, (F l : ℚ) * xp n a k l = 1)
    (hFr : F r = 0) (h3 : 3 ≤ F i) : False := by
  have hn0 : 0 < n := by omega
  have hFa2 : F i * a i + F j * a j = n := by
    rw [sum3 (fun l => F l * a l) hij hir hjr, hFr] at hFa; simpa using hFa
  obtain ⟨D, hD10, hDa, hDF⟩ := big_div hij hir hjr hn hpos hsum hgcd hFa hR hFr h3
  rcases Nat.eq_zero_or_pos (F j) with hFj | hFj
  · -- F = (p,0,0)
    rw [hFj] at hFa2
    have hFi : F i * a i = n := by simpa using hFa2
    have hv := four_values hn0 hpos hsum hFa hR i h3
    have hai := hpos i
    have hp : F i = 3 ∨ F i = 4 ∨ F i = 6 ∨ F i = 10 := by
      rcases hv with h | h | h | h | h
      · left; exact Nat.eq_of_mul_eq_mul_right hai (by rw [hFi]; omega)
      · right; left; exact Nat.eq_of_mul_eq_mul_right hai (by rw [hFi]; omega)
      · right; right; left; exact Nat.eq_of_mul_eq_mul_right hai (by rw [hFi]; omega)
      · right; right; right; exact Nat.eq_of_mul_eq_mul_right hai (by rw [hFi]; omega)
      · exfalso
        have h1 : 10 * (F i * a i) = F i * (10 * a i) := by ring
        rw [hFi, h] at h1
        have h2 : n * 10 = n * (F i * 3) := by linarith
        have h3' := Nat.eq_of_mul_eq_mul_left hn0 h2
        omega
    exact claimQ hij hir hjr hn hsm hpos hsum hgcd hFi hFj hFr hp hR
  · have hDle : D ≤ F j := Nat.le_of_dvd hFj hDF
    have h3j : 3 ≤ F j := by omega
    obtain ⟨D', hD'10, hD'a, hD'F⟩ := big_div hij.symm hjr hir hn hpos hsum hgcd hFa hR hFr h3j
    have hFi : 0 < F i := by omega
    have h1 : D' ≤ F i := Nat.le_of_dvd hFi hD'F
    have h2 : D ≤ a i := Nat.le_of_dvd (hpos i) hDa
    have h4 : D' * D ≤ n := le_trans (Nat.mul_le_mul h1 h2) (le_trans (Nat.le_add_right _ _) hFa2.le)
    nlinarith

/-- **Shapes, uniform.**  For `n > 200` with only prime factors `<= 5` and a primitive tile, Lemma K's conclusion (`K1 /\ K2` at every unit) gives
`ABC ~ T` or half-isosceles, with NO appeal to Lemma S, certificates or the exceptional tables. -/
theorem shapes_of_K_uniform {f : Fin 3 → Fin 3 → ℕ} (hn : 200 < n) (hsm : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ℓ ≤ 5)
    (hpos : ∀ i, 1 ≤ a i) (hsum : ∑ i, a i = n) (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (hf : ∀ j, f j ≠ 0) (hu : ∑ j, uu a f j = n)
    (hK : ∀ k : ℤ, Int.gcd k n = 1 → K1 n a f k ∧ K2 n a f k) :
    LemmaF.Similar a f ∨ HalfIso n a f := by
  have hn0 : 0 < n := by omega
  have hFa : ∑ l, FF f l * a l = n := by
    rw [← hu]
    simp only [uu, FF, Finset.sum_mul]
    exact Finset.sum_comm
  have hR : ∀ k : ℤ, Int.gcd k n = 1 → ∑ l, (FF f l : ℚ) * xp n a k l = 1 := fun k hk =>
    R1_conj_eq hk hn0 hpos hsum (hK k hk).1 (hK k hk).2
  by_cases hz : ∃ r, FF f r = 0
  · obtain ⟨r, hr⟩ := hz
    -- generic zero-case lemma on (i, j, r)
    have key : ∀ {i j r : Fin 3}, i ≠ j → i ≠ r → j ≠ r → FF f r = 0 → LemmaF.Similar a f ∨ HalfIso n a f := by
      intro i j r hij hir hjr hFr
      have hFa2 : FF f i * a i + FF f j * a j = n := by
        rw [sum3 (fun l => FF f l * a l) hij hir hjr, hFr] at hFa; simpa using hFa
      have hs3 : a i + a j + a r = n := by rw [← hsum]; exact (sum3 a hij hir hjr).symm
      have hFi2 : FF f i ≤ 2 := by
        by_contra h; push_neg at h
        exact no_big hij hir hjr hn hsm hpos hsum hgcd hFa hR hFr h
      have hFj2 : FF f j ≤ 2 := by
        by_contra h; push_neg at h
        exact no_big hij.symm hjr hir hn hsm hpos hsum hgcd hFa hR hFr h
      have hm := mass_ge hf
      rw [sum3 (FF f) hij hir hjr, hFr] at hm
      have hcases : (FF f i = 2 ∧ FF f j = 1) ∨ (FF f i = 1 ∧ FF f j = 2) ∨ (FF f i = 2 ∧ FF f j = 2) := by omega
      rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        have hM : ∑ l, FF f l = 3 := by rw [sum3 (FF f) hij hir hjr, hFr, h1, h2]
        intro x
        rw [count_mass3 hf hM x, sum3 (fun l => FF f l * (if a l = x then 1 else 0)) hij hir hjr, hFr, h1, h2, sum3 (fun l => if a l = x then 1 else 0) hij hir hjr]
        rw [h1, h2] at hFa2
        have : a r = a i := by omega
        rw [this]
        split_ifs <;> omega
      · left
        have hM : ∑ l, FF f l = 3 := by rw [sum3 (FF f) hij hir hjr, hFr, h1, h2]
        intro x
        rw [count_mass3 hf hM x, sum3 (fun l => FF f l * (if a l = x then 1 else 0)) hij hir hjr, hFr, h1, h2, sum3 (fun l => if a l = x then 1 else 0) hij hir hjr]
        rw [h1, h2] at hFa2
        have : a r = a j := by omega
        rw [this]
        split_ifs <;> omega
      · rw [h1, h2] at hFa2
        exact right_case hij hir hjr (by omega) (by omega) hf hFr h1 h2
    have hr3 : r = 0 ∨ r = 1 ∨ r = 2 := by fin_cases r <;> simp
    rcases hr3 with rfl | rfl | rfl
    · exact key (i := 1) (j := 2) (by decide) (by decide) (by decide) hr
    · exact key (i := 0) (j := 2) (by decide) (by decide) (by decide) hr
    · exact key (i := 0) (j := 1) (by decide) (by decide) (by decide) hr
  · push_neg at hz
    left
    have hge : ∀ l, a l ≤ FF f l * a l := fun l => Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (hz l))
    have hsum' := hsum
    rw [Fin.sum_univ_three] at hsum' hFa
    have e0 := hge 0; have e1 := hge 1; have e2 := hge 2
    have hall : ∀ l, FF f l = 1 := by
      intro l
      have hl : FF f l * a l = a l := by
        fin_cases l <;> simp <;> omega
      exact Nat.eq_of_mul_eq_mul_right (hpos l) (by simpa using hl)
    have hM : ∑ l, FF f l = 3 := by simp [hall]
    intro x
    rw [count_mass3 hf hM x]
    simp [hall]

end Erdos634.Draft.LaczFormal
