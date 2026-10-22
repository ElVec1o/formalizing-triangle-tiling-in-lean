-- Draft/LaczFormal51Gen1.lean -- Laczkovich (Discrete Math 140 (1995)) Thm 5.1, the ARITHMETIC CORE for every denominator n (tile (alpha, beta, 2 alpha + beta), 3 alpha + 2 beta = pi).
--   `kstar_frac` : KStar + a corner count P_l >= 3  ==>  {k a_l / n} <= 1/3 or >= 2/3 for every k prime to 2n   (the printed "p alpha' <= pi");
--   `n_small`    : Lemma 5.2 (`Lacz51.lemma52`) for that angle + the family relation  ==>  Covered n  (n | 2*{3,4,6,10} or 3*{3,4,6,10});
--   `uncov_core` : for n NOT Covered, the target angles are a permutation of the tile angles, or some tile angle is pi/2 (n = 2 a_l).
-- NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) Thm 5.1, Lemma 5.2; Combinatorica 10 (1990)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormal51L52
import Erdos634.Draft.LaczFormal51Cov
import Erdos634.Draft.CaseALemmaKStar

open scoped BigOperators Classical
open Erdos634.LemmaKStar Erdos634.Draft.LaczFormal

namespace Erdos634.Lacz51Gen

theorem coprime2_gcd {n k : ℕ} (hk : Nat.Coprime k (2 * n)) : Int.gcd (k : ℤ) n = 1 := by
  have h : Nat.Coprime k n := Nat.Coprime.coprime_dvd_right (Dvd.intro_left 2 rfl) hk
  simpa [Int.gcd_natCast_natCast] using h

/-- **Printed: "`p alpha' <= pi` for the conjugate tiling".**  `P_l = FF f l >= 3` forces `{k a_l / n} <= 1/3` or `>= 2/3`. -/
theorem kstar_frac {n : ℕ} {a : Fin 3 → ℕ} {f : Fin 3 → Fin 3 → ℕ} (hsum : ∑ i, a i = n) (ha : ∀ i, 1 ≤ a i)
    (hK : KStar n a f) (l : Fin 3) (hl : 3 ≤ FF f l) (k : ℕ) (hk : Nat.Coprime k (2 * n)) :
    3 * ((k * a l) % n) ≤ n ∨ 2 * n ≤ 3 * ((k * a l) % n) := by
  have hn : 0 < n := by have := a_lt hsum ha 0; omega
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  have hk' := coprime2_gcd hk
  have yval : ∀ κ : ℤ, κ = (k : ℤ) → yv n a κ l = (((k * a l) % n : ℕ) : ℚ) / n := by
    intro κ hκ
    subst hκ
    unfold yv
    have : ((((k : ℤ) * (a l : ℤ) : ℤ)) : ℚ) = ((k * a l : ℕ) : ℚ) := by push_cast; ring
    rw [this]
    exact Int.fract_div_natCast_eq_div_natCast_mod
  have bound : ∀ κ : ℤ, Int.gcd κ n = 1 → sT n a κ = 1 → 3 * yv n a κ l ≤ 1 := by
    intro κ hκ h1
    have hk1 := hK κ hκ h1
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ (FF f i : ℚ) * yv n a κ i := fun i _ =>
      mul_nonneg (by positivity) (Int.fract_nonneg _)
    have := Finset.single_le_sum hnn (Finset.mem_univ l)
    rw [hk1] at this
    have h3 : (3 : ℚ) ≤ FF f l := by exact_mod_cast hl
    nlinarith [Int.fract_nonneg (((κ * (a l : ℤ) : ℤ) : ℚ) / n), (show yv n a κ l = Int.fract (((κ * (a l : ℤ) : ℤ) : ℚ) / n) from rfl)]
  rcases sT_12 hsum ha hk' with h | h
  · left
    have := bound (k : ℤ) hk' h
    rw [yval _ rfl] at this
    have h2 : (3 : ℚ) * ((((k * a l) % n : ℕ)) : ℚ) ≤ n := by
      have := mul_le_mul_of_nonneg_left this hnq.le
      field_simp at this
      linarith
    exact_mod_cast h2
  · right
    have hneg := gcd_neg' (n := n) hk'
    have hs : sT n a (-(k : ℤ)) = 1 := by rw [sT_neg hsum ha hk', h]; norm_num
    have := bound _ hneg hs
    rw [yv_neg hsum ha hk' l, yval _ rfl] at this
    have h2 : (2 : ℚ) * n ≤ 3 * ((((k * a l) % n : ℕ)) : ℚ) := by
      have h4 : (3 : ℚ) * (1 - ((((k * a l) % n : ℕ)) : ℚ) / n) ≤ 1 := this
      have h5 : (1 - ((((k * a l) % n : ℕ)) : ℚ) / n) = (n - (((k * a l) % n : ℕ) : ℚ)) / n := by field_simp
      rw [h5] at h4
      have := mul_le_mul_of_nonneg_left (show 3 * ((n - (((k * a l) % n : ℕ) : ℚ)) / n) ≤ 1 from by linarith) hnq.le
      field_simp at this
      linarith
    exact_mod_cast h2

theorem covered_small (n : ℕ) (h : n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 12 ∨ n = 18 ∨ n = 20 ∨ n = 30) :
    Covered n := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Covered, CertN2, CertN]

/-- Lemma 5.2's output for the angle `t in {b0, b1}` and the family relation give a covered `n`. -/
theorem n_small {n b0 b1 b2 : ℕ} (hb0 : 0 < b0) (hb1 : 0 < b1) (hrel : 3 * b0 + 2 * b1 = n) (h2 : b2 = 2 * b0 + b1)
    (hd : ∀ d, d ∣ b0 → d ∣ b1 → d ∣ b2 → d = 1) {t : ℕ} (ht : t = b0 ∨ t = b1)
    (h52 : n / Nat.gcd t n = 3 ∨ n / Nat.gcd t n = 4 ∨ n / Nat.gcd t n = 6 ∨ n / Nat.gcd t n = 10) : Covered n := by
  have hcop : Nat.Coprime b0 b1 := by
    apply hd
    · exact Nat.gcd_dvd_left _ _
    · exact Nat.gcd_dvd_right _ _
    · rw [h2]; exact dvd_add (Dvd.dvd.mul_left (Nat.gcd_dvd_left _ _) 2) (Nat.gcd_dvd_right _ _)
  set g := Nat.gcd t n with hg
  have hgn : g ∣ n := Nat.gcd_dvd_right _ _
  have hgt : g ∣ t := Nat.gcd_dvd_left _ _
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right _ (by omega)
  have hn : n = g * (n / g) := (Nat.mul_div_cancel' hgn).symm
  have hg12 : g = 1 ∨ g = 2 ∨ g = 3 := by
    rcases ht with rfl | rfl
    · have h1 : g ∣ 3 * t + 2 * b1 := hrel ▸ hgn
      have h3 : g ∣ 3 * t := Dvd.dvd.mul_left hgt 3
      have h4 : g ∣ 2 * b1 := (Nat.dvd_add_right h3).mp h1
      have hc : Nat.Coprime g b1 := Nat.Coprime.coprime_dvd_left hgt hcop
      have h5 : g ∣ 2 := hc.dvd_of_dvd_mul_right h4
      have := Nat.le_of_dvd (by norm_num) h5
      omega
    · have h1 : g ∣ 3 * b0 + 2 * t := hrel ▸ hgn
      have h3 : g ∣ 2 * t := Dvd.dvd.mul_left hgt 2
      have h4 : g ∣ 3 * b0 := (Nat.dvd_add_left h3).mp h1
      have hc : Nat.Coprime g b0 := Nat.Coprime.coprime_dvd_left hgt hcop.symm
      have h5 : g ∣ 3 := hc.dvd_of_dvd_mul_right h4
      have := Nat.le_of_dvd (by norm_num) h5
      omega
  apply covered_small
  rcases hg12 with h | h | h <;> rcases h52 with h' | h' | h' | h' <;> (rw [h] at hn h'; omega)

theorem hPsum_eq {n : ℕ} {a : Fin 3 → ℕ} {f : Fin 3 → Fin 3 → ℕ} (hu : ∑ j, uu a f j = n) :
    ∑ l, FF f l * a l = n := by
  rw [← hu]
  unfold FF uu
  rw [Finset.sum_comm]
  simp [Finset.sum_mul]

set_option maxHeartbeats 4000000 in
/-- **The core.**  Hypotheses: tile `a` (positive, sum `n`, no common divisor), family relation along a labelling `sigma`,
corner figures `f` (rows nonzero, target angles `u_j = f_j . a` summing to `n`), Lemma K* (`KStar`), `n` not covered.
Conclusion: the target numerators are a permutation of the tile numerators, or a tile angle is `pi/2`. -/
theorem uncov_core {n : ℕ} {a : Fin 3 → ℕ} {f : Fin 3 → Fin 3 → ℕ} (ha : ∀ i, 1 ≤ a i) (hsum : ∑ i, a i = n)
    (hd : ∀ d, (∀ i, d ∣ a i) → d = 1)
    (σ : Equiv.Perm (Fin 3)) (hr1 : 3 * a (σ 0) + 2 * a (σ 1) = n) (hr2 : a (σ 2) = 2 * a (σ 0) + a (σ 1))
    (hf : ∀ j, f j ≠ 0) (hu : ∑ j, uu a f j = n) (hK : KStar n a f) (hnc : ¬ Covered n) :
    ((uu a f 0 = a 0 ∧ uu a f 1 = a 1 ∧ uu a f 2 = a 2) ∨ (uu a f 0 = a 0 ∧ uu a f 1 = a 2 ∧ uu a f 2 = a 1) ∨
      (uu a f 0 = a 1 ∧ uu a f 1 = a 0 ∧ uu a f 2 = a 2) ∨ (uu a f 0 = a 1 ∧ uu a f 1 = a 2 ∧ uu a f 2 = a 0) ∨
      (uu a f 0 = a 2 ∧ uu a f 1 = a 0 ∧ uu a f 2 = a 1) ∨ (uu a f 0 = a 2 ∧ uu a f 1 = a 1 ∧ uu a f 2 = a 0)) ∨
    ∃ l, 2 * a l = n := by
  have hPs := hPsum_eq hu
  rw [Fin.sum_univ_three] at hPs hsum
  have a1 := ha 0; have a2 := ha 1; have a3 := ha 2
  have hcov_all : ∀ m : Fin 3, ¬ (3 ≤ FF f (σ m)) := by
    intro m hm
    apply hnc
    have hle : FF f (σ m) * a (σ m) ≤ n := by
      rw [← hPs]
      have : FF f (σ m) * a (σ m) ≤ ∑ l, FF f l * a l :=
        Finset.single_le_sum (f := fun l => FF f l * a l) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (σ m))
      rw [Fin.sum_univ_three] at this
      exact this
    have h3a : 3 * a (σ m) ≤ n := le_trans (Nat.mul_le_mul_right _ hm) hle
    have hnlt : a (σ m) < n := by
      have := LemmaKStar.a_lt (n := n) (a := a) (by rw [Fin.sum_univ_three]; exact hsum) ha (σ m); exact this
    have h52 := Erdos634.Lacz51.lemma52 (a (σ m)) n (ha _) hnlt
      (fun k hk => kstar_frac (by rw [Fin.sum_univ_three]; exact hsum) ha hK (σ m) hm k hk)
    have hdd : ∀ d, d ∣ a (σ 0) → d ∣ a (σ 1) → d ∣ a (σ 2) → d = 1 := by
      intro d h0 h1 h2
      apply hd
      intro i
      obtain ⟨m', rfl⟩ := σ.surjective i
      fin_cases m' <;> assumption
    fin_cases m
    · exact n_small (ha _) (ha _) hr1 hr2 hdd (Or.inl rfl) h52
    · exact n_small (ha _) (ha _) hr1 hr2 hdd (Or.inr rfl) h52
    · exfalso; simp at h3a; omega
  have hle2 : ∀ l, FF f l ≤ 2 := by
    intro l
    obtain ⟨m, rfl⟩ := σ.surjective l
    have := hcov_all m
    omega
  have hrow : ∀ j, 1 ≤ ∑ i, f j i := by
    intro j
    by_contra hcon
    apply hf j
    funext i
    have : ∑ i, f j i = 0 := by omega
    exact Finset.sum_eq_zero_iff.mp this i (Finset.mem_univ _)
  have hSS : ∑ j, ∑ i, f j i = ∑ l, FF f l := by
    unfold FF; rw [Finset.sum_comm]
  have e0 : FF f 0 = f 0 0 + f 1 0 + f 2 0 := by unfold FF; rw [Fin.sum_univ_three]
  have e1 : FF f 1 = f 0 1 + f 1 1 + f 2 1 := by unfold FF; rw [Fin.sum_univ_three]
  have e2 : FF f 2 = f 0 2 + f 1 2 + f 2 2 := by unfold FF; rw [Fin.sum_univ_three]
  have hr0 := hrow 0; have hr1' := hrow 1; have hr2' := hrow 2
  simp only [Fin.sum_univ_three] at hr0 hr1' hr2' hSS
  have l0 := hle2 0; have l1 := hle2 1; have l2 := hle2 2
  have d0 : FF f 0 = 0 ∨ FF f 0 = 1 ∨ FF f 0 = 2 := by omega
  have d1 : FF f 1 = 0 ∨ FF f 1 = 1 ∨ FF f 1 = 2 := by omega
  have d2 : FF f 2 = 0 ∨ FF f 2 = 1 ∨ FF f 2 = 2 := by omega
  have hsum3 : FF f 0 + FF f 1 + FF f 2 = 3 ∨ ∃ l, 2 * a l = n := by
    rcases d0 with h0 | h0 | h0 <;> rcases d1 with h1 | h1 | h1 <;> rcases d2 with h2 | h2 | h2 <;>
      rw [h0, h1, h2] at hPs <;>
      first
      | (left; omega)
      | (exfalso; omega)
      | (right; exact ⟨0, by omega⟩)
      | (right; exact ⟨1, by omega⟩)
      | (right; exact ⟨2, by omega⟩)
  rcases hsum3 with h3 | hr
  · left
    have hu' := hu
    simp only [Fin.sum_univ_three] at hu'
    have row0 : (f 0 0 = 1 ∧ f 0 1 = 0 ∧ f 0 2 = 0) ∨ (f 0 0 = 0 ∧ f 0 1 = 1 ∧ f 0 2 = 0) ∨ (f 0 0 = 0 ∧ f 0 1 = 0 ∧ f 0 2 = 1) := by omega
    have row1 : (f 1 0 = 1 ∧ f 1 1 = 0 ∧ f 1 2 = 0) ∨ (f 1 0 = 0 ∧ f 1 1 = 1 ∧ f 1 2 = 0) ∨ (f 1 0 = 0 ∧ f 1 1 = 0 ∧ f 1 2 = 1) := by omega
    have row2 : (f 2 0 = 1 ∧ f 2 1 = 0 ∧ f 2 2 = 0) ∨ (f 2 0 = 0 ∧ f 2 1 = 1 ∧ f 2 2 = 0) ∨ (f 2 0 = 0 ∧ f 2 1 = 0 ∧ f 2 2 = 1) := by omega
    simp only [uu, Fin.sum_univ_three] at hu' ⊢
    rcases row0 with ⟨p0, p1, p2⟩ | ⟨p0, p1, p2⟩ | ⟨p0, p1, p2⟩ <;>
    rcases row1 with ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ <;>
    rcases row2 with ⟨r0, r1, r2⟩ | ⟨r0, r1, r2⟩ | ⟨r0, r1, r2⟩ <;>
    simp only [p0, p1, p2, q0, q1, q2, r0, r1, r2] at hu' ⊢ <;>
    first
    | omega
    | (exfalso; omega)
  · right; exact hr

end Erdos634.Lacz51Gen

#print axioms Erdos634.Lacz51Gen.uncov_core
