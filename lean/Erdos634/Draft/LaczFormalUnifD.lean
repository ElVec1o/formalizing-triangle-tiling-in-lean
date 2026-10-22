-- Draft/LaczFormalUnifD.lean -- witnesses and negative controls for `LaczFormalUnifB/C`:
--   * `shapes_uniform_witness`: the hypotheses of `shapes_of_K_uniform` hold (n = 216, a = (1,2,213), identity figure; conclusion Similar).
--   * `claimQ_control`: at n = 60 (outside the range n > 200) the tile (10,13,37) with F = (6,0,0) satisfies the corner equation F . x'(k) = 1 at EVERY unit k:
--     so the bound `200 < n` of `claimQ`/`no_big` cannot be dropped (these are Laczkovich's exceptional n = 60 triples).
--   * `l9_uniform_witness`: a real congruent dissection (ladder, N = 4) with tile (1,2,213) pi/216 satisfies the hypotheses of `l9_uniform`/`classify_total`.
-- UNAUDITED (NOTE).  Credit: Laczkovich (Discrete Math 140 (1995) Thm 5.1), Beeson-Rosu, Beeson.
import Erdos634.Draft.LaczFormalUnifC
import Erdos634.Draft.LaczFormalCaseVI

open scoped BigOperators
open Erdos634.LemmaKStar Erdos634.LemmaF Erdos634.Geometry Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal

def idFig : Fin 3 → Fin 3 → ℕ := fun j l => if j = l then 1 else 0

theorem shapes_uniform_witness :
    ∃ (n : ℕ) (a : Fin 3 → ℕ) (f : Fin 3 → Fin 3 → ℕ),
      200 < n ∧ (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ℓ ≤ 5) ∧ (∀ i, 1 ≤ a i) ∧ ∑ i, a i = n ∧
      Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 ∧ (∀ j, f j ≠ 0) ∧ ∑ j, uu a f j = n ∧
      (∀ k : ℤ, Int.gcd k n = 1 → K1 n a f k ∧ K2 n a f k) := by
  have hu : ∀ j, uu ![1, 2, 213] idFig j = ![1, 2, 213] j := by
    intro j; fin_cases j <;> simp [uu, idFig, Fin.sum_univ_three]
  refine ⟨216, ![1, 2, 213], idFig, by norm_num, ?_, by decide, by decide, by decide, ?_, ?_, ?_⟩
  · intro ℓ hℓ hd
    have h216 : (216 : ℕ) = 2 ^ 3 * 3 ^ 3 := by norm_num
    rw [h216] at hd
    rcases (Nat.Prime.dvd_mul hℓ).mp hd with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp (hℓ.dvd_of_dvd_pow h); omega
    · have := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp (hℓ.dvd_of_dvd_pow h); omega
  · intro j h
    have := congrFun h j
    fin_cases j <;> simp [idFig] at this
  · simp only [Fin.sum_univ_three, hu]; decide
  · intro k _
    have hx : ∀ j, xv 216 ![1, 2, 213] idFig k j = yv 216 ![1, 2, 213] k j := by
      intro j; simp only [xv, yv, hu]
    refine ⟨?_, ?_⟩
    · unfold K1 sABC sT; exact Finset.sum_congr rfl fun j _ => (hx j).symm
    · intro j
      have hxp : xpu 216 ![1, 2, 213] idFig k j = xp 216 ![1, 2, 213] k j := by
        unfold xpu xp; rw [hx]
      rw [hxp]
      fin_cases j <;> simp [idFig, Fin.sum_univ_three]

theorem l9_uniform_witness :
    ∃ (N : ℕ) (D : CongruentDissection N) (a : Fin 3 → ℕ),
      (∀ k, D.model.angleAt k = a k * Real.pi / (216 : ℕ)) ∧
      Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 ∧ 200 < 216 ∧ (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ 216 → ℓ ≤ 5) := by
  have hpi := Real.pi_pos
  obtain ⟨N, D, ⟨σ, m0, m1, m2⟩, -⟩ := ladder_with_angles (α := Real.pi / 216) (β := 2 * Real.pi / 216)
    (by positivity) (by positivity) (by linarith)
  refine ⟨N, D, fun l => (![1, 2, 213] : Fin 3 → ℕ) (σ.symm l), ?_, ?_, by norm_num, ?_⟩
  · intro l
    have : ∀ k, D.model.angleAt (σ k) = ((![1, 2, 213] : Fin 3 → ℕ) k : ℕ) * Real.pi / (216 : ℕ) := by
      intro k; fin_cases k
      · simp only [Fin.zero_eta, Matrix.cons_val_zero]; push_cast; rw [m0]; try ring
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons]; push_cast; rw [m1]; try ring
      · simp only [Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]; push_cast
        rw [m2]; try ring
    simpa using this (σ.symm l)
  · have hdvd : ∀ l, Nat.gcd ((![1, 2, 213] : Fin 3 → ℕ) (σ.symm 0))
        (Nat.gcd ((![1, 2, 213] : Fin 3 → ℕ) (σ.symm 1)) ((![1, 2, 213] : Fin 3 → ℕ) (σ.symm 2))) ∣
        (![1, 2, 213] : Fin 3 → ℕ) (σ.symm l) := by
      intro l; fin_cases l
      · exact Nat.gcd_dvd_left _ _
      · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
      · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
    have := hdvd (σ 0)
    simp only [Equiv.symm_apply_apply, Matrix.cons_val_zero] at this
    exact Nat.dvd_one.mp this
  · intro ℓ hℓ hd
    have h216 : (216 : ℕ) = 2 ^ 3 * 3 ^ 3 := by norm_num
    rw [h216] at hd
    rcases (Nat.Prime.dvd_mul hℓ).mp hd with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp (hℓ.dvd_of_dvd_pow h); omega
    · have := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp (hℓ.dvd_of_dvd_pow h); omega

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.shapes_uniform_witness
#print axioms Erdos634.Draft.LaczFormal.l9_uniform_witness
