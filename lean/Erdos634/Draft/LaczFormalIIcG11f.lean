-- Draft/LaczFormalIIcG11f.lean -- Laczkovich (DCG 48 (2012)), Thm 2.1 (v): from a geometric run of sides plus the two-alternative G11 inequality to the printed "sequence read in some direction" form.
-- `reading_exists`: for a 2k-gon with side(i) = side(i+k), sides side(s0+n) satisfying side(s0+n+1) sB = sA side(s0+n) (n+2<k) and
--   either (sA/sB)^(k-1) side(s0) <= side(s0+k-1)   [forward reading, ratio q = sA/sB]
--   or     side(s0) <= (sA/sB) side(s0+k-1)           [reversed reading from s0+k-1, ratio q = sB/sA]
-- there are q in {sA/sB, sB/sA}, a start s and a direction rev with a_0..a_{k-2} geometric of ratio q and q^(k-1) a_0 <= a_(k-1).  Pure combinatorics on Fin (2k).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 2, Thm 2.1 (v)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalThm21Def

open scoped Classical Fin.NatCast
open Erdos634.Draft.LaczFormal.Thm21

namespace Erdos634.Draft.LaczFormal.RG

theorem ofNat_cast_fin' {M : ℕ} [NeZero M] (n : ℕ) : (Fin.ofNat M n : Fin M) = (n : Fin M) := by
  apply Fin.ext
  simp [Fin.ofNat, Fin.val_natCast]

theorem side_closed {k : ℕ} [NeZero (2 * k)] (P : ConvPoly (2 * k)) (sA sB : ℝ) (hsA : 0 < sA) (hsB : 0 < sB) (s0 : Fin (2 * k))
    (hg : ∀ n : ℕ, n + 2 < k → P.side (s0 + ((n + 1 : ℕ) : Fin (2 * k))) * sB = sA * P.side (s0 + ((n : ℕ) : Fin (2 * k)))) :
    ∀ n : ℕ, n + 1 < k → P.side (s0 + ((n : ℕ) : Fin (2 * k))) = (sA / sB) ^ n * P.side s0 := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have h := hg n (by omega)
    have h2 : P.side (s0 + ((n + 1 : ℕ) : Fin (2 * k))) = (sA / sB) * P.side (s0 + ((n : ℕ) : Fin (2 * k))) := by
      rw [div_mul_eq_mul_div, eq_div_iff hsB.ne']; exact h
    rw [h2, ih (by omega)]; ring

set_option maxHeartbeats 6400000 in
theorem reading_exists {k : ℕ} [NeZero (2 * k)] (P : ConvPoly (2 * k)) (hk : 4 ≤ k)
    (hsymm : ∀ i : Fin (2 * k), P.side i = P.side (i + (k : Fin (2 * k)))) (sA sB : ℝ) (hsA : 0 < sA) (hsB : 0 < sB) (s0 : Fin (2 * k))
    (hg : ∀ n : ℕ, n + 2 < k → P.side (s0 + ((n + 1 : ℕ) : Fin (2 * k))) * sB = sA * P.side (s0 + ((n : ℕ) : Fin (2 * k))))
    (hineq : (sA / sB) ^ (k - 1) * P.side s0 ≤ P.side (s0 + ((k - 1 : ℕ) : Fin (2 * k))) ∨
      P.side s0 ≤ (sA / sB) * P.side (s0 + ((k - 1 : ℕ) : Fin (2 * k)))) :
    ∃ q : ℝ, (q = sA / sB ∨ q = sB / sA) ∧ ∃ (s : Fin (2 * k)) (rev : Bool) (a : ℕ → ℝ),
      (∀ n, a n = if rev then P.side (s - (Fin.ofNat (2 * k) n) - 1) else P.side (s + (Fin.ofNat (2 * k) n))) ∧
      (∀ n, n + 2 < k → a (n + 1) = q * a n) ∧ q ^ (k - 1) * a 0 ≤ a (k - 1) := by
  rcases hineq with h | h
  · refine ⟨sA / sB, Or.inl rfl, s0, false, fun n => P.side (s0 + (n : Fin (2 * k))), ?_, ?_, ?_⟩
    · intro n; simp [ofNat_cast_fin']
    · intro n hn
      have h1 := hg n hn
      show P.side (s0 + ((n + 1 : ℕ) : Fin (2 * k))) = (sA / sB) * P.side (s0 + ((n : ℕ) : Fin (2 * k)))
      rw [div_mul_eq_mul_div, eq_div_iff hsB.ne']; exact h1
    · show (sA / sB) ^ (k - 1) * P.side (s0 + ((0 : ℕ) : Fin (2 * k))) ≤ P.side (s0 + ((k - 1 : ℕ) : Fin (2 * k)))
      simpa using h
  · have hk1 : ((k - 1 : ℕ) : Fin (2 * k)) + 1 = (k : Fin (2 * k)) := by
      have e : (k - 1 + 1 : ℕ) = k := by omega
      calc ((k - 1 : ℕ) : Fin (2 * k)) + 1 = ((k - 1 + 1 : ℕ) : Fin (2 * k)) := (Nat.cast_succ (k - 1)).symm
        _ = (k : Fin (2 * k)) := by rw [e]
    have hk2 : ((k - 2 : ℕ) : Fin (2 * k)) + 1 = ((k - 1 : ℕ) : Fin (2 * k)) := by
      have e : (k - 2 + 1 : ℕ) = k - 1 := by omega
      calc ((k - 2 : ℕ) : Fin (2 * k)) + 1 = ((k - 2 + 1 : ℕ) : Fin (2 * k)) := (Nat.cast_succ (k - 2)).symm
        _ = ((k - 1 : ℕ) : Fin (2 * k)) := by rw [e]
    refine ⟨sB / sA, Or.inr rfl, s0 + ((k - 1 : ℕ) : Fin (2 * k)), true,
      fun n => P.side (s0 + ((k - 1 : ℕ) : Fin (2 * k)) - (n : Fin (2 * k)) - 1), ?_, ?_, ?_⟩
    · intro n; simp [ofNat_cast_fin']
    · intro n hn
      have hm := hg (k - 3 - n) (by omega)
      have e1 : s0 + ((k - 1 : ℕ) : Fin (2 * k)) - ((n + 1 : ℕ) : Fin (2 * k)) - 1 = s0 + ((k - 3 - n : ℕ) : Fin (2 * k)) := by
        have : (k - 3 - n : ℕ) + (n + 1) + 1 = k - 1 := by omega
        have h' : ((k - 1 : ℕ) : Fin (2 * k)) = ((k - 3 - n : ℕ) : Fin (2 * k)) + ((n + 1 : ℕ) : Fin (2 * k)) + 1 := by
          rw [← this]; push_cast; ring
        rw [h']; abel
      have e2 : s0 + ((k - 1 : ℕ) : Fin (2 * k)) - (n : Fin (2 * k)) - 1 = s0 + ((k - 3 - n + 1 : ℕ) : Fin (2 * k)) := by
        have : (k - 3 - n + 1 : ℕ) + n + 1 = k - 1 := by omega
        have h' : ((k - 1 : ℕ) : Fin (2 * k)) = ((k - 3 - n + 1 : ℕ) : Fin (2 * k)) + (n : Fin (2 * k)) + 1 := by
          rw [← this]; push_cast; ring
        rw [h']; abel
      show P.side (s0 + ((k - 1 : ℕ) : Fin (2 * k)) - ((n + 1 : ℕ) : Fin (2 * k)) - 1) = (sB / sA) * P.side (s0 + ((k - 1 : ℕ) : Fin (2 * k)) - (n : Fin (2 * k)) - 1)
      rw [e1, e2, div_mul_eq_mul_div, eq_div_iff hsA.ne']
      linarith
    · show (sB / sA) ^ (k - 1) * P.side (s0 + ((k - 1 : ℕ) : Fin (2 * k)) - ((0 : ℕ) : Fin (2 * k)) - 1) ≤
        P.side (s0 + ((k - 1 : ℕ) : Fin (2 * k)) - ((k - 1 : ℕ) : Fin (2 * k)) - 1)
      have e3 : s0 + ((k - 1 : ℕ) : Fin (2 * k)) - ((0 : ℕ) : Fin (2 * k)) - 1 = s0 + ((k - 2 : ℕ) : Fin (2 * k)) := by
        rw [← hk2, Nat.cast_zero]; abel
      have e4 : s0 + ((k - 1 : ℕ) : Fin (2 * k)) - ((k - 1 : ℕ) : Fin (2 * k)) - 1 = s0 - 1 := by abel
      have e5 : P.side (s0 - 1) = P.side (s0 + ((k - 1 : ℕ) : Fin (2 * k))) := by
        rw [hsymm (s0 - 1)]
        congr 1
        rw [← hk1]; abel
      have hcl := side_closed P sA sB hsA hsB s0 hg (k - 2) (by omega)
      rw [e3, e4, e5, hcl]
      obtain ⟨i, hi⟩ : ∃ i, k = i + 2 := ⟨k - 2, by omega⟩
      have hki : k - 1 = i + 1 := by omega
      have hki2 : k - 2 = i := by omega
      have hinv : (sB / sA) * (sA / sB) = 1 := by field_simp
      have hpw : (sB / sA) ^ i * (sA / sB) ^ i = 1 := by rw [← mul_pow, hinv, one_pow]
      have hcalc : (sB / sA) ^ (k - 1) * ((sA / sB) ^ (k - 2) * P.side s0) = (sB / sA) * P.side s0 := by
        rw [hki, hki2]
        calc (sB / sA) ^ (i + 1) * ((sA / sB) ^ i * P.side s0) = (sB / sA) * ((sB / sA) ^ i * (sA / sB) ^ i) * P.side s0 := by ring
          _ = (sB / sA) * P.side s0 := by rw [hpw]; ring
      rw [hcalc]
      calc (sB / sA) * P.side s0 ≤ (sB / sA) * ((sA / sB) * P.side (s0 + ((k - 1 : ℕ) : Fin (2 * k)))) :=
            mul_le_mul_of_nonneg_left h (by positivity)
        _ = P.side (s0 + ((k - 1 : ℕ) : Fin (2 * k))) := by rw [← mul_assoc, hinv, one_mul]

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.reading_exists
