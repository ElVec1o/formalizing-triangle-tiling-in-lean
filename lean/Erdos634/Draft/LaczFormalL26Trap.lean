import Erdos634.Draft.LaczFormalL26Util

/-!
# Laczkovich Theorem 2.4, fourth triple: the trapezoid `L R Q S` is the union of the triangles `L R Q`, `L Q S`

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94), Beeson, Beeson-Zhang, Zhang.

The scaled chart image of the standard trapezoid `trapSet τ` (`τ = b²/(a²K)`, the scaling `(x₀, x₁) ↦ (a²K x₀, N x₁)`) is
`F ∪ G` with `F = L R Q`, `G = L Q S`.
-/

namespace Erdos634.LaczL26

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL24

variable {a : ℝ}

theorem detpos_F (h : Hyp a) : 0 < det3 0 0 (sR a) 0 (sQ a) (tQ a) := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  rw [det_F h]; positivity

theorem detpos_G (h : Hyp a) : 0 < det3 0 0 (sQ a) (tQ a) 0 (tS a) := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  rw [det_G h]; positivity

theorem trap_poly (h : Hyp a) :
    (fun x : Plane => mkPt (sR a * x 0) (tQ a * x 1)) '' trapSet (sQ a / sR a)
      = (triF h).carrier ∪ (triG h).carrier := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have hA : 0 < sR a := by unfold sR; positivity
  have hn : 0 < tQ a := hN
  have hβ : 0 < sQ a := by unfold sQ; positivity
  have eF : (triF h).carrier = detSet 0 0 (sR a) 0 (sQ a) (tQ a) :=
    carrier_eq_dets _ _ _ _ _ _ (detpos_F h)
  have eG : (triG h).carrier = detSet 0 0 (sQ a) (tQ a) 0 (tS a) :=
    carrier_eq_dets _ _ _ _ _ _ (detpos_G h)
  rw [eF, eG]
  have hS : tS a = tQ a := rfl
  rw [hS]
  generalize sR a = A at *
  generalize sQ a = β at *
  generalize tQ a = n at *
  ext z
  constructor
  · rintro ⟨x, ⟨x1, x2, x3, x4⟩, rfl⟩
    have hs : 0 ≤ A + (β - A) * x 1 - A * x 0 := by
      have := mul_le_mul_of_nonneg_left x4 hA.le
      have e : A * (1 + (β / A - 1) * x 1) = A + (β - A) * x 1 := by field_simp
      linarith
    by_cases hc : 0 ≤ n * (A * x 0) - β * (n * x 1)
    · left
      simp only [detSet, Set.mem_setOf_eq, mkPt_zero, mkPt_one, det3]
      refine ⟨?_, ?_, ?_⟩
      · nlinarith [mul_nonneg hn.le hs]
      · nlinarith
      · nlinarith [mul_nonneg hA.le (mul_nonneg hn.le x1)]
    · right
      push_neg at hc
      simp only [detSet, Set.mem_setOf_eq, mkPt_zero, mkPt_one, det3]
      refine ⟨?_, ?_, ?_⟩
      · nlinarith [mul_nonneg hβ.le (mul_nonneg hn.le (sub_nonneg.2 x2))]
      · nlinarith [mul_nonneg hA.le (mul_nonneg hn.le x3)]
      · nlinarith
  · intro hz
    have hAne := hA.ne'
    have hnne := hn.ne'
    refine ⟨mkPt (z 0 / A) (z 1 / n), ?_, ?_⟩
    · obtain ⟨X0, hX0⟩ : ∃ X0 : ℝ, z 0 = A * X0 := ⟨z 0 / A, by field_simp⟩
      obtain ⟨X1, hX1⟩ : ∃ X1 : ℝ, z 1 = n * X1 := ⟨z 1 / n, by field_simp⟩
      have e0 : z 0 / A = X0 := by rw [hX0]; field_simp
      have e1 : z 1 / n = X1 := by rw [hX1]; field_simp
      simp only [trapSet, Set.mem_setOf_eq, mkPt_zero, mkPt_one, e0, e1]
      have hτ : A + (β - A) * X1 - A * X0 ≥ 0 → X0 ≤ 1 + (β / A - 1) * X1 := by
        intro hs
        have e : 1 + (β / A - 1) * X1 = (A + (β - A) * X1) / A := by field_simp
        rw [e, le_div_iff₀ hA]; linarith
      rcases hz with hz | hz
      · simp only [detSet, Set.mem_setOf_eq, det3, hX0, hX1] at hz
        obtain ⟨f1, f2, f3⟩ := hz
        have s1 : 0 ≤ n * (A + (β - A) * X1 - A * X0) := by nlinarith
        have s2 : 0 ≤ n * (A * X0 - β * X1) := by nlinarith
        have s3 : 0 ≤ A * n * X1 := by nlinarith
        have p1 : 0 ≤ A + (β - A) * X1 - A * X0 := nonneg_of_mul_nonneg_right s1 hn
        have p2 : 0 ≤ A * X0 - β * X1 := nonneg_of_mul_nonneg_right s2 hn
        have p3 : 0 ≤ X1 := by
          have : 0 ≤ (A * n) * X1 := by linarith
          exact nonneg_of_mul_nonneg_right this (mul_pos hA hn)
        have q1 : X1 ≤ 1 := by nlinarith
        have q0 : 0 ≤ X0 := by
          have : 0 ≤ A * X0 := by nlinarith
          exact nonneg_of_mul_nonneg_right this hA
        exact ⟨p3, q1, q0, hτ p1⟩
      · simp only [detSet, Set.mem_setOf_eq, det3, hX0, hX1] at hz
        obtain ⟨f1, f2, f3⟩ := hz
        have s1 : 0 ≤ β * n * (1 - X1) := by nlinarith
        have s2 : 0 ≤ A * n * X0 := by nlinarith
        have s3 : 0 ≤ n * (β * X1 - A * X0) := by nlinarith
        have p1 : 0 ≤ 1 - X1 := nonneg_of_mul_nonneg_right s1 (mul_pos hβ hn)
        have p2 : 0 ≤ X0 := nonneg_of_mul_nonneg_right s2 (mul_pos hA hn)
        have p3 : 0 ≤ β * X1 - A * X0 := nonneg_of_mul_nonneg_right s3 hn
        have q1 : 0 ≤ X1 := by
          have : 0 ≤ β * X1 := by nlinarith [mul_nonneg hA.le p2]
          exact nonneg_of_mul_nonneg_right this hβ
        refine ⟨q1, by linarith, p2, hτ ?_⟩
        nlinarith [mul_nonneg hA.le p1]
    · simp only [mkPt_zero, mkPt_one]
      ext i
      fin_cases i
      · simp [mkPt]; field_simp
      · simp [mkPt]; field_simp

end Erdos634.LaczL26
