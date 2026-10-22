import Erdos634.Draft.ZhangRat4Prop11Derived

/-!
# Witness for `ZhangRat4Prop11Derived`: the rational tile `(3/2, 5/2, 7/2)`, `m = 10`, `m' = 5`

The hypotheses of `zhang_prop11_1_derived` / `zhang_prop11_2_derived` (orientation, three squared
side lengths, `k m = m'` natural, `b ∣ m'`) are satisfied by explicit points (the half-scale copy of
`ZhangRat2.prop11_wit`, the Prop 6(2) triangle for `(3,5,7)`), and the theorem then yields the
tilings of the hypothesis triangle by `3575` tiles and of the extended triangle by
`3575 + 65^2 = 7800` (part 1: `(A+2B)m' = 13*5`).  Only part 1 is witnessed here (part 2 has the same hypotheses with `a,b` exchanged).  UNAUDITED.
Credit Zhang (arXiv 2512.22696v4), Beeson, Beeson-Zhang, Laczkovich.
-/

namespace Erdos634.ZhangRat4

open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.ZhangRat Erdos634.ZhangRat3
  Erdos634.LaczL22 Erdos634.ZhangSporadic Erdos634.ZhangL1 Erdos634.CertGeom

/-- the primitive integer model of `(3/2,5/2,7/2)` is `(3,5,7)` with `k = 1/2`. -/
theorem data_357 (A B C : ℕ) (k : ℚ) (hA : 0 < A) (hk : 0 < k) (hcop : Nat.Coprime A B)
    (hh : C * C = A * A + B * B + A * B) (ha : k * A = 3 / 2) (hb : k * B = 5 / 2) :
    A = 3 ∧ B = 5 ∧ C = 7 ∧ k = 1 / 2 := by
  have h5 : (5 * A : ℚ) = 3 * B := by
    have : k * (5 * A) = k * (3 * B) := by linarith
    exact mul_left_cancel₀ hk.ne' this
  have h5n : 5 * A = 3 * B := by exact_mod_cast h5
  have hAd : A ∣ 3 := by
    have : A ∣ 3 * B := ⟨5, by omega⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_right hcop this)
  have hBd : B ∣ 5 := by
    have : B ∣ 5 * A := ⟨3, by omega⟩
    exact (Nat.Coprime.symm hcop).dvd_of_dvd_mul_right this
  have hA3 : A ≤ 3 := Nat.le_of_dvd (by norm_num) hAd
  have hB5 : B ≤ 5 := Nat.le_of_dvd (by norm_num) hBd
  have hA3' : A = 3 := by interval_cases A <;> omega
  subst hA3'
  have hB5' : B = 5 := by omega
  subst hB5'
  have hC : C = 7 := by
    have : C * C = 7 * 7 := by omega
    nlinarith
  refine ⟨rfl, rfl, hC, ?_⟩
  have : k * 3 = 3 / 2 := by exact_mod_cast ha
  linarith

theorem wit_prop11_1 : ∃ R : RTri, R.a = 3 / 2 ∧ R.b = 5 / 2 ∧ R.c = 7 / 2 ∧
    ∃ Ax Ay Bx By Dx Dy : ℝ, 0 < det3 Ax Ay Dx Dy Bx By ∧
      (Ax - Dx) ^ 2 + (Ay - Dy) ^ 2 = ((((R.a : ℝ) + 2 * R.b) * R.a * 10)) ^ 2 ∧
      (Bx - Dx) ^ 2 + (By - Dy) ^ 2 = ((((R.b : ℝ) + 2 * R.a) * R.b * 10)) ^ 2 ∧
      (Ax - Bx) ^ 2 + (Ay - By) ^ 2 = (((R.c : ℝ) ^ 2 * 10)) ^ 2 ∧
      ∃ Cx Cy : ℝ,
        (Cx - Bx) ^ 2 + (Cy - By) ^ 2 = (3 * ((R.a : ℝ) + R.b) * R.b * 10) ^ 2 ∧
        TileDis R (TriSet Ax Ay Dx Dy Bx By) 3575 ∧
        TileDis R (TriSet Ax Ay Cx Cy Bx By) 7800 := by
  obtain ⟨R, ha, hb, hc, hrel, hab⟩ := rat_wit
  refine ⟨R, ha, hb, hc, ?_⟩
  obtain ⟨A, B, C, k, hA, hB, hk, ea, eb, ec, hh, hcop, H⟩ := zhang_prop11_1_derived R hrel hab
  have ha' : k * (A : ℚ) = 3 / 2 := by rw [← ea, ha]
  have hb' : k * (B : ℚ) = 5 / 2 := by rw [← eb, hb]
  obtain ⟨rfl, rfl, rfl, rfl⟩ := data_357 A B C k hA hk hcop hh ha' hb'
  obtain ⟨Ax, Ay, Bx, By, Dx, Dy, hD, h1, h2, h3⟩ := ZhangRat2.prop11_wit
  have hr : ∀ x : ℝ, ((1 / 2 : ℚ) : ℝ) * x = x / 2 := by intro x; push_cast; ring
  have hD' : 0 < det3 (Ax / 2) (Ay / 2) (Dx / 2) (Dy / 2) (Bx / 2) (By / 2) := by
    have : det3 (Ax / 2) (Ay / 2) (Dx / 2) (Dy / 2) (Bx / 2) (By / 2)
        = (1 / 4) * det3 Ax Ay Dx Dy Bx By := by simp only [det3]; ring
    rw [this]; positivity
  have hRa : (R.a : ℝ) = 3 / 2 := by rw [ha]; norm_num
  have hRb : (R.b : ℝ) = 5 / 2 := by rw [hb]; norm_num
  have hRc : (R.c : ℝ) = 7 / 2 := by rw [hc]; norm_num
  have e1 : (Ax / 2 - Dx / 2) ^ 2 + (Ay / 2 - Dy / 2) ^ 2 = (1 / 4) * ((Ax - Dx) ^ 2 + (Ay - Dy) ^ 2) := by ring
  have e2 : (Bx / 2 - Dx / 2) ^ 2 + (By / 2 - Dy / 2) ^ 2 = (1 / 4) * ((Bx - Dx) ^ 2 + (By - Dy) ^ 2) := by ring
  have e3 : (Ax / 2 - Bx / 2) ^ 2 + (Ay / 2 - By / 2) ^ 2 = (1 / 4) * ((Ax - Bx) ^ 2 + (Ay - By) ^ 2) := by ring
  have g1 : (Ax / 2 - Dx / 2) ^ 2 + (Ay / 2 - Dy / 2) ^ 2 = (((R.a : ℝ) + 2 * R.b) * R.a * 10) ^ 2 := by
    rw [e1, h1, hRa, hRb]; push_cast; norm_num
  have g2 : (Bx / 2 - Dx / 2) ^ 2 + (By / 2 - Dy / 2) ^ 2 = (((R.b : ℝ) + 2 * R.a) * R.b * 10) ^ 2 := by
    rw [e2, h2, hRa, hRb]; push_cast; norm_num
  have g3 : (Ax / 2 - Bx / 2) ^ 2 + (Ay / 2 - By / 2) ^ 2 = ((R.c : ℝ) ^ 2 * 10) ^ 2 := by
    rw [e3, h3, hRc]; push_cast; norm_num
  obtain ⟨Cx, Cy, -, -, hm1, -, hT0, -, hT1, -⟩ :=
    H 10 5 (by norm_num) (by push_cast; norm_num) (Or.inl dvd_rfl) (Ax / 2) (Ay / 2) (Bx / 2) (By / 2)
      (Dx / 2) (Dy / 2) hD' g1 g2 g3
  refine ⟨Ax / 2, Ay / 2, Bx / 2, By / 2, Dx / 2, Dy / 2, hD', g1, g2, g3, Cx, Cy, hm1, ?_, ?_⟩
  · simpa using hT0
  · simpa using hT1

end Erdos634.ZhangRat4

#print axioms Erdos634.ZhangRat4.wit_prop11_1
