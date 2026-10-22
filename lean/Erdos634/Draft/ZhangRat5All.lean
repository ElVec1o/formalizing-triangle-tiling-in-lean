import Erdos634.Draft.ZhangRat5Swap

/-!
# Zhang Prop 11: unified statements for every rational tile

For every rational tile `(a, b, c)` with `c^2 = a^2 + b^2 + ab` (any order of `a, b`; `a = b` is impossible)
and every `m'` in the numerical semigroup `<max(A,B), C>` (primitive model `(A,B,C)`, `R = k (A,B,C)`,
`m' = k m`), the hypothesis triangle `((a+2b)am, (b+2a)bm, c^2 m)` is tiled (Prop 6(1), 6(2), Thm 7 of Zhang,
exchanging `a <-> b` when `b < a`) and the printed conclusions of Prop 11 (1) and (2) hold, with the tile
counts.  Remaining restriction: `m'` in the semigroup `<max(A,B), C>`; for other `m'` the tileability of the
hypothesis triangle is a genuine hypothesis of the printed proposition (`ZhangRat3.zhang_prop11_*_printed`,
no restriction on `m`, `a`, `b`).  UNAUDITED.  Credit Zhang (arXiv 2512.22696v4), Beeson, Beeson-Zhang, Laczkovich.
-/

set_option maxHeartbeats 3200000

namespace Erdos634.ZhangRat5

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.SssCongruent Erdos634.ZhangPara Erdos634.ZhangL1 Erdos634.ZhangSporadic
  Erdos634.ZhangRat Erdos634.ZhangRational Erdos634.LaczL22 Erdos634.Realizable Erdos634.BeesonCor5
  Erdos634.ZhangThm4 Erdos634.ZhangRat3 Erdos634.ZhangRat4

section main
variable (R : RTri) (hrel : R.c ^ 2 = R.a ^ 2 + R.b ^ 2 + R.a * R.b)
include hrel

/-- **Zhang Prop 11 (1), every rational tile.**  No ordering of `a, b`; the hypothesis triangle is tiled for every `m'` in the semigroup
`<max(A,B), C>`; the printed conclusions (triangle sides, tilings, tile counts) follow. -/
theorem zhang_prop11_1_final :
    ∃ (A B C : ℕ) (k : ℚ) (hA : 0 < A) (hB : 0 < B), 0 < k ∧ R.a = k * A ∧ R.b = k * B ∧ R.c = k * C ∧
      C * C = A * A + B * B + A * B ∧ Nat.Coprime A B ∧ A ≠ B ∧
      ∀ (m : ℝ) (m' : ℕ), 0 < m' → (k : ℝ) * m = m' → (∃ i j : ℕ, m' = max A B * i + C * j) →
        ∀ (Ax Ay Bx By Dx Dy : ℝ),
        0 < det3 Ax Ay Dx Dy Bx By →
        (Ax - Dx) ^ 2 + (Ay - Dy) ^ 2 = (((R.a : ℝ) + 2 * R.b) * R.a * m) ^ 2 →
        (Bx - Dx) ^ 2 + (By - Dy) ^ 2 = (((R.b : ℝ) + 2 * R.a) * R.b * m) ^ 2 →
        (Ax - Bx) ^ 2 + (Ay - By) ^ 2 = ((R.c : ℝ) ^ 2 * m) ^ 2 →
        ∃ Cx Cy : ℝ,
          Cx = Dx + (((R.a : ℝ) + 2 * R.b) / ((R.b : ℝ) + 2 * R.a)) * (Dx - Bx) ∧
          Cy = Dy + (((R.a : ℝ) + 2 * R.b) / ((R.b : ℝ) + 2 * R.a)) * (Dy - By) ∧
          (Cx - Bx) ^ 2 + (Cy - By) ^ 2 = (3 * ((R.a : ℝ) + R.b) * R.b * m) ^ 2 ∧
          (Cx - Ax) ^ 2 + (Cy - Ay) ^ 2 = (((R.a : ℝ) + 2 * R.b) * m * R.c) ^ 2 ∧
          TileDis R (TriSet Ax Ay Dx Dy Bx By) ((B + 2 * A) * (A + 2 * B) * (m' * m')) ∧
          (((B + 2 * A) * (A + 2 * B) * (m' * m') : ℕ) : ℝ)
            = ((R.a : ℝ) + 2 * R.b) * ((R.b : ℝ) + 2 * R.a) * m ^ 2 ∧
          TileDis R (TriSet Ax Ay Cx Cy Bx By)
            ((B + 2 * A) * (A + 2 * B) * (m' * m') + ((A + 2 * B) * m') * ((A + 2 * B) * m')) ∧
          ((((B + 2 * A) * (A + 2 * B) * (m' * m') + ((A + 2 * B) * m') * ((A + 2 * B) * m') : ℕ) : ℝ)
            = 3 * m ^ 2 * ((R.a : ℝ) + 2 * R.b) * ((R.a : ℝ) + R.b)) := by
  obtain ⟨A0, B0, C0, k0, hk0, hA0, hB0, hC0, hh0, hcop0, ea0, eb0, ec0⟩ := rat_data R hrel
  rcases lt_trichotomy A0 B0 with hlt | heq | hgt
  · have hab : R.a < R.b := by
      rw [ea0, eb0]
      have : (A0 : ℚ) < B0 := by exact_mod_cast hlt
      exact mul_lt_mul_of_pos_left this hk0
    obtain ⟨A, B, C, k, hA, hB, hk, ea, eb, ec, hh, hcop, hlt', H⟩ := zhang_prop11_1_S R hrel hab
    refine ⟨A, B, C, k, hA, hB, hk, ea, eb, ec, hh, hcop, hlt'.ne, ?_⟩
    intro m m' h1 h2 hS
    rw [max_eq_right hlt'.le] at hS
    exact H m m' h1 h2 hS
  · exfalso
    subst heq
    have h1 : A0 = 1 := by simpa using hcop0
    subst h1
    have hc3 : C0 * C0 = 3 := by omega
    have : C0 ≤ 2 := by nlinarith
    interval_cases C0 <;> omega
  · have hba : R.b < R.a := by
      rw [ea0, eb0]
      have : (B0 : ℚ) < A0 := by exact_mod_cast hgt
      exact mul_lt_mul_of_pos_left this hk0
    obtain ⟨A, B, C, k, hA, hB, hk, ea, eb, ec, hh, hcop, hgt', H⟩ := zhang_prop11_1_Sb R hrel hba
    refine ⟨A, B, C, k, hA, hB, hk, ea, eb, ec, hh, hcop, hgt'.ne', ?_⟩
    intro m m' h1 h2 hS
    rw [max_eq_left hgt'.le] at hS
    exact H m m' h1 h2 hS

/-- **Zhang Prop 11 (2), every rational tile.**  No ordering of `a, b`; the hypothesis triangle is tiled for every `m'` in the semigroup
`<max(A,B), C>`; the printed conclusions (triangle sides, tilings, tile counts) follow. -/
theorem zhang_prop11_2_final :
    ∃ (A B C : ℕ) (k : ℚ) (hA : 0 < A) (hB : 0 < B), 0 < k ∧ R.a = k * A ∧ R.b = k * B ∧ R.c = k * C ∧
      C * C = A * A + B * B + A * B ∧ Nat.Coprime A B ∧ A ≠ B ∧
      ∀ (m : ℝ) (m' : ℕ), 0 < m' → (k : ℝ) * m = m' → (∃ i j : ℕ, m' = max A B * i + C * j) →
        ∀ (Ax Ay Bx By Dx Dy : ℝ),
        0 < det3 Ax Ay Dx Dy Bx By →
        (Ax - Dx) ^ 2 + (Ay - Dy) ^ 2 = (((R.b : ℝ) + 2 * R.a) * R.b * m) ^ 2 →
        (Bx - Dx) ^ 2 + (By - Dy) ^ 2 = (((R.a : ℝ) + 2 * R.b) * R.a * m) ^ 2 →
        (Ax - Bx) ^ 2 + (Ay - By) ^ 2 = ((R.c : ℝ) ^ 2 * m) ^ 2 →
        ∃ Cx Cy : ℝ,
          Cx = Dx + (((R.b : ℝ) + 2 * R.a) / ((R.a : ℝ) + 2 * R.b)) * (Dx - Bx) ∧
          Cy = Dy + (((R.b : ℝ) + 2 * R.a) / ((R.a : ℝ) + 2 * R.b)) * (Dy - By) ∧
          (Cx - Bx) ^ 2 + (Cy - By) ^ 2 = (3 * ((R.a : ℝ) + R.b) * R.a * m) ^ 2 ∧
          (Cx - Ax) ^ 2 + (Cy - Ay) ^ 2 = (((R.b : ℝ) + 2 * R.a) * m * R.c) ^ 2 ∧
          TileDis R (TriSet Ax Ay Dx Dy Bx By) ((B + 2 * A) * (A + 2 * B) * (m' * m')) ∧
          (((B + 2 * A) * (A + 2 * B) * (m' * m') : ℕ) : ℝ)
            = ((R.b : ℝ) + 2 * R.a) * ((R.a : ℝ) + 2 * R.b) * m ^ 2 ∧
          TileDis R (TriSet Ax Ay Cx Cy Bx By)
            ((B + 2 * A) * (A + 2 * B) * (m' * m') + ((B + 2 * A) * m') * ((B + 2 * A) * m')) ∧
          ((((B + 2 * A) * (A + 2 * B) * (m' * m') + ((B + 2 * A) * m') * ((B + 2 * A) * m') : ℕ) : ℝ)
            = 3 * m ^ 2 * ((R.b : ℝ) + 2 * R.a) * ((R.a : ℝ) + R.b)) := by
  obtain ⟨A0, B0, C0, k0, hk0, hA0, hB0, hC0, hh0, hcop0, ea0, eb0, ec0⟩ := rat_data R hrel
  rcases lt_trichotomy A0 B0 with hlt | heq | hgt
  · have hab : R.a < R.b := by
      rw [ea0, eb0]
      have : (A0 : ℚ) < B0 := by exact_mod_cast hlt
      exact mul_lt_mul_of_pos_left this hk0
    obtain ⟨A, B, C, k, hA, hB, hk, ea, eb, ec, hh, hcop, hlt', H⟩ := zhang_prop11_2_S R hrel hab
    refine ⟨A, B, C, k, hA, hB, hk, ea, eb, ec, hh, hcop, hlt'.ne, ?_⟩
    intro m m' h1 h2 hS
    rw [max_eq_right hlt'.le] at hS
    exact H m m' h1 h2 hS
  · exfalso
    subst heq
    have h1 : A0 = 1 := by simpa using hcop0
    subst h1
    have hc3 : C0 * C0 = 3 := by omega
    have : C0 ≤ 2 := by nlinarith
    interval_cases C0 <;> omega
  · have hba : R.b < R.a := by
      rw [ea0, eb0]
      have : (B0 : ℚ) < A0 := by exact_mod_cast hgt
      exact mul_lt_mul_of_pos_left this hk0
    obtain ⟨A, B, C, k, hA, hB, hk, ea, eb, ec, hh, hcop, hgt', H⟩ := zhang_prop11_2_Sb R hrel hba
    refine ⟨A, B, C, k, hA, hB, hk, ea, eb, ec, hh, hcop, hgt'.ne', ?_⟩
    intro m m' h1 h2 hS
    rw [max_eq_left hgt'.le] at hS
    exact H m m' h1 h2 hS

end main

end Erdos634.ZhangRat5

#print axioms Erdos634.ZhangRat5.zhang_prop11_1_final
#print axioms Erdos634.ZhangRat5.zhang_prop11_2_final
