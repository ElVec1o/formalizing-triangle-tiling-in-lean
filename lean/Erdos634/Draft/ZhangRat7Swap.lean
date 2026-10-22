import Erdos634.Draft.ZhangRat5Swap

/-!
# Zhang Prop 6 and Thm 7 for `b < a` and in unordered form (arXiv 2512.22696v4)

The ordered statements of `ZhangRat` need `a < b`.  The tile `swapR R` (sides `(b, a, c)`) is congruent to `R`
(`congruent_permTri`), so the statements for `R.b < R.a` follow from those for `swapR R`; `R.a = R.b` is impossible
(`c^2 = 3 a^2`).  Reading note: the printed proof of Prop 6 draws the trapezoid with `y = ab(a-b)` but Cor 1 and
Thm 7 use `(a,b) = (3,5)` and the count `b^2 = 25`; the Lean statements carry the larger side as `A + d` (count with
the larger side squared).  The literal "a > b with the smaller side squared" is a different tiling and is NOT claimed.
UNAUDITED.  Credit Zhang (arXiv 2512.22696v4), Beeson, Beeson-Zhang, Laczkovich.
-/

namespace Erdos634.ZhangRat7

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.SssCongruent Erdos634.ZhangRat Erdos634.ZhangRat5 Erdos634.ZhangRational Erdos634.LaczL22
  Erdos634.ZhangThm4 Erdos634.ZhangPara

theorem a_ne_b (R : RTri) (hrel : R.c ^ 2 = R.a ^ 2 + R.b ^ 2 + R.a * R.b) : R.a ≠ R.b := by
  intro h
  obtain ⟨A, B, C, k, hk, hA, hB, hC, hh, hcop, ea, eb, ec⟩ := rat_data R hrel
  have hAB : (A : ℚ) = B := by
    rw [ea, eb] at h; exact mul_left_cancel₀ hk.ne' h
  have hAB' : A = B := by exact_mod_cast hAB
  subst hAB'
  have h1 : A = 1 := by simpa using hcop
  subst h1
  have : C * C = 3 := by simpa using hh
  rcases Nat.lt_or_ge C 2 with h2 | h2
  · interval_cases C <;> omega
  · nlinarith

section main
variable (R : RTri) (hrel : R.c ^ 2 = R.a ^ 2 + R.b ^ 2 + R.a * R.b)
include hrel

theorem zhang_prop6_1_gt (hba : R.b < R.a) :
    ∃ (A d C : ℕ) (k : ℚ) (hA : 0 < A), 0 < k ∧ 0 < d ∧ R.b = k * A ∧ R.a = k * (A + d) ∧
      ∃ C1 : CongruentRegionDissection (((A + d) + 2 * A) * (A + 2 * (A + d)) * (C * C)),
        C1.region = dil (k : ℝ) (ZhangLat.LT 0 (ZhangProp6.pAv (A : ℝ) d) (ZhangProp6.pCu (A : ℝ) d) 0
          (ZhangProp6.pBu (A : ℝ) d) (ZhangProp6.pBv (A : ℝ) d)) ∧ C1.model.Congruent R.Δ := by
  obtain ⟨A, d, C, k, hA, hk, hd, ea, eb, C1, hr, hc⟩ :=
    zhang_prop6_1_rational (swapR R) (swapR_rel R hrel) hba
  exact ⟨A, d, C, k, hA, hk, hd, ea, eb, C1, hr, hc.trans (congruent_permTri R.Δ _)⟩

theorem zhang_prop6_2_gt (hba : R.b < R.a) :
    ∃ (A d C : ℕ) (k : ℚ) (hA : 0 < A), 0 < k ∧ 0 < d ∧ R.b = k * A ∧ R.a = k * (A + d) ∧
      ∃ C1 : CongruentRegionDissection (((A + d) + 2 * A) * (A + 2 * (A + d)) * ((A + d) * (A + d))),
        C1.region = dil (k : ℝ) (ZhangLat.LT (ZhangProp6b.qAu (A : ℝ) d) 0 (ZhangProp6.pFu (A : ℝ) d) 0
          (ZhangProp6b.qBu (A : ℝ) d) (ZhangProp6b.qBv (A : ℝ) d)) ∧ C1.model.Congruent R.Δ := by
  obtain ⟨A, d, C, k, hA, hk, hd, ea, eb, C1, hr, hc⟩ :=
    zhang_prop6_2_rational (swapR R) (swapR_rel R hrel) hba
  exact ⟨A, d, C, k, hA, hk, hd, ea, eb, C1, hr, hc.trans (congruent_permTri R.Δ _)⟩

theorem zhang_thm7_gt (hba : R.b < R.a) :
    ∃ (A d C : ℕ) (k : ℚ) (hA : 0 < A), 0 < k ∧ 0 < d ∧ R.b = k * A ∧ R.a = k * (A + d) ∧
      ∀ m : ℕ, (A + d) * C < m + (A + d) + C →
      ∃ C1 : CongruentRegionDissection (((A + d) + 2 * A) * (A + 2 * (A + d)) * (m * m)),
        C1.region = dil (k : ℝ) (ZhangLat.LT 0 0 ((A : ℝ) * (A + 2 * ((A : ℝ) + d)) * m) 0
          (((A : ℝ) * (A + 2 * ((A : ℝ) + d)) - ((A : ℝ) + d) * (2 * A + ((A : ℝ) + d))) * m)
          ((((A : ℝ) + d)) * (2 * A + ((A : ℝ) + d)) * m)) ∧ C1.model.Congruent R.Δ := by
  obtain ⟨A, d, C, k, hA, hk, hd, ea, eb, H⟩ := zhang_thm7_rational (swapR R) (swapR_rel R hrel) hba
  refine ⟨A, d, C, k, hA, hk, hd, ea, eb, fun m hm => ?_⟩
  obtain ⟨C1, hr, hc⟩ := H m hm
  exact ⟨C1, hr, hc.trans (congruent_permTri R.Δ _)⟩

/-- **Theorem 7, unordered**: for every rational tile (`a != b` automatically), with `l = A + d` the larger side
in the lattice normalisation `{R.a, R.b} = k {A, A+d}`. -/
theorem zhang_thm7_any :
    ∃ (A d C : ℕ) (k : ℚ) (hA : 0 < A), 0 < k ∧ 0 < d ∧
      ((R.a = k * A ∧ R.b = k * (A + d)) ∨ (R.b = k * A ∧ R.a = k * (A + d))) ∧
      ∀ m : ℕ, (A + d) * C < m + (A + d) + C →
      ∃ C1 : CongruentRegionDissection (((A + d) + 2 * A) * (A + 2 * (A + d)) * (m * m)),
        C1.region = dil (k : ℝ) (ZhangLat.LT 0 0 ((A : ℝ) * (A + 2 * ((A : ℝ) + d)) * m) 0
          (((A : ℝ) * (A + 2 * ((A : ℝ) + d)) - ((A : ℝ) + d) * (2 * A + ((A : ℝ) + d))) * m)
          ((((A : ℝ) + d)) * (2 * A + ((A : ℝ) + d)) * m)) ∧ C1.model.Congruent R.Δ := by
  rcases lt_trichotomy R.a R.b with h | h | h
  · obtain ⟨A, d, C, k, hA, hk, hd, ea, eb, H⟩ := zhang_thm7_rational R hrel h
    exact ⟨A, d, C, k, hA, hk, hd, Or.inl ⟨ea, eb⟩, H⟩
  · exact absurd h (a_ne_b R hrel)
  · obtain ⟨A, d, C, k, hA, hk, hd, ea, eb, H⟩ := zhang_thm7_gt R hrel h
    exact ⟨A, d, C, k, hA, hk, hd, Or.inr ⟨ea, eb⟩, H⟩

end main

/-- witness for `b < a`: the tile `swapR` of `(3/2, 5/2, 7/2)`, with the derived Thm 7 data. -/
theorem gt_wit : ∃ R : RTri, R.a = 5 / 2 ∧ R.b = 3 / 2 ∧ R.c = 7 / 2 ∧
    R.c ^ 2 = R.a ^ 2 + R.b ^ 2 + R.a * R.b ∧ R.b < R.a ∧ ∃ (A d C : ℕ) (k : ℚ), 0 < k ∧ R.b = k * A ∧
      R.a = k * (A + d) := by
  obtain ⟨R0, ha0, hb0, hc0, hrel0, hab0⟩ := rat_wit
  have hrel := swapR_rel R0 hrel0
  have hlt : (swapR R0).b < (swapR R0).a := hab0
  obtain ⟨A, d, C, k, hA, hk, hd, ea, eb, -⟩ := zhang_thm7_gt (swapR R0) hrel hlt
  exact ⟨swapR R0, hb0, ha0, hc0, hrel, hlt, A, d, C, k, hk, ea, eb⟩

end Erdos634.ZhangRat7

#print axioms Erdos634.ZhangRat7.zhang_thm7_any
#print axioms Erdos634.ZhangRat7.zhang_prop6_1_gt
#print axioms Erdos634.ZhangRat7.zhang_prop6_2_gt
#print axioms Erdos634.ZhangRat7.gt_wit
#print axioms Erdos634.ZhangRat7.a_ne_b
