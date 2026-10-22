import Erdos634.Draft.ZhangRat2Prop11

/-!
# Zhang Prop 11 for rational tiles WITHOUT the tiling hypothesis (`a < b`, `b ∣ m`)

`ZhangRat.zhang_prop11_*_rational` keep the integer core's hypothesis "the integer-length
configuration is tiled by `n0` model tiles".  Here that hypothesis is replaced by the geometric
data alone (the three squared side lengths and orientation), for `m = B t` and `R.a < R.b`: the
tiling of `A D B` comes from Prop 6(2) (`ZhangRat2Prop11.prop11_{1,2}_tiled`).  LIMIT: `B ∣ m`
and `a < b` only.  UNAUDITED.  Credit Zhang (arXiv 2512.22696), Beeson, Beeson-Zhang, Laczkovich.
-/

namespace Erdos634.ZhangRat2

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.SssCongruent Erdos634.ZhangPara Erdos634.ZhangL1 Erdos634.ZhangSporadic
  Erdos634.ZhangRat Erdos634.ZhangRational Erdos634.LaczL22 Erdos634.Realizable Erdos634.BeesonCor5
  Erdos634.ZhangThm4

section r11
variable (R : RTri) (hrel : R.c ^ 2 = R.a ^ 2 + R.b ^ 2 + R.a * R.b)
include hrel

theorem zhang_prop11_1_rational_derived (hab : R.a < R.b) :
    ∃ (A d : ℕ) (k : ℚ) (hA : 0 < A), 0 < k ∧ 0 < d ∧ R.a = k * A ∧ R.b = k * (A + d) ∧
      ∀ (t : ℕ) (ht : 0 < t) (Ax Ay Bx By Dx Dy : ℝ) (hD : 0 < det3 Ax Ay Dx Dy Bx By)
        (hAD : (Ax - Dx) ^ 2 + (Ay - Dy) ^ 2
          = ((((A : ℝ) + 2 * ((A + d : ℕ) : ℝ)) * (((A + d) * t : ℕ) : ℝ)) * A) ^ 2)
        (hBD : (Bx - Dx) ^ 2 + (By - Dy) ^ 2
          = (((((A + d : ℕ) : ℝ) + 2 * A) * ((A + d : ℕ) : ℝ)) * (((A + d) * t : ℕ) : ℝ)) ^ 2)
        (hAB : (Ax - Bx) ^ 2 + (Ay - By) ^ 2
          = ((((A : ℝ) ^ 2 + A * ((A + d : ℕ) : ℝ) + ((A + d : ℕ) : ℝ) ^ 2))
              * (((A + d) * t : ℕ) : ℝ)) ^ 2),
      ∃ C1 : CongruentRegionDissection
          ((((A + d) + 2 * A) * (A + 2 * (A + d)) * (((A + d) * t) * ((A + d) * t)))
            + (((A + 2 * (A + d)) * ((A + d) * t)) * ((A + 2 * (A + d)) * ((A + d) * t)))),
        C1.region = dil (k : ℝ) (TriSet Ax Ay
          (Dx + ((((A : ℝ) + 2 * ((A + d : ℕ) : ℝ)) / (((A + d : ℕ) : ℝ) + 2 * A)) : ℝ) * (Dx - Bx))
          (Dy + ((((A : ℝ) + 2 * ((A + d : ℕ) : ℝ)) / (((A + d : ℕ) : ℝ) + 2 * A)) : ℝ) * (Dy - By))
          Bx By) ∧ C1.model.Congruent R.Δ := by
  obtain ⟨A, B, C, k, hk, hA, hB, hC, hh, hcop, ea, eb, ec⟩ := rat_data R hrel
  have hlt : A < B := by
    rw [ea, eb] at hab
    exact_mod_cast lt_of_mul_lt_mul_left hab hk.le
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hlt.le
  have hd : 0 < d := by omega
  refine ⟨A, d, k, hA, hk, hd, ea, by rw [eb, Nat.cast_add], fun t ht Ax Ay Bx By Dx Dy hD hAD hBD hAB => ?_⟩
  have hT := prop11_1_tiled A d C t hA hd hh hcop ht Ax Ay Bx By Dx Dy hD hAD hBD hAB
  exact rat_dis R A (A + d) C k hk hA hB hh ea eb ec
    (ZhangProp11.zhang_prop11_core A (A + d) ((A + d) * t) hA hB (Nat.mul_pos hB ht) Ax Ay Bx By Dx Dy hD
      hAD hBD hAB hT)

theorem zhang_prop11_2_rational_derived (hab : R.a < R.b) :
    ∃ (A d : ℕ) (k : ℚ) (hA : 0 < A), 0 < k ∧ 0 < d ∧ R.a = k * A ∧ R.b = k * (A + d) ∧
      ∀ (t : ℕ) (ht : 0 < t) (Ax Ay Bx By Dx Dy : ℝ) (hD : 0 < det3 Ax Ay Dx Dy Bx By)
        (hAD : (Ax - Dx) ^ 2 + (Ay - Dy) ^ 2
          = (((((A + d : ℕ) : ℝ) + 2 * A) * (((A + d) * t : ℕ) : ℝ)) * ((A + d : ℕ) : ℝ)) ^ 2)
        (hBD : (Bx - Dx) ^ 2 + (By - Dy) ^ 2
          = ((((A : ℝ) + 2 * ((A + d : ℕ) : ℝ)) * A) * (((A + d) * t : ℕ) : ℝ)) ^ 2)
        (hAB : (Ax - Bx) ^ 2 + (Ay - By) ^ 2
          = ((((A : ℝ) ^ 2 + A * ((A + d : ℕ) : ℝ) + ((A + d : ℕ) : ℝ) ^ 2))
              * (((A + d) * t : ℕ) : ℝ)) ^ 2),
      ∃ C1 : CongruentRegionDissection
          ((((A + d) + 2 * A) * (A + 2 * (A + d)) * (((A + d) * t) * ((A + d) * t)))
            + ((((A + d) + 2 * A) * ((A + d) * t)) * (((A + d) + 2 * A) * ((A + d) * t)))),
        C1.region = dil (k : ℝ) (TriSet Ax Ay
          (Dx + ((((( A + d : ℕ) : ℝ) + 2 * A) / ((A : ℝ) + 2 * ((A + d : ℕ) : ℝ))) : ℝ) * (Dx - Bx))
          (Dy + ((((( A + d : ℕ) : ℝ) + 2 * A) / ((A : ℝ) + 2 * ((A + d : ℕ) : ℝ))) : ℝ) * (Dy - By))
          Bx By) ∧ C1.model.Congruent R.Δ := by
  obtain ⟨A, B, C, k, hk, hA, hB, hC, hh, hcop, ea, eb, ec⟩ := rat_data R hrel
  have hlt : A < B := by
    rw [ea, eb] at hab
    exact_mod_cast lt_of_mul_lt_mul_left hab hk.le
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hlt.le
  have hd : 0 < d := by omega
  refine ⟨A, d, k, hA, hk, hd, ea, by rw [eb, Nat.cast_add], fun t ht Ax Ay Bx By Dx Dy hD hAD hBD hAB => ?_⟩
  have hT := prop11_2_tiled A d C t hA hd hh hcop ht Ax Ay Bx By Dx Dy hD hAD hBD hAB
  exact rat_dis R A (A + d) C k hk hA hB hh ea eb ec
    (ZhangProp11b.zhang_prop11_2_core A (A + d) ((A + d) * t) hA hB (Nat.mul_pos hB ht) Ax Ay Bx By Dx Dy hD
      hAD hBD hAB hT)

end r11

end Erdos634.ZhangRat2
