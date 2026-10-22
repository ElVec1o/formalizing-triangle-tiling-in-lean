import Erdos634.Draft.ZhangRational

/-!
# Zhang Theorems 4 and 5 for every rational tile, in the printed form "for ALL `m >= M`"

arXiv 2512.22696v4, Thm 4: "Let `M = 3 ceil((c^2-a-b)/(ab))`.  Then for all integers `m >= M`, `m a b`
is equiconstructible by `(a,b,c)`.  As a consequence there is a `m^2 a b` tiling."  Thm 5 is the same
with `(a^2+b^2-a-b)/(ab)` and the tile with an angle `pi/3`.

`ZhangRational.zhang_thm4_rational` / `zhang_thm5_rational` only gave ONE equilateral triangle for
a rational tile (`m = M`).  Here: for a tile `R` with rational sides, with `(a,b,c) = k (A,B,C)`
primitive (`Nat.Coprime A B`), there is a threshold `M` such that for EVERY natural `m >= M` the
triangle `Tri3 0 0 (k m A B)` carries `m^2 A B` tiles congruent to `R.Δ`.
(`M` is Zhang's `3 (floor((C^2-A-B)/(AB)) + 1)`; ceiling vs floor+1 agree on all admissible tiles
because `(C^2-A-B)/(AB)` is never an integer.)  UNAUDITED.
Credit Zhang (arXiv 2512.22696v4), Beeson, Beeson-Zhang, Laczkovich.
-/

namespace Erdos634.ZhangRat6

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.SssCongruent Erdos634.ZhangL1 Erdos634.ZhangPara Erdos634.ZhangThm4 Erdos634.ZhangThm5
  Erdos634.ZhangPi3 Erdos634.Realizable Erdos634.LaczL22 Erdos634.BeesonCor5 Erdos634.ZhangRational

theorem zhang_thm4_rational_all (R : RTri) (hrel : R.c ^ 2 = R.a ^ 2 + R.b ^ 2 + R.a * R.b) :
    ∃ (A B : ℕ) (k : ℚ), 0 < k ∧ 0 < A ∧ 0 < B ∧ R.a = k * A ∧ R.b = k * B ∧ Nat.Coprime A B ∧
      ∃ M : ℕ, 0 < M ∧ ∀ m : ℕ, M ≤ m →
        ∃ C : CongruentRegionDissection (m * m * (A * B)),
          C.region = Tri3 0 0 ((k : ℝ) * ((m : ℝ) * ((A : ℝ) * B))) ∧ C.model.Congruent R.Δ := by
  obtain ⟨A, B, C, k, hk, hA, hB, hC, ea, eb, ec, hg⟩ := rat_scale R.a R.b R.c R.pa R.pb R.pc
  have hq : (C : ℚ) * C = A * A + B * B + A * B := by
    have h1 : k ^ 2 * ((C : ℚ) * C) = k ^ 2 * (A * A + B * B + A * B) := by
      have := hrel; rw [ea, eb, ec] at this; nlinarith [this]
    exact mul_left_cancel₀ (by positivity) h1
  have hh : C * C = A * A + B * B + A * B := by exact_mod_cast hq
  have hcop := coprime_thm4 A B C hh hg
  have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hcR : (C : ℝ) ^ 2 = (A : ℝ) ^ 2 + (B : ℝ) ^ 2 + A * B := by
    exact_mod_cast (by nlinarith [hh] : C ^ 2 = A ^ 2 + B ^ 2 + A * B)
  have hA' : (0 : ℝ) < (A : ℝ) := Nat.cast_pos.mpr hA
  have hB' : (0 : ℝ) < (B : ℝ) := Nat.cast_pos.mpr hB
  refine ⟨A, B, k, hk, hA, hB, ea, eb, hcop, 3 * ((C * C - A - B) / (A * B) + 1), by positivity,
    fun m hm => ?_⟩
  have key := zhang_thm4 A B C hA hB hC hh hcop m hm
  unfold EquiConstr at key
  obtain ⟨C0, hr, hmod⟩ := key
  have d01 := R_d01 (c := (C : ℝ)) hA' hB' hcR
  have d12 := R_d12 hA' hB'
  have d02 := R_d02 hA' hB'
  have n01 := dist_eq_of_sq dist_nonneg (Nat.cast_nonneg C) d01
  have n12 := dist_eq_of_sq dist_nonneg (Nat.cast_nonneg A) d12
  have n02 := dist_eq_of_sq dist_nonneg (Nat.cast_nonneg B) d02
  obtain ⟨C1, hreg, hcong⟩ := transfer C0 (k : ℝ) hkr R.Δ (by
    rw [hmod]
    apply hd_of_three
    · rw [n01, R.hc, ec]; push_cast; ring
    · rw [n12, R.ha, ea]; push_cast; ring
    · rw [dist_comm, n02, R.hb, eb]; push_cast; ring)
  refine ⟨C1, ?_, hcong⟩
  rw [hreg, hr, tri3_scale (k : ℝ) hkr]

/-- Thm 5, `pi/3` tile.  Zhang's `(a,b,c)` is `(C,B,A)` in the `RTri` labelling (`|12| = A k`, `|20| = B k`,
`|01| = C k`); the primitive pair is `(C,B)`. -/
theorem zhang_thm5_rational_all (R : RTri) (hrel : R.a ^ 2 + R.c * R.b = R.c ^ 2 + R.b ^ 2)
    (hne : R.c ≠ R.b) :
    ∃ (P Q : ℕ) (k : ℚ), 0 < k ∧ 0 < P ∧ 0 < Q ∧ R.c = k * P ∧ R.b = k * Q ∧ Nat.Coprime P Q ∧
      1 < P * Q ∧
      ∃ M : ℕ, 0 < M ∧ ∀ m : ℕ, M ≤ m →
        ∃ C : CongruentRegionDissection (m * m * (P * Q)),
          C.region = Tri3 0 0 ((k : ℝ) * ((m : ℝ) * ((P : ℝ) * Q))) ∧ C.model.Congruent R.Δ := by
  obtain ⟨A, B, C, k, hk, hA, hB, hC, ea, eb, ec, hg⟩ := rat_scale R.a R.b R.c R.pa R.pb R.pc
  have hq : (A : ℚ) * A + C * B = C * C + B * B := by
    have h1 : k ^ 2 * ((A : ℚ) * A + C * B) = k ^ 2 * (C * C + B * B) := by
      have := hrel; rw [ea, eb, ec] at this; nlinarith [this]
    exact mul_left_cancel₀ (by positivity) h1
  have hh : A * A + C * B = C * C + B * B := by exact_mod_cast hq
  have hcop : Nat.Coprime C B := coprime_thm5 C B A hh (fun d h1 h2 h3 =>
    Nat.dvd_one.mp (hg ▸ Nat.dvd_gcd (Nat.dvd_gcd h3 h2) h1))
  have h1 : 1 < C * B := by
    by_contra hcon
    have hC1 : C = 1 := by nlinarith [Nat.mul_pos hC hB]
    have hB1 : B = 1 := by nlinarith [Nat.mul_pos hC hB]
    apply hne
    rw [ec, eb, hC1, hB1]
  have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hC' : (0 : ℝ) < (C : ℝ) := Nat.cast_pos.mpr hC
  have hB' : (0 : ℝ) < (B : ℝ) := Nat.cast_pos.mpr hB
  refine ⟨C, B, k, hk, hC, hB, ec, eb, hcop, h1, 3 * ((C * C + B * B - C - B) / (C * B) + 1),
    by positivity, fun m hm => ?_⟩
  have key := zhang_thm5 C B A hC hB hA h1 hh hcop m hm
  unfold EquiConstr3 at key
  obtain ⟨C0, hr, hmod⟩ := key
  have hcR : (A : ℝ) ^ 2 = (C : ℝ) ^ 2 - C * B + (B : ℝ) ^ 2 := by
    have : (A : ℝ) ^ 2 + C * B = C ^ 2 + B ^ 2 := by
      exact_mod_cast (by nlinarith [hh] : A ^ 2 + C * B = C ^ 2 + B ^ 2)
    linarith
  have d01 := R3_01 hC' hB'
  have d12 := R3_12 hC' hB'
  have d02 := R3_02 hC' hB'
  have n01 := dist_eq_of_sq dist_nonneg (Nat.cast_nonneg C) d01
  have n12 := dist_eq_of_sq dist_nonneg (Nat.cast_nonneg A) (d12.trans hcR.symm)
  have n02 := dist_eq_of_sq dist_nonneg (Nat.cast_nonneg B) d02
  obtain ⟨C1, hreg, hcong⟩ := transfer C0 (k : ℝ) hkr R.Δ (by
    rw [hmod]
    apply hd_of_three
    · rw [n01, R.hc, ec]; push_cast; ring
    · rw [n12, R.ha, ea]; push_cast; ring
    · rw [n02, dist_comm, R.hb, eb]; push_cast; ring)
  refine ⟨C1, ?_, hcong⟩
  rw [hreg, hr, tri3_scale (k : ℝ) hkr]

end Erdos634.ZhangRat6

#print axioms Erdos634.ZhangRat6.zhang_thm4_rational_all
#print axioms Erdos634.ZhangRat6.zhang_thm5_rational_all
