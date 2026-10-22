import Erdos634.Draft.ZhangRat6Equi

/-!
# Zhang Thm 4 and Thm 5: `ceil` versus `floor + 1` (arXiv 2512.22696v4)

Zhang's threshold is `M = 3 ceil((c^2-a-b)/(ab))` (Thm 4) and `3 ceil((a^2+b^2-a-b)/(ab))` (Thm 5).  The Lean
integer theorems use `3 (floor + 1)`.  They agree exactly when `ab` does not divide the numerator.  Here this is
PROVED for every admissible tile:
* `not_dvd_thm4`: `C*C = A*A+B*B+A*B`, `A,B > 0`, coprime  =>  `A*B` does not divide `C*C - A - B`;
* `not_dvd_thm5`: `C*C + A*B = A*A + B*B`, coprime, `1 < A*B`  =>  `A*B` does not divide `A*A+B*B-A-B`;
* `ceil_thm4`, `ceil_thm5`: `Nat.ceil` of the rational quotient equals floor + 1;
* `zhang_thm4_rational_ceil`, `zhang_thm5_rational_ceil`: Thm 4/5 for every rational tile with the PRINTED threshold
  `M = 3 * Nat.ceil(...)`.
Mechanism: `A | B(B-1)`, `B | A(A-1)`, coprimality gives `A | B-1`, `B | A-1`; for `A,B >= 2` this forces `A < B < A`;
for `A = 1` or `B = 1` the relation is a square strictly between consecutive squares.  UNAUDITED.
Credit Zhang (arXiv 2512.22696v4), Beeson, Beeson-Zhang, Laczkovich.
-/

namespace Erdos634.ZhangRat7Ceil

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.SssCongruent Erdos634.ZhangL1 Erdos634.ZhangPara Erdos634.ZhangThm4 Erdos634.ZhangThm5
  Erdos634.ZhangPi3 Erdos634.Realizable Erdos634.LaczL22 Erdos634.BeesonCor5 Erdos634.ZhangRational

theorem divs (A B : ℕ) (hcop : Nat.Coprime A B) (t : ℤ) (e : ℤ) (he : e = A * B ∨ e = 0)
    (h : (A : ℤ) ^ 2 + B ^ 2 + e - A - B = A * B * t) :
    (A : ℤ) ∣ B - 1 ∧ (B : ℤ) ∣ A - 1 := by
  have hc : IsCoprime (A : ℤ) B := Nat.isCoprime_iff_coprime.mpr hcop
  have h1 : (A : ℤ) ∣ B * (B - 1) := by
    rcases he with he | he
    · exact ⟨B * t - A - B + 1, by subst he; linear_combination h⟩
    · exact ⟨B * t - A + 1, by subst he; linear_combination h⟩
  have h2 : (B : ℤ) ∣ A * (A - 1) := by
    rcases he with he | he
    · exact ⟨A * t - B - A + 1, by subst he; linear_combination h⟩
    · exact ⟨A * t - B + 1, by subst he; linear_combination h⟩
  exact ⟨hc.dvd_of_dvd_mul_left h1, hc.symm.dvd_of_dvd_mul_left h2⟩

theorem both_ge2 (A B : ℕ) (hA : 2 ≤ A) (hB : 2 ≤ B) (d1 : (A : ℤ) ∣ B - 1) (d2 : (B : ℤ) ∣ A - 1) : False := by
  have l1 := Int.le_of_dvd (by omega) d1
  have l2 := Int.le_of_dvd (by omega) d2
  omega

theorem sq_between (X C : ℕ) (hX : 1 ≤ X) (h : C * C = X * X + X + 1) : False := by
  rcases Nat.lt_or_ge X C with h1 | h1
  · nlinarith
  · nlinarith

theorem sq_between' (X C : ℕ) (hX : 2 ≤ X) (h : C * C + X = X * X + 1) : False := by
  rcases Nat.lt_or_ge (X - 1) C with h1 | h1
  · obtain ⟨Y, rfl⟩ : ∃ Y, X = Y + 2 := ⟨X - 2, by omega⟩
    have : Y + 1 < C := by omega
    nlinarith
  · obtain ⟨Y, rfl⟩ : ∃ Y, X = Y + 2 := ⟨X - 2, by omega⟩
    have : C ≤ Y + 1 := by omega
    nlinarith

theorem not_dvd_thm4 (A B C : ℕ) (hA : 0 < A) (hB : 0 < B) (hh : C * C = A * A + B * B + A * B)
    (hcop : Nat.Coprime A B) : ¬ (A * B ∣ C * C - A - B) := by
  rintro ⟨t, ht⟩
  have hle : A + B ≤ C * C := by nlinarith [Nat.mul_pos hA hB]
  have key : C * C = A * B * t + A + B := by
    generalize C * C = X at ht hle ⊢
    generalize A * B * t = Y at ht ⊢
    omega
  have hz : (A : ℤ) ^ 2 + B ^ 2 + (A * B : ℤ) - A - B = A * B * (t : ℤ) := by
    have k1 : ((C : ℤ)) * C = A * B * t + A + B := by exact_mod_cast key
    have hh' : ((C : ℤ)) * C = A * A + B * B + A * B := by exact_mod_cast hh
    nlinarith [k1, hh']
  obtain ⟨d1, d2⟩ := divs A B hcop t _ (Or.inl rfl) hz
  rcases Nat.lt_or_ge A 2 with h1 | h1
  · have : A = 1 := by omega
    subst this
    exact sq_between B C hB (by nlinarith [hh])
  rcases Nat.lt_or_ge B 2 with h2 | h2
  · have : B = 1 := by omega
    subst this
    exact sq_between A C hA (by nlinarith [hh])
  exact both_ge2 A B h1 h2 d1 d2

theorem not_dvd_thm5 (A B C : ℕ) (hA : 0 < A) (hB : 0 < B) (h1 : 1 < A * B)
    (hh : C * C + A * B = A * A + B * B) (hcop : Nat.Coprime A B) : ¬ (A * B ∣ A * A + B * B - A - B) := by
  rintro ⟨t, ht⟩
  have hle : A + B ≤ A * A + B * B := by nlinarith
  have key : A * A + B * B = A * B * t + A + B := by
    generalize A * A + B * B = X at ht hle ⊢
    generalize A * B * t = Y at ht ⊢
    omega
  have hz : (A : ℤ) ^ 2 + B ^ 2 + 0 - A - B = A * B * (t : ℤ) := by
    have k1 : ((A : ℤ)) * A + B * B = A * B * t + A + B := by exact_mod_cast key
    nlinarith [k1]
  obtain ⟨d1, d2⟩ := divs A B hcop t _ (Or.inr rfl) hz
  rcases Nat.lt_or_ge A 2 with g1 | g1
  · have : A = 1 := by omega
    subst this
    have hB2 : 2 ≤ B := by omega
    exact sq_between' B C hB2 (by nlinarith [hh])
  rcases Nat.lt_or_ge B 2 with g2 | g2
  · have : B = 1 := by omega
    subst this
    exact sq_between' A C g1 (by nlinarith [hh])
  exact both_ge2 A B g1 g2 d1 d2

theorem ceil_of_not_dvd (n d : ℕ) (hd : 0 < d) (hn : ¬ d ∣ n) (q : ℚ) (hq : q = (n : ℚ) / d) :
    ⌈q⌉₊ = n / d + 1 := by
  have hr : 0 < n % d := Nat.pos_of_ne_zero (fun h => hn (Nat.dvd_of_mod_eq_zero h))
  have hrl : n % d < d := Nat.mod_lt _ hd
  have hdiv : d * (n / d) + n % d = n := Nat.div_add_mod n d
  rw [Nat.ceil_eq_iff (Nat.succ_ne_zero _)]
  try simp only [Nat.add_sub_cancel, Nat.succ_sub_one]
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  rw [hq, lt_div_iff₀ hdq, div_le_iff₀ hdq]
  constructor
  · push_cast [Nat.succ_eq_add_one]
    have : ((d * (n / d) + n % d : ℕ) : ℚ) = n := by exact_mod_cast hdiv
    push_cast at this
    have : (0 : ℚ) < ((n % d : ℕ) : ℚ) := by exact_mod_cast hr
    nlinarith
  · push_cast [Nat.succ_eq_add_one]
    have : ((d * (n / d) + n % d : ℕ) : ℚ) = n := by exact_mod_cast hdiv
    push_cast at this
    have : ((n % d : ℕ) : ℚ) < d := by exact_mod_cast hrl
    nlinarith

theorem ceil_thm4 (A B C : ℕ) (hA : 0 < A) (hB : 0 < B) (hh : C * C = A * A + B * B + A * B)
    (hcop : Nat.Coprime A B) :
    ⌈(((C : ℚ) * C - A - B) / (A * B))⌉₊ = (C * C - A - B) / (A * B) + 1 := by
  have hle : A + B ≤ C * C := by nlinarith [Nat.mul_pos hA hB]
  refine ceil_of_not_dvd (C * C - A - B) (A * B) (Nat.mul_pos hA hB) (not_dvd_thm4 A B C hA hB hh hcop) _ ?_
  have e : ((C * C - A - B : ℕ) : ℚ) = (C : ℚ) * C - A - B := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  rw [e]; push_cast; ring

theorem ceil_thm5 (A B C : ℕ) (hA : 0 < A) (hB : 0 < B) (h1 : 1 < A * B)
    (hh : C * C + A * B = A * A + B * B) (hcop : Nat.Coprime A B) :
    ⌈(((A : ℚ) * A + B * B - A - B) / (A * B))⌉₊ = (A * A + B * B - A - B) / (A * B) + 1 := by
  have hle : A + B ≤ A * A + B * B := by nlinarith
  refine ceil_of_not_dvd (A * A + B * B - A - B) (A * B) (Nat.mul_pos hA hB)
    (not_dvd_thm5 A B C hA hB h1 hh hcop) _ ?_
  have e : ((A * A + B * B - A - B : ℕ) : ℚ) = (A : ℚ) * A + B * B - A - B := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  rw [e]; push_cast; ring

/-- **Thm 4 with the printed threshold** `M = 3 ceil((c^2-a-b)/(ab))`, every rational tile, all `m >= M`. -/
theorem zhang_thm4_rational_ceil (R : RTri) (hrel : R.c ^ 2 = R.a ^ 2 + R.b ^ 2 + R.a * R.b) :
    ∃ (A B C : ℕ) (k : ℚ), 0 < k ∧ 0 < A ∧ 0 < B ∧ R.a = k * A ∧ R.b = k * B ∧ Nat.Coprime A B ∧
      C * C = A * A + B * B + A * B ∧
      ∀ m : ℕ, 3 * ⌈(((C : ℚ) * C - A - B) / (A * B))⌉₊ ≤ m →
        ∃ C1 : CongruentRegionDissection (m * m * (A * B)),
          C1.region = Tri3 0 0 ((k : ℝ) * ((m : ℝ) * ((A : ℝ) * B))) ∧ C1.model.Congruent R.Δ := by
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
  refine ⟨A, B, C, k, hk, hA, hB, ea, eb, hcop, hh, fun m hm => ?_⟩
  rw [ceil_thm4 A B C hA hB hh hcop] at hm
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

/-- **Thm 5 with the printed threshold** `M = 3 ceil((a^2+b^2-a-b)/(ab))`, `pi/3` tile. -/
theorem zhang_thm5_rational_ceil (R : RTri) (hrel : R.a ^ 2 + R.c * R.b = R.c ^ 2 + R.b ^ 2)
    (hne : R.c ≠ R.b) :
    ∃ (P Q : ℕ) (k : ℚ), 0 < k ∧ 0 < P ∧ 0 < Q ∧ R.c = k * P ∧ R.b = k * Q ∧ Nat.Coprime P Q ∧
      1 < P * Q ∧
      ∀ m : ℕ, 3 * ⌈(((P : ℚ) * P + Q * Q - P - Q) / (P * Q))⌉₊ ≤ m →
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
  refine ⟨C, B, k, hk, hC, hB, ec, eb, hcop, h1, fun m hm => ?_⟩
  rw [ceil_thm5 C B A hC hB h1 (by omega) hcop] at hm
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

end Erdos634.ZhangRat7Ceil

#print axioms Erdos634.ZhangRat7Ceil.ceil_thm4
#print axioms Erdos634.ZhangRat7Ceil.ceil_thm5
#print axioms Erdos634.ZhangRat7Ceil.zhang_thm4_rational_ceil
#print axioms Erdos634.ZhangRat7Ceil.zhang_thm5_rational_ceil
