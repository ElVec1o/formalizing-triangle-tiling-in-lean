import Erdos634.Draft.ZhangThm5
import Erdos634.Draft.ZhangThm4
import Erdos634.Draft.BeesonCor5

/-!
# Zhang's Theorems 4 and 5 for every tile with commensurable sides

Zhang (arXiv 2512.22696) states his constructions for integer sides `a, b, c` ("by normalization").
Here the TILE is any `RTri` (a triangle in the plane with rational side lengths `a, b, c`), not the
integer model.  By `BeesonCor5.rat_scale`, `(a, b, c) = k (A, B, C)` with `A, B, C` coprime
naturals, `k` rational; the integer construction (Theorem 4 / Theorem 5) is dilated by the real
factor `k` about the origin (`scaleCongruentRegionDissection`), which carries the model onto a
triangle with sides `(a, b, c)`, congruent to the given tile by SSS.

* `zhang_thm4_rational`: tile with `c^2 = a^2 + b^2 + a b` (`|12| = a`, `|20| = b`, `|01| = c`):
  some equilateral triangle `Tri3 0 0 X` carries `n` tiles congruent to the tile.
* `zhang_thm5_rational`: tile with `a^2 + c b = c^2 + b^2` in `RTri` labelling (`|01| = c`,
  `|20| = b`, `|12| = a`; angle `pi/3` between sides `c` and `b`), not equilateral (`c != b`).
* `transfer`: the generic transfer lemma (any congruent region dissection with a model whose
  sides are `1/k` of a given triangle's gives one with that model, region scaled by `k`).
UNAUDITED.  Credit Zhang (arXiv 2512.22696), Beeson, Laczkovich.
-/

namespace Erdos634.ZhangRational

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.SssCongruent Erdos634.ZhangL1 Erdos634.ZhangPara Erdos634.ZhangThm4 Erdos634.ZhangThm5
  Erdos634.ZhangPi3 Erdos634.Realizable Erdos634.LaczL22 Erdos634.BeesonCor5

theorem transfer {N : ℕ} (C : CongruentRegionDissection N) (k : ℝ) (hk : 0 < k) (R : Tri)
    (hd : ∀ i j, dist (R.pts i) (R.pts j) = k * dist (C.model.pts i) (C.model.pts j)) :
    ∃ C' : CongruentRegionDissection N,
      C'.region = (homothetyEquiv 0 k hk.ne') '' C.region ∧ C'.model.Congruent R := by
  refine ⟨scaleCongruentRegionDissection 0 k hk.ne' C, rfl, ?_⟩
  apply congruent_of_dist
  intro i j
  show dist (homothetyEquiv 0 k hk.ne' (C.model.pts i)) (homothetyEquiv 0 k hk.ne' (C.model.pts j))
    = _
  rw [homothetyEquiv_apply, homothetyEquiv_apply, dist_homothety, abs_of_pos hk, hd]

theorem hd_of_three (R M : Tri) (k : ℝ)
    (h01 : dist (R.pts 0) (R.pts 1) = k * dist (M.pts 0) (M.pts 1))
    (h12 : dist (R.pts 1) (R.pts 2) = k * dist (M.pts 1) (M.pts 2))
    (h02 : dist (R.pts 0) (R.pts 2) = k * dist (M.pts 0) (M.pts 2)) :
    ∀ i j, dist (R.pts i) (R.pts j) = k * dist (M.pts i) (M.pts j) := by
  have htri : ∀ y : Fin 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide
  intro i j
  rcases htri i with rfl | rfl | rfl <;> rcases htri j with rfl | rfl | rfl <;>
    simp_all [dist_comm]

theorem tri3_scale (k : ℝ) (hk : 0 < k) (X : ℝ) :
    (homothetyEquiv 0 k hk.ne') '' Tri3 0 0 X = Tri3 0 0 (k * X) := by
  ext q
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨h1, h2, h3⟩ := hy
    rw [homothetyEquiv_apply]
    have e1 : uu 0 0 (AffineMap.homothety (0 : Plane) k y) = k * uu 0 0 y := by
      simp [uu, AffineMap.homothety_apply]; ring
    have e2 : vv 0 0 (AffineMap.homothety (0 : Plane) k y) = k * vv 0 0 y := by
      simp [vv, AffineMap.homothety_apply]; ring
    refine ⟨?_, ?_, ?_⟩
    · rw [e1]; positivity
    · rw [e2]; positivity
    · rw [e1, e2, ← mul_add]; exact mul_le_mul_of_nonneg_left h3 hk.le
  · intro hq
    obtain ⟨h1, h2, h3⟩ := hq
    refine ⟨k⁻¹ • q, ?_, ?_⟩
    · have e1 : uu 0 0 (k⁻¹ • q) = k⁻¹ * uu 0 0 q := by simp [uu]; ring
      have e2 : vv 0 0 (k⁻¹ • q) = k⁻¹ * vv 0 0 q := by simp [vv]; ring
      refine ⟨?_, ?_, ?_⟩
      · rw [e1]; positivity
      · rw [e2]; positivity
      · rw [e1, e2, ← mul_add]
        have : uu 0 0 q + vv 0 0 q ≤ k * X := h3
        calc k⁻¹ * (uu 0 0 q + vv 0 0 q) ≤ k⁻¹ * (k * X) := mul_le_mul_of_nonneg_left this (by positivity)
          _ = X := by field_simp
    · rw [homothetyEquiv_apply, AffineMap.homothety_apply]
      simp [smul_smul, hk.ne']

theorem coprime_thm4 (A B C : ℕ) (h : C * C = A * A + B * B + A * B)
    (hg : Nat.gcd (Nat.gcd A B) C = 1) : Nat.Coprime A B := by
  set d := Nat.gcd A B with hd
  obtain ⟨A', hA'⟩ := Nat.gcd_dvd_left A B
  obtain ⟨B', hB'⟩ := Nat.gcd_dvd_right A B
  rw [← hd] at hA' hB'
  have hdd : d * d ∣ C * C := ⟨A' * A' + B' * B' + A' * B', by rw [h, hA', hB']; ring⟩
  have hdC : d ∣ C := (Nat.pow_dvd_pow_iff two_ne_zero).mp (by simpa [sq] using hdd)
  have : d ∣ Nat.gcd d C := Nat.dvd_gcd dvd_rfl hdC
  rw [hg] at this
  exact Nat.dvd_one.mp this

theorem coprime_thm5 (a b c : ℕ) (h : c * c + a * b = a * a + b * b)
    (hg : ∀ d : ℕ, d ∣ a → d ∣ b → d ∣ c → d = 1) : Nat.Coprime a b := by
  set d := Nat.gcd a b with hd
  obtain ⟨A', hA'⟩ := Nat.gcd_dvd_left a b
  obtain ⟨B', hB'⟩ := Nat.gcd_dvd_right a b
  rw [← hd] at hA' hB'
  have h1 : d * d ∣ c * c + a * b := ⟨A' * A' + B' * B', by rw [h, hA', hB']; ring⟩
  have h2 : d * d ∣ a * b := ⟨A' * B', by rw [hA', hB']; ring⟩
  have hdd : d * d ∣ c * c := (Nat.dvd_add_left h2).mp h1
  have hdc : d ∣ c := (Nat.pow_dvd_pow_iff two_ne_zero).mp (by simpa [sq] using hdd)
  exact hg d (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b) hdc

theorem dist_eq_of_sq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ^ 2 = y ^ 2) : x = y :=
  (sq_eq_sq₀ hx hy).mp h

/-- **Zhang's Theorem 4 for every tile with rational sides (UNAUDITED).**  `R.Δ` has sides
`|12| = a`, `|20| = b`, `|01| = c` (rational) with `c^2 = a^2 + b^2 + a b`.  Then some equilateral
triangle `Tri3 0 0 X` carries `n` triangles congruent to `R.Δ`. -/
theorem zhang_thm4_rational (R : RTri) (hrel : R.c ^ 2 = R.a ^ 2 + R.b ^ 2 + R.a * R.b) :
    ∃ (X : ℝ) (n : ℕ), 0 < X ∧ ∃ C : CongruentRegionDissection n,
      C.region = Tri3 0 0 X ∧ C.model.Congruent R.Δ := by
  obtain ⟨A, B, C, k, hk, hA, hB, hC, ea, eb, ec, hg⟩ := rat_scale R.a R.b R.c R.pa R.pb R.pc
  have hq : (C : ℚ) * C = A * A + B * B + A * B := by
    have h1 : k ^ 2 * ((C : ℚ) * C) = k ^ 2 * (A * A + B * B + A * B) := by
      have := hrel; rw [ea, eb, ec] at this; nlinarith [this]
    exact mul_left_cancel₀ (by positivity) h1
  have hh : C * C = A * A + B * B + A * B := by exact_mod_cast hq
  have hcop := coprime_thm4 A B C hh hg
  have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  set m := 3 * ((C * C - A - B) / (A * B) + 1) with hm
  have key := zhang_thm4 A B C hA hB hC hh hcop m le_rfl
  unfold EquiConstr at key
  obtain ⟨C0, hr, hmod⟩ := key
  have hcR : (C : ℝ) ^ 2 = (A : ℝ) ^ 2 + (B : ℝ) ^ 2 + A * B := by exact_mod_cast (by nlinarith [hh] : C ^ 2 = A ^ 2 + B ^ 2 + A * B)
  have hA' : (0 : ℝ) < (A : ℝ) := Nat.cast_pos.mpr hA
  have hB' : (0 : ℝ) < (B : ℝ) := Nat.cast_pos.mpr hB
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
  refine ⟨(k : ℝ) * ((m : ℝ) * ((A : ℝ) * B)), m * m * (A * B),
    mul_pos hkr (mul_pos (Nat.cast_pos.mpr (by rw [hm]; positivity)) (mul_pos hA' hB')), C1, ?_, hcong⟩
  rw [hreg, hr, tri3_scale (k : ℝ) hkr]

/-- **Zhang's Theorem 5 for every non-equilateral tile with rational sides and angle `pi/3`
(UNAUDITED).**  `R.Δ` has `|12| = a`, `|20| = b`, `|01| = c` with `a^2 + c b = c^2 + b^2`
(angle `pi/3` between the sides `c`, `b`), and `c != b`. -/
theorem zhang_thm5_rational (R : RTri) (hrel : R.a ^ 2 + R.c * R.b = R.c ^ 2 + R.b ^ 2)
    (hne : R.c ≠ R.b) :
    ∃ (X : ℝ) (n : ℕ), 0 < X ∧ ∃ C : CongruentRegionDissection n,
      C.region = Tri3 0 0 X ∧ C.model.Congruent R.Δ := by
  obtain ⟨A, B, C, k, hk, hA, hB, hC, ea, eb, ec, hg⟩ := rat_scale R.a R.b R.c R.pa R.pb R.pc
  have hq : (A : ℚ) * A + C * B = C * C + B * B := by
    have h1 : k ^ 2 * ((A : ℚ) * A + C * B) = k ^ 2 * (C * C + B * B) := by
      have := hrel; rw [ea, eb, ec] at this; nlinarith [this]
    exact mul_left_cancel₀ (by positivity) h1
  have hh : A * A + C * B = C * C + B * B := by exact_mod_cast hq
  -- Zhang's (a, b, c) = (C, B, A)
  have hcop : Nat.Coprime C B := coprime_thm5 C B A hh (fun d h1 h2 h3 =>
    Nat.dvd_one.mp (hg ▸ Nat.dvd_gcd (Nat.dvd_gcd h3 h2) h1))
  have h1 : 1 < C * B := by
    by_contra hcon
    have hC1 : C = 1 := by nlinarith [Nat.mul_pos hC hB]
    have hB1 : B = 1 := by nlinarith [Nat.mul_pos hC hB]
    apply hne
    rw [ec, eb, hC1, hB1]
  have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  set m := 3 * ((C * C + B * B - C - B) / (C * B) + 1) with hm
  have key := zhang_thm5 C B A hC hB hA h1 hh hcop m le_rfl
  unfold EquiConstr3 at key
  obtain ⟨C0, hr, hmod⟩ := key
  have hC' : (0 : ℝ) < (C : ℝ) := Nat.cast_pos.mpr hC
  have hB' : (0 : ℝ) < (B : ℝ) := Nat.cast_pos.mpr hB
  have hcR : (A : ℝ) ^ 2 = (C : ℝ) ^ 2 - C * B + (B : ℝ) ^ 2 := by
    have : (A : ℝ) ^ 2 + C * B = C ^ 2 + B ^ 2 := by exact_mod_cast (by nlinarith [hh] : A ^ 2 + C * B = C ^ 2 + B ^ 2)
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
  refine ⟨(k : ℝ) * ((m : ℝ) * ((C : ℝ) * B)), m * m * (C * B),
    mul_pos hkr (mul_pos (Nat.cast_pos.mpr (by rw [hm]; positivity)) (mul_pos hC' hB')), C1, ?_, hcong⟩
  rw [hreg, hr, tri3_scale (k : ℝ) hkr]

/-! ### Witnesses: every hypothesis is satisfiable by a non-integer rational tile -/

/-- The integer model tile `Rmodel A B` scaled by the rational `k` is an `RTri` with sides
`|12| = kA`, `|20| = kB`, `|01| = kC`. -/
theorem exists_RTri_thm4 (A B C : ℕ) (hA : 0 < A) (hB : 0 < B) (hh : C * C = A * A + B * B + A * B)
    (k : ℚ) (hk : 0 < k) :
    ∃ R : RTri, R.a = k * A ∧ R.b = k * B ∧ R.c = k * C := by
  have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hA' : (0 : ℝ) < (A : ℝ) := Nat.cast_pos.mpr hA
  have hB' : (0 : ℝ) < (B : ℝ) := Nat.cast_pos.mpr hB
  have hcR : (C : ℝ) ^ 2 = (A : ℝ) ^ 2 + (B : ℝ) ^ 2 + A * B := by
    exact_mod_cast (by nlinarith [hh] : C ^ 2 = A ^ 2 + B ^ 2 + A * B)
  have n01 := dist_eq_of_sq dist_nonneg (Nat.cast_nonneg C) (R_d01 (c := (C : ℝ)) hA' hB' hcR)
  have n12 := dist_eq_of_sq dist_nonneg (Nat.cast_nonneg A) (R_d12 hA' hB')
  have n02 := dist_eq_of_sq dist_nonneg (Nat.cast_nonneg B) (R_d02 hA' hB')
  have hC : 0 < C := by
    rcases Nat.eq_zero_or_pos C with h | h
    · subst h; nlinarith [Nat.mul_pos hA hB]
    · exact h
  refine ⟨{ Δ := Erdos634.DissectionMap.mapTri (homothetyEquiv 0 (k : ℝ) hkr.ne') (Rmodel hA' hB')
            a := k * A, b := k * B, c := k * C, ha := ?_, hb := ?_, hc := ?_,
            pa := by positivity, pb := by positivity, pc := by positivity }, rfl, rfl, rfl⟩
  · show dist (homothetyEquiv 0 (k : ℝ) hkr.ne' ((Rmodel hA' hB').pts 1))
      (homothetyEquiv 0 (k : ℝ) hkr.ne' ((Rmodel hA' hB').pts 2)) = _
    rw [homothetyEquiv_apply, homothetyEquiv_apply, dist_homothety, abs_of_pos hkr, n12]; push_cast; ring
  · show dist (homothetyEquiv 0 (k : ℝ) hkr.ne' ((Rmodel hA' hB').pts 2))
      (homothetyEquiv 0 (k : ℝ) hkr.ne' ((Rmodel hA' hB').pts 0)) = _
    rw [homothetyEquiv_apply, homothetyEquiv_apply, dist_homothety, abs_of_pos hkr, dist_comm, n02]
    push_cast; ring
  · show dist (homothetyEquiv 0 (k : ℝ) hkr.ne' ((Rmodel hA' hB').pts 0))
      (homothetyEquiv 0 (k : ℝ) hkr.ne' ((Rmodel hA' hB').pts 1)) = _
    rw [homothetyEquiv_apply, homothetyEquiv_apply, dist_homothety, abs_of_pos hkr, n01]; push_cast; ring

/-- Non-vacuity of `zhang_thm4_rational` at a NON-integer tile: sides `(3/2, 5/2, 7/2)`. -/
theorem zhang_thm4_rational_wit_half :
    ∃ R : RTri, R.a = 3 / 2 ∧ R.b = 5 / 2 ∧ R.c = 7 / 2 ∧
      ∃ (X : ℝ) (n : ℕ), 0 < X ∧ ∃ C : CongruentRegionDissection n,
        C.region = Tri3 0 0 X ∧ C.model.Congruent R.Δ := by
  obtain ⟨R, h1, h2, h3⟩ := exists_RTri_thm4 3 5 7 (by norm_num) (by norm_num) (by norm_num)
    (1 / 2) (by norm_num)
  have ha : R.a = 3 / 2 := by rw [h1]; norm_num
  have hb : R.b = 5 / 2 := by rw [h2]; norm_num
  have hc : R.c = 7 / 2 := by rw [h3]; norm_num
  exact ⟨R, ha, hb, hc, zhang_thm4_rational R (by rw [ha, hb, hc]; norm_num)⟩

/-- Non-vacuity of `zhang_thm5_rational`: sides `|12| = 7/3`, `|20| = 8/3`, `|01| = 5/3` (the tile
`(5,8,7)` scaled by `1/3`; `c != b`). -/
theorem zhang_thm5_rational_wit_third :
    ∃ R : RTri, R.a = 7 / 3 ∧ R.b = 8 / 3 ∧ R.c = 5 / 3 ∧
      ∃ (X : ℝ) (n : ℕ), 0 < X ∧ ∃ C : CongruentRegionDissection n,
        C.region = Tri3 0 0 X ∧ C.model.Congruent R.Δ := by
  have hkr : (0 : ℝ) < ((1 / 3 : ℚ) : ℝ) := by norm_num
  have hC' : (0 : ℝ) < ((5 : ℕ) : ℝ) := by norm_num
  have hB' : (0 : ℝ) < ((8 : ℕ) : ℝ) := by norm_num
  have n01 := dist_eq_of_sq dist_nonneg (Nat.cast_nonneg 5) (R3_01 hC' hB')
  have n02 := dist_eq_of_sq dist_nonneg (Nat.cast_nonneg 8) (R3_02 hC' hB')
  have n12 : dist ((R3 hC' hB').pts 1) ((R3 hC' hB').pts 2) = ((7 : ℕ) : ℝ) :=
    dist_eq_of_sq dist_nonneg (Nat.cast_nonneg 7) ((R3_12 hC' hB').trans (by norm_num))
  let R : RTri :=
    { Δ := Erdos634.DissectionMap.mapTri (homothetyEquiv 0 ((1 / 3 : ℚ) : ℝ) hkr.ne') (R3 hC' hB')
      a := 7 / 3, b := 8 / 3, c := 5 / 3
      ha := by
        show dist (homothetyEquiv 0 _ hkr.ne' ((R3 hC' hB').pts 1))
          (homothetyEquiv 0 _ hkr.ne' ((R3 hC' hB').pts 2)) = _
        rw [homothetyEquiv_apply, homothetyEquiv_apply, dist_homothety, abs_of_pos hkr, n12]
        push_cast; norm_num
      hb := by
        show dist (homothetyEquiv 0 _ hkr.ne' ((R3 hC' hB').pts 2))
          (homothetyEquiv 0 _ hkr.ne' ((R3 hC' hB').pts 0)) = _
        rw [homothetyEquiv_apply, homothetyEquiv_apply, dist_homothety, abs_of_pos hkr, dist_comm, n02]
        push_cast; norm_num
      hc := by
        show dist (homothetyEquiv 0 _ hkr.ne' ((R3 hC' hB').pts 0))
          (homothetyEquiv 0 _ hkr.ne' ((R3 hC' hB').pts 1)) = _
        rw [homothetyEquiv_apply, homothetyEquiv_apply, dist_homothety, abs_of_pos hkr, n01]
        push_cast; norm_num
      pa := by norm_num, pb := by norm_num, pc := by norm_num }
  exact ⟨R, rfl, rfl, rfl, zhang_thm5_rational R (by show (7/3 : ℚ)^2 + 5/3 * (8/3) = (5/3)^2 + (8/3)^2; norm_num)
    (by show (5 / 3 : ℚ) ≠ 8 / 3; norm_num)⟩

end Erdos634.ZhangRational
