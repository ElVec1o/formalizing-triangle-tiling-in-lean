import Erdos634.Draft.ZhangRational
import Erdos634.Draft.ZhangSporadic
import Erdos634.Draft.ZhangProp6
import Erdos634.Draft.ZhangProp6b
import Erdos634.Draft.ZhangProp11
import Erdos634.Draft.ZhangProp11b
import Erdos634.Draft.ZhangThm7

/-!
# Zhang's Props 6, 8, 9, 10, 11 and Theorem 7 for every tile with rational sides

Companion of `ZhangRational` (Thms 4, 5).  The tile is any `RTri R` with `R.c^2 = R.a^2 + R.b^2 +
R.a R.b` (sides `|12| = a`, `|20| = b`, `|01| = c`).  By `rat_scale` its sides are `k (A, B, C)` with
`A, B, C` coprime naturals, `k > 0` rational; the integer statement is dilated by `k`
(`transfer`): the conclusion is a `CongruentRegionDissection` of the `k`-dilate of the integer
region whose model is congruent to `R.Δ`.  UNAUDITED.  Credit Zhang (arXiv 2512.22696), Beeson,
Beeson-Zhang, Laczkovich.
-/

namespace Erdos634.ZhangRat

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.SssCongruent Erdos634.ZhangL1 Erdos634.ZhangPara Erdos634.ZhangThm4
  Erdos634.LaczL22 Erdos634.ZhangPi3 Erdos634.Realizable Erdos634.BeesonCor5 Erdos634.ZhangRational Erdos634.ZhangSporadic

/-- The `k`-dilate of a planar set. -/
def dil (k : ℝ) (S : Set Plane) : Set Plane := (fun p : Plane => k • p) '' S

theorem hom_image_eq (k : ℝ) (hk : 0 < k) (S : Set Plane) :
    (homothetyEquiv 0 k hk.ne') '' S = dil k S := by
  unfold dil
  refine Set.image_congr (fun y _ => ?_)
  simp [homothetyEquiv_apply, AffineMap.homothety_apply]

/-- Normalised data of a rational `(a,b,c)` tile with `c^2 = a^2+b^2+ab`. -/
theorem rat_data (R : RTri) (hrel : R.c ^ 2 = R.a ^ 2 + R.b ^ 2 + R.a * R.b) :
    ∃ (A B C : ℕ) (k : ℚ), 0 < k ∧ 0 < A ∧ 0 < B ∧ 0 < C ∧ C * C = A * A + B * B + A * B ∧
      Nat.Coprime A B ∧ R.a = k * A ∧ R.b = k * B ∧ R.c = k * C := by
  obtain ⟨A, B, C, k, hk, hA, hB, hC, ea, eb, ec, hg⟩ := rat_scale R.a R.b R.c R.pa R.pb R.pc
  have hq : (C : ℚ) * C = A * A + B * B + A * B := by
    have h1 : k ^ 2 * ((C : ℚ) * C) = k ^ 2 * (A * A + B * B + A * B) := by
      have := hrel; rw [ea, eb, ec] at this; nlinarith [this]
    exact mul_left_cancel₀ (by positivity) h1
  have hh : C * C = A * A + B * B + A * B := by exact_mod_cast hq
  exact ⟨A, B, C, k, hk, hA, hB, hC, hh, coprime_thm4 A B C hh hg, ea, eb, ec⟩

/-- Generic transfer of an integer-model `Dis` to the rational tile. -/
theorem rat_dis (R : RTri) (A B C : ℕ) (k : ℚ) (hk : 0 < k) (hA : 0 < A) (hB : 0 < B)
    (hh : C * C = A * A + B * B + A * B)
    (ea : R.a = k * A) (eb : R.b = k * B) (ec : R.c = k * C) {S : Set Plane} {n : ℕ}
    (h : Dis (Rmodel (Nat.cast_pos.mpr hA : (0:ℝ) < A) (Nat.cast_pos.mpr hB : (0:ℝ) < B)) S n) :
    ∃ C1 : CongruentRegionDissection n, C1.region = dil (k : ℝ) S ∧ C1.model.Congruent R.Δ := by
  obtain ⟨C0, hr, hmod⟩ := h
  have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hA' : (0 : ℝ) < (A : ℝ) := Nat.cast_pos.mpr hA
  have hB' : (0 : ℝ) < (B : ℝ) := Nat.cast_pos.mpr hB
  have hcR : (C : ℝ) ^ 2 = (A : ℝ) ^ 2 + (B : ℝ) ^ 2 + A * B := by
    exact_mod_cast (by nlinarith [hh] : C ^ 2 = A ^ 2 + B ^ 2 + A * B)
  have n01 := dist_eq_of_sq dist_nonneg (Nat.cast_nonneg C) (R_d01 (c := (C : ℝ)) hA' hB' hcR)
  have n12 := dist_eq_of_sq dist_nonneg (Nat.cast_nonneg A) (R_d12 hA' hB')
  have n02 := dist_eq_of_sq dist_nonneg (Nat.cast_nonneg B) (R_d02 hA' hB')
  obtain ⟨C1, hreg, hcong⟩ := transfer C0 (k : ℝ) hkr R.Δ (by
    rw [hmod]
    apply hd_of_three
    · rw [n01, R.hc, ec]; push_cast; ring
    · rw [n12, R.ha, ea]; push_cast; ring
    · rw [dist_comm, n02, R.hb, eb]; push_cast; ring)
  exact ⟨C1, by rw [hreg, hr, hom_image_eq (k : ℝ) hkr], hcong⟩

/-- `EquiConstr` for the data, at `m = 3 M0`. -/
theorem equi_data (A B C : ℕ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hh : C * C = A * A + B * B + A * B) (hcop : Nat.Coprime A B) :
    ∃ m : ℕ, 0 < m ∧ EquiConstr A B hA hB ((m : ℝ) * ((A : ℝ) * B)) (m * m * (A * B)) := by
  refine ⟨3 * ((C * C - A - B) / (A * B) + 1), by positivity, ?_⟩
  exact zhang_thm4 A B C hA hB hC hh hcop _ le_rfl

/-! ### Props 8, 9, 10 -/

section p8
variable (R : RTri) (hrel : R.c ^ 2 = R.a ^ 2 + R.b ^ 2 + R.a * R.b)
include hrel

/-- Prop 9 (1), rational tile: dilated triangle `E, (-m B^2, 0), (m A B, 0)`, `m^2 B (A+B)` tiles. -/
theorem zhang_prop9_1_rational :
    ∃ (A B m : ℕ) (k : ℚ) (hA : 0 < A) (hB : 0 < B), 0 < k ∧ 0 < m ∧ R.a = k * A ∧ R.b = k * B ∧
      ∃ C1 : CongruentRegionDissection (m * m * (B * (A + B))),
        C1.region = dil (k : ℝ) (TriSet (((m : ℝ) * ((A : ℝ) * B)) / 2)
          (((m : ℝ) * ((A : ℝ) * B)) * zs / 2) (-((m : ℝ) * B * B)) 0 ((m : ℝ) * ((A : ℝ) * B)) 0) ∧
        C1.model.Congruent R.Δ := by
  obtain ⟨A, B, C, k, hk, hA, hB, hC, hh, hcop, ea, eb, ec⟩ := rat_data R hrel
  obtain ⟨m, hm, hE⟩ := equi_data A B C hA hB hC hh hcop
  exact ⟨A, B, m, k, hA, hB, hk, hm, ea, eb,
    rat_dis R A B C k hk hA hB hh ea eb ec (zhang_prop9_1 A B m hA hB hm hE)⟩

theorem zhang_prop9_2_rational :
    ∃ (A B m : ℕ) (k : ℚ) (hA : 0 < A) (hB : 0 < B), 0 < k ∧ 0 < m ∧ R.a = k * A ∧ R.b = k * B ∧
      ∃ C1 : CongruentRegionDissection (m * m * (A * (A + B))),
        C1.region = dil (k : ℝ) (TriSet (((m : ℝ) * ((A : ℝ) * B)) / 2)
          (((m : ℝ) * ((A : ℝ) * B)) * zs / 2) (-((m : ℝ) * A * A)) 0 ((m : ℝ) * ((A : ℝ) * B)) 0) ∧
        C1.model.Congruent R.Δ := by
  obtain ⟨A, B, C, k, hk, hA, hB, hC, hh, hcop, ea, eb, ec⟩ := rat_data R hrel
  obtain ⟨m, hm, hE⟩ := equi_data A B C hA hB hC hh hcop
  exact ⟨A, B, m, k, hA, hB, hk, hm, ea, eb,
    rat_dis R A B C k hk hA hB hh ea eb ec (zhang_prop9_2 A B m hA hB hm hE)⟩

theorem zhang_prop8_1_rational :
    ∃ (A B m : ℕ) (k : ℚ) (hA : 0 < A) (hB : 0 < B), 0 < k ∧ 0 < m ∧ R.a = k * A ∧ R.b = k * B ∧
      ∃ C1 : CongruentRegionDissection (m * m * (B * (A + 2 * B))),
        C1.region = dil (k : ℝ) (TriSet (((m : ℝ) * ((A : ℝ) * B)) / 2)
          (((m : ℝ) * ((A : ℝ) * B)) * zs / 2) (-((m : ℝ) * B * B)) 0
          (((m : ℝ) * ((A : ℝ) * B)) + (m : ℝ) * B * B) 0) ∧
        C1.model.Congruent R.Δ := by
  obtain ⟨A, B, C, k, hk, hA, hB, hC, hh, hcop, ea, eb, ec⟩ := rat_data R hrel
  obtain ⟨m, hm, hE⟩ := equi_data A B C hA hB hC hh hcop
  exact ⟨A, B, m, k, hA, hB, hk, hm, ea, eb,
    rat_dis R A B C k hk hA hB hh ea eb ec (zhang_prop8_1 A B m hA hB hm hE)⟩

theorem zhang_prop8_2_rational :
    ∃ (A B m : ℕ) (k : ℚ) (hA : 0 < A) (hB : 0 < B), 0 < k ∧ 0 < m ∧ R.a = k * A ∧ R.b = k * B ∧
      ∃ C1 : CongruentRegionDissection (m * m * (A * (B + 2 * A))),
        C1.region = dil (k : ℝ) (TriSet (((m : ℝ) * ((A : ℝ) * B)) / 2)
          (((m : ℝ) * ((A : ℝ) * B)) * zs / 2) (-((m : ℝ) * A * A)) 0
          (((m : ℝ) * ((A : ℝ) * B)) + (m : ℝ) * A * A) 0) ∧
        C1.model.Congruent R.Δ := by
  obtain ⟨A, B, C, k, hk, hA, hB, hC, hh, hcop, ea, eb, ec⟩ := rat_data R hrel
  obtain ⟨m, hm, hE⟩ := equi_data A B C hA hB hC hh hcop
  exact ⟨A, B, m, k, hA, hB, hk, hm, ea, eb,
    rat_dis R A B C k hk hA hB hh ea eb ec (zhang_prop8_2 A B m hA hB hm hE)⟩

theorem zhang_prop10_1_rational :
    ∃ (A B m : ℕ) (k : ℚ) (hA : 0 < A) (hB : 0 < B), 0 < k ∧ 0 < m ∧ R.a = k * A ∧ R.b = k * B ∧
      ∃ C1 : CongruentRegionDissection (m * m * ((A + B) * (2 * A + B))),
        C1.region = dil (k : ℝ) (TriSet (-((m : ℝ) * A * A)) 0
          (((m : ℝ) * ((A : ℝ) * B)) + (m : ℝ) * (A + B) * B / 2)
          (-((m : ℝ) * (A + B) * B * zs / 2))
          (((m : ℝ) * ((A : ℝ) * B)) / 2) (((m : ℝ) * ((A : ℝ) * B)) * zs / 2)) ∧
        C1.model.Congruent R.Δ := by
  obtain ⟨A, B, C, k, hk, hA, hB, hC, hh, hcop, ea, eb, ec⟩ := rat_data R hrel
  obtain ⟨m, hm, hE⟩ := equi_data A B C hA hB hC hh hcop
  exact ⟨A, B, m, k, hA, hB, hk, hm, ea, eb,
    rat_dis R A B C k hk hA hB hh ea eb ec (zhang_prop10_1 A B m hA hB hm hE)⟩

theorem zhang_prop10_2_rational :
    ∃ (A B m : ℕ) (k : ℚ) (hA : 0 < A) (hB : 0 < B), 0 < k ∧ 0 < m ∧ R.a = k * A ∧ R.b = k * B ∧
      ∃ C1 : CongruentRegionDissection (m * m * ((A + B) * (A + 2 * B))),
        C1.region = dil (k : ℝ) (TriSet (-((m : ℝ) * B * B)) 0
          (((m : ℝ) * ((A : ℝ) * B)) + (m : ℝ) * (A + B) * A / 2)
          (-((m : ℝ) * (A + B) * A * zs / 2))
          (((m : ℝ) * ((A : ℝ) * B)) / 2) (((m : ℝ) * ((A : ℝ) * B)) * zs / 2)) ∧
        C1.model.Congruent R.Δ := by
  obtain ⟨A, B, C, k, hk, hA, hB, hC, hh, hcop, ea, eb, ec⟩ := rat_data R hrel
  obtain ⟨m, hm, hE⟩ := equi_data A B C hA hB hC hh hcop
  exact ⟨A, B, m, k, hA, hB, hk, hm, ea, eb,
    rat_dis R A B C k hk hA hB hh ea eb ec (zhang_prop10_2 A B m hA hB hm hE)⟩

/-! ### Props 6 (1), (2) and Theorem 7 (need `a < b`) -/

theorem zhang_prop6_1_rational (hab : R.a < R.b) :
    ∃ (A d C : ℕ) (k : ℚ) (hA : 0 < A), 0 < k ∧ 0 < d ∧ R.a = k * A ∧ R.b = k * (A + d) ∧
      ∃ C1 : CongruentRegionDissection (((A + d) + 2 * A) * (A + 2 * (A + d)) * (C * C)),
        C1.region = dil (k : ℝ) (ZhangLat.LT 0 (ZhangProp6.pAv (A : ℝ) d) (ZhangProp6.pCu (A : ℝ) d) 0
          (ZhangProp6.pBu (A : ℝ) d) (ZhangProp6.pBv (A : ℝ) d)) ∧ C1.model.Congruent R.Δ := by
  obtain ⟨A, B, C, k, hk, hA, hB, hC, hh, hcop, ea, eb, ec⟩ := rat_data R hrel
  have hkr : (0 : ℚ) < k := hk
  have hlt : A < B := by
    rw [ea, eb] at hab
    exact_mod_cast lt_of_mul_lt_mul_left hab hk.le
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hlt.le
  have hd : 0 < d := by omega
  refine ⟨A, d, C, k, hA, hk, hd, ea, by rw [eb, Nat.cast_add], ?_⟩
  exact rat_dis R A (A + d) C k hk hA hB hh ea eb ec
    (ZhangProp6.zhang_prop6_1 A d C hA hd hh hcop)

theorem zhang_prop6_2_rational (hab : R.a < R.b) :
    ∃ (A d C : ℕ) (k : ℚ) (hA : 0 < A), 0 < k ∧ 0 < d ∧ R.a = k * A ∧ R.b = k * (A + d) ∧
      ∃ C1 : CongruentRegionDissection (((A + d) + 2 * A) * (A + 2 * (A + d)) * ((A + d) * (A + d))),
        C1.region = dil (k : ℝ) (ZhangLat.LT (ZhangProp6b.qAu (A : ℝ) d) 0 (ZhangProp6.pFu (A : ℝ) d) 0
          (ZhangProp6b.qBu (A : ℝ) d) (ZhangProp6b.qBv (A : ℝ) d)) ∧ C1.model.Congruent R.Δ := by
  obtain ⟨A, B, C, k, hk, hA, hB, hC, hh, hcop, ea, eb, ec⟩ := rat_data R hrel
  have hlt : A < B := by
    rw [ea, eb] at hab
    exact_mod_cast lt_of_mul_lt_mul_left hab hk.le
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hlt.le
  have hd : 0 < d := by omega
  refine ⟨A, d, C, k, hA, hk, hd, ea, by rw [eb, Nat.cast_add], ?_⟩
  exact rat_dis R A (A + d) C k hk hA hB hh ea eb ec
    (ZhangProp6b.zhang_prop6_2 A d C hA hd hh hcop)

/-- **Theorem 7, rational tile**: for every `m` with `B C < m + B + C` the dilated lattice triangle
carries `(B+2A)(A+2B) m^2` tiles. -/
theorem zhang_thm7_rational (hab : R.a < R.b) :
    ∃ (A d C : ℕ) (k : ℚ) (hA : 0 < A), 0 < k ∧ 0 < d ∧ R.a = k * A ∧ R.b = k * (A + d) ∧
      ∀ m : ℕ, (A + d) * C < m + (A + d) + C →
      ∃ C1 : CongruentRegionDissection (((A + d) + 2 * A) * (A + 2 * (A + d)) * (m * m)),
        C1.region = dil (k : ℝ) (ZhangLat.LT 0 0 ((A : ℝ) * (A + 2 * ((A : ℝ) + d)) * m) 0
          (((A : ℝ) * (A + 2 * ((A : ℝ) + d)) - ((A : ℝ) + d) * (2 * A + ((A : ℝ) + d))) * m)
          ((((A : ℝ) + d)) * (2 * A + ((A : ℝ) + d)) * m)) ∧ C1.model.Congruent R.Δ := by
  obtain ⟨A, B, C, k, hk, hA, hB, hC, hh, hcop, ea, eb, ec⟩ := rat_data R hrel
  have hlt : A < B := by
    rw [ea, eb] at hab
    exact_mod_cast lt_of_mul_lt_mul_left hab hk.le
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hlt.le
  have hd : 0 < d := by omega
  refine ⟨A, d, C, k, hA, hk, hd, ea, (by rw [eb, Nat.cast_add]), fun m hm => ?_⟩
  exact rat_dis R A (A + d) C k hk hA hB hh ea eb ec
    (ZhangThm7.zhang_thm7 A d C m hA hd hh hcop hm)


/-- **Prop 11 (1), rational tile**: for every integer-length configuration `A D B` (lengths as in
`ZhangProp11.zhang_prop11_core`) tiled by `n0` model tiles, the dilated extension is tiled by `n0 + (..m)^2` tiles
congruent to `R.Δ`. -/
theorem zhang_prop11_1_rational :
    ∃ (A B : ℕ) (k : ℚ) (hA : 0 < A) (hB : 0 < B), 0 < k ∧ R.a = k * A ∧ R.b = k * B ∧
      ∀ (m : ℕ) (hm : 0 < m) {n0 : ℕ} (Ax Ay Bx By Dx Dy : ℝ) (hD : 0 < det3 Ax Ay Dx Dy Bx By)
        (hAD : (Ax - Dx) ^ 2 + (Ay - Dy) ^ 2 = (((A : ℝ) + 2 * B) * m * A) ^ 2)
        (hBD : (Bx - Dx) ^ 2 + (By - Dy) ^ 2 = (((B : ℝ) + 2 * A) * B * m) ^ 2)
        (hAB : (Ax - Bx) ^ 2 + (Ay - By) ^ 2 = (((A : ℝ) ^ 2 + A * B + B ^ 2) * m) ^ 2)
        (hT : Dis (RM A B hA hB) (TriSet Ax Ay Dx Dy Bx By) n0),
      ∃ C1 : CongruentRegionDissection (n0 + ((A + 2 * B) * m) * ((A + 2 * B) * m)),
        C1.region = dil (k : ℝ) (TriSet Ax Ay (Dx + ((((A : ℝ) + 2 * B) / (B + 2 * A)) : ℝ) * (Dx - Bx))
          (Dy + ((((A : ℝ) + 2 * B) / (B + 2 * A)) : ℝ) * (Dy - By)) Bx By) ∧ C1.model.Congruent R.Δ := by
  obtain ⟨A, B, C, k, hk, hA, hB, hC, hh, hcop, ea, eb, ec⟩ := rat_data R hrel
  refine ⟨A, B, k, hA, hB, hk, ea, eb, fun m hm n0 Ax Ay Bx By Dx Dy hD hAD hBD hAB hT => ?_⟩
  exact rat_dis R A B C k hk hA hB hh ea eb ec (ZhangProp11.zhang_prop11_core A B m hA hB hm Ax Ay Bx By Dx Dy hD hAD hBD hAB hT)

/-- **Prop 11 (2), rational tile**: for every integer-length configuration `A D B` (lengths as in
`ZhangProp11b.zhang_prop11_2_core`) tiled by `n0` model tiles, the dilated extension is tiled by `n0 + (..m)^2` tiles
congruent to `R.Δ`. -/
theorem zhang_prop11_2_rational :
    ∃ (A B : ℕ) (k : ℚ) (hA : 0 < A) (hB : 0 < B), 0 < k ∧ R.a = k * A ∧ R.b = k * B ∧
      ∀ (m : ℕ) (hm : 0 < m) {n0 : ℕ} (Ax Ay Bx By Dx Dy : ℝ) (hD : 0 < det3 Ax Ay Dx Dy Bx By)
        (hAD : (Ax - Dx) ^ 2 + (Ay - Dy) ^ 2 = (((B : ℝ) + 2 * A) * m * B) ^ 2)
        (hBD : (Bx - Dx) ^ 2 + (By - Dy) ^ 2 = (((A : ℝ) + 2 * B) * A * m) ^ 2)
        (hAB : (Ax - Bx) ^ 2 + (Ay - By) ^ 2 = (((A : ℝ) ^ 2 + A * B + B ^ 2) * m) ^ 2)
        (hT : Dis (RM A B hA hB) (TriSet Ax Ay Dx Dy Bx By) n0),
      ∃ C1 : CongruentRegionDissection (n0 + ((B + 2 * A) * m) * ((B + 2 * A) * m)),
        C1.region = dil (k : ℝ) (TriSet Ax Ay (Dx + ((((B : ℝ) + 2 * A) / (A + 2 * B)) : ℝ) * (Dx - Bx))
          (Dy + ((((B : ℝ) + 2 * A) / (A + 2 * B)) : ℝ) * (Dy - By)) Bx By) ∧ C1.model.Congruent R.Δ := by
  obtain ⟨A, B, C, k, hk, hA, hB, hC, hh, hcop, ea, eb, ec⟩ := rat_data R hrel
  refine ⟨A, B, k, hA, hB, hk, ea, eb, fun m hm n0 Ax Ay Bx By Dx Dy hD hAD hBD hAB hT => ?_⟩
  exact rat_dis R A B C k hk hA hB hh ea eb ec (ZhangProp11b.zhang_prop11_2_core A B m hA hB hm Ax Ay Bx By Dx Dy hD hAD hBD hAB hT)

end p8

/-- Witness of every hypothesis: a non-integer tile `(3/2, 5/2, 7/2)` (`a < b`, `c^2 = a^2+b^2+ab`). -/
theorem rat_wit : ∃ R : RTri, R.a = 3 / 2 ∧ R.b = 5 / 2 ∧ R.c = 7 / 2 ∧
    R.c ^ 2 = R.a ^ 2 + R.b ^ 2 + R.a * R.b ∧ R.a < R.b := by
  obtain ⟨R, h1, h2, h3⟩ := exists_RTri_thm4 3 5 7 (by norm_num) (by norm_num) (by norm_num)
    (1 / 2) (by norm_num)
  have ha : R.a = 3 / 2 := by rw [h1]; norm_num
  have hb : R.b = 5 / 2 := by rw [h2]; norm_num
  have hc : R.c = 7 / 2 := by rw [h3]; norm_num
  exact ⟨R, ha, hb, hc, by rw [ha, hb, hc]; norm_num, by rw [ha, hb]; norm_num⟩

theorem rat_wit_thm7 : ∃ R : RTri, R.a = 3 / 2 ∧ R.b = 5 / 2 ∧ R.c = 7 / 2 ∧ ∃ (A d C : ℕ) (k : ℚ),
    0 < k ∧ R.a = k * A ∧ R.b = k * (A + d) := by
  obtain ⟨R, ha, hb, hc, hrel, hab⟩ := rat_wit
  obtain ⟨A, d, C, k, hA, hk, hd, ea, eb, _⟩ := zhang_thm7_rational R hrel hab
  exact ⟨R, ha, hb, hc, A, d, C, k, hk, ea, eb⟩

end Erdos634.ZhangRat

#print axioms Erdos634.ZhangRat.zhang_thm7_rational
#print axioms Erdos634.ZhangRat.zhang_prop6_1_rational
#print axioms Erdos634.ZhangRat.zhang_prop6_2_rational
#print axioms Erdos634.ZhangRat.zhang_prop8_1_rational
#print axioms Erdos634.ZhangRat.zhang_prop10_2_rational
#print axioms Erdos634.ZhangRat.zhang_prop11_1_rational
#print axioms Erdos634.ZhangRat.zhang_prop11_2_rational
#print axioms Erdos634.ZhangRat.rat_wit_thm7
