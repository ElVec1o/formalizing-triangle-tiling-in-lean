import Erdos634.Draft.ZhangRat4Tiled
import Erdos634.Draft.ZhangRat4Count

/-!
# Zhang Prop 11, printed conclusions, with the tiling hypothesis and the count DERIVED

`ZhangRat3Prop11.zhang_prop11_{1,2}_printed` take the tiling of the hypothesis triangle
`((a+2b)am, (b+2a)bm, c^2 m)` as a hypothesis `TileDis R S n0` and the count `n0 = (a+2b)(b+2a)m^2` as a
second hypothesis of the count identity.  Here, for the rational tile `R` with `R.a < R.b` and
`m' = k m` a natural number that is admissible (`b ∣ m'` or `b c < m' + b + c`, `(A,B,C)` the primitive
integer model, `R = k (A,B,C)`):

* the tiling hypothesis is DERIVED (`ZhangRat4Tiled`, from Prop 6(2) / Thm 7), with exactly
  `N0 = (B+2A)(A+2B) m'^2` tiles, so that `N0 = (a+2b)(b+2a)m^2` is a theorem, not a hypothesis;
* the extended triangle `A C B` is tiled by `N0 + ((A+2B)m')^2 = 3m^2 (a+2b)(a+b)` tiles (part 1), resp.
  `N0 + ((B+2A)m')^2 = 3 m^2 (2a+b)(a+b)` (part 2).
The only remaining restriction is `a < b` and admissibility of `m'` (see `ZhangRat4Tiled`).  The count
uniqueness `ZhangRat4Count.tiledis_count_unique` shows that any tiling of the hypothesis triangle
has this `N0` tiles.  UNAUDITED.  Credit Zhang (arXiv 2512.22696v4), Beeson, Beeson-Zhang, Laczkovich.
-/

set_option maxHeartbeats 3200000

namespace Erdos634.ZhangRat4

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.SssCongruent Erdos634.ZhangPara Erdos634.ZhangL1 Erdos634.ZhangSporadic
  Erdos634.ZhangRat Erdos634.ZhangRational Erdos634.LaczL22 Erdos634.Realizable Erdos634.BeesonCor5
  Erdos634.ZhangThm4 Erdos634.ZhangRat3

section main
variable (R : RTri) (hrel : R.c ^ 2 = R.a ^ 2 + R.b ^ 2 + R.a * R.b)
include hrel

/-- **Zhang Prop 11 (1), tiling hypothesis and count derived.** -/
theorem zhang_prop11_1_derived (hab : R.a < R.b) :
    ∃ (A B C : ℕ) (k : ℚ) (hA : 0 < A) (hB : 0 < B), 0 < k ∧ R.a = k * A ∧ R.b = k * B ∧ R.c = k * C ∧
      C * C = A * A + B * B + A * B ∧ Nat.Coprime A B ∧
      ∀ (m : ℝ) (m' : ℕ), 0 < m' → (k : ℝ) * m = m' → (B ∣ m' ∨ B * C < m' + B + C) →
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
  obtain ⟨A, B, C, k, hk, hA, hB, hC, hh, hcop, ea, eb, ec⟩ := rat_data R hrel
  have hlt : A < B := by
    rw [ea, eb] at hab
    exact_mod_cast lt_of_mul_lt_mul_left hab hk.le
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hlt.le
  have hd : 0 < d := by omega
  set B := A + d with hBdef
  refine ⟨A, B, C, k, hA, hB, hk, ea, eb, ec, hh, hcop, ?_⟩
  intro m m' hm' hkm hadm Ax Ay Bx By Dx Dy hD hAD hBD hAB
  have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≠ 0 := hkr.ne'
  have ea' : (R.a : ℝ) = k * A := by exact_mod_cast ea
  have eb' : (R.b : ℝ) = k * (B : ℝ) := by exact_mod_cast eb
  have ec' : (R.c : ℝ) = k * C := by exact_mod_cast ec
  have hA' : (0 : ℝ) < (A : ℝ) := Nat.cast_pos.mpr hA
  have hB' : (0 : ℝ) < (B : ℝ) := Nat.cast_pos.mpr hB
  have hhR : (C : ℝ) ^ 2 = (A : ℝ) ^ 2 + (B : ℝ) ^ 2 + A * (B : ℝ) := by
    exact_mod_cast (by nlinarith [hh] : C ^ 2 = A ^ 2 + (A + d) ^ 2 + A * (A + d))
  have hcc : (R.c : ℝ) ^ 2 = k ^ 2 * ((A : ℝ) ^ 2 + A * (B : ℝ) + (B : ℝ) ^ 2) := by
    rw [ec', mul_pow, hhR]; ring
  have hpq : (R.a : ℝ) ^ 2 + (R.a : ℝ) * R.b + (R.b : ℝ) ^ 2 = (R.c : ℝ) ^ 2 := by
    rw [hcc, ea', eb']; ring
  have hlam : (((R.a : ℝ) + 2 * R.b) / ((R.b : ℝ) + 2 * R.a))
      = ((A : ℝ) + 2 * B) / ((B : ℝ) + 2 * A) := by
    rw [ea', eb']; field_simp
  have hmm : m = m' / k := by field_simp; linarith
  have hD' : 0 < det3 ((k : ℝ)⁻¹ * Ax) ((k : ℝ)⁻¹ * Ay) ((k : ℝ)⁻¹ * Dx) ((k : ℝ)⁻¹ * Dy)
      ((k : ℝ)⁻¹ * Bx) ((k : ℝ)⁻¹ * By) := by
    rw [det3_smul]; positivity
  have sq : ∀ x1 y1 x2 y2 : ℝ, ((k : ℝ)⁻¹ * x1 - (k : ℝ)⁻¹ * x2) ^ 2 + ((k : ℝ)⁻¹ * y1 - (k : ℝ)⁻¹ * y2) ^ 2
      = ((k : ℝ)⁻¹) ^ 2 * ((x1 - x2) ^ 2 + (y1 - y2) ^ 2) := by intro x1 y1 x2 y2; ring
  have hAD' : ((k : ℝ)⁻¹ * Ax - (k : ℝ)⁻¹ * Dx) ^ 2 + ((k : ℝ)⁻¹ * Ay - (k : ℝ)⁻¹ * Dy) ^ 2
      = ((((A : ℝ) + 2 * (B : ℝ)) * (m' : ℝ)) * A) ^ 2 := by
    rw [sq, hAD, ea', eb', hmm]; field_simp
  have hBD' : ((k : ℝ)⁻¹ * Bx - (k : ℝ)⁻¹ * Dx) ^ 2 + ((k : ℝ)⁻¹ * By - (k : ℝ)⁻¹ * Dy) ^ 2
      = ((((B : ℝ) + 2 * A) * (B : ℝ)) * (m' : ℝ)) ^ 2 := by
    rw [sq, hBD, ea', eb', hmm]; field_simp
  have hAB' : ((k : ℝ)⁻¹ * Ax - (k : ℝ)⁻¹ * Bx) ^ 2 + ((k : ℝ)⁻¹ * Ay - (k : ℝ)⁻¹ * By) ^ 2
      = ((((A : ℝ) ^ 2 + A * (B : ℝ) + (B : ℝ) ^ 2)) * (m' : ℝ)) ^ 2 := by
    rw [sq, hAB, hcc, hmm]; field_simp
  have hT0 := prop11_1_tiled_all A d C m' hA hd (by nlinarith [hh]) hcop hm' hadm
    _ _ _ _ _ _ hD' hAD' hBD' hAB'
  have hcore := ZhangProp11.zhang_prop11_core A (A + d) m' hA hB hm' _ _ _ _ _ _ hD' hAD' hBD' hAB' hT0
  obtain ⟨C1, hr1, hc1⟩ := rat_dis R A (A + d) C k hk hA hB hh ea eb ec hcore
  obtain ⟨C0, hr0, hc0⟩ := rat_dis R A (A + d) C k hk hA hB hh ea eb ec hT0
  have hm1 := ext_metric (R.a : ℝ) (R.b : ℝ) m ((R.c : ℝ) ^ 2) (by rw [ea']; positivity)
    (by rw [eb']; positivity) hpq.symm Ax Ay Bx By Dx Dy hAD hBD hAB
  have e1 : ∀ x : ℝ, (k : ℝ) * ((k : ℝ)⁻¹ * x) = x := fun x => mul_inv_cancel_left₀ hk0 x
  refine ⟨_, _, rfl, rfl, hm1.1, ?_, ⟨C0, ?_, hc0⟩, ?_, ⟨C1, ?_, hc1⟩, ?_⟩
  · rw [hm1.2]; rw [mul_pow, mul_pow]; ring
  · rw [hr0, dil_TriSet _ hkr]; simp only [e1]
  · push_cast
    rw [ea', eb', hmm]; field_simp
  · rw [hr1, dil_TriSet _ hkr, ← hlam]
    have eC : ∀ x y : ℝ, (k : ℝ) * ((k : ℝ)⁻¹ * x + (((R.a : ℝ) + 2 * R.b) / ((R.b : ℝ) + 2 * R.a))
        * ((k : ℝ)⁻¹ * x - (k : ℝ)⁻¹ * y)) = x + (((R.a : ℝ) + 2 * R.b) / ((R.b : ℝ) + 2 * R.a)) * (x - y) := by
      intro x y; field_simp
    simp only [e1, eC]
  · push_cast
    rw [ea', eb', hmm]; field_simp; ring

/-- **Zhang Prop 11 (2), tiling hypothesis and count derived.** -/
theorem zhang_prop11_2_derived (hab : R.a < R.b) :
    ∃ (A B C : ℕ) (k : ℚ) (hA : 0 < A) (hB : 0 < B), 0 < k ∧ R.a = k * A ∧ R.b = k * B ∧ R.c = k * C ∧
      C * C = A * A + B * B + A * B ∧ Nat.Coprime A B ∧
      ∀ (m : ℝ) (m' : ℕ), 0 < m' → (k : ℝ) * m = m' → (B ∣ m' ∨ B * C < m' + B + C) →
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
  obtain ⟨A, B, C, k, hk, hA, hB, hC, hh, hcop, ea, eb, ec⟩ := rat_data R hrel
  have hlt : A < B := by
    rw [ea, eb] at hab
    exact_mod_cast lt_of_mul_lt_mul_left hab hk.le
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hlt.le
  have hd : 0 < d := by omega
  set B := A + d with hBdef
  refine ⟨A, B, C, k, hA, hB, hk, ea, eb, ec, hh, hcop, ?_⟩
  intro m m' hm' hkm hadm Ax Ay Bx By Dx Dy hD hAD hBD hAB
  have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≠ 0 := hkr.ne'
  have ea' : (R.a : ℝ) = k * A := by exact_mod_cast ea
  have eb' : (R.b : ℝ) = k * (B : ℝ) := by exact_mod_cast eb
  have ec' : (R.c : ℝ) = k * C := by exact_mod_cast ec
  have hA' : (0 : ℝ) < (A : ℝ) := Nat.cast_pos.mpr hA
  have hB' : (0 : ℝ) < (B : ℝ) := Nat.cast_pos.mpr hB
  have hhR : (C : ℝ) ^ 2 = (A : ℝ) ^ 2 + (B : ℝ) ^ 2 + A * (B : ℝ) := by
    exact_mod_cast (by nlinarith [hh] : C ^ 2 = A ^ 2 + (A + d) ^ 2 + A * (A + d))
  have hcc : (R.c : ℝ) ^ 2 = k ^ 2 * ((A : ℝ) ^ 2 + A * (B : ℝ) + (B : ℝ) ^ 2) := by
    rw [ec', mul_pow, hhR]; ring
  have hpq : (R.b : ℝ) ^ 2 + (R.b : ℝ) * R.a + (R.a : ℝ) ^ 2 = (R.c : ℝ) ^ 2 := by
    rw [hcc, ea', eb']; ring
  have hlam : (((R.b : ℝ) + 2 * R.a) / ((R.a : ℝ) + 2 * R.b))
      = ((B : ℝ) + 2 * A) / ((A : ℝ) + 2 * B) := by
    rw [ea', eb']; field_simp
  have hmm : m = m' / k := by field_simp; linarith
  have hD' : 0 < det3 ((k : ℝ)⁻¹ * Ax) ((k : ℝ)⁻¹ * Ay) ((k : ℝ)⁻¹ * Dx) ((k : ℝ)⁻¹ * Dy)
      ((k : ℝ)⁻¹ * Bx) ((k : ℝ)⁻¹ * By) := by
    rw [det3_smul]; positivity
  have sq : ∀ x1 y1 x2 y2 : ℝ, ((k : ℝ)⁻¹ * x1 - (k : ℝ)⁻¹ * x2) ^ 2 + ((k : ℝ)⁻¹ * y1 - (k : ℝ)⁻¹ * y2) ^ 2
      = ((k : ℝ)⁻¹) ^ 2 * ((x1 - x2) ^ 2 + (y1 - y2) ^ 2) := by intro x1 y1 x2 y2; ring
  have hAD' : ((k : ℝ)⁻¹ * Ax - (k : ℝ)⁻¹ * Dx) ^ 2 + ((k : ℝ)⁻¹ * Ay - (k : ℝ)⁻¹ * Dy) ^ 2
      = ((((B : ℝ) + 2 * A) * (m' : ℝ)) * (B : ℝ)) ^ 2 := by
    rw [sq, hAD, ea', eb', hmm]; field_simp
  have hBD' : ((k : ℝ)⁻¹ * Bx - (k : ℝ)⁻¹ * Dx) ^ 2 + ((k : ℝ)⁻¹ * By - (k : ℝ)⁻¹ * Dy) ^ 2
      = ((((A : ℝ) + 2 * (B : ℝ)) * A) * (m' : ℝ)) ^ 2 := by
    rw [sq, hBD, ea', eb', hmm]; field_simp
  have hAB' : ((k : ℝ)⁻¹ * Ax - (k : ℝ)⁻¹ * Bx) ^ 2 + ((k : ℝ)⁻¹ * Ay - (k : ℝ)⁻¹ * By) ^ 2
      = ((((A : ℝ) ^ 2 + A * (B : ℝ) + (B : ℝ) ^ 2)) * (m' : ℝ)) ^ 2 := by
    rw [sq, hAB, hcc, hmm]; field_simp
  have hT0 := prop11_2_tiled_all A d C m' hA hd (by nlinarith [hh]) hcop hm' hadm
    _ _ _ _ _ _ hD' hAD' hBD' hAB'
  have hcore := ZhangProp11b.zhang_prop11_2_core A (A + d) m' hA hB hm' _ _ _ _ _ _ hD'
    (by rw [hAD']) hBD' hAB' hT0
  obtain ⟨C1, hr1, hc1⟩ := rat_dis R A (A + d) C k hk hA hB hh ea eb ec hcore
  obtain ⟨C0, hr0, hc0⟩ := rat_dis R A (A + d) C k hk hA hB hh ea eb ec hT0
  have hm1 := ext_metric (R.b : ℝ) (R.a : ℝ) m ((R.c : ℝ) ^ 2) (by rw [eb']; positivity)
    (by rw [ea']; positivity) hpq.symm Ax Ay Bx By Dx Dy hAD hBD hAB
  have e1 : ∀ x : ℝ, (k : ℝ) * ((k : ℝ)⁻¹ * x) = x := fun x => mul_inv_cancel_left₀ hk0 x
  refine ⟨_, _, rfl, rfl, by rw [hm1.1]; ring, ?_, ⟨C0, ?_, hc0⟩, ?_, ⟨C1, ?_, hc1⟩, ?_⟩
  · rw [hm1.2]; rw [mul_pow, mul_pow]; ring
  · rw [hr0, dil_TriSet _ hkr]; simp only [e1]
  · push_cast
    rw [ea', eb', hmm]; field_simp
  · rw [hr1, dil_TriSet _ hkr, ← hlam]
    have eC : ∀ x y : ℝ, (k : ℝ) * ((k : ℝ)⁻¹ * x + (((R.b : ℝ) + 2 * R.a) / ((R.a : ℝ) + 2 * R.b))
        * ((k : ℝ)⁻¹ * x - (k : ℝ)⁻¹ * y)) = x + (((R.b : ℝ) + 2 * R.a) / ((R.a : ℝ) + 2 * R.b)) * (x - y) := by
      intro x y; field_simp
    simp only [e1, eC]
  · push_cast
    rw [ea', eb', hmm]; field_simp; ring

end main

end Erdos634.ZhangRat4

#print axioms Erdos634.ZhangRat4.zhang_prop11_1_derived
#print axioms Erdos634.ZhangRat4.zhang_prop11_2_derived
