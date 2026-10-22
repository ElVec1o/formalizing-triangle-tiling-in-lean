import Erdos634.Draft.ZhangRat2Prop11Rat

/-!
# Zhang Prop 11, PRINTED conclusions (1) and (2), stated for the tile `R` itself

arXiv 2512.22696v4, Prop. 11: if the `((a+2b)am, (b+2a)bm, c^2 m)` triangle tiles into `(a,b,c)`, then
(1) the `(c^2 m, (a+2b)mc, 3(a+b)mb)` triangle (angles `(alpha, 2alpha, 3beta)`) tiles into
`3m^2(a+2b)(a+b)` copies of `(a,b,c)`; (2) the `(c^2 m, (b+2a)mc, 3(a+b)ma)` triangle (angles
`(beta, 2beta, 3alpha)`) tiles into `3m^2(2a+b)(a+b)` copies.

Earlier modules (`ZhangProp11`, `ZhangRat.zhang_prop11_*_rational`) state the INTEGER-model/dilated form.
Here the hypothesis and conclusion are in the terms of the printed statement, for `R : RTri` with
`c^2 = a^2+ab+b^2` (rational sides) and a real parameter `m` with `k*m = m'` a positive natural
(`(a,b,c) = k (A,B,C)`, `A,B,C` coprime; this is the only way `(a+2b)m` can be the integer side of
the tile-scaled triangle `A D C`, whose tile count is its square).  Tilings are `TileDis R S n`:
a `CongruentRegionDissection` into `n` tiles of region `S`, model congruent to `R.Δ`.  Conclusions
proved: the point `C = D + ((a+2b)/(b+2a))(D-B)`, `|BC| = 3(a+b)mb`, `|AC| = (a+2b)m c`, `|AB| = c^2 m`
(hypothesis), the tiling of `A C B` by `n0 + ((A+2B) m')^2` tiles and, if `n0 = (a+2b)(b+2a)m^2`
(the area count of the hypothesis triangle), the total `3m^2(a+2b)(a+b)`.  The "angles" clause is
not a separate Lean statement: the triangle is determined by its three side lengths.
NOT derived here: the tiling hypothesis itself (that is `ZhangRat2Prop11Rat`, for `b | m`,
`a < b`).  UNAUDITED.  Credit Zhang (arXiv 2512.22696), Beeson, Beeson-Zhang, Laczkovich.
-/

set_option maxHeartbeats 3200000

namespace Erdos634.ZhangRat3

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.SssCongruent Erdos634.ZhangPara Erdos634.ZhangL1 Erdos634.ZhangSporadic
  Erdos634.ZhangRat Erdos634.ZhangRational Erdos634.LaczL22 Erdos634.Realizable Erdos634.BeesonCor5
  Erdos634.ZhangThm4

/-- `S` is tiled by `n` copies of the tile `R`. -/
def TileDis (R : RTri) (S : Set Plane) (n : ℕ) : Prop :=
  ∃ C : CongruentRegionDissection n, C.region = S ∧ C.model.Congruent R.Δ

/-- Change the model of a congruent region dissection to a congruent triangle. -/
def reModel {n : ℕ} (C : CongruentRegionDissection n) (M : Tri) (h : C.model.Congruent M) :
    CongruentRegionDissection n where
  toRegionDissection := C.toRegionDissection
  model := M
  tiles_congruent := fun i => (C.tiles_congruent i).trans h

theorem det3_smul (c a b c' d e f : ℝ) :
    det3 (c * a) (c * b) (c * c') (c * d) (c * e) (c * f) = c ^ 2 * det3 a b c' d e f := by
  simp only [det3]; ring

theorem dil_TriSet (c : ℝ) (hc : 0 < c) (x0 y0 x1 y1 x2 y2 : ℝ) :
    dil c (TriSet x0 y0 x1 y1 x2 y2) = TriSet (c * x0) (c * y0) (c * x1) (c * y1) (c * x2) (c * y2) := by
  have hc2 : 0 < c ^ 2 := by positivity
  ext p
  constructor
  · rintro ⟨q, ⟨h1, h2, h3⟩, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · show 0 ≤ det3 (c * q 0) (c * q 1) (c * x1) (c * y1) (c * x2) (c * y2)
      rw [det3_smul]; exact mul_nonneg hc2.le h1
    · show 0 ≤ det3 (c * x0) (c * y0) (c * q 0) (c * q 1) (c * x2) (c * y2)
      rw [det3_smul]; exact mul_nonneg hc2.le h2
    · show 0 ≤ det3 (c * x0) (c * y0) (c * x1) (c * y1) (c * q 0) (c * q 1)
      rw [det3_smul]; exact mul_nonneg hc2.le h3
  · rintro ⟨h1, h2, h3⟩
    refine ⟨c⁻¹ • p, ⟨?_, ?_, ?_⟩, smul_inv_smul₀ hc.ne' p⟩
    · have e := det3_smul c (c⁻¹ * p 0) (c⁻¹ * p 1) x1 y1 x2 y2
      rw [mul_inv_cancel_left₀ hc.ne', mul_inv_cancel_left₀ hc.ne'] at e
      rw [e] at h1
      exact (mul_nonneg_iff_of_pos_left hc2).mp h1
    · have e := det3_smul c x0 y0 (c⁻¹ * p 0) (c⁻¹ * p 1) x2 y2
      rw [mul_inv_cancel_left₀ hc.ne', mul_inv_cancel_left₀ hc.ne'] at e
      rw [e] at h2
      exact (mul_nonneg_iff_of_pos_left hc2).mp h2
    · have e := det3_smul c x0 y0 x1 y1 (c⁻¹ * p 0) (c⁻¹ * p 1)
      rw [mul_inv_cancel_left₀ hc.ne', mul_inv_cancel_left₀ hc.ne'] at e
      rw [e] at h3
      exact (mul_nonneg_iff_of_pos_left hc2).mp h3

/-- Integer-model tiling from a tiling by `R`: the `1/k` dilate of an `R`-tiled set is tiled by the
model `(A,B,C)`. -/
theorem tile_to_Dis (R : RTri) (A B C : ℕ) (k : ℚ) (hk : 0 < k) (hA : 0 < A) (hB : 0 < B)
    (hh : C * C = A * A + B * B + A * B)
    (ea : R.a = k * A) (eb : R.b = k * B) (ec : R.c = k * C) {S : Set Plane} {n : ℕ}
    (h : TileDis R S n) : Dis (RM A B hA hB) (dil ((k : ℝ)⁻¹) S) n := by
  obtain ⟨C0, hr, hmod⟩ := h
  have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hki : (0 : ℝ) < (k : ℝ)⁻¹ := inv_pos.mpr hkr
  have hA' : (0 : ℝ) < (A : ℝ) := Nat.cast_pos.mpr hA
  have hB' : (0 : ℝ) < (B : ℝ) := Nat.cast_pos.mpr hB
  have hcR : (C : ℝ) ^ 2 = (A : ℝ) ^ 2 + (B : ℝ) ^ 2 + A * B := by
    exact_mod_cast (by nlinarith [hh] : C ^ 2 = A ^ 2 + B ^ 2 + A * B)
  have n01 := dist_eq_of_sq dist_nonneg (Nat.cast_nonneg C) (R_d01 (c := (C : ℝ)) hA' hB' hcR)
  have n12 := dist_eq_of_sq dist_nonneg (Nat.cast_nonneg A) (R_d12 hA' hB')
  have n02 := dist_eq_of_sq dist_nonneg (Nat.cast_nonneg B) (R_d02 hA' hB')
  have ea' : (R.a : ℝ) = k * A := by exact_mod_cast ea
  have eb' : (R.b : ℝ) = k * B := by exact_mod_cast eb
  have ec' : (R.c : ℝ) = k * C := by exact_mod_cast ec
  have hk0 : (k : ℝ) ≠ 0 := hkr.ne'
  let C1 := reModel C0 R.Δ hmod
  obtain ⟨C2, hreg, hcong⟩ := transfer C1 ((k : ℝ)⁻¹) hki (RM A B hA hB) (by
    apply hd_of_three
    · rw [n01, show C1.model = R.Δ from rfl, R.hc, ec']; field_simp
    · rw [n12, show C1.model = R.Δ from rfl, R.ha, ea']; field_simp
    · rw [n02, show C1.model = R.Δ from rfl, dist_comm (R.Δ.pts 0) (R.Δ.pts 2), R.hb, eb']; field_simp)
  refine ⟨reModel C2 (RM A B hA hB) hcong, ?_, rfl⟩
  show C2.region = _
  rw [hreg, show C1.region = C0.region from rfl, hr, hom_image_eq _ hki]

/-- Side lengths of the extended triangle, for the tile sides `p, q` (in the order of the hypothesis
triangle `AD = (p+2q) p m`, `BD = (q+2p) q m`, `AB = c^2 m`, `c^2 = p^2+pq+q^2`):
`C = D + ((p+2q)/(q+2p))(D-B)` has `BC = 3(p+q) q m` and `AC = (p+2q) m c`. -/
theorem ext_metric (p q m c2 : ℝ) (hp : 0 < p) (hq : 0 < q) (hc : c2 = p ^ 2 + p * q + q ^ 2)
    (Ax Ay Bx By Dx Dy : ℝ)
    (hAD : (Ax - Dx) ^ 2 + (Ay - Dy) ^ 2 = ((p + 2 * q) * p * m) ^ 2)
    (hBD : (Bx - Dx) ^ 2 + (By - Dy) ^ 2 = ((q + 2 * p) * q * m) ^ 2)
    (hAB : (Ax - Bx) ^ 2 + (Ay - By) ^ 2 = (c2 * m) ^ 2) :
    (Dx + ((p + 2 * q) / (q + 2 * p)) * (Dx - Bx) - Bx) ^ 2
        + (Dy + ((p + 2 * q) / (q + 2 * p)) * (Dy - By) - By) ^ 2 = (3 * (p + q) * q * m) ^ 2 ∧
    (Dx + ((p + 2 * q) / (q + 2 * p)) * (Dx - Bx) - Ax) ^ 2
        + (Dy + ((p + 2 * q) / (q + 2 * p)) * (Dy - By) - Ay) ^ 2 = ((p + 2 * q) * m) ^ 2 * c2 := by
  have hl0 : (q + 2 * p) ≠ 0 := by positivity
  set lam : ℝ := (p + 2 * q) / (q + 2 * p) with hlam
  subst hc
  constructor
  · have e : (Dx + lam * (Dx - Bx) - Bx) ^ 2 + (Dy + lam * (Dy - By) - By) ^ 2
        = (1 + lam) ^ 2 * ((Bx - Dx) ^ 2 + (By - Dy) ^ 2) := by ring
    rw [e, hBD, hlam]; field_simp; ring
  · have hdot : (Ax - Dx) * (Bx - Dx) + (Ay - Dy) * (By - Dy)
        = ((p + 2 * q) * p * m) ^ 2 / 2 + ((q + 2 * p) * q * m) ^ 2 / 2
          - ((p ^ 2 + p * q + q ^ 2) * m) ^ 2 / 2 := by
      linear_combination (1/2) * hAD + (1/2) * hBD - (1/2) * hAB
    have e : (Dx + lam * (Dx - Bx) - Ax) ^ 2 + (Dy + lam * (Dy - By) - Ay) ^ 2
        = ((Ax - Dx) ^ 2 + (Ay - Dy) ^ 2) + 2 * lam * ((Ax - Dx) * (Bx - Dx) + (Ay - Dy) * (By - Dy))
          + lam ^ 2 * ((Bx - Dx) ^ 2 + (By - Dy) ^ 2) := by ring
    rw [e, hdot, hAD, hBD, hlam]
    field_simp
    ring

section main
variable (R : RTri) (hrel : R.c ^ 2 = R.a ^ 2 + R.b ^ 2 + R.a * R.b)
include hrel

/-- **Zhang Prop 11 (1), as printed.**  See the module header. -/
theorem zhang_prop11_1_printed :
    ∃ (A B : ℕ) (k : ℚ) (hA : 0 < A) (hB : 0 < B), 0 < k ∧ R.a = k * A ∧ R.b = k * B ∧
      ∀ (m : ℝ) (m' : ℕ), 0 < m' → (k : ℝ) * m = m' → ∀ {n0 : ℕ} (Ax Ay Bx By Dx Dy : ℝ),
        0 < det3 Ax Ay Dx Dy Bx By →
        (Ax - Dx) ^ 2 + (Ay - Dy) ^ 2 = (((R.a : ℝ) + 2 * R.b) * R.a * m) ^ 2 →
        (Bx - Dx) ^ 2 + (By - Dy) ^ 2 = (((R.b : ℝ) + 2 * R.a) * R.b * m) ^ 2 →
        (Ax - Bx) ^ 2 + (Ay - By) ^ 2 = ((R.c : ℝ) ^ 2 * m) ^ 2 →
        TileDis R (TriSet Ax Ay Dx Dy Bx By) n0 →
        ∃ Cx Cy : ℝ,
          Cx = Dx + (((R.a : ℝ) + 2 * R.b) / ((R.b : ℝ) + 2 * R.a)) * (Dx - Bx) ∧
          Cy = Dy + (((R.a : ℝ) + 2 * R.b) / ((R.b : ℝ) + 2 * R.a)) * (Dy - By) ∧
          (Cx - Bx) ^ 2 + (Cy - By) ^ 2 = (3 * ((R.a : ℝ) + R.b) * R.b * m) ^ 2 ∧
          (Cx - Ax) ^ 2 + (Cy - Ay) ^ 2 = (((R.a : ℝ) + 2 * R.b) * m * R.c) ^ 2 ∧
          TileDis R (TriSet Ax Ay Cx Cy Bx By) (n0 + ((A + 2 * B) * m') * ((A + 2 * B) * m')) ∧
          ((n0 : ℝ) = ((R.a : ℝ) + 2 * R.b) * ((R.b : ℝ) + 2 * R.a) * m ^ 2 →
            ((n0 + ((A + 2 * B) * m') * ((A + 2 * B) * m') : ℕ) : ℝ)
              = 3 * m ^ 2 * ((R.a : ℝ) + 2 * R.b) * ((R.a : ℝ) + R.b)) := by
  obtain ⟨A, B, C, k, hk, hA, hB, hC, hh, hcop, ea, eb, ec⟩ := rat_data R hrel
  refine ⟨A, B, k, hA, hB, hk, ea, eb, ?_⟩
  intro m m' hm' hkm n0 Ax Ay Bx By Dx Dy hD hAD hBD hAB hT
  have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≠ 0 := hkr.ne'
  have ea' : (R.a : ℝ) = k * A := by exact_mod_cast ea
  have eb' : (R.b : ℝ) = k * B := by exact_mod_cast eb
  have ec' : (R.c : ℝ) = k * C := by exact_mod_cast ec
  have hA' : (0 : ℝ) < (A : ℝ) := Nat.cast_pos.mpr hA
  have hB' : (0 : ℝ) < (B : ℝ) := Nat.cast_pos.mpr hB
  have hhR : (C : ℝ) ^ 2 = (A : ℝ) ^ 2 + (B : ℝ) ^ 2 + A * B := by
    exact_mod_cast (by nlinarith [hh] : C ^ 2 = A ^ 2 + B ^ 2 + A * B)
  have hcc : (R.c : ℝ) ^ 2 = k ^ 2 * ((A : ℝ) ^ 2 + A * B + B ^ 2) := by
    rw [ec', mul_pow, hhR]; ring
  have hpq : (R.a : ℝ) ^ 2 + (R.a : ℝ) * R.b + (R.b : ℝ) ^ 2 = (R.c : ℝ) ^ 2 := by
    rw [hcc, ea', eb']; ring
  have hlam : (((R.a : ℝ) + 2 * R.b) / ((R.b : ℝ) + 2 * R.a))
      = ((A : ℝ) + 2 * B) / ((B : ℝ) + 2 * A) := by
    rw [ea', eb']; field_simp
  have hmm : m = m' / k := by field_simp; linarith
  have hT0 := tile_to_Dis R A B C k hk hA hB hh ea eb ec hT
  rw [dil_TriSet _ (inv_pos.mpr hkr)] at hT0
  have hD' : 0 < det3 ((k : ℝ)⁻¹ * Ax) ((k : ℝ)⁻¹ * Ay) ((k : ℝ)⁻¹ * Dx) ((k : ℝ)⁻¹ * Dy)
      ((k : ℝ)⁻¹ * Bx) ((k : ℝ)⁻¹ * By) := by
    rw [det3_smul]; positivity
  have hAD' : ((k : ℝ)⁻¹ * Ax - (k : ℝ)⁻¹ * Dx) ^ 2 + ((k : ℝ)⁻¹ * Ay - (k : ℝ)⁻¹ * Dy) ^ 2
      = (((A : ℝ) + 2 * B) * m' * A) ^ 2 := by
    have e : ((k : ℝ)⁻¹ * Ax - (k : ℝ)⁻¹ * Dx) ^ 2 + ((k : ℝ)⁻¹ * Ay - (k : ℝ)⁻¹ * Dy) ^ 2
        = ((k : ℝ)⁻¹) ^ 2 * ((Ax - Dx) ^ 2 + (Ay - Dy) ^ 2) := by ring
    rw [e, hAD, ea', eb', hmm]; field_simp
  have hBD' : ((k : ℝ)⁻¹ * Bx - (k : ℝ)⁻¹ * Dx) ^ 2 + ((k : ℝ)⁻¹ * By - (k : ℝ)⁻¹ * Dy) ^ 2
      = (((B : ℝ) + 2 * A) * B * m') ^ 2 := by
    have e : ((k : ℝ)⁻¹ * Bx - (k : ℝ)⁻¹ * Dx) ^ 2 + ((k : ℝ)⁻¹ * By - (k : ℝ)⁻¹ * Dy) ^ 2
        = ((k : ℝ)⁻¹) ^ 2 * ((Bx - Dx) ^ 2 + (By - Dy) ^ 2) := by ring
    rw [e, hBD, ea', eb', hmm]; field_simp
  have hAB' : ((k : ℝ)⁻¹ * Ax - (k : ℝ)⁻¹ * Bx) ^ 2 + ((k : ℝ)⁻¹ * Ay - (k : ℝ)⁻¹ * By) ^ 2
      = (((A : ℝ) ^ 2 + A * B + B ^ 2) * m') ^ 2 := by
    have e : ((k : ℝ)⁻¹ * Ax - (k : ℝ)⁻¹ * Bx) ^ 2 + ((k : ℝ)⁻¹ * Ay - (k : ℝ)⁻¹ * By) ^ 2
        = ((k : ℝ)⁻¹) ^ 2 * ((Ax - Bx) ^ 2 + (Ay - By) ^ 2) := by ring
    rw [e, hAB, hcc, hmm]; field_simp
  have hcore := ZhangProp11.zhang_prop11_core A B m' hA hB hm' _ _ _ _ _ _ hD' hAD' hBD' hAB' hT0
  obtain ⟨C1, hr1, hc1⟩ := rat_dis R A B C k hk hA hB hh ea eb ec hcore
  have hm1 := ext_metric (R.a : ℝ) (R.b : ℝ) m ((R.c : ℝ) ^ 2) (by rw [ea']; positivity)
    (by rw [eb']; positivity) hpq.symm Ax Ay Bx By Dx Dy hAD hBD hAB
  refine ⟨_, _, rfl, rfl, hm1.1, ?_, ⟨C1, ?_, hc1⟩, ?_⟩
  · rw [hm1.2]; rw [mul_pow, mul_pow]; ring
  · rw [hr1, dil_TriSet _ hkr, ← hlam]
    have e1 : ∀ x : ℝ, (k : ℝ) * ((k : ℝ)⁻¹ * x) = x := fun x => mul_inv_cancel_left₀ hk0 x
    have eC : ∀ x y : ℝ, (k : ℝ) * ((k : ℝ)⁻¹ * x + (((R.a : ℝ) + 2 * R.b) / ((R.b : ℝ) + 2 * R.a))
        * ((k : ℝ)⁻¹ * x - (k : ℝ)⁻¹ * y)) = x + (((R.a : ℝ) + 2 * R.b) / ((R.b : ℝ) + 2 * R.a)) * (x - y) := by
      intro x y; field_simp
    simp only [e1, eC]
  · intro hn0
    push_cast
    rw [hn0, ← hkm, ea', eb']; ring

/-- **Zhang Prop 11 (2), as printed.**  See the module header. -/
theorem zhang_prop11_2_printed :
    ∃ (A B : ℕ) (k : ℚ) (hA : 0 < A) (hB : 0 < B), 0 < k ∧ R.a = k * A ∧ R.b = k * B ∧
      ∀ (m : ℝ) (m' : ℕ), 0 < m' → (k : ℝ) * m = m' → ∀ {n0 : ℕ} (Ax Ay Bx By Dx Dy : ℝ),
        0 < det3 Ax Ay Dx Dy Bx By →
        (Ax - Dx) ^ 2 + (Ay - Dy) ^ 2 = (((R.b : ℝ) + 2 * R.a) * R.b * m) ^ 2 →
        (Bx - Dx) ^ 2 + (By - Dy) ^ 2 = (((R.a : ℝ) + 2 * R.b) * R.a * m) ^ 2 →
        (Ax - Bx) ^ 2 + (Ay - By) ^ 2 = ((R.c : ℝ) ^ 2 * m) ^ 2 →
        TileDis R (TriSet Ax Ay Dx Dy Bx By) n0 →
        ∃ Cx Cy : ℝ,
          Cx = Dx + (((R.b : ℝ) + 2 * R.a) / ((R.a : ℝ) + 2 * R.b)) * (Dx - Bx) ∧
          Cy = Dy + (((R.b : ℝ) + 2 * R.a) / ((R.a : ℝ) + 2 * R.b)) * (Dy - By) ∧
          (Cx - Bx) ^ 2 + (Cy - By) ^ 2 = (3 * ((R.a : ℝ) + R.b) * R.a * m) ^ 2 ∧
          (Cx - Ax) ^ 2 + (Cy - Ay) ^ 2 = (((R.b : ℝ) + 2 * R.a) * m * R.c) ^ 2 ∧
          TileDis R (TriSet Ax Ay Cx Cy Bx By) (n0 + ((B + 2 * A) * m') * ((B + 2 * A) * m')) ∧
          ((n0 : ℝ) = ((R.b : ℝ) + 2 * R.a) * ((R.a : ℝ) + 2 * R.b) * m ^ 2 →
            ((n0 + ((B + 2 * A) * m') * ((B + 2 * A) * m') : ℕ) : ℝ)
              = 3 * m ^ 2 * ((R.b : ℝ) + 2 * R.a) * ((R.a : ℝ) + R.b)) := by
  obtain ⟨A, B, C, k, hk, hA, hB, hC, hh, hcop, ea, eb, ec⟩ := rat_data R hrel
  refine ⟨A, B, k, hA, hB, hk, ea, eb, ?_⟩
  intro m m' hm' hkm n0 Ax Ay Bx By Dx Dy hD hAD hBD hAB hT
  have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≠ 0 := hkr.ne'
  have ea' : (R.a : ℝ) = k * A := by exact_mod_cast ea
  have eb' : (R.b : ℝ) = k * B := by exact_mod_cast eb
  have ec' : (R.c : ℝ) = k * C := by exact_mod_cast ec
  have hA' : (0 : ℝ) < (A : ℝ) := Nat.cast_pos.mpr hA
  have hB' : (0 : ℝ) < (B : ℝ) := Nat.cast_pos.mpr hB
  have hhR : (C : ℝ) ^ 2 = (A : ℝ) ^ 2 + (B : ℝ) ^ 2 + A * B := by
    exact_mod_cast (by nlinarith [hh] : C ^ 2 = A ^ 2 + B ^ 2 + A * B)
  have hcc : (R.c : ℝ) ^ 2 = k ^ 2 * ((A : ℝ) ^ 2 + A * B + B ^ 2) := by
    rw [ec', mul_pow, hhR]; ring
  have hpq : (R.b : ℝ) ^ 2 + (R.b : ℝ) * R.a + (R.a : ℝ) ^ 2 = (R.c : ℝ) ^ 2 := by
    rw [hcc, ea', eb']; ring
  have hlam : (((R.b : ℝ) + 2 * R.a) / ((R.a : ℝ) + 2 * R.b))
      = ((B : ℝ) + 2 * A) / ((A : ℝ) + 2 * B) := by
    rw [ea', eb']; field_simp
  have hmm : m = m' / k := by field_simp; linarith
  have hT0 := tile_to_Dis R A B C k hk hA hB hh ea eb ec hT
  rw [dil_TriSet _ (inv_pos.mpr hkr)] at hT0
  have hD' : 0 < det3 ((k : ℝ)⁻¹ * Ax) ((k : ℝ)⁻¹ * Ay) ((k : ℝ)⁻¹ * Dx) ((k : ℝ)⁻¹ * Dy)
      ((k : ℝ)⁻¹ * Bx) ((k : ℝ)⁻¹ * By) := by
    rw [det3_smul]; positivity
  have hAD' : ((k : ℝ)⁻¹ * Ax - (k : ℝ)⁻¹ * Dx) ^ 2 + ((k : ℝ)⁻¹ * Ay - (k : ℝ)⁻¹ * Dy) ^ 2
      = (((B : ℝ) + 2 * A) * m' * B) ^ 2 := by
    have e : ((k : ℝ)⁻¹ * Ax - (k : ℝ)⁻¹ * Dx) ^ 2 + ((k : ℝ)⁻¹ * Ay - (k : ℝ)⁻¹ * Dy) ^ 2
        = ((k : ℝ)⁻¹) ^ 2 * ((Ax - Dx) ^ 2 + (Ay - Dy) ^ 2) := by ring
    rw [e, hAD, ea', eb', hmm]; field_simp
  have hBD' : ((k : ℝ)⁻¹ * Bx - (k : ℝ)⁻¹ * Dx) ^ 2 + ((k : ℝ)⁻¹ * By - (k : ℝ)⁻¹ * Dy) ^ 2
      = (((A : ℝ) + 2 * B) * A * m') ^ 2 := by
    have e : ((k : ℝ)⁻¹ * Bx - (k : ℝ)⁻¹ * Dx) ^ 2 + ((k : ℝ)⁻¹ * By - (k : ℝ)⁻¹ * Dy) ^ 2
        = ((k : ℝ)⁻¹) ^ 2 * ((Bx - Dx) ^ 2 + (By - Dy) ^ 2) := by ring
    rw [e, hBD, ea', eb', hmm]; field_simp
  have hAB' : ((k : ℝ)⁻¹ * Ax - (k : ℝ)⁻¹ * Bx) ^ 2 + ((k : ℝ)⁻¹ * Ay - (k : ℝ)⁻¹ * By) ^ 2
      = (((A : ℝ) ^ 2 + A * B + B ^ 2) * m') ^ 2 := by
    have e : ((k : ℝ)⁻¹ * Ax - (k : ℝ)⁻¹ * Bx) ^ 2 + ((k : ℝ)⁻¹ * Ay - (k : ℝ)⁻¹ * By) ^ 2
        = ((k : ℝ)⁻¹) ^ 2 * ((Ax - Bx) ^ 2 + (Ay - By) ^ 2) := by ring
    rw [e, hAB, hcc, hmm]; field_simp
  have hcore := ZhangProp11b.zhang_prop11_2_core A B m' hA hB hm' _ _ _ _ _ _ hD'
    (by rw [hAD']) hBD' hAB' hT0
  obtain ⟨C1, hr1, hc1⟩ := rat_dis R A B C k hk hA hB hh ea eb ec hcore
  have hm1 := ext_metric (R.b : ℝ) (R.a : ℝ) m ((R.c : ℝ) ^ 2) (by rw [eb']; positivity)
    (by rw [ea']; positivity) hpq.symm Ax Ay Bx By Dx Dy hAD hBD hAB
  refine ⟨_, _, rfl, rfl, ?_, ?_, ⟨C1, ?_, hc1⟩, ?_⟩
  · rw [hm1.1]; ring
  · rw [hm1.2]; rw [mul_pow, mul_pow]; ring
  · rw [hr1, dil_TriSet _ hkr, ← hlam]
    have e1 : ∀ x : ℝ, (k : ℝ) * ((k : ℝ)⁻¹ * x) = x := fun x => mul_inv_cancel_left₀ hk0 x
    have eC : ∀ x y : ℝ, (k : ℝ) * ((k : ℝ)⁻¹ * x + (((R.b : ℝ) + 2 * R.a) / ((R.a : ℝ) + 2 * R.b))
        * ((k : ℝ)⁻¹ * x - (k : ℝ)⁻¹ * y)) = x + (((R.b : ℝ) + 2 * R.a) / ((R.a : ℝ) + 2 * R.b)) * (x - y) := by
      intro x y; field_simp
    simp only [e1, eC]
  · intro hn0
    push_cast
    rw [hn0, ← hkm, ea', eb']; ring

end main

end Erdos634.ZhangRat3

#print axioms Erdos634.ZhangRat3.zhang_prop11_1_printed
#print axioms Erdos634.ZhangRat3.zhang_prop11_2_printed
