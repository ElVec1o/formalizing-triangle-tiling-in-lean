import Erdos634.Draft.ZhangProp6

/-!
# Zhang Proposition 6, part (2) (arXiv 2512.22696v4, Fig. 7 bottom)

Fig. 7 (bottom), read from the PDF (page 8) and reconstructed from the printed side labels
(`ab(b-a)`, `abc`, `ac²`, `bc²`); every length was checked numerically for `(a,b,c) = (3,5,7)`
(pieces `1225, 1225, 441, 36` and trapezoid `648`: `3575 = (b+2a)(a+2b)b²`).
Notation `d = b - a > 0`, `W = c²`; lattice coordinates `u e₁ + v e₂`, `F` the origin:

* `F=(0,0)`, `E=(0,Y)`, `G=(X,Y)`, `C=(X+Y,0)` with `X = a c²`, `Y = ab(b-a)`: `F C G E` is the
  ideal trapezoid `Tz 0 0 X Y` (legs `FE`, `CG` of length `Y`).
* `A = (-a²(b-a), 0)` on the line `FC`, `D = (a³, ab²)` on the line `AE`, `B = (a³-b³, b²(2a+b))`.
* Four triangles similar to the tile: `ABD` and `DGB` (scale `bc`), `EGD` (scale `ac`),
  `AEF` (scale `a(b-a)`); `G` lies on `BC`.  The big triangle `ABC` has sides `AB = bc²`,
  `AC = (a+2b)ab`, `BC = (b+2a)b²` and angles `2α, 2β, α+β` at `B, A, C`... (`AC` along `FC`).

Gluing: wedge at `D` for `ABD` (lines `AD`, `BD`), then lines `u=0`, `DG`, `v=Y`.
Credit Zhang (arXiv 2512.22696), Beeson, Beeson-Rosu, Laczkovich.  UNAUDITED.
-/

namespace Erdos634.ZhangProp6b

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.GlueCut Erdos634.SssCongruent Erdos634.ZhangL1 Erdos634.ZhangPara
  Erdos634.ZhangProp3 Erdos634.ZhangThm4 Erdos634.ZhangSporadic Erdos634.ZhangLat
  Erdos634.ZhangProp6

/-! ### Unit tiles with a `c` in the denominator -/

section tilesc
variable {a b c : ℝ}

theorem Dis_LT_tile1c (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (k : ℕ) (hk : 0 < k) (κ : ℝ)
    (hκ : (k : ℝ) = κ * c) (u0 v0 m1 n1 m2 n2 : ℝ) (hU : 0 < ld 0 0 m1 n1 m2 n2)
    (h1 : m1 ^ 2 + m1 * n1 + n1 ^ 2 = a ^ 2 * c ^ 2)
    (h2 : m2 ^ 2 + m2 * n2 + n2 ^ 2 = b ^ 2 * c ^ 2)
    (h12 : (m2 - m1) ^ 2 + (m2 - m1) * (n2 - n1) + (n2 - n1) ^ 2 = (a ^ 2 + b ^ 2 + a * b) * c ^ 2)
    (U1 V1 U2 V2 : ℝ) (hU1 : U1 = u0 + κ * m1) (hV1 : V1 = v0 + κ * n1)
    (hU2 : U2 = u0 + κ * m2) (hV2 : V2 = v0 + κ * n2) :
    Dis (Rmodel ha hb) (LT u0 v0 U1 V1 U2 V2) (k * k) := by
  have hc0 : c ≠ 0 := hc.ne'
  refine Dis_LT_tile1 ha hb k hk u0 v0 (m1 / c) (n1 / c) (m2 / c) (n2 / c) ?_ ?_ ?_ ?_ U1 V1 U2 V2
    ?_ ?_ ?_ ?_
  · have : ld 0 0 (m1 / c) (n1 / c) (m2 / c) (n2 / c) = ld 0 0 m1 n1 m2 n2 / c ^ 2 := by
      simp only [ld]; field_simp; ring
    rw [this]; positivity
  · field_simp; linear_combination h1
  · field_simp; linear_combination h2
  · field_simp; linear_combination h12
  · rw [hU1, hκ]; field_simp
  · rw [hV1, hκ]; field_simp
  · rw [hU2, hκ]; field_simp
  · rw [hV2, hκ]; field_simp

theorem Dis_LT_tile2c (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (k : ℕ) (hk : 0 < k) (κ : ℝ)
    (hκ : (k : ℝ) = κ * c) (u0 v0 m1 n1 m2 n2 : ℝ) (hU : 0 < ld 0 0 m1 n1 m2 n2)
    (h1 : m1 ^ 2 + m1 * n1 + n1 ^ 2 = b ^ 2 * c ^ 2)
    (h2 : m2 ^ 2 + m2 * n2 + n2 ^ 2 = a ^ 2 * c ^ 2)
    (h12 : (m2 - m1) ^ 2 + (m2 - m1) * (n2 - n1) + (n2 - n1) ^ 2 = (a ^ 2 + b ^ 2 + a * b) * c ^ 2)
    (U1 V1 U2 V2 : ℝ) (hU1 : U1 = u0 + κ * m1) (hV1 : V1 = v0 + κ * n1)
    (hU2 : U2 = u0 + κ * m2) (hV2 : V2 = v0 + κ * n2) :
    Dis (Rmodel ha hb) (LT u0 v0 U1 V1 U2 V2) (k * k) := by
  have hc0 : c ≠ 0 := hc.ne'
  refine Dis_LT_tile2 ha hb k hk u0 v0 (m1 / c) (n1 / c) (m2 / c) (n2 / c) ?_ ?_ ?_ ?_ U1 V1 U2 V2
    ?_ ?_ ?_ ?_
  · have : ld 0 0 (m1 / c) (n1 / c) (m2 / c) (n2 / c) = ld 0 0 m1 n1 m2 n2 / c ^ 2 := by
      simp only [ld]; field_simp; ring
    rw [this]; positivity
  · field_simp; linear_combination h1
  · field_simp; linear_combination h2
  · field_simp; linear_combination h12
  · rw [hU1, hκ]; field_simp
  · rw [hV1, hκ]; field_simp
  · rw [hU2, hκ]; field_simp
  · rw [hV2, hκ]; field_simp

end tilesc

section coords
variable (a d : ℝ)

noncomputable def qAu : ℝ := -(a ^ 2 * d)
noncomputable def qBu : ℝ := a ^ 3 - (a + d) ^ 3
noncomputable def qBv : ℝ := (a + d) ^ 2 * (3 * a + d)
noncomputable def qDu (a _d : ℝ) : ℝ := a ^ 3
noncomputable def qDv (a d : ℝ) : ℝ := a * (a + d) ^ 2
noncomputable def pg2 : ℝ := (2 * a + d) * a ^ 3 + (a + d) * (a * (a + d) ^ 2)
noncomputable def pg3 : ℝ := a * a ^ 3 + (2 * a + d) * (a * (a + d) ^ 2)
noncomputable def l1 (u v : ℝ) : ℝ := (a + d) * u - a * v + a * pY a d
noncomputable def l2 (u v : ℝ) : ℝ := pg2 a d - (2 * a + d) * u - (a + d) * v
noncomputable def l3 (u v : ℝ) : ℝ := a * u + (2 * a + d) * v - pg3 a d

/-- the three half-plane conditions of the big triangle `A C B` (counterclockwise). -/
def InT' (u v : ℝ) : Prop :=
  0 ≤ ld u v (pFu a d) 0 (qBu a d) (qBv a d) ∧ 0 ≤ ld (qAu a d) 0 u v (qBu a d) (qBv a d) ∧
    0 ≤ ld (qAu a d) 0 (pFu a d) 0 u v

end coords

section vertices
variable {a d : ℝ}

theorem inT'_A (ha : 0 < a) (hd : 0 < d) : InT' a d (qAu a d) (0) := by
  refine ⟨?_, ?_, ?_⟩
  · have e : ld (qAu a d) (0) (pFu a d) 0 (qBu a d) (qBv a d) = a*(a + d)^3*(3*a + d)*(3*a + 2*d) := by
      simp only [ld, pW, pY, pX, pFu, qAu, qBu, qBv, qDu, qDv]; ring
    rw [e]; positivity
  · apply le_of_eq; symm; simp only [ld, pW, pY, pX, pFu, qAu, qBu, qBv, qDu, qDv]; ring
  · apply le_of_eq; symm; simp only [ld, pW, pY, pX, pFu, qAu, qBu, qBv, qDu, qDv]; ring

theorem inT'_B (ha : 0 < a) (hd : 0 < d) : InT' a d (qBu a d) (qBv a d) := by
  refine ⟨?_, ?_, ?_⟩
  · apply le_of_eq; symm; simp only [ld, pW, pY, pX, pFu, qAu, qBu, qBv, qDu, qDv]; ring
  · apply le_of_eq; symm; simp only [ld, pW, pY, pX, pFu, qAu, qBu, qBv, qDu, qDv]; ring
  · have e : ld (qAu a d) 0 (pFu a d) 0 (qBu a d) (qBv a d) = a*(a + d)^3*(3*a + d)*(3*a + 2*d) := by
      simp only [ld, pW, pY, pX, pFu, qAu, qBu, qBv, qDu, qDv]; ring
    rw [e]; positivity

theorem inT'_C (ha : 0 < a) (hd : 0 < d) : InT' a d (pFu a d) (0) := by
  refine ⟨?_, ?_, ?_⟩
  · apply le_of_eq; symm; simp only [ld, pW, pY, pX, pFu, qAu, qBu, qBv, qDu, qDv]; ring
  · have e : ld (qAu a d) 0 (pFu a d) (0) (qBu a d) (qBv a d) = a*(a + d)^3*(3*a + d)*(3*a + 2*d) := by
      simp only [ld, pW, pY, pX, pFu, qAu, qBu, qBv, qDu, qDv]; ring
    rw [e]; positivity
  · apply le_of_eq; symm; simp only [ld, pW, pY, pX, pFu, qAu, qBu, qBv, qDu, qDv]; ring

theorem inT'_D (ha : 0 < a) (hd : 0 < d) : InT' a d (qDu a d) (qDv a d) := by
  refine ⟨?_, ?_, ?_⟩
  · have e : ld (qDu a d) (qDv a d) (pFu a d) 0 (qBu a d) (qBv a d) = a*(a + d)^4*(3*a + d) := by
      simp only [ld, pW, pY, pX, pFu, qAu, qBu, qBv, qDu, qDv]; ring
    rw [e]; positivity
  · have e : ld (qAu a d) 0 (qDu a d) (qDv a d) (qBu a d) (qBv a d) = a*(a + d)^3*(3*a^2 + 3*a*d + d^2) := by
      simp only [ld, pW, pY, pX, pFu, qAu, qBu, qBv, qDu, qDv]; ring
    rw [e]; positivity
  · have e : ld (qAu a d) 0 (pFu a d) 0 (qDu a d) (qDv a d) = a^2*(a + d)^3*(3*a + 2*d) := by
      simp only [ld, pW, pY, pX, pFu, qAu, qBu, qBv, qDu, qDv]; ring
    rw [e]; positivity

theorem inT'_E (ha : 0 < a) (hd : 0 < d) : InT' a d (0) (pY a d) := by
  refine ⟨?_, ?_, ?_⟩
  · have e : ld (0) (pY a d) (pFu a d) 0 (qBu a d) (qBv a d) = a*(a + d)^2*(3*a + d)*(3*a^2 + 3*a*d + d^2) := by
      simp only [ld, pW, pY, pX, pFu, qAu, qBu, qBv, qDu, qDv]; ring
    rw [e]; positivity
  · have e : ld (qAu a d) 0 (0) (pY a d) (qBu a d) (qBv a d) = a*d*(a + d)^2*(3*a^2 + 3*a*d + d^2) := by
      simp only [ld, pW, pY, pX, pFu, qAu, qBu, qBv, qDu, qDv]; ring
    rw [e]; positivity
  · have e : ld (qAu a d) 0 (pFu a d) 0 (0) (pY a d) = a^2*d*(a + d)^2*(3*a + 2*d) := by
      simp only [ld, pW, pY, pX, pFu, qAu, qBu, qBv, qDu, qDv]; ring
    rw [e]; positivity

theorem inT'_F (ha : 0 < a) (hd : 0 < d) : InT' a d (0) (0) := by
  refine ⟨?_, ?_, ?_⟩
  · have e : ld (0) (0) (pFu a d) 0 (qBu a d) (qBv a d) = a*(a + d)^2*(3*a + d)*(3*a^2 + 4*a*d + 2*d^2) := by
      simp only [ld, pW, pY, pX, pFu, qAu, qBu, qBv, qDu, qDv]; ring
    rw [e]; positivity
  · have e : ld (qAu a d) 0 (0) (0) (qBu a d) (qBv a d) = a^2*d*(a + d)^2*(3*a + d) := by
      simp only [ld, pW, pY, pX, pFu, qAu, qBu, qBv, qDu, qDv]; ring
    rw [e]; positivity
  · apply le_of_eq; symm; simp only [ld, pW, pY, pX, pFu, qAu, qBu, qBv, qDu, qDv]; ring

theorem inT'_G (ha : 0 < a) (hd : 0 < d) : InT' a d (pX a d) (pY a d) := by
  refine ⟨?_, ?_, ?_⟩
  · apply le_of_eq; symm; simp only [ld, pW, pY, pX, pFu, qAu, qBu, qBv, qDu, qDv]; ring
  · have e : ld (qAu a d) 0 (pX a d) (pY a d) (qBu a d) (qBv a d) = a*(a + d)^2*(3*a + 2*d)*(3*a^2 + 3*a*d + d^2) := by
      simp only [ld, pW, pY, pX, pFu, qAu, qBu, qBv, qDu, qDv]; ring
    rw [e]; positivity
  · have e : ld (qAu a d) 0 (pFu a d) 0 (pX a d) (pY a d) = a^2*d*(a + d)^2*(3*a + 2*d) := by
      simp only [ld, pW, pY, pX, pFu, qAu, qBu, qBv, qDu, qDv]; ring
    rw [e]; positivity

theorem l_sum (u v : ℝ) : l1 a d u v + l2 a d u v + l3 a d u v = 0 := by
  simp only [l1, l2, l3, pg2, pg3, pY]; ring

theorem pg2_gt (ha : 0 < a) (hd : 0 < d) : 0 < pg2 a d - (a + d) * pY a d := by
  have : pg2 a d - (a + d) * pY a d = a ^ 2 * pW a d := by
    simp only [pg2, pY, pW]; ring
  rw [this]; have := pW_pos ha hd; positivity

theorem ABD_f (ha : 0 < a) (hd : 0 < d) {u v : ℝ}
    (h : LC (qDu a d) (qDv a d) (qBu a d) (qBv a d) (qAu a d) 0 u v) :
    l1 a d u v ≤ 0 ∧ 0 ≤ l2 a d u v := by
  obtain ⟨c1, c2, c3⟩ := h
  have k2 : ld (qDu a d) (qDv a d) u v (qAu a d) 0 = -(a * (a + d)) * l1 a d u v := by
    simp only [ld, l1, qDu, qDv, qAu, pY]; ring
  have k3 : ld (qDu a d) (qDv a d) (qBu a d) (qBv a d) u v = (a + d) ^ 2 * l2 a d u v := by
    simp only [ld, l2, qDu, qDv, qBu, qBv, pg2]; ring
  rw [k2] at c2
  rw [k3] at c3
  refine ⟨?_, nn_of_mul (by positivity : 0 < (a + d) ^ 2) c3⟩
  have := nn_of_mul (by positivity : 0 < a * (a + d)) (x := -l1 a d u v) (by linarith)
  linarith

theorem AEF_f (ha : 0 < a) (hd : 0 < d) {u v : ℝ}
    (h : LC 0 0 0 (pY a d) (qAu a d) 0 u v) :
    0 ≤ l1 a d u v ∧ 0 ≤ v ∧ u ≤ 0 ∧ v ≤ pY a d := by
  obtain ⟨c1, c2, c3⟩ := h
  have k1 : ld u v 0 (pY a d) (qAu a d) 0 = a * d * l1 a d u v := by
    simp only [ld, l1, qAu, pY]; ring
  have k2 : ld 0 0 u v (qAu a d) 0 = a ^ 2 * d * v := by simp only [ld, qAu]; ring
  have k3 : ld 0 0 0 (pY a d) u v = a * d * (a + d) * (-u) := by simp only [ld, pY]; ring
  rw [k1] at c1; rw [k2] at c2; rw [k3] at c3
  have h1 := nn_of_mul (by positivity : 0 < a * d) c1
  have h2 := nn_of_mul (by positivity : 0 < a ^ 2 * d) c2
  have h3 := nn_of_mul (by positivity : 0 < a * d * (a + d)) c3
  refine ⟨h1, h2, by linarith, ?_⟩
  have key : a * (pY a d - v) = l1 a d u v + (a + d) * (-u) := by simp only [l1]; ring
  have : 0 ≤ a * (pY a d - v) := by rw [key]; nlinarith
  have := nn_of_mul ha this
  linarith

theorem EGD_f (ha : 0 < a) (hd : 0 < d) {u v : ℝ}
    (h : LC (qDu a d) (qDv a d) 0 (pY a d) (pX a d) (pY a d) u v) :
    pY a d ≤ v ∧ l3 a d u v ≤ 0 ∧ 0 ≤ l1 a d u v := by
  obtain ⟨c1, c2, c3⟩ := h
  have k1 : ld u v 0 (pY a d) (pX a d) (pY a d) = a * pW a d * (v - pY a d) := by
    simp only [ld, pX, pY, pW]; ring
  have k2 : ld (qDu a d) (qDv a d) u v (pX a d) (pY a d) = -(a * (a + d)) * l3 a d u v := by
    simp only [ld, l3, pg3, qDu, qDv, pX, pY, pW]; ring
  have k3 : ld (qDu a d) (qDv a d) 0 (pY a d) u v = a ^ 2 * l1 a d u v := by
    simp only [ld, l1, qDu, qDv, pY]; ring
  rw [k1] at c1; rw [k2] at c2; rw [k3] at c3
  have hW := pW_pos ha hd
  have h1 := nn_of_mul (by positivity : 0 < a * pW a d) c1
  have h3 := nn_of_mul (by positivity : 0 < a ^ 2) c3
  have h2 := nn_of_mul (by positivity : 0 < a * (a + d)) (x := -l3 a d u v) (by linarith)
  exact ⟨by linarith, by linarith, h3⟩

theorem DGB_f (ha : 0 < a) (hd : 0 < d) {u v : ℝ}
    (h : LC (qDu a d) (qDv a d) (pX a d) (pY a d) (qBu a d) (qBv a d) u v) :
    pY a d ≤ v ∧ 0 ≤ l3 a d u v ∧ l2 a d u v ≤ 0 ∧ u + v ≤ pFu a d := by
  obtain ⟨c1, c2, c3⟩ := h
  have hW := pW_pos ha hd
  have k1 : ld u v (pX a d) (pY a d) (qBu a d) (qBv a d) =
      -((a + d) * pW a d) * (u + v - pFu a d) := by
    simp only [ld, pX, pY, pW, pFu, qBu, qBv]; ring
  have k2 : ld (qDu a d) (qDv a d) u v (qBu a d) (qBv a d) = -((a + d) ^ 2) * l2 a d u v := by
    simp only [ld, l2, pg2, qDu, qDv, qBu, qBv]; ring
  have k3 : ld (qDu a d) (qDv a d) (pX a d) (pY a d) u v = a * (a + d) * l3 a d u v := by
    simp only [ld, l3, pg3, qDu, qDv, pX, pY, pW]; ring
  have hΔ : 0 < ld (qDu a d) (qDv a d) (pX a d) (pY a d) (qBu a d) (qBv a d) := by
    have : ld (qDu a d) (qDv a d) (pX a d) (pY a d) (qBu a d) (qBv a d) =
        a * (a + d) ^ 3 * pW a d := by
      simp only [ld, pX, pY, pW, qDu, qDv, qBu, qBv]; ring
    rw [this]; positivity
  have key : ld (qDu a d) (qDv a d) (pX a d) (pY a d) (qBu a d) (qBv a d) * (v - pY a d) =
      ld u v (pX a d) (pY a d) (qBu a d) (qBv a d) * (a ^ 2 * (a + d)) +
        ld (qDu a d) (qDv a d) (pX a d) (pY a d) u v * ((a + d) * pW a d) := by
    simp only [ld, pX, pY, pW, qDu, qDv, qBu, qBv]; ring
  rw [k1] at c1; rw [k2] at c2; rw [k3] at c3
  have h1 := nn_of_mul (by positivity : 0 < (a + d) * pW a d) (x := -(u + v - pFu a d)) (by linarith)
  have h2 := nn_of_mul (by positivity : 0 < (a + d) ^ 2) (x := -l2 a d u v) (by linarith)
  have h3 := nn_of_mul (by positivity : 0 < a * (a + d)) c3
  refine ⟨?_, h3, by linarith, by linarith⟩
  have hv : 0 ≤ ld (qDu a d) (qDv a d) (pX a d) (pY a d) (qBu a d) (qBv a d) * (v - pY a d) := by
    rw [key]
    have e1 : 0 ≤ ld u v (pX a d) (pY a d) (qBu a d) (qBv a d) := by rw [k1]; exact c1
    have e3 : 0 ≤ ld (qDu a d) (qDv a d) (pX a d) (pY a d) u v := by rw [k3]; exact c3
    positivity
  have := nn_of_mul hΔ hv
  linarith

theorem InT'_c1 (ha : 0 < a) (hd : 0 < d) (u v : ℝ) (h : InT' a d u v) : u + v ≤ pFu a d := by
  obtain ⟨c1, -, -⟩ := h
  have key : ld u v (pFu a d) 0 (qBu a d) (qBv a d) =
      (a + d) ^ 2 * (3 * a + d) * (pFu a d - (u + v)) := by
    simp only [ld, pFu, pX, pY, pW, qBu, qBv]; ring
  rw [key] at c1
  have := nn_of_mul (by positivity : 0 < (a + d) ^ 2 * (3 * a + d)) c1
  linarith

theorem InT'_c3 (ha : 0 < a) (hd : 0 < d) (u v : ℝ) (h : InT' a d u v) : 0 ≤ v := by
  obtain ⟨-, -, c3⟩ := h
  have key : ld (qAu a d) 0 (pFu a d) 0 u v = a * (a + d) * (3 * a + 2 * d) * v := by
    simp only [ld, pFu, pX, pY, pW, qAu]; ring
  rw [key] at c3
  exact nn_of_mul (by positivity : 0 < a * (a + d) * (3 * a + 2 * d)) c3

theorem tz_sub' (ha : 0 < a) (hd : 0 < d) :
    Tz 0 0 (pX a d) (pY a d) ⊆ LT (qAu a d) 0 (pFu a d) 0 (qBu a d) (qBv a d) := by
  intro q hq
  obtain ⟨hu, hv, hvy, huv⟩ := hq
  rw [mem_LT]
  set u := uu 0 0 q
  set v := vv 0 0 q
  refine ⟨?_, ?_, ?_⟩
  · have key : ld u v (pFu a d) 0 (qBu a d) (qBv a d) =
        (a + d) ^ 2 * (3 * a + d) * (pFu a d - (u + v)) := by
      simp only [ld, pFu, pX, pY, pW, qBu, qBv]; ring
    rw [key]
    have : 0 ≤ pFu a d - (u + v) := by unfold pFu; linarith
    positivity
  · have key : ld (qAu a d) 0 u v (qBu a d) (qBv a d) =
        (a + d) ^ 2 * (3 * a + d) * u + d * (a + d) * (2 * a + d) * v +
          a ^ 2 * d * (a + d) ^ 2 * (3 * a + d) := by
      simp only [ld, qAu, qBu, qBv]; ring
    rw [key]; positivity
  · have key : ld (qAu a d) 0 (pFu a d) 0 u v = a * (a + d) * (3 * a + 2 * d) * v := by
      simp only [ld, pFu, pX, pY, pW, qAu]; ring
    rw [key]; positivity

theorem cover' (ha : 0 < a) (hd : 0 < d) (u v : ℝ) (hT : InT' a d u v) :
    (0 ≤ u ∧ 0 ≤ v ∧ v ≤ pY a d ∧ u + v ≤ pX a d + pY a d) ∨
    LC (qDu a d) (qDv a d) (qBu a d) (qBv a d) (qAu a d) 0 u v ∨
    LC 0 0 0 (pY a d) (qAu a d) 0 u v ∨
    LC (qDu a d) (qDv a d) 0 (pY a d) (pX a d) (pY a d) u v ∨
    LC (qDu a d) (qDv a d) (pX a d) (pY a d) (qBu a d) (qBv a d) u v := by
  have c1' := InT'_c1 ha hd u v hT
  have c3' := InT'_c3 ha hd u v hT
  obtain ⟨-, c2, -⟩ := hT
  have hY := pY_pos ha hd
  have hW := pW_pos ha hd
  have hsum := l_sum (a := a) (d := d) u v
  by_cases hW' : l1 a d u v ≤ 0 ∧ 0 ≤ l2 a d u v
  · right; left
    obtain ⟨h1, h2⟩ := hW'
    refine ⟨?_, ?_, ?_⟩
    · simp only [ld] at c2 ⊢; linarith
    · have k2 : ld (qDu a d) (qDv a d) u v (qAu a d) 0 = -(a * (a + d)) * l1 a d u v := by
        simp only [ld, l1, qDu, qDv, qAu, pY]; ring
      rw [k2]; nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ a * (a + d)) (neg_nonneg.mpr h1)]
    · have k3 : ld (qDu a d) (qDv a d) (qBu a d) (qBv a d) u v = (a + d) ^ 2 * l2 a d u v := by
        simp only [ld, l2, qDu, qDv, qBu, qBv, pg2]; ring
      rw [k3]; positivity
  by_cases hv : v ≤ pY a d
  · by_cases hu : 0 ≤ u
    · left
      refine ⟨hu, c3', hv, ?_⟩
      have : pFu a d = pX a d + pY a d := rfl
      linarith
    · push_neg at hu
      right; right; left
      have hl1 : 0 ≤ l1 a d u v := by
        by_contra hl
        push_neg at hl
        have hl2 : l2 a d u v < 0 := by
          by_contra h2; push_neg at h2; exact hW' ⟨hl.le, h2⟩
        have := pg2_gt ha hd
        simp only [l2] at hl2
        nlinarith [mul_pos (by positivity : (0:ℝ) < 2 * a + d) (neg_pos.mpr hu),
          mul_nonneg (by positivity : (0:ℝ) ≤ a + d) (sub_nonneg.mpr hv)]
      refine ⟨?_, ?_, ?_⟩
      · have k1 : ld u v 0 (pY a d) (qAu a d) 0 = a * d * l1 a d u v := by
          simp only [ld, l1, qAu, pY]; ring
        rw [k1]; positivity
      · have k2 : ld 0 0 u v (qAu a d) 0 = a ^ 2 * d * v := by simp only [ld, qAu]; ring
        rw [k2]; have := c3'; positivity
      · have k3 : ld 0 0 0 (pY a d) u v = a * d * (a + d) * (-u) := by simp only [ld, pY]; ring
        rw [k3]; nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ a * d * (a + d)) (neg_nonneg.mpr hu.le)]
  · push_neg at hv
    by_cases h3 : l3 a d u v ≤ 0
    · right; right; right; left
      have hl1 : 0 ≤ l1 a d u v := by
        by_contra hl
        push_neg at hl
        have hl2 : l2 a d u v < 0 := by
          by_contra h2; push_neg at h2; exact hW' ⟨hl.le, h2⟩
        linarith
      refine ⟨?_, ?_, ?_⟩
      · have k1 : ld u v 0 (pY a d) (pX a d) (pY a d) = a * pW a d * (v - pY a d) := by
          simp only [ld, pX, pY, pW]; ring
        rw [k1]; nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ a * pW a d) (sub_nonneg.mpr hv.le)]
      · have k2 : ld (qDu a d) (qDv a d) u v (pX a d) (pY a d) = -(a * (a + d)) * l3 a d u v := by
          simp only [ld, l3, pg3, qDu, qDv, pX, pY, pW]; ring
        rw [k2]; nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ a * (a + d)) (neg_nonneg.mpr h3)]
      · have k3 : ld (qDu a d) (qDv a d) 0 (pY a d) u v = a ^ 2 * l1 a d u v := by
          simp only [ld, l1, qDu, qDv, pY]; ring
        rw [k3]; positivity
    · push_neg at h3
      right; right; right; right
      have hl2 : l2 a d u v ≤ 0 := by
        by_contra h2; push_neg at h2
        have hl1 : 0 < l1 a d u v := by
          by_contra hl; push_neg at hl; exact hW' ⟨hl, h2.le⟩
        linarith
      refine ⟨?_, ?_, ?_⟩
      · have k1 : ld u v (pX a d) (pY a d) (qBu a d) (qBv a d) =
            -((a + d) * pW a d) * (u + v - pFu a d) := by
          simp only [ld, pX, pY, pW, pFu, qBu, qBv]; ring
        rw [k1]; nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ (a + d) * pW a d) (sub_nonneg.mpr c1')]
      · have k2 : ld (qDu a d) (qDv a d) u v (qBu a d) (qBv a d) = -((a + d) ^ 2) * l2 a d u v := by
          simp only [ld, l2, pg2, qDu, qDv, qBu, qBv]; ring
        rw [k2]; nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ (a + d) ^ 2) (neg_nonneg.mpr hl2)]
      · have k3 : ld (qDu a d) (qDv a d) (pX a d) (pY a d) u v = a * (a + d) * l3 a d u v := by
          simp only [ld, l3, pg3, qDu, qDv, pX, pY, pW]; ring
        rw [k3]; positivity

/-- **Zhang Prop. 6(2), real form.**  `c` real with `c² = a²+ab+b²`; naturals `k1 = bc`, `k2 = ac`,
`k3 = a(b-a)`; the trapezoid `Tz 0 0 X Y` is tiled by `nT` tiles.  Then the triangle `A C B`
is tiled by `k1² + (k3² + nT + (k2² + k1²))` tiles. -/
theorem prop6b_real (ha : 0 < a) (hd : 0 < d) {b : ℝ} (hb : 0 < b) (hbd : b = a + d)
    (c : ℝ) (hc : 0 < c) (hcc : c * c = pW a d) (k1 k2 k3 : ℕ)
    (hk1 : (k1 : ℝ) = (a + d) * c) (hk2 : (k2 : ℝ) = a * c) (hk3 : (k3 : ℝ) = a * d)
    {nT : ℕ} (hTz : Dis (Rmodel ha hb) (Tz 0 0 (pX a d) (pY a d)) nT) :
    Dis (Rmodel ha hb) (LT (qAu a d) 0 (pFu a d) 0 (qBu a d) (qBv a d))
      (k1 * k1 + (k3 * k3 + nT + (k2 * k2 + k1 * k1))) := by
  subst hbd
  have hW := pW_pos ha hd
  have hc2 : c ^ 2 = pW a d := by rw [sq]; exact hcc
  have hk1p : 0 < k1 := Nat.cast_pos.mp (by rw [hk1]; positivity)
  have hk2p : 0 < k2 := Nat.cast_pos.mp (by rw [hk2]; positivity)
  have hk3p : 0 < k3 := Nat.cast_pos.mp (by rw [hk3]; positivity)
  have hABD : Dis (Rmodel ha hb) (LT (qDu a d) (qDv a d) (qBu a d) (qBv a d) (qAu a d) 0) (k1 * k1) :=
    Dis_LT_tile2c ha hb hc k1 hk1p (a + d) hk1 (qDu a d) (qDv a d)
      (-((a + d) ^ 2)) ((a + d) * (2 * a + d)) (-(a ^ 2)) (-(a * (a + d)))
      (by have : ld 0 0 (-((a + d) ^ 2)) ((a + d) * (2 * a + d)) (-(a ^ 2)) (-(a * (a + d))) =
            a * (a + d) * pW a d := by simp only [ld, pW]; ring
          rw [this]; positivity)
      (by rw [hc2]; simp only [pW]; ring) (by rw [hc2]; simp only [pW]; ring)
      (by rw [hc2]; simp only [pW]; ring) _ _ _ _
      (by simp only [qBu, qDu]; ring) (by simp only [qBv, qDv]; ring)
      (by simp only [qAu, qDu]; ring) (by simp only [qDv]; ring)
  have hDGB : Dis (Rmodel ha hb) (LT (qDu a d) (qDv a d) (pX a d) (pY a d) (qBu a d) (qBv a d)) (k1 * k1) :=
    Dis_LT_tile1c ha hb hc k1 hk1p (a + d) hk1 (qDu a d) (qDv a d)
      (a * (2 * a + d)) (-(a ^ 2)) (-((a + d) ^ 2)) ((a + d) * (2 * a + d))
      (by have : ld 0 0 (a * (2 * a + d)) (-(a ^ 2)) (-((a + d) ^ 2)) ((a + d) * (2 * a + d)) =
            a * (a + d) * pW a d := by simp only [ld, pW]; ring
          rw [this]; positivity)
      (by rw [hc2]; simp only [pW]; ring) (by rw [hc2]; simp only [pW]; ring)
      (by rw [hc2]; simp only [pW]; ring) _ _ _ _
      (by simp only [pX, pW, qDu]; ring) (by simp only [pY, qDv]; ring)
      (by simp only [qBu, qDu]; ring) (by simp only [qBv, qDv]; ring)
  have hEGD : Dis (Rmodel ha hb) (LT (qDu a d) (qDv a d) 0 (pY a d) (pX a d) (pY a d)) (k2 * k2) :=
    Dis_LT_tile1c ha hb hc k2 hk2p a hk2 (qDu a d) (qDv a d)
      (-(a ^ 2)) (-(a * (a + d))) ((a + d) * (2 * a + d)) (-(a * (a + d)))
      (by have : ld 0 0 (-(a ^ 2)) (-(a * (a + d))) ((a + d) * (2 * a + d)) (-(a * (a + d))) =
            a * (a + d) * pW a d := by simp only [ld, pW]; ring
          rw [this]; positivity)
      (by rw [hc2]; simp only [pW]; ring) (by rw [hc2]; simp only [pW]; ring)
      (by rw [hc2]; simp only [pW]; ring) _ _ _ _
      (by simp only [qDu]; ring) (by simp only [pY, qDv]; ring)
      (by simp only [pX, pW, qDu]; ring) (by simp only [pY, qDv]; ring)
  have hAEF : Dis (Rmodel ha hb) (LT 0 0 0 (pY a d) (qAu a d) 0) (k3 * k3) :=
    Dis_LT_tile2 ha hb k3 hk3p 0 0 0 (a + d) (-a) 0
      (by have : ld 0 0 0 (a + d) (-a) 0 = a * (a + d) := by simp only [ld]; ring
          rw [this]; positivity)
      (by ring) (by ring) (by ring) _ _ _ _
      (by ring) (by rw [hk3]; simp only [pY]; ring) (by rw [hk3]; simp only [qAu]; ring) (by ring)
  -- gluing
  have hQlow := Dis.glue_lat hAEF hTz 1 0 0 (by norm_num)
    (fun q hq => by
      have := (AEF_f ha hd ((mem_LT_LC _ _ _ _ _ _ q).1 hq)).2.2.1; linarith)
    (fun q hq => by have := hq.1; linarith)
  have hQup := Dis.glue_lat hEGD hDGB a (2 * a + d) (pg3 a d) (by positivity)
    (fun q hq => by
      have := (EGD_f ha hd ((mem_LT_LC _ _ _ _ _ _ q).1 hq)).2.1
      simp only [l3] at this; linarith)
    (fun q hq => by
      have := (DGB_f ha hd ((mem_LT_LC _ _ _ _ _ _ q).1 hq)).2.1
      simp only [l3] at this; linarith)
  have hQmid := Dis.glue_lat hQlow hQup 0 1 (pY a d) (by norm_num)
    (fun q hq => by
      rcases hq with hq | hq
      · have := (AEF_f ha hd ((mem_LT_LC _ _ _ _ _ _ q).1 hq)).2.2.2; linarith
      · have := hq.2.2.1; linarith)
    (fun q hq => by
      rcases hq with hq | hq
      · have := (EGD_f ha hd ((mem_LT_LC _ _ _ _ _ _ q).1 hq)).1; linarith
      · have := (DGB_f ha hd ((mem_LT_LC _ _ _ _ _ _ q).1 hq)).1; linarith)
  have hQall := Dis.glue_quad_lat hABD hQmid (a + d) (-a) (-(a * pY a d)) (2 * a + d) (a + d)
    (pg2 a d) (by positivity) (by positivity)
    (fun q hq => by
      have := (ABD_f ha hd ((mem_LT_LC _ _ _ _ _ _ q).1 hq)).1
      simp only [l1] at this; linarith)
    (fun q hq => by
      have := (ABD_f ha hd ((mem_LT_LC _ _ _ _ _ _ q).1 hq)).2
      simp only [l2] at this; linarith)
    (fun q hq => by
      rcases hq with (hq | hq) | (hq | hq)
      · left
        have := (AEF_f ha hd ((mem_LT_LC _ _ _ _ _ _ q).1 hq)).1
        simp only [l1] at this; linarith
      · left
        have h1 := hq.1
        have h2 := hq.2.2.1
        have hY := pY_pos ha hd
        nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ a + d) h1, mul_nonneg ha.le (sub_nonneg.mpr h2)]
      · left
        have := (EGD_f ha hd ((mem_LT_LC _ _ _ _ _ _ q).1 hq)).2.2
        simp only [l1] at this; linarith
      · right
        have := (DGB_f ha hd ((mem_LT_LC _ _ _ _ _ _ q).1 hq)).2.2.1
        simp only [l2] at this; linarith)
  refine Dis.congr hQall ?_ rfl
  ext q
  constructor
  · intro hq
    rcases hq with hq | (hq | hq) | (hq | hq)
    · exact LT_sub (by
          have : ld (qDu a d) (qDv a d) (qBu a d) (qBv a d) (qAu a d) 0 = a * (a + d) ^ 3 * pW a d := by
            simp only [ld, pW, qDu, qDv, qBu, qBv, qAu]; ring
          rw [this]; positivity) (inT'_D ha hd) (inT'_B ha hd) (inT'_A ha hd) hq
    · exact LT_sub (by
          have : ld 0 0 0 (pY a d) (qAu a d) 0 = a ^ 3 * d ^ 2 * (a + d) := by
            simp only [ld, pY, qAu]; ring
          rw [this]; positivity) (inT'_F ha hd) (inT'_E ha hd) (inT'_A ha hd) hq
    · exact tz_sub' ha hd hq
    · exact LT_sub (by
          have : ld (qDu a d) (qDv a d) 0 (pY a d) (pX a d) (pY a d) = a ^ 3 * (a + d) * pW a d := by
            simp only [ld, pW, pX, pY, qDu, qDv]; ring
          rw [this]; positivity) (inT'_D ha hd) (inT'_E ha hd) (inT'_G ha hd) hq
    · exact LT_sub (by
          have : ld (qDu a d) (qDv a d) (pX a d) (pY a d) (qBu a d) (qBv a d) = a * (a + d) ^ 3 * pW a d := by
            simp only [ld, pW, pX, pY, qDu, qDv, qBu, qBv]; ring
          rw [this]; positivity) (inT'_D ha hd) (inT'_G ha hd) (inT'_B ha hd) hq
  · intro hq
    have hT : InT' a d (uu 0 0 q) (vv 0 0 q) := (mem_LT_LC _ _ _ _ _ _ q).1 hq
    rcases cover' ha hd _ _ hT with h | h | h | h | h
    · exact Or.inr (Or.inl (Or.inr ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩))
    · exact Or.inl ((mem_LT_LC _ _ _ _ _ _ q).2 h)
    · exact Or.inr (Or.inl (Or.inl ((mem_LT_LC _ _ _ _ _ _ q).2 h)))
    · exact Or.inr (Or.inr (Or.inl ((mem_LT_LC _ _ _ _ _ _ q).2 h)))
    · exact Or.inr (Or.inr (Or.inr ((mem_LT_LC _ _ _ _ _ _ q).2 h)))

end vertices

/-- **Zhang's Proposition 6(2) (UNAUDITED).**  `a < b = a+d`, `c² = a²+ab+b²`, `gcd(a,b)=1`.
The triangle `A C B` with lattice vertices `A = (-a²d, 0)`, `C = (aW+abd, 0)`,
`B = (a³-b³, b²(2a+b))` (`W = c²`; sides `AB = bc²`, `AC = (a+2b)ab`, `BC = (b+2a)b²`) is tiled by
`(b+2a)(a+2b)b²` copies of the tile `Rmodel`. -/
theorem zhang_prop6_2 (a d c : ℕ) (ha : 0 < a) (hd : 0 < d)
    (hcab : c * c = a * a + (a + d) * (a + d) + a * (a + d)) (hcop : Nat.Coprime a (a + d)) :
    Dis (Rmodel (Nat.cast_pos.mpr ha : (0:ℝ) < a) (Nat.cast_pos.mpr (by omega) : (0:ℝ) < ((a + d : ℕ) : ℝ)))
      (LT (qAu (a : ℝ) d) 0 (pFu (a : ℝ) d) 0 (qBu (a : ℝ) d) (qBv (a : ℝ) d))
      (((a + d) + 2 * a) * (a + 2 * (a + d)) * ((a + d) * (a + d))) := by
  have hc : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · subst h; nlinarith [Nat.mul_pos ha ha]
    · exact h
  have hT := zhang_prop3 a (a + d) c (a * (c * c)) d ha (by omega) hc hcab hcop
    (by nlinarith [Nat.mul_pos hc hc, Nat.mul_pos ha (Nat.mul_pos hc hc)]) hd 0 0
  have hrW : ((c : ℝ)) * c = pW (a : ℝ) d := by
    have : ((c * c : ℕ) : ℝ) = ((a * a + (a + d) * (a + d) + a * (a + d) : ℕ) : ℝ) := by rw [hcab]
    push_cast at this
    rw [this]; simp only [pW]; ring
  have hrW' : ((c * c : ℕ) : ℝ) = pW (a : ℝ) d := by push_cast; exact hrW
  have hR := prop6b_real (a := (a : ℝ)) (d := (d : ℝ)) (Nat.cast_pos.mpr ha) (Nat.cast_pos.mpr hd)
    (b := ((a + d : ℕ) : ℝ)) (Nat.cast_pos.mpr (by omega)) (by push_cast; ring) (c : ℝ)
    (Nat.cast_pos.mpr hc) hrW ((a + d) * c) (a * c) (a * d)
    (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)
    (nT := d * (2 * (a * (c * c)) + d * (a * (a + d))))
    (hT.congr (by
      ext q
      simp only [pX, pY, ← hrW']
      push_cast
      ring_nf) rfl)
  refine hR.congr rfl ?_
  have h' : ((c * c : ℕ) : ℤ) = (a : ℤ) * a + ((a : ℤ) + d) * ((a : ℤ) + d) + (a : ℤ) * ((a : ℤ) + d) := by
    exact_mod_cast hcab
  zify
  push_cast at h' ⊢
  linear_combination (2 * (a : ℤ) * d + (a : ℤ) ^ 2 + 2 * ((a : ℤ) + d) ^ 2) * h'

/-- Witness `(a,b,c) = (3,5,7)`, `d = 2`: `3575` tiles (Zhang's Corollary 1).  Area check
`(b+2a)(a+2b)b² = 11·13·25 = 3575 = 2·1225 + 441 + 36 + 648` (pieces `ABD, DGB` scale `bc = 35`,
`EGD` scale `ac = 21`, `AEF` scale `a(b-a) = 6`, trapezoid `Tz 0 0 147 30` with `648` tiles). -/
theorem zhang_prop6_2_357 : ∃ n : ℕ, n = 3575 ∧ ∃ C : CongruentRegionDissection n,
    C.region = LT (qAu (3 : ℝ) (2 : ℕ)) 0 (pFu (3 : ℝ) (2 : ℕ)) 0 (qBu (3 : ℝ) (2 : ℕ))
      (qBv (3 : ℝ) (2 : ℕ)) := by
  have h := zhang_prop6_2 3 2 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, hr, -⟩ := h
  exact ⟨_, by norm_num, C, by simpa using hr⟩

end Erdos634.ZhangProp6b
