import Erdos634.Draft.ZhangLat

/-!
# Zhang Proposition 6, part (1) (arXiv 2512.22696v4, Fig. 7 top): the `(2α, 2β, α+β)` triangle

Reading of Fig. 7 (top), reconstructed from the printed side labels and verified numerically for
`(a,b,c) = (3,5,7)` (piece areas `2401, 2401, 1521, 36, 648` tiles, total `7007 = (b+2a)(a+2b)c²`).
Notation: `d = b - a > 0`, `W = c² = a²+ab+b²`.  Lattice coordinates `u e₁ + v e₂`:

* `E=(0,0)`, `F=(X+Y,0)`, `G=(X,Y)`, `D=(0,Y)` with `X = a c²`, `Y = ab(b-a)`:
  `EFGD` is the ideal trapezoid `Tz 0 0 X Y` (short side `x = a c²`, legs `y = ab(b-a)`).
* `A = (0, -a²(a+2b))` (on the line `ED`), `B = D + c²(-b, b)`, `C = (ab(a+2b), 0)` (on the line `EF`).
* Four triangles similar to the tile: `ABD` (scale `c²`, 120° at `D`), `BDG` (scale `c²`), `AEC`
  (scale `a(a+2b)`, 120° at `E`), `CFG` (scale `a(b-a)`, 120° at `F`); `G` lies on `BC`.

The big triangle `ABC` has sides `AC = (a+2b)ac`, `BC = (b+2a)bc`, `AB = c³`.  Reals `a d` here;
the natural-number statement is in `Erdos634.ZhangProp6`.  Credit Zhang (arXiv 2512.22696),
Beeson, Beeson-Rosu, Laczkovich.  UNAUDITED.
-/

namespace Erdos634.ZhangProp6

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.GlueCut Erdos634.SssCongruent Erdos634.ZhangL1 Erdos634.ZhangPara
  Erdos634.ZhangProp3 Erdos634.ZhangThm4 Erdos634.ZhangSporadic Erdos634.ZhangLat

section coords
variable (a d : ℝ)

noncomputable def pW : ℝ := a ^ 2 + a * (a + d) + (a + d) ^ 2
noncomputable def pY : ℝ := a * (a + d) * d
noncomputable def pX : ℝ := a * pW a d
noncomputable def pAv : ℝ := -(a ^ 2 * (a + 2 * (a + d)))
noncomputable def pBu : ℝ := -((a + d) * pW a d)
noncomputable def pBv : ℝ := pY a d + (a + d) * pW a d
noncomputable def pCu : ℝ := a * (a + d) * (a + 2 * (a + d))
noncomputable def pFu : ℝ := pX a d + pY a d

/-- the three half-plane conditions of the big triangle `ABC` (`A,C,B` counterclockwise). -/
def InT (u v : ℝ) : Prop :=
  0 ≤ ld u v (pCu a d) 0 (pBu a d) (pBv a d) ∧ 0 ≤ ld 0 (pAv a d) u v (pBu a d) (pBv a d) ∧
    0 ≤ ld 0 (pAv a d) (pCu a d) 0 u v

end coords

theorem LT_sub {tu0 tv0 tu1 tv1 tu2 tv2 u0 v0 u1 v1 u2 v2 : ℝ} (hΔ : 0 < ld u0 v0 u1 v1 u2 v2)
    (h0 : 0 ≤ ld u0 v0 tu1 tv1 tu2 tv2 ∧ 0 ≤ ld tu0 tv0 u0 v0 tu2 tv2 ∧
      0 ≤ ld tu0 tv0 tu1 tv1 u0 v0)
    (h1 : 0 ≤ ld u1 v1 tu1 tv1 tu2 tv2 ∧ 0 ≤ ld tu0 tv0 u1 v1 tu2 tv2 ∧
      0 ≤ ld tu0 tv0 tu1 tv1 u1 v1)
    (h2 : 0 ≤ ld u2 v2 tu1 tv1 tu2 tv2 ∧ 0 ≤ ld tu0 tv0 u2 v2 tu2 tv2 ∧
      0 ≤ ld tu0 tv0 tu1 tv1 u2 v2) :
    LT u0 v0 u1 v1 u2 v2 ⊆ LT tu0 tv0 tu1 tv1 tu2 tv2 := by
  intro q hq
  rw [mem_LT] at hq ⊢
  obtain ⟨c0, c1, c2⟩ := hq
  set u := uu 0 0 q
  set v := vv 0 0 q
  refine ⟨?_, ?_, ?_⟩
  · refine nn_of_mul hΔ ?_
    have key : ld u v tu1 tv1 tu2 tv2 * ld u0 v0 u1 v1 u2 v2 =
        ld u v u1 v1 u2 v2 * ld u0 v0 tu1 tv1 tu2 tv2 + ld u0 v0 u v u2 v2 * ld u1 v1 tu1 tv1 tu2 tv2 +
        ld u0 v0 u1 v1 u v * ld u2 v2 tu1 tv1 tu2 tv2 := by simp only [ld]; ring
    rw [mul_comm, key]
    exact add_nonneg (add_nonneg (mul_nonneg c0 h0.1) (mul_nonneg c1 h1.1)) (mul_nonneg c2 h2.1)
  · refine nn_of_mul hΔ ?_
    have key : ld tu0 tv0 u v tu2 tv2 * ld u0 v0 u1 v1 u2 v2 =
        ld u v u1 v1 u2 v2 * ld tu0 tv0 u0 v0 tu2 tv2 + ld u0 v0 u v u2 v2 * ld tu0 tv0 u1 v1 tu2 tv2 +
        ld u0 v0 u1 v1 u v * ld tu0 tv0 u2 v2 tu2 tv2 := by simp only [ld]; ring
    rw [mul_comm, key]
    exact add_nonneg (add_nonneg (mul_nonneg c0 h0.2.1) (mul_nonneg c1 h1.2.1)) (mul_nonneg c2 h2.2.1)
  · refine nn_of_mul hΔ ?_
    have key : ld tu0 tv0 tu1 tv1 u v * ld u0 v0 u1 v1 u2 v2 =
        ld u v u1 v1 u2 v2 * ld tu0 tv0 tu1 tv1 u0 v0 + ld u0 v0 u v u2 v2 * ld tu0 tv0 tu1 tv1 u1 v1 +
        ld u0 v0 u1 v1 u v * ld tu0 tv0 tu1 tv1 u2 v2 := by simp only [ld]; ring
    rw [mul_comm, key]
    exact add_nonneg (add_nonneg (mul_nonneg c0 h0.2.2) (mul_nonneg c1 h1.2.2)) (mul_nonneg c2 h2.2.2)

section vertices
variable {a d : ℝ}

theorem inT_A (ha : 0 < a) (hd : 0 < d) : InT a d (0) (pAv a d) := by
  refine ⟨?_, ?_, ?_⟩
  · have e : ld (0) (pAv a d) (pCu a d) 0 (pBu a d) (pBv a d) = a*(a+d)*(3*a+d)*(3*a+2*d)*(3*a^2+3*a*d+d^2) := by
      simp only [ld, pW, pY, pX, pAv, pBu, pBv, pCu, pFu]; ring
    rw [e]; positivity
  · apply le_of_eq; symm; simp only [ld, pW, pY, pX, pAv, pBu, pBv, pCu, pFu]; ring
  · apply le_of_eq; symm; simp only [ld, pW, pY, pX, pAv, pBu, pBv, pCu, pFu]; ring

theorem inT_B (ha : 0 < a) (hd : 0 < d) : InT a d (pBu a d) (pBv a d) := by
  refine ⟨?_, ?_, ?_⟩
  · apply le_of_eq; symm; simp only [ld, pW, pY, pX, pAv, pBu, pBv, pCu, pFu]; ring
  · apply le_of_eq; symm; simp only [ld, pW, pY, pX, pAv, pBu, pBv, pCu, pFu]; ring
  · have e : ld 0 (pAv a d) (pCu a d) 0 (pBu a d) (pBv a d) = a*(a+d)*(3*a+d)*(3*a+2*d)*(3*a^2+3*a*d+d^2) := by
      simp only [ld, pW, pY, pX, pAv, pBu, pBv, pCu, pFu]; ring
    rw [e]; positivity

theorem inT_C (ha : 0 < a) (hd : 0 < d) : InT a d (pCu a d) (0) := by
  refine ⟨?_, ?_, ?_⟩
  · apply le_of_eq; symm; simp only [ld, pW, pY, pX, pAv, pBu, pBv, pCu, pFu]; ring
  · have e : ld 0 (pAv a d) (pCu a d) (0) (pBu a d) (pBv a d) = a*(a+d)*(3*a+d)*(3*a+2*d)*(3*a^2+3*a*d+d^2) := by
      simp only [ld, pW, pY, pX, pAv, pBu, pBv, pCu, pFu]; ring
    rw [e]; positivity
  · apply le_of_eq; symm; simp only [ld, pW, pY, pX, pAv, pBu, pBv, pCu, pFu]; ring

theorem inT_D (ha : 0 < a) (hd : 0 < d) : InT a d (0) (pY a d) := by
  refine ⟨?_, ?_, ?_⟩
  · have e : ld (0) (pY a d) (pCu a d) 0 (pBu a d) (pBv a d) = a*(a+d)^2*(3*a+d)*(3*a^2+3*a*d+d^2) := by
      simp only [ld, pW, pY, pX, pAv, pBu, pBv, pCu, pFu]; ring
    rw [e]; positivity
  · have e : ld 0 (pAv a d) (0) (pY a d) (pBu a d) (pBv a d) = a*(a+d)*(3*a^2+3*a*d+d^2)^2 := by
      simp only [ld, pW, pY, pX, pAv, pBu, pBv, pCu, pFu]; ring
    rw [e]; positivity
  · have e : ld 0 (pAv a d) (pCu a d) 0 (0) (pY a d) = a^2*(a+d)*(3*a+2*d)*(3*a^2+3*a*d+d^2) := by
      simp only [ld, pW, pY, pX, pAv, pBu, pBv, pCu, pFu]; ring
    rw [e]; positivity

theorem inT_E (ha : 0 < a) (hd : 0 < d) : InT a d (0) (0) := by
  refine ⟨?_, ?_, ?_⟩
  · have e : ld (0) (0) (pCu a d) 0 (pBu a d) (pBv a d) = a*(a+d)^3*(3*a+d)*(3*a+2*d) := by
      simp only [ld, pW, pY, pX, pAv, pBu, pBv, pCu, pFu]; ring
    rw [e]; positivity
  · have e : ld 0 (pAv a d) (0) (0) (pBu a d) (pBv a d) = a^2*(a+d)*(3*a+2*d)*(3*a^2+3*a*d+d^2) := by
      simp only [ld, pW, pY, pX, pAv, pBu, pBv, pCu, pFu]; ring
    rw [e]; positivity
  · have e : ld 0 (pAv a d) (pCu a d) 0 (0) (0) = a^3*(a+d)*(3*a+2*d)^2 := by
      simp only [ld, pW, pY, pX, pAv, pBu, pBv, pCu, pFu]; ring
    rw [e]; positivity

theorem inT_F (ha : 0 < a) (hd : 0 < d) : InT a d (pFu a d) (0) := by
  refine ⟨?_, ?_, ?_⟩
  · have e : ld (pFu a d) (0) (pCu a d) 0 (pBu a d) (pBv a d) = a^2*d*(a+d)^2*(3*a+d) := by
      simp only [ld, pW, pY, pX, pAv, pBu, pBv, pCu, pFu]; ring
    rw [e]; positivity
  · have e : ld 0 (pAv a d) (pFu a d) (0) (pBu a d) (pBv a d) = a*(3*a^2+3*a*d+d^2)*(9*a^3+16*a^2*d+10*a*d^2+2*d^3) := by
      simp only [ld, pW, pY, pX, pAv, pBu, pBv, pCu, pFu]; ring
    rw [e]; positivity
  · have e : ld 0 (pAv a d) (pCu a d) 0 (pFu a d) (0) = a^4*d*(3*a+2*d) := by
      simp only [ld, pW, pY, pX, pAv, pBu, pBv, pCu, pFu]; ring
    rw [e]; positivity

theorem inT_G (ha : 0 < a) (hd : 0 < d) : InT a d (pX a d) (pY a d) := by
  refine ⟨?_, ?_, ?_⟩
  · apply le_of_eq; symm; simp only [ld, pW, pY, pX, pAv, pBu, pBv, pCu, pFu]; ring
  · have e : ld 0 (pAv a d) (pX a d) (pY a d) (pBu a d) (pBv a d) = a*(3*a+2*d)*(3*a^2+3*a*d+d^2)^2 := by
      simp only [ld, pW, pY, pX, pAv, pBu, pBv, pCu, pFu]; ring
    rw [e]; positivity
  · have e : ld 0 (pAv a d) (pCu a d) 0 (pX a d) (pY a d) = a^2*d*(3*a+2*d)*(3*a^2+3*a*d+d^2) := by
      simp only [ld, pW, pY, pX, pAv, pBu, pBv, pCu, pFu]; ring
    rw [e]; positivity

/-- membership in the triangle with lattice vertices, at lattice coordinates `(u,v)`. -/
def LC (u0 v0 u1 v1 u2 v2 u v : ℝ) : Prop :=
  0 ≤ ld u v u1 v1 u2 v2 ∧ 0 ≤ ld u0 v0 u v u2 v2 ∧ 0 ≤ ld u0 v0 u1 v1 u v

theorem mem_LT_LC (u0 v0 u1 v1 u2 v2 : ℝ) (q : Plane) :
    q ∈ LT u0 v0 u1 v1 u2 v2 ↔ LC u0 v0 u1 v1 u2 v2 (uu 0 0 q) (vv 0 0 q) := mem_LT u0 v0 u1 v1 u2 v2 q

theorem pW_pos (ha : 0 < a) (hd : 0 < d) : 0 < pW a d := by unfold pW; positivity
theorem pY_pos (ha : 0 < a) (hd : 0 < d) : 0 < pY a d := by unfold pY; positivity
theorem pX_pos (ha : 0 < a) (hd : 0 < d) : 0 < pX a d := by
  unfold pX; have := pW_pos ha hd; positivity
theorem pCu_pos (ha : 0 < a) (hd : 0 < d) : 0 < pCu a d := by unfold pCu; positivity
theorem pAv_neg (ha : 0 < a) (hd : 0 < d) : pAv a d < 0 := by
  unfold pAv
  have : 0 < a ^ 2 * (a + 2 * (a + d)) := by positivity
  linarith
theorem bW_pos (ha : 0 < a) (hd : 0 < d) : 0 < (a + d) * pW a d := by
  have := pW_pos ha hd; positivity
theorem CF_pos (ha : 0 < a) (hd : 0 < d) : 0 < pCu a d - pFu a d := by
  have : pCu a d - pFu a d = a ^ 2 * d := by
    simp only [pCu, pFu, pX, pY, pW]; ring
  rw [this]; positivity

theorem CFG_facts (ha : 0 < a) (hd : 0 < d) {u v : ℝ}
    (h : LC (pFu a d) 0 (pCu a d) 0 (pX a d) (pY a d) u v) :
    0 ≤ v ∧ v ≤ pY a d ∧ pX a d + pY a d ≤ u + v := by
  obtain ⟨c1, c2, c3⟩ := h
  have hY := pY_pos ha hd
  have hCF := CF_pos ha hd
  have hv : 0 ≤ v := by
    refine nn_of_mul hCF ?_
    simp only [ld] at c3; linarith
  refine ⟨hv, ?_, ?_⟩
  · have key : (pCu a d - pFu a d) * pY a d * (pY a d - v) =
        pY a d * (ld u v (pCu a d) 0 (pX a d) (pY a d) + ld (pFu a d) 0 u v (pX a d) (pY a d)) := by
      simp only [ld, pFu]; ring
    have h12 : 0 ≤ (pCu a d - pFu a d) * pY a d * (pY a d - v) := by
      rw [key]; exact mul_nonneg hY.le (add_nonneg c1 c2)
    have := nn_of_mul (mul_pos hCF hY) h12
    linarith
  · have key : pY a d * (u + v - (pX a d + pY a d)) = ld (pFu a d) 0 u v (pX a d) (pY a d) := by
      simp only [ld, pFu]; ring
    have := nn_of_mul hY (key ▸ c2)
    linarith

theorem BDG_facts (ha : 0 < a) (hd : 0 < d) {u v : ℝ}
    (h : LC 0 (pY a d) (pX a d) (pY a d) (pBu a d) (pBv a d) u v) :
    pY a d ≤ v ∧ pY a d ≤ u + v := by
  obtain ⟨c1, c2, c3⟩ := h
  have hX := pX_pos ha hd
  have hbW := bW_pos ha hd
  constructor
  · have key : pX a d * (v - pY a d) = ld 0 (pY a d) (pX a d) (pY a d) u v := by
      simp only [ld]; ring
    have := nn_of_mul hX (key ▸ c3)
    linarith
  · have key : (a + d) * pW a d * (u + v - pY a d) = ld 0 (pY a d) u v (pBu a d) (pBv a d) := by
      simp only [ld, pBu, pBv]; ring
    have := nn_of_mul hbW (key ▸ c2)
    linarith

theorem ABD_facts (ha : 0 < a) (hd : 0 < d) {u v : ℝ}
    (h : LC 0 (pY a d) (pBu a d) (pBv a d) 0 (pAv a d) u v) :
    u ≤ 0 ∧ u + v ≤ pY a d := by
  obtain ⟨c1, c2, c3⟩ := h
  have hbW := bW_pos ha hd
  have hY := pY_pos ha hd
  have hA := pAv_neg ha hd
  constructor
  · have key : (pY a d - pAv a d) * (-u) = ld 0 (pY a d) u v 0 (pAv a d) := by
      simp only [ld]; ring
    have := nn_of_mul (by linarith : 0 < pY a d - pAv a d) (key ▸ c2)
    linarith
  · have key : (a + d) * pW a d * (pY a d - (u + v)) = ld 0 (pY a d) (pBu a d) (pBv a d) u v := by
      simp only [ld, pBu, pBv]; ring
    have := nn_of_mul hbW (key ▸ c3)
    linarith

theorem AEC_facts (ha : 0 < a) (hd : 0 < d) {u v : ℝ}
    (h : LC 0 0 0 (pAv a d) (pCu a d) 0 u v) : 0 ≤ u ∧ v ≤ 0 := by
  obtain ⟨c1, c2, c3⟩ := h
  have hA := pAv_neg ha hd
  have hC := pCu_pos ha hd
  constructor
  · have key : -pAv a d * u = ld 0 0 0 (pAv a d) u v := by simp only [ld]; ring
    have := nn_of_mul (by linarith : 0 < -pAv a d) (key ▸ c3)
    linarith
  · have key : pCu a d * (-v) = ld 0 0 u v (pCu a d) 0 := by simp only [ld]; ring
    have := nn_of_mul hC (key ▸ c2)
    linarith

theorem cover_lat (ha : 0 < a) (hd : 0 < d) (u v : ℝ) (hT : InT a d u v) :
    (0 ≤ u ∧ 0 ≤ v ∧ v ≤ pY a d ∧ u + v ≤ pX a d + pY a d) ∨
    LC (pFu a d) 0 (pCu a d) 0 (pX a d) (pY a d) u v ∨
    LC 0 (pY a d) (pX a d) (pY a d) (pBu a d) (pBv a d) u v ∨
    LC 0 (pY a d) (pBu a d) (pBv a d) 0 (pAv a d) u v ∨
    LC 0 0 0 (pAv a d) (pCu a d) 0 u v := by
  obtain ⟨c1, c2, c3⟩ := hT
  have hY := pY_pos ha hd
  have hX := pX_pos ha hd
  have hC := pCu_pos ha hd
  have hA := pAv_neg ha hd
  have hbW := bW_pos ha hd
  have hCF := CF_pos ha hd
  by_cases h1 : 0 ≤ u ∧ v ≤ 0
  · right; right; right; right
    obtain ⟨hu, hv⟩ := h1
    refine ⟨?_, ?_, ?_⟩
    · simp only [ld] at c3 ⊢; linarith
    · simp only [ld]; nlinarith [mul_nonneg hC.le (neg_nonneg.mpr hv)]
    · simp only [ld]; nlinarith [mul_nonneg hu (neg_nonneg.mpr hA.le)]
  by_cases h2 : u ≤ 0 ∧ u + v ≤ pY a d
  · right; right; right; left
    obtain ⟨hu, huv⟩ := h2
    refine ⟨?_, ?_, ?_⟩
    · simp only [ld] at c2 ⊢; linarith
    · simp only [ld]; nlinarith [mul_nonneg (neg_nonneg.mpr hu) (by linarith : 0 ≤ pY a d - pAv a d)]
    · simp only [ld, pBu, pBv]
      nlinarith [mul_nonneg hbW.le (by linarith : 0 ≤ pY a d - (u + v))]
  by_cases h3 : pY a d ≤ v
  · right; right; left
    have huv : pY a d ≤ u + v := by
      by_contra hlt
      push_neg at hlt
      exact h2 ⟨by linarith, hlt.le⟩
    refine ⟨?_, ?_, ?_⟩
    · have key : (a + d) * (3 * a + d) * ld u v (pX a d) (pY a d) (pBu a d) (pBv a d) =
          pW a d * ld u v (pCu a d) 0 (pBu a d) (pBv a d) := by
        simp only [ld, pX, pY, pBu, pBv, pCu, pW]; ring
      have := nn_of_mul (by positivity : 0 < (a + d) * (3 * a + d)) (by rw [key]; exact mul_nonneg (pW_pos ha hd).le c1)
      exact this
    · simp only [ld, pBu, pBv]
      nlinarith [mul_nonneg hbW.le (by linarith : 0 ≤ u + v - pY a d)]
    · simp only [ld]; nlinarith [mul_nonneg hX.le (by linarith : 0 ≤ v - pY a d)]
  push_neg at h3
  have hv0 : 0 ≤ v := by
    by_contra hv
    push_neg at hv
    have hu : u < 0 := by
      by_contra hu; push_neg at hu; exact h1 ⟨hu, hv.le⟩
    exact h2 ⟨hu.le, by linarith⟩
  have hu0 : 0 ≤ u := by
    by_contra hu
    push_neg at hu
    have : pY a d < u + v := by
      by_contra hn; push_neg at hn; exact h2 ⟨hu.le, hn⟩
    linarith
  by_cases h4 : u + v ≤ pX a d + pY a d
  · left; exact ⟨hu0, hv0, h3.le, h4⟩
  · push_neg at h4
    right; left
    refine ⟨?_, ?_, ?_⟩
    · have key : (a + d) * (3 * a + d) * ld u v (pCu a d) 0 (pX a d) (pY a d) =
          a * d * ld u v (pCu a d) 0 (pBu a d) (pBv a d) := by
        simp only [ld, pX, pY, pBu, pBv, pCu, pW]; ring
      exact nn_of_mul (by positivity : 0 < (a + d) * (3 * a + d))
        (by rw [key]; exact mul_nonneg (by positivity) c1)
    · simp only [ld, pFu]
      nlinarith [mul_nonneg hY.le (by linarith : 0 ≤ u + v - (pX a d + pY a d))]
    · simp only [ld]; nlinarith [mul_nonneg hCF.le hv0]

theorem tz_sub (ha : 0 < a) (hd : 0 < d) :
    Tz 0 0 (pX a d) (pY a d) ⊆ LT 0 (pAv a d) (pCu a d) 0 (pBu a d) (pBv a d) := by
  intro q hq
  obtain ⟨hu, hv, hvy, huv⟩ := hq
  rw [mem_LT]
  set u := uu 0 0 q
  set v := vv 0 0 q
  have g4 : 0 ≤ pX a d + pY a d - (u + v) := by
    have := huv; simp only [pY] at this ⊢; linarith
  have g3 : 0 ≤ pY a d - v := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have hp : 0 ≤ (a + d) ^ 2 * (3 * a + d) := by positivity
    have hrp : 0 ≤ (a + d) * (3 * a + d) * a := by positivity
    simp only [ld, pX, pY, pAv, pBu, pBv, pCu, pW] at g4 g3 ⊢
    nlinarith [mul_nonneg hp g4, mul_nonneg hrp g3]
  · have h1 : 0 ≤ (2 * a + d) * (3 * a ^ 2 + 3 * a * d + d ^ 2) := by positivity
    have h2 : 0 ≤ (a + d) * (3 * a ^ 2 + 3 * a * d + d ^ 2) := by positivity
    have h3 : 0 ≤ a ^ 2 * (a + d) * (3 * a + 2 * d) * (3 * a ^ 2 + 3 * a * d + d ^ 2) := by positivity
    simp only [ld, pX, pY, pAv, pBu, pBv, pCu, pW]
    nlinarith [mul_nonneg h1 hu, mul_nonneg h2 hv]
  · have hp : 0 ≤ a ^ 2 * (3 * a + 2 * d) := by positivity
    have hr : 0 ≤ a ^ 2 * (3 * a + 2 * d) + a * (a + d) * (3 * a + 2 * d) := by positivity
    have h3 : 0 ≤ a ^ 4 * d * (3 * a + 2 * d) := by positivity
    simp only [ld, pX, pY, pAv, pBu, pBv, pCu, pW] at g4 g3 ⊢
    nlinarith [mul_nonneg hp g4, mul_nonneg hr hv]

/-- **Zhang Prop. 6(1), real form.**  `k1 = c²`, `k2 = a(a+2b)`, `k3 = a(b-a)` as naturals and
the trapezoid `Tz 0 0 X Y` (`X = a c²`, `Y = ab(b-a)`) tiled by `nT` tiles; then the triangle
`A C B` is tiled by `nT + k3² + 2 k1² + k2²` tiles. -/
theorem prop6_real (ha : 0 < a) (hd : 0 < d) {b : ℝ} (hb : 0 < b) (hbd : b = a + d) (k1 k2 k3 : ℕ)
    (hk1 : (k1 : ℝ) = pW a d) (hk2 : (k2 : ℝ) = a * (a + 2 * (a + d))) (hk3 : (k3 : ℝ) = a * d)
    {nT : ℕ} (hTz : Dis (Rmodel ha hb) (Tz 0 0 (pX a d) (pY a d)) nT) :
    Dis (Rmodel ha hb) (LT 0 (pAv a d) (pCu a d) 0 (pBu a d) (pBv a d))
      (nT + k3 * k3 + k1 * k1 + k1 * k1 + k2 * k2) := by
  subst hbd
  have hY := pY_pos ha hd
  have hX := pX_pos ha hd
  have hC := pCu_pos ha hd
  have hA := pAv_neg ha hd
  have hbW := bW_pos ha hd
  have hCF := CF_pos ha hd
  have hW := pW_pos ha hd
  have hk1p : 0 < k1 := Nat.cast_pos.mp (by rw [hk1]; exact hW)
  have hk2p : 0 < k2 := Nat.cast_pos.mp (by rw [hk2]; positivity)
  have hk3p : 0 < k3 := Nat.cast_pos.mp (by rw [hk3]; positivity)
  -- the four similar triangles
  have hCFG : Dis (Rmodel ha hb) (LT (pFu a d) 0 (pCu a d) 0 (pX a d) (pY a d)) (k3 * k3) :=
    Dis_LT_tile1 ha hb k3 hk3p (pFu a d) 0 a 0 (-(a + d)) (a + d)
      (by have : ld 0 0 a 0 (-(a + d)) (a + d) = a * (a + d) := by simp only [ld]; ring
          rw [this]; positivity)
      (by ring) (by ring) (by ring) _ _ _ _
      (by rw [hk3]; simp only [pCu, pFu, pX, pY, pW]; ring) (by ring)
      (by rw [hk3]; simp only [pFu, pX, pY, pW]; ring) (by rw [hk3]; simp only [pY]; ring)
  have hBDG : Dis (Rmodel ha hb) (LT 0 (pY a d) (pX a d) (pY a d) (pBu a d) (pBv a d)) (k1 * k1) :=
    Dis_LT_tile1 ha hb k1 hk1p 0 (pY a d) a 0 (-(a + d)) (a + d)
      (by have : ld 0 0 a 0 (-(a + d)) (a + d) = a * (a + d) := by simp only [ld]; ring
          rw [this]; positivity)
      (by ring) (by ring) (by ring) _ _ _ _
      (by rw [hk1]; simp only [pX]; ring) (by ring)
      (by rw [hk1]; simp only [pBu]; ring) (by rw [hk1]; simp only [pBv]; ring)
  have hABD : Dis (Rmodel ha hb) (LT 0 (pY a d) (pBu a d) (pBv a d) 0 (pAv a d)) (k1 * k1) :=
    Dis_LT_tile2 ha hb k1 hk1p 0 (pY a d) (-(a + d)) (a + d) 0 (-a)
      (by have : ld 0 0 (-(a + d)) (a + d) 0 (-a) = a * (a + d) := by simp only [ld]; ring
          rw [this]; positivity)
      (by ring) (by ring) (by ring) _ _ _ _
      (by rw [hk1]; simp only [pBu]; ring) (by rw [hk1]; simp only [pBv]; ring)
      (by ring) (by rw [hk1]; simp only [pAv, pY, pW]; ring)
  have hAEC : Dis (Rmodel ha hb) (LT 0 0 0 (pAv a d) (pCu a d) 0) (k2 * k2) :=
    Dis_LT_tile1 ha hb k2 hk2p 0 0 0 (-a) (a + d) 0
      (by have : ld 0 0 0 (-a) (a + d) 0 = a * (a + d) := by simp only [ld]; ring
          rw [this]; positivity)
      (by ring) (by ring) (by ring) _ _ _ _
      (by ring) (by rw [hk2]; simp only [pAv]; ring)
      (by rw [hk2]; simp only [pCu]; ring) (by ring)
  -- gluing
  have hQ1 := Dis.glue_lat hTz hCFG 1 1 (pX a d + pY a d) (by norm_num)
    (fun q hq => by have := hq.2.2.2; linarith)
    (fun q hq => by
      obtain ⟨-, h2, -⟩ := (mem_LT_LC _ _ _ _ _ _ q).1 hq
      have := (CFG_facts ha hd ((mem_LT_LC _ _ _ _ _ _ q).1 hq)).2.2
      linarith)
  have hQ2 := Dis.glue_lat hQ1 hBDG 0 1 (pY a d) (by norm_num)
    (fun q hq => by
      rcases hq with hq | hq
      · have := hq.2.2.1; linarith
      · have := (CFG_facts ha hd ((mem_LT_LC _ _ _ _ _ _ q).1 hq)).2.1; linarith)
    (fun q hq => by
      have := (BDG_facts ha hd ((mem_LT_LC _ _ _ _ _ _ q).1 hq)).1; linarith)
  have hQ3 := Dis.glue_quad_lat hABD hQ2 1 0 0 1 1 (pY a d) (by norm_num) (by norm_num)
    (fun q hq => by
      have := (ABD_facts ha hd ((mem_LT_LC _ _ _ _ _ _ q).1 hq)).1; linarith)
    (fun q hq => by
      have := (ABD_facts ha hd ((mem_LT_LC _ _ _ _ _ _ q).1 hq)).2; linarith)
    (fun q hq => by
      rcases hq with (hq | hq) | hq
      · left; have := hq.1; linarith
      · right
        have h1 := (CFG_facts ha hd ((mem_LT_LC _ _ _ _ _ _ q).1 hq)).2.2
        have h2 := (CFG_facts ha hd ((mem_LT_LC _ _ _ _ _ _ q).1 hq)).1
        simp only [pX, pY] at h1 hY ⊢; nlinarith
      · right
        have := (BDG_facts ha hd ((mem_LT_LC _ _ _ _ _ _ q).1 hq)).2; linarith)
  have hQ4 := Dis.glue_quad_lat hAEC hQ3 (-1) 0 0 0 1 0 (by norm_num) (by norm_num)
    (fun q hq => by
      have := (AEC_facts ha hd ((mem_LT_LC _ _ _ _ _ _ q).1 hq)).1; linarith)
    (fun q hq => by
      have := (AEC_facts ha hd ((mem_LT_LC _ _ _ _ _ _ q).1 hq)).2; linarith)
    (fun q hq => by
      rcases hq with hq | ((hq | hq) | hq)
      · left; have := (ABD_facts ha hd ((mem_LT_LC _ _ _ _ _ _ q).1 hq)).1; linarith
      · right; have := hq.2.1; linarith
      · right; have := (CFG_facts ha hd ((mem_LT_LC _ _ _ _ _ _ q).1 hq)).1; linarith
      · right; have := (BDG_facts ha hd ((mem_LT_LC _ _ _ _ _ _ q).1 hq)).1; linarith)
  refine (Dis.congr hQ4 ?_ (by ring))
  -- set equality
  ext q
  constructor
  · intro hq
    rcases hq with hq | hq | ((hq | hq) | hq)
    · exact LT_sub (by simp only [ld]; nlinarith [mul_pos hC (neg_pos.2 hA)]) (inT_E ha hd) (inT_A ha hd)
        (inT_C ha hd) hq
    · exact LT_sub (by simp only [ld, pBu, pBv]; nlinarith [mul_pos hbW (sub_pos.2 (hA.trans hY))])
        (inT_D ha hd) (inT_B ha hd) (inT_A ha hd) hq
    · exact tz_sub ha hd hq
    · exact LT_sub (by simp only [ld]; nlinarith [mul_pos hCF hY]) (inT_F ha hd) (inT_C ha hd)
        (inT_G ha hd) hq
    · exact LT_sub (by simp only [ld, pBv]; nlinarith [mul_pos hX hbW]) (inT_D ha hd) (inT_G ha hd)
        (inT_B ha hd) hq
  · intro hq
    have hT : InT a d (uu 0 0 q) (vv 0 0 q) := (mem_LT_LC _ _ _ _ _ _ q).1 hq
    rcases cover_lat ha hd _ _ hT with h | h | h | h | h
    · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩)))
    · exact Or.inr (Or.inr (Or.inl (Or.inr ((mem_LT_LC _ _ _ _ _ _ q).2 h))))
    · exact Or.inr (Or.inr (Or.inr ((mem_LT_LC _ _ _ _ _ _ q).2 h)))
    · exact Or.inr (Or.inl ((mem_LT_LC _ _ _ _ _ _ q).2 h))
    · exact Or.inl ((mem_LT_LC _ _ _ _ _ _ q).2 h)

end vertices

/-- **Zhang's Proposition 6(1) (UNAUDITED).**  `a < b`, `c² = a²+ab+b²` naturals, `gcd(a,b)=1`.
The triangle `A C B` (lattice vertices `A=(0,-a²(a+2b))`, `C=(ab(a+2b),0)`,
`B=(-b c², ab(b-a)+b c²)`; angles `2β, 2α, α+β`... sides `AC=(a+2b)ac`, `BC=(b+2a)bc`, `AB=c³`)
is tiled by `(b+2a)(a+2b)c²` copies of the tile `Rmodel` (sides `a,b,c`, angle `2π/3` between
`a` and `b`).  The case `a > b` is the mirror (swap `a,b`; not stated here). -/
theorem zhang_prop6_1 (a d c : ℕ) (ha : 0 < a) (hd : 0 < d)
    (hcab : c * c = a * a + (a + d) * (a + d) + a * (a + d)) (hcop : Nat.Coprime a (a + d)) :
    Dis (Rmodel (Nat.cast_pos.mpr ha : (0:ℝ) < a) (Nat.cast_pos.mpr (by omega) : (0:ℝ) < ((a + d : ℕ) : ℝ)))
      (LT 0 (pAv (a : ℝ) d) (pCu (a : ℝ) d) 0 (pBu (a : ℝ) d) (pBv (a : ℝ) d))
      (((a + d) + 2 * a) * (a + 2 * (a + d)) * (c * c)) := by
  have hc : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · subst h; nlinarith [Nat.mul_pos ha ha]
    · exact h
  have hT := zhang_prop3 a (a + d) c (a * (c * c)) d ha (by omega) hc hcab hcop
    (by nlinarith [Nat.mul_pos hc hc, Nat.mul_pos ha (Nat.mul_pos hc hc)]) hd 0 0
  have hrW : ((c * c : ℕ) : ℝ) = pW (a : ℝ) d := by
    have : ((c * c : ℕ) : ℝ) = ((a * a + (a + d) * (a + d) + a * (a + d) : ℕ) : ℝ) := by rw [hcab]
    rw [this]; push_cast; simp only [pW]; ring
  have hR := prop6_real (a := (a : ℝ)) (d := (d : ℝ)) (Nat.cast_pos.mpr ha) (Nat.cast_pos.mpr hd)
    (b := ((a + d : ℕ) : ℝ)) (Nat.cast_pos.mpr (by omega)) (by push_cast; ring) (c * c)
    (a * (a + 2 * (a + d))) (a * d) hrW (by push_cast; ring) (by push_cast; ring)
    (nT := d * (2 * (a * (c * c)) + d * (a * (a + d))))
    (hT.congr (by
      ext q
      simp only [pX, pY, hrW.symm]
      push_cast
      ring_nf) rfl)
  refine hR.congr rfl ?_
  have h' : ((c * c : ℕ) : ℤ) = (a : ℤ) * a + ((a : ℤ) + d) * ((a : ℤ) + d) + (a : ℤ) * ((a : ℤ) + d) := by
    exact_mod_cast hcab
  zify
  push_cast at h' ⊢
  linear_combination (2 * ((c : ℤ) * c) - 3 * (a : ℤ) * a - (a : ℤ) * d) * h'

/-- Witness `(a,b,c) = (3,5,7)`, `d = 2`: 7007 tiles.  Area check
`(b+2a)(a+2b)c² = 11·13·49 = 7007 = 2·2401 + 1521 + 36 + 648` (pieces `ABD, BDG, AEC, CFG`,
trapezoid `Tz 0 0 147 30`).  Hypotheses: `49 = 9+25+15`, `gcd(3,5)=1`. -/
theorem zhang_prop6_1_357 : ∃ n : ℕ, n = 7007 ∧ ∃ C : CongruentRegionDissection n,
    C.region = LT 0 (pAv (3 : ℝ) (2 : ℕ)) (pCu (3 : ℝ) (2 : ℕ)) 0 (pBu (3 : ℝ) (2 : ℕ))
      (pBv (3 : ℝ) (2 : ℕ)) := by
  have h := zhang_prop6_1 3 2 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, hr, -⟩ := h
  exact ⟨_, by norm_num, C, by simpa using hr⟩

end Erdos634.ZhangProp6
