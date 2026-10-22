import Mathlib
import Erdos634.Draft.FDDShapes

/-!
# Beeson, "Tiling a triangle into a prime number of congruent triangles" (arXiv 2607.23453 v1), Sect. 3:
# Lemmas 11, 12, 13, 14, 15, 16 for the tile (alpha, beta, 2 pi/3)

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 2607.23453 v1; arXiv 1206.2229 v4 Lemma 30 for the gcd statement),
Beeson-Zhang, Laczkovich (DCG 48 (2012)).  Formalization debt, not progress on the /goal outcomes.  No H1 is needed:
everything here is arithmetic, or trigonometry of a single tile defined from its sides by the law of cosines.

Map rows (MAP_RECOUNT_2026-10-22_v5): R-L11, R-L12 (= printed Lemma 11, trigonometric formulas, together with the
printed Lemma 10 formulas for alpha), R-L13 (printed Lemma 12, pairwise coprime), R-L14 (printed Lemma 16, 3 does not
divide c), R-L15 (printed Lemma 13, the gcd of the three vertices), R-L16 (printed Lemma 15, a+b composite),
R-L17 (printed Lemma 14, integrality of the scale).  Previously the arithmetic ones existed only for `Nat.Coprime a b`
(`FDDShapes.coprime_c`, `three_not_dvd_c`, `apb_not_prime`); here they are stated with the PRINTED hypothesis
"(a,b,c) have no common divisor", `gcd (gcd a b) c = 1`.

Printed gap noted: Lemma 13 is cited to [6] Lemma 30; here it is proved from Lemma 12 and 16 (no citation).
-/

namespace Erdos634.BeesonRow

open Real

/-- Printed Lemma 12 (R-L13): `c^2 = a^2+b^2+ab`, `(a,b,c)` without common divisor => pairwise coprime. -/
theorem rl13_pairwise (a b c : ℕ) (h : c ^ 2 = a ^ 2 + b ^ 2 + a * b)
    (hg : Nat.gcd (Nat.gcd a b) c = 1) :
    Nat.Coprime a b ∧ Nat.Coprime a c ∧ Nat.Coprime b c := by
  have none : ∀ p : ℕ, p.Prime → p ∣ a → p ∣ b → p ∣ c → False := by
    intro p hp h1 h2 h3
    have : p ∣ Nat.gcd (Nat.gcd a b) c := Nat.dvd_gcd (Nat.dvd_gcd h1 h2) h3
    rw [hg] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  refine ⟨?_, ?_, ?_⟩
  · apply Nat.coprime_of_dvd
    intro p hp h1 h2
    refine ?_
    have : p ∣ c ^ 2 := by
      rw [h]
      exact dvd_add (dvd_add (dvd_pow h1 two_ne_zero) (dvd_pow h2 two_ne_zero)) (Dvd.dvd.mul_right h1 b)
    exact none p hp h1 h2 (hp.dvd_of_dvd_pow this)
  · apply Nat.coprime_of_dvd
    intro p hp h1 h3
    have hb2 : p ∣ b ^ 2 := by
      have e : b ^ 2 + (a ^ 2 + a * b) = c ^ 2 := by rw [h]; ring
      have hc2 : p ∣ c ^ 2 := dvd_pow h3 two_ne_zero
      have hs : p ∣ a ^ 2 + a * b :=
        dvd_add (dvd_pow h1 two_ne_zero) (Dvd.dvd.mul_right h1 b)
      rw [← e] at hc2
      exact (Nat.dvd_add_left hs).mp hc2
    exact none p hp h1 (hp.dvd_of_dvd_pow hb2) h3
  · apply Nat.coprime_of_dvd
    intro p hp h2 h3
    have ha2 : p ∣ a ^ 2 := by
      have e : a ^ 2 + (b ^ 2 + a * b) = c ^ 2 := by rw [h]; ring
      have hc2 : p ∣ c ^ 2 := dvd_pow h3 two_ne_zero
      have hs : p ∣ b ^ 2 + a * b :=
        dvd_add (dvd_pow h2 two_ne_zero) (Dvd.dvd.mul_left h2 a)
      rw [← e] at hc2
      exact (Nat.dvd_add_left hs).mp hc2
    exact none p hp (hp.dvd_of_dvd_pow ha2) h2 h3

private theorem to_fdd (a b c : ℕ) (h : c ^ 2 = a ^ 2 + b ^ 2 + a * b) :
    c ^ 2 = a ^ 2 + a * b + b ^ 2 := by rw [h]; ring

/-- Printed Lemma 16 (R-L14): `3 ∤ c`. -/
theorem rl14_three_not_dvd (a b c : ℕ) (h : c ^ 2 = a ^ 2 + b ^ 2 + a * b)
    (hg : Nat.gcd (Nat.gcd a b) c = 1) : ¬ 3 ∣ c :=
  Erdos634.Draft.FDDShapes.three_not_dvd_c a b c (rl13_pairwise a b c h hg).1 (to_fdd a b c h)

/-- Printed Lemma 13 (R-L15): `gcd(c^2, c(a+2b), 3b(a+b)) = 1`.  Proved here (the paper cites [6] Lemma 30). -/
theorem rl15_gcd (a b c : ℕ) (h : c ^ 2 = a ^ 2 + b ^ 2 + a * b)
    (hg : Nat.gcd (Nat.gcd a b) c = 1) :
    Nat.gcd (Nat.gcd (c ^ 2) (c * (a + 2 * b))) (3 * b * (a + b)) = 1 := by
  obtain ⟨_, hcb, hcab, _, _, hc3⟩ :=
    Erdos634.Draft.FDDShapes.coprime_c a b c (rl13_pairwise a b c h hg).1 (to_fdd a b c h)
  have : Nat.Coprime (c ^ 2) (3 * b * (a + b)) :=
    Nat.Coprime.pow_left 2 (Nat.Coprime.mul_right (Nat.Coprime.mul_right hc3 hcb) hcab)
  exact Erdos634.Draft.FDDShapes.gcd3_one_of_xz this

/-- Printed Lemma 15 (R-L16): `a + b` is composite. -/
theorem rl16_composite (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (h : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    1 < a + b ∧ ¬ Nat.Prime (a + b) :=
  ⟨by omega, Erdos634.Draft.FDDShapes.apb_not_prime a b c ha hb h⟩

/-- Printed Lemma 14 (R-L17): sides `(X,Y,Z)` proportional to `(X0,Y0,Z0)` with `gcd = 1` are an INTEGER multiple. -/
theorem rl17_integer_scale (X Y Z X0 Y0 Z0 : ℕ) (h0 : 0 < X0)
    (hg : Nat.gcd (Nat.gcd X0 Y0) Z0 = 1) (hy : X * Y0 = Y * X0) (hz : X * Z0 = Z * X0) :
    ∃ l : ℕ, X = l * X0 ∧ Y = l * Y0 ∧ Z = l * Z0 := by
  have hd : X0 ∣ X := by
    have h1 : X0 ∣ X * X0 := Dvd.intro_left _ rfl
    have h2 : X0 ∣ X * Y0 := ⟨Y, by rw [hy]; ring⟩
    have h3 : X0 ∣ X * Z0 := ⟨Z, by rw [hz]; ring⟩
    have := Nat.dvd_gcd (Nat.dvd_gcd h1 h2) h3
    rw [Nat.gcd_mul_left, Nat.gcd_mul_left, hg, mul_one] at this
    exact this
  obtain ⟨l, rfl⟩ := hd
  refine ⟨l, Nat.mul_comm _ _, ?_, ?_⟩
  · apply Nat.eq_of_mul_eq_mul_right h0
    nlinarith [hy]
  · apply Nat.eq_of_mul_eq_mul_right h0
    nlinarith [hz]

/-- The angles of the tile with sides `a,b,c` opposite `alpha,beta,gamma`, from the law of cosines. -/
noncomputable def angA (a b c : ℝ) : ℝ := Real.arccos ((b ^ 2 + c ^ 2 - a ^ 2) / (2 * b * c))
noncomputable def angB (a b c : ℝ) : ℝ := Real.arccos ((a ^ 2 + c ^ 2 - b ^ 2) / (2 * a * c))

/-- Printed Lemmas 10, 11 (R-L11, R-L12): tile `(alpha, beta, 2 pi/3)`, sides `(a,b,c)`, `c^2 = a^2+b^2+ab`
(the law of cosines at gamma = 2 pi/3).  Then alpha + beta = pi/3 (so the tile has angle 2pi/3), and
sin beta = b sqrt 3/(2c), cos beta = (2a+b)/(2c), sin 2beta = b sqrt 3 (2a+b)/(2 c^2),
sin(2alpha+beta) = sin(alpha+2beta) = sqrt 3 (a+b)/(2c); also sin alpha = a sqrt 3/(2c), cos alpha = (a+2b)/(2c). -/
theorem rl11_trig (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : c ^ 2 = a ^ 2 + b ^ 2 + a * b) (α β : ℝ) (hα : α = angA a b c) (hβ : β = angB a b c) :
    α + β = π / 3 ∧
    Real.cos α = (a + 2 * b) / (2 * c) ∧ Real.sin α = a * √3 / (2 * c) ∧
    Real.cos β = (2 * a + b) / (2 * c) ∧ Real.sin β = b * √3 / (2 * c) ∧
    Real.sin (2 * β) = b * √3 * (2 * a + b) / (2 * c ^ 2) ∧
    Real.sin (2 * α + β) = √3 * (a + b) / (2 * c) ∧
    Real.sin (α + 2 * β) = √3 * (a + b) / (2 * c) := by
  have s3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have s3p : 0 < √3 := Real.sqrt_pos.mpr (by norm_num)
  have xa : (b ^ 2 + c ^ 2 - a ^ 2) / (2 * b * c) = (a + 2 * b) / (2 * c) := by
    field_simp; nlinarith [h]
  have xb : (a ^ 2 + c ^ 2 - b ^ 2) / (2 * a * c) = (2 * a + b) / (2 * c) := by
    field_simp; nlinarith [h]
  have ca : Real.cos α = (a + 2 * b) / (2 * c) := by
    rw [hα, angA, Real.cos_arccos, xa]
    · have : -1 ≤ (a + 2 * b) / (2 * c) := by
        have : 0 ≤ (a + 2 * b) / (2 * c) := by positivity
        linarith
      rw [xa]; exact this
    · rw [xa, div_le_one (by positivity)]; nlinarith [h]
  have cb : Real.cos β = (2 * a + b) / (2 * c) := by
    rw [hβ, angB, Real.cos_arccos, xb]
    · have : 0 ≤ (2 * a + b) / (2 * c) := by positivity
      rw [xb]; linarith
    · rw [xb, div_le_one (by positivity)]; nlinarith [h]
  have sa : Real.sin α = a * √3 / (2 * c) := by
    rw [hα, angA, Real.sin_arccos, xa]
    have e : 1 - ((a + 2 * b) / (2 * c)) ^ 2 = (a * √3 / (2 * c)) ^ 2 := by
      field_simp; nlinarith [h, s3]
    rw [e]; exact Real.sqrt_sq (by positivity)
  have sb : Real.sin β = b * √3 / (2 * c) := by
    rw [hβ, angB, Real.sin_arccos, xb]
    have e : 1 - ((2 * a + b) / (2 * c)) ^ 2 = (b * √3 / (2 * c)) ^ 2 := by
      field_simp; nlinarith [h, s3]
    rw [e]; exact Real.sqrt_sq (by positivity)
  have hsum : α + β = π / 3 := by
    have hc' : Real.cos (α + β) = Real.cos (π / 3) := by
      rw [Real.cos_add, ca, cb, sa, sb, Real.cos_pi_div_three]
      field_simp; nlinarith [h, s3]
    have a0 : 0 ≤ α := hα ▸ Real.arccos_nonneg _
    have b0 : 0 ≤ β := hβ ▸ Real.arccos_nonneg _
    have a1 : α ≤ π / 2 := by
      rw [hα, angA]; apply Real.arccos_le_pi_div_two.mpr; rw [xa]; positivity
    have b1 : β ≤ π / 2 := by
      rw [hβ, angB]; apply Real.arccos_le_pi_div_two.mpr; rw [xb]; positivity
    apply Real.injOn_cos ⟨by linarith, by linarith [Real.pi_pos]⟩
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ hc'
  refine ⟨hsum, ca, sa, cb, sb, ?_, ?_, ?_⟩
  · rw [Real.sin_two_mul, sb, cb]; field_simp
  · have : 2 * α + β = π / 3 + α := by linarith
    rw [this, Real.sin_add, Real.sin_pi_div_three, Real.cos_pi_div_three, ca, sa]
    field_simp; ring
  · have : α + 2 * β = π / 3 + β := by linarith
    rw [this, Real.sin_add, Real.sin_pi_div_three, Real.cos_pi_div_three, cb, sb]
    field_simp; ring

/-- Witness for the hypotheses: the tile (3,5,7), 49 = 9+25+15. -/
theorem wit_357 : (7 : ℕ) ^ 2 = 3 ^ 2 + 5 ^ 2 + 3 * 5 ∧ Nat.gcd (Nat.gcd 3 5) 7 = 1 := by decide

end Erdos634.BeesonRow
