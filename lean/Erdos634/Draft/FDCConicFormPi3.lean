-- Draft/FDCConicFormPi3.lean — `prop:conicform`, π/3 half: the "requires" direction from a real tiling.
-- A tiling of an equilateral target by a π/3 tile `(α, 2π/3 − α, π/3)` with integer sides and
-- `α ∉ ℚπ` yields the conic form of the paper: `uv = 16N²`, `(u+v)/2 = 5N − M²`,
-- `0 < M < √N`, `M ≡ N (mod 2)`.
-- Route: `Row5.theoremE_sixty` (FluxCRow5: tiling → integers `m₁ > m₂ ≥ 1`, `m₁m₂ = 3N`, parities)
-- then `M := m₂`, `y := m₂·q` with `q = |2S(a−b)/(ab)|` an integer, and the ring identity
-- `(9N − m₂²)(N − m₂²) = (m₂ q)²`.  Strictness `M² < N` is exactly where `α ∉ ℚπ` enters:
-- `a = b` would force `α = 2π/3 − α`, i.e. `α = π/3`.
-- Written 2026-10-05.  UNAUDITED.
import Erdos634.Draft.FDCEqSpec
import Erdos634.Draft.FluxERow2E
import Erdos634.EquilateralConic

namespace Erdos634.Draft.FDCConicFormPi3

open Erdos634.Geometry Erdos634.Draft Erdos634.Draft.FDCEqSpec

/-- **`prop:eqspecint`, π/3 analogue.**  `D` an `N`-tiling of an equilateral target (all angles
`π/3`, side `S`) by the `π/3` tile of sides `(a,b,c)` (integers), `α ∉ ℚπ`.  Then there are integers
`m₁ > m₂ ≥ 1` with `m₁ ≡ m₂ ≡ N (mod 2)`, `m₁(a+b−c) = 3S`, `m₂(a+b+c) = 3S`, `S² = N·ab`,
`m₁m₂ = 3N`, and a positive integer `q = |2S(a−b)/(ab)|` with `(m₁+m₂)² − 16N = q²`. -/
theorem eqspecint_sixty {N : ℕ} (D : CongruentDissection N) {α a b c S : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.SixtyData α a b c)
    (hint : ∃ a' b' c' : ℤ, (a' : ℝ) = a ∧ (b' : ℝ) = b ∧ (c' : ℝ) = c)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3)
    (hS : ∀ k, D.target.oppLen k = S) :
    ∃ m₁ m₂ q : ℤ, 1 ≤ m₂ ∧ m₂ < m₁ ∧ (2 : ℤ) ∣ m₁ - N ∧ (2 : ℤ) ∣ m₂ - N ∧
      (m₁ : ℝ) = 3 * S / (a + b - c) ∧ (m₂ : ℝ) = 3 * S / (a + b + c) ∧
      (q : ℝ) = |2 * S * (a - b) / (a * b)| ∧ 1 ≤ q ∧
      S ^ 2 = N * a * b ∧ m₁ * m₂ = 3 * N ∧ (m₁ + m₂) ^ 2 - 16 * (N : ℤ) = q ^ 2 := by
  obtain ⟨m₁, m₂, hp1, hp2, hm1, hm1N, hm2, hm2N, e1, e2, harea, hprod, hlt, -⟩ :=
    Row5.theoremE_sixty D hα h hP
  have hS0 := hS 0
  rw [hS0] at e1 e2 harea
  obtain ⟨σ, hA0, oa, hA1, ob, hA2, oc⟩ := h
  have ha0 : 0 < a := oa ▸ D.model.oppLen_pos (σ 0)
  have hb0 : 0 < b := ob ▸ D.model.oppLen_pos (σ 1)
  have hc0 : 0 < c := oc ▸ D.model.oppLen_pos (σ 2)
  have hSpos : 0 < S := hS0 ▸ D.target.oppLen_pos 0
  have tc := D.model.oppLen_lt_perm σ 2
  rw [oa, ob, oc] at tc
  have hXp : 0 < a + b - c := by linarith
  have hYp : 0 < a + b + c := by linarith
  have hcos : c ^ 2 = a ^ 2 + b ^ 2 + (-1) * a * b := by
    have hl := D.model.lawCos_perm σ
    rw [oa, ob, oc, hA2, Real.cos_pi_div_three] at hl
    linear_combination hl
  have hab : a * b ≠ 0 := (mul_pos ha0 hb0).ne'
  have hXY : (a + b - c) * (a + b + c) = 3 * (a * b) := by linear_combination (-1 : ℝ) * hcos
  have hm1v : (m₁ : ℝ) * (a * b) = S * (a + b + c) := by
    apply mul_right_cancel₀ hXp.ne'
    linear_combination (a * b) * e1 - S * hXY
  have hm2v : (m₂ : ℝ) * (a * b) = S * (a + b - c) := by
    apply mul_right_cancel₀ hYp.ne'
    linear_combination (a * b) * e2 - S * hXY
  have hsumv : ((m₁ : ℝ) + m₂) * (a * b) = 2 * S * (a + b) := by
    linear_combination hm1v + hm2v
  have hz2 : (2 * S * (a - b) / (a * b)) ^ 2 = ((m₁ : ℝ) + m₂) ^ 2 - 16 * (N : ℝ) := by
    rw [div_pow, div_eq_iff (pow_ne_zero 2 hab)]
    linear_combination (-(((m₁ : ℝ) + m₂) * (a * b) + 2 * S * (a + b))) * hsumv
      + (-16 * (a * b)) * harea
  have hab_ne : a ≠ b := by
    intro hab_eq
    have h01 : σ 0 ≠ σ 1 := fun h' => absurd (σ.injective h') (by decide)
    have hang := D.model.angle_eq_of_oppLen_eq h01 (oa.trans (hab_eq.trans ob.symm))
    rw [hA0, hA1] at hang
    exact hα ⟨1 / 3, by push_cast; linarith⟩
  have hz0 : 2 * S * (a - b) / (a * b) ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hSpos.ne') (sub_ne_zero.mpr hab_ne)) hab
  obtain ⟨a', b', c', ea, eb, ec⟩ := hint
  have hzrat : ∃ x : ℚ, (x : ℝ) = 2 * S * (a - b) / (a * b) := by
    refine ⟨2 * (((m₁ : ℚ) * ((a' : ℚ) + b' - c')) / 3) * ((a' : ℚ) - b') / ((a' : ℚ) * b'), ?_⟩
    have hSv : S = (m₁ : ℝ) * (a + b - c) / 3 := by linarith
    rw [hSv, ← ea, ← eb, ← ec]
    push_cast
    try ring
  obtain ⟨x₀, hx₀⟩ := hzrat
  obtain ⟨q, hq0, hqe⟩ := exists_int_of_sq_int (r := |2 * S * (a - b) / (a * b)|)
    (abs_pos.mpr hz0) ⟨|x₀|, by rw [Rat.cast_abs, hx₀]⟩ ((m₁ + m₂) ^ 2 - 16 * (N : ℤ))
    (by rw [sq_abs, hz2]; push_cast; try ring)
  refine ⟨m₁, m₂, q, hm2, hlt, hp1, hp2, ?_, ?_, hqe, by omega, harea, hprod, ?_⟩
  · rw [eq_div_iff hXp.ne']; exact e1
  · rw [eq_div_iff hYp.ne']; exact e2
  · have : (((m₁ + m₂) ^ 2 - 16 * (N : ℤ) : ℤ) : ℝ) = ((q ^ 2 : ℤ) : ℝ) := by
      push_cast
      rw [hqe, sq_abs, hz2]
    exact_mod_cast this

/-- **`prop:conicform`, π/3 half, "requires" direction from a real tiling.**  Given a
`CongruentDissection N` of an equilateral target by a π/3 tile with integer sides and
`α ∉ ℚπ`, there are integers `u, v, M` with `uv = 16N²`, `2 ∣ u + v`, `(u+v)/2 = 5N − M²`,
`0 < M < √N` and `M ≡ N (mod 2)`. -/
theorem conicform_pi3_of_tiling {N : ℕ} (D : CongruentDissection N) {α a b c S : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.SixtyData α a b c)
    (hint : ∃ a' b' c' : ℤ, (a' : ℝ) = a ∧ (b' : ℝ) = b ∧ (c' : ℝ) = c)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3)
    (hS : ∀ k, D.target.oppLen k = S) :
    ∃ u v M : ℤ, u * v = 16 * (N : ℤ) ^ 2 ∧ (2 : ℤ) ∣ (u + v) ∧
      (u + v) / 2 = 5 * (N : ℤ) - M ^ 2 ∧ 0 < M ∧ (M : ℝ) < Real.sqrt N ∧ (2 : ℤ) ∣ M - N := by
  obtain ⟨m₁, m₂, q, hm2, hlt, -, h2, -, -, -, hq1, -, hprod, hconic⟩ :=
    eqspecint_sixty D hα h hint hP hS
  have hsq : (9 * (N : ℤ) - m₂ ^ 2) * ((N : ℤ) - m₂ ^ 2) = (m₂ * q) ^ 2 := by
    linear_combination (-(3 * (N : ℤ) + m₁ * m₂ + 2 * m₂ ^ 2)) * hprod + m₂ ^ 2 * hconic
  obtain ⟨u, v, huv, hpar, hhalf⟩ := EquilateralConic.conicform_pi3 N m₂ (m₂ * q) hsq
  have key : (3 * m₁ - m₂) * (m₁ - 3 * m₂) = 3 * q ^ 2 := by
    linear_combination (-16 : ℤ) * hprod + 3 * hconic
  have hpos : 0 < (3 * m₁ - m₂) * (m₁ - 3 * m₂) := by
    rw [key]; nlinarith
  have hlt3 : 3 * m₂ < m₁ := by
    have h3 : 0 < 3 * m₁ - m₂ := by omega
    have := (pos_iff_pos_of_mul_pos hpos).mp h3
    omega
  have hMN : m₂ ^ 2 < (N : ℤ) := by
    have : 3 * m₂ * m₂ < m₁ * m₂ := mul_lt_mul_of_pos_right hlt3 (by omega)
    nlinarith
  refine ⟨u, v, m₂, huv, hpar, hhalf, by omega, ?_, h2⟩
  exact (Real.lt_sqrt (by exact_mod_cast (show (0 : ℤ) ≤ m₂ by omega))).mpr
    (by exact_mod_cast hMN)

/-- **`prop:conicform`, 2π/3 half, with the paper's parity clause.**  Same as
`FDCConicForm.conicform_of_tiling` but also keeping `s ≡ 3N/s ≡ N (mod 2)`, which that wrapper
discards although `eqspecint_paper` supplies it. -/
theorem conicform_2pi3_of_tiling_full {N : ℕ} (D : CongruentDissection N) {α a b c S : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoPiThreeData α a b c)
    (hint : ∃ a' b' c' : ℤ, (a' : ℝ) = a ∧ (b' : ℝ) = b ∧ (c' : ℝ) = c)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3)
    (hS : ∀ k, D.target.oppLen k = S) :
    ∃ u v : ℤ, u * v = 16 * (N : ℤ) ^ 2 ∧ (2 : ℤ) ∣ (u + v) ∧
      ∃ s : ℤ, (u + v) / 2 - 5 * (N : ℤ) = s ^ 2 ∧ s ∣ 3 * (N : ℤ) ∧
        (2 : ℤ) ∣ s - N ∧ (2 : ℤ) ∣ 3 * (N : ℤ) / s - N := by
  obtain ⟨s, t, q, hs1, -, -, hs2, ht2, -, -, -, -, hst, hconic⟩ :=
    eqspecint_paper D hα h hint hP hS
  obtain ⟨u, v, huv, hpar, hsum, hdvd⟩ := EquilateralConic.conicform_2pi3 s t N q
    (mul_comm s t ▸ hst) hconic
  have hs0 : s ≠ 0 := by omega
  have h3 : 3 * (N : ℤ) / s = t := by
    rw [← hst]; exact Int.mul_ediv_cancel_left t hs0
  exact ⟨u, v, huv, hpar, s, hsum, hdvd, hs2, by rw [h3]; exact ht2⟩

/-- **`prop:conicform`, both halves, as the paper states it** (`erdos-634.tex`, "Conic form"):
for every `N`, a `2π/3` tile tiling an equilateral target requires a factorization `uv = 16N²`
with `u + v ≡ 0 (mod 2)` and `(u+v)/2 − 5N = s²` for a divisor `s` of `3N` with
`s ≡ 3N/s ≡ N (mod 2)`; a `π/3` tile requires `uv = 16N²` with `(u+v)/2 = 5N − M²` for some
`0 < M < √N`, `M ≡ N (mod 2)`.  The tile has integer sides and `α ∉ ℚπ`, the paper's standing
normalization (as in `prop:eqspecint`). -/
theorem conicform_paper (N : ℕ) :
    (∀ (D : CongruentDissection N) (α a b c S : ℝ), (¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) →
      D.model.TwoPiThreeData α a b c →
      (∃ a' b' c' : ℤ, (a' : ℝ) = a ∧ (b' : ℝ) = b ∧ (c' : ℝ) = c) →
      (∀ k, D.target.angleAt k = Real.pi / 3) → (∀ k, D.target.oppLen k = S) →
      ∃ u v : ℤ, u * v = 16 * (N : ℤ) ^ 2 ∧ (2 : ℤ) ∣ (u + v) ∧
        ∃ s : ℤ, (u + v) / 2 - 5 * (N : ℤ) = s ^ 2 ∧ s ∣ 3 * (N : ℤ) ∧
          (2 : ℤ) ∣ s - N ∧ (2 : ℤ) ∣ 3 * (N : ℤ) / s - N) ∧
    (∀ (D : CongruentDissection N) (α a b c S : ℝ), (¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) →
      D.model.SixtyData α a b c →
      (∃ a' b' c' : ℤ, (a' : ℝ) = a ∧ (b' : ℝ) = b ∧ (c' : ℝ) = c) →
      (∀ k, D.target.angleAt k = Real.pi / 3) → (∀ k, D.target.oppLen k = S) →
      ∃ u v M : ℤ, u * v = 16 * (N : ℤ) ^ 2 ∧ (2 : ℤ) ∣ (u + v) ∧
        (u + v) / 2 = 5 * (N : ℤ) - M ^ 2 ∧ 0 < M ∧ (M : ℝ) < Real.sqrt N ∧ (2 : ℤ) ∣ M - N) :=
  ⟨fun D _ _ _ _ _ hα h hint hP hS => conicform_2pi3_of_tiling_full D hα h hint hP hS,
   fun D _ _ _ _ _ hα h hint hP hS => conicform_pi3_of_tiling D hα h hint hP hS⟩

/-- Arithmetic instance of the conclusion at Herdt's `N = 1944` (tile `(3,8,7)`, `S = 216`,
`m₁ = 162`, `m₂ = 36`, `q = 90`): `M = 36`, `u = 5184`, `v = 11664`. -/
theorem conicform_pi3_instance_1944 :
    ∃ u v M : ℤ, u * v = 16 * (1944 : ℤ) ^ 2 ∧ (2 : ℤ) ∣ (u + v) ∧
      (u + v) / 2 = 5 * (1944 : ℤ) - M ^ 2 ∧ 0 < M ∧ M ^ 2 < 1944 ∧ (2 : ℤ) ∣ M - 1944 :=
  ⟨5184, 11664, 36, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

end Erdos634.Draft.FDCConicFormPi3

#print axioms Erdos634.Draft.FDCConicFormPi3.eqspecint_sixty
#print axioms Erdos634.Draft.FDCConicFormPi3.conicform_pi3_of_tiling
#print axioms Erdos634.Draft.FDCConicFormPi3.conicform_2pi3_of_tiling_full
#print axioms Erdos634.Draft.FDCConicFormPi3.conicform_paper
#print axioms Erdos634.Draft.FDCConicFormPi3.conicform_pi3_instance_1944
