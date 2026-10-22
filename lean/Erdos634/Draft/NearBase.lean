-- Draft/NearBase.lean — R5 ((private working notes, not included) R5; (private working notes, not included) §2–4 and
-- (private working notes, not included)): the arithmetic / trigonometric core of the near-base vertex
-- lemma NB, its (4,7) instance, the tile (2,3,4) threshold, and the named infinite family
-- `(f+1) ∣ e²` (with the reviewer's repaired thin / thick inequalities).  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
-- Everything here is proved (no `sorry`).  NB's geometric statement is in Draft/NearBaseVertex.lean.
--
-- Conventions (as ThickEFminus1Probe / Draft/MirrorStripR2): tile `(a,b,c) = (ef, f²−e², f²)`,
-- `x = α/2` with `sin x = e/(2f)`, `0 < cos x`; `3α + 2β = π`, `γ = 2α + β = π/2 + α/2`.
-- NB's data: `ℓ = min(a,b)` (shortest side), `L = c` (longest), `H = b·sin α` (the altitude onto `c`,
-- `= 2·Area/c`, the least altitude since `c` is the longest side).
--   (1)  h < ℓ·cos(γ/2)                    ⟺  4f·h² < ℓ²·(2f − e)
--   (2)  h·(1 + L/ℓ) < H·√(1 − h²/ℓ²)       ⟺  h²·((ℓ+L)² + H²) < H²·ℓ²   (for 0 ≤ h < ℓ)
-- so `h₁² = ℓ²(2f−e)/(4f)` and `h₂² = H²ℓ²/((ℓ+L)² + H²)` are rational in `e, f` (with
-- `H² = e²b²(4f²−e²)/(4f⁴)`).
--
-- NOVELTY ((private working notes, not included) 2026-09-23, "cos (γ / 2)", "least altitude", "h₀", "2 * (f + 1) ≤";
-- grep "below the base"): no statement of NB or of the family in the corpus.  Technique-level
-- neighbours only: ThickEFminus1Probe.alpha_corner_below / beta_corner_below (a flank reaching below
-- the base), ThickBlockingLemmas "below the base" escape lemmas, CertNode §7 `hblocked` below the base.
import Mathlib

namespace Erdos634.Draft.NearBase

open Real

/-! ## §1 NB's two conditions in squared form (pure real algebra) -/

/-- **(1) squared.**  For `h ≥ 0`, `ℓ > 0`, `cg > 0`: `h < ℓ·cg ↔ h² < ℓ²·cg²`. -/
theorem cond1_iff_sq {h ℓ cg : ℝ} (hh : 0 ≤ h) (hℓ : 0 < ℓ) (hcg : 0 < cg) :
    h < ℓ * cg ↔ h ^ 2 < ℓ ^ 2 * cg ^ 2 := by
  have hp : 0 < ℓ * cg := mul_pos hℓ hcg
  constructor
  · intro h1; nlinarith
  · intro h1; by_contra h2; push Not at h2; nlinarith

/-- **(2) from its squared form.**  For `0 ≤ h < ℓ`, `L ≥ 0`, `H ≥ 0`:
`h²((ℓ+L)² + H²) < H²ℓ²  ⟹  h·(1 + L/ℓ) < H·√(1 − h²/ℓ²)`. -/
theorem cond2_of_sq {h ℓ L H : ℝ} (hh : 0 ≤ h) (hℓ : 0 < ℓ) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hlt : h < ℓ) (hsq : h ^ 2 * ((ℓ + L) ^ 2 + H ^ 2) < H ^ 2 * ℓ ^ 2) :
    h * (1 + L / ℓ) < H * √(1 - h ^ 2 / ℓ ^ 2) := by
  have hℓ2 : 0 < ℓ ^ 2 := by positivity
  have hr : 0 ≤ 1 - h ^ 2 / ℓ ^ 2 := by
    rw [sub_nonneg, div_le_one hℓ2]; nlinarith
  set s := √(1 - h ^ 2 / ℓ ^ 2) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 - h ^ 2 / ℓ ^ 2 := Real.sq_sqrt hr
  have hlhs : h * (1 + L / ℓ) = h * (ℓ + L) / ℓ := by field_simp
  rw [hlhs]
  have hR : 0 ≤ H * s := mul_nonneg hH hs0
  -- compare squares
  have key : (h * (ℓ + L) / ℓ) ^ 2 < (H * s) ^ 2 := by
    rw [mul_pow, hs2, div_pow]
    rw [div_lt_iff₀ hℓ2]
    have : H ^ 2 * (1 - h ^ 2 / ℓ ^ 2) * ℓ ^ 2 = H ^ 2 * ℓ ^ 2 - H ^ 2 * h ^ 2 := by
      field_simp
    rw [this]; nlinarith
  by_contra hc; push Not at hc
  nlinarith

/-- **(2) squared, the converse** (so the squared form is exactly NB's condition (2)). -/
theorem sq_of_cond2 {h ℓ L H : ℝ} (hh : 0 ≤ h) (hℓ : 0 < ℓ) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hlt : h < ℓ) (h2 : h * (1 + L / ℓ) < H * √(1 - h ^ 2 / ℓ ^ 2)) :
    h ^ 2 * ((ℓ + L) ^ 2 + H ^ 2) < H ^ 2 * ℓ ^ 2 := by
  have hℓ2 : 0 < ℓ ^ 2 := by positivity
  have hr : 0 ≤ 1 - h ^ 2 / ℓ ^ 2 := by
    rw [sub_nonneg, div_le_one hℓ2]; nlinarith
  have hs2 : √(1 - h ^ 2 / ℓ ^ 2) ^ 2 = 1 - h ^ 2 / ℓ ^ 2 := Real.sq_sqrt hr
  have hl0 : 0 ≤ h * (1 + L / ℓ) := mul_nonneg hh (by positivity)
  have hsq : (h * (1 + L / ℓ)) ^ 2 < (H * √(1 - h ^ 2 / ℓ ^ 2)) ^ 2 := by
    have := mul_self_lt_mul_self hl0 h2; nlinarith
  rw [mul_pow, mul_pow, hs2] at hsq
  have e1 : (1 + L / ℓ) ^ 2 = (ℓ + L) ^ 2 / ℓ ^ 2 := by field_simp
  rw [e1] at hsq
  have e2 : h ^ 2 * ((ℓ + L) ^ 2 / ℓ ^ 2) = h ^ 2 * (ℓ + L) ^ 2 / ℓ ^ 2 := by ring
  have e3 : H ^ 2 * (1 - h ^ 2 / ℓ ^ 2) = (H ^ 2 * ℓ ^ 2 - H ^ 2 * h ^ 2) / ℓ ^ 2 := by
    field_simp
  rw [e2, e3, div_lt_div_iff_of_pos_right hℓ2] at hsq
  nlinarith

/-- `h₂² = H²ℓ²/((ℓ+L)² + H²)` for `h₂ = H/√((1 + L/ℓ)² + H²/ℓ²)` (the report's threshold). -/
theorem h2_sq {ℓ L H : ℝ} (hℓ : 0 < ℓ) :
    (H / √((1 + L / ℓ) ^ 2 + H ^ 2 / ℓ ^ 2)) ^ 2 = H ^ 2 * ℓ ^ 2 / ((ℓ + L) ^ 2 + H ^ 2) := by
  have hpos : 0 ≤ (1 + L / ℓ) ^ 2 + H ^ 2 / ℓ ^ 2 := by positivity
  rw [div_pow, Real.sq_sqrt hpos]
  have hℓ' : ℓ ≠ 0 := hℓ.ne'
  field_simp

/-! ## §2 The base-β tile at `m = 1`: exact forms of `cos²(α/2)`, `cos²(γ/2)`, `H²` -/

/-- `γ = π/2 + α/2` from `3α + 2β = π`, `γ = 2α + β` (the corpus angle relations). -/
theorem gamma_eq {α β γ : ℝ} (hrel : 3 * α + 2 * β = π) (hγ : γ = 2 * α + β) :
    γ = π / 2 + α / 2 := by subst hγ; linarith

/-- `cos²(α/2) = (4f² − e²)/(4f²)`. -/
theorem cos_sq_half {e f x : ℝ} (hf : f ≠ 0) (hs : sin x = e / (2 * f)) :
    cos x ^ 2 = (4 * f ^ 2 - e ^ 2) / (4 * f ^ 2) := by
  rw [cos_sq', hs]; field_simp; ring

/-- `cos²(γ/2) = (2f − e)/(4f)` for `γ = π/2 + x` (`x = α/2`). -/
theorem cos_sq_gamma_half {e f x : ℝ} (hf : f ≠ 0) (hs : sin x = e / (2 * f)) :
    cos ((π / 2 + x) / 2) ^ 2 = (2 * f - e) / (4 * f) := by
  have h1 : cos ((π / 2 + x) / 2) ^ 2 = 1 / 2 + cos (π / 2 + x) / 2 := by
    rw [cos_sq]; congr 2; ring_nf
  rw [h1, cos_add, cos_pi_div_two, sin_pi_div_two, hs]
  field_simp; ring

/-- `cos(γ/2) > 0` for `x = α/2 ∈ (0, π/2)` (indeed `γ/2 < π/2`). -/
theorem cos_gamma_half_pos {x : ℝ} (hx0 : 0 < x) (hx1 : x < π / 2) :
    0 < cos ((π / 2 + x) / 2) := by
  apply cos_pos_of_mem_Ioo; constructor <;> linarith [pi_pos]

/-- `H² = (b·sin α)² = e²b²(4f² − e²)/(4f⁴)` (`α = 2x`). -/
theorem H_sq {e f b x : ℝ} (hf : f ≠ 0) (hs : sin x = e / (2 * f)) :
    (b * sin (2 * x)) ^ 2 = e ^ 2 * b ^ 2 * (4 * f ^ 2 - e ^ 2) / (4 * f ^ 4) := by
  rw [sin_two_mul, mul_pow, mul_pow, mul_pow, cos_sq_half hf hs, hs]
  field_simp

/-- `H = b·sin α = 2·Area/c` with `Area = ½·b·c·sin α` (the angle `α` lies between sides `b`, `c`);
since `c` is the longest side, this is the least altitude. -/
theorem H_eq_two_area_div {b c s : ℝ} (hc : c ≠ 0) : b * s = 2 * ((1 / 2) * b * c * s) / c := by
  field_simp

/-- `c = f²` is the longest side: `ef < f²` and `f² − e² < f²` (`0 < e < f`). -/
theorem c_longest {e f : ℝ} (he : 0 < e) (hef : e < f) : e * f < f ^ 2 ∧ f ^ 2 - e ^ 2 < f ^ 2 := by
  constructor <;> nlinarith

/-- A real `x = α/2` with `sin x = e/(2f)`, `0 < x < π/2` exists for `0 < e < 2f` (non-vacuity of
the trigonometric hypotheses). -/
theorem exists_half_angle {e f : ℝ} (he : 0 < e) (hef : e < 2 * f) :
    ∃ x : ℝ, sin x = e / (2 * f) ∧ 0 < x ∧ x < π / 2 ∧ 0 < cos x := by
  have hf : 0 < f := by linarith
  have h1 : e / (2 * f) < 1 := by rw [div_lt_one (by positivity)]; exact hef
  have h0 : 0 < e / (2 * f) := by positivity
  refine ⟨arcsin (e / (2 * f)), sin_arcsin (by linarith) h1.le, arcsin_pos.mpr h0,
    arcsin_lt_pi_div_two.mpr h1, ?_⟩
  rw [cos_arcsin]; apply Real.sqrt_pos.mpr; nlinarith

/-! ## §3 The (4,7) instance (`N = 131`): `x₀` at distance 2 along `r`, height `2·cos(α/2)` -/

/-- `h² = 180/49` for `h = 2·cos(α/2)` at `(e,f) = (4,7)` (`h = 6√5/7`). -/
theorem h_sq_47 {x : ℝ} (hs : sin x = 4 / (2 * 7)) : (2 * cos x) ^ 2 = 180 / 49 := by
  rw [mul_pow, cos_sq_half (by norm_num : (7 : ℝ) ≠ 0) hs]; norm_num

/-- `H² = 784080/2401` at `(4,7)` (`b = 33`). -/
theorem H_sq_47 {x : ℝ} (hs : sin x = 4 / (2 * 7)) :
    ((33 : ℝ) * sin (2 * x)) ^ 2 = 784080 / 2401 := by
  rw [H_sq (by norm_num : (7 : ℝ) ≠ 0) hs]; norm_num

/-- **The exact margins at (4,7)** (`ℓ = a = 28`, `L = c = 49`, `h² = 180/49`,
`H² = 784080/2401`, `cos²(γ/2) = 10/28`): margin (1) `ℓ²cos²(γ/2) − h² = 13540/49`, margin (2)
`H²(1 − h²/ℓ²) − h²(1 + L/ℓ)² = 6854421915/23059204` (`23059204 = 4·7⁸`). -/
theorem margins_47 :
    (28 : ℚ) ^ 2 * ((2 * 7 - 4) / (4 * 7)) - 180 / 49 = 13540 / 49 ∧
    (784080 / 2401 : ℚ) * (1 - (180 / 49) / 28 ^ 2) - (180 / 49) * (1 + 49 / 28) ^ 2
      = 6854421915 / 23059204 := by
  norm_num

/-- **NB's hypotheses (1) and (2) at x₀ = 229, (4,7), as real inequalities.** -/
theorem nb_holds_47 {x : ℝ} (hs : sin x = 4 / (2 * 7)) (hx0 : 0 < x) (hx1 : x < π / 2) :
    2 * cos x < 28 * cos ((π / 2 + x) / 2) ∧
      2 * cos x * (1 + 49 / 28) < (33 * sin (2 * x)) * √(1 - (2 * cos x) ^ 2 / 28 ^ 2) := by
  have hc : 0 < cos x := cos_pos_of_mem_Ioo ⟨by linarith, hx1⟩
  have hh := h_sq_47 hs
  have hH := H_sq_47 hs
  have hg := cos_sq_gamma_half (by norm_num : (7 : ℝ) ≠ 0) hs
  have hgpos := cos_gamma_half_pos hx0 hx1
  have hsin2 : 0 < sin (2 * x) := by
    rw [sin_two_mul]; have : 0 < sin x := by rw [hs]; norm_num
    positivity
  constructor
  · rw [cond1_iff_sq (by positivity) (by norm_num) hgpos, hh, hg]; norm_num
  · apply cond2_of_sq (by positivity) (by norm_num) (by norm_num) (by positivity)
    · nlinarith
    · rw [hh, hH]; norm_num

/-! ## §4 Tile (2,3,4): `h₁² = 3/2`, `h₂² = 60/271`, so `h₀² = 60/271` -/

/-- Tile `(2,3,4)`: `cos γ = −1/4`, `cos²(γ/2) = 3/8`, `h₁² = ℓ²·3/8 = 3/2`; `Area² = 135/16`
(Heron), `H² = (2·Area/4)² = 135/64`, `h₂² = H²ℓ²/((ℓ+L)² + H²) = 60/271`; `h₀² = min = 60/271`. -/
theorem tile234_threshold :
    ((2 : ℚ) ^ 2 + 3 ^ 2 - 4 ^ 2) / (2 * 2 * 3) = -1 / 4 ∧
    (2 : ℚ) ^ 2 * ((1 + (-1 / 4)) / 2) = 3 / 2 ∧
    (9 / 2 : ℚ) * (9 / 2 - 2) * (9 / 2 - 3) * (9 / 2 - 4) = 135 / 16 ∧
    (2 : ℚ) ^ 2 * (135 / 16) / 4 ^ 2 = 135 / 64 ∧
    (135 / 64 : ℚ) * 2 ^ 2 / ((2 + 4) ^ 2 + 135 / 64) = 60 / 271 ∧
    min (3 / 2 : ℚ) (60 / 271) = 60 / 271 := by
  norm_num

/-! ## §5 The named infinite family `(f+1) ∣ e²` -/

/-- The divisibility step of the thick case: `(f+1) ∣ e²`, `gcd(e,f) = 1`, `k = f − e ≥ 2` ⟹
`2(f+1) ≤ (k+1)²`.  (`e ≡ −(k+1) mod (f+1)`, so `(f+1) ∣ (k+1)²`; quotient `1` forces
`f = k(k+2)`, `e = k(k+1)`, `gcd = k ≥ 2`.) -/
theorem two_mul_le_sq {e f k : ℕ} (hcop : Nat.Coprime e f) (hk : e + k = f) (hk2 : 2 ≤ k)
    (hdvd : (f + 1) ∣ e ^ 2) : 2 * (f + 1) ≤ (k + 1) ^ 2 := by
  have hdz : ((f : ℤ) + 1) ∣ ((k : ℤ) + 1) ^ 2 := by
    have h1 : ((f : ℤ) + 1) ∣ (e : ℤ) ^ 2 := by exact_mod_cast hdvd
    have h2 : ((k : ℤ) + 1) ^ 2 = (e : ℤ) ^ 2 + ((f : ℤ) + 1) * ((k : ℤ) + 1 - e) := by
      have : (f : ℤ) = e + k := by exact_mod_cast hk.symm
      rw [this]; ring
    rw [h2]; exact dvd_add h1 (dvd_mul_right _ _)
  have hdn : (f + 1) ∣ (k + 1) ^ 2 := by exact_mod_cast hdz
  obtain ⟨m, hm⟩ := hdn
  rcases Nat.lt_or_ge m 2 with h | h
  · exfalso
    interval_cases m
    · simp at hm
    · -- f + 1 = (k+1)², so f = k(k+2), e = k(k+1): k ∣ gcd e f = 1
      have hf : f = k * (k + 2) := by nlinarith
      have he : e = k * (k + 1) := by
        have : e + k = k * (k + 2) := by rw [hk, hf]
        nlinarith
      have hke : k ∣ e := ⟨k + 1, he⟩
      have hkf : k ∣ f := ⟨k + 2, hf⟩
      have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hke hcop) hkf
      omega
  · rw [hm]; nlinarith

/-- **Thick polynomial core.**  `e = f − k`, `b = k(2f − k)`, with `2 ≤ k`, `2(f+1) ≤ (k+1)²`,
`5k ≤ 2f`: `e²f²(b + f²)² + e⁴b² < (f+1)²b⁴`. -/
theorem thick_poly {f k e b : ℝ} (he : e = f - k) (hb : b = k * (2 * f - k)) (hk2 : 2 ≤ k)
    (hdiv : 2 * (f + 1) ≤ (k + 1) ^ 2) (h52 : 5 * k ≤ 2 * f) :
    e ^ 2 * f ^ 2 * (b + f ^ 2) ^ 2 + e ^ 4 * b ^ 2 < (f + 1) ^ 2 * b ^ 4 := by
  have hf : 5 ≤ f := by linarith
  have hf0 : 0 < f := by linarith
  have he0 : 0 < e := by rw [he]; linarith
  have hef : e < f := by rw [he]; linarith
  have hb1 : 8 / 5 * k * f ≤ b := by
    rw [hb]; nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ k) (by linarith : (0 : ℝ) ≤ 2 * f - 5 * k)]
  have hk2' : 6 / 5 * f + 1 ≤ k ^ 2 := by nlinarith
  have hkf : 0 ≤ 8 / 5 * k * f := by positivity
  have hbpos : 0 < b := by nlinarith
  have hB : 3 * f ^ 3 ≤ b ^ 2 := by
    have h1 : (8 / 5 * k * f) ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hkf hb1 2
    have h2 : (6 / 5 * f + 1) * f ^ 2 ≤ k ^ 2 * f ^ 2 :=
      mul_le_mul_of_nonneg_right hk2' (sq_nonneg f)
    have h3 : (8 / 5 * k * f) ^ 2 = 64 / 25 * (k ^ 2 * f ^ 2) := by ring
    have h4 : 0 ≤ f ^ 2 := sq_nonneg f
    have h5 : 0 ≤ f ^ 3 := by positivity
    nlinarith
  have hbe : b = f ^ 2 - e ^ 2 := by rw [hb, he]; ring
  have he2 : e ^ 2 < f ^ 2 := by nlinarith
  have hbc : b + f ^ 2 < 2 * f ^ 2 := by rw [hbe]; nlinarith
  have hbc0 : 0 < b + f ^ 2 := by positivity
  have t1 : e ^ 2 * f ^ 2 * (b + f ^ 2) ^ 2 < 4 * f ^ 8 := by
    have a2 : (b + f ^ 2) ^ 2 < (2 * f ^ 2) ^ 2 := pow_lt_pow_left₀ hbc hbc0.le two_ne_zero
    have a3 : e ^ 2 * (f ^ 2 * (b + f ^ 2) ^ 2) ≤ f ^ 2 * (f ^ 2 * (b + f ^ 2) ^ 2) :=
      mul_le_mul_of_nonneg_right he2.le (by positivity)
    have a4 : f ^ 2 * f ^ 2 * (b + f ^ 2) ^ 2 < f ^ 2 * f ^ 2 * (2 * f ^ 2) ^ 2 :=
      mul_lt_mul_of_pos_left a2 (by positivity)
    have : f ^ 2 * f ^ 2 * (2 * f ^ 2) ^ 2 = 4 * f ^ 8 := by ring
    nlinarith
  have t2 : e ^ 4 * b ^ 2 ≤ f ^ 4 * b ^ 2 := by
    have : e ^ 4 ≤ f ^ 4 := pow_le_pow_left₀ he0.le hef.le 4
    exact mul_le_mul_of_nonneg_right this (sq_nonneg b)
  have t3 : 4 * f ^ 8 + f ^ 4 * b ^ 2 ≤ f ^ 2 * b ^ 4 := by
    have hf3 : f ^ 2 ≤ 3 * f ^ 3 := by nlinarith
    have s1 : 3 * f ^ 3 * (3 * f ^ 3 - f ^ 2) ≤ b ^ 2 * (b ^ 2 - f ^ 2) :=
      mul_le_mul hB (by linarith) (by linarith) (by positivity)
    have s2 : 4 * f ^ 6 ≤ 3 * f ^ 3 * (3 * f ^ 3 - f ^ 2) := by
      have : 3 * f ^ 5 ≤ 5 * f ^ 6 := by
        have : f ^ 5 ≤ f ^ 6 := pow_le_pow_right₀ (by linarith) (by norm_num)
        have : 0 ≤ f ^ 6 := by positivity
        linarith
      nlinarith
    have s3 : 4 * f ^ 6 + f ^ 2 * b ^ 2 ≤ b ^ 4 := by nlinarith
    have := mul_le_mul_of_nonneg_left s3 (sq_nonneg f)
    nlinarith
  have t4 : f ^ 2 * b ^ 4 < (f + 1) ^ 2 * b ^ 4 := by
    have : 0 < b ^ 4 := by positivity
    have : f ^ 2 < (f + 1) ^ 2 := by nlinarith
    exact mul_lt_mul_of_pos_right this (by positivity)
  linarith

/-- **Thin polynomial core** (`ℓ = a = ef`, no divisibility needed):
`e²f²(ef + f²)² + e⁴b² < (f+1)²b²(ef)²`, `b = f² − e²`, for `0 < e`, `e + 1 ≤ f`. -/
theorem thin_poly {e f : ℝ} (he : 0 < e) (hef : e + 1 ≤ f) :
    e ^ 2 * f ^ 2 * (e * f + f ^ 2) ^ 2 + e ^ 4 * (f ^ 2 - e ^ 2) ^ 2
      < (f + 1) ^ 2 * (f ^ 2 - e ^ 2) ^ 2 * (e * f) ^ 2 := by
  have hf : 0 < f := by linarith
  have hk : 1 ≤ f - e := by linarith
  -- factor: both sides carry e²(f+e)²
  have hid1 : e ^ 2 * f ^ 2 * (e * f + f ^ 2) ^ 2 + e ^ 4 * (f ^ 2 - e ^ 2) ^ 2
      = e ^ 2 * (f + e) ^ 2 * (f ^ 4 + e ^ 2 * (f - e) ^ 2) := by ring
  have hid2 : (f + 1) ^ 2 * (f ^ 2 - e ^ 2) ^ 2 * (e * f) ^ 2
      = e ^ 2 * (f + e) ^ 2 * ((f + 1) ^ 2 * (f - e) ^ 2 * f ^ 2) := by ring
  rw [hid1, hid2]
  have hpos : 0 < e ^ 2 * (f + e) ^ 2 := by positivity
  apply mul_lt_mul_of_pos_left _ hpos
  have hk2 : 1 ≤ (f - e) ^ 2 := by nlinarith
  have a1 : e ^ 2 * (f - e) ^ 2 < f ^ 2 * (f - e) ^ 2 := by
    have : e ^ 2 < f ^ 2 := by nlinarith
    nlinarith
  have a2 : f ^ 4 + f ^ 2 * (f - e) ^ 2 ≤ (f + 1) ^ 2 * (f - e) ^ 2 * f ^ 2 := by
    have : f ^ 2 ≤ (f ^ 2 + 2 * f) * (f - e) ^ 2 := by nlinarith
    nlinarith
  linarith

/-- The identity behind (2) for the family: with `h² = e⁴C/(f+1)²` (`h = (e²/(f+1))·cos x`,
`C = cos²x`) and `H² = b²e²C/f²`, `H²ℓ² − h²((ℓ+L)² + H²) = (C e²/(f²(f+1)²))·KEY` where
`KEY = (f+1)²b²ℓ² − e²f²(ℓ+L)² − e⁴b²C`. -/
theorem cond2_sq_of_key {e f b ℓ L C : ℝ} (he : 0 < e) (hf : 0 < f) (hC : 0 < C)
    (hkey : 0 < (f + 1) ^ 2 * b ^ 2 * ℓ ^ 2 - e ^ 2 * f ^ 2 * (ℓ + L) ^ 2 - e ^ 4 * b ^ 2 * C) :
    (e ^ 2 / (f + 1)) ^ 2 * C * ((ℓ + L) ^ 2 + b ^ 2 * e ^ 2 * C / f ^ 2)
      < b ^ 2 * e ^ 2 * C / f ^ 2 * ℓ ^ 2 := by
  rw [← sub_pos]
  have hf1 : (f + 1) ≠ 0 := by positivity
  have hid : b ^ 2 * e ^ 2 * C / f ^ 2 * ℓ ^ 2
      - (e ^ 2 / (f + 1)) ^ 2 * C * ((ℓ + L) ^ 2 + b ^ 2 * e ^ 2 * C / f ^ 2)
      = C * e ^ 2 / (f ^ 2 * (f + 1) ^ 2) *
        ((f + 1) ^ 2 * b ^ 2 * ℓ ^ 2 - e ^ 2 * f ^ 2 * (ℓ + L) ^ 2 - e ^ 4 * b ^ 2 * C) := by
    field_simp; ring
  rw [hid]; positivity

/-- NB's two conclusions from `2h < ℓ` and the polynomial `KEY > 0` (small-context helper of
`family_nb`): `h² = δ²C` with `δ = e²/(f+1)`, `H² = b²e²C/f²`, `cg² = cos²(γ/2) = (2f−e)/(4f)`. -/
theorem nb_finish {e f b h H C cg ℓ : ℝ} (he : 0 < e) (hf : 0 < f) (hef : e ≤ f) (hh0 : 0 ≤ h)
    (hhsq : h ^ 2 = (e ^ 2 / (f + 1)) ^ 2 * C) (hC : 0 < C) (hg : cg ^ 2 = (2 * f - e) / (4 * f))
    (hgpos : 0 < cg) (hHsq : H ^ 2 = b ^ 2 * e ^ 2 * C / f ^ 2) (hH : 0 ≤ H) (hℓ : 0 < ℓ)
    (h2ℓ : 2 * h < ℓ)
    (hkey : 0 < (f + 1) ^ 2 * b ^ 2 * ℓ ^ 2 - e ^ 2 * f ^ 2 * (ℓ + f ^ 2) ^ 2 - e ^ 4 * b ^ 2 * C) :
    h < ℓ * cg ∧ h * (1 + f ^ 2 / ℓ) < H * √(1 - h ^ 2 / ℓ ^ 2) := by
  constructor
  · rw [cond1_iff_sq hh0 hℓ hgpos, hg]
    have q : 1 / 4 ≤ (2 * f - e) / (4 * f) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have q2 : ℓ ^ 2 * (1 / 4) ≤ ℓ ^ 2 * ((2 * f - e) / (4 * f)) :=
      mul_le_mul_of_nonneg_left q (sq_nonneg _)
    have q3 : (2 * h) ^ 2 < ℓ ^ 2 := pow_lt_pow_left₀ h2ℓ (by linarith) two_ne_zero
    nlinarith
  · apply cond2_of_sq hh0 hℓ (by positivity) hH (by linarith)
    rw [hhsq, hHsq]
    exact cond2_sq_of_key he hf hC hkey

/-- `5k ≤ 2f` in the thick case: `k(2f − k) ≤ (f − k)f` (i.e. `b ≤ a`) with `0 ≤ k ≤ f`. -/
theorem thick_k_bound {f k : ℝ} (hk0 : 0 ≤ k) (hkf : k ≤ f) (hthick : k * (2 * f - k) ≤ (f - k) * f) :
    5 * k ≤ 2 * f := by
  by_contra hcon; push Not at hcon
  nlinarith [mul_pos (by linarith : (0 : ℝ) < 5 * k - 2 * f) (by linarith : (0 : ℝ) < 13 * f - 5 * k)]

/-- **The family lemma (R5), real form.**  Coprime `2 ≤ e ≤ f − 2` with `(f+1) ∣ e²`; `x = α/2`
(`sin x = e/(2f)`, `0 < x < π/2`); the survivor distance `δ = e²/(f+1)` along `r`, height
`h = δ·cos(α/2)`.  Then NB's (1) and (2) hold: `h < ℓ·cos(γ/2)` and
`h·(1 + L/ℓ) < H·√(1 − h²/ℓ²)`, with `ℓ = min(ef, f²−e²)`, `L = f²`, `H = (f²−e²)·sin α`.
Thin (`a ≤ b`) needs only `δ < e²/f` (`thin_poly`); thick (`b < a`) uses `(f+1) ∣ e²` through
`two_mul_le_sq` (`thick_poly`) — the reviewer's repaired proof. -/
theorem family_nb {e f : ℕ} (hcop : Nat.Coprime e f) (he : 2 ≤ e) (hef : e + 2 ≤ f)
    (hdvd : (f + 1) ∣ e ^ 2) {x : ℝ} (hs : sin x = e / (2 * f)) (hx0 : 0 < x) (hx1 : x < π / 2) :
    (e ^ 2 / (f + 1) * cos x : ℝ) < min ((e : ℝ) * f) ((f : ℝ) ^ 2 - e ^ 2) * cos ((π / 2 + x) / 2) ∧
    (e ^ 2 / (f + 1) * cos x : ℝ) * (1 + (f : ℝ) ^ 2 / min ((e : ℝ) * f) ((f : ℝ) ^ 2 - e ^ 2))
      < (((f : ℝ) ^ 2 - e ^ 2) * sin (2 * x)) *
        √(1 - (e ^ 2 / (f + 1) * cos x : ℝ) ^ 2 / min ((e : ℝ) * f) ((f : ℝ) ^ 2 - e ^ 2) ^ 2) := by
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast he
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast hef
  have hfR : (0 : ℝ) < f := by linarith
  have hf0 : (f : ℝ) ≠ 0 := hfR.ne'
  have hc : 0 < cos x := cos_pos_of_mem_Ioo ⟨by linarith, hx1⟩
  have hC : cos x ^ 2 = (4 * f ^ 2 - e ^ 2) / (4 * f ^ 2) := cos_sq_half hf0 hs
  have hC0 : 0 < cos x ^ 2 := by positivity
  have hC1 : cos x ^ 2 ≤ 1 := by rw [← cos_sq_add_sin_sq x]; nlinarith [sq_nonneg (sin x)]
  have hg := cos_sq_gamma_half hf0 hs
  have hgpos := cos_gamma_half_pos hx0 hx1
  have hsin2 : 0 < sin (2 * x) := by
    rw [sin_two_mul]
    have : 0 < sin x := by rw [hs]; positivity
    positivity
  have hb0 : 0 < (f : ℝ) ^ 2 - e ^ 2 := by nlinarith
  have hHsq : (((f : ℝ) ^ 2 - e ^ 2) * sin (2 * x)) ^ 2
      = ((f : ℝ) ^ 2 - e ^ 2) ^ 2 * e ^ 2 * cos x ^ 2 / f ^ 2 := by
    rw [H_sq hf0 hs, hC]; field_simp
  have hhsq : (e ^ 2 / (f + 1) * cos x : ℝ) ^ 2 = (e ^ 2 / (f + 1)) ^ 2 * cos x ^ 2 := by
    rw [mul_pow]
  have hh0 : (0 : ℝ) ≤ e ^ 2 / (f + 1) * cos x := by positivity
  have hδ1 : (e : ℝ) ^ 2 / (f + 1) ≤ e ^ 2 / f :=
    div_le_div_of_nonneg_left (by positivity) hfR (by linarith)
  have hhδ : (e ^ 2 / (f + 1) * cos x : ℝ) ≤ e ^ 2 / f := by
    have : cos x ≤ 1 := cos_le_one x
    have : (0 : ℝ) ≤ e ^ 2 / (f + 1) := by positivity
    nlinarith
  have hH0 : 0 ≤ ((f : ℝ) ^ 2 - e ^ 2) * sin (2 * x) := by positivity
  have fin := fun ℓ hℓ h2ℓ hkey =>
    nb_finish (e := (e : ℝ)) (f := f) (b := (f : ℝ) ^ 2 - e ^ 2) (C := cos x ^ 2)
      (ℓ := ℓ) (by linarith) hfR (by linarith) hh0 hhsq hC0 hg hgpos hHsq hH0 hℓ h2ℓ hkey
  rcases le_total ((e : ℝ) * f) ((f : ℝ) ^ 2 - e ^ 2) with hthin | hthick
  · -- thin: ℓ = a = ef
    rw [min_eq_left hthin]
    apply fin _ (by positivity)
    · have : 2 * ((e : ℝ) ^ 2 / f) < e * f := by
        rw [← mul_div_assoc, div_lt_iff₀ hfR]; nlinarith
      linarith
    · have hp := thin_poly (e := (e : ℝ)) (f := f) (by linarith) (by linarith)
      have : (e : ℝ) ^ 4 * ((f : ℝ) ^ 2 - e ^ 2) ^ 2 * cos x ^ 2
          ≤ (e : ℝ) ^ 4 * ((f : ℝ) ^ 2 - e ^ 2) ^ 2 :=
        mul_le_of_le_one_right (by positivity) hC1
      linarith
  · -- thick: ℓ = b = f² − e²
    rw [min_eq_right hthick]
    obtain ⟨k, hk⟩ : ∃ k, e + k = f := ⟨f - e, by omega⟩
    have hk2 : 2 ≤ k := by omega
    have hdiv := two_mul_le_sq hcop hk hk2 hdvd
    have hkR : (f : ℝ) = e + k := by exact_mod_cast hk.symm
    have hdivR : 2 * ((f : ℝ) + 1) ≤ ((k : ℝ) + 1) ^ 2 := by exact_mod_cast hdiv
    have hk2R : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    have hek : (e : ℝ) = f - k := by linarith
    have hbk : (f : ℝ) ^ 2 - e ^ 2 = k * (2 * f - k) := by rw [hek]; ring
    have h52 : 5 * (k : ℝ) ≤ 2 * f := by
      apply thick_k_bound (by linarith) (by linarith)
      rw [← hbk, ← hek]; linarith
    apply fin _ hb0
    · have q1 : (k : ℝ) * (8 / 5 * f) ≤ k * (2 * f - k) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      have q2 : 2 * (8 / 5 * (f : ℝ)) ≤ (k : ℝ) * (8 / 5 * f) :=
        mul_le_mul_of_nonneg_right hk2R (by positivity)
      have : 3 * (f : ℝ) < (f : ℝ) ^ 2 - e ^ 2 := by rw [hbk]; linarith
      have he2 : (e : ℝ) ^ 2 < f ^ 2 := pow_lt_pow_left₀ (by linarith) (by positivity) two_ne_zero
      have : (e : ℝ) ^ 2 / f < f := by
        rw [div_lt_iff₀ hfR]; have := sq (f : ℝ); linarith
      linarith
    · have hp := thick_poly (f := (f : ℝ)) (k := k) hek hbk hk2R hdivR h52
      have : (e : ℝ) ^ 4 * ((f : ℝ) ^ 2 - e ^ 2) ^ 2 * cos x ^ 2
          ≤ (e : ℝ) ^ 4 * ((f : ℝ) ^ 2 - e ^ 2) ^ 2 :=
        mul_le_of_le_one_right (by positivity) hC1
      have hb4 : ((f : ℝ) ^ 2 - e ^ 2) ^ 2 * ((f : ℝ) ^ 2 - e ^ 2) ^ 2
          = ((f : ℝ) ^ 2 - e ^ 2) ^ 4 := by ring
      linarith

/-! ## §6 Witnesses (vacuity rule): family members exist, thin and thick -/

/-- `(4,7)` (`N = 131`, thin), `(3,8)` (thin), `(12,17)` (thick: `b = 145 < a = 204`) satisfy every
hypothesis of `family_nb` (coprime, `2 ≤ e ≤ f − 2`, `(f+1) ∣ e²`); the angle hypothesis is
`exists_half_angle`. -/
theorem family_witnesses :
    (Nat.Coprime 4 7 ∧ 2 ≤ 4 ∧ 4 + 2 ≤ 7 ∧ (7 + 1) ∣ 4 ^ 2) ∧
    (Nat.Coprime 3 8 ∧ 2 ≤ 3 ∧ 3 + 2 ≤ 8 ∧ (8 + 1) ∣ 3 ^ 2) ∧
    (Nat.Coprime 12 17 ∧ 2 ≤ 12 ∧ 12 + 2 ≤ 17 ∧ (17 + 1) ∣ 12 ^ 2 ∧ 17 ^ 2 - 12 ^ 2 < 12 * 17) := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

/-- `two_mul_le_sq` needs coprimality: at `(e,f) = (6,8)` (`k = 2`, `gcd = 2`), `9 ∣ 36` and
`2·9 > 9`.  (This is the `j′ = 1` case the reviewer excludes.) -/
theorem two_mul_le_sq_needs_coprime :
    (8 + 1) ∣ 6 ^ 2 ∧ 6 + 2 = 8 ∧ ¬ (2 * (8 + 1) ≤ (2 + 1) ^ 2) ∧ ¬ Nat.Coprime 6 8 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

end Erdos634.Draft.NearBase

#print axioms Erdos634.Draft.NearBase.cond1_iff_sq
#print axioms Erdos634.Draft.NearBase.cond2_of_sq
#print axioms Erdos634.Draft.NearBase.sq_of_cond2
#print axioms Erdos634.Draft.NearBase.h2_sq
#print axioms Erdos634.Draft.NearBase.gamma_eq
#print axioms Erdos634.Draft.NearBase.cos_sq_half
#print axioms Erdos634.Draft.NearBase.cos_sq_gamma_half
#print axioms Erdos634.Draft.NearBase.cos_gamma_half_pos
#print axioms Erdos634.Draft.NearBase.H_sq
#print axioms Erdos634.Draft.NearBase.H_eq_two_area_div
#print axioms Erdos634.Draft.NearBase.c_longest
#print axioms Erdos634.Draft.NearBase.exists_half_angle
#print axioms Erdos634.Draft.NearBase.h_sq_47
#print axioms Erdos634.Draft.NearBase.H_sq_47
#print axioms Erdos634.Draft.NearBase.margins_47
#print axioms Erdos634.Draft.NearBase.nb_holds_47
#print axioms Erdos634.Draft.NearBase.tile234_threshold
#print axioms Erdos634.Draft.NearBase.two_mul_le_sq
#print axioms Erdos634.Draft.NearBase.thick_poly
#print axioms Erdos634.Draft.NearBase.thin_poly
#print axioms Erdos634.Draft.NearBase.cond2_sq_of_key
#print axioms Erdos634.Draft.NearBase.family_nb
#print axioms Erdos634.Draft.NearBase.family_witnesses
#print axioms Erdos634.Draft.NearBase.nb_finish
#print axioms Erdos634.Draft.NearBase.thick_k_bound
#print axioms Erdos634.Draft.NearBase.two_mul_le_sq_needs_coprime
