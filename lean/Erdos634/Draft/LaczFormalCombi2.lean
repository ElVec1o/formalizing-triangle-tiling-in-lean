-- Draft/LaczFormalCombi2.lean -- the ARITHMETIC CORES of Laczkovich, DCG 48 (2012), Lemma 3.8 (cases s/m = 2/3 and 3/4), Lemma 3.9
-- (last step) and the 'only if' arithmetic of Cor 3.7.  No tiling is involved: these are exactly the field computations
-- ("comparing the areas") the printed proofs perform AFTER the geometric inputs [1, Thm 2] / [1, Thm 23] of
-- Combinatorica 10 (1990) have been used; the geometric inputs themselves are NOT proved here (see (private working notes, not included)).
-- NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Comput. Geom. 48 (2012) 330-372, Lemmas 3.8, 3.9, Cor 3.7; Combinatorica 10 (1990)), Beeson, Beeson-Zhang.
import Mathlib

open scoped Classical

namespace Erdos634.Laczkovich.Combi2

/-! ### Cor 3.7, 'only if' arithmetic -/

/-- If a rectangle with side ratio `(m/n) (a/b)` is a square, then `a/b` is rational (`a * n = b * m`). -/
theorem cor37_only_if_arith {a b W H : ℝ} (hb : 0 < b) (hH : 0 < H) (m n : ℕ) (hn : 0 < n)
    (hratio : W / H = (m / n) * (a / b)) (hsq : W = H) : a / b = (n : ℝ) / m ∨ m = 0 := by
  by_cases hm : m = 0
  · exact Or.inr hm
  left
  have h1 : (1 : ℝ) = (m / n) * (a / b) := by rw [← hratio, hsq, div_self hH.ne']
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp at h1 ⊢
  linarith

/-- linear independence of `1, d` over `Q` for irrational `d`. -/
theorem irr_lin {d : ℝ} (hd : Irrational d) (r s : ℚ) (h : (r : ℝ) + s * d = 0) : r = 0 ∧ s = 0 := by
  by_cases hs : s = 0
  · subst hs
    simp at h
    exact ⟨by exact_mod_cast h, rfl⟩
  · exfalso
    apply hd
    refine ⟨-r / s, ?_⟩
    have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs
    push_cast
    field_simp
    linarith

/-! ### Lemma 3.8, case `s/m = 2/3` (`alpha = pi/3`, sides `1, 2, sqrt 3`) -/

/-- `(x sqrt3 + y)(z sqrt3 + u) = (t/2) sqrt3` with naturals and `t > 0`  ==>  `x = u = 0` or `y = z = 0`
(one side an integer multiple of `sin alpha = sqrt3/2`, the other of `cos alpha = 1/2`). -/
theorem lem38_case23 (x y z u t : ℕ) (ht : 0 < t)
    (h : ((x : ℝ) * Real.sqrt 3 + y) * ((z : ℝ) * Real.sqrt 3 + u) = (t / 2) * Real.sqrt 3) :
    (x = 0 ∧ u = 0) ∨ (y = 0 ∧ z = 0) := by
  have hirr : Irrational (Real.sqrt 3) := by
    have := (Nat.Prime.irrational_sqrt (p := 3) (by norm_num)); simpa using this
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have key : (((3 * x * z + y * u : ℚ)) : ℝ) + (((x * u + y * z - t / 2 : ℚ)) : ℝ) * Real.sqrt 3 = 0 := by
    push_cast
    linear_combination h - ((x : ℝ) * z) * h3
  obtain ⟨hr, hq⟩ := irr_lin hirr _ _ key
  have hxz : x * z = 0 := by
    have : ((3 * x * z + y * u : ℚ)) = 0 := hr
    have h' : (3 * (x * z) + y * u : ℕ) = 0 := by
      have : ((3 * (x * z) + y * u : ℕ) : ℚ) = 0 := by push_cast; linarith
      exact_mod_cast this
    omega
  have hyu : y * u = 0 := by
    have : ((3 * x * z + y * u : ℚ)) = 0 := hr
    have h' : (3 * (x * z) + y * u : ℕ) = 0 := by
      have : ((3 * (x * z) + y * u : ℕ) : ℚ) = 0 := by push_cast; linarith
      exact_mod_cast this
    omega
  have hxuyz : 2 * (x * u + y * z) = t := by
    have h1 : ((2 * (x * u + y * z) : ℕ) : ℚ) = t := by push_cast; linarith
    exact_mod_cast h1
  rcases Nat.mul_eq_zero.mp hxz with hx | hz <;> rcases Nat.mul_eq_zero.mp hyu with hy | hu
  · subst hx; subst hy; simp at hxuyz; omega
  · subst hx; exact Or.inl ⟨rfl, hu⟩
  · subst hz; exact Or.inr ⟨hy, rfl⟩
  · subst hz; subst hu; simp at hxuyz; omega

/-! ### Lemma 3.8, case `s/m = 3/4` (`alpha = 3 pi/8`, sides `sin alpha, cos alpha, 1`) -/

section c34
variable {c s : ℝ}

/-- a rational with square `32` does not exist. -/
theorem no_sq32 (w : ℚ) : w ^ 2 ≠ 32 := by
  intro hw
  have hirr : Irrational (Real.sqrt 2) := irrational_sqrt_two
  apply hirr
  refine ⟨|w| / 4, ?_⟩
  have h2 : ((|w| / 4 : ℚ) : ℝ) ^ 2 = 2 := by
    push_cast
    rw [div_pow, sq_abs]
    have : (w : ℝ) ^ 2 = 32 := by exact_mod_cast hw
    rw [this]; norm_num
  exact (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg 2)).mp (by rw [h2, Real.sq_sqrt (by norm_num)])

/-- `cos alpha` is not in `Q(sqrt 2)`: `c^2 = (2 - sqrt 2)/4` has no square root `p + q sqrt 2`. -/
theorem c_irr (hc2 : c ^ 2 = (2 - Real.sqrt 2) / 4) : ¬ ∃ p q : ℚ, c = p + q * Real.sqrt 2 := by
  rintro ⟨p, q, hpq⟩
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hirr : Irrational (Real.sqrt 2) := irrational_sqrt_two
  have e : ((p ^ 2 + 2 * q ^ 2 - 1 / 2 : ℚ) : ℝ) + ((2 * p * q + 1 / 4 : ℚ) : ℝ) * Real.sqrt 2 = 0 := by
    have := hc2; rw [hpq] at this; push_cast; nlinarith [h2]
  obtain ⟨ha, hb⟩ := irr_lin hirr _ _ e
  have hq2 : (2 * p * q) ^ 2 = 1 / 16 := by
    rw [show 2 * p * q = -1 / 4 by linarith]; norm_num
  have hw : (32 * p ^ 2 - 8) ^ 2 = 32 := by
    linear_combination (1024 * p ^ 2) * ha - 512 * hq2
  exact no_sq32 _ hw

/-- `1, c` are linearly independent over `Q(sqrt 2)` (coefficients written `alpha + beta sqrt 2`, rational). -/
theorem lin_indep (hc2 : c ^ 2 = (2 - Real.sqrt 2) / 4) (α β γ δ : ℚ)
    (h : (α : ℝ) + β * Real.sqrt 2 + ((γ : ℝ) + δ * Real.sqrt 2) * c = 0) :
    α = 0 ∧ β = 0 ∧ γ = 0 ∧ δ = 0 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hirr : Irrational (Real.sqrt 2) := irrational_sqrt_two
  by_cases hg : (γ : ℝ) + δ * Real.sqrt 2 = 0
  · obtain ⟨rfl, rfl⟩ := irr_lin hirr γ δ hg
    have h' : (α : ℝ) + β * Real.sqrt 2 = 0 := by simpa using h
    obtain ⟨h1, h2'⟩ := irr_lin hirr α β h'
    exact ⟨h1, h2', rfl, rfl⟩
  · exfalso
    apply c_irr hc2
    have hD : ((γ ^ 2 - 2 * δ ^ 2 : ℚ) : ℝ) ≠ 0 := by
      intro h0
      have h0' : (γ : ℝ) ^ 2 - 2 * (δ : ℝ) ^ 2 = 0 := by push_cast at h0; exact h0
      have hm : ((γ : ℝ) + δ * Real.sqrt 2) * ((γ : ℝ) - δ * Real.sqrt 2) = 0 := by
        linear_combination h0' - (δ : ℝ) ^ 2 * h2
      rcases mul_eq_zero.mp hm with h1 | h1
      · exact hg h1
      · have : (γ : ℝ) + (-δ : ℚ) * Real.sqrt 2 = 0 := by push_cast; linarith
        obtain ⟨r1, r2⟩ := irr_lin hirr γ (-δ) this
        apply hg
        have : δ = 0 := by linarith
        subst this; simp [r1]
    have e2 : (((α * γ - 2 * β * δ : ℚ)) : ℝ) + ((β * γ - α * δ : ℚ) : ℝ) * Real.sqrt 2
        + ((γ ^ 2 - 2 * δ ^ 2 : ℚ) : ℝ) * c = 0 := by
      push_cast
      linear_combination ((γ : ℝ) - δ * Real.sqrt 2) * h + ((β : ℝ) * δ + (δ : ℝ) ^ 2 * c) * h2
    refine ⟨-(α * γ - 2 * β * δ) / (γ ^ 2 - 2 * δ ^ 2), -(β * γ - α * δ) / (γ ^ 2 - 2 * δ ^ 2), ?_⟩
    have hD' : (γ : ℝ) ^ 2 - 2 * (δ : ℝ) ^ 2 ≠ 0 := by push_cast at hD; exact hD
    push_cast at e2 ⊢
    field_simp
    linarith

/-- **Lemma 3.8, case `s/m = 3/4`, arithmetic core (printed equations (9)-(11)).**  With `c = cos alpha`, `s = sin alpha`,
`alpha = 3 pi/8` (`c^2 = (2 - sqrt 2)/4`, `s = (sqrt 2 + 1) c`), sides `x c + y s + z`, `u c + v s + w` (naturals, not
all zero) and area equation `(x c + y s + z)(u c + v s + w) = (t/2) c s` with `t > 0`:  one side is an integer multiple
of `s`, the other of `c`, and `z = w = 0`. -/
theorem lem38_case34 (hc : 0 < c) (hc2 : c ^ 2 = (2 - Real.sqrt 2) / 4) (hs : s = (Real.sqrt 2 + 1) * c)
    (x y z u v w t : ℕ) (ht : 0 < t) (hA : x + y + z ≠ 0) (hB : u + v + w ≠ 0)
    (h : ((x : ℝ) * c + y * s + z) * ((u : ℝ) * c + v * s + w) = (t / 2) * c * s) :
    (x = 0 ∧ v = 0 ∧ z = 0 ∧ w = 0) ∨ (y = 0 ∧ u = 0 ∧ z = 0 ∧ w = 0) := by
  subst hs
  set r := Real.sqrt 2 with hr
  have h2 : r * r = 2 := Real.mul_self_sqrt (by norm_num)
  have E : (((((2 * ((x + y) * (u + v) + 2 * y * v) - 2 * ((x + y) * v + y * (u + v))) / 4 : ℚ) + z * w : ℚ)) : ℝ)
      + ((((2 * ((x + y) * v + y * (u + v)) - ((x + y) * (u + v) + 2 * y * v)) / 4 - t / 8 : ℚ)) : ℝ) * r
      + (((((x + y) * w + z * (u + v) : ℚ)) : ℝ) + (((y * w + z * v : ℚ)) : ℝ) * r) * c = 0 := by
    push_cast
    linear_combination h - (((x : ℝ) + y) * (u + v) + (((x : ℝ) + y) * v + y * (u + v)) * r + y * v * r ^ 2
        - (t / 2) * (r + 1)) * hc2
      - ((-(((x : ℝ) + y) * v + y * (u + v)) + y * v * (2 - r)) / 4 + t / 8) * h2
  obtain ⟨hα, hβ, hγ, hδ⟩ := lin_indep hc2 _ _ _ _ E
  have hyw : y * w = 0 ∧ z * v = 0 := by
    have : ((y * w + z * v : ℕ) : ℚ) = 0 := by push_cast; exact hδ
    have : y * w + z * v = 0 := by exact_mod_cast this
    omega
  have hxw : (x + y) * w = 0 ∧ z * (u + v) = 0 := by
    have : (((x + y) * w + z * (u + v) : ℕ) : ℚ) = 0 := by push_cast; exact hγ
    have : (x + y) * w + z * (u + v) = 0 := by exact_mod_cast this
    omega
  have hα' : x * u + y * v + 2 * (z * w) = 0 := by
    have : ((x * u + y * v + 2 * (z * w) : ℕ) : ℚ) = 0 := by push_cast; linarith
    exact_mod_cast this
  have hβ' : 2 * (x * v + y * u + y * v) = t + 2 * (x * u) := by
    have : ((2 * (x * v + y * u + y * v) : ℕ) : ℚ) = ((t + 2 * (x * u) : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  have h1 : x * u = 0 := by omega
  have h2' : y * v = 0 := by omega
  have h3 : z * w = 0 := by omega
  obtain ⟨hyw1, hzv⟩ := hyw
  obtain ⟨hxw1, hzu⟩ := hxw
  have hxw2 : x * w = 0 := by nlinarith [Nat.zero_le (x * w), Nat.zero_le (y * w)]
  have hzu2 : z * u = 0 := by nlinarith [Nat.zero_le (z * u), Nat.zero_le (z * v)]
  have hz : z = 0 := by
    by_contra hz
    have hz' : 0 < z := Nat.pos_of_ne_zero hz
    have hu0 : u = 0 := by
      rcases Nat.mul_eq_zero.mp hzu2 with h | h
      · exact absurd h hz
      · exact h
    have hv0 : v = 0 := by
      rcases Nat.mul_eq_zero.mp hzv with h | h
      · exact absurd h hz
      · exact h
    have hw0 : w = 0 := by
      rcases Nat.mul_eq_zero.mp h3 with h | h
      · exact absurd h hz
      · exact h
    omega
  have hw : w = 0 := by
    by_contra hw
    have hw' : 0 < w := Nat.pos_of_ne_zero hw
    have hx0 : x = 0 := by
      rcases Nat.mul_eq_zero.mp hxw2 with h | h
      · exact h
      · exact absurd h hw
    have hy0 : y = 0 := by
      rcases Nat.mul_eq_zero.mp hyw1 with h | h
      · exact h
      · exact absurd h hw
    omega
  subst hz; subst hw
  rcases Nat.mul_eq_zero.mp h1 with hx | hu <;> rcases Nat.mul_eq_zero.mp h2' with hy | hv
  · subst hx; subst hy; simp at hβ'; omega
  · subst hx; exact Or.inl ⟨rfl, hv, rfl, rfl⟩
  · subst hu; exact Or.inr ⟨hy, rfl, rfl, rfl⟩
  · subst hu; subst hv; simp at hβ'; omega

end c34

/-! ### Lemma 3.9, last step (both quadratic fields) -/

/-- **The closing area comparison of Lemma 3.9** (first and second triple).  Tile sides `a, b` with `a/b = d - 1`, `d = sqrt 2`
or `sqrt 3` (`d * d = n`), tile area `a b d / 4`.  If both sides of the rectangle are integer multiples `p sigma_1`, `q sigma_2`
of tile sides `sigma_i in {a, b}`, and the area is `t` tile areas, then `False` ("each of these numbers is irrational"). -/
theorem lem39_area {d a b : ℝ} (hd : Irrational d) (n : ℕ) (hdn : d * d = n) (hb : 0 < b) (ha : 0 < a) (hab : a = (d - 1) * b)
    (p q t : ℕ) (hp : 0 < p) (hq : 0 < q) (ht : 0 < t) (σ₁ σ₂ : ℝ) (h1 : σ₁ = a ∨ σ₁ = b) (h2 : σ₂ = a ∨ σ₂ = b)
    (h : ((p : ℝ) * σ₁) * ((q : ℝ) * σ₂) = t * (a * b * d / 4)) : False := by
  have hP : (0 : ℝ) < (p : ℝ) * q := by positivity
  have hPq : ((p : ℚ) * q) ≠ 0 := by positivity
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] at h
  · -- a, a
    have e1 : (p : ℝ) * q * a = t * b * d / 4 := by
      apply mul_left_cancel₀ ha.ne'
      linear_combination h
    have e2 : (p : ℝ) * q * (d - 1) = t * d / 4 := by
      apply mul_left_cancel₀ hb.ne'
      rw [hab] at e1; linear_combination e1
    have key : ((-(p * q : ℚ) : ℚ) : ℝ) + (((p * q : ℚ) - t / 4 : ℚ) : ℝ) * d = 0 := by
      push_cast; linarith
    have := (irr_lin hd _ _ key).1
    apply hPq; linarith
  · -- a, b
    have e1 : (p : ℝ) * q = t * d / 4 := by
      apply mul_left_cancel₀ (mul_pos ha hb).ne'
      linear_combination h
    have key : ((-(p * q : ℚ) : ℚ) : ℝ) + ((t / 4 : ℚ) : ℝ) * d = 0 := by
      push_cast; linarith
    have := (irr_lin hd _ _ key).1
    apply hPq; linarith
  · -- b, a
    have e1 : (p : ℝ) * q = t * d / 4 := by
      apply mul_left_cancel₀ (mul_pos ha hb).ne'
      linear_combination h
    have key : ((-(p * q : ℚ) : ℚ) : ℝ) + ((t / 4 : ℚ) : ℝ) * d = 0 := by
      push_cast; linarith
    have := (irr_lin hd _ _ key).1
    apply hPq; linarith
  · -- b, b
    have e1 : (p : ℝ) * q * b = t * a * d / 4 := by
      apply mul_left_cancel₀ hb.ne'
      linear_combination h
    have e2 : (p : ℝ) * q = t * (d - 1) * d / 4 := by
      apply mul_left_cancel₀ hb.ne'
      rw [hab] at e1; linear_combination e1
    have key : (((p * q : ℚ) - t * n / 4 : ℚ) : ℝ) + ((t / 4 : ℚ) : ℝ) * d = 0 := by
      push_cast; linear_combination e2 + ((t : ℝ) / 4) * hdn
    have := (irr_lin hd _ _ key).2
    have ht' : ((t : ℚ) / 4) ≠ 0 := by positivity
    exact ht' this

/-- instance for the first triple `(pi/8, 5 pi/8, pi/4)`: `d = sqrt 2`. -/
theorem lem39_area_sqrt2 {a b : ℝ} (hb : 0 < b) (ha : 0 < a) (hab : a = (Real.sqrt 2 - 1) * b)
    (p q t : ℕ) (hp : 0 < p) (hq : 0 < q) (ht : 0 < t) (σ₁ σ₂ : ℝ) (h1 : σ₁ = a ∨ σ₁ = b) (h2 : σ₂ = a ∨ σ₂ = b)
    (h : ((p : ℝ) * σ₁) * ((q : ℝ) * σ₂) = t * (a * b * Real.sqrt 2 / 4)) : False :=
  lem39_area irrational_sqrt_two 2 (by rw [Real.mul_self_sqrt (by norm_num)]; norm_num) hb ha hab p q t hp hq ht σ₁ σ₂ h1 h2 h

/-- instance for the second triple `(pi/4, 5 pi/12, pi/3)`: `d = sqrt 3`. -/
theorem lem39_area_sqrt3 {a b : ℝ} (hb : 0 < b) (ha : 0 < a) (hab : a = (Real.sqrt 3 - 1) * b)
    (p q t : ℕ) (hp : 0 < p) (hq : 0 < q) (ht : 0 < t) (σ₁ σ₂ : ℝ) (h1 : σ₁ = a ∨ σ₁ = b) (h2 : σ₂ = a ∨ σ₂ = b)
    (h : ((p : ℝ) * σ₁) * ((q : ℝ) * σ₂) = t * (a * b * Real.sqrt 3 / 4)) : False :=
  lem39_area (by have := (Nat.Prime.irrational_sqrt (p := 3) (by norm_num)); simpa using this) 3
    (by rw [Real.mul_self_sqrt (by norm_num)]; norm_num) hb ha hab p q t hp hq ht σ₁ σ₂ h1 h2 h

/-! ### Witnesses for `lem38_case23` and `lem38_case34` -/

theorem lem38_case23_witness :
    ∃ x y z u t : ℕ, 0 < t ∧
      ((x : ℝ) * Real.sqrt 3 + y) * ((z : ℝ) * Real.sqrt 3 + u) = (t / 2) * Real.sqrt 3 ∧
      ((x = 0 ∧ u = 0) ∨ (y = 0 ∧ z = 0)) := by
  refine ⟨0, 1, 1, 0, 2, by norm_num, by push_cast; ring, ?_⟩
  exact lem38_case23 0 1 1 0 2 (by norm_num) (by push_cast; ring)

theorem lem38_case34_witness :
    ∃ c s : ℝ, 0 < c ∧ c ^ 2 = (2 - Real.sqrt 2) / 4 ∧ s = (Real.sqrt 2 + 1) * c ∧
      ∃ x y z u v w t : ℕ, 0 < t ∧ x + y + z ≠ 0 ∧ u + v + w ≠ 0 ∧
        ((x : ℝ) * c + y * s + z) * ((u : ℝ) * c + v * s + w) = (t / 2) * c * s ∧
        ((x = 0 ∧ v = 0 ∧ z = 0 ∧ w = 0) ∨ (y = 0 ∧ u = 0 ∧ z = 0 ∧ w = 0)) := by
  have h2 : (0 : ℝ) < 2 - Real.sqrt 2 := by
    have : Real.sqrt 2 < 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  have hc : 0 < Real.sqrt (2 - Real.sqrt 2) / 2 := by positivity
  have hc2 : (Real.sqrt (2 - Real.sqrt 2) / 2) ^ 2 = (2 - Real.sqrt 2) / 4 := by
    rw [div_pow, Real.sq_sqrt h2.le]; norm_num
  refine ⟨_, (Real.sqrt 2 + 1) * (Real.sqrt (2 - Real.sqrt 2) / 2), hc, hc2, rfl, 0, 1, 0, 1, 0, 0, 2, by norm_num,
    by norm_num, by norm_num, by push_cast; ring, ?_⟩
  exact lem38_case34 hc hc2 rfl 0 1 0 1 0 0 2 (by norm_num) (by norm_num) (by norm_num) (by push_cast; ring)

end Erdos634.Laczkovich.Combi2

#print axioms Erdos634.Laczkovich.Combi2.cor37_only_if_arith
#print axioms Erdos634.Laczkovich.Combi2.lem38_case23
#print axioms Erdos634.Laczkovich.Combi2.lem38_case34
#print axioms Erdos634.Laczkovich.Combi2.lem39_area_sqrt2
#print axioms Erdos634.Laczkovich.Combi2.lem39_area_sqrt3
#print axioms Erdos634.Laczkovich.Combi2.lem38_case23_witness
#print axioms Erdos634.Laczkovich.Combi2.lem38_case34_witness
