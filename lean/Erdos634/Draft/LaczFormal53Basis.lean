import Mathlib

/-!
# Laczkovich Thm 5.3, case (vii): the algebra of `Q(sqrt 2, sin (pi/8))` (basis `1, sqrt2, u, sqrt2 u`)

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Thm 5.3; the printed proof treats (iv), (v) and says
"similar arguments apply" for (vi), (vii)), Beeson, Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.

`u = sin (pi/8)`, `u^2 = (2 - sqrt2)/4`.  `1, sqrt2, u, sqrt2 u` are `Q`-linearly independent (`E4.ev_eq_zero`).  `E4` is the
coefficient tuple, `E4.mul` its product, `E4.ev_mul` the ring-hom property.  Also: `x^2 = 2 y^2` over `Q` forces `y = 0`.
-/

namespace Erdos634.Lacz53

open Real

/-- `x^2 = 2 y^2` has only the trivial rational solution (irrationality of `sqrt 2`). -/
theorem sq_eq_two_sq {x y : ℚ} (h : x ^ 2 = 2 * y ^ 2) : y = 0 := by
  by_contra hy
  have h2 : (((x / y : ℚ)) : ℝ) ^ 2 = 2 := by
    push_cast
    have hy' : (y : ℝ) ≠ 0 := by exact_mod_cast hy
    field_simp
    have h' : x ^ 2 = y ^ 2 * 2 := by linarith
    exact_mod_cast h'
  have h3 : Real.sqrt 2 = |((x / y : ℚ) : ℝ)| := by
    rw [← h2]; exact Real.sqrt_sq_eq_abs _
  apply irrational_sqrt_two
  refine ⟨|x / y|, ?_⟩
  rw [h3]; push_cast; rfl

/-- `p + q sqrt2 = 0` over `Q` forces `p = q = 0`. -/
theorem pq_zero {p q : ℚ} (h : (p : ℝ) + q * Real.sqrt 2 = 0) : p = 0 ∧ q = 0 := by
  have hq : q = 0 := by
    by_contra hq
    apply irrational_sqrt_two
    refine ⟨-p / q, ?_⟩
    have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
    push_cast
    field_simp
    linarith
  refine ⟨?_, hq⟩
  rw [hq] at h; simpa using h

/-- `u = sin (pi/8)`. -/
noncomputable def uu : ℝ := Real.sin (Real.pi / 8)

theorem s2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem uu_sq : uu ^ 2 = (2 - Real.sqrt 2) / 4 := by
  unfold uu
  rw [Real.sin_pi_div_eight, div_pow, Real.sq_sqrt]
  · norm_num
  · have : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    linarith

theorem uu_pos : 0 < uu := by
  unfold uu
  apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
  linarith [Real.pi_pos]

/-- `u` is not in `Q(sqrt2)`. -/
theorem uu_not_mem {p q : ℚ} : uu ≠ p + q * Real.sqrt 2 := by
  intro h
  have hs := s2_sq
  have hu := uu_sq
  have e : (p : ℝ) ^ 2 + 2 * q ^ 2 + 2 * p * q * Real.sqrt 2 = 1 / 2 - (1 / 4) * Real.sqrt 2 := by
    have : uu ^ 2 = ((p : ℝ) + q * Real.sqrt 2) ^ 2 := by rw [h]
    nlinarith [this, hu, hs]
  have e1 : ((p ^ 2 + 2 * q ^ 2 - 1 / 2 : ℚ) : ℝ) + ((2 * p * q + 1 / 4 : ℚ) : ℝ) * Real.sqrt 2 = 0 := by
    push_cast; linarith
  obtain ⟨h1, h2⟩ := pq_zero e1
  have h8 : (8 * p ^ 2 - 2) ^ 2 = 2 * 1 ^ 2 := by
    linear_combination (64 * p ^ 2) * h1 + (-32 * (2 * p * q - 1 / 4)) * h2
  have := sq_eq_two_sq h8
  norm_num at this

/-- Coefficient tuple of `a + b sqrt2 + (c + d sqrt2) u`. -/
@[ext] structure E4 where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ

namespace E4

/-- The real number. -/
noncomputable def ev (x : E4) : ℝ := x.a + x.b * Real.sqrt 2 + (x.c + x.d * Real.sqrt 2) * uu

/-- Product (uses `sqrt2^2 = 2`, `u^2 = (2 - sqrt2)/4`). -/
def mul (x y : E4) : E4 :=
  ⟨x.a * y.a + 2 * x.b * y.b + ((x.c * y.c + 2 * x.d * y.d) - (x.c * y.d + x.d * y.c)) / 2,
   x.a * y.b + x.b * y.a + (x.c * y.d + x.d * y.c) / 2 - (x.c * y.c + 2 * x.d * y.d) / 4,
   x.a * y.c + 2 * x.b * y.d + x.c * y.a + 2 * x.d * y.b,
   x.a * y.d + x.b * y.c + x.c * y.b + x.d * y.a⟩

def add (x y : E4) : E4 := ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩

def smul (r : ℚ) (x : E4) : E4 := ⟨r * x.a, r * x.b, r * x.c, r * x.d⟩

theorem ev_mul (x y : E4) : (x.mul y).ev = x.ev * y.ev := by
  have hs := s2_sq
  have hu := uu_sq
  simp only [ev, mul]
  push_cast
  set s := Real.sqrt 2
  set u := uu
  linear_combination (-(((y.c : ℝ) + y.d * s) * ((x.c : ℝ) + x.d * s))) * hu +
    (-((y.b : ℝ) * x.b + y.b * x.d * u - y.c * x.d / 4 + y.d * x.b * u - y.d * x.c / 4 - y.d * x.d * s / 4
      + y.d * x.d / 2)) * hs

/-- Linear independence of `1, sqrt2, u, sqrt2 u` over `Q`. -/
theorem indep {a b c d : ℚ} (h : (a : ℝ) + b * Real.sqrt 2 + (c + d * Real.sqrt 2) * uu = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  by_cases hX : (c : ℝ) + d * Real.sqrt 2 = 0
  · obtain ⟨hc, hd⟩ := pq_zero hX
    subst hc; subst hd
    simp at h
    obtain ⟨ha, hb⟩ := pq_zero (by simpa using h)
    exact ⟨ha, hb, rfl, rfl⟩
  · exfalso
    -- u = -(a + b s)/(c + d s) = p + q s
    have hn : ((c ^ 2 - 2 * d ^ 2 : ℚ) : ℝ) ≠ 0 := by
      intro h0
      have h0' : c ^ 2 - 2 * d ^ 2 = 0 := by exact_mod_cast h0
      have hd : d = 0 := sq_eq_two_sq (x := c) (by linarith)
      subst hd
      have : c = 0 := by simpa using h0'
      subst this
      simp at hX
    have hs := s2_sq
    have hcd : ((c : ℝ) + d * Real.sqrt 2) * ((c : ℝ) - d * Real.sqrt 2) = ((c ^ 2 - 2 * d ^ 2 : ℚ) : ℝ) := by
      push_cast; linear_combination (-(d : ℝ) ^ 2) * hs
    set nX : ℚ := c ^ 2 - 2 * d ^ 2 with hnX
    -- u * X = -Y
    have hY : (a : ℝ) + b * Real.sqrt 2 = -(uu * ((c : ℝ) + d * Real.sqrt 2)) := by linarith
    -- u * nX = -Y * (c - d s)
    have hu1 : uu * (nX : ℝ) = -(((a : ℝ) + b * Real.sqrt 2) * ((c : ℝ) - d * Real.sqrt 2)) := by
      rw [← hcd, hY]; ring
    have hnX' : (nX : ℝ) ≠ 0 := hn
    -- u = p + q s with p = -(a c - 2 b d)/nX, q = -(b c - a d)/nX
    refine uu_not_mem (p := -(a * c - 2 * b * d) / nX) (q := -(b * c - a * d) / nX) ?_
    push_cast
    field_simp
    have : uu * (nX : ℝ) = -(((a : ℝ) * c - 2 * b * d) + (b * c - a * d) * Real.sqrt 2) := by
      rw [hu1]; linear_combination ((b : ℝ) * d) * hs
    rw [hnX] at this ⊢
    push_cast at this ⊢
    linarith

theorem ev_eq_zero {x : E4} (h : x.ev = 0) : x = ⟨0, 0, 0, 0⟩ := by
  obtain ⟨h1, h2, h3, h4⟩ := indep h
  ext <;> simp [h1, h2, h3, h4]

theorem ev_inj {x y : E4} (h : x.ev = y.ev) : x = y := by
  have : ((x.a - y.a : ℚ) : ℝ) + ((x.b - y.b : ℚ) : ℝ) * Real.sqrt 2
      + (((x.c - y.c : ℚ) : ℝ) + ((x.d - y.d : ℚ) : ℝ) * Real.sqrt 2) * uu = 0 := by
    unfold ev at h; push_cast; linarith
  obtain ⟨h1, h2, h3, h4⟩ := indep this
  ext <;> linarith

end E4

end Erdos634.Lacz53
