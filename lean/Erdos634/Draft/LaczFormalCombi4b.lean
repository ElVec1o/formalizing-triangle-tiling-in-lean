-- Draft/LaczFormalCombi4b.lean -- Laczkovich, DCG 48 (2012), Lemma 3.8: the whole ARITHMETIC of the lemma, assembled.
--   (a) `alpha_list`: m alpha = s pi/2 with pi/4 < alpha < pi/2, m >= 1, s <= 4  ==>  alpha in {pi/3, 3pi/8, 3pi/10, 2pi/5, 2pi/7} (the printed list (8)).
--   (b) `Dich S C` (S = sin alpha, C = cos alpha): the area equation of a rectangle with sides x S + y C + z, u S + v C + w forces one side to be an
--       integer multiple of S and the other of C, in the five cases (Combi2: pi/3, 3pi/8; Combi3c: 3pi/10, 2pi/5, 2pi/7).
--   (c) `lem38_rect_arith`: for the tile (a, b, c) = k (sin alpha, cos alpha, 1) and a rectangle W x H with W = x a + y b + z c, H = u a + v b + w c, N a b = 2 W H:
--       W/H = q a/b or H/W = q a/b with q rational.
--   (d) `iso_rect_arith`: the isosceles right tile (a = b, c = a sqrt 2): W/H rational -- by arithmetic, WITHOUT [1, Thm 2] (the printed proof cites it).
-- NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Comput. Geom. 48 (2012) 330-372, Lemma 3.8; Combinatorica 10 (1990)), Beeson, Beeson-Zhang.
import Mathlib
import Erdos634.Draft.LaczFormalCombi3c

open scoped Classical
open Polynomial

namespace Erdos634.Laczkovich.Combi4

open Erdos634.Laczkovich.Combi2 (irr_lin lem38_case23 lem38_case34)
open Erdos634.Laczkovich.Combi3 (lem38_case35 lem38_case45 lem38_case47)

/-- (a) the printed list (8), in terms of `alpha`. -/
theorem alpha_list (α : ℝ) (h1 : Real.pi / 4 < α) (h2 : α < Real.pi / 2) (m s : ℕ) (hm : 0 < m) (hs4 : s ≤ 4)
    (h : (m : ℝ) * α = s * Real.pi / 2) :
    α = Real.pi / 3 ∨ α = 3 * Real.pi / 8 ∨ α = 3 * Real.pi / 10 ∨ α = 2 * Real.pi / 5 ∨ α = 2 * Real.pi / 7 := by
  have hpi := Real.pi_pos
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hl : (s : ℝ) < m := by
    by_contra hc
    push Not at hc
    nlinarith
  have hu : (m : ℝ) < 2 * s := by
    by_contra hc
    push Not at hc
    nlinarith
  have hl' : s < m := by exact_mod_cast hl
  have hu' : m < 2 * s := by exact_mod_cast hu
  have hcase : (s = 2 ∧ m = 3) ∨ (s = 3 ∧ m = 4) ∨ (s = 3 ∧ m = 5) ∨ (s = 4 ∧ m = 5) ∨ (s = 4 ∧ m = 6) ∨ (s = 4 ∧ m = 7) := by
    omega
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> push_cast at h
  · left; linarith
  · right; left; linarith
  · right; right; left; linarith
  · right; right; right; left; linarith
  · left; linarith
  · right; right; right; right; linarith

/-! ### (b) the dichotomy -/

/-- With `S = sin alpha`, `C = cos alpha`: the area equation of a rectangle with sides `x S + y C + z`, `u S + v C + w` forces one side to be
an integer multiple of `S` and the other of `C`. -/
def Dich (S C : ℝ) : Prop :=
  ∀ x y z u v w t : ℕ, 0 < t → x + y + z ≠ 0 → u + v + w ≠ 0 →
    ((x : ℝ) * S + y * C + z) * ((u : ℝ) * S + v * C + w) = (t / 2) * S * C →
    ∃ p r : ℕ, (((x : ℝ) * S + y * C + z = p * S) ∧ ((u : ℝ) * S + v * C + w = r * C)) ∨
               (((x : ℝ) * S + y * C + z = p * C) ∧ ((u : ℝ) * S + v * C + w = r * S))

theorem dich_of_core (S C : ℝ)
    (core : ∀ x y z u v w t : ℕ, 0 < t → x + y + z ≠ 0 → u + v + w ≠ 0 →
      ((x : ℝ) * C + y * S + z) * ((u : ℝ) * C + v * S + w) = (t / 2) * C * S →
      (x = 0 ∧ z = 0 ∧ v = 0 ∧ w = 0) ∨ (y = 0 ∧ z = 0 ∧ u = 0 ∧ w = 0)) : Dich S C := by
  intro x y z u v w t ht hA hB h
  have hh : ((y : ℝ) * C + x * S + z) * ((v : ℝ) * C + u * S + w) = (t / 2) * C * S := by linear_combination h
  rcases core y x z v u w t ht (by omega) (by omega) hh with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · subst h1; subst h2; subst h3; subst h4
    exact ⟨x, v, Or.inl ⟨by simp, by simp⟩⟩
  · subst h1; subst h2; subst h3; subst h4
    exact ⟨y, u, Or.inr ⟨by simp, by simp⟩⟩

theorem dich_310 : Dich (Real.sin (3 * Real.pi / 10)) (Real.cos (3 * Real.pi / 10)) :=
  dich_of_core _ _ (fun x y z u v w t ht _ _ h => lem38_case35 x y z u v w t ht h)

theorem dich_25 : Dich (Real.sin (2 * Real.pi / 5)) (Real.cos (2 * Real.pi / 5)) :=
  dich_of_core _ _ (fun x y z u v w t ht _ _ h => lem38_case45 x y z u v w t ht h)

theorem dich_27 : Dich (Real.sin (2 * Real.pi / 7)) (Real.cos (2 * Real.pi / 7)) :=
  dich_of_core _ _ (fun x y z u v w t ht _ _ h => lem38_case47 x y z u v w t ht h)

theorem dich_38 : Dich (Real.sin (3 * Real.pi / 8)) (Real.cos (3 * Real.pi / 8)) := by
  have hpi := Real.pi_pos
  have hc : 0 < Real.cos (3 * Real.pi / 8) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs : 0 < Real.sin (3 * Real.pi / 8) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hc2 : Real.cos (3 * Real.pi / 8) ^ 2 = (2 - Real.sqrt 2) / 4 := by
    have e : 2 * (3 * Real.pi / 8) = Real.pi - Real.pi / 4 := by ring
    have := Real.cos_sq (3 * Real.pi / 8)
    rw [e, Real.cos_pi_sub, Real.cos_pi_div_four] at this
    rw [this]; ring
  have hsin : Real.sin (3 * Real.pi / 8) = (Real.sqrt 2 + 1) * Real.cos (3 * Real.pi / 8) := by
    have hsq : Real.sin (3 * Real.pi / 8) ^ 2 = ((Real.sqrt 2 + 1) * Real.cos (3 * Real.pi / 8)) ^ 2 := by
      have := Real.sin_sq_add_cos_sq (3 * Real.pi / 8)
      rw [mul_pow, hc2]
      nlinarith [h2]
    have hpos : 0 < (Real.sqrt 2 + 1) * Real.cos (3 * Real.pi / 8) := by positivity
    exact (sq_eq_sq₀ hs.le hpos.le).mp hsq
  refine dich_of_core _ _ (fun x y z u v w t ht hA hB h => ?_)
  have := lem38_case34 hc hc2 hsin x y z u v w t ht hA hB (by linear_combination h)
  rcases this with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · exact Or.inl ⟨h1, h3, h2, h4⟩
  · exact Or.inr ⟨h1, h3, h2, h4⟩

theorem dich_3 : Dich (Real.sin (Real.pi / 3)) (Real.cos (Real.pi / 3)) := by
  rw [Real.sin_pi_div_three, Real.cos_pi_div_three]
  intro x y z u v w t ht hA hB h
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have key := lem38_case23 x (y + 2 * z) u (v + 2 * w) t ht (by push_cast; linear_combination 4 * h)
  rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨y + 2 * z, u, Or.inr ⟨?_, ?_⟩⟩
    · subst h1; push_cast; ring
    · have hv : v = 0 := by omega
      have hw : w = 0 := by omega
      subst hv; subst hw; subst h1; simp
  · have hy : y = 0 := by omega
    have hz : z = 0 := by omega
    refine ⟨x, v + 2 * w, Or.inl ⟨?_, ?_⟩⟩
    · subst hy; subst hz; simp
    · subst h2; push_cast; ring

/-- (b) all five cases. -/
theorem dich_all (α : ℝ) (h1 : Real.pi / 4 < α) (h2 : α < Real.pi / 2) (m s : ℕ) (hm : 0 < m) (hs4 : s ≤ 4)
    (h : (m : ℝ) * α = s * Real.pi / 2) : Dich (Real.sin α) (Real.cos α) := by
  rcases alpha_list α h1 h2 m s hm hs4 h with rfl | rfl | rfl | rfl | rfl
  · exact dich_3
  · exact dich_38
  · exact dich_310
  · exact dich_25
  · exact dich_27

/-! ### (c) the rectangle -/

/-- **Lemma 3.8, arithmetic part.**  Tile `(a, b, c) = k (sin alpha, cos alpha, 1)`, `alpha` in the printed list; a rectangle `W x H`, `W = x a + y b + z c`,
`H = u a + v b + w c` (not both zero), `N a b = 2 W H`, `N > 0`: then `W / H` or `H / W` is a rational multiple of `a / b`. -/
theorem lem38_rect_arith (α k : ℝ) (hk : 0 < k) (h1 : Real.pi / 4 < α) (h2 : α < Real.pi / 2) (m s : ℕ) (hm : 0 < m) (hs4 : s ≤ 4)
    (hα : (m : ℝ) * α = s * Real.pi / 2) (W H : ℝ) (x y z u v w N : ℕ) (hN : 0 < N)
    (hW : W = x * (k * Real.sin α) + y * (k * Real.cos α) + z * k)
    (hH : H = u * (k * Real.sin α) + v * (k * Real.cos α) + w * k)
    (hx : x + y + z ≠ 0) (hu : u + v + w ≠ 0)
    (harea : (N : ℝ) * ((k * Real.sin α) * (k * Real.cos α)) = 2 * (W * H)) :
    (∃ q : ℚ, W / H = q * ((k * Real.sin α) / (k * Real.cos α))) ∨ (∃ q : ℚ, H / W = q * ((k * Real.sin α) / (k * Real.cos α))) := by
  have hpi := Real.pi_pos
  have hS : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hC : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith, h2⟩
  have hd := dich_all α h1 h2 m s hm hs4 hα
  have hW' : W = k * ((x : ℝ) * Real.sin α + y * Real.cos α + z) := by rw [hW]; ring
  have hH' : H = k * ((u : ℝ) * Real.sin α + v * Real.cos α + w) := by rw [hH]; ring
  have hkk : (k * k) ≠ 0 := by positivity
  obtain ⟨p, r, hpr⟩ := hd x y z u v w N hN hx hu (by
    apply mul_left_cancel₀ hkk
    rw [hW', hH'] at harea
    linear_combination (-1 / 2 : ℝ) * harea)
  have hpos : ∀ n : ℕ, n ≠ 0 → (0 : ℝ) < n := fun n hn => by exact_mod_cast Nat.pos_of_ne_zero hn
  have hWpos : 0 < (x : ℝ) * Real.sin α + y * Real.cos α + z := by
    rcases Nat.eq_zero_or_pos x with h0 | h0
    · rcases Nat.eq_zero_or_pos y with h0' | h0'
      · have : z ≠ 0 := by omega
        have := hpos z this
        subst h0; subst h0'; simpa using this
      · have := hpos y (by omega)
        subst h0; positivity
    · positivity
  have hHpos : 0 < (u : ℝ) * Real.sin α + v * Real.cos α + w := by
    rcases Nat.eq_zero_or_pos u with h0 | h0
    · rcases Nat.eq_zero_or_pos v with h0' | h0'
      · have : w ≠ 0 := by omega
        have := hpos w this
        subst h0; subst h0'; simpa using this
      · have := hpos v (by omega)
        subst h0; positivity
    · positivity
  rcases hpr with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · left
    have hp : (p : ℝ) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at e1; linarith
    have hr : (r : ℝ) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at e2; linarith
    refine ⟨(p : ℚ) / r, ?_⟩
    rw [hW', hH', e1, e2]
    push_cast
    field_simp
  · right
    have hp : (p : ℝ) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at e1; linarith
    have hr : (r : ℝ) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at e2; linarith
    refine ⟨(r : ℚ) / p, ?_⟩
    rw [hW', hH', e1, e2]
    push_cast
    field_simp

/-! ### (d) the isosceles right tile (`alpha = beta = pi/4`): no [1, Theorem 2] needed -/

/-- Tile `(l, l, l sqrt 2)`; rectangle `W x H` with `W = x l + y l + z l sqrt 2`, `H = u l + v l + w l sqrt 2` (positive), `N l^2 = 2 W H`: `W / H` is rational.
(The printed proof says "the sides of A are commensurable by [1, Theorem 2]"; the area equation and the irrationality of `sqrt 2` suffice.) -/
theorem iso_rect_arith (l : ℝ) (hl : 0 < l) (W H : ℝ) (x y z u v w N : ℕ)
    (hW : W = x * l + y * l + z * (l * Real.sqrt 2)) (hH : H = u * l + v * l + w * (l * Real.sqrt 2))
    (hWp : 0 < W) (hHp : 0 < H) (harea : (N : ℝ) * (l * l) = 2 * (W * H)) :
    ∃ q : ℚ, W / H = q * (l / l) := by
  have hirr : Irrational (Real.sqrt 2) := irrational_sqrt_two
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  set X : ℕ := x + y with hX
  set U : ℕ := u + v with hU
  have hW' : W = l * ((X : ℝ) + z * Real.sqrt 2) := by rw [hW, hX]; push_cast; ring
  have hH' : H = l * ((U : ℝ) + w * Real.sqrt 2) := by rw [hH, hU]; push_cast; ring
  have hll : l * l ≠ 0 := by positivity
  have hprod : ((X : ℝ) + z * Real.sqrt 2) * ((U : ℝ) + w * Real.sqrt 2) = N / 2 := by
    apply mul_left_cancel₀ hll
    rw [hW', hH'] at harea
    linear_combination (-1 / 2 : ℝ) * harea
  have key : ((((X : ℚ) * U + 2 * z * w - N / 2 : ℚ)) : ℝ) + (((X : ℚ) * w + z * U : ℚ) : ℝ) * Real.sqrt 2 = 0 := by
    push_cast
    linear_combination hprod - ((z : ℝ) * w) * h2
  obtain ⟨-, k2⟩ := irr_lin hirr _ _ key
  have hk : X * w + z * U = 0 := by
    have : (((X * w + z * U : ℕ)) : ℚ) = 0 := by push_cast; exact k2
    exact_mod_cast this
  have hXw : X * w = 0 := by omega
  have hzU : z * U = 0 := by omega
  have hWX : 0 < (X : ℝ) + z * Real.sqrt 2 := by
    have : 0 < l * ((X : ℝ) + z * Real.sqrt 2) := hW' ▸ hWp
    exact pos_of_mul_pos_right this hl.le
  have hHU : 0 < (U : ℝ) + w * Real.sqrt 2 := by
    have : 0 < l * ((U : ℝ) + w * Real.sqrt 2) := hH' ▸ hHp
    exact pos_of_mul_pos_right this hl.le
  rcases Nat.eq_zero_or_pos X with hX0 | hX0
  · -- X = 0, so z > 0, U = 0, w > 0
    have hz : 0 < z := by
      by_contra hz0
      have : z = 0 := by omega
      rw [hX0, this] at hWX; simp at hWX
    have hU0 : U = 0 := (Nat.mul_eq_zero.mp hzU).resolve_left hz.ne'
    have hw : 0 < w := by
      by_contra hw0
      have : w = 0 := by omega
      rw [hU0, this] at hHU; simp at hHU
    refine ⟨(z : ℚ) / w, ?_⟩
    rw [hW', hH', hX0, hU0]
    have hw' : (w : ℝ) ≠ 0 := by exact_mod_cast hw.ne'
    have hs0 : Real.sqrt 2 ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · have hw0 : w = 0 := (Nat.mul_eq_zero.mp hXw).resolve_left hX0.ne'
    have hU : 0 < U := by
      by_contra hU0
      have : U = 0 := by omega
      rw [this, hw0] at hHU; simp at hHU
    have hz0 : z = 0 := (Nat.mul_eq_zero.mp hzU).resolve_right hU.ne'
    refine ⟨(X : ℚ) / U, ?_⟩
    rw [hW', hH', hw0, hz0]
    have hU' : (U : ℝ) ≠ 0 := by exact_mod_cast hU.ne'
    push_cast
    field_simp
    ring

end Erdos634.Laczkovich.Combi4

#print axioms Erdos634.Laczkovich.Combi4.alpha_list
#print axioms Erdos634.Laczkovich.Combi4.dich_all
#print axioms Erdos634.Laczkovich.Combi4.lem38_rect_arith
#print axioms Erdos634.Laczkovich.Combi4.iso_rect_arith
