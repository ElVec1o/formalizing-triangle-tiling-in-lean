import Erdos634.Draft.LaczFormalMJArith

/-!
# The two lattices of the Column Lemma: arithmetic layer

Erdős #634, base-`β` row, Column Lemma (AI assistant's mixed-row session 2026-10-21, `ANSWER.md` §0–§1).
Credit: AI assistant (the Column Lemma proposal, C1–C4), Beeson–Roșu (the tile, the relation lattice `K`), Beeson,
Laczkovich.  UNAUDITED.  Axiom-clean; no `sorry`.

Tile `(a,b,c) = (ef, f²−e², f²)`, `1 ≤ e < f`, `gcd(e,f) = 1`.  Two lattices share the direction `u_β`
(a unit vector at angle `β` to the horizontal, `u = cos β`, `s = sin β > 0`):

* `pc i j = (i c + j a u, j a s)`  (the `c`-lattice `L_c = ⟨(c,0), a u_β⟩`),
* `pa k l = (k a + l c u, l c s)`  (the `a`-lattice `L_a = ⟨(a,0), c u_β⟩`).

`lattices_meet`: `pc i j = pa k l ↔ j a = l c ∧ i c = k a`; with `gcd(e,f) = 1` this is
`i = e s, k = f s, j = f t, l = e t`: **the lattices coincide exactly on `⟨(ec, 0), ec · u_β⟩`**
(`meet_param`, `ec = fa`).  Arithmetic consequences (the numerical content of C1, C2, C3 of the Column Lemma):

* `common_height`: along a `β`-wall with `a`-edges on one side and `c`-edges on the other the first common vertex is
  at height `e c = f a`, needing exactly `f` `a`-edges and `e` `c`-edges (`wall_first_common`);
  no common vertex below (`wall_no_common_below`);                                   [C2]
* `MJ_ka_unique`: a horizontal cover of `k a`, `k < f`, is `a^k` (pure `a`-rows in columns narrower than `f a`);
  `MJ_jc_unique` (existing): the same for `c`, `j < e`;                                 [C1]
* negative controls: the statements fail at width `e c = f a` (`MJ_ec_eq_fa`, `col_pure_c_fails_at_e`,
  `col_pure_a_fails_at_f`, `wall_common_at_ec`).
-/

namespace Erdos634.LaczColumn

open Erdos634.LaczJunction

/-! ## Geometry of the two lattices (real coordinates) -/

section Real

variable (e f : ℕ) (u s : ℝ)

/-- A point of the `c`-lattice `⟨(c,0), a·u_β⟩`, `u_β = (u, s)`. -/
def pc (i j : ℝ) : ℝ × ℝ := (i * (tc e f : ℝ) + j * (ta e f : ℝ) * u, j * (ta e f : ℝ) * s)

/-- A point of the `a`-lattice `⟨(a,0), c·u_β⟩`. -/
def pa (k l : ℝ) : ℝ × ℝ := (k * (ta e f : ℝ) + l * (tc e f : ℝ) * u, l * (tc e f : ℝ) * s)

theorem ta_pos' (he : 1 ≤ e) (hef : e < f) : (0 : ℝ) < ta e f := by
  unfold ta; have : 0 < e * f := Nat.mul_pos (by omega) (by omega); exact_mod_cast this

theorem tc_pos' (hef : e < f) : (0 : ℝ) < tc e f := by
  unfold tc
  have hf : 0 < f := by omega
  exact_mod_cast pow_pos hf 2

/-- **The two lattices meet exactly where the heights and the abscissae match.** -/
theorem lattices_meet (he : 1 ≤ e) (hef : e < f) (hs : 0 < s) (i j k l : ℝ) :
    pc e f u s i j = pa e f u s k l ↔ j * (ta e f : ℝ) = l * (tc e f : ℝ) ∧ i * (tc e f : ℝ) = k * (ta e f : ℝ) := by
  unfold pc pa
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only at h1 h2
    have hj : j * (ta e f : ℝ) = l * (tc e f : ℝ) := by
      have : (j * (ta e f : ℝ) - l * (tc e f : ℝ)) * s = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact absurd h hs.ne'
    refine ⟨hj, ?_⟩
    have : j * (ta e f : ℝ) * u = l * (tc e f : ℝ) * u := by rw [hj]
    linarith
  · rintro ⟨hj, hi⟩
    refine Prod.ext ?_ ?_
    · simp only
      have : j * (ta e f : ℝ) * u = l * (tc e f : ℝ) * u := by rw [hj]
      linarith
    · simp only; rw [hj]

end Real

/-! ## The integer content: the intersection is `⟨ec⟩` -/

theorem ec_eq_fa' (e f : ℕ) : e * tc e f = f * ta e f := by unfold tc ta; ring

/-- `j a = l c` (positive integers) iff `j = f t`, `l = e t`: the first common height is `t = 1`, i.e. `e c = f a`. -/
theorem common_height (e f j l : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f) :
    j * ta e f = l * tc e f ↔ ∃ t : ℕ, j = f * t ∧ l = e * t := by
  constructor
  · intro h
    have hf : 0 < f := by omega
    have h1 : j * e = l * f := by
      unfold ta tc at h
      have : (j * e) * f = (l * f) * f := by nlinarith
      exact Nat.eq_of_mul_eq_mul_right hf this
    have hfj : f ∣ j * e := ⟨l, by rw [h1]; ring⟩
    have hfj' : f ∣ j := (Nat.Coprime.dvd_of_dvd_mul_right hcop.symm hfj)
    obtain ⟨t, ht⟩ := hfj'
    refine ⟨t, ht, ?_⟩
    rw [ht] at h1
    have : (f * t) * e = (e * t) * f := by nlinarith
    have h2 : (f * t) * e = l * f := h1
    have : l * f = (e * t) * f := by rw [← h2]; ring
    exact Nat.eq_of_mul_eq_mul_right hf this
  · rintro ⟨t, rfl, rfl⟩
    unfold ta tc; ring

/-- `i c = k a` iff `i = e s`, `k = f s`. -/
theorem common_abscissa (e f i k : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f) :
    i * tc e f = k * ta e f ↔ ∃ t : ℕ, i = e * t ∧ k = f * t := by
  constructor
  · intro h
    have hf : 0 < f := by omega
    have h1 : i * f = k * e := by
      unfold ta tc at h
      have : (i * f) * f = (k * e) * f := by nlinarith
      exact Nat.eq_of_mul_eq_mul_right hf this
    have hei : e ∣ i * f := ⟨k, by rw [h1]; ring⟩
    have hei' : e ∣ i := Nat.Coprime.dvd_of_dvd_mul_right hcop hei
    obtain ⟨t, ht⟩ := hei'
    refine ⟨t, ht, ?_⟩
    rw [ht] at h1
    have h2 : (e * t) * f = k * e := h1
    have : k * e = (f * t) * e := by rw [← h2]; ring
    exact Nat.eq_of_mul_eq_mul_right (by omega) this
  · rintro ⟨t, rfl, rfl⟩
    unfold ta tc; ring

/-- **The meet of the two lattices, in parameters**: `pc i j = pa k l` for natural coordinates iff
`(i,j,k,l) = (e s, f t, f s, e t)`.  The common lattice is `⟨(ec, 0), ec · u_β⟩`. -/
theorem meet_param (e f : ℕ) (u s : ℝ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f) (hs : 0 < s)
    (i j k l : ℕ) :
    pc e f u s (i : ℝ) (j : ℝ) = pa e f u s (k : ℝ) (l : ℝ) ↔
      ∃ s' t : ℕ, i = e * s' ∧ k = f * s' ∧ j = f * t ∧ l = e * t := by
  rw [lattices_meet e f u s he hef hs]
  have hn1 : (j : ℝ) * (ta e f : ℝ) = (l : ℝ) * (tc e f : ℝ) ↔ j * ta e f = l * tc e f := by
    constructor <;> intro h <;> exact_mod_cast h
  have hn2 : (i : ℝ) * (tc e f : ℝ) = (k : ℝ) * (ta e f : ℝ) ↔ i * tc e f = k * ta e f := by
    constructor <;> intro h <;> exact_mod_cast h
  rw [hn1, hn2, common_height e f j l he hef hcop, common_abscissa e f i k he hef hcop]
  constructor
  · rintro ⟨⟨t, hj, hl⟩, ⟨s', hi, hk⟩⟩; exact ⟨s', t, hi, hk, hj, hl⟩
  · rintro ⟨s', t, hi, hk, hj, hl⟩; exact ⟨⟨t, hj, hl⟩, ⟨s', hi, hk⟩⟩

/-- **First common vertex on a `β`-wall (C2).**  The `a`-edges on one side and the `c`-edges on the other have a common
vertex at positive height `H = j a = l c` only if `j = f t`, `l = e t`; in particular `H ≥ e c = f a`. -/
theorem wall_common_ge (e f j l : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (hj : 0 < j) (h : j * ta e f = l * tc e f) : e * tc e f ≤ j * ta e f := by
  obtain ⟨t, rfl, rfl⟩ := (common_height e f j l he hef hcop).mp h
  have ht : 0 < t := by
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp at hj
    · exact ht
  rw [ec_eq_fa']
  exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ ht)

/-- No common vertex below the height `e c`: `j a = l c` with `0 < j < f` is impossible. -/
theorem wall_no_common_below (e f j l : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (hj : 0 < j) (hjf : j < f) : j * ta e f ≠ l * tc e f := by
  intro h
  obtain ⟨t, rfl, rfl⟩ := (common_height e f j l he hef hcop).mp h
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp at hj
  · have : f ≤ f * t := Nat.le_mul_of_pos_right _ ht
    omega

/-- The same with `l`: `l c = j a` with `0 < l < e` is impossible. -/
theorem wall_no_common_below' (e f j l : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (hl : 0 < l) (hle : l < e) : j * ta e f ≠ l * tc e f := by
  intro h
  obtain ⟨t, rfl, rfl⟩ := (common_height e f j l he hef hcop).mp h
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp at hl
  · have : e ≤ e * t := Nat.le_mul_of_pos_right _ ht
    omega

/-- **W2.**  A common vertex at exactly height `e c` needs exactly `f` `a`-edges against `e` `c`-edges. -/
theorem wall_first_common (e f j l : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (h : j * ta e f = e * tc e f) (hl : l * tc e f = e * tc e f) : j = f ∧ l = e := by
  have hc : 0 < tc e f := by unfold tc; exact pow_pos (by omega) 2
  have ha : 0 < ta e f := by unfold ta; exact Nat.mul_pos (by omega) (by omega)
  rw [ec_eq_fa'] at h
  exact ⟨Nat.eq_of_mul_eq_mul_right ha h, Nat.eq_of_mul_eq_mul_right hc (by rw [hl]) |>.trans rfl⟩

/-- **Witness at the first common height**: `f` `a`-edges and `e` `c`-edges do meet (so the bound `e c` is sharp). -/
theorem wall_common_at_ec (e f : ℕ) : f * ta e f = e * tc e f := (ec_eq_fa' e f).symm

/-! ## Pure rows in a narrow column (C1) -/

/-- **`MJ_ka_unique`.**  A horizontal cover of `k a`, `k < f`, by sides is `a^k`: an `a`-column of width `< f a` has pure
rows (no `b`, no `c`). -/
theorem MJ_ka_unique (e f x y z k : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (hk : k < f) (h : x * ta e f + y * tb e f + z * tc e f = k * ta e f) :
    x = k ∧ y = 0 ∧ z = 0 := by
  have hb := tb_cast e f hef
  have hZ : ((x : ℤ) - k) * (e * f) + (y : ℤ) * ((f:ℤ)^2 - (e:ℤ)^2) + (z : ℤ) * (f:ℤ)^2 = 0 := by
    have := congrArg (fun n : ℕ => (n : ℤ)) h
    simp only [ta, tc] at this
    push_cast at this
    rw [hb] at this
    linarith
  obtain ⟨η, ζ, hx, hy, hz⟩ := relation_lattice e f he hef hcop ((x : ℤ) - k) (y : ℤ) (z : ℤ) hZ
  have he' : (1 : ℤ) ≤ e := by exact_mod_cast he
  have hef' : (e : ℤ) < f := by exact_mod_cast hef
  have hk' : (k : ℤ) < f := by exact_mod_cast hk
  have hx0 : (0 : ℤ) ≤ x := by positivity
  have hy0 : (0 : ℤ) ≤ y := by positivity
  have hz0 : (0 : ℤ) ≤ z := by positivity
  have hη0 : 0 ≤ η := by
    by_contra hneg
    push_neg at hneg
    nlinarith
  rcases hη0.eq_or_lt with hη | hη
  · subst hη
    have hζ0 : 0 ≤ ζ := by nlinarith
    have hζ1 : ζ = 0 := by
      by_contra hne
      have : 1 ≤ ζ := by omega
      nlinarith
    subst hζ1
    refine ⟨by exact_mod_cast (by linarith : (x:ℤ) = k), by exact_mod_cast (by linarith : (y:ℤ) = 0),
      by exact_mod_cast (by linarith : (z:ℤ) = 0)⟩
  · exfalso
    have hζ : η < ζ := by
      by_contra hc
      push_neg at hc
      nlinarith
    nlinarith

#print axioms MJ_ka_unique

/-- The `c`-column version, restated: a horizontal cover of `j c`, `j < e`, is `c^j` (existing `MJ_jc_unique`). -/
theorem col_pure_c (e f x y z j : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f) (hj : j < e)
    (h : x * ta e f + y * tb e f + z * tc e f = j * tc e f) : x = 0 ∧ y = 0 ∧ z = j :=
  MJ_jc_unique e f x y z j he hef hcop hj h

/-- **Negative control (C1, `c`-column).** At width `e c` the cover is not pure: `f` `a`-edges. -/
theorem col_pure_c_fails_at_e (e f : ℕ) (he : 1 ≤ e) (hf : 1 ≤ f) :
    ¬ (∀ x y z : ℕ, x * ta e f + y * tb e f + z * tc e f = e * tc e f → x = 0 ∧ y = 0 ∧ z = e) :=
  MJ_jc_unique_fails_at_e e f he hf

/-- **Negative control (C1, `a`-column).** At width `f a` (`= e c`) the cover `a^f` is not the only one: `c^e`. -/
theorem col_pure_a_fails_at_f (e f : ℕ) (he : 1 ≤ e) (hef : e < f) :
    ¬ (∀ x y z : ℕ, x * ta e f + y * tb e f + z * tc e f = f * ta e f → x = f ∧ y = 0 ∧ z = 0) := by
  intro H
  have := H 0 0 e (by rw [ec_eq_fa']; ring)
  omega

/-- A column of width `w < e c`, `w` a multiple of `c`, is pure; of width `< f a`, a multiple of `a`, is pure: both
statements are sharp, and the two thresholds are the SAME length `e c = f a`. -/
theorem thresholds_coincide (e f : ℕ) : e * tc e f = f * ta e f := ec_eq_fa' e f

/-! ## `b`-free covers and the chord threshold -/

/-- **The `b`-free covers of `n c`**: `x a + z c = n c` iff `x = s f`, `z = n − s e` (`s` blocks of `f` `a`-edges replace
`e` `c`-edges each).  So the non-pure rows of a `b`-free stack are exactly the `a`-blocks of width `f a = e c`. -/
theorem bfree_cover_c (e f x z n : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (h : x * ta e f + z * tc e f = n * tc e f) : ∃ s : ℕ, x = s * f ∧ z + s * e = n := by
  have h' : x * ta e f + 0 * tb e f + z * tc e f = n * tc e f := by simpa using h
  have hb := tb_cast e f hef
  have hZ : (x : ℤ) * (e * f) + (0 : ℤ) * ((f:ℤ)^2 - (e:ℤ)^2) + ((z : ℤ) - n) * (f:ℤ)^2 = 0 := by
    have := congrArg (fun n : ℕ => (n : ℤ)) h'
    simp only [ta, tc] at this
    push_cast at this
    rw [hb] at this
    linarith
  obtain ⟨η, ζ, hx, hy, hz⟩ := relation_lattice e f he hef hcop (x : ℤ) 0 ((z : ℤ) - n) hZ
  have hfpos : (0 : ℤ) < f := by exact_mod_cast (by omega : 0 < f)
  have hη : η = 0 := by
    have : η * f = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact h0
    · exact absurd h0 hfpos.ne'
  subst hη
  have hx0 : (0 : ℤ) ≤ x := by positivity
  have hζ : ζ ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    nlinarith
  refine ⟨(-ζ).toNat, ?_, ?_⟩
  · have : ((-ζ).toNat : ℤ) = -ζ := Int.toNat_of_nonneg (by omega)
    have : (x : ℤ) = (((-ζ).toNat : ℕ) : ℤ) * f := by rw [this]; linarith
    exact_mod_cast this
  · have h1 : ((-ζ).toNat : ℤ) = -ζ := Int.toNat_of_nonneg (by omega)
    have : (z : ℤ) + (((-ζ).toNat : ℕ) : ℤ) * e = n := by rw [h1]; linarith
    exact_mod_cast this

/-- **The `b`-free covers of `n a`**: `x a + z c = n a` iff `z = s e`, `x = n − s f`. -/
theorem bfree_cover_a (e f x z n : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (h : x * ta e f + z * tc e f = n * ta e f) : ∃ s : ℕ, z = s * e ∧ x + s * f = n := by
  have h' : x * ta e f + 0 * tb e f + z * tc e f = n * ta e f := by simpa using h
  have hb := tb_cast e f hef
  have hZ : ((x : ℤ) - n) * (e * f) + (0 : ℤ) * ((f:ℤ)^2 - (e:ℤ)^2) + (z : ℤ) * (f:ℤ)^2 = 0 := by
    have := congrArg (fun n : ℕ => (n : ℤ)) h'
    simp only [ta, tc] at this
    push_cast at this
    rw [hb] at this
    linarith
  obtain ⟨η, ζ, hx, hy, hz⟩ := relation_lattice e f he hef hcop ((x : ℤ) - n) 0 (z : ℤ) hZ
  have hfpos : (0 : ℤ) < f := by exact_mod_cast (by omega : 0 < f)
  have hη : η = 0 := by
    have : η * f = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact h0
    · exact absurd h0 hfpos.ne'
  subst hη
  have hz0 : (0 : ℤ) ≤ z := by positivity
  have hepos : (0 : ℤ) < e := by exact_mod_cast he
  have hζ : 0 ≤ ζ := by
    by_contra hneg
    push_neg at hneg
    nlinarith
  refine ⟨ζ.toNat, ?_, ?_⟩
  · have h1 : ((ζ.toNat : ℕ) : ℤ) = ζ := Int.toNat_of_nonneg hζ
    have : (z : ℤ) = (((ζ.toNat : ℕ)) : ℤ) * e := by rw [h1]; linarith
    exact_mod_cast this
  · have h1 : ((ζ.toNat : ℕ) : ℤ) = ζ := Int.toNat_of_nonneg hζ
    have : (x : ℤ) + (((ζ.toNat : ℕ)) : ℤ) * f = n := by rw [h1]; linarith
    exact_mod_cast this

/-- **The chord threshold**: `f b = (f − e)(a + c)` (the second cover of a chord of length `f b`). -/
theorem chord_second_cover (e f : ℕ) (hef : e < f) :
    f * tb e f = (f - e) * ta e f + (f - e) * tc e f := by
  have h2 : e ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left hef.le 2
  unfold ta tb tc
  zify [h2, hef.le]
  ring

/-- Negative control for the chord: `MJ_jb_unique` fails at `j = f`. -/
theorem chord_cover_fails_at_f (e f : ℕ) (he : 1 ≤ e) (hef : e < f) :
    ¬ (∀ x y z : ℕ, x * ta e f + y * tb e f + z * tc e f = f * tb e f → x = 0 ∧ y = f ∧ z = 0) := by
  intro H
  have := H (f - e) 0 (f - e) (by rw [chord_second_cover e f hef]; ring)
  omega


/-- **Unique counts below `e c`** (`b`-free): two `b`-free multisets of the same total width `< e c` have the same numbers of
`a`- and of `c`-edges.  (Above `e c` the counts can change by blocks `(f, −e)`; `b`-edges would break this already at
`a + c = 3b` for `(e,f) = (2,3)`, which is why the statement is `b`-free: W4 of the hand proof.) -/
theorem bfree_unique_below (e f x z x' z' : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (h : x * ta e f + z * tc e f = x' * ta e f + z' * tc e f) (hw : x * ta e f + z * tc e f < e * tc e f) :
    x = x' ∧ z = z' := by
  have hb := tb_cast e f hef
  have hZ : ((x : ℤ) - x') * (e * f) + (0 : ℤ) * ((f:ℤ)^2 - (e:ℤ)^2) + ((z : ℤ) - z') * (f:ℤ)^2 = 0 := by
    have := congrArg (fun n : ℕ => (n : ℤ)) h
    simp only [ta, tc] at this
    push_cast at this
    linarith
  obtain ⟨η, ζ, hx, hy, hz⟩ := relation_lattice e f he hef hcop ((x : ℤ) - x') 0 ((z : ℤ) - z') hZ
  have hfpos : (0 : ℤ) < f := by exact_mod_cast (by omega : 0 < f)
  have hη : η = 0 := by
    have : η * f = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact h0
    · exact absurd h0 hfpos.ne'
  subst hη
  have hec : e * tc e f = f * ta e f := ec_eq_fa' e f
  have hx0 : (0 : ℤ) ≤ x := by positivity
  have hx0' : (0 : ℤ) ≤ x' := by positivity
  have hζ : ζ = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · -- ζ < 0: x = x' + (-ζ) f ≥ f
      have hxf : (f : ℤ) ≤ x := by nlinarith
      have : f ≤ x := by exact_mod_cast hxf
      have h1 : f * ta e f ≤ x * ta e f := Nat.mul_le_mul_right _ this
      omega
    · have hxf : (f : ℤ) ≤ x' := by nlinarith
      have : f ≤ x' := by exact_mod_cast hxf
      have h1 : f * ta e f ≤ x' * ta e f := Nat.mul_le_mul_right _ this
      omega
  subst hζ
  exact ⟨by exact_mod_cast (by linarith : (x : ℤ) = x'), by exact_mod_cast (by linarith : (z : ℤ) = z')⟩

end Erdos634.LaczColumn
