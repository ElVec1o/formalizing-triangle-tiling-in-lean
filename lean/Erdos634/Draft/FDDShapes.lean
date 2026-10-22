import Mathlib.Tactic
import Erdos634.AdmissibleSpectrum

/-!
# FDD item 2: the shape table of `prop:reduction` / `prop:otherspectra` as a Lean definition

Formalization debt (Rule 5), NOT progress on the /goal.  New file; no existing file edited.
Paper: `sub:shapes` (`paper/erdos-634.tex:965`), `eq:area` (:1003), `prop:reduction` (:1048),
`prop:otherspectra` (:1770).

## What this file defines and proves

`Shape` has the paper's eleven shapes of `ABC` (equilateral, two isosceles, `F₁…F₄`, the reflections
`F₁′, F₃′, F₄′` (`F₂` is self-paired), and the tile-similar triangle).  For each shape the table
carries

* `corners` : the corner-type triple `{(m_i,k_i)}`, angle `m_i α + k_i π/3`;
* `sideVec` : the primitive integer side-proportion vector in terms of the tile `(a,b,c)`;
* `num/den` : `N₀ = num/den` (the area ratio of `eq:area`), so the area equation is
  `N·den = k²·num` (`Shape.AreaEq`).

Theorems:

* `shapes_complete`, `shapes_sound`, `corners_injective`, `corners_reflect` : the corner-type
  classification of `sub:shapes` -- the realizable triples of pairs with `Σm=0, Σk=3` are EXACTLY the
  eleven listed, distinct shapes have distinct corner multisets, and reflection acts as the paper says
  (`(m,k) ↦ (-m, m+k)`).  (Exhaustive finite check by `decide`, as the paper says "done in exact
  arithmetic".)
* `heron_table` : for every shape, Heron's `16·Area²` of the side vector times `den²` equals
  `num² · 16·Area(T)²` -- i.e. the `N₀` column IS the area ratio of the side-vector column (this is
  an independent re-derivation of the table's `N₀` entries from its side vectors).
* `vecGcd_one` : each side vector is primitive (`gcd = 1`), so `eq:area`'s `k` is an integer scale.
* `not_prime_of_areaEq` : the arithmetic content of `prop:reduction`: for every shape other than the
  equilateral and the two isosceles ones, `AreaEq` forces `N` composite.
* `prime_forces_iso_or_equi` : the exact arithmetic statement "N prime ⟹ shape ∈ {iso α, iso β,
  equilateral}"; the equilateral case is NOT excluded here (see below).
* `F1_scale`, `scalene_N0`, `equilateral_clauses` : the clauses of `prop:otherspectra`.

## What is NOT proved (exactly)

1. The passage from a real `CongruentDissection` to a corner-type triple and a shape (the classification
   is proved on the arithmetic side only), and to the area equation `N = k²N₀` with `k` an integer
   scale (needs: each side of `ABC` is a union of whole tile edges, plus the area ratio for real
   triangles).  The Lean statements are therefore about the arithmetic table, WEAKER than the paper's
   tiling-level wording.
2. The equilateral case of `prop:reduction` (paper: `\cite[Thm.~6]{BeesonEq}`); not derivable from the
   area equation alone (`N·ab = S²` is satisfiable with `N` prime, e.g. `a=b=...` is not needed:
   `N = S²/(ab)` needs only `N ∣ ab`-type conditions).
3. `prop:otherspectra`'s equilateral divisibilities `(c+a-b) ∣ 3S`, `(c+b-a) ∣ 3S` come from `cor:int`
   on a real dissection (boundary flux `±3S`); here they appear only as the trivial consequence of
   hypotheses `Ma·X = 3S`, `Mb·Y = 3S`.
-/

namespace Erdos634.Draft.FDDShapes

/-! ## Corner types -/

abbrev Corner := ℤ × ℤ

/-- Realizable corner pair `(m,k)` (paper `eq:realizable`): `k ≥ 1, m ≥ -k` or `k = 0, m ≥ 1`. -/
def Realizable (p : Corner) : Prop := (1 ≤ p.2 ∧ -p.2 ≤ p.1) ∨ (p.2 = 0 ∧ 1 ≤ p.1)

instance : DecidablePred Realizable := fun p => by unfold Realizable; infer_instance

inductive Shape
  | equilateral | isoAlpha | isoBeta | F1 | F1' | F2 | F3 | F3' | F4 | F4' | tileSimilar
  deriving DecidableEq, Fintype, Repr

/-- The corner-type triple of each shape: angle `m α + k π/3` (with `β = π/3 - α`).
`iso α`: `(α,α,α+3β)`, `α+3β = π-2α = (-2,3)`; `iso β`: `(β,β,β+3α)`; `F₁ = (α,α+β,α+2β)`;
`F₂ = (2α,2β,α+β)`; `F₃ = (α,2α,3β)`; `F₄ = (α,2β,2α+β)`; tile-similar `(α,β,2π/3)`. -/
def Shape.corners : Shape → Multiset Corner
  | .equilateral => {(0, 1), (0, 1), (0, 1)}
  | .isoAlpha => {(1, 0), (1, 0), (-2, 3)}
  | .isoBeta => {(-1, 1), (-1, 1), (2, 1)}
  | .F1 => {(1, 0), (0, 1), (-1, 2)}
  | .F1' => {(-1, 1), (0, 1), (1, 1)}
  | .F2 => {(2, 0), (-2, 2), (0, 1)}
  | .F3 => {(1, 0), (2, 0), (-3, 3)}
  | .F3' => {(-1, 1), (-2, 2), (3, 0)}
  | .F4 => {(1, 0), (-2, 2), (1, 1)}
  | .F4' => {(-1, 1), (2, 0), (-1, 2)}
  | .tileSimilar => {(1, 0), (-1, 1), (0, 2)}

/-- Reflection `α ↔ β` on corner pairs: `m α + k π/3 = m(π/3-β)+kπ/3`, so `(m,k) ↦ (-m, m+k)`. -/
def reflectC (p : Corner) : Corner := (-p.1, p.1 + p.2)

def Shape.reflect : Shape → Shape
  | .equilateral => .equilateral | .isoAlpha => .isoBeta | .isoBeta => .isoAlpha
  | .F1 => .F1' | .F1' => .F1 | .F2 => .F2 | .F3 => .F3' | .F3' => .F3
  | .F4 => .F4' | .F4' => .F4 | .tileSimilar => .tileSimilar

theorem corners_reflect : ∀ s : Shape, s.reflect.corners = s.corners.map reflectC := by decide

theorem corners_injective : Function.Injective Shape.corners := by
  intro s t h; revert s t; decide

theorem shapes_sound : ∀ s : Shape, (s.corners.map Prod.fst).sum = 0 ∧
    (s.corners.map Prod.snd).sum = 3 ∧ ∀ c ∈ s.corners, Realizable c := by decide

private def okTriple (x y z : Corner) : Bool :=
  !(decide (Realizable x ∧ Realizable y ∧ Realizable z ∧ x.1 + y.1 + z.1 = 0 ∧ x.2 + y.2 + z.2 = 3))
    || decide (∃ s : Shape, ({x, y, z} : Multiset Corner) = s.corners)

private def checkAll : Bool :=
  (List.range 7).all fun i1 => (List.range 4).all fun j1 => (List.range 7).all fun i2 =>
  (List.range 4).all fun j2 => (List.range 7).all fun i3 => (List.range 4).all fun j3 =>
    okTriple ((i1 : ℤ) - 3, (j1 : ℤ)) ((i2 : ℤ) - 3, (j2 : ℤ)) ((i3 : ℤ) - 3, (j3 : ℤ))

private theorem checkAll_true : checkAll = true := by decide +kernel

/-- **Corner-type classification (`sub:shapes`).**  Three realizable corner pairs with
`Σ m_i = 0`, `Σ k_i = 3` form, up to order, the corner multiset of exactly one of the eleven shapes. -/
theorem shapes_complete (c1 c2 c3 : Corner) (h1 : Realizable c1) (h2 : Realizable c2)
    (h3 : Realizable c3) (hm : c1.1 + c2.1 + c3.1 = 0) (hk : c1.2 + c2.2 + c3.2 = 3) :
    ∃ s : Shape, ({c1, c2, c3} : Multiset Corner) = s.corners := by
  obtain ⟨m1, k1⟩ := c1; obtain ⟨m2, k2⟩ := c2; obtain ⟨m3, k3⟩ := c3
  have h1' := h1; have h2' := h2; have h3' := h3
  simp only [Realizable] at h1 h2 h3 hm hk
  obtain ⟨i1, hi1⟩ : ∃ i : ℕ, (i : ℤ) = m1 + 3 := ⟨(m1 + 3).toNat, by omega⟩
  obtain ⟨i2, hi2⟩ : ∃ i : ℕ, (i : ℤ) = m2 + 3 := ⟨(m2 + 3).toNat, by omega⟩
  obtain ⟨i3, hi3⟩ : ∃ i : ℕ, (i : ℤ) = m3 + 3 := ⟨(m3 + 3).toNat, by omega⟩
  obtain ⟨j1, hj1⟩ : ∃ i : ℕ, (i : ℤ) = k1 := ⟨k1.toNat, by omega⟩
  obtain ⟨j2, hj2⟩ : ∃ i : ℕ, (i : ℤ) = k2 := ⟨k2.toNat, by omega⟩
  obtain ⟨j3, hj3⟩ : ∃ i : ℕ, (i : ℤ) = k3 := ⟨k3.toNat, by omega⟩
  have e1 : m1 = (i1 : ℤ) - 3 := by omega
  have e2 : m2 = (i2 : ℤ) - 3 := by omega
  have e3 : m3 = (i3 : ℤ) - 3 := by omega
  have hi1' : i1 < 7 := by omega
  have hi2' : i2 < 7 := by omega
  have hi3' : i3 < 7 := by omega
  have hj1' : j1 < 4 := by omega
  have hj2' : j2 < 4 := by omega
  have hj3' : j3 < 4 := by omega
  subst e1 e2 e3 hj1 hj2 hj3
  have key := checkAll_true
  simp only [checkAll, List.all_eq_true, List.mem_range] at key
  have := key i1 hi1' j1 hj1' i2 hi2' j2 hj2' i3 hi3' j3 hj3'
  simp only [okTriple, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq] at this
  rcases this with hn | hy
  · exact absurd ⟨h1', h2', h3', hm, hk⟩ hn
  · exact hy

/-! ## The numeric table: side vectors, `N₀ = num/den`, area equation -/

/-- Primitive side-proportion vector of each shape, in terms of the tile `(a,b,c)`
(paper `prop:reduction` proof and `prop:ratfree`; reflections swap `a ↔ b`). -/
def Shape.sideVec : Shape → ℕ → ℕ → ℕ → ℕ × ℕ × ℕ
  | .equilateral, _, _, _ => (1, 1, 1)
  | .isoAlpha, a, b, c => (c, c, a + 2 * b)
  | .isoBeta, a, b, c => (c, c, 2 * a + b)
  | .F1, a, b, c => (a, c, a + b)
  | .F1', a, b, c => (b, c, a + b)
  | .F2, a, b, c => (a * (a + 2 * b), b * (2 * a + b), c ^ 2)
  | .F3, a, b, c => (c ^ 2, (a + 2 * b) * c, 3 * b * (a + b))
  | .F3', a, b, c => (c ^ 2, (2 * a + b) * c, 3 * a * (a + b))
  | .F4, a, b, c => (a * c, b * (2 * a + b), (a + b) * c)
  | .F4', a, b, c => (b * c, a * (a + 2 * b), (a + b) * c)
  | .tileSimilar, a, b, c => (a, b, c)

/-- Numerator of `N₀ = Area(D)/Area(T)`. -/
def Shape.num : Shape → ℕ → ℕ → ℕ
  | .equilateral, _, _ => 1
  | .isoAlpha, a, b => a + 2 * b
  | .isoBeta, a, b => 2 * a + b
  | .F1, a, b => a + b
  | .F1', a, b => a + b
  | .F2, a, b => (a + 2 * b) * (2 * a + b)
  | .F3, a, b => 3 * (a + b) * (a + 2 * b)
  | .F3', a, b => 3 * (a + b) * (2 * a + b)
  | .F4, a, b => (a + b) * (2 * a + b)
  | .F4', a, b => (a + b) * (a + 2 * b)
  | .tileSimilar, _, _ => 1

/-- Denominator of `N₀`. -/
def Shape.den : Shape → ℕ → ℕ → ℕ
  | .equilateral, a, b => a * b
  | .isoAlpha, _, b => b
  | .isoBeta, a, _ => a
  | .F1, _, b => b
  | .F1', a, _ => a
  | _, _, _ => 1

/-- The area equation `eq:area` with `k` the integer scale of `ABC = k·D`: `N = k² N₀`, cleared of
denominators.  (Equilateral: `k = S` and `N ab = S²`.) -/
def Shape.AreaEq (s : Shape) (a b k N : ℕ) : Prop := N * s.den a b = k ^ 2 * s.num a b

instance (s : Shape) (a b k N : ℕ) : Decidable (s.AreaEq a b k N) := by
  unfold Shape.AreaEq; infer_instance

/-- Reflection swaps `a ↔ b` in `N₀` (the side vectors of the reflected shape are the swapped
ones up to the order of the three entries -- for the self-paired `F₂` and the tile-similar shape the
order of entries is exchanged -- so no vector-level statement is made). -/
theorem num_reflect (s : Shape) (a b : ℕ) : s.reflect.num a b = s.num b a := by
  cases s <;> simp only [Shape.reflect, Shape.num] <;> ring

theorem den_reflect (s : Shape) (a b : ℕ) : s.reflect.den a b = s.den b a := by
  cases s <;> simp only [Shape.reflect, Shape.den] <;> ring

/-- **The `N₀` column is the area ratio of the side-vector column** (Heron).  With
`H(x,y,z) = 4x²y² - (x²+y²-z²)² = 16·Area²`, and `H(a,b,c) = 3a²b²` for the tile, for every shape
`H(D)·den² = num²·3a²b²`, i.e. `Area(D)/Area(T) = num/den`. -/
theorem heron_table (s : Shape) (a b c : ℕ) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (4 * ((s.sideVec a b c).1 : ℤ) ^ 2 * ((s.sideVec a b c).2.1 : ℤ) ^ 2
      - (((s.sideVec a b c).1 : ℤ) ^ 2 + ((s.sideVec a b c).2.1 : ℤ) ^ 2
          - ((s.sideVec a b c).2.2 : ℤ) ^ 2) ^ 2) * (s.den a b : ℤ) ^ 2
    = (s.num a b : ℤ) ^ 2 * (3 * (a : ℤ) ^ 2 * (b : ℤ) ^ 2) := by
  have h : (c : ℤ) ^ 2 = (a : ℤ) ^ 2 + a * b + b ^ 2 := by exact_mod_cast hc
  cases s <;> simp only [Shape.sideVec, Shape.num, Shape.den] <;> push_cast
  · ring
  · linear_combination (4*(a:ℤ)^2*b^2 + 16*a*b^3 + 16*b^4) * h
  · linear_combination (16*(a:ℤ)^4 + 16*a^3*b + 4*a^2*b^2) * h
  · linear_combination (3*(a:ℤ)^2*b^2 + 3*a*b^3 + b^4 - b^2*c^2) * h
  · linear_combination ((a:ℤ)^4 + 3*a^3*b + 3*a^2*b^2 - a^2*c^2) * h
  · linear_combination ((a:ℤ)^6 + 7*a^5*b + 20*a^4*b^2 + 25*a^3*b^3 + 20*a^2*b^4 + 7*a*b^5 + b^6 - c^6
      + c^4*(-a^2 - a*b - b^2) + c^2*(a^4 + 6*a^3*b + 13*a^2*b^2 + 6*a*b^3 + b^4)) * h
  · linear_combination (27*(a:ℤ)^4*b^2 + 135*a^3*b^3 + 270*a^2*b^4 + 243*a*b^5 + 81*b^6 - c^6
      + c^4*(a^2 + 7*a*b + 7*b^2) + c^2*(9*a^2*b^2 + 18*a*b^3 + 9*b^4)) * h
  · linear_combination (81*(a:ℤ)^6 + 243*a^5*b + 270*a^4*b^2 + 135*a^3*b^3 + 27*a^2*b^4 - c^6
      + c^4*(7*a^2 + 7*a*b + b^2) + c^2*(9*a^4 + 18*a^3*b + 9*a^2*b^2)) * h
  · linear_combination (12*(a:ℤ)^4*b^2 + 24*a^3*b^3 + 19*a^2*b^4 + 7*a*b^5 + b^6
      + c^2*(-4*a^2*b^2 - 4*a*b^3 - b^4)) * h
  · linear_combination ((a:ℤ)^6 + 7*a^5*b + 19*a^4*b^2 + 24*a^3*b^3 + 12*a^2*b^4
      + c^2*(-a^4 - 4*a^3*b - 4*a^2*b^2)) * h
  · linear_combination ((a:ℤ)^2 - a*b + b^2 - c^2) * h

/-! ## Arithmetic of the tile and primitivity of the side vectors -/

theorem three_not_dvd_c (a b c : ℕ) (hcop : Nat.Coprime a b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ¬ 3 ∣ c := by
  intro h3
  obtain ⟨t, rfl⟩ := h3
  have h9 : (a ^ 2 + a * b + b ^ 2) % 9 = 0 := by rw [← hc]; ring_nf; omega
  have key : ∀ x : ℕ, x < 9 → ∀ y : ℕ, y < 9 → (x * x + x * y + y * y) % 9 = 0 →
      x % 3 = 0 ∧ y % 3 = 0 := by decide
  have hmod : (a ^ 2 + a * b + b ^ 2) % 9
      = ((a % 9) * (a % 9) + (a % 9) * (b % 9) + (b % 9) * (b % 9)) % 9 := by
    simp [Nat.add_mod, Nat.mul_mod, pow_two]
  have h := key (a % 9) (Nat.mod_lt _ (by norm_num)) (b % 9) (Nat.mod_lt _ (by norm_num))
    (by rw [← hmod]; exact h9)
  have ha3 : 3 ∣ a := by omega
  have hb3 : 3 ∣ b := by omega
  have := Nat.dvd_gcd ha3 hb3
  rw [Nat.Coprime.gcd_eq_one hcop] at this
  omega

/-- A prime dividing `c` divides none of `a`, `b`, `a+b`, `a+2b`, `2a+b`, `3`. -/
theorem prime_dvd_c (a b c : ℕ) (hcop : Nat.Coprime a b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (p : ℕ) (hp : p.Prime) (hpc : p ∣ c) :
    ¬ p ∣ a ∧ ¬ p ∣ b ∧ ¬ p ∣ a + b ∧ ¬ p ∣ a + 2 * b ∧ ¬ p ∣ 2 * a + b ∧ p ≠ 3 := by
  have hpc2 : p ∣ c ^ 2 := dvd_pow hpc (by norm_num)
  have hab : ¬ (p ∣ a ∧ p ∣ b) := by
    rintro ⟨h1, h2⟩
    have := Nat.dvd_gcd h1 h2
    rw [Nat.Coprime.gcd_eq_one hcop] at this
    exact hp.not_dvd_one this
  have ha : ¬ p ∣ a := by
    intro h1
    have h2 : p ∣ b := by
      have : p ∣ a ^ 2 + a * b + b ^ 2 := hc ▸ hpc2
      have h3 : p ∣ a ^ 2 + a * b := dvd_add (dvd_pow h1 (by norm_num)) (dvd_mul_of_dvd_left h1 b)
      have h4 : p ∣ b ^ 2 := (Nat.dvd_add_right h3).mp this
      exact hp.dvd_of_dvd_pow h4
    exact hab ⟨h1, h2⟩
  have hb : ¬ p ∣ b := by
    intro h2
    have h1 : p ∣ a := by
      have : p ∣ a ^ 2 + a * b + b ^ 2 := hc ▸ hpc2
      have h3 : p ∣ a * b + b ^ 2 := dvd_add (dvd_mul_of_dvd_right h2 a) (dvd_pow h2 (by norm_num))
      have h4 : p ∣ a ^ 2 := by
        have : p ∣ a ^ 2 + (a * b + b ^ 2) := by rw [← add_assoc]; exact hc ▸ hpc2
        exact (Nat.dvd_add_left h3).mp this
      exact hp.dvd_of_dvd_pow h4
    exact hab ⟨h1, h2⟩
  have hp3 : p ≠ 3 := by
    rintro rfl; exact three_not_dvd_c a b c hcop hc hpc
  have hapb : ¬ p ∣ a + b := by
    intro h
    have h1 : p ∣ (a + b) ^ 2 := dvd_pow h (by norm_num)
    have h2 : (a + b) ^ 2 = c ^ 2 + a * b := by rw [hc]; ring
    have h3 : p ∣ a * b := (Nat.dvd_add_right hpc2).mp (h2 ▸ h1)
    rcases (Nat.Prime.dvd_mul hp).mp h3 with h4 | h4
    · exact hb ((Nat.dvd_add_right h4).mp h)
    · exact ha ((Nat.dvd_add_left h4).mp h)
  refine ⟨ha, hb, hapb, ?_, ?_, hp3⟩
  · intro h
    have h1 : p ∣ (a + 2 * b) ^ 2 := dvd_pow h (by norm_num)
    have h2 : (a + 2 * b) ^ 2 = c ^ 2 + 3 * (b * (a + b)) := by rw [hc]; ring
    have h3 : p ∣ 3 * (b * (a + b)) := (Nat.dvd_add_right hpc2).mp (h2 ▸ h1)
    rcases (Nat.Prime.dvd_mul hp).mp h3 with h4 | h4
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h4)
    · rcases (Nat.Prime.dvd_mul hp).mp h4 with h5 | h5
      · exact hb h5
      · exact hapb h5
  · intro h
    have h1 : p ∣ (2 * a + b) ^ 2 := dvd_pow h (by norm_num)
    have h2 : (2 * a + b) ^ 2 = c ^ 2 + 3 * (a * (a + b)) := by rw [hc]; ring
    have h3 : p ∣ 3 * (a * (a + b)) := (Nat.dvd_add_right hpc2).mp (h2 ▸ h1)
    rcases (Nat.Prime.dvd_mul hp).mp h3 with h4 | h4
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h4)
    · rcases (Nat.Prime.dvd_mul hp).mp h4 with h5 | h5
      · exact ha h5
      · exact hapb h5

theorem coprime_c (a b c : ℕ) (hcop : Nat.Coprime a b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    Nat.Coprime c a ∧ Nat.Coprime c b ∧ Nat.Coprime c (a + b) ∧ Nat.Coprime c (a + 2 * b) ∧
    Nat.Coprime c (2 * a + b) ∧ Nat.Coprime c 3 := by
  have h := fun p hp hpc => prime_dvd_c a b c hcop hc p hp hpc
  refine ⟨Nat.coprime_of_dvd fun p hp h1 h2 => (h p hp h1).1 h2,
    Nat.coprime_of_dvd fun p hp h1 h2 => (h p hp h1).2.1 h2,
    Nat.coprime_of_dvd fun p hp h1 h2 => (h p hp h1).2.2.1 h2,
    Nat.coprime_of_dvd fun p hp h1 h2 => (h p hp h1).2.2.2.1 h2,
    Nat.coprime_of_dvd fun p hp h1 h2 => (h p hp h1).2.2.2.2.1 h2,
    Nat.coprime_of_dvd fun p hp h1 h2 => (h p hp h1).2.2.2.2.2
      ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h2)⟩

theorem gcd3_one_of_yz {x y z : ℕ} (h : Nat.Coprime y z) : Nat.gcd (Nat.gcd x y) z = 1 :=
  Nat.eq_one_of_dvd_one (by
    rw [← h.gcd_eq_one]
    exact Nat.dvd_gcd ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)) (Nat.gcd_dvd_right _ _))

theorem gcd3_one_of_xz {x y z : ℕ} (h : Nat.Coprime x z) : Nat.gcd (Nat.gcd x y) z = 1 :=
  Nat.eq_one_of_dvd_one (by
    rw [← h.gcd_eq_one]
    exact Nat.dvd_gcd ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)) (Nat.gcd_dvd_right _ _))

theorem gcd3_one_of_xy {x y z : ℕ} (h : Nat.Coprime x y) : Nat.gcd (Nat.gcd x y) z = 1 := by
  rw [h.gcd_eq_one]; exact Nat.gcd_one_left z

/-- **Each side vector of the table is primitive** (`gcd = 1`), for every primitive `120°`-triple. -/
theorem vecGcd_one (s : Shape) (a b c : ℕ) (hcop : Nat.Coprime a b)
    (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    Nat.gcd (Nat.gcd (s.sideVec a b c).1 (s.sideVec a b c).2.1) (s.sideVec a b c).2.2 = 1 := by
  obtain ⟨hca, hcb, hcab, hca2b, hc2ab, hc3⟩ := coprime_c a b c hcop hc
  have hba : Nat.Coprime b a := hcop.symm
  have hb2 : Nat.Coprime b (a + 2 * b) := by
    simpa using (Nat.coprime_add_mul_right_right b a 2).mpr hba
  have ha2 : Nat.Coprime a (2 * a + b) := by
    simpa [add_comm] using (Nat.coprime_add_mul_right_right a b 2).mpr hcop
  cases s <;> simp only [Shape.sideVec]
  · simp
  · exact gcd3_one_of_xz hca2b
  · exact gcd3_one_of_xz hc2ab
  · exact gcd3_one_of_xy hca.symm
  · exact gcd3_one_of_xy hcb.symm
  · exact gcd3_one_of_yz (Nat.Coprime.pow_right 2 (Nat.coprime_mul_iff_left.mpr ⟨hcb.symm, hc2ab.symm⟩))
  · exact gcd3_one_of_xz (Nat.Coprime.pow_left 2 (Nat.Coprime.mul_right
      (Nat.Coprime.mul_right hc3 hcb) hcab))
  · exact gcd3_one_of_xz (Nat.Coprime.pow_left 2 (Nat.Coprime.mul_right
      (Nat.Coprime.mul_right hc3 hca) hcab))
  · exact gcd3_one_of_xy (Nat.coprime_mul_iff_left.mpr ⟨Nat.Coprime.mul_right hcop ha2,
      Nat.Coprime.mul_right hcb hc2ab⟩)
  · exact gcd3_one_of_xy (Nat.coprime_mul_iff_left.mpr ⟨Nat.Coprime.mul_right hba hb2,
      Nat.Coprime.mul_right hca hca2b⟩)
  · exact gcd3_one_of_xy hcop

/-! ## `prop:reduction`: arithmetic -/

/-- **`a + b` is never prime** for a `120°`-triple (`c² = a²+ab+b²`, `a,b > 0`).  Proof:
`c < a+b`, `c > a`, `c > b`, and `(c-a)(c+a) = b(a+b)`; a prime `p = a+b` would divide `c-a ∈ (0,b)` or
`c+a ∈ (0,2p)`, forcing `c+a = p`, i.e. `c = b`.  (Replaces the paper's discriminant
factorization of `3p²`; it needs no coprimality.) -/
theorem apb_not_prime (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ¬ Nat.Prime (a + b) := by
  intro hp
  have hab : 0 < a * b := Nat.mul_pos ha hb
  have hclt : c < a + b := by
    by_contra h; push Not at h; nlinarith
  have hca : a < c := by
    by_contra h; push Not at h; nlinarith
  have hcb : b < c := by
    by_contra h; push Not at h; nlinarith
  obtain ⟨d, hd⟩ : ∃ d, c = a + d := ⟨c - a, by omega⟩
  have hprod : d * (a + c) = b * (a + b) := by
    subst hd; nlinarith
  have hdvd : (a + b) ∣ d * (a + c) := ⟨b, by rw [hprod]; ring⟩
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
  · have : a + b ≤ d := Nat.le_of_dvd (by omega) h
    omega
  · obtain ⟨q, hq⟩ := h
    have hq2 : q < 2 := by
      by_contra hh; push Not at hh; nlinarith
    have hq0 : 0 < q := by
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · subst h0; omega
      · exact h0
    have : q = 1 := by omega
    subst this
    omega

/-- **`F₁`**: `N b = k²(a+b)` forces `N` composite. -/
theorem F1_not_prime (a b c k N : ℕ) (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) (hk : 0 < k) (h : N * b = k ^ 2 * (a + b)) :
    ¬ Nat.Prime N := by
  have hcb : Nat.Coprime b (a + b) := Nat.coprime_add_self_right.mpr hcop.symm
  have hbk : b ∣ k ^ 2 := by
    have : b ∣ k ^ 2 * (a + b) := ⟨N, by rw [← h]; ring⟩
    exact hcb.dvd_of_dvd_mul_right this
  obtain ⟨t, ht⟩ := hbk
  have hN : N = t * (a + b) := by
    have : N * b = (t * (a + b)) * b := by rw [h, ht]; ring
    exact Nat.eq_of_mul_eq_mul_right hb this
  have ht0 : t ≠ 0 := by
    rintro rfl; simp at ht; omega
  intro hp
  by_cases ht1 : t = 1
  · subst ht1
    have hN' : N = a + b := by simpa using hN
    rw [hN'] at hp
    exact apb_not_prime a b c ha hb hc hp
  · exact Nat.not_prime_mul ht1 (by omega) (hN ▸ hp)

theorem not_prime_sq (k N : ℕ) (h : N = k ^ 2) : ¬ Nat.Prime N := by
  intro hp
  have hk : k ∣ N := ⟨k, by rw [h]; ring⟩
  rcases hp.eq_one_or_self_of_dvd k hk with h1 | h1
  · rw [h1] at h; simp at h; exact hp.one_lt.ne' h
  · have := hp.two_le
    rw [h1] at h; nlinarith

/-- **The arithmetic content of `prop:reduction`.**  For every shape other than the equilateral and
the two isosceles ones, the area equation `N = k² N₀` (`k ≥ 1`) makes `N` composite.  (`k²N₀` with
`N₀ = xy`, `x,y ≥ 3` for `F₂,F₄`; `3 ∣ N` for `F₃`; `N = t(a+b)` with `a+b` composite for `F₁`;
`N = k²` tile-similar.) -/
theorem not_prime_of_areaEq (s : Shape)
    (hs : s ≠ .equilateral ∧ s ≠ .isoAlpha ∧ s ≠ .isoBeta)
    (a b c k N : ℕ) (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) (hk : 0 < k) (h : s.AreaEq a b k N) : ¬ Nat.Prime N := by
  have hk2 : 0 < k ^ 2 := by positivity
  have hcs : c ^ 2 = b ^ 2 + b * a + a ^ 2 := by rw [hc]; ring
  cases s with
  | equilateral => exact absurd rfl hs.1
  | isoAlpha => exact absurd rfl hs.2.1
  | isoBeta => exact absurd rfl hs.2.2
  | F1 => exact F1_not_prime a b c k N ha hb hcop hc hk (by simpa [Shape.AreaEq, Shape.den, Shape.num] using h)
  | F1' =>
    exact F1_not_prime b a c k N hb ha hcop.symm hcs hk
      (by simpa [Shape.AreaEq, Shape.den, Shape.num, add_comm] using h)
  | F2 =>
    simp only [Shape.AreaEq, Shape.den, Shape.num, mul_one] at h
    rw [h]
    have : k ^ 2 * ((a + 2 * b) * (2 * a + b)) = (k ^ 2 * (a + 2 * b)) * (2 * a + b) := by ring
    rw [this]; exact Nat.not_prime_mul (by nlinarith) (by omega)
  | F3 =>
    simp only [Shape.AreaEq, Shape.den, Shape.num, mul_one] at h
    rw [h]
    have : k ^ 2 * (3 * (a + b) * (a + 2 * b)) = (3 * k ^ 2 * (a + b)) * (a + 2 * b) := by ring
    rw [this]; exact Nat.not_prime_mul (by nlinarith) (by omega)
  | F3' =>
    simp only [Shape.AreaEq, Shape.den, Shape.num, mul_one] at h
    rw [h]
    have : k ^ 2 * (3 * (a + b) * (2 * a + b)) = (3 * k ^ 2 * (a + b)) * (2 * a + b) := by ring
    rw [this]; exact Nat.not_prime_mul (by nlinarith) (by omega)
  | F4 =>
    simp only [Shape.AreaEq, Shape.den, Shape.num, mul_one] at h
    rw [h]
    have : k ^ 2 * ((a + b) * (2 * a + b)) = (k ^ 2 * (a + b)) * (2 * a + b) := by ring
    rw [this]; exact Nat.not_prime_mul (by nlinarith) (by omega)
  | F4' =>
    simp only [Shape.AreaEq, Shape.den, Shape.num, mul_one] at h
    rw [h]
    have : k ^ 2 * ((a + b) * (a + 2 * b)) = (k ^ 2 * (a + b)) * (a + 2 * b) := by ring
    rw [this]; exact Nat.not_prime_mul (by nlinarith) (by omega)
  | tileSimilar =>
    simp only [Shape.AreaEq, Shape.den, Shape.num, mul_one] at h
    exact not_prime_sq k N h

/-- **`prop:reduction`, arithmetic form.**  A prime `N` with `N = k² N₀` for the shape `s` forces
`s ∈ {equilateral, iso α, iso β}`; the equilateral case is the cited input (Beeson), NOT excluded
here.  The isosceles shapes are never equilateral (`corners_injective`). -/
theorem prime_forces_iso_or_equi (s : Shape) (a b c k N : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hcop : Nat.Coprime a b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) (hk : 0 < k)
    (h : s.AreaEq a b k N) (hp : Nat.Prime N) :
    s = .equilateral ∨ s = .isoAlpha ∨ s = .isoBeta := by
  by_contra hne
  push Not at hne
  exact not_prime_of_areaEq s hne a b c k N ha hb hcop hc hk h hp

theorem iso_not_equilateral : Shape.isoAlpha.corners ≠ Shape.equilateral.corners ∧
    Shape.isoBeta.corners ≠ Shape.equilateral.corners := by decide

/-! ## `prop:otherspectra` -/

/-- **`F₁` clause.**  `N b = k²(a+b)`, `b = d e²`, `d` squarefree: `k = d e w`, `N = d w² (a+b)`. -/
theorem F1_scale (a b d e k N : ℕ) (hb : 0 < b) (hcop : Nat.Coprime a b) (hbde : b = d * e ^ 2)
    (hd : Squarefree d) (hk : 0 < k) (h : N * b = k ^ 2 * (a + b)) :
    ∃ w : ℕ, 0 < w ∧ k = d * e * w ∧ N = d * w ^ 2 * (a + b) := by
  have hcb : Nat.Coprime b (a + b) := Nat.coprime_add_self_right.mpr hcop.symm
  have hbk2 : b ∣ k ^ 2 := by
    have : b ∣ k ^ 2 * (a + b) := ⟨N, by rw [← h]; ring⟩
    exact hcb.dvd_of_dvd_mul_right this
  obtain ⟨w, hw⟩ := Erdos634.AdmissibleSpectrum.sqfree_scale_dvd hbde hd hk.ne' hbk2
  have hwpos : 0 < w := by
    rcases Nat.eq_zero_or_pos w with h0 | h0
    · subst h0; simp at hw; omega
    · exact h0
  refine ⟨w, hwpos, hw, ?_⟩
  have : N * b = (d * w ^ 2 * (a + b)) * b := by rw [h, hw, hbde]; ring
  exact Nat.eq_of_mul_eq_mul_right hb this

/-- **`F₂,F₃,F₄` clause**: the area equation IS `N = N₀ k²` with the listed `N₀`
(`(a+2b)(2a+b)`, `3(a+b)(a+2b)`, `(a+b)(2a+b)`); and tile-similar `N = n²`. -/
theorem scalene_N0 (a b k N : ℕ) :
    (Shape.F2.AreaEq a b k N ↔ N = (a + 2 * b) * (2 * a + b) * k ^ 2) ∧
    (Shape.F3.AreaEq a b k N ↔ N = 3 * (a + b) * (a + 2 * b) * k ^ 2) ∧
    (Shape.F4.AreaEq a b k N ↔ N = (a + b) * (2 * a + b) * k ^ 2) ∧
    (Shape.tileSimilar.AreaEq a b k N ↔ N = k ^ 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Shape.AreaEq, Shape.den, Shape.num, mul_one] <;>
    constructor <;> intro h <;> linarith

/-- **Equilateral clause.**  `N ab = S²` (`S > 0`): `ab ∣ S²`, `N = S²/(ab)`, and `N`, `ab` have the
same parity of `p`-adic valuation at every prime (= same squarefree kernel).  The divisibilities
`(c+a-b) ∣ 3S`, `(c+b-a) ∣ 3S` follow from the integer invariant values `M_α X = 3S`, `M_β Y = 3S`
(supplied by `cor:int` for a real dissection; hypotheses here). -/
theorem equilateral_clauses (a b c N S : ℕ) (hS : 0 < S) (h : Shape.equilateral.AreaEq a b S N)
    (Ma Mb : ℤ) (hMa : Ma * ((c : ℤ) + a - b) = 3 * S) (hMb : Mb * ((c : ℤ) + b - a) = 3 * S) :
    a * b ∣ S ^ 2 ∧ N = S ^ 2 / (a * b) ∧
    (∀ p : ℕ, N.factorization p % 2 = (a * b).factorization p % 2) ∧
    ((c : ℤ) + a - b) ∣ 3 * S ∧ ((c : ℤ) + b - a) ∣ 3 * S := by
  simp only [Shape.AreaEq, Shape.den, Shape.num, mul_one] at h
  have hS2 : 0 < S ^ 2 := by positivity
  have hN0 : N ≠ 0 := by rintro rfl; rw [zero_mul] at h; omega
  have hab0 : a * b ≠ 0 := by intro h0; rw [h0, mul_zero] at h; omega
  refine ⟨⟨N, by rw [← h]; ring⟩, ?_, fun p => ?_, ⟨Ma, by rw [← hMa]; ring⟩, ⟨Mb, by rw [← hMb]; ring⟩⟩
  · rw [← h, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hab0)]
  · exact Erdos634.AdmissibleSpectrum.same_valuation_parity hN0 hab0 h p

/-! ## Non-vacuity and controls -/

/-- Table check on the tile `(3,5,7)`: `F₂` has `N₀ = (3+10)(6+5) = 143`; the vector
`(3·13, 5·11, 49) = (39,55,49)`; Heron identity at these numbers. -/
theorem witness_F2_357 :
    Shape.F2.sideVec 3 5 7 = (39, 55, 49) ∧ Shape.F2.num 3 5 = 143 ∧
    Nat.gcd (Nat.gcd 39 55) 49 = 1 := by decide

/-- Non-vacuity of `AreaEq`: the isosceles `α` shape on the tile `(3,5,7)` has the solution
`N = 65`, `k = 5` (`65·5 = 25·13`).  (`65` is composite, so this is the shape table agreeing with
`prop:reduction`'s claim only the *isosceles* shapes can carry a prime `N`: for them
`not_prime_of_areaEq` is, correctly, not available.) -/
theorem iso_shapes_not_excluded_by_table :
    ∃ N k : ℕ, 0 < k ∧ Shape.isoAlpha.AreaEq 3 5 k N ∧ N = 65 ∧ k = 5 := ⟨65, 5, by norm_num, by decide, rfl, rfl⟩

end Erdos634.Draft.FDDShapes

#print axioms Erdos634.Draft.FDDShapes.shapes_complete
#print axioms Erdos634.Draft.FDDShapes.shapes_sound
#print axioms Erdos634.Draft.FDDShapes.corners_injective
#print axioms Erdos634.Draft.FDDShapes.corners_reflect
#print axioms Erdos634.Draft.FDDShapes.heron_table
#print axioms Erdos634.Draft.FDDShapes.vecGcd_one
#print axioms Erdos634.Draft.FDDShapes.apb_not_prime
#print axioms Erdos634.Draft.FDDShapes.not_prime_of_areaEq
#print axioms Erdos634.Draft.FDDShapes.prime_forces_iso_or_equi
#print axioms Erdos634.Draft.FDDShapes.F1_scale
#print axioms Erdos634.Draft.FDDShapes.scalene_N0
#print axioms Erdos634.Draft.FDDShapes.equilateral_clauses
