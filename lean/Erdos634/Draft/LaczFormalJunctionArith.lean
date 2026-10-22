import Mathlib.Tactic

/-!
# Band junction rules: the pure arithmetic (Erdős #634, base-`β` band)

Formalizes the arithmetic facts used in the hand proof of the band junction rules
((private working notes, not included), audit `AUDIT_C1.md`).  Credit: AI assistant (the band
lemma / item-3 proposal and the C1/C2/C3 observations), Beeson–Roșu (base-`β` tiles and band
grammar), Beeson, Laczkovich, Paliy.

Tile `(a,b,c) = (ef, f²−e², f²)`, `1 ≤ e < f`, `gcd(e,f)=1`.

* `a_not_dvd_b` — `a ∤ b` for every coprime `f > e ≥ 1`.
* `b_lt_c`.
* `cover_unique` — `x a + y b + z c = b` forces `(x,y,z) = (0,1,0)`.
* `band_f_gt_three_e` — the band `f ≤ 2Me < f+e`, `M ≥ 2` gives `f > 3e`.
* `band_a_lt_b` — hence `b > a` (used by rules I, Im).
* `L_gt_a` — the side length `L = Me(3f²−e²)` exceeds `a`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.LaczJunction

def ta (e f : ℕ) : ℕ := e * f
def tb (e f : ℕ) : ℕ := f ^ 2 - e ^ 2
def tc (_e f : ℕ) : ℕ := f ^ 2

/-- `a ∤ b` for all coprime `f > e ≥ 1` (thin or thick). -/
theorem a_not_dvd_b (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f) :
    ¬ ta e f ∣ tb e f := by
  intro h
  have hfd : f ∣ f ^ 2 - e ^ 2 := Dvd.dvd.trans (Dvd.intro_left e rfl) h
  have hle : e ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left hef.le 2
  have hf2 : f ∣ f ^ 2 := Dvd.intro_left f (by ring)
  have hfe : f ∣ e ^ 2 := by
    have := (Nat.dvd_sub hf2 hfd)
    rwa [Nat.sub_sub_self hle] at this
  have hc : Nat.Coprime f (e ^ 2) := (Nat.Coprime.pow_right 2 hcop.symm)
  have := Nat.Coprime.eq_one_of_dvd hc hfe
  omega

theorem b_lt_c (e f : ℕ) (he : 1 ≤ e) (hef : e < f) : tb e f < tc e f := by
  unfold tb tc
  have : 0 < e ^ 2 := by positivity
  have : e ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left hef.le 2
  omega

theorem a_pos (e f : ℕ) (he : 1 ≤ e) (hef : e < f) : 0 < ta e f := by
  unfold ta; exact Nat.mul_pos (by omega) (by omega)

theorem b_pos (e f : ℕ) (he : 1 ≤ e) (hef : e < f) : 0 < tb e f := by
  unfold tb
  have : e ^ 2 < f ^ 2 := Nat.pow_lt_pow_left hef (by norm_num)
  omega

/-- The only way to write `b` as a sum of side lengths from `{a,b,c}` is `b` itself. -/
theorem cover_unique (e f x y z : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (h : x * ta e f + y * tb e f + z * tc e f = tb e f) : x = 0 ∧ y = 1 ∧ z = 0 := by
  have hbc := b_lt_c e f he hef
  have hb := b_pos e f he hef
  have ha := a_pos e f he hef
  have hz : z = 0 := by
    by_contra hz
    have : tc e f ≤ z * tc e f := Nat.le_mul_of_pos_left _ (by omega)
    omega
  subst hz
  simp only [zero_mul, add_zero] at h
  have hy : y ≤ 1 := by
    by_contra hy
    have : 2 * tb e f ≤ y * tb e f := Nat.mul_le_mul_right _ (by omega)
    omega
  interval_cases y
  · exfalso
    simp only [zero_mul, add_zero] at h
    exact a_not_dvd_b e f he hef hcop ⟨x, by rw [← h]; ring⟩
  · have hx : x * ta e f = 0 := by omega
    rcases Nat.mul_eq_zero.mp hx with h0 | h0
    · exact ⟨h0, rfl, rfl⟩
    · omega

/-- Band: `f ≤ 2Me < f+e` and `M ≥ 2` give `f > 3e`. -/
theorem band_f_gt_three_e (e f M : ℕ) (he : 1 ≤ e) (hM : 2 ≤ M)
    (h2 : 2 * M * e < f + e) : 3 * e < f := by
  have : 2 * e ≤ M * e := Nat.mul_le_mul_right _ hM
  nlinarith

/-- In the band, `b > a`. -/
theorem band_a_lt_b (e f M : ℕ) (he : 1 ≤ e) (hM : 2 ≤ M) (h2 : 2 * M * e < f + e) :
    ta e f < tb e f := by
  have h3 := band_f_gt_three_e e f M he hM h2
  unfold ta tb
  have hle : e ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have : e * f + e ^ 2 < f ^ 2 := by nlinarith
  omega

/-- `H3`: the side length `L = Me(3f²−e²)` exceeds `a = ef` (needs only `M ≥ 1`, `f > e ≥ 1`). -/
theorem L_gt_a (e f M : ℕ) (he : 1 ≤ e) (hef : e < f) (hM : 1 ≤ M) :
    ta e f < M * e * (3 * f ^ 2 - e ^ 2) := by
  unfold ta
  have hle : e ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left hef.le 2
  have h1 : 2 * f ^ 2 ≤ 3 * f ^ 2 - e ^ 2 := by omega
  have h2 : f ≤ 2 * f ^ 2 := by nlinarith
  have h3 : f < 3 * f ^ 2 - e ^ 2 := by
    have : 0 < f := by omega
    nlinarith
  have h4 : e * f < e * (3 * f ^ 2 - e ^ 2) := Nat.mul_lt_mul_of_pos_left h3 (by omega)
  have h5 : e * (3 * f ^ 2 - e ^ 2) ≤ M * e * (3 * f ^ 2 - e ^ 2) := by
    have : e ≤ M * e := Nat.le_mul_of_pos_left _ (by omega)
    exact Nat.mul_le_mul_right _ this
  omega

/-! ## Sanity checks (bounded exhaustive, kernel `decide`/`#eval`) -/

/-- `a ∤ b` for every coprime pair `1 ≤ e < f < 60`. -/
def checkNotDvd : Bool :=
  (List.range 60).all fun f => (List.range f).all fun e =>
    e < 1 || !(Nat.gcd e f == 1) || !(tb e f % ta e f == 0)

/-- Every band row `(e,f,M)` with `M ∈ [2,10]`, `f ≤ 2Me < f+e`, `f < 200` has `b>a` and `L>a`. -/
def checkBand : Bool :=
  (List.range 200).all fun f => (List.range f).all fun e =>
    (List.range 11).all fun M =>
      e < 1 || M < 2 || !(f ≤ 2 * M * e && 2 * M * e < f + e && Nat.gcd e f == 1) ||
        (decide (ta e f < tb e f) && decide (ta e f < M * e * (3 * f ^ 2 - e ^ 2)))

#eval checkNotDvd
#eval checkBand
theorem checkNotDvd_true : checkNotDvd = true := by native_decide

#print axioms a_not_dvd_b
#print axioms cover_unique
#print axioms band_a_lt_b
#print axioms L_gt_a

end Erdos634.LaczJunction
