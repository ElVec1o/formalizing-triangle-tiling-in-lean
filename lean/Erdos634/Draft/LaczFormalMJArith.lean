import Erdos634.Draft.LaczFormalW2Arith

/-!
# Rule `M(j)`: the arithmetic (A) of `PROOF_BAND.md` §1 for every `j`

Erdős #634, base-`β` band.  Credit: AI assistant (item 3, band program, arithmetic (A)), Beeson–Roșu (Lemma 28:
the relation lattice `K`), Beeson, Laczkovich, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.

Tile `(a,b,c) = (ef, f²−e², f²)`, `1 ≤ e < f`, `gcd(e,f) = 1`.  Stand-alone theorems for all such `(e,f)`
and all `j` in the stated range (not numerical checks; the range was also brute-forced, see (private working notes, not included)):

* `MJ_jb_unique` : `1 ≤ j < f`, `x a + y b + z c = j b` forces `(x,y,z) = (0,j,0)`.
* `MJ_jc_unique` : `j < e`, `x a + y b + z c = j c` forces `(x,y,z) = (0,0,j)`.
* `MJ_jc_sub_b`  : `j < f`: `j c − b` is not a sum of side lengths.
* `MJ_ec_eq_fa`  : NEGATIVE CONTROL: `e c = f a`, so `MJ_jc_unique` fails exactly at `j = e`
  (this is why the range of `M(j)` is sharp: `j ≤ e` uses `(j−1) < e`).
The proofs use only the relation lattice `relation_lattice`.
-/

namespace Erdos634.LaczJunction

/-- `j b` has only the decomposition `b^j` for `1 ≤ j < f`. -/
theorem MJ_jb_unique (e f x y z j : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (hj : j < f) (h : x * ta e f + y * tb e f + z * tc e f = j * tb e f) :
    x = 0 ∧ y = j ∧ z = 0 := by
  have hb := tb_cast e f hef
  have hZ : (x : ℤ) * (e * f) + ((y : ℤ) - j) * ((f:ℤ)^2 - (e:ℤ)^2) + z * (f:ℤ)^2 = 0 := by
    have := congrArg (fun n : ℕ => (n : ℤ)) h
    simp only [ta, tc] at this
    push_cast at this
    rw [hb] at this
    linarith
  obtain ⟨η, ζ, hx, hy, hz⟩ := relation_lattice e f he hef hcop (x : ℤ) ((y : ℤ) - j) (z : ℤ) hZ
  have he' : (1 : ℤ) ≤ e := by exact_mod_cast he
  have hef' : (e : ℤ) < f := by exact_mod_cast hef
  have hj' : (j : ℤ) < f := by exact_mod_cast hj
  have hx0 : (0 : ℤ) ≤ x := by positivity
  have hy0 : (0 : ℤ) ≤ y := by positivity
  have hz0 : (0 : ℤ) ≤ z := by positivity
  have hη0 : 0 ≤ η := by
    by_contra hneg
    push_neg at hneg
    nlinarith
  have hη1 : η = 0 := by
    by_contra hne
    have hη : 1 ≤ η := by omega
    have hz' : (z : ℤ) = ζ * e - η * f := by linarith
    have hζ : η < ζ := by
      by_contra hc
      push_neg at hc
      nlinarith
    nlinarith
  subst hη1
  have hζ1 : ζ = 0 := by
    have h1 : (x : ℤ) = -ζ * f := by linarith
    have h2 : (z : ℤ) = ζ * e := by linarith
    have : ζ ≤ 0 := by nlinarith
    have : 0 ≤ ζ := by nlinarith
    omega
  subst hζ1
  refine ⟨by exact_mod_cast (by linarith : (x:ℤ) = 0), ?_, by exact_mod_cast (by linarith : (z:ℤ) = 0)⟩
  exact_mod_cast (by linarith : (y : ℤ) = j)

/-- `j c` has only the decomposition `c^j` for `j < e`. -/
theorem MJ_jc_unique (e f x y z j : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (hj : j < e) (h : x * ta e f + y * tb e f + z * tc e f = j * tc e f) :
    x = 0 ∧ y = 0 ∧ z = j := by
  have hb := tb_cast e f hef
  have hZ : (x : ℤ) * (e * f) + y * ((f:ℤ)^2 - (e:ℤ)^2) + ((z : ℤ) - j) * (f:ℤ)^2 = 0 := by
    have := congrArg (fun n : ℕ => (n : ℤ)) h
    simp only [ta, tc] at this
    push_cast at this
    rw [hb] at this
    linarith
  obtain ⟨η, ζ, hx, hy, hz⟩ := relation_lattice e f he hef hcop (x : ℤ) (y : ℤ) ((z : ℤ) - j) hZ
  have he' : (1 : ℤ) ≤ e := by exact_mod_cast he
  have hef' : (e : ℤ) < f := by exact_mod_cast hef
  have hj' : (j : ℤ) < e := by exact_mod_cast hj
  have hx0 : (0 : ℤ) ≤ x := by positivity
  have hy0 : (0 : ℤ) ≤ y := by positivity
  have hz0 : (0 : ℤ) ≤ z := by positivity
  have hη0 : 0 ≤ η := by
    by_contra hneg
    push_neg at hneg
    nlinarith
  have hη1 : η = 0 := by
    by_contra hne
    have hη : 1 ≤ η := by omega
    have hζ : ζ < η := by
      by_contra hc
      push_neg at hc
      nlinarith
    nlinarith
  subst hη1
  have hζ1 : ζ = 0 := by
    have h1 : (x : ℤ) = -ζ * f := by linarith
    have h2 : (z : ℤ) = ζ * e + j := by linarith
    have : ζ ≤ 0 := by nlinarith
    have : 0 ≤ ζ := by nlinarith
    omega
  subst hζ1
  refine ⟨by exact_mod_cast (by linarith : (x:ℤ) = 0), by exact_mod_cast (by linarith : (y:ℤ) = 0), ?_⟩
  exact_mod_cast (by linarith : (z : ℤ) = j)

/-- `j c − b` is not a sum of side lengths, `j < f`. -/
theorem MJ_jc_sub_b (e f x y z j : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (hj : j < f) : x * ta e f + y * tb e f + z * tc e f + tb e f ≠ j * tc e f := by
  intro h
  have hb := tb_cast e f hef
  have hZ : (x : ℤ) * (e * f) + ((y : ℤ) + 1) * ((f:ℤ)^2 - (e:ℤ)^2) + ((z : ℤ) - j) * (f:ℤ)^2 = 0 := by
    have := congrArg (fun n : ℕ => (n : ℤ)) h
    simp only [ta, tc] at this
    push_cast at this
    rw [hb] at this
    linarith
  obtain ⟨η, ζ, hx, hy, hz⟩ :=
    relation_lattice e f he hef hcop (x : ℤ) ((y : ℤ) + 1) ((z : ℤ) - j) hZ
  have he' : (1 : ℤ) ≤ e := by exact_mod_cast he
  have hef' : (e : ℤ) < f := by exact_mod_cast hef
  have hj' : (j : ℤ) < f := by exact_mod_cast hj
  have hx0 : (0 : ℤ) ≤ x := by positivity
  have hy0 : (0 : ℤ) ≤ y := by positivity
  have hz0 : (0 : ℤ) ≤ z := by positivity
  have hη1 : 1 ≤ η := by
    by_contra hneg
    push_neg at hneg
    nlinarith
  have hζ : ζ < η := by
    by_contra hc
    push_neg at hc
    nlinarith
  nlinarith

/-- NEGATIVE CONTROL: `e c = f a`.  So `MJ_jc_unique` is false at `j = e`. -/
theorem MJ_ec_eq_fa (e f : ℕ) : e * tc e f = f * ta e f := by
  unfold tc ta; ring

theorem MJ_jc_unique_fails_at_e (e f : ℕ) (he : 1 ≤ e) (hf : 1 ≤ f) :
    ¬ (∀ x y z : ℕ, x * ta e f + y * tb e f + z * tc e f = e * tc e f → x = 0 ∧ y = 0 ∧ z = e) := by
  intro H
  have := H f 0 0 (by rw [MJ_ec_eq_fa]; ring)
  omega

#print axioms MJ_jb_unique
#print axioms MJ_jc_unique
#print axioms MJ_jc_sub_b

end Erdos634.LaczJunction
