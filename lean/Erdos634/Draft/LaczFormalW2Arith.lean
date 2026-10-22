import Erdos634.Draft.LaczFormalJunctionArith

/-!
# Rule W2: the arithmetic facts D1-D4 and the relation lattice, for all `e, f`

Erdős #634, base-`β` band.  Credit: AI assistant (item 3, band program), Beeson–Roșu (Lemma 28: the
relation lattice `K`), Beeson, Laczkovich, Paliy.  Hand proof: `PROOF_W2.md`, `PROOF_U.md` Part A
((private working notes, not included)); the audit re-derived D2, D3 independently.

Tile `(a,b,c) = (ef, f²−e², f²)`, `1 ≤ e < f`, `gcd(e,f) = 1`.  Everything is a stand-alone theorem
for *all* such `(e,f)` (not a numerical check):

* `D1_a_not_dvd_b` (restated from `a_not_dvd_b`): `a ∤ b`.
* `D2_two_b` : for `f ≥ 3`, `x a + y b + z c = 2b` forces `(x,y,z) = (0,2,0)`.
* `D3_c_unique` : for `e ≥ 2`, `x a + y b + z c = c` forces `(x,y,z) = (0,0,1)`.
  (False for `e = 1`: `c = f·a`; `D3_fails_e1` is the explicit negative control.)
* `D4_b_sub_a` : `b − a` is not a sum of side lengths, i.e. `x a + y b + z c + a = b` is impossible.
  (No hypothesis `a < b` is needed.)
* `c_sub_b_lt_a` : `c − b = e² < ef = a`.
* `relation_lattice` : every integer solution of `p a + q b + r c = 0` is
  `(p,q,r) = η(e,f,−f) + ζ(−f,0,e)` (the lattice `K` of BR Lemma 28).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

namespace Erdos634.LaczJunction

theorem tb_cast (e f : ℕ) (hef : e < f) : (tb e f : ℤ) = (f : ℤ) ^ 2 - (e : ℤ) ^ 2 := by
  unfold tb
  have : e ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left hef.le 2
  push_cast [Nat.cast_sub this]
  ring

/-- `D1`. -/
theorem D1_a_not_dvd_b (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f) :
    ¬ ta e f ∣ tb e f := a_not_dvd_b e f he hef hcop

/-- `c − b = e² < a`. -/
theorem c_sub_b_lt_a (e f : ℕ) (he : 1 ≤ e) (hef : e < f) :
    tc e f - tb e f = e ^ 2 ∧ e ^ 2 < ta e f := by
  unfold tc tb ta
  have : e ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left hef.le 2
  constructor
  · omega
  · nlinarith

/-- `D2`: the only way to write `2b` as a sum of side lengths is `b + b` (needs `f ≥ 3`). -/
theorem D2_two_b (e f x y z : ℕ) (he : 1 ≤ e) (hef : e < f) (hf3 : 3 ≤ f)
    (hcop : Nat.Coprime e f)
    (h : x * ta e f + y * tb e f + z * tc e f = 2 * tb e f) : x = 0 ∧ y = 2 ∧ z = 0 := by
  have hb := tb_cast e f hef
  have hZ : (x : ℤ) * (e * f) + y * ((f:ℤ)^2 - (e:ℤ)^2) + z * (f:ℤ)^2 =
      2 * ((f:ℤ)^2 - (e:ℤ)^2) := by
    have := congrArg (fun n : ℕ => (n : ℤ)) h
    simp only [ta, tc] at this
    push_cast at this
    rw [hb] at this
    linarith
  have hdvd : (f : ℤ) ∣ (e : ℤ) ^ 2 * ((y : ℤ) - 2) :=
    ⟨x * e + y * f + z * f - 2 * f, by linear_combination (-1 : ℤ) * hZ⟩
  have hcopZ : IsCoprime (f : ℤ) ((e : ℤ) ^ 2) := by
    have : Nat.Coprime f (e ^ 2) := Nat.Coprime.pow_right 2 hcop.symm
    simpa using Nat.isCoprime_iff_coprime.mpr this
  have hdy : (f : ℤ) ∣ (y : ℤ) - 2 := by
    have := hcopZ.dvd_of_dvd_mul_left hdvd
    exact this
  obtain ⟨η, hη⟩ := hdy
  have hfpos : (0 : ℤ) < f := by exact_mod_cast (by omega : 0 < f)
  have hf3Z : (3 : ℤ) ≤ f := by exact_mod_cast hf3
  have hbpos : (0 : ℤ) < (f:ℤ)^2 - (e:ℤ)^2 := by
    have : (e:ℤ) < f := by exact_mod_cast hef
    have : (0:ℤ) < e := by exact_mod_cast he
    nlinarith
  have hy0 : (0 : ℤ) ≤ y := by exact_mod_cast Nat.zero_le y
  have hx0 : (0 : ℤ) ≤ x := by exact_mod_cast Nat.zero_le x
  have hz0 : (0 : ℤ) ≤ z := by exact_mod_cast Nat.zero_le z
  have hxe : (0:ℤ) ≤ (x:ℤ) * (e * f) := by positivity
  have hzf : (0:ℤ) ≤ (z:ℤ) * (f:ℤ)^2 := by positivity
  have hη0 : η = 0 := by
    rcases lt_trichotomy η 0 with hlt | heq | hgt
    · exfalso
      have : (y : ℤ) ≤ 2 - f := by
        have : η ≤ -1 := by omega
        nlinarith
      linarith
    · exact heq
    · exfalso
      have hy2 : (y : ℤ) ≥ 2 + f := by
        have : η ≥ 1 := by omega
        nlinarith
      have : (y : ℤ) * ((f:ℤ)^2 - (e:ℤ)^2) ≥ (2 + f) * ((f:ℤ)^2 - (e:ℤ)^2) :=
        mul_le_mul_of_nonneg_right hy2 hbpos.le
      nlinarith
  subst hη0
  have hy : (y : ℤ) = 2 := by linarith
  rw [hy] at hZ
  have hxz : (x : ℤ) * (e * f) + z * (f:ℤ)^2 = 0 := by linarith
  have hef0 : (0:ℤ) < (e:ℤ) * f := by
    have : (0:ℤ) < e := by exact_mod_cast he
    positivity
  have hx : (x : ℤ) = 0 := by
    by_contra hx'
    have : (0:ℤ) < x := lt_of_le_of_ne hx0 (Ne.symm hx')
    nlinarith
  have hz : (z : ℤ) = 0 := by
    have : z * (f:ℤ)^2 = 0 := by rw [hx] at hxz; linarith
    have hf2 : (0:ℤ) < (f:ℤ)^2 := by positivity
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hf2.ne'
  refine ⟨by exact_mod_cast hx, ?_, by exact_mod_cast hz⟩
  exact_mod_cast hy

/-- `D3`: the only way to write `c` as a sum of side lengths is `c` itself (needs `e ≥ 2`). -/
theorem D3_c_unique (e f x y z : ℕ) (he : 2 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (h : x * ta e f + y * tb e f + z * tc e f = tc e f) : x = 0 ∧ y = 0 ∧ z = 1 := by
  have hb := tb_cast e f hef
  have he1 : 1 ≤ e := by omega
  have hZ : (x : ℤ) * (e * f) + y * ((f:ℤ)^2 - (e:ℤ)^2) + z * (f:ℤ)^2 = (f:ℤ)^2 := by
    have := congrArg (fun n : ℕ => (n : ℤ)) h
    simp only [ta, tc] at this
    push_cast at this
    rw [hb] at this
    linarith
  have hcopZ : IsCoprime (f : ℤ) ((e : ℤ) ^ 2) := by
    have : Nat.Coprime f (e ^ 2) := Nat.Coprime.pow_right 2 hcop.symm
    simpa using Nat.isCoprime_iff_coprime.mpr this
  have hcopE : IsCoprime (f : ℤ) (e : ℤ) := by
    simpa using Nat.isCoprime_iff_coprime.mpr hcop.symm
  have hdvd : (f : ℤ) ∣ (e : ℤ) ^ 2 * (y : ℤ) :=
    ⟨x * e + y * f + z * f - f, by linear_combination (-1 : ℤ) * hZ⟩
  obtain ⟨η, hη⟩ := hcopZ.dvd_of_dvd_mul_left hdvd
  have hfpos : (0 : ℤ) < f := by exact_mod_cast (by omega : 0 < f)
  have hbpos : (0 : ℤ) < (f:ℤ)^2 - (e:ℤ)^2 := by
    have : (e:ℤ) < f := by exact_mod_cast hef
    have : (0:ℤ) < e := by exact_mod_cast he1
    nlinarith
  have hy0 : (0 : ℤ) ≤ y := by exact_mod_cast Nat.zero_le y
  have hx0 : (0 : ℤ) ≤ x := by exact_mod_cast Nat.zero_le x
  have hz0 : (0 : ℤ) ≤ z := by exact_mod_cast Nat.zero_le z
  have heZ : (2:ℤ) ≤ e := by exact_mod_cast he
  have hefZ : (e:ℤ) < f := by exact_mod_cast hef
  have hxe : (0:ℤ) ≤ (x:ℤ) * (e * f) := by positivity
  have hzf : (0:ℤ) ≤ (z:ℤ) * (f:ℤ)^2 := by positivity
  have hη0 : η = 0 := by
    rcases lt_trichotomy η 0 with hlt | heq | hgt
    · exfalso
      have : (y:ℤ) < 0 := by rw [hη]; nlinarith
      linarith
    · exact heq
    · exfalso
      have hy2 : (y : ℤ) ≥ f := by
        rw [hη]; nlinarith
      have h1 : (y : ℤ) * ((f:ℤ)^2 - (e:ℤ)^2) ≥ (f:ℤ) * ((f:ℤ)^2 - (e:ℤ)^2) :=
        mul_le_mul_of_nonneg_right hy2 hbpos.le
      have h2 : (f:ℤ) * ((f:ℤ)^2 - (e:ℤ)^2) > (f:ℤ)^2 := by
        have : (f:ℤ)^2 - (e:ℤ)^2 ≥ f + e := by nlinarith
        nlinarith
      nlinarith
  subst hη0
  have hy : (y : ℤ) = 0 := by rw [hη]; ring
  rw [hy] at hZ
  -- x e + z f = f
  have hxz : (x : ℤ) * e + z * f = f := by
    have : (f:ℤ) * ((x:ℤ) * e + z * f - f) = 0 := by linear_combination hZ
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hfpos.ne'
    · linarith
  have hfx : (f:ℤ) ∣ (x:ℤ) * e := ⟨1 - z, by linear_combination hxz⟩
  obtain ⟨ξ, hξ⟩ := hcopE.dvd_of_dvd_mul_right hfx
  -- x = f ξ, ξ e + z = 1
  have hξ' : ξ * e + z = 1 := by
    have : (f:ℤ) * (ξ * e + z - 1) = 0 := by
      have : (x:ℤ) * e = f * ξ * e := by rw [hξ]
      linear_combination hxz - this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hfpos.ne'
    · linarith
  have hξ0 : 0 ≤ ξ := by
    by_contra hneg
    have : ξ ≤ -1 := by omega
    nlinarith
  have hξz : ξ = 0 := by
    by_contra hne
    have : 1 ≤ ξ := by omega
    nlinarith
  subst hξz
  refine ⟨?_, ?_, ?_⟩
  · have : (x:ℤ) = 0 := by rw [hξ]; ring
    exact_mod_cast this
  · exact_mod_cast hy
  · have : (z:ℤ) = 1 := by linarith
    exact_mod_cast this

/-- Negative control for `D3`: for `e = 1` the length `c = f·a` is also a sum of `a`'s. -/
theorem D3_fails_e1 (f : ℕ) :
    f * ta 1 f + 0 * tb 1 f + 0 * tc 1 f = tc 1 f := by
  unfold ta tc; ring

/-- `D4`: `b − a` is not a sum of side lengths (`x a + y b + z c + a = b` is impossible). -/
theorem D4_b_sub_a (e f x y z : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f) :
    x * ta e f + y * tb e f + z * tc e f + ta e f ≠ tb e f := by
  intro h
  have hapos := a_pos e f he hef
  have hbpos := b_pos e f he hef
  have hbc := b_lt_c e f he hef
  have hy : y = 0 := by
    by_contra hy
    have : tb e f ≤ y * tb e f := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hz : z = 0 := by
    by_contra hz
    have : tc e f ≤ z * tc e f := Nat.le_mul_of_pos_left _ (by omega)
    omega
  subst hy; subst hz
  apply a_not_dvd_b e f he hef hcop
  exact ⟨x + 1, by nlinarith⟩

/-- **The relation lattice** (BR Lemma 28): the integer solutions of `p a + q b + r c = 0`. -/
theorem relation_lattice (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (p q r : ℤ) (h : p * (e * f) + q * ((f:ℤ)^2 - (e:ℤ)^2) + r * (f:ℤ)^2 = 0) :
    ∃ η ζ : ℤ, p = η * e - ζ * f ∧ q = η * f ∧ r = -η * f + ζ * e := by
  have hfpos : (0 : ℤ) < f := by exact_mod_cast (by omega : 0 < f)
  have hepos : (0 : ℤ) < e := by exact_mod_cast he
  have hcopZ : IsCoprime (f : ℤ) ((e : ℤ) ^ 2) := by
    have : Nat.Coprime f (e ^ 2) := Nat.Coprime.pow_right 2 hcop.symm
    simpa using Nat.isCoprime_iff_coprime.mpr this
  have hcopE : IsCoprime (e : ℤ) (f : ℤ) := by
    simpa using Nat.isCoprime_iff_coprime.mpr hcop
  have hdvd : (f : ℤ) ∣ (e : ℤ) ^ 2 * q := ⟨p * e + q * f + r * f, by linear_combination (-1 : ℤ) * h⟩
  obtain ⟨η, hη⟩ := hcopZ.dvd_of_dvd_mul_left hdvd
  -- p e + η (f² − e²) + r f = 0
  have h2 : p * e + η * ((f:ℤ)^2 - (e:ℤ)^2) + r * f = 0 := by
    have : (f:ℤ) * (p * e + η * ((f:ℤ)^2 - (e:ℤ)^2) + r * f) = 0 := by
      rw [hη] at h; linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hfpos.ne'
    · exact h'
  have hdvd2 : (e : ℤ) ∣ η * f + r := by
    have : (e:ℤ) ∣ (η * f + r) * f := ⟨η * e - p, by linear_combination h2⟩
    exact hcopE.dvd_of_dvd_mul_right this
  obtain ⟨ζ, hζ⟩ := hdvd2
  refine ⟨η, ζ, ?_, by rw [hη]; ring, ?_⟩
  · have : (e:ℤ) * (p - (η * e - ζ * f)) = 0 := by
      have hr : r = e * ζ - η * f := by linarith
      rw [hr] at h2; linear_combination h2
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hepos.ne'
    · linarith
  · linarith

#print axioms D2_two_b
#print axioms D3_c_unique
#print axioms D4_b_sub_a
#print axioms relation_lattice

end Erdos634.LaczJunction
