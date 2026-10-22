import Erdos634.Draft.LaczFormalW2Arith

/-!
# The Band Lemma (BL) and Proposition B1 arithmetic

Erdős #634, base-`β` band.  Credit: AI assistant (item 3, band program), Beeson–Roșu (Lemma 28: relation lattice,
Lemma 30(D): the case `M = 1`), Beeson, Laczkovich, Paliy.  Hand proof: (private working notes, not included)
§1 (brute-checked there for `f ≤ 40` and by lattice enumeration for `f ≤ 200`); here it is proved for all
`e, f, M`.  UNAUDITED.  Axiom-clean; no `sorry`.

`band_lemma`: let `1 ≤ e < f` coprime, `M ≥ 1`, `f ≤ 2Me < f + e`.  If `p·a + q·b + r·c = M e (3f² − e²)`
(`= Me(b + 2c)`, the base of `T_M(e,f)`) with `r ≥ f`, then `(p,q,r) = (0, Me, 2Me)`.
`band_lemma_thin`: if `2Me < f` there is no decomposition with `r ≥ f` (the Lean `cor:ebelow(b)` arithmetic).
-/

namespace Erdos634.LaczJunction

theorem band_lemma (e f M p q r : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (hM : 1 ≤ M) (hlo : f ≤ 2 * M * e) (hhi : 2 * M * e < f + e)
    (h : p * ta e f + q * tb e f + r * tc e f = M * e * (3 * f ^ 2 - e ^ 2)) (hr : f ≤ r) :
    p = 0 ∧ q = M * e ∧ r = 2 * M * e := by
  have hb := tb_cast e f hef
  have hf2 : e ^ 2 ≤ 3 * f ^ 2 := by nlinarith
  have hZ : (p : ℤ) * (e * f) + ((q : ℤ) - M * e) * ((f:ℤ)^2 - (e:ℤ)^2) +
      ((r : ℤ) - 2 * M * e) * (f:ℤ)^2 = 0 := by
    have := congrArg (fun n : ℕ => (n : ℤ)) h
    simp only [ta, tc] at this
    push_cast [Nat.cast_sub hf2] at this
    rw [hb] at this
    linarith
  obtain ⟨η, ζ, hp, hq, hr'⟩ := relation_lattice e f he hef hcop (p : ℤ) ((q : ℤ) - M * e)
    ((r : ℤ) - 2 * M * e) hZ
  have heZ : (1:ℤ) ≤ e := by exact_mod_cast he
  have hefZ : (e:ℤ) < f := by exact_mod_cast hef
  have hMZ : (1:ℤ) ≤ M := by exact_mod_cast hM
  have hloZ : (f:ℤ) ≤ 2 * M * e := by exact_mod_cast hlo
  have hhiZ : 2 * (M:ℤ) * e < f + e := by exact_mod_cast hhi
  have hrZ : (f:ℤ) ≤ r := by exact_mod_cast hr
  have hp0 : (0:ℤ) ≤ p := by positivity
  have hq0 : (0:ℤ) ≤ q := by positivity
  have hMe : (M:ℤ) * e < f := by nlinarith
  have hη : 0 ≤ η := by
    by_contra hneg
    have : η ≤ -1 := by omega
    nlinarith
  have hη0 : η = 0 := by
    by_contra hne
    have hη1 : 1 ≤ η := by omega
    have hζ : ζ ≤ η - 1 := by
      by_contra hz
      have h1 : η ≤ ζ := by omega
      have h2 : η * f ≤ ζ * f := mul_le_mul_of_nonneg_right h1 (by omega)
      have h3 : η * e < η * f := mul_lt_mul_of_pos_left hefZ (by omega)
      linarith
    have h1 : ζ * e ≤ (η - 1) * e := mul_le_mul_of_nonneg_right hζ (by omega)
    have h2 : (f - e) ≤ η * (f - e) := by nlinarith
    linarith
  subst hη0
  have hξ : ζ = 0 := by
    have hζ0 : ζ ≤ 0 := by
      by_contra hz
      have : 1 ≤ ζ := by omega
      have h2 : f ≤ ζ * f := by nlinarith
      linarith
    by_contra hne
    have h1 : ζ ≤ -1 := by omega
    have h2 : ζ * e ≤ -1 * e := mul_le_mul_of_nonneg_right h1 (by omega)
    linarith
  subst hξ
  refine ⟨?_, ?_, ?_⟩
  · have : (p:ℤ) = 0 := by rw [hp]; ring
    exact_mod_cast this
  · have : (q:ℤ) = M * e := by rw [show (q:ℤ) = ((q:ℤ) - M * e) + M * e by ring, hq]; ring
    exact_mod_cast this
  · have : (r:ℤ) = 2 * M * e := by rw [show (r:ℤ) = ((r:ℤ) - 2 * M * e) + 2 * M * e by ring, hr']; ring
    exact_mod_cast this

/-- Thin range: no decomposition of the base with `r ≥ f` when `2Me < f`. -/
theorem band_lemma_thin (e f M p q r : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (hM : 1 ≤ M) (hlt : 2 * M * e < f)
    (h : p * ta e f + q * tb e f + r * tc e f = M * e * (3 * f ^ 2 - e ^ 2)) (hr : f ≤ r) :
    False := by
  have hb := tb_cast e f hef
  have hf2 : e ^ 2 ≤ 3 * f ^ 2 := by nlinarith
  have hZ : (p : ℤ) * (e * f) + ((q : ℤ) - M * e) * ((f:ℤ)^2 - (e:ℤ)^2) +
      ((r : ℤ) - 2 * M * e) * (f:ℤ)^2 = 0 := by
    have := congrArg (fun n : ℕ => (n : ℤ)) h
    simp only [ta, tc] at this
    push_cast [Nat.cast_sub hf2] at this
    rw [hb] at this
    linarith
  obtain ⟨η, ζ, hp, hq, hr'⟩ := relation_lattice e f he hef hcop (p : ℤ) ((q : ℤ) - M * e)
    ((r : ℤ) - 2 * M * e) hZ
  have heZ : (1:ℤ) ≤ e := by exact_mod_cast he
  have hefZ : (e:ℤ) < f := by exact_mod_cast hef
  have hMZ : (1:ℤ) ≤ M := by exact_mod_cast hM
  have hltZ : 2 * (M:ℤ) * e < f := by exact_mod_cast hlt
  have hrZ : (f:ℤ) ≤ r := by exact_mod_cast hr
  have hp0 : (0:ℤ) ≤ p := by positivity
  have hq0 : (0:ℤ) ≤ q := by positivity
  have hη : 0 ≤ η := by
    by_contra hneg
    have : η ≤ -1 := by omega
    nlinarith
  by_cases hη0 : η = 0
  · subst hη0
    have hζ0 : ζ ≤ 0 := by nlinarith
    nlinarith
  · have hη1 : 1 ≤ η := by omega
    have hζ : ζ ≤ η - 1 := by
      by_contra hz
      have : η ≤ ζ := by omega
      nlinarith
    nlinarith

#print axioms band_lemma
#print axioms band_lemma_thin

end Erdos634.LaczJunction
