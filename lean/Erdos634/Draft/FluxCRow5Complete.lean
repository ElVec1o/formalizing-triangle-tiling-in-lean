-- Draft/FluxCRow5Complete.lean — closes E7b, E8 and the two irrationality closings of Theorem E
-- ((private working notes, not included) §4, "E7b" / "E8" / "2π/3 conclusion" / "π/3 conclusion"),
-- composing with the EXISTING `Row5.theoremE_twoPiThree` / `Row5.theoremE_sixty`
-- (`Draft/FluxCRow5.lean`, NOT edited here).  NOT imported into `All.lean`.
--
-- HONEST SCOPE.
-- * The two irrationality closings (`(N+1)(N+9)` never a square for `N ≥ 1`; `(N-1)(N-9)` a square
--   only at `N ∈ {1,9,10}`) are proved IN FULL, unconditionally, over `ℤ`.  Grep of the corpus found
--   no existing Lean copy; `EquilateralConic.lean`'s `conic_pi3` is the DIFFERENT quantity
--   `(9N−M²)(N−M²)`, used BEFORE the prime pinning `M ∈ {3,N}`, not this one. Not a rediscovery.
-- * E7b (the "uniform-sign trick" of AUDIT.md P6) is proved IN FULL as an abstract combinatorial
--   fact: a `±1`-valued sum over `N` terms equal to `N` (resp. `−N`) forces every term `+1`
--   (resp. `−1`).  This is the general tool; AUDIT.md P6 records it as "Range: CONJECTURE (one use)"
--   because the EDGE-LEVEL bridge — "this Σε is literally the sum of the model's `w₁`-signs over the
--   tile boundary, and an edge with the wrong sign cannot lie on ∂ABC" — needs the flux functional
--   promoted to a real oriented placement (AUDIT.md §7 (L1); PAPER_MAP's `lem:value` blocker, still
--   open; not attempted here, per the F-4 lesson in (private working notes, not included) against promising one build unlocks a
--   consumer).  So the final `sixty_forces_le_three` theorem below takes "no `c`-edge on `∂ABC`"
--   (formalized as `r = 0` in the side decomposition) as an EXPLICIT hypothesis `hr0`, named plainly
--   as not derived from a real dissection here.
-- * E8's ALGEBRA (closed forms for `c`, `a+b`, `a−b`, and the final "matching irrational parts ⇒
--   `N ≤ 3`" step) is proved IN FULL, composing with `Row5.theoremE_twoPiThree` / `Row5.theoremE_sixty`
--   for the coefficients, GIVEN the side decomposition `S = p•a + q•b + r•c` (`p q r : ℤ`, `0 ≤ p,q,r`)
--   as an explicit hypothesis.  That hypothesis is AUDIT.md's own E8 (paper `eq:area`,
--   `WallEndpoints.chain_endpoints`); AUDIT.md §7/§9 names its promotion to a SPECIFIC real
--   dissection as the unbuilt geometric layer (L1)-(L4).  Not attempted here.
-- * NON-VACUITY.  `Row5.theoremE_twoPiThree`/`_sixty`'s own hypotheses (a `CongruentDissection` of an
--   equilateral target by an irrational `2π/3`/`π/3` tile) have NO real witness in the corpus
--   (`Draft/FluxCRow5Witness.lean`'s header: "no Lean dissection of an equilateral target... exists";
--   the smallest known real ones have 1215/1440 tiles, held only as numbers, not coordinates).  So
--   every theorem below that is stated in terms of a `CongruentDissection` inherits that same
--   conditionality — a PAPER-LEVEL fact, not a Lean gap, stated again so it is not silently dropped.
--   The two irrationality closings and the abstract E7b tool are UNCONDITIONAL and need no witness;
--   the closed-form and final theorems are algebra composed over abstract `a b c S : ℝ` with the
--   hypotheses `Row5.theoremE_*` would supply — they are exercised on concrete numeric instances
--   below (`example`s) as a witness that the HYPOTHESES of the pure-algebra lemmas are jointly
--   satisfiable (even though no matching real tiling is known).
--
-- Reuse (cited): `Row5.theoremE_twoPiThree`, `Row5.theoremE_sixty` (`Draft/FluxCRow5.lean`, not
-- edited); Mathlib's `irrational_sqrt_natCast_iff`, `Real.sqrt_sq_eq_abs`.
import Erdos634.Draft.FluxCRow5

open scoped Classical
open Finset

namespace Erdos634.Geometry

/-! ## The two irrationality closings (AUDIT.md §4 E8, "2π/3 conclusion" step 2 / "π/3 conclusion"
step 3). Both reduce to the same shifted-square fact. -/

/-- **The shifted-square lemma.**  If `x² − 16 = k²` then `x ∈ {5, 4, −4, −5}`. -/
theorem sq16_cases (x k : ℤ) (h : x ^ 2 - 16 = k ^ 2) :
    x = 5 ∨ x = 4 ∨ x = -4 ∨ x = -5 := by
  have hfact : (x - k) * (x + k) = 16 := by linear_combination h
  have hu : (x - k) ∣ (16 : ℤ) := ⟨x + k, hfact.symm⟩
  have hub : x - k ≤ 16 := Int.le_of_dvd (by norm_num) hu
  have hlb : -16 ≤ x - k := by
    have h2 : -(x - k) ≤ 16 := Int.le_of_dvd (by norm_num) (neg_dvd.mpr hu)
    linarith
  set d := x - k with hd
  interval_cases d <;> omega

/-- **E8, `2π/3` irrationality closing.**  `(N+1)(N+9)` is never a perfect square for `N ≥ 1`. -/
theorem not_sq_Np1Np9 (N : ℤ) (hN : 1 ≤ N) (k : ℤ) : (N + 1) * (N + 9) ≠ k ^ 2 := by
  intro hk
  have heq : (N + 5) ^ 2 - 16 = k ^ 2 := by
    have e : (N + 5) ^ 2 - 16 = (N + 1) * (N + 9) := by ring
    rw [e, hk]
  rcases sq16_cases (N + 5) k heq with h1 | h2 | h3 | h4 <;> omega

/-- **E8, `π/3` irrationality closing.**  `(N−1)(N−9)` is a perfect square, for `N ≥ 1`, only at
`N ∈ {1, 9, 10}` (AUDIT.md §4, "π/3 conclusion" step 3). -/
theorem sq_Nm1Nm9_cases (N : ℤ) (hN : 1 ≤ N) (k : ℤ) (h : (N - 1) * (N - 9) = k ^ 2) :
    N = 1 ∨ N = 9 ∨ N = 10 := by
  have heq : (N - 5) ^ 2 - 16 = k ^ 2 := by
    have e : (N - 5) ^ 2 - 16 = (N - 1) * (N - 9) := by ring
    rw [e, h]
  rcases sq16_cases (N - 5) k heq with h1 | h2 | h3 | h4 <;> omega

/-- **`ℕ` form of the `2π/3` closing**, matching Mathlib's `irrational_sqrt_natCast_iff`.  (`N ≥ 1`
is needed: `N = 0` gives `1·9 = 9 = 3²`, a square.) -/
theorem not_isSquare_nat_Np1Np9 (N : ℕ) (hN : 1 ≤ N) : ¬ IsSquare ((N + 1) * (N + 9)) := by
  rintro ⟨k, hk⟩
  have hZ : ((N : ℤ) + 1) * ((N : ℤ) + 9) = (k : ℤ) ^ 2 := by
    have hk' : ((N + 1) * (N + 9) : ℤ) = (k : ℤ) * (k : ℤ) := by exact_mod_cast hk
    rw [hk']; ring
  exact not_sq_Np1Np9 (N : ℤ) (by exact_mod_cast hN) (k : ℤ) hZ

/-- Sanity instance: `(11+1)(11+9) = 240` is not a perfect square (`15² = 225 < 240 < 256 = 16²`). -/
example : ¬ IsSquare ((11 + 1) * (11 + 9)) := not_isSquare_nat_Np1Np9 11 (by norm_num)

/-- Sanity instance for the `π/3` closing: `N = 11` gives `(10)(2) = 20`, not a square, and
`N = 9` (excluded by primality elsewhere) is exactly a listed exceptional value. -/
example : (9:ℤ) = 1 ∨ (9:ℤ) = 9 ∨ (9:ℤ) = 10 :=
  sq_Nm1Nm9_cases 9 (by norm_num) 0 (by norm_num)

/-! ## E7b: the uniform-sign trick (AUDIT.md P6, "the new step"). Abstract tool, no edge-level
geometry — see the file header for what remains to reach the edge-level statement. -/

/-- **Uniform sign.**  If `ε : Fin N → ℤ` takes only values `±1` and `Σ ε i = N`, every value is
`+1`. -/
theorem uniform_sign_pos {N : ℕ} (ε : Fin N → ℤ) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hsum : ∑ i, ε i = (N : ℤ)) : ∀ i, ε i = 1 := by
  intro i0
  by_contra hcon
  have hi0' : ε i0 = -1 := (hε i0).resolve_left hcon
  have hle : ∀ i ∈ (univ : Finset (Fin N)), ε i ≤ (1 : ℤ) :=
    fun i _ => (hε i).elim le_of_eq (fun h => by omega)
  have hlt : ∑ i, ε i < ∑ _i : Fin N, (1 : ℤ) :=
    Finset.sum_lt_sum hle ⟨i0, mem_univ _, by omega⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    at hlt
  omega

/-- **Uniform sign, negative case.** -/
theorem uniform_sign_neg {N : ℕ} (ε : Fin N → ℤ) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hsum : ∑ i, ε i = -(N : ℤ)) : ∀ i, ε i = -1 := by
  intro i0
  by_contra hcon
  have hi0' : ε i0 = 1 := (hε i0).resolve_right hcon
  have hle : ∀ i ∈ (univ : Finset (Fin N)), (-1 : ℤ) ≤ ε i :=
    fun i _ => (hε i).elim (fun h => by omega) ge_of_eq
  have hlt : ∑ _i : Fin N, (-1 : ℤ) < ∑ i, ε i :=
    Finset.sum_lt_sum hle ⟨i0, mem_univ _, by omega⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    neg_mul] at hlt
  omega

/-- Sanity instance: `N = 3`, `ε = (1,1,1)`, sum `= 3`, forces every term `1`. -/
example : ∀ i : Fin 3, (fun _ => (1:ℤ)) i = 1 :=
  uniform_sign_pos (N := 3) (fun _ => 1) (fun _ => Or.inl rfl) (by decide)

/-! ## E8: closed forms, composing with the existing `Row5.theoremE_*`. -/

section ClosedForms

variable {N : ℕ}

/-- **E8, `2π/3` closed forms.**  Composing `Row5.theoremE_twoPiThree`: at a prime `N`, the target
side `S`, the tile's `c` and `a-b` and `a+b` satisfy `2Nc = S(N+3)`, `2N(a-b) = ±S(N-3)`, and
`4N²(a+b)² = S²(N+1)(N+9)` (AUDIT.md §4, "2π/3 conclusion" step 1). -/
theorem Row5.twoPiThree_closedForms (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoPiThreeData α a b c)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) (hNp : N.Prime) :
    2 * (N : ℝ) * c = D.target.oppLen 0 * ((N : ℝ) + 3) ∧
      (2 * (N : ℝ) * (a - b) = D.target.oppLen 0 * ((N : ℝ) - 3)
        ∨ 2 * (N : ℝ) * (a - b) = D.target.oppLen 0 * (3 - (N : ℝ))) ∧
      4 * (N : ℝ) ^ 2 * (a + b) ^ 2
        = D.target.oppLen 0 ^ 2 * ((N : ℝ) + 1) * ((N : ℝ) + 9) := by
  obtain ⟨s, t, -, -, hs1, hsN, ht1, htN, hSeq1, hSeq2, harea, hst, hpin⟩ :=
    Row5.theoremE_twoPiThree D hα h hP
  set S := D.target.oppLen 0
  rcases hpin hNp with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · subst hs; subst ht
    have eq1 : c + a - b = S := by
      have h := hSeq1; push_cast at h; linarith
    have eq2 : (N : ℝ) * (c + b - a) = 3 * S := by exact_mod_cast hSeq2
    have hc2 : 2 * (N : ℝ) * c = S * ((N : ℝ) + 3) := by linear_combination (N : ℝ) * eq1 + eq2
    have hD : 2 * (N : ℝ) * (a - b) = S * ((N : ℝ) - 3) := by linear_combination (N : ℝ) * eq1 - eq2
    have hD2 : 4 * (N : ℝ) ^ 2 * (a - b) ^ 2 = S ^ 2 * ((N : ℝ) - 3) ^ 2 := by
      rw [show (4 * (N : ℝ) ^ 2 * (a - b) ^ 2) = (2 * (N : ℝ) * (a - b)) ^ 2 by ring,
        show S ^ 2 * ((N : ℝ) - 3) ^ 2 = (S * ((N : ℝ) - 3)) ^ 2 by ring, hD]
    exact ⟨hc2, Or.inl hD, by linear_combination hD2 - 16 * (N : ℝ) * harea⟩
  · subst hs; subst ht
    have eq1 : (N : ℝ) * (c + a - b) = 3 * S := by exact_mod_cast hSeq1
    have eq2 : c + b - a = S := by
      have h := hSeq2; push_cast at h; linarith
    have hc2 : 2 * (N : ℝ) * c = S * ((N : ℝ) + 3) := by linear_combination eq1 + (N : ℝ) * eq2
    have hD : 2 * (N : ℝ) * (a - b) = S * (3 - (N : ℝ)) := by linear_combination eq1 - (N : ℝ) * eq2
    have hD2 : 4 * (N : ℝ) ^ 2 * (a - b) ^ 2 = S ^ 2 * ((N : ℝ) - 3) ^ 2 := by
      rw [show (4 * (N : ℝ) ^ 2 * (a - b) ^ 2) = (2 * (N : ℝ) * (a - b)) ^ 2 by ring,
        show S ^ 2 * ((N : ℝ) - 3) ^ 2 = (S * (3 - (N : ℝ))) ^ 2 by ring, hD]
    exact ⟨hc2, Or.inr hD, by linear_combination hD2 - 16 * (N : ℝ) * harea⟩

/-- **E8, `π/3` closed forms.**  Composing `Row5.theoremE_sixty`: at a prime `N > 3`, `2N(a+b) =
S(N+3)`, `2Nc = S(N−3)`, and `4N²(a−b)² = S²(N−1)(N−9)` (AUDIT.md §4, "π/3 conclusion" step 1). -/
theorem Row5.sixty_closedForms (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.SixtyData α a b c)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) (hNp : N.Prime) (hN3 : 3 < N) :
    2 * (N : ℝ) * (a + b) = D.target.oppLen 0 * ((N : ℝ) + 3) ∧
      2 * (N : ℝ) * c = D.target.oppLen 0 * ((N : ℝ) - 3) ∧
      4 * (N : ℝ) ^ 2 * (a - b) ^ 2
        = D.target.oppLen 0 ^ 2 * ((N : ℝ) - 1) * ((N : ℝ) - 9) := by
  obtain ⟨m₁, m₂, -, -, hm1, hm1N, hm2, hm2N, hSeq1, hSeq2, harea, hprod, hlt, hpin⟩ :=
    Row5.theoremE_sixty D hα h hP
  set S := D.target.oppLen 0
  obtain ⟨ha, hb⟩ := hpin hNp hN3
  subst ha; subst hb
  have eq1 : (N : ℝ) * (a + b - c) = 3 * S := by exact_mod_cast hSeq1
  have eq2 : a + b + c = S := by
    have h := hSeq2; push_cast at h; linarith
  have hc2 : 2 * (N : ℝ) * c = S * ((N : ℝ) - 3) := by linear_combination (N : ℝ) * eq2 - eq1
  have hab2 : 2 * (N : ℝ) * (a + b) = S * ((N : ℝ) + 3) := by
    linear_combination 2 * (N : ℝ) * eq2 - hc2
  have hab_sq : 4 * (N : ℝ) ^ 2 * (a + b) ^ 2 = S ^ 2 * ((N : ℝ) + 3) ^ 2 := by
    rw [show (4 * (N : ℝ) ^ 2 * (a + b) ^ 2) = (2 * (N : ℝ) * (a + b)) ^ 2 by ring,
      show S ^ 2 * ((N : ℝ) + 3) ^ 2 = (S * ((N : ℝ) + 3)) ^ 2 by ring, hab2]
  exact ⟨hab2, hc2, by linear_combination hab_sq + 16 * (N : ℝ) * harea⟩

end ClosedForms

/-! ## E8: the side decomposition forces `N ≤ 3` / a contradiction.

The side decomposition `S = p•a + q•b + r•c` (AUDIT.md's E8, paper `eq:area`) is taken as an
explicit hypothesis: its promotion from a real `CongruentDissection` is the unbuilt geometric layer
named in the file header and in AUDIT.md §7 (L1)-(L4), not attempted here.  For the `π/3` branch,
`r = 0` (E7b's geometric conclusion "no c-edge on ∂ABC") is likewise an explicit hypothesis. -/

/-- **`2π/3` conclusion (AUDIT.md §4, steps 2–4).**  Given the closed forms and a side decomposition
`S = p•a + q•b + r•c` with `p, q, r ≥ 0` integers, `N ≤ 3`.  E7b is not needed on this branch:
irrationality of `(a+b)/S` alone forces `p = q = 0`. -/
theorem Row5.twoPiThree_forces_le_three {N : ℕ} {a b c S : ℝ} (hNp : N.Prime)
    (hc2 : 2 * (N : ℝ) * c = S * ((N : ℝ) + 3))
    (hD : 2 * (N : ℝ) * (a - b) = S * ((N : ℝ) - 3)
      ∨ 2 * (N : ℝ) * (a - b) = S * (3 - (N : ℝ)))
    (hab2 : 4 * (N : ℝ) ^ 2 * (a + b) ^ 2 = S ^ 2 * ((N : ℝ) + 1) * ((N : ℝ) + 9))
    (hS0 : 0 < S) (haPos : 0 < a) (hbPos : 0 < b) (p q r : ℤ)
    (hp0 : 0 ≤ p) (hq0 : 0 ≤ q) (hside : S = p * a + q * b + r * c) : N ≤ 3 := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNp.pos
  have hSne : S ≠ 0 := ne_of_gt hS0
  -- irrationality of `X / S`, `X := 2N(a+b)`
  have hxirr : Irrational (2 * (N : ℝ) * (a + b) / S) := by
    have hnotsq : ¬ IsSquare ((N + 1) * (N + 9)) := not_isSquare_nat_Np1Np9 N hNp.pos
    have hirr0 : Irrational (Real.sqrt (((N + 1) * (N + 9) : ℕ) : ℝ)) :=
      irrational_sqrt_natCast_iff.mpr hnotsq
    have hxsq : (2 * (N : ℝ) * (a + b) / S) ^ 2 = (((N + 1) * (N + 9) : ℕ) : ℝ) := by
      rw [div_pow, div_eq_iff (pow_ne_zero 2 hSne)]
      push_cast
      linear_combination hab2
    have hxnn : 0 ≤ 2 * (N : ℝ) * (a + b) / S := by positivity
    have hxeq : 2 * (N : ℝ) * (a + b) / S = Real.sqrt (((N + 1) * (N + 9) : ℕ) : ℝ) := by
      rw [← Real.sqrt_sq hxnn, hxsq]
    rwa [hxeq]
  -- Both signs of `hD` give `(p+q)•X = S•M` for an integer `M` (case 2 is case 1 with `p,q`
  -- swapped); either way this forces `p + q = 0`, hence (with `p, q ≥ 0`) `p = q = 0`.
  have hpq0 : p + q = 0 := by
    rcases hD with hD | hD
    · set M : ℤ := 4 * (N : ℤ) - (p - q) * ((N : ℤ) - 3) - 2 * r * ((N : ℤ) + 3) with hMdef
      have heqM : ((p : ℝ) + q) * (2 * (N : ℝ) * (a + b)) = S * (M : ℝ) := by
        have hMcast : (M : ℝ) = 4 * (N : ℝ) - ((p : ℝ) - q) * ((N : ℝ) - 3)
            - 2 * (r : ℝ) * ((N : ℝ) + 3) := by rw [hMdef]; push_cast; ring
        rw [hMcast]
        linear_combination (-4 * (N : ℝ)) * hside - ((p : ℝ) - q) * hD - 2 * (r : ℝ) * hc2
      by_contra hne
      have hnz : ((p : ℝ) + q) ≠ 0 := by exact_mod_cast hne
      apply hxirr
      refine ⟨(M : ℚ) / ((p : ℚ) + q), ?_⟩
      push_cast
      rw [div_eq_div_iff hnz hSne]
      linear_combination -heqM
    · set M : ℤ := 4 * (N : ℤ) - (q - p) * ((N : ℤ) - 3) - 2 * r * ((N : ℤ) + 3) with hMdef
      have heqM : ((p : ℝ) + q) * (2 * (N : ℝ) * (a + b)) = S * (M : ℝ) := by
        have hMcast : (M : ℝ) = 4 * (N : ℝ) - ((q : ℝ) - p) * ((N : ℝ) - 3)
            - 2 * (r : ℝ) * ((N : ℝ) + 3) := by rw [hMdef]; push_cast; ring
        rw [hMcast]
        linear_combination (-4 * (N : ℝ)) * hside + ((q : ℝ) - p) * hD - 2 * (r : ℝ) * hc2
      by_contra hne
      have hnz : ((p : ℝ) + q) ≠ 0 := by exact_mod_cast hne
      apply hxirr
      refine ⟨(M : ℚ) / ((p : ℚ) + q), ?_⟩
      push_cast
      rw [div_eq_div_iff hnz hSne]
      linear_combination -heqM
  have hp0' : p = 0 := by omega
  have hq0' : q = 0 := by omega
  subst hp0'; subst hq0'
  have hrS : S = r * c := by rw [hside]; push_cast; ring
  have hr0 : r ≠ 0 := by
    rintro h0; rw [h0] at hrS; simp at hrS; linarith
  have hcne : c ≠ 0 := by rintro h0; rw [h0, mul_zero] at hrS; exact hSne hrS
  -- substitute `S = r•c` into `hc2` and cancel `c` to get `2N = r(N+3)`.
  have hc2' : 2 * (N : ℝ) * c = ((r : ℝ) * c) * ((N : ℝ) + 3) := by rw [hrS] at hc2; exact hc2
  have hc2'' : (2 * (N : ℝ)) * c = ((r : ℝ) * ((N : ℝ) + 3)) * c := by linear_combination hc2'
  have hrform : 2 * (N : ℝ) = (r : ℝ) * ((N : ℝ) + 3) := mul_right_cancel₀ hcne hc2''
  have hrZ : 2 * (N : ℤ) = r * ((N : ℤ) + 3) := by exact_mod_cast hrform
  have hdvd : ((N : ℤ) + 3) ∣ 6 := ⟨2 - r, by linear_combination -hrZ⟩
  have hle : (N : ℤ) + 3 ≤ 6 := Int.le_of_dvd (by norm_num) hdvd
  omega

/-- **`π/3` conclusion (AUDIT.md §4, steps 2–4).**  Given the closed forms, `E7b`'s conclusion
`r = 0` (hypothesis `hr0`, see file header), and a side decomposition, `3 < N` is impossible. -/
theorem Row5.sixty_forces_not_gt_three {N : ℕ} {a b c S : ℝ} (hNp : N.Prime) (hN3 : 3 < N)
    (hab2 : 2 * (N : ℝ) * (a + b) = S * ((N : ℝ) + 3))
    (hfin2 : 4 * (N : ℝ) ^ 2 * (a - b) ^ 2 = S ^ 2 * ((N : ℝ) - 1) * ((N : ℝ) - 9))
    (hS0 : 0 < S) (p q r : ℤ) (hp0 : 0 ≤ p) (hq0 : 0 ≤ q)
    (hside : S = p * a + q * b + r * c) (hr0 : r = 0) : False := by
  subst hr0
  have hside2 : S = p * a + q * b := by rw [hside]; push_cast; ring
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNp.pos
  have hSne : S ≠ 0 := ne_of_gt hS0
  -- `(N-1)(N-9) ≥ 0` forces `N ∉ {5,7}`; with primality this forces `N ≥ 11`.
  have hnn : (0 : ℝ) ≤ ((N : ℝ) - 1) * ((N : ℝ) - 9) := by
    have h1 : (0 : ℝ) ≤ 4 * (N : ℝ) ^ 2 * (a - b) ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ S ^ 2 * (((N : ℝ) - 1) * ((N : ℝ) - 9)) := by
      have := hfin2; nlinarith [h1]
    have hS2 : 0 < S ^ 2 := by positivity
    by_contra hcon
    push_neg at hcon
    have : S ^ 2 * (((N : ℝ) - 1) * ((N : ℝ) - 9)) < 0 := mul_neg_of_pos_of_neg hS2 hcon
    linarith
  have hnnZ : (0 : ℤ) ≤ ((N : ℤ) - 1) * ((N : ℤ) - 9) := by exact_mod_cast hnn
  have hN9 : N ≠ 9 := by rintro rfl; exact absurd hNp (by decide)
  have hN10 : N ≠ 10 := by rintro rfl; exact absurd hNp (by decide)
  have hN11 : 11 ≤ N := by
    by_contra hcon
    push_neg at hcon
    have hle10 : (N : ℤ) ≤ 10 := by exact_mod_cast Nat.lt_succ_iff.mp hcon
    have hNge : 3 < (N : ℤ) := by exact_mod_cast hN3
    interval_cases N <;> omega
  have h1N : (1 : ℕ) ≤ N := by omega
  have h9N : (9 : ℕ) ≤ N := by omega
  -- irrationality of `X' / S`, `X' := 2N(a-b)`
  have hxirr : Irrational (2 * (N : ℝ) * (a - b) / S) := by
    have hcases : ¬ ((N : ℤ) = 1 ∨ (N : ℤ) = 9 ∨ (N : ℤ) = 10) := by omega
    have hnotsq : ¬ IsSquare ((N - 1) * (N - 9)) := by
      rintro ⟨k, hk⟩
      have hZ : ((N : ℤ) - 1) * ((N : ℤ) - 9) = (k : ℤ) ^ 2 := by
        have hk' : (((N - 1) * (N - 9) : ℕ) : ℤ) = (k : ℤ) * (k : ℤ) := by exact_mod_cast hk
        have hNsub : (((N - 1) * (N - 9) : ℕ) : ℤ) = ((N : ℤ) - 1) * ((N : ℤ) - 9) := by
          rw [Nat.cast_mul, Nat.cast_sub h1N, Nat.cast_sub h9N]; push_cast; ring
        rw [← hNsub, hk']; ring
      exact hcases (sq_Nm1Nm9_cases (N : ℤ) (by omega) (k : ℤ) hZ)
    have hirr0 : Irrational (Real.sqrt (((N - 1) * (N - 9) : ℕ) : ℝ)) :=
      irrational_sqrt_natCast_iff.mpr hnotsq
    have hcast : (((N - 1) * (N - 9) : ℕ) : ℝ) = ((N : ℝ) - 1) * ((N : ℝ) - 9) := by
      rw [Nat.cast_mul, Nat.cast_sub h1N, Nat.cast_sub h9N]; push_cast; ring
    have hxsq : (2 * (N : ℝ) * (a - b) / S) ^ 2 = (((N - 1) * (N - 9) : ℕ) : ℝ) := by
      rw [div_pow, div_eq_iff (pow_ne_zero 2 hSne), hcast]
      linear_combination hfin2
    have hxabs : |2 * (N : ℝ) * (a - b) / S| = Real.sqrt (((N - 1) * (N - 9) : ℕ) : ℝ) := by
      rw [← Real.sqrt_sq_eq_abs, hxsq]
    have hxabsirr : Irrational |2 * (N : ℝ) * (a - b) / S| := hxabs ▸ hirr0
    rcases abs_choice (2 * (N : ℝ) * (a - b) / S) with heq | heq
    · rwa [heq] at hxabsirr
    · rw [heq] at hxabsirr
      have hneg := hxabsirr.neg
      simpa using hneg
  -- `(p−q)•X' = S•(4N − (p+q)(N+3))`, so `p = q`.
  set M' : ℤ := 4 * (N : ℤ) - (p + q) * ((N : ℤ) + 3) with hMdef
  have heqM : ((p : ℝ) - q) * (2 * (N : ℝ) * (a - b)) = S * (M' : ℝ) := by
    have hMcast : (M' : ℝ) = 4 * (N : ℝ) - ((p : ℝ) + q) * ((N : ℝ) + 3) := by
      rw [hMdef]; push_cast; ring
    rw [hMcast]
    linear_combination (-4 * (N : ℝ)) * hside2 - ((p : ℝ) + q) * hab2
  have hpq0 : p = q := by
    by_contra hne
    have hnz : ((p : ℝ) - q) ≠ 0 := by
      intro h0
      apply hne
      have hpq : (p : ℝ) = q := by linarith
      exact_mod_cast hpq
    apply hxirr
    refine ⟨(M' : ℚ) / ((p : ℚ) - q), ?_⟩
    push_cast
    rw [div_eq_div_iff hnz hSne]
    linear_combination -heqM
  subst hpq0
  have hM'0 : M' = 0 := by
    have hz : ((p : ℝ) - p) * (2 * (N : ℝ) * (a - b)) = 0 := by ring
    rw [hz] at heqM
    rcases mul_eq_zero.mp heqM.symm with h | h
    · exact absurd h hSne
    · exact_mod_cast h
  have hpN3 : p * ((N : ℤ) + 3) = 2 * (N : ℤ) := by
    have hm : 4 * (N : ℤ) - (p + p) * ((N : ℤ) + 3) = 0 := hMdef ▸ hM'0
    linarith
  have hdvd : ((N : ℤ) + 3) ∣ 6 := ⟨2 - p, by linear_combination hpN3⟩
  have hle : (N : ℤ) + 3 ≤ 6 := Int.le_of_dvd (by norm_num) hdvd
  have hN3le : (N : ℤ) ≤ 3 := by omega
  have hNge : 3 < (N : ℤ) := by exact_mod_cast hN3
  omega


end Erdos634.Geometry

#print axioms Erdos634.Geometry.sq16_cases
#print axioms Erdos634.Geometry.not_sq_Np1Np9
#print axioms Erdos634.Geometry.sq_Nm1Nm9_cases
#print axioms Erdos634.Geometry.not_isSquare_nat_Np1Np9
#print axioms Erdos634.Geometry.uniform_sign_pos
#print axioms Erdos634.Geometry.uniform_sign_neg
#print axioms Erdos634.Geometry.Row5.twoPiThree_closedForms
#print axioms Erdos634.Geometry.Row5.sixty_closedForms
#print axioms Erdos634.Geometry.Row5.twoPiThree_forces_le_three
#print axioms Erdos634.Geometry.Row5.sixty_forces_not_gt_three
