-- Draft/FluxGRow3.lean — row 3 of the AUDIT_ROWS scope (right-angled tile, α ∉ ℚπ), Gaussian grid.
-- Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).  Source: (private working notes, not included) ("row3" below).
--
-- Formalization debt on an already paper-level-PROVED result (row3 PROOF.md P7: Lemma A,
-- Proposition RP, Corollary all PROVED, Rule 0, two independent hostile reviews HOLD). This file is
-- NOT progress on the three /goal outcomes.
--
-- NAMING: "G" for "Gaussian" (the ℤ[i]-valued grid weight of row3 Steps 2–7), matching the corpus's
-- FluxC/FluxD/FluxE prefixes for other rows' grids.
--
-- SCOPE (read in full before trusting any claim below): this file does **not** build Lemma A,
-- Proposition RP, or the Corollary. It builds exactly two of the six items row3 PROOF.md §6/P9
-- lists as missing:
--   (2) grid uniqueness for Zα + Z(π/2), given α ∉ ℚπ (row3 PROOF.md Step 2);
--   (5, the "2-adic step" half only) the pure ℤ[i]-arithmetic endgame of Proposition RP Step 7:
--       λ² + sλ + t = 0 with s, t ∈ ℤ[i] (here: s = a+bi, t = c+di, a b c d : ℤ) and (N:ℝ) = 2λ²
--       (λ = AB/c of row3 Prop RP Step 1) together force `Even N`.
-- Both are proved unconditionally (no `sorry`), each with a concrete non-vacuous witness.
--
-- NOT built here, stated plainly (row3 PROOF.md §6 items 1, 3, 4, and the rest of item 5):
--   (1) the actual Gaussian/order-4 weight f_X : Dir → ℂ on a real `CongruentDissection` (the paper's
--       f_X(θ) = [k(θ)=X]·i^{j(θ)}) and its instantiation into `Dissection.flux_cancel`
--       (`FluxCancel.lean`, already VERIFIED for a fully general odd `f : Dir → E`, `E` any
--       `ℝ`-module — reused, not rebuilt; row3's own remark that this is "the real blocker" is
--       stale: the *generic* flux/cancellation machinery is not the gap, the *specific Gaussian
--       weight* f_X is, and it is not constructed here);
--   (3) the corner fact for a right tile at ABC's vertices and Lemma A's case split (the analogue
--       of `TileAt.congruentDissection_base_corner_counts` for base-β, not attempted for row3);
--   (4) the similarity of ABM to T and the area identity N = 2λ² (Prop RP Step 1);
--   (5, the rest) the Laurent-polynomial cancellation c(1−e^{iα}z⁻¹)(P(z)−e^{−iα}zQ(z)) = ... down to
--       (★): P(z) − uzQ(z) = −λ(z−u) (Prop RP Steps 4–6). This is genuinely new work (no
--       `LaurentPolynomial` use exists anywhere in `Erdos634`, confirmed by row3 PROOF.md P9); it was
--       not attempted in this pass.
--
-- So: Lemma A, Proposition RP and the Corollary all remain OPEN in Lean after this file. What is
-- closed is the two arithmetic/algebraic sub-lemmas above, each independently useful to whatever
-- later attempts Prop RP's Steps 2 and 7.
--
-- Rediscovery check (Rule 0.5): grepped `lean/Erdos634` for `Zsqrtd`, `GaussianInt`,
-- `LaurentPolynomial`, `grid_unique`, and "Gaussian" — no hits outside this file. `GridChar` exists
-- (`FluxWeight.lean`, order-2 characters, reused elsewhere per EVIDENCE P45/P46/A25) but is not
-- reused here: `GridChar.ψ` is valued in a `CommRing R` and *could* carry an order-4 character, but
-- `GridChar` bundles a single scalar `chi : Real.Angle → R`, not the (k, j)-graded, formal-variable
-- structure row3's Step 2–6 actually needs (a Laurent polynomial in a *second* indeterminate z
-- tracking k, with ℤ[i] coefficients from j). Reusing `GridChar` for the finished construction (item
-- 1 above) remains the right starting point for whoever attempts it next; it is not used for the two
-- items actually proved here, which are independent of the flux machinery.
import Erdos634.Draft.FluxCancel
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Complex.Basic

open scoped Classical

namespace Erdos634.Geometry.Row3

/-! ## Item 2 (row3 PROOF.md Step 2): grid uniqueness for `Zα + Z(π/2)`, `α ∉ ℚπ`

The paper's grid is `G = θ₀ + Zα + Z(π/2) (mod 2π)`, and every `θ ∈ G` has a *unique* expression
`θ₀ + kα + jπ/2` with `k ∈ ℤ`, `j ∈ ℤ/4`. Stated here without the base direction `θ₀` (it cancels):
two grid displacements `kα + jπ/2` and `k'α + j'π/2` agree mod `2π` iff `k = k'` and `j ≡ j' (mod 4)`.
-/

/-- **Grid uniqueness.** If `α / π` is irrational and `kα + jπ/2 = k'α + j'π/2 + m·2π` for integers
`k, k', j, j', m`, then `k = k'` and `j ≡ j' (mod 4)`. This is row3 PROOF.md's Step 2 ("every
`θ ∈ G` has a unique expression `θ₀ + kα + jπ/2`"), stripped of the base point `θ₀` and of the
`Real.Angle` packaging (the mod-`2π` congruence is stated directly as an equation with an explicit
integer multiple of `2π`, which is exactly what `θ = θ' (mod 2π)` unfolds to). -/
theorem grid_unique {α : ℝ} (hα : Irrational (α / Real.pi)) (k k' j j' m : ℤ)
    (heq : (k : ℝ) * α + (j : ℝ) * (Real.pi / 2)
         = (k' : ℝ) * α + (j' : ℝ) * (Real.pi / 2) + (m : ℝ) * (2 * Real.pi)) :
    k = k' ∧ (4 : ℤ) ∣ (j - j') := by
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  -- Clear denominators: `2(k-k')α = ((j'-j) + 4m)·π`.
  have hlin : (2 * (k - k') : ℝ) * α = ((j' - j) + 4 * m : ℝ) * Real.pi := by
    have h2 : (2:ℝ) * ((k : ℝ) * α + (j : ℝ) * (Real.pi / 2))
        = 2 * ((k' : ℝ) * α + (j' : ℝ) * (Real.pi / 2) + (m : ℝ) * (2 * Real.pi)) := by
      rw [heq]
    push_cast
    push_cast at h2
    ring_nf
    ring_nf at h2
    linarith
  have hkk' : k = k' := by
    by_contra hne
    have hne' : (2 * (k - k') : ℤ) ≠ 0 := by
      intro h0
      apply hne
      rcases mul_eq_zero.mp h0 with h | h
      · norm_num at h
      · omega
    have hd : ((2 * (k - k') : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hne'
    have hd' : (2 * ((k:ℝ) - (k':ℝ)) : ℝ) ≠ 0 := by
      have : ((2 * (k - k') : ℤ) : ℝ) = 2 * ((k:ℝ) - (k':ℝ)) := by push_cast; ring
      rwa [this] at hd
    apply hα
    refine ⟨(((j' - j) + 4 * m : ℤ) : ℚ) / ((2 * (k - k') : ℤ) : ℚ), ?_⟩
    rw [Rat.cast_div]
    push_cast
    rw [div_eq_div_iff hd' hpi]
    linarith [hlin]
  refine ⟨hkk', ?_⟩
  subst hkk'
  have h0 : ((j' - j : ℝ) + 4 * m) * Real.pi = 0 := by
    have := hlin
    simp only [sub_self, mul_zero, zero_mul] at this
    linarith [this]
  have h1 : (j' - j : ℝ) + 4 * m = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact h
    · exact absurd h hpi
  have h2 : (j' : ℤ) - j + 4 * m = 0 := by exact_mod_cast h1
  exact ⟨m, by omega⟩

/-- Non-vacuity witness for `grid_unique`'s hypothesis: `α = √2·π` has `α / π = √2` irrational. -/
theorem grid_unique_witness : Irrational ((Real.sqrt 2 * Real.pi) / Real.pi) := by
  rw [mul_div_assoc, div_self Real.pi_ne_zero, mul_one]
  exact irrational_sqrt_two

/-! ## Item 5, the endgame only (row3 PROOF.md Step 7): the ℤ[i]-quadratic forces `N` even

Proposition RP Step 7: `λ² + sλ + t = 0` with `s = P₁ + Q₋₁`, `t = P₁Q₋₁ − P₀Q₀ ∈ ℤ[i]`, and
`λ² = N/2` (Step 1). Gaussian integers are represented here directly as pairs `(a,b) ↦ a + bi : ℂ`
(no `GaussianInt`/`Zsqrtd` import: the two arithmetic facts needed, real/imaginary parts and integer
divisibility, are simpler to drive by hand than through that structure's API, and neither `Zsqrtd`
nor `LaurentPolynomial` is used anywhere else in `Erdos634`, so this avoids an import with no other
consumer). -/

/-- **The integer core of Step 7's endgame**: `N·q² = 2·p²` with `q ≠ 0` forces `N` even. This is
the arithmetic engine behind *both* of row3's Step 7 branches (`s ≠ 0 ⇒ λ ∈ ℚ, N = 2m²`; `s = 0 ⇒
N/2 ∈ ℤ`): both reduce `λ` to a ratio of two integers `p/q`, and `N = 2λ²` then forces this form. -/
theorem even_of_two_mul_sq_eq (N : ℕ) (p q : ℤ) (hq : q ≠ 0) (h : (N : ℤ) * q ^ 2 = 2 * p ^ 2) :
    Even N := by
  set P := p.natAbs with hP
  set Q := q.natAbs with hQ
  have hQ0 : Q ≠ 0 := by simp [hQ, hq]
  have hPQ : N * Q ^ 2 = 2 * P ^ 2 := by
    have e1 : (p:ℤ) ^ 2 = (P:ℤ) ^ 2 := by rw [hP, Int.natAbs_sq]
    have e2 : (q:ℤ) ^ 2 = (Q:ℤ) ^ 2 := by rw [hQ, Int.natAbs_sq]
    have : (N:ℤ) * (Q:ℤ) ^ 2 = 2 * (P:ℤ) ^ 2 := by rw [← e1, ← e2]; exact h
    exact_mod_cast this
  clear h hP hQ
  -- reduce by g = gcd P Q
  set g := Nat.gcd P Q with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right P (Nat.pos_of_ne_zero hQ0)
  obtain ⟨P', hP'⟩ := Nat.gcd_dvd_left P Q
  obtain ⟨Q', hQ'⟩ := Nat.gcd_dvd_right P Q
  have hcop : Nat.Coprime P' Q' := by
    have := Nat.coprime_div_gcd_div_gcd (m := P) (n := Q) hgpos
    have eP : P / g = P' := by rw [hP']; exact Nat.mul_div_cancel_left _ hgpos
    have eQ : Q / g = Q' := by rw [hQ']; exact Nat.mul_div_cancel_left _ hgpos
    rwa [eP, eQ] at this
  have hQ'0 : Q' ≠ 0 := by
    intro h0; apply hQ0; rw [hQ', h0, mul_zero]
  have hred : 2 * P' ^ 2 = N * Q' ^ 2 := by
    have hmain : N * (g * Q') ^ 2 = 2 * (g * P') ^ 2 := by rw [← hP', ← hQ']; exact hPQ
    have h1 : (g * Q') ^ 2 = g ^ 2 * Q' ^ 2 := by ring
    have h2 : (g * P') ^ 2 = g ^ 2 * P' ^ 2 := by ring
    rw [h1, h2] at hmain
    have hg2 : g ^ 2 ≠ 0 := pow_ne_zero 2 hgpos.ne'
    have heq2 : g ^ 2 * (N * Q' ^ 2) = g ^ 2 * (2 * P' ^ 2) := by
      rw [show g ^ 2 * (N * Q' ^ 2) = N * (g ^ 2 * Q' ^ 2) by ring,
          show g ^ 2 * (2 * P' ^ 2) = 2 * (g ^ 2 * P' ^ 2) by ring]
      exact hmain
    exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hg2) heq2).symm
  have hdvd : Q' ^ 2 ∣ 2 * P' ^ 2 := ⟨N, by rw [hred]; ring⟩
  have hcopsq : Nat.Coprime (Q' ^ 2) (P' ^ 2) := (hcop.symm.pow_left 2).pow_right 2
  have hdvd2 : Q' ^ 2 ∣ 2 := (Nat.Coprime.dvd_of_dvd_mul_right hcopsq hdvd)
  have hle : Q' ^ 2 ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2
  have hub : Q' ≤ 2 := by nlinarith
  have hQ'1 : Q' = 1 := by
    interval_cases Q'
    · exact absurd rfl hQ'0
    · rfl
    · exfalso; norm_num at hle
  rw [hQ'1] at hred
  simp only [one_pow, mul_one] at hred
  exact ⟨P' ^ 2, by omega⟩

/-- **Row3 Proposition RP, Step 7's endgame.** `λ² + sλ + t = 0` (`s = a+bi`, `t = c+di`,
`a b c d : ℤ`), together with `(N:ℝ) = 2λ²` (Step 1's area identity), forces `Even N`. Real/imaginary
parts of the complex equation give `2a·λ = −N − 2c` and `b·λ = −d`; whichever of `a, b` is nonzero
exhibits `λ` as a ratio of two integers, and `even_of_two_mul_sq_eq` finishes. If `a = b = 0` (the
paper's `s = 0` branch), the real part alone gives `N = −2c` directly. -/
theorem step7_even (N : ℕ) (a b c d : ℤ) (lam : ℝ) (hN : (N : ℝ) = 2 * lam ^ 2)
    (heq : (lam:ℂ) ^ 2 + ((a:ℂ) + (b:ℂ) * Complex.I) * (lam:ℂ) + ((c:ℂ) + (d:ℂ) * Complex.I) = 0) :
    Even N := by
  have hre : lam ^ 2 + (a:ℝ) * lam + (c:ℝ) = 0 := by
    have h1 := congrArg Complex.re heq
    simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im, Complex.zero_re] at h1
    linarith [h1]
  have him : (b:ℝ) * lam + (d:ℝ) = 0 := by
    have h1 := congrArg Complex.im heq
    simp only [pow_two, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im, Complex.zero_im] at h1
    linarith [h1]
  have heq1 : 2 * (a:ℝ) * lam = -(N:ℝ) - 2 * (c:ℝ) := by rw [hN]; nlinarith [hre]
  by_cases hb : b = 0
  · subst hb
    have hd0 : (d:ℝ) = 0 := by simpa using him
    have hd0' : d = 0 := by exact_mod_cast hd0
    by_cases ha : a = 0
    · subst ha
      have h0 : -(N:ℝ) - 2 * (c:ℝ) = 0 := by simpa using heq1.symm
      have hNc' : (N:ℝ) = -2 * (c:ℝ) := by linarith
      have hNc : (N:ℤ) = -2 * c := by exact_mod_cast hNc'
      exact ⟨(-c).toNat, by omega⟩
    · have haR : (a:ℝ) ≠ 0 := by exact_mod_cast ha
      apply even_of_two_mul_sq_eq N (N + 2*c) (2*a) (by
        intro h0; apply ha; omega)
      have hlam : lam = -((N:ℝ) + 2*c) / (2*a) := by
        field_simp
        linarith [heq1]
      have hsq : lam ^ 2 = ((N:ℝ) + 2*c) ^ 2 / (2*a) ^ 2 := by
        rw [hlam]; ring
      have hkey : (N:ℝ) * (2*a) ^ 2 = 2 * ((N:ℝ) + 2*c) ^ 2 := by
        have h2a2 : ((2:ℝ)*a) ^ 2 ≠ 0 := by positivity
        have hN' := hN
        rw [hsq] at hN'
        field_simp at hN'
        linarith [hN']
      have hcast : ((N:ℤ):ℝ) * (((2*a:ℤ)):ℝ) ^ 2 = 2 * (((N + 2*c:ℤ)):ℝ) ^ 2 := by
        push_cast; linarith [hkey]
      exact_mod_cast hcast
  · have hbR : (b:ℝ) ≠ 0 := by exact_mod_cast hb
    apply even_of_two_mul_sq_eq N d b hb
    have hlam : lam = -(d:ℝ) / b := by field_simp; linarith [him]
    have : (N:ℝ) * (b:ℝ) ^ 2 = 2 * (d:ℝ) ^ 2 := by
      have hb2 : (b:ℝ) ^ 2 ≠ 0 := by positivity
      have hsq : lam ^ 2 = (d:ℝ) ^ 2 / (b:ℝ) ^ 2 := by rw [hlam]; ring
      rw [hsq] at hN
      field_simp at hN
      linarith [hN]
    exact_mod_cast this

/-- Non-vacuity witness for `step7_even`: row3 PROOF.md's `N = 2` case (§5 table, `λ = 1`, `s ≠ 0`
in the sense `a = 1, b = 0`; `c = -1, d = 0`), i.e. the quadratic `λ² + λ − 1 + ... ` — concretely
`λ = 1` solves `λ² − 1 = 0` (`a=b=0, c=-1, d=0`, the `s = 0` branch, `N = 2λ² = 2`). -/
theorem step7_even_witness_N2 : Even (2 : ℕ) := by
  apply step7_even 2 0 0 (-1) 0 (1:ℝ) (by norm_num)
  push_cast
  ring

/-- A second, `s ≠ 0` witness: `a = 1, b = 0, c = 0, d = 0`, `λ = -1` solves `λ² + λ = 0`? Check:
`1 - 1 = 0` ✓, and `N = 2λ² = 2`. -/
theorem step7_even_witness_N2' : Even (2 : ℕ) := by
  apply step7_even 2 1 0 0 0 (-1:ℝ) (by norm_num)
  push_cast
  ring

end Erdos634.Geometry.Row3

#print axioms Erdos634.Geometry.Row3.grid_unique
#print axioms Erdos634.Geometry.Row3.grid_unique_witness
#print axioms Erdos634.Geometry.Row3.even_of_two_mul_sq_eq
#print axioms Erdos634.Geometry.Row3.step7_even
#print axioms Erdos634.Geometry.Row3.step7_even_witness_N2
#print axioms Erdos634.Geometry.Row3.step7_even_witness_N2'
