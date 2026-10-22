-- Draft/FluxDRow11Prime.lean — ROW 11 AT PRIME N: no `N`-tiling, `N` prime, of the base-α target
-- `(α, α, α + 2β)` by the `3α + 2β = π` tile with `α ∉ ℚπ` (reflections allowed, not necessarily
-- edge-to-edge).  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- ROUTE: R11 + `prop:isoalphaprime` (rationality_proofs.md P0 / ROW11_RATIONALITY.md P2
-- "Consequences": "R11 plus prop:isoalphaprime gives a second, independent route to R15's exclusion").
-- * R11 (`Row11.rational`, Draft/FluxDRow11): `s = a/c = e/f`, `gcd(e, f) = 1`, `0 < e < f`.
-- * The tiling equation `N(f−e)(2f+e)² = M²(f+e)(2f²−e²)` (`Row11.area`): Theorem 1's `M`
--   (`Row11.setup`), S, and the area identity (`abs_detTri_target`, Heron in symmetric form).
-- * Side integrality: the leg word (W, Draft/FluxDSideWord) gives `X'·(2f+e) = M·f²·(f+e)` with
--   `X' = n_a·ef + n_b·(f²−e²) + n_c·f² ∈ ℕ`.
-- * `IsoAlpha.isoalpha_X_forces` ((2f+e) ∣ M) and `IsoAlpha.isoalpha_not_prime` (the verified corpus's
--   arithmetic of prop:isoalphaprime) close it.
-- This supplies, in Lean, the rationality input whose citation review 2b flagged as the scope defect of
-- prop:isoalphaprime as written (PAPER_ERRATA R2b-2): here it is R11, not Beeson III.
--
-- REDISCOVERY STATUS, said plainly: the conclusion is R15's (PROVED, two reviews) and
-- prop:isoalphaprime's; nothing new mathematically.  It is formalization debt: row 11 at primes, with
-- every geometric step from the flux layer, W and the area identity.
-- CONDITIONAL: the base-α target has no known real tiling at ANY `N` (ROW11_RATIONALITY.md §5), so
-- the hypotheses have no known joint instance even without primality.  The arithmetic chain is
-- exercised (Draft/FluxDRow11PrimeWitness.lean) on the algebraic model `s = 1/2`, `M = 5`,
-- `N = 21 = 21·1²` (`e = 1, f = 2, d = 1, m = 1`, leg `X' = 12`), which meets every arithmetic
-- hypothesis except primality.
--
-- Formalization debt; not progress on the three /goal outcomes (row 11 is not the base-β branch).
import Erdos634.Draft.FluxDRow11
import Erdos634.IsoAlphaPrime

open scoped Classical

namespace Erdos634.Geometry

variable {N : ℕ}

/-- **Row 11's tiling equation** `N(1−s)(2+s)² = M²(1+s)(2−s²)` (`q = N/M² = F(s)`), with the leg
`X(2+s) = M c (1+s)`, `M ≥ 1`. -/
theorem Row11.area (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hP0 : D.target.angleAt 0 = α) (hP1 : D.target.angleAt 1 = α) :
    ∃ (s : ℝ) (M : ℤ), 0 < s ∧ s < 1 ∧ 0 < c ∧ a = s * c ∧ b = (1 - s ^ 2) * c ∧ 1 ≤ M ∧
      D.target.oppLen 0 * (2 + s) = M * c * (1 + s) ∧
      (N : ℝ) * (1 - s) * (2 + s) ^ 2 = (M : ℝ) ^ 2 * (1 + s) * (2 - s ^ 2) := by
  have hP2 : D.target.angleAt 2 = α + 2 * β := by
    have := D.target.angleAt_sum; rw [hP0, hP1] at this; linarith
  obtain ⟨s, K, M, hs0, hs1, hc, ha, hb, -, -, -, -, hM1, -, -, hleg, hY⟩ :=
    Row11.setup D hα hrel h hP0 hP1
  obtain ⟨-, -, -, -, -, -, -, -, hX1⟩ := Row11.sides D hrel h hP0 hP1 hP2
  have hX : 0 < D.target.oppLen 0 := D.target.oppLen_pos 0
  have hs2lt : s ^ 2 < 1 := by
    have h' : s * s < s * 1 := mul_lt_mul_of_pos_left hs1 hs0
    have : s ^ 2 = s * s := sq s
    linarith
  obtain ⟨σ, -, o0, -, o1, -, o2⟩ := h
  set X := D.target.oppLen 0 with hXdef
  -- area: `|det P| = N |det T|`, Heron on both sides
  have hA := D.abs_detTri_target
  have hsq : Erdos634.AreaDet.detTri D.target ^ 2
      = (N : ℝ) ^ 2 * Erdos634.AreaDet.detTri D.model ^ 2 := by
    rw [← sq_abs (Erdos634.AreaDet.detTri D.target), hA, mul_pow, sq_abs]
  have hT := D.target.four_detTri_sq_symm
  have hMo := D.model.four_detTri_sq_symm
  rw [Tri.sum_pow_perm' D.model 2 σ, Tri.sum_pow_perm' D.model 4 σ, o0, o1, o2] at hMo
  rw [Fin.sum_univ_three, Fin.sum_univ_three, hX1, ← hXdef, hY] at hT
  rw [ha, hb] at hMo
  have hG : 0 < s ^ 2 * (4 - s ^ 2) := mul_pos (pow_pos hs0 2) (by linarith)
  have key : (s ^ 2 * (4 - s ^ 2)) * (((2 - s ^ 2) * X ^ 2 - N * (1 - s ^ 2) * c ^ 2)
      * ((2 - s ^ 2) * X ^ 2 + N * (1 - s ^ 2) * c ^ 2)) = 0 := by
    linear_combination (-1 : ℝ) * hT + (N : ℝ) ^ 2 * hMo + 4 * hsq
  have hsum : 0 < (2 - s ^ 2) * X ^ 2 + N * (1 - s ^ 2) * c ^ 2 :=
    add_pos_of_pos_of_nonneg (mul_pos (by linarith) (pow_pos hX 2))
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg N) (by linarith)) (sq_nonneg c))
  have hAB : (2 - s ^ 2) * X ^ 2 = N * (1 - s ^ 2) * c ^ 2 := by
    rcases mul_eq_zero.mp key with e | e
    · exact absurd e hG.ne'
    · rcases mul_eq_zero.mp e with e' | e'
      · linarith
      · exact absurd e' hsum.ne'
  have hgoal : c ^ 2 * (1 + s) * ((N : ℝ) * (1 - s) * (2 + s) ^ 2 - (M : ℝ) ^ 2 * (1 + s) * (2 - s ^ 2))
      = 0 := by
    linear_combination (-(2 + s) ^ 2) * hAB + ((2 - s ^ 2) * (X * (2 + s) + M * c * (1 + s))) * hleg
  have hne : c ^ 2 * (1 + s) ≠ 0 := (mul_pos (pow_pos hc 2) (by linarith)).ne'
  refine ⟨s, M, hs0, hs1, hc, ha, hb, hM1, hleg, ?_⟩
  exact sub_eq_zero.mp ((mul_eq_zero.mp hgoal).resolve_left hne)

/-- **ROW 11 AT PRIME N** (R15's conclusion; route R11 + prop:isoalphaprime): there is no `N`-tiling,
`N` prime, of the base-α target by the `3α + 2β = π` tile with `α ∉ ℚπ`. -/
theorem Row11.prime_excluded (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hP0 : D.target.angleAt 0 = α) (hP1 : D.target.angleAt 1 = α) (hN : N.Prime) : False := by
  obtain ⟨s, M, hs0, hs1, hc, ha, hb, hM1, hleg, harea⟩ := Row11.area D hα hrel h hP0 hP1
  obtain ⟨r, hr⟩ := Row11.rational D hα hrel h hP0 hP1
  have hsr : s = r := by
    have : c * (s - r) = 0 := by rw [ha] at hr; linear_combination hr
    linarith [(mul_eq_zero.mp this).resolve_left hc.ne']
  -- `s = e/f` in lowest terms, `f = e + d`, `e, d ≥ 1`
  have hr0 : 0 < r := by exact_mod_cast (hsr ▸ hs0 : (0 : ℝ) < r)
  obtain ⟨e, he⟩ : ∃ e : ℕ, r.num = e := ⟨r.num.toNat, (Int.toNat_of_nonneg (Rat.num_pos.mpr hr0).le).symm⟩
  obtain ⟨f, hfdef⟩ : ∃ f : ℕ, f = r.den := ⟨_, rfl⟩
  have hf0 : 0 < f := hfdef ▸ r.den_pos
  have hcop : Nat.Coprime e f := by
    have := r.reduced; rw [he, ← hfdef] at this; simpa using this
  have hsef : s = (e : ℝ) / f := by
    rw [hsr, ← Rat.num_div_den r, he, ← hfdef]
    push_cast <;> ring
  have hfR : (0 : ℝ) < f := by exact_mod_cast hf0
  have he1 : 1 ≤ e := by
    have : (0 : ℝ) < e := by
      have h1 := hs0; rw [hsef] at h1
      have h2 := mul_pos h1 hfR
      rwa [div_mul_cancel₀ _ hfR.ne'] at h2
    exact_mod_cast this
  have hef : e < f := by
    have : (e : ℝ) < f := by
      have := hs1; rw [hsef, div_lt_one hfR] at this; exact this
    exact_mod_cast this
  obtain ⟨d, hd⟩ : ∃ d, f = e + d := ⟨f - e, by omega⟩
  have hd1 : 1 ≤ d := by omega
  -- `M` natural
  obtain ⟨m', rfl⟩ := Int.eq_ofNat_of_zero_le (by linarith : (0 : ℤ) ≤ M)
  push_cast at hleg harea
  have hfd : (f : ℝ) = e + d := by rw [hd]; push_cast; ring
  -- the tiling equation over ℕ: `N·d·(3e+2d)² = m'²·(2e+d)·(e²+4ed+2d²)`
  have hNeq : N * d * (3 * e + 2 * d) ^ 2 = m' ^ 2 * ((2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2)) := by
    have hf' : (f : ℝ) ≠ 0 := hfR.ne'
    have key : (N : ℝ) * d * (3 * e + 2 * d) ^ 2 - (m' : ℝ) ^ 2 * ((2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2))
        = (f : ℝ) ^ 3 * ((N : ℝ) * (1 - s) * (2 + s) ^ 2 - (m' : ℝ) ^ 2 * (1 + s) * (2 - s ^ 2)) := by
      rw [hsef, hfd]
      have hed : (e : ℝ) + d ≠ 0 := by rw [← hfd]; exact hf'
      field_simp <;> ring
    rw [harea, sub_self, mul_zero, sub_eq_zero] at key
    exact_mod_cast key
  -- the leg word gives `X'·(2f+e) = m'·f²·(f+e)`
  obtain ⟨na, nb, nc, hw⟩ := D.side_word_threeAlpha h 0
  set X' : ℕ := na * (e * (e + d)) + nb * (d * (2 * e + d)) + nc * (e + d) ^ 2 with hX'def
  have hXeq : X' * (2 * (e + d) + e) = m' * ((e + d + e) * (e + d) ^ 2) := by
    have hf' : (f : ℝ) ≠ 0 := hfR.ne'
    have hX'R : (X' : ℝ) * c = D.target.oppLen 0 * (f : ℝ) ^ 2 := by
      rw [hw, ha, hb, hsef, hfd, hX'def]
      have hed : (e : ℝ) + d ≠ 0 := by rw [← hfd]; exact hf'
      push_cast
      field_simp <;> ring
    have hlegf : D.target.oppLen 0 * (2 * f + e) = m' * c * (f + e) := by
      have := hleg
      rw [hsef] at this
      field_simp at this
      linear_combination this
    have hc' : c ≠ 0 := hc.ne'
    have : c * ((X' : ℝ) * (2 * (e + d) + e) - m' * ((e + d + e) * (e + d) ^ 2)) = 0 := by
      rw [hfd] at hlegf hX'R
      linear_combination (2 * ((e : ℝ) + d) + e) * hX'R + ((e : ℝ) + d) ^ 2 * hlegf
    have h2 := sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hc')
    exact_mod_cast h2
  -- `(2f+e) ∣ M`
  have hcop' : Nat.Coprime e (e + d) := by rw [← hd]; exact hcop
  obtain ⟨m, hm⟩ := Erdos634.IsoAlpha.isoalpha_X_forces e (e + d) m' X' hcop' hXeq
  -- the reduced equation `N·d = m²·(2e+d)·(e²+4ed+2d²)`
  have hred : N * d = m ^ 2 * ((2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2)) := by
    rw [hm] at hNeq
    have h3 : 0 < (3 * e + 2 * d) ^ 2 := by positivity
    have e2 : 2 * (e + d) + e = 3 * e + 2 * d := by ring
    rw [e2] at hNeq
    have : (3 * e + 2 * d) ^ 2 * (N * d) = (3 * e + 2 * d) ^ 2 * (m ^ 2 * ((2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2))) := by
      calc (3 * e + 2 * d) ^ 2 * (N * d) = N * d * (3 * e + 2 * d) ^ 2 := by ring
        _ = ((3 * e + 2 * d) * m) ^ 2 * ((2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2)) := hNeq
        _ = _ := by ring
    exact Nat.eq_of_mul_eq_mul_left h3 this
  exact Erdos634.IsoAlpha.isoalpha_not_prime N e d m hN he1 hd1 hcop' hred

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row11.area
#print axioms Erdos634.Geometry.Row11.prime_excluded
