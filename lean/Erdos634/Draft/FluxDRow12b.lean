-- Draft/FluxDRow12b.lean — ROW 12(b) (rationality/rationality_proofs.md §4(b); second review
-- review2_rationality_b/VERDICT_BLIND §2): on the base-β target `(β, β, 3α)`, at PRIME `N`, the
-- `3α + 2β = π` tile with `α ∉ ℚπ` is rational.  Also ROW 12(a) in its strict form (`q > 1`).
-- Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- The file's proof, step by step, with where each input comes from:
-- * Theorem 1's colouring number `M`: `M(a+b+c) = Y + 2X`, `M ≡ N (2)`, `|M| ≤ N` — the χ₋ half of
--   `Row12.flux_identities` (FluxCRow12).  The χ₊ integer `K` is DISCARDED: the file's 12(b) proof
--   does not use it (with `K`, `Row12.rational` already gives `s ∈ ℚ` for every `N`; see below).
-- * S (law of sines): `a = s·c`, `b = (1−s²)c`, `Y = s(3−s²)X`, legs equal, `0 < s < 1`
--   (`Row12.sides`, a re-derivation of the first lines of `Row12.ratio`'s proof, which are not
--   exported — said plainly).  Hence the leg `X(1+s) = M·c`.
-- * Area (`CongruentDissection.abs_detTri_target`, `Tri.four_detTri_sq`, FluxCRow2): Heron in
--   symmetric form gives `X²(3−s²) = N·c²`, i.e. the tiling quadratic
--   `(N+M²)s² + 2Ns + (N−3M²) = 0` (`q = N/M² = (3−s²)/(1+s)²`).
-- * W (side words, Draft/FluxDSideWord): leg `= n_a a + n_b b + n_c c`, base `= m_a a + m_b b + m_c c`.
-- * `s ∉ ℚ` ⇒ coordinates in `{1, s}` are unique (`irr_coord_eq_zero`).  Leg s-coordinate:
--   `2M(N+M²)n_a + 4MN·n_b = (N+M²)²` (`Row12.leg_coeff`), so `M ∣ N²`.  Base s-coordinate:
--   `M(N+M²)m_a + 2MN·m_b = N(M²−N)` (`Row12.base_coeff`; = the file's `Mq(1−q)/(q+1)`).
-- * `N` prime, `0 < M ≤ N`, `M ∣ N²` ⇒ `M ∈ {1, N}`.  `M = 1`: the base coefficient is
--   `N(1−N) < 0` ⊥ (the file's step 3 via (a)).
--   DEVIATION (named): `M = N` is excluded here by the range `q > 1/2` (`q = 1/N ≤ 1/2`, while
--   `(3−s²)/(1+s)² > 1/2` on `(0,1)`), NOT by the file's step 2 `M ≤ N − 2` ("some two tiles share an
--   edge, so there is a white tile") — that adjacency fact has no Lean.
--
-- REDUNDANCY, said plainly: `Row12.rational` (FluxCRow12, R12 via the second character χ₊) already
-- proves `a/c ∈ ℚ` for EVERY `N`, so the conclusion here is not new in Lean.  This file formalizes
-- the file's own route (Theorem 1 + area + words, no χ₊), i.e. the debt row "12(b)" as written.
--
-- Witnesses: Draft/FluxDRow12bWitness.lean.  The geometric hypotheses minus primality are met by the
-- real 44- and 99-tilings; NO real prime-`N` tiling of this target is known (that is the open base-β
-- question itself), so the full hypothesis set has no known instance.  The algebraic lemmas are
-- witnessed with an irrational `s` (the review's `N = 15`, `M = 5`, `s = (−3+√105)/8` model).
--
-- Formalization debt; not progress on the three /goal outcomes.
import Erdos634.Draft.FluxDSideWord
import Erdos634.Draft.FluxCRow12
import Erdos634.Draft.FluxCRow2

open scoped Classical

namespace Erdos634.Geometry

variable {N : ℕ}

/-! ## Unique coordinates, Heron in symmetric form -/

/-- **Coordinates in `{1, s}` are unique when `s ∉ ℚ`**: `q·s + p = 0` with `p, q ∈ ℤ` forces
`q = p = 0`. -/
theorem irr_coord_eq_zero {s : ℝ} (hs : ¬ ∃ r : ℚ, s = r) {p q : ℤ}
    (h : (q : ℝ) * s + p = 0) : q = 0 ∧ p = 0 := by
  by_cases hq : q = 0
  · subst hq
    refine ⟨rfl, ?_⟩
    have : (p : ℝ) = 0 := by simpa using h
    exact_mod_cast this
  · exfalso
    apply hs
    have hq' : (q : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hq
    refine ⟨-(p : ℚ) / q, ?_⟩
    push_cast
    rw [eq_div_iff hq']
    linear_combination h

/-- Heron (Cayley–Menger) in symmetric form: `4·det² = (Σ ℓ²)² − 2 Σ ℓ⁴`. -/
theorem Tri.four_detTri_sq_symm (T : Tri) :
    4 * Erdos634.AreaDet.detTri T ^ 2
      = (∑ k, T.oppLen k ^ 2) ^ 2 - 2 * ∑ k, T.oppLen k ^ 4 := by
  rw [T.four_detTri_sq, Fin.sum_univ_three, Fin.sum_univ_three]
  ring

/-- Power sums of the sides under a relabelling (copy of `Tri.sum_perm`, Draft/FluxCRow5, to avoid
that import). -/
theorem Tri.sum_pow_perm' (T : Tri) (n : ℕ) (σ : Equiv.Perm (Fin 3)) :
    ∑ k, T.oppLen k ^ n = T.oppLen (σ 0) ^ n + T.oppLen (σ 1) ^ n + T.oppLen (σ 2) ^ n := by
  rw [← Equiv.sum_comp σ (fun k => T.oppLen k ^ n), Fin.sum_univ_three]

/-! ## S: the sides of the base-β target and of the tile -/

/-- **S for the base-β target** (re-derivation of the first lines of `Row12.ratio`'s proof):
`a = s c`, `b = (1 − s²) c`, `Y = s(3 − s²) X`, `X₁ = X`, with `s = 2 sin(α/2) ∈ (0, 1)`. -/
theorem Row12.sides (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi) (h : D.model.ThreeAlphaData α β a b c)
    (hP0 : D.target.angleAt 0 = β) (hP1 : D.target.angleAt 1 = β)
    (hP2 : D.target.angleAt 2 = 3 * α) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ 0 < c ∧ 0 < D.target.oppLen 0 ∧
      a = s * c ∧ b = (1 - s ^ 2) * c ∧
      D.target.oppLen 2 = s * (3 - s ^ 2) * D.target.oppLen 0 ∧
      D.target.oppLen 1 = D.target.oppLen 0 := by
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  obtain ⟨tγ, tα, tβ, t3α⟩ := threeAlpha_sin_table hrel
  have ls1 := D.model.lawSin (σ 0) (σ 2)
  have ls2 := D.model.lawSin (σ 1) (σ 2)
  rw [h0, o2, h2, o0, tα, tγ] at ls1
  rw [h1, o2, h2, o1, tβ, tγ] at ls2
  have lt0 := D.target.lawSin 0 2
  have lt1 := D.target.lawSin 1 2
  rw [hP0, hP2, tβ, t3α] at lt0
  rw [hP1, hP2, tβ, t3α] at lt1
  have hαpos : 0 < α := h0 ▸ D.model.angleAt_pos' (σ 0)
  have hβpos : 0 < β := h1 ▸ D.model.angleAt_pos' (σ 1)
  have hπ := Real.pi_pos
  have hco : 0 < Real.cos (α / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs0 : 0 < Real.sin (α / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hs1 : Real.sin (α / 2) < 1 / 2 := by
    rw [← Real.sin_pi_div_six]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  have hc : 0 < c := o2 ▸ D.model.oppLen_pos (σ 2)
  have hX : 0 < D.target.oppLen 0 := D.target.oppLen_pos 0
  set u := Real.sin (α / 2) with hudef
  set co := Real.cos (α / 2) with hcodef
  set X := D.target.oppLen 0 with hXdef
  set X₁ := D.target.oppLen 1 with hX1def
  set Y := D.target.oppLen 2 with hYdef
  have hq : 0 < 1 - 4 * u ^ 2 := by nlinarith
  have ha : a = 2 * u * c :=
    mul_left_cancel₀ hco.ne' (by linear_combination (-1 : ℝ) * ls1)
  have hb : b = (1 - 4 * u ^ 2) * c :=
    mul_left_cancel₀ hco.ne' (by linear_combination (-1 : ℝ) * ls2)
  have hcq : co * (1 - 4 * u ^ 2) ≠ 0 := (mul_pos hco hq).ne'
  have hY : Y = 2 * u * (3 - 4 * u ^ 2) * X :=
    mul_left_cancel₀ hcq (by linear_combination lt0)
  have hY1 : Y = 2 * u * (3 - 4 * u ^ 2) * X₁ :=
    mul_left_cancel₀ hcq (by linear_combination lt1)
  have hr : 2 * u * (3 - 4 * u ^ 2) ≠ 0 := by
    have : 0 < 3 - 4 * u ^ 2 := by nlinarith
    exact (mul_pos (mul_pos two_pos hs0) this).ne'
  have hX1 : X₁ = X := mul_left_cancel₀ hr (by linear_combination hY - hY1)
  refine ⟨2 * u, by linarith, by linarith, hc, hX, ?_, ?_, ?_, hX1⟩
  · rw [ha]
  · rw [hb]; ring
  · rw [hY]; ring

/-! ## Theorem 1 + S + area: the leg and the tiling quadratic -/

/-- **Row 12's tiling data.**  With Theorem 1's `M` (χ₋ half of `Row12.flux_identities`; `K` is not
used): `M ≡ N (2)`, `0 < M ≤ N`, the leg `X(1+s) = M·c`, `Y = s(3−s²)X`, and the area quadratic
`(N+M²)s² + 2Ns + (N−3M²) = 0`. -/
theorem Row12.setup (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hP0 : D.target.angleAt 0 = β) (hP1 : D.target.angleAt 1 = β) :
    ∃ (s : ℝ) (M : ℤ), 0 < s ∧ s < 1 ∧ 0 < c ∧ a = s * c ∧ b = (1 - s ^ 2) * c ∧
      (2 : ℤ) ∣ M - N ∧ |M| ≤ N ∧ 0 < M ∧
      (M : ℝ) * (a + b + c) = D.target.oppLen 2 + 2 * D.target.oppLen 0 ∧
      (M : ℝ) * c = D.target.oppLen 0 * (1 + s) ∧
      D.target.oppLen 2 = s * (3 - s ^ 2) * D.target.oppLen 0 ∧
      ((N : ℝ) + (M : ℝ) ^ 2) * s ^ 2 + 2 * N * s + (N - 3 * (M : ℝ) ^ 2) = 0 := by
  have hP2 : D.target.angleAt 2 = 3 * α := by
    have := D.target.angleAt_sum; rw [hP0, hP1] at this; linarith
  obtain ⟨-, M, -, hM2, -, hMN, -, hM⟩ := Row12.flux_identities D hα hrel h hP0 hP1 hP2
  obtain ⟨s, hs0, hs1, hc, hX, ha, hb, hY, hX1⟩ := Row12.sides D hrel h hP0 hP1 hP2
  have hs2lt : s ^ 2 < 1 := by
    have h' : s * s < s * 1 := mul_lt_mul_of_pos_left hs1 hs0
    have : s ^ 2 = s * s := sq s
    linarith
  obtain ⟨σ, -, o0, -, o1, -, o2⟩ := h
  rw [hX1] at hM
  have hMid : (M : ℝ) * (a + b + c) = D.target.oppLen 2 + 2 * D.target.oppLen 0 := by
    rw [hM]; ring
  set X := D.target.oppLen 0 with hXdef
  set Y := D.target.oppLen 2 with hYdef
  subst ha hb
  rw [hY] at hM
  -- the leg: `(2−s)(1+s)(Mc − X(1+s)) = 0`
  have hpos : 0 < (2 - s) * (1 + s) := mul_pos (by linarith) (by linarith)
  have hleg : (M : ℝ) * c = X * (1 + s) := by
    have e : (2 - s) * (1 + s) * ((M : ℝ) * c - X * (1 + s)) = 0 := by linear_combination hM
    rcases mul_eq_zero.mp e with e0 | e0
    · exact absurd e0 hpos.ne'
    · linarith
  have hM0 : 0 < M := by
    by_contra hm
    push Not at hm
    have hm' : (M : ℝ) ≤ 0 := by exact_mod_cast hm
    have : 0 < X * (1 + s) := mul_pos hX (by linarith)
    have := mul_nonpos_of_nonpos_of_nonneg hm' hc.le
    linarith
  -- area: `|det P| = N |det T|`, Heron on both sides
  have hA := D.abs_detTri_target
  have hsq : Erdos634.AreaDet.detTri D.target ^ 2
      = (N : ℝ) ^ 2 * Erdos634.AreaDet.detTri D.model ^ 2 := by
    rw [← sq_abs (Erdos634.AreaDet.detTri D.target), hA, mul_pow, sq_abs]
  have hT := D.target.four_detTri_sq_symm
  have hMo := D.model.four_detTri_sq_symm
  rw [Tri.sum_pow_perm' D.model 2 σ, Tri.sum_pow_perm' D.model 4 σ, o0, o1, o2] at hMo
  rw [Fin.sum_univ_three, Fin.sum_univ_three, hX1, ← hXdef, ← hYdef, hY] at hT
  have hG : 0 < s ^ 2 * (1 - s ^ 2) ^ 2 * (4 - s ^ 2) := by
    have h1 : 0 < 1 - s ^ 2 := by linarith
    have h2 : 0 < 4 - s ^ 2 := by linarith
    exact mul_pos (mul_pos (pow_pos hs0 2) (pow_pos h1 2)) h2
  have key : (s ^ 2 * (1 - s ^ 2) ^ 2 * (4 - s ^ 2))
      * ((X ^ 2 * (3 - s ^ 2) - N * c ^ 2) * (X ^ 2 * (3 - s ^ 2) + N * c ^ 2)) = 0 := by
    linear_combination (-1 : ℝ) * hT + (N : ℝ) ^ 2 * hMo + 4 * hsq
  have hsum : 0 < X ^ 2 * (3 - s ^ 2) + N * c ^ 2 := by
    have : 0 < 3 - s ^ 2 := by linarith
    exact add_pos_of_pos_of_nonneg (mul_pos (pow_pos hX 2) this)
      (mul_nonneg (Nat.cast_nonneg N) (sq_nonneg c))
  have hAB : X ^ 2 * (3 - s ^ 2) = N * c ^ 2 := by
    rcases mul_eq_zero.mp key with e | e
    · exact absurd e hG.ne'
    · rcases mul_eq_zero.mp e with e' | e'
      · linarith
      · exact absurd e' hsum.ne'
  have hquad : c ^ 2 * (((N : ℝ) + (M : ℝ) ^ 2) * s ^ 2 + 2 * N * s + (N - 3 * (M : ℝ) ^ 2)) = 0 := by
    linear_combination (-(1 + s) ^ 2) * hAB + (-(3 - s ^ 2) * ((M : ℝ) * c + X * (1 + s))) * hleg
  refine ⟨s, M, hs0, hs1, hc, rfl, rfl, hM2, hMN, hM0, hMid, hleg, hY, ?_⟩
  rcases mul_eq_zero.mp hquad with e | e
  · exact absurd e (pow_pos hc 2).ne'
  · exact e

/-! ## The two s-coordinates (pure algebra) -/

/-- **The leg's s-coordinate** (file §4(b) step 1, review 2b §2 step 1): if `s ∉ ℚ` satisfies the
tiling quadratic and the leg word `(1+s)(n_a s + n_b(1−s²) + n_c) = M` holds, then
`2M(N+M²)n_a + 4MN·n_b = (N+M²)²`. -/
theorem Row12.leg_coeff {s : ℝ} (hs : ¬ ∃ r : ℚ, s = r) (hs0 : 0 < s) {M : ℤ} {N : ℕ}
    (hq : ((N : ℝ) + (M : ℝ) ^ 2) * s ^ 2 + 2 * N * s + (N - 3 * (M : ℝ) ^ 2) = 0)
    {na nb nc : ℕ} (hw : (1 + s) * (na * s + nb * (1 - s ^ 2) + nc) = M) :
    2 * M * (N + M ^ 2) * na + 4 * M * N * nb = ((N : ℤ) + M ^ 2) ^ 2 := by
  have h1 : (1 + s) * ((((2 * M * (N + M ^ 2) * na + 4 * M * N * nb - (N + M ^ 2) ^ 2 : ℤ)) : ℝ) * s
      + (((4 * M * (N - M ^ 2) * nb + 2 * M * (N + M ^ 2) * nc - (N - M ^ 2) * (N + M ^ 2) : ℤ))
        : ℝ)) = 0 := by
    push_cast
    linear_combination (2 * (M : ℝ) * ((N : ℝ) + (M : ℝ) ^ 2)) * hw
      + (-(M : ℝ) ^ 2 + 2 * M * nb * s + 2 * M * nb - N) * hq
  have hE := (mul_eq_zero.mp h1).resolve_left (by linarith)
  obtain ⟨hB, -⟩ := irr_coord_eq_zero hs hE
  linear_combination hB

/-- **The base's s-coordinate** (file §4(a)): if `s ∉ ℚ` satisfies the tiling quadratic and the base
word `(1+s)(m_a s + m_b(1−s²) + m_c) = M s(3−s²)` holds, then
`M(N+M²)m_a + 2MN·m_b = N(M²−N)` (the file's `Mq(1−q)/(q+1)`, cleared). -/
theorem Row12.base_coeff {s : ℝ} (hs : ¬ ∃ r : ℚ, s = r) (hs0 : 0 < s) {M : ℤ} {N : ℕ}
    (hq : ((N : ℝ) + (M : ℝ) ^ 2) * s ^ 2 + 2 * N * s + (N - 3 * (M : ℝ) ^ 2) = 0)
    {ma mb mc : ℕ} (hw : (1 + s) * (ma * s + mb * (1 - s ^ 2) + mc) = M * s * (3 - s ^ 2)) :
    M * (N + M ^ 2) * ma + 2 * M * N * mb = (N : ℤ) * (M ^ 2 - N) := by
  have h1 : (1 + s) * ((((M * (N + M ^ 2) * ma + 2 * M * N * mb - N * (M ^ 2 - N) : ℤ)) : ℝ) * s
      + (((2 * M * (N - M ^ 2) * mb + M * (N + M ^ 2) * mc - N * (3 * M ^ 2 - N) : ℤ)) : ℝ))
      = 0 := by
    push_cast
    linear_combination ((M : ℝ) * ((N : ℝ) + (M : ℝ) ^ 2)) * hw
      + (-(M : ℝ) ^ 2 * s + M * mb * s + M * mb + N) * hq
  have hE := (mul_eq_zero.mp h1).resolve_left (by linarith)
  obtain ⟨hB, -⟩ := irr_coord_eq_zero hs hE
  linear_combination hB

/-! ## The words, read in `s` -/

/-- The leg and base words of a base-β tiling, divided by `c` and read in `s`. -/
theorem Row12.words (D : CongruentDissection N) {α β a b c : ℝ}
    (h : D.model.ThreeAlphaData α β a b c) {s : ℝ} {M : ℤ} (hc : 0 < c) (ha : a = s * c)
    (hb : b = (1 - s ^ 2) * c) (hleg : (M : ℝ) * c = D.target.oppLen 0 * (1 + s))
    (hY : D.target.oppLen 2 = s * (3 - s ^ 2) * D.target.oppLen 0) :
    (∃ na nb nc : ℕ, (1 + s) * (na * s + nb * (1 - s ^ 2) + nc) = M) ∧
    (∃ ma mb mc : ℕ, (1 + s) * (ma * s + mb * (1 - s ^ 2) + mc) = M * s * (3 - s ^ 2)) := by
  obtain ⟨na, nb, nc, hwl⟩ := D.side_word_threeAlpha h 0
  obtain ⟨ma, mb, mc, hwb⟩ := D.side_word_threeAlpha h 2
  rw [ha, hb] at hwl hwb
  constructor
  · refine ⟨na, nb, nc, mul_left_cancel₀ hc.ne' ?_⟩
    linear_combination (-(1 + s)) * hwl - hleg
  · refine ⟨ma, mb, mc, mul_left_cancel₀ hc.ne' ?_⟩
    linear_combination (-(1 + s)) * hwb + (1 + s) * hY - s * (3 - s ^ 2) * hleg

/-! ## Row 12(a) (strict) and Row 12(b) -/

/-- **Row 12(a), strict form** (file §4(a), `q > 1`): Theorem 1's colouring number `M` exists, and
if `M² < N` the tile is rational.  (`q = 1`, the golden case (a′), is not formalized.) -/
theorem Row12.case_a (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hP0 : D.target.angleAt 0 = β) (hP1 : D.target.angleAt 1 = β) :
    ∃ M : ℤ, 0 < M ∧ (M : ℝ) * (a + b + c) = D.target.oppLen 2 + 2 * D.target.oppLen 0 ∧
      (M ^ 2 < N → ∃ r : ℚ, a = (r : ℝ) * c) := by
  obtain ⟨s, M, hs0, hs1, hc, ha, hb, -, -, hM0, hMid, hleg, hY, hq⟩ :=
    Row12.setup D hα hrel h hP0 hP1
  refine ⟨M, hM0, hMid, fun hlt => ?_⟩
  by_contra hrat
  have hirr : ¬ ∃ r : ℚ, s = r := fun ⟨r, hr⟩ => hrat ⟨r, by rw [ha, hr]⟩
  obtain ⟨-, ma, mb, mc, hw2⟩ := Row12.words D h hc ha hb hleg hY
  have hB := Row12.base_coeff hirr hs0 hq hw2
  have h1 : 0 ≤ M * (N + M ^ 2) * ma :=
    mul_nonneg (mul_nonneg hM0.le (by positivity)) (Nat.cast_nonneg ma)
  have h2 : 0 ≤ 2 * M * N * mb :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM0.le) (Nat.cast_nonneg N)) (Nat.cast_nonneg mb)
  have h3 : (N : ℤ) * (M ^ 2 - N) < 0 := by
    have hN0 : (0 : ℤ) < N := lt_of_le_of_lt (sq_nonneg M) hlt
    exact mul_neg_of_pos_of_neg hN0 (by linarith)
  linarith

/-- **ROW 12(b)** (rationality_proofs.md §4(b), PROVED after two reviews): an `N`-tiling, `N` prime,
of the base-β target `(β, β, 3α)` by the `3α + 2β = π` tile with `α ∉ ℚπ` (reflections allowed,
not necessarily edge-to-edge) has a rational tile: `a/c ∈ ℚ`. -/
theorem Row12.prime_rational (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hP0 : D.target.angleAt 0 = β) (hP1 : D.target.angleAt 1 = β) (hN : N.Prime) :
    ∃ r : ℚ, a = (r : ℝ) * c := by
  obtain ⟨s, M, hs0, hs1, hc, ha, hb, -, hMN, hM0, -, hleg, hY, hq⟩ :=
    Row12.setup D hα hrel h hP0 hP1
  by_contra hrat
  have hirr : ¬ ∃ r : ℚ, s = r := fun ⟨r, hr⟩ => hrat ⟨r, by rw [ha, hr]⟩
  obtain ⟨⟨na, nb, nc, hw1⟩, ⟨ma, mb, mc, hw2⟩⟩ := Row12.words D h hc ha hb hleg hY
  have hL := Row12.leg_coeff hirr hs0 hq hw1
  have hB := Row12.base_coeff hirr hs0 hq hw2
  -- step 1: `M ∣ N²`
  have hdvd : M ∣ (N : ℤ) ^ 2 :=
    ⟨2 * (N + M ^ 2) * na + 4 * N * nb - 2 * N * M - M ^ 3, by linear_combination (-1 : ℤ) * hL⟩
  have hN2 : 2 ≤ N := hN.two_le
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hM0.le
  have hmN : m ≤ N := by
    rw [abs_of_nonneg (by positivity)] at hMN; exact_mod_cast hMN
  have hmdvd : m ∣ N ^ 2 := by exact_mod_cast hdvd
  -- step 3: `N` prime, so `m ∈ {1, N, N²}`
  obtain ⟨i, hi, hmi⟩ := (Nat.dvd_prime_pow hN).mp hmdvd
  interval_cases i
  · -- `M = 1`: the base's s-coordinate is `N(1 − N) < 0`
    rw [pow_zero] at hmi
    rw [hmi] at hB
    push_cast at hB
    have hN2z : (2 : ℤ) ≤ N := by exact_mod_cast hN2
    have h1 : (0 : ℤ) ≤ (N + 1) * ma := by positivity
    have h2 : (0 : ℤ) ≤ 2 * N * mb := by positivity
    have h4 : (2 : ℤ) * N ≤ N * N := mul_le_mul_of_nonneg_right hN2z (by positivity)
    have h5 : (N : ℤ) * (1 - N) = N - N * N := by ring
    linarith
  · -- `M = N`: `q = 1/N ≤ 1/2`, but `q = (3−s²)/(1+s)² > 1/2` on `(0, 1)`
    rw [pow_one] at hmi
    rw [hmi] at hq
    push_cast at hq
    have hN0 : (0 : ℝ) < N := by linarith
    have e : (N : ℝ) * ((1 + (N : ℝ)) * s ^ 2 + 2 * s + (1 - 3 * N)) = 0 := by
      linear_combination hq
    have e2 := (mul_eq_zero.mp e).resolve_left hN0.ne'
    have hs2lt : s ^ 2 < 1 := by
      have h' : s * s < s * 1 := mul_lt_mul_of_pos_left hs1 hs0
      have : s ^ 2 = s * s := sq s
      linarith
    have h3 : 0 ≤ ((N : ℝ) - 2) * (3 - s ^ 2) := mul_nonneg (by linarith) (by linarith)
    have e3 : 3 * s ^ 2 + 2 * s - 5 = ((N : ℝ) - 2) * (3 - s ^ 2) := by linear_combination e2
    linarith
  · -- `M = N² > N`
    rw [hmi, sq] at hmN
    have : N * 2 ≤ N * N := Nat.mul_le_mul_left N hN2
    linarith

end Erdos634.Geometry

#print axioms Erdos634.Geometry.irr_coord_eq_zero
#print axioms Erdos634.Geometry.Tri.four_detTri_sq_symm
#print axioms Erdos634.Geometry.Row12.sides
#print axioms Erdos634.Geometry.Row12.setup
#print axioms Erdos634.Geometry.Row12.leg_coeff
#print axioms Erdos634.Geometry.Row12.base_coeff
#print axioms Erdos634.Geometry.Row12.words
#print axioms Erdos634.Geometry.Row12.case_a
#print axioms Erdos634.Geometry.Row12.prime_rational
