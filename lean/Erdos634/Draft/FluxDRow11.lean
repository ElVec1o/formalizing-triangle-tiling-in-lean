-- Draft/FluxDRow11.lean — ROW 11, THEOREM R11 ((private working notes, not included)
-- §§3.2–3.4, P2): on the base-α target `(α, α, α + 2β)`, an `N`-tiling (any `N`) by the
-- `3α + 2β = π` tile with `α ∉ ℚπ` (reflections allowed, not necessarily edge-to-edge) has a
-- rational tile, `a/c ∈ ℚ`.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- * `Row11.boundary_baseAlpha` = L2 + L3 (boundary values anchored at the base, through
--   `CongruentDissection.triangle_boundary_anchor`, FluxCBoundary): both characters see every side
--   with sign `+`, so `K(c+b−a) = Y + X₀ + X₁ = M(a+b+c)`, `K ≡ M ≡ N (2)`, `|K|, |M| ≤ N`.
-- * `Row11.sides` = S for this target: `X₁ = X₀`, `Y = (2 − s²)X`, `a = sc`, `b = (1−s²)c`.
-- * `Row11.L4` (pure algebra, the file's exact hypotheses): `K > M` and `s² + λs − 2 = 0`,
--   `λ = (K+M)/(K−M) ∈ ℚ`, `λ > 1`.
-- * `Row11.L5a` (pure algebra): `s ∉ ℚ` + a leg word `n_a s + n_b(1−s²) + n_c = M(1+s)/(2+s)` ⇒ ⊥.
--   The file's `y₀ = M/(2(1−λ)) < 0` is carried in cleared integer form:
--   `M(4((K−M)n_a + (K+M)n_b) + (K−M)²) = 0`, impossible for `M, K − M > 0`.
-- * `Row11.rational` = Theorem R11, from the above and W (Draft/FluxDSideWord).
-- L5b (closing by area) is NOT formalized (not needed: L5a closes alone, file §3.5 "either W or area").
--
-- CONDITIONAL AT THE GEOMETRIC LEVEL: the base-α target has NO known real tiling (Beeson's searches
-- found none; the corpus has none; ROW11_RATIONALITY.md §5), so `boundary_baseAlpha`, `setup` and
-- `rational` have no witness of their full hypothesis set.  Each ALGEBRAIC hypothesis of L4/L5a is
-- witnessed separately (Draft/FluxDRow11Witness.lean): the rational branch `s = 1/2, M = 5, K = 9`,
-- the `(M, K) = (1, 5)`, `s = (−3+√41)/4` model (irrational, passes L3/L4, fails W), and the
-- `N = 896`, `M = 40`, `s = (−8+√86)/11` model (irrational, leg word `44a + 16c`, fails χ₊).
--
-- At prime N this is a SECOND route (R15 already excludes base-α prime tilings on paper; errata 1);
-- its content is rationality for composite N.  Formalization debt; not progress on the three /goal
-- outcomes.
import Erdos634.Draft.FluxDRow12b

open scoped Classical

namespace Erdos634.Geometry

variable {N : ℕ}

/-! ## L2 + L3: the boundary values on the base-α target -/

/-- **L2 + L3 (`Row11.boundary_baseAlpha`).**  For an `N`-tiling of a base-α isosceles target
(angles `α, α, α + 2β` at vertices `0, 1, 2`; base = side `01` = `oppLen 2`) by a `3α + 2β = π` tile
with `α ∉ ℚπ`: integers `K, M ≡ N (mod 2)`, `|K|, |M| ≤ N`, with
`K(c+b−a) = Y + X₀ + X₁ = M(a+b+c)`. -/
theorem Row11.boundary_baseAlpha (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hP0 : D.target.angleAt 0 = α) (hP1 : D.target.angleAt 1 = α)
    (hP2 : D.target.angleAt 2 = α + 2 * β) :
    ∃ K M : ℤ, (2 : ℤ) ∣ K - N ∧ (2 : ℤ) ∣ M - N ∧ |K| ≤ N ∧ |M| ≤ N ∧
      (K : ℝ) * (c + b - a) = D.target.oppLen 2 + D.target.oppLen 0 + D.target.oppLen 1 ∧
      (M : ℝ) * (a + b + c) = D.target.oppLen 2 + D.target.oppLen 0 + D.target.oppLen 1 := by
  set anc := (D.target.leftUnit 0).angle with hancdef
  have eα : ((α : ℝ) : Real.Angle)
      = ((((-1 : ℤ) : ℝ) * Real.pi + ((2 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) : ℝ) : Real.Angle) := by
    congr 1; push_cast; ring
  have eA : ((α + 2 * β : ℝ) : Real.Angle)
      = ((((3 : ℤ) : ℝ) * Real.pi + ((-4 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) : ℝ) : Real.Angle) := by
    congr 1; push_cast; linarith
  have htarget : ∀ b' : ZMod 2, ∀ k,
      ((D.target.angleAt k : ℝ) : Real.Angle) ∈ (chiAt α hα b' anc).L := by
    intro b' k
    fin_cases k
    · show ((D.target.angleAt 0 : ℝ) : Real.Angle) ∈ _
      rw [hP0, eα]; exact chiAt_mem _ _ _ _ _ _
    · show ((D.target.angleAt 1 : ℝ) : Real.Angle) ∈ _
      rw [hP1, eα]; exact chiAt_mem _ _ _ _ _ _
    · show ((D.target.angleAt 2 : ℝ) : Real.Angle) ∈ _
      rw [hP2, eA]; exact chiAt_mem _ _ _ _ _ _
  have hmodel : ∀ b' : ZMod 2, ∀ k,
      ((D.model.angleAt k : ℝ) : Real.Angle) ∈ (chiAt α hα b' anc).L :=
    fun b' => D.model.threeAlpha_angles_mem hα hrel h b'
  -- both corner classes have `χ₊ = χ₋ = −1`
  have hc1 : ∀ b' : ZMod 2, (chiAt α hα b' anc).chi ((α : ℝ) : Real.Angle) = -1 := by
    intro b'
    rw [eα, chiAt_chi, if_neg]
    have h1 : ((-1 : ℤ) : ZMod 2) = 1 := by decide
    have h2 : ((2 : ℤ) : ZMod 2) = 0 := by decide
    rw [h1, h2, mul_zero, add_zero]
    decide
  have hc2 : ∀ b' : ZMod 2, (chiAt α hα b' anc).chi ((α + 2 * β : ℝ) : Real.Angle) = -1 := by
    intro b'
    rw [eA, chiAt_chi, if_neg]
    have h1 : ((3 : ℤ) : ZMod 2) = 1 := by decide
    have h2 : ((-4 : ℤ) : ZMod 2) = 0 := by decide
    rw [h1, h2, mul_zero, add_zero]
    decide
  have hPK : ∀ b' : ZMod 2, (chiAt α hα b' anc).paperK D.target
      = D.target.oppLen 2 + D.target.oppLen 0 + D.target.oppLen 1 := by
    intro b'
    unfold GridChar.paperK
    rw [Fin.sum_univ_three, hP0, hP1, hP2, hc1, hc2]
    ring
  have hchi2 : ∀ b' : ZMod 2,
      (chiAt α hα b' anc).chi ((D.target.angleAt (0 + 2) : ℝ) : Real.Angle) = -1 := by
    intro b'
    rw [show (0 : Fin 3) + 2 = 2 from rfl, hP2, hc2]
  have hMp : (chiAt α hα 0 anc).paperK D.model = -(c + b - a) := by
    rw [← GridChar.tileValue_eq_paperK _ (chiAt_sq _ _ _ _) _ (hmodel 0), chiAt_tileValue]
    exact threeAlpha_tileValue_plus D.model hα hrel h
  have hMm : (chiAt α hα 1 anc).paperK D.model = a + b + c := by
    rw [← GridChar.tileValue_eq_paperK _ (chiAt_sq _ _ _ _) _ (hmodel 1), chiAt_tileValue]
    exact threeAlpha_tileValue_minus D.model hα hrel h
  obtain ⟨S, hS2, hSN, hSe⟩ := D.triangle_boundary_anchor (chiAt α hα 0 anc) (chiAt_sq _ _ _ _)
    (hmodel 0) (htarget 0) 0 rfl
  obtain ⟨S', hS2', hSN', hSe'⟩ := D.triangle_boundary_anchor (chiAt α hα 1 anc)
    (chiAt_sq _ _ _ _) (hmodel 1) (htarget 1) 0 rfl
  rw [hMp, hchi2, hPK] at hSe
  rw [hMm, hchi2, hPK] at hSe'
  refine ⟨-S, S', ?_, hS2', ?_, hSN', ?_, ?_⟩
  · rw [show -S - (N : ℤ) = -(S - N) - 2 * N by ring]
    exact dvd_sub (dvd_neg.mpr hS2) (dvd_mul_right 2 _)
  · rw [abs_neg]; exact hSN
  · push_cast; linear_combination hSe
  · linear_combination hSe'

/-! ## S for the base-α target -/

/-- **S (law of sines) for the base-α target**: `X₁ = X₀`, `Y = (2 − s²) X₀`, `a = s c`,
`b = (1 − s²) c`, `s = 2 sin(α/2) ∈ (0, 1)`.  (The model half re-derives lines of `Row12.ratio`.) -/
theorem Row11.sides (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi) (h : D.model.ThreeAlphaData α β a b c)
    (hP0 : D.target.angleAt 0 = α) (hP1 : D.target.angleAt 1 = α)
    (hP2 : D.target.angleAt 2 = α + 2 * β) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ 0 < c ∧ 0 < D.target.oppLen 0 ∧
      a = s * c ∧ b = (1 - s ^ 2) * c ∧
      D.target.oppLen 2 = (2 - s ^ 2) * D.target.oppLen 0 ∧
      D.target.oppLen 1 = D.target.oppLen 0 := by
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  obtain ⟨tγ, tα, tβ, -⟩ := threeAlpha_sin_table hrel
  have ls1 := D.model.lawSin (σ 0) (σ 2)
  have ls2 := D.model.lawSin (σ 1) (σ 2)
  rw [h0, o2, h2, o0, tα, tγ] at ls1
  rw [h1, o2, h2, o1, tβ, tγ] at ls2
  have hαpos : 0 < α := h0 ▸ D.model.angleAt_pos' (σ 0)
  have hβpos : 0 < β := h1 ▸ D.model.angleAt_pos' (σ 1)
  have hπ := Real.pi_pos
  have hA2 : Real.sin (α + 2 * β) = 2 * Real.sin α * Real.cos α := by
    rw [show α + 2 * β = Real.pi - 2 * α by linarith, Real.sin_pi_sub, Real.sin_two_mul]
  have lt0 := D.target.lawSin 0 2
  have lt1 := D.target.lawSin 1 2
  rw [hP0, hP2, hA2] at lt0
  rw [hP1, hP2, hA2] at lt1
  have hco : 0 < Real.cos (α / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs0 : 0 < Real.sin (α / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hs1 : Real.sin (α / 2) < 1 / 2 := by
    rw [← Real.sin_pi_div_six]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  have hsα : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hαpos (by linarith)
  have hcα : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcos : Real.cos α = 1 - 2 * Real.sin (α / 2) ^ 2 := by
    have e := Real.cos_two_mul (α / 2)
    rw [show 2 * (α / 2) = α by ring] at e
    have p := Real.sin_sq_add_cos_sq (α / 2)
    linear_combination e + 2 * p
  have hc : 0 < c := o2 ▸ D.model.oppLen_pos (σ 2)
  have hX : 0 < D.target.oppLen 0 := D.target.oppLen_pos 0
  set u := Real.sin (α / 2) with hudef
  set co := Real.cos (α / 2) with hcodef
  set X := D.target.oppLen 0 with hXdef
  set X₁ := D.target.oppLen 1 with hX1def
  set Y := D.target.oppLen 2 with hYdef
  have ha : a = 2 * u * c :=
    mul_left_cancel₀ hco.ne' (by linear_combination (-1 : ℝ) * ls1)
  have hb : b = (1 - 4 * u ^ 2) * c :=
    mul_left_cancel₀ hco.ne' (by linear_combination (-1 : ℝ) * ls2)
  have hY : Y = 2 * Real.cos α * X := mul_left_cancel₀ hsα.ne' (by linear_combination lt0)
  have hY1 : Y = 2 * Real.cos α * X₁ := mul_left_cancel₀ hsα.ne' (by linear_combination lt1)
  have hX1 : X₁ = X :=
    mul_left_cancel₀ (mul_pos two_pos hcα).ne' (by linear_combination hY - hY1)
  refine ⟨2 * u, by linarith, by linarith, hc, hX, ?_, ?_, ?_, hX1⟩
  · rw [ha]
  · rw [hb]; ring
  · rw [hY, hcos]; ring

/-! ## L4 and L5a (pure algebra) -/

/-- **L4** (file P2, exact hypotheses): for `0 < s < 1` and integers `K, M ≥ 1` with
`K(1−s)(2+s) = M(1+s)(2−s)`: `K > M`, and `s² + λs − 2 = 0` with `λ = (K+M)/(K−M) ∈ ℚ`, `λ > 1`. -/
theorem Row11.L4 {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {K M : ℤ} (hM : 1 ≤ M) (_hK : 1 ≤ K)
    (h : (K : ℝ) * (1 - s) * (2 + s) = M * (1 + s) * (2 - s)) :
    M < K ∧ s ^ 2 + ((((K + M : ℤ) : ℚ) / ((K - M : ℤ) : ℚ) : ℚ) : ℝ) * s - 2 = 0 ∧
      (1 : ℚ) < ((K + M : ℤ) : ℚ) / ((K - M : ℤ) : ℚ) := by
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have e : ((K : ℝ) - M) * ((1 - s) * (2 + s)) = 2 * s * M := by linear_combination h
  have hKM : M < K := by
    have hpos : 0 < (1 - s) * (2 + s) := mul_pos (by linarith) (by linarith)
    have : (0 : ℝ) < (K : ℝ) - M := by
      by_contra hn; push Not at hn
      have := mul_nonpos_of_nonpos_of_nonneg hn hpos.le
      have := mul_pos hs0 (by linarith : (0 : ℝ) < M)
      linarith
    exact_mod_cast (by linarith : (M : ℝ) < K)
  have hD : (0 : ℝ) < (K : ℝ) - M := by
    have : (M : ℝ) < K := by exact_mod_cast hKM
    linarith
  have hD' : (K : ℝ) - M ≠ 0 := hD.ne'
  refine ⟨hKM, ?_, ?_⟩
  · have hlam : ((K : ℝ) + M) / ((K : ℝ) - M) * ((K : ℝ) - M) = (K : ℝ) + M :=
      div_mul_cancel₀ _ hD'
    have e2 : ((K : ℝ) - M) * (s ^ 2 + ((K : ℝ) + M) / ((K : ℝ) - M) * s - 2) = 0 := by
      linear_combination (-1 : ℝ) * h + s * hlam
    have e3 := (mul_eq_zero.mp e2).resolve_left hD'
    push_cast
    linear_combination e3
  · have hDq : (0 : ℚ) < ((K - M : ℤ) : ℚ) := by exact_mod_cast (show (0 : ℤ) < K - M by omega)
    rw [lt_div_iff₀ hDq]
    push_cast
    have : (0 : ℚ) < M := by exact_mod_cast (show (0 : ℤ) < M by omega)
    linarith

/-- **L5a** (file P2 / §3.4): `s ∉ ℚ`, `0 < s < 1`, integers `K`, `M ≥ 1` with
`K(1−s)(2+s) = M(1+s)(2−s)`, and a leg word `(n_a s + n_b(1−s²) + n_c)(2+s) = M(1+s)` with
`n_• ∈ ℕ`: impossible.  (The leg's s-coordinate `y₀ = M/(2(1−λ)) < 0` against `n_a + λn_b ≥ 0`, in
cleared form `M(4((K−M)n_a + (K+M)n_b) + (K−M)²) = 0`.) -/
theorem Row11.L5a {s : ℝ} (hs : ¬ ∃ r : ℚ, s = r) (hs0 : 0 < s) (hs1 : s < 1) {K M : ℤ}
    (hM : 1 ≤ M) (hKM : (K : ℝ) * (1 - s) * (2 + s) = M * (1 + s) * (2 - s))
    {na nb nc : ℕ} (hw : (na * s + nb * (1 - s ^ 2) + nc) * (2 + s) = M * (1 + s)) : False := by
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  -- `K > M ≥ 1`
  have e : ((K : ℝ) - M) * ((1 - s) * (2 + s)) = 2 * s * M := by linear_combination hKM
  have hpos : 0 < (1 - s) * (2 + s) := mul_pos (by linarith) (by linarith)
  have hD : (0 : ℝ) < (K : ℝ) - M := by
    by_contra hn; push Not at hn
    have := mul_nonpos_of_nonpos_of_nonneg hn hpos.le
    have := mul_pos hs0 (by linarith : (0 : ℝ) < M)
    linarith
  have hDz : (0 : ℤ) < K - M := by
    have : M < K := by exact_mod_cast (by linarith : (M : ℝ) < K)
    omega
  -- the quadratic `(K−M)s² + (K+M)s − 2(K−M) = 0`
  have hq : ((K : ℝ) - M) * s ^ 2 + ((K : ℝ) + M) * s - 2 * ((K : ℝ) - M) = 0 := by
    linear_combination (-1 : ℝ) * hKM
  -- coordinates of `(K−M)²·((2+s)w − M(1+s))` in `{1, s}`
  have h1 : (((-K ^ 2 * M + K ^ 2 * na + K ^ 2 * nc + 2 * K * M ^ 2 - 4 * K * M * na
      - 2 * K * M * nc - M ^ 3 + 3 * M ^ 2 * na - 4 * M ^ 2 * nb + M ^ 2 * nc : ℤ)) : ℝ) * s
      + (((-(K - M) * (K * M - 2 * K * na - 2 * K * nc - M ^ 2 + 2 * M * na - 4 * M * nb
        + 2 * M * nc) : ℤ)) : ℝ) = 0 := by
    push_cast
    linear_combination (((K : ℝ) - M) ^ 2) * hw
      - ((K : ℝ) * na - K * nb * s - K * nb - M * na + M * nb * s + 3 * M * nb) * hq
  obtain ⟨hp1, hp0⟩ := irr_coord_eq_zero hs h1
  have key : M * (4 * ((K - M) * na + (K + M) * nb) + (K - M) ^ 2) = 0 := by
    linear_combination hp0 - 2 * hp1
  have hpos' : 0 < M * (4 * ((K - M) * na + (K + M) * nb) + (K - M) ^ 2) := by
    have h3 : 0 ≤ (K - M) * (na : ℤ) := mul_nonneg hDz.le (Nat.cast_nonneg _)
    have h4 : 0 ≤ (K + M) * (nb : ℤ) := mul_nonneg (by linarith) (Nat.cast_nonneg _)
    have h5 : 0 < (K - M) ^ 2 := pow_pos hDz 2
    exact mul_pos (by linarith) (by linarith)
  linarith

/-! ## Theorem R11 -/

/-- **Row 11's tiling data** (L3 + S): `K ≡ M ≡ N (2)`, `|K|, |M| ≤ N`, `1 ≤ M < K`,
`K(1−s)(2+s) = M(1+s)(2−s)`, and the leg `X(2+s) = M c (1+s)`. -/
theorem Row11.setup (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hP0 : D.target.angleAt 0 = α) (hP1 : D.target.angleAt 1 = α) :
    ∃ (s : ℝ) (K M : ℤ), 0 < s ∧ s < 1 ∧ 0 < c ∧ a = s * c ∧ b = (1 - s ^ 2) * c ∧
      (2 : ℤ) ∣ K - N ∧ (2 : ℤ) ∣ M - N ∧ |K| ≤ N ∧ |M| ≤ N ∧ 1 ≤ M ∧ 1 ≤ K ∧
      (K : ℝ) * (1 - s) * (2 + s) = M * (1 + s) * (2 - s) ∧
      D.target.oppLen 0 * (2 + s) = M * c * (1 + s) ∧
      D.target.oppLen 2 = (2 - s ^ 2) * D.target.oppLen 0 := by
  have hP2 : D.target.angleAt 2 = α + 2 * β := by
    have := D.target.angleAt_sum; rw [hP0, hP1] at this; linarith
  obtain ⟨K, M, hK2, hM2, hKN, hMN, hK, hM⟩ := Row11.boundary_baseAlpha D hα hrel h hP0 hP1 hP2
  obtain ⟨s, hs0, hs1, hc, hX, ha, hb, hY, hX1⟩ := Row11.sides D hrel h hP0 hP1 hP2
  rw [hX1, hY] at hK hM
  set X := D.target.oppLen 0 with hXdef
  subst ha hb
  have hleg : X * (2 + s) = M * c * (1 + s) := by
    have e : (2 - s) * (X * (2 + s) - M * c * (1 + s)) = 0 := by linear_combination -hM
    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left (by linarith))
  have hKMe : (K : ℝ) * (1 - s) * (2 + s) = M * (1 + s) * (2 - s) := by
    have e : c * ((K : ℝ) * (1 - s) * (2 + s) - M * (1 + s) * (2 - s)) = 0 := by
      linear_combination hK - hM
    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left hc.ne')
  have hMpos : (0 : ℝ) < M := by
    have h1 : 0 < M * c * (1 + s) := by rw [← hleg]; exact mul_pos hX (by linarith)
    by_contra hn; push Not at hn
    have : (M : ℝ) * c * (1 + s) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hn hc.le) (by linarith)
    linarith
  have hKpos : (0 : ℝ) < K := by
    have h1 : 0 < (M : ℝ) * (1 + s) * (2 - s) := mul_pos (mul_pos hMpos (by linarith)) (by linarith)
    rw [← hKMe] at h1
    by_contra hn; push Not at hn
    have : (K : ℝ) * (1 - s) * (2 + s) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hn (by linarith)) (by linarith)
    linarith
  refine ⟨s, K, M, hs0, hs1, hc, rfl, rfl, hK2, hM2, hKN, hMN, ?_, ?_, hKMe, hleg, hY⟩
  · have : (0 : ℤ) < M := by exact_mod_cast hMpos
    omega
  · have : (0 : ℤ) < K := by exact_mod_cast hKpos
    omega

/-- **THEOREM R11** (ROW11_RATIONALITY.md §1/P2, PROVED after two reviews): an `N`-tiling (any `N`)
of the base-α target `(α, α, α + 2β)` by the `3α + 2β = π` tile with `α ∉ ℚπ` has `a/c ∈ ℚ`.
CONDITIONAL: no real tiling of this target is known. -/
theorem Row11.rational (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hP0 : D.target.angleAt 0 = α) (hP1 : D.target.angleAt 1 = α) :
    ∃ r : ℚ, a = (r : ℝ) * c := by
  obtain ⟨s, K, M, hs0, hs1, hc, ha, hb, -, -, -, -, hM1, -, hKM, hleg, -⟩ :=
    Row11.setup D hα hrel h hP0 hP1
  by_contra hrat
  have hirr : ¬ ∃ r : ℚ, s = r := fun ⟨r, hr⟩ => hrat ⟨r, by rw [ha, hr]⟩
  obtain ⟨na, nb, nc, hw⟩ := D.side_word_threeAlpha h 0
  rw [ha, hb] at hw
  have hw' : (na * s + nb * (1 - s ^ 2) + nc) * (2 + s) = M * (1 + s) := by
    refine mul_left_cancel₀ hc.ne' ?_
    linear_combination (-(2 + s)) * hw + hleg
  exact Row11.L5a hirr hs0 hs1 hM1 hKM hw'

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row11.boundary_baseAlpha
#print axioms Erdos634.Geometry.Row11.sides
#print axioms Erdos634.Geometry.Row11.L4
#print axioms Erdos634.Geometry.Row11.L5a
#print axioms Erdos634.Geometry.Row11.setup
#print axioms Erdos634.Geometry.Row11.rational
