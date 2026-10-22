-- Draft/FluxCRow12.lean — consumer layer, item 3: ROW 12(b) / THEOREM R12
-- ((private working notes, not included) "Theorem R12", statement repaired by
-- erratum 4: K, M defined with the BASE as anchor).  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- Setting (B): tile `T` with angles `α, β, γ = 2α + β`, `3α + 2β = π`, `α ∉ ℚπ`, sides `a, b, c`
-- opposite them; target `ABC` isosceles with base angles `β` (angles `β, β, 3α`; base `Y` opposite
-- the apex, legs `X`), `N` congruent copies, reflections allowed, NOT necessarily edge-to-edge.
-- * `Row12.flux_identities` (= L2β + L3β): from the boundary lemma (FluxCBoundary) with the
--   characters `χ₊ = (−1)^j`, `χ₋ = (−1)^(j+k)` on `jπ + kθ`, anchored at the base:
--   `K(c+b−a) = Y − X₀ − X₁`, `M(a+b+c) = Y + X₀ + X₁`, `K ≡ M ≡ N (mod 2)`, `|K|, |M| ≤ N`.
-- * `threeAlpha_sin_table` (item 8, "S"): `sin γ = cos(α/2)`, `sin α = 2 sin(α/2) cos(α/2)`,
--   `sin β = cos(α/2)(1 − 4 sin²(α/2))`, `sin 3α = 2 sin(α/2)(3 − 4 sin²(α/2))·sin β`.
-- * `Row12.ratio` (= R12): `a/c = (M+K)/(M−K)`, `K < 0 < M`; `Row12.rational`: `a/c ∈ ℚ`;
--   `Row12.rational_paper`: the target-theorem statement of ROW11_RATIONALITY.md item 9.
--
-- Formalization debt on the prime-case VERIFIED path; not progress on the three /goal outcomes.
-- R12 at prime N is a reproduction of row 12(b) (ROW11_RATIONALITY.md P0 row 3); its content is
-- rationality of the tile for composite N.  The sign/anchor facts are erratum 4's.
--
-- Reuse (cited): `CongruentDissection.triangle_boundary_anchor`, `GridChar.tileValue_eq_paperK`
-- (FluxCBoundary); `theta_irr_of_alpha`, `Tri.ThreeAlphaData`, `Tri.threeAlpha_angles_mem`,
-- `threeAlpha_tileValue_plus/minus` (FluxRow11); `GridChar.rank2_mem/chi/sq` (FluxGrids);
-- `TriLawSin.sin_angleAt_mul_sideOpp` (law of sines); `MarchFlank.cornerAngle_pos`; Mathlib
-- `Real.sin_three_mul`, `Real.cos_three_mul`, `Real.sin_two_mul`.
import Erdos634.Draft.FluxCBoundary
import Erdos634.Draft.FluxRow11
import Erdos634.TriLawSin
import Erdos634.MarchFlank

open scoped Classical

namespace Erdos634.Geometry

variable {N : ℕ}

/-! ## Law of sines, every index pair; positivity -/

/-- The law of sines for any two vertices of a `Tri` (from `TriLawSin.sin_angleAt_mul_sideOpp`,
whose `angleAt`/`sideOpp` are definitionally `Tri.angleAt`/`Tri.oppLen`). -/
theorem Tri.lawSin (T : Tri) (i j : Fin 3) :
    Real.sin (T.angleAt i) * T.oppLen j = Real.sin (T.angleAt j) * T.oppLen i := by
  have h0 : Real.sin (T.angleAt 1) * T.oppLen 0 = Real.sin (T.angleAt 0) * T.oppLen 1 :=
    Erdos634.TriLawSin.sin_angleAt_mul_sideOpp T 0
  have h1 : Real.sin (T.angleAt 2) * T.oppLen 1 = Real.sin (T.angleAt 1) * T.oppLen 2 :=
    Erdos634.TriLawSin.sin_angleAt_mul_sideOpp T 1
  have h2 : Real.sin (T.angleAt 0) * T.oppLen 2 = Real.sin (T.angleAt 2) * T.oppLen 0 :=
    Erdos634.TriLawSin.sin_angleAt_mul_sideOpp T 2
  fin_cases i <;> fin_cases j
  · rfl
  · exact h0.symm
  · exact h2
  · exact h0
  · rfl
  · exact h1.symm
  · exact h2.symm
  · exact h1
  · rfl

theorem Tri.angleAt_pos' (T : Tri) (j : Fin 3) : 0 < T.angleAt j :=
  Erdos634.MarchFlank.cornerAngle_pos T j

theorem Tri.oppLen_pos (T : Tri) (k : Fin 3) : 0 < T.oppLen k := by
  unfold Tri.oppLen
  have hne : k + 1 ≠ k + 2 := by fin_cases k <;> decide
  exact dist_pos.mpr fun h => hne (T.indep.injective h)

/-! ## The trigonometric table `S` -/

/-- **The sine table of the `3α + 2β = π` tile** (ROW11_RATIONALITY.md item 8, "S"), in
`u = α/2`: `sin γ = cos u`, `sin α = 2 sin u cos u`, `sin β = cos u (1 − 4 sin² u)`,
`sin 3α = 2 sin u (3 − 4 sin² u) · cos u (1 − 4 sin² u)`.  With `s = 2 sin u` these are
`a/c = s`, `b/c = 1 − s²`, `sin 3α / sin γ = s(3 − s²)(1 − s²)`. -/
theorem threeAlpha_sin_table {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi) :
    Real.sin (2 * α + β) = Real.cos (α / 2)
    ∧ Real.sin α = 2 * Real.sin (α / 2) * Real.cos (α / 2)
    ∧ Real.sin β = Real.cos (α / 2) * (1 - 4 * Real.sin (α / 2) ^ 2)
    ∧ Real.sin (3 * α) = 2 * Real.sin (α / 2) * (3 - 4 * Real.sin (α / 2) ^ 2)
        * (Real.cos (α / 2) * (1 - 4 * Real.sin (α / 2) ^ 2)) := by
  obtain ⟨u, rfl⟩ : ∃ u, α = 2 * u := ⟨α / 2, by ring⟩
  rw [show 2 * u / 2 = u by ring]
  have pyth := Real.sin_sq_add_cos_sq u
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show 2 * (2 * u) + β = u + Real.pi / 2 by linarith, Real.sin_add_pi_div_two]
  · exact Real.sin_two_mul u
  · rw [show β = Real.pi / 2 - 3 * u by linarith, Real.sin_pi_div_two_sub, Real.cos_three_mul]
    linear_combination (4 * Real.cos u) * pyth
  · rw [show 3 * (2 * u) = 2 * (3 * u) by ring, Real.sin_two_mul, Real.sin_three_mul,
      Real.cos_three_mul]
    linear_combination (8 * Real.sin u * (3 - 4 * Real.sin u ^ 2) * Real.cos u) * pyth

/-! ## The anchored characters -/

/-- R12's characters, anchored at `anc`: `rank2` on `ℤπ + ℤθ`, `θ = α/2 + π/2`, parity `j + b·k`.
`b = 0` is `χ₊`, `b = 1` is `χ₋`. -/
noncomputable def chiAt (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (b : ZMod 2)
    (anc : Real.Angle) : GridChar ℝ :=
  GridChar.rank2 (α / 2 + Real.pi / 2) (theta_irr_of_alpha hα) b anc

theorem chiAt_anchor (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (b : ZMod 2)
    (anc : Real.Angle) : (chiAt α hα b anc).anchor = anc := rfl

theorem chiAt_sq (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (b : ZMod 2)
    (anc : Real.Angle) :
    ∀ l ∈ (chiAt α hα b anc).L, (chiAt α hα b anc).chi l * (chiAt α hα b anc).chi l = 1 :=
  GridChar.rank2_sq _ _ _ _

theorem chiAt_mem (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (b : ZMod 2)
    (anc : Real.Angle) (j k : ℤ) :
    (((j : ℝ) * Real.pi + (k : ℝ) * (α / 2 + Real.pi / 2) : ℝ) : Real.Angle)
      ∈ (chiAt α hα b anc).L :=
  GridChar.rank2_mem _ _ _ _ _ _

theorem chiAt_chi (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (b : ZMod 2)
    (anc : Real.Angle) (j k : ℤ) :
    (chiAt α hα b anc).chi (((j : ℝ) * Real.pi + (k : ℝ) * (α / 2 + Real.pi / 2) : ℝ) : Real.Angle)
      = if (j : ZMod 2) + b * (k : ZMod 2) = 0 then 1 else -1 :=
  GridChar.rank2_chi _ _ _ _ _ _

/-- The character (hence `L`, `tileValue`) does not see the anchor. -/
theorem chiAt_tileValue (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (b : ZMod 2)
    (anc : Real.Angle) (T : Tri) :
    (chiAt α hα b anc).tileValue T
      = (GridChar.rank2 (α / 2 + Real.pi / 2) (theta_irr_of_alpha hα) b 0).tileValue T := rfl

/-! ## L2β + L3β -/

/-- **R12's flux identities (L2β + L3β), base anchor.**  For an `N`-tiling of a base-`β`
isosceles target (`angles β, β, 3α` at vertices `0, 1, 2`; base = side `01`, opposite vertex `2`)
by a `3α + 2β = π` tile with `α ∉ ℚπ`: there are integers `K, M ≡ N (mod 2)`, `|K|, |M| ≤ N`, with
`K(c+b−a) = Y − X₀ − X₁` and `M(a+b+c) = Y + X₀ + X₁` (`Y` = base, `X₀, X₁` = legs). -/
theorem Row12.flux_identities (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hP0 : D.target.angleAt 0 = β) (hP1 : D.target.angleAt 1 = β)
    (hP2 : D.target.angleAt 2 = 3 * α) :
    ∃ K M : ℤ, (2 : ℤ) ∣ K - N ∧ (2 : ℤ) ∣ M - N ∧ |K| ≤ N ∧ |M| ≤ N ∧
      (K : ℝ) * (c + b - a) = D.target.oppLen 2 - D.target.oppLen 0 - D.target.oppLen 1 ∧
      (M : ℝ) * (a + b + c) = D.target.oppLen 2 + D.target.oppLen 0 + D.target.oppLen 1 := by
  set anc := (D.target.leftUnit 0).angle with hancdef
  have eβ : β = ((2 : ℤ) : ℝ) * Real.pi + ((-3 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) := by
    push_cast; linarith
  have e3α : 3 * α = ((-3 : ℤ) : ℝ) * Real.pi + ((6 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) := by
    push_cast; ring
  have htarget : ∀ b' : ZMod 2, ∀ k,
      ((D.target.angleAt k : ℝ) : Real.Angle) ∈ (chiAt α hα b' anc).L := by
    intro b' k
    fin_cases k
    · show ((D.target.angleAt 0 : ℝ) : Real.Angle) ∈ _
      rw [hP0, eβ]; exact chiAt_mem _ _ _ _ _ _
    · show ((D.target.angleAt 1 : ℝ) : Real.Angle) ∈ _
      rw [hP1, eβ]; exact chiAt_mem _ _ _ _ _ _
    · show ((D.target.angleAt 2 : ℝ) : Real.Angle) ∈ _
      rw [hP2, e3α]; exact chiAt_mem _ _ _ _ _ _
  have hmodel : ∀ b' : ZMod 2, ∀ k,
      ((D.model.angleAt k : ℝ) : Real.Angle) ∈ (chiAt α hα b' anc).L :=
    fun b' => D.model.threeAlpha_angles_mem hα hrel h b'
  -- the target's `K_χ`, read off its corner angles and sides
  have hPK : ∀ b' : ZMod 2, (chiAt α hα b' anc).paperK D.target
      = -((if ((2 : ℤ) : ZMod 2) + b' * ((-3 : ℤ) : ZMod 2) = 0 then 1 else -1)
            * (D.target.oppLen 0 + D.target.oppLen 1)
          + (if ((-3 : ℤ) : ZMod 2) + b' * ((6 : ℤ) : ZMod 2) = 0 then 1 else -1)
            * D.target.oppLen 2) := by
    intro b'
    unfold GridChar.paperK
    rw [Fin.sum_univ_three, hP0, hP1, hP2, eβ, e3α, chiAt_chi, chiAt_chi]
    ring
  -- the apex angle `3α` has `χ₊ = χ₋ = −1`
  have hchi2 : ∀ b' : ZMod 2,
      (chiAt α hα b' anc).chi ((D.target.angleAt (0 + 2) : ℝ) : Real.Angle) = -1 := by
    intro b'
    rw [show (0 : Fin 3) + 2 = 2 from rfl, hP2, e3α, chiAt_chi, if_neg]
    have h3 : ((-3 : ℤ) : ZMod 2) = 1 := by decide
    have h6 : ((6 : ℤ) : ZMod 2) = 0 := by decide
    rw [h3, h6, mul_zero, add_zero]
    decide
  -- the model's `K_χ`
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
  rw [hMp, hchi2, hPK, if_pos (by decide), if_neg (by decide)] at hSe
  rw [hMm, hchi2, hPK, if_neg (by decide), if_neg (by decide)] at hSe'
  refine ⟨-S, S', ?_, hS2', ?_, hSN', ?_, ?_⟩
  · rw [show -S - (N : ℤ) = -(S - N) - 2 * N by ring]
    exact dvd_sub (dvd_neg.mpr hS2) (dvd_mul_right 2 _)
  · rw [abs_neg]; exact hSN
  · push_cast; linear_combination hSe
  · linear_combination hSe'

/-! ## R12 -/

/-- **Theorem R12 (ROW11_RATIONALITY.md, erratum-4 form).**  Same setting: with `K, M` of
`Row12.flux_identities` (base anchor), `K < 0 < M` and `a/c = (M+K)/(M−K)`; the target's legs are
equal (`X₀ = X₁ = X`) and `K(c+b−a) = Y − 2X`, `M(a+b+c) = Y + 2X`. -/
theorem Row12.ratio (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hP0 : D.target.angleAt 0 = β) (hP1 : D.target.angleAt 1 = β)
    (hP2 : D.target.angleAt 2 = 3 * α) :
    ∃ K M : ℤ, (2 : ℤ) ∣ K - N ∧ (2 : ℤ) ∣ M - N ∧ |K| ≤ N ∧ |M| ≤ N ∧
      D.target.oppLen 1 = D.target.oppLen 0 ∧
      (K : ℝ) * (c + b - a) = D.target.oppLen 2 - 2 * D.target.oppLen 0 ∧
      (M : ℝ) * (a + b + c) = D.target.oppLen 2 + 2 * D.target.oppLen 0 ∧
      (K : ℝ) < 0 ∧ (0 : ℝ) < M ∧ a / c = ((M : ℝ) + K) / ((M : ℝ) - K) := by
  obtain ⟨K, M, hK2, hM2, hKN, hMN, hK, hM⟩ := Row12.flux_identities D hα hrel h hP0 hP1 hP2
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  obtain ⟨tγ, tα, tβ, t3α⟩ := threeAlpha_sin_table hrel
  -- law of sines, model and target
  have ls1 := D.model.lawSin (σ 0) (σ 2)
  have ls2 := D.model.lawSin (σ 1) (σ 2)
  rw [h0, o2, h2, o0, tα, tγ] at ls1
  rw [h1, o2, h2, o1, tβ, tγ] at ls2
  have lt0 := D.target.lawSin 0 2
  have lt1 := D.target.lawSin 1 2
  rw [hP0, hP2, tβ, t3α] at lt0
  rw [hP1, hP2, tβ, t3α] at lt1
  -- positivity
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
  -- `a = 2u·c`, `b = (1 − 4u²)c`, `Y = 2u(3 − 4u²)X`, `X₁ = X`
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
  rw [hX1] at hK hM
  -- `K c = −X(1 − 2u)`, `M c = X(1 + 2u)`
  have f1 : (2 * (1 - 2 * u) * (1 + u)) ≠ 0 :=
    (mul_pos (mul_pos two_pos (by linarith)) (by linarith)).ne'
  have f2 : (2 * (1 + 2 * u) * (1 - u)) ≠ 0 :=
    (mul_pos (mul_pos two_pos (by linarith)) (by linarith)).ne'
  have hKc : (K : ℝ) * c = -X * (1 - 2 * u) := by
    refine mul_left_cancel₀ f1 ?_
    rw [ha, hb, hY] at hK
    linear_combination hK
  have hMc : (M : ℝ) * c = X * (1 + 2 * u) := by
    refine mul_left_cancel₀ f2 ?_
    rw [ha, hb, hY] at hM
    linear_combination hM
  have hp1 : 0 < X * (1 - 2 * u) := mul_pos hX (by linarith)
  have hp2 : 0 < X * (1 + 2 * u) := mul_pos hX (by linarith)
  have hKneg : (K : ℝ) < 0 := by
    by_contra hk; push Not at hk
    have := mul_nonneg hk hc.le
    linarith
  have hMpos : (0 : ℝ) < M := by
    by_contra hm; push Not at hm
    have := mul_nonneg (neg_nonneg.mpr hm) hc.le
    linarith
  have hMK : (0 : ℝ) < (M : ℝ) - K := by linarith
  refine ⟨K, M, hK2, hM2, hKN, hMN, hX1, ?_, ?_, hKneg, hMpos, ?_⟩
  · linear_combination hK
  · linear_combination hM
  · rw [div_eq_div_iff hc.ne' hMK.ne']
    linear_combination ((M : ℝ) - K) * ha + (2 * u - 1) * hMc - (2 * u + 1) * hKc

/-- **R12: the tile is rational** (`a/c ∈ ℚ`, every `N`). -/
theorem Row12.rational (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hP0 : D.target.angleAt 0 = β) (hP1 : D.target.angleAt 1 = β) :
    ∃ r : ℚ, a = (r : ℝ) * c := by
  have hP2 : D.target.angleAt 2 = 3 * α := by
    have := D.target.angleAt_sum; rw [hP0, hP1] at this; linarith
  obtain ⟨K, M, -, -, -, -, -, -, -, -, -, hs⟩ := Row12.ratio D hα hrel h hP0 hP1 hP2
  have hc : 0 < c := by
    obtain ⟨σ, -, -, -, -, -, o2⟩ := h
    exact o2 ▸ D.model.oppLen_pos (σ 2)
  refine ⟨((M : ℚ) + K) / ((M : ℚ) - K), ?_⟩
  push_cast
  rw [← hs, div_mul_cancel₀ _ hc.ne']

/-- **R12 in the target-theorem form of ROW11_RATIONALITY.md item 9** (`row12_rational`): model
angles `α, β` at vertices `0, 1`, target angles `β, β` at vertices `0, 1`. -/
theorem Row12.rational_paper (D : CongruentDissection N) (α β : ℝ)
    (hB : 3 * α + 2 * β = Real.pi) (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hT : D.model.angleAt 0 = α ∧ D.model.angleAt 1 = β)
    (hABC : D.target.angleAt 0 = β ∧ D.target.angleAt 1 = β) :
    ∃ r : ℚ, D.model.oppLen 0 = (r : ℝ) * D.model.oppLen 2 := by
  have h2 : D.model.angleAt 2 = 2 * α + β := by
    have := D.model.angleAt_sum; rw [hT.1, hT.2] at this; linarith
  exact Row12.rational D hirr hB
    ⟨1, hT.1, rfl, hT.2, rfl, h2, rfl⟩ hABC.1 hABC.2

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Tri.lawSin
#print axioms Erdos634.Geometry.threeAlpha_sin_table
#print axioms Erdos634.Geometry.Row12.flux_identities
#print axioms Erdos634.Geometry.Row12.ratio
#print axioms Erdos634.Geometry.Row12.rational
#print axioms Erdos634.Geometry.Row12.rational_paper
