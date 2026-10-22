-- Draft/FluxDRow13.lean — ROW 13 (rationality/rationality_proofs.md §1, PROVED after two reviews):
-- on the base-(α+β) target `(α+β, α+β, α)`, an `N`-tiling (any `N`) by the `3α + 2β = π` tile with
-- `α ∉ ℚπ` (reflections allowed, not necessarily edge-to-edge) has a rational tile, `a/c ∈ ℚ`.
-- Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- ROUTE (named; differs from §1's): §1 uses Theorem 1 + the area identity (`q = (1+s)/(1−s)`); here
-- the two characters of the flux layer are used instead, as in ROW11_RATIONALITY.md §6 ("Base α+β
-- (row 13): (1+s)/(1−s). So s = (K−M)/(K+M), a second proof of rationality_proofs.md §1
-- (reproduction)"): anchored at the base, `K(c+b−a) = Y + 2X` and `M(a+b+c) = 2X − Y` (Theorem 1's
-- signed perimeter, minus on the side opposite the single-tile apex), and S gives `Y = sX`, so
-- `Kc(1−s) = X = Mc(1+s)`, `s = (K−M)/(K+M)`.  No area, no side word.
--
-- CONDITIONAL AT THE GEOMETRIC LEVEL: "Row 13 still has no real-tiling witness" (review 2 record);
-- the algebraic step is witnessed in Draft/FluxDRow13Witness.lean (`s = 1/2`, `(K, M) = (3, 1)`).
--
-- Formalization debt; not progress on the three /goal outcomes.
import Erdos634.Draft.FluxDRow11

open scoped Classical

namespace Erdos634.Geometry

variable {N : ℕ}

/-- **Row 13's boundary identities** (base anchor): `K(c+b−a) = Y + X₀ + X₁`,
`M(a+b+c) = X₀ + X₁ − Y`, `K ≡ M ≡ N (2)`, `|K|, |M| ≤ N`. -/
theorem Row13.boundary (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hP0 : D.target.angleAt 0 = α + β) (hP1 : D.target.angleAt 1 = α + β)
    (hP2 : D.target.angleAt 2 = α) :
    ∃ K M : ℤ, (2 : ℤ) ∣ K - N ∧ (2 : ℤ) ∣ M - N ∧ |K| ≤ N ∧ |M| ≤ N ∧
      (K : ℝ) * (c + b - a) = D.target.oppLen 2 + D.target.oppLen 0 + D.target.oppLen 1 ∧
      (M : ℝ) * (a + b + c) = D.target.oppLen 0 + D.target.oppLen 1 - D.target.oppLen 2 := by
  set anc := (D.target.leftUnit 0).angle with hancdef
  have eα : ((α : ℝ) : Real.Angle)
      = ((((-1 : ℤ) : ℝ) * Real.pi + ((2 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) : ℝ) : Real.Angle) := by
    congr 1; push_cast; ring
  have eAB : ((α + β : ℝ) : Real.Angle)
      = ((((1 : ℤ) : ℝ) * Real.pi + ((-1 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) : ℝ) : Real.Angle) := by
    congr 1; push_cast; linarith
  have htarget : ∀ b' : ZMod 2, ∀ k,
      ((D.target.angleAt k : ℝ) : Real.Angle) ∈ (chiAt α hα b' anc).L := by
    intro b' k
    fin_cases k
    · show ((D.target.angleAt 0 : ℝ) : Real.Angle) ∈ _
      rw [hP0, eAB]; exact chiAt_mem _ _ _ _ _ _
    · show ((D.target.angleAt 1 : ℝ) : Real.Angle) ∈ _
      rw [hP1, eAB]; exact chiAt_mem _ _ _ _ _ _
    · show ((D.target.angleAt 2 : ℝ) : Real.Angle) ∈ _
      rw [hP2, eα]; exact chiAt_mem _ _ _ _ _ _
  have hmodel : ∀ b' : ZMod 2, ∀ k,
      ((D.model.angleAt k : ℝ) : Real.Angle) ∈ (chiAt α hα b' anc).L :=
    fun b' => D.model.threeAlpha_angles_mem hα hrel h b'
  -- `χ(α) = −1` for both characters; `χ₊(α+β) = −1`, `χ₋(α+β) = +1`
  have hcα : ∀ b' : ZMod 2, (chiAt α hα b' anc).chi ((α : ℝ) : Real.Angle) = -1 := by
    intro b'
    rw [eα, chiAt_chi, if_neg]
    have h1 : ((-1 : ℤ) : ZMod 2) = 1 := by decide
    have h2 : ((2 : ℤ) : ZMod 2) = 0 := by decide
    rw [h1, h2, mul_zero, add_zero]
    decide
  have hcAB0 : (chiAt α hα 0 anc).chi ((α + β : ℝ) : Real.Angle) = -1 := by
    rw [eAB, chiAt_chi, if_neg (by decide)]
  have hcAB1 : (chiAt α hα 1 anc).chi ((α + β : ℝ) : Real.Angle) = 1 := by
    rw [eAB, chiAt_chi, if_pos (by decide)]
  have hchi2 : ∀ b' : ZMod 2,
      (chiAt α hα b' anc).chi ((D.target.angleAt (0 + 2) : ℝ) : Real.Angle) = -1 := by
    intro b'
    rw [show (0 : Fin 3) + 2 = 2 from rfl, hP2, hcα]
  have hPK0 : (chiAt α hα 0 anc).paperK D.target
      = D.target.oppLen 2 + D.target.oppLen 0 + D.target.oppLen 1 := by
    unfold GridChar.paperK
    rw [Fin.sum_univ_three, hP0, hP1, hP2, hcAB0, hcα]
    ring
  have hPK1 : (chiAt α hα 1 anc).paperK D.target
      = D.target.oppLen 2 - D.target.oppLen 0 - D.target.oppLen 1 := by
    unfold GridChar.paperK
    rw [Fin.sum_univ_three, hP0, hP1, hP2, hcAB1, hcα]
    ring
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
  rw [hMp, hchi2, hPK0] at hSe
  rw [hMm, hchi2, hPK1] at hSe'
  have hneg : ∀ T : ℤ, (2 : ℤ) ∣ T - N → (2 : ℤ) ∣ -T - N := fun T hT => by
    rw [show -T - (N : ℤ) = -(T - N) - 2 * N by ring]
    exact dvd_sub (dvd_neg.mpr hT) (dvd_mul_right 2 _)
  refine ⟨-S, -S', hneg S hS2, hneg S' hS2', by rw [abs_neg]; exact hSN,
    by rw [abs_neg]; exact hSN', ?_, ?_⟩
  · push_cast; linear_combination hSe
  · push_cast; linear_combination -hSe'

/-- **ROW 13 (rationality_proofs.md §1): the tile is rational on the base-(α+β) target**, every `N`,
with `a/c = (K − M)/(K + M)`.  CONDITIONAL: no real tiling of this target is known. -/
theorem Row13.rational (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hP0 : D.target.angleAt 0 = α + β) (hP1 : D.target.angleAt 1 = α + β) :
    ∃ K M : ℤ, 0 < K ∧ 0 < M ∧ a / c = ((K : ℝ) - M) / ((K : ℝ) + M) ∧ ∃ r : ℚ, a = (r : ℝ) * c := by
  have hP2 : D.target.angleAt 2 = α := by
    have := D.target.angleAt_sum; rw [hP0, hP1] at this; linarith
  obtain ⟨K, M, -, -, -, -, hK, hM⟩ := Row13.boundary D hα hrel h hP0 hP1 hP2
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  obtain ⟨tγ, tα, tβ, -⟩ := threeAlpha_sin_table hrel
  have ls1 := D.model.lawSin (σ 0) (σ 2)
  have ls2 := D.model.lawSin (σ 1) (σ 2)
  rw [h0, o2, h2, o0, tα, tγ] at ls1
  rw [h1, o2, h2, o1, tβ, tγ] at ls2
  have hαpos : 0 < α := h0 ▸ D.model.angleAt_pos' (σ 0)
  have hβpos : 0 < β := h1 ▸ D.model.angleAt_pos' (σ 1)
  have hπ := Real.pi_pos
  have hAB : Real.sin (α + β) = Real.cos (α / 2) := by
    rw [show α + β = Real.pi - (2 * α + β) by linarith, Real.sin_pi_sub, tγ]
  have lt0 := D.target.lawSin 0 2
  have lt1 := D.target.lawSin 1 2
  rw [hP0, hP2, hAB, tα] at lt0
  rw [hP1, hP2, hAB, tα] at lt1
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
  have ha : a = 2 * u * c := mul_left_cancel₀ hco.ne' (by linear_combination (-1 : ℝ) * ls1)
  have hb : b = (1 - 4 * u ^ 2) * c := mul_left_cancel₀ hco.ne' (by linear_combination (-1 : ℝ) * ls2)
  -- `Y = sX`, `X₁ = X`
  have hY : Y = 2 * u * X := mul_left_cancel₀ hco.ne' (by linear_combination lt0)
  have hY1 : Y = 2 * u * X₁ := mul_left_cancel₀ hco.ne' (by linear_combination lt1)
  have hX1 : X₁ = X := mul_left_cancel₀ (mul_pos two_pos hs0).ne' (by linear_combination hY - hY1)
  rw [hX1, hY, ha, hb] at hK hM
  -- `K c (1 − s) = X`, `M c (1 + s) = X` (`s = 2u`)
  have hKc : (K : ℝ) * c * (1 - 2 * u) = X := by
    have e : (2 + 2 * u) * ((K : ℝ) * c * (1 - 2 * u) - X) = 0 := by linear_combination hK
    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left (by linarith))
  have hMc : (M : ℝ) * c * (1 + 2 * u) = X := by
    have e : (2 - 2 * u) * ((M : ℝ) * c * (1 + 2 * u) - X) = 0 := by linear_combination hM
    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left (by linarith))
  have hKpos : (0 : ℝ) < K := by
    by_contra hn; push Not at hn
    have := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hn hc.le)
      (by linarith : (0 : ℝ) ≤ 1 - 2 * u)
    linarith
  have hMpos : (0 : ℝ) < M := by
    by_contra hn; push Not at hn
    have := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hn hc.le)
      (by linarith : (0 : ℝ) ≤ 1 + 2 * u)
    linarith
  have hKM : (0 : ℝ) < (K : ℝ) + M := by linarith
  have hratio : a / c = ((K : ℝ) - M) / ((K : ℝ) + M) := by
    rw [div_eq_div_iff hc.ne' hKM.ne', ha]
    linear_combination (-1 : ℝ) * hKc + hMc
  refine ⟨K, M, by exact_mod_cast hKpos, by exact_mod_cast hMpos, hratio,
    ((K : ℚ) - M) / ((K : ℚ) + M), ?_⟩
  push_cast
  rw [← hratio, div_mul_cancel₀ _ hc.ne']

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row13.boundary
#print axioms Erdos634.Geometry.Row13.rational
