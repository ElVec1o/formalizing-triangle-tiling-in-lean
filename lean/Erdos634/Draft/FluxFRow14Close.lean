-- Draft/FluxFRow14Close.lean — ROW 14 (rationality_proofs.md §2) for a REAL `CongruentDissection`:
-- on the scalene target `(2α, β, α+β)` (angles at target vertices 0, 1, 2), any `N`-tiling by the
-- `3α + 2β = π` tile with `α ∉ ℚπ` (model angles `α, β` at model vertices 0, 1) has `a/c ∈ ℚ`.
--
-- This discharges BOTH hypotheses of `Row14.row14_rational` (`hword`, `hF4`) from the dissection:
-- * Theorem 1 (flux, `χ₋` anchored at vertex 0) + law of sines give `S·c = s·Z` (`Z` = side
--   opposite `α+β`), `Y = (1−s²)Z` (`Y` = side opposite `β`);
-- * the area identity (Heron, `|det P| = N|det T|`) gives `N s² = S²(2 − s²)`, so `t = s² ∈ ℚ`;
-- * `Row14F4.row14_side_word` (the real chain of side `Y`) gives the word with `R ≥ 1` (F4);
-- * `Row14.row14_rational` closes.
-- Model scalene-ness is derived (`a = b` would force `α = π/5`, `golden_alpha`).
--
-- REUSE: flux pattern copied from `Row13.boundary`, area pattern from `Row11.area`, all wall setup
-- from `WallDir`/`WallThird`/`ApexLegWord.hdirab_dirFun`/`BaseWalkGeneral.hiso_wallFun'`.
-- NO real tiling of this target is known (rationality_proofs.md P8); the theorem is witnessed only
-- at the level of its ingredients (see the end of the file).  Formalization debt (paper-level
-- PROVED); not progress on the three /goal outcomes.
import Erdos634.Draft.FluxFRow14F4
import Erdos634.Draft.FluxFRow14
import Erdos634.Draft.FluxDRow13
import Erdos634.Draft.FluxDRow12a
import Erdos634.Draft.ApexLegWord
import Erdos634.WallThird
import Erdos634.WallDir
import Erdos634.BaseWalkGeneral

open scoped Classical

namespace Erdos634.Geometry

variable {N : ℕ}

set_option maxHeartbeats 1000000 in
/-- **Row 14's Theorem 1 + law of sines + area.** -/
theorem Row14.setup (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hP0 : D.target.angleAt 0 = 2 * α) (hP1 : D.target.angleAt 1 = β)
    (hP2 : D.target.angleAt 2 = α + β) :
    ∃ (s : ℝ) (S : ℤ), 0 < s ∧ s < 1 ∧ 0 < c ∧ a = s * c ∧ b = (1 - s ^ 2) * c ∧
      D.target.oppLen 1 = (1 - s ^ 2) * D.target.oppLen 2 ∧
      (S : ℝ) * c = s * D.target.oppLen 2 ∧
      (N : ℝ) * s ^ 2 = (S : ℝ) ^ 2 * (2 - s ^ 2) := by
  -- flux (χ₋, anchor 0)
  set anc := (D.target.leftUnit 0).angle with hancdef
  have e2α : ((2 * α : ℝ) : Real.Angle)
      = ((((-2 : ℤ) : ℝ) * Real.pi + ((4 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) : ℝ) : Real.Angle) := by
    congr 1; push_cast; ring
  have eβ : ((β : ℝ) : Real.Angle)
      = ((((2 : ℤ) : ℝ) * Real.pi + ((-3 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) : ℝ) : Real.Angle) := by
    congr 1; push_cast; linarith
  have eAB : ((α + β : ℝ) : Real.Angle)
      = ((((1 : ℤ) : ℝ) * Real.pi + ((-1 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) : ℝ) : Real.Angle) := by
    congr 1; push_cast; linarith
  have htarget : ∀ k, ((D.target.angleAt k : ℝ) : Real.Angle) ∈ (chiAt α hα 1 anc).L := by
    intro k
    fin_cases k
    · show ((D.target.angleAt 0 : ℝ) : Real.Angle) ∈ _
      rw [hP0, e2α]; exact chiAt_mem _ _ _ _ _ _
    · show ((D.target.angleAt 1 : ℝ) : Real.Angle) ∈ _
      rw [hP1, eβ]; exact chiAt_mem _ _ _ _ _ _
    · show ((D.target.angleAt 2 : ℝ) : Real.Angle) ∈ _
      rw [hP2, eAB]; exact chiAt_mem _ _ _ _ _ _
  have hmodel : ∀ k, ((D.model.angleAt k : ℝ) : Real.Angle) ∈ (chiAt α hα 1 anc).L :=
    D.model.threeAlpha_angles_mem hα hrel h 1
  have hc2α : (chiAt α hα 1 anc).chi ((2 * α : ℝ) : Real.Angle) = 1 := by
    rw [e2α, chiAt_chi, if_pos (by decide)]
  have hcβ : (chiAt α hα 1 anc).chi ((β : ℝ) : Real.Angle) = -1 := by
    rw [eβ, chiAt_chi, if_neg (by decide)]
  have hcAB : (chiAt α hα 1 anc).chi ((α + β : ℝ) : Real.Angle) = 1 := by
    rw [eAB, chiAt_chi, if_pos (by decide)]
  have hPK : (chiAt α hα 1 anc).paperK D.target
      = -(D.target.oppLen 0 - D.target.oppLen 1 + D.target.oppLen 2) := by
    unfold GridChar.paperK
    rw [Fin.sum_univ_three, hP0, hP1, hP2, hc2α, hcβ, hcAB]
    ring
  have hMm : (chiAt α hα 1 anc).paperK D.model = a + b + c := by
    rw [← GridChar.tileValue_eq_paperK _ (chiAt_sq _ _ _ _) _ hmodel, chiAt_tileValue]
    exact threeAlpha_tileValue_minus D.model hα hrel h
  obtain ⟨S, -, -, hSe⟩ := D.triangle_boundary_anchor (chiAt α hα 1 anc)
    (chiAt_sq _ _ _ _) hmodel htarget 0 rfl
  have hchi2 : (chiAt α hα 1 anc).chi ((D.target.angleAt (0 + 2) : ℝ) : Real.Angle) = 1 := by
    rw [show (0 : Fin 3) + 2 = 2 from rfl, hP2, hcAB]
  rw [hMm, hchi2, hPK] at hSe
  -- law of sines
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  obtain ⟨tγ, tα, tβ, -⟩ := threeAlpha_sin_table hrel
  have ls1 := D.model.lawSin (σ 0) (σ 2)
  have ls2 := D.model.lawSin (σ 1) (σ 2)
  rw [h0, o2, h2, o0, tα, tγ] at ls1
  rw [h1, o2, h2, o1, tβ, tγ] at ls2
  have hαpos : 0 < α := h0 ▸ D.model.angleAt_pos' (σ 0)
  have hβpos : 0 < β := h1 ▸ D.model.angleAt_pos' (σ 1)
  have hπ := Real.pi_pos
  have hco : 0 < Real.cos (α / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hu0 : 0 < Real.sin (α / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hu1 : Real.sin (α / 2) < 1 / 2 := by
    rw [← Real.sin_pi_div_six]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  have hAB : Real.sin (α + β) = Real.cos (α / 2) := by
    rw [show α + β = Real.pi / 2 - α / 2 by linarith, Real.sin_pi_div_two_sub]
  have hcos : Real.cos α = 1 - 2 * Real.sin (α / 2) ^ 2 := by
    have e := Real.cos_two_mul (α / 2)
    rw [show 2 * (α / 2) = α by ring] at e
    have p := Real.sin_sq_add_cos_sq (α / 2)
    linear_combination e + 2 * p
  have h2α : Real.sin (2 * α) = 2 * Real.sin (α / 2) * Real.cos (α / 2) * (2 - 4 * Real.sin (α / 2) ^ 2) := by
    rw [Real.sin_two_mul, tα, hcos]; ring
  have lt0 := D.target.lawSin 0 2
  have lt1 := D.target.lawSin 1 2
  rw [hP0, hP2, h2α, hAB] at lt0
  rw [hP1, hP2, tβ, hAB] at lt1
  have hc : 0 < c := o2 ▸ D.model.oppLen_pos (σ 2)
  have hZ : 0 < D.target.oppLen 2 := D.target.oppLen_pos 2
  set u := Real.sin (α / 2) with hudef
  set co := Real.cos (α / 2) with hcodef
  set X := D.target.oppLen 0 with hXdef
  set Y := D.target.oppLen 1 with hYdef
  set Z := D.target.oppLen 2 with hZdef
  have ha : a = 2 * u * c :=
    mul_left_cancel₀ hco.ne' (by linear_combination (-1 : ℝ) * ls1)
  have hb : b = (1 - 4 * u ^ 2) * c :=
    mul_left_cancel₀ hco.ne' (by linear_combination (-1 : ℝ) * ls2)
  have hXZ : X = 2 * u * (2 - 4 * u ^ 2) * Z :=
    mul_left_cancel₀ hco.ne' (by linear_combination (-1 : ℝ) * lt0)
  have hYZ : Y = (1 - 4 * u ^ 2) * Z :=
    mul_left_cancel₀ hco.ne' (by linear_combination (-1 : ℝ) * lt1)
  set s := 2 * u with hsdef
  have hs0 : 0 < s := by linarith
  have hs1 : s < 1 := by linarith
  have hfac : 0 < 2 + s - s ^ 2 := by have : s * s < 1 * 1 := mul_lt_mul hs1 hs1.le hs0 zero_le_one; nlinarith [sq s]
  have hSZ : (S : ℝ) * c = s * Z := by
    have e : (2 + s - s ^ 2) * ((S : ℝ) * c - s * Z) = 0 := by
      rw [ha, hb, hXZ, hYZ] at hSe
      linear_combination hSe
    have := (mul_eq_zero.mp e).resolve_left hfac.ne'
    linarith
  -- area
  have hA := D.abs_detTri_target
  have hsq : Erdos634.AreaDet.detTri D.target ^ 2
      = (N : ℝ) ^ 2 * Erdos634.AreaDet.detTri D.model ^ 2 := by
    rw [← sq_abs (Erdos634.AreaDet.detTri D.target), hA, mul_pow, sq_abs]
  have hT := D.target.four_detTri_sq_symm
  have hMo := D.model.four_detTri_sq_symm
  rw [Tri.sum_pow_perm' D.model 2 σ, Tri.sum_pow_perm' D.model 4 σ, o0, o1, o2] at hMo
  rw [Fin.sum_univ_three, Fin.sum_univ_three, ← hXdef, ← hYdef, ← hZdef, hXZ, hYZ] at hT
  rw [ha, hb] at hMo
  have hG : 0 < s ^ 2 * (2 - s) * (1 - s) ^ 2 * (1 + s) ^ 2 * (2 + s) := by
    have e1 : 0 < (1 - s) ^ 2 := pow_pos (by linarith) 2
    have e2 : 0 < (1 + s) ^ 2 := pow_pos (by linarith) 2
    have e3 : 0 < s ^ 2 := pow_pos hs0 2
    have h1 : 0 < 2 - s := by linarith
    have h2 : 0 < 2 + s := by linarith
    exact mul_pos (mul_pos (mul_pos (mul_pos e3 h1) e1) e2) h2
  have key : (s ^ 2 * (2 - s) * (1 - s) ^ 2 * (1 + s) ^ 2 * (2 + s)) *
      ((Z ^ 2 * (2 - s ^ 2) - N * c ^ 2) * (Z ^ 2 * (2 - s ^ 2) + N * c ^ 2)) = 0 := by
    rw [hsdef] at hT hMo ⊢
    linear_combination (-1 : ℝ) * hT + (N : ℝ) ^ 2 * hMo + 4 * hsq
  have hsum : 0 < Z ^ 2 * (2 - s ^ 2) + N * c ^ 2 :=
    add_pos_of_pos_of_nonneg (mul_pos (pow_pos hZ 2) (by have := mul_lt_mul hs1 hs1.le hs0 zero_le_one; linarith [sq s]))
      (mul_nonneg (Nat.cast_nonneg N) (sq_nonneg c))
  have hArea : Z ^ 2 * (2 - s ^ 2) = N * c ^ 2 := by
    rcases mul_eq_zero.mp key with e | e
    · exact absurd e hG.ne'
    · rcases mul_eq_zero.mp e with e' | e'
      · linarith
      · exact absurd e' hsum.ne'
  have hfin : c ^ 2 * ((N : ℝ) * s ^ 2 - (S : ℝ) ^ 2 * (2 - s ^ 2)) = 0 := by
    linear_combination (-(s ^ 2)) * hArea - (2 - s ^ 2) * (s * Z + (S : ℝ) * c) * hSZ
  refine ⟨s, S, hs0, hs1, hc, ?_, ?_, ?_, hSZ, ?_⟩
  · rw [ha]
  · rw [hb]; ring
  · rw [hYZ]; ring
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hfin).resolve_left (pow_pos hc 2).ne')

/-- **ROW 14, closed for a real `CongruentDissection`.**  Model angles `α, β` at model vertices
`0, 1` (so `γ = 2α+β` at vertex `2`), `3α + 2β = π`, `α ∉ ℚπ`; target angles `2α, β` at target
vertices `0, 1` (so `α+β` at vertex `2`).  Then `a/c ∈ ℚ`.  No hypothesis beyond these. -/
theorem Row14.rational_real (D : CongruentDissection N) (α β : ℝ)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (hm0 : D.model.angleAt 0 = α) (hm1 : D.model.angleAt 1 = β)
    (hP0 : D.target.angleAt 0 = 2 * α) (hP1 : D.target.angleAt 1 = β) :
    ∃ r : ℚ, D.model.oppLen 0 = (r : ℝ) * D.model.oppLen 2 := by
  have hm2 : D.model.angleAt 2 = 2 * α + β := by
    have := D.model.angleAt_sum; rw [hm0, hm1] at this; linarith
  have hP2 : D.target.angleAt 2 = α + β := by
    have := D.target.angleAt_sum; rw [hP0, hP1] at this; linarith
  have h3 : D.model.ThreeAlphaData α β (D.model.oppLen 0) (D.model.oppLen 1) (D.model.oppLen 2) :=
    ⟨1, hm0, rfl, hm1, rfl, hm2, rfl⟩
  obtain ⟨s, S, hs0, hs1, hc, ha, hb, hYZ, hSZ, hArea⟩ := Row14.setup D hirr hrel h3 hP0 hP1 hP2
  have hN : 0 < N := D.toDissection.pos
  -- angle facts
  have hαpos : 0 < α := hm0 ▸ D.model.angleAt_pos' 0
  have hβpos : 0 < β := hm1 ▸ D.model.angleAt_pos' 1
  have hπ := Real.pi_pos
  set γ := 2 * α + β with hγdef
  have hαβ : α ≠ β := by
    intro e; apply hirr; exact ⟨1 / 5, by push_cast; linarith⟩
  have hαγ : α ≠ γ := by intro e; linarith
  have hβγ : β ≠ γ := by intro e; linarith
  have hαπ : α ≠ Real.pi := by intro e; linarith
  have hβπ : β ≠ Real.pi := by intro e; linarith
  have hγπ : γ ≠ Real.pi := by intro e; linarith
  -- model scalene: `a = b` would force `α = π/5`
  have hscal : ∀ m m' : Fin 3, m ≠ m' →
      TilePlacement.sideOpp D.model m ≠ TilePlacement.sideOpp D.model m' := by
    have hs2 : s ^ 2 < 1 := by nlinarith
    have hab : D.model.oppLen 0 ≠ D.model.oppLen 1 := by
      intro e
      rw [ha, hb] at e
      have e' : s = 1 - s ^ 2 := mul_right_cancel₀ hc.ne' e
      -- `s = 2 sin(α/2)` is not recoverable here; argue through `golden_alpha` via the sine table
      have hsin : s = 2 * Real.sin (α / 2) := by
        obtain ⟨tγ, tα, -, -⟩ := threeAlpha_sin_table hrel
        have ls := D.model.lawSin 0 2
        rw [hm0, hm2, tα, tγ, ha] at ls
        have hco : 0 < Real.cos (α / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
        have : (s - 2 * Real.sin (α / 2)) * (Real.cos (α / 2) * D.model.oppLen 2) = 0 := by
          linear_combination (-1 : ℝ) * ls
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right (mul_pos hco hc).ne')
      have hq : 4 * Real.sin (α / 2) ^ 2 + 2 * Real.sin (α / 2) - 1 = 0 := by
        rw [hsin] at e'; linear_combination e'
      have := golden_alpha hαpos (by linarith) hq
      exact hirr ⟨1 / 5, by push_cast; linarith⟩
    have hac : D.model.oppLen 0 ≠ D.model.oppLen 2 := by
      intro e; rw [ha] at e
      have : (s - 1) * D.model.oppLen 2 = 0 := by linear_combination e
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · linarith
    have hbc : D.model.oppLen 1 ≠ D.model.oppLen 2 := by
      intro e; rw [hb] at e
      have : s ^ 2 * D.model.oppLen 2 = 0 := by linear_combination -e
      rcases mul_eq_zero.mp this with h | h
      · nlinarith
      · linarith
    intro m m' hmm'
    show D.model.oppLen m ≠ D.model.oppLen m'
    fin_cases m <;> fin_cases m' <;> simp at hmm' ⊢
    · exact hab
    · exact hac
    · exact fun e => hab e.symm
    · exact hbc
    · exact fun e => hac e.symm
    · exact fun e => hbc e.symm
  -- the real side word of `Y` (target side `2 → 0`), with `R ≥ 1` (F4)
  obtain ⟨Pc, Qc, Rc, hRc, hw⟩ := Erdos634.Row14F4.row14_side_word hN D α β γ hαβ hαγ hαπ
    hαpos.ne' hβγ hβπ hβpos.ne' hγπ (by linarith) hπ.ne' rfl hrel hirr hscal hm0 hm1 hm2 2
    (dirFun D.target 2).linear (hker_wallFun D.target 2)
    (Erdos634.Draft.ApexLegWord.hdirab_dirFun D.target 2)
    (hthird_general D.toDissection _ 0
      (wallFun_linear_ne_zero D.target 2)
      (fun y hy => Erdos634.SideWall.wallFun_le D.target 2 hy))
    (Or.inr hP2) (Or.inl hP0) (hiso_wallFun' D.target 2)
  have hw' : D.target.oppLen 1 = Pc * (s * D.model.oppLen 2) + Qc * ((1 - s ^ 2) * D.model.oppLen 2)
      + Rc * D.model.oppLen 2 := by
    rw [← ha, ← hb]; exact hw
  -- `t = s²` is rational
  have hS : (S : ℝ) ≠ 0 := by
    intro e; rw [e, zero_mul] at hSZ
    have := mul_pos hs0 (D.target.oppLen_pos 2); linarith
  have hS' : S ≠ 0 := by exact_mod_cast hS
  have hden : (0 : ℚ) < N + S ^ 2 := by positivity
  set T : ℚ := 2 * S ^ 2 / (N + S ^ 2) with hTdef
  have ht : s ^ 2 = (T : ℝ) := by
    rw [hTdef]; push_cast
    have hd : (0 : ℝ) < N + (S : ℝ) ^ 2 := by exact_mod_cast hden
    rw [eq_div_iff hd.ne']; linear_combination hArea
  have hT0 : T ≠ 0 := div_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero 2 (Int.cast_ne_zero.mpr hS'))) hden.ne'
  have ht1 : (0 : ℝ) < 1 - s ^ 2 := by nlinarith
  have key : (Pc : ℝ) * s + Qc * (1 - s ^ 2) + Rc = S * (1 - s ^ 2) / s := by
    rw [eq_div_iff hs0.ne']
    refine mul_left_cancel₀ hc.ne' ?_
    linear_combination (-s) * hw' + s * hYZ - (1 - s ^ 2) * hSZ
  have hword : ((Pc : ℤ) : ℝ) * s + (Qc : ℝ) * (1 - s ^ 2) + (Rc : ℝ)
      = ((S : ℤ) : ℝ) * (1 - s ^ 2) / s ^ 2 * s := by
    push_cast; rw [key]; field_simp
  have hrat := Erdos634.Row14.row14_rational s (s ^ 2) T ht hT0 ht1 (Pc : ℤ) S Qc Rc hword hRc
  unfold Erdos634.Row14.NotRat at hrat
  push_neg at hrat
  obtain ⟨q, hq⟩ := hrat
  exact ⟨q, by rw [ha, hq]⟩

/-- **Non-vacuity of the model half**: the model hypotheses of `Row14.rational_real` are
satisfiable together with `α ∉ ℚπ` — any `α` with `α/π` irrational in `(0, π/3)` gives a real
triangle `(α, β, 2α+β)`, `β = (π − 3α)/2 > 0`.  Here only the arithmetic consistency is checked
(the angles are positive and sum to `π`) at a symbolic `α`; no real tiling of the row-14 target is
known (rationality_proofs.md P8), so the full hypothesis set has no Lean witness. -/
theorem Row14.rational_real_angle_witness (α : ℝ) (h0 : 0 < α) (h1 : α < Real.pi / 3) :
    let β := (Real.pi - 3 * α) / 2
    0 < β ∧ 3 * α + 2 * β = Real.pi ∧ α + β + (2 * α + β) = Real.pi ∧
      0 < 2 * α ∧ 0 < α + β ∧ 2 * α + β + (α + β) = Real.pi := by
  intro β
  refine ⟨by simp only [β]; linarith, by simp only [β]; ring, by simp only [β]; ring,
    by linarith, by simp only [β]; linarith, by simp only [β]; ring⟩

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row14.setup
#print axioms Erdos634.Geometry.Row14.rational_real
#print axioms Erdos634.Geometry.Row14.rational_real_angle_witness
