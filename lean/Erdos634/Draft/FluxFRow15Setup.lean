-- Draft/FluxFRow15Setup.lean — ROW 15 (rationality_proofs.md §5) dissection-level setup: for a REAL
-- `CongruentDissection` of the target `(2α, α, 2β)` (angles at target vertices 0, 1, 2) by the
-- `3α + 2β = π` tile, `α ∉ ℚπ`, derive, with `s = a/c = 2 sin(α/2)`, `h(s) = (1−s)(2+s)`,
-- `g(s) = (2−s²)(3−s²)` and `Y` the side opposite `α`:
-- * law of sines: `X = (2−s²)·Y` (side opposite `2α`), `Z = (1−s²)(3−s²)·Y` (opposite `2β`);
-- * Theorem 1 (flux `χ₋` anchored at target vertex 0, `CongruentDissection.triangle_boundary_anchor`):
--   `S·c = h(s)·Y` for an integer `S` (the paper's `M`, sign pattern `X − Y + Z`);
-- * area (Heron, `|det P| = N |det T|`): `N·h(s)² = S²·g(s)`, i.e. `F(s) = N/S² = q ∈ ℚ`.
-- Pattern copied from `Row14.setup` (Draft/FluxFRow14Close.lean): same character, same area
-- combination; only the target's angle encoding and the sine values differ.
--
-- Formalization debt (paper-level PROVED); not progress on the three /goal outcomes.
import Erdos634.Draft.FluxFRow14Close

open scoped Classical

namespace Erdos634.Geometry

variable {N : ℕ}

set_option maxHeartbeats 1000000 in
/-- **Row 15's Theorem 1 + law of sines + area.** -/
theorem Row15.setup (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hP0 : D.target.angleAt 0 = 2 * α) (hP1 : D.target.angleAt 1 = α)
    (hP2 : D.target.angleAt 2 = 2 * β) :
    ∃ (s : ℝ) (S : ℤ), 0 < s ∧ s < 1 ∧ 0 < c ∧ a = s * c ∧ b = (1 - s ^ 2) * c ∧
      D.target.oppLen 0 = (2 - s ^ 2) * D.target.oppLen 1 ∧
      D.target.oppLen 2 = (1 - s ^ 2) * (3 - s ^ 2) * D.target.oppLen 1 ∧
      (S : ℝ) * c = (1 - s) * (2 + s) * D.target.oppLen 1 ∧
      (N : ℝ) * ((1 - s) * (2 + s)) ^ 2 = (S : ℝ) ^ 2 * ((2 - s ^ 2) * (3 - s ^ 2)) := by
  -- flux (χ₋, anchor 0)
  set anc := (D.target.leftUnit 0).angle with hancdef
  have e2α : ((2 * α : ℝ) : Real.Angle)
      = ((((-2 : ℤ) : ℝ) * Real.pi + ((4 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) : ℝ) : Real.Angle) := by
    congr 1; push_cast; ring
  have eα : ((α : ℝ) : Real.Angle)
      = ((((-1 : ℤ) : ℝ) * Real.pi + ((2 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) : ℝ) : Real.Angle) := by
    congr 1; push_cast; ring
  have e2β : ((2 * β : ℝ) : Real.Angle)
      = ((((4 : ℤ) : ℝ) * Real.pi + ((-6 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) : ℝ) : Real.Angle) := by
    congr 1; push_cast; linarith
  have htarget : ∀ k, ((D.target.angleAt k : ℝ) : Real.Angle) ∈ (chiAt α hα 1 anc).L := by
    intro k
    fin_cases k
    · show ((D.target.angleAt 0 : ℝ) : Real.Angle) ∈ _
      rw [hP0, e2α]; exact chiAt_mem _ _ _ _ _ _
    · show ((D.target.angleAt 1 : ℝ) : Real.Angle) ∈ _
      rw [hP1, eα]; exact chiAt_mem _ _ _ _ _ _
    · show ((D.target.angleAt 2 : ℝ) : Real.Angle) ∈ _
      rw [hP2, e2β]; exact chiAt_mem _ _ _ _ _ _
  have hmodel : ∀ k, ((D.model.angleAt k : ℝ) : Real.Angle) ∈ (chiAt α hα 1 anc).L :=
    D.model.threeAlpha_angles_mem hα hrel h 1
  have hc2α : (chiAt α hα 1 anc).chi ((2 * α : ℝ) : Real.Angle) = 1 := by
    rw [e2α, chiAt_chi, if_pos (by decide)]
  have hcα : (chiAt α hα 1 anc).chi ((α : ℝ) : Real.Angle) = -1 := by
    rw [eα, chiAt_chi, if_neg (by decide)]
  have hc2β : (chiAt α hα 1 anc).chi ((2 * β : ℝ) : Real.Angle) = 1 := by
    rw [e2β, chiAt_chi, if_pos (by decide)]
  have hPK : (chiAt α hα 1 anc).paperK D.target
      = -(D.target.oppLen 0 - D.target.oppLen 1 + D.target.oppLen 2) := by
    unfold GridChar.paperK
    rw [Fin.sum_univ_three, hP0, hP1, hP2, hc2α, hcα, hc2β]
    ring
  have hMm : (chiAt α hα 1 anc).paperK D.model = a + b + c := by
    rw [← GridChar.tileValue_eq_paperK _ (chiAt_sq _ _ _ _) _ hmodel, chiAt_tileValue]
    exact threeAlpha_tileValue_minus D.model hα hrel h
  obtain ⟨S, -, -, hSe⟩ := D.triangle_boundary_anchor (chiAt α hα 1 anc)
    (chiAt_sq _ _ _ _) hmodel htarget 0 rfl
  have hchi2 : (chiAt α hα 1 anc).chi ((D.target.angleAt (0 + 2) : ℝ) : Real.Angle) = 1 := by
    rw [show (0 : Fin 3) + 2 = 2 from rfl, hP2, hc2β]
  rw [hMm, hchi2, hPK] at hSe
  -- law of sines
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  obtain ⟨tγ, tα, tβ, t3α⟩ := threeAlpha_sin_table hrel
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
  have hcos : Real.cos α = 1 - 2 * Real.sin (α / 2) ^ 2 := by
    have e := Real.cos_two_mul (α / 2)
    rw [show 2 * (α / 2) = α by ring] at e
    have p := Real.sin_sq_add_cos_sq (α / 2)
    linear_combination e + 2 * p
  have h2α : Real.sin (2 * α) = 2 * Real.sin (α / 2) * Real.cos (α / 2) * (2 - 4 * Real.sin (α / 2) ^ 2) := by
    rw [Real.sin_two_mul, tα, hcos]; ring
  have h2β : Real.sin (2 * β) = Real.sin (3 * α) := by
    rw [show 2 * β = Real.pi - 3 * α by linarith, Real.sin_pi_sub]
  have lt0 := D.target.lawSin 0 1
  have lt2 := D.target.lawSin 2 1
  rw [hP0, hP1, h2α, tα] at lt0
  rw [hP2, hP1, h2β, t3α, tα] at lt2
  have hc : 0 < c := o2 ▸ D.model.oppLen_pos (σ 2)
  have hY : 0 < D.target.oppLen 1 := D.target.oppLen_pos 1
  set u := Real.sin (α / 2) with hudef
  set co := Real.cos (α / 2) with hcodef
  set X := D.target.oppLen 0 with hXdef
  set Y := D.target.oppLen 1 with hYdef
  set Z := D.target.oppLen 2 with hZdef
  have hucpos : 0 < 2 * u * co := by positivity
  have ha : a = 2 * u * c :=
    mul_left_cancel₀ hco.ne' (by linear_combination (-1 : ℝ) * ls1)
  have hb : b = (1 - 4 * u ^ 2) * c :=
    mul_left_cancel₀ hco.ne' (by linear_combination (-1 : ℝ) * ls2)
  have hXY : X = (2 - 4 * u ^ 2) * Y :=
    mul_left_cancel₀ hucpos.ne' (by linear_combination (-1 : ℝ) * lt0)
  have hZY : Z = (3 - 4 * u ^ 2) * (1 - 4 * u ^ 2) * Y :=
    mul_left_cancel₀ hucpos.ne' (by linear_combination (-1 : ℝ) * lt2)
  set s := 2 * u with hsdef
  have hs0 : 0 < s := by linarith
  have hs1 : s < 1 := by linarith
  have hfac : 0 < (2 - s) * (1 + s) := mul_pos (by linarith) (by linarith)
  have hSY : (S : ℝ) * c = (1 - s) * (2 + s) * Y := by
    have e : ((2 - s) * (1 + s)) * ((S : ℝ) * c - (1 - s) * (2 + s) * Y) = 0 := by
      rw [ha, hb, hXY, hZY] at hSe
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
  rw [Fin.sum_univ_three, Fin.sum_univ_three, ← hXdef, ← hYdef, ← hZdef, hXY, hZY] at hT
  rw [ha, hb] at hMo
  have hG : 0 < s ^ 2 * (2 - s) * (1 - s) ^ 2 * (1 + s) ^ 2 * (2 + s) := by
    have e1 : 0 < (1 - s) ^ 2 := pow_pos (by linarith) 2
    have e2 : 0 < (1 + s) ^ 2 := pow_pos (by linarith) 2
    have e3 : 0 < s ^ 2 := pow_pos hs0 2
    have h1 : 0 < 2 - s := by linarith
    have h2 : 0 < 2 + s := by linarith
    exact mul_pos (mul_pos (mul_pos (mul_pos e3 h1) e1) e2) h2
  have hg : 0 < (2 - s ^ 2) * (3 - s ^ 2) := by
    have : s ^ 2 < 1 := by nlinarith
    exact mul_pos (by linarith) (by linarith)
  have key : (s ^ 2 * (2 - s) * (1 - s) ^ 2 * (1 + s) ^ 2 * (2 + s)) *
      ((Y ^ 2 * ((2 - s ^ 2) * (3 - s ^ 2)) - N * c ^ 2) *
        (Y ^ 2 * ((2 - s ^ 2) * (3 - s ^ 2)) + N * c ^ 2)) = 0 := by
    rw [hsdef]
    linear_combination (-1 : ℝ) * hT + (N : ℝ) ^ 2 * hMo + 4 * hsq
  have hsum : 0 < Y ^ 2 * ((2 - s ^ 2) * (3 - s ^ 2)) + N * c ^ 2 :=
    add_pos_of_pos_of_nonneg (mul_pos (pow_pos hY 2) hg)
      (mul_nonneg (Nat.cast_nonneg N) (sq_nonneg c))
  have hArea : Y ^ 2 * ((2 - s ^ 2) * (3 - s ^ 2)) = N * c ^ 2 := by
    rcases mul_eq_zero.mp key with e | e
    · exact absurd e hG.ne'
    · rcases mul_eq_zero.mp e with e' | e'
      · linarith
      · exact absurd e' hsum.ne'
  have hfin : c ^ 2 * ((N : ℝ) * ((1 - s) * (2 + s)) ^ 2
      - (S : ℝ) ^ 2 * ((2 - s ^ 2) * (3 - s ^ 2))) = 0 := by
    linear_combination (-((1 - s) * (2 + s)) ^ 2) * hArea
      - ((2 - s ^ 2) * (3 - s ^ 2)) * ((S : ℝ) * c + (1 - s) * (2 + s) * Y) * hSY
  refine ⟨s, S, hs0, hs1, hc, ?_, ?_, ?_, ?_, hSY, ?_⟩
  · rw [ha]
  · rw [hb]; ring
  · rw [hXY]; ring
  · rw [hZY]; ring
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hfin).resolve_left (pow_pos hc 2).ne')

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row15.setup
