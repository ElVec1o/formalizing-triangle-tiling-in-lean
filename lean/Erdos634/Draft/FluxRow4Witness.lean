-- Draft/FluxRow4Witness.lean — NON-VACUITY WITNESS for `Row4.flux_signs` (Draft/FluxRow4.lean):
-- the `γ = 2α` tile `(a, b, c) = (4, 5, 6)` (`cos α = 3/4`, `cos 2α = 1/8`; `α ∉ ℚπ` by Niven) and
-- its scale-2 ladder, a real `CongruentDissection 4`.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
-- `Row4.invariants`' target-shape hypotheses (base-α target) are NOT witnessed here or anywhere
-- in the corpus (DESIGN.md §5).
-- `cos_cornerAngle'`, `cornerAngle_mem'`, `dist_eq_of_sq`, `ne_of_dist'` are reused from this
-- room's `FluxPaperWitness`.
import Erdos634.Draft.FluxRow4
import Erdos634.Draft.FluxPaperWitness

open scoped Classical

namespace Erdos634.Draft.FluxRow4Witness

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.FluxPaperWitness

theorem det456 : det3 0 0 6 0 (15/4) (5 * Real.sqrt 7 / 4) ≠ 0 := by
  rw [show det3 0 0 6 0 (15/4) (5 * Real.sqrt 7 / 4) = 30 * Real.sqrt 7 / 4 by unfold det3; ring]
  have : 0 < Real.sqrt 7 := Real.sqrt_pos.mpr (by norm_num)
  positivity

/-- The `(4,5,6)` triangle: `A = (0,0)` (angle α), `B = (6,0)` (angle π − 3α),
`C = (15/4, 5√7/4)` (angle 2α). -/
noncomputable def T456 : Tri := mkTri 0 0 6 0 (15/4) (5 * Real.sqrt 7 / 4) det456

theorem s7 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)

theorem e01 : dist (T456.pts 0) (T456.pts 1) = 6 := by
  apply dist_eq_of_sq (by norm_num)
  show dist (mkPt 0 0) (mkPt 6 0) ^ 2 = 6 ^ 2
  rw [dist_sq_mkPt]; norm_num

theorem e12 : dist (T456.pts 1) (T456.pts 2) = 4 := by
  apply dist_eq_of_sq (by norm_num)
  show dist (mkPt 6 0) (mkPt (15/4) (5 * Real.sqrt 7 / 4)) ^ 2 = 4 ^ 2
  rw [dist_sq_mkPt]; nlinarith [s7]

theorem e20 : dist (T456.pts 2) (T456.pts 0) = 5 := by
  apply dist_eq_of_sq (by norm_num)
  show dist (mkPt (15/4) (5 * Real.sqrt 7 / 4)) (mkPt 0 0) ^ 2 = 5 ^ 2
  rw [dist_sq_mkPt]; nlinarith [s7]

noncomputable def α456 : ℝ := T456.angleAt 0

theorem cos_α456 : Real.cos α456 = 3 / 4 := by
  unfold α456 Tri.angleAt
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl]
  rw [cos_cornerAngle' (ne_of_dist' e01 (by norm_num)).symm (ne_of_dist' e20 (by norm_num)),
    dist_comm (T456.pts 1) (T456.pts 0), e01, e20, e12]
  norm_num

theorem α456_irr : ¬ ∃ r : ℚ, α456 = (r : ℝ) * Real.pi := by
  intro hr
  have hmem := niven hr ⟨3 / 4, by rw [cos_α456]; norm_num⟩
  rw [cos_α456] at hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h | h | h <;> norm_num at h

theorem angle2_456 : T456.angleAt 2 = 2 * α456 := by
  have hcos : Real.cos (T456.angleAt 2) = 1 / 8 := by
    unfold Tri.angleAt
    simp only [show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
    rw [cos_cornerAngle' (ne_of_dist' e20 (by norm_num)).symm (ne_of_dist' e12 (by norm_num)),
      dist_comm (T456.pts 0) (T456.pts 2), e20, e12, e01]
    norm_num
  have hc2 : Real.cos (2 * α456) = 1 / 8 := by rw [Real.cos_two_mul, cos_α456]; norm_num
  have hα0 : 0 ≤ α456 := (cornerAngle_mem' _ _ _).1
  have hαπ : α456 ≤ Real.pi := (cornerAngle_mem' _ _ _).2
  have hle : α456 ≤ Real.pi / 2 := by
    by_contra h
    push Not at h
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity : (0:ℝ) ≤ Real.pi / 2) hαπ h
    rw [Real.cos_pi_div_two, cos_α456] at this
    norm_num at this
  exact Real.injOn_cos (cornerAngle_mem' _ _ _) ⟨by linarith, by linarith⟩ (hcos.trans hc2.symm)

theorem angle1_456 : T456.angleAt 1 = Real.pi - 3 * α456 := by
  have h := T456.angleAt_sum
  rw [angle2_456] at h
  unfold α456 at h ⊢
  linarith

theorem opp_456 : T456.oppLen 0 = 4 ∧ T456.oppLen 1 = 5 ∧ T456.oppLen 2 = 6 := by
  unfold Tri.oppLen
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl,
    show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl,
    show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
  exact ⟨e12, e20, e01⟩

theorem data456 : T456.TwoAlphaData α456 4 5 6 :=
  ⟨Equiv.refl _, rfl, opp_456.1, angle1_456, opp_456.2.1, angle2_456, opp_456.2.2⟩

/-- The scale-2 ladder of the `(4,5,6)` tile: a real `CongruentDissection 4`. -/
noncomputable def D456 : CongruentDissection (2 * 2) where
  toDissection := Erdos634.Subdivision.ladderDissection (mkPt 0 0) (mkPt 6 0)
    (mkPt (15/4) (5 * Real.sqrt 7 / 4)) T456.indep 2 (by norm_num)
  model := T456
  tiles_congruent := fun n => (Erdos634.Subdivision.ladderDissection_congruent (mkPt 0 0)
    (mkPt 6 0) (mkPt (15/4) (5 * Real.sqrt 7 / 4)) T456.indep 2 (by norm_num) n).symm

/-- **`Row4.flux_signs` on a real dissection: all hypotheses exhibited.** -/
theorem flux_signs_456 : ∃ S₁ S₂ : ℤ, (2 : ℤ) ∣ S₁ - ((2 * 2 : ℕ) : ℤ)
    ∧ (2 : ℤ) ∣ S₂ - ((2 * 2 : ℕ) : ℤ) ∧ |S₁| ≤ ((2 * 2 : ℕ) : ℤ) ∧ |S₂| ≤ ((2 * 2 : ℕ) : ℤ) ∧
    D456.target.flux (GridChar.rank2 α456 α456_irr 0 0).weight = (S₁ : ℝ) * (4 + 6 - 5) ∧
    D456.target.flux (GridChar.rank2 α456 α456_irr 1 0).weight = (S₂ : ℝ) * (5 + 6 - 4) :=
  Row4.flux_signs D456 α456_irr data456

end Erdos634.Draft.FluxRow4Witness

#print axioms Erdos634.Draft.FluxRow4Witness.flux_signs_456
