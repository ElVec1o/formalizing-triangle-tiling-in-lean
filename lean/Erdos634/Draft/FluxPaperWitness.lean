-- Draft/FluxPaperWitness.lean — NON-VACUITY WITNESS for `Paper.lem_value_alpha/beta` and
-- `Paper.cor_int` (Draft/FluxPaper.lean).  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- * `T357`: the `2π/3` triangle with sides `(a, b, c) = (3, 5, 7)`, vertices `A = (5, 0)` (angle α),
--   `B = (−3/2, 3√3/2)` (angle β = π/3 − α), `C = (0, 0)` (angle 2π/3).  `cos α = 13/14`, so
--   `α ∉ ℚπ` by Niven (`niven`).  All hypotheses of `Paper.lem_value_alpha/beta` hold.
-- * `D357`: `Subdivision.ladderDissection` of `2·T357` into `4` copies of `T357` — a genuine
--   `CongruentDissection 4` (edge-to-edge; the only `2π/3` dissection with a Lean witness in the
--   corpus).  All hypotheses of `Paper.cor_int` hold.  The corpus has NO non-edge-to-edge `2π/3`
--   tiling in Lean (the certified 28/44/77/99 tilings are `3α+2β = π` tiles).
-- `cos_cornerAngle'`/`cornerAngle_mem'` duplicate this room's `FluxGridWitness.cos_cornerAngle`
-- /`cornerAngle_mem` (to avoid importing the 44-tiling here).
import Erdos634.Draft.FluxPaper
import Erdos634.CellCoord
import Erdos634.CertCoord
import Mathlib.NumberTheory.Niven

open scoped Classical

namespace Erdos634.Draft.FluxPaperWitness

open Erdos634.Geometry Erdos634.CertCoord

theorem cos_cornerAngle' {p q r : Plane} (hp : p ≠ q) (hr : r ≠ q) :
    Real.cos (cornerAngle p q r)
      = (dist p q ^ 2 + dist r q ^ 2 - dist p r ^ 2) / (2 * dist p q * dist r q) := by
  have hlaw :=
    EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle p q r
  have h1 : 0 < dist p q := dist_pos.mpr hp
  have h2 : 0 < dist r q := dist_pos.mpr hr
  unfold cornerAngle
  rw [eq_div_iff (by positivity)]
  linear_combination hlaw

theorem cornerAngle_mem' (p q r : Plane) : 0 ≤ cornerAngle p q r ∧ cornerAngle p q r ≤ Real.pi :=
  ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩

theorem dist_eq_of_sq {x y : Plane} {s : ℝ} (hs : 0 ≤ s) (h : dist x y ^ 2 = s ^ 2) :
    dist x y = s :=
  (pow_left_inj₀ dist_nonneg hs two_ne_zero).mp h

theorem ne_of_dist' {p q : Plane} {c : ℝ} (h : dist p q = c) (hc : c ≠ 0) : p ≠ q := by
  rintro rfl; rw [dist_self] at h; exact hc h.symm

theorem det357 : det3 5 0 (-3/2) (3 * Real.sqrt 3 / 2) 0 0 ≠ 0 := by
  rw [show det3 5 0 (-3/2) (3 * Real.sqrt 3 / 2) 0 0 = 15 * Real.sqrt 3 / 2 by unfold det3; ring]
  have : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  positivity

/-- The `(3,5,7)` triangle: `A = (5,0)`, `B = (−3/2, 3√3/2)`, `C = (0,0)`. -/
noncomputable def T357 : Tri := mkTri 5 0 (-3/2) (3 * Real.sqrt 3 / 2) 0 0 det357

theorem s3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem d01 : dist (T357.pts 0) (T357.pts 1) = 7 := by
  apply dist_eq_of_sq (by norm_num)
  show dist (mkPt 5 0) (mkPt (-3/2) (3 * Real.sqrt 3 / 2)) ^ 2 = 7 ^ 2
  rw [dist_sq_mkPt]
  nlinarith [s3]

theorem d12 : dist (T357.pts 1) (T357.pts 2) = 3 := by
  apply dist_eq_of_sq (by norm_num)
  show dist (mkPt (-3/2) (3 * Real.sqrt 3 / 2)) (mkPt 0 0) ^ 2 = 3 ^ 2
  rw [dist_sq_mkPt]
  nlinarith [s3]

theorem d20 : dist (T357.pts 2) (T357.pts 0) = 5 := by
  apply dist_eq_of_sq (by norm_num)
  show dist (mkPt 0 0) (mkPt 5 0) ^ 2 = 5 ^ 2
  rw [dist_sq_mkPt]
  norm_num

/-- `α`: the angle at `A`. -/
noncomputable def α357 : ℝ := T357.angleAt 0

theorem cos_α357 : Real.cos α357 = 13 / 14 := by
  unfold α357 Tri.angleAt
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl]
  rw [cos_cornerAngle' (ne_of_dist' d01 (by norm_num)).symm (ne_of_dist' d20 (by norm_num)),
    dist_comm (T357.pts 1) (T357.pts 0), d01, d20, d12]
  norm_num

/-- `α ∉ ℚπ` (Niven: `13/14 ∉ {0, ±1/2, ±1}`). -/
theorem α357_irr : ¬ ∃ r : ℚ, α357 = (r : ℝ) * Real.pi := by
  intro hr
  have hmem := niven hr ⟨13 / 14, by rw [cos_α357]; norm_num⟩
  rw [cos_α357] at hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h | h | h <;> norm_num at h

theorem angle2_357 : T357.angleAt 2 = 2 * Real.pi / 3 := by
  have hcos : Real.cos (T357.angleAt 2) = -1 / 2 := by
    unfold Tri.angleAt
    simp only [show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
    rw [cos_cornerAngle' (ne_of_dist' d20 (by norm_num)).symm (ne_of_dist' d12 (by norm_num)),
      dist_comm (T357.pts 0) (T357.pts 2), d20, d12, d01]
    norm_num
  have hc : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three]
    norm_num
  have hpi := Real.pi_pos
  exact Real.injOn_cos (cornerAngle_mem' _ _ _) ⟨by positivity, by linarith⟩ (hcos.trans hc.symm)

theorem angle1_357 : T357.angleAt 1 = Real.pi / 3 - α357 := by
  have h := T357.angleAt_sum
  rw [angle2_357] at h
  unfold α357
  linarith

theorem opp_357 : T357.oppLen 0 = 3 ∧ T357.oppLen 1 = 5 ∧ T357.oppLen 2 = 7 := by
  unfold Tri.oppLen
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl,
    show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl,
    show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
  exact ⟨d12, d20, d01⟩

/-- **The hypothesis of `lem:value` holds for `T357`** (identity vertex order). -/
theorem data357 : T357.TwoPiThreeData α357 3 5 7 :=
  ⟨Equiv.refl _, rfl, opp_357.1, angle1_357, opp_357.2.1, angle2_357, opp_357.2.2⟩

/-- `lem:value` instance: `C_{f_α}(T357) = ±(7 + 3 − 5) = ±5`. -/
theorem lem_value_357 :
    T357.flux (fAlpha α357 α357_irr).weight = 7 + 3 - 5
      ∨ T357.flux (fAlpha α357 α357_irr).weight = -(7 + 3 - 5) :=
  Paper.lem_value_alpha T357 α357_irr data357

/-- `lem:value` instance: `C_{f_β}(T357) = ±(7 + 5 − 3) = ±9`. -/
theorem lem_value_357_beta :
    T357.flux (fBeta α357 α357_irr).weight = 7 + 5 - 3
      ∨ T357.flux (fBeta α357 α357_irr).weight = -(7 + 5 - 3) :=
  Paper.lem_value_beta T357 α357_irr data357

/-- **A real `CongruentDissection 4` by the `(3,5,7)` tile**: the scale-2 ladder. -/
noncomputable def D357 : CongruentDissection (2 * 2) where
  toDissection := Erdos634.Subdivision.ladderDissection (mkPt 5 0)
    (mkPt (-3/2) (3 * Real.sqrt 3 / 2)) (mkPt 0 0) T357.indep 2 (by norm_num)
  model := T357
  tiles_congruent := fun n => (Erdos634.Subdivision.ladderDissection_congruent (mkPt 5 0)
    (mkPt (-3/2) (3 * Real.sqrt 3 / 2)) (mkPt 0 0) T357.indep 2 (by norm_num) n).symm

/-- **`cor:int` instance on `D357`**: all hypotheses exhibited. -/
theorem cor_int_357 : ∃ Mα Mβ : ℤ, (2 : ℤ) ∣ Mα - ((2 * 2 : ℕ) : ℤ) ∧ (2 : ℤ) ∣ Mβ - ((2 * 2 : ℕ) : ℤ) ∧
      D357.target.flux (fAlpha α357 α357_irr).weight = (Mα : ℝ) * (7 + 3 - 5) ∧
      D357.target.flux (fBeta α357 α357_irr).weight = (Mβ : ℝ) * (7 + 5 - 3) :=
  Paper.cor_int D357 α357_irr data357

end Erdos634.Draft.FluxPaperWitness

#print axioms Erdos634.Draft.FluxPaperWitness.lem_value_357
#print axioms Erdos634.Draft.FluxPaperWitness.cor_int_357
