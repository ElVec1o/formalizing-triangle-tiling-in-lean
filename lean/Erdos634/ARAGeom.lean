import Erdos634.CongruentArea
import Erdos634.AreaDet
import Erdos634.BADFinal

/-!
# ARA: the area relation of a `CongruentDissection` in Heron form

Written 2026-10-03.  UNAUDITED.  `CongruentArea.congruentDissection_volume_target` (existing, no
hypotheses) gives `|target| = N |model|` in `ℝ≥0∞`.  Here: `4 det² = Hh(sides)` (Heron, square
roots cleared) and hence, for any `CongruentDissection N`,
`N² · Hh(model sides) = Hh(target sides)`  (`area_heron`), plus Heron's invariance under the
vertex relabelling (`Hh_perm`).
-/

namespace Erdos634.ARA
open Erdos634.Geometry MeasureTheory

noncomputable section

/-- `16 · Area²` of the triangle with side lengths `a b c`. -/
def Hh (a b c : ℝ) : ℝ := 2*a^2*b^2 + 2*b^2*c^2 + 2*c^2*a^2 - a^4 - b^4 - c^4

theorem dist_sq' (x y : Plane) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

theorem four_det_sq (T : Tri) :
    4 * Erdos634.AreaDet.detTri T ^ 2 = Hh (T.oppLen 0) (T.oppLen 1) (T.oppLen 2) := by
  have h0 : T.oppLen 0 = dist (T.pts 1) (T.pts 2) := rfl
  have h1 : T.oppLen 1 = dist (T.pts 2) (T.pts 0) := rfl
  have h2 : T.oppLen 2 = dist (T.pts 0) (T.pts 1) := rfl
  rw [Erdos634.AreaDet.detTri_eq, Hh, h0, h1, h2]
  have e0 := dist_sq' (T.pts 1) (T.pts 2)
  have e1 := dist_sq' (T.pts 2) (T.pts 0)
  have e2 := dist_sq' (T.pts 0) (T.pts 1)
  have q : ∀ x : ℝ, x ^ 4 = (x ^ 2) ^ 2 := fun x => by ring
  simp only [q, e0, e1, e2]
  simp only [PiLp.sub_apply]
  ring

theorem Hh_perm (T : Tri) (σ : Equiv.Perm (Fin 3)) :
    Hh (T.oppLen (σ 0)) (T.oppLen (σ 1)) (T.oppLen (σ 2)) =
      Hh (T.oppLen 0) (T.oppLen 1) (T.oppLen 2) := by
  have d1 : σ 0 ≠ σ 1 := fun h => by have := σ.injective h; simp at this
  have d2 : σ 0 ≠ σ 2 := fun h => by have := σ.injective h; simp at this
  have d3 : σ 1 ≠ σ 2 := fun h => by have := σ.injective h; simp at this
  rcases Erdos634.BADL2.perm3 _ _ _ d1 d2 d3 with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ |
    ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ <;>
  · rw [hx, hy, hz]; try (unfold Hh; ring)

/-- **Area relation in Heron form** (no hypotheses). -/
theorem area_heron {N : ℕ} (D : CongruentDissection N) :
    (N : ℝ) ^ 2 * Hh (D.model.oppLen 0) (D.model.oppLen 1) (D.model.oppLen 2) =
      Hh (D.target.oppLen 0) (D.target.oppLen 1) (D.target.oppLen 2) := by
  have hv := Erdos634.CongruentArea.congruentDissection_volume_target D
  rw [Erdos634.AreaDet.volume_eq_det_mul, Erdos634.AreaDet.volume_eq_det_mul] at hv
  have hM := D.model.volume_pos
  rw [Erdos634.AreaDet.volume_eq_det_mul] at hM
  have hc0 : volume Erdos634.AreaDet.stdCarrier ≠ 0 := by
    intro h; rw [h, mul_zero] at hM; exact lt_irrefl _ hM
  have hct : volume Erdos634.AreaDet.stdCarrier ≠ ⊤ :=
    (Erdos634.AreaDet.isCompact_stdCarrier.measure_lt_top).ne
  rw [← mul_assoc] at hv
  have h2 := (ENNReal.mul_left_inj hc0 hct).1 hv
  have h3 : ENNReal.ofReal |Erdos634.AreaDet.detTri D.target| =
      ENNReal.ofReal ((N : ℝ) * |Erdos634.AreaDet.detTri D.model|) := by
    rw [h2, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  have h4 := (ENNReal.ofReal_eq_ofReal_iff (abs_nonneg _) (by positivity)).1 h3
  rw [← four_det_sq, ← four_det_sq]
  have : Erdos634.AreaDet.detTri D.target ^ 2 =
      ((N : ℝ) * |Erdos634.AreaDet.detTri D.model|) ^ 2 := by
    rw [← h4, sq_abs]
  rw [this, mul_pow, sq_abs]; ring

end

end Erdos634.ARA

#print axioms Erdos634.ARA.area_heron
