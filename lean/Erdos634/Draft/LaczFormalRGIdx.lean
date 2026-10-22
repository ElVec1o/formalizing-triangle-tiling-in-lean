-- Draft/LaczFormalRGIdx.lean -- S4 of PLAN_THM21: an ANGLE-matching vertex correspondence of a congruent dissection is automatically DISTANCE-matching.
-- (Lengths of a triangle are determined by the law of sines from the angles; two correspondences with the same angles differ by a symmetry of the model's angles.)
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 2: "the angle of Delta_j at V_i is alpha, beta or gamma"), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRGCaseV

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

theorem sideOpp_law (M : Tri) (j : Fin 3) : sideOpp M j * Real.sin (angleAt M 0) = sideOpp M 0 * Real.sin (angleAt M j) := by
  fin_cases j
  · rfl
  · have := Erdos634.TriLawSin.sin_angleAt_mul_sideOpp M 0
    have e : (0 + 1 : Fin 3) = 1 := rfl
    rw [e] at this
    show sideOpp M 1 * Real.sin (angleAt M 0) = sideOpp M 0 * Real.sin (angleAt M 1)
    linarith
  · have := Erdos634.TriLawSin.sin_angleAt_mul_sideOpp M 2
    have e : (2 + 1 : Fin 3) = 0 := rfl
    rw [e] at this
    show sideOpp M 2 * Real.sin (angleAt M 0) = sideOpp M 0 * Real.sin (angleAt M 2)
    linarith

theorem dist_eq_sideOpp (M : Tri) (x y z : Fin 3) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    dist (M.pts x) (M.pts y) = sideOpp M z := by
  unfold sideOpp
  fin_cases x <;> fin_cases y <;> fin_cases z <;> simp_all <;> first | rfl | exact dist_comm _ _

theorem fin3_third_exists : ∀ x y : Fin 3, x ≠ y → ∃ z : Fin 3, x ≠ z ∧ y ≠ z := by decide

theorem model_dist_of_angles (M : Tri) (x y x' y' : Fin 3) (hxy : x ≠ y) (hxy' : x' ≠ y')
    (hx : angleAt M x = angleAt M x') (hy : angleAt M y = angleAt M y') :
    dist (M.pts x) (M.pts y) = dist (M.pts x') (M.pts y') := by
  -- third vertices
  obtain ⟨z, hxz, hyz⟩ := fin3_third_exists x y hxy
  obtain ⟨z', hxz', hyz'⟩ := fin3_third_exists x' y' hxy'
  rw [dist_eq_sideOpp M x y z hxy hxz hyz, dist_eq_sideOpp M x' y' z' hxy' hxz' hyz']
  have hs : angleAt M 0 + angleAt M 1 + angleAt M 2 = Real.pi := Erdos634.Draft.LaczFormal.angleAt_sum M
  -- angle at z is pi - angle x - angle y
  have hz : angleAt M z = Real.pi - angleAt M x - angleAt M y := by
    have : ∀ x y z : Fin 3, x ≠ y → x ≠ z → y ≠ z → angleAt M x + angleAt M y + angleAt M z = Real.pi := by
      intro x y z h1 h2 h3
      fin_cases x <;> fin_cases y <;> fin_cases z <;> simp_all <;> linarith
    have := this x y z hxy hxz hyz
    linarith
  have hz' : angleAt M z' = Real.pi - angleAt M x' - angleAt M y' := by
    have : ∀ x y z : Fin 3, x ≠ y → x ≠ z → y ≠ z → angleAt M x + angleAt M y + angleAt M z = Real.pi := by
      intro x y z h1 h2 h3
      fin_cases x <;> fin_cases y <;> fin_cases z <;> simp_all <;> linarith
    have := this x' y' z' hxy' hxz' hyz'
    linarith
  have hzz : angleAt M z = angleAt M z' := by rw [hz, hz', hx, hy]
  have h0 := Erdos634.Draft.LaczFormal.Thm21.sin_angleAt_pos M 0
  have l1 := sideOpp_law M z
  have l2 := sideOpp_law M z'
  rw [hzz] at l1
  apply mul_right_cancel₀ h0.ne'
  rw [l1, l2]

/-- **Angle-matching implies distance-matching.** -/
theorem idx_dist_of_angle (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hA : ∀ i v, angleAt D.model (idx i v) = angleAt (D.tile i) v) :
    ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')) := by
  obtain ⟨σ, hσd, hσa⟩ := exists_idx_both D
  intro i k k'
  by_cases hkk : k = k'
  · subst hkk; simp
  · rw [hσd i k k']
    apply model_dist_of_angles D.model (σ i k) (σ i k') (idx i k) (idx i k')
      (fun h => hkk ((σ i).injective h)) (fun h => hkk ((idx i).injective h))
    · rw [hσa i k, hA i k]
    · rw [hσa i k', hA i k']

end Erdos634.Draft.LaczFormal.RG
