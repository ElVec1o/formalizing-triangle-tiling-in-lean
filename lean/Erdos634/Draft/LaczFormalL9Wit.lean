-- Draft/LaczFormalL9Wit.lean -- WITNESS for `LaczFormalL9Gen.l9_generic`: a triangle with angles (pi/7, 2pi/7, 4pi/7) (exact denominator
-- n = 7, a prime >= 7), and its scale-2 ladder dissection (N = 4) whose target is similar to the tile.  Also the general lemma
-- `exists_tri_angles` (a triangle with prescribed angles alpha, beta).  UNAUDITED.
import Erdos634.Draft.LaczFormalL9Gen
import Erdos634.Draft.LaczFormalL6Wit1

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord Erdos634.TilePlacement Erdos634.Subdivision
  Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.FluxPaperWitness (cornerAngle_mem' dist_eq_of_sq cos_cornerAngle' ne_of_dist')

namespace Erdos634.Draft.LaczFormal

theorem exists_tri_angles {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hs : α + β < Real.pi) :
    ∃ T : Tri, T.angleAt 0 = α ∧ T.angleAt 1 = β := by
  have hpi := Real.pi_pos
  have sα : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα (by linarith)
  have sβ : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi hβ (by linarith)
  have sab : 0 < Real.sin (α + β) := Real.sin_pos_of_pos_of_lt_pi (by linarith) hs
  set s := Real.sin (α + β) with hsdef
  have hsexp : s = Real.sin α * Real.cos β + Real.cos α * Real.sin β := Real.sin_add α β
  set r := Real.sin β / s with hr
  have hrpos : 0 < r := div_pos sβ sab
  have pa := Real.sin_sq_add_cos_sq α
  have pb := Real.sin_sq_add_cos_sq β
  have hdet : det3 0 0 1 0 (r * Real.cos α) (r * Real.sin α) ≠ 0 := by
    rw [show det3 0 0 1 0 (r * Real.cos α) (r * Real.sin α) = r * Real.sin α by unfold det3; ring]
    positivity
  refine ⟨mkTri 0 0 1 0 (r * Real.cos α) (r * Real.sin α) hdet, ?_, ?_⟩
  · -- angle at A
    have d01 : dist (mkPt (1 : ℝ) 0) (mkPt 0 0) = 1 := by
      apply dist_eq_of_sq (by norm_num); rw [dist_sq_mkPt]; norm_num
    have d02 : dist (mkPt (r * Real.cos α) (r * Real.sin α)) (mkPt 0 0) = r := by
      apply dist_eq_of_sq hrpos.le; rw [dist_sq_mkPt]; nlinarith [pa]
    have d12 : dist (mkPt (1 : ℝ) 0) (mkPt (r * Real.cos α) (r * Real.sin α)) ^ 2
        = 1 + r ^ 2 - 2 * r * Real.cos α := by
      rw [dist_sq_mkPt]; nlinarith [pa]
    show cornerAngle (mkPt (1 : ℝ) 0) (mkPt 0 0) (mkPt (r * Real.cos α) (r * Real.sin α)) = α
    refine Real.injOn_cos (cornerAngle_mem' _ _ _) ⟨hα.le, by linarith⟩ ?_
    rw [cos_cornerAngle' (ne_of_dist' d01 (by norm_num)) (ne_of_dist' d02 hrpos.ne'), d01, d02, d12]
    field_simp; ring
  · -- angle at B
    have hBC2 : dist (mkPt (r * Real.cos α) (r * Real.sin α)) (mkPt 1 0) ^ 2
        = (Real.sin α / s) ^ 2 := by
      rw [dist_sq_mkPt]
      have : (r * Real.cos α - 1) ^ 2 + (r * Real.sin α - 0) ^ 2 = 1 + r ^ 2 - 2 * r * Real.cos α := by
        nlinarith [pa]
      rw [this, hr, div_pow, div_pow]
      field_simp
      rw [hsexp]; nlinarith [pa, pb]
    have dBC : dist (mkPt (r * Real.cos α) (r * Real.sin α)) (mkPt 1 0) = Real.sin α / s :=
      dist_eq_of_sq (div_pos sα sab).le hBC2
    have dBA : dist (mkPt (0 : ℝ) 0) (mkPt 1 0) = 1 := by
      apply dist_eq_of_sq (by norm_num); rw [dist_sq_mkPt]; norm_num
    have dCA : dist (mkPt (r * Real.cos α) (r * Real.sin α)) (mkPt 0 0) = r := by
      apply dist_eq_of_sq hrpos.le; rw [dist_sq_mkPt]; nlinarith [pa]
    show cornerAngle (mkPt (r * Real.cos α) (r * Real.sin α)) (mkPt (1 : ℝ) 0) (mkPt 0 0) = β
    refine Real.injOn_cos (cornerAngle_mem' _ _ _) ⟨hβ.le, by linarith⟩ ?_
    rw [cos_cornerAngle' (ne_of_dist' dBC (div_pos sα sab).ne') (ne_of_dist' dBA (by norm_num)), dBC, dBA]
    rw [dCA, hr]
    rw [div_eq_iff (by positivity)]
    field_simp
    rw [hsexp]
    first
      | linear_combination (Real.sin α ^ 2) * pb - (Real.sin β ^ 2) * pa
      | linear_combination (-(Real.sin α ^ 2)) * pb + (Real.sin β ^ 2) * pa
      | nlinarith [pa, pb]

/-- **Witness.** A real `CongruentDissection 4` (scale-2 ladder) of a triangle by a tile with angles `(1,2,4)·π/7`: all hypotheses of
`l9_generic` hold (n = 7, a = (1,2,4), gcd 1, prime 7), and its conclusion (target similar to tile) is true. -/
theorem l9_generic_witness :
    ∃ (N : ℕ) (D : CongruentDissection N) (n : ℕ) (a : Fin 3 → ℕ), 0 < n ∧
      (∀ k, D.model.angleAt k = a k * Real.pi / n) ∧
      Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 ∧ 7 ∣ n ∧ SimilarTM D := by
  have hpi := Real.pi_pos
  obtain ⟨T, h0, h1⟩ := exists_tri_angles (α := Real.pi / 7) (β := 2 * Real.pi / 7) (by positivity)
    (by positivity) (by linarith)
  have h2 : T.angleAt 2 = 4 * Real.pi / 7 := by
    have := angleAt_sum T; rw [h0, h1] at this; linarith
  have hpts : (![T.pts 0, T.pts 1, T.pts 2] : Fin 3 → Plane) = T.pts := by
    funext i; fin_cases i <;> rfl
  have hind : AffineIndependent ℝ ![T.pts 0, T.pts 1, T.pts 2] := by rw [hpts]; exact T.indep
  set Tm : Tri := ⟨![T.pts 0, T.pts 1, T.pts 2], hind⟩ with hTm
  have hang : ∀ k, Tm.angleAt k = T.angleAt k := by
    intro k
    have : Tm.pts = T.pts := hpts
    simp only [Tri.angleAt, this]
  let D : CongruentDissection (2 * 2) :=
    { toDissection := ladderDissection (T.pts 0) (T.pts 1) (T.pts 2) hind 2 (by norm_num)
      model := Tm
      tiles_congruent := fun n =>
        (ladderDissection_congruent (T.pts 0) (T.pts 1) (T.pts 2) hind 2 (by norm_num) n).symm }
  refine ⟨_, D, 7, ![1, 2, 4], by norm_num, ?_, by decide, by norm_num, ?_⟩
  · intro k
    show Tm.angleAt k = _
    rw [hang]
    fin_cases k
    · simp [h0]
    · simp [h1]
    · simp [h2]
  · refine ⟨2, 1, fun k => ⟨?_, ?_⟩⟩
    · show (bigTri (T.pts 0) (T.pts 1) (T.pts 2) hind 2 (by norm_num)).angleAt k = Tm.angleAt k
      rw [bigTri_angleAt]
    · show (bigTri (T.pts 0) (T.pts 1) (T.pts 2) hind 2 (by norm_num)).oppLen k = _
      rw [bigTri_oppLen]; norm_num; rfl

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.exists_tri_angles
#print axioms Erdos634.Draft.LaczFormal.l9_generic_witness
