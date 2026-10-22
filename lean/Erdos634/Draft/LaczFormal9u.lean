import Erdos634.Draft.LaczFormal9t
import Erdos634.Draft.LaczFormalL35Print

/-!
# Laczkovich DM 140 (1995), Theorem 2.3 AS PRINTED, and a witness

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.3, Fig. 3), Beeson (arXiv 1206.2229), Beeson-Zhang, Zhang.
Formalization debt, not /goal progress.

Printed Thm 2.3: let `T` be an isosceles triangle with angles `α, α, π - 2α`, `α < π/3` and `cos α` rational.  Then `T` can be dissected
into congruent triangles with angles `α, 2α, π - 3α`.  Lean: `thm23_printed` (angle hypothesis in the `HasAngles` form of
`LaczFormalL35Print`; the conclusion is `PrintedConcl`: a `CongruentDissection M` of a triangle with the carrier of `T`, whose model is
congruent to a triangle with angles `(α, 2α, π - 3α)`).  The construction is the one of Fig. 3, rendered from the printed page.
-/

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL21 Erdos634.Realizable
  Erdos634.LaczL35 Erdos634.LaczTransport Erdos634.LaczL28 Erdos634.DissectionMap EuclideanGeometry

namespace Erdos634.Laczkovich9u

open Erdos634.Laczkovich9r Erdos634.Laczkovich9t

/-- **Theorem 2.3 for every triangle with angle `α` at `T'₀` and at `T'₁`** (explicit form). -/
theorem thm23_any (R : RTri) (k : ℚ) (hk : (1 : ℚ) / 2 < k) (hk2 : k < 1)
    (hB : R.b = 2 * k * R.a) (hC : R.c = (4 * k ^ 2 - 1) * R.a) (T' : Tri)
    (h0 : cornerAngle (T'.pts 1) (T'.pts 0) (T'.pts 2)
      = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2))
    (h1 : cornerAngle (T'.pts 2) (T'.pts 1) (T'.pts 0)
      = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2)) :
    ∃ (s : ℝ) (hs : 0 < s) (M : ℕ) (D' : CongruentDissection M),
      D'.target.carrier = T'.carrier ∧ D'.model.Congruent (scaleTri s hs.ne' R.Δ) := by
  obtain ⟨T, q, hq, M, C, hC1, hC2, hang0, hang1⟩ := thm23_first R k hk hk2 hB hC
  obtain ⟨s, hs, D', e1, e2⟩ := transport_region R.Δ T q hq M C hC1 hC2 T' 2 0 1 (by decide) (by decide)
    (by decide)
    (by rw [angle_comm (T.pts 2) (T.pts 0) (T.pts 1), angle_comm (T'.pts 2) (T'.pts 0) (T'.pts 1)]
        exact hang0.trans h0.symm)
    (by rw [angle_comm (T.pts 0) (T.pts 1) (T.pts 2), angle_comm (T'.pts 0) (T'.pts 1) (T'.pts 2)]
        exact hang1.trans h1.symm)
  exact ⟨s, hs, M, D', e1, e2⟩

/-- The rational tile of Theorem 2.3: sides `a : b : c = 1 : 2 cos α : 4 cos² α - 1`. -/
theorem tile23 (α : ℝ) (h0 : 0 < α) (h1 : α < Real.pi / 3) (q : ℚ) (hq : Real.cos α = q) :
    ∃ (R : RTri) (k : ℚ), (1 : ℚ) / 2 < k ∧ k < 1 ∧ R.b = 2 * k * R.a ∧ R.c = (4 * k ^ 2 - 1) * R.a ∧
      vang R.Δ 0 = α ∧ vang R.Δ 1 = 2 * α ∧ vang R.Δ 2 = Real.pi - 3 * α := by
  have hpi := Real.pi_pos
  have hqhalf : (1 : ℝ) / 2 < q := by
    rw [← hq, ← Real.cos_pi_div_three]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) h1
  have hqone : (q : ℝ) < 1 := by
    rw [← hq, ← Real.cos_zero]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl _) (by linarith) h0
  have hq1 : (1 : ℚ) / 2 < q := by
    have : (((1 : ℚ) / 2 : ℚ) : ℝ) < q := by push_cast; exact hqhalf
    exact_mod_cast this
  have hq2 : q < 1 := by exact_mod_cast hqone
  obtain ⟨R, hRa, hRb, hRc⟩ := exists_RTri_rat 1 (2 * q) (4 * q ^ 2 - 1) one_pos (by linarith) (by nlinarith)
    (by nlinarith) (by nlinarith) (by nlinarith)
  have hcc : (0 : ℝ) < 4 * (q : ℝ) ^ 2 - 1 := by nlinarith
  have hq0 : (0 : ℝ) < q := by linarith
  have hcos2 : Real.cos (2 * α) = 2 * (q : ℝ) ^ 2 - 1 := by rw [Real.cos_two_mul, hq]
  have hR := RTri.angles_of R α (2 * α) h0 (by linarith) (by linarith)
    (by
      rw [hq, hRa, hRb, hRc]; push_cast
      rw [div_eq_iff (by apply ne_of_gt; nlinarith)]
      ring)
    (by
      rw [hcos2, hRa, hRb, hRc]; push_cast
      rw [div_eq_iff (by apply ne_of_gt; nlinarith)]
      ring)
  refine ⟨R, q, hq1, hq2, by rw [hRa, hRb]; ring, by rw [hRa, hRc]; ring, hR.1, hR.2.1, ?_⟩
  rw [hR.2.2]; ring

/-- **Laczkovich DM 140 (1995), Theorem 2.3, as printed.**  `0 < α < π/3`, `cos α` rational; a triangle `T` with angles
`(α, α, π - 2α)` is a union of finitely many congruent triangles with angles `(α, 2α, π - 3α)`. -/
theorem thm23_printed (α : ℝ) (h0 : 0 < α) (h1 : α < Real.pi / 3) (hq : ∃ q : ℚ, Real.cos α = q) (T : Tri)
    (hT : HasAngles T α α (Real.pi - 2 * α)) :
    PrintedConcl T α (2 * α) (Real.pi - 3 * α) := by
  obtain ⟨q, hq⟩ := hq
  obtain ⟨R, k, hk1, hk2, hB, hC, r0, r1, r2⟩ := tile23 α h0 h1 q hq
  obtain ⟨T', hc, e0, e1, e2⟩ := hT.canon
  have hd := thm23_any R k hk1 hk2 hB hC T' (e0.trans r0.symm) (e1.trans r0.symm)
  exact concl_of R α (2 * α) (Real.pi - 3 * α) r0 r1 r2 T T' hc hd

/-! ### Witness: `cos α = 3/4` (tile `(4, 6, 5)`), hypotheses satisfiable -/

theorem wit_tile_456 : ∃ R : RTri, R.a = 4 ∧ R.b = 6 ∧ R.c = 5 := by
  obtain ⟨R, a, b, c⟩ := exists_RTri_rat 4 6 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  exact ⟨R, a, b, c⟩

/-- The hypotheses of `thm23_first` are satisfied (`k = 3/4`, tile `(4, 6, 5)`), and the conclusion is obtained. -/
theorem wit_thm23_first :
    ∃ (R : RTri) (T : Tri) (q : ℕ) (hq : 0 < q) (M : ℕ)
      (C : Erdos634.RegionDissection.CongruentRegionDissection M),
      C.region = T.carrier ∧
      C.model = scaleTri (1 / (q : ℝ)) (one_div_pos.mpr (Nat.cast_pos.mpr hq)).ne' R.Δ := by
  obtain ⟨R, ha, hb, hc⟩ := wit_tile_456
  obtain ⟨T, q, hq, M, C, h1, h2, -, -⟩ := thm23_first R (3 / 4) (by norm_num) (by norm_num)
    (by rw [ha, hb]; norm_num) (by rw [ha, hc]; norm_num)
  exact ⟨R, T, q, hq, M, C, h1, h2⟩

end Erdos634.Laczkovich9u

#print axioms Erdos634.Laczkovich9u.thm23_printed
#print axioms Erdos634.Laczkovich9u.wit_thm23_first
