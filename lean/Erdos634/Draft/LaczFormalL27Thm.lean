import Erdos634.Draft.LaczFormalL27Ex2

/-!
# Laczkovich Theorem 2.4, triples 2, 3, 5: angle facts of the explicit triangles

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.4, Fig. 5), Beeson, Beeson-Zhang, Zhang.
-/

namespace Erdos634.LaczL27

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL24 Erdos634.LaczL26 EuclideanGeometry

/-- chart image of the point `(s, t)`. -/
noncomputable abbrev cp (w d : Plane) (hdet : w 0 * d 1 - w 1 * d 0 ≠ 0) (s t : ℝ) : Plane :=
  chartEquiv 0 w d hdet (mkPt s t)

theorem ang_axis' (w d : Plane) (hdet : w 0 * d 1 - w 1 * d 0 ≠ 0) (p : Plane) {x s l : ℝ} (t : ℝ)
    (hl : l - x ≠ 0) (hpos : 0 < (s - x) / (l - x)) :
    ∠ p (cp w d hdet x t) (cp w d hdet s t) = ∠ p (cp w d hdet x t) (cp w d hdet l t) :=
  ang_axis w d hdet p t hpos (div_mul_cancel₀ _ hl).symm

theorem ang_line' (w d : Plane) (hdet : w 0 * d 1 - w 1 * d 0 ≠ 0) (e1 e2 : ℝ) (p : Plane) {x s l : ℝ}
    (hl : l - x ≠ 0) (hpos : 0 < (s - x) / (l - x)) :
    ∠ p (chartEquiv 0 w d hdet (mkPt (0 + x * e1) (0 + x * e2))) (chartEquiv 0 w d hdet (mkPt (0 + s * e1) (0 + s * e2)))
      = ∠ p (chartEquiv 0 w d hdet (mkPt (0 + x * e1) (0 + x * e2))) (chartEquiv 0 w d hdet (mkPt (0 + l * e1) (0 + l * e2))) :=
  ang_line w d hdet e1 e2 p hpos (div_mul_cancel₀ _ hl).symm

theorem ratio_pos_of {s x l : ℝ} (h : 0 < (s - x) * (l - x)) : 0 < (s - x) / (l - x) := by
  have hl : l - x ≠ 0 := fun h0 => by rw [h0] at h; simp at h
  have : (s - x) / (l - x) = ((s - x) * (l - x)) / (l - x) ^ 2 := by field_simp
  rw [this]; positivity

section main

variable (R : RTri) (a0 : ℚ) (ha0 : 0 < a0) (ha1 : a0 < 1)
  (hA : R.a = a0 * R.c) (hB : R.b = (1 - a0 ^ 2) * R.c)
  (hN : T4RSD R a0 ha0 ha1) (w1 d1 : Plane) (hdet : w1 0 * d1 1 - w1 1 * d1 0 ≠ 0)
  (hw : inner ℝ w1 w1 = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2)
  (hd : inner ℝ d1 d1 = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2)
  (hwd : inner ℝ w1 d1 = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2 * (2 - (a0 : ℝ) ^ 2) / 2)

include ha0 ha1 hA hB hN hdet hw hd hwd

/-- Tile `P X L` (`α` at `P`, `β` at `X`). -/
theorem angles_tileL :
    ∠ (cp w1 d1 hdet (xL (a0 : ℝ)) 0) (cp w1 d1 hdet (sP (a0 : ℝ)) (tP (a0 : ℝ))) (cp w1 d1 hdet 0 0)
        = ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) ∧
      ∠ (cp w1 d1 hdet (sP (a0 : ℝ)) (tP (a0 : ℝ))) (cp w1 d1 hdet (xL (a0 : ℝ)) 0) (cp w1 d1 hdet 0 0)
        = ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) := by
  have hyp := hyp0_of_q a0 ha0 ha1
  obtain ⟨k, hk, hkr⟩ := tile_rat a0 ha0 ha1
  have hb : gb (a0 : ℝ) ≠ 0 := hyp.hb.ne'
  have hkpos : 0 < kk (a0 : ℝ) := by rw [← hkr]; exact_mod_cast hk
  exact tile_angles R a0 ha0 ha1 hA hB w1 d1 hdet hw hd hwd (sP (a0 : ℝ)) (tP (a0 : ℝ)) (xL (a0 : ℝ)) 0 0 0 _ hkpos
    (idp_L01 hb) (idp_L12 hb) (idp_L20 hb)

/-- Tile `P Y R` (`α` at `P`, `β` at `Y`). -/
theorem angles_tileR :
    ∠ (cp w1 d1 hdet (xY (a0 : ℝ)) 0) (cp w1 d1 hdet (sP (a0 : ℝ)) (tP (a0 : ℝ))) (cp w1 d1 hdet (sR (a0 : ℝ)) 0)
        = ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) ∧
      ∠ (cp w1 d1 hdet (sP (a0 : ℝ)) (tP (a0 : ℝ))) (cp w1 d1 hdet (xY (a0 : ℝ)) 0) (cp w1 d1 hdet (sR (a0 : ℝ)) 0)
        = ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) := by
  have hyp := hyp0_of_q a0 ha0 ha1
  obtain ⟨k, hk, hkr⟩ := tile_rat a0 ha0 ha1
  have hb : gb (a0 : ℝ) ≠ 0 := hyp.hb.ne'
  have hkpos : 0 < kk (a0 : ℝ) := by rw [← hkr]; exact_mod_cast hk
  exact tile_angles R a0 ha0 ha1 hA hB w1 d1 hdet hw hd hwd (sP (a0 : ℝ)) (tP (a0 : ℝ)) (xY (a0 : ℝ)) 0 (sR (a0 : ℝ)) 0 _
    hkpos (idp_R01 hb) (idp_R12 hb) (idp_R20 hb)

/-- Tile `V A L` (`α` at `V`, `β` at `A`). -/
theorem angles_tile1 :
    ∠ (cp w1 d1 hdet (xY (a0 : ℝ)) 0) (cp w1 d1 hdet (vX (a0 : ℝ)) (vY (a0 : ℝ))) (cp w1 d1 hdet 0 0)
        = ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) := by
  have hyp := hyp0_of_q a0 ha0 ha1
  obtain ⟨k, hk, hkr⟩ := tile_rat1 a0 ha0 ha1
  have hb : gb (a0 : ℝ) ≠ 0 := hyp.hb.ne'
  have hkpos : 0 < k1 (a0 : ℝ) := by rw [← hkr]; exact_mod_cast hk
  exact (tile_angles R a0 ha0 ha1 hA hB w1 d1 hdet hw hd hwd (vX (a0 : ℝ)) (vY (a0 : ℝ)) (xY (a0 : ℝ)) 0 0 0 _ hkpos
    (id_V01 hb) (id_V12 hb) (id_V20 hb)).1

/-- **Fifth triple**: angles of `B5 = P X R`: `β` at `X`, `α + β` at `R`. -/
theorem fifth_angles :
    ∠ (cp w1 d1 hdet (sP (a0 : ℝ)) (tP (a0 : ℝ))) (cp w1 d1 hdet (xL (a0 : ℝ)) 0) (cp w1 d1 hdet (sR (a0 : ℝ)) 0)
        = ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) ∧
      ∠ (cp w1 d1 hdet (xL (a0 : ℝ)) 0) (cp w1 d1 hdet (sR (a0 : ℝ)) 0) (cp w1 d1 hdet (sP (a0 : ℝ)) (tP (a0 : ℝ)))
        = ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) + ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) := by
  have hyp := hyp0_of_q a0 ha0 ha1
  have hxl := xL_neg hyp
  have hsr := sR_pos hyp
  constructor
  · rw [ang_axis' w1 d1 hdet _ 0 (x := xL (a0 : ℝ)) (s := sR (a0 : ℝ)) (l := 0) (ne_of_gt (by linarith))
      (ratio_pos_of (by nlinarith))]
    exact (angles_tileL R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd).2
  · rw [angle_comm, ang_axis' w1 d1 hdet _ 0 (x := sR (a0 : ℝ)) (s := xL (a0 : ℝ)) (l := 0) (ne_of_lt (by linarith))
      (ratio_pos_of (by nlinarith))]
    exact (T4_base R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd).2

/-- **Second triple**: angles of `B2 = P X Y`: `β` at `X` and at `Y`. -/
theorem second_angles :
    ∠ (cp w1 d1 hdet (sP (a0 : ℝ)) (tP (a0 : ℝ))) (cp w1 d1 hdet (xL (a0 : ℝ)) 0) (cp w1 d1 hdet (xY (a0 : ℝ)) 0)
        = ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) ∧
      ∠ (cp w1 d1 hdet (xL (a0 : ℝ)) 0) (cp w1 d1 hdet (xY (a0 : ℝ)) 0) (cp w1 d1 hdet (sP (a0 : ℝ)) (tP (a0 : ℝ)))
        = ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) := by
  have hyp := hyp0_of_q a0 ha0 ha1
  have hxl := xL_neg hyp
  have hsr := sR_pos hyp
  have hsy := sR_lt_xY hyp
  constructor
  · rw [ang_axis' w1 d1 hdet _ 0 (x := xL (a0 : ℝ)) (s := xY (a0 : ℝ)) (l := 0) (ne_of_gt (by linarith))
      (ratio_pos_of (by nlinarith))]
    exact (angles_tileL R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd).2
  · rw [angle_comm, ang_axis' w1 d1 hdet _ 0 (x := xY (a0 : ℝ)) (s := xL (a0 : ℝ)) (l := sR (a0 : ℝ))
      (ne_of_lt (by linarith)) (ratio_pos_of (by nlinarith))]
    exact (angles_tileR R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd).2



end main

theorem cp_P (w d : Plane) (hdet : w 0 * d 1 - w 1 * d 0 ≠ 0) (a : ℝ) :
    cp w d hdet (sP a) (tP a) = chartEquiv 0 w d hdet (mkPt (0 + -gK a * gb a) (0 + -gK a * -1)) := by
  have : mkPt (0 + -gK a * gb a) (0 + -gK a * -1) = mkPt (sP a) (tP a) := by
    congr 1 <;> (try simp only [sP, tP]) <;> ring
  rw [this]

theorem cp_V (w d : Plane) (hdet : w 0 * d 1 - w 1 * d 0 ≠ 0) (a : ℝ) :
    cp w d hdet (vX a) (vY a) = chartEquiv 0 w d hdet (mkPt (0 + cL a * gb a) (0 + cL a * -1)) := by
  have : mkPt (0 + cL a * gb a) (0 + cL a * -1) = mkPt (vX a) (vY a) := by
    congr 1 <;> (try simp only [cL, vX, vY]) <;> ring
  rw [this]

theorem cp_L (w d : Plane) (hdet : w 0 * d 1 - w 1 * d 0 ≠ 0) (a : ℝ) :
    cp w d hdet 0 0 = chartEquiv 0 w d hdet (mkPt (0 + 0 * gb a) (0 + 0 * -1)) := by
  have : mkPt (0 + 0 * gb a) (0 + 0 * -1) = mkPt 0 0 := by congr 1 <;> ring
  rw [this]

theorem cp_ne (w d : Plane) (hdet : w 0 * d 1 - w 1 * d 0 ≠ 0) {s s' : ℝ} (t t' : ℝ) (h : s ≠ s') :
    cp w d hdet s t ≠ cp w d hdet s' t' := by
  intro he
  have := (chartEquiv 0 w d hdet).injective he
  apply h
  have h0 := congrArg (fun z : Plane => z 0) this
  simpa using h0

section main3

variable (R : RTri) (a0 : ℚ) (ha0 : 0 < a0) (ha1 : a0 < 1)
  (hA : R.a = a0 * R.c) (hB : R.b = (1 - a0 ^ 2) * R.c)
  (hN : T4RSD R a0 ha0 ha1) (w1 d1 : Plane) (hdet : w1 0 * d1 1 - w1 1 * d1 0 ≠ 0)
  (hw : inner ℝ w1 w1 = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2)
  (hd : inner ℝ d1 d1 = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2)
  (hwd : inner ℝ w1 d1 = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2 * (2 - (a0 : ℝ) ^ 2) / 2)

include ha0 ha1 hA hB hN hdet hw hd hwd

/-- **Third triple**: angles of `B3 = A P V`: `α` at `V` and `α + α` at `P`. -/
theorem third_angles :
    ∠ (cp w1 d1 hdet (xY (a0 : ℝ)) 0) (cp w1 d1 hdet (sP (a0 : ℝ)) (tP (a0 : ℝ))) (cp w1 d1 hdet (vX (a0 : ℝ)) (vY (a0 : ℝ)))
        = ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) + ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) ∧
      ∠ (cp w1 d1 hdet (sP (a0 : ℝ)) (tP (a0 : ℝ))) (cp w1 d1 hdet (vX (a0 : ℝ)) (vY (a0 : ℝ))) (cp w1 d1 hdet (xY (a0 : ℝ)) 0)
        = ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) := by
  have hyp := hyp0_of_q a0 ha0 ha1
  have hxl := xL_neg hyp
  have hsr := sR_pos hyp
  have hsy := sR_lt_xY hyp
  have hxy := xY_pos hyp
  have hK := hyp.hK
  have hcpos : 0 < cL (a0 : ℝ) := by
    have := hyp.hb; unfold cL; unfold gb at *; unfold gK at *; positivity
  have hrel := tile_relation R a0 ha0 ha1 hA hB
  have tL := angles_tileL R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd
  have tR := angles_tileR R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd
  have t1 := angles_tile1 R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd
  have t4 := T4_base R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd
  constructor
  · -- angle at P
    have hAL : cp w1 d1 hdet (xY (a0 : ℝ)) 0 ≠ cp w1 d1 hdet 0 0 := cp_ne w1 d1 hdet 0 0 hxy.ne'
    have hsum := angle_add_angle_add_angle_eq_pi (cp w1 d1 hdet (sP (a0 : ℝ)) (tP (a0 : ℝ))) (p₁ := cp w1 d1 hdet 0 0)
      (p₂ := cp w1 d1 hdet (xY (a0 : ℝ)) 0) hAL
    -- ∠ L A P = β
    have hLAP : ∠ (cp w1 d1 hdet 0 0) (cp w1 d1 hdet (xY (a0 : ℝ)) 0) (cp w1 d1 hdet (sP (a0 : ℝ)) (tP (a0 : ℝ)))
        = ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) := by
      rw [angle_comm, ang_axis' w1 d1 hdet _ 0 (x := xY (a0 : ℝ)) (s := 0) (l := sR (a0 : ℝ)) (ne_of_lt (by linarith))
        (ratio_pos_of (by nlinarith))]
      exact tR.2
    -- ∠ P L A = α + β
    have hPLA : ∠ (cp w1 d1 hdet (sP (a0 : ℝ)) (tP (a0 : ℝ))) (cp w1 d1 hdet 0 0) (cp w1 d1 hdet (xY (a0 : ℝ)) 0)
        = ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) + ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) := by
      rw [ang_axis' w1 d1 hdet _ 0 (x := 0) (s := xY (a0 : ℝ)) (l := sR (a0 : ℝ)) (ne_of_gt (by linarith))
        (ratio_pos_of (by nlinarith))]
      exact t4.1
    have hAPL : ∠ (cp w1 d1 hdet (xY (a0 : ℝ)) 0) (cp w1 d1 hdet (sP (a0 : ℝ)) (tP (a0 : ℝ))) (cp w1 d1 hdet 0 0)
        = ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) + ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) := by
      rw [hLAP, hPLA] at hsum
      linarith
    rw [cp_P w1 d1 hdet (a0 : ℝ), cp_V w1 d1 hdet (a0 : ℝ)]
    rw [cp_P w1 d1 hdet (a0 : ℝ), cp_L w1 d1 hdet (a0 : ℝ)] at hAPL
    rw [ang_line' w1 d1 hdet (gb (a0 : ℝ)) (-1) _ (x := -gK (a0 : ℝ)) (s := cL (a0 : ℝ)) (l := 0)
      (ne_of_gt (by linarith)) (ratio_pos_of (by nlinarith))]
    exact hAPL
  · -- angle at V
    rw [angle_comm, cp_P w1 d1 hdet (a0 : ℝ), cp_V w1 d1 hdet (a0 : ℝ)]
    rw [ang_line' w1 d1 hdet (gb (a0 : ℝ)) (-1) _ (x := cL (a0 : ℝ)) (s := -gK (a0 : ℝ)) (l := 0)
      (ne_of_lt (by linarith)) (ratio_pos_of (by nlinarith))]
    rw [← cp_V w1 d1 hdet (a0 : ℝ), ← cp_L w1 d1 hdet (a0 : ℝ)] 
    exact t1

end main3

end Erdos634.LaczL27
