import Erdos634.Draft.ZhangRat7Int
import Erdos634.Draft.ZhangRat4Angles
import Erdos634.TriLawSin

/-!
# Zhang Lemma 5, geometric part (arXiv 2512.22696v4)

Lemma 5: "If `a != b (mod 3)`, then if some triangle with angles `(2 alpha, 2 beta, alpha + beta)` can be tiled into
`N` tiles, `N = (a+2b)(b+2a) m^2` for some integer `m`."  Proof printed: the sides are `((a+2b) a m, (b+2a) b m, c^2 m)`, all
integers, `m` rational; coprimality forces `m` integer.  `ZhangRat6Arith.lemma5` is the arithmetic core.  Here the steps
"sides are `((a+2b) a m, ...)`", "sides are integers" and "`N = (a+2b)(b+2a) m^2`" are DERIVED for a real
`CongruentDissection` whose target has angles `(2 alpha, 2 beta, alpha + beta)` at its vertices `0, 1, 2`
(`alpha, beta` the model's angles at `0, 1`; the vertex order is WLOG a relabelling of the target):
* `model_trig`: `cos alpha = (A+2B)/(2C)`, `cos beta = (2A+B)/(2C)`, `sin alpha = sqrt 3 A/(2C)`, `sin beta = sqrt 3 B/(2C)`;
* law of sines on the target (`TriLawSin.sin_angleAt_mul_sideOpp`): sides `(A(A+2B) m, B(B+2A) m, C^2 m)`;
* area: `N A B = A(A+2B) B(B+2A) m^2` (`ZhangRat7Int.det_target_eq`, `det_sq_sides`);
* integrality: `ZhangRat7Int.target_side_walk` (sides are natural combinations of `A, B, C`), so `m` is rational;
* `zhang_lemma5_geom`: with `Coprime A B`, `A % 3 != B % 3`: `N = (A+2B)(B+2A) k^2`, `k` natural.
UNAUDITED.  Credit Zhang (arXiv 2512.22696v4), Beeson, Beeson-Zhang, Laczkovich.
-/

set_option maxHeartbeats 3200000

namespace Erdos634.ZhangRat7Lem5

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.ZhangRat7Int Erdos634.AreaDet

theorem model_trig (T : Erdos634.Geometry.Tri) (A B C : ℕ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hh : C * C = A * A + B * B + A * B)
    (h0 : sideOpp T 0 = A) (h1 : sideOpp T 1 = B) (h2 : sideOpp T 2 = C) :
    Real.cos (angleAt T 0) = ((A : ℝ) + 2 * B) / (2 * C) ∧
    Real.cos (angleAt T 1) = (2 * (A : ℝ) + B) / (2 * C) ∧
    Real.sin (angleAt T 0) = Real.sqrt 3 * A / (2 * C) ∧
    Real.sin (angleAt T 1) = Real.sqrt 3 * B / (2 * C) := by
  have hAr : (0 : ℝ) < A := Nat.cast_pos.mpr hA
  have hBr : (0 : ℝ) < B := Nat.cast_pos.mpr hB
  have hCr : (0 : ℝ) < C := Nat.cast_pos.mpr hC
  have hcR : (C : ℝ) ^ 2 = (A : ℝ) ^ 2 + (B : ℝ) ^ 2 + A * B := by
    exact_mod_cast (by nlinarith [hh] : C ^ 2 = A ^ 2 + B ^ 2 + A * B)
  have e0 : dist (T.pts 1) (T.pts 2) = A := h0
  have e1 : dist (T.pts 2) (T.pts 0) = B := h1
  have e2 : dist (T.pts 0) (T.pts 1) = C := h2
  have hc0 : Real.cos (angleAt T 0) = ((A : ℝ) + 2 * B) / (2 * C) := by
    have h := Erdos634.ZhangRat4.cosang (T.pts 1) (T.pts 0) (T.pts 2) (u := (C : ℝ)) (w := (B : ℝ)) (s := (A : ℝ))
      (by rw [dist_comm]; exact e2) e1 e0 hCr hBr
    unfold angleAt cornerAngle
    rw [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl, h,
      div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (2 * (C : ℝ)) * hcR
  have hc1 : Real.cos (angleAt T 1) = (2 * (A : ℝ) + B) / (2 * C) := by
    have h := Erdos634.ZhangRat4.cosang (T.pts 2) (T.pts 1) (T.pts 0) (u := (A : ℝ)) (w := (C : ℝ)) (s := (B : ℝ))
      (by rw [dist_comm]; exact e0) e2 e1 hAr hCr
    unfold angleAt cornerAngle
    rw [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl, h,
      div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (2 * (C : ℝ)) * hcR
  have hr3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hr30 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have key : ∀ (θ : ℝ) (X : ℝ), 0 ≤ θ → θ ≤ Real.pi → 0 < X → Real.cos θ ^ 2 = 1 - 3 * X ^ 2 / (4 * (C : ℝ) ^ 2) →
      Real.sin θ = Real.sqrt 3 * X / (2 * C) := by
    intro θ X hθ0 hθπ hX hcos
    have hs0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 hθπ
    have hsq : Real.sin θ ^ 2 = (Real.sqrt 3 * X / (2 * C)) ^ 2 := by
      have := Real.sin_sq_add_cos_sq θ
      rw [div_pow, mul_pow, hr3]
      field_simp
      field_simp at hcos
      nlinarith [this, hcos]
    exact (sq_eq_sq₀ hs0 (by positivity)).mp hsq
  refine ⟨hc0, hc1, ?_, ?_⟩
  · refine key _ A (EuclideanGeometry.angle_nonneg _ _ _) (EuclideanGeometry.angle_le_pi _ _ _) hAr ?_
    rw [hc0, div_pow]; field_simp; nlinarith [hcR]
  · refine key _ B (EuclideanGeometry.angle_nonneg _ _ _) (EuclideanGeometry.angle_le_pi _ _ _) hBr ?_
    rw [hc1, div_pow]; field_simp; nlinarith [hcR]

theorem sides_of_angles {N : ℕ} (A B C : ℕ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hh : C * C = A * A + B * B + A * B) (D : CongruentDissection N)
    (h0 : sideOpp D.model 0 = A) (h1 : sideOpp D.model 1 = B) (h2 : sideOpp D.model 2 = C)
    (hφ0 : angleAt D.target 0 = 2 * angleAt D.model 0)
    (hφ1 : angleAt D.target 1 = 2 * angleAt D.model 1)
    (hφ2 : angleAt D.target 2 = angleAt D.model 0 + angleAt D.model 1) :
    ∃ m : ℝ, 0 < m ∧ sideOpp D.target 0 = A * (A + 2 * B) * m ∧
      sideOpp D.target 1 = B * (B + 2 * A) * m ∧ sideOpp D.target 2 = (C : ℝ) ^ 2 * m := by
  obtain ⟨hc0, hc1, hs0, hs1⟩ := model_trig D.model A B C hA hB hC hh h0 h1 h2
  have hAr : (0 : ℝ) < A := Nat.cast_pos.mpr hA
  have hBr : (0 : ℝ) < B := Nat.cast_pos.mpr hB
  have hCr : (0 : ℝ) < C := Nat.cast_pos.mpr hC
  have hcR : (C : ℝ) ^ 2 = (A : ℝ) ^ 2 + (B : ℝ) ^ 2 + A * B := by
    exact_mod_cast (by nlinarith [hh] : C ^ 2 = A ^ 2 + B ^ 2 + A * B)
  have hr30 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have l1 : Real.sin (angleAt D.target 1) * sideOpp D.target 0
      = Real.sin (angleAt D.target 0) * sideOpp D.target 1 := Erdos634.TriLawSin.sin_angleAt_mul_sideOpp D.target 0
  have l2 : Real.sin (angleAt D.target 2) * sideOpp D.target 1
      = Real.sin (angleAt D.target 1) * sideOpp D.target 2 := Erdos634.TriLawSin.sin_angleAt_mul_sideOpp D.target 1
  have sin2a : Real.sin (angleAt D.target 0) = Real.sqrt 3 * (A * (A + 2 * B)) / (2 * (C : ℝ) ^ 2) := by
    rw [hφ0, Real.sin_two_mul, hs0, hc0]; field_simp
  have sin2b : Real.sin (angleAt D.target 1) = Real.sqrt 3 * (B * (B + 2 * A)) / (2 * (C : ℝ) ^ 2) := by
    rw [hφ1, Real.sin_two_mul, hs1, hc1]; field_simp; ring
  have sinab : Real.sin (angleAt D.target 2) = Real.sqrt 3 / 2 := by
    rw [hφ2, Real.sin_add, hs0, hc1, hc0, hs1]
    field_simp
    nlinarith [hcR, hr30]
  have s2pos : 0 < sideOpp D.target 2 := by
    have : sideOpp D.target 2 = dist (D.target.pts 0) (D.target.pts 1) := rfl
    rw [this]; exact dist_pos.mpr (Erdos634.TilePlacement.pts_ne D.target (by decide))
  have k1 : (B : ℝ) * (B + 2 * A) * sideOpp D.target 0 = A * (A + 2 * B) * sideOpp D.target 1 := by
    have h := l1
    rw [sin2a, sin2b] at h
    field_simp at h
    linarith [h]
  have k2 : sideOpp D.target 1 * (C : ℝ) ^ 2 = B * (B + 2 * A) * sideOpp D.target 2 := by
    have h := l2
    rw [sinab, sin2b] at h
    field_simp at h
    linarith [h]
  have hne : (B : ℝ) * (B + 2 * A) ≠ 0 := by positivity
  refine ⟨sideOpp D.target 2 / (C : ℝ) ^ 2, by positivity, ?_, ?_, ?_⟩
  · field_simp
    apply mul_left_cancel₀ hne
    linear_combination (C : ℝ) ^ 2 * k1 + (A : ℝ) * (A + 2 * B) * k2
  · field_simp
    exact k2
  · field_simp

/-- **Zhang Lemma 5, geometric form.** -/
theorem zhang_lemma5_geom {N : ℕ} (A B C : ℕ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hh : C * C = A * A + B * B + A * B) (hcop : Nat.Coprime A B) (h3 : A % 3 ≠ B % 3)
    (D : CongruentDissection N) (hN : 0 < N)
    (h0 : sideOpp D.model 0 = A) (h1 : sideOpp D.model 1 = B) (h2 : sideOpp D.model 2 = C)
    (hφ0 : angleAt D.target 0 = 2 * angleAt D.model 0)
    (hφ1 : angleAt D.target 1 = 2 * angleAt D.model 1)
    (hφ2 : angleAt D.target 2 = angleAt D.model 0 + angleAt D.model 1) :
    ∃ k : ℕ, N = (A + 2 * B) * (B + 2 * A) * k ^ 2 := by
  have hAr : (0 : ℝ) < A := Nat.cast_pos.mpr hA
  have hBr : (0 : ℝ) < B := Nat.cast_pos.mpr hB
  have hCr : (0 : ℝ) < C := Nat.cast_pos.mpr hC
  have hcR : (C : ℝ) ^ 2 = (A : ℝ) ^ 2 + (B : ℝ) ^ 2 + A * B := by
    exact_mod_cast (by nlinarith [hh] : C ^ 2 = A ^ 2 + B ^ 2 + A * B)
  have hAB := ne_of_rel A B C hh hcop
  have hCA : A ≠ C := by intro h; subst h; nlinarith [Nat.mul_pos hA hB]
  have hCB : B ≠ C := by intro h; subst h; nlinarith [Nat.mul_pos hA hB]
  have hsc : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m' := by
    intro m m' hm
    fin_cases m <;> fin_cases m' <;> simp [h0, h1, h2] <;> first | exact absurd rfl hm | skip
    all_goals first
      | exact_mod_cast hAB | exact_mod_cast hAB.symm | exact_mod_cast hCA | exact_mod_cast hCA.symm
      | exact_mod_cast hCB | exact_mod_cast hCB.symm
  obtain ⟨m, hm, e0, e1, e2⟩ := sides_of_angles A B C hA hB hC hh D h0 h1 h2 hφ0 hφ1 hφ2
  -- area
  have hdt := det_sq_sides D.target
  have hdm := det_sq_sides D.model
  rw [e0, e1, e2, hcR] at hdt
  rw [h0, h1, h2, hcR] at hdm
  have habs := det_target_eq D
  have hsq : (detTri D.target) ^ 2 = (N : ℝ) ^ 2 * (detTri D.model) ^ 2 := by
    rw [← sq_abs (detTri D.target), habs, mul_pow, sq_abs]
  have a1 : 4 * (detTri D.target) ^ 2
      = 3 * ((A : ℝ) * (A + 2 * B)) ^ 2 * ((B : ℝ) * (B + 2 * A)) ^ 2 * m ^ 4 := by
    rw [hdt]; ring
  have a2 : 4 * (detTri D.model) ^ 2 = 3 * (A : ℝ) ^ 2 * (B : ℝ) ^ 2 := by
    rw [hdm]; ring
  have e5 : ((N : ℝ) * A * B) ^ 2 = ((A : ℝ) * (A + 2 * B) * (B * (B + 2 * A)) * m ^ 2) ^ 2 := by
    have : 4 * (detTri D.target) ^ 2 = (N : ℝ) ^ 2 * (4 * (detTri D.model) ^ 2) := by rw [hsq]; ring
    rw [a1, a2] at this
    nlinarith [this]
  have e6 : (N : ℝ) * A * B = (A : ℝ) * (A + 2 * B) * (B * (B + 2 * A)) * m ^ 2 :=
    (sq_eq_sq₀ (by positivity) (by positivity)).mp e5
  have e7 : (N : ℝ) = (A + 2 * B) * (B + 2 * A) * m ^ 2 := by
    apply mul_right_cancel₀ (mul_pos hAr hBr).ne'
    nlinarith [e6]
  -- integrality
  obtain ⟨P0, Q0, R0, w0⟩ := target_side_walk D hN hsc 1
  obtain ⟨P1, Q1, R1, w1⟩ := target_side_walk D hN hsc 2
  obtain ⟨P2, Q2, R2, w2⟩ := target_side_walk D hN hsc 0
  have ee0 : dist (D.target.pts 1) (D.target.pts (1 + 1)) = sideOpp D.target 0 := rfl
  have ee1 : dist (D.target.pts 2) (D.target.pts (2 + 1)) = sideOpp D.target 1 := rfl
  have ee2 : dist (D.target.pts 0) (D.target.pts (0 + 1)) = sideOpp D.target 2 := rfl
  rw [ee0, h0, h1, h2] at w0
  rw [ee1, h0, h1, h2] at w1
  rw [ee2, h0, h1, h2] at w2
  set n0 : ℕ := P0 * A + Q0 * B + R0 * C with hn0
  set n1 : ℕ := P1 * A + Q1 * B + R1 * C with hn1
  set n2 : ℕ := P2 * A + Q2 * B + R2 * C with hn2
  have r0 : ((n0 : ℕ) : ℝ) = A * (A + 2 * B) * m := by rw [← e0, w0]; simp only [hn0]; push_cast; ring
  have r1 : ((n1 : ℕ) : ℝ) = B * (B + 2 * A) * m := by rw [← e1, w1]; simp only [hn1]; push_cast; ring
  have r2 : ((n2 : ℕ) : ℝ) = (C : ℝ) ^ 2 * m := by rw [← e2, w2]; simp only [hn2]; push_cast; ring
  set mq : ℚ := (n2 : ℚ) / ((C : ℚ) ^ 2) with hmq
  have hmqR : (mq : ℝ) = m := by
    rw [hmq]; push_cast; rw [r2]; field_simp
  have hmq0 : 0 < mq := by
    have : (0 : ℝ) < (mq : ℝ) := by rw [hmqR]; exact hm
    exact_mod_cast this
  obtain ⟨k, hk, hNk⟩ := Erdos634.ZhangRat6Arith.lemma5 A B N mq hmq0 hA hB hcop h3 n0 n1
    (by apply Rat.cast_injective (α := ℝ); push_cast; rw [r0, hmqR]; ring)
    (by apply Rat.cast_injective (α := ℝ); push_cast; rw [r1, hmqR]; ring)
    (by apply Rat.cast_injective (α := ℝ); push_cast; rw [hmqR]; rw [e7]; ring)
  exact ⟨k, hNk⟩

end Erdos634.ZhangRat7Lem5

#print axioms Erdos634.ZhangRat7Lem5.model_trig
#print axioms Erdos634.ZhangRat7Lem5.sides_of_angles
#print axioms Erdos634.ZhangRat7Lem5.zhang_lemma5_geom
