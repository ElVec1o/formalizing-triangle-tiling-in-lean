import Erdos634.Draft.LaczFormalTrapChart2

/-!
# Laczkovich Lemma 2.2 (ii) with ALL FOUR printed angles; parallelism and the top ratio are DERIVED

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Lemma 2.2 (ii): "every rational trapezoid with angles
`β, α+β, γ, α+γ`"), Beeson, Beeson-Zhang, Zhang.

`lemma22_ii_four`: a convex quadrilateral `A B C D` (counterclockwise: four strict left turns; this is the orientation condition)
with `‖AB‖ = W`, `‖AD‖ = D` rational and the four ANGLES `∠DAB = β`, `∠ABC = α+β`, `∠BCD = γ`, `∠CDA = α+γ` (`α, β, γ` the
vertex angles of the rational triangle `Δ`) satisfies `C - D = τ (B - A)` with the forced `τ = tTau a b c W D` (parallelism is
derived from `∠DAB + ∠CDA = π` and the orientation; `τ` from the angle at `B` and the law of sines) and is a finite union of
rational triangles similar to `Δ`.  The angle at `C` is implied by the other three and is not used in the proof.
-/

namespace Erdos634.LaczTrapChart

open Erdos634 Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL24 Erdos634.LaczL35 Erdos634.LaczL37
  EuclideanGeometry

/-- dot product and (positively oriented) cross product of two vectors of the plane in terms of their angle. -/
theorem dotcr (p q : Plane) (θ : ℝ) (h : InnerProductGeometry.angle p q = θ) :
    p 0 * q 0 + p 1 * q 1 = ‖p‖ * ‖q‖ * Real.cos θ ∧
    (0 < p 0 * q 1 - p 1 * q 0 → p 0 * q 1 - p 1 * q 0 = ‖p‖ * ‖q‖ * Real.sin θ) := by
  have hin : ∀ x y : Plane, inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
    intro x y; simp [PiLp.inner_apply, Fin.sum_univ_two]; ring
  have hn : ∀ x : Plane, ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    intro x; rw [← real_inner_self_eq_norm_sq, hin]; ring
  have hcos := InnerProductGeometry.cos_angle_mul_norm_mul_norm p q
  rw [h, hin] at hcos
  have hdot : p 0 * q 0 + p 1 * q 1 = ‖p‖ * ‖q‖ * Real.cos θ := by rw [← hcos]; ring
  refine ⟨hdot, fun hpos => ?_⟩
  have hs : 0 ≤ Real.sin θ := h ▸ InnerProductGeometry.sin_angle_nonneg p q
  have hsc := Real.sin_sq_add_cos_sq θ
  have e : (p 0 * q 1 - p 1 * q 0) ^ 2 = ‖p‖ ^ 2 * ‖q‖ ^ 2 - (p 0 * q 0 + p 1 * q 1) ^ 2 := by
    rw [hn p, hn q]; ring
  rw [hdot] at e
  have h2 : (p 0 * q 1 - p 1 * q 0) ^ 2 = (‖p‖ * ‖q‖ * Real.sin θ) ^ 2 := by
    linear_combination e - (‖p‖ * ‖q‖) ^ 2 * hsc
  exact (pow_left_inj₀ hpos.le (by positivity) two_ne_zero).mp h2

theorem angleD (P Q S : Plane) (θ : ℝ) (h : ∠ P Q S = θ) :
    (P 0 - Q 0) * (S 0 - Q 0) + (P 1 - Q 1) * (S 1 - Q 1) = ‖P - Q‖ * ‖S - Q‖ * Real.cos θ ∧
    (0 < (P 0 - Q 0) * (S 1 - Q 1) - (P 1 - Q 1) * (S 0 - Q 0) →
      (P 0 - Q 0) * (S 1 - Q 1) - (P 1 - Q 1) * (S 0 - Q 0) = ‖P - Q‖ * ‖S - Q‖ * Real.sin θ) := by
  have := dotcr (P - Q) (S - Q) θ h
  simpa only [PiLp.sub_apply] using this

theorem RTri.cos_vang2 (R : RTri) :
    Real.cos (vang R.Δ 2) = ((R.a : ℝ) ^ 2 + R.b ^ 2 - R.c ^ 2) / (2 * R.a * R.b) := by
  have ha : (R.a : ℝ) ≠ 0 := by exact_mod_cast R.pa.ne'
  have hb : (R.b : ℝ) ≠ 0 := by exact_mod_cast R.pb.ne'
  have h := law_cos (R.Δ.pts 0) (R.Δ.pts 2) (R.Δ.pts 1)
  have e1 : dist (R.Δ.pts 0) (R.Δ.pts 1) = R.c := R.hc
  have e2 : dist (R.Δ.pts 0) (R.Δ.pts 2) = R.b := by rw [dist_comm]; exact R.hb
  have e3 : dist (R.Δ.pts 1) (R.Δ.pts 2) = R.a := R.ha
  rw [e1, e2, e3, ← vang2] at h
  field_simp
  nlinarith [h]

/-- law of sines for `Δ` at vertices 1, 2, and positivity of both sines. -/
theorem sin_rel (R : RTri) :
    Real.sin (vang R.Δ 1) * R.c = Real.sin (vang R.Δ 2) * R.b ∧ 0 < Real.sin (vang R.Δ 1) ∧ 0 < Real.sin (vang R.Δ 2) := by
  have ha : (0 : ℝ) < R.a := by exact_mod_cast R.pa
  have hb : (0 : ℝ) < R.b := by exact_mod_cast R.pb
  have hc : (0 : ℝ) < R.c := by exact_mod_cast R.pc
  have sb0 : 0 ≤ Real.sin (vang R.Δ 1) := Real.sin_nonneg_of_nonneg_of_le_pi (angle_nonneg _ _ _) (angle_le_pi _ _ _)
  have sg0 : 0 ≤ Real.sin (vang R.Δ 2) := Real.sin_nonneg_of_nonneg_of_le_pi (angle_nonneg _ _ _) (angle_le_pi _ _ _)
  have hcb := RTri.cos_vang1 R
  have hcg := RTri.cos_vang2 R
  have s1 := Real.sin_sq_add_cos_sq (vang R.Δ 1)
  have s2 := Real.sin_sq_add_cos_sq (vang R.Δ 2)
  have hsq : (Real.sin (vang R.Δ 1) * R.c) ^ 2 = (Real.sin (vang R.Δ 2) * R.b) ^ 2 := by
    have e1 : Real.sin (vang R.Δ 1) ^ 2 = 1 - Real.cos (vang R.Δ 1) ^ 2 := by linarith
    have e2 : Real.sin (vang R.Δ 2) ^ 2 = 1 - Real.cos (vang R.Δ 2) ^ 2 := by linarith
    rw [mul_pow, mul_pow, e1, e2, hcb, hcg]
    field_simp
    ring
  have heq : Real.sin (vang R.Δ 1) * R.c = Real.sin (vang R.Δ 2) * R.b :=
    (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp hsq
  have hlt : (R.cos1 : ℝ) ^ 2 < 1 := by rw [← RTri.rot_cos0]; exact R.rot.cos0_sq_lt
  have hc1 : (R.cos1 : ℝ) = ((R.a : ℝ) ^ 2 + R.c ^ 2 - R.b ^ 2) / (2 * R.a * R.c) := by
    simp only [RTri.cos1]; push_cast; ring
  have sbpos : 0 < Real.sin (vang R.Δ 1) := by
    rcases sb0.lt_or_eq with h | h
    · exact h
    · exfalso
      have : Real.cos (vang R.Δ 1) ^ 2 = 1 := by rw [← h] at s1; linarith
      rw [hcb, ← hc1] at this
      linarith
  refine ⟨heq, sbpos, ?_⟩
  have : Real.sin (vang R.Δ 2) = Real.sin (vang R.Δ 1) * R.c / R.b := by field_simp; linarith
  rw [this]; positivity

theorem trap_alg1 (u0 u1 v0 v1 w0 w1 W Dd n cb sb : ℝ) (hD : 0 < Dd) (hv : v0 ^ 2 + v1 ^ 2 = Dd ^ 2)
    (d1 : u0 * v0 + u1 * v1 = W * Dd * cb) (c1 : u0 * v1 - u1 * v0 = W * Dd * sb)
    (d2 : w0 * v0 + w1 * v1 = n * Dd * cb) (c2 : w0 * v1 - w1 * v0 = n * Dd * sb) :
    W * w0 = n * u0 ∧ W * w1 = n * u1 := by
  have hD2 : 0 < Dd ^ 2 := by positivity
  have e0 : (W * w0 - n * u0) * (v0 ^ 2 + v1 ^ 2) = 0 := by
    linear_combination (v0 * W) * d2 - (v0 * n) * d1 + (v1 * W) * c2 - (v1 * n) * c1
  have e1 : (W * w1 - n * u1) * (v0 ^ 2 + v1 ^ 2) = 0 := by
    linear_combination (v1 * W) * d2 - (v1 * n) * d1 - (v0 * W) * c2 + (v0 * n) * c1
  rw [hv] at e0 e1
  exact ⟨by nlinarith [(mul_eq_zero.mp e0).resolve_right hD2.ne'], by nlinarith [(mul_eq_zero.mp e1).resolve_right hD2.ne']⟩

theorem trap_alg2 (W Dd τ a b c cb cg sb sg Z : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hsg : 0 < sg)
    (e1 : Z * sg = Dd * sb) (e2 : (τ - 1) * W + Dd * cb = Z * cg) (hsin : sb * c = sg * b)
    (hcb : cb = (a ^ 2 + c ^ 2 - b ^ 2) / (2 * a * c)) (hcg : cg = (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b)) :
    (τ - 1) * W * c * a = Dd * (b ^ 2 - c ^ 2) := by
  have h3 : ((τ - 1) * W + Dd * cb) * c = Dd * b * cg := by
    apply mul_right_cancel₀ hsg.ne'
    linear_combination (c * sg) * e2 + (cg * c) * e1 + (cg * Dd) * hsin
  rw [hcb, hcg] at h3
  field_simp at h3
  nlinarith [h3]

theorem norm_sq_plane (x : Plane) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  have hin : ∀ x y : Plane, inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
    intro x y; simp [PiLp.inner_apply, Fin.sum_univ_two]; ring
  rw [← real_inner_self_eq_norm_sq, hin]; ring

set_option maxHeartbeats 3200000 in
/-- **Laczkovich Lemma 2.2 (ii) with all four printed angles** (see the header). -/
theorem lemma22_ii_four (R : RTri) (A B C D : Plane) (W Dd : ℚ) (hW : 0 < W) (hD : 0 < Dd)
    (hwn : ‖B - A‖ = W) (hdn : ‖D - A‖ = Dd)
    (hAng : ∠ B A D = vang R.Δ 1) (hBng : ∠ A B C = vang R.Δ 0 + vang R.Δ 1)
    (_hCng : ∠ B C D = vang R.Δ 2) (hDng : ∠ C D A = vang R.Δ 0 + vang R.Δ 2)
    (o1 : 0 < (B 0 - A 0) * (C 1 - B 1) - (B 1 - A 1) * (C 0 - B 0))
    (_o2 : 0 < (C 0 - B 0) * (D 1 - C 1) - (C 1 - B 1) * (D 0 - C 0))
    (o3 : 0 < (D 0 - C 0) * (A 1 - D 1) - (D 1 - C 1) * (A 0 - D 0))
    (o4 : 0 < (A 0 - D 0) * (B 1 - A 1) - (A 1 - D 1) * (B 0 - A 0)) :
    C - D = ((tTau R.a R.b R.c W Dd : ℚ) : ℝ) • (B - A) ∧ RatSimDiss R.Δ (convexHull ℝ {A, B, C, D}) := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hDr : (0 : ℝ) < Dd := by exact_mod_cast hD
  have ha : (0 : ℝ) < R.a := by exact_mod_cast R.pa
  have hb : (0 : ℝ) < R.b := by exact_mod_cast R.pb
  have hc : (0 : ℝ) < R.c := by exact_mod_cast R.pc
  have hsum := vang_sum R.Δ
  have hcb := RTri.cos_vang1 R
  have hcg := RTri.cos_vang2 R
  obtain ⟨hsin, hsb, hsg⟩ := sin_rel R
  have hag : vang R.Δ 0 + vang R.Δ 2 = Real.pi - vang R.Δ 1 := by linarith
  have hab : vang R.Δ 0 + vang R.Δ 1 = Real.pi - vang R.Δ 2 := by linarith
  obtain ⟨E1d, E1c⟩ := angleD B A D _ hAng
  obtain ⟨E4d, E4c⟩ := angleD A D C (vang R.Δ 0 + vang R.Δ 2) (by rw [angle_comm]; exact hDng)
  obtain ⟨E2d, E2c⟩ := angleD C B A (vang R.Δ 0 + vang R.Δ 1) (by rw [angle_comm]; exact hBng)
  rw [hag, Real.cos_pi_sub] at E4d
  rw [hag, Real.sin_pi_sub] at E4c
  rw [hab, Real.cos_pi_sub] at E2d
  rw [hab, Real.sin_pi_sub] at E2c
  have nAD : ‖A - D‖ = Dd := by rw [norm_sub_rev]; exact hdn
  have nAB : ‖A - B‖ = W := by rw [norm_sub_rev]; exact hwn
  rw [hwn, hdn] at E1d E1c
  rw [nAD] at E4d E4c
  rw [nAB] at E2d E2c
  have E1c' := E1c (by
    have e : (B 0 - A 0) * (D 1 - A 1) - (B 1 - A 1) * (D 0 - A 0) = (A 0 - D 0) * (B 1 - A 1) - (A 1 - D 1) * (B 0 - A 0) := by ring
    rw [e]; exact o4)
  have E4c' := E4c (by
    have e : (A 0 - D 0) * (C 1 - D 1) - (A 1 - D 1) * (C 0 - D 0) = (D 0 - C 0) * (A 1 - D 1) - (D 1 - C 1) * (A 0 - D 0) := by ring
    rw [e]; exact o3)
  have E2c' := E2c (by
    have e : (C 0 - B 0) * (A 1 - B 1) - (C 1 - B 1) * (A 0 - B 0) = (B 0 - A 0) * (C 1 - B 1) - (B 1 - A 1) * (C 0 - B 0) := by ring
    rw [e]; exact o1)
  obtain ⟨n, hn⟩ : ∃ n, n = ‖C - D‖ := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = ‖C - B‖ := ⟨_, rfl⟩
  rw [← hn] at E4d E4c'
  rw [← hZ] at E2d E2c'
  have hnpos : 0 < n := by
    rcases (hn ▸ norm_nonneg (C - D)).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at E4c'
      have : (0 : ℝ) < (A 0 - D 0) * (C 1 - D 1) - (A 1 - D 1) * (C 0 - D 0) := by
        have e : (A 0 - D 0) * (C 1 - D 1) - (A 1 - D 1) * (C 0 - D 0) = (D 0 - C 0) * (A 1 - D 1) - (D 1 - C 1) * (A 0 - D 0) := by ring
        rw [e]; exact o3
      rw [E4c'] at this
      simp at this
  have hvv : (D 0 - A 0) ^ 2 + (D 1 - A 1) ^ 2 = (Dd : ℝ) ^ 2 := by
    have := norm_sq_plane (D - A)
    rw [hdn] at this
    simp only [PiLp.sub_apply] at this
    linarith
  have huu : (B 0 - A 0) ^ 2 + (B 1 - A 1) ^ 2 = (W : ℝ) ^ 2 := by
    have := norm_sq_plane (B - A)
    rw [hwn] at this
    simp only [PiLp.sub_apply] at this
    linarith
  obtain ⟨h0, h1⟩ := trap_alg1 (B 0 - A 0) (B 1 - A 1) (D 0 - A 0) (D 1 - A 1) (C 0 - D 0) (C 1 - D 1) W Dd n
    (Real.cos (vang R.Δ 1)) (Real.sin (vang R.Δ 1)) hDr hvv
    (by linear_combination E1d) (by linear_combination E1c')
    (by linear_combination (-1) * E4d) (by linear_combination E4c')
  set τ : ℝ := n / W with hτdef
  have hτpos : 0 < τ := by positivity
  have hw0 : C 0 - D 0 = τ * (B 0 - A 0) := by rw [hτdef]; field_simp; linarith
  have hw1 : C 1 - D 1 = τ * (B 1 - A 1) := by rw [hτdef]; field_simp; linarith
  have hCD : C - D = τ • (B - A) := by
    ext i
    fin_cases i
    · simpa using hw0
    · simpa using hw1
  have e1 : Z * Real.sin (vang R.Δ 2) = Dd * Real.sin (vang R.Δ 1) := by
    have : (W : ℝ) * (Z * Real.sin (vang R.Δ 2)) = W * (Dd * Real.sin (vang R.Δ 1)) := by
      linear_combination (-1) * E2c' + (-(B 1 - A 1)) * hw0 + (B 0 - A 0) * hw1 + E1c'
    exact mul_left_cancel₀ hWr.ne' this
  have e2 : (τ - 1) * W + Dd * Real.cos (vang R.Δ 1) = Z * Real.cos (vang R.Δ 2) := by
    have : (W : ℝ) * ((τ - 1) * W + Dd * Real.cos (vang R.Δ 1)) = W * (Z * Real.cos (vang R.Δ 2)) := by
      linear_combination (-1) * E2d + (-(τ - 1)) * huu + (-1) * E1d + (-(B 0 - A 0)) * hw0 + (-(B 1 - A 1)) * hw1
    exact mul_left_cancel₀ hWr.ne' this
  have key := trap_alg2 W Dd τ R.a R.b R.c _ _ _ _ Z ha hb hc hsg e1 e2 hsin hcb hcg
  have hτq : ((tTau R.a R.b R.c W Dd : ℚ) : ℝ) = τ := by
    simp only [tTau]
    push_cast
    field_simp
    nlinarith [key]
  have hC' : C - D = ((tTau R.a R.b R.c W Dd : ℚ) : ℝ) • (B - A) := by rw [hτq]; exact hCD
  have hpos : 0 < tTau R.a R.b R.c W Dd := by
    have : (0 : ℝ) < ((tTau R.a R.b R.c W Dd : ℚ) : ℝ) := by rw [hτq]; exact hτpos
    exact_mod_cast this
  exact ⟨hC', lemma22_ii_vert R A B C D W Dd hW hD hwn hdn hAng _ rfl hpos hC'⟩

theorem ang_of (P Q S : Plane) (x p s c : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ Real.pi) (hP : ‖P - Q‖ = p) (hS : ‖S - Q‖ = s)
    (hp : 0 < p) (hs : 0 < s) (hin : inner ℝ (P - Q) (S - Q) = p * s * c) (hc : Real.cos x = c) : ∠ P Q S = x := by
  show InnerProductGeometry.angle (P - Q) (S - Q) = x
  apply angle_eq_of_cos (InnerProductGeometry.angle_nonneg _ _) (InnerProductGeometry.angle_le_pi _ _) hx0 hx1
  rw [InnerProductGeometry.cos_angle, hP, hS, hin, hc]
  field_simp

set_option maxHeartbeats 3200000 in
/-- **Witness for `lemma22_ii_four`** (every hypothesis holds): tile `(2,3,4)`, base `4`, leg `1`, vertices `A = (0,0)`, `B = (4,0)`,
`C = (61/16, √135/16)`, `D = (11/16, √135/16)`; the four angles are `β, α+β, γ, α+γ`, orientation counterclockwise. -/
theorem wit_ii_four :
    RatSimDiss R234.Δ (convexHull ℝ {mkPt 0 0, mkPt 4 0, mkPt (61 / 16) (Real.sqrt 135 / 16),
      mkPt (11 / 16) (Real.sqrt 135 / 16)}) := by
  have h135 : Real.sqrt 135 * Real.sqrt 135 = 135 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 135 := Real.sqrt_pos.mpr (by norm_num)
  have hpi := Real.pi_pos
  have hcb : Real.cos (vang R234.Δ 1) = 11 / 16 := by rw [RTri.cos_vang1]; simp [R234]; norm_num
  have hcg : Real.cos (vang R234.Δ 2) = -1 / 4 := by rw [RTri.cos_vang2]; simp [R234]; norm_num
  have hsum := vang_sum R234.Δ
  have g0 : 0 ≤ vang R234.Δ 0 := angle_nonneg _ _ _
  have g1 : 0 ≤ vang R234.Δ 1 := angle_nonneg _ _ _
  have g2 : 0 ≤ vang R234.Δ 2 := angle_nonneg _ _ _
  have hwn : ‖mkPt 4 0 - mkPt 0 0‖ = ((4 : ℚ) : ℝ) := by
    rw [mkPt_sub]; exact norm_mkPt_of _ _ _ (by norm_num) (by norm_num)
  have hdn : ‖mkPt (11 / 16) (Real.sqrt 135 / 16) - mkPt 0 0‖ = ((1 : ℚ) : ℝ) := by
    rw [mkPt_sub]; exact norm_mkPt_of _ _ _ (by norm_num) (by push_cast; nlinarith)
  have hAng : ∠ (mkPt 4 0) (mkPt 0 0) (mkPt (11 / 16) (Real.sqrt 135 / 16)) = vang R234.Δ 1 := by
    apply ang_of _ _ _ _ 4 1 (11 / 16) g1 (by linarith) (by rw [hwn]; norm_num) (by rw [hdn]; norm_num) (by norm_num) (by norm_num)
    · rw [mkPt_sub, mkPt_sub, inner_mkPt]; norm_num
    · exact hcb
  have hBng : ∠ (mkPt 0 0) (mkPt 4 0) (mkPt (61 / 16) (Real.sqrt 135 / 16)) = vang R234.Δ 0 + vang R234.Δ 1 := by
    have hab : vang R234.Δ 0 + vang R234.Δ 1 = Real.pi - vang R234.Δ 2 := by linarith
    rw [hab]
    apply ang_of _ _ _ _ 4 (3 / 4) (1 / 4) (by linarith) (by linarith)
    · rw [mkPt_sub]; exact norm_mkPt_of _ _ _ (by norm_num) (by norm_num)
    · rw [mkPt_sub]; exact norm_mkPt_of _ _ _ (by norm_num) (by nlinarith)
    · norm_num
    · norm_num
    · rw [mkPt_sub, mkPt_sub, inner_mkPt]; norm_num
    · rw [Real.cos_pi_sub, hcg]; norm_num
  have hCng : ∠ (mkPt 4 0) (mkPt (61 / 16) (Real.sqrt 135 / 16)) (mkPt (11 / 16) (Real.sqrt 135 / 16)) = vang R234.Δ 2 := by
    apply ang_of _ _ _ _ (3 / 4) (25 / 8) (-1 / 4) g2 (by linarith)
    · rw [mkPt_sub]; exact norm_mkPt_of _ _ _ (by norm_num) (by nlinarith)
    · rw [mkPt_sub]; exact norm_mkPt_of _ _ _ (by norm_num) (by nlinarith)
    · norm_num
    · norm_num
    · rw [mkPt_sub, mkPt_sub, inner_mkPt]; norm_num
    · exact hcg
  have hDng : ∠ (mkPt (61 / 16) (Real.sqrt 135 / 16)) (mkPt (11 / 16) (Real.sqrt 135 / 16)) (mkPt 0 0)
      = vang R234.Δ 0 + vang R234.Δ 2 := by
    have hag : vang R234.Δ 0 + vang R234.Δ 2 = Real.pi - vang R234.Δ 1 := by linarith
    rw [hag]
    apply ang_of _ _ _ _ (25 / 8) 1 (-11 / 16) (by linarith) (by linarith)
    · rw [mkPt_sub]; exact norm_mkPt_of _ _ _ (by norm_num) (by nlinarith)
    · rw [mkPt_sub]; exact norm_mkPt_of _ _ _ (by norm_num) (by nlinarith)
    · norm_num
    · norm_num
    · rw [mkPt_sub, mkPt_sub, inner_mkPt]; norm_num
    · rw [Real.cos_pi_sub, hcb]; norm_num
  have hwn' : ‖mkPt 4 0 - mkPt 0 0‖ = ((4 : ℚ) : ℝ) := hwn
  have key := lemma22_ii_four R234 (mkPt 0 0) (mkPt 4 0) (mkPt (61 / 16) (Real.sqrt 135 / 16)) (mkPt (11 / 16) (Real.sqrt 135 / 16))
    4 1 (by norm_num) (by norm_num) hwn hdn hAng hBng hCng hDng
    (by simp only [PiLp.sub_apply, mkPt_zero, mkPt_one]; nlinarith)
    (by simp only [PiLp.sub_apply, mkPt_zero, mkPt_one]; nlinarith)
    (by simp only [PiLp.sub_apply, mkPt_zero, mkPt_one]; nlinarith)
    (by simp only [PiLp.sub_apply, mkPt_zero, mkPt_one]; nlinarith)
  exact key.2

end Erdos634.LaczTrapChart

#print axioms Erdos634.LaczTrapChart.dotcr
#print axioms Erdos634.LaczTrapChart.RTri.cos_vang2
#print axioms Erdos634.LaczTrapChart.sin_rel
#print axioms Erdos634.LaczTrapChart.trap_alg1
#print axioms Erdos634.LaczTrapChart.trap_alg2
#print axioms Erdos634.LaczTrapChart.lemma22_ii_four
#print axioms Erdos634.LaczTrapChart.wit_ii_four
