import Erdos634.Draft.LaczFormalL34Final
import Erdos634.Draft.BeesonCor5
import Erdos634.SssTri

/-!
# Laczkovich Theorems 2.4 and 2.5 AS PRINTED (angle hypotheses, arbitrary triangle `T`)

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorems 2.4 and 2.5), Beeson (arXiv 1206.2229),
Beeson-Zhang, Zhang.

Printed statements:
* Thm 2.4: `0 < α < π/3`, `sin(α/2)` rational, `β = (π-3α)/2`, `γ = (π+α)/2`; a triangle `T` whose angles are one of the five
  triples `(α,α,π-2α)`, `(α,α+β,α+β)`, `(β,β,3α)`, `(α,2α,2β)`, `(β,2α,α+β)` can be dissected into congruent triangles with
  angles `α, β, γ`.
* Thm 2.5: `0 < α < π/3`, `√3 sin α` and `cos α` rational, `β = π/3-α`, `γ = 2π/3`; a triangle `T` with angles one of the six
  triples `(α,α,π-2α)`, `(α,2α,π-3α)`, `(α,2β,2α+β)`, `(α,α+β,α+2β)`, `(2α,2β,α+β)`, `(α+β,α+β,α+β)` can be dissected into
  congruent triangles with angles `α, β, γ`.

"Angles of `T` are the triple" = for SOME bijection `σ` of the vertices the angle at `T.pts (σ i)` is the `i`-th entry
(`HasAngles`); the conclusion is a `CongruentDissection M` (`M` free) with target carrier `T.carrier` whose model is congruent
to a triangle `Δ'` with `vang Δ' = (α, β, γ)` (`PrintedConcl`).  The bridge from the angle hypotheses to a rational tile
(`RTri`) is proved here (`tile24`, `tile25`), via the law of cosines (`exists_RTri_rat`).
-/

namespace Erdos634.LaczL35

open Erdos634 Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.Realizable Erdos634.LaczL28
  Erdos634.SssTri EuclideanGeometry

/-- The angle of `T` at vertex `i`. -/
noncomputable def vang (T : Tri) (i : Fin 3) : ℝ := ∠ (T.pts (i + 1)) (T.pts i) (T.pts (i + 2))

theorem vang0 (T : Tri) : vang T 0 = ∠ (T.pts 1) (T.pts 0) (T.pts 2) := rfl
theorem vang1 (T : Tri) : vang T 1 = ∠ (T.pts 2) (T.pts 1) (T.pts 0) := rfl
theorem vang2 (T : Tri) : vang T 2 = ∠ (T.pts 0) (T.pts 2) (T.pts 1) := rfl

theorem ang1 (T : Tri) : ∠ (T.pts 0) (T.pts 1) (T.pts 2) = vang T 1 := by rw [vang1, angle_comm]
theorem ang2 (T : Tri) : ∠ (T.pts 1) (T.pts 2) (T.pts 0) = vang T 2 := by rw [vang2, angle_comm]

theorem vang_sum (T : Tri) : vang T 0 + vang T 1 + vang T 2 = Real.pi := by
  have hne : T.pts 0 ≠ T.pts 2 := fun he => absurd (T.indep.injective he) (by decide)
  have h := angle_add_angle_add_angle_eq_pi (p₁ := T.pts 2) (p₂ := T.pts 0) (T.pts 1) hne
  have a := angle_comm (T.pts 2) (T.pts 0) (T.pts 1)
  have b := angle_comm (T.pts 0) (T.pts 1) (T.pts 2)
  have c := angle_comm (T.pts 1) (T.pts 2) (T.pts 0)
  rw [vang0, vang1, vang2]
  linarith [h]

/-! ### vertex relabelling -/

/-- `T` with its vertices relabelled by `σ`. -/
noncomputable def permT (T : Tri) (σ : Equiv.Perm (Fin 3)) : Tri :=
  ⟨T.pts ∘ σ, AffineIndependent.comp_embedding σ.toEmbedding T.indep⟩

theorem permT_carrier (T : Tri) (σ : Equiv.Perm (Fin 3)) : (permT T σ).carrier = T.carrier := by
  unfold Tri.carrier
  show convexHull ℝ (Set.range (T.pts ∘ σ)) = _
  rw [(Equiv.surjective σ).range_comp]

theorem perm_cases (σ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (σ (k + 1) = σ k + 1 ∧ σ (k + 2) = σ k + 2) ∨ (σ (k + 1) = σ k + 2 ∧ σ (k + 2) = σ k + 1) := by
  revert σ k; decide

theorem vang_permT (T : Tri) (σ : Equiv.Perm (Fin 3)) (k : Fin 3) : vang (permT T σ) k = vang T (σ k) := by
  unfold vang
  show ∠ (T.pts (σ (k + 1))) (T.pts (σ k)) (T.pts (σ (k + 2))) = _
  rcases perm_cases σ k with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, angle_comm]

/-- The angles of `T` are the triple `(x,y,z)` in some order. -/
def HasAngles (T : Tri) (x y z : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3), vang T (σ 0) = x ∧ vang T (σ 1) = y ∧ vang T (σ 2) = z

theorem HasAngles.s12 {T : Tri} {x y z : ℝ} (h : HasAngles T x y z) : HasAngles T x z y := by
  obtain ⟨σ, h0, h1, h2⟩ := h
  refine ⟨σ * Equiv.swap 1 2, ?_, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, show Equiv.swap (1 : Fin 3) 2 0 = 0 by decide]; exact h0
  · rw [Equiv.Perm.mul_apply, show Equiv.swap (1 : Fin 3) 2 1 = 2 by decide]; exact h2
  · rw [Equiv.Perm.mul_apply, show Equiv.swap (1 : Fin 3) 2 2 = 1 by decide]; exact h1

theorem HasAngles.s01 {T : Tri} {x y z : ℝ} (h : HasAngles T x y z) : HasAngles T y x z := by
  obtain ⟨σ, h0, h1, h2⟩ := h
  refine ⟨σ * Equiv.swap 0 1, ?_, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, show Equiv.swap (0 : Fin 3) 1 0 = 1 by decide]; exact h1
  · rw [Equiv.Perm.mul_apply, show Equiv.swap (0 : Fin 3) 1 1 = 0 by decide]; exact h0
  · rw [Equiv.Perm.mul_apply, show Equiv.swap (0 : Fin 3) 1 2 = 2 by decide]; exact h2

/-- Canonical labelling: a relabelled `T'` with the same carrier and `vang T' = (x, y, z)`. -/
theorem HasAngles.canon {T : Tri} {x y z : ℝ} (h : HasAngles T x y z) :
    ∃ T' : Tri, T'.carrier = T.carrier ∧ vang T' 0 = x ∧ vang T' 1 = y ∧ vang T' 2 = z := by
  obtain ⟨σ, h0, h1, h2⟩ := h
  exact ⟨permT T σ, permT_carrier T σ, by rw [vang_permT]; exact h0, by rw [vang_permT]; exact h1,
    by rw [vang_permT]; exact h2⟩

/-! ### isosceles from equal angles -/

theorem iso_apex1 (S : Tri) (h : vang S 0 = vang S 2) (hp : vang S 1 ≠ Real.pi) :
    dist (S.pts 1) (S.pts 0) = dist (S.pts 1) (S.pts 2) := by
  apply dist_eq_of_angle_eq_angle_of_angle_ne_pi
  · rw [vang0, vang2, angle_comm (S.pts 0) (S.pts 2) (S.pts 1)] at h; exact h
  · rw [vang1, angle_comm] at hp; exact hp

theorem iso_apex2 (S : Tri) (h : vang S 0 = vang S 1) (hp : vang S 2 ≠ Real.pi) :
    dist (S.pts 2) (S.pts 0) = dist (S.pts 2) (S.pts 1) := by
  apply dist_eq_of_angle_eq_angle_of_angle_ne_pi
  · rw [vang0, vang1, angle_comm (S.pts 1) (S.pts 0) (S.pts 2)] at h
    rw [h]
  · exact hp

/-! ### a rational tile with given rational sides -/

theorem exists_RTri_rat (a b c : ℚ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : a < b + c) (h2 : b < a + c)
    (h3 : c < a + b) : ∃ R : RTri, R.a = a ∧ R.b = b ∧ R.c = c := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have h1R : (a : ℝ) < b + c := by exact_mod_cast h1
  have h2R : (b : ℝ) < a + c := by exact_mod_cast h2
  have h3R : (c : ℝ) < a + b := by exact_mod_cast h3
  have key : (b : ℝ) ^ 2 - (xCoord a b c) ^ 2
      = ((a : ℝ) + b + c) * (b + c - a) * (a + c - b) * (a + b - c) / (4 * (c : ℝ) ^ 2) := by
    unfold xCoord; field_simp; ring
  have hpos : (0 : ℝ) < (b : ℝ) ^ 2 - (xCoord a b c) ^ 2 := by
    rw [key]
    have : 0 < (a : ℝ) + b - c := by linarith
    have : 0 < (a : ℝ) + c - b := by linarith
    have : 0 < (b : ℝ) + c - a := by linarith
    positivity
  have hh : (Real.sqrt ((b : ℝ) ^ 2 - (xCoord a b c) ^ 2)) ^ 2 = (b : ℝ) ^ 2 - (xCoord a b c) ^ 2 :=
    Real.sq_sqrt hpos.le
  have hne : Real.sqrt ((b : ℝ) ^ 2 - (xCoord a b c) ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  refine ⟨⟨sssTri a b c _ hcR.ne' hne, a, b, c, ?_, ?_, ?_, ha, hb, hc⟩, rfl, rfl, rfl⟩
  · exact dist12 (a : ℝ) (b : ℝ) (c : ℝ) (Real.sqrt ((b : ℝ) ^ 2 - (xCoord a b c) ^ 2)) hcR.ne' haR.le hh
  · rw [dist_comm]; exact dist02 (a : ℝ) (b : ℝ) (c : ℝ) (Real.sqrt ((b : ℝ) ^ 2 - (xCoord a b c) ^ 2)) hbR.le hh
  · exact dist01 (a : ℝ) (b : ℝ) (c : ℝ) (Real.sqrt ((b : ℝ) ^ 2 - (xCoord a b c) ^ 2)) hcR.le

/-! ### angles of an `RTri` from its sides -/

theorem RTri.cos_vang0 (R : RTri) :
    Real.cos (vang R.Δ 0) = ((R.b : ℝ) ^ 2 + R.c ^ 2 - R.a ^ 2) / (2 * R.b * R.c) := by
  have hb : (R.b : ℝ) ≠ 0 := by exact_mod_cast R.pb.ne'
  have hc : (R.c : ℝ) ≠ 0 := by exact_mod_cast R.pc.ne'
  have h := law_cos (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2)
  have e1 : dist (R.Δ.pts 1) (R.Δ.pts 2) = R.a := R.ha
  have e2 : dist (R.Δ.pts 1) (R.Δ.pts 0) = R.c := by rw [dist_comm]; exact R.hc
  have e3 : dist (R.Δ.pts 2) (R.Δ.pts 0) = R.b := R.hb
  rw [e1, e2, e3, ← vang0] at h
  field_simp
  nlinarith [h]

theorem RTri.cos_vang1 (R : RTri) :
    Real.cos (vang R.Δ 1) = ((R.a : ℝ) ^ 2 + R.c ^ 2 - R.b ^ 2) / (2 * R.a * R.c) := by
  have ha : (R.a : ℝ) ≠ 0 := by exact_mod_cast R.pa.ne'
  have hc : (R.c : ℝ) ≠ 0 := by exact_mod_cast R.pc.ne'
  have h := law_cos (R.Δ.pts 2) (R.Δ.pts 1) (R.Δ.pts 0)
  have e1 : dist (R.Δ.pts 2) (R.Δ.pts 0) = R.b := R.hb
  have e2 : dist (R.Δ.pts 2) (R.Δ.pts 1) = R.a := by rw [dist_comm]; exact R.ha
  have e3 : dist (R.Δ.pts 0) (R.Δ.pts 1) = R.c := R.hc
  rw [e1, e2, e3, ← vang1] at h
  field_simp
  nlinarith [h]

theorem angle_eq_of_cos {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ Real.pi) (hy0 : 0 ≤ y) (hy1 : y ≤ Real.pi)
    (h : Real.cos x = Real.cos y) : x = y :=
  Real.injOn_cos ⟨hx0, hx1⟩ ⟨hy0, hy1⟩ h

theorem RTri.angles_of (R : RTri) (α β : ℝ) (hα0 : 0 < α) (hβ0 : 0 < β) (hαβ : α + β < Real.pi)
    (c0 : ((R.b : ℝ) ^ 2 + R.c ^ 2 - R.a ^ 2) / (2 * R.b * R.c) = Real.cos α)
    (c1 : ((R.a : ℝ) ^ 2 + R.c ^ 2 - R.b ^ 2) / (2 * R.a * R.c) = Real.cos β) :
    vang R.Δ 0 = α ∧ vang R.Δ 1 = β ∧ vang R.Δ 2 = Real.pi - α - β := by
  have e0 : vang R.Δ 0 = α :=
    angle_eq_of_cos (angle_nonneg _ _ _) (angle_le_pi _ _ _) hα0.le (by linarith [Real.pi_pos])
      ((RTri.cos_vang0 R).trans c0)
  have e1 : vang R.Δ 1 = β :=
    angle_eq_of_cos (angle_nonneg _ _ _) (angle_le_pi _ _ _) hβ0.le (by linarith [Real.pi_pos])
      ((RTri.cos_vang1 R).trans c1)
  refine ⟨e0, e1, ?_⟩
  have := vang_sum R.Δ
  linarith

/-! ### the bridge for Theorem 2.4 -/

theorem tile24 (α : ℝ) (h0 : 0 < α) (h1 : α < Real.pi / 3) (q : ℚ) (hq : Real.sin (α / 2) = q) :
    ∃ (R : RTri) (a0 : ℚ), 0 < a0 ∧ a0 < 1 ∧ R.a = a0 * R.c ∧ R.b = (1 - a0 ^ 2) * R.c ∧
      vang R.Δ 0 = α ∧ vang R.Δ 1 = (Real.pi - 3 * α) / 2 ∧ vang R.Δ 2 = (Real.pi + α) / 2 := by
  have hqpos : (0 : ℝ) < q := by
    rw [← hq]; exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hqhalf : (q : ℝ) < 1 / 2 := by
    rw [← hq, ← Real.sin_pi_div_six]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
      (by linarith)
  have hqp : 0 < q := by exact_mod_cast hqpos
  have hqh : q < 1 / 2 := by
    have : ((q : ℚ) : ℝ) < ((1 / 2 : ℚ) : ℝ) := by push_cast; exact hqhalf
    exact_mod_cast this
  obtain ⟨R, hRa, hRb, hRc⟩ := exists_RTri_rat (2 * q) (1 - (2 * q) ^ 2) 1 (by linarith) (by nlinarith) one_pos
    (by nlinarith) (by nlinarith) (by nlinarith)
  have hcos : Real.cos α = 1 - 2 * (q : ℝ) ^ 2 := by
    have := Real.cos_two_mul (α / 2)
    rw [show 2 * (α / 2) = α by ring] at this
    rw [this, ← hq]; nlinarith [Real.sin_sq_add_cos_sq (α / 2)]
  have hcos2 : Real.cos ((Real.pi - 3 * α) / 2) = 3 * (q : ℝ) - 4 * (q : ℝ) ^ 3 := by
    rw [show (Real.pi - 3 * α) / 2 = Real.pi / 2 - 3 * (α / 2) by ring, Real.cos_pi_div_two_sub,
      Real.sin_three_mul, hq]
  have hb : (0 : ℝ) < 1 - (2 * (q : ℝ)) ^ 2 := by nlinarith
  have hq0 : (q : ℝ) ≠ 0 := hqpos.ne'
  have hR := RTri.angles_of R α ((Real.pi - 3 * α) / 2) h0 (by linarith) (by linarith [Real.pi_pos])
    (by
      rw [hcos, hRa, hRb, hRc]
      push_cast
      rw [div_eq_iff (by apply ne_of_gt; nlinarith [hb])]
      ring)
    (by
      rw [hcos2, hRa, hRb, hRc]
      push_cast
      rw [div_eq_iff (by apply ne_of_gt; nlinarith [hqpos])]
      ring)
  refine ⟨R, 2 * q, by linarith, by linarith, by rw [hRa, hRc]; ring, by rw [hRb, hRc]; ring, hR.1, hR.2.1, ?_⟩
  rw [hR.2.2]; ring

/-! ### the bridge for Theorem 2.5 -/

theorem tile25 (α : ℝ) (h0 : 0 < α) (h1 : α < Real.pi / 3) (u v : ℚ) (hu : Real.sqrt 3 * Real.sin α = u)
    (hv : Real.cos α = v) :
    ∃ R : RTri, R.a ^ 2 + R.a * R.b + R.b ^ 2 = R.c ^ 2 ∧ vang R.Δ 0 = α ∧ vang R.Δ 1 = Real.pi / 3 - α ∧
      vang R.Δ 2 = 2 * Real.pi / 3 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3p : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hsa : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hup : (0 : ℝ) < u := by rw [← hu]; positivity
  have hup' : 0 < u := by exact_mod_cast hup
  have hrel : (u : ℝ) ^ 2 / 3 + (v : ℝ) ^ 2 = 1 := by
    rw [← hu, ← hv, mul_pow, h3]; nlinarith [Real.sin_sq_add_cos_sq α]
  have hrel' : u ^ 2 / 3 + v ^ 2 = 1 := by exact_mod_cast hrel
  have hbpos : (0 : ℝ) < (v : ℝ) - u / 3 := by
    have e : Real.sqrt 3 / 2 * ((v : ℝ) - u / 3) = Real.sin (Real.pi / 3 - α) := by
      rw [Real.sin_sub, Real.sin_pi_div_three, Real.cos_pi_div_three, hv, ← hu]; nlinarith [h3]
    have hs : 0 < Real.sin (Real.pi / 3 - α) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    rw [← e] at hs
    by_contra hc
    push_neg at hc
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt 3 / 2) (neg_nonneg.mpr hc)]
  have hbp : 0 < v - u / 3 := by exact_mod_cast hbpos
  have hap : 0 < 2 * u / 3 := by linarith
  have hsq : (2 * u / 3) ^ 2 + (2 * u / 3) * (v - u / 3) + (v - u / 3) ^ 2 = 1 := by nlinarith [hrel']
  obtain ⟨R, hRa, hRb, hRc⟩ := exists_RTri_rat (2 * u / 3) (v - u / 3) 1 hap hbp one_pos
    (by nlinarith) (by nlinarith) (by nlinarith [mul_pos hap hbp])
  have hcos1 : Real.cos (Real.pi / 3 - α) = ((u : ℝ) + v) / 2 := by
    rw [Real.cos_sub, Real.cos_pi_div_three, Real.sin_pi_div_three, hv]
    have : Real.sqrt 3 / 2 * Real.sin α = u / 2 := by rw [← hu]; ring
    linarith
  have hsqR : (2 * (u : ℝ) / 3) ^ 2 + (2 * u / 3) * (v - u / 3) + (v - u / 3) ^ 2 = 1 := by exact_mod_cast hsq
  have hR := RTri.angles_of R α (Real.pi / 3 - α) h0 (by linarith) (by linarith [Real.pi_pos])
    (by
      rw [hv, hRa, hRb, hRc]; push_cast
      rw [div_eq_iff (by apply ne_of_gt; nlinarith [hbpos])]
      first | linear_combination (-1 : ℝ) * hsqR | nlinarith [hsqR])
    (by
      rw [hcos1, hRa, hRb, hRc]; push_cast
      rw [div_eq_iff (by apply ne_of_gt; nlinarith [hup])]
      first | linear_combination (-1 : ℝ) * hsqR | nlinarith [hsqR])
  refine ⟨R, ?_, hR.1, hR.2.1, ?_⟩
  · rw [hRa, hRb, hRc]; linarith [hsq]
  · rw [hR.2.2]; ring

/-! ### the printed conclusion -/

/-- `T` is a union of finitely many congruent triangles with angles `(α, β, γ)`. -/
def PrintedConcl (T : Tri) (α β γ : ℝ) : Prop :=
  ∃ Δ' : Tri, vang Δ' 0 = α ∧ vang Δ' 1 = β ∧ vang Δ' 2 = γ ∧
    ∃ (M : ℕ) (D : CongruentDissection M), D.target.carrier = T.carrier ∧ D.model.Congruent Δ'

theorem concl_of (R : RTri) (α β γ : ℝ) (r0 : vang R.Δ 0 = α) (r1 : vang R.Δ 1 = β) (r2 : vang R.Δ 2 = γ)
    (T T' : Tri) (hc : T'.carrier = T.carrier) (hD : Dissectable R T') : PrintedConcl T α β γ := by
  obtain ⟨s, hs, M, D, e1, e2⟩ := hD
  have sc : ∀ i j k : Fin 3, i ≠ j → k ≠ j →
      cornerAngle ((scaleTri s hs.ne' R.Δ).pts i) ((scaleTri s hs.ne' R.Δ).pts j) ((scaleTri s hs.ne' R.Δ).pts k)
        = cornerAngle (R.Δ.pts i) (R.Δ.pts j) (R.Δ.pts k) :=
    fun i j k hij hkj => Erdos634.BeesonCor5.angle_scale R.Δ s hs i j k hij hkj
  refine ⟨scaleTri s hs.ne' R.Δ, ?_, ?_, ?_, M, D, by rw [e1, hc], e2⟩
  · rw [← r0]; exact sc 1 0 2 (by decide) (by decide)
  · rw [← r1]; exact sc 2 1 0 (by decide) (by decide)
  · rw [← r2]; exact sc 0 2 1 (by decide) (by decide)

/-! ### Theorem 2.4 as printed -/

/-- **Laczkovich Theorem 2.4, as printed.**  `0 < α < π/3`, `sin(α/2) ∈ ℚ`, `β = (π-3α)/2`, `γ = (π+α)/2`.  Every triangle `T`
whose angles are one of `(α,α,π-2α)`, `(α,α+β,α+β)`, `(β,β,3α)`, `(α,2α,2β)`, `(β,2α,α+β)` is a union of finitely many
congruent triangles with angles `(α, β, γ)`. -/
theorem thm24_printed (α β γ : ℝ) (h0 : 0 < α) (h1 : α < Real.pi / 3) (hq : ∃ q : ℚ, Real.sin (α / 2) = q)
    (hβ : β = (Real.pi - 3 * α) / 2) (hγ : γ = (Real.pi + α) / 2) (T : Tri)
    (hT : HasAngles T α α (Real.pi - 2 * α) ∨ HasAngles T α (α + β) (α + β) ∨ HasAngles T β β (3 * α) ∨
      HasAngles T α (2 * α) (2 * β) ∨ HasAngles T β (2 * α) (α + β)) :
    PrintedConcl T α β γ := by
  obtain ⟨q, hq⟩ := hq
  obtain ⟨R, a0, ha0, ha1, hA, hB, r0, r1, r2⟩ := tile24 α h0 h1 q hq
  rw [← hβ] at r1
  rw [← hγ] at r2
  have hpi := Real.pi_pos
  have hall := thm24_all_triples R a0 ha0 ha1 hA hB
  have Rα : cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) = α := r0
  have Rβ : ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) = β := by rw [ang1]; exact r1
  have Rα' : ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) = α := r0
  rcases hT with hT | hT | hT | hT | hT
  · obtain ⟨T', hc, e0, e1, e2⟩ := hT.s12.canon
    refine concl_of R α β γ r0 r1 r2 T T' hc (hall.1 T' ?_ ?_)
    · exact iso_apex1 T' (by rw [e0, e2]) (by rw [e1]; intro h; linarith)
    · rw [Rα]; exact e0
  · obtain ⟨T', hc, e0, e1, e2⟩ := hT.s01.s12.canon
    refine concl_of R α β γ r0 r1 r2 T T' hc (hall.2.1 T' ?_ ?_)
    · exact iso_apex2 T' (by rw [e0, e1]) (by rw [e2]; intro h; linarith)
    · rw [Rα]; exact e2
  · obtain ⟨T', hc, e0, e1, e2⟩ := hT.s12.s01.canon
    refine concl_of R α β γ r0 r1 r2 T T' hc (hall.2.2.1 T' ?_ ?_)
    · rw [Rβ, ang1]; exact e1
    · rw [Rβ, ang2]; exact e2
  · obtain ⟨T', hc, e0, e1, e2⟩ := hT.s01.s12.s01.canon
    refine concl_of R α β γ r0 r1 r2 T T' hc (hall.2.2.2.1 T' ?_ ?_)
    · rw [Rα', ang1, e1]; ring
    · rw [Rα', ang2]; exact e2
  · obtain ⟨T', hc, e0, e1, e2⟩ := hT.s01.canon
    refine concl_of R α β γ r0 r1 r2 T T' hc (hall.2.2.2.2 T' ?_ ?_)
    · rw [Rβ, ang1]; exact e1
    · rw [Rα', Rβ, ang2]; exact e2

/-! ### Theorem 2.5 as printed -/

/-- **Laczkovich Theorem 2.5, as printed.**  `0 < α < π/3`, `√3 sin α` and `cos α` rational, `β = π/3 - α`, `γ = 2π/3`.
Every triangle `T` whose angles are one of `(α,α,π-2α)`, `(α,2α,π-3α)`, `(α,2β,2α+β)`, `(α,α+β,α+2β)`, `(2α,2β,α+β)`,
`(α+β,α+β,α+β)` is a union of finitely many congruent triangles with angles `(α, β, γ)`. -/
theorem thm25_printed (α β γ : ℝ) (h0 : 0 < α) (h1 : α < Real.pi / 3)
    (hu : ∃ u : ℚ, Real.sqrt 3 * Real.sin α = u) (hv : ∃ v : ℚ, Real.cos α = v)
    (hβ : β = Real.pi / 3 - α) (hγ : γ = 2 * Real.pi / 3) (T : Tri)
    (hT : HasAngles T α α (Real.pi - 2 * α) ∨ HasAngles T α (2 * α) (Real.pi - 3 * α) ∨
      HasAngles T α (2 * β) (2 * α + β) ∨ HasAngles T α (α + β) (α + 2 * β) ∨
      HasAngles T (2 * α) (2 * β) (α + β) ∨ HasAngles T (α + β) (α + β) (α + β)) :
    PrintedConcl T α β γ := by
  obtain ⟨u, hu⟩ := hu
  obtain ⟨v, hv⟩ := hv
  obtain ⟨R, hRγ, r0, r1, r2⟩ := tile25 α h0 h1 u v hu hv
  rw [← hβ] at r1
  rw [← hγ] at r2
  have hpi := Real.pi_pos
  have hall := Erdos634.LaczL34.thm25_all_triples R hRγ
  have Rα : cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) = α := r0
  have Rβ : cornerAngle (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) = β := by
    show ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) = β
    rw [ang1]; exact r1
  rcases hT with hT | hT | hT | hT | hT | hT
  · obtain ⟨T', hc, e0, e1, e2⟩ := hT.s12.canon
    refine concl_of R α β γ r0 r1 r2 T T' hc (hall.1 T' ?_ ?_)
    · exact iso_apex1 T' (by rw [e0, e2]) (by rw [e1]; intro h; linarith)
    · rw [Rα]; exact e0
  · obtain ⟨T', hc, e0, e1, e2⟩ := hT.canon
    refine concl_of R α β γ r0 r1 r2 T T' hc (hall.2.1 T' ?_ ?_)
    · rw [Rα]; exact e0
    · rw [Rα]; show vang T' 1 = _; rw [e1]; ring
  · obtain ⟨T', hc, e0, e1, e2⟩ := hT.canon
    refine concl_of R α β γ r0 r1 r2 T T' hc (hall.2.2.1 T' ?_ ?_)
    · rw [Rα]; exact e0
    · rw [Rβ]; show vang T' 1 = _; rw [e1]; ring
  · obtain ⟨T', hc, e0, e1, e2⟩ := hT.canon
    refine concl_of R α β γ r0 r1 r2 T T' hc (hall.2.2.2.1 T' ?_ ?_)
    · rw [Rα]; exact e0
    · show vang T' 1 = _; rw [e1]; linarith
  · obtain ⟨T', hc, e0, e1, e2⟩ := hT.canon
    refine concl_of R α β γ r0 r1 r2 T T' hc (hall.2.2.2.2.1 T' ?_ ?_)
    · rw [Rα]; show vang T' 0 = _; rw [e0]; ring
    · rw [Rβ]; show vang T' 1 = _; rw [e1]; ring
  · obtain ⟨T', hc, e0, e1, e2⟩ := hT.canon
    refine concl_of R α β γ r0 r1 r2 T T' hc (hall.2.2.2.2.2 T' ?_ ?_)
    · show vang T' 0 = _; rw [e0]; linarith
    · show vang T' 1 = _; rw [e1]; linarith

#print axioms thm24_printed
#print axioms thm25_printed

end Erdos634.LaczL35
