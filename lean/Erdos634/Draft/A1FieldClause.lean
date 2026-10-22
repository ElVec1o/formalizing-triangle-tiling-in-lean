-- Draft/A1FieldClause.lean — row0c Lemma 1 (node A1), the field clause "L ⊂ ℚ(ζ_{4n})", and the
-- full Lemma 1 as written (PROOF_row0c.md §2 L1 row; P2 L1 row).
--
-- Formalization debt on a paper-level PROVED result; NOT /goal progress.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
-- H59: no (e, f) evaluated.
--
-- Normalized frame.  `circD T = |side opp. 0| / sin(angle 0)` is the circumdiameter (law of sines:
-- every side is `circD · sin(opposite angle)`); `wAB D = (B − A)/|B − A|` in ℂ; the coordinate map is
-- `zc D P = (P − A)·wAB⁻¹ / circD`.  Then `zc A = 0`, `zc B ∈ ℝ>0`, the side lengths become
-- `s_i = sin(a_i π/n)`, and every tile corner lies in `Lpaper n a = Σ ℤ sin(a_k π/n) e^{ijπ/n}`
-- (`j ∈ ℤ`), which lies in `Kf n = ℚ(ζ_{4n}) ⊂ ℂ` (`CaseALemmaVSines.Kf`, the cyclotomic field
-- used by Lemma V).
-- Route: `A1Pos.lemma1_positions` (frame-free) pushed through the additive map `zc`; generators of
-- `Lform` map to generators of `Lpaper` (law of sines + angle coset); `sin`, `e^{ijπ/n}` are
-- Laurent polynomials in `ζ_{4n}`.
import Erdos634.Draft.A1CornerLattice

open scoped Classical

namespace Erdos634.Geometry.A1Field

open Erdos634.Geometry Complex
open Erdos634.Geometry.CaseA.LemmaV (zeta Kf zeta_pow_n law_sines angle_pos angle_lt_pi)

variable {N : ℕ}

/-! ## Membership in `ℚ(ζ_{4n})` -/

theorem zeta_mem (n : ℕ) : zeta n ∈ Kf n := IntermediateField.mem_adjoin_simple_self ℚ _

theorem exp_int_mem {n : ℕ} (hn : 0 < n) (j : ℤ) :
    Complex.exp (((j : ℝ) * Real.pi / n : ℝ) * I) ∈ Kf n := by
  have h : Complex.exp (((j : ℝ) * Real.pi / n : ℝ) * I) = zeta n ^ (2 * j) := by
    rw [zeta, ← Complex.exp_int_mul]
    congr 1
    have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast; field_simp; ring
  rw [h]; exact zpow_mem (zeta_mem n) _

theorem sin_mem {n : ℕ} (hn : 0 < n) (a : ℕ) :
    ((Real.sin ((a : ℝ) * Real.pi / n) : ℝ) : ℂ) ∈ Kf n := by
  have hI : I ∈ Kf n := by rw [← zeta_pow_n hn]; exact pow_mem (zeta_mem n) n
  have e1 := exp_int_mem hn (a : ℤ)
  have e2 := exp_int_mem hn (-(a : ℤ))
  have h : ((Real.sin ((a : ℝ) * Real.pi / n) : ℝ) : ℂ)
      = (Complex.exp ((((-(a : ℤ) : ℤ) : ℝ) * Real.pi / n : ℝ) * I)
          - Complex.exp ((((a : ℤ) : ℝ) * Real.pi / n : ℝ) * I)) * I * (1 + 1)⁻¹ := by
    rw [Complex.ofReal_sin, Complex.sin]; push_cast; ring_nf
  rw [h]
  exact mul_mem (mul_mem (sub_mem e2 e1) hI) (inv_mem (add_mem (one_mem _) (one_mem _)))

/-! ## The circumdiameter (law of sines) -/

/-- The circumdiameter `λ` of a triangle: `|side opposite vertex 0| / sin(angle at 0)`. -/
noncomputable def circD (T : Tri) : ℝ := T.oppLen 0 / Real.sin (T.angleAt 0)

theorem sin_angle_pos (T : Tri) (k : Fin 3) : 0 < Real.sin (T.angleAt k) :=
  Real.sin_pos_of_pos_of_lt_pi (angle_pos T k) (angle_lt_pi T k)

theorem circD_pos (T : Tri) : 0 < circD T := by
  have h12 : T.pts 1 ≠ T.pts 2 := fun h => absurd (T.indep.injective h) (by decide)
  exact div_pos (dist_pos.mpr h12) (sin_angle_pos T 0)

/-- **Law of sines**: every side is `λ · sin(opposite angle)`. -/
theorem oppLen_eq (T : Tri) (k : Fin 3) : T.oppLen k = circD T * Real.sin (T.angleAt k) := by
  have hs := (sin_angle_pos T 0).ne'
  have h0 : Real.sin (T.angleAt 1) * T.oppLen 0 = Real.sin (T.angleAt 0) * T.oppLen 1 :=
    law_sines T 0
  have h2 := law_sines T 2
  have e : (2 : Fin 3) + 1 = 0 := rfl
  rw [e] at h2
  unfold circD
  fin_cases k
  · show T.oppLen 0 = T.oppLen 0 / Real.sin (T.angleAt 0) * Real.sin (T.angleAt 0)
    field_simp
  · show T.oppLen 1 = T.oppLen 0 / Real.sin (T.angleAt 0) * Real.sin (T.angleAt 1)
    field_simp; linarith
  · show T.oppLen 2 = T.oppLen 0 / Real.sin (T.angleAt 0) * Real.sin (T.angleAt 2)
    field_simp; linarith

/-! ## The normalized frame -/

/-- `e^{iθ₀}`, `θ₀ = dir(AB)`, as a unit complex number. -/
noncomputable def wAB (D : CongruentDissection N) : ℂ :=
  ((‖D.target.pts 1 - D.target.pts 0‖⁻¹ : ℝ) : ℂ) * toC (D.target.pts 1 - D.target.pts 0)

/-- The paper's coordinate: `z(P) = e^{−iθ₀}(P − A)/λ`. -/
noncomputable def zc (D : CongruentDissection N) (P : Plane) : ℂ :=
  toC (P - D.target.pts 0) * ((wAB D)⁻¹ / ((circD D.model : ℝ) : ℂ))

/-- The paper's `L = Σ_{i, j ∈ ℤ} ℤ s_i e^{ijπ/n}`, `s_i = sin(a_i π/n)`. -/
noncomputable def Lpaper (n : ℕ) (a : Fin 3 → ℕ) : AddSubgroup ℂ :=
  AddSubgroup.closure {x | ∃ (k : Fin 3) (j : ℤ),
    x = ((Real.sin ((a k : ℝ) * Real.pi / n) : ℝ) : ℂ) * Complex.exp (((j : ℝ) * Real.pi / n : ℝ) * I)}

theorem AB_ne (D : CongruentDissection N) : D.target.pts 1 - D.target.pts 0 ≠ 0 :=
  sub_ne_zero.mpr fun h => absurd (D.target.indep.injective h) (by decide)

theorem norm_wAB (D : CongruentDissection N) : ‖wAB D‖ = 1 := by
  have hx : ‖D.target.pts 1 - D.target.pts 0‖ ≠ 0 := norm_ne_zero_iff.mpr (AB_ne D)
  rw [wAB, norm_mul, Complex.norm_real, LinearIsometryEquiv.norm_map, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hx]

theorem wAB_ne (D : CongruentDissection N) : wAB D ≠ 0 := by
  intro h; have := norm_wAB D; rw [h, norm_zero] at this; norm_num at this

theorem arg_wAB (D : CongruentDissection N) {n : ℕ} (hn : 0 < n) :
    ((arg (wAB D) : ℝ) : Real.Angle) - (D.target.leftUnit 0).angle ∈ A1Dir.H n := by
  have hpos : 0 < ‖D.target.pts 1 - D.target.pts 0‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr (AB_ne D))
  rw [wAB, Complex.arg_real_mul _ hpos, Tri.leftUnit_angle]
  have e01 : (0 : Fin 3) + 1 = 1 := rfl
  rcases D.target.leftDir_eq_or 0 with h | h <;> rw [e01] at h
  · rw [h]; simp
  · rw [h, map_neg, Complex.arg_neg_coe_angle (toC_ne_zero (AB_ne D))]
    have := neg_mem (A1Dir.pi_mem hn)
    convert this using 1
    abel

theorem exp_eq_of_angle {x y : ℝ} (h : (x : Real.Angle) = y) :
    Complex.exp ((x : ℂ) * I) = Complex.exp ((y : ℂ) * I) := by
  have hc : Real.cos x = Real.cos y := by rw [← Real.Angle.cos_coe, h, Real.Angle.cos_coe]
  have hs : Real.sin x = Real.sin y := by rw [← Real.Angle.sin_coe, h, Real.Angle.sin_coe]
  rw [Complex.exp_mul_I, Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin, ← ofReal_cos,
    ← ofReal_sin, hc, hs]

theorem unit_eq_exp {u : ℂ} (hu : ‖u‖ = 1) : u = Complex.exp ((arg u : ℂ) * I) := by
  have := Complex.norm_mul_exp_arg_mul_I u
  rw [hu] at this
  simpa using this.symm

/-- A unit `u` whose argument differs from `arg w` by an element of `(π/n)ℤ`: `u w⁻¹ = e^{ijπ/n}`. -/
theorem rot_eq {n : ℕ} {u w : ℂ} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (h : ((arg u : ℝ) : Real.Angle) - (arg w : Real.Angle) ∈ A1Dir.H n) :
    ∃ j : ℤ, u * w⁻¹ = Complex.exp (((j : ℝ) * Real.pi / n : ℝ) * I) := by
  obtain ⟨j, hj⟩ := AddSubgroup.mem_zmultiples_iff.mp h
  refine ⟨j, ?_⟩
  rw [unit_eq_exp hu, unit_eq_exp hw, ← Complex.exp_neg, ← Complex.exp_add]
  have hang : ((arg u - arg w : ℝ) : Real.Angle) = (((j : ℝ) * Real.pi / n : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_sub, ← hj, ← Real.Angle.coe_zsmul, zsmul_eq_mul]
    congr 1; ring
  have := exp_eq_of_angle hang
  rw [← this]; congr 1; push_cast; ring

/-- **Normalized-frame positions**: `zc` maps `A + Lform` into `Lpaper`. -/
theorem Lform_map (D : CongruentDissection N) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) :
    ∀ v ∈ A1Pos.Lform D n, toC v * ((wAB D)⁻¹ / ((circD D.model : ℝ) : ℂ)) ∈ Lpaper n a := by
  set c : ℂ := (wAB D)⁻¹ / ((circD D.model : ℝ) : ℂ) with hcdef
  let f : Plane →+ ℂ := AddMonoidHom.mk' (fun v => toC v * c) (fun x y => by
    simp only [map_add, add_mul])
  have hL : ((circD D.model : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (circD_pos D.model).ne'
  have hle : A1Pos.Lform D n ≤ (Lpaper n a).comap f := by
    rw [A1Pos.Lform, AddSubgroup.closure_le]
    rintro _ ⟨k, d, hd, rfl⟩
    show toC (dist (D.model.pts k) (D.model.pts (k + 1)) • d.1) * c ∈ Lpaper n a
    have hsd : dist (D.model.pts k) (D.model.pts (k + 1)) = D.model.oppLen (k + 2) := by
      have e1 : k + 2 + 1 = k := by revert k; decide
      have e2 : k + 2 + 2 = k + 1 := by revert k; decide
      rw [Tri.oppLen, e1, e2]
    have hu : ‖toC d.1‖ = 1 := by rw [LinearIsometryEquiv.norm_map]; exact d.2
    have hdiff : ((arg (toC d.1) : ℝ) : Real.Angle) - (arg (wAB D) : Real.Angle) ∈ A1Dir.H n := by
      have := sub_mem hd (arg_wAB D hn)
      convert this using 1
      show _ = (Dir.angle d) - _ - _
      unfold Dir.angle; abel
    obtain ⟨j, hj⟩ := rot_eq hu (norm_wAB D) hdiff
    have hval : toC (dist (D.model.pts k) (D.model.pts (k + 1)) • d.1) * c
        = ((Real.sin ((a (k + 2) : ℝ) * Real.pi / n) : ℝ) : ℂ)
            * Complex.exp (((j : ℝ) * Real.pi / n : ℝ) * I) := by
      rw [map_smul, Complex.real_smul, hsd, oppLen_eq, ha, ← hj, hcdef]
      push_cast
      field_simp
    rw [hval]
    exact AddSubgroup.subset_closure ⟨k + 2, j, rfl⟩
  intro v hv
  exact hle hv

/-- **The field clause**: `L ⊂ ℚ(ζ_{4n})`. -/
theorem Lpaper_le {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ) : ∀ x ∈ Lpaper n a, x ∈ Kf n := by
  intro x hx
  have hle : Lpaper n a ≤ (Kf n).toSubfield.toSubring.toAddSubgroup := by
    rw [Lpaper, AddSubgroup.closure_le]
    rintro _ ⟨k, j, rfl⟩
    exact (show _ ∈ Kf n from mul_mem (sin_mem hn (a k)) (exp_int_mem hn j))
  exact hle hx

theorem zc_A (D : CongruentDissection N) : zc D (D.target.pts 0) = 0 := by
  simp [zc]

theorem zc_B (D : CongruentDissection N) :
    zc D (D.target.pts 1)
      = ((dist (D.target.pts 1) (D.target.pts 0) / circD D.model : ℝ) : ℂ) := by
  have hx := AB_ne D
  have hn : (‖D.target.pts 1 - D.target.pts 0‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr hx
  have hz := toC_ne_zero hx
  have hL : ((circD D.model : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (circD_pos D.model).ne'
  rw [zc, wAB, dist_eq_norm]
  push_cast
  field_simp

/-- **Lemma 1 as written (row0c §2 L1; P2 L1).**  With `A = 0`, `AB` along `ℝ>0` and the tile at
circumdiameter 1 (coordinate `zc`), the side lengths are `s_i = sin(a_i π/n)` and every tile corner
(and every target corner) lies in `L = Σ ℤ s_i e^{ijπ/n}`, and `L ⊂ ℚ(ζ_{4n})`.  The frame-free
form (`A + Lform`) is included. -/
theorem lemma1_full (D : CongruentDissection N) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) :
    0 < circD D.model ∧
    (∀ k, D.model.oppLen k = circD D.model * Real.sin ((a k : ℝ) * Real.pi / n)) ∧
    zc D (D.target.pts 0) = 0 ∧
    zc D (D.target.pts 1) = ((dist (D.target.pts 1) (D.target.pts 0) / circD D.model : ℝ) : ℂ) ∧
    0 < dist (D.target.pts 1) (D.target.pts 0) / circD D.model ∧
    (∀ i k, (D.tile i).pts k - D.target.pts 0 ∈ A1Pos.Lform D n) ∧
    (∀ i k, zc D ((D.tile i).pts k) ∈ Lpaper n a) ∧
    (∀ k, zc D (D.target.pts k) ∈ Lpaper n a) ∧
    (∀ x ∈ Lpaper n a, x ∈ Kf n) := by
  refine ⟨circD_pos _, fun k => by rw [oppLen_eq, ha], zc_A D, zc_B D, ?_,
    A1Pos.lemma1_positions D hn a ha, fun i k => ?_, fun k => ?_, Lpaper_le hn a⟩
  · exact div_pos (dist_pos.mpr fun h => absurd (D.target.indep.injective h) (by decide))
      (circD_pos _)
  · exact Lform_map D hn a ha _ (A1Pos.lemma1_positions D hn a ha i k)
  · exact Lform_map D hn a ha _ (A1Pos.lemma1_positions_target D hn a ha k)

/-- Witness: the real `CongruentDissection 2` of `CaseALemmaHPiFour` (n = 4, angles (1,2,1)·π/4)
satisfies every hypothesis of `lemma1_full`. -/
theorem lemma1_full_witness :
    (∀ i k, zc Erdos634.Draft.CaseALemmaHPiFour.dissection
        ((Erdos634.Draft.CaseALemmaHPiFour.dissection.tile i).pts k) ∈ Lpaper 4 ![1, 2, 1]) ∧
      ∀ x ∈ Lpaper 4 ![1, 2, 1], x ∈ Kf 4 :=
  have h := lemma1_full Erdos634.Draft.CaseALemmaHPiFour.dissection (n := 4) (by norm_num)
    ![1, 2, 1] Erdos634.Draft.CaseALemmaVWitness.model_angles
  ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

end Erdos634.Geometry.A1Field

#print axioms Erdos634.Geometry.A1Field.Lpaper_le
#print axioms Erdos634.Geometry.A1Field.Lform_map
#print axioms Erdos634.Geometry.A1Field.lemma1_full
#print axioms Erdos634.Geometry.A1Field.lemma1_full_witness
