-- Draft/KConjAngle.lean — CASE A, node A3 (Lemma K, K2 half): the ANGLES of a conjugated triangle
-- (PROOF_row0c.md §3.3 (i)+(ii)).
--
--   If T has corners with complex coordinates in K and angle bπ/n at vertex v, then the conjugated
--   triangle Φ(T) (Draft/KConjAe.phiTri, σ(ζ) = ζ^m, m ≡ 1 mod 4) has angle
--        π·y   or   π·(1 − y)   at v,      y = {m b / n}.
--
-- Route (instead of the paper's cotangent rule): the edge ratio q = (z_{v+1} − z_v)/(z_{v+2} − z_v)
-- lies in K and equals |q|·e^{±ibπ/n}; |q| = q·e^{∓ibπ/n} ∈ K is real, so σ(|q|) is real and
-- σ(q) = σ(|q|)·e^{±ibmπ/n} = ρ·e^{±iπy} with ρ real, ρ ≠ 0; the unoriented angle is |arg σ(q)|.
-- Formalization debt on a paper-level PROVED node; NOT /goal progress.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
-- H59: no parameter pair (e, f) is evaluated here.
import Erdos634.Draft.KConjAe
import Mathlib.Analysis.Complex.Angle

open Complex

namespace Erdos634.KConj

open Erdos634.Geometry Erdos634.Geometry.CaseA.LemmaV Erdos634.Geometry.A1Field

/-! ## Pure complex facts -/

theorem arg_exp_I {θ : ℝ} (h1 : -Real.pi < θ) (h2 : θ ≤ Real.pi) :
    arg (Complex.exp ((θ : ℂ) * I)) = θ := by
  rw [arg_exp]
  simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
  rw [toIocMod_eq_self]
  constructor <;> linarith

theorem exp_sub_pi (θ : ℝ) :
    Complex.exp ((θ : ℂ) * I) = -Complex.exp (((θ - Real.pi : ℝ) : ℂ) * I) := by
  have : Complex.exp (((θ - Real.pi : ℝ) : ℂ) * I)
      = Complex.exp ((θ : ℂ) * I) * Complex.exp (-(Real.pi : ℂ) * I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [this, neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]; ring

theorem exp_add_pi (θ : ℝ) :
    Complex.exp ((θ : ℂ) * I) = -Complex.exp (((θ + Real.pi : ℝ) : ℂ) * I) := by
  have : Complex.exp (((θ + Real.pi : ℝ) : ℂ) * I)
      = Complex.exp ((θ : ℂ) * I) * Complex.exp ((Real.pi : ℂ) * I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [this, Complex.exp_pi_mul_I]; ring

/-- `|arg(ρ e^{±iπy})|` is `πy` or `π(1 − y)` for real `ρ ≠ 0`, `0 < y < 1`. -/
theorem abs_arg_phase {ρ y : ℝ} (hρ : ρ ≠ 0) (hy0 : 0 < y) (hy1 : y < 1) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) :
    |arg ((ρ : ℂ) * Complex.exp (((ε * Real.pi * y : ℝ) : ℂ) * I))| = Real.pi * y ∨
    |arg ((ρ : ℂ) * Complex.exp (((ε * Real.pi * y : ℝ) : ℂ) * I))| = Real.pi * (1 - y) := by
  have hp := Real.pi_pos
  rcases lt_or_gt_of_ne hρ with hneg | hpos
  · right
    rcases hε with rfl | rfl
    · rw [exp_sub_pi, mul_neg, ← neg_mul, ← ofReal_neg, arg_real_mul _ (by linarith),
        arg_exp_I (by nlinarith) (by nlinarith), abs_of_neg (by nlinarith)]
      ring
    · rw [exp_add_pi, mul_neg, ← neg_mul, ← ofReal_neg, arg_real_mul _ (by linarith),
        arg_exp_I (by nlinarith) (by nlinarith), abs_of_pos (by nlinarith)]
      ring
  · left
    rcases hε with rfl | rfl
    · rw [arg_real_mul _ hpos, arg_exp_I (by nlinarith) (by nlinarith), abs_of_pos (by nlinarith)]
      ring
    · rw [arg_real_mul _ hpos, arg_exp_I (by nlinarith) (by nlinarith), abs_of_neg (by nlinarith)]
      ring

/-- A corner angle, in complex coordinates. -/
theorem cornerAngle_toC (p q r : Plane) :
    cornerAngle p q r = InnerProductGeometry.angle (toC p - toC q) (toC r - toC q) := by
  rw [cornerAngle, EuclideanGeometry.angle, ← toC.toLinearIsometry.angle_map]
  simp [vsub_eq_sub, map_sub]

/-! ## The phase of a conjugated element -/

variable {n m : ℕ} (hn : 0 < n) (σ : Kf n →ₐ[ℚ] ℂ)
  (hσ : σ (IntermediateField.AdjoinSimple.gen ℚ (zeta n)) = zeta n ^ m) (hm4 : m % 4 = 1)

/-- `y = {m b / n}` as a real number. -/
noncomputable def yf (n m b : ℕ) : ℝ := ((Int.fract ((((m : ℤ) * (b : ℤ) : ℤ) : ℚ) / n) : ℚ) : ℝ)

include hn hσ in
/-- **Phase of σ(q)**: if `|arg q| = bπ/n` then `σ q = ρ e^{±iπy}`, `ρ` real nonzero. -/
theorem sigma_phase (q : Kf n) (hq : q ≠ 0) (b : ℕ)
    (hb : |arg (q : ℂ)| = b * Real.pi / n) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧ ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      σ q = (ρ : ℂ) * Complex.exp (((ε * Real.pi * yf n m b : ℝ) : ℂ) * I) := by
  have hq' : (q : ℂ) ≠ 0 := fun h => hq (Subtype.ext h)
  -- the sign ε of arg q
  obtain ⟨ε, hε, hθ⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ arg (q : ℂ) = ((ε * b : ℤ) : ℝ) * Real.pi / n := by
    rcases abs_eq (by positivity : (0 : ℝ) ≤ b * Real.pi / n) |>.mp hb with h | h
    · exact ⟨1, Or.inl rfl, by rw [h]; push_cast; ring⟩
    · exact ⟨-1, Or.inr rfl, by rw [h]; push_cast; ring⟩
  set E : Kf n := ⟨Complex.exp ((((ε * b : ℤ) : ℝ) * Real.pi / n : ℝ) * I), exp_int_mem hn _⟩
  have hE0 : E ≠ 0 := fun h => Complex.exp_ne_zero _ (congrArg Subtype.val h)
  set R : Kf n := q * E⁻¹
  have hRc : ((R : Kf n) : ℂ) = ((‖(q : ℂ)‖ : ℝ) : ℂ) := by
    have h1 := Complex.norm_mul_exp_arg_mul_I (q : ℂ)
    have hE' : ((E : Kf n) : ℂ) = Complex.exp ((arg (q : ℂ) : ℂ) * I) := by
      show Complex.exp (((((ε * b : ℤ) : ℝ) * Real.pi / n : ℝ)) * I) = _
      rw [hθ]
    rw [show ((R : Kf n) : ℂ) = (q : ℂ) * ((E : Kf n) : ℂ)⁻¹ by simp [R], hE', eq_comm,
      eq_mul_inv_iff_mul_eq₀ (Complex.exp_ne_zero _)]
    exact h1
  have hR0 : R ≠ 0 := mul_ne_zero hq (inv_ne_zero hE0)
  -- σ R is real
  have hreal : (starRingEnd ℂ) (σ R) = σ R := sigma_real σ hσ R (by rw [hRc, Complex.conj_ofReal])
  set r := (σ R).re
  have hr : σ R = (r : ℂ) := (Complex.conj_eq_iff_re.mp hreal).symm
  have hr0 : r ≠ 0 := by
    intro h; rw [h, Complex.ofReal_zero] at hr
    exact hR0 (σ.toRingHom.injective (by rw [map_zero]; exact hr))
  -- σ E
  have hσE := sigma_exp σ hσ hn (ε * b)
  -- decomposition of m b / n
  set x : ℚ := (((m : ℤ) * (b : ℤ) : ℤ) : ℚ) / n
  have hq2 := Int.fract_add_floor x
  have hx : (((ε * b * m : ℤ) : ℝ) * Real.pi / n)
      = (ε : ℝ) * Real.pi * yf n m b + ((ε * ⌊x⌋ : ℤ) : ℝ) * Real.pi := by
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hxr : ((x : ℚ) : ℝ) = (((m : ℤ) * (b : ℤ) : ℤ) : ℝ) / n := by simp [x]
    have hq3 := congrArg (fun t : ℚ => (t : ℝ)) hq2
    simp only [Rat.cast_add, Rat.cast_intCast] at hq3
    have hyf : yf n m b = ((Int.fract x : ℚ) : ℝ) := rfl
    have hmb : (((m : ℤ) * (b : ℤ) : ℤ) : ℝ) = ((Int.fract x : ℚ) : ℝ) * n + (⌊x⌋ : ℝ) * n := by
      rw [← add_mul, hq3, hxr]; field_simp
    have e1 : (((ε * b * m : ℤ) : ℝ)) = (ε : ℝ) * (((m : ℤ) * (b : ℤ) : ℤ) : ℝ) := by push_cast; ring
    have e2 : ((ε * ⌊x⌋ : ℤ) : ℝ) = (ε : ℝ) * (⌊x⌋ : ℝ) := by push_cast; ring
    rw [e1, hmb, hyf, e2]
    field_simp
  refine ⟨r * (-1) ^ ⌊x⌋, ?_, ε, ?_, ?_⟩
  · exact mul_ne_zero hr0 (zpow_ne_zero _ (by norm_num))
  · rcases hε with rfl | rfl <;> simp
  · have hqRE : q = R * E := by simp [R, hE0]
    rw [hqRE, map_mul, hr, hσE]
    have e1 : Complex.exp ((((ε * b * m : ℤ) : ℝ) * Real.pi / n : ℝ) * I)
        = (((-1 : ℝ) ^ ⌊x⌋ : ℝ) : ℂ) * Complex.exp ((((ε : ℝ) * Real.pi * yf n m b : ℝ) : ℂ) * I) := by
      rw [hx]
      push_cast
      rw [add_mul, Complex.exp_add, mul_comm (Complex.exp _)]
      congr 1
      have : ((ε : ℂ) * (⌊x⌋ : ℂ) * (Real.pi : ℂ) * I) = ((ε * ⌊x⌋ : ℤ) : ℂ) * ((Real.pi : ℂ) * I) := by
        push_cast; ring
      rw [this, Complex.exp_int_mul, Complex.exp_pi_mul_I]
      rcases hε with rfl | rfl
      · simp
      · simp only [Int.reduceNeg, neg_mul, one_mul, zpow_neg]
        rw [← inv_zpow, inv_neg, inv_one]
    rw [e1]; push_cast; ring

/-! ## Angles of the conjugated triangle -/

include hσ hm4 in
/-- **Angles of Φ(T).** -/
theorem phi_angle (T : Tri) (hT : ∀ k, toC (T.pts k) ∈ Kf n) (v : Fin 3) (b : ℕ)
    (hb : T.angleAt v = b * Real.pi / n) (hy0 : 0 < yf n m b) :
    (phiTri hn σ hσ hm4 T hT).angleAt v = Real.pi * yf n m b ∨
    (phiTri hn σ hσ hm4 T hT).angleAt v = Real.pi * (1 - yf n m b) := by
  set z : Fin 3 → Kf n := fun k => ⟨toC (T.pts k), hT k⟩
  have hne : ∀ j : Fin 3, j ≠ v → z j - z v ≠ 0 := by
    intro j hj h
    have h' : toC (T.pts j) = toC (T.pts v) := by
      have := congrArg Subtype.val h; simpa [z, sub_eq_zero] using this
    exact hj (T.indep.injective (toC.injective h'))
  have h1 : v + 1 ≠ v := (by decide : ∀ w : Fin 3, w + 1 ≠ w) v
  have h2 : v + 2 ≠ v := (by decide : ∀ w : Fin 3, w + 2 ≠ w) v
  set q : Kf n := (z (v + 1) - z v) / (z (v + 2) - z v)
  have hq0 : q ≠ 0 := div_ne_zero (hne _ h1) (hne _ h2)
  have hcoe : ∀ j, ((z j - z v : Kf n) : ℂ) ≠ 0 → True := fun _ _ => trivial
  have hzne : ∀ j : Fin 3, j ≠ v → ((z j : ℂ) - (z v : ℂ)) ≠ 0 := by
    intro j hj h; apply hne j hj; ext; simpa using h
  -- the original angle
  have hang : T.angleAt v = |arg (q : ℂ)| := by
    rw [Tri.angleAt, cornerAngle_toC, Complex.angle_eq_abs_arg (hzne _ h1) (hzne _ h2)]
    simp [q, z]
  rw [hang] at hb
  obtain ⟨ρ, hρ, ε, hε, hσq⟩ := sigma_phase hn σ hσ q hq0 b hb
  -- the conjugated angle
  have hzne' : ∀ j : Fin 3, j ≠ v → σ (z j) - σ (z v) ≠ 0 := by
    intro j hj h
    rw [← map_sub] at h
    exact hne j hj (σ.toRingHom.injective (by rw [map_zero]; exact h))
  have hang' : (phiTri hn σ hσ hm4 T hT).angleAt v = |arg (σ q)| := by
    rw [Tri.angleAt, cornerAngle_toC, toC_phiTri, toC_phiTri, toC_phiTri]
    show InnerProductGeometry.angle (σ (z (v + 1)) - σ (z v)) (σ (z (v + 2)) - σ (z v)) = _
    rw [Complex.angle_eq_abs_arg (hzne' _ h1) (hzne' _ h2)]
    simp [q, map_div₀, map_sub, sw, z]
  have hy1 : yf n m b < 1 := by
    rw [yf]; exact_mod_cast Int.fract_lt_one _
  rw [hang', hσq]
  exact abs_arg_phase hρ hy0 hy1 hε

end Erdos634.KConj

#print axioms Erdos634.KConj.abs_arg_phase
#print axioms Erdos634.KConj.sigma_phase
#print axioms Erdos634.KConj.phi_angle
