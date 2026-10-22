-- Draft/F1EdgeAlign.lean — BLOCKER-K1: wire wedge_forces_ray_eq to CongruentDissection.
--
-- Provides:
--   `tri_corner_cone_of_mem`      — if q ∈ T.carrier then q−T.pts 0 is a
--                                   nonneg combination of the two edge directions.
--   `tri_corner_cone_of_mem'`     — generalisation to any vertex k (not just 0).
--   `nonneg_comb_oangle_mem_uIcc` — if w = r₁•u + r₂•v with r₁,r₂ ≥ 0 and
--                                   angle(u,v) = β ∈ (0,π) then
--                                   (o.oangle u w).toReal ∈ uIcc 0 (o.oangle u v).toReal.
--
-- Together these discharge the two sub-hypotheses of `wedge_forces_ray_eq`
-- (CornerParaLink.lean) when u',v' are "other vertices of T₁ seen from V₁."
--
-- Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).  ZERO sorry.

import Erdos634.Dissection
import Erdos634.CornerParaLink
import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

open scoped Classical
open Real (pi pi_pos)

namespace Erdos634.Geometry

/-! ### Barycentric cone at a triangle vertex -/

/-- If a point `q` lies in the carrier of `T`, then the displacement `q − T.pts 0` is a
    nonneg-coefficient combination of the two edge directions. -/
theorem tri_corner_cone_of_mem (T : Tri) (q : Plane) (hq : q ∈ T.carrier) :
    ∃ c₁ c₂ : ℝ, 0 ≤ c₁ ∧ 0 ≤ c₂ ∧
      q - T.pts 0 = c₁ • (T.pts 1 - T.pts 0) + c₂ • (T.pts 2 - T.pts 0) := by
  rw [T.carrier_eq_nonneg_coord] at hq
  refine ⟨T.basis.coord 1 q, T.basis.coord 2 q, hq 1, hq 2, ?_⟩
  have hcomb : ∑ i : Fin 3, T.basis.coord i q • T.pts i = q :=
    T.basis.linear_combination_coord_eq_self q
  have hsum : ∑ i : Fin 3, T.basis.coord i q = 1 :=
    T.basis.sum_coord_apply_eq_one q
  have hkey : q - T.pts 0 =
      ∑ i : Fin 3, T.basis.coord i q • (T.pts i - T.pts 0) := by
    have : ∑ i : Fin 3, T.basis.coord i q • (T.pts i - T.pts 0) =
        (∑ i : Fin 3, T.basis.coord i q • T.pts i) -
        (∑ i : Fin 3, T.basis.coord i q • T.pts 0) := by
      simp [smul_sub, Finset.sum_sub_distrib]
    rw [this, hcomb, ← Finset.sum_smul, hsum, one_smul]
  simp only [Fin.sum_univ_three] at hkey
  simp only [sub_self, smul_zero, zero_add] at hkey
  exact hkey

/-! ### Per-vertex helpers for `tri_corner_cone_of_mem'`
    Each uses only Fin numerals (no free `k`), so `Fin.sum_univ_three` + `sub_self` work cleanly. -/

private lemma tri_corner_cone_k0 (T : Tri) (q : Plane)
    (hq : ∀ i : Fin 3, 0 ≤ T.basis.coord i q) :
    ∃ c₁ c₂ : ℝ, 0 ≤ c₁ ∧ 0 ≤ c₂ ∧
      q - T.pts 0 = c₁ • (T.pts 1 - T.pts 0) + c₂ • (T.pts 2 - T.pts 0) := by
  refine ⟨T.basis.coord 1 q, T.basis.coord 2 q, hq 1, hq 2, ?_⟩
  have hcomb : ∑ i : Fin 3, T.basis.coord i q • T.pts i = q :=
    T.basis.linear_combination_coord_eq_self q
  have hsum : ∑ i : Fin 3, T.basis.coord i q = 1 :=
    T.basis.sum_coord_apply_eq_one q
  have hkey : q - T.pts 0 = ∑ i : Fin 3, T.basis.coord i q • (T.pts i - T.pts 0) := by
    have : ∑ i : Fin 3, T.basis.coord i q • (T.pts i - T.pts 0) =
        (∑ i : Fin 3, T.basis.coord i q • T.pts i) -
        (∑ i : Fin 3, T.basis.coord i q • T.pts 0) := by
      simp [smul_sub, Finset.sum_sub_distrib]
    rw [this, hcomb, ← Finset.sum_smul, hsum, one_smul]
  simp only [Fin.sum_univ_three, sub_self, smul_zero, zero_add] at hkey; exact hkey

private lemma tri_corner_cone_k1 (T : Tri) (q : Plane)
    (hq : ∀ i : Fin 3, 0 ≤ T.basis.coord i q) :
    ∃ c₁ c₂ : ℝ, 0 ≤ c₁ ∧ 0 ≤ c₂ ∧
      q - T.pts 1 = c₁ • (T.pts 2 - T.pts 1) + c₂ • (T.pts 0 - T.pts 1) := by
  refine ⟨T.basis.coord 2 q, T.basis.coord 0 q, hq 2, hq 0, ?_⟩
  have hcomb : ∑ i : Fin 3, T.basis.coord i q • T.pts i = q :=
    T.basis.linear_combination_coord_eq_self q
  have hsum : ∑ i : Fin 3, T.basis.coord i q = 1 :=
    T.basis.sum_coord_apply_eq_one q
  have hkey : q - T.pts 1 = ∑ i : Fin 3, T.basis.coord i q • (T.pts i - T.pts 1) := by
    have : ∑ i : Fin 3, T.basis.coord i q • (T.pts i - T.pts 1) =
        (∑ i : Fin 3, T.basis.coord i q • T.pts i) -
        (∑ i : Fin 3, T.basis.coord i q • T.pts 1) := by
      simp [smul_sub, Finset.sum_sub_distrib]
    rw [this, hcomb, ← Finset.sum_smul, hsum, one_smul]
  -- hkey: q - T.pts 1 = coord 0 q • (T.pts 0 - T.pts 1) + coord 2 q • (T.pts 2 - T.pts 1)
  -- Goal needs the two summands swapped.
  simp only [Fin.sum_univ_three, sub_self, smul_zero, add_zero] at hkey
  rw [add_comm] at hkey; exact hkey

private lemma tri_corner_cone_k2 (T : Tri) (q : Plane)
    (hq : ∀ i : Fin 3, 0 ≤ T.basis.coord i q) :
    ∃ c₁ c₂ : ℝ, 0 ≤ c₁ ∧ 0 ≤ c₂ ∧
      q - T.pts 2 = c₁ • (T.pts 0 - T.pts 2) + c₂ • (T.pts 1 - T.pts 2) := by
  refine ⟨T.basis.coord 0 q, T.basis.coord 1 q, hq 0, hq 1, ?_⟩
  have hcomb : ∑ i : Fin 3, T.basis.coord i q • T.pts i = q :=
    T.basis.linear_combination_coord_eq_self q
  have hsum : ∑ i : Fin 3, T.basis.coord i q = 1 :=
    T.basis.sum_coord_apply_eq_one q
  have hkey : q - T.pts 2 = ∑ i : Fin 3, T.basis.coord i q • (T.pts i - T.pts 2) := by
    have : ∑ i : Fin 3, T.basis.coord i q • (T.pts i - T.pts 2) =
        (∑ i : Fin 3, T.basis.coord i q • T.pts i) -
        (∑ i : Fin 3, T.basis.coord i q • T.pts 2) := by
      simp [smul_sub, Finset.sum_sub_distrib]
    rw [this, hcomb, ← Finset.sum_smul, hsum, one_smul]
  simp only [Fin.sum_univ_three, sub_self, smul_zero, add_zero] at hkey; exact hkey

/-- **Generalised barycentric cone at any vertex.**
    If `q ∈ T.carrier`, then `q − T.pts k` is a nonneg combination of the two edge
    directions at vertex `k`, for any `k : Fin 3`. -/
theorem tri_corner_cone_of_mem' (T : Tri) (k : Fin 3) (q : Plane) (hq : q ∈ T.carrier) :
    ∃ c₁ c₂ : ℝ, 0 ≤ c₁ ∧ 0 ≤ c₂ ∧
      q - T.pts k = c₁ • (T.pts (k + 1) - T.pts k) + c₂ • (T.pts (k + 2) - T.pts k) := by
  rw [T.carrier_eq_nonneg_coord] at hq
  -- Dispatch to per-vertex helpers; `exact` uses isDefEq which handles Fin arithmetic
  -- and proof irrelevance to unify `T.pts ⟨j,h⟩` with `T.pts j` (numeral).
  fin_cases k
  · exact tri_corner_cone_k0 T q hq
  · exact tri_corner_cone_k1 T q hq
  · exact tri_corner_cone_k2 T q hq

/-! ### Helper: same-sign product is nonneg -/

private lemma mul_nonneg_of_sign_eq {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : SignType.sign x = SignType.sign y) : 0 ≤ x * y := by
  rcases lt_trichotomy x 0 with hnx | rfl | hpx
  · have hny : y < 0 := by
      by_contra hge
      push Not at hge
      rcases hge.lt_or_eq with hpy | rfl
      · rw [sign_neg hnx, sign_pos hpy] at h; exact absurd h (by decide)
      · exact hy rfl
    nlinarith
  · exact absurd rfl hx
  · have hpy : 0 < y := by
      by_contra hle
      push Not at hle
      rcases hle.lt_or_eq with hny | rfl
      · rw [sign_pos hpx, sign_neg hny] at h; exact absurd h (by decide)
      · exact hy rfl
    exact mul_nonneg hpx.le hpy.le

/-! ### Oriented angle of a nonneg combination lies in the wedge -/

section NonnegCombOangle

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))

/-- **Wedge membership for nonneg combinations.**
    If `w = r₁ • u + r₂ • v` with `r₁, r₂ ≥ 0`, `w ≠ 0`, `u ≠ 0`, `v ≠ 0`, and
    `InnerProductGeometry.angle u v = β ∈ (0, π)`, then
    `(o.oangle u w).toReal ∈ Set.uIcc 0 (o.oangle u v).toReal`. -/
theorem nonneg_comb_oangle_mem_uIcc
    {u v w : V} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂)
    (heq : w = r₁ • u + r₂ • v)
    {β : ℝ} (hβ0 : 0 < β) (hβπ : β < Real.pi)
    (hangle : InnerProductGeometry.angle u v = β) :
    (o.oangle u w).toReal ∈ Set.uIcc 0 (o.oangle u v).toReal := by
  set σ := (o.oangle u v).toReal with hσdef
  have hσ_abs : |σ| = β := by
    rw [hσdef, ← hangle, o.angle_eq_abs_oangle_toReal hu hv]
  have hσ_ne0 : σ ≠ 0 := by intro h; rw [h, abs_zero] at hσ_abs; linarith
  have hσ_ne_pi_angle : o.oangle u v ≠ ↑Real.pi := by
    intro h
    have : σ = Real.pi := by rw [hσdef, h, Real.Angle.toReal_pi]
    rw [this, abs_of_pos (by linarith)] at hσ_abs; linarith
  have hσ_ne_zero_angle : o.oangle u v ≠ 0 := by
    intro h
    have : σ = 0 := by rw [hσdef, h]; simp
    exact hσ_ne0 this
  have hσ_sign_ne0 : (o.oangle u v).sign ≠ 0 :=
    Real.Angle.sign_ne_zero_iff.mpr ⟨hσ_ne_zero_angle, hσ_ne_pi_angle⟩
  -- Helper: from sign(oangle) = sign(σ), derive toReal sign = sign(σ) as SignType
  have hσ_toReal_sign : SignType.sign σ = (o.oangle u v).sign :=
    Real.Angle.sign_toReal hσ_ne_pi_angle
  rcases hr₂.lt_or_eq with hr₂pos | rfl
  · -- r₂ > 0
    have hs_sign : (o.oangle u w).sign = (o.oangle u v).sign := by
      rw [heq, o.oangle_sign_smul_add_smul_right u v r₁ r₂, sign_pos hr₂pos, one_mul]
    have hs_ne_pi : o.oangle u w ≠ ↑Real.pi := by
      intro h; simp [h] at hs_sign; exact hσ_sign_ne0 hs_sign.symm
    have hs_ne0 : o.oangle u w ≠ 0 := by
      intro h; simp [h] at hs_sign; exact hσ_sign_ne0 hs_sign.symm
    -- sign of s = sign of σ (as real numbers)
    have hs_toReal_sign : SignType.sign (o.oangle u w).toReal = SignType.sign σ := by
      rw [Real.Angle.sign_toReal hs_ne_pi, hs_sign, ← hσ_toReal_sign]
    -- 0 ≤ s * σ
    have hs_signum : 0 ≤ (o.oangle u w).toReal * σ := by
      apply mul_nonneg_of_sign_eq
      · intro h; exact hs_ne0 (Real.Angle.toReal_eq_zero_iff.mp h)
      · exact hσ_ne0
      · exact hs_toReal_sign
    -- sign(oangle w v) ≠ π; handle r₁ = 0 and r₁ > 0
    have ht_ne_pi : o.oangle w v ≠ ↑Real.pi := by
      rcases hr₁.lt_or_eq with hr₁pos | rfl
      · have hts : (o.oangle w v).sign = (o.oangle u v).sign := by
          rw [heq, o.oangle_sign_smul_add_smul_left u v r₁ r₂, sign_pos hr₁pos, one_mul]
        intro h; simp [h] at hts; exact hσ_sign_ne0 hts.symm
      · have hw_eq : w = r₂ • v := by rw [heq]; simp
        have : o.oangle w v = 0 := by
          rw [hw_eq]; exact o.oangle_smul_left_self_of_nonneg v (le_of_lt hr₂pos)
        intro h; rw [this] at h; exact Real.Angle.pi_ne_zero h.symm
    -- 0 ≤ t * σ
    have ht_signum : 0 ≤ (o.oangle w v).toReal * σ := by
      rcases hr₁.lt_or_eq with hr₁pos | rfl
      · have hts : (o.oangle w v).sign = (o.oangle u v).sign := by
          rw [heq, o.oangle_sign_smul_add_smul_left u v r₁ r₂, sign_pos hr₁pos, one_mul]
        have ht_ne0 : o.oangle w v ≠ 0 := by
          intro h; simp [h] at hts; exact hσ_sign_ne0 hts.symm
        have ht_toReal_sign : SignType.sign (o.oangle w v).toReal = SignType.sign σ := by
          rw [Real.Angle.sign_toReal ht_ne_pi, hts, ← hσ_toReal_sign]
        apply mul_nonneg_of_sign_eq
        · intro h; exact ht_ne0 (Real.Angle.toReal_eq_zero_iff.mp h)
        · exact hσ_ne0
        · exact ht_toReal_sign
      · -- r₁ = 0: w = r₂•v, oangle(w,v) = 0
        have hw_eq : w = r₂ • v := by rw [heq]; simp
        have : (o.oangle w v).toReal = 0 := by
          have : o.oangle w v = 0 := by
            rw [hw_eq]; exact o.oangle_smul_left_self_of_nonneg v (le_of_lt hr₂pos)
          simp [this]
        simp [this]
    -- s + t = σ (as reals): use oangle_add + toReal_add_eq_toReal_add_toReal
    have hadd : o.oangle u w + o.oangle w v = o.oangle u v :=
      o.oangle_add hu hw hv
    have hsign_cond : (o.oangle u w).sign ≠ (o.oangle w v).sign ∨
        (o.oangle u w).sign = (o.oangle u w + o.oangle w v).sign := by
      right; rw [hadd, hs_sign]
    have hst_sum : (o.oangle u w).toReal + (o.oangle w v).toReal = σ := by
      have := Real.Angle.toReal_add_eq_toReal_add_toReal hs_ne_pi ht_ne_pi hsign_cond
      rw [hadd] at this; linarith [this.symm]
    -- Conclude: s ∈ uIcc 0 σ
    rw [Set.mem_uIcc]
    rcases lt_or_ge σ 0 with hσ_neg | hσ_nn
    · right
      have hs_np : (o.oangle u w).toReal ≤ 0 := by
        rcases le_or_gt (o.oangle u w).toReal 0 with h | h; exact h
        linarith [mul_pos h (neg_pos.mpr hσ_neg)]
      have ht_np : (o.oangle w v).toReal ≤ 0 := by
        rcases le_or_gt (o.oangle w v).toReal 0 with h | h; exact h
        linarith [mul_pos h (neg_pos.mpr hσ_neg)]
      exact ⟨by linarith, hs_np⟩
    · left
      have hσ_pos : 0 < σ := lt_of_le_of_ne hσ_nn (Ne.symm hσ_ne0)
      have hs_nn : 0 ≤ (o.oangle u w).toReal := by
        rcases le_or_gt 0 (o.oangle u w).toReal with h | h; exact h
        linarith [mul_neg_of_neg_of_pos h hσ_pos, hs_signum]
      have ht_nn : 0 ≤ (o.oangle w v).toReal := by
        rcases le_or_gt 0 (o.oangle w v).toReal with h | h; exact h
        linarith [mul_neg_of_neg_of_pos h hσ_pos, ht_signum]
      exact ⟨hs_nn, by linarith⟩
  · -- r₂ = 0: w = r₁ • u (r₁ > 0 since w ≠ 0)
    rcases hr₁.lt_or_eq with hr₁pos | rfl
    · have hw_eq : w = r₁ • u := by rw [heq]; simp
      have : (o.oangle u w).toReal = 0 := by
        have h : o.oangle u w = 0 := by
          rw [hw_eq]; exact o.oangle_smul_right_self_of_nonneg u (le_of_lt hr₁pos)
        simp [h]
      rw [this]; exact Set.left_mem_uIcc
    · exfalso; apply hw; rw [heq]; simp

end NonnegCombOangle

end Erdos634.Geometry
