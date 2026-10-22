-- Draft/KConjNormal.lean — CASE A, node A3 (Lemma K, K2 half): the NORMALISED dissection.
--
-- For a real `CongruentDissection D` with model angles a_i π/n, the paper's coordinate
-- z(P) = e^{−iθ₀}(P − A)/λ (`A1Field.zc`, Lemma 1, VERIFIED) is an affine similarity `eN D` of the
-- plane; `Dn D = mapDissection (eN D) D` is a `Dissection N` which satisfies every hypothesis of
-- `KConj.phiDissection` (Draft/KConjAe.lean):
--   * every corner has complex coordinate in K = ℚ(ζ_{4n})       (`A1Field.lemma1_full`),
--   * every tile has |det| = P, the target |det| = N·P            (congruence + area identity),
-- and it has the same corner angles and the same corner incidences as D.
-- Formalization debt on a paper-level PROVED node; NOT /goal progress.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
-- H59: no parameter pair (e, f) is evaluated here.
import Erdos634.Draft.KConjAngle
import Erdos634.DissectionMap
import Erdos634.CollarAreaM4
import Erdos634.CongruentArea

open Complex MeasureTheory

namespace Erdos634.KConj

open Erdos634.Geometry Erdos634.Geometry.CaseA.LemmaV Erdos634.Geometry.A1Field
  Erdos634.DissectionMap Erdos634.AreaDet

variable {N : ℕ} (D : CongruentDissection N)

/-- The complex factor `e^{−iθ₀}/λ`. -/
noncomputable def cN : ℂ := (wAB D)⁻¹ / ((circD D.model : ℝ) : ℂ)

theorem cN_ne : cN D ≠ 0 :=
  div_ne_zero (inv_ne_zero (wAB_ne D)) (ofReal_ne_zero.mpr (circD_pos _).ne')

/-- The linear part of the normalisation. -/
noncomputable def linN : Plane ≃ₗ[ℝ] Plane :=
  toC.toLinearEquiv ≪≫ₗ ((LinearEquiv.smulOfNeZero ℂ ℂ (cN D) (cN_ne D)).restrictScalars ℝ) ≪≫ₗ
    toC.symm.toLinearEquiv

/-- The normalisation `P ↦ z(P)`, as an affine equivalence of the plane. -/
noncomputable def eN : Plane ≃ᵃ[ℝ] Plane :=
  (AffineEquiv.constVAdd ℝ Plane (-D.target.pts 0)).trans (linN D).toAffineEquiv

theorem toC_eN (P : Plane) : toC (eN D P) = zc D P := by
  simp only [eN, linN, AffineEquiv.trans_apply, AffineEquiv.constVAdd_apply, vadd_eq_add,
    LinearEquiv.coe_toAffineEquiv, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    LinearEquiv.smulOfNeZero_apply, LinearIsometryEquiv.coe_toLinearEquiv,
    LinearIsometryEquiv.apply_symm_apply, smul_eq_mul, zc, cN]
  rw [neg_add_eq_sub, mul_comm]

/-- The normalised dissection. -/
noncomputable def Dn : Dissection N := mapDissection (eN D) D.toDissection

theorem Dn_tile_pts (i : Fin N) (k : Fin 3) : ((Dn D).tile i).pts k = eN D ((D.tile i).pts k) :=
  rfl

theorem Dn_target_pts (k : Fin 3) : (Dn D).target.pts k = eN D (D.target.pts k) := rfl

/-! ## Coordinates in K -/

theorem Dn_hK {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) (i : Fin N) (k : Fin 3) :
    toC (((Dn D).tile i).pts k) ∈ Kf n := by
  rw [Dn_tile_pts, toC_eN]
  have h := lemma1_full D hn a ha
  exact h.2.2.2.2.2.2.2.2 _ (h.2.2.2.2.2.2.1 i k)

theorem Dn_hKT {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) (k : Fin 3) :
    toC ((Dn D).target.pts k) ∈ Kf n := by
  rw [Dn_target_pts, toC_eN]
  have h := lemma1_full D hn a ha
  exact h.2.2.2.2.2.2.2.2 _ (h.2.2.2.2.2.2.2.1 k)

/-! ## Determinants -/

theorem detTri_eq_det' (T : Tri) : detTri T = T.det := by
  rw [detTri_eq]; unfold Tri.det; ring

/-- Congruent triangles have equal |det|. -/
theorem abs_det_congr {T U : Tri} (h : T.Congruent U) : |T.det| = |U.det| := by
  have hv := Erdos634.CongruentArea.volume_congruent h
  rw [volume_eq_det_mul, volume_eq_det_mul, detTri_eq_det', detTri_eq_det'] at hv
  have hS0 : volume stdCarrier ≠ 0 := by
    have hp := U.volume_pos
    rw [volume_eq_det_mul, detTri_eq_det'] at hp
    intro h0; rw [h0, mul_zero] at hp; exact lt_irrefl _ hp
  have hST : volume stdCarrier ≠ ⊤ := by
    have hf := U.volume_ne_top
    rw [volume_eq_det_mul, detTri_eq_det'] at hf
    intro h0; apply hf; rw [h0]
    exact ENNReal.mul_top (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact abs_pos.mpr U.det_ne_zero)
  have := (ENNReal.mul_left_inj hS0 hST).mp hv
  exact (ENNReal.ofReal_eq_ofReal_iff (abs_nonneg _) (abs_nonneg _)).mp this

/-- The common |det| of the normalised tiles. -/
noncomputable def PN : ℝ := |LinearMap.det ((eN D).linear : Plane →ₗ[ℝ] Plane)| * |D.model.det|

theorem Dn_hP (i : Fin N) : |((Dn D).tile i).det| = PN D := by
  rw [Dn, mapDissection_tile, ← detTri_eq_det', detTri_mapTri, abs_mul, detTri_eq_det',
    abs_det_congr (D.tiles_congruent i), PN]

theorem Dn_hPT : |(Dn D).target.det| = N * PN D := by
  rw [Dn, mapDissection_target, ← detTri_eq_det', detTri_mapTri, abs_mul, detTri_eq_det',
    Erdos634.Geometry.Row3.RP.abs_det_target D, PN]
  ring

/-! ## Angles and incidences are preserved -/

theorem angleAt_eN (T : Tri) (v : Fin 3) : (mapTri (eN D) T).angleAt v = T.angleAt v := by
  have key : ∀ p q : Plane, toC (eN D p) - toC (eN D q) = (toC p - toC q) * cN D := by
    intro p q
    rw [toC_eN, toC_eN, zc, zc, map_sub, map_sub]
    simp only [cN]; ring
  rw [Tri.angleAt, Tri.angleAt, cornerAngle_toC, cornerAngle_toC]
  show InnerProductGeometry.angle (toC (eN D _) - toC (eN D _)) (toC (eN D _) - toC (eN D _)) = _
  rw [key, key, Complex.angle_mul_right (cN_ne D)]

theorem eN_inj {p q : Plane} : eN D p = eN D q ↔ p = q := (eN D).injective.eq_iff

end Erdos634.KConj

#print axioms Erdos634.KConj.Dn_hK
#print axioms Erdos634.KConj.Dn_hP
#print axioms Erdos634.KConj.Dn_hPT
#print axioms Erdos634.KConj.angleAt_eN
