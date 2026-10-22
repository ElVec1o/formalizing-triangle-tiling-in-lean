-- Draft/CutGen.lean — a cevian cut of a triangle: `ABC = ABP ⊔ APC`, P on BC, general.
-- Coordinate-free; reused by the R-W and R-A gluing (prop:cevianatom).  Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.CertGeom
import Erdos634.CertNode

open scoped Classical
open Erdos634.Geometry

namespace Erdos634.Draft.CutGen

/-- **Cevian cut.**  If `T1 = (A, B, P)` and `T2 = (A, P, C)` with `P = B + t(C - B)`, `0 < t < 1`,
then `T1 ∪ T2 = T = (A, B, C)` as sets and the interiors are disjoint. -/
theorem cut_carrier (T T1 T2 : Tri) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (h1 : T1.pts 0 = T.pts 0) (h2 : T1.pts 1 = T.pts 1)
    (h3 : T1.pts 2 = AffineMap.lineMap (T.pts 1) (T.pts 2) t)
    (g1 : T2.pts 0 = T.pts 0) (g2 : T2.pts 1 = AffineMap.lineMap (T.pts 1) (T.pts 2) t)
    (g3 : T2.pts 2 = T.pts 2) :
    T1.carrier ∪ T2.carrier = T.carrier ∧
      Disjoint (interior T1.carrier) (interior T2.carrier) := by
  have hP : AffineMap.lineMap (T.pts 1) (T.pts 2) t
      = (0 : ℝ) • T.pts 0 + (1 - t) • T.pts 1 + t • T.pts 2 := by
    rw [AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add, zero_smul, zero_add, smul_sub, sub_smul, one_smul]
    abel
  have hPmem : AffineMap.lineMap (T.pts 1) (T.pts 2) t ∈ T.carrier :=
    Erdos634.CertGeom.mem_carrier_of_combo T _ ![0, 1 - t, t] (by simp) (by
      intro k; fin_cases k <;> simp <;> linarith) (by simpa using hP)
  have hvert : ∀ k, T.pts k ∈ T.carrier := fun k => subset_convexHull ℝ _ ⟨k, rfl⟩
  have hconv : Convex ℝ T.carrier := convex_convexHull ℝ _
  have hsub1 : T1.carrier ⊆ T.carrier := by
    refine convexHull_min ?_ hconv
    rintro _ ⟨k, rfl⟩
    fin_cases k
    · exact h1 ▸ hvert 0
    · exact h2 ▸ hvert 1
    · exact h3 ▸ hPmem
  have hsub2 : T2.carrier ⊆ T.carrier := by
    refine convexHull_min ?_ hconv
    rintro _ ⟨k, rfl⟩
    fin_cases k
    · exact g1 ▸ hvert 0
    · exact g2 ▸ hPmem
    · exact g3 ▸ hvert 2
  refine ⟨?_, ?_⟩
  · refine Set.Subset.antisymm (Set.union_subset hsub1 hsub2) ?_
    · intro x hx
      rw [T.carrier_eq_nonneg_coord] at hx
      have hx' : ∀ i, 0 ≤ T.basis.coord i x := hx
      set u0 := T.basis.coord 0 x with hu0
      set u1 := T.basis.coord 1 x with hu1
      set u2 := T.basis.coord 2 x with hu2
      have hsum : u0 + u1 + u2 = 1 := by
        have := T.basis.sum_coord_apply_eq_one x
        rwa [Fin.sum_univ_three] at this
      have hxeq : x = u0 • T.pts 0 + u1 • T.pts 1 + u2 • T.pts 2 := by
        have := T.basis.linear_combination_coord_eq_self x
        rw [Fin.sum_univ_three] at this
        exact this.symm
      by_cases hcase : u2 * (1 - t) ≤ u1 * t
      · left
        refine Erdos634.CertGeom.mem_carrier_of_combo T1 x ![u0, u1 - u2 * (1 - t) / t, u2 / t]
          (by simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; field_simp; linear_combination t * hsum) (by
            intro k; fin_cases k
            · simpa using hx' 0
            · show 0 ≤ u1 - u2 * (1 - t) / t
              have : u2 * (1 - t) / t ≤ u1 := by rw [div_le_iff₀ ht0]; linarith
              linarith
            · show 0 ≤ u2 / t
              exact div_nonneg (hx' 2) ht0.le) (by
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
              Matrix.head_cons, Matrix.tail_cons]
            rw [h1, h2, h3, hP, hxeq]
            ext i
            simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
            field_simp
            ring)
      · right
        push Not at hcase
        refine Erdos634.CertGeom.mem_carrier_of_combo T2 x ![u0, u1 / (1 - t), u2 - u1 * t / (1 - t)]
          (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; have : (1 - t) ≠ 0 := by linarith
              field_simp; linear_combination (1 - t) * hsum) (by
            intro k; fin_cases k
            · simpa using hx' 0
            · show 0 ≤ u1 / (1 - t)
              exact div_nonneg (hx' 1) (by linarith)
            · show 0 ≤ u2 - u1 * t / (1 - t)
              have : u1 * t / (1 - t) ≤ u2 := by rw [div_le_iff₀ (by linarith)]; linarith
              linarith) (by
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
              Matrix.head_cons, Matrix.tail_cons]
            rw [g1, g2, g3, hP, hxeq]
            ext i
            simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
            have : (1 - t) ≠ 0 := by linarith
            field_simp
            ring)
  · -- disjoint interiors, separated by the affine functional `t·u₁ − (1−t)·u₂`
    have hcoord : ∀ i j : Fin 3, T.basis.coord i (T.pts j) = if i = j then 1 else 0 := by
      intro i j
      by_cases hij : i = j
      · subst hij; rw [if_pos rfl]; exact T.basis.coord_apply_eq i
      · rw [if_neg hij]; exact T.basis.coord_apply_ne hij
    set f : Plane →ᵃ[ℝ] ℝ := t • T.basis.coord 1 - (1 - t) • T.basis.coord 2 with hf
    have fapp : ∀ x, f x = t * T.basis.coord 1 x - (1 - t) * T.basis.coord 2 x := by
      intro x; simp [hf]
    have f0 : f (T.pts 0) = 0 := by rw [fapp, hcoord, hcoord]; simp
    have f1 : f (T.pts 1) = t := by rw [fapp, hcoord, hcoord]; simp
    have f2 : f (T.pts 2) = -(1 - t) := by rw [fapp, hcoord, hcoord]; simp
    have fP : f (AffineMap.lineMap (T.pts 1) (T.pts 2) t) = 0 := by
      rw [AffineMap.apply_lineMap, f1, f2, AffineMap.lineMap_apply]
      simp only [vsub_eq_sub, vadd_eq_add, smul_eq_mul]; ring
    have hflin : f.linear ≠ 0 := by
      intro h0
      have := f.linearMap_vsub (T.pts 1) (T.pts 0)
      rw [h0] at this
      simp only [LinearMap.zero_apply] at this
      rw [f1, f0, vsub_eq_sub, sub_zero] at this
      linarith
    have hT1 : ∀ x ∈ T1.carrier, -f x ≤ 0 := by
      refine Erdos634.CertGeom.le_of_forall_pts_le (t := T1) (-f) (c := 0) ?_
      intro k; fin_cases k
      · show -f (T1.pts 0) ≤ 0; rw [h1, f0]; simp
      · show -f (T1.pts 1) ≤ 0; rw [h2, f1]; linarith
      · show -f (T1.pts 2) ≤ 0; rw [h3, fP]; simp
    have hT2 : ∀ x ∈ T2.carrier, f x ≤ 0 := by
      refine Erdos634.CertGeom.le_of_forall_pts_le (t := T2) f (c := 0) ?_
      intro k; fin_cases k
      · show f (T2.pts 0) ≤ 0; rw [g1, f0]
      · show f (T2.pts 1) ≤ 0; rw [g2, fP]
      · show f (T2.pts 2) ≤ 0; rw [g3, f2]; linarith
    exact (Erdos634.CertGeom.interiors_disjoint_of_separating (t := T2) (u := T1) f hflin 0 hT2
      (fun x hx => by have := hT1 x hx; linarith)).symm

end Erdos634.Draft.CutGen

#print axioms Erdos634.Draft.CutGen.cut_carrier
