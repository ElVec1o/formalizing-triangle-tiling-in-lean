-- Draft/CentroidSplit.lean — a triangle is the union of the three triangles (p_i, p_{i+1}, G) with
-- disjoint interiors, G the centroid.  Used for the 3-tiling of the equilateral triangle.
-- Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.Draft.CutGen
import Erdos634.CellCoord

open scoped Classical
open Erdos634.Geometry

namespace Erdos634.Draft.CentroidSplit

/-- The centroid. -/
noncomputable def G (T : Tri) : Plane := (1 / 3 : ℝ) • (T.pts 0 + T.pts 1 + T.pts 2)

theorem coord_pts (T : Tri) (i j : Fin 3) :
    T.basis.coord i (T.pts j) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst hij; rw [if_pos rfl]; exact T.basis.coord_apply_eq i
  · rw [if_neg hij]; exact T.basis.coord_apply_ne hij

theorem G_eq (T : Tri) : G T = (1 / 3 : ℝ) • T.pts 0 + (1 / 3 : ℝ) • T.pts 1 + (1 / 3 : ℝ) • T.pts 2 := by
  unfold G; simp only [smul_add]

theorem coord_G (T : Tri) (i : Fin 3) : T.basis.coord i (G T) = 1 / 3 := by
  have := Erdos634.Subdivision.Tri.coord_eq_of_combo T (G T) ![1 / 3, 1 / 3, 1 / 3] (by simp; norm_num)
    (by simpa using G_eq T) i
  fin_cases i <;> simpa using this

/-- Separation of two sub-triangles by the barycentric functional `u_i − u_j`. -/
theorem sep_lemma (T S S' : Tri) (i j : Fin 3) (hij : i ≠ j)
    (hS : ∀ k, T.basis.coord j (S.pts k) ≤ T.basis.coord i (S.pts k))
    (hS' : ∀ k, T.basis.coord i (S'.pts k) ≤ T.basis.coord j (S'.pts k)) :
    Disjoint (interior S.carrier) (interior S'.carrier) := by
  set f : Plane →ᵃ[ℝ] ℝ := T.basis.coord i - T.basis.coord j with hf
  have fapp : ∀ x, f x = T.basis.coord i x - T.basis.coord j x := fun x => by simp [hf]
  have hlin : f.linear ≠ 0 := by
    intro h0
    have := f.linearMap_vsub (T.pts i) (T.pts j)
    rw [h0] at this
    simp only [LinearMap.zero_apply] at this
    rw [fapp, fapp, coord_pts, coord_pts, coord_pts, coord_pts, if_pos rfl, if_neg hij, if_neg hij.symm,
      if_pos rfl, vsub_eq_sub] at this
    norm_num at this
  have hSb : ∀ x ∈ S.carrier, -f x ≤ 0 := by
    refine Erdos634.CertGeom.le_of_forall_pts_le (t := S) (-f) (c := 0) ?_
    intro k; have := hS k; show -f (S.pts k) ≤ 0; rw [fapp]; linarith
  have hS'b : ∀ x ∈ S'.carrier, f x ≤ 0 := by
    refine Erdos634.CertGeom.le_of_forall_pts_le (t := S') f (c := 0) ?_
    intro k; have := hS' k; rw [fapp]; linarith
  exact (Erdos634.CertGeom.interiors_disjoint_of_separating (t := S') (u := S) f hlin 0 hS'b
    (fun x hx => by have := hSb x hx; linarith)).symm

theorem centroid_split (T T0 T1 T2 : Tri)
    (a0 : T0.pts 0 = T.pts 0) (a1 : T0.pts 1 = T.pts 1) (a2 : T0.pts 2 = G T)
    (b0 : T1.pts 0 = T.pts 1) (b1 : T1.pts 1 = T.pts 2) (b2 : T1.pts 2 = G T)
    (c0 : T2.pts 0 = T.pts 2) (c1 : T2.pts 1 = T.pts 0) (c2 : T2.pts 2 = G T) :
    (T0.carrier ∪ T1.carrier ∪ T2.carrier = T.carrier) ∧
    Disjoint (interior T0.carrier) (interior T1.carrier) ∧
    Disjoint (interior T1.carrier) (interior T2.carrier) ∧
    Disjoint (interior T0.carrier) (interior T2.carrier) := by
  have hcoordT : ∀ i j, T.basis.coord i (T.pts j) = if i = j then 1 else 0 := coord_pts T
  have hGmem : G T ∈ T.carrier := by
    rw [T.carrier_eq_nonneg_coord]; intro k; show 0 ≤ T.basis.coord k (G T); rw [coord_G]; norm_num
  have hvert : ∀ k, T.pts k ∈ T.carrier := fun k => subset_convexHull ℝ _ ⟨k, rfl⟩
  have hconv := T.convex
  have sub : ∀ S : Tri, (∀ k, S.pts k ∈ T.carrier) → S.carrier ⊆ T.carrier := fun S h =>
    convexHull_min (by rintro _ ⟨k, rfl⟩; exact h k) hconv
  have s0 : T0.carrier ⊆ T.carrier := sub T0 (fun k => by
    fin_cases k
    · show T0.pts 0 ∈ _; rw [a0]; exact hvert 0
    · show T0.pts 1 ∈ _; rw [a1]; exact hvert 1
    · show T0.pts 2 ∈ _; rw [a2]; exact hGmem)
  have s1 : T1.carrier ⊆ T.carrier := sub T1 (fun k => by
    fin_cases k
    · show T1.pts 0 ∈ _; rw [b0]; exact hvert 1
    · show T1.pts 1 ∈ _; rw [b1]; exact hvert 2
    · show T1.pts 2 ∈ _; rw [b2]; exact hGmem)
  have s2 : T2.carrier ⊆ T.carrier := sub T2 (fun k => by
    fin_cases k
    · show T2.pts 0 ∈ _; rw [c0]; exact hvert 2
    · show T2.pts 1 ∈ _; rw [c1]; exact hvert 0
    · show T2.pts 2 ∈ _; rw [c2]; exact hGmem)
  refine ⟨Set.Subset.antisymm (Set.union_subset (Set.union_subset s0 s1) s2) ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [T.carrier_eq_nonneg_coord] at hx
    have hx' : ∀ i, 0 ≤ T.basis.coord i x := hx
    set u0 := T.basis.coord 0 x with hu0
    set u1 := T.basis.coord 1 x with hu1
    set u2 := T.basis.coord 2 x with hu2
    have hsum : u0 + u1 + u2 = 1 := by
      have := T.basis.sum_coord_apply_eq_one x; rwa [Fin.sum_univ_three] at this
    have hxeq : x = u0 • T.pts 0 + u1 • T.pts 1 + u2 • T.pts 2 := by
      have := T.basis.linear_combination_coord_eq_self x
      rw [Fin.sum_univ_three] at this; exact this.symm
    have h0 := hx' 0; have h1 := hx' 1; have h2 := hx' 2
    by_cases m2 : u2 ≤ u0 ∧ u2 ≤ u1
    · left; left
      refine Erdos634.CertGeom.mem_carrier_of_combo T0 x ![u0 - u2, u1 - u2, 3 * u2]
        (by simp; linarith) (by intro k; fin_cases k <;> simp <;> linarith [m2.1, m2.2]) ?_
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons]
      rw [a0, a1, a2, G_eq, hxeq]; module
    · by_cases m0 : u0 ≤ u1 ∧ u0 ≤ u2
      · left; right
        refine Erdos634.CertGeom.mem_carrier_of_combo T1 x ![u1 - u0, u2 - u0, 3 * u0]
          (by simp; linarith) (by intro k; fin_cases k <;> simp <;> linarith [m0.1, m0.2]) ?_
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.tail_cons]
        rw [b0, b1, b2, G_eq, hxeq]; module
      · right
        have m1 : u1 ≤ u2 ∧ u1 ≤ u0 := by
          push Not at m2 m0
          rcases le_total u2 u0 with h | h
          · have := m2 h; exact ⟨by linarith, by linarith⟩
          · rcases le_total u0 u1 with h' | h'
            · have := m0 h'; exfalso; linarith
            · exact ⟨by linarith, by linarith⟩
        refine Erdos634.CertGeom.mem_carrier_of_combo T2 x ![u2 - u1, u0 - u1, 3 * u1]
          (by simp; linarith) (by intro k; fin_cases k <;> simp <;> linarith [m1.1, m1.2]) ?_
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.tail_cons]
        rw [c0, c1, c2, G_eq, hxeq]; module
  · refine sep_lemma T T0 T1 0 2 (by decide) ?_ ?_ <;> intro k <;> fin_cases k <;>
      simp [a0, a1, a2, b0, b1, b2, hcoordT, coord_G]
  · refine sep_lemma T T1 T2 1 0 (by decide) ?_ ?_ <;> intro k <;> fin_cases k <;>
      simp [b0, b1, b2, c0, c1, c2, hcoordT, coord_G]
  · refine sep_lemma T T0 T2 1 2 (by decide) ?_ ?_ <;> intro k <;> fin_cases k <;>
      simp [a0, a1, a2, c0, c1, c2, hcoordT, coord_G]

end Erdos634.Draft.CentroidSplit

#print axioms Erdos634.Draft.CentroidSplit.centroid_split
