import Erdos634.Draft.LaczFormalL26Geo

/-!
# Laczkovich Theorem 2.4, fourth triple: utilities

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94), Beeson, Beeson-Zhang, Zhang.

* `carrier_eq_dets`: the carrier of a positively oriented coordinate triangle is given by three determinant inequalities;
* `disj_biUnion`, `ratSimDiss_iUnion`: finite unions of closed, pairwise interior-disjoint rational similar dissections.
-/

namespace Erdos634.LaczL26

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL24

/-- The closed half-plane triple of a positively oriented triangle. -/
def detSet (x0 y0 x1 y1 x2 y2 : ℝ) : Set Plane :=
  {z | 0 ≤ det3 (z 0) (z 1) x1 y1 x2 y2 ∧ 0 ≤ det3 x0 y0 (z 0) (z 1) x2 y2 ∧
    0 ≤ det3 x0 y0 x1 y1 (z 0) (z 1)}

theorem convex_detSet (x0 y0 x1 y1 x2 y2 : ℝ) : Convex ℝ (detSet x0 y0 x1 y1 x2 y2) := by
  intro x hx y hy p q hp hq hpq
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  simp only [detSet, Set.mem_setOf_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, det3] at *
  obtain rfl : q = 1 - p := by linarith
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [mul_nonneg hp hx1, mul_nonneg hq hy1]
  · nlinarith [mul_nonneg hp hx2, mul_nonneg hq hy2]
  · nlinarith [mul_nonneg hp hx3, mul_nonneg hq hy3]

private theorem htri9 : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide

theorem carrier_eq_dets (x0 y0 x1 y1 x2 y2 : ℝ) (hD : 0 < det3 x0 y0 x1 y1 x2 y2) :
    (mkTri x0 y0 x1 y1 x2 y2 hD.ne').carrier = detSet x0 y0 x1 y1 x2 y2 := by
  apply Set.Subset.antisymm
  · refine convexHull_min (Set.range_subset_iff.mpr ?_) (convex_detSet _ _ _ _ _ _)
    intro k
    have hD' := hD
    simp only [det3] at hD'
    rcases htri9 k with rfl | rfl | rfl
    · show mkPt x0 y0 ∈ detSet x0 y0 x1 y1 x2 y2
      simp only [detSet, Set.mem_setOf_eq, mkPt_zero, mkPt_one, det3]
      refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
    · show mkPt x1 y1 ∈ detSet x0 y0 x1 y1 x2 y2
      simp only [detSet, Set.mem_setOf_eq, mkPt_zero, mkPt_one, det3]
      refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
    · show mkPt x2 y2 ∈ detSet x0 y0 x1 y1 x2 y2
      simp only [detSet, Set.mem_setOf_eq, mkPt_zero, mkPt_one, det3]
      refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
  · intro z hz
    obtain ⟨h0, h1, h2⟩ := hz
    rw [← mkPt_self z]
    exact mem_carrier_of_dets hD h0 h1 h2

/-- Finite unions of closed sets with interiors disjoint from a fixed set have interior disjoint from it. -/
theorem disj_biUnion {ι : Type*} [DecidableEq ι] (s : Finset ι) (S : ι → Set Plane)
    (hcl : ∀ i, IsClosed (S i)) (U : Set Plane)
    (h : ∀ i ∈ s, Disjoint (interior (S i)) (interior U)) :
    Disjoint (interior (⋃ i ∈ s, S i)) (interior U) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.set_biUnion_insert, Set.union_comm]
    refine disjoint_interior_union ?_ (ih (fun j hj => h j (Finset.mem_insert_of_mem hj))) (h i (Finset.mem_insert_self i s))
    exact (s.finite_toSet.isClosed_biUnion (fun j _ => hcl j))

/-- A finite union of closed, pairwise interior-disjoint rational similar dissections is one. -/
theorem ratSimDiss_iUnion {Δ : Tri} {ι : Type*} [Fintype ι] [DecidableEq ι] (S : ι → Set Plane)
    (hr : ∀ i, RatSimDiss Δ (S i)) (hcl : ∀ i, IsClosed (S i))
    (hd : Pairwise fun i j => Disjoint (interior (S i)) (interior (S j))) :
    RatSimDiss Δ (⋃ i, S i) := by
  have key : ∀ s : Finset ι, RatSimDiss Δ (⋃ i ∈ s, S i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using RatSimDiss.empty Δ
    | insert i s hi ih =>
      rw [Finset.set_biUnion_insert]
      refine RatSimDiss.union (hr i) ih ?_
      refine (disj_biUnion s S hcl (S i) (fun j hj => hd ?_)).symm
      intro hij; exact hi (hij ▸ hj)
  simpa using key Finset.univ

end Erdos634.LaczL26
