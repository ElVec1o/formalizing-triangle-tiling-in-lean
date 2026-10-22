import Erdos634.Draft.LaczFormalL33Trap
import Erdos634.Draft.LaczFormalL30All

/-!
# Laczkovich Theorem 2.5, triple `(α+β, α+β, α+β)`: the equilateral triangle, every rational tile with `γ = 2π/3`

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.5, Fig. 7), Beeson, Beeson-Zhang, Zhang.
-/

namespace Erdos634.LaczL33

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL24 Erdos634.Realizable Erdos634.DissectionMap
  Erdos634.LaczL30
open Erdos634.LaczL27 (carrier_eq_of_range range_mk3)

private theorem htri3 : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide

section strapsep

variable {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1)

noncomputable def strapE : Set Plane := (tU1 hk0 hk1).carrier ∪ (tU2 hk0 hk1).carrier

theorem strapE_closed : IsClosed (strapE hk0 hk1) :=
  ((tU1 hk0 hk1).isCompact.isClosed).union ((tU2 hk0 hk1).isCompact.isClosed)

theorem d_Pa_strap : Disjoint (interior (tPa hk0 hk1).carrier) (interior (strapE hk0 hk1)) := by
  have hk2 : 0 < k ^ 2 := by positivity
  refine disjoint_interior_of_sep (coordFun 0 1 0) (coordFun_linear_ne_zero 0 (Or.inr one_ne_zero)) 0 ?_ ?_
  · exact Erdos634.CertGeom.le_of_forall_pts_le _
      (fun i => by rcases htri3 i with rfl | rfl | rfl <;> simp [tPa, mkPt_zero, mkPt_one, hk0.le])
  · intro x hx
    rcases hx with hx | hx
    · exact ge_of_forall_pts_ge (coordFun 0 1 0)
        (fun i => by rcases htri3 i with rfl | rfl | rfl <;> simp [tU1, mkPt_zero, mkPt_one]) x hx
    · exact ge_of_forall_pts_ge (coordFun 0 1 0)
        (fun i => by rcases htri3 i with rfl | rfl | rfl <;> simp [tU2, mkPt_zero, mkPt_one, hk2.le]) x hx

theorem d_Pb_strap : Disjoint (interior (tPb hk0 hk1).carrier) (interior (strapE hk0 hk1)) := by
  have hk3 : 0 < k ^ 3 := by positivity
  have h1 : 0 < 1 - k := by linarith
  refine disjoint_interior_of_sep (coordFun 1 0 0) (coordFun_linear_ne_zero 0 (Or.inl one_ne_zero)) 0 ?_ ?_
  · exact Erdos634.CertGeom.le_of_forall_pts_le _
      (fun i => by rcases htri3 i with rfl | rfl | rfl <;> simp [tPb, mkPt_zero, mkPt_one, hk0.le])
  · intro x hx
    rcases hx with hx | hx
    · exact ge_of_forall_pts_ge (coordFun 1 0 0)
        (fun i => by rcases htri3 i with rfl | rfl | rfl <;> simp [tU1, mkPt_zero, mkPt_one, hk3.le, h1.le]) x hx
    · exact ge_of_forall_pts_ge (coordFun 1 0 0)
        (fun i => by rcases htri3 i with rfl | rfl | rfl <;> simp [tU2, mkPt_zero, mkPt_one, hk3.le, h1.le]) x hx

theorem d_Pc_strap : Disjoint (interior (tPc hk0 hk1).carrier) (interior (strapE hk0 hk1)) := by
  have hk2 : 0 < k ^ 2 := by positivity
  have hk3 : 0 < k ^ 3 := by positivity
  have hk5 : 0 < k ^ 5 := by positivity
  have h25 := k5_le_k2 hk0 hk1
  have h1 : 0 < 1 - k := by linarith
  refine disjoint_interior_of_sep (coordFun (k ^ 2) (k ^ 3) 0) (coordFun_linear_ne_zero 0 (Or.inl hk2.ne')) (k ^ 5) ?_ ?_
  · exact Erdos634.CertGeom.le_of_forall_pts_le _
      (fun i => by rcases htri3 i with rfl | rfl | rfl <;> simp [tPc, mkPt_zero, mkPt_one] <;> nlinarith)
  · intro x hx
    rcases hx with hx | hx
    · exact ge_of_forall_pts_ge (coordFun (k ^ 2) (k ^ 3) 0)
        (fun i => by rcases htri3 i with rfl | rfl | rfl <;> simp [tU1, mkPt_zero, mkPt_one] <;> nlinarith) x hx
    · exact ge_of_forall_pts_ge (coordFun (k ^ 2) (k ^ 3) 0)
        (fun i => by rcases htri3 i with rfl | rfl | rfl <;> simp [tU2, mkPt_zero, mkPt_one] <;> nlinarith) x hx

noncomputable def epieces : Fin 4 → Set Plane :=
  ![(tPa hk0 hk1).carrier, (tPb hk0 hk1).carrier, (tPc hk0 hk1).carrier, strapE hk0 hk1]

theorem epieces_cover : (⋃ i, epieces hk0 hk1 i) = (tE hk0 hk1).carrier := by
  rw [← cover5 hk0 hk1]
  ext z
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact ⟨0, hi⟩
    · exact ⟨1, hi⟩
    · exact ⟨2, hi⟩
    · rcases hi with hi | hi
      · exact ⟨3, hi⟩
      · exact ⟨4, hi⟩
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact ⟨0, hi⟩
    · exact ⟨1, hi⟩
    · exact ⟨2, hi⟩
    · exact ⟨3, Or.inl hi⟩
    · exact ⟨3, Or.inr hi⟩

end strapsep

section equi

variable (R : RTri) (hγ : R.a ^ 2 + R.a * R.b + R.b ^ 2 = R.c ^ 2) (hab : R.b < R.a)
  (w d : Plane) (hdet : w 0 * d 1 - w 1 * d 0 ≠ 0)
  (hw : inner ℝ w w = (R.a : ℝ) ^ 2) (hd : inner ℝ d d = (R.a : ℝ) ^ 2)
  (hwd : inner ℝ w d = (R.a : ℝ) * (R.a : ℝ) * (-1 / 2))

include hγ hab hdet hw hd hwd

/-- **The equilateral triangle is a rational similar dissection.** -/
theorem chart_E : ChartRSD R 0 w d hdet (tE (hK0 R) (hK1 R hab)).carrier := by
  have hk0 := hK0 R
  have hk1 := hK1 R hab
  have key := Erdos634.LaczL26.chart_iUnion (R := R) (A := 0) (w := w) (d := d) (h := hdet) (ι := Fin 4)
    (epieces hk0 hk1)
    (by
      intro i; fin_cases i
      · exact chart_P2 R hγ hab w d hdet hw hd hwd
      · exact chart_Pb R hγ hab w d hdet hw hd hwd
      · exact chart_Pc R hγ hab w d hdet hw hd hwd
      · exact chart_strapE R hγ hab w d hdet hw hd hwd)
    (by
      intro i; fin_cases i
      · exact (tPa hk0 hk1).isCompact.isClosed
      · exact (tPb hk0 hk1).isCompact.isClosed
      · exact (tPc hk0 hk1).isCompact.isClosed
      · exact strapE_closed hk0 hk1)
    (by
      intro i j hij
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact d_Pa_Pb hk0 hk1
      · exact d_Pa_Pc hk0 hk1
      · exact d_Pa_strap hk0 hk1
      · exact (d_Pa_Pb hk0 hk1).symm
      · exact absurd rfl hij
      · exact d_Pb_Pc hk0 hk1
      · exact d_Pb_strap hk0 hk1
      · exact (d_Pa_Pc hk0 hk1).symm
      · exact (d_Pb_Pc hk0 hk1).symm
      · exact absurd rfl hij
      · exact d_Pc_strap hk0 hk1
      · exact (d_Pa_strap hk0 hk1).symm
      · exact (d_Pb_strap hk0 hk1).symm
      · exact (d_Pc_strap hk0 hk1).symm
      · exact absurd rfl hij)
  rw [epieces_cover hk0 hk1] at key
  exact key

set_option maxHeartbeats 4000000 in
/-- the three sides of the equilateral triangle are `c`. -/
theorem equi_dist (K : ℝ) (hKR : K = ((kq R : ℚ) : ℝ)) :
    dist (chartEquiv 0 w d hdet (mkPt (-K) (-K))) (chartEquiv 0 w d hdet (mkPt 1 0)) = R.c ∧
    dist (chartEquiv 0 w d hdet (mkPt 1 0)) (chartEquiv 0 w d hdet (mkPt (1 - K) 1)) = R.c ∧
    dist (chartEquiv 0 w d hdet (mkPt (-K) (-K))) (chartEquiv 0 w d hdet (mkPt (1 - K) 1)) = R.c := by
  obtain ⟨hb, hc2⟩ := real_facts R hγ
  rw [← hKR] at hb hc2
  have hc0 : (0 : ℝ) < R.c := by exact_mod_cast R.pc
  refine ⟨?_, ?_, ?_⟩ <;> refine eq_of_sq_eq' dist_nonneg hc0.le ?_ <;>
    rw [chart_dsq R w d hdet hw hd hwd, hc2] <;> ring

end equi

end Erdos634.LaczL33
