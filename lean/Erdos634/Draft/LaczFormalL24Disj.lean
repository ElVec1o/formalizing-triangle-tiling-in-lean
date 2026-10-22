import Erdos634.Draft.LaczFormalL24Cover

/-!
# Theorem 2.4, first triple: pairwise disjointness of the five pieces of Fig. 4

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.4, Fig. 4), Beeson, Beeson-Zhang, Zhang.
Five separating lines: `BC`, `t = 1`, `s = τ`, `CD`, `AD`.
-/

namespace Erdos634.LaczL24

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22

private theorem htri3''' : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide

/-- Separation of two triangles by an affine functional, from vertex values. -/
theorem sep_vertices {T U : Tri} (f : Plane →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) (c : ℝ)
    (h₀ : f (T.pts 0) ≤ c) (h₁ : f (T.pts 1) ≤ c) (h₂ : f (T.pts 2) ≤ c)
    (g₀ : c ≤ f (U.pts 0)) (g₁ : c ≤ f (U.pts 1)) (g₂ : c ≤ f (U.pts 2)) :
    Disjoint (interior T.carrier) (interior U.carrier) := by
  refine sep_tri f hf c ?_ ?_
  · intro k; rcases htri3''' k with rfl | rfl | rfl <;> assumption
  · intro k; rcases htri3''' k with rfl | rfl | rfl <;> assumption

theorem trap_other {τ : ℝ} (T : Tri) (hT : ∀ k, 1 ≤ (T.pts k) 1) :
    Disjoint (interior (trapSet τ)) (interior T.carrier) :=
  sepY 1 (fun z hz => hz.2.1) (fun z hz => by
    have := ge_of_forall_pts_ge (coordFun 0 1 0) (c := 1) (t := T) (fun k => by simpa using hT k) z hz
    simpa using this)

section disj
variable {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)

theorem BCA_pts : (triBCA a ha0 ha1).pts 0 = mkPt 1 0 ∧ (triBCA a ha0 ha1).pts 1 = mkPt (gTau a) 1 ∧
    (triBCA a ha0 ha1).pts 2 = mkPt (gTau a) (2 - a ^ 2) := ⟨rfl, rfl, rfl⟩
theorem ACD_pts : (triACD a ha0 ha1).pts 0 = mkPt (gTau a) (2 - a ^ 2) ∧
    (triACD a ha0 ha1).pts 1 = mkPt (gTau a) 1 ∧ (triACD a ha0 ha1).pts 2 = mkPt 0 (gDel a) :=
  ⟨rfl, rfl, rfl⟩
theorem ADE_pts : (triADE a ha0 ha1).pts 0 = mkPt (gTau a) (2 - a ^ 2) ∧
    (triADE a ha0 ha1).pts 1 = mkPt 0 (gDel a) ∧ (triADE a ha0 ha1).pts 2 = mkPt 0 (gE a) :=
  ⟨rfl, rfl, rfl⟩
theorem CDF_pts : (triCDF a ha0 ha1).pts 0 = mkPt (gTau a) 1 ∧
    (triCDF a ha0 ha1).pts 1 = mkPt 0 (gDel a) ∧ (triCDF a ha0 ha1).pts 2 = mkPt 0 1 :=
  ⟨rfl, rfl, rfl⟩

include ha0 ha1

theorem trap_BCA : Disjoint (interior (trapSet (gTau a))) (interior (triBCA a ha0 ha1).carrier) := by
  have hb := gb_pos ha0 ha1
  have hτ1 := gTau_lt_one ha0 ha1
  obtain ⟨p0, p1, p2⟩ := BCA_pts ha0 ha1
  refine disjoint_interior_of_sep (coordFun 1 (-(gTau a - 1)) (-1))
    (coordFun_linear_ne_zero _ (Or.inl one_ne_zero)) 0 ?_ ?_
  · intro z hz
    obtain ⟨h1, h2, h3, h4⟩ := hz
    simp only [coordFun_apply]; nlinarith
  · intro z hz
    refine ge_of_forall_pts_ge (coordFun 1 (-(gTau a - 1)) (-1)) ?_ z hz
    intro k
    rcases htri3''' k with rfl | rfl | rfl
    · rw [p0]; simp
    · rw [p1]; simp
    · rw [p2]; simp <;> nlinarith

theorem trap_ACD : Disjoint (interior (trapSet (gTau a))) (interior (triACD a ha0 ha1).carrier) := by
  have hb := gb_pos ha0 ha1; have hd1 := gDel_gt ha0 ha1
  obtain ⟨p0, p1, p2⟩ := ACD_pts ha0 ha1
  refine trap_other _ ?_
  intro k; rcases htri3''' k with rfl | rfl | rfl
  · rw [p0]; simp <;> nlinarith
  · rw [p1]; simp
  · rw [p2]; simp <;> linarith

theorem trap_ADE : Disjoint (interior (trapSet (gTau a))) (interior (triADE a ha0 ha1).carrier) := by
  have hb := gb_pos ha0 ha1; have hd1 := gDel_gt ha0 ha1; have he := gE_gt ha0 ha1
  obtain ⟨p0, p1, p2⟩ := ADE_pts ha0 ha1
  refine trap_other _ ?_
  intro k; rcases htri3''' k with rfl | rfl | rfl
  · rw [p0]; simp <;> nlinarith
  · rw [p1]; simp <;> linarith
  · rw [p2]; simp <;> linarith

theorem trap_CDF : Disjoint (interior (trapSet (gTau a))) (interior (triCDF a ha0 ha1).carrier) := by
  have hd1 := gDel_gt ha0 ha1
  obtain ⟨p0, p1, p2⟩ := CDF_pts ha0 ha1
  refine trap_other _ ?_
  intro k; rcases htri3''' k with rfl | rfl | rfl
  · rw [p0]; simp
  · rw [p1]; simp <;> linarith
  · rw [p2]; simp

theorem tau_other (T : Tri) (hT : ∀ k, (T.pts k) 0 ≤ gTau a) :
    Disjoint (interior T.carrier) (interior (triBCA a ha0 ha1).carrier) := by
  have hb := gb_pos ha0 ha1
  have hτ1 := gTau_lt_one ha0 ha1
  obtain ⟨p0, p1, p2⟩ := BCA_pts ha0 ha1
  exact sepX (gTau a)
    (fun z hz => by
      have := Erdos634.CertGeom.le_of_forall_pts_le (coordFun 1 0 0) (c := gTau a) (t := T)
        (fun k => by simpa using hT k) z hz
      simpa using this)
    (fun z hz => by
      have := ge_of_forall_pts_ge (coordFun 1 0 0) (c := gTau a) (t := triBCA a ha0 ha1) (fun k => by
        rcases htri3''' k with rfl | rfl | rfl
        · rw [p0]; simp <;> linarith
        · rw [p1]; simp
        · rw [p2]; simp) z hz
      simpa using this)

theorem ACD_BCA : Disjoint (interior (triACD a ha0 ha1).carrier) (interior (triBCA a ha0 ha1).carrier) := by
  obtain ⟨p0, p1, p2⟩ := ACD_pts ha0 ha1
  refine tau_other ha0 ha1 _ ?_
  intro k; rcases htri3''' k with rfl | rfl | rfl
  · rw [p0]; simp
  · rw [p1]; simp
  · rw [p2]; simp; exact (gTau_pos ha0 ha1).le

theorem ADE_BCA : Disjoint (interior (triADE a ha0 ha1).carrier) (interior (triBCA a ha0 ha1).carrier) := by
  obtain ⟨p0, p1, p2⟩ := ADE_pts ha0 ha1
  refine tau_other ha0 ha1 _ ?_
  intro k; rcases htri3''' k with rfl | rfl | rfl
  · rw [p0]; simp
  · rw [p1]; simp; exact (gTau_pos ha0 ha1).le
  · rw [p2]; simp; exact (gTau_pos ha0 ha1).le

theorem CDF_BCA : Disjoint (interior (triCDF a ha0 ha1).carrier) (interior (triBCA a ha0 ha1).carrier) := by
  obtain ⟨p0, p1, p2⟩ := CDF_pts ha0 ha1
  refine tau_other ha0 ha1 _ ?_
  intro k; rcases htri3''' k with rfl | rfl | rfl
  · rw [p0]; simp
  · rw [p1]; simp; exact (gTau_pos ha0 ha1).le
  · rw [p2]; simp; exact (gTau_pos ha0 ha1).le

theorem CDF_ACD : Disjoint (interior (triCDF a ha0 ha1).carrier) (interior (triACD a ha0 ha1).carrier) := by
  have hb := gb_pos ha0 ha1; have hτ0 := gTau_pos ha0 ha1; have hd1 := gDel_gt ha0 ha1
  obtain ⟨p0, p1, p2⟩ := CDF_pts ha0 ha1
  obtain ⟨q0, q1, q2⟩ := ACD_pts ha0 ha1
  refine sep_vertices (coordFun (gDel a - 1) (gTau a) (-(gTau a * gDel a)))
    (coordFun_linear_ne_zero _ (Or.inr hτ0.ne')) 0 ?_ ?_ ?_ ?_ ?_ ?_
  · rw [p0]; simp <;> nlinarith
  · rw [p1]; simp
  · rw [p2]; simp <;> nlinarith
  · rw [q0]; simp <;> nlinarith
  · rw [q1]; simp <;> nlinarith
  · rw [q2]; simp

theorem CDF_ADE : Disjoint (interior (triCDF a ha0 ha1).carrier) (interior (triADE a ha0 ha1).carrier) := by
  have hb := gb_pos ha0 ha1; have hτ0 := gTau_pos ha0 ha1; have hd1 := gDel_gt ha0 ha1
  have he := gE_gt ha0 ha1
  obtain ⟨p0, p1, p2⟩ := CDF_pts ha0 ha1
  obtain ⟨q0, q1, q2⟩ := ADE_pts ha0 ha1
  refine sep_vertices (coordFun (gDel a - 1) (gTau a) (-(gTau a * gDel a)))
    (coordFun_linear_ne_zero _ (Or.inr hτ0.ne')) 0 ?_ ?_ ?_ ?_ ?_ ?_
  · rw [p0]; simp <;> nlinarith
  · rw [p1]; simp
  · rw [p2]; simp <;> nlinarith
  · rw [q0]; simp <;> nlinarith
  · rw [q1]; simp <;> nlinarith
  · rw [q2]; simp <;> nlinarith

theorem ACD_ADE : Disjoint (interior (triACD a ha0 ha1).carrier) (interior (triADE a ha0 ha1).carrier) := by
  have hb := gb_pos ha0 ha1; have hτ0 := gTau_pos ha0 ha1; have hd1 := gDel_gt ha0 ha1
  have he := gE_gt ha0 ha1
  obtain ⟨p0, p1, p2⟩ := ACD_pts ha0 ha1
  obtain ⟨q0, q1, q2⟩ := ADE_pts ha0 ha1
  refine sep_vertices (coordFun (gDel a - 1 - (1 - a ^ 2)) (gTau a) (-(gTau a * gDel a)))
    (coordFun_linear_ne_zero _ (Or.inr hτ0.ne')) 0 ?_ ?_ ?_ ?_ ?_ ?_
  · rw [p0]; simp <;> nlinarith
  · rw [p1]; simp <;> nlinarith
  · rw [p2]; simp
  · rw [q0]; simp <;> nlinarith
  · rw [q1]; simp
  · rw [q2]; simp <;> nlinarith

end disj

end Erdos634.LaczL24
