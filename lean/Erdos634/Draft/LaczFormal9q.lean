import Erdos634.Draft.LaczFormal9p

/-!
# Laczkovich DM 140 (1995), Theorem 2.3: the ten pairwise interior-disjointness facts of Fig. 3

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.3, Fig. 3), Beeson, Beeson-Zhang, Zhang.  Formalization debt,
not /goal progress.
-/

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL24 Erdos634.Laczkovich9n Erdos634.Laczkovich9o
  Erdos634.Laczkovich9p Erdos634.CertGeom

namespace Erdos634.Laczkovich9q

private theorem htri3 : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide

section disj
variable {c : ℝ} (hc : 0 < c)
include hc

theorem trap_EB (T : Tri) (hT : ∀ k, fEB c (T.pts k) ≤ 0) :
    Disjoint (interior (trapSet (wt c))) (interior T.carrier) := by
  refine (disjoint_interior_of_sep (S := T.carrier) (U := trapSet (wt c)) (fEB c) (fEB_ne hc) 0
    (le_of_forall_pts_le (fEB c) hT) ?_).symm
  intro x hx
  obtain ⟨-, -, -, h4⟩ := hx
  unfold fEB
  rw [lineFun_apply]
  nlinarith

theorem d_tr_P1 : Disjoint (interior (trapSet (wt c))) (interior (triABC c hc).carrier) := by
  refine trap_other _ ?_
  intro k; rcases htri3 k with rfl | rfl | rfl
  · show (1 : ℝ) ≤ (mkPt 0 1) 1; simp
  · show (1 : ℝ) ≤ (mkPt (wt c) 1) 1; simp
  · show (1 : ℝ) ≤ (mkPt 0 (wh c)) 1; simpa using (wh_gt hc).le

theorem d_tr_P2 : Disjoint (interior (trapSet (wt c))) (interior (triBCD c hc).carrier) := by
  have h := n_pos hc
  refine trap_EB hc _ ?_
  intro k; rcases htri3 k with rfl | rfl | rfl
  · show fEB c (pB c) ≤ 0; rw [EB_B hc]
  · show fEB c (pC c) ≤ 0; rw [EB_C hc]; have : 0 < c / (c ^ 2 + 1) := by positivity
    linarith
  · show fEB c (pD c) ≤ 0; rw [EB_D hc]; have : 0 < c / (c ^ 2 + 1) := by positivity
    linarith

theorem d_tr_P3 : Disjoint (interior (trapSet (wt c))) (interior (triBDE c hc).carrier) := by
  have h := n_pos hc
  refine trap_EB hc _ ?_
  intro k; rcases htri3 k with rfl | rfl | rfl
  · show fEB c (pB c) ≤ 0; rw [EB_B hc]
  · show fEB c (pD c) ≤ 0; rw [EB_D hc]; have : 0 < c / (c ^ 2 + 1) := by positivity
    linarith
  · show fEB c pE ≤ 0; rw [EB_E hc]

theorem d_tr_P4 : Disjoint (interior (trapSet (wt c))) (interior (triDEF c hc).carrier) := by
  have h := n_pos hc
  refine trap_EB hc _ ?_
  intro k; rcases htri3 k with rfl | rfl | rfl
  · show fEB c (pD c) ≤ 0; rw [EB_D hc]; have : 0 < c / (c ^ 2 + 1) := by positivity
    linarith
  · show fEB c pE ≤ 0; rw [EB_E hc]
  · show fEB c (pF c) ≤ 0; rw [EB_F hc]; have : 0 < c / (c ^ 2 + 1) := by positivity
    linarith

theorem BC_P1 : ∀ k, 0 ≤ fBC c ((triABC c hc).pts k) := by
  have h := n_pos hc
  intro k; rcases htri3 k with rfl | rfl | rfl
  · show 0 ≤ fBC c pA; rw [BC_A hc]; positivity
  · show 0 ≤ fBC c (pB c); rw [BC_B hc]
  · show 0 ≤ fBC c (pC c); rw [BC_C hc]

theorem d_P1_P2 : Disjoint (interior (triBCD c hc).carrier) (interior (triABC c hc).carrier) := by
  have h := n_pos hc
  refine sep_tri (fBC c) (fBC_ne hc) 0 ?_ (BC_P1 hc)
  intro k; rcases htri3 k with rfl | rfl | rfl
  · show fBC c (pB c) ≤ 0; rw [BC_B hc]
  · show fBC c (pC c) ≤ 0; rw [BC_C hc]
  · show fBC c (pD c) ≤ 0; rw [BC_D hc]; have : 0 < c * (c + 1) / (c ^ 2 + 1) := by positivity
    linarith

theorem d_P1_P3 : Disjoint (interior (triBDE c hc).carrier) (interior (triABC c hc).carrier) := by
  have h := n_pos hc
  refine sep_tri (fBC c) (fBC_ne hc) 0 ?_ (BC_P1 hc)
  intro k; rcases htri3 k with rfl | rfl | rfl
  · show fBC c (pB c) ≤ 0; rw [BC_B hc]
  · show fBC c (pD c) ≤ 0; rw [BC_D hc]; have : 0 < c * (c + 1) / (c ^ 2 + 1) := by positivity
    linarith
  · show fBC c pE ≤ 0; rw [BC_E hc]; have : 0 < c / (c ^ 2 + 1) := by positivity
    linarith

theorem d_P1_P4 : Disjoint (interior (triDEF c hc).carrier) (interior (triABC c hc).carrier) := by
  have h := n_pos hc
  refine sep_tri (fBC c) (fBC_ne hc) 0 ?_ (BC_P1 hc)
  intro k; rcases htri3 k with rfl | rfl | rfl
  · show fBC c (pD c) ≤ 0; rw [BC_D hc]; have : 0 < c * (c + 1) / (c ^ 2 + 1) := by positivity
    linarith
  · show fBC c pE ≤ 0; rw [BC_E hc]; have : 0 < c / (c ^ 2 + 1) := by positivity
    linarith
  · show fBC c (pF c) ≤ 0; rw [BC_F hc]; have : 0 < c * (c ^ 2 + c + 1) / (c ^ 2 + 1) := by positivity
    linarith

theorem BD_P2 : ∀ k, 0 ≤ fBD c ((triBCD c hc).pts k) := by
  have h := n_pos hc
  intro k; rcases htri3 k with rfl | rfl | rfl
  · show 0 ≤ fBD c (pB c); rw [BD_B hc]
  · show 0 ≤ fBD c (pC c); rw [BD_C hc]; positivity
  · show 0 ≤ fBD c (pD c); rw [BD_D hc]

theorem d_P2_P3 : Disjoint (interior (triBDE c hc).carrier) (interior (triBCD c hc).carrier) := by
  have h := n_pos hc
  refine sep_tri (fBD c) (fBD_ne hc) 0 ?_ (BD_P2 hc)
  intro k; rcases htri3 k with rfl | rfl | rfl
  · show fBD c (pB c) ≤ 0; rw [BD_B hc]
  · show fBD c (pD c) ≤ 0; rw [BD_D hc]
  · show fBD c pE ≤ 0; rw [BD_E hc]; have : 0 < c / (c ^ 2 + 1) := by positivity
    linarith

theorem d_P2_P4 : Disjoint (interior (triDEF c hc).carrier) (interior (triBCD c hc).carrier) := by
  have h := n_pos hc
  refine sep_tri (fBD c) (fBD_ne hc) 0 ?_ (BD_P2 hc)
  intro k; rcases htri3 k with rfl | rfl | rfl
  · show fBD c (pD c) ≤ 0; rw [BD_D hc]
  · show fBD c pE ≤ 0; rw [BD_E hc]; have : 0 < c / (c ^ 2 + 1) := by positivity
    linarith
  · show fBD c (pF c) ≤ 0; rw [BD_F hc]; have : 0 < c ^ 3 / (c ^ 2 + 1) := by positivity
    linarith

theorem d_P3_P4 : Disjoint (interior (triBDE c hc).carrier) (interior (triDEF c hc).carrier) := by
  have h := n_pos hc
  refine sep_tri (fDE c) (fDE_ne hc) 0 ?_ ?_
  · intro k; rcases htri3 k with rfl | rfl | rfl
    · show fDE c (pB c) ≤ 0; rw [DE_B hc]; have : 0 < c / (c ^ 2 + 1) := by positivity
      linarith
    · show fDE c (pD c) ≤ 0; rw [DE_D hc]
    · show fDE c pE ≤ 0; rw [DE_E hc]
  · intro k; rcases htri3 k with rfl | rfl | rfl
    · show 0 ≤ fDE c (pD c); rw [DE_D hc]
    · show 0 ≤ fDE c pE; rw [DE_E hc]
    · show 0 ≤ fDE c (pF c); rw [DE_F hc]; positivity

end disj

end Erdos634.Laczkovich9q

#print axioms Erdos634.Laczkovich9q.d_P3_P4
#print axioms Erdos634.Laczkovich9q.d_tr_P2
