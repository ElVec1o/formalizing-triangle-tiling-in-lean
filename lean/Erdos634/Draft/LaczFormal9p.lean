import Erdos634.Draft.LaczFormal9o

/-!
# Laczkovich DM 140 (1995), Theorem 2.3: Fig. 3, containment of the pieces and pairwise interior-disjointness

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.3, Fig. 3), Beeson, Beeson-Zhang, Zhang.  Formalization debt,
not /goal progress.

Separating lines (functionals `lineFun`): `y = 1` (trapezoid | `ABC`), `EB` (trapezoid | `BCD`, `BDE`, `DEF`),
`BC` (`ABC` | the rest), `BD` (`BCD` | `BDE`, `DEF`), `DE` (`BDE` | `DEF`).  Every vertex value is computed exactly
(`field_simp; ring`) and its sign read off.
-/

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL24 Erdos634.Laczkovich9n Erdos634.Laczkovich9o
  Erdos634.CertGeom

namespace Erdos634.Laczkovich9p

private theorem htri3 : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide

section cont
variable {c : ℝ} (hc : 0 < c)
include hc

theorem vt_ok {x y : ℝ} (h1 : 0 ≤ x) (h2 : 0 ≤ y) (h3 : (c ^ 2 + 1) * x + y ≤ c ^ 2 + c + 1) :
    inTgt c (mkPt x y) := by
  unfold inTgt
  simp only [mkPt_zero, mkPt_one]
  exact ⟨h1, h2, h3⟩

theorem tri_sub_tgt (T : Tri) (hT : ∀ k, inTgt c (T.pts k)) : T.carrier ⊆ (triT c hc).carrier := by
  rw [triT_carrier hc]
  exact convexHull_min (Set.range_subset_iff.mpr hT) (convex_inTgt c)

theorem pieces_sub : (((trapSet (wt c) ∪ (triABC c hc).carrier) ∪ (triBCD c hc).carrier) ∪
      (triBDE c hc).carrier) ∪ (triDEF c hc).carrier ⊆ (triT c hc).carrier := by
  have hn := n_pos hc
  have hh := h_pos hc
  have hwt : wt c * (c ^ 2 + 1) = c ^ 2 := by unfold wt; field_simp
  have hwf : wf c * (c ^ 2 + 1) = c ^ 2 + c + 1 := by unfold wf; field_simp
  have hwp : wp c * (c ^ 2 + 1) = c + 1 := by unfold wp; field_simp
  have vA : inTgt c pA := vt_ok hc (x := 0) (y := 1) (le_refl _) zero_le_one (by nlinarith)
  have vB : inTgt c (pB c) := vt_ok hc (x := wt c) (y := 1) (wt_pos hc).le zero_le_one (by nlinarith)
  have vC : inTgt c (pC c) := vt_ok hc (x := 0) (y := wh c) (le_refl _) (by unfold wh; positivity)
    (by unfold wh; nlinarith)
  have vD : inTgt c (pD c) := vt_ok hc (x := wp c) (y := wq c) (wp_pos hc).le (wq_pos hc).le
    (by unfold wq; nlinarith)
  have vE : inTgt c pE := vt_ok hc (x := 1) (y := 0) zero_le_one (le_refl _) (by nlinarith)
  have vF : inTgt c (pF c) := vt_ok hc (x := wf c) (y := 0) (by have := wf_gt hc; linarith) (le_refl _)
    (by nlinarith)
  intro z hz
  rcases hz with (((hz | hz) | hz) | hz) | hz
  · rw [triT_carrier hc]
    obtain ⟨h1, h2, h3, h4⟩ := hz
    refine ⟨h3, h1, ?_⟩
    have e : wt c * (c ^ 2 + 1) = c ^ 2 := hwt
    have h5 : z 0 * (c ^ 2 + 1) ≤ (1 + (wt c - 1) * z 1) * (c ^ 2 + 1) :=
      mul_le_mul_of_nonneg_right h4 hn.le
    nlinarith
  · exact tri_sub_tgt hc _ (fun k => by rcases htri3 k with rfl | rfl | rfl <;> assumption) hz
  · exact tri_sub_tgt hc _ (fun k => by rcases htri3 k with rfl | rfl | rfl <;> assumption) hz
  · exact tri_sub_tgt hc _ (fun k => by rcases htri3 k with rfl | rfl | rfl <;> assumption) hz
  · exact tri_sub_tgt hc _ (fun k => by rcases htri3 k with rfl | rfl | rfl <;> assumption) hz

end cont

/-! ## Separating lines -/

noncomputable def fEB (c : ℝ) : Plane →ᵃ[ℝ] ℝ := lineFun 1 0 (wt c) 1
noncomputable def fBC (c : ℝ) : Plane →ᵃ[ℝ] ℝ := lineFun (wt c) 1 0 (wh c)
noncomputable def fBD (c : ℝ) : Plane →ᵃ[ℝ] ℝ := lineFun (wt c) 1 (wp c) (wq c)
noncomputable def fDE (c : ℝ) : Plane →ᵃ[ℝ] ℝ := lineFun (wp c) (wq c) 1 0

theorem lf_mk (px py qx qy x y : ℝ) :
    lineFun px py qx qy (mkPt x y) = (qx - px) * (y - py) - (x - px) * (qy - py) := by
  simp [lineFun_apply]

section sep
variable {c : ℝ} (hc : 0 < c)
include hc

theorem fEB_ne : (fEB c).linear ≠ 0 :=
  lineFun_linear_ne_zero (Or.inl (by have := wt_lt hc; intro h; linarith))
theorem fBC_ne : (fBC c).linear ≠ 0 :=
  lineFun_linear_ne_zero (Or.inl (by have := wt_pos hc; intro h; linarith))
theorem fDE_ne : (fDE c).linear ≠ 0 :=
  lineFun_linear_ne_zero (Or.inr (by have := wq_pos hc; intro h; linarith))
theorem fBD_ne : (fBD c).linear ≠ 0 := by
  by_cases h : (1 : ℝ) = wq c
  · refine lineFun_linear_ne_zero (Or.inl ?_)
    have hc1 : c = 1 := by unfold wq at h; nlinarith
    subst hc1
    unfold wt wp; norm_num
  · exact lineFun_linear_ne_zero (Or.inr h)

local macro "lfv" : tactic =>
  `(tactic| (simp only [pA, pB, pC, pD, pE, pF, pG, lf_mk, mkPt_zero, mkPt_one, wt, wh, wp, wq, wf, wn]; field_simp; ring))

-- line EB
theorem EB_B : fEB c (pB c) = 0 := by have := n_pos hc; unfold fEB; lfv
theorem EB_E : fEB c pE = 0 := by have := n_pos hc; unfold fEB; lfv
theorem EB_C : fEB c (pC c) = -(c / (c ^ 2 + 1)) := by have := n_pos hc; unfold fEB; lfv
theorem EB_D : fEB c (pD c) = -(c / (c ^ 2 + 1)) := by have := n_pos hc; unfold fEB; lfv
theorem EB_F : fEB c (pF c) = -(c / (c ^ 2 + 1)) := by have := n_pos hc; unfold fEB; lfv
-- line BC
theorem BC_A : fBC c pA = c ^ 3 * (c + 1) / (c ^ 2 + 1) := by have := n_pos hc; unfold fBC; lfv
theorem BC_B : fBC c (pB c) = 0 := by have := n_pos hc; unfold fBC; lfv
theorem BC_C : fBC c (pC c) = 0 := by have := n_pos hc; unfold fBC; lfv
theorem BC_D : fBC c (pD c) = -(c * (c + 1) / (c ^ 2 + 1)) := by have := n_pos hc; unfold fBC; lfv
theorem BC_E : fBC c pE = -(c / (c ^ 2 + 1)) := by have := n_pos hc; unfold fBC; lfv
theorem BC_F : fBC c (pF c) = -(c * (c ^ 2 + c + 1) / (c ^ 2 + 1)) := by have := n_pos hc; unfold fBC; lfv
-- line BD
theorem BD_B : fBD c (pB c) = 0 := by have := n_pos hc; unfold fBD; lfv
theorem BD_D : fBD c (pD c) = 0 := by have := n_pos hc; unfold fBD; lfv
theorem BD_C : fBD c (pC c) = c * (c + 1) / (c ^ 2 + 1) := by have := n_pos hc; unfold fBD; lfv
theorem BD_E : fBD c pE = -(c / (c ^ 2 + 1)) := by have := n_pos hc; unfold fBD; lfv
theorem BD_F : fBD c (pF c) = -(c ^ 3 / (c ^ 2 + 1)) := by have := n_pos hc; unfold fBD; lfv
-- line DE
theorem DE_D : fDE c (pD c) = 0 := by have := n_pos hc; unfold fDE; lfv
theorem DE_E : fDE c pE = 0 := by have := n_pos hc; unfold fDE; lfv
theorem DE_B : fDE c (pB c) = -(c / (c ^ 2 + 1)) := by have := n_pos hc; unfold fDE; lfv
theorem DE_F : fDE c (pF c) = c ^ 3 / (c ^ 2 + 1) := by have := n_pos hc; unfold fDE; lfv

end sep

end Erdos634.Laczkovich9p

#print axioms Erdos634.Laczkovich9p.pieces_sub
#print axioms Erdos634.Laczkovich9p.BD_F
