/-
Draft/HBCFalse3.lean -- HBC item (1): `HBSimilar 3` is FALSE.  The 30-60-90 triangle (legs 1, sqrt 3, hyp 2) is cut into
THREE congruent 30-60-90 triangles (legs sqrt3/3, 1, hyp 2 sqrt3/3): bisect the 60-degree vertex B (cevian to D on the long leg),
then split the isosceles 30-30-120 triangle ABD by the altitude DM (M = midpoint of AB).  The target is the homothetic image
(ratio sqrt 3) of the model, N = 3 is not x^2 + y^2.  UNAUDITED.  Formalization debt, NOT /goal progress.
-/
import Erdos634.Draft.CVCCevianCut
import Erdos634.Draft.FluxRow2Witness
import Erdos634.Draft.ChainComposite

open scoped Classical

namespace Erdos634.Draft.HBCFalse3

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.CVCCevianCut
open Erdos634.Draft.FDBBaseBetaE1 (HasSides congruent_of_hasSides)
open Erdos634.Draft.FluxRow2Witness (homothety_angle_opp)
open Erdos634.Draft.ChainComposite

noncomputable def s : ℝ := Real.sqrt 3
theorem s_sq : s * s = 3 := Real.mul_self_sqrt (by norm_num)
theorem s_pos : 0 < s := Real.sqrt_pos.mpr (by norm_num)

theorem pt_eq (p q : Plane) (h0 : p 0 = q 0) (h1 : p 1 = q 1) : p = q := by
  ext i; fin_cases i
  · exact h0
  · exact h1

theorem dd (x1 y1 x2 y2 d : ℝ) (hd : 0 ≤ d) (h : (x1 - x2) ^ 2 + (y1 - y2) ^ 2 = d ^ 2) :
    dist (mkPt x1 y1) (mkPt x2 y2) = d :=
  dist_of_sqd _ _ d hd (by simpa using h)

noncomputable abbrev pC : Plane := mkPt 0 0
noncomputable abbrev pB : Plane := mkPt 1 0
noncomputable abbrev pA : Plane := mkPt 0 s
noncomputable abbrev pD : Plane := mkPt 0 (s / 3)
noncomputable abbrev pM : Plane := mkPt (1 / 2) (s / 2)

theorem cr_CBA : cr pC pB pA ≠ 0 := by
  simp only [cr, mkPt_zero, mkPt_one]; intro h; nlinarith [s_pos]
theorem cr_BCA : cr pB pC pA ≠ 0 := by
  simp only [cr, mkPt_zero, mkPt_one]; intro h; nlinarith [s_pos]
theorem cr_DAB : cr pD pA pB ≠ 0 := by
  simp only [cr, mkPt_zero, mkPt_one]; intro h; nlinarith [s_pos]
theorem cr_CDB : cr pC pD pB ≠ 0 := by
  simp only [cr, mkPt_zero, mkPt_one]; intro h; nlinarith [s_pos]
theorem cr_MDA : cr pM pD pA ≠ 0 := by
  simp only [cr, mkPt_zero, mkPt_one]; intro h; nlinarith [s_pos]
theorem cr_MDB : cr pM pD pB ≠ 0 := by
  simp only [cr, mkPt_zero, mkPt_one]; intro h; nlinarith [s_pos]
theorem cr_mdl : cr pC (mkPt (s / 3) 0) (mkPt 0 1) ≠ 0 := by
  simp only [cr, mkPt_zero, mkPt_one]; intro h; nlinarith [s_pos]

noncomputable def tgt : Tri := triOf pC pB pA cr_CBA
noncomputable def mdl : Tri := triOf pC (mkPt (s / 3) 0) (mkPt 0 1) cr_mdl
noncomputable def t0 : Tri := triOf pC pD pB cr_CDB
noncomputable def t1 : Tri := triOf pM pD pA cr_MDA
noncomputable def t2 : Tri := triOf pM pD pB cr_MDB
noncomputable def tiles : Fin 3 → Tri := ![t0, t1, t2]

/-! ## Congruence of every tile to the model (SSS) -/

theorem d_DB : dist pD pB = 2 * s / 3 :=
  dd _ _ _ _ _ (by linarith [s_pos]) (by nlinarith [s_sq])
theorem d_BC : dist pB pC = 1 := dd _ _ _ _ _ (by norm_num) (by norm_num)
theorem d_CD : dist pC pD = s / 3 := dd _ _ _ _ _ (by linarith [s_pos]) (by ring)
theorem d_DA : dist pD pA = 2 * s / 3 :=
  dd _ _ _ _ _ (by linarith [s_pos]) (by nlinarith [s_sq])
theorem d_AM : dist pA pM = 1 := dd _ _ _ _ _ (by norm_num) (by nlinarith [s_sq])
theorem d_MD : dist pM pD = s / 3 :=
  dd _ _ _ _ _ (by linarith [s_pos]) (by nlinarith [s_sq])
theorem d_BM : dist pB pM = 1 := dd _ _ _ _ _ (by norm_num) (by nlinarith [s_sq])

theorem mdl_sides : HasSides mdl (2 * s / 3) 1 (s / 3) :=
  ⟨1, dd _ _ _ _ _ (by linarith [s_pos]) (by nlinarith [s_sq]),
    dd _ _ _ _ _ (by norm_num) (by norm_num),
    dd _ _ _ _ _ (by linarith [s_pos]) (by nlinarith [s_sq])⟩

theorem tc (i : Fin 3) : (tiles i).Congruent mdl := by
  fin_cases i
  · exact (congruent_of_hasSides mdl_sides (U := t0) d_DB d_BC d_CD).symm
  · exact (congruent_of_hasSides mdl_sides (U := t1) d_DA d_AM d_MD).symm
  · exact (congruent_of_hasSides mdl_sides (U := t2) d_DB d_BM d_MD).symm


/-! ## Covering and disjointness: two cevians -/

theorem hD : pD = pC + (1 / 3 : ℝ) • (pA - pC) :=
  pt_eq _ _ (by simp) (by simp; ring)
theorem hM : pM = pA + (1 / 2 : ℝ) • (pB - pA) :=
  pt_eq _ _ (by simp) (by simp; ring)

theorem F1 : convexHull ℝ ({pB, pC, pA} : Set Plane) =
    convexHull ℝ {pB, pC, pD} ∪ convexHull ℝ {pB, pD, pA} := fan_cover pB pC pA pD (1 / 3) (by norm_num) (by norm_num) hD
theorem F2 : convexHull ℝ ({pD, pA, pB} : Set Plane) =
    convexHull ℝ {pD, pA, pM} ∪ convexHull ℝ {pD, pM, pB} := fan_cover pD pA pB pM (1 / 2) (by norm_num) (by norm_num) hM
theorem G1 : Disjoint (interior (convexHull ℝ ({pB, pC, pD} : Set Plane)))
    (interior (convexHull ℝ ({pB, pD, pA} : Set Plane))) := fan_disjoint pB pC pA pD (1 / 3) (by norm_num) (by norm_num) hD cr_BCA
theorem G2 : Disjoint (interior (convexHull ℝ ({pD, pA, pM} : Set Plane)))
    (interior (convexHull ℝ ({pD, pM, pB} : Set Plane))) := fan_disjoint pD pA pB pM (1 / 2) (by norm_num) (by norm_num) hM cr_DAB

theorem ea : ({pC, pB, pA} : Set Plane) = {pB, pC, pA} := by
  ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
theorem eb : ({pC, pD, pB} : Set Plane) = {pB, pC, pD} := by
  ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
theorem ec : ({pB, pD, pA} : Set Plane) = {pD, pA, pB} := by
  ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
theorem ed : ({pM, pD, pA} : Set Plane) = {pD, pA, pM} := by
  ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
theorem ee : ({pM, pD, pB} : Set Plane) = {pD, pM, pB} := by
  ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

theorem c0 : t0.carrier = convexHull ℝ {pB, pC, pD} := by
  unfold t0; rw [carrier_triOf, eb]
theorem c1 : t1.carrier = convexHull ℝ {pD, pA, pM} := by
  unfold t1; rw [carrier_triOf, ed]
theorem c2 : t2.carrier = convexHull ℝ {pD, pM, pB} := by
  unfold t2; rw [carrier_triOf, ee]
theorem ctgt : tgt.carrier = convexHull ℝ {pB, pC, pA} := by
  unfold tgt; rw [carrier_triOf, ea]

theorem covers_all : (⋃ i : Fin 3, (tiles i).carrier) = tgt.carrier := by
  have hU : (⋃ i : Fin 3, (tiles i).carrier) = t0.carrier ∪ t1.carrier ∪ t2.carrier := by
    ext x; simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩; fin_cases i
      · exact Or.inl (Or.inl hi)
      · exact Or.inl (Or.inr hi)
      · exact Or.inr hi
    · rintro ((h | h) | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
  rw [hU, c0, c1, c2, ctgt, F1, ec, F2, Set.union_assoc]

theorem d01 : Disjoint (interior t0.carrier) (interior t1.carrier) := by
  rw [c0, c1]
  have hsub : convexHull ℝ ({pD, pA, pM} : Set Plane) ⊆ convexHull ℝ {pB, pD, pA} := by
    rw [ec, F2]; exact Set.subset_union_left
  exact Disjoint.mono le_rfl (interior_mono hsub) G1
theorem d02 : Disjoint (interior t0.carrier) (interior t2.carrier) := by
  rw [c0, c2]
  have hsub : convexHull ℝ ({pD, pM, pB} : Set Plane) ⊆ convexHull ℝ {pB, pD, pA} := by
    rw [ec, F2]; exact Set.subset_union_right
  exact Disjoint.mono le_rfl (interior_mono hsub) G1
theorem d12 : Disjoint (interior t1.carrier) (interior t2.carrier) := by
  rw [c1, c2]; exact G2

theorem disj_all : Pairwise fun i j : Fin 3 =>
    Disjoint (interior (tiles i).carrier) (interior (tiles j).carrier) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact d01
  · exact d02
  · exact d01.symm
  · exact absurd rfl hij
  · exact d12
  · exact d02.symm
  · exact d12.symm
  · exact absurd rfl hij

/-- **A real `CongruentDissection 3`** of the 30-60-90 triangle into three congruent 30-60-90 triangles. -/
noncomputable def D3 : CongruentDissection 3 where
  target := tgt
  tile := tiles
  covers := covers_all
  interiors_disjoint := disj_all
  model := mdl
  tiles_congruent := tc

theorem hom (i : Fin 3) : tgt.pts i = mkPt 0 0 + s • (mdl.pts i - mkPt 0 0) := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  rcases hi with rfl | rfl | rfl
  · exact pt_eq _ _ (by simp [tgt, mdl, triOf]) (by simp [tgt, mdl, triOf])
  · refine pt_eq _ _ ?_ ?_ <;> simp [tgt, mdl, triOf] <;> nlinarith [s_sq]
  · refine pt_eq _ _ ?_ ?_ <;> simp [tgt, mdl, triOf]

theorem D3_sim (k : Fin 3) :
    D3.target.angleAt k = D3.model.angleAt ((1 : Equiv.Perm (Fin 3)) k) ∧
      D3.target.oppLen k = s * D3.model.oppLen ((1 : Equiv.Perm (Fin 3)) k) :=
  homothety_angle_opp mdl tgt (mkPt 0 0) s s_pos hom k

theorem three_not_sumsq : ¬ ∃ x y : ℕ, 3 = x ^ 2 + y ^ 2 := by
  rintro ⟨x, y, h⟩
  have hx : x ≤ 1 := by nlinarith
  have hy : y ≤ 1 := by nlinarith
  interval_cases x <;> interval_cases y <;> omega

/-- **`HBSimilar 3` is false**: the statement as written in `ChainComposite` is refuted by a real dissection. -/
theorem not_hbSimilar_3 : ¬ HBSimilar 3 :=
  fun h => three_not_sumsq (h D3 s 1 D3_sim)

end Erdos634.Draft.HBCFalse3

#print axioms Erdos634.Draft.HBCFalse3.D3
#print axioms Erdos634.Draft.HBCFalse3.not_hbSimilar_3
