-- Draft/CaseALemmaHPiFour.lean — JOINT witness for Lemma H (Draft/CaseALemmaHExc2.lean `lemmaH`):
-- a real `CongruentDissection 2` of the isosceles right triangle (π/4, π/4, π/2) with vertices
-- B = (−1,0), C = (1,0), A = (0,1), cut by the altitude M = (0,0) into two right tiles (B,M,A),
-- (C,M,A) with acute angle π/4 ∈ ℚπ — every hypothesis of `lemmaH` discharged at once
-- (conclusion ¬(Prime 2 ∧ 5 ≤ 2), as the lemma predicts for N = 2; LEMMA_H.md §6 lists N = 2 as the
-- control showing "odd" is necessary).  Transcribes `FluxGRow3Witness.lean` (P74, legs (2,1)) at
-- legs (1,1), reusing its half-plane interior lemmas.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
-- Formalization debt; NOT /goal progress.  H59: no (e, f) evaluated.
import Erdos634.Draft.FluxGRow3Witness
import Erdos634.Draft.CaseALemmaHExc2

namespace Erdos634.Draft.CaseALemmaHPiFour

open Erdos634.Geometry Erdos634.CertCoord Erdos634.AreaDet Erdos634.AngleThreshold
open Erdos634.Draft.FluxGRow3Witness (interior_lt0_of_le0 interior_gt0_of_ge0 convex_le0
  convex_ge0 dist_eq_of_sq)

theorem hdet0 : det3 (-1) 0 0 0 0 1 ≠ 0 := by norm_num [det3]
theorem hdet1 : det3 1 0 0 0 0 1 ≠ 0 := by norm_num [det3]
theorem hDTpos : (0:ℝ) < det3 (-1) 0 1 0 0 1 := by norm_num [det3]

noncomputable def tile0 : Tri := mkTri (-1) 0 0 0 0 1 hdet0
noncomputable def tile1 : Tri := mkTri 1 0 0 0 0 1 hdet1
noncomputable def target : Tri := mkTri (-1) 0 1 0 0 1 hDTpos.ne'
noncomputable def model : Tri := tile0
noncomputable def tileF : Fin 2 → Tri := ![tile0, tile1]

theorem tile0_pts : tile0.pts = ![mkPt (-1) 0, mkPt 0 0, mkPt 0 1] := mkTri_pts _ _ _ _ _ _ _
theorem tile1_pts : tile1.pts = ![mkPt 1 0, mkPt 0 0, mkPt 0 1] := mkTri_pts _ _ _ _ _ _ _
theorem target_pts : target.pts = ![mkPt (-1) 0, mkPt 1 0, mkPt 0 1] := mkTri_pts _ _ _ _ _ _ _

theorem hd01 : ∀ i, dist ((tileF i).pts 0) ((tileF i).pts 1) = dist (model.pts 0) (model.pts 1) := by
  intro i; fin_cases i
  · rfl
  · show dist ((tile1).pts 0) ((tile1).pts 1) = dist ((tile0).pts 0) ((tile0).pts 1)
    rw [tile0_pts, tile1_pts]
    show dist (mkPt 1 0) (mkPt 0 0) = dist (mkPt (-1) 0) (mkPt 0 0)
    apply Erdos634.SssCongruent.dist_of_sq
    rw [dist_sq_mkPt, dist_sq_mkPt]; ring

theorem hd12 : ∀ i, dist ((tileF i).pts 1) ((tileF i).pts 2) = dist (model.pts 1) (model.pts 2) := by
  intro i; fin_cases i
  · rfl
  · show dist ((tile1).pts 1) ((tile1).pts 2) = dist ((tile0).pts 1) ((tile0).pts 2)
    rw [tile0_pts, tile1_pts]
    simp

theorem hd20 : ∀ i, dist ((tileF i).pts 2) ((tileF i).pts 0) = dist (model.pts 2) (model.pts 0) := by
  intro i; fin_cases i
  · rfl
  · show dist ((tile1).pts 2) ((tile1).pts 0) = dist ((tile0).pts 2) ((tile0).pts 0)
    rw [tile0_pts, tile1_pts]
    show dist (mkPt 0 1) (mkPt 1 0) = dist (mkPt 0 1) (mkPt (-1) 0)
    apply Erdos634.SssCongruent.dist_of_sq
    rw [dist_sq_mkPt, dist_sq_mkPt]; ring

theorem memB : mkPt (-1 : ℝ) 0 ∈ target.carrier :=
  mem_carrier_of_dets hDTpos (by norm_num [det3]) (by norm_num [det3]) (by norm_num [det3])
theorem memM : mkPt (0 : ℝ) 0 ∈ target.carrier :=
  mem_carrier_of_dets hDTpos (by norm_num [det3]) (by norm_num [det3]) (by norm_num [det3])
theorem memA : mkPt (0 : ℝ) 1 ∈ target.carrier :=
  mem_carrier_of_dets hDTpos (by norm_num [det3]) (by norm_num [det3]) (by norm_num [det3])
theorem memC : mkPt (1 : ℝ) 0 ∈ target.carrier :=
  mem_carrier_of_dets hDTpos (by norm_num [det3]) (by norm_num [det3]) (by norm_num [det3])

theorem hsub : ∀ i, (tileF i).carrier ⊆ target.carrier := by
  intro i; fin_cases i
  · show Erdos634.Geometry.Tri.carrier tile0 ⊆ target.carrier
    unfold Erdos634.Geometry.Tri.carrier
    rw [tile0_pts]
    apply convexHull_min _ target.convex
    rintro p ⟨i, rfl⟩
    fin_cases i
    · exact memB
    · exact memM
    · exact memA
  · show Erdos634.Geometry.Tri.carrier tile1 ⊆ target.carrier
    unfold Erdos634.Geometry.Tri.carrier
    rw [tile1_pts]
    apply convexHull_min _ target.convex
    rintro p ⟨i, rfl⟩
    fin_cases i
    · exact memC
    · exact memM
    · exact memA

theorem tile0_le0 : tile0.carrier ⊆ {p : Plane | p 0 ≤ 0} := by
  show Erdos634.Geometry.Tri.carrier tile0 ⊆ _
  unfold Erdos634.Geometry.Tri.carrier
  rw [tile0_pts]
  apply convexHull_min _ convex_le0
  rintro p ⟨i, rfl⟩
  fin_cases i <;> simp [mkPt_zero]

theorem tile1_ge0 : tile1.carrier ⊆ {p : Plane | 0 ≤ p 0} := by
  show Erdos634.Geometry.Tri.carrier tile1 ⊆ _
  unfold Erdos634.Geometry.Tri.carrier
  rw [tile1_pts]
  apply convexHull_min _ convex_ge0
  rintro p ⟨i, rfl⟩
  fin_cases i <;> simp [mkPt_zero]

theorem hdisj :
    Pairwise fun i j => Disjoint (interior ((tileF i)).carrier) (interior ((tileF j)).carrier) := by
  have h01 : Disjoint (interior tile0.carrier) (interior tile1.carrier) := by
    rw [Set.disjoint_left]
    intro p hp0 hp1
    have h0 : p 0 < 0 := interior_lt0_of_le0 tile0 tile0_le0 hp0
    have h1 : 0 < p 0 := interior_gt0_of_ge0 tile1 tile1_ge0 hp1
    linarith
  intro i j hij
  fin_cases i <;> fin_cases j <;> first
    | exact absurd rfl hij
    | exact h01
    | exact h01.symm

theorem hdet : ∑ i, |detTri (tileF i)| = |detTri target| := by
  have e0 : detTri tile0 = det3 (-1) 0 0 0 0 1 := detTri_mkTri _ _ _ _ _ _ hdet0
  have e1 : detTri tile1 = det3 1 0 0 0 0 1 := detTri_mkTri _ _ _ _ _ _ hdet1
  have eT : detTri target = det3 (-1) 0 1 0 0 1 := detTri_mkTri _ _ _ _ _ _ hDTpos.ne'
  simp only [tileF, Fin.sum_univ_two]
  show |detTri tile0| + |detTri tile1| = _
  rw [e0, e1, eT]
  norm_num [det3]

noncomputable def dissection : CongruentDissection 2 :=
  Erdos634.CertBridge.ofCert target model tileF hd01 hd12 hd20 hsub hdisj hdet

/-! ## The angles -/

theorem dist_mk (a b c d s : ℝ) (hs : 0 ≤ s) (h : (a - c) ^ 2 + (b - d) ^ 2 = s ^ 2) :
    dist (mkPt a b) (mkPt c d) = s := dist_eq_of_sq hs (by rw [dist_sq_mkPt]; exact h)

theorem angle_pi4 {P Q R : Plane} (hPQ : dist P Q = 1) (hRQ : dist R Q = Real.sqrt 2)
    (hPR : dist P R = 1) : cornerAngle P Q R = Real.pi / 4 := by
  have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hs : 0 < Real.sqrt 2 := by positivity
  have hcos : Real.cos (cornerAngle P Q R) = Real.cos (Real.pi / 4) := by
    rw [cos_of_sides _ _ _ (by rw [hPQ]; norm_num) (by rw [hRQ]; exact hs.ne'), hPQ, hRQ, hPR,
      Real.cos_pi_div_four]
    field_simp
    nlinarith
  exact Real.injOn_cos ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
    ⟨by positivity, by linarith [Real.pi_pos]⟩ hcos

theorem angle_pi4' {P Q R : Plane} (hPQ : dist P Q = 2) (hRQ : dist R Q = Real.sqrt 2)
    (hPR : dist P R = Real.sqrt 2) : cornerAngle P Q R = Real.pi / 4 := by
  have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hs : 0 < Real.sqrt 2 := by positivity
  have hcos : Real.cos (cornerAngle P Q R) = Real.cos (Real.pi / 4) := by
    rw [cos_of_sides _ _ _ (by rw [hPQ]; norm_num) (by rw [hRQ]; exact hs.ne'), hPQ, hRQ, hPR,
      Real.cos_pi_div_four]
    field_simp
    nlinarith
  exact Real.injOn_cos ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
    ⟨by positivity, by linarith [Real.pi_pos]⟩ hcos

theorem model_angleAt0 : dissection.model.angleAt 0 = Real.pi / 4 := by
  show cornerAngle (tile0.pts 1) (tile0.pts 0) (tile0.pts 2) = Real.pi / 4
  rw [tile0_pts]
  show cornerAngle (mkPt 0 0) (mkPt (-1) 0) (mkPt 0 1) = Real.pi / 4
  have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  exact angle_pi4 (dist_mk _ _ _ _ _ (by norm_num) (by norm_num))
    (dist_mk _ _ _ _ _ (by positivity) (by rw [h2]; norm_num))
    (dist_mk _ _ _ _ _ (by norm_num) (by norm_num))

theorem model_angleAt1 : dissection.model.angleAt 1 = Real.pi / 2 := by
  show cornerAngle (tile0.pts 2) (tile0.pts 1) (tile0.pts 0) = Real.pi / 2
  rw [tile0_pts]
  show cornerAngle (mkPt 0 1) (mkPt 0 0) (mkPt (-1) 0) = Real.pi / 2
  have hcos : Real.cos (cornerAngle (mkPt 0 1) (mkPt 0 0) (mkPt (-1) 0)) = 0 := by
    rw [cos_of_sides _ _ _ (by rw [dist_mk 0 1 0 0 1 (by norm_num) (by norm_num)]; norm_num)
      (by rw [dist_mk (-1) 0 0 0 1 (by norm_num) (by norm_num)]; norm_num),
      dist_mk 0 1 0 0 1 (by norm_num) (by norm_num), dist_mk (-1) 0 0 0 1 (by norm_num) (by norm_num)]
    have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    rw [dist_mk 0 1 (-1) 0 (Real.sqrt 2) (by positivity) (by rw [h2]; norm_num), h2]
    norm_num
  have hmem : cornerAngle (mkPt 0 1) (mkPt (0:ℝ) 0) (mkPt (-1) 0) ∈ Set.Icc 0 Real.pi :=
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
  have hres := Real.arccos_cos hmem.1 hmem.2
  rw [hcos, Real.arccos_zero] at hres
  exact hres.symm

theorem target_angleAt0 : dissection.target.angleAt 0 = Real.pi / 4 := by
  show cornerAngle (target.pts 1) (target.pts 0) (target.pts 2) = Real.pi / 4
  rw [target_pts]
  show cornerAngle (mkPt 1 0) (mkPt (-1) 0) (mkPt 0 1) = Real.pi / 4
  have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  exact angle_pi4' (dist_mk _ _ _ _ _ (by norm_num) (by norm_num))
    (dist_mk _ _ _ _ _ (by positivity) (by rw [h2]; norm_num))
    (dist_mk _ _ _ _ _ (by positivity) (by rw [h2]; norm_num))

theorem target_angleAt1 : dissection.target.angleAt 1 = Real.pi / 4 := by
  show cornerAngle (target.pts 2) (target.pts 1) (target.pts 0) = Real.pi / 4
  rw [target_pts]
  show cornerAngle (mkPt 0 1) (mkPt 1 0) (mkPt (-1) 0) = Real.pi / 4
  have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  rw [show cornerAngle (mkPt 0 1) (mkPt 1 0) (mkPt (-1) 0)
      = cornerAngle (mkPt (-1) 0) (mkPt 1 0) (mkPt 0 1) from EuclideanGeometry.angle_comm _ _ _]
  exact angle_pi4' (dist_mk _ _ _ _ _ (by norm_num) (by norm_num))
    (dist_mk _ _ _ _ _ (by positivity) (by rw [h2]; norm_num))
    (dist_mk _ _ _ _ _ (by positivity) (by rw [h2]; norm_num))

/-- **Joint witness**: every hypothesis of `lemmaH` holds on this real dissection (θ = π/4 = ¼·π,
model angle θ at vertex 0 and π/2 at vertex 1, target angle θ at vertices 0 and 1). -/
theorem lemmaH_joint_witness : ¬ (Nat.Prime 2 ∧ 5 ≤ 2) :=
  Erdos634.Geometry.CaseA.LemmaH.lemmaH dissection ⟨1 / 4, by push_cast; ring⟩ (by positivity)
    (by linarith [Real.pi_pos]) (p := 0) (q := 1) (by decide) model_angleAt0 model_angleAt1
    (i := 0) (j := 1) (by decide) target_angleAt0 target_angleAt1

/-- `count_eq` on the same dissection (X = 1: equal side √2, hypotenuse √2). -/
theorem count_eq_witness_pi4 :
    ∃ r x y : ℕ, ((2 : ℕ) : ℝ) = 2 * ((r : ℝ) + x * Real.sin (Real.pi / 4)
      + y * Real.cos (Real.pi / 4)) ^ 2 :=
  Erdos634.Geometry.CaseA.LemmaH.count_eq dissection (by positivity) (by linarith [Real.pi_pos])
    (p := 0) (q := 1) (by decide) model_angleAt0 model_angleAt1
    (i := 0) (j := 1) (by decide) target_angleAt0 target_angleAt1

end Erdos634.Draft.CaseALemmaHPiFour

#print axioms Erdos634.Draft.CaseALemmaHPiFour.dissection
#print axioms Erdos634.Draft.CaseALemmaHPiFour.lemmaH_joint_witness
#print axioms Erdos634.Draft.CaseALemmaHPiFour.count_eq_witness_pi4
