-- Draft/LaczFormal32e3.lean -- WITNESS for `lemma32_tri`/`lemma32_tiling`: the isosceles right triangle (-1,0),(1,0),(0,1) cut by its altitude into two tiles
-- (pi/4, pi/2, pi/4) (`CaseALemmaHPiFour.dissection`, N = 2) is IRREGULAR for idx = identity (corner counts B (1,0,0), C (1,0,0), M (0,2,0), A (0,0,2)),
-- so every hypothesis of `lemma32_tri` holds on a real dissection; conclusion: the tile angles lie in the Q-span of the target angles.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012) Lemma 3.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormal32e2
import Erdos634.Draft.CaseALemmaHPiFour

open scoped Classical
open Erdos634.Draft.LaczFormal.Thm21 Erdos634.AreaDet Erdos634.AngleThreshold
open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.TilePlacement Erdos634.Draft.CaseALemmaHPiFour

namespace Erdos634.Draft.LaczFormal.RG

noncomputable abbrev WD := Erdos634.Draft.CaseALemmaHPiFour.dissection

theorem w_tile0 : WD.tile 0 = tile0 := rfl
theorem w_tile1 : WD.tile 1 = tile1 := rfl

theorem tile1_angleAt0 : tile1.angleAt 0 = Real.pi / 4 := by
  show cornerAngle (tile1.pts 1) (tile1.pts 0) (tile1.pts 2) = Real.pi / 4
  rw [tile1_pts]
  show cornerAngle (mkPt 0 0) (mkPt 1 0) (mkPt 0 1) = Real.pi / 4
  have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  exact angle_pi4 (dist_mk _ _ _ _ _ (by norm_num) (by norm_num))
    (dist_mk _ _ _ _ _ (by positivity) (by rw [h2]; norm_num))
    (dist_mk _ _ _ _ _ (by norm_num) (by norm_num))

theorem tile1_angleAt1 : tile1.angleAt 1 = Real.pi / 2 := by
  show cornerAngle (tile1.pts 2) (tile1.pts 1) (tile1.pts 0) = Real.pi / 2
  rw [tile1_pts]
  show cornerAngle (mkPt 0 1) (mkPt 0 0) (mkPt 1 0) = Real.pi / 2
  have hcos : Real.cos (cornerAngle (mkPt 0 1) (mkPt 0 0) (mkPt 1 0)) = 0 := by
    rw [cos_of_sides _ _ _ (by rw [dist_mk 0 1 0 0 1 (by norm_num) (by norm_num)]; norm_num)
      (by rw [dist_mk 1 0 0 0 1 (by norm_num) (by norm_num)]; norm_num),
      dist_mk 0 1 0 0 1 (by norm_num) (by norm_num), dist_mk 1 0 0 0 1 (by norm_num) (by norm_num)]
    have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    rw [dist_mk 0 1 1 0 (Real.sqrt 2) (by positivity) (by rw [h2]; norm_num), h2]
    norm_num
  have hmem : cornerAngle (mkPt 0 1) (mkPt (0:ℝ) 0) (mkPt 1 0) ∈ Set.Icc 0 Real.pi :=
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
  have hres := Real.arccos_cos hmem.1 hmem.2
  rw [hcos, Real.arccos_zero] at hres
  exact hres.symm

theorem angleAt_sum_t (T : Tri) : T.angleAt 0 + T.angleAt 1 + T.angleAt 2 = Real.pi :=
  Erdos634.Draft.LaczFormal.angleAt_sum T

theorem tile0_angleAt2 : tile0.angleAt 2 = Real.pi / 4 := by
  have h := angleAt_sum_t tile0
  have h0 : tile0.angleAt 0 = Real.pi / 4 := model_angleAt0
  have h1 : tile0.angleAt 1 = Real.pi / 2 := model_angleAt1
  linarith

theorem tile1_angleAt2 : tile1.angleAt 2 = Real.pi / 4 := by
  have h := angleAt_sum_t tile1
  linarith [tile1_angleAt0, tile1_angleAt1]

theorem w_idxA : ∀ (i : Fin 2) (v : Fin 3), angleAt WD.model ((fun _ => (1 : Equiv.Perm (Fin 3))) i v) = angleAt (WD.tile i) v := by
  intro i v
  fin_cases i <;> fin_cases v
  · rfl
  · rfl
  · rfl
  · show tile0.angleAt 0 = tile1.angleAt 0
    rw [tile1_angleAt0]; exact model_angleAt0
  · show tile0.angleAt 1 = tile1.angleAt 1
    rw [tile1_angleAt1]; exact model_angleAt1
  · show tile0.angleAt 2 = tile1.angleAt 2
    rw [tile1_angleAt2]; exact tile0_angleAt2

theorem cntR_ne {C : CongruentRegionDissection 2} (X : Plane) (l l' : Fin 3)
    (h1 : ∃ i : Fin 2, (C.tile i).pts l = X) (h2 : ∀ i : Fin 2, (C.tile i).pts l' ≠ X) :
    cntR C (fun _ => 1) X l ≠ cntR C (fun _ => 1) X l' := by
  have e2 : cntR C (fun _ => 1) X l' = 0 := by
    unfold cntR
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro ⟨i, v⟩ _ ⟨hp, hv⟩
    simp only [Equiv.Perm.coe_one, id_eq] at hv hp
    subst hv
    exact h2 i hp
  have e1 : 0 < cntR C (fun _ => 1) X l := by
    unfold cntR
    obtain ⟨i, hi⟩ := h1
    exact Finset.card_pos.mpr ⟨(i, l), by simp [hi]⟩
  omega

theorem mk_ne {a b c d : ℝ} (h : a ≠ c ∨ b ≠ d) : mkPt a b ≠ mkPt c d := by
  intro e
  rcases h with h | h
  · exact h (by simpa using congrFun (congrArg (fun p : Plane => (p : Fin 2 → ℝ)) e) 0)
  · exact h (by simpa using congrFun (congrArg (fun p : Plane => (p : Fin 2 → ℝ)) e) 1)

theorem w_irr : IrregularIdx WD.toRegion (fun _ => 1) := by
  have P0 : ∀ i : Fin 2, (WD.toRegion.tile i).pts 0 = (tileF i).pts 0 := fun i => rfl
  refine ⟨⟨mkPt (-1) 0, cntR_ne _ 0 1 ⟨0, ?_⟩ ?_⟩, ⟨mkPt (-1) 0, cntR_ne _ 0 2 ⟨0, ?_⟩ ?_⟩,
    ⟨mkPt 0 0, cntR_ne _ 1 2 ⟨0, ?_⟩ ?_⟩⟩
  · show tile0.pts 0 = _; rw [tile0_pts]; rfl
  · intro i; fin_cases i
    · show tile0.pts 1 ≠ _; rw [tile0_pts]; exact mk_ne (Or.inl (by norm_num))
    · show tile1.pts 1 ≠ _; rw [tile1_pts]; exact mk_ne (Or.inl (by norm_num))
  · show tile0.pts 0 = _; rw [tile0_pts]; rfl
  · intro i; fin_cases i
    · show tile0.pts 2 ≠ _; rw [tile0_pts]; exact mk_ne (Or.inl (by norm_num))
    · show tile1.pts 2 ≠ _; rw [tile1_pts]; exact mk_ne (Or.inl (by norm_num))
  · show tile0.pts 1 = _; rw [tile0_pts]; rfl
  · intro i; fin_cases i
    · show tile0.pts 2 ≠ _; rw [tile0_pts]; exact mk_ne (Or.inr (by norm_num))
    · show tile1.pts 2 ≠ _; rw [tile1_pts]; exact mk_ne (Or.inr (by norm_num))

theorem witness_lemma32_tri : ∀ l : Fin 3, angleAt WD.model l ∈ Submodule.span ℚ (Set.range WD.target.angleAt) :=
  lemma32_tri WD (fun _ => 1) w_idxA w_irr

#print axioms witness_lemma32_tri

end Erdos634.Draft.LaczFormal.RG
