import Erdos634.Draft.LaczFormal9i
import Erdos634.Draft.LaczFormalL6Wit3
import Erdos634.Draft.LaczFormalL22Base

/-!
# Laczkovich, Discrete Math. 140 (1995), Theorem 5.3: existence of the second congruent dissection of an isosceles triangle

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) Thm 5.3, the clause `c(T) = 2`), Beeson.
Formalization debt, not progress on the /goal outcomes.

`isosceles_split`: every triangle `S` with `dist (S.pts 2) (S.pts 0) = dist (S.pts 2) (S.pts 1)` (apex at vertex 2) is a real
`CongruentDissection 2` by its altitude: tiles `(P0, M, P2)` and `(P1, M, P2)` with `M` the midpoint of `P0 P1`; the model has angles
`(alpha, pi/2, pi/2 - alpha)` with `alpha = S.angleAt 0` the base angle.  With `thm53_c_classify` this is the clause `c(T) = 2` for an
isosceles `T` that is neither right nor equilateral: the second tile `(alpha, pi/2 - alpha, pi/2)` is not similar to `T`
(`isosceles_split_not_similar`).
-/

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.TheoremPConditional Erdos634.Draft.LaczFormal Erdos634.LaczL22

namespace Erdos634.Laczkovich9

theorem det_half0 (S : Tri) :
    det3 (S.pts 0 0) (S.pts 0 1) ((S.pts 0 0 + S.pts 1 0) / 2) ((S.pts 0 1 + S.pts 1 1) / 2) (S.pts 2 0) (S.pts 2 1)
      = S.det / 2 := by
  unfold det3 Tri.det
  simp only [PiLp.sub_apply]
  ring

theorem det_half1 (S : Tri) :
    det3 (S.pts 1 0) (S.pts 1 1) ((S.pts 0 0 + S.pts 1 0) / 2) ((S.pts 0 1 + S.pts 1 1) / 2) (S.pts 2 0) (S.pts 2 1)
      = -(S.det / 2) := by
  unfold det3 Tri.det
  simp only [PiLp.sub_apply]
  ring

noncomputable def halfTri0 (S : Tri) : Tri :=
  mkTri (S.pts 0 0) (S.pts 0 1) ((S.pts 0 0 + S.pts 1 0) / 2) ((S.pts 0 1 + S.pts 1 1) / 2) (S.pts 2 0) (S.pts 2 1)
    (by rw [det_half0]; exact div_ne_zero S.det_ne_zero two_ne_zero)

noncomputable def halfTri1 (S : Tri) : Tri :=
  mkTri (S.pts 1 0) (S.pts 1 1) ((S.pts 0 0 + S.pts 1 0) / 2) ((S.pts 0 1 + S.pts 1 1) / 2) (S.pts 2 0) (S.pts 2 1)
    (by rw [det_half1]; exact neg_ne_zero.mpr (div_ne_zero S.det_ne_zero two_ne_zero))

theorem mid_coords (S : Tri) : mkPt ((S.pts 0 0 + S.pts 1 0) / 2) ((S.pts 0 1 + S.pts 1 1) / 2) = Mid S := by
  unfold Mid
  ext i; fin_cases i <;> simp [mkPt_zero, mkPt_one] <;> ring

theorem h0_pts0 (S : Tri) : (halfTri0 S).pts 0 = S.pts 0 := mkPt_self _
theorem h0_pts1 (S : Tri) : (halfTri0 S).pts 1 = Mid S := mid_coords S
theorem h0_pts2 (S : Tri) : (halfTri0 S).pts 2 = S.pts 2 := mkPt_self _
theorem h1_pts0 (S : Tri) : (halfTri1 S).pts 0 = S.pts 1 := mkPt_self _
theorem h1_pts1 (S : Tri) : (halfTri1 S).pts 1 = Mid S := mid_coords S
theorem h1_pts2 (S : Tri) : (halfTri1 S).pts 2 = S.pts 2 := mkPt_self _

theorem dist_mid0 (S : Tri) : dist (S.pts 0) (Mid S) = dist (S.pts 0) (S.pts 1) / 2 := by
  unfold Mid
  rw [dist_eq_norm, dist_eq_norm, show S.pts 0 - (1 / 2 : ℝ) • (S.pts 0 + S.pts 1) = (1 / 2 : ℝ) • (S.pts 0 - S.pts 1) by module,
    norm_smul]
  norm_num; ring

theorem dist_mid1 (S : Tri) : dist (S.pts 1) (Mid S) = dist (S.pts 0) (S.pts 1) / 2 := by
  unfold Mid
  rw [dist_eq_norm, dist_eq_norm, show S.pts 1 - (1 / 2 : ℝ) • (S.pts 0 + S.pts 1) = (-(1 / 2 : ℝ)) • (S.pts 0 - S.pts 1) by module,
    norm_smul]
  norm_num; ring

/-- **The altitude split of an isosceles triangle** (apex at vertex 2). -/
theorem isosceles_split (S : Tri) (hiso : dist (S.pts 2) (S.pts 0) = dist (S.pts 2) (S.pts 1)) :
    ∃ D : CongruentDissection 2, D.target = S ∧ D.model = halfTri0 S := by
  obtain ⟨hcov, hdis⟩ := halve_split S (halfTri0 S) (halfTri1 S) (h0_pts0 S) (h0_pts1 S) (h0_pts2 S) (h1_pts0 S)
    (h1_pts1 S) (h1_pts2 S)
  have c1 : (halfTri1 S).Congruent (halfTri0 S) := by
    refine Erdos634.SssCongruent.congruent_of_dist_three ?_ ?_ ?_
    · rw [h1_pts0, h1_pts1, h0_pts0, h0_pts1, dist_mid1, dist_mid0]
    · rw [h1_pts1, h1_pts2, h0_pts1, h0_pts2]
    · rw [h1_pts2, h1_pts0, h0_pts2, h0_pts0]; exact hiso.symm
  refine ⟨⟨⟨S, ![halfTri0 S, halfTri1 S], ?_, ?_⟩, halfTri0 S, ?_⟩, rfl, rfl⟩
  · rw [← hcov]
    ext x
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
    · rintro (h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | exact hdis | exact hdis.symm
  · intro i; fin_cases i
    · exact Tri.Congruent.refl _
    · exact c1

/-- The angles of the half: `(alpha, pi/2, pi/2 - alpha)` with `alpha` the base angle of `S` at vertex 0. -/
theorem isosceles_split_angles (S : Tri) (hiso : dist (S.pts 2) (S.pts 0) = dist (S.pts 2) (S.pts 1)) :
    (halfTri0 S).angleAt 0 = S.angleAt 0 ∧ (halfTri0 S).angleAt 1 = Real.pi / 2 ∧
      (halfTri0 S).angleAt 2 = Real.pi / 2 - S.angleAt 0 := by
  have h0 : (halfTri0 S).angleAt 0 = S.angleAt 0 := by
    show cornerAngle ((halfTri0 S).pts 1) ((halfTri0 S).pts 0) ((halfTri0 S).pts 2) =
      cornerAngle (S.pts 1) (S.pts 0) (S.pts 2)
    rw [h0_pts0, h0_pts1, h0_pts2]
    unfold cornerAngle
    rw [EuclideanGeometry.angle, EuclideanGeometry.angle]
    have : Mid S -ᵥ S.pts 0 = (1 / 2 : ℝ) • (S.pts 1 -ᵥ S.pts 0) := by
      unfold Mid; simp only [vsub_eq_sub]; module
    rw [this]
    exact InnerProductGeometry.angle_smul_left_of_pos _ _ (by norm_num)
  have h1 : (halfTri0 S).angleAt 1 = Real.pi / 2 := by
    show cornerAngle ((halfTri0 S).pts 2) ((halfTri0 S).pts 1) ((halfTri0 S).pts 0) = Real.pi / 2
    rw [h0_pts0, h0_pts1, h0_pts2]
    unfold cornerAngle
    rw [EuclideanGeometry.angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
    simp only [vsub_eq_sub]
    -- <P2 - M, P0 - M> = 0 since |P2 - P0| = |P2 - P1| and M is the midpoint
    have e0 : S.pts 0 - Mid S = (1 / 2 : ℝ) • (S.pts 0 - S.pts 1) := by unfold Mid; module
    have e1 : S.pts 2 - Mid S = (S.pts 2 - S.pts 0) + (1 / 2 : ℝ) • (S.pts 0 - S.pts 1) := by unfold Mid; module
    rw [e0, e1, inner_smul_right, inner_add_left, inner_smul_left]
    have hn : ‖S.pts 2 - S.pts 0‖ = ‖S.pts 2 - S.pts 1‖ := by
      rw [← dist_eq_norm, ← dist_eq_norm]; exact hiso
    have key : inner ℝ (S.pts 2 - S.pts 0) (S.pts 0 - S.pts 1) + (1 / 2 : ℝ) * inner ℝ (S.pts 0 - S.pts 1) (S.pts 0 - S.pts 1) = 0 := by
      have a : S.pts 2 - S.pts 1 = (S.pts 2 - S.pts 0) + (S.pts 0 - S.pts 1) := by abel
      have b := congrArg (fun x : ℝ => x ^ 2) hn
      simp only at b
      rw [a, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right] at b
      have c : inner ℝ (S.pts 0 - S.pts 1) (S.pts 2 - S.pts 0) = inner ℝ (S.pts 2 - S.pts 0) (S.pts 0 - S.pts 1) :=
        real_inner_comm _ _
      linarith
    simp only [conj_trivial, RCLike.conj_to_real]
    nlinarith [key]
  refine ⟨h0, h1, ?_⟩
  have := (halfTri0 S).angleAt_sum
  linarith

/-- The dissection of the isosceles triangle `S` and its tile angles in the `TileAngles` form. -/
theorem isosceles_split_tileAngles (S : Tri) (hiso : dist (S.pts 2) (S.pts 0) = dist (S.pts 2) (S.pts 1)) :
    ∃ D : CongruentDissection 2, D.target = S ∧
      TileAngles D (S.angleAt 0) (Real.pi / 2 - S.angleAt 0) (Real.pi / 2) := by
  obtain ⟨D, ht, hm⟩ := isosceles_split S hiso
  obtain ⟨a0, a1, a2⟩ := isosceles_split_angles S hiso
  refine ⟨D, ht, Equiv.swap 1 2, ?_, ?_, ?_⟩
  · show D.model.angleAt ((Equiv.swap (1 : Fin 3) 2) 0) = _
    rw [show (Equiv.swap (1 : Fin 3) 2) 0 = 0 by decide, hm]; exact a0
  · show D.model.angleAt ((Equiv.swap (1 : Fin 3) 2) 1) = _
    rw [show (Equiv.swap (1 : Fin 3) 2) 1 = 2 by decide, hm]; exact a2
  · show D.model.angleAt ((Equiv.swap (1 : Fin 3) 2) 2) = _
    rw [show (Equiv.swap (1 : Fin 3) 2) 2 = 1 by decide, hm]; exact a1

/-- If the base angle `alpha` is not `pi/4`, the right tile `(alpha, pi/2 - alpha, pi/2)` is not similar to the isosceles
triangle `(alpha, alpha, pi - 2 alpha)` (it has a right angle, the target has none unless `alpha = pi/4`). -/
theorem isosceles_split_not_similar (α : ℝ) (hα : α ≠ Real.pi / 4) (hα0 : 0 < α) (hα2 : α < Real.pi / 2)
    (σ : Equiv.Perm (Fin 3)) :
    ¬ (∀ k, (![α, Real.pi / 2 - α, Real.pi / 2] : Fin 3 → ℝ) (σ k) = (![α, α, Real.pi - 2 * α] : Fin 3 → ℝ) k) := by
  intro h
  -- the right angle pi/2 occurs in the tile; it must equal one of alpha, alpha, pi - 2 alpha
  obtain ⟨m, hm⟩ := σ.surjective 2
  have := h m
  rw [hm] at this
  simp only [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at this
  fin_cases m <;> simp at this
  · exact absurd (by linarith : α = Real.pi / 4 + Real.pi / 4) (by intro e; apply hα; linarith)
  · exact absurd (by linarith : α = Real.pi / 4 + Real.pi / 4) (by intro e; apply hα; linarith)
  · apply hα; linarith

end Erdos634.Laczkovich9

#print axioms Erdos634.Laczkovich9.isosceles_split
#print axioms Erdos634.Laczkovich9.isosceles_split_angles
#print axioms Erdos634.Laczkovich9.isosceles_split_tileAngles
#print axioms Erdos634.Laczkovich9.isosceles_split_not_similar

namespace Erdos634.Laczkovich9

open Erdos634.Geometry EuclideanGeometry

theorem iso_base_angles (S : Tri) (hiso : dist (S.pts 2) (S.pts 0) = dist (S.pts 2) (S.pts 1)) :
    S.angleAt 1 = S.angleAt 0 ∧ S.angleAt 2 = Real.pi - 2 * S.angleAt 0 := by
  have h := EuclideanGeometry.angle_eq_angle_of_dist_eq hiso
  have e0 : S.angleAt 0 = ∠ (S.pts 2) (S.pts 0) (S.pts 1) := by
    show cornerAngle (S.pts 1) (S.pts 0) (S.pts 2) = _
    unfold cornerAngle; rw [EuclideanGeometry.angle_comm]
  have e1 : S.angleAt 1 = ∠ (S.pts 2) (S.pts 1) (S.pts 0) := rfl
  have h1 : S.angleAt 1 = S.angleAt 0 := by rw [e0, e1]; exact h.symm
  refine ⟨h1, ?_⟩
  have := S.angleAt_sum
  linarith

/-- The trivial dissection of `S` by itself (one tile). -/
noncomputable def selfDissection (S : Tri) : CongruentDissection 1 :=
  ⟨⟨S, ![S], by ext x; simp, by intro i j hij; exact absurd (Subsingleton.elim i j) hij⟩, S, fun i => by fin_cases i; exact Tri.Congruent.refl S⟩

/-- **DM 140 (1995) Thm 5.3, the `c(T) = 2` package for an isosceles `T` that is neither right nor equilateral**
(apex at vertex 2, base angle `alpha`, rational angles).  (a) every `CongruentDissection` of `T` is by a tile of `T`'s own shape
`(alpha, alpha, pi - 2 alpha)` or by the right tile `(alpha, pi/2 - alpha, pi/2)`; (b) `T` itself is tiled by its own shape;
(c) `T` is tiled by the right tile (altitude split); (d) the two shapes are not similar. -/
theorem thm53_c_isosceles (S : Tri) (hiso : dist (S.pts 2) (S.pts 0) = dist (S.pts 2) (S.pts 1))
    (hcomm : CommAngles S) (hr : S.angleAt 0 ≠ Real.pi / 4) (he : S.angleAt 0 ≠ Real.pi / 3) :
    (∀ (N : ℕ) (D : CongruentDissection N), D.target = S →
      TileAngles D (S.angleAt 0) (S.angleAt 0) (Real.pi - 2 * S.angleAt 0) ∨
      TileAngles D (S.angleAt 0) (Real.pi / 2 - S.angleAt 0) (Real.pi / 2)) ∧
    (∃ D : CongruentDissection 1, D.target = S ∧ TileAngles D (S.angleAt 0) (S.angleAt 0) (Real.pi - 2 * S.angleAt 0)) ∧
    (∃ D : CongruentDissection 2, D.target = S ∧ TileAngles D (S.angleAt 0) (Real.pi / 2 - S.angleAt 0) (Real.pi / 2)) ∧
    (S.angleAt 0 < Real.pi / 2 →
      ∀ σ : Equiv.Perm (Fin 3), ¬ (∀ k, (![S.angleAt 0, Real.pi / 2 - S.angleAt 0, Real.pi / 2] : Fin 3 → ℝ) (σ k) =
        (![S.angleAt 0, S.angleAt 0, Real.pi - 2 * S.angleAt 0] : Fin 3 → ℝ) k)) := by
  obtain ⟨b1, b2⟩ := iso_base_angles S hiso
  have hpi := Real.pi_pos
  have hpos : 0 < S.angleAt 0 := Erdos634.MarchFlank.cornerAngle_pos S 0
  refine ⟨?_, ?_, isosceles_split_tileAngles S hiso, ?_⟩
  · intro N D hD
    have hne : ¬ Equilateral D := by
      intro hE
      have := hE 2
      rw [hD, b2] at this
      apply he; linarith
    have hc : CommAngles D.target := by rw [hD]; exact hcomm
    rcases thm53_c_classify D hne hc with ⟨σ, hσ⟩ | ⟨α, j₁, j₂, hj, h1, h2, ht⟩
    · left
      refine ⟨σ, ?_, ?_, ?_⟩
      · rw [hσ 0, hD]
      · rw [hσ 1, hD, b1]
      · rw [hσ 2, hD, b2]
    · right
      rw [hD] at h1 h2
      have hα : α = S.angleAt 0 := by
        have vals : ∀ j : Fin 3, S.angleAt j = ![S.angleAt 0, S.angleAt 0, Real.pi - 2 * S.angleAt 0] j := by
          intro j; fin_cases j
          · rfl
          · exact b1
          · exact b2
        rw [vals j₁] at h1
        rw [vals j₂] at h2
        fin_cases j₁ <;> fin_cases j₂ <;> simp at hj h1 h2 <;> first | linarith | (exfalso; apply he; linarith)
      rw [hα] at ht
      exact ht
  · refine ⟨selfDissection S, rfl, ?_⟩
    refine ⟨Equiv.refl _, ?_, ?_, ?_⟩
    · rfl
    · exact b1
    · exact b2
  · intro hlt
    exact isosceles_split_not_similar _ hr hpos hlt

end Erdos634.Laczkovich9

#print axioms Erdos634.Laczkovich9.thm53_c_isosceles
