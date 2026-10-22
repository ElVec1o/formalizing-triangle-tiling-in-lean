-- Draft/LaczFormalBZL7c3.lean -- Beeson-Zhang (arXiv 2604.01314v1) Lemmas 3.5, 3.6 for a TRIANGLE target whose angles are among {pi/3, 2 alpha, 2 beta} (beta = pi/3 - alpha), in the language of `CongruentDissection`/`TwoPiThreeData`:
--   `exists_convpoly_of_tri`  : any triangle is a convex 3-gon with the same carrier and the same angles (up to a permutation of the vertices; either orientation);
--   `bz_lemma35_row`          : `NotComb a b c` is impossible;
--   `bz_ab_comm_row`          : `a`, `b` are commensurable (Lemma 3.5 for `a` and for `b`, Lemma 3.6).
-- NOTE, UNAUDITED.  Credit: Beeson-Zhang (arXiv 2604.01314v1, Lemmas 3.5, 3.6, Thm 5.3), Laczkovich (DCG 48 (2012), Sect. 4, 7), Beeson.
import Erdos634.Draft.LaczFormalBZ6
import Erdos634.Draft.LaczFormalBZL7c2

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

/-- **Any triangle is a convex 3-gon** (same carrier, angles permuted). -/
theorem exists_convpoly_of_tri (T : Tri) :
    ∃ P : ConvPoly 3, P.carrier = T.carrier ∧ ∃ τ : Equiv.Perm (Fin 3), ∀ i, P.angle i = T.angleAt (τ i) := by
  have hdet : T.det = cross2 (T.pts 1 - T.pts 0) (T.pts 2 - T.pts 0) := rfl
  rcases T.det_pos_or_neg with hpos | hneg
  · have h : 0 < cross2 (T.pts 1 - T.pts 0) (T.pts 2 - T.pts 0) := by rw [← hdet]; exact hpos
    refine ⟨convPoly3 (T.pts 0) (T.pts 1) (T.pts 2) h, ?_, 1, fun i => ?_⟩
    · rw [convPoly3_carrier]
      show convexHull ℝ (Set.range ![T.pts 0, T.pts 1, T.pts 2]) = convexHull ℝ (Set.range T.pts)
      have : (![T.pts 0, T.pts 1, T.pts 2] : Fin 3 → Plane) = T.pts := by
        funext k; fin_cases k <;> rfl
      rw [this]
    · rw [convPoly3_angle]
      fin_cases i <;> rfl
  · have h : 0 < cross2 (T.pts 2 - T.pts 0) (T.pts 1 - T.pts 0) := by
      have : cross2 (T.pts 2 - T.pts 0) (T.pts 1 - T.pts 0) = - T.det := by
        rw [hdet]; unfold cross2; ring
      rw [this]; linarith
    refine ⟨convPoly3 (T.pts 0) (T.pts 2) (T.pts 1) h, ?_, Equiv.swap 1 2, fun i => ?_⟩
    · rw [convPoly3_carrier]
      show convexHull ℝ (Set.range ![T.pts 0, T.pts 2, T.pts 1]) = convexHull ℝ (Set.range T.pts)
      congr 1
      ext x
      simp only [Set.mem_range]
      constructor
      · rintro ⟨k, rfl⟩
        fin_cases k
        · exact ⟨0, rfl⟩
        · exact ⟨2, rfl⟩
        · exact ⟨1, rfl⟩
      · rintro ⟨k, rfl⟩
        fin_cases k
        · exact ⟨0, rfl⟩
        · exact ⟨2, rfl⟩
        · exact ⟨1, rfl⟩
    · rw [convPoly3_angle]
      fin_cases i
      · show cornerAngle _ _ _ = cornerAngle _ _ _
        simp [triOf, cornerAngle, Tri.angleAt]
        rw [EuclideanGeometry.angle_comm]
        rfl
      · show cornerAngle _ _ _ = cornerAngle _ _ _
        simp [triOf, cornerAngle]
        rw [EuclideanGeometry.angle_comm]
      · show cornerAngle _ _ _ = cornerAngle _ _ _
        simp [triOf, cornerAngle]
        rw [EuclideanGeometry.angle_comm]

/-- **Beeson-Zhang Lemma 3.5 for a triangle target with angles among `π/3, 2α, 2β`.** -/
theorem bz_lemma35_row (D : CongruentDissection N) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoPiThreeData α a b c)
    (hT : ∀ j, D.target.angleAt j = Real.pi / 3 ∨ D.target.angleAt j = 2 * α ∨ D.target.angleAt j = 2 * (Real.pi / 3 - α)) :
    ¬ NotComb a b c := by
  intro hnc
  obtain ⟨P, hPc, τ, hτ⟩ := exists_convpoly_of_tri D.target
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  set Dr := relabel D.toRegion σ with hDr
  have hreg : Dr.region = P.carrier := by rw [hPc]; rfl
  haveI : HasFansC Dr.toRegionDissection := hasFansC_poly _ P hreg
  obtain ⟨idx, hidx, hidxA⟩ := exists_idx_both Dr
  have hang : ∀ j, Dr.model.angleAt j = D.model.angleAt (σ j) := fun j => relabel_angleAt D.toRegion σ j
  have hsl : ∀ t, slen Dr t = D.model.oppLen (σ t) := fun t => relabel_slen D.toRegion σ t
  have hA0 : Dr.model.angleAt 0 = α := by rw [hang]; exact h0
  have hA1 : Dr.model.angleAt 1 = Real.pi / 3 - α := by rw [hang]; exact h1
  refine bz_lemma35_gen Dr P hreg idx hidx hidxA ?_ ?_ ?_ ?_ ?_
  · have e0 : slen Dr 0 = a := by rw [hsl]; exact o0
    have e1 : slen Dr 1 = b := by rw [hsl]; exact o1
    have e2 : slen Dr 2 = c := by rw [hsl]; exact o2
    rw [e0, e1, e2]; exact hnc
  · rw [hang]; exact h2
  · rw [hA0, hA1]; ring
  · rw [hA0]; exact hα
  · intro i
    rw [hτ i, hA0, hA1]
    exact hT (τ i)

/-- **Beeson-Zhang Lemmas 3.5 and 3.6 for a triangle target with angles among `π/3, 2α, 2β`**: `a` and `b` are commensurable. -/
theorem bz_ab_comm_row (D : CongruentDissection N) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoPiThreeData α a b c)
    (hT : ∀ j, D.target.angleAt j = Real.pi / 3 ∨ D.target.angleAt j = 2 * α ∨ D.target.angleAt j = 2 * (Real.pi / 3 - α)) :
    Comm a b := by
  have h1 := bz_lemma35_row D hα h hT
  have hα' : ¬ ∃ r : ℚ, Real.pi / 3 - α = (r : ℝ) * Real.pi := by
    rintro ⟨r, hr⟩
    apply hα
    refine ⟨1 / 3 - r, ?_⟩
    push_cast
    linarith
  have hT' : ∀ j, D.target.angleAt j = Real.pi / 3 ∨ D.target.angleAt j = 2 * (Real.pi / 3 - α) ∨
      D.target.angleAt j = 2 * (Real.pi / 3 - (Real.pi / 3 - α)) := by
    intro j
    rcases hT j with e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inr (by rw [e]; ring))
    · exact Or.inr (Or.inl e)
  have h2 := bz_lemma35_row D hα' (tpt_swap h) hT'
  unfold NotComb at h1 h2
  push Not at h1 h2
  obtain ⟨r, p, q, hr, e1⟩ := h1
  obtain ⟨r', p', q', hr', e2⟩ := h2
  have ha : 0 < a := by
    obtain ⟨σ, -, o0, -⟩ := h
    rw [← o0]; exact D.model.oppLen_pos' _
  have hb : 0 < b := by
    obtain ⟨σ, -, -, -, o1, -⟩ := h
    rw [← o1]; exact D.model.oppLen_pos' _
  exact comm_of_two_combs ha hb hr e1 hr' e2

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.exists_convpoly_of_tri
#print axioms Erdos634.Draft.LaczFormal.RG.bz_lemma35_row
#print axioms Erdos634.Draft.LaczFormal.RG.bz_ab_comm_row
