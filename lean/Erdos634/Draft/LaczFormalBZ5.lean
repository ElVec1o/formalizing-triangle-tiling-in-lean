-- Draft/LaczFormalBZ5.lean -- Beeson-Zhang (arXiv 2604.01314v1) Theorem 5.2, assembly: an equilateral triangle tiled by (alpha, beta, 2 pi/3), alpha not in Q pi, has commensurable sides.
--   bridge: `exists_convpoly_of_equilateral` (a triangle with equal sides is a convex polygon with all angles pi/3, same carrier);
--   `bz_lemma35_tri`: NotComb a b c is impossible (LaczFormalBZ4, after relabeling the model by the permutation of `TwoPiThreeData`);
--   `bz_ab_comm`: a, b commensurable (Lemma 3.6: an a-relation and a b-relation, `comm_of_two_combs`);
--   `bz_thm52`: a, b, c pairwise commensurable (with `bz_c_rational` of LaczFormalBZPhi3).
-- UNAUDITED.  Credit: Beeson-Zhang (arXiv 2604.01314v1, Thm 5.2), Laczkovich (DCG 48 (2012), Sect. 4, 7: the graphs Gamma_a and the invariant Phi).
import Erdos634.Draft.LaczFormalBZ4
import Erdos634.Draft.LaczFormalBZPhi3

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

/-- The polygon `a, b, c` (counterclockwise) as a `ConvPoly 3`. -/
noncomputable def convPoly3 (a b c : Plane) (h : 0 < cross2 (b - a) (c - a)) : ConvPoly 3 where
  v := ![a, b, c]
  three_le := le_refl _
  left := by
    intro i j hji hji1
    unfold cross2 at h ⊢
    simp only [PiLp.sub_apply] at h
    fin_cases i <;> fin_cases j <;> simp at hji hji1 ⊢ <;> nlinarith [h]

theorem convPoly3_carrier (a b c : Plane) (h : 0 < cross2 (b - a) (c - a)) : (convPoly3 a b c h).carrier = (triOf a b c h).carrier := by
  ext y
  rw [triOf_carrier]
  unfold ConvPoly.carrier convPoly3
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hh
    exact ⟨by simpa using hh 0, by simpa using hh 1, by simpa using hh 2⟩
  · rintro ⟨h1, h2, h3⟩ i
    fin_cases i
    · simpa using h1
    · simpa using h2
    · simpa using h3

theorem convPoly3_angle (a b c : Plane) (h : 0 < cross2 (b - a) (c - a)) (i : Fin 3) :
    (convPoly3 a b c h).angle i = (triOf a b c h).angleAt i := by
  unfold ConvPoly.angle Tri.angleAt cornerAngle
  have e : i - 1 = i + 2 := by fin_cases i <;> decide
  rw [e, EuclideanGeometry.angle_comm]
  rfl

/-- **An equilateral triangle is a convex polygon with all angles `π/3`** (same carrier). -/
theorem exists_convpoly_of_equilateral (T : Tri) (heq : ∀ j : Fin 3, dist (T.pts j) (T.pts (j + 1)) = dist (T.pts 0) (T.pts 1)) :
    ∃ P : ConvPoly 3, P.carrier = T.carrier ∧ ∀ i, P.angle i = Real.pi / 3 := by
  have h01 : dist (T.pts 0) (T.pts 1) = dist (T.pts 0) (T.pts 1) := rfl
  have h12 : dist (T.pts 1) (T.pts 2) = dist (T.pts 0) (T.pts 1) := heq 1
  have h20 : dist (T.pts 2) (T.pts 0) = dist (T.pts 0) (T.pts 1) := heq 2
  -- a counterclockwise ordering
  have key : ∀ (a b c : Plane) (h : 0 < cross2 (b - a) (c - a)), (triOf a b c h).carrier = T.carrier →
      dist a b = dist (T.pts 0) (T.pts 1) → dist b c = dist (T.pts 0) (T.pts 1) → dist c a = dist (T.pts 0) (T.pts 1) →
      ∃ P : ConvPoly 3, P.carrier = T.carrier ∧ ∀ i, P.angle i = Real.pi / 3 := by
    intro a b c h hcar d1 d2 d3
    refine ⟨convPoly3 a b c h, by rw [convPoly3_carrier, hcar], fun i => ?_⟩
    rw [convPoly3_angle]
    set t := triOf a b c h with ht
    have o0 : t.oppLen 0 = dist (T.pts 0) (T.pts 1) := by unfold Tri.oppLen; exact d2
    have o1 : t.oppLen 1 = dist (T.pts 0) (T.pts 1) := by unfold Tri.oppLen; exact d3
    have o2 : t.oppLen 2 = dist (T.pts 0) (T.pts 1) := by unfold Tri.oppLen; exact d1
    have a01 := t.angleAt_eq_of_oppLen_eq (show (0 : Fin 3) ≠ 1 by decide) (o0.trans o1.symm)
    have a12 := t.angleAt_eq_of_oppLen_eq (show (1 : Fin 3) ≠ 2 by decide) (o1.trans o2.symm)
    have hs := t.angleAt_sum
    fin_cases i
    · show t.angleAt 0 = _; linarith
    · show t.angleAt 1 = _; linarith
    · show t.angleAt 2 = _; linarith
  have hdet : T.det = cross2 (T.pts 1 - T.pts 0) (T.pts 2 - T.pts 0) := rfl
  rcases T.det_pos_or_neg with hpos | hneg
  · have h : 0 < cross2 (T.pts 1 - T.pts 0) (T.pts 2 - T.pts 0) := by rw [← hdet]; exact hpos
    refine key (T.pts 0) (T.pts 1) (T.pts 2) h ?_ rfl h12 h20
    have : (![T.pts 0, T.pts 1, T.pts 2] : Fin 3 → Plane) = T.pts := by
      funext k; fin_cases k <;> rfl
    show convexHull ℝ (Set.range ![T.pts 0, T.pts 1, T.pts 2]) = convexHull ℝ (Set.range T.pts)
    rw [this]
  · have h : 0 < cross2 (T.pts 2 - T.pts 0) (T.pts 1 - T.pts 0) := by
      have : cross2 (T.pts 2 - T.pts 0) (T.pts 1 - T.pts 0) = - T.det := by
        rw [hdet]; unfold cross2; ring
      rw [this]; linarith
    refine key (T.pts 0) (T.pts 2) (T.pts 1) h ?_ ?_ ?_ ?_
    · show convexHull ℝ (Set.range ![T.pts 0, T.pts 2, T.pts 1]) = convexHull ℝ (Set.range T.pts)
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
    · rw [dist_comm]; exact h20
    · rw [dist_comm]; exact h12
    · exact dist_comm _ _

/-- The swapped placement of the tile. -/
theorem tpt_swap {T : Tri} {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
    T.TwoPiThreeData (Real.pi / 3 - α) b a c := by
  obtain ⟨σ, h0, ha, h1, hb, h2, hc⟩ := h
  refine ⟨σ * Equiv.swap 0 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]; exact h1
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]; exact hb
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_right]; rw [h0]; ring
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_right]; exact ha
  · simp only [Equiv.Perm.mul_apply]
    have : Equiv.swap (0 : Fin 3) 1 2 = 2 := by decide
    rw [this]; exact h2
  · simp only [Equiv.Perm.mul_apply]
    have : Equiv.swap (0 : Fin 3) 1 2 = 2 := by decide
    rw [this]; exact hc

/-- **Beeson-Zhang Lemma 3.5 for an equilateral target**, in the language of `CongruentDissection` and `TwoPiThreeData`:
`a` is a nonnegative rational combination of `b, c`. -/
theorem bz_lemma35_tri (D : CongruentDissection N) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoPiThreeData α a b c)
    (heq : ∀ j : Fin 3, dist (D.target.pts j) (D.target.pts (j + 1)) = dist (D.target.pts 0) (D.target.pts 1)) :
    ¬ NotComb a b c := by
  intro hnc
  obtain ⟨P, hPc, hPang⟩ := exists_convpoly_of_equilateral D.target heq
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  set Dr := relabel D.toRegion σ with hDr
  have hreg : Dr.region = P.carrier := by rw [hPc]; rfl
  haveI : HasFansC Dr.toRegionDissection := hasFansC_poly _ P hreg
  obtain ⟨idx, hidx, hidxA⟩ := exists_idx_both Dr
  have hang : ∀ j, Dr.model.angleAt j = D.model.angleAt (σ j) := fun j => relabel_angleAt D.toRegion σ j
  have hsl : ∀ t, slen Dr t = D.model.oppLen (σ t) := fun t => relabel_slen D.toRegion σ t
  refine bz_lemma35 Dr P hreg idx hidx hidxA ?_ ?_ ?_ ?_ hPang
  · have e0 : slen Dr 0 = a := by rw [hsl]; exact o0
    have e1 : slen Dr 1 = b := by rw [hsl]; exact o1
    have e2 : slen Dr 2 = c := by rw [hsl]; exact o2
    rw [e0, e1, e2]; exact hnc
  · rw [hang]; exact h2
  · rw [hang, hang, h0, h1]; ring
  · rw [hang]; rw [h0]; exact hα

end Erdos634.Draft.LaczFormal.RG
