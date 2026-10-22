-- Draft/LaczFormalBZL7d5b.lean -- Beeson-Zhang (arXiv 2604.01314v1) THEOREM 3.7 / the last step of Lemma 3.4, formal and complete for every triangle target not similar to the tile:
--   `bz_allc_false` : D : CongruentDissection N of a triangle by the tile (alpha, pi/3 - alpha, 2 pi/3) (`TwoPiThreeData alpha a b c`), alpha not in Q pi, NotSim D, a and b commensurable, c NOT commensurable with a  ==>  False.
-- Route: no c-relation (NotComb c b a, from Comm a b and c not in Q a) => every side of the triangle is a positive multiple of c (LaczFormalBZL7d4b `sides_all_c`: uniform status along each side by `walk_status_chain` +
-- `side_has_c`), so every boundary tile edge has length c (`sideEdges_all_c`); then the flux identity of f_alpha (`bz_phi_gen`) gives (a - b) * sum_j m_j w_j = 0, hence sum_j eps_j m_j = 0 with eps_j = chi(pi - angle) in {+1,-1},
-- product 1 (`Tri.chi_prod`), and m_j < m_{j+1} + m_{j+2} (strict triangle inequality): impossible (`sign_contradiction`).  This replaces BZ Thm 5.2/5.3 AND the corner count of Lemma 3.4 by one argument valid for all targets.
-- NOTE, UNAUDITED.  Credit: Beeson-Zhang (arXiv 2604.01314v1, Lemma 3.4, Thm 3.7, 5.2, 5.3), Laczkovich (DCG 48 (2012), Sect. 4, 7.3), Beeson.
import Erdos634.Draft.LaczFormalBZL7d4b
import Erdos634.Draft.LaczFormalBZL7d3
import Erdos634.Draft.LaczFormalBZL7d5a
import Erdos634.Draft.LaczFormalBZL7c7

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

/-- **Any triangle is a convex 3-gon** (same carrier, angles permuted). -/
theorem exists_convpoly_of_tri' (T : Tri) :
    ∃ P : ConvPoly 3, P.carrier = T.carrier ∧ ∃ τ : Equiv.Perm (Fin 3), (∀ i, P.angle i = T.angleAt (τ i)) ∧ (∀ i, P.v i = T.pts (τ i)) := by
  have hdet : T.det = cross2 (T.pts 1 - T.pts 0) (T.pts 2 - T.pts 0) := rfl
  rcases T.det_pos_or_neg with hpos | hneg
  · have h : 0 < cross2 (T.pts 1 - T.pts 0) (T.pts 2 - T.pts 0) := by rw [← hdet]; exact hpos
    refine ⟨convPoly3 (T.pts 0) (T.pts 1) (T.pts 2) h, ?_, 1, fun i => ?_, fun i => ?_⟩
    · rw [convPoly3_carrier]
      show convexHull ℝ (Set.range ![T.pts 0, T.pts 1, T.pts 2]) = convexHull ℝ (Set.range T.pts)
      have : (![T.pts 0, T.pts 1, T.pts 2] : Fin 3 → Plane) = T.pts := by
        funext k; fin_cases k <;> rfl
      rw [this]
    · rw [convPoly3_angle]
      fin_cases i <;> rfl
    · fin_cases i <;> rfl
  · have h : 0 < cross2 (T.pts 2 - T.pts 0) (T.pts 1 - T.pts 0) := by
      have : cross2 (T.pts 2 - T.pts 0) (T.pts 1 - T.pts 0) = - T.det := by
        rw [hdet]; unfold cross2; ring
      rw [this]; linarith
    refine ⟨convPoly3 (T.pts 0) (T.pts 2) (T.pts 1) h, ?_, Equiv.swap 1 2, fun i => ?_, fun i => ?_⟩
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
    · fin_cases i <;> first | rfl | simp [convPoly3, Equiv.swap_apply_def]

/-- The sides of the convex 3-gon `P` are the sides of the triangle. -/
theorem target_side_eq (T : Tri) (P : ConvPoly 3) (τ : Equiv.Perm (Fin 3)) (hv : ∀ i, P.v i = T.pts (τ i)) (j : Fin 3) :
    ∃ i, P.side i = dist (T.pts j) (T.pts (j + 1)) := by
  have f1 : ∀ a b : Fin 3, b ≠ a → b = a + 1 ∨ b = a + 2 := by
    intro a b h1
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl h1 | exact Or.inl rfl | exact Or.inr rfl
  have f2 : ∀ a b c : Fin 3, b ≠ a → c ≠ a → c ≠ b → b = a + 2 → c = a + 1 := by
    intro a b c h1 h2 h3 h4
    fin_cases a <;> fin_cases b <;> fin_cases c <;> first | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd rfl h3 | exact rfl | (exfalso; revert h4; decide)
  have g1 : ∀ x : Fin 3, x + 1 ≠ x := by intro x; fin_cases x <;> decide
  have g2 : ∀ x : Fin 3, x + 2 ≠ x := by intro x; fin_cases x <;> decide
  have g3 : ∀ x : Fin 3, x + 2 ≠ x + 1 := by intro x; fin_cases x <;> decide
  have g4 : ∀ x : Fin 3, x + 2 + 1 = x := by intro x; fin_cases x <;> decide
  set i0 := τ.symm j with hi0
  have h0 : τ i0 = j := by simp [hi0]
  have hne1 : τ (i0 + 1) ≠ j := by
    rw [← h0]
    intro e
    exact g1 i0 (τ.injective e)
  rcases f1 j (τ (i0 + 1)) hne1 with hb | hb
  · refine ⟨i0, ?_⟩
    unfold ConvPoly.side
    rw [hv, hv, h0, hb]
  · have hc : τ (i0 + 2) = j + 1 := by
      apply f2 j (τ (i0 + 1)) (τ (i0 + 2)) hne1 _ _ hb
      · rw [← h0]; intro e; exact g2 i0 (τ.injective e)
      · intro e; exact g3 i0 (τ.injective e)
    refine ⟨i0 + 2, ?_⟩
    unfold ConvPoly.side
    rw [hv, g4, hv, hc, h0, dist_comm]

/-- Standard set-up for a triangle target with the vertex facts of the 3-gon (continuation form). -/
theorem tri_setup2 (D : CongruentDissection N) {α a b c : ℝ} (h : D.model.TwoPiThreeData α a b c) {R : Prop}
    (k : ∀ (Dr : CongruentRegionDissection N) [HasFansC Dr.toRegionDissection] (P : ConvPoly 3) (hreg : Dr.region = P.carrier)
      (idx : Fin N → Equiv.Perm (Fin 3))
      (hidx : ∀ i k k', dist ((Dr.tile i).pts k) ((Dr.tile i).pts k') = dist (Dr.model.pts (idx i k)) (Dr.model.pts (idx i k')))
      (hidxA : ∀ i v, Dr.model.angleAt (idx i v) = (Dr.tile i).angleAt v),
      slen Dr 0 = a → slen Dr 1 = b → slen Dr 2 = c →
      Dr.model.angleAt 0 = α → Dr.model.angleAt 1 = Real.pi / 3 - α → Dr.model.angleAt 2 = 2 * Real.pi / 3 →
      P.angle 0 + P.angle 1 + P.angle 2 = Real.pi → (∀ i, 0 < P.angle i) → (∀ i, P.angle i < Real.pi) →
      (NotSim D → ¬ ∃ ρ : Equiv.Perm (Fin 3), ∀ k : Fin 3, P.angle (k + 1) = Dr.model.angleAt (ρ k)) →
      ∀ τ : Equiv.Perm (Fin 3), (∀ i, P.v i = D.target.pts (τ i)) → (∀ i, P.angle i = D.target.angleAt (τ i)) → R) : R := by
  obtain ⟨P, hPc, τ, hτ, hτv⟩ := exists_convpoly_of_tri' D.target
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  set Dr := relabel D.toRegion σ with hDr
  have hreg : Dr.region = P.carrier := by rw [hPc]; rfl
  haveI : HasFansC Dr.toRegionDissection := hasFansC_poly _ P hreg
  obtain ⟨idx, hidx, hidxA⟩ := exists_idx_both Dr
  have hang : ∀ j, Dr.model.angleAt j = D.model.angleAt (σ j) := fun j => relabel_angleAt D.toRegion σ j
  have hsl : ∀ t, slen Dr t = D.model.oppLen (σ t) := fun t => relabel_slen D.toRegion σ t
  have hs : D.target.angleAt 0 + D.target.angleAt 1 + D.target.angleAt 2 = Real.pi := angleAt_sum D.target
  have hp : ∀ j, 0 < D.target.angleAt j := fun j => D.target.angleAt_pos'' j
  have hPsum : P.angle 0 + P.angle 1 + P.angle 2 = Real.pi := by
    simp only [hτ]
    have : ∑ i : Fin 3, D.target.angleAt (τ i) = ∑ i : Fin 3, D.target.angleAt i := Equiv.sum_comp τ (fun i => D.target.angleAt i)
    simp only [Fin.sum_univ_three] at this
    linarith
  refine k Dr P hreg idx hidx hidxA (by rw [hsl]; exact o0) (by rw [hsl]; exact o1) (by rw [hsl]; exact o2)
    (by rw [hang]; exact h0) (by rw [hang]; exact h1) (by rw [hang]; exact h2) hPsum (fun i => by rw [hτ]; exact hp _) (fun i => ?_) ?_ τ hτv hτ
  · rw [hτ]
    have fin3 : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
    have e : ∀ j : Fin 3, D.target.angleAt j < Real.pi := by
      intro j
      rcases fin3 j with rfl | rfl | rfl <;> linarith [hp 0, hp 1, hp 2]
    exact e _
  · intro hNS ⟨ρ, hρ⟩
    apply hNS
    refine ⟨τ.symm.trans ((Equiv.addRight (-1 : Fin 3)).trans (ρ.trans σ)), fun j => ?_⟩
    obtain ⟨m, rfl⟩ := τ.surjective j
    have := hρ (m - 1)
    rw [hτ, hang] at this
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.coe_addRight]
    have e : m - 1 + 1 = m := by simp
    rw [e] at this
    rw [show m + -1 = m - 1 from by simp [sub_eq_add_neg]]
    exact this

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.exists_convpoly_of_tri'
#print axioms Erdos634.Draft.LaczFormal.RG.target_side_eq
#print axioms Erdos634.Draft.LaczFormal.RG.tri_setup2
