-- Draft/LaczFormalBZPhi1.lean -- Beeson-Zhang (arXiv 2604.01314v1) Sect. 4: the invariant Phi of Laczkovich (DCG 48 (2012) p. 351, 365) on a SINGLE TILE.
-- The repo's flux layer (`GridChar`, `Tri.flux`, `fAlpha`: the grid {j pi/3 + k alpha}, weight (-1)^j) IS Phi.  New here: the sign of the tile's flux in terms of the direction of its `c`-edge:
--   `Tri.flux_cedge`: for a placement T of the tile (alpha, beta = pi/3 - alpha, gamma = 2 pi/3) and the vertex kg of angle 2 pi/3,
--   flux_{f_alpha}(T) = weight(leftUnit of the edge opposite kg) * (c + a - b)         [Beeson-Zhang, Lemma 5.1's computation, both orientations]
-- (`Tri.weight_form`: every edge direction weight is s * chi(pi - angle of the opposite vertex), for a +-1 character).  Plus the classification of the edge lengths of a placement.
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), p. 351, 365: the invariant Phi), Beeson-Zhang (arXiv 2604.01314v1, Sect. 4, 5).
import Erdos634.Draft.FluxPaper
import Erdos634.MarchFlank

open scoped Classical

namespace Erdos634.Geometry

/-- Positivity of the sides (opposite lengths) of a triangle. -/
theorem Tri.oppLen_pos' (T : Tri) (k : Fin 3) : 0 < T.oppLen k := by
  unfold Tri.oppLen
  have hne : k + 1 ≠ k + 2 := by fin_cases k <;> decide
  exact dist_pos.mpr fun h => hne (T.indep.injective h)

theorem Tri.angleAt_pos'' (T : Tri) (j : Fin 3) : 0 < T.angleAt j :=
  Erdos634.MarchFlank.cornerAngle_pos T j

/-- **Every edge direction weight is `s * chi(pi - angle of the opposite vertex)`**, and the flux is `s` times the tile value (either orientation). -/
theorem Tri.weight_form (G : GridChar ℝ) (hsq : ∀ l ∈ G.L, G.chi l * G.chi l = 1) (T : Tri)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) :
    ∃ s : ℝ, (∀ k : Fin 3, G.weight (T.leftUnit k) = s * G.chi ((Real.pi - T.angleAt (k + 2) : ℝ) : Real.Angle)) ∧
      T.flux G.weight = s * G.tileValue T := by
  have hc0 := hsq _ (T.pi_sub_angleAt_mem G h 0)
  have hc1 := hsq _ (T.pi_sub_angleAt_mem G h 1)
  have hc2 := hsq _ (T.pi_sub_angleAt_mem G h 2)
  have hprod := T.chi_prod G h
  have hK : G.tileValue T
      = G.chi ((Real.pi - T.angleAt 0 : ℝ) : Real.Angle) * T.oppLen 0
        + G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle) * T.oppLen 1
        + G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle) * T.oppLen 2 := by
    unfold GridChar.tileValue
    rw [Fin.sum_univ_three]
  set c0 := G.chi ((Real.pi - T.angleAt 0 : ℝ) : Real.Angle) with hc0def
  set c1 := G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle) with hc1def
  set c2 := G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle) with hc2def
  have e1 : c0 * c2 = c1 := by linear_combination c1 * hprod - (c0 * c2) * hc1
  have e2 : c0 * c1 = c2 := by linear_combination c2 * hprod - (c0 * c1) * hc2
  rcases T.det_pos_or_neg with hT | hT
  · have t1 := T.leftUnit_turn_of_pos hT 0
    have t2 := T.leftUnit_turn_of_pos hT 1
    simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl] at t1 t2
    have w1 : G.weight (T.leftUnit 1) = c1 * G.weight (T.leftUnit 0) := by
      unfold GridChar.weight
      rw [t1, G.val_add _ (T.pi_sub_angleAt_mem G h 1)]
    have w2 : G.weight (T.leftUnit 2) = c2 * G.weight (T.leftUnit 1) := by
      unfold GridChar.weight
      rw [t2, G.val_add _ (T.pi_sub_angleAt_mem G h 2)]
    set w := G.weight (T.leftUnit 0) with hwdef
    refine ⟨w * c2, ?_, ?_⟩
    · intro k
      fin_cases k
      · show G.weight (T.leftUnit 0) = w * c2 * c2
        rw [← hwdef]; linear_combination (-w) * hc2
      · show G.weight (T.leftUnit 1) = w * c2 * c0
        rw [w1]; linear_combination (-w) * e1
      · show G.weight (T.leftUnit 2) = w * c2 * c1
        rw [w2, w1]; ring
    · rw [T.flux_grid_of_pos G hT h, hK]
      linear_combination (-(w * T.oppLen 2)) * hc2 - (w * T.oppLen 0) * e1
  · have t0 := T.leftUnit_turn_of_neg hT 0
    have t1 := T.leftUnit_turn_of_neg hT 1
    simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl] at t0 t1
    have w1 : G.weight (T.leftUnit 1) = c2 * G.weight (T.leftUnit 2) := by
      unfold GridChar.weight
      rw [t1, G.val_add _ (T.pi_sub_angleAt_mem G h 2)]
    have w0 : G.weight (T.leftUnit 0) = c1 * G.weight (T.leftUnit 1) := by
      unfold GridChar.weight
      rw [t0, G.val_add _ (T.pi_sub_angleAt_mem G h 1)]
    set w := G.weight (T.leftUnit 2) with hwdef
    refine ⟨w * c1, ?_, ?_⟩
    · intro k
      fin_cases k
      · show G.weight (T.leftUnit 0) = w * c1 * c2
        rw [w0, w1]; ring
      · show G.weight (T.leftUnit 1) = w * c1 * c0
        rw [w1]; linear_combination (-w) * e2
      · show G.weight (T.leftUnit 2) = w * c1 * c1
        rw [← hwdef]; linear_combination (-w) * hc1
    · rw [T.flux_grid_of_neg G hT h, hK]
      linear_combination (-(w * T.oppLen 1)) * hc1 - (w * T.oppLen 0) * e2

/-- **The sign of a tile's flux** (Beeson-Zhang, Lemma 5.1 computation): for a placement `T` of the `2 pi/3` tile, with `kg` the vertex of angle `2 pi/3`, the flux of `f_alpha` through `T`
is the weight of the left-hand direction of the `c`-edge (the edge `kg + 1`, opposite `kg`) times `c + a - b`.  Both orientations. -/
theorem Tri.flux_cedge (T : Tri) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.TwoPiThreeData α a b c) (kg : Fin 3) (hkg : T.angleAt kg = 2 * Real.pi / 3) :
    T.flux (fAlpha α hα).weight = (fAlpha α hα).weight (T.leftUnit (kg + 1)) * (c + a - b) := by
  obtain ⟨s, hw, hf⟩ := T.weight_form (fAlpha α hα) (GridChar.rankn_sq _ _ _ _ _ _ _) (T.data_angles_mem hα h 0)
  have hk : kg + 1 + 2 = kg := by fin_cases kg <;> rfl
  have hchi : (fAlpha α hα).chi ((Real.pi - 2 * Real.pi / 3 : ℝ) : Real.Angle) = -1 := by
    unfold fAlpha
    rw [show Real.pi - 2 * Real.pi / 3 = ((1 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((0 : ℤ) : ℝ) * α by
      push_cast; ring, GridChar.rankn_chi]
    simp
  have h1 := hw (kg + 1)
  rw [hk, hkg, hchi] at h1
  rw [h1, hf, data_tileValue_alpha T hα h]
  ring

/-- For a placement of the tile, every vertex carries one of the three angles together with the opposite side. -/
theorem Tri.TwoPiThreeData.cases {T : Tri} {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) (k : Fin 3) :
    (T.angleAt k = 2 * Real.pi / 3 ∧ T.oppLen k = c) ∨ (T.angleAt k = α ∧ T.oppLen k = a) ∨
      (T.angleAt k = Real.pi / 3 - α ∧ T.oppLen k = b) := by
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  obtain ⟨j, rfl⟩ := σ.surjective k
  fin_cases j
  · exact Or.inr (Or.inl ⟨h0, o0⟩)
  · exact Or.inr (Or.inr ⟨h1, o1⟩)
  · exact Or.inl ⟨h2, o2⟩

/-- Congruent triangles are placements of the same data. -/
theorem Tri.TwoPiThreeData.of_congruent {T U : Tri} (hc : T.Congruent U) {α a b c : ℝ} (h : U.TwoPiThreeData α a b c) :
    T.TwoPiThreeData α a b c := by
  obtain ⟨σ, hσ⟩ := hc.exists_perm
  obtain ⟨τ, h0, o0, h1, o1, h2, o2⟩ := h
  refine ⟨τ.trans σ.symm, ?_⟩
  simp only [Equiv.trans_apply]
  have e : ∀ j, T.angleAt (σ.symm (τ j)) = U.angleAt (τ j) ∧ T.oppLen (σ.symm (τ j)) = U.oppLen (τ j) := by
    intro j
    have := hσ (σ.symm (τ j))
    rw [Equiv.apply_symm_apply] at this
    exact this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(e 0).1, h0]
  · rw [(e 0).2, o0]
  · rw [(e 1).1, h1]
  · rw [(e 1).2, o1]
  · rw [(e 2).1, h2]
  · rw [(e 2).2, o2]

/-- The angles of a placement lie strictly between `0` and `π/3` for `α, β`. -/
theorem Tri.TwoPiThreeData.alpha_range {T : Tri} {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
    0 < α ∧ α < Real.pi / 3 := by
  obtain ⟨σ, h0, -, h1, -, -, -⟩ := h
  have p0 := T.angleAt_pos'' (σ 0)
  have p1 := T.angleAt_pos'' (σ 1)
  rw [h0] at p0
  rw [h1] at p1
  exact ⟨p0, by linarith⟩

/-- Exactly one vertex has angle `2π/3`. -/
theorem Tri.TwoPiThreeData.gamma_unique {T : Tri} {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
    ∃ kg : Fin 3, T.angleAt kg = 2 * Real.pi / 3 ∧ ∀ k, T.angleAt k = 2 * Real.pi / 3 → k = kg := by
  have hr := h.alpha_range
  have hpi := Real.pi_pos
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  refine ⟨σ 2, h2, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ := σ.surjective k
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
  rcases hj with rfl | rfl | rfl
  · exfalso; rw [h0] at hk; linarith [hr.1, hr.2]
  · exfalso; rw [h1] at hk; linarith [hr.1, hr.2]
  · rfl

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Tri.weight_form
#print axioms Erdos634.Geometry.Tri.flux_cedge
#print axioms Erdos634.Geometry.Tri.TwoPiThreeData.gamma_unique
