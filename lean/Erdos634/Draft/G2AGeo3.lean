/-
Draft/G2AGeo3.lean — `Row4.L8_nob`: if NEITHER leg of the `γ = 2α` base-α target contains a `b`-edge, contradiction.
Each leg's edge at the apex presents `β` there (`Row4.leg_beta_apex`); at most one tile presents `β` at the apex
(`Row4.corner_B`), so one tile `T` has an edge on each leg, both ending at the apex `B`; then the tile angle at `B`,
which is the angle between the two legs, equals `π − 2α`, but a tile presenting `β` there has angle `π − 3α`.
This replaces `Row4.L8_ac` (which needed legs of exactly two edges `{a, c}`).  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.G2AGeo2

open scoped Classical

namespace Erdos634.Geometry

variable {N : ℕ}

/-- A point of a segment `[B, A]` other than `B` lies on a ray from `B` through `A`. -/
theorem seg_dir {B A p : Plane} (hp : p ∈ segment ℝ B A) (hpB : p ≠ B) :
    ∃ s : ℝ, 0 < s ∧ p -ᵥ B = s • (A -ᵥ B) := by
  rw [segment_eq_image'] at hp
  obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hp
  have hθ : θ ≠ 0 := by
    rintro rfl
    exact hpB (by simp)
  refine ⟨θ, lt_of_le_of_ne h0 (Ne.symm hθ), ?_⟩
  simp [vsub_eq_sub]

/-- **The angle between two sub-rays.**  If `p ∈ [B, A] \ {B}` and `q ∈ [B, C] \ {B}`, `∠ p B q = ∠ A B C`. -/
theorem angle_of_subsegments {B A C p q : Plane} (hp : p ∈ segment ℝ B A) (hpB : p ≠ B)
    (hq : q ∈ segment ℝ B C) (hqB : q ≠ B) :
    cornerAngle p B q = cornerAngle A B C := by
  obtain ⟨s, hs, hps⟩ := seg_dir hp hpB
  obtain ⟨t, ht, hqt⟩ := seg_dir hq hqB
  unfold cornerAngle EuclideanGeometry.angle
  rw [hps, hqt, InnerProductGeometry.angle_smul_left_of_pos _ _ hs,
    InnerProductGeometry.angle_smul_right_of_pos _ _ ht]

theorem Row4.L8_nob (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    (hA : D.target.angleAt 0 = α) (hC : D.target.angleAt 1 = α)
    (hAB : ∀ e ∈ D.sideEdges 2, D.eLen e ≠ b) (hCB : ∀ e ∈ D.sideEdges 1, D.eLen e ≠ b) : False := by
  obtain ⟨hα0, hα3, -⟩ := Row4.model_sides D h
  have hB : D.target.angleAt 2 = Real.pi - 2 * α := by
    have := D.target.angleAt_sum; rw [hA, hC] at this; linarith
  have hP0 := fun i => Row4.corner_A D hα h hα0 hα3 hA i
  have hP1 := fun i => Row4.corner_A D hα h hα0 hα3 hC i
  obtain ⟨hBγ, hBβ⟩ := Row4.corner_B D hα h hα0 hα3 hB
  have hne : ∀ i j : Fin 3, i ≠ j → D.target.pts i ≠ D.target.pts j := fun i j hij e =>
    hij (D.target.indep.injective e)
  have hsAB : D.target.edge 2 = segment ℝ (D.target.pts 0) (D.target.pts 2) := by
    show segment ℝ (D.target.pts 2) (D.target.pts (2 + 1)) = _
    rw [show (2 : Fin 3) + 1 = 0 from rfl, segment_symm]
  have hsCB : D.target.edge 1 = segment ℝ (D.target.pts 1) (D.target.pts 2) := rfl
  have hendsAB : ∀ v, D.target.pts v ∈ segment ℝ (D.target.pts 0) (D.target.pts 2) →
      D.target.pts v = D.target.pts 0 ∨ D.target.pts v = D.target.pts 2 := by
    intro v hv
    have h3 : v = 0 ∨ v = 1 ∨ v = 2 := by fin_cases v <;> simp
    rcases h3 with rfl | rfl | rfl
    · exact Or.inl rfl
    · rw [segment_symm] at hv
      exact absurd hv (Row4.third_not_on_side D.target 2)
    · exact Or.inr rfl
  have hendsCB : ∀ v, D.target.pts v ∈ segment ℝ (D.target.pts 1) (D.target.pts 2) →
      D.target.pts v = D.target.pts 1 ∨ D.target.pts v = D.target.pts 2 := by
    intro v hv
    have h3 : v = 0 ∨ v = 1 ∨ v = 2 := by fin_cases v <;> simp
    rcases h3 with rfl | rfl | rfl
    · exact absurd hv (Row4.third_not_on_side D.target 1)
    · exact Or.inl rfl
    · exact Or.inr rfl
  obtain ⟨e₁, he₁, hβ₁, m₁, hm₁, hm₁B⟩ := Row4.leg_beta_apex D hα h (hne 0 2 (by decide)) hsAB hendsAB
    (fun i => (hP0 i).1) hAB
  obtain ⟨e₂, he₂, hβ₂, m₂, hm₂, hm₂B⟩ := Row4.leg_beta_apex D hα h (hne 1 2 (by decide)) hsCB hendsCB
    (fun i => (hP1 i).1) hCB
  have ht : e₁.1 = e₂.1 := hBβ e₁.1 e₂.1 hβ₁ hβ₂
  have hne12 : e₁ ≠ e₂ := fun e => by
    have h1 : e₁ ∈ D.sideEdges 2 := he₁
    have h2 : e₁ ∈ D.sideEdges 1 := by rw [e]; exact he₂
    exact Finset.disjoint_left.mp (D.toDissection.sideEdges_disjoint (by decide : (2 : Fin 3) ≠ 1)) h1 h2
  have hk : e₁.2 ≠ e₂.2 := fun e => hne12 (Prod.ext ht e)
  -- the vertex of the tile at the apex
  set T := D.tile e₁.1 with hT
  have hm₂B' : T.pts m₂ = D.target.pts 2 := by rw [hT, ht]; exact hm₂B
  have hmm : m₁ = m₂ := T.indep.injective (hm₁B.trans hm₂B'.symm)
  subst hmm
  -- the other endpoints of the two edges
  have hseg1 : ∀ n : Fin 3, (n = e₁.2 ∨ n = e₁.2 + 1) → T.pts n ∈ segment ℝ (D.target.pts 0) (D.target.pts 2) := by
    intro n hn
    have hsub : D.eSet e₁ ⊆ segment ℝ (D.target.pts 0) (D.target.pts 2) := by
      rw [← hsAB]
      have h1 : e₁ ∈ D.sideEdges 2 := he₁
      unfold Dissection.sideEdges at h1
      exact (Finset.mem_filter.mp h1).2
    apply hsub
    rcases hn with rfl | rfl
    · exact left_mem_segment ℝ _ _
    · exact right_mem_segment ℝ _ _
  have hseg2 : ∀ n : Fin 3, (n = e₂.2 ∨ n = e₂.2 + 1) → (D.tile e₂.1).pts n ∈ segment ℝ (D.target.pts 1) (D.target.pts 2) := by
    intro n hn
    have hsub : D.eSet e₂ ⊆ segment ℝ (D.target.pts 1) (D.target.pts 2) := by
      rw [← hsCB]
      have h1 : e₂ ∈ D.sideEdges 1 := he₂
      unfold Dissection.sideEdges at h1
      exact (Finset.mem_filter.mp h1).2
    apply hsub
    rcases hn with rfl | rfl
    · exact left_mem_segment ℝ _ _
    · exact right_mem_segment ℝ _ _
  -- indices: m is the apex vertex; n₁, n₂ the other endpoints
  have hidx : ∀ m k₁ k₂ : Fin 3, k₁ ≠ k₂ → (m = k₁ ∨ m = k₁ + 1) → (m = k₂ ∨ m = k₂ + 1) →
      ∃ n₁ n₂ : Fin 3, (n₁ = k₁ ∨ n₁ = k₁ + 1) ∧ (n₂ = k₂ ∨ n₂ = k₂ + 1) ∧ n₁ ≠ m ∧ n₂ ≠ m ∧
        ((n₁ = m + 1 ∧ n₂ = m + 2) ∨ (n₁ = m + 2 ∧ n₂ = m + 1)) := by
    decide
  obtain ⟨n₁, n₂, hn₁, hn₂, hn₁m, hn₂m, hcase⟩ := hidx m₁ e₁.2 e₂.2 hk hm₁ hm₂
  have hp1 : T.pts n₁ ∈ segment ℝ (D.target.pts 2) (D.target.pts 0) := by
    rw [segment_symm]; exact hseg1 n₁ hn₁
  have hq2 : T.pts n₂ ∈ segment ℝ (D.target.pts 2) (D.target.pts 1) := by
    rw [segment_symm, hT, ht]; exact hseg2 n₂ hn₂
  have hp1B : T.pts n₁ ≠ D.target.pts 2 := fun e => hn₁m (T.indep.injective (e.trans hm₁B.symm))
  have hq2B : T.pts n₂ ≠ D.target.pts 2 := fun e => hn₂m (T.indep.injective (e.trans hm₁B.symm))
  have hang : cornerAngle (T.pts (m₁ + 1)) (T.pts m₁) (T.pts (m₁ + 2)) = Real.pi - 3 * α := by
    rw [← T.localAngle_vertex m₁, hm₁B]; exact hβ₁
  have hAng : cornerAngle (T.pts n₁) (D.target.pts 2) (T.pts n₂) = Real.pi - 2 * α := by
    rw [angle_of_subsegments hp1 hp1B hq2 hq2B]
    rw [← hB]; rfl
  have hcomm : ∀ p q r : Plane, cornerAngle p q r = cornerAngle r q p :=
    fun p q r => EuclideanGeometry.angle_comm (V := Plane) p q r
  have hmain : cornerAngle (T.pts (m₁ + 1)) (T.pts m₁) (T.pts (m₁ + 2)) = Real.pi - 2 * α := by
    rcases hcase with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [← e1, ← e2, hm₁B]; exact hAng
    · rw [← e1, ← e2, hm₁B, hcomm]; exact hAng
  linarith

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row4.L8_nob
