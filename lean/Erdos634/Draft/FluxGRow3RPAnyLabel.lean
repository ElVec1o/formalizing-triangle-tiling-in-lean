-- Draft/FluxGRow3RPAnyLabel.lean — row 3 (AUDIT_ROWS), Proposition RP for EVERY labelling.
-- Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- Formalization debt on an already paper-level-PROVED result; not /goal progress; no target of
-- (private working notes, not included) moves. A relabelling wrapper around `Row3.RP.row3_RP_even`
-- (Draft/FluxGRow3RP.lean), which fixes: model angle α at vertex 0 and π/2 at vertex 2; target
-- angles α at vertices 0, 1; `0 < D.target.det`. Here:
--   * the model has angle α at SOME vertex p and π/2 at SOME other vertex q (so its angles are
--     {α, π/2 − α, π/2}); the model is replaced by its relabelling (tiles stay congruent to it);
--   * the target has two equal base angles γ at ANY two distinct vertices i, j, with γ = α OR
--     γ = π/2 − α (the paper's (β, β, π − 2β) case, handled by renaming α ↔ β);
--   * no orientation hypothesis: a negatively oriented target is relabelled by `swap 0 1`.
import Erdos634.Draft.FluxGRow3RP
import Erdos634.Draft.FluxDRow4AnyLabel

open scoped Classical

namespace Erdos634.Geometry.Row3.RP

open Real Erdos634.Geometry

/-- The same dissection with its model replaced by the model relabelled by `τ`. -/
noncomputable def relabelModel {N : ℕ} (D : CongruentDissection N) (τ : Equiv.Perm (Fin 3)) :
    CongruentDissection N :=
  { toDissection := D.toDissection, model := D.model.relabel τ,
    tiles_congruent := fun i => (D.tiles_congruent i).relabel τ }

/-- Angle at a vertex of a relabelled triangle. -/
theorem angleAt_of_pts {T U : Tri} (τ : Equiv.Perm (Fin 3)) (h : ∀ k, U.pts k = T.pts (τ k))
    (k : Fin 3) : U.angleAt k = T.angleAt (τ k) := by
  have key : ∀ a b c : Fin 3, b ≠ a → c ≠ a → b ≠ c →
      cornerAngle (T.pts b) (T.pts a) (T.pts c) = cornerAngle (T.pts (a + 1)) (T.pts a) (T.pts (a + 2)) := by
    intro a b c hba hca hbc
    fin_cases a <;> fin_cases b <;> fin_cases c <;> simp at hba hca hbc ⊢ <;>
      first | rfl | exact EuclideanGeometry.angle_comm (V := Plane) _ _ _
  unfold Tri.angleAt
  rw [h, h, h]
  exact key _ _ _ (fun e => by have := τ.injective e; revert this; fin_cases k <;> decide)
    (fun e => by have := τ.injective e; revert this; fin_cases k <;> decide)
    (fun e => by have := τ.injective e; revert this; fin_cases k <;> decide)

theorem perm_exists : ∀ p q r s : Fin 3, p ≠ q → r ≠ s →
    ∃ τ : Equiv.Perm (Fin 3), τ r = p ∧ τ s = q := by decide

theorem angle_third {T : Tri} {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    T.angleAt p + T.angleAt q + T.angleAt r = Real.pi := by
  have := T.angleAt_sum
  fin_cases p <;> fin_cases q <;> fin_cases r <;> simp at hpq hpr hqr ⊢ <;> linarith

/-- The core: base angle α (the α-case), arbitrary labelling and orientation. -/
theorem row3_RP_even_alpha {N : ℕ} (D : CongruentDissection N) {α : ℝ} (hα0 : 0 < α)
    (hα2 : α < Real.pi / 2) (hirr : Irrational (α / Real.pi))
    {p q : Fin 3} (hpq : p ≠ q) (hmp : D.model.angleAt p = α) (hmq : D.model.angleAt q = Real.pi / 2)
    {i j : Fin 3} (hij : i ≠ j) (hi : D.target.angleAt i = α) (hj : D.target.angleAt j = α) :
    Even N := by
  obtain ⟨τ, hτ0, hτ2⟩ := perm_exists p q 0 2 hpq (by decide)
  obtain ⟨σ, hσ0, hσ1⟩ := perm_exists i j 0 1 hij (by decide)
  set D2 := (relabelModel D τ).relabelTarget' σ with hD2
  have hm0 : D2.model.angleAt 0 = α := by
    rw [angleAt_of_pts (T := D.model) τ (fun k => rfl), hτ0, hmp]
  have hm2 : D2.model.angleAt 2 = Real.pi / 2 := by
    rw [angleAt_of_pts (T := D.model) τ (fun k => rfl), hτ2, hmq]
  have ht0 : D2.target.angleAt 0 = α := by
    rw [angleAt_of_pts (T := D.target) σ (fun k => rfl), hσ0, hi]
  have ht1 : D2.target.angleAt 1 = α := by
    rw [angleAt_of_pts (T := D.target) σ (fun k => rfl), hσ1, hj]
  rcases lt_or_gt_of_ne D2.target.det_ne_zero with hneg | hpos
  · set D3 := D2.relabelTarget' (Equiv.swap 0 1) with hD3
    have e0 : D3.target.angleAt 0 = α := by
      rw [angleAt_of_pts (T := D2.target) (Equiv.swap 0 1) (fun k => rfl)]
      simpa using ht1
    have e1 : D3.target.angleAt 1 = α := by
      rw [angleAt_of_pts (T := D2.target) (Equiv.swap 0 1) (fun k => rfl)]
      simpa using ht0
    have hdet : D3.target.det = - D2.target.det := by
      have p0 : D3.target.pts 0 = D2.target.pts 1 := rfl
      have p1 : D3.target.pts 1 = D2.target.pts 0 := rfl
      have p2 : D3.target.pts 2 = D2.target.pts 2 := rfl
      unfold Tri.det; rw [p0, p1, p2]; simp only [PiLp.sub_apply]; ring
    exact row3_RP_even D3 hα0 hα2 hirr hm0 hm2 e0 e1 (by rw [hdet]; linarith)
  · exact row3_RP_even D2 hα0 hα2 hirr hm0 hm2 ht0 ht1 hpos

/-- **Proposition RP (row 3), any labelling.** Right tile with angles `{α, π/2 − α, π/2}`
(`α` at some vertex `p`, `π/2` at another vertex `q`), `0 < α < π/2`, `α/π ∉ ℚ`; target with equal
angles `γ` at two distinct vertices, `γ = α` or `γ = π/2 − α` (i.e. target angles `(α, α, π−2α)`
or `(β, β, π−2β)`, `β = π/2 − α`). Then `N` is even. -/
theorem row3_RP_even_any_label {N : ℕ} (D : CongruentDissection N) {α : ℝ} (hα0 : 0 < α)
    (hα2 : α < Real.pi / 2) (hirr : Irrational (α / Real.pi))
    {p q : Fin 3} (hpq : p ≠ q) (hmp : D.model.angleAt p = α) (hmq : D.model.angleAt q = Real.pi / 2)
    {γ : ℝ} (hγ : γ = α ∨ γ = Real.pi / 2 - α)
    {i j : Fin 3} (hij : i ≠ j) (hi : D.target.angleAt i = γ) (hj : D.target.angleAt j = γ) :
    Even N := by
  rcases hγ with hγ | hγ <;> subst hγ
  · exact row3_RP_even_alpha D hα0 hα2 hirr hpq hmp hmq hij hi hj
  · -- the β-case: rename α ↔ β = π/2 − α; β sits at the third model vertex r
    obtain ⟨r, hrp, hrq⟩ : ∃ r : Fin 3, p ≠ r ∧ q ≠ r := by
      fin_cases p <;> fin_cases q <;> simp at hpq ⊢ <;> decide
    have hmr : D.model.angleAt r = Real.pi / 2 - α := by
      have := angle_third (T := D.model) hpq hrp hrq; linarith
    have hirr' : Irrational ((Real.pi / 2 - α) / Real.pi) := by
      have h : (Real.pi / 2 - α) / Real.pi = ((1 / 2 : ℚ) : ℝ) - α / Real.pi := by
        field_simp; push_cast; ring
      rw [h]; exact irrational_ratCast_sub_iff.mpr hirr
    have hβ0 : 0 < Real.pi / 2 - α := by linarith
    have hβ2 : Real.pi / 2 - α < Real.pi / 2 := by linarith
    exact row3_RP_even_alpha D hβ0 hβ2 hirr' (Ne.symm hrq) hmr hmq hij hi hj

/-! ## RP's first conclusion, `N = 2λ²` with `λ = AB/c`, any labelling -/

/-- Side opposite a vertex of a relabelled triangle. -/
theorem oppLen_of_pts {T U : Tri} (τ : Equiv.Perm (Fin 3)) (h : ∀ k, U.pts k = T.pts (τ k))
    (k : Fin 3) : U.oppLen k = T.oppLen (τ k) := by
  have key : ∀ a b c : Fin 3, b ≠ a → c ≠ a → b ≠ c →
      dist (T.pts b) (T.pts c) = dist (T.pts (a + 1)) (T.pts (a + 2)) := by
    intro a b c hba hca hbc
    fin_cases a <;> fin_cases b <;> fin_cases c <;> simp at hba hca hbc ⊢ <;>
      first | rfl | exact dist_comm _ _
  unfold Tri.oppLen
  rw [h, h]
  exact key (τ k) _ _ (fun e => by have := τ.injective e; revert this; fin_cases k <;> decide)
    (fun e => by have := τ.injective e; revert this; fin_cases k <;> decide)
    (fun e => by have := τ.injective e; revert this; fin_cases k <;> decide)

/-- Step 1 of RP in normal position (angles only; no orientation needed). -/
theorem area_normal {N : ℕ} (D : CongruentDissection N) {α : ℝ} (hα0 : 0 < α)
    (hα2 : α < Real.pi / 2) (hm0 : D.model.angleAt 0 = α) (hm2 : D.model.angleAt 2 = Real.pi / 2)
    (ht0 : D.target.angleAt 0 = α) (ht1 : D.target.angleAt 1 = α) :
    (N : ℝ) = 2 * (D.target.oppLen 1 / D.model.oppLen 2) ^ 2 := by
  set c := D.model.oppLen 2 with hc
  have hc0 : 0 < c := oppLen_pos _ _
  obtain ⟨hmb, _⟩ := right_sides D.model hm2
  rw [hm0] at hmb
  obtain ⟨_, te2⟩ := iso_sides D.target hα0 hα2 ht0 ht1
  set L := D.target.oppLen 1 with hL
  set lam := L / c with hlam
  have hLc : L = lam * c := by rw [hlam]; field_simp
  have h := abs_det_target D
  rw [abs_det_eq, abs_det_eq, ht0, hm0, te2, hmb, ← hL, ← hc] at h
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith [Real.pi_pos])
  have hco : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith, hα2⟩
  have hk : (2 * lam ^ 2 - N) * (c ^ 2 * Real.cos α * Real.sin α) = 0 := by
    rw [hLc] at h; linear_combination h
  have := (mul_eq_zero.mp hk).resolve_right (by positivity)
  linarith

theorem row3_RP_area_alpha {N : ℕ} (D : CongruentDissection N) {α : ℝ} (hα0 : 0 < α)
    (hα2 : α < Real.pi / 2)
    {p q : Fin 3} (hpq : p ≠ q) (hmp : D.model.angleAt p = α) (hmq : D.model.angleAt q = Real.pi / 2)
    {i j : Fin 3} (hij : i ≠ j) (hi : D.target.angleAt i = α) (hj : D.target.angleAt j = α) :
    (N : ℝ) = 2 * (D.target.oppLen j / D.model.oppLen q) ^ 2 := by
  obtain ⟨τ, hτ0, hτ2⟩ := perm_exists p q 0 2 hpq (by decide)
  obtain ⟨σ, hσ0, hσ1⟩ := perm_exists i j 0 1 hij (by decide)
  set D2 := (relabelModel D τ).relabelTarget' σ with hD2
  have hm0 : D2.model.angleAt 0 = α := by
    rw [angleAt_of_pts (T := D.model) τ (fun k => rfl), hτ0, hmp]
  have hm2 : D2.model.angleAt 2 = Real.pi / 2 := by
    rw [angleAt_of_pts (T := D.model) τ (fun k => rfl), hτ2, hmq]
  have ht0 : D2.target.angleAt 0 = α := by
    rw [angleAt_of_pts (T := D.target) σ (fun k => rfl), hσ0, hi]
  have ht1 : D2.target.angleAt 1 = α := by
    rw [angleAt_of_pts (T := D.target) σ (fun k => rfl), hσ1, hj]
  have h := area_normal D2 hα0 hα2 hm0 hm2 ht0 ht1
  have e1 : D2.target.oppLen 1 = D.target.oppLen j := by
    rw [oppLen_of_pts (T := D.target) (U := D2.target) σ (fun k => rfl), hσ1]
  have e2 : D2.model.oppLen 2 = D.model.oppLen q := by
    rw [oppLen_of_pts (T := D.model) (U := D2.model) τ (fun k => rfl), hτ2]
  rwa [e1, e2] at h

/-- **RP, first conclusion, any labelling**: `N = 2λ²`, `λ = AB/c`, where `AB` is an equal side of
the isosceles target (the side opposite a base vertex `j`) and `c` the tile's hypotenuse (the side
opposite the right-angle vertex `q`). Same hypotheses as `row3_RP_even_any_label` minus
irrationality (Step 1 is pure area). -/
theorem row3_RP_area_any_label {N : ℕ} (D : CongruentDissection N) {α : ℝ} (hα0 : 0 < α)
    (hα2 : α < Real.pi / 2)
    {p q : Fin 3} (hpq : p ≠ q) (hmp : D.model.angleAt p = α) (hmq : D.model.angleAt q = Real.pi / 2)
    {γ : ℝ} (hγ : γ = α ∨ γ = Real.pi / 2 - α)
    {i j : Fin 3} (hij : i ≠ j) (hi : D.target.angleAt i = γ) (hj : D.target.angleAt j = γ) :
    (N : ℝ) = 2 * (D.target.oppLen j / D.model.oppLen q) ^ 2 := by
  rcases hγ with hγ | hγ <;> subst hγ
  · exact row3_RP_area_alpha D hα0 hα2 hpq hmp hmq hij hi hj
  · obtain ⟨r, hrp, hrq⟩ : ∃ r : Fin 3, p ≠ r ∧ q ≠ r := by
      fin_cases p <;> fin_cases q <;> simp at hpq ⊢ <;> decide
    have hmr : D.model.angleAt r = Real.pi / 2 - α := by
      have := angle_third (T := D.model) hpq hrp hrq; linarith
    exact row3_RP_area_alpha D (by linarith) (by linarith) (Ne.symm hrq) hmr hmq hij hi hj

end Erdos634.Geometry.Row3.RP

#print axioms Erdos634.Geometry.Row3.RP.row3_RP_even_any_label
#print axioms Erdos634.Geometry.Row3.RP.row3_RP_area_any_label
