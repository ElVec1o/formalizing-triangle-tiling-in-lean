-- Draft/FluxGRow3Relabel.lean — row 3 (AUDIT_ROWS), Proposition RP, general N: the per-tile
-- normal form. Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- Formalization debt on an already paper-level-PROVED result (row3 PROOF.md, Prop RP). Not /goal
-- progress.
--
-- What this file supplies (all for an ARBITRARY tile of an arbitrary real dissection):
--   (1) `Tri.flux_relabel` — the flux `Tri.flux f` does not depend on the vertex labelling
--       (any of the 6 permutations; orientation-reversing ones flip `det` and the `leftDir`s
--       re-index, both handled).
--   (2) `Tri.Congruent.exists_normal` — a tile congruent to `U` has a relabelling whose angles and
--       opposite sides are literally `U`'s, vertex by vertex.
--   (3) `rightTile_flux_value` — for a tile with the right tile's normal-form angles/sides
--       (`β` at 1, `π/2` at 2, sides `(sin α, cos α, 1)`), its Gaussian flux at every grid degree is
--       `Step6.tileVal` — including the OFF-GRID case (hypotenuse direction not in `θ₀ + ℤα + ℤπ/2`),
--       where the value is `0` (row3 PROOF.md Step 3, last bullet). So NO grid placement of the
--       tiles is needed: the previously-named "every tile's hypotenuse is on the grid" item (P97) is
--       not a prerequisite of Prop RP.
import Erdos634.Congruence
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Erdos634.Draft.FluxGRow3Cancel
import Erdos634.Draft.FluxGRow3Step6Alg

open scoped Classical

namespace Erdos634.Geometry.Row3

open Real Erdos634.Geometry

/-! ## (1) Flux is independent of the labelling -/

theorem fin3_perm_shape : ∀ x y z : Fin 3, x ≠ y → x ≠ z → y ≠ z →
    (y = x + 1 ∧ z = x + 2) ∨ (y = x - 1 ∧ z = x - 2) := by decide

theorem perm3_rot_or_rev (τ : Equiv.Perm (Fin 3)) :
    (∀ k, τ k = τ 0 + k) ∨ (∀ k, τ k = τ 0 - k) := by
  have h01 : τ 0 ≠ τ 1 := fun h => absurd (τ.injective h) (by decide)
  have h02 : τ 0 ≠ τ 2 := fun h => absurd (τ.injective h) (by decide)
  have h12 : τ 1 ≠ τ 2 := fun h => absurd (τ.injective h) (by decide)
  rcases fin3_perm_shape _ _ _ h01 h02 h12 with ⟨a, b⟩ | ⟨a, b⟩
  · left; intro k; fin_cases k
    · simp
    · simpa using a
    · simpa using b
  · right; intro k; fin_cases k
    · simp
    · simpa using a
    · simpa using b

theorem cross_swap (u v : Plane) : cross v u = - cross u v := by
  simp only [cross]; ring

theorem Tri.flux_relabel {E : Type*} [AddCommGroup E] [Module ℝ E] (T : Tri)
    (τ : Equiv.Perm (Fin 3)) (f : Dir → E) : (T.relabel τ).flux f = T.flux f := by
  set r := τ 0 with hr
  rcases perm3_rot_or_rev τ with hA | hB
  · have hpts : ∀ k, (T.relabel τ).pts k = T.pts (r + k) := fun k => by
      rw [Tri.relabel_pts, hA]
    have hdet : (T.relabel τ).det = T.det := by
      have h := T.det_cyclic r
      show cross ((T.relabel τ).pts 1 - (T.relabel τ).pts 0)
        ((T.relabel τ).pts 2 - (T.relabel τ).pts 0) = _
      rw [hpts, hpts, hpts, add_zero, ← h]
    have hleft : ∀ k, (T.relabel τ).leftDir k = T.leftDir (r + k) := fun k => by
      unfold Tri.leftDir
      rw [hdet, hpts, hpts, add_assoc]
    have hunit : ∀ k, (T.relabel τ).leftUnit k = T.leftUnit (r + k) := fun k => by
      apply Subtype.ext
      show ‖(T.relabel τ).leftDir k‖⁻¹ • (T.relabel τ).leftDir k
        = ‖T.leftDir (r + k)‖⁻¹ • T.leftDir (r + k)
      rw [hleft]
    unfold Tri.flux
    have hterm : ∀ k, dist ((T.relabel τ).pts k) ((T.relabel τ).pts (k + 1))
        • f ((T.relabel τ).leftUnit k)
        = (fun m => dist (T.pts m) (T.pts (m + 1)) • f (T.leftUnit m)) (Equiv.addLeft r k) := by
      intro k
      simp only [Equiv.coe_addLeft, hpts, hunit, add_assoc]
    rw [Finset.sum_congr rfl (fun k _ => hterm k)]
    exact Equiv.sum_comp (Equiv.addLeft r) (fun m => dist (T.pts m) (T.pts (m + 1)) • f (T.leftUnit m))
  · have hpts : ∀ k, (T.relabel τ).pts k = T.pts (r - k) := fun k => by
      rw [Tri.relabel_pts, hB]
    have hdet : (T.relabel τ).det = - T.det := by
      have h := T.det_cyclic r
      show cross ((T.relabel τ).pts 1 - (T.relabel τ).pts 0)
        ((T.relabel τ).pts 2 - (T.relabel τ).pts 0) = _
      rw [hpts, hpts, hpts, sub_zero, ← h, cross_swap]
      have e1 : r - 1 = r + 2 := (by decide : ∀ s : Fin 3, s - 1 = s + 2) r
      have e2 : r - 2 = r + 1 := (by decide : ∀ s : Fin 3, s - 2 = s + 1) r
      rw [e1, e2]
    have hleft : ∀ k, (T.relabel τ).leftDir k = T.leftDir (r - k - 1) := fun k => by
      have e : r - k - 1 + 1 = r - k := (by decide : ∀ a b : Fin 3, a - b - 1 + 1 = a - b) r k
      have e' : r - (k + 1) = r - k - 1 := (by decide : ∀ a b : Fin 3, a - (b + 1) = a - b - 1) r k
      unfold Tri.leftDir
      rw [hdet, hpts, hpts, e', e]
      rcases lt_or_gt_of_ne T.det_ne_zero with hneg | hpos
      · rw [if_pos (by linarith), if_neg (by linarith)]
      · rw [if_neg (by linarith), if_pos hpos]
    have hunit : ∀ k, (T.relabel τ).leftUnit k = T.leftUnit (r - k - 1) := fun k => by
      apply Subtype.ext
      show ‖(T.relabel τ).leftDir k‖⁻¹ • (T.relabel τ).leftDir k
        = ‖T.leftDir (r - k - 1)‖⁻¹ • T.leftDir (r - k - 1)
      rw [hleft]
    unfold Tri.flux
    have hterm : ∀ k, dist ((T.relabel τ).pts k) ((T.relabel τ).pts (k + 1))
        • f ((T.relabel τ).leftUnit k)
        = (fun m => dist (T.pts m) (T.pts (m + 1)) • f (T.leftUnit m))
            (Equiv.subLeft (r - 1) k) := by
      intro k
      have e : r - 1 - k = r - k - 1 := (by decide : ∀ a b : Fin 3, a - 1 - b = a - b - 1) r k
      have e' : r - (k + 1) = r - k - 1 := (by decide : ∀ a b : Fin 3, a - (b + 1) = a - b - 1) r k
      have e'' : r - k - 1 + 1 = r - k := (by decide : ∀ a b : Fin 3, a - b - 1 + 1 = a - b) r k
      simp only [Equiv.subLeft_apply, hpts, hunit, e, e', e'']
      rw [dist_comm]
    rw [Finset.sum_congr rfl (fun k _ => hterm k)]
    exact Equiv.sum_comp (Equiv.subLeft (r - 1)) (fun m => dist (T.pts m) (T.pts (m + 1)) • f (T.leftUnit m))

/-! ## (2) Congruent tiles have a normal-form relabelling -/

theorem angle_oppLen_of_isometry {T U : Tri} (f : Plane ≃ᵢ Plane)
    (hf : ∀ k, f (T.pts k) = U.pts k) (k : Fin 3) :
    T.angleAt k = U.angleAt k ∧ T.oppLen k = U.oppLen k := by
  constructor
  · unfold Tri.angleAt cornerAngle
    rw [← hf, ← hf, ← hf]
    rw [show (f : Plane → Plane) = f.toRealAffineIsometryEquiv from
      (IsometryEquiv.coeFn_toRealAffineIsometryEquiv f).symm]
    exact (f.toRealAffineIsometryEquiv.toAffineIsometry.angle_map _ _ _).symm
  · unfold Tri.oppLen
    rw [← hf, ← hf, f.dist_eq]

theorem Tri.Congruent.exists_normal {T U : Tri} (h : T.Congruent U) :
    ∃ τ : Equiv.Perm (Fin 3), ∀ k,
      (T.relabel τ).angleAt k = U.angleAt k ∧ (T.relabel τ).oppLen k = U.oppLen k := by
  obtain ⟨f, σ, hf⟩ := h
  refine ⟨σ.symm, angle_oppLen_of_isometry f (fun k => ?_)⟩
  rw [Tri.relabel_pts, hf, Equiv.apply_symm_apply]

/-! ## (3) The value of one normal-form right tile, on or off the grid -/

theorem isGridA_of_eq_add {α θ₀ : ℝ} {θ θ' : Real.Angle} (p q : ℤ)
    (h : θ' = θ + (((p : ℝ) * α + (q : ℝ) * (Real.pi / 2) : ℝ) : Real.Angle))
    (hg : IsGridA α θ₀ θ') : IsGridA α θ₀ θ := by
  obtain ⟨k, j, hk⟩ := hg
  refine ⟨k - p, j - q, ?_⟩
  have e : θ = θ' - (((p : ℝ) * α + (q : ℝ) * (Real.pi / 2) : ℝ) : Real.Angle) := by
    rw [h]; abel
  rw [e, hk, ← Real.Angle.coe_sub]
  congr 1; push_cast; ring

theorem isGridA_of_eq_add' {α θ₀ : ℝ} {θ θ' : Real.Angle} (p q : ℤ)
    (h : θ' = θ + (((p : ℝ) * α + (q : ℝ) * (Real.pi / 2) : ℝ) : Real.Angle))
    (hg : IsGridA α θ₀ θ) : IsGridA α θ₀ θ' := by
  rw [h]; exact isGridA_add_shift hg p q

theorem gaussWeight_offGrid {α θ₀ : ℝ} (X : ℤ) (d : Dir) (h : ¬ IsGridA α θ₀ d.angle) :
    gaussWeight α θ₀ X d = 0 := by
  unfold gaussWeight gaussWeightA; rw [dif_neg h]

/-- If the hypotenuse direction `leftUnit 0` is off the grid, so are the two legs. -/
theorem legs_offGrid {α θ₀ : ℝ} (T : Tri)
    (hβ : T.angleAt 1 = Real.pi / 2 - α) (hγ : T.angleAt 2 = Real.pi / 2)
    (h0 : ¬ IsGridA α θ₀ (T.leftUnit 0).angle) :
    ¬ IsGridA α θ₀ (T.leftUnit 1).angle ∧ ¬ IsGridA α θ₀ (T.leftUnit 2).angle := by
  have c1 : ((Real.pi - (Real.pi / 2 - α) : ℝ) : Real.Angle)
      = ((((1 : ℤ) : ℝ) * α + ((1 : ℤ) : ℝ) * (Real.pi / 2) : ℝ) : Real.Angle) := by
    congr 1; push_cast; ring
  have c2 : ((Real.pi - Real.pi / 2 : ℝ) : Real.Angle)
      = ((((0 : ℤ) : ℝ) * α + ((1 : ℤ) : ℝ) * (Real.pi / 2) : ℝ) : Real.Angle) := by
    congr 1; push_cast; ring
  rcases lt_or_gt_of_ne T.det_ne_zero with hneg | hpos
  · have t0 := T.leftUnit_turn_of_neg hneg 0
    have t1 := T.leftUnit_turn_of_neg hneg 1
    simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (1 : Fin 3) + 1 = 2 from rfl] at t0 t1
    rw [hβ, c1] at t0
    rw [hγ, c2] at t1
    have g1 : ¬ IsGridA α θ₀ (T.leftUnit 1).angle := fun h => h0 (isGridA_of_eq_add' _ _ t0 h)
    exact ⟨g1, fun h => g1 (isGridA_of_eq_add' _ _ t1 h)⟩
  · have t0 := T.leftUnit_turn_of_pos hpos 0
    have t1 := T.leftUnit_turn_of_pos hpos 1
    simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (1 : Fin 3) + 1 = 2 from rfl] at t0 t1
    rw [hβ, c1] at t0
    rw [hγ, c2] at t1
    have g1 : ¬ IsGridA α θ₀ (T.leftUnit 1).angle := fun h => h0 (isGridA_of_eq_add _ _ t0 h)
    exact ⟨g1, fun h => g1 (isGridA_of_eq_add _ _ t1 h)⟩

/-- **One tile's Gaussian flux = `Step6.tileVal`**, for any tile in right-tile normal form
(`β = π/2 − α` at vertex 1, `π/2` at vertex 2, opposite sides `(sin α, cos α, 1)`), with no grid
hypothesis: the off-grid case is value `0`. -/
theorem rightTile_flux_value {α θ₀ : ℝ} (hα : Irrational (α / Real.pi)) (T : Tri)
    (hβ : T.angleAt 1 = Real.pi / 2 - α) (hγ : T.angleAt 2 = Real.pi / 2)
    (ha : T.oppLen 0 = Real.sin α) (hb : T.oppLen 1 = Real.cos α) (hc : T.oppLen 2 = 1)
    (X : ℤ) :
    T.flux (gaussWeight α θ₀ X)
      = Step6.tileVal α (IsGridA α θ₀ (T.leftUnit 0).angle) (T.det < 0)
          (gridK α θ₀ (T.leftUnit 0).angle) (gridJ α θ₀ (T.leftUnit 0).angle) X := by
  unfold Step6.tileVal
  by_cases hg : IsGridA α θ₀ (T.leftUnit 0).angle
  · rw [if_pos hg]
    rcases lt_or_gt_of_ne T.det_ne_zero with hneg | hpos
    · rw [if_pos hneg, Tri.flux_gauss_reflected T hα hneg hβ hγ hg X, ha, hb, hc]
      unfold Step6.vv; push_cast; ring
    · rw [if_neg (by linarith), Tri.flux_gauss_direct T hα hpos hβ hγ hg X, ha, hb, hc]
      unfold Step6.uu; push_cast; ring
  · rw [if_neg hg]
    obtain ⟨g1, g2⟩ := legs_offGrid T hβ hγ hg
    unfold Tri.flux
    rw [Fin.sum_univ_three, gaussWeight_offGrid X _ hg, gaussWeight_offGrid X _ g1,
      gaussWeight_offGrid X _ g2]
    simp

end Erdos634.Geometry.Row3

#print axioms Erdos634.Geometry.Row3.Tri.flux_relabel
#print axioms Erdos634.Geometry.Row3.Tri.Congruent.exists_normal
#print axioms Erdos634.Geometry.Row3.rightTile_flux_value
