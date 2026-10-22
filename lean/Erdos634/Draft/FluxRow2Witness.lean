-- Draft/FluxRow2Witness.lean — NON-VACUITY WITNESS for `Row2.lemmaW` (Draft/FluxRow2.lean).
-- Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).  Design: (private working notes, not included) §5 (row "row 2").
--
-- `D2`: `Subdivision.ladderDissection` of the doubled `(2,3,4)·8` model tile of the 44-tiling
-- (`N = 4`, target = `2·model` by the homothety at vertex 0).  `hsim` holds with `μ = 2`
-- (`homothety_angle_opp`), and `π ∉ 2Λ` for `Λ = ⟨β, γ, π⟩ = ℤπ + ℤθ` (`θ = α/2 + π/2 ∉ ℚπ`,
-- from `FluxGridWitness`).  Lemma W then returns `μ = 2 = S` with `S ≡ 4 (mod 2)`.
-- (The design proposed the (2,3,4) triangle with its own coordinates; the 44-model is the same tile
-- up to scale and already carries the angle facts.)
import Erdos634.Draft.FluxRow2
import Erdos634.Draft.FluxGridWitness
import Erdos634.CellCoord

open scoped Classical

namespace Erdos634.Draft.FluxRow2Witness

open Erdos634.Geometry Erdos634.Tiling44Bridge Erdos634.CertCoord
open Erdos634.Draft.FluxGridWitness Erdos634.Subdivision

/-- A homothety with ratio `r > 0` keeps the angles and scales the sides. -/
theorem homothety_angle_opp (T U : Tri) (c : Plane) (r : ℝ) (hr : 0 < r)
    (h : ∀ i, U.pts i = c + r • (T.pts i - c)) (k : Fin 3) :
    U.angleAt k = T.angleAt k ∧ U.oppLen k = r * T.oppLen k := by
  have hd : ∀ i j, U.pts i - U.pts j = r • (T.pts i - T.pts j) := by
    intro i j; rw [h i, h j, smul_sub, smul_sub, smul_sub]; abel
  refine ⟨?_, ?_⟩
  · unfold Tri.angleAt cornerAngle EuclideanGeometry.angle
    simp only [vsub_eq_sub]
    rw [hd, hd, InnerProductGeometry.angle_smul_left_of_pos _ _ hr,
      InnerProductGeometry.angle_smul_right_of_pos _ _ hr]
  · unfold Tri.oppLen
    rw [dist_eq_norm, dist_eq_norm, hd, norm_smul, Real.norm_eq_abs, abs_of_pos hr]

/-- The model's vertices, as a vector. -/
theorem hpts : (![M44.pts 0, M44.pts 1, M44.pts 2] : Fin 3 → Plane) = M44.pts := by
  funext i; fin_cases i <;> rfl

theorem hind : AffineIndependent ℝ ![M44.pts 0, M44.pts 1, M44.pts 2] := by
  rw [hpts]; exact M44.indep

/-- The model, rebuilt on the vector `![A, B, C]` the ladder takes. -/
noncomputable def M' : Tri := ⟨![M44.pts 0, M44.pts 1, M44.pts 2], hind⟩

theorem M'_pts : M'.pts = M44.pts := hpts

theorem M'_angle (k : Fin 3) : M'.angleAt k = M44.angleAt k := by
  unfold Tri.angleAt
  rw [M'_pts]

/-- **The scale-2 ladder of the model: a real `CongruentDissection 4`.** -/
noncomputable def D2 : CongruentDissection (2 * 2) where
  toDissection := ladderDissection (M44.pts 0) (M44.pts 1) (M44.pts 2) hind 2 (by norm_num)
  model := M'
  tiles_congruent := fun n =>
    (ladderDissection_congruent (M44.pts 0) (M44.pts 1) (M44.pts 2) hind 2 (by norm_num) n).symm

theorem D2_target : D2.target = bigTri (M44.pts 0) (M44.pts 1) (M44.pts 2) hind 2 (by norm_num) :=
  rfl

theorem D2_hom (i : Fin 3) :
    D2.target.pts i = M44.pts 0 + (2 : ℝ) • (M'.pts i - M44.pts 0) := by
  rw [D2_target]
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  rcases hi with rfl | rfl | rfl
  · rw [bigTri_pts0]
    show M44.pts 0 = M44.pts 0 + (2 : ℝ) • (M44.pts 0 - M44.pts 0)
    simp
  · rw [bigTri_pts1]
    show P (M44.pts 0) (M44.pts 1) (M44.pts 2) 2 0 = M44.pts 0 + (2 : ℝ) • (M44.pts 1 - M44.pts 0)
    unfold P
    push_cast
    simp
  · rw [bigTri_pts2]
    show P (M44.pts 0) (M44.pts 1) (M44.pts 2) 0 2 = M44.pts 0 + (2 : ℝ) • (M44.pts 2 - M44.pts 0)
    unfold P
    push_cast
    simp

theorem D2_sim (k : Fin 3) :
    D2.target.angleAt k = D2.model.angleAt k ∧ D2.target.oppLen k = 2 * D2.model.oppLen k :=
  homothety_angle_opp M' D2.target (M44.pts 0) 2 (by norm_num) D2_hom k

/-- Every element of `⟨β, γ, π⟩` is `jπ + kθ`. -/
theorem closure_form (y : ℝ)
    (hy : y ∈ AddSubgroup.closure ({D2.model.angleAt 0, D2.model.angleAt 1, Real.pi} : Set ℝ)) :
    ∃ j k : ℤ, y = (j : ℝ) * Real.pi + (k : ℝ) * θ44 := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · refine ⟨2, -3, ?_⟩
      show M'.angleAt 0 = _
      rw [M'_angle, β44_eq]
    · refine ⟨0, 1, ?_⟩
      show M'.angleAt 1 = _
      rw [M'_angle, γ44_eq]
    · exact ⟨1, 0, by push_cast; ring⟩
  | zero => exact ⟨0, 0, by push_cast; ring⟩
  | add x y _ _ hx hy =>
    obtain ⟨j, k, rfl⟩ := hx
    obtain ⟨j', k', rfl⟩ := hy
    exact ⟨j + j', k + k', by push_cast; ring⟩
  | neg x _ hx =>
    obtain ⟨j, k, rfl⟩ := hx
    exact ⟨-j, -k, by push_cast; ring⟩

/-- **`π ∉ 2Λ`** for the `(2,3,4)` tile. -/
theorem D2_pi (y : ℝ)
    (hy : y ∈ AddSubgroup.closure ({D2.model.angleAt 0, D2.model.angleAt 1, Real.pi} : Set ℝ)) :
    Real.pi ≠ 2 * y := by
  obtain ⟨j, k, rfl⟩ := closure_form y hy
  intro h
  by_cases hk : k = 0
  · subst hk
    have h1 : ((1 : ℝ) - 2 * j) * Real.pi = 0 := by push_cast at h; linear_combination h
    have h2 : (1 : ℝ) - 2 * j = 0 := (mul_eq_zero.mp h1).resolve_right Real.pi_ne_zero
    have h3 : (1 : ℤ) = 2 * j := by exact_mod_cast (by linarith : (1 : ℝ) = 2 * j)
    omega
  · apply θ44_irr
    have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
    refine ⟨((1 - 2 * j : ℤ) : ℚ) / ((2 * k : ℤ) : ℚ), ?_⟩
    push_cast
    rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero two_ne_zero hk')]
    linear_combination (-1 : ℝ) * h

/-- **Lemma W on a real dissection: `μ = 2` is an integer `≡ N = 4 (mod 2)`.** -/
theorem lemmaW_D2 : ∃ S : ℤ, (2 : ℝ) = S ∧ (2 : ℤ) ∣ S - ((2 * 2 : ℕ) : ℤ) :=
  Row2.lemmaW D2 2 D2_sim D2_pi

end Erdos634.Draft.FluxRow2Witness

#print axioms Erdos634.Draft.FluxRow2Witness.lemmaW_D2
