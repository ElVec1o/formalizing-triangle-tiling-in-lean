-- Draft/FluxGridWitness.lean — NON-VACUITY WITNESS for layer 2 (`Tri.flux_grid_pm`,
-- `CongruentDissection.target_flux_signs`, `GridChar.rank2`) on the REAL 44-tiling.
-- Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).  Design: (private working notes, not included) §5 (row "layer 2 and row 12").
--
-- The model tile of `Tiling44Bridge.dissection` has sides `(16, 24, 32)` = `8·(2,3,4)`; its angles
-- are `β` (vertex 0, cos 11/16), `γ` (vertex 1, cos −1/4), `α` (vertex 2, cos 7/8), with
-- `3α + 2β = π` (proved here from the cosines) and `α ∉ ℚπ` (`BaseBetaE1.tile_alpha_irrational`,
-- `e = 1, f = 2`).  With `θ = α/2 + π/2` the three angles lie in `L = ℤπ + ℤθ`:
-- `α = −π + 2θ`, `β = 2π − 3θ`, `γ = θ`.  The grid characters `χ₊ = rank2 θ 0`, `χ₋ = rank2 θ 1`
-- (anchor `0` = the target's base direction) give tile values `K₊ = −40`, `K₋ = 72`
-- (= `−8(c+b−a)`, `8(a+b+c)`), target fluxes `−80` and `432`, hence the sums of signs of `cor:int`
-- are `S₊ = 2`, `S₋ = 6` — matching the float check (`K = −2, M = 6` in `check_flux_numeric.out`,
-- normalised by `c+b−a` and `a+b+c`) and EVIDENCE's control `M = 6`.
import Erdos634.Draft.FluxGrids
import Erdos634.Draft.FluxValue
import Erdos634.Draft.FluxWitness
import Erdos634.BaseBetaE1

open scoped Classical

namespace Erdos634.Draft.FluxGridWitness

open Erdos634.Geometry Erdos634.Z15Real Erdos634.Tiling44Bridge Erdos634.CertCoord
open Erdos634.Draft.FluxWitness

/-- Law of cosines, cosine form. -/
theorem cos_cornerAngle {p q r : Plane} (hp : p ≠ q) (hr : r ≠ q) :
    Real.cos (cornerAngle p q r)
      = (dist p q ^ 2 + dist r q ^ 2 - dist p r ^ 2) / (2 * dist p q * dist r q) := by
  have hlaw :=
    EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle p q r
  have h1 : 0 < dist p q := dist_pos.mpr hp
  have h2 : 0 < dist r q := dist_pos.mpr hr
  unfold cornerAngle
  rw [eq_div_iff (by positivity)]
  linear_combination hlaw

theorem cornerAngle_mem (p q r : Plane) : 0 ≤ cornerAngle p q r ∧ cornerAngle p q r ≤ Real.pi :=
  ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩

/-! ## The model tile -/

/-- The model tile `(16, 24, 32)`. -/
noncomputable abbrev M44 : Tri := pieceTri headI_mem_tiles

theorem m_d01 : dist (M44.pts 0) (M44.pts 1) = 16 := by
  have e : Tiling44.dist2 (vertexOf Tiling44.tiles.headI 0) (vertexOf Tiling44.tiles.headI 1)
      = ((256:ℤ),(0:ℤ)) := by decide
  exact dist_of_sq' (by norm_num)
    (by rw [pieceTri_dist_sq _ headI_mem_tiles 0 1, e]; simp [toR]; norm_num)

theorem m_d12 : dist (M44.pts 1) (M44.pts 2) = 24 := by
  have e : Tiling44.dist2 (vertexOf Tiling44.tiles.headI 1) (vertexOf Tiling44.tiles.headI 2)
      = ((576:ℤ),(0:ℤ)) := by decide
  exact dist_of_sq' (by norm_num)
    (by rw [pieceTri_dist_sq _ headI_mem_tiles 1 2, e]; simp [toR]; norm_num)

theorem m_d20 : dist (M44.pts 2) (M44.pts 0) = 32 := by
  have e : Tiling44.dist2 (vertexOf Tiling44.tiles.headI 2) (vertexOf Tiling44.tiles.headI 0)
      = ((1024:ℤ),(0:ℤ)) := by decide
  exact dist_of_sq' (by norm_num)
    (by rw [pieceTri_dist_sq _ headI_mem_tiles 2 0, e]; simp [toR]; norm_num)

theorem ne_of_dist {p q : Plane} {c : ℝ} (h : dist p q = c) (hc : c ≠ 0) : p ≠ q := by
  rintro rfl; rw [dist_self] at h; exact hc h.symm

/-- `α`: the model's angle at vertex 2. -/
noncomputable def α44 : ℝ := M44.angleAt 2
/-- `β`: the model's angle at vertex 0. -/
noncomputable def β44 : ℝ := M44.angleAt 0
/-- `θ = α/2 + π/2`, the free generator of the grid. -/
noncomputable def θ44 : ℝ := α44 / 2 + Real.pi / 2

theorem cos_α44 : Real.cos α44 = 7 / 8 := by
  unfold α44 Tri.angleAt
  simp only [show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
  rw [cos_cornerAngle (ne_of_dist m_d20 (by norm_num)).symm (ne_of_dist m_d12 (by norm_num)), dist_comm (M44.pts 0) (M44.pts 2), m_d20, m_d12, m_d01]
  norm_num

theorem cos_β44 : Real.cos β44 = 11 / 16 := by
  unfold β44 Tri.angleAt
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl]
  rw [cos_cornerAngle (ne_of_dist m_d01 (by norm_num)).symm (ne_of_dist m_d20 (by norm_num)), dist_comm (M44.pts 1) (M44.pts 0), m_d01, m_d20, m_d12]
  norm_num

theorem α44_le : α44 ≤ Real.pi / 3 := by
  by_contra h
  push Not at h
  have := Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity : (0:ℝ) ≤ Real.pi / 3)
    (cornerAngle_mem _ _ _).2 h
  rw [Real.cos_pi_div_three] at this
  have h2 : Real.cos α44 < 1 / 2 := this
  rw [cos_α44] at h2
  norm_num at h2

theorem β44_le : β44 ≤ Real.pi / 2 := by
  by_contra h
  push Not at h
  have := Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity : (0:ℝ) ≤ Real.pi / 2)
    (cornerAngle_mem _ _ _).2 h
  rw [Real.cos_pi_div_two] at this
  have h2 : Real.cos β44 < 0 := this
  rw [cos_β44] at h2
  norm_num at h2

/-- **`3α + 2β = π`** for the model, from the cosines. -/
theorem three_α_two_β : 3 * α44 + 2 * β44 = Real.pi := by
  have hα0 : 0 ≤ α44 := (cornerAngle_mem _ _ _).1
  have hβ0 : 0 ≤ β44 := (cornerAngle_mem _ _ _).1
  have hc1 : Real.cos (3 * α44) = 7 / 128 := by rw [Real.cos_three_mul, cos_α44]; norm_num
  have hc2 : Real.cos (Real.pi - 2 * β44) = 7 / 128 := by
    rw [Real.cos_pi_sub, Real.cos_two_mul, cos_β44]; norm_num
  have hαle := α44_le
  have hβle := β44_le
  have := Real.injOn_cos ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
    (hc1.trans hc2.symm)
  linarith

/-- `α ∉ ℚπ` (Niven, via `BaseBetaE1.tile_alpha_irrational` at `e = 1, f = 2`). -/
theorem α44_irr : ¬ ∃ r : ℚ, α44 = (r : ℝ) * Real.pi := by
  have hα0 : 0 ≤ α44 := (cornerAngle_mem _ _ _).1
  have hαπ : α44 ≤ Real.pi := (cornerAngle_mem _ _ _).2
  have hdouble := Real.cos_two_mul (α44 / 2)
  rw [show 2 * (α44 / 2) = α44 by ring, cos_α44] at hdouble
  have hsc := Real.sin_sq_add_cos_sq (α44 / 2)
  have hs2 : Real.sin (α44 / 2) ^ 2 = 1 / 16 := by linarith
  have hs0 : 0 ≤ Real.sin (α44 / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hs : Real.sin (α44 / 2) = 1 / 4 := by
    have hprod : (Real.sin (α44 / 2) - 1 / 4) * (Real.sin (α44 / 2) + 1 / 4) = 0 := by
      linear_combination hs2
    rcases mul_eq_zero.mp hprod with h | h
    · linarith
    · linarith
  exact Erdos634.BaseBetaE1.tile_alpha_irrational 1 2 le_rfl (by norm_num) α44
    (by rw [hs]; norm_num)

theorem θ44_irr : ¬ ∃ r : ℚ, θ44 = (r : ℝ) * Real.pi := by
  rintro ⟨r, hr⟩
  apply α44_irr
  refine ⟨2 * r - 1, ?_⟩
  push_cast
  unfold θ44 at hr
  linear_combination 2 * hr

theorem α44_eq : M44.angleAt 2 = ((-1 : ℤ) : ℝ) * Real.pi + ((2 : ℤ) : ℝ) * θ44 := by
  show α44 = _
  unfold θ44; push_cast; ring

theorem β44_eq : M44.angleAt 0 = ((2 : ℤ) : ℝ) * Real.pi + ((-3 : ℤ) : ℝ) * θ44 := by
  show β44 = _
  have h := three_α_two_β
  unfold θ44; push_cast; linarith

theorem γ44_eq : M44.angleAt 1 = ((0 : ℤ) : ℝ) * Real.pi + ((1 : ℤ) : ℝ) * θ44 := by
  have hsum := M44.angleAt_sum
  have h := three_α_two_β
  have ha : M44.angleAt 2 = α44 := rfl
  have hb : M44.angleAt 0 = β44 := rfl
  unfold θ44; push_cast
  linarith

/-! ## The two grid characters -/

/-- `χ₊`: parity `j` on `jπ + kθ`. -/
noncomputable def Gplus : GridChar ℝ := GridChar.rank2 θ44 θ44_irr 0 0
/-- `χ₋`: parity `j + k` on `jπ + kθ`. -/
noncomputable def Gminus : GridChar ℝ := GridChar.rank2 θ44 θ44_irr 1 0

theorem model_angles_mem (b : ZMod 2) :
    ∀ k, ((M44.angleAt k : ℝ) : Real.Angle) ∈ (GridChar.rank2 θ44 θ44_irr b 0).L := by
  intro k
  fin_cases k
  · show ((M44.angleAt 0 : ℝ) : Real.Angle) ∈ _
    rw [β44_eq]; exact GridChar.rank2_mem _ _ _ _ _ _
  · show ((M44.angleAt 1 : ℝ) : Real.Angle) ∈ _
    rw [γ44_eq]; exact GridChar.rank2_mem _ _ _ _ _ _
  · show ((M44.angleAt 2 : ℝ) : Real.Angle) ∈ _
    rw [α44_eq]; exact GridChar.rank2_mem _ _ _ _ _ _

theorem ext0 : Real.pi - M44.angleAt 0 = ((-1 : ℤ) : ℝ) * Real.pi + ((3 : ℤ) : ℝ) * θ44 := by
  rw [β44_eq]; push_cast; ring
theorem ext1 : Real.pi - M44.angleAt 1 = ((1 : ℤ) : ℝ) * Real.pi + ((-1 : ℤ) : ℝ) * θ44 := by
  rw [γ44_eq]; push_cast; ring
theorem ext2 : Real.pi - M44.angleAt 2 = ((2 : ℤ) : ℝ) * Real.pi + ((-2 : ℤ) : ℝ) * θ44 := by
  rw [α44_eq]; push_cast; ring

theorem m_opp : M44.oppLen 0 = 24 ∧ M44.oppLen 1 = 32 ∧ M44.oppLen 2 = 16 := by
  unfold Tri.oppLen
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl,
    show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl,
    show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
  exact ⟨m_d12, m_d20, m_d01⟩

/-- **Tile value for `χ₊`: `K₊ = −24 − 32 + 16 = −40`** (`= −8(c+b−a)`). -/
theorem tileValue_plus : Gplus.tileValue M44 = -40 := by
  unfold Gplus GridChar.tileValue
  rw [Fin.sum_univ_three, ext0, ext1, ext2, GridChar.rank2_chi, GridChar.rank2_chi,
    GridChar.rank2_chi, m_opp.1, m_opp.2.1, m_opp.2.2]
  rw [if_neg (by decide), if_neg (by decide), if_pos (by decide)]
  norm_num

/-- **Tile value for `χ₋`: `K₋ = 24 + 32 + 16 = 72`** (`= 8(a+b+c)`). -/
theorem tileValue_minus : Gminus.tileValue M44 = 72 := by
  unfold Gminus GridChar.tileValue
  rw [Fin.sum_univ_three, ext0, ext1, ext2, GridChar.rank2_chi, GridChar.rank2_chi,
    GridChar.rank2_chi, m_opp.1, m_opp.2.1, m_opp.2.2]
  rw [if_pos (by decide), if_pos (by decide), if_pos (by decide)]
  norm_num

/-! ## `cor:int` on the real 44-tiling (all hypotheses exhibited) -/

theorem cor_int_44_plus : ∃ S : ℤ, (2 : ℤ) ∣ S - Tiling44.tiles.length
    ∧ |S| ≤ Tiling44.tiles.length ∧ dissection.target.flux Gplus.weight = (S : ℝ) * (-40) := by
  obtain ⟨S, h1, h2, h3⟩ := dissection.target_flux_signs Gplus
    (GridChar.rank2_sq _ _ _ _) (model_angles_mem 0)
  exact ⟨S, h1, h2, by rw [h3]; congr 1; exact tileValue_plus⟩

theorem cor_int_44_minus : ∃ S : ℤ, (2 : ℤ) ∣ S - Tiling44.tiles.length
    ∧ |S| ≤ Tiling44.tiles.length ∧ dissection.target.flux Gminus.weight = (S : ℝ) * 72 := by
  obtain ⟨S, h1, h2, h3⟩ := dissection.target_flux_signs Gminus
    (GridChar.rank2_sq _ _ _ _) (model_angles_mem 1)
  exact ⟨S, h1, h2, by rw [h3]; congr 1; exact tileValue_minus⟩

/-! ## Evaluating the target side: `S₊ = 2`, `S₋ = 6` -/

theorem t_angle0 : targetTri.angleAt 0 = β44 := by
  have hcos : Real.cos (targetTri.angleAt 0) = 11 / 16 := by
    unfold Tri.angleAt
    simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl]
    rw [cos_cornerAngle (ne_of_dist target44_d01 (by norm_num)).symm
      (ne_of_dist target44_d20 (by norm_num)), dist_comm (targetTri.pts 1) (targetTri.pts 0),
      target44_d01, target44_d20, target44_d12]
    norm_num
  exact Real.injOn_cos (cornerAngle_mem _ _ _) (cornerAngle_mem _ _ _) (hcos.trans cos_β44.symm)

theorem t_angle1 : targetTri.angleAt 1 = β44 := by
  have hcos : Real.cos (targetTri.angleAt 1) = 11 / 16 := by
    unfold Tri.angleAt
    simp only [show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl]
    rw [cos_cornerAngle (ne_of_dist target44_d12 (by norm_num)).symm
      (ne_of_dist target44_d01 (by norm_num)), dist_comm (targetTri.pts 2) (targetTri.pts 1),
      target44_d12, target44_d01, target44_d20]
    norm_num
  exact Real.injOn_cos (cornerAngle_mem _ _ _) (cornerAngle_mem _ _ _) (hcos.trans cos_β44.symm)

theorem t_angle2 : targetTri.angleAt 2 = 3 * α44 := by
  have hcos : Real.cos (targetTri.angleAt 2) = 7 / 128 := by
    unfold Tri.angleAt
    simp only [show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
    rw [cos_cornerAngle (ne_of_dist target44_d20 (by norm_num)).symm
      (ne_of_dist target44_d12 (by norm_num)), dist_comm (targetTri.pts 0) (targetTri.pts 2),
      target44_d20, target44_d12, target44_d01]
    norm_num
  have hc3 : Real.cos (3 * α44) = 7 / 128 := by rw [Real.cos_three_mul, cos_α44]; norm_num
  have hα0 : 0 ≤ α44 := (cornerAngle_mem _ _ _).1
  have hαle := α44_le
  exact Real.injOn_cos (cornerAngle_mem _ _ _) ⟨by linarith, by linarith⟩ (hcos.trans hc3.symm)

theorem target_angles_mem (b : ZMod 2) :
    ∀ k, ((targetTri.angleAt k : ℝ) : Real.Angle) ∈ (GridChar.rank2 θ44 θ44_irr b 0).L := by
  have hβ : β44 = ((2 : ℤ) : ℝ) * Real.pi + ((-3 : ℤ) : ℝ) * θ44 := β44_eq
  have h3α : 3 * α44 = ((-3 : ℤ) : ℝ) * Real.pi + ((6 : ℤ) : ℝ) * θ44 := by
    unfold θ44; push_cast; ring
  intro k
  fin_cases k
  · show ((targetTri.angleAt 0 : ℝ) : Real.Angle) ∈ _
    rw [t_angle0, hβ]; exact GridChar.rank2_mem _ _ _ _ _ _
  · show ((targetTri.angleAt 1 : ℝ) : Real.Angle) ∈ _
    rw [t_angle1, hβ]; exact GridChar.rank2_mem _ _ _ _ _ _
  · show ((targetTri.angleAt 2 : ℝ) : Real.Angle) ∈ _
    rw [t_angle2, h3α]; exact GridChar.rank2_mem _ _ _ _ _ _

/-- The target's base direction has angle `0` (the anchor). -/
theorem t_leftUnit0_angle : (targetTri.leftUnit 0).angle = 0 := by
  have hL0 : targetTri.leftDir 0 = targetTri.pts 1 - targetTri.pts 0 := by
    unfold Tri.leftDir; rw [if_pos target44_det_pos]; rfl
  have hC : toC (targetTri.leftDir 0) = ((176 : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [toC_re, hL0, target44_pts1, target44_pts0]; simp
    · rw [toC_im, hL0, target44_pts1, target44_pts0]; simp
  rw [Tri.leftUnit_angle, hC, Complex.arg_ofReal_of_nonneg (by norm_num), Real.Angle.coe_zero]

theorem t_ext1 : Real.pi - targetTri.angleAt 1 = ((-1 : ℤ) : ℝ) * Real.pi + ((3 : ℤ) : ℝ) * θ44 := by
  rw [t_angle1, β44_eq']
  push_cast; ring
where β44_eq' : β44 = ((2 : ℤ) : ℝ) * Real.pi + ((-3 : ℤ) : ℝ) * θ44 := β44_eq

theorem t_ext2 : Real.pi - targetTri.angleAt 2 = ((4 : ℤ) : ℝ) * Real.pi + ((-6 : ℤ) : ℝ) * θ44 := by
  rw [t_angle2]
  unfold θ44; push_cast; ring

theorem t_opp : targetTri.oppLen 0 = 128 ∧ targetTri.oppLen 1 = 128 ∧ targetTri.oppLen 2 = 176 := by
  unfold Tri.oppLen
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl,
    show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl,
    show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
  exact ⟨target44_d12, target44_d20, target44_d01⟩

theorem t_weight0 (b : ZMod 2) :
    (GridChar.rank2 θ44 θ44_irr b 0).weight (targetTri.leftUnit 0) = 1 := by
  unfold GridChar.weight
  rw [t_leftUnit0_angle]
  exact GridChar.val_anchor _

/-- **Target flux for `χ₋`: `176 + 128 + 128 = 432`.** -/
theorem target_flux_minus : dissection.target.flux Gminus.weight = 432 := by
  show targetTri.flux Gminus.weight = 432
  unfold Gminus
  rw [targetTri.flux_grid_of_pos _ target44_det_pos (target_angles_mem 1), t_weight0, t_ext1,
    t_ext2, GridChar.rank2_chi, GridChar.rank2_chi, t_opp.1, t_opp.2.1, t_opp.2.2]
  rw [if_pos (by decide), if_pos (by decide)]
  norm_num

/-- **Target flux for `χ₊`: `176 − 128 − 128 = −80`.** -/
theorem target_flux_plus : dissection.target.flux Gplus.weight = -80 := by
  show targetTri.flux Gplus.weight = -80
  unfold Gplus
  rw [targetTri.flux_grid_of_pos _ target44_det_pos (target_angles_mem 0), t_weight0, t_ext1,
    t_ext2, GridChar.rank2_chi, GridChar.rank2_chi, t_opp.1, t_opp.2.1, t_opp.2.2]
  rw [if_neg (by decide), if_pos (by decide)]
  norm_num

/-- **`cor:int` evaluated: the sum of 44 signs for `χ₋` is `M = 6`** (even, as `44` is). -/
theorem cor_int_44_minus_value : ∃ S : ℤ, S = 6 ∧ (2 : ℤ) ∣ S - Tiling44.tiles.length
    ∧ |S| ≤ Tiling44.tiles.length ∧ dissection.target.flux Gminus.weight = (S : ℝ) * 72 := by
  obtain ⟨S, h1, h2, h3⟩ := cor_int_44_minus
  refine ⟨S, ?_, h1, h2, h3⟩
  rw [target_flux_minus] at h3
  have : (S : ℝ) = 6 := by linarith
  exact_mod_cast this

/-- **`cor:int` evaluated: the sum of 44 signs for `χ₊` is `2`.** -/
theorem cor_int_44_plus_value : ∃ S : ℤ, S = 2 ∧ (2 : ℤ) ∣ S - Tiling44.tiles.length
    ∧ |S| ≤ Tiling44.tiles.length ∧ dissection.target.flux Gplus.weight = (S : ℝ) * (-40) := by
  obtain ⟨S, h1, h2, h3⟩ := cor_int_44_plus
  refine ⟨S, ?_, h1, h2, h3⟩
  rw [target_flux_plus] at h3
  have : (S : ℝ) = 2 := by linarith
  exact_mod_cast this

end Erdos634.Draft.FluxGridWitness

#print axioms Erdos634.Draft.FluxGridWitness.cor_int_44_minus_value
#print axioms Erdos634.Draft.FluxGridWitness.cor_int_44_plus_value
#print axioms Erdos634.Draft.FluxGridWitness.tileValue_plus
