-- Draft/R1Kill.lean — R1 steps 2–4 on the parallel frame `R1Frame`: the tile `L′` across `VP′`, the
-- corner `Z` against the ray `ρ` (r beyond `V`), the census forcing `Z` to be an `α`-corner, and
-- the depth exit.  Imported into All.lean (header updated 2026-10-01).  Part of the R1 formalization
-- ((private working notes, not included); reviews review_R1_fresh, review2_R1_fresh).
--
-- WHAT IS PROVED (no `sorry`):
--   `Lprime_exists`  (step 2) — the non-`T₂` side of `VP′` is ONE `a`-edge `[V, P′]` of a tile `L′`,
--       whose corner at `V` is `β` or `γ`.  TRACE COVERING on the line `VP′` (`TraceCovering.wall_sum`):
--       start `V` not straddled (the piercer crosses the line at `V`: `near_interior_of_across`), end
--       `P′` not straddled (two `γ` at `P′`: `R1Pierce.no_straight_at_pprime`), then
--       `ThickEFminus1Steps.a_rep_unique` (the only representation of `a` is `a`).
--   `Z_exists` — the near-side tile across the piercer's edge at `V` along `ρ` has a CORNER at `V`
--       with one flank positively along `u_r` and the other on `P′`'s side
--       (`ApexPlacement.flank_neighbour_gen`, the edge case excluded by the piercer's uniqueness).
--   `Z_alpha` (step 3) — the census at `V` (`R1Pierce.fill_at_V`) + irrationality force `Z` to be `α`
--       (`L′ ≠ Z` by the angle `π − β` between `u_r` and `VP′`).
--   `r1_frame_false` (step 4) — `Z`'s `c`-flank ends beyond the base: its cone coordinates sum to
--       `2c/(f·b) > 1`.  The ONLY place the member enters is `hdepth : f·b < 2c`, which holds
--       exactly on the line `e = f − 1` (`depth_thick`).  The flank along `u(−α/2)` is identified as
--       the direction of `AP′` (`coord_align`: same inner product and same side as `P′ − A`).
-- The steps use no `β < α`, no `a − b` parity and hold at `f = 2`.
--
-- Build (scratch oleans; never .lake): R1Pierce, NearBaseBridge oleans in $S, then lean_guard.sh.
import Erdos634.Draft.R1Pierce
import Erdos634.Draft.NearBaseBridge

namespace Erdos634.Draft.R1Kill

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.HalfTurnR3R4Glue
open Erdos634.Draft.R1Frame Erdos634.Draft.R1Pierce
open Erdos634.Draft.CornerAdjacency Erdos634.Draft.ApexPlacement Erdos634.Draft.NearBaseVertex

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ}

/-! ## §0 Plane coordinates -/

theorem norm_sq_coords (w : Plane) : ‖w‖ ^ 2 = w 0 ^ 2 + w 1 ^ 2 := by
  have := dist_sq' w 0
  rw [dist_zero_right] at this
  simpa using this

/-- A vector with zero cross product against a unit vector is a multiple of it. -/
theorem smul_of_cross_zero_unit {u w : Plane} (hu : ‖u‖ = 1) (h : cross u w = 0) :
    w = (u 0 * w 0 + u 1 * w 1) • u := by
  have h1 : u 0 ^ 2 + u 1 ^ 2 = 1 := by rw [← norm_sq_coords, hu]; norm_num
  rw [cross_apply] at h
  ext i; fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, PiLp.smul_apply, smul_eq_mul]
    linear_combination (-(w 0)) * h1 - (u 1) * h
  · simp only [Fin.mk_one, Fin.isValue, PiLp.smul_apply, smul_eq_mul]
    linear_combination (-(w 1)) * h1 + (u 0) * h

/-- **The alignment identity.**  `u` unit; `w` of length `c` with `|b·u − w| = a`; `g` of length `b`
with `|c·u − g| = a`; `w`, `g` strictly on the same side of `ℝu`.  Then `b·w = c·g`. -/
theorem coord_align {u0 u1 w0 w1 g0 g1 a b c : ℝ} (hb : 0 < b) (hc : 0 < c)
    (h1 : u0 ^ 2 + u1 ^ 2 = 1) (h2 : w0 ^ 2 + w1 ^ 2 = c ^ 2)
    (h3 : (b * u0 - w0) ^ 2 + (b * u1 - w1) ^ 2 = a ^ 2) (h4 : g0 ^ 2 + g1 ^ 2 = b ^ 2)
    (h5 : (c * u0 - g0) ^ 2 + (c * u1 - g1) ^ 2 = a ^ 2)
    (h6 : 0 < (u0 * w1 - u1 * w0) * (u0 * g1 - u1 * g0)) :
    b * w0 = c * g0 ∧ b * w1 = c * g1 := by
  set p := u0 * w0 + u1 * w1 with hp
  set q := u0 * w1 - u1 * w0 with hq
  set p' := u0 * g0 + u1 * g1 with hp'
  set q' := u0 * g1 - u1 * g0 with hq'
  have e3 : b ^ 2 - 2 * b * p + c ^ 2 = a ^ 2 := by
    rw [hp]; linear_combination h3 - b ^ 2 * h1 - h2
  have e5 : c ^ 2 - 2 * c * p' + b ^ 2 = a ^ 2 := by
    rw [hp']; linear_combination h5 - c ^ 2 * h1 - h4
  have hbp : b * p = c * p' := by linarith
  have hL1 : p ^ 2 + q ^ 2 = c ^ 2 := by
    rw [hp, hq]; linear_combination (w0 ^ 2 + w1 ^ 2) * h1 + h2
  have hL2 : p' ^ 2 + q' ^ 2 = b ^ 2 := by
    rw [hp', hq']; linear_combination (g0 ^ 2 + g1 ^ 2) * h1 + h4
  have hsq : (b * q) ^ 2 = (c * q') ^ 2 := by
    have : (b * p) ^ 2 = (c * p') ^ 2 := by rw [hbp]
    linear_combination b ^ 2 * hL1 - c ^ 2 * hL2 - this
  have hbq : b * q = c * q' := by
    have hpos : 0 < (b * q) * (c * q') := by
      have : (b * q) * (c * q') = (b * c) * (q * q') := by ring
      rw [this]; exact mul_pos (mul_pos hb hc) h6
    have h0 : (b * q - c * q') * (b * q + c * q') = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp h0 with h | h
    · linarith
    · exfalso
      have : b * q = -(c * q') := by linarith
      rw [this] at hpos; nlinarith [sq_nonneg (c * q')]
  have hw0 : w0 = u0 * p - u1 * q := by rw [hp, hq]; linear_combination (-w0) * h1
  have hw1 : w1 = u1 * p + u0 * q := by rw [hp, hq]; linear_combination (-w1) * h1
  have hg0 : g0 = u0 * p' - u1 * q' := by rw [hp', hq']; linear_combination (-g0) * h1
  have hg1 : g1 = u1 * p' + u0 * q' := by rw [hp', hq']; linear_combination (-g1) * h1
  constructor
  · rw [hw0, hg0]; linear_combination u0 * hbp - u1 * hbq
  · rw [hw1, hg1]; linear_combination u1 * hbp + u0 * hbq

/-! ## §1 Corner data at a vertex (general `1 ≤ e < f`) -/

/-- Every corner of a tile is `α`, `β` or `γ`. -/
theorem vertex_angle_mem (D : CongruentDissection N) {α β γ : ℝ}
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (j : Fin N) (m : Fin 3) :
    (D.tile j).localAngle ((D.tile j).pts m) = α ∨ (D.tile j).localAngle ((D.tile j).pts m) = β ∨
      (D.tile j).localAngle ((D.tile j).pts m) = γ := by
  rw [Tri.localAngle_vertex]
  obtain ⟨k, hk⟩ := congruent_corner_angles (D.tiles_congruent j).symm m
  rw [hk]
  have hall : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  rcases hall k with rfl | rfl | rfl
  · exact Or.inl hα'
  · exact Or.inr (Or.inl hβ')
  · exact Or.inr (Or.inr hγ')

/-- **Corner data** (the pattern of `MirrorStripR2Real.corner_data` / `LemmaGRowReal.corner_dataG`,
general `e`): the flank lengths and the opposite side of a corner, by its angle. -/
theorem corner_data1 (D : CongruentDissection N) {e f : ℕ} {α β γ : ℝ}
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (hM : ModelDataE D e f α β γ) (hAD : MarchSlots.AngleData α β γ)
    {i : Fin N} {m : Fin 3} {x U W : Plane} (hm : (D.tile i).pts m = x)
    (hUW : IsFlankPair (D.tile i) m x U W) :
    ((D.tile i).localAngle x = α →
      ((‖U‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧ ‖W‖ = (f : ℝ) ^ 2) ∨
        (‖U‖ = (f : ℝ) ^ 2 ∧ ‖W‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ∧
      dist (x + U) (x + W) = (e : ℝ) * f) ∧
    ((D.tile i).localAngle x = β →
      ((‖U‖ = (e : ℝ) * f ∧ ‖W‖ = (f : ℝ) ^ 2) ∨ (‖U‖ = (f : ℝ) ^ 2 ∧ ‖W‖ = (e : ℝ) * f)) ∧
      dist (x + U) (x + W) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ∧
    ((D.tile i).localAngle x = γ →
      ((‖U‖ = (e : ℝ) * f ∧ ‖W‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ∨
        (‖U‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧ ‖W‖ = (e : ℝ) * f)) ∧
      dist (x + U) (x + W) = (f : ℝ) ^ 2) := by
  obtain ⟨hab, hac, hbc⟩ := sides_distinct1 hco he hef
  have hP := NearBaseBridge.tile_triple (D.tiles_congruent i) hM.hs0 hM.hs1 hM.hs2 m
  have hL := localAngle_of_oppSideE D hab hac hbc hM.hs0 hM.hs1 hM.hs2 hM.hα' hM.hβ' hM.hγ' i m
  rw [hm] at hP hL
  have hα := hAD.hα
  have hβ := hAD.hβ
  have hγd := hAD.hγdef
  have hαβ := hAD.hαβ
  obtain ⟨e1, e2, e3⟩ := hL
  have hx : ∀ q : Fin 3, ‖(D.tile i).pts q - x‖ = dist ((D.tile i).pts q) x :=
    fun q => (dist_eq_norm _ _).symm
  have hy : ∀ q : Fin 3, x + ((D.tile i).pts q - x) = (D.tile i).pts q := fun q => by abel
  unfold NearBaseBridge.Perm3 at hP
  rcases hUW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [hx, hx, hy, hy]
    rcases hP with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2, h3⟩ <;>
    refine ⟨fun hg => ?_, fun hg => ?_, fun hg => ?_⟩ <;>
    first
      | exact ⟨Or.inl ⟨h1, h2⟩, h3⟩
      | exact ⟨Or.inr ⟨h1, h2⟩, h3⟩
      | (exfalso; have h4 := (e1 h3).symm.trans hg
         first | linarith | exact hαβ h4 | exact hαβ h4.symm)
      | (exfalso; have h4 := (e2 h3).symm.trans hg
         first | linarith | exact hαβ h4 | exact hαβ h4.symm)
      | (exfalso; have h4 := (e3 h3).symm.trans hg
         first | linarith | exact hαβ h4 | exact hαβ h4.symm)
  · rw [hx, hx, hy, hy, dist_comm ((D.tile i).pts (m + 2)) ((D.tile i).pts (m + 1))]
    rcases hP with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2, h3⟩ <;>
    refine ⟨fun hg => ?_, fun hg => ?_, fun hg => ?_⟩ <;>
    first
      | exact ⟨Or.inl ⟨h2, h1⟩, h3⟩
      | exact ⟨Or.inr ⟨h2, h1⟩, h3⟩
      | (exfalso; have h4 := (e1 h3).symm.trans hg
         first | linarith | exact hαβ h4 | exact hαβ h4.symm)
      | (exfalso; have h4 := (e2 h3).symm.trans hg
         first | linarith | exact hαβ h4 | exact hαβ h4.symm)
      | (exfalso; have h4 := (e3 h3).symm.trans hg
         first | linarith | exact hαβ h4 | exact hαβ h4.symm)

/-- The local angle at a vertex, read as the angle between the other two vertices. -/
theorem localAngle_of_range_angle {T : Tri} {X Y Z : Plane} (hr : Set.range T.pts = {X, Y, Z}) :
    T.localAngle X = InnerProductGeometry.angle (Y - X) (Z - X) := by
  obtain ⟨k, hk⟩ := MarchInduction.mem_range_of_eq hr (Set.mem_insert _ _)
  rcases MarchInduction.vertex_data_of_range hr hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact flank_angle hk (Or.inl ⟨by rw [h1], by rw [h2]⟩)
  · exact flank_angle hk (Or.inr ⟨by rw [h2], by rw [h1]⟩)

/-! ## §2 Frame facts at `V` -/

theorem hV_eq (F : R1Frame D e f α β γ) : F.h F.V = F.h F.A := by
  rw [F.hV]; exact TraceCovering.f_param rfl F.hhuR _

/-- `VP′` is not parallel to `r` (`P′` is strictly on the near side). -/
theorem cross_uR_PV (F : R1Frame D e f α β γ) : cross F.uR (F.P - F.V) ≠ 0 := by
  intro h0
  have hw := smul_of_cross_zero_unit F.huR h0
  have := congrArg F.h hw
  rw [map_smul, F.hhuR, smul_zero, map_sub, hV_eq F] at this
  have := F.hhP
  linarith

/-- `T₂`'s angle at `V`, as the angle between `A − V` and `P′ − V`, is `β`. -/
theorem T2_angle_V (F : R1Frame D e f α β γ) :
    InnerProductGeometry.angle (F.A - F.V) (F.P - F.V) = β := by
  obtain ⟨i2, -, h2, -, -⟩ := T2_indexed F
  have h2' : Set.range (D.tile i2).pts = {F.V, F.A, F.P} := by
    rw [h2]; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rw [← localAngle_of_range_angle h2']
  exact T2_beta_at_V F h2

/-! ## §3 Step 2: the tile `L′` across `VP′` -/

set_option maxHeartbeats 1000000 in
/-- **R1 step 2 — the single `a`-edge across `VP′`.**  Some tile `L′` not containing `A` (so
`L′ ≠ T₂`) has `V` as a vertex with the flank `P′ − V`, and presents `β` or `γ` at `V`. -/
theorem Lprime_exists (F : R1Frame D e f α β γ) :
    ∃ (j : Fin N) (mj : Fin 3) (W : Plane), (D.tile j).pts mj = F.V ∧
      IsFlankPair (D.tile j) mj F.V (F.P - F.V) W ∧
      ((D.tile j).localAngle F.V = β ∨ (D.tile j).localAngle F.V = γ) ∧
      F.A ∉ (D.tile j).carrier := by
  classical
  have hef := F.hef
  have he := F.he
  have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  have he0 : (0 : ℝ) < e := by linarith
  have hf0 : (0 : ℝ) < f := by linarith
  have ha0 : (0 : ℝ) < (e : ℝ) * f := mul_pos he0 hf0
  have hb0 : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hc0 : (0 : ℝ) < (f : ℝ) ^ 2 := by positivity
  obtain ⟨hab, hac, hbc⟩ := sides_distinct1 F.hco F.he F.hef
  have hee : e ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left (by omega) 2
  -- the unit direction of `VP′`
  have hPV : ‖F.P - F.V‖ = (e : ℝ) * f := by rw [← dist_eq_norm, dist_comm]; exact F.hVP
  set a : ℝ := (e : ℝ) * f with ha
  set u : Plane := a⁻¹ • (F.P - F.V) with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_smul, hPV, Real.norm_of_nonneg (inv_nonneg.mpr ha0.le), inv_mul_cancel₀ ha0.ne']
  have hu0 : u ≠ 0 := TraceCovering.ne_zero_of_norm hu1
  have hVa : F.V + a • u = F.P := by
    rw [hu, smul_smul, mul_inv_cancel₀ ha0.ne', one_smul]; abel
  have hV0 : F.V + (0 : ℝ) • u = F.V := by rw [zero_smul, add_zero]
  -- the normal functional `g` of `VP′`, `T₂` on `{g < g V}`
  have hAV : F.A - F.V = (-((f : ℝ) ^ 2)) • F.uR := by rw [F.hV]; module
  have hcPV := cross_uR_PV F
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = cross u (F.A - F.V) := ⟨_, rfl⟩
  have hσ' : σ = a⁻¹ * (f : ℝ) ^ 2 * cross F.uR (F.P - F.V) := by
    rw [hσ, hu, hAV]
    simp only [cross_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; ring
  have hσ0 : σ ≠ 0 := by
    rw [hσ']; exact mul_ne_zero (mul_ne_zero (inv_ne_zero ha0.ne') hc0.ne') hcPV
  set g : Plane →ₗ[ℝ] ℝ := (-σ) • crossL u with hg
  have happ : ∀ w, g w = -σ * cross u w := fun w => by
    rw [hg, LinearMap.smul_apply, crossL_apply, smul_eq_mul]
  have hgu : g u = 0 := by rw [happ, cross_self, mul_zero]
  have hgAV : g F.A < g F.V := by
    have : g F.A - g F.V = -σ * σ := by rw [← map_sub, happ, ← hσ]
    have : 0 < σ * σ := mul_self_pos.mpr hσ0
    linarith
  have hg0 : g ≠ 0 := by
    intro h0; rw [h0] at hgAV; simp at hgAV
  have hguR : g F.uR ≠ 0 := by
    rw [happ]
    have : cross u F.uR = -(a⁻¹ * cross F.uR (F.P - F.V)) := by
      rw [hu]; simp only [cross_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; ring
    rw [this]
    exact mul_ne_zero (neg_ne_zero.mpr hσ0)
      (neg_ne_zero.mpr (mul_ne_zero (inv_ne_zero ha0.ne') hcPV))
  have hgV : g F.V = g F.V := rfl
  -- `T₂`'s edge `[V, P′]`
  obtain ⟨i2, m2, h2r, hm01, hm2⟩ := T2_indexed F
  have hedgeVP : ∃ k, (D.tile i2).edge k = segment ℝ F.V F.P := by
    rcases hm01 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨m2 + 1, ?_⟩
      rw [Tri.edge, show m2 + 1 + 1 = m2 + 2 from (by decide : ∀ x : Fin 3, x + 1 + 1 = x + 2) _,
        h2, hm2]
    · refine ⟨m2 + 2, ?_⟩
      rw [Tri.edge, show m2 + 2 + 1 = m2 from (by decide : ∀ x : Fin 3, x + 2 + 1 = x) _, hm2, h1]
      exact segment_symm ℝ _ _
  obtain ⟨kVP, hkVP⟩ := hedgeVP
  have hsegVP : segment ℝ F.V F.P = (fun x : ℝ => F.V + x • u) '' Set.Icc 0 a := by
    have := TraceCovering.segment_param (X := F.V) (u := u) 0 a
    rw [hV0, hVa, min_eq_left ha0.le, max_eq_right ha0.le] at this
    exact this
  have hint : ∀ x ∈ Set.Ioo 0 a, F.V + x • u ∈ interior D.target.carrier := by
    intro x hx
    apply (D.target.convex.interior).segment_subset (V_interior F) F.hPint
    rw [hsegVP]; exact ⟨x, ⟨hx.1.le, hx.2.le⟩, rfl⟩
  have hwall : ∀ x ∈ Set.Ioo 0 a, ∀ i, F.V + x • u ∉ interior (D.tile i).carrier := by
    intro x hx i
    have hmem : F.V + x • u ∈ (D.tile i2).edge kVP := by
      rw [hkVP, hsegVP]; exact ⟨x, ⟨hx.1.le, hx.2.le⟩, rfl⟩
    exact D.toDissection.edge_point_not_interior hmem i
  -- start: the piercer crosses the line `VP′` at `V`
  obtain ⟨εp, hεp, hVp, -, -⟩ := piercer F
  have huR1 := F.huR
  have huR0 : F.uR ≠ 0 := TraceCovering.ne_zero_of_norm huR1
  have hhe0 : F.h ((D.tile εp.1).pts εp.2) = F.h F.A := by
    have := (Dissection.mem_lineChain.mp hεp).1
    simpa only [LinearMap.neg_apply, neg_inj] using this
  have hhe1 : F.h ((D.tile εp.1).pts (εp.2 + 1)) = F.h F.A := by
    have := (Dissection.mem_lineChain.mp hεp).2.1
    simpa only [LinearMap.neg_apply, neg_inj] using this
  obtain ⟨μ, hμ⟩ := TraceCovering.exists_param F.hh0 (hV_eq F) F.hhuR huR0 hhe0
  obtain ⟨ν, hν⟩ := TraceCovering.exists_param F.hh0 (hV_eq F) F.hhuR huR0 hhe1
  have hμν : μ ≠ ν := by
    intro h
    apply (D.tile εp.1).indep.injective.ne (TraceCovering.fin3_succ_ne εp.2)
    rw [hμ, hν, h]
  have hμν0 : μ * ν < 0 := by
    have hV' := hVp
    rw [hμ, hν, TraceCovering.openSegment_param hμν] at hV'
    obtain ⟨x, hx, hxV⟩ := hV'
    have hx0 : x = 0 := by
      have : F.V + x • F.uR = F.V + (0 : ℝ) • F.uR := by rw [zero_smul, add_zero]; exact hxV
      exact TraceCovering.lm_injective (X := F.V) huR0 this
    subst hx0
    rcases le_total μ ν with h | h
    · rw [min_eq_left h, max_eq_right h] at hx; nlinarith [hx.1, hx.2]
    · rw [min_eq_right h, max_eq_left h] at hx; nlinarith [hx.1, hx.2]
  have hge0 : g ((D.tile εp.1).pts εp.2) = g F.V + μ * g F.uR := by
    rw [hμ, map_add, map_smul, smul_eq_mul]
  have hge1 : g ((D.tile εp.1).pts (εp.2 + 1)) = g F.V + ν * g F.uR := by
    rw [hν, map_add, map_smul, smul_eq_mul]
  have hprod : (μ * g F.uR) * (ν * g F.uR) < 0 := by
    have : (μ * g F.uR) * (ν * g F.uR) = (μ * ν) * (g F.uR * g F.uR) := by ring
    rw [this]; exact mul_neg_of_neg_of_pos hμν0 (mul_self_pos.mpr hguR)
  have hVmem : F.V ∈ (D.tile εp.1).carrier :=
    (D.tile εp.1).edge_subset_carrier εp.2 (by rw [Tri.edge]; exact openSegment_subset_segment ℝ _ _ hVp)
  have he0mem : (D.tile εp.1).pts εp.2 ∈ (D.tile εp.1).carrier :=
    subset_convexHull ℝ _ (Set.mem_range_self _)
  have he1mem : (D.tile εp.1).pts (εp.2 + 1) ∈ (D.tile εp.1).carrier :=
    subset_convexHull ℝ _ (Set.mem_range_self _)
  have hμg : μ * g F.uR ≠ 0 := by
    intro h; rw [h, zero_mul] at hprod; exact lt_irrefl _ hprod
  have hnear : ∀ δ : ℝ, δ > 0 → ∃ x : ℝ, |x - 0| < δ ∧
      ∃ i, F.V + x • u ∈ interior (D.tile i).carrier := by
    intro δ hδ
    have hY : F.V + (0 : ℝ) • u ∈ (D.tile εp.1).carrier := by rw [hV0]; exact hVmem
    rcases lt_or_gt_of_ne hμg with hneg | hpos
    · have hpos' : 0 < ν * g F.uR := by
        by_contra hc; push Not at hc; nlinarith
      obtain ⟨x, hx, hxi⟩ := TraceCovering.near_interior_of_across (D.tile εp.1) hg0 hgV hgu hu0
        hY he0mem he1mem (by rw [hge0]; linarith) (by rw [hge1]; linarith) δ hδ
      exact ⟨x, hx, εp.1, hxi⟩
    · have hneg' : ν * g F.uR < 0 := by
        by_contra hc; push Not at hc; nlinarith
      obtain ⟨x, hx, hxi⟩ := TraceCovering.near_interior_of_across (D.tile εp.1) hg0 hgV hgu hu0
        hY he1mem he0mem (by rw [hge1]; linarith) (by rw [hge0]; linarith) δ hδ
      exact ⟨x, hx, εp.1, hxi⟩
  have hs := TraceCovering.not_straddled_of_near_interior (D := D.toDissection) (g := -g)
    (d := -(g F.V)) TraceCovering.neg_iff hg0 hgV hgu hu0 (x₀ := 0) hnear
  -- end: no edge passes through `P′`
  have hend : ¬ TraceCovering.Straddled D.toDissection (-g) (-(g F.V)) (F.V + a • u) := by
    rw [hVa]
    rintro ⟨ε, -, hε⟩
    apply no_straight_at_pprime F ε.1
    have e1' : ε.2 + 2 + 1 = ε.2 := (by decide : ∀ x : Fin 3, x + 2 + 1 = x) _
    have e2' : ε.2 + 2 + 2 = ε.2 + 1 := (by decide : ∀ x : Fin 3, x + 2 + 2 = x + 1) _
    apply Erdos634.RouteOne.openSegment_localAngle_pi (D.tile ε.1) (ε.2 + 2)
    rw [e1', e2']; exact hε
  -- TRACE COVERING on `[V, P′]`, non-`T₂` side
  have hsum := TraceCovering.wall_sum (D := D.toDissection) (g := -g) (d := -(g F.V)) (f := g)
    (c := g F.V) (X := F.V) (u := u) (neg_ne_zero.mpr hg0) TraceCovering.neg_iff hg0 hgV hgu hu1
    ha0.le hint hwall hs hend
  set sF := (D.toDissection.lineChain (-g) (-(g F.V))).filter
    (fun e => (D.toDissection.tile e.1).edge e.2 ⊆
      segment ℝ (F.V + (0 : ℝ) • u) (F.V + a • u)) with hsF
  have hne : sF.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h0; rw [h0, Finset.sum_empty] at hsum; linarith
  obtain ⟨ε₀, hε₀⟩ := hne
  rw [← Finset.add_sum_erase sF _ hε₀] at hsum
  obtain ⟨P', Q', R', hPQR, -⟩ := sum_three_values (sF.erase ε₀)
    (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
    ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)
    (fun ε _ => edge_len_mem D F.hM.hs0 F.hM.hs1 F.hM.hs2 ε.1 ε.2)
  have hlen0 : dist ((D.tile ε₀.1).pts ε₀.2) ((D.tile ε₀.1).pts (ε₀.2 + 1)) = a := by
    rcases edge_len_mem D F.hM.hs0 F.hM.hs1 F.hM.hs2 ε₀.1 ε₀.2 with h | h | h
    · exact h
    · exfalso
      have hnat : P' * (e * f) + (Q' + 1) * (f ^ 2 - e ^ 2) + R' * f ^ 2 = e * f := by
        have : ((P' * (e * f) + (Q' + 1) * (f ^ 2 - e ^ 2) + R' * f ^ 2 : ℕ) : ℝ)
            = ((e * f : ℕ) : ℝ) := by
          push_cast [Nat.cast_sub hee]
          rw [h] at hsum
          linarith
        exact_mod_cast this
      have := (ThickEFminus1Steps.a_rep_unique e f P' (Q' + 1) R' (f ^ 2 - e ^ 2) he hef F.hco
        (by omega) hnat).2.1
      omega
    · exfalso
      have hnat : P' * (e * f) + Q' * (f ^ 2 - e ^ 2) + (R' + 1) * f ^ 2 = e * f := by
        have : ((P' * (e * f) + Q' * (f ^ 2 - e ^ 2) + (R' + 1) * f ^ 2 : ℕ) : ℝ)
            = ((e * f : ℕ) : ℝ) := by
          push_cast [Nat.cast_sub hee]
          rw [h] at hsum
          linarith
        exact_mod_cast this
      have := (ThickEFminus1Steps.a_rep_unique e f P' Q' (R' + 1) (f ^ 2 - e ^ 2) he hef F.hco
        (by omega) hnat).2.2
      omega
  -- the edge `ε₀` is exactly `[V, P′]`
  have hε₀c : ε₀ ∈ D.toDissection.lineChain (-g) (-(g F.V)) := (Finset.mem_filter.mp hε₀).1
  have hε₀s := (Finset.mem_filter.mp hε₀).2
  obtain ⟨hon0, hon1⟩ := TraceCovering.onLine TraceCovering.neg_iff hε₀c
  obtain ⟨-, -, -, hdlh⟩ := TraceCovering.edge_data hg0 hgV hgu hu0 hon0 hon1
  have hdl := hdlh hu1
  have hin := (TraceCovering.inside_iff TraceCovering.neg_iff hg0 hgV hgu hu0 hε₀c ha0.le).mp hε₀s
  rw [hlen0] at hdl
  have hlo : TraceCovering.lo D.toDissection F.V u ε₀ = 0 := by linarith [hin.1, hin.2]
  have hhi : TraceCovering.hi D.toDissection F.V u ε₀ = a := by linarith [hin.1, hin.2]
  have hp0 := TraceCovering.par_spec (TraceCovering.exists_param hg0 hgV hgu hu0 hon0)
  have hp1 := TraceCovering.par_spec (TraceCovering.exists_param hg0 hgV hgu hu0 hon1)
  simp only [TraceCovering.lo, TraceCovering.hi] at hlo hhi
  -- `A` is not in `L′` (it lies on the `T₂` side)
  have hAnot : F.A ∉ (D.tile ε₀.1).carrier := by
    intro hA
    have := (D.tile ε₀.1).carrier_subset_halfplane (-g) (-(g F.V))
      (Dissection.mem_lineChain.mp hε₀c).2.2 F.A hA
    simp only [LinearMap.neg_apply, neg_le_neg_iff] at this
    linarith
  -- the flank at `V`, and the angle there
  have hcase : ∃ (mj : Fin 3) (W : Plane), (D.tile ε₀.1).pts mj = F.V ∧
      IsFlankPair (D.tile ε₀.1) mj F.V (F.P - F.V) W := by
    rcases le_total (TraceCovering.par F.V u ((D.tile ε₀.1).pts ε₀.2))
        (TraceCovering.par F.V u ((D.tile ε₀.1).pts (ε₀.2 + 1))) with hle | hle
    · rw [min_eq_left hle] at hlo; rw [max_eq_right hle] at hhi
      rw [hlo, hV0] at hp0; rw [hhi, hVa] at hp1
      exact ⟨ε₀.2, (D.tile ε₀.1).pts (ε₀.2 + 2) - F.V, hp0, Or.inl ⟨by rw [hp1], rfl⟩⟩
    · rw [min_eq_right hle] at hlo; rw [max_eq_left hle] at hhi
      rw [hlo, hV0] at hp1; rw [hhi, hVa] at hp0
      refine ⟨ε₀.2 + 1, (D.tile ε₀.1).pts (ε₀.2 + 1 + 1) - F.V, hp1, Or.inr ⟨?_, rfl⟩⟩
      rw [show ε₀.2 + 1 + 2 = ε₀.2 from (by decide : ∀ x : Fin 3, x + 1 + 2 = x) _, hp0]
  obtain ⟨mj, W, hmj, hUW⟩ := hcase
  refine ⟨ε₀.1, mj, W, hmj, hUW, ?_, hAnot⟩
  have hmem := vertex_angle_mem D F.hM.hα' F.hM.hβ' F.hM.hγ' ε₀.1 mj
  rw [hmj] at hmem
  rcases hmem with h | h | h
  · exfalso
    obtain ⟨hn, -⟩ := (corner_data1 D F.hco F.he F.hef F.hM F.hAng hmj hUW).1 h
    rw [hPV] at hn
    rcases hn with ⟨hn, -⟩ | ⟨hn, -⟩
    · exact hab hn
    · exact hac hn
  · exact Or.inl h
  · exact Or.inr h

/-! ## §4 The corner against `ρ` -/

set_option maxHeartbeats 1000000 in
/-- **The corner `Z` against `ρ`.**  Some tile `Z` has a corner at `V` with one flank `U′` positively
along `u_r` (`u_r = S·U′`, `S > 0`) and the other `W′` strictly on `P′`'s side of `r`. -/
theorem Z_exists (F : R1Frame D e f α β γ) :
    ∃ (j : Fin N) (mj : Fin 3) (U' W' : Plane) (S : ℝ), (D.tile j).pts mj = F.V ∧
      IsFlankPair (D.tile j) mj F.V U' W' ∧ 0 < S ∧ F.uR = S • U' ∧
      cross F.uR W' * cross F.uR (F.V - F.P) < 0 := by
  classical
  have huR1 := F.huR
  have huR0 : F.uR ≠ 0 := TraceCovering.ne_zero_of_norm huR1
  have hcPV := cross_uR_PV F
  have hΔ : cross F.uR (F.V - F.P) ≠ 0 := by
    have : cross F.uR (F.V - F.P) = -cross F.uR (F.P - F.V) := by
      simp only [cross_apply, PiLp.sub_apply]; ring
    rw [this]; exact neg_ne_zero.mpr hcPV
  have hVint := V_interior F
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hVint)
  obtain ⟨i2, -, -, -, -⟩ := T2_indexed F
  have hN : 0 < N := Fin.pos i2
  set Dn : ℕ → Plane := fun n => F.uR - (1 / ((n : ℝ) + (1 : ℕ))) • (F.V - F.P) with hDn
  have hDn0 : ∀ n, Dn n ≠ 0 := by
    intro n h0
    have hk : (0 : ℝ) < 1 / ((n : ℝ) + ((1 : ℕ) : ℝ)) := by positivity
    have hc : cross F.uR (Dn n)
        = -(1 / ((n : ℝ) + ((1 : ℕ) : ℝ))) * cross F.uR (F.V - F.P) := by
      rw [hDn]; simp only [cross_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [h0] at hc
    have hz : cross F.uR (0 : Plane) = 0 := by simp [cross_apply]
    rw [hz] at hc
    exact mul_ne_zero (neg_ne_zero.mpr hk.ne') hΔ hc.symm
  -- approach directions are covered
  have hcovn : ∀ n : ℕ, ∃ (j : Fin N) (ε : ℝ), 0 < ε ∧ F.V ∈ (D.tile j).carrier ∧
      F.V + ε • (F.uR - (1 / ((n : ℝ) + (1 : ℕ))) • (F.V - F.P)) ∈ (D.tile j).carrier := by
    intro n
    have hD0 := hDn0 n
    have hnD : 0 < ‖Dn n‖ := norm_pos_iff.mpr hD0
    obtain ⟨j, ε, hε, h1, h2⟩ := cover_tile_dir D.tile F.V hN hD0 (τ₀ := r / (2 * ‖Dn n‖))
      (by positivity) (fun τ hτ hτ0 => by
        rw [D.covers]
        apply hball
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
          Real.norm_of_nonneg hτ.le]
        have : τ * ‖Dn n‖ ≤ r / 2 := by
          calc τ * ‖Dn n‖ ≤ r / (2 * ‖Dn n‖) * ‖Dn n‖ := mul_le_mul_of_nonneg_right hτ0 hnD.le
            _ = r / 2 := by rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hnD.ne']
        linarith)
    exact ⟨j, ε, hε, h1, h2⟩
  -- the piercer's edge through `V`, in the parametrization of `r` from `V`
  have hstr := V_pierced F
  have hstr' : TraceCovering.Straddled D.toDissection (-F.h) (-(F.h F.A))
      (F.V + (0 : ℝ) • F.uR) := by rw [zero_smul, add_zero]; exact hstr
  rw [TraceCovering.str_iff TraceCovering.neg_iff F.hh0 (hV_eq F) F.hhuR huR0] at hstr'
  obtain ⟨εp, hεp, hlo, hhi⟩ := hstr'
  -- the tiles containing `V`, reindexed
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin N),
      S = Finset.univ.filter (fun j => F.V ∈ (D.tile j).carrier) := ⟨_, rfl⟩
  have hmemS : ∀ j, j ∈ S ↔ F.V ∈ (D.tile j).carrier := by
    intro j; rw [hS]; simp
  obtain ⟨em⟩ : Nonempty (Fin S.card ≃ S) := ⟨S.equivFin.symm⟩
  obtain ⟨T', hT'⟩ : ∃ T' : Fin S.card → Tri, ∀ k, T' k = D.tile (em k).1 := ⟨_, fun _ => rfl⟩
  have hVT' : ∀ k, F.V ∈ (T' k).carrier := fun k => by
    rw [hT']; exact (hmemS _).mp (em k).2
  have hcovn' : ∀ n : ℕ, ∃ (k : Fin S.card) (ε : ℝ), 0 < ε ∧ F.V ∈ (T' k).carrier ∧
      F.V + ε • (F.uR - (1 / ((n : ℝ) + (1 : ℕ))) • (F.V - F.P)) ∈ (T' k).carrier := by
    intro n
    obtain ⟨j, ε, hε, h1, h2⟩ := hcovn n
    have hjS : j ∈ S := (hmemS j).mpr h1
    refine ⟨em.symm ⟨j, hjS⟩, ε, hε, ?_, ?_⟩
    · rw [hT', Equiv.apply_symm_apply]; exact h1
    · rw [hT', Equiv.apply_symm_apply]; exact h2
  have hy_near : ∀ (n : ℕ) (ε : ℝ), 0 < ε →
      F.h (F.V + ε • (F.uR - (1 / ((n : ℝ) + (1 : ℕ))) • (F.V - F.P))) < F.h F.A := by
    intro n ε hε
    have hk : (0 : ℝ) < 1 / ((n : ℝ) + ((1 : ℕ) : ℝ)) := by positivity
    have e : F.h (F.V + ε • (F.uR - (1 / ((n : ℝ) + (1 : ℕ))) • (F.V - F.P)))
        = F.h F.A - ε * (1 / ((n : ℝ) + (1 : ℕ))) * (F.h F.A - F.h F.P) := by
      simp only [map_add, map_smul, map_sub, F.hhuR, smul_eq_mul]
      rw [hV_eq F]; ring
    rw [e]
    have : 0 < ε * (1 / ((n : ℝ) + (1 : ℕ))) * (F.h F.A - F.h F.P) :=
      mul_pos (mul_pos hε hk) (by linarith [F.hhP])
    linarith
  have hopen' : ∀ k : Fin S.card, (∃ (n : ℕ) (ε : ℝ), 0 < ε ∧
        F.V + ε • (F.uR - (1 / ((n : ℝ) + (1 : ℕ))) • (F.V - F.P)) ∈ (T' k).carrier) →
      ∀ s t τ : ℝ, 0 < s → 0 < t → 0 < τ → τ * (s + t) < 1 →
        F.V + τ • (s • F.uR + t • (F.V - F.P)) ∉ interior (T' k).carrier := by
    rintro k ⟨n, ε, hε, hy⟩ s t τ hs ht hτ - hz
    have hqc : F.h F.A < F.h (F.V + τ • (s • F.uR + t • (F.V - F.P))) := by
      have e : F.h (F.V + τ • (s • F.uR + t • (F.V - F.P)))
          = F.h F.A + τ * t * (F.h F.A - F.h F.P) := by
        simp only [map_add, map_smul, map_sub, F.hhuR, smul_eq_mul]
        rw [hV_eq F]; ring
      rw [e]
      have : 0 < τ * t * (F.h F.A - F.h F.P) := mul_pos (mul_pos hτ ht) (by linarith [F.hhP])
      linarith
    have hY : F.V + (0 : ℝ) • F.uR ∈ (T' k).carrier := by rw [zero_smul, add_zero]; exact hVT' k
    obtain ⟨x, hx, hxi⟩ := TraceCovering.near_interior_of_across (T' k) F.hh0 (hV_eq F) F.hhuR
      huR0 hY hy (interior_subset hz) (hy_near n ε hε) hqc
      (min (-(TraceCovering.lo D.toDissection F.V F.uR εp))
        (TraceCovering.hi D.toDissection F.V F.uR εp)) (lt_min (by linarith) hhi)
    rw [sub_zero] at hx
    have hx1 := lt_of_lt_of_le hx (min_le_left _ _)
    have hx2 := lt_of_lt_of_le hx (min_le_right _ _)
    rw [abs_lt] at hx1 hx2
    have hmem : F.V + x • F.uR ∈ (D.tile εp.1).edge εp.2 :=
      (TraceCovering.mem_edge_iff TraceCovering.neg_iff F.hh0 (hV_eq F) F.hhuR huR0 hεp x).mpr
        ⟨by linarith, by linarith⟩
    rw [hT'] at hxi
    exact D.toDissection.edge_point_not_interior hmem (em k).1 hxi
  obtain ⟨k, -, ⟨n, ε, hε, hy⟩, hcase⟩ := flank_neighbour_gen T' F.V hΔ 1 le_rfl hcovn' hopen'
  rw [hT'] at hy
  rcases hcase with ⟨m', hm', U', W', hUW', S', hS', hU, hside⟩ | ⟨m', h0, hpos, -, -⟩
  · rw [hT'] at hm' hUW'
    exact ⟨(em k).1, m', U', W', S', hm', hUW', hS', hU, hside⟩
  · exfalso
    rw [hT'] at h0 hpos
    have hπ : (D.tile (em k).1).localAngle F.V = Real.pi :=
      Erdos634.RouteOne.localAngle_pi_of_coords _ _ m' h0 hpos
    obtain ⟨εq, -, -, hπq, hfarq⟩ := piercer F
    obtain ⟨i2', -, h2', -, -⟩ := T2_indexed F
    obtain ⟨hc1, -, -⟩ := fill_at_V F hπq (T2_beta_at_V F h2')
    have heq : (em k).1 = εq.1 := by
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hc1
      have h1 : (em k).1 ∈ ({i | (D.tile i).localAngle F.V = Real.pi} : Finset (Fin N)) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hπ
      have h2 : εq.1 ∈ ({i | (D.tile i).localAngle F.V = Real.pi} : Finset (Fin N)) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hπq
      rw [hx, Finset.mem_singleton] at h1 h2
      rw [h1, h2]
    have hy' : F.V + ε • (F.uR - (1 / ((n : ℝ) + (1 : ℕ))) • (F.V - F.P))
        ∈ (D.tile εq.1).carrier := by rw [← heq]; exact hy
    have := hfarq _ hy'
    have := hy_near n ε hε
    linarith

/-! ## §5 Step 3: the census forces `Z` to be an `α`-corner -/

/-- **R1 step 3.**  Given `T₂` (`β` at `V`), `L′` (`β` or `γ`), and a third tile `Z` at `V` distinct
from both, the fill `π − β` (`fill_at_V`) and irrationality force `Z` to present `α`. -/
theorem Z_alpha (F : R1Frame D e f α β γ) {i2 L Z : Fin N}
    (h2 : (D.tile i2).localAngle F.V = β)
    (hL : (D.tile L).localAngle F.V = β ∨ (D.tile L).localAngle F.V = γ)
    (hZ : (D.tile Z).localAngle F.V = α ∨ (D.tile Z).localAngle F.V = β ∨
      (D.tile Z).localAngle F.V = γ)
    (hZ2 : Z ≠ i2) (hZL : Z ≠ L) (hL2 : L ≠ i2) : (D.tile Z).localAngle F.V = α := by
  classical
  obtain ⟨εq, -, -, hπq, -⟩ := piercer F
  obtain ⟨-, -, hfill⟩ := fill_at_V F hπq h2
  have hA := F.hAng
  set sα := ({i | (D.tile i).localAngle F.V = α} : Finset (Fin N)) with hsα
  set sβ := ({i | (D.tile i).localAngle F.V = β} : Finset (Fin N)) with hsβ
  set sγ := ({i | (D.tile i).localAngle F.V = γ} : Finset (Fin N)) with hsγ
  have mem : ∀ {s : Finset (Fin N)} {v : ℝ} {i : Fin N},
      s = ({i | (D.tile i).localAngle F.V = v} : Finset (Fin N)) →
      (D.tile i).localAngle F.V = v → i ∈ s := by
    intro s v i hs hi; rw [hs]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hi
  have h2m : i2 ∈ sβ := mem hsβ h2
  have hβ1 : 1 ≤ sβ.card := Finset.card_pos.mpr ⟨i2, h2m⟩
  have hsum : (sα.card : ℝ) * α + ((sβ.card - 1 : ℕ) : ℝ) * β + (sγ.card : ℝ) * (2 * α + β)
      = ((3 : ℤ) : ℝ) * α + ((1 : ℤ) : ℝ) * β := by
    rw [Nat.cast_sub hβ1, ← hA.hγdef]
    push_cast
    have := hA.hrel
    linarith
  obtain ⟨-, hc2⟩ := vertex_multiplicities hA.hrel hA.hirr _ _ _ 3 1 hsum
  have hc2' : sβ.card - 1 + sγ.card = 1 := by omega
  rcases hZ with h | h | h
  · exact h
  · exfalso
    have hZm : Z ∈ sβ := mem hsβ h
    rcases hL with hl | hl
    · have : 2 < sβ.card := Finset.two_lt_card.mpr
        ⟨i2, h2m, Z, hZm, L, mem hsβ hl, hZ2.symm, hL2.symm, hZL⟩
      omega
    · have : 1 < sβ.card := Finset.one_lt_card.mpr ⟨i2, h2m, Z, hZm, hZ2.symm⟩
      have : 0 < sγ.card := Finset.card_pos.mpr ⟨L, mem hsγ hl⟩
      omega
  · exfalso
    have hZm : Z ∈ sγ := mem hsγ h
    rcases hL with hl | hl
    · have : 1 < sβ.card := Finset.one_lt_card.mpr ⟨i2, h2m, L, mem hsβ hl, hL2.symm⟩
      have : 0 < sγ.card := Finset.card_pos.mpr ⟨Z, hZm⟩
      omega
    · have : 1 < sγ.card := Finset.one_lt_card.mpr ⟨Z, hZm, L, mem hsγ hl, hZL⟩
      omega

/-! ## §6 Step 4: the depth exit -/

/-- The depth inequality `f·b < 2c` holds on the thick line `e = f − 1` (`f ≥ 2`). -/
theorem depth_thick {e f : ℕ} (hef1 : e + 1 = f) :
    (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) < 2 * (f : ℝ) ^ 2 := by
  have h : (e : ℝ) = f - 1 := by
    have : ((e + 1 : ℕ) : ℝ) = f := by exact_mod_cast hef1
    push_cast at this; linarith
  rw [h]
  have hf : (1 : ℝ) ≤ f := by exact_mod_cast (show 1 ≤ f by omega)
  nlinarith

/-- A point whose cone coordinates sum to more than `1` is outside the target. -/
theorem out_of_cone (F : R1Frame D e f α β γ) {X : Plane} {x y : ℝ}
    (hX : X - F.A = x • (((f : ℝ) ^ 3) • F.uL) + y • (F.R - F.A)) (hxy : 1 < x + y) :
    X ∉ D.target.carrier := by
  have := F.hout x y hxy
  rwa [show F.A + (x • (((f : ℝ) ^ 3) • F.uL) + y • (F.R - F.A)) = X by rw [← hX]; abel] at this

set_option maxHeartbeats 1000000 in
/-- **R1 on the frame: no real dissection carries the frame when `f·b < 2c`** (i.e. on the line
`e = f − 1`, `depth_thick`).  Steps 1–4 of `proof_R1_compressed.md`. -/
theorem r1_frame_false (F : R1Frame D e f α β γ)
    (hdepth : (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) < 2 * (f : ℝ) ^ 2) : False := by
  classical
  have hef := F.hef
  have he := F.he
  have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  have he0 : (0 : ℝ) < e := by linarith
  have hf0 : (0 : ℝ) < f := by linarith
  have hb0 : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hc0 : (0 : ℝ) < (f : ℝ) ^ 2 := by positivity
  -- the tiles at `V`
  obtain ⟨i2, -, h2r, -, -⟩ := T2_indexed F
  have h2β := T2_beta_at_V F h2r
  obtain ⟨L, mL, WL, hmL, hUWL, hLang, hLA⟩ := Lprime_exists F
  obtain ⟨Z, mZ, U', W', S, hmZ, hUWZ, hS, hU', hside⟩ := Z_exists F
  have hAi2 : F.A ∈ (D.tile i2).carrier :=
    subset_convexHull ℝ _ (by rw [h2r]; exact Set.mem_insert _ _)
  have hL2 : L ≠ i2 := by rintro rfl; exact hLA hAi2
  have hU'0 : U' ≠ 0 := by
    rintro rfl; rw [smul_zero] at hU'; exact TraceCovering.ne_zero_of_norm F.huR hU'
  have hhU' : F.h U' = 0 := by
    have := congrArg F.h hU'
    rw [F.hhuR, map_smul, smul_eq_mul] at this
    rcases mul_eq_zero.mp this.symm with h | h
    · linarith
    · exact h
  have hhPV : F.h (F.P - F.V) ≠ 0 := by rw [map_sub, hV_eq F]; linarith [F.hhP]
  have hVA : F.V - F.A = ((f : ℝ) ^ 2) • F.uR := by rw [F.hV]; abel
  -- `Z ≠ T₂`: `T₂`'s flanks at `V` are `A − V` (antiparallel to `u_r`) and `P′ − V` (off `r`)
  have hZ2 : Z ≠ i2 := by
    intro hZi
    rw [hZi] at hmZ hUWZ
    have hr := range_of_flank hmZ hUWZ
    have hX : F.V + U' ∈ ({F.A, F.V, F.P} : Set Plane) := by rw [← h2r, hr]; simp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with hX | hX | hX
    · have hUA : U' = (-((f : ℝ) ^ 2)) • F.uR := by
        rw [show U' = F.A - F.V by rw [← hX]; abel, F.hV]; module
      rw [hUA, smul_smul] at hU'
      have h1 : (1 - S * -((f : ℝ) ^ 2)) • F.uR = 0 := by
        rw [sub_smul, one_smul, ← hU', sub_self]
      rcases smul_eq_zero.mp h1 with h | h
      · nlinarith
      · exact TraceCovering.ne_zero_of_norm F.huR h
    · exact hU'0 (by simpa using hX)
    · apply hhPV
      rw [show F.P - F.V = U' by rw [← hX]; abel]; exact hhU'
  -- `Z ≠ L′`: otherwise `Z`'s angle would be `π − β`
  have hZang := vertex_angle_mem D F.hM.hα' F.hM.hβ' F.hM.hγ' Z mZ
  rw [hmZ] at hZang
  have hZL : Z ≠ L := by
    intro hZLe
    rw [← hZLe] at hmL hUWL
    have hmm : mZ = mL := (D.tile Z).indep.injective (hmZ.trans hmL.symm)
    rw [← hmm] at hUWL
    rcases flank_cases hUWL hUWZ with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact hhPV (by rw [← h1]; exact hhU')
    · have hang : (D.tile Z).localAngle F.V = Real.pi - β := by
        rw [flank_angle hmZ hUWZ, h2]
        have e1 : U' = S⁻¹ • F.uR := by rw [hU', smul_smul, inv_mul_cancel₀ hS.ne', one_smul]
        rw [e1, InnerProductGeometry.angle_smul_left_of_pos _ _ (inv_pos.mpr hS)]
        have e2 : F.A - F.V = ((f : ℝ) ^ 2) • (-F.uR) := by rw [F.hV]; module
        have := T2_angle_V F
        rw [e2, InnerProductGeometry.angle_smul_left_of_pos _ _ hc0,
          InnerProductGeometry.angle_neg_left] at this
        linarith
      have hA := F.hAng
      have := hA.hrel
      have := hA.hγdef
      have := hA.hα
      have := hA.hβ
      rcases hZang with h | h | h <;> rw [h] at hang <;> linarith
  -- step 3: `Z` presents `α`
  have hZα := Z_alpha F h2β hLang hZang hZ2 hZL hL2
  obtain ⟨hnorm, hopp⟩ := (corner_data1 D F.hco F.he F.hef F.hM F.hAng hmZ hUWZ).1 hZα
  -- `Z`'s vertices lie in the target
  have hr := range_of_flank hmZ hUWZ
  have hmemZ : ∀ X ∈ ({F.V, F.V + U', F.V + W'} : Set Plane), X ∈ D.target.carrier := by
    intro X hX
    rw [← hr] at hX
    exact tile_sub_target D.toDissection Z (subset_convexHull ℝ _ hX)
  have hU'n : U' = S⁻¹ • F.uR := by rw [hU', smul_smul, inv_mul_cancel₀ hS.ne', one_smul]
  have hnU' : ‖U'‖ = S⁻¹ := by
    rw [hU'n, norm_smul, F.huR, mul_one, Real.norm_of_nonneg (inv_nonneg.mpr hS.le)]
  obtain ⟨s1, t1, -, -, hVc, hst1⟩ := F.hVc
  obtain ⟨s3, t3, -, -, hPc, hst3⟩ := F.hPc
  have hfb : (1 : ℝ) < 2 * (f : ℝ) ^ 2 / (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * f) := by
    rw [lt_div_iff₀ (mul_pos hb0 hf0)]; linarith
  rcases hnorm with ⟨hUb, hWc⟩ | ⟨hUc, -⟩
  · -- `b` along `ρ`, `c` along the other flank: that flank is the direction of `AP′`
    have hSb : S⁻¹ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by rw [← hnU', hUb]
    have hUe : U' = ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR := by rw [hU'n, hSb]
    have hGn : ‖F.P - F.A‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
      rw [← dist_eq_norm, dist_comm]; exact F.hAP
    have hcG : ‖((f : ℝ) ^ 2) • F.uR - (F.P - F.A)‖ = (e : ℝ) * f := by
      rw [← hVA, show F.V - F.A - (F.P - F.A) = F.V - F.P by abel, ← dist_eq_norm]
      exact F.hVP
    have hUW : ‖U' - W'‖ = (e : ℝ) * f := by
      rw [← hopp, dist_eq_norm, show F.V + U' - (F.V + W') = U' - W' by abel]
    have hside' : 0 < cross F.uR W' * cross F.uR (F.P - F.A) := by
      have e3 : cross F.uR (F.V - F.P) = -cross F.uR (F.P - F.A) := by
        rw [show F.V - F.P = ((f : ℝ) ^ 2) • F.uR - (F.P - F.A) by rw [← hVA]; abel]
        simp only [cross_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
      rw [e3] at hside
      nlinarith
    have hu := norm_sq_coords F.uR
    have hw := norm_sq_coords W'
    have hg := norm_sq_coords (F.P - F.A)
    have h3 := norm_sq_coords (U' - W')
    have h5 := norm_sq_coords (((f : ℝ) ^ 2) • F.uR - (F.P - F.A))
    rw [F.huR, one_pow] at hu
    rw [hWc] at hw
    rw [hGn] at hg
    rw [hUW, hUe] at h3
    rw [hcG] at h5
    rw [cross_apply, cross_apply] at hside'
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at h3 h5 hg hside'
    obtain ⟨hw0, hw1⟩ := coord_align hb0 hc0 hu.symm hw.symm h3.symm hg.symm h5.symm hside'
    have hWG : W' = ((f : ℝ) ^ 2 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • (F.P - F.A) := by
      ext i; fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
        rw [div_mul_eq_mul_div, eq_div_iff hb0.ne']; linarith
      · simp only [Fin.mk_one, Fin.isValue, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
        rw [div_mul_eq_mul_div, eq_div_iff hb0.ne']; linarith
    set κ : ℝ := (f : ℝ) ^ 2 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) with hκ
    have hκb : κ * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) = (f : ℝ) ^ 2 := by
      rw [hκ, div_mul_cancel₀ _ hb0.ne']
    have e1 : F.V + W' - F.A = κ • (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR) + κ • (F.P - F.A) := by
      rw [hWG, smul_smul, hκb, F.hV]; module
    have e2 : F.V + W' - F.A = (κ * (s1 + s3)) • (((f : ℝ) ^ 3) • F.uL)
        + (κ * (t1 + t3)) • (F.R - F.A) := by
      rw [e1, hVc, hPc]; module
    have hsum : 1 < κ * (s1 + s3) + κ * (t1 + t3) := by
      have : κ * (s1 + s3) + κ * (t1 + t3)
          = 2 * (f : ℝ) ^ 2 / (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * f) := by
        rw [← mul_add, show s1 + s3 + (t1 + t3) = (s1 + t1) + (s3 + t3) by ring, hst1, hst3, hκ,
          show 1 / (f : ℝ) + 1 / (f : ℝ) = 2 / (f : ℝ) by ring, div_mul_div_comm, mul_comm _ (2 : ℝ)]
      rw [this]; exact hfb
    exact out_of_cone F e2 hsum (hmemZ _ (by simp))
  · -- `c` along `ρ`
    have hSc : S⁻¹ = (f : ℝ) ^ 2 := by rw [← hnU', hUc]
    have hUe : U' = ((f : ℝ) ^ 2) • F.uR := by rw [hU'n, hSc]
    set κ : ℝ := 2 * (f : ℝ) ^ 2 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) with hκ
    have hκb : κ * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) = 2 * (f : ℝ) ^ 2 := by
      rw [hκ, div_mul_cancel₀ _ hb0.ne']
    have e1 : F.V + U' - F.A = κ • (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR) := by
      rw [hUe, smul_smul, hκb, F.hV]; module
    have e2 : F.V + U' - F.A = (κ * s1) • (((f : ℝ) ^ 3) • F.uL) + (κ * t1) • (F.R - F.A) := by
      rw [e1, hVc]; module
    have hsum : 1 < κ * s1 + κ * t1 := by
      have : κ * s1 + κ * t1 = 2 * (f : ℝ) ^ 2 / (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * f) := by
        rw [← mul_add, hst1, hκ, div_mul_div_comm, mul_one]
      rw [this]; exact hfb
    exact out_of_cone F e2 hsum (hmemZ _ (by simp))

/-- **R1 on the frame, thick line: `e + 1 = f`.** -/
theorem r1_frame_false_thick (F : R1Frame D e f α β γ) (hef1 : e + 1 = f) : False :=
  r1_frame_false F (depth_thick hef1)

end Erdos634.Draft.R1Kill

#print axioms Erdos634.Draft.R1Kill.smul_of_cross_zero_unit
#print axioms Erdos634.Draft.R1Kill.coord_align
#print axioms Erdos634.Draft.R1Kill.corner_data1
#print axioms Erdos634.Draft.R1Kill.Lprime_exists
#print axioms Erdos634.Draft.R1Kill.Z_exists
#print axioms Erdos634.Draft.R1Kill.Z_alpha
#print axioms Erdos634.Draft.R1Kill.r1_frame_false
#print axioms Erdos634.Draft.R1Kill.r1_frame_false_thick
