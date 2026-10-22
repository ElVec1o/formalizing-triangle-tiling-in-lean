-- Draft/MirrorStripR2Real.lean — R2 (the level-1 mirror branch (M) is impossible at m = 1) for
-- REAL dissections: the strip glue G1 (`strip_base`) and G2 (`strip_step`) of
-- Draft/MirrorStripR2Glue.lean PROVED (under the frame's extra data `R2Extra`), the assembly
-- `mirror_impossible'`, and, via the apex frame, `K_present_real`: every real m = 1 dissection is
-- in branch (H).  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- Build (scratch oleans; never .lake): ApexR2Frame and its deps oleans in $S, then
--   lake env bash -c 'LEAN_PATH=$S:$LEAN_PATH lean Erdos634/Draft/MirrorStripR2Real.lean'
import Erdos634.Draft.ApexR2Frame

namespace Erdos634.Draft.MirrorStripR2Real

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.ApexPlacement
open Erdos634.Draft.CornerAdjacency Erdos634.Draft.MirrorStripR2Glue

/-! ## §1 Plane algebra -/

/-- A vector killed by a functional that does not kill `w` is not parallel to `w`. -/
theorem cross_ne_of_g {u w : Plane} (g : Plane →ₗ[ℝ] ℝ) (hu : u ≠ 0) (hgu : g u = 0)
    (hgw : g w ≠ 0) : cross u w ≠ 0 := by
  intro h
  rw [NearBaseVertex.cross_apply] at h
  have e0 : (u 0) • w = (w 0) • u := by
    ext i; fin_cases i <;> simp <;> first | ring1 | linear_combination h | linear_combination -h
  have e1 : (u 1) • w = (w 1) • u := by
    ext i; fin_cases i <;> simp <;> first | ring1 | linear_combination h | linear_combination -h
  have g0 := congrArg g e0
  have g1 := congrArg g e1
  rw [map_smul, map_smul, hgu, smul_zero, smul_eq_mul] at g0 g1
  have hu0 : u 0 = 0 := by
    rcases mul_eq_zero.mp g0 with h0 | h0
    · exact h0
    · exact absurd h0 hgw
  have hu1 : u 1 = 0 := by
    rcases mul_eq_zero.mp g1 with h0 | h0
    · exact h0
    · exact absurd h0 hgw
  apply hu
  ext i; fin_cases i <;> simp [hu0, hu1]

/-- **Third vertex, cross form**: `Z`, `Z'` strictly on the same side of the line `XY` with the same
distances to `X` and `Y` coincide (`TileIdent.third_vertex_unique` with `h = ±cross(Y − X, ·)`). -/
theorem third_vertex_cross {X Y Z Z' : Plane} (hXY : X ≠ Y)
    (hs : 0 < cross (Y - X) (Z - X) * cross (Y - X) (Z' - X))
    (d1 : dist X Z = dist X Z') (d2 : dist Y Z = dist Y Z') : Z = Z' := by
  have hc : ∀ p, crossL (Y - X) p - crossL (Y - X) X = cross (Y - X) (p - X) := by
    intro p; rw [crossL_apply, crossL_apply, cross_sub_right']
  have hY := hc Y
  rw [cross_self'] at hY
  have hne : cross (Y - X) (Z - X) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hs; exact lt_irrefl _ hs
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hneg' : cross (Y - X) (Z' - X) < 0 := by
      by_contra hc'; push Not at hc'; nlinarith
    refine TileIdent.third_vertex_unique (-crossL (Y - X)) hXY ?_ ?_ ?_ d1 d2
    · simp only [LinearMap.neg_apply, neg_inj]; linarith
    · simp only [LinearMap.neg_apply, neg_lt_neg_iff]; have := hc Z; linarith
    · simp only [LinearMap.neg_apply, neg_lt_neg_iff]; have := hc Z'; linarith
  · have hpos' : 0 < cross (Y - X) (Z' - X) := by
      by_contra hc'; push Not at hc'; nlinarith
    refine TileIdent.third_vertex_unique (crossL (Y - X)) hXY ?_ ?_ ?_ d1 d2
    · linarith
    · have := hc Z; linarith
    · have := hc Z'; linarith

/-- A point of the open edge `(p_a, p_{a+1})` has coordinate `0` at `a+2`, positive at `a`, `a+1`. -/
theorem openSeg_coords (T : Tri) (a : Fin 3) {x : Plane}
    (hx : x ∈ openSegment ℝ (T.pts a) (T.pts (a + 1))) :
    T.basis.coord (a + 2) x = 0 ∧ 0 < T.basis.coord a x ∧ 0 < T.basis.coord (a + 1) x := by
  obtain ⟨s, t, hs, ht, hst, heq⟩ := hx
  have hlm : x = AffineMap.lineMap (T.pts a) (T.pts (a + 1)) t := by
    rw [AffineMap.lineMap_apply, ← heq]
    have hs' : s = 1 - t := by linarith
    rw [hs']
    simp only [vsub_eq_sub, vadd_eq_add, smul_sub, sub_smul, one_smul]
    abel
  have n1 : a + 2 ≠ a := NearBaseVertex.succ_succ_ne' a
  have n2 : a + 2 ≠ a + 1 := by fin_cases a <;> decide
  have n3 : a ≠ a + 1 := (NearBaseVertex.succ_ne' a).symm
  rw [hlm, AffineMap.apply_lineMap, AffineMap.apply_lineMap, AffineMap.apply_lineMap,
    NearBaseVertex.coord_other T n1, NearBaseVertex.coord_other T n2,
    NearBaseVertex.coord_self, NearBaseVertex.coord_other T n3,
    NearBaseVertex.coord_other T n3.symm, NearBaseVertex.coord_self]
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
  refine ⟨by ring, by nlinarith, by nlinarith⟩

theorem eq_of_card_one {N : ℕ} {s : Finset (Fin N)} (h : s.card = 1) {x y : Fin N} (hx : x ∈ s)
    (hy : y ∈ s) : x = y :=
  Finset.card_le_one.mp h.le x hx y hy

/-! ## §2 The frame's extra data and metric facts -/

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ}

/-- **What R2's glue needs beyond `R2Frame`**: the member bounds, `P′` interior, and the `b`-freeness
of the leg `A + ℝ·uL` (`lem:sidenob` on the real leg chain, `ApexLegWord.leg_no_b`).  Discharged for
every real `m = 1` dissection in §7. -/
structure R2Extra (F : R2Frame D e f α β γ) : Prop where
  he2 : 2 ≤ e
  hef2 : e + 2 ≤ f
  hPint : F.P ∈ interior D.target.carrier
  hlegnob : ∀ (i : Fin N) (m : Fin 3) (s t : ℝ), (D.tile i).pts m = F.A + s • F.uL →
    (D.tile i).pts (m + 1) = F.A + t • F.uL →
    dist ((D.tile i).pts m) ((D.tile i).pts (m + 1)) ≠ (f : ℝ) ^ 2 - (e : ℝ) ^ 2

end Erdos634.Draft.MirrorStripR2Real

namespace Erdos634.Draft.MirrorStripR2Glue.R2Frame

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.CornerAdjacency
open Erdos634.Draft.MirrorStripR2Real

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ}
variable (F : R2Frame D e f α β γ)

theorem Q_zero : F.Q 0 = F.P := by simp [R2Frame.Q]
theorem J_zero : F.J 0 = F.A := by simp [R2Frame.J]
theorem J_one : F.J 1 = F.A + ((f : ℝ) ^ 2) • F.uL := by simp [R2Frame.J]

theorem Q_sub_J (k : ℕ) : F.Q k - F.J k = F.P - F.A := by
  simp only [R2Frame.Q, R2Frame.J]; abel

theorem J_succ_sub_Q (k : ℕ) : F.J (k + 1) - F.Q k = ((f : ℝ) ^ 2) • F.uL - (F.P - F.A) := by
  simp only [R2Frame.Q, R2Frame.J]; push_cast; module

theorem Q_succ_sub_Q (k : ℕ) : F.Q (k + 1) - F.Q k = ((f : ℝ) ^ 2) • F.uL := by
  simp only [R2Frame.Q]; push_cast; module

theorem J_succ_sub_J (k : ℕ) : F.J (k + 1) - F.J k = ((f : ℝ) ^ 2) • F.uL := by
  simp only [R2Frame.J]; push_cast; module

theorem J_two_sub_J (k : ℕ) : F.J (k + 2) - F.J (k + 1) = ((f : ℝ) ^ 2) • F.uL := by
  simp only [R2Frame.J]; push_cast; module

theorem J_two_sub_Q (k : ℕ) :
    F.J (k + 2) - F.Q (k + 1) = ((f : ℝ) ^ 2) • F.uL - (F.P - F.A) := by
  simp only [R2Frame.Q, R2Frame.J]; push_cast; module

theorem w_norm : ‖F.P - F.A‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
  rw [← dist_eq_norm, dist_comm]; exact F.hAP

theorem cw_norm : ‖((f : ℝ) ^ 2) • F.uL - (F.P - F.A)‖ = (e : ℝ) * f := by
  have : ((f : ℝ) ^ 2) • F.uL - (F.P - F.A) = (F.A + ((f : ℝ) ^ 2) • F.uL) - F.P := by abel
  rw [this, ← dist_eq_norm, dist_comm]; exact F.hPJ1

theorem c_norm : ‖((f : ℝ) ^ 2) • F.uL‖ = (f : ℝ) ^ 2 := by
  rw [norm_smul, F.huL, mul_one, Real.norm_of_nonneg (by positivity)]

theorem gw_pos : 0 < F.g (F.P - F.A) := by rw [map_sub]; linarith [F.hgA]

theorem uL_ne : F.uL ≠ 0 := by
  intro h; have := F.huL; rw [h, norm_zero] at this; exact zero_ne_one this

theorem cross_uL_w : cross F.uL (F.P - F.A) ≠ 0 :=
  cross_ne_of_g F.g F.uL_ne F.hguL F.gw_pos.ne'

theorem cross_w_uL : cross (F.P - F.A) F.uL ≠ 0 := by
  rw [cross_anti]; exact neg_ne_zero.mpr F.cross_uL_w

theorem dist_A_J (j : ℕ) : dist F.A (F.J j) = (j : ℝ) * (f : ℝ) ^ 2 :=
  HalfTurnR3R4Glue.dist_self_add_unit F.huL (by positivity)

/-! ### The leg points `J j` -/

theorem L_mem : F.A + ((f : ℝ) ^ 3) • F.uL ∈ D.target.carrier := by
  apply subset_convexHull ℝ _; rw [F.htarget]; simp

theorem A_mem : F.A ∈ D.target.carrier := by
  apply subset_convexHull ℝ _; rw [F.htarget]; simp

theorem J_mem_target (j : ℕ) (hj : j ≤ f) : F.J j ∈ D.target.carrier := by
  have hf : (0 : ℝ) < f := by exact_mod_cast (show 0 < f by have := F.hef; omega)
  have hjR : (j : ℝ) ≤ f := by exact_mod_cast hj
  have ht : (j : ℝ) / f ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity, by rw [div_le_one hf]; exact hjR⟩
  have h := D.target.convex.add_smul_sub_mem F.A_mem F.L_mem ht
  have e1 : F.A + ((j : ℝ) / f) • (F.A + ((f : ℝ) ^ 3) • F.uL - F.A) = F.J j := by
    rw [R2Frame.J, add_sub_cancel_left, smul_smul]
    congr 2; field_simp
  rwa [e1] at h

/-- The leg points are not interior (the barycentric coordinate of `R` vanishes on the leg line). -/
theorem J_not_interior (j : ℕ) : F.J j ∉ interior D.target.carrier := by
  intro hJ
  have hpos := (Tri.mem_interior_iff_coord_pos _ _).mp hJ
  have hef := F.hef
  have hf : (0 : ℝ) < f := by exact_mod_cast (by omega : 0 < f)
  set L := F.A + ((f : ℝ) ^ 3) • F.uL with hL
  obtain ⟨iA, hiA⟩ := Erdos634.MarchInduction.mem_range_of_eq F.htarget
    (by simp : F.A ∈ ({F.A, L, F.R} : Set Plane))
  obtain ⟨iL, hiL⟩ := Erdos634.MarchInduction.mem_range_of_eq F.htarget
    (by simp : L ∈ ({F.A, L, F.R} : Set Plane))
  obtain ⟨iR, hiR⟩ := Erdos634.MarchInduction.mem_range_of_eq F.htarget
    (by simp : F.R ∈ ({F.A, L, F.R} : Set Plane))
  have hinj := D.target.indep.injective
  have hRA : F.R ≠ F.A := by
    intro h; have := F.hlegR; rw [h, dist_self] at this
    have : (0 : ℝ) < (f : ℝ) ^ 3 := by positivity
    linarith
  have hiRA : iR ≠ iA := fun h => hRA (by rw [← hiR, ← hiA, h])
  have hiRL : iR ≠ iL := by
    intro h
    have hq : ∀ q, D.target.pts q = F.A ∨ D.target.pts q = L := by
      intro q
      have : D.target.pts q ∈ ({F.A, L, F.R} : Set Plane) := F.htarget ▸ ⟨q, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
      rcases this with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
      · right; rw [h1, ← hiR, h, hiL]
    rcases hq 0 with h0 | h0 <;> rcases hq 1 with h1 | h1 <;> rcases hq 2 with h2 | h2
    all_goals first
      | exact absurd (hinj (h0.trans h1.symm)) (by decide)
      | exact absurd (hinj (h0.trans h2.symm)) (by decide)
      | exact absurd (hinj (h1.trans h2.symm)) (by decide)
  have hline : F.J j = AffineMap.lineMap F.A L ((j : ℝ) / (f : ℝ)) := by
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, hL, add_sub_cancel_left, smul_smul,
      R2Frame.J]
    rw [show (j : ℝ) / (f : ℝ) * (f : ℝ) ^ 3 = (j : ℝ) * (f : ℝ) ^ 2 by field_simp]
    abel
  have h0 := hpos iR
  rw [hline, AffineMap.apply_lineMap, ← hiA, ← hiL, NearBaseVertex.coord_other _ hiRA,
    NearBaseVertex.coord_other _ hiRL, AffineMap.lineMap_same_apply] at h0
  exact lt_irrefl _ h0

theorem J_frontier (j : ℕ) (hj : j ≤ f) : F.J j ∈ frontier D.target.carrier :=
  ⟨subset_closure (F.J_mem_target j hj), F.J_not_interior j⟩

theorem J_not_vertex (j : ℕ) (hj1 : 1 ≤ j) (hjf : j + 1 ≤ f) :
    F.J j ∉ Set.range D.target.pts := by
  rw [F.htarget]
  have hd := F.dist_A_J j
  have hf : (0 : ℝ) < f := by exact_mod_cast (show 0 < f by omega)
  have hj1R : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  have hjfR : (j : ℝ) + 1 ≤ f := by exact_mod_cast hjf
  have hlt : (j : ℝ) * (f : ℝ) ^ 2 < (f : ℝ) ^ 3 := by nlinarith
  intro hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h
  · rw [h, dist_self] at hd
    have : (0 : ℝ) < (j : ℝ) * (f : ℝ) ^ 2 := by positivity
    linarith
  · rw [h, HalfTurnR3R4Glue.dist_self_add_unit F.huL (by positivity)] at hd
    linarith
  · rw [h, F.hlegR] at hd; linarith

end Erdos634.Draft.MirrorStripR2Glue.R2Frame

namespace Erdos634.Draft.MirrorStripR2Real

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.ApexPlacement
open Erdos634.Draft.CornerAdjacency Erdos634.Draft.MirrorStripR2Glue

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ}

/-! ## §3 Counting at a point -/

/-- The integer form of the angle sum at an interior point (`n_α + 3n_π + 6n_{2π} + 2n_γ = 6`,
`n_β + 2n_π + 4n_{2π} + n_γ = 4`). -/
theorem interior_card_eqs (D : CongruentDissection N) (hAD : MarchSlots.AngleData α β γ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    {x : Plane} (hx : x ∈ interior D.target.carrier) :
    ({i | (D.tile i).localAngle x = α} : Finset (Fin N)).card
      + 3 * ({i | (D.tile i).localAngle x = Real.pi} : Finset (Fin N)).card
      + 6 * ({i | (D.tile i).localAngle x = 2 * Real.pi} : Finset (Fin N)).card
      + 2 * ({i | (D.tile i).localAngle x = γ} : Finset (Fin N)).card = 6 ∧
    ({i | (D.tile i).localAngle x = β} : Finset (Fin N)).card
      + 2 * ({i | (D.tile i).localAngle x = Real.pi} : Finset (Fin N)).card
      + 4 * ({i | (D.tile i).localAngle x = 2 * Real.pi} : Finset (Fin N)).card
      + ({i | (D.tile i).localAngle x = γ} : Finset (Fin N)).card = 4 := by
  classical
  have hπ := Real.pi_pos
  have hα := hAD.hα
  have hβ := hAD.hβ
  have hγd := hAD.hγdef
  have hrel := hAD.hrel
  have hvals : ∀ i, (D.tile i).localAngle x ∈ ({α, β, γ, Real.pi, 2 * Real.pi, 0} : Finset ℝ) :=
    fun i => congruentDissection_localAngle_mem_all D α β γ hα' hβ' hγ' x i
  have key := VertexFigureReal.interior_multiplicities_cards D.toDissection α β γ hAD.hαβ
    (by intro h; linarith) (by intro h; linarith) (by intro h; linarith) (by intro h; linarith)
    (by intro h; linarith) (by intro h; linarith) (by intro h; linarith) (by intro h; linarith)
    (by intro h; linarith) (by intro h; linarith) (by intro h; linarith)
    (by intro h; linarith) (by intro h; linarith) (by intro h; linarith) hx hvals
  set nA := ({i | (D.tile i).localAngle x = α} : Finset (Fin N)).card with hnA
  set nB := ({i | (D.tile i).localAngle x = β} : Finset (Fin N)).card with hnB
  set nC := ({i | (D.tile i).localAngle x = γ} : Finset (Fin N)).card with hnC
  set nP := ({i | (D.tile i).localAngle x = Real.pi} : Finset (Fin N)).card with hnP
  set nU := ({i | (D.tile i).localAngle x = 2 * Real.pi} : Finset (Fin N)).card with hnU
  have h' : ((nA + 3 * nP + 6 * nU : ℕ) : ℝ) * α + ((nB + 2 * nP + 4 * nU : ℕ) : ℝ) * β
      + (nC : ℝ) * (2 * α + β) = ((6 : ℤ) : ℝ) * α + ((4 : ℤ) : ℝ) * β := by
    rw [hγd] at key
    push_cast
    linear_combination key + ((nP : ℝ) + 2 * (nU : ℝ) - 2) * hrel
  obtain ⟨e1, e2⟩ := Geometry.vertex_multiplicities hrel hAD.hirr _ _ _ 6 4 h'
  push_cast at e1 e2
  omega

theorem mem_filter_of {N : ℕ} {D : CongruentDissection N} {x : Plane} {θ : ℝ} {i : Fin N}
    (h : (D.tile i).localAngle x = θ) :
    i ∈ ({i | (D.tile i).localAngle x = θ} : Finset (Fin N)) := by simp [h]

/-- A vertex of a tile carries `α`, `β` or `γ`. -/
theorem vertex_angle (F : R2Frame D e f α β γ) (hX : R2Extra F) (i : Fin N) {m : Fin 3}
    {x : Plane} (hm : (D.tile i).pts m = x) :
    (D.tile i).localAngle x = α ∨ (D.tile i).localAngle x = β ∨ (D.tile i).localAngle x = γ := by
  obtain ⟨hab, hac, hbc⟩ :=
    HalfTurnR3R4Glue.sides_distinct F.hco hX.he2 (by have := hX.hef2; omega)
  have hL := HalfTurnR3R4Glue.localAngle_of_oppSideE D hab hac hbc F.hM.hs0 F.hM.hs1 F.hM.hs2
    F.hM.hα' F.hM.hβ' F.hM.hγ' i m
  rw [hm] at hL
  have hd := NearBaseBridge.tile_dist_mem (D.tiles_congruent i) F.hM.hs0 F.hM.hs1 F.hM.hs2
    (m + 1) (m + 2) (by fin_cases m <;> decide)
  rcases hd with h | h | h
  · exact Or.inl (hL.1 h)
  · exact Or.inr (Or.inl (hL.2.1 h))
  · exact Or.inr (Or.inr (hL.2.2 h))

/-- **Corner data.**  A tile with a corner at `x` (flanks `U`, `W`): at a `β` corner the flanks are
`{a, c}` and the opposite side `b`; at an `α` corner the flanks are `{b, c}` and the opposite `a`. -/
theorem corner_data (F : R2Frame D e f α β γ) (hX : R2Extra F) {i : Fin N} {m : Fin 3}
    {x U W : Plane} (hm : (D.tile i).pts m = x) (hUW : IsFlankPair (D.tile i) m x U W) :
    ((D.tile i).localAngle x = β →
      ((‖U‖ = (e : ℝ) * f ∧ ‖W‖ = (f : ℝ) ^ 2) ∨ (‖U‖ = (f : ℝ) ^ 2 ∧ ‖W‖ = (e : ℝ) * f)) ∧
      dist (x + U) (x + W) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ∧
    ((D.tile i).localAngle x = α →
      ((‖U‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧ ‖W‖ = (f : ℝ) ^ 2) ∨
        (‖U‖ = (f : ℝ) ^ 2 ∧ ‖W‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ∧
      dist (x + U) (x + W) = (e : ℝ) * f) := by
  obtain ⟨hab, hac, hbc⟩ :=
    HalfTurnR3R4Glue.sides_distinct F.hco hX.he2 (by have := hX.hef2; omega)
  have hP := NearBaseBridge.tile_triple (D.tiles_congruent i) F.hM.hs0 F.hM.hs1 F.hM.hs2 m
  have hL := HalfTurnR3R4Glue.localAngle_of_oppSideE D hab hac hbc F.hM.hs0 F.hM.hs1 F.hM.hs2
    F.hM.hα' F.hM.hβ' F.hM.hγ' i m
  rw [hm] at hP hL
  have hAD := F.hA
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
    refine ⟨fun hg => ?_, fun hg => ?_⟩ <;>
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
    refine ⟨fun hg => ?_, fun hg => ?_⟩ <;>
    first
      | exact ⟨Or.inl ⟨h2, h1⟩, h3⟩
      | exact ⟨Or.inr ⟨h2, h1⟩, h3⟩
      | (exfalso; have h4 := (e1 h3).symm.trans hg
         first | linarith | exact hαβ h4 | exact hαβ h4.symm)
      | (exfalso; have h4 := (e2 h3).symm.trans hg
         first | linarith | exact hαβ h4 | exact hαβ h4.symm)
      | (exfalso; have h4 := (e3 h3).symm.trans hg
         first | linarith | exact hαβ h4 | exact hαβ h4.symm)


/-- The third side of a tile whose sides at `x` are `a` and `b` is `c`. -/
theorem third_side_c (F : R2Frame D e f α β γ) (hX : R2Extra F) {i : Fin N} {x Y Z : Plane}
    (hr : Set.range (D.tile i).pts = {x, Y, Z}) (hY : dist Y x = (e : ℝ) * f)
    (hZ : dist Z x = (f : ℝ) ^ 2 - (e : ℝ) ^ 2) : dist Y Z = (f : ℝ) ^ 2 := by
  obtain ⟨hab, hac, hbc⟩ :=
    HalfTurnR3R4Glue.sides_distinct F.hco hX.he2 (by have := hX.hef2; omega)
  obtain ⟨m, hm⟩ := MarchInduction.mem_range_of_eq hr (Set.mem_insert _ _)
  have hP := NearBaseBridge.tile_triple (D.tiles_congruent i) F.hM.hs0 F.hM.hs1 F.hM.hs2 m
  rw [hm] at hP
  unfold NearBaseBridge.Perm3 at hP
  rcases MarchInduction.vertex_data_of_range hr hm with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h1, h2] at hP
  · rw [hY, hZ] at hP
    rcases hP with ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩ |
      ⟨p1, p2, p3⟩ <;>
    first
      | exact p3
      | exact absurd p1 hab
      | exact absurd p1 hac
      | exact absurd p2 hbc
      | exact absurd p2 hab.symm
      | exact absurd p1 hac.symm
      | exact absurd p2 hbc.symm
  · rw [hY, hZ] at hP
    rw [dist_comm]
    rcases hP with ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩ |
      ⟨p1, p2, p3⟩ <;>
    first
      | exact p3
      | exact absurd p2 hab
      | exact absurd p2 hac
      | exact absurd p1 hbc
      | exact absurd p1 hab.symm
      | exact absurd p2 hac.symm
      | exact absurd p1 hbc.symm

/-- `‖(c/b)·w − b·u‖ = a` from `‖c·u − w‖ = a`, `‖u‖ = 1`, `‖w‖ = b` (the reflected corner). -/
theorem refl_norm {u w : Plane} {a b c : ℝ} (hu : ‖u‖ = 1) (hw : ‖w‖ = b) (hb : 0 < b)
    (ha : 0 ≤ a) (hcw : ‖c • u - w‖ = a) : ‖(c / b) • w - b • u‖ = a := by
  have h1 : ‖c • u - w‖ ^ 2 = a ^ 2 := by rw [hcw]
  rw [norm_sub_sq_real, norm_smul, hu, real_inner_smul_left, hw, Real.norm_eq_abs, mul_one,
    sq_abs] at h1
  have h2 : ‖(c / b) • w - b • u‖ ^ 2 = a ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, norm_smul, hu, hw, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm u w, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, sq_abs, mul_one, sq_abs]
    have e1 : (c / b) ^ 2 * b ^ 2 = c ^ 2 := by field_simp
    have e2 : c / b * (b * inner ℝ u w) = c * inner ℝ u w := by field_simp
    rw [e1, e2]; linarith [h1]
  exact (pow_left_inj₀ (norm_nonneg _) ha two_ne_zero).mp h2

/-! ## §4 Tile identification in the strip -/

/-- **The `β`-tile at `Q k` across `J (k+1) − Q k` is the strip cell `Z k`.**  Its flank along
`Q k J (k+1)` is `a` (a `c` would make the leg point `J (k+1)` interior), so its other flank is `c`
and its third vertex, at distance `b` from `J (k+1)` on the far side, is `Q (k+1)`. -/
theorem beta_ident (F : R2Frame D e f α β γ) (hX : R2Extra F) (k : ℕ)
    (hQint : F.Q k ∈ interior D.target.carrier)
    {z : Fin N} {mz : Fin 3} {U W : Plane} (hmz : (D.tile z).pts mz = F.Q k)
    (hUW : IsFlankPair (D.tile z) mz (F.Q k) U W) {S : ℝ} (hS : 0 < S)
    (hU : F.J (k + 1) - F.Q k = S • U)
    (hside : cross (F.J (k + 1) - F.Q k) W * cross (F.J (k + 1) - F.Q k) (F.J k - F.Q k) < 0)
    (hβz : (D.tile z).localAngle (F.Q k) = β) :
    Set.range (D.tile z).pts = F.Z k := by
  obtain ⟨hn, hopp⟩ := (corner_data F hX hmz hUW).1 hβz
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast hX.he2
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast hX.hef2
  have ha0 : (0 : ℝ) < (e : ℝ) * f := by nlinarith
  have hac : (e : ℝ) * f < (f : ℝ) ^ 2 := by nlinarith
  have hU0 : ‖F.J (k + 1) - F.Q k‖ = (e : ℝ) * f := by rw [F.J_succ_sub_Q]; exact F.cw_norm
  have hSU : S * ‖U‖ = (e : ℝ) * f := by
    rw [← hU0, hU, norm_smul, Real.norm_of_nonneg hS.le]
  have hE : F.Q k + U ∈ D.target.carrier := by
    rcases hUW with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1, add_sub_cancel]; exact MarchInduction.pts_mem_target D.toDissection z _
    · rw [h1, add_sub_cancel]; exact MarchInduction.pts_mem_target D.toDissection z _
  have hUa : ‖U‖ = (e : ℝ) * f := by
    rcases hn with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exfalso
      rw [h1] at hSU
      have hS1 : S < 1 := by
        by_contra hc; push Not at hc; nlinarith
      apply F.J_not_interior (k + 1)
      refine (D.target.convex.openSegment_interior_closure_subset_interior hQint
        (subset_closure hE)) ⟨1 - S, S, by linarith, hS, by ring, ?_⟩
      have : F.J (k + 1) = F.Q k + S • U := by rw [← hU]; abel
      rw [this]; module
  have hS1 : S = 1 := by
    rw [hUa] at hSU
    have : S * ((e : ℝ) * f) = 1 * ((e : ℝ) * f) := by rw [hSU, one_mul]
    exact mul_right_cancel₀ ha0.ne' this
  have hUe : U = F.J (k + 1) - F.Q k := by rw [hU, hS1, one_smul]
  have hUeq : F.Q k + U = F.J (k + 1) := by rw [hUe]; abel
  have hWc : ‖W‖ = (f : ℝ) ^ 2 := by
    rcases hn with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact h2
    · rw [hUa] at h1; exact absurd h1 hac.ne
  have hid : F.Q (k + 1) - F.Q k = (F.J (k + 1) - F.Q k) - (F.J k - F.Q k) := by
    rw [F.Q_succ_sub_Q, show (F.J (k + 1) - F.Q k) - (F.J k - F.Q k) = F.J (k + 1) - F.J k by abel,
      F.J_succ_sub_J]
  have hZ : F.Q k + W = F.Q (k + 1) := by
    apply third_vertex_cross (X := F.Q k) (Y := F.J (k + 1))
    · intro h; rw [← h, sub_self, norm_zero] at hU0; linarith
    · rw [add_sub_cancel_left, hid, cross_sub_right', cross_self', zero_sub, mul_neg]
      linarith
    · rw [dist_comm, dist_eq_norm, add_sub_cancel_left, hWc, dist_comm, dist_eq_norm,
        F.Q_succ_sub_Q, F.c_norm]
    · rw [← hUeq, hopp, hUeq, dist_comm, dist_eq_norm, F.Q_sub_J, F.w_norm]
  rw [range_of_flank hmz hUW, hUeq, hZ]
  rfl

/-- **The `α`-tile at the leg point `J (k+1)` across `w = Q (k+1) − J (k+1)` is `Z′ k`.**  Its flank
along `w` is `b` or `c`; with `c`, its `b`-flank would be the leg edge `[J (k+1), J (k+1) + b·uL]`
(`third_vertex_cross`), which `lem:sidenob` forbids; with `b`, the third vertex is `J (k+2)`. -/
theorem alpha_ident (F : R2Frame D e f α β γ) (hX : R2Extra F) (k : ℕ)
    {j : Fin N} {mj : Fin 3} {U W : Plane} (hmj : (D.tile j).pts mj = F.J (k + 1))
    (hUW : IsFlankPair (D.tile j) mj (F.J (k + 1)) U W) {S : ℝ} (hS : 0 < S)
    (hU : F.Q (k + 1) - F.J (k + 1) = S • U)
    (hside : cross (F.Q (k + 1) - F.J (k + 1)) W
      * cross (F.Q (k + 1) - F.J (k + 1)) (F.Q k - F.J (k + 1)) < 0)
    (hαj : (D.tile j).localAngle (F.J (k + 1)) = α) :
    Set.range (D.tile j).pts = F.Z' k := by
  obtain ⟨hn, hopp⟩ := (corner_data F hX hmj hUW).2 hαj
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast hX.he2
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast hX.hef2
  have hb0 : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hc0 : (0 : ℝ) < (f : ℝ) ^ 2 := by nlinarith
  have ha0 : (0 : ℝ) < (e : ℝ) * f := by nlinarith
  have hbc : (f : ℝ) ^ 2 - (e : ℝ) ^ 2 < (f : ℝ) ^ 2 := by nlinarith
  have hU0e : F.Q (k + 1) - F.J (k + 1) = F.P - F.A := F.Q_sub_J (k + 1)
  have hU0 : ‖F.Q (k + 1) - F.J (k + 1)‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rw [hU0e]; exact F.w_norm
  have hid : cross (F.Q (k + 1) - F.J (k + 1)) (((f : ℝ) ^ 2) • F.uL)
      = - cross (F.Q (k + 1) - F.J (k + 1)) (F.Q k - F.J (k + 1)) := by
    have : ((f : ℝ) ^ 2) • F.uL = (F.Q (k + 1) - F.J (k + 1)) - (F.Q k - F.J (k + 1)) := by
      rw [show (F.Q (k + 1) - F.J (k + 1)) - (F.Q k - F.J (k + 1)) = F.Q (k + 1) - F.Q k by abel,
        F.Q_succ_sub_Q]
    rw [this, cross_sub_right', cross_self', zero_sub]
  have hJ2 : F.J (k + 2) = F.J (k + 1) + ((f : ℝ) ^ 2) • F.uL := by
    rw [← F.J_two_sub_J k]; abel
  have hSU : S * ‖U‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rw [← hU0, hU, norm_smul, Real.norm_of_nonneg hS.le]
  rcases hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- the `b`-flank lies on `J (k+1) Q (k+1)`: the tile is `Z′ k`
    have hS1 : S = 1 := by
      rw [h1] at hSU
      have : S * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) = 1 * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
        rw [hSU, one_mul]
      exact mul_right_cancel₀ hb0.ne' this
    have hUe : U = F.Q (k + 1) - F.J (k + 1) := by rw [hU, hS1, one_smul]
    have hUeq : F.J (k + 1) + U = F.Q (k + 1) := by rw [hUe]; abel
    have hZ : F.J (k + 1) + W = F.J (k + 2) := by
      apply third_vertex_cross (X := F.J (k + 1)) (Y := F.Q (k + 1))
      · intro h; rw [← h, sub_self, norm_zero] at hU0; linarith
      · rw [add_sub_cancel_left, hJ2, add_sub_cancel_left, hid, mul_neg]; linarith
      · rw [dist_comm, dist_eq_norm, add_sub_cancel_left, h2, hJ2, dist_comm, dist_eq_norm,
          add_sub_cancel_left, F.c_norm]
      · have e1 : dist (F.Q (k + 1)) (F.J (k + 1) + W) = (e : ℝ) * f := by rw [← hUeq]; exact hopp
        have e2 : dist (F.Q (k + 1)) (F.J (k + 2)) = (e : ℝ) * f := by
          rw [dist_comm, dist_eq_norm, F.J_two_sub_Q, F.cw_norm]
        rw [e1, e2]
    rw [range_of_flank hmj hUW, hUeq, hZ]
    show _ = ({F.J (k + 1), F.J (k + 2), F.Q (k + 1)} : Set Plane)
    ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  · -- the `c`-flank lies along `w`: the `b`-flank is then a leg edge — `lem:sidenob` forbids it
    exfalso
    have hUc : U = ((f : ℝ) ^ 2 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • (F.P - F.A) := by
      rw [← hU0e]; exact eq_smul_of_norms hS hU hU0 h1 hb0
    have hU0' : F.Q (k + 1) - F.J (k + 1) = S • U := hU
    rw [hU0'] at hside hid
    simp only [cross_smul_left'] at hside hid
    have hS2 : 0 < S * S := mul_pos hS hS
    have hpq : cross U W * cross U (F.Q k - F.J (k + 1)) < 0 := by
      by_contra hc; push Not at hc
      have : 0 ≤ (S * S) * (cross U W * cross U (F.Q k - F.J (k + 1))) := by positivity
      nlinarith
    have hr : (f : ℝ) ^ 2 * cross U F.uL = - cross U (F.Q k - F.J (k + 1)) := by
      rw [cross_smul_right] at hid
      have : S * ((f : ℝ) ^ 2 * cross U F.uL) = S * (- cross U (F.Q k - F.J (k + 1))) := by
        rw [hid]; ring
      exact mul_left_cancel₀ hS.ne' this
    have hU0n : U ≠ 0 := by
      intro h; rw [h, norm_zero] at h1; linarith
    have hZ : F.J (k + 1) + W = F.J (k + 1) + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uL := by
      apply third_vertex_cross (X := F.J (k + 1)) (Y := F.J (k + 1) + U)
      · intro h; apply hU0n
        have := congrArg (fun p => p - F.J (k + 1)) h
        simpa using this.symm
      · rw [add_sub_cancel_left, add_sub_cancel_left, add_sub_cancel_left, cross_smul_right]
        have key : (f : ℝ) ^ 2 * (cross U W * (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * cross U F.uL))
            = ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * (cross U W * ((f : ℝ) ^ 2 * cross U F.uL)) := by ring
        rw [hr] at key
        have hpos : 0 < ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)
            * (cross U W * - cross U (F.Q k - F.J (k + 1))) :=
          mul_pos hb0 (by rw [mul_neg]; linarith)
        rw [← key] at hpos
        exact pos_of_mul_pos_right hpos hc0.le
      · rw [dist_comm, dist_eq_norm, add_sub_cancel_left, h2,
          HalfTurnR3R4Glue.dist_self_add_unit F.huL hb0.le]
      · rw [hopp, dist_eq_norm, add_sub_add_left_eq_sub, hUc]
        exact (refl_norm F.huL F.w_norm hb0 ha0.le F.cw_norm).symm
    have hW : W = ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uL := add_left_cancel hZ
    have hWn : ‖W‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := h2
    have hJs : F.J (k + 1) = F.A + (((k + 1 : ℕ) : ℝ) * (f : ℝ) ^ 2) • F.uL := rfl
    have hJW : F.J (k + 1) + W
        = F.A + ((((k + 1 : ℕ) : ℝ) * (f : ℝ) ^ 2) + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • F.uL := by
      rw [hW, hJs, add_smul]; abel
    rcases hUW with ⟨-, hW'⟩ | ⟨-, hW'⟩
    · -- `W = p (mj+2) − J`: the edge `(mj+2, mj)` lies on the leg
      have hp2 : (D.tile j).pts (mj + 2) = F.J (k + 1) + W := by rw [hW']; abel
      have hp3 : (D.tile j).pts (mj + 2 + 1) = F.J (k + 1) := by
        rw [HalfTurnR3R4Order.fin3_add_two_add_one]; exact hmj
      apply hX.hlegnob j (mj + 2) _ _ (hp2.trans hJW) (hp3.trans hJs)
      rw [hp2, hp3, dist_eq_norm, add_sub_cancel_left, hWn]
    · -- `W = p (mj+1) − J`: the edge `(mj, mj+1)` lies on the leg
      have hp1 : (D.tile j).pts (mj + 1) = F.J (k + 1) + W := by rw [hW']; abel
      apply hX.hlegnob j mj _ _ (hmj.trans hJs) (hp1.trans hJW)
      rw [hmj, hp1, dist_comm, dist_eq_norm, add_sub_cancel_left, hWn]


/-! ## §5 The three steps -/

/-- Angles other than `2π` at a boundary point. -/
theorem two_pi_not_mem {α β γ : ℝ} (hAD : MarchSlots.AngleData α β γ) :
    2 * Real.pi ∉ ({α, β, γ, Real.pi, 0} : Finset ℝ) := by
  have hπ := Real.pi_pos
  have hα := hAD.hα
  have hβ := hAD.hβ
  have hγd := hAD.hγdef
  have hrel := hAD.hrel
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> linarith

/-- **The leg step (`prop:selfsim` at `J (k+1)`).**  With the row tile `{J k, J (k+1), Q k}` (`β` at
`J (k+1)`) and the strip cell `Z k` (`γ` there) present, the leg point `J (k+1)` carries exactly one
more tile, an `α`, across `Z k`'s flank `w`; it is `Z′ k` (`alpha_ident`). -/
theorem leg_step (F : R2Frame D e f α β γ) (hX : R2Extra F) (k : ℕ) (hk : k + 2 ≤ f)
    (hY : Present D {F.J k, F.J (k + 1), F.Q k}) (hZ : Present D (F.Z k)) :
    Present D (F.Z' k) := by
  classical
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast hX.he2
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast hX.hef2
  have hc0 : (0 : ℝ) < (f : ℝ) ^ 2 := by nlinarith
  have hAD := F.hA
  obtain ⟨hαβ, hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hγπ, hγ0, -, -, -⟩ := angle_facts hAD
  have hJf : F.J (k + 1) ∈ frontier D.target.carrier := F.J_frontier (k + 1) (by omega)
  have hJv : F.J (k + 1) ∉ Set.range D.target.pts := F.J_not_vertex (k + 1) (by omega) (by omega)
  obtain ⟨hab, hac, hbc⟩ :=
    HalfTurnR3R4Glue.sides_distinct F.hco hX.he2 (by have := hX.hef2; omega)
  have hloc := fun {i : Fin N} {P Q R : Plane} (hr : Set.range (D.tile i).pts = {P, Q, R}) =>
    HalfTurnR3R4Glue.localAngle_of_rangeE D hab hac hbc F.hM.hs0 F.hM.hs1 F.hM.hs2 F.hM.hα'
      F.hM.hβ' F.hM.hγ' hr
  obtain ⟨iY, hiY⟩ := hY
  obtain ⟨iZ, hiZ⟩ := hZ
  have hiY' : Set.range (D.tile iY).pts = {F.J (k + 1), F.J k, F.Q k} := by
    rw [hiY]; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hiZ' : Set.range (D.tile iZ).pts = {F.J (k + 1), F.Q (k + 1), F.Q k} := by
    rw [hiZ, R2Frame.Z]; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hYβ : (D.tile iY).localAngle (F.J (k + 1)) = β := by
    apply (hloc hiY').2.1
    rw [dist_comm, dist_eq_norm, F.Q_sub_J]; exact F.w_norm
  have hZγ : (D.tile iZ).localAngle (F.J (k + 1)) = γ := by
    apply (hloc hiZ').2.2
    rw [dist_eq_norm, F.Q_succ_sub_Q]; exact F.c_norm
  -- the figure at `J (k+1)`: one `α`, one `β`, one `γ`, no straight angle
  have hvals := fun i => Dissection.congruentDissection_localAngle_mem_boundary D α β γ F.hM.hα'
    F.hM.hβ' F.hM.hγ' hJf hJv i
  obtain ⟨cA, cB, cC, cP⟩ := VertexFigureReal.gamma_boundary_figure_real D.toDissection hαβ hαγ
    hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 Real.pi_ne_zero hAD.hγdef hAD.hrel hAD.hirr hJf hJv hvals iZ hZγ
  have hvert : ∀ i, F.J (k + 1) ∈ (D.tile i).carrier → ∃ m, (D.tile i).pts m = F.J (k + 1) := by
    intro i hi
    by_contra hv; push Not at hv
    rcases HalfTurnR3R4Order.localAngle_mem_pi_of_mem (D.tile i) hi hv with h | h
    · have := hvals i; rw [h] at this; exact two_pi_not_mem hAD this
    · have : 1 ≤ ({i | (D.tile i).localAngle (F.J (k + 1)) = Real.pi} : Finset (Fin N)).card :=
        Finset.card_pos.mpr ⟨i, mem_filter_of h⟩
      omega
  -- `Z k`'s corner at `J (k+1)`: flanks `w = Q (k+1) − J (k+1)` and `Q k − J (k+1)`
  obtain ⟨mZ, hmZ⟩ := MarchInduction.mem_range_of_eq hiZ' (Set.mem_insert _ _)
  have hflZ : IsFlankPair (D.tile iZ) mZ (F.J (k + 1)) (F.Q (k + 1) - F.J (k + 1))
      (F.Q k - F.J (k + 1)) := by
    rcases MarchInduction.vertex_data_of_range hiZ' hmZ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨by rw [h1], by rw [h2]⟩
    · right; exact ⟨by rw [h2], by rw [h1]⟩
  have hU0 : F.Q (k + 1) - F.J (k + 1) = F.P - F.A := F.Q_sub_J (k + 1)
  have hW0 : F.Q k - F.J (k + 1) = (F.P - F.A) - ((f : ℝ) ^ 2) • F.uL := by
    rw [show F.Q k - F.J (k + 1) = (F.Q k - F.J k) - (F.J (k + 1) - F.J k) by abel, F.Q_sub_J,
      F.J_succ_sub_J]
  have hΔ : cross (F.Q (k + 1) - F.J (k + 1)) (F.Q k - F.J (k + 1)) ≠ 0 := by
    rw [hU0, hW0, cross_sub_right', cross_self', cross_smul_right, zero_sub, neg_ne_zero]
    exact mul_ne_zero hc0.ne' F.cross_w_uL
  have hN : 0 < N := Fin.pos iZ
  have hQ1 : F.Q (k + 1) ∈ D.target.carrier := by
    obtain ⟨q, hq⟩ := MarchInduction.mem_range_of_eq hiZ'
      (show F.Q (k + 1) ∈ ({F.J (k + 1), F.Q (k + 1), F.Q k} : Set Plane) by simp)
    rw [← hq]; exact MarchInduction.pts_mem_target D.toDissection iZ q
  have hJ2 : F.J (k + 2) ∈ D.target.carrier := F.J_mem_target (k + 2) hk
  have hJm : F.J (k + 1) ∈ D.target.carrier := F.J_mem_target (k + 1) (by omega)
  -- the approach directions just outside `Z k`'s flank `w` are covered (convexity)
  have hcovn : ∀ n : ℕ, ∃ (j : Fin N) (ε : ℝ), 0 < ε ∧ F.J (k + 1) ∈ (D.tile j).carrier ∧
      F.J (k + 1) + ε • ((F.Q (k + 1) - F.J (k + 1))
        - (1 / ((n : ℝ) + ((1 : ℕ) : ℝ))) • (F.Q k - F.J (k + 1))) ∈ (D.tile j).carrier := by
    intro n
    set t := 1 / ((n : ℝ) + ((1 : ℕ) : ℝ)) with ht
    have ht0 : 0 < t := by rw [ht]; positivity
    have ht1 : t ≤ 1 := by
      rw [ht, Nat.cast_one, div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hD0 : (F.Q (k + 1) - F.J (k + 1)) - t • (F.Q k - F.J (k + 1)) ≠ 0 := by
      intro h0
      have := congrArg (cross (F.Q (k + 1) - F.J (k + 1))) h0
      rw [cross_sub_right', cross_self', cross_smul_right, zero_sub, cross_zero_right] at this
      have h' : t * cross (F.Q (k + 1) - F.J (k + 1)) (F.Q k - F.J (k + 1)) = 0 := by linarith
      rcases mul_eq_zero.mp h' with h | h
      · linarith
      · exact hΔ h
    refine cover_tile_dir D.tile (F.J (k + 1)) hN hD0 one_pos (fun τ hτ hτ1 => ?_)
    rw [D.covers]
    have hM : (1 - t) • F.Q (k + 1) + t • F.J (k + 2) ∈ D.target.carrier :=
      D.target.convex hQ1 hJ2 (by linarith) ht0.le (by ring)
    have hpt := D.target.convex hJm hM (by linarith : (0 : ℝ) ≤ 1 - τ) hτ.le (by ring)
    have e1 : F.J (k + 1) + τ • ((F.Q (k + 1) - F.J (k + 1)) - t • (F.Q k - F.J (k + 1)))
        = (1 - τ) • F.J (k + 1) + τ • ((1 - t) • F.Q (k + 1) + t • F.J (k + 2)) := by
      have hJ2e : F.J (k + 2) = F.J (k + 1) + ((f : ℝ) ^ 2) • F.uL := by
        rw [← F.J_two_sub_J k]; abel
      have hQe : F.Q (k + 1) = F.J (k + 1) + (F.P - F.A) := by rw [← hU0]; abel
      rw [hW0, hJ2e, hQe]; module
    rw [e1]; exact hpt
  -- no tile covering an approach direction meets `Z k`'s open wedge
  have hopen : ∀ j : Fin N, (∃ (n : ℕ) (ε : ℝ), 0 < ε ∧
        F.J (k + 1) + ε • ((F.Q (k + 1) - F.J (k + 1))
          - (1 / ((n : ℝ) + ((1 : ℕ) : ℝ))) • (F.Q k - F.J (k + 1))) ∈ (D.tile j).carrier) →
      ∀ s t τ : ℝ, 0 < s → 0 < t → 0 < τ → τ * (s + t) < 1 →
        F.J (k + 1) + τ • (s • (F.Q (k + 1) - F.J (k + 1)) + t • (F.Q k - F.J (k + 1)))
          ∉ interior (D.tile j).carrier := by
    intro j ⟨n, ε, hε, hy⟩ s t τ hs ht hτ hτ1 hz
    by_cases hji : j = iZ
    · subst hji
      exact not_cover_own hmZ hflZ (invK_pos le_rfl n) hε hy
    · have z1 := open_dir_interior (D.tile iZ) mZ hmZ hflZ hs ht hτ hτ1
      exact Set.disjoint_left.mp (D.interiors_disjoint (Ne.symm hji)) z1 hz
  obtain ⟨j, hJj, ⟨n, ε, hε, hy⟩, hcase⟩ :=
    flank_neighbour_gen D.tile (F.J (k + 1)) hΔ 1 le_rfl hcovn hopen
  have hjZ : j ≠ iZ := by
    rintro rfl; exact not_cover_own hmZ hflZ (invK_pos le_rfl n) hε hy
  rcases hcase with ⟨m, hm, U', W', hUW', S, hS, hU, hside⟩ | ⟨m, -, hmpos, -, -⟩
  swap
  · exfalso
    obtain ⟨m', hm'⟩ := hvert j hJj
    exact NearBaseVertex.vertex_not_edge (D.tile j) m' hm' m hmpos
  -- `j` is not the row tile: its flanks at `J (k+1)` are `−c·uL` and `Q k − J (k+1)`
  have hjY : j ≠ iY := by
    rintro rfl
    obtain ⟨mY, hmY⟩ := MarchInduction.mem_range_of_eq hiY' (Set.mem_insert _ _)
    have hmm : mY = m := (D.tile j).indep.injective (hmY.trans hm.symm)
    subst hmm
    have hflY : IsFlankPair (D.tile j) mY (F.J (k + 1)) (F.J k - F.J (k + 1))
        (F.Q k - F.J (k + 1)) := by
      rcases MarchInduction.vertex_data_of_range hiY' hmY with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; exact ⟨by rw [h1], by rw [h2]⟩
      · right; exact ⟨by rw [h2], by rw [h1]⟩
    have hJk : F.J k - F.J (k + 1) = (-((f : ℝ) ^ 2)) • F.uL := by
      rw [neg_smul, ← F.J_succ_sub_J k]; abel
    rcases flank_cases hflY hUW' with ⟨hU', -⟩ | ⟨hU', -⟩
    · rw [hU', hJk] at hU
      have := congrArg (cross F.uL) hU
      rw [hU0, cross_smul_right, cross_smul_right, cross_self', mul_zero, mul_zero] at this
      exact F.cross_uL_w this
    · rw [hU'] at hU
      have := congrArg (cross (F.Q (k + 1) - F.J (k + 1))) hU
      rw [cross_self', cross_smul_right] at this
      rcases mul_eq_zero.mp this.symm with h | h
      · linarith
      · exact hΔ h
  have hjα : (D.tile j).localAngle (F.J (k + 1)) = α := by
    rcases vertex_angle F hX j hm with h | h | h
    · exact h
    · exact absurd (eq_of_card_one cB (mem_filter_of h) (mem_filter_of hYβ)) hjY
    · exact absurd (eq_of_card_one cC (mem_filter_of h) (mem_filter_of hZγ)) hjZ
  exact ⟨j, alpha_ident F hX k hm hUW' hS hU hside hjα⟩


/-- **The step at `P′` (G1, first half).**  `T₂`, `T₃`, `M` present `γ` at the interior point `P′`,
so the figure there is `{β, γ, γ, γ}` and every tile at `P′` has it as a vertex.  The tile across
`T₃`'s flank `P′J₁` is none of `T₂`, `T₃`, `M` (flank directions), hence the `β`-tile; it is `Z 0`. -/
theorem pprime_step (F : R2Frame D e f α β γ) (hX : R2Extra F) : Present D (F.Z 0) := by
  classical
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast hX.he2
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast hX.hef2
  have hc0 : (0 : ℝ) < (f : ℝ) ^ 2 := by nlinarith
  have hb0 : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have ha0 : (0 : ℝ) < (e : ℝ) * f := by nlinarith
  have hAD := F.hA
  obtain ⟨hab, hac, hbc⟩ :=
    HalfTurnR3R4Glue.sides_distinct F.hco hX.he2 (by have := hX.hef2; omega)
  have hloc := fun {i : Fin N} {P Q R : Plane} (hr : Set.range (D.tile i).pts = {P, Q, R}) =>
    HalfTurnR3R4Glue.localAngle_of_rangeE D hab hac hbc F.hM.hs0 F.hM.hs1 F.hM.hs2 F.hM.hα'
      F.hM.hβ' F.hM.hγ' hr
  set J1 := F.A + ((f : ℝ) ^ 2) • F.uL with hJ1
  set As := F.P + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uL with hAs
  obtain ⟨i2, h2⟩ := F.hT2
  obtain ⟨i3, h3⟩ := F.hT3
  obtain ⟨iM, hMr⟩ := F.hMir
  have h2' : Set.range (D.tile i2).pts = {F.P, F.A, F.V} := by
    rw [h2]; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have h3' : Set.range (D.tile i3).pts = {F.P, J1, F.A} := by
    rw [h3]; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hM' : Set.range (D.tile iM).pts = {F.P, F.V, As} := by
    rw [hMr]; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hgJ1 : F.g J1 = F.g F.A := by rw [hJ1, map_add, map_smul, F.hguL, smul_zero, add_zero]
  have hgAs : F.g As = F.g F.P := by rw [hAs, map_add, map_smul, F.hguL, smul_zero, add_zero]
  have hgA := F.hgA
  have hgV := F.hgV
  -- the three `γ`'s at `P′`
  have g2 : (D.tile i2).localAngle F.P = γ := (hloc h2').2.2 F.hAV
  have g3 : (D.tile i3).localAngle F.P = γ := by
    apply (hloc h3').2.2
    rw [dist_comm]; exact HalfTurnR3R4Glue.dist_self_add_unit F.huL hc0.le
  have hAsP : dist As F.P = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rw [hAs, dist_eq_norm, add_sub_cancel_left, norm_smul, F.huL, mul_one,
      Real.norm_of_nonneg hb0.le]
  have gM : (D.tile iM).localAngle F.P = γ :=
    (hloc hM').2.2 (third_side_c F hX hM' F.hVP hAsP)
  -- distinctness
  have hVA : F.V ≠ F.A := by intro h; rw [h] at hgV; linarith
  have hVP : F.V ≠ F.P := by intro h; rw [h] at hgV; linarith
  have hVJ : F.V ≠ J1 := by intro h; rw [h, hgJ1] at hgV; linarith
  have hAP : F.A ≠ F.P := by intro h; rw [h] at hgA; linarith
  have hAAs : F.A ≠ As := by intro h; rw [h, hgAs] at hgA; linarith
  have h23 : i2 ≠ i3 := by
    intro h; rw [h] at h2'
    have : F.V ∈ ({F.P, J1, F.A} : Set Plane) := by rw [← h3', h2']; simp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with h | h | h
    · exact hVP h
    · exact hVJ h
    · exact hVA h
  have h2M : i2 ≠ iM := by
    intro h; rw [h] at h2'
    have : F.A ∈ ({F.P, F.V, As} : Set Plane) := by rw [← hM', h2']; simp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with h | h | h
    · exact hAP h
    · exact hVA h.symm
    · exact hAAs h
  have h3M : i3 ≠ iM := by
    intro h; rw [h] at h3'
    have : F.A ∈ ({F.P, F.V, As} : Set Plane) := by rw [← hM', h3']; simp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with h | h | h
    · exact hAP h
    · exact hVA h.symm
    · exact hAAs h
  -- counting at `P′`
  obtain ⟨E1, E2⟩ := interior_card_eqs D hAD F.hM.hα' F.hM.hβ' F.hM.hγ' hX.hPint
  have hsub : ({i2, i3, iM} : Finset (Fin N)) ⊆
      ({i | (D.tile i).localAngle F.P = γ} : Finset (Fin N)) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact mem_filter_of g2
    · exact mem_filter_of g3
    · exact mem_filter_of gM
  have h3card : ({i2, i3, iM} : Finset (Fin N)).card = 3 :=
    Finset.card_eq_three.mpr ⟨i2, i3, iM, h23, h2M, h3M, rfl⟩
  have hC3 := Finset.card_le_card hsub
  rw [h3card] at hC3
  have hvert : ∀ i, F.P ∈ (D.tile i).carrier → ∃ m, (D.tile i).pts m = F.P := by
    intro i hi
    by_contra hv; push Not at hv
    rcases HalfTurnR3R4Order.localAngle_mem_pi_of_mem (D.tile i) hi hv with h | h
    · have : 1 ≤ ({i | (D.tile i).localAngle F.P = 2 * Real.pi} : Finset (Fin N)).card :=
        Finset.card_pos.mpr ⟨i, mem_filter_of h⟩
      omega
    · have : 1 ≤ ({i | (D.tile i).localAngle F.P = Real.pi} : Finset (Fin N)).card :=
        Finset.card_pos.mpr ⟨i, mem_filter_of h⟩
      omega
  -- the tile across `T₃`'s flank `P′J₁`
  obtain ⟨m3, hm3⟩ := MarchInduction.mem_range_of_eq h3' (Set.mem_insert _ _)
  have hfl3 : IsFlankPair (D.tile i3) m3 F.P (J1 - F.P) (F.A - F.P) := by
    rcases MarchInduction.vertex_data_of_range h3' hm3 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨by rw [h1], by rw [h2]⟩
    · right; exact ⟨by rw [h2], by rw [h1]⟩
  obtain ⟨z, hz3, hPz, hcase⟩ := flank_neighbour_dissection D.toDissection hX.hPint hm3 hfl3
  rcases hcase with ⟨mz, hmz, U, W, hUW, S, hS, hJU, hside⟩ | ⟨m', -, hmpos, -, -⟩
  swap
  · exfalso
    obtain ⟨m'', hm''⟩ := hvert z hPz
    exact NearBaseVertex.vertex_not_edge (D.tile z) m'' hm'' m' hmpos
  have hJP : J1 - F.P = ((f : ℝ) ^ 2) • F.uL - (F.P - F.A) := by rw [hJ1]; abel
  have hJPn : ‖J1 - F.P‖ = (e : ℝ) * f := by rw [hJP]; exact F.cw_norm
  have hwneg : cross (F.P - F.A) (F.A - F.P) = 0 := by
    simp only [NearBaseVertex.cross_apply, PiLp.sub_apply]; ring
  -- `J₁ − P′` is not along `V − P′`, `A − P′`, `uL`
  have hnotV : ∀ S : ℝ, 0 < S → J1 - F.P ≠ S • (F.V - F.P) := by
    intro S hS h
    have hn : ‖J1 - F.P‖ = S * ‖F.V - F.P‖ := by rw [h, norm_smul, Real.norm_of_nonneg hS.le]
    rw [hJPn, ← dist_eq_norm, F.hVP] at hn
    have hS1 : S = 1 := by
      have : S * ((e : ℝ) * f) = 1 * ((e : ℝ) * f) := by linarith
      exact mul_right_cancel₀ ha0.ne' this
    rw [hS1, one_smul] at h
    exact hVJ (sub_left_inj.mp h).symm
  have hnotA : ∀ S : ℝ, J1 - F.P ≠ S • (F.A - F.P) := by
    intro S h
    have := congrArg (cross (F.P - F.A)) h
    rw [cross_smul_right, hwneg, mul_zero, hJP, cross_sub_right', cross_self', sub_zero,
      cross_smul_right] at this
    rcases mul_eq_zero.mp this with h' | h'
    · linarith
    · exact F.cross_w_uL h'
  have hnotL : ∀ S : ℝ, J1 - F.P ≠ S • (As - F.P) := by
    intro S h
    have hAs' : As - F.P = ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uL := by rw [hAs]; abel
    rw [hAs'] at h
    have := congrArg (cross F.uL) h
    rw [hJP, cross_sub_right', cross_smul_right, cross_self', mul_zero, zero_sub,
      cross_smul_right, cross_smul_right, cross_self', mul_zero, mul_zero, neg_eq_zero] at this
    exact F.cross_uL_w this
  have hz2 : z ≠ i2 := by
    rintro rfl
    obtain ⟨m2, hm2⟩ := MarchInduction.mem_range_of_eq h2' (Set.mem_insert _ _)
    have hmm : m2 = mz := (D.tile z).indep.injective (hm2.trans hmz.symm)
    subst hmm
    have hfl2 : IsFlankPair (D.tile z) m2 F.P (F.A - F.P) (F.V - F.P) := by
      rcases MarchInduction.vertex_data_of_range h2' hm2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; exact ⟨by rw [h1], by rw [h2]⟩
      · right; exact ⟨by rw [h2], by rw [h1]⟩
    rcases flank_cases hfl2 hUW with ⟨hU', -⟩ | ⟨hU', -⟩
    · rw [hU'] at hJU; exact hnotA S hJU
    · rw [hU'] at hJU; exact hnotV S hS hJU
  have hzM : z ≠ iM := by
    rintro rfl
    obtain ⟨m2, hm2⟩ := MarchInduction.mem_range_of_eq hM' (Set.mem_insert _ _)
    have hmm : m2 = mz := (D.tile z).indep.injective (hm2.trans hmz.symm)
    subst hmm
    have hflM : IsFlankPair (D.tile z) m2 F.P (F.V - F.P) (As - F.P) := by
      rcases MarchInduction.vertex_data_of_range hM' hm2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; exact ⟨by rw [h1], by rw [h2]⟩
      · right; exact ⟨by rw [h2], by rw [h1]⟩
    rcases flank_cases hflM hUW with ⟨hU', -⟩ | ⟨hU', -⟩
    · rw [hU'] at hJU; exact hnotV S hS hJU
    · rw [hU'] at hJU; exact hnotL S hJU
  have hzβ : (D.tile z).localAngle F.P = β := by
    rcases vertex_angle F hX z hmz with h | h | h
    · have : 1 ≤ ({i | (D.tile i).localAngle F.P = α} : Finset (Fin N)).card :=
        Finset.card_pos.mpr ⟨z, mem_filter_of h⟩
      omega
    · exact h
    · exfalso
      have hle : ({i | (D.tile i).localAngle F.P = γ} : Finset (Fin N)).card
          ≤ ({i2, i3, iM} : Finset (Fin N)).card := by rw [h3card]; omega
      have heq := Finset.eq_of_subset_of_card_le hsub hle
      have hzmem : z ∈ ({i2, i3, iM} : Finset (Fin N)) := by rw [heq]; exact mem_filter_of h
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzmem
      rcases hzmem with h | h | h
      · exact hz2 h
      · exact hz3 h
      · exact hzM h
  -- the `β`-tile is `Z 0`
  have eQ : F.Q 0 = F.P := F.Q_zero
  have eJ1 : F.J (0 + 1) = J1 := F.J_one
  have eJ0 : F.J 0 = F.A := F.J_zero
  rw [← eJ0] at hside
  rw [← eQ] at hmz hUW hzβ hJU hside
  rw [← eJ1] at hJU hside
  exact ⟨z, beta_ident F hX 0 (by rw [eQ]; exact hX.hPint) hmz hUW hS hJU hside hzβ⟩

theorem fin3_add_two_add_two (m : Fin 3) : m + 2 + 2 = m + 1 := by fin_cases m <;> decide

/-- **The step at `Q (k+1)` (G2, first half).**  `Z k` (`α`), `Z′ k` (`γ`) and the straight band edge
through `Q (k+1)` leave one `β`; the tile across `Z′ k`'s flank `Q (k+1) J (k+2)` is that `β`-tile (the
edge case would put a second straight edge through `Q (k+1)`, not along `L`), and it is `Z (k+1)`. -/
theorem qk_step (F : R2Frame D e f α β γ) (hX : R2Extra F) (k : ℕ) (hk : k + 3 ≤ f)
    (hZp : Present D (F.Z k)) (hZ'p : Present D (F.Z' k))
    (hthrough : ∃ ε ∈ F.band, R2Frame.Straddles (D := D) (F.Q (k + 1)) ε) :
    Present D (F.Z (k + 1)) := by
  classical
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast hX.he2
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast hX.hef2
  have hc0 : (0 : ℝ) < (f : ℝ) ^ 2 := by nlinarith
  have hAD := F.hA
  obtain ⟨hab, hac, hbc⟩ :=
    HalfTurnR3R4Glue.sides_distinct F.hco hX.he2 (by have := hX.hef2; omega)
  have hloc := fun {i : Fin N} {P Q R : Plane} (hr : Set.range (D.tile i).pts = {P, Q, R}) =>
    HalfTurnR3R4Glue.localAngle_of_rangeE D hab hac hbc F.hM.hs0 F.hM.hs1 F.hM.hs2 F.hM.hα'
      F.hM.hβ' F.hM.hγ' hr
  -- `Q (k+1)` is interior
  have hxint : F.Q (k + 1) ∈ interior D.target.carrier := by
    have hk' : ((k + 1 : ℕ) : ℝ) < (f : ℝ) - 1 := by
      have : ((k + 3 : ℕ) : ℝ) ≤ f := by exact_mod_cast hk
      push_cast at this ⊢; linarith
    exact F.hLint _ (mul_pos (by positivity) hc0) (mul_lt_mul_of_pos_right hk' hc0)
  obtain ⟨iA, hiA⟩ := hZp
  obtain ⟨iC, hiC⟩ := hZ'p
  obtain ⟨ε, hεb, hstr⟩ := hthrough
  have hiA' : Set.range (D.tile iA).pts = {F.Q (k + 1), F.Q k, F.J (k + 1)} := by
    rw [hiA, R2Frame.Z]; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hiC' : Set.range (D.tile iC).pts = {F.Q (k + 1), F.J (k + 2), F.J (k + 1)} := by
    rw [hiC, R2Frame.Z']; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have gA : (D.tile iA).localAngle (F.Q (k + 1)) = α := by
    apply (hloc hiA').1
    rw [dist_comm, dist_eq_norm, F.J_succ_sub_Q]; exact F.cw_norm
  have gC : (D.tile iC).localAngle (F.Q (k + 1)) = γ := by
    apply (hloc hiC').2.2
    rw [dist_eq_norm, F.J_two_sub_J]; exact F.c_norm
  -- the band tile: `Q (k+1)` inside its edge on `L`
  obtain ⟨hc2, hc0', hc1⟩ := openSeg_coords (D.tile ε.1) ε.2 hstr
  have hxb : F.Q (k + 1) ∈ (D.tile ε.1).carrier := by
    rw [NearBaseVertex.mem_carrier_iff]; intro l
    rcases HalfTurnR3R4Order.fin3_cases3 ε.2 l with rfl | rfl | rfl
    · exact hc0'.le
    · exact hc1.le
    · exact hc2.ge
  have hbpos : ∀ l, l ≠ ε.2 + 2 → 0 < (D.tile ε.1).basis.coord l (F.Q (k + 1)) := by
    intro l hl
    rcases HalfTurnR3R4Order.fin3_cases3 ε.2 l with rfl | rfl | rfl
    · exact hc0'
    · exact hc1
    · exact absurd rfl hl
  have hbnv : ∀ q, (D.tile ε.1).pts q ≠ F.Q (k + 1) := fun q hq =>
    NearBaseVertex.vertex_not_edge _ q hq _ hbpos
  have hbang := HalfTurnR3R4Order.localAngle_mem_pi_of_mem (D.tile ε.1) hxb hbnv
  -- counting: one each of `α`, `β`, `γ`, `π`
  obtain ⟨E1, E2⟩ := interior_card_eqs D hAD F.hM.hα' F.hM.hβ' F.hM.hγ' hxint
  have cA1 : 1 ≤ ({i | (D.tile i).localAngle (F.Q (k + 1)) = α} : Finset (Fin N)).card :=
    Finset.card_pos.mpr ⟨iA, mem_filter_of gA⟩
  have cC1 : 1 ≤ ({i | (D.tile i).localAngle (F.Q (k + 1)) = γ} : Finset (Fin N)).card :=
    Finset.card_pos.mpr ⟨iC, mem_filter_of gC⟩
  have hbπ : (D.tile ε.1).localAngle (F.Q (k + 1)) = Real.pi := by
    rcases hbang with h | h
    · exfalso
      have : 1 ≤ ({i | (D.tile i).localAngle (F.Q (k + 1)) = 2 * Real.pi} :
          Finset (Fin N)).card := Finset.card_pos.mpr ⟨ε.1, mem_filter_of h⟩
      omega
    · exact h
  have cP1 : 1 ≤ ({i | (D.tile i).localAngle (F.Q (k + 1)) = Real.pi} : Finset (Fin N)).card :=
    Finset.card_pos.mpr ⟨ε.1, mem_filter_of hbπ⟩
  have cA : ({i | (D.tile i).localAngle (F.Q (k + 1)) = α} : Finset (Fin N)).card = 1 := by omega
  have cC : ({i | (D.tile i).localAngle (F.Q (k + 1)) = γ} : Finset (Fin N)).card = 1 := by omega
  have cP : ({i | (D.tile i).localAngle (F.Q (k + 1)) = Real.pi} : Finset (Fin N)).card = 1 := by
    omega
  have cU : ({i | (D.tile i).localAngle (F.Q (k + 1)) = 2 * Real.pi} : Finset (Fin N)).card = 0 :=
    by omega
  -- the tile across `Z′ k`'s flank `Q (k+1) J (k+2)`
  obtain ⟨mC, hmC⟩ := MarchInduction.mem_range_of_eq hiC' (Set.mem_insert _ _)
  have hflC : IsFlankPair (D.tile iC) mC (F.Q (k + 1)) (F.J (k + 2) - F.Q (k + 1))
      (F.J (k + 1) - F.Q (k + 1)) := by
    rcases MarchInduction.vertex_data_of_range hiC' hmC with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨by rw [h1], by rw [h2]⟩
    · right; exact ⟨by rw [h2], by rw [h1]⟩
  have hU0 : F.J (k + 2) - F.Q (k + 1) = ((f : ℝ) ^ 2) • F.uL - (F.P - F.A) := F.J_two_sub_Q k
  have hgU0 : F.g (F.J (k + 2) - F.Q (k + 1)) ≠ 0 := by
    rw [hU0, map_sub, map_smul, F.hguL, smul_zero, zero_sub, neg_ne_zero]
    exact F.gw_pos.ne'
  obtain ⟨z, hzC, hxz, hcase⟩ := flank_neighbour_dissection D.toDissection hxint hmC hflC
  rcases hcase with ⟨mz, hmz, U, W, hUW, S, hS, hJU, hside⟩ | ⟨m, hm0, hmpos, hcr, -⟩
  swap
  · -- edge case: `z` would be the band tile, with a second straight edge through `Q (k+1)`
    exfalso
    have hznv : ∀ q, (D.tile z).pts q ≠ F.Q (k + 1) := fun q hq =>
      NearBaseVertex.vertex_not_edge _ q hq m hmpos
    have hzπ : (D.tile z).localAngle (F.Q (k + 1)) = Real.pi := by
      rcases HalfTurnR3R4Order.localAngle_mem_pi_of_mem (D.tile z) hxz hznv with h | h
      · exfalso
        have : 1 ≤ ({i | (D.tile i).localAngle (F.Q (k + 1)) = 2 * Real.pi} :
            Finset (Fin N)).card := Finset.card_pos.mpr ⟨z, mem_filter_of h⟩
        omega
      · exact h
    have hzb : z = ε.1 := eq_of_card_one cP (mem_filter_of hzπ) (mem_filter_of hbπ)
    subst hzb
    have hm : m = ε.2 + 2 := by
      by_contra hne
      have := hmpos (ε.2 + 2) (Ne.symm hne)
      linarith
    subst hm
    rw [fin3_add_two_add_two, HalfTurnR3R4Order.fin3_add_two_add_one] at hcr
    have hε' : ε ∈ D.toDissection.lineChain (-F.g) (-(F.g F.P)) := hεb
    obtain ⟨h0, h1, -⟩ := Dissection.mem_lineChain.mp hε'
    rw [LinearMap.neg_apply] at h0 h1
    have hd0 : (D.tile ε.1).pts (ε.2 + 1) - (D.tile ε.1).pts ε.2 ≠ 0 := by
      have hne' : ∀ x : Fin 3, x ≠ x + 1 := by decide
      exact sub_ne_zero.mpr (pts_ne _ (hne' _)).symm
    have hgd : F.g ((D.tile ε.1).pts (ε.2 + 1) - (D.tile ε.1).pts ε.2) = 0 := by
      rw [map_sub]; linarith
    exact cross_ne_of_g F.g hd0 hgd hgU0 hcr
  -- vertex case: `z` is none of `Z k`, `Z′ k`, the band tile, so it is the `β`-tile
  have hzA : z ≠ iA := by
    rintro rfl
    obtain ⟨mA, hmA⟩ := MarchInduction.mem_range_of_eq hiA' (Set.mem_insert _ _)
    have hmm : mA = mz := (D.tile z).indep.injective (hmA.trans hmz.symm)
    subst hmm
    have hflA : IsFlankPair (D.tile z) mA (F.Q (k + 1)) (F.Q k - F.Q (k + 1))
        (F.J (k + 1) - F.Q (k + 1)) := by
      rcases MarchInduction.vertex_data_of_range hiA' hmA with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; exact ⟨by rw [h1], by rw [h2]⟩
      · right; exact ⟨by rw [h2], by rw [h1]⟩
    rcases flank_cases hflA hUW with ⟨hU', -⟩ | ⟨hU', -⟩
    · rw [hU'] at hJU
      have hQk : F.Q k - F.Q (k + 1) = (-((f : ℝ) ^ 2)) • F.uL := by
        rw [neg_smul, ← F.Q_succ_sub_Q k]; abel
      rw [hQk] at hJU
      have := congrArg (cross F.uL) hJU
      rw [hU0, cross_sub_right', cross_smul_right, cross_self', mul_zero, zero_sub,
        cross_smul_right, cross_smul_right, cross_self', mul_zero, mul_zero, neg_eq_zero] at this
      exact F.cross_uL_w this
    · rw [hU'] at hJU
      rw [hJU] at hside
      simp [cross_smul_left'] at hside
  have hzβ : (D.tile z).localAngle (F.Q (k + 1)) = β := by
    rcases vertex_angle F hX z hmz with h | h | h
    · exact absurd (eq_of_card_one cA (mem_filter_of h) (mem_filter_of gA)) hzA
    · exact h
    · exact absurd (eq_of_card_one cC (mem_filter_of h) (mem_filter_of gC)) hzC
  exact ⟨z, beta_ident F hX (k + 1) hxint hmz hUW hS hJU hside hzβ⟩

/-! ## §6 G1, G2 and the assembly -/

/-- **G1 — `strip_base`, PROVED** (under `R2Extra`). -/
theorem strip_base' (F : R2Frame D e f α β γ) (hX : R2Extra F) :
    Present D (F.Z 0) ∧ Present D (F.Z' 0) := by
  have h0 := pprime_step F hX
  refine ⟨h0, leg_step F hX 0 (by have := hX.hef2; omega) ?_ h0⟩
  obtain ⟨i3, h3⟩ := F.hT3
  refine ⟨i3, ?_⟩
  rw [h3, F.J_zero, show F.J (0 + 1) = F.A + ((f : ℝ) ^ 2) • F.uL from F.J_one, F.Q_zero]
  ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

/-- **G2 — `strip_step`, PROVED** (under `R2Extra`). -/
theorem strip_step' (F : R2Frame D e f α β γ) (hX : R2Extra F) (k : ℕ) (hk1 : 1 ≤ k)
    (hkf : k ≤ f - 2) (hprev : ∀ j < k, Present D (F.Z j) ∧ Present D (F.Z' j))
    (hthrough : ∃ ε ∈ F.band, R2Frame.Straddles (D := D) (F.Q k) ε) :
    Present D (F.Z k) ∧ Present D (F.Z' k) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hf := hX.hef2
  have hZ := qk_step F hX k' (by omega) (hprev k' (by omega)).1 (hprev k' (by omega)).2 hthrough
  exact ⟨hZ, leg_step F hX (k' + 1) (by omega) (hprev k' (by omega)).2 hZ⟩

/-- **R2, PROVED (under `R2Extra`): the mirror branch (M) is impossible at `m = 1`.**  The assembly
of `MirrorStripR2Glue.mirror_impossible` with G1, G2 discharged (`strip_base'`, `strip_step'`), G3
(`band_junction_rep`) and G4 (`base_is_junction`), and Lemma A (`Inflation.c_side_no_b`). -/
theorem mirror_impossible' (F : R2Frame D e f α β γ) (hX : R2Extra F) : False := by
  have hf2 : 2 ≤ f := by have := hX.hef2; omega
  have hee : e ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left F.hef.le 2
  have lemA : ∀ k na nb nc : ℕ, k < f →
      na * (e * f) + nb * (f ^ 2 - e ^ 2) + nc * f ^ 2 = k * f ^ 2 → nb = 0 :=
    fun k na nb nc hk h =>
      Inflation.c_side_no_b e f (f ^ 2 - e ^ 2) k na nb nc F.he F.hef F.hco (by omega) hk h
  have hall : ∀ k, k ≤ f - 2 → ∀ j ≤ k, Present D (F.Z j) ∧ Present D (F.Z' j) := by
    intro k
    induction k with
    | zero =>
      intro _ j hj
      have : j = 0 := by omega
      subst this
      exact strip_base' F hX
    | succ k ih =>
      intro hk j hj
      have hprev : ∀ j < k + 1, Present D (F.Z j) ∧ Present D (F.Z' j) :=
        fun j hj' => ih (by omega) j (by omega)
      rcases Nat.lt_or_ge j (k + 1) with hlt | hge
      · exact hprev j hlt
      · have hj' : j = k + 1 := by omega
        subst hj'
        have hthrough : ∃ ε ∈ F.band, R2Frame.Straddles (D := D) (F.Q (k + 1)) ε := by
          by_contra hno
          push Not at hno
          obtain ⟨na, nb, nc, hnb, hrep⟩ :=
            F.band_junction_rep (k + 1) (by omega) (by omega) hprev hno
          have := lemA (k + 1) na nb nc (by omega) hrep
          omega
        exact strip_step' F hX (k + 1) (by omega) hk hprev hthrough
  have hprev : ∀ j < f - 1, Present D (F.Z j) ∧ Present D (F.Z' j) :=
    fun j hj => hall (f - 2) le_rfl j (by omega)
  obtain ⟨na, nb, nc, hnb, hrep⟩ :=
    F.band_junction_rep (f - 1) (by omega) le_rfl hprev F.base_is_junction
  have := lemA (f - 1) na nb nc (by omega) hrep
  omega


/-! ## §7 `R2Extra` for a real `m = 1` dissection -/

open Erdos634.Draft.ApexR2Frame in
set_option maxHeartbeats 1000000 in
/-- **The mirror frame from a real dissection in branch (M), with its link to the apex frame.**
Verbatim copy of `ApexR2Frame.r2frame_of_mirror` (whose conclusion is only `Nonempty`), recording that
the constructed `R2Frame` has the apex frame's `A`, `P′`, `uL` — needed to transport `P′ ∈ interior`. -/
theorem r2frame_of_mirror_eq {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ}
    (F : HalfTurnR3R4Glue.HFrame D e f α β γ) (FC : FrameCoords F) {M : Plane}
    (hMir : HalfTurnR3R4Glue.IsMirror F.A F.V F.P M)
    (hMP : HalfTurnR3R4Glue.Present D {F.V, F.P, M}) :
    ∃ G : MirrorStripR2Glue.R2Frame D e f α β γ, G.A = F.A ∧ G.P = F.P ∧ G.uL = F.uL := by
  classical
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast F.he
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast F.hef
  have he0 : (0 : ℝ) < e := by linarith
  have hf0 : (0 : ℝ) < f := by linarith
  have hb0 : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hK : (0 : ℝ) < 3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hMeq := mirror_eq F FC hMir
  obtain ⟨s3, t3, hs3, ht3, hP, hv3, hsum3⟩ := FC.hP
  obtain ⟨s1, t1, hs1, ht1, hV, hv1, hsum1⟩ := FC.hV
  set b : ℝ := (f : ℝ) ^ 2 - (e : ℝ) ^ 2 with hbdef
  have hbne := hb0.ne'
  obtain ⟨v, hvdef⟩ : ∃ v : Plane, v = ((f : ℝ) ^ 3) • F.uL := ⟨_, rfl⟩
  obtain ⟨u, hudef⟩ : ∃ u : Plane, u = F.R - F.A := ⟨_, rfl⟩
  rw [← hvdef, ← hudef] at hP hV
  have hd : cross v u ≠ 0 := by
    have := FC.hcone.det
    rw [show F.A + ((f : ℝ) ^ 3) • F.uL - F.A = v by rw [hvdef]; abel, ← hudef] at this
    exact this
  have huL : F.uL = (1 / (f : ℝ) ^ 3) • v := by
    rw [hvdef, smul_smul, one_div_mul_cancel (by positivity), one_smul]
  have hPe : F.P - F.A = s3 • v + t3 • u := hP
  have hVe : F.V - F.A = ((f : ℝ) ^ 2 / b) • (s1 • v + t1 • u) := by
    rw [F.hV, add_sub_cancel_left, ← hV, smul_smul, div_mul_cancel₀ _ hbne]
  -- `g`: the normal functional of the leg, positive into the target
  set g : Plane →ₗ[ℝ] ℝ := (cross v u) • Erdos634.Geometry.crossL v with hgdef
  have happ : ∀ w, g w = cross v u * cross v w := fun w => by
    rw [hgdef, LinearMap.smul_apply, Erdos634.Geometry.crossL_apply, smul_eq_mul]
  have hgcomb : ∀ x y : ℝ, g (x • v + y • u) = y * (cross v u) ^ 2 := by
    intro x y
    rw [happ, cross_add_right, cross_smul_right, cross_smul_right, cross_self']; ring
  have hd2 : 0 < (cross v u) ^ 2 := by positivity
  have hgP : g F.P - g F.A = t3 * (cross v u) ^ 2 := by
    rw [← map_sub, hPe, hgcomb]
  have hgV : g F.V - g F.A = (f : ℝ) ^ 2 / b * t1 * (cross v u) ^ 2 := by
    rw [← map_sub, hVe, map_smul, hgcomb, smul_eq_mul]; ring
  -- `t3 < (f²/b)·t1`
  have hlt : t3 < (f : ℝ) ^ 2 / b * t1 := by
    have es1 : s1 = f / (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by rw [eq_div_iff hK.ne']; exact hv1
    have et3 : t3 = f / (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by rw [eq_div_iff hK.ne']; exact hv3
    have et1 : t1 = 1 / (f : ℝ) - f / (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by rw [← es1]; linarith
    rw [et3, et1, hbdef, div_lt_iff₀ hK]
    have : (f : ℝ) ^ 2 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)
        * (1 / (f : ℝ) - f / (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
        = (f : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
      have hK1 : (f : ℝ) ^ 2 * 3 - (e : ℝ) ^ 2 ≠ 0 := by intro h; linarith
      have hK2 := hK.ne'
      have hb1 := hb0.ne'
      have hf1 := hf0.ne'
      field_simp; ring
    rw [this, lt_div_iff₀ hb0]
    nlinarith
  -- the line `L` through `P′` along `uL`, in cone coordinates
  have hLpt : ∀ x : ℝ, F.P + x • F.uL = F.A + ((s3 + x / (f : ℝ) ^ 3) • v + t3 • u) := by
    intro x
    have : F.P = F.A + (s3 • v + t3 • u) := by rw [← hPe]; abel
    rw [this, huL]; module
  have hgV' : g F.P < g F.V := by
    have := mul_lt_mul_of_pos_right hlt hd2
    linarith
  have hgA' : g F.A < g F.P := by
    have := mul_pos ht3 hd2
    linarith
  obtain ⟨i2, hi2⟩ := F.hT2
  obtain ⟨i3, hi3⟩ := F.hT3
  obtain ⟨iM, hiM⟩ := hMP
  refine ⟨{
    A := F.A
    P := F.P
    V := F.V
    R := F.R
    uL := F.uL
    g := g
    hco := F.hco
    he := by have := F.he; omega
    hef := by have := F.hef; omega
    hM := ⟨F.hM.hs0, F.hM.hs1, F.hM.hs2, F.hM.hα', F.hM.hβ', F.hM.hγ'⟩
    hA := F.hAng
    htarget := F.htarget
    hlegR := F.hlegR
    huL := F.huL
    hAP := F.hAP
    hAV := by rw [F.hV]; exact HalfTurnR3R4Glue.dist_self_add_unit F.huR (by positivity)
    hVP := F.hVP
    hPJ1 := F.hPJ1
    hg0 := ?_
    hguL := ?_
    hgV := hgV'
    hgA := hgA'
    hbase := ?_
    hLint := ?_
    hT2 := ⟨i2, hi2⟩
    hT3 := ⟨i3, hi3⟩
    hMir := ⟨iM, by rw [hiM, hMeq]⟩ }, rfl, rfl, rfl⟩
  · intro h0
    have := congrArg (fun φ : Plane →ₗ[ℝ] ℝ => φ u) h0
    simp only [LinearMap.zero_apply] at this
    have h1 := hgcomb 0 1
    rw [zero_smul, zero_add, one_smul, this] at h1
    linarith
  · rw [huL, map_smul, happ, cross_self', mul_zero, smul_zero]
  · intro t ht hmem
    rw [hLpt, hvdef, hudef] at hmem
    apply FC.hout (s3 + ((((f : ℝ) - 1) * (f : ℝ) ^ 2 + t)) / (f : ℝ) ^ 3) t3 _ hmem
    have : s3 + (((f : ℝ) - 1) * (f : ℝ) ^ 2 + t) / (f : ℝ) ^ 3 + t3
        = 1 + t / (f : ℝ) ^ 3 := by
      have hf3 : (f : ℝ) ^ 3 ≠ 0 := by positivity
      rw [show s3 + (((f : ℝ) - 1) * (f : ℝ) ^ 2 + t) / (f : ℝ) ^ 3 + t3
          = (s3 + t3) + (((f : ℝ) - 1) * (f : ℝ) ^ 2 + t) / (f : ℝ) ^ 3 by ring, hsum3]
      field_simp; ring
    rw [this]
    have : 0 < t / (f : ℝ) ^ 3 := by positivity
    linarith
  · intro t ht ht2
    rw [hLpt]
    have hC := FC.hcone
    have := hC.inter (s3 + t / (f : ℝ) ^ 3) t3 1 (by positivity) ht3 one_pos (by
      rw [one_mul, show s3 + t / (f : ℝ) ^ 3 + t3 = (s3 + t3) + t / (f : ℝ) ^ 3 by ring, hsum3]
      have hf3 : (0 : ℝ) < (f : ℝ) ^ 3 := by positivity
      have : t / (f : ℝ) ^ 3 < ((f : ℝ) - 1) / f := by
        rw [div_lt_div_iff₀ hf3 hf0]; nlinarith
      have : 1 / (f : ℝ) + ((f : ℝ) - 1) / f = 1 := by field_simp; ring
      linarith)
    rw [show F.A + ((f : ℝ) ^ 3) • F.uL - F.A = v by rw [hvdef]; abel, ← hudef,
      one_smul] at this
    exact this


/-- `e(3f² − e²) ≠ f³` at a coprime member `e ≥ 2` (else `e ∣ f³`). -/
theorem base_ne_leg {e f : ℕ} (hco : Nat.Coprime e f) (he : 2 ≤ e) :
    (e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ≠ (f : ℝ) ^ 3 := by
  intro h
  have h' : ((e * (3 * f ^ 2) : ℕ) : ℝ) = ((f ^ 3 + e ^ 3 : ℕ) : ℝ) := by
    push_cast; linear_combination h
  have hN : e * (3 * f ^ 2) = f ^ 3 + e ^ 3 := by exact_mod_cast h'
  have hd : e ∣ f ^ 3 := by
    have h1 : e ∣ e ^ 3 + f ^ 3 := ⟨3 * f ^ 2, by rw [add_comm]; exact hN.symm⟩
    exact (Nat.dvd_add_right (dvd_pow_self e (by norm_num))).mp h1
  have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right 3 hco) hd
  omega

theorem fin3_other (q k : Fin 3) (h : q ≠ k) : q = k + 1 ∨ q = k + 2 := by
  revert h; fin_cases q <;> fin_cases k <;> decide

/-- **The apex of a frame is the apex of `M1Data`.**  If the target's vertices are `{A, L, R}` with
`|AL| = |AR| = f³`, then `A` is the `3α` corner `k` (the base `e(3f² − e²)` is not `f³`), and `L` is one
of the base corners. -/
theorem apex_ident {D : CongruentDissection N} {k : Fin 3}
    (h : ApexFrameReal.M1Data D e f α β γ k) {A L R : Plane}
    (ht : Set.range D.target.pts = {A, L, R}) (hAL : dist A L = (f : ℝ) ^ 3)
    (hAR : dist A R = (f : ℝ) ^ 3) :
    A = D.target.pts k ∧ (L = D.target.pts (k + 1) ∨ L = D.target.pts (k + 2)) := by
  have hbl := base_ne_leg (f := f) h.hco h.he
  have hf : (0 : ℝ) < f := by exact_mod_cast (show 0 < f by have := h.hef; omega)
  have hinj := D.target.indep.injective
  obtain ⟨q, hq⟩ : A ∈ Set.range D.target.pts := by rw [ht]; simp
  have hfar : ∀ r, D.target.pts r ≠ A → dist A (D.target.pts r) = (f : ℝ) ^ 3 := by
    intro r hr
    have : D.target.pts r ∈ ({A, L, R} : Set Plane) := ht ▸ ⟨r, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with h1 | h1 | h1
    · exact absurd h1 hr
    · rw [h1]; exact hAL
    · rw [h1]; exact hAR
  have hqk : q = k := by
    by_contra hne
    rcases fin3_other q k hne with rfl | rfl
    · have := hfar (k + 2) (fun h' => absurd (hinj (h'.trans hq.symm)) (by fin_cases k <;> decide))
      rw [← hq, h.hbase] at this; exact hbl this
    · have := hfar (k + 1) (fun h' => absurd (hinj (h'.trans hq.symm)) (by fin_cases k <;> decide))
      rw [← hq, dist_comm, h.hbase] at this; exact hbl this
  subst hqk
  refine ⟨hq.symm, ?_⟩
  obtain ⟨r, hr⟩ : L ∈ Set.range D.target.pts := by rw [ht]; simp
  have hLA : L ≠ A := by
    intro h'; rw [h', dist_self] at hAL
    have : (0 : ℝ) < (f : ℝ) ^ 3 := by positivity
    linarith
  have hrq : r ≠ q := fun h' => hLA (by rw [← hr, h', hq])
  rcases fin3_other r q hrq with rfl | rfl
  · left; exact hr.symm
  · right; exact hr.symm

open Erdos634.SideWall Erdos634.Draft.ApexLegWord in
/-- **A target side from a `β` corner `k'` to the `3α` apex `k'+1` carries no tile edge of length `b`**
(`ApexLegWord.leg_no_b`, stated for edges given by their two endpoints on the side's line). -/
theorem side_no_b (D : CongruentDissection N) (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e < f)
    (hM : HalfTurnR3R4Glue.ModelDataE D e f α β γ) (hAng : MarchSlots.AngleData α β γ)
    (k' : Fin 3)
    (hcornerbase : cornerAngle (D.target.pts (k' + 1)) (D.target.pts k')
      (D.target.pts (k' + 2)) = β)
    (hcornerapex : cornerAngle (D.target.pts (k' + 1 + 1)) (D.target.pts (k' + 1))
      (D.target.pts (k' + 1 + 2)) = 3 * α)
    (hLen : dist (D.target.pts k') (D.target.pts (k' + 1)) = (f : ℝ) ^ 3)
    (i : Fin N) (m : Fin 3) (s t : ℝ)
    (h1 : (D.tile i).pts m
      = D.target.pts (k' + 1) + s • (D.target.pts k' - D.target.pts (k' + 1)))
    (h2 : (D.tile i).pts (m + 1)
      = D.target.pts (k' + 1) + t • (D.target.pts k' - D.target.pts (k' + 1))) :
    dist ((D.tile i).pts m) ((D.tile i).pts (m + 1)) ≠ (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
  classical
  obtain ⟨hαβ, hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hγπ, hγ0, -, -, -⟩ := angle_facts hAng
  have hN : 0 < N := Fin.pos i
  obtain ⟨hab, hac, hbc⟩ := HalfTurnR3R4Glue.sides_distinct hco he hef
  have h01 : sideOpp D.model 0 ≠ sideOpp D.model 1 := by rw [hM.hs0, hM.hs1]; exact hab
  have h02 : sideOpp D.model 0 ≠ sideOpp D.model 2 := by rw [hM.hs0, hM.hs2]; exact hac
  have h12 : sideOpp D.model 1 ≠ sideOpp D.model 2 := by rw [hM.hs1, hM.hs2]; exact hbc
  have hscalene : ∀ j j' : Fin 3, j ≠ j' → sideOpp D.model j ≠ sideOpp D.model j' := by
    intro j j' hjj'
    fin_cases j <;> fin_cases j' <;> first | exact absurd rfl hjj' | exact h01 | exact h02 | exact h12 | exact h01.symm | exact h02.symm | exact h12.symm
  have hee : e * e ≤ f * f := Nat.mul_le_mul hef.le hef.le
  have hthirdD : ∀ p ∈ Erdos634.BaseChain.wallList D.toDissection (wallFun D.target k') 0,
      wallFun D.target k' ((D.tile p.1).pts (p.2 + 2)) < 0 :=
    hthird_general D.toDissection (wallFun D.target k') 0 (wallFun_linear_ne_zero D.target k')
      (fun y hy => by simpa using wallFun_le D.target k' hy)
  have hnob := leg_no_b D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 Real.pi_ne_zero hAng.hγdef
    hAng.hrel hAng.hirr hscalene hM.hα' hM.hβ' hM.hγ' k' (dirFun D.target k').linear
    (hker_wallFun D.target k') (hdirab_dirFun D.target k') hthirdD hcornerbase hcornerapex
    (hiso_wallFun' D.target k') hN e f (f * f - e * e) hef hco (Nat.sub_add_cancel hee)
    hM.hs0 (by rw [hM.hs1]; push_cast [Nat.cast_sub hee]; ring) hM.hs2 hLen
  have hz : ∀ u : ℝ, wallFun D.target k'
      (D.target.pts (k' + 1) + u • (D.target.pts k' - D.target.pts (k' + 1))) = 0 := by
    intro u
    simp only [wallFun, AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero]
    exact coord_line_zero D.target (show k' + 2 ≠ k' + 1 by fin_cases k' <;> decide)
      (show k' + 2 ≠ k' by fin_cases k' <;> decide) _
  have hq : ((i, m) : Fin N × Fin 3) ∈
      Erdos634.BaseChain.wallList D.toDissection (wallFun D.target k') 0 := by
    rw [Erdos634.BaseChain.mem_wallList]
    exact ⟨by simp only; rw [h1]; exact hz s, by simp only; rw [h2]; exact hz t⟩
  have hnb := hnob (i, m) hq
  simp only at hnb
  rw [hM.hs1] at hnb
  exact hnb

/-- **The legs of a real `m = 1` dissection are `b`-free, in frame form.**  For any description of
the target as `{A, A + f³·uL, R}` with `|AR| = f³`, no tile edge with both endpoints on the line
`A + ℝ·uL` has length `b`. -/
theorem leg_nob_real {D : CongruentDissection N} {k : Fin 3}
    (h : ApexFrameReal.M1Data D e f α β γ k) {A uL R : Plane} (hu : ‖uL‖ = 1)
    (ht : Set.range D.target.pts = {A, A + ((f : ℝ) ^ 3) • uL, R})
    (hAR : dist A R = (f : ℝ) ^ 3) :
    ∀ (i : Fin N) (m : Fin 3) (s t : ℝ), (D.tile i).pts m = A + s • uL →
      (D.tile i).pts (m + 1) = A + t • uL →
      dist ((D.tile i).pts m) ((D.tile i).pts (m + 1)) ≠ (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
  intro i m s t h1 h2
  have hf : (0 : ℝ) < f := by exact_mod_cast (show 0 < f by have := h.hef; omega)
  have hf3 : (f : ℝ) ^ 3 ≠ 0 := by positivity
  have hAL : dist A (A + ((f : ℝ) ^ 3) • uL) = (f : ℝ) ^ 3 :=
    HalfTurnR3R4Glue.dist_self_add_unit hu (by positivity)
  obtain ⟨hA, hL⟩ := apex_ident h ht hAL hAR
  have hpt : ∀ u : ℝ, A + u • uL = A + (u / (f : ℝ) ^ 3) • ((A + ((f : ℝ) ^ 3) • uL) - A) := by
    intro u; rw [add_sub_cancel_left, smul_smul, div_mul_cancel₀ _ hf3]
  have e1 : k + 2 + 1 = k := by fin_cases k <;> rfl
  have e2 : k + 2 + 2 = k + 1 := by fin_cases k <;> rfl
  have e3 : k + 2 + 1 + 1 = k + 1 := by fin_cases k <;> rfl
  have e5 : k + 1 + 1 = k + 2 := by fin_cases k <;> rfl
  have e6 : k + 1 + 2 = k := by fin_cases k <;> rfl
  rcases hL with hL | hL
  · -- the leg `k → k+1`: relabel the target by the transposition `(k, k+1)`
    let σ : Equiv.Perm (Fin 3) := Equiv.swap k (k + 1)
    let D' : CongruentDissection N :=
      { toDissection := Erdos634.NormalPosition.relabelTarget D.toDissection σ
        model := D.model
        tiles_congruent := D.tiles_congruent }
    have hp0 : D'.target.pts k = D.target.pts (k + 1) := by
      show D.target.pts (σ k) = _; simp [σ]
    have hp1 : D'.target.pts (k + 1) = D.target.pts k := by
      show D.target.pts (σ (k + 1)) = _; simp [σ]
    have hp2 : D'.target.pts (k + 2) = D.target.pts (k + 2) := by
      show D.target.pts (σ (k + 2)) = _
      rw [Equiv.swap_apply_of_ne_of_ne (by fin_cases k <;> decide) (by fin_cases k <;> decide)]
    have hM' : HalfTurnR3R4Glue.ModelDataE D' e f α β γ :=
      ⟨h.hM.hs0, h.hM.hs1, h.hM.hs2, h.hM.hα', h.hM.hβ', h.hM.hγ'⟩
    have hb' : cornerAngle (D'.target.pts (k + 1)) (D'.target.pts k) (D'.target.pts (k + 2))
        = β := by
      rw [hp0, hp1, hp2, cornerAngle, EuclideanGeometry.angle_comm]; exact h.hβ1
    have ha' : cornerAngle (D'.target.pts (k + 1 + 1)) (D'.target.pts (k + 1))
        (D'.target.pts (k + 1 + 2)) = 3 * α := by
      rw [e5, e6, hp1, hp2, hp0, cornerAngle, EuclideanGeometry.angle_comm]; exact h.hcorner
    have hL' : dist (D'.target.pts k) (D'.target.pts (k + 1)) = (f : ℝ) ^ 3 := by
      rw [hp0, hp1, dist_comm]; exact h.hleg1
    have hs : ∀ u : ℝ, A + u • uL = D'.target.pts (k + 1)
        + (u / (f : ℝ) ^ 3) • (D'.target.pts k - D'.target.pts (k + 1)) := by
      intro u; rw [hp0, hp1, ← hL, ← hA]; exact hpt u
    exact side_no_b D' h.hco h.he (by have := h.hef; omega) hM' h.hAng k hb' ha' hL' i m _ _
      (h1.trans (hs s)) (h2.trans (hs t))
  · -- the leg `k+2 → k`
    have hb' : cornerAngle (D.target.pts (k + 2 + 1)) (D.target.pts (k + 2))
        (D.target.pts (k + 2 + 2)) = β := by rw [e1, e2]; exact h.hβ2
    have ha' : cornerAngle (D.target.pts (k + 2 + 1 + 1)) (D.target.pts (k + 2 + 1))
        (D.target.pts (k + 2 + 1 + 2)) = 3 * α := by rw [e3, e1]; exact h.hcorner
    have hL' : dist (D.target.pts (k + 2)) (D.target.pts (k + 2 + 1)) = (f : ℝ) ^ 3 := by
      rw [e1, dist_comm]; exact h.hleg2
    have hs : ∀ u : ℝ, A + u • uL = D.target.pts (k + 2 + 1)
        + (u / (f : ℝ) ^ 3) • (D.target.pts (k + 2) - D.target.pts (k + 2 + 1)) := by
      intro u; rw [e1, ← hL, ← hA]; exact hpt u
    exact side_no_b D h.hco h.he (by have := h.hef; omega) h.hM h.hAng (k + 2) hb' ha' hL' i m _ _
      (h1.trans (hs s)) (h2.trans (hs t))

/-- **R2 for a real dissection, frame form — PROVED.**  No `R2Frame` whose `P′` is interior exists
on a real `m = 1` dissection (the frame built from the apex frame has `P′` interior). -/
theorem mirror_impossible_real {D : CongruentDissection N} {k : Fin 3}
    (h : ApexFrameReal.M1Data D e f α β γ k) (G : R2Frame D e f α β γ)
    (hPint : G.P ∈ interior D.target.carrier) : False :=
  mirror_impossible' G ⟨h.he, h.hef, hPint, leg_nob_real h G.huL G.htarget G.hlegR⟩

/-- **Branch (M) never occurs in a real `m = 1` dissection — PROVED.**  In the apex frame of a real
dissection, the mirror of `T₂` across `VP′` is not a tile. -/
theorem no_mirror_real {D : CongruentDissection N} {k : Fin 3}
    (h : ApexFrameReal.M1Data D e f α β γ k) (F : HalfTurnR3R4Glue.HFrame D e f α β γ)
    (FC : FrameCoords F) {M : Plane} (hMir : HalfTurnR3R4Glue.IsMirror F.A F.V F.P M)
    (hMP : HalfTurnR3R4Glue.Present D {F.V, F.P, M}) : False := by
  obtain ⟨G, -, hGP, -⟩ := r2frame_of_mirror_eq F FC hMir hMP
  exact mirror_impossible_real h G (hGP ▸ F.hPint)

/-- **`K_present_real` — branch (H) for EVERY real `m = 1` dissection — PROVED.**  Every congruent
dissection of the `m = 1` base-β target (coprime `2 ≤ e ≤ f − 2`, `M1Data`) carries the apex frame
`F` (with its cone coordinates), and the tile `K = T₂ + (VP′ half-turn)` is present. -/
theorem K_present_real {D : CongruentDissection N} {k : Fin 3}
    (h : ApexFrameReal.M1Data D e f α β γ k) :
    ∃ F : HalfTurnR3R4Glue.HFrame D e f α β γ, FrameCoords F ∧ HalfTurnR3R4Glue.Present D F.K := by
  obtain ⟨F, FC⟩ := ApexLegWord.exists_hframe_coords_m1 D h.hco h.he h.hef h.hM h.hAng k
    h.hcorner h.hβ1 h.hβ2 h.hleg1 h.hleg2 h.hbase
  refine ⟨F, FC, ?_⟩
  rcases TileIdent.lemmaG_frame F with hK | ⟨M, hMir, hMP⟩
  · exact hK
  · exact (no_mirror_real h F FC hMir hMP).elim

end Erdos634.Draft.MirrorStripR2Real

#print axioms Erdos634.Draft.MirrorStripR2Real.leg_step
#print axioms Erdos634.Draft.MirrorStripR2Real.pprime_step
#print axioms Erdos634.Draft.MirrorStripR2Real.qk_step
#print axioms Erdos634.Draft.MirrorStripR2Real.strip_base'
#print axioms Erdos634.Draft.MirrorStripR2Real.strip_step'
#print axioms Erdos634.Draft.MirrorStripR2Real.mirror_impossible'
#print axioms Erdos634.Draft.MirrorStripR2Real.r2frame_of_mirror_eq
#print axioms Erdos634.Draft.MirrorStripR2Real.side_no_b
#print axioms Erdos634.Draft.MirrorStripR2Real.leg_nob_real
#print axioms Erdos634.Draft.MirrorStripR2Real.mirror_impossible_real
#print axioms Erdos634.Draft.MirrorStripR2Real.no_mirror_real
#print axioms Erdos634.Draft.MirrorStripR2Real.K_present_real
