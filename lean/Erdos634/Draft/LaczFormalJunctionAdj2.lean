import Erdos634.Draft.LaczFormalJunctionAdj

/-!
# Band junction rules: the adjacent `α`-tile (derivation of `hU`)

Erdős #634, base-`β` band.  Credit: AI assistant (band lemma / item-3 proposal), Beeson–Roșu, Beeson,
Laczkovich, Paliy.

`exists_alpha_edge`: in the interior-pair configuration `X, cBA` at an interior base point `Q`
(`X` the left neighbour, presenting `β` or `γ` at `Q`), there is a tile `U` with a vertex at `Q`
and an edge along the ray `QG` of length `b` or `c`, hence longer than `a = |QG|`; so `G` lies
strictly inside that edge.  This is the input `hUa/hUb` of `band_interior_pair_impossible`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.LaczJunction

open Erdos634.Geometry Erdos634.Draft.TraceCovering Erdos634.TilePlacement
  Erdos634.CornerBaseEdgesReal Erdos634.Geometry.Dissection Set

variable {N : ℕ}

/-- The tile `X` cannot also be the tile `U`: its corner at `Q` would be `π − β`. -/
theorem corner_supplement (α β γ : ℝ) (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hα0 : 0 < α) (θ : ℝ) (hθ : θ = Real.pi - β) : θ ≠ β ∧ θ ≠ γ := by
  constructor <;> intro h <;> rw [hθ] at h <;> [skip; rw [hγdef] at h] <;> linarith

/-- **A tile cannot have all three vertices on one side line of the target**: if `P, Q` (vertices
`j`, `j+2`) and `G` (vertex `j+1`) of a tile have the same `m`-th barycentric coordinate `0`, the
tile is degenerate. -/
theorem tile_vertex_off_side (T : Tri) (T1 : Tri) (m : Fin 3) (j : Fin 3)
    (h0 : T.basis.coord m (T1.pts j) = 0) (h1 : T.basis.coord m (T1.pts (j+1)) = 0)
    (h2 : T.basis.coord m (T1.pts (j+2)) = 0) : False := by
  set g : Plane →ₗ[ℝ] ℝ := (T.basis.coord m).linear with hg
  have hg0 : g ≠ 0 := T.coord_linear_ne_zero m
  have hn := rotVec_ne_zero hg0
  have e1 : cross (rotVec g) (T1.pts (j+1) - T1.pts j) = 0 := by
    rw [← rotVec_spec, hg, ← vsub_eq_sub, AffineMap.linearMap_vsub, h0, h1]; simp
  have e2 : cross (rotVec g) (T1.pts (j+2) - T1.pts j) = 0 := by
    rw [← rotVec_spec, hg, ← vsub_eq_sub, AffineMap.linearMap_vsub, h0, h2]; simp
  have := cross_eq_zero_of_common_ker hn e1 e2
  rw [T1.det_cyclic j] at this
  exact T1.det_ne_zero this

/-- **The adjacent `α`-tile.** -/
theorem exists_alpha_edge (D : CongruentDissection N) (e f : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hband : ta e f < tb e f) (α β γ : ℝ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hα0 : 0 < α) (hβ0 : 0 < β)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hsa : sideOpp D.model 0 = (ta e f : ℝ)) (hsb : sideOpp D.model 1 = (tb e f : ℝ))
    (hsc : sideOpp D.model 2 = (tc e f : ℝ))
    {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {P Q G : Plane}
    (hP : P ∈ openSegment ℝ (D.target.pts p) (D.target.pts q))
    (hQ : Q ∈ openSegment ℝ (D.target.pts p) (D.target.pts q))
    (hGr : 0 < D.target.basis.coord r G)
    (i1 : Fin N) (j1 : Fin 3) (hPv : (D.tile i1).pts j1 = P) (hGv : (D.tile i1).pts (j1+1) = G)
    (hQv : (D.tile i1).pts (j1+2) = Q)
    (hα1 : (D.tile i1).localAngle P = α) (hβ1 : (D.tile i1).localAngle Q = β)
    (iX : Fin N) (kX mX : Fin 3) (Y : Plane) (hXQ : (D.tile iX).pts kX = Q)
    (hXY : (D.tile iX).pts mX = Y) (hmk : mX ≠ kX) (s : ℝ) (hs : 0 < s)
    (hYQ : Y - Q = (-s) • (P - Q))
    (hXne : iX ≠ i1) (hXang : (D.tile iX).localAngle Q = β ∨ (D.tile iX).localAngle Q = γ) :
    ∃ (iU : Fin N) (l1 l2 : ℝ), l1 < 0 ∧ 0 < l2 ∧
      (∃ ka, (D.tile iU).pts ka = G + l1 • (G - Q)) ∧
      (∃ kb, (D.tile iU).pts kb = G + l2 • (G - Q)) := by
  classical
  have hαβ : α ≠ β := by
    intro h
    apply hirr
    refine ⟨1/5, ?_⟩
    have : α = Real.pi / 5 := by rw [← h] at hrel; linarith
    rw [this]; push_cast; ring
  have hαγ : α ≠ γ := by rw [hγdef]; intro h; linarith
  have hnea : sideOpp D.model 0 ≠ sideOpp D.model 1 := by
    rw [hsa, hsb]; intro h
    have h' : ta e f = tb e f := by exact_mod_cast h
    omega
  have hneac : sideOpp D.model 0 ≠ sideOpp D.model 2 := by
    rw [hsa, hsc]; intro h
    have h' : ta e f = tc e f := by exact_mod_cast h
    have := b_lt_c e f he hef; omega
  -- the length of `GQ`
  have hGQ : dist G Q = (ta e f : ℝ) := by
    have hα1' : (D.tile i1).localAngle ((D.tile i1).pts j1) = α := by rw [hPv]; exact hα1
    rcases tile_vertex_angle_cases D α β γ hα' hβ' hγ' i1 j1 with ⟨_, h1⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [hGv, hQv] at h1; rw [h1, hsa]
    · exact absurd (hα1'.symm.trans h1) hαβ
    · exact absurd (hα1'.symm.trans h1) hαγ
  have hapos : (0:ℝ) < (ta e f : ℝ) := by exact_mod_cast a_pos e f he hef
  have hQG : Q ≠ G := by
    intro h; rw [h, dist_self] at hGQ; linarith
  -- coordinates
  obtain ⟨sP, hsP0, hsP1, hP0, hP1, hP2⟩ := coords_side D.target hpq hpr hqr hP
  obtain ⟨sQ, hsQ0, hsQ1, hQ0, hQ1, hQ2⟩ := coords_side D.target hpq hpr hqr hQ
  have hGc : G ∈ D.target.carrier :=
    tile_subset_target D.toDissection i1 (subset_convexHull ℝ _ ⟨j1+1, hGv⟩)
  obtain ⟨hint, hbef⟩ := chord_geometry_int D.target hpq hpr hqr hQ hGc hGr
  obtain ⟨hfront, hnv⟩ := side_frontier D.target hpq hpr hqr hQ
  -- the functional of the line `QG`, with `T₁` below
  have hj : j1 + 1 + 1 = j1 + 2 := by fin_cases j1 <;> rfl
  have hj' : j1 + 1 + 2 = j1 := by fin_cases j1 <;> rfl
  obtain ⟨f', c, hf0, hfG, hfQ, hfP⟩ := side_functional (D.tile i1) (j1+1) (A := G) (B := Q)
    hGv (by rw [hj]; exact hQv)
  rw [hj', hPv] at hfP
  set a : ℝ := (ta e f : ℝ) with ha
  set u : Plane := a⁻¹ • (G - Q) with hu
  have hu0 : u ≠ 0 := smul_ne_zero (inv_ne_zero hapos.ne') (sub_ne_zero.mpr hQG.symm)
  have hfu : f' u = 0 := by rw [hu, map_smul, map_sub, hfG, hfQ]; simp
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, Real.norm_of_nonneg hapos.le, ← dist_eq_norm, hGQ]
    field_simp
  have hnf : (-f' : Plane →ₗ[ℝ] ℝ) ≠ 0 := fun h => hf0 (neg_eq_zero.mp h)
  have hint' : ∀ x ∈ Ioo (0:ℝ) a, Q + x • u ∈ interior D.target.carrier := by
    intro x hx
    rw [hu, line_param Q G hapos.ne' x]
    exact hint _ (div_pos hx.1 hapos) ((div_lt_one hapos).mpr hx.2)
  have hseg : ∀ x : ℝ, 0 ≤ x → x ≤ a → Q + x • u ∈ segment ℝ G Q := by
    intro x hx0 hx1
    rw [hu, line_param Q G hapos.ne' x, segment_symm, segment_eq_image_lineMap]
    exact ⟨x / a, ⟨div_nonneg hx0 hapos.le, (div_le_one hapos).mpr hx1⟩, rfl⟩
  have hwall : ∀ x ∈ Ioo (0:ℝ) a, ∀ i, Q + x • u ∉ interior (D.tile i).carrier := by
    intro x hx i
    have hmem : Q + x • u ∈ (D.tile i1).edge (j1+1) := by
      show Q + x • u ∈ segment ℝ ((D.tile i1).pts (j1+1)) ((D.tile i1).pts (j1+1+1))
      rw [hGv, hj, hQv]; exact hseg x hx.1.le hx.2.le
    exact D.edge_point_not_interior hmem i
  have hgd : ∀ y, (-f') y = -c ↔ f' y = c := neg_iff
  have hs0 : ¬ Straddled D.toDissection (-f') (-c) Q := by
    have := not_straddled_of_outside_before (D := D.toDissection) (X := Q) (u := u) hgd hf0 hfQ
      hfu hu0 (x₀ := 0) (fun t ht => by
        rw [hu, line_param Q G hapos.ne' t]
        exact hbef _ (div_neg_of_neg_of_pos ht hapos))
    simpa using this
  obtain ⟨e0, he0, hlo, hhi⟩ := exists_start_edge D.toDissection hf0 hfQ hfu hu1 hapos hint' hwall hs0
  set H := hi D.toDissection Q u e0 with hH
  have hends : ∃ ka kb : Fin 3, kb ≠ ka ∧ (D.tile e0.1).pts ka = Q ∧
      (D.tile e0.1).pts kb = Q + H • u ∧ dist ((D.tile e0.1).pts ka) ((D.tile e0.1).pts kb) = H := by
    obtain ⟨h0, h1⟩ := onLine (D := D.toDissection) hgd he0
    obtain ⟨hlt, hedge, -, hdist⟩ := edge_data (D := D.toDissection) hf0 hfQ hfu hu0 h0 h1
    have hd : dist ((D.tile e0.1).pts e0.2) ((D.tile e0.1).pts (e0.2 + 1)) = H := by
      rw [hdist hu1, hlo, sub_zero]
    have s0 := par_spec (exists_param hf0 hfQ hfu hu0 h0)
    have s1 := par_spec (exists_param hf0 hfQ hfu hu0 h1)
    have hlo' : min (par Q u ((D.tile e0.1).pts e0.2)) (par Q u ((D.tile e0.1).pts (e0.2 + 1))) = 0 :=
      hlo
    have hhi' : max (par Q u ((D.tile e0.1).pts e0.2)) (par Q u ((D.tile e0.1).pts (e0.2 + 1))) = H :=
      rfl
    rcases le_total (par Q u ((D.tile e0.1).pts e0.2)) (par Q u ((D.tile e0.1).pts (e0.2 + 1))) with hle | hle
    · rw [min_eq_left hle] at hlo'
      rw [max_eq_right hle] at hhi'
      refine ⟨e0.2, e0.2 + 1, ?_, ?_, ?_, hd⟩
      · exact (fin3_succ_ne e0.2).symm
      · rw [s0, hlo', zero_smul, add_zero]
      · rw [s1, hhi']
    · rw [min_eq_right hle] at hlo'
      rw [max_eq_left hle] at hhi'
      refine ⟨e0.2 + 1, e0.2, ?_, ?_, ?_, ?_⟩
      · exact fin3_succ_ne e0.2
      · rw [s1, hlo', zero_smul, add_zero]
      · rw [s0, hhi']
      · rw [dist_comm]; exact hd
  obtain ⟨ka, kb, hkab, hka, hkb, hdab⟩ := hends
  have hHpos : 0 < H := hhi
  -- `U` is not `T₁`
  have hUne1 : e0.1 ≠ i1 := by
    intro h
    have hmem := (Dissection.mem_lineChain.mp he0).2.2 j1
    rw [h, hPv] at hmem
    simp only [LinearMap.neg_apply] at hmem
    linarith
  have hLAU : (D.tile e0.1).localAngle Q = α ∨ (D.tile e0.1).localAngle Q = β ∨
      (D.tile e0.1).localAngle Q = γ := by
    rcases tile_vertex_angle_cases D α β γ hα' hβ' hγ' e0.1 ka with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;>
      rw [hka] at h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  -- the corner of `T₁` at `Q`
  have hcornQ : EuclideanGeometry.angle P Q G = β := by
    have := hβ1
    rw [← hQv, Tri.localAngle_vertex] at this
    have e1 : j1 + 2 + 1 = j1 := by fin_cases j1 <;> rfl
    have e2 : j1 + 2 + 2 = j1 + 1 := by fin_cases j1 <;> rfl
    rw [e1, e2, hPv, hGv, hQv] at this
    exact this
  -- `U` is not `X`
  have hUneX : e0.1 ≠ iX := by
    intro hUX
    have h1 : (D.tile iX).pts ka = Q := by rw [← hUX]; exact hka
    have hkaX : ka = kX := (D.tile iX).indep.injective (h1.trans hXQ.symm)
    have h2 : (D.tile iX).pts kb = Q + H • u := by rw [← hUX]; exact hkb
    have hQr : D.target.basis.coord r Q = 0 := hQ2
    have hPr : D.target.basis.coord r P = 0 := hP2
    have hYr : D.target.basis.coord r Y = 0 := by
      have hY : Y = AffineMap.lineMap Q P (-s) := by
        rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, ← hYQ]; abel
      rw [hY, coord_lineMap, hQr, hPr]; ring
    have hbr : 0 < D.target.basis.coord r (Q + H • u) := by
      rw [hu, line_param Q G hapos.ne' H, coord_lineMap, hQr]
      have : 0 < H / a := div_pos hHpos hapos
      nlinarith
    have hmb : mX ≠ kb := by
      intro h
      rw [← h, hXY] at h2
      rw [← h2] at hbr; linarith
    have hangX : (D.tile iX).localAngle Q = Real.pi - β := by
      rw [← hXQ, Tri.localAngle_vertex, ← hkaX, h1]
      have hang : EuclideanGeometry.angle Y Q (Q + H • u) = Real.pi - β := by
        unfold EuclideanGeometry.angle
        rw [vsub_eq_sub, vsub_eq_sub, add_sub_cancel_left, hYQ, hu, smul_smul,
          show (-s) • (P - Q) = s • (-(P - Q)) by rw [smul_neg, neg_smul],
          InnerProductGeometry.angle_smul_left_of_pos _ _ hs,
          InnerProductGeometry.angle_smul_right_of_pos _ _ (mul_pos hHpos (inv_pos.mpr hapos)),
          InnerProductGeometry.angle_neg_left, ← hcornQ]
        rfl
      rcases fin3_cases mX ka (by rw [hkaX]; exact hmk) with e1 | e1 <;>
        rcases fin3_cases kb ka hkab with e2 | e2
      · exact absurd (e1.trans e2.symm) hmb
      · rw [← hang, ← hXY, ← h2, e1, e2]; rfl
      · rw [← hang, ← hXY, ← h2, e1, e2, EuclideanGeometry.angle_comm]; rfl
      · exact absurd (e1.trans e2.symm) hmb
    have := corner_supplement α β γ hγdef hrel hα0 _ hangX
    rcases hXang with h | h
    · exact this.1 h
    · exact this.2 h
  have hαQ : (D.tile e0.1).localAngle Q = α :=
    alpha_corner_of_figure D α β γ hγdef hrel hirr hα0 hβ0 hα' hβ' hγ' hfront hnv i1 iX e0.1 hβ1
      hXang hXne hUne1 hUneX hLAU
  have hαka : (D.tile e0.1).localAngle ((D.tile e0.1).pts ka) = α := by rw [hka]; exact hαQ
  obtain ⟨hedge1, hedge2⟩ := alpha_vertex_edges D α β γ hα' hβ' hγ' hαβ hαγ hnea hneac e0.1 ka hαka
  have hHbc : H = (tb e f : ℝ) ∨ H = (tc e f : ℝ) := by
    rcases fin3_cases kb ka hkab with e2 | e2
    · rw [e2] at hdab
      rcases hedge1 with h | h
      · exact Or.inl (by rw [← hdab, h, hsb])
      · exact Or.inr (by rw [← hdab, h, hsc])
    · rw [e2, dist_comm] at hdab
      rcases hedge2 with h | h
      · exact Or.inl (by rw [← hdab, h, hsb])
      · exact Or.inr (by rw [← hdab, h, hsc])
  have hbc := b_lt_c e f he hef
  have hHa : a < H := by
    rcases hHbc with h | h
    · rw [h, ha]; exact_mod_cast hband
    · rw [h, ha]; exact_mod_cast (hband.trans hbc)
  refine ⟨e0.1, -1, H / a - 1, by norm_num, by
    have : 1 < H / a := (one_lt_div hapos).mpr hHa
    linarith, ⟨ka, ?_⟩, ⟨kb, ?_⟩⟩
  · rw [hka]; module
  · rw [hkb, hu]
    simp only [div_eq_mul_inv]
    module

#print axioms exists_alpha_edge

end Erdos634.LaczJunction
