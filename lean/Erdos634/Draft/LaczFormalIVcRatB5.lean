-- Draft/LaczFormalIVcRatB5.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch), BLUEPRINT Part B, item B5: V and W are not on the boundary.
--   `vw_not_boundary` : T a VWTiling of a CONVEX set A (hb : 0 < b), then no apex V of a kite and no base midpoint W of a kite lies in `frontier A`.
--   Proof (measure level, no polygon structure): the equilateral cells of the derived `cellDiss` all have corner angle pi/3 (`localAngle_vertex_equi`);
--   at a point of the frontier of a convex region with interior the tiles' local angles add to at most pi (`sum_localAngle_frontier_le`, via a supporting half-plane from Hahn-Banach and
--   `volume_halfplane_inter_ball_at`); but at V k = W k' the apex cell of k and the three cells at W of k' are four distinct cells with vertex there: 4 pi/3 > pi.
--   `vw_point_not_frontier` is the statement for one coincidence `V k = W k'` (also used by B6).
--   Blueprint deviation: the blueprint cites `angle_sum_boundary` (an equality pi at a smooth boundary point); the inequality `<= pi` at ANY frontier point of a convex region
--   is what is needed (corners of A are frontier points) and is proved here from the half-plane volume lemma of Dissection.lean.
--   Hypotheses: A convex (named); `VWTiling` data; no polygon structure on A is used.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatB4
import Erdos634.Draft.LaczFormalRGLoc
import Erdos634.MarchFlank

open scoped Classical Fin.NatCast
open MeasureTheory
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

/-! ## Equilateral tiles: corner angle pi/3 -/

theorem eqT_dist {b : ℝ} (hb : 0 < b) {i j : Fin 3} (hij : i ≠ j) : dist ((eqT b hb).pts i) ((eqT b hb).pts j) = b := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hq : (Real.sqrt 3 * b / 2) ^ 2 = 3 * b ^ 2 / 4 := by rw [div_pow, mul_pow, hs]; ring
  have key : ∀ x y : ℝ, ∀ x' y' : ℝ, (x - x') ^ 2 + (y - y') ^ 2 = b ^ 2 → dist (mkPt x y) (mkPt x' y') = b := by
    intro x y x' y' h
    have h2 : dist (mkPt x y) (mkPt x' y') ^ 2 = b ^ 2 := by rw [sqd_mk]; exact h
    nlinarith [dist_nonneg (x := mkPt x y) (y := mkPt x' y'), h2]
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | skip
  all_goals
    simp only [eqT, mkTri_pts]
    first
    | exact key _ _ _ _ (by nlinarith)
    | (rw [dist_comm]; exact key _ _ _ _ (by nlinarith))

theorem congr_dist_eqT {T : Tri} {b : ℝ} (hb : 0 < b) (h : T.Congruent (eqT b hb)) {i j : Fin 3} (hij : i ≠ j) :
    dist (T.pts i) (T.pts j) = b := by
  obtain ⟨f, σ, hf⟩ := h
  have : dist (T.pts i) (T.pts j) = dist (f (T.pts i)) (f (T.pts j)) := (f.dist_eq _ _).symm
  rw [this, hf, hf]
  exact eqT_dist hb (fun e => hij (σ.injective e))

theorem cornerAngle_of_equi {b : ℝ} (hb : 0 < b) {p q r : Plane} (hpq : dist p q = b) (hrq : dist r q = b) (hpr : dist p r = b) :
    cornerAngle p q r = Real.pi / 3 := by
  have hl := EuclideanGeometry.law_cos (V := Plane) p q r
  rw [hpq, hrq, hpr] at hl
  have hcos : Real.cos (EuclideanGeometry.angle (V := Plane) p q r) = 1 / 2 := by
    have hb2 : 0 < b * b := mul_pos hb hb
    nlinarith
  unfold cornerAngle
  apply Real.injOn_cos ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  rw [hcos, Real.cos_pi_div_three]

private theorem fin3_ne (j : Fin 3) : j + 1 ≠ j ∧ j + 2 ≠ j ∧ j + 1 ≠ j + 2 := by revert j; decide

theorem localAngle_vertex_equi {T : Tri} {b : ℝ} (hb : 0 < b) (h : T.Congruent (eqT b hb)) (j : Fin 3) :
    T.localAngle (T.pts j) = Real.pi / 3 := by
  rw [Tri.localAngle_vertex]
  obtain ⟨h1, h2, h3⟩ := fin3_ne j
  exact cornerAngle_of_equi hb (congr_dist_eqT hb h h1) (congr_dist_eqT hb h h2) (congr_dist_eqT hb h h3)

/-- Local angle cases (read off the definition). -/
theorem localAngle_cases' (T : Tri) (p : Plane) :
    (∃ j : Fin 3, p = T.pts j ∧ T.localAngle p = cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2))) ∨
    T.localAngle p = 2 * Real.pi ∨ T.localAngle p = Real.pi ∨ T.localAngle p = 0 := by
  by_cases h : ∃ j, p = T.pts j
  · left
    exact ⟨h.choose, h.choose_spec, by rw [Tri.localAngle, dif_pos h]⟩
  · by_cases h2 : ∀ j, 0 < T.basis.coord j p
    · right; left
      rw [Tri.localAngle, dif_neg h, if_pos h2]
    · by_cases h3 : ∃ k, T.basis.coord k p = 0 ∧ ∀ j, j ≠ k → 0 < T.basis.coord j p
      · right; right; left
        rw [Tri.localAngle, dif_neg h, if_neg h2, if_pos h3]
      · right; right; right
        rw [Tri.localAngle, dif_neg h, if_neg h2, if_neg h3]

/-- An equilateral tile containing `p`: its local angle at `p` is at least pi/3, with equality exactly at a vertex. -/
theorem localAngle_mem_equi {T : Tri} {b : ℝ} (hb : 0 < b) (h : T.Congruent (eqT b hb)) {p : Plane} (hp : p ∈ T.carrier) :
    Real.pi / 3 ≤ T.localAngle p ∧ (T.localAngle p = Real.pi / 3 → ∃ j, p = T.pts j) := by
  have hne := Erdos634.MarchFlank.localAngle_ne_zero_of_mem T hp
  have hpi := Real.pi_pos
  rcases localAngle_cases' T p with ⟨j, hj, hv⟩ | h2 | h2 | h2
  · have : T.localAngle p = Real.pi / 3 := by rw [hj]; exact localAngle_vertex_equi hb h j
    exact ⟨this.ge, fun _ => ⟨j, hj⟩⟩
  · rw [h2]; exact ⟨by linarith, fun e => by linarith⟩
  · rw [h2]; exact ⟨by linarith, fun e => by linarith⟩
  · exact absurd h2 hne

/-! ## Convex regions: a supporting half-plane at a frontier point -/

theorem convex_frontier_halfplane {A : Set Plane} (hA : Convex ℝ A) (hint : (interior A).Nonempty) (hcl : IsClosed A) {q : Plane}
    (hq : q ∈ frontier A) :
    ∃ g : Plane →ᵃ[ℝ] ℝ, g.linear ≠ 0 ∧ g q = 0 ∧ ∀ y ∈ A, 0 ≤ g y := by
  have hqi : q ∉ interior A := hq.2
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hA.interior isOpen_interior hqi
  let g : Plane →ᵃ[ℝ] ℝ :=
    { toFun := fun y => f q - f y
      linear := -(f : Plane →ₗ[ℝ] ℝ)
      map_vadd' := fun p v => by simp [vadd_eq_add]; ring }
  have hg : ∀ y, g y = f q - f y := fun y => rfl
  have hclo : A ⊆ {y | f y ≤ f q} := by
    intro y hy
    have : y ∈ closure (interior A) := by
      rw [hA.closure_interior_eq_closure_of_nonempty_interior hint, hcl.closure_eq]; exact hy
    refine closure_minimal (fun a ha => (hf a ha).le) (isClosed_le f.continuous continuous_const) this
  refine ⟨g, ?_, by rw [hg]; ring, fun y hy => by
    have h5 := hclo hy
    simp only [Set.mem_setOf_eq] at h5
    rw [hg]; linarith⟩
  intro h0
  obtain ⟨a, ha⟩ := hint
  have h1 : g.linear = -(f : Plane →ₗ[ℝ] ℝ) := rfl
  rw [h1] at h0
  have : (f : Plane →ₗ[ℝ] ℝ) = 0 := by simpa using h0
  have h2 : f a = 0 := by have := congrArg (fun L : Plane →ₗ[ℝ] ℝ => L a) this; simpa using this
  have h3 : f q = 0 := by have := congrArg (fun L : Plane →ₗ[ℝ] ℝ => L q) this; simpa using this
  have := hf a ha
  linarith

theorem volume_inter_ball_le_half {A : Set Plane} (hA : Convex ℝ A) (hint : (interior A).Nonempty) (hcl : IsClosed A) {q : Plane}
    (hq : q ∈ frontier A) {r : ℝ} (hr : 0 < r) :
    volume (A ∩ Metric.ball q r) ≤ ENNReal.ofReal (Real.pi / 2 * r ^ 2) := by
  obtain ⟨g, hL, hgq, hgA⟩ := convex_frontier_halfplane hA hint hcl hq
  have h2 := volume_halfplane_inter_ball_at g hL hgq r
  rw [volume_ball_plane q hr.le] at h2
  have hhalf : (2 : ENNReal) * ENNReal.ofReal (Real.pi / 2 * r ^ 2) = ENNReal.ofReal (Real.pi * r ^ 2) := by
    rw [show ((2 : ENNReal)) = ENNReal.ofReal (2 : ℝ) by simp, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1; ring
  rw [← hhalf] at h2
  have h3 := (ENNReal.mul_right_inj (by norm_num) (by norm_num)).mp h2
  rw [← h3]
  exact measure_mono (Set.inter_subset_inter (fun y hy => hgA y hy) le_rfl)

/-- At any frontier point of a convex region (with interior, closed), the tiles' local angles add to at most pi. -/
theorem sum_localAngle_frontier_le {N : ℕ} (D : RegionDissection N) (hN : 0 < N) (hA : Convex ℝ D.region) (hint : (interior D.region).Nonempty)
    (hcl : IsClosed D.region) {q : Plane} (hq : q ∈ frontier D.region) :
    ∑ i, (D.tile i).localAngle q ≤ Real.pi := by
  choose ri hri hcontrib using fun i => (D.tile i).volume_inter_ball_localAngle q
  obtain ⟨r0, hr0, hr0le⟩ := exists_common_radius hN ri hri
  have hsum := volume_inter_ball_eq_sum D q r0
  have htiles : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      volume ((D.tile i).carrier ∩ Metric.ball q r0) = ENNReal.ofReal ((D.tile i).localAngle q / 2 * r0 ^ 2) := fun i _ =>
    hcontrib i r0 hr0 (hr0le i)
  rw [Finset.sum_congr rfl htiles,
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => by have := (D.tile i).localAngle_nonneg q; positivity)] at hsum
  have hle := volume_inter_ball_le_half hA hint hcl hq hr0
  rw [hsum] at hle
  have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle
  have hfact : ∑ i, (D.tile i).localAngle q / 2 * r0 ^ 2 = (∑ i, (D.tile i).localAngle q) * (r0 ^ 2 / 2) := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hfact] at this
  have hr2 : (0 : ℝ) < r0 ^ 2 / 2 := by positivity
  nlinarith

/-! ## B5 -/

namespace VWTiling
variable {b : ℝ} {A : Set Plane} {ιK ιR : Type} [Fintype ιK] [Fintype ιR] (T : VWTiling b A ιK ιR)

/-- Sum over the flat `Fin N` index equals the sum over cell indices. -/
theorem sum_cellDiss (hb : 0 < b) (q : Plane) :
    ∑ i, ((T.cellDiss hb).tile i).localAngle q = ∑ c : CellIdx ιK ιR, (T.cellT c).localAngle q :=
  (Fintype.equivFin (CellIdx ιK ιR)).symm.sum_comp (fun c => (T.cellT c).localAngle q)

include T in
theorem region_closed : IsClosed A := by
  have h := isClosed_iUnion_of_finite fun c : CellIdx ιK ιR => (T.cellT c).isCompact.isClosed
  rwa [T.cells_cover] at h

include T in
theorem interior_nonempty_of_cell (c : CellIdx ιK ιR) : (interior A).Nonempty := by
  obtain ⟨x, hx⟩ := (T.cellT c).interior_nonempty
  exact ⟨x, interior_mono ((Set.subset_iUnion (fun c => (T.cellT c).carrier) c).trans T.cells_cover.subset) hx⟩

/-- **One coincidence `V k = W k'` is never a frontier point of a convex `A`.** -/
theorem vw_point_not_frontier (hb : 0 < b) (hconv : Convex ℝ A) (k k' : ιK) (h : (T.K k).V = (T.K k').W) :
    (T.K k).V ∉ frontier A := by
  intro hfr
  have hkk : k ≠ k' := by
    rintro rfl
    exact (T.K k).V_ne_W h
  have hN : 0 < Fintype.card (CellIdx ιK ιR) := Fintype.card_pos_iff.mpr ⟨Sum.inl (k, 0)⟩
  have hle := sum_localAngle_frontier_le (T.cellDiss hb).toRegionDissection hN hconv (T.interior_nonempty_of_cell (Sum.inl (k, 0)))
    T.region_closed (q := (T.K k).V) hfr
  rw [T.sum_cellDiss hb] at hle
  -- four distinct cells with vertex at q
  have hc := T.cell_congruent hb
  obtain ⟨hW1, hW2, hW3⟩ := kite_W_vertices (T.K k').hD
  have v0 : (T.cellT (Sum.inl (k, 0))).localAngle (T.K k).V = Real.pi / 3 := by
    have e : (T.K k).V = ((T.K k).cell 0).pts 2 := (kite_apex_vertex (T.K k).hD).symm
    show ((T.K k).cell 0).localAngle (T.K k).V = _
    rw [e]; exact localAngle_vertex_equi hb (hc (Sum.inl (k, 0))) 2
  have v1 : (T.cellT (Sum.inl (k', 1))).localAngle (T.K k).V = Real.pi / 3 := by
    have e : (T.K k').W = ((T.K k').cell 1).pts 1 := hW1.symm
    show ((T.K k').cell 1).localAngle (T.K k).V = _
    rw [h, e]; exact localAngle_vertex_equi hb (hc (Sum.inl (k', 1))) 1
  have v2 : (T.cellT (Sum.inl (k', 2))).localAngle (T.K k).V = Real.pi / 3 := by
    have e : (T.K k').W = ((T.K k').cell 2).pts 0 := hW2.symm
    show ((T.K k').cell 2).localAngle (T.K k).V = _
    rw [h, e]; exact localAngle_vertex_equi hb (hc (Sum.inl (k', 2))) 0
  have v3 : (T.cellT (Sum.inl (k', 3))).localAngle (T.K k).V = Real.pi / 3 := by
    have e : (T.K k').W = ((T.K k').cell 3).pts 2 := hW3.symm
    show ((T.K k').cell 3).localAngle (T.K k).V = _
    rw [h, e]; exact localAngle_vertex_equi hb (hc (Sum.inl (k', 3))) 2
  set S : Finset (CellIdx ιK ιR) := {Sum.inl (k, 0), Sum.inl (k', 1), Sum.inl (k', 2), Sum.inl (k', 3)} with hS
  have hsum : ∑ c ∈ S, (T.cellT c).localAngle (T.K k).V = 4 * (Real.pi / 3) := by
    rw [hS, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton, v0, v1, v2, v3]
    · ring
    all_goals simp [hkk]
  have hge : ∑ c ∈ S, (T.cellT c).localAngle (T.K k).V ≤ ∑ c : CellIdx ιK ιR, (T.cellT c).localAngle (T.K k).V :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun c _ _ => (T.cellT c).localAngle_nonneg _)
  linarith [Real.pi_pos]

/-- **B5.** In a V/W tiling of a convex `A`, no apex `V` and no base midpoint `W` of a kite lies on the frontier of `A`. -/
theorem vw_not_boundary (hb : 0 < b) (hconv : Convex ℝ A) :
    (∀ k, (T.K k).V ∉ frontier A) ∧ (∀ k, (T.K k).W ∉ frontier A) := by
  refine ⟨fun k => ?_, fun k => ?_⟩
  · obtain ⟨k', hk'⟩ := T.vwV k
    exact T.vw_point_not_frontier hb hconv k k' hk'
  · obtain ⟨k'', hk''⟩ := T.vwW k
    rw [hk'']
    exact T.vw_point_not_frontier hb hconv k'' k hk''.symm

end VWTiling

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.sum_localAngle_frontier_le
#print axioms Erdos634.Draft.LaczFormal.RG.VWTiling.vw_not_boundary
#print axioms Erdos634.Draft.LaczFormal.RG.localAngle_mem_equi
