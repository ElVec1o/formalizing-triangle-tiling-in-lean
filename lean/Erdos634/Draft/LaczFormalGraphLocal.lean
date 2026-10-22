-- Draft/LaczFormalGraphLocal.lean -- D0 (part 2): the LOCAL SECTORS of the tiles of a `Dissection` at a point `V`.
--
-- For a tile `T` and a point `V ∈ T`, near `V` the tile is a closed convex cone `V + cone(p, q)`:
--  * `V` a vertex `pts k`:        `(p, q)` = the two edge vectors at `V`, ordered counterclockwise (`cross p q = T.det` or `-T.det`);
--  * `V` interior to an edge:     a straight sector `q = -p` (a half-plane), `p` the direction of the edge with the tile on its left;
--  * `V` interior to the tile:    the full plane (excluded from the fan: then `V` lies on no other tile).
-- `LocalCone T V p q` records this (a ball `r` on which membership in the tile is membership of `y - V` in the cone).  `wd p q`
-- (`LaczFormalGraphFan`) equals `T.localAngle V`.  Everything is proved from `Tri.inter_ball_eq_vertexCone` (VertexSector.lean),
-- `Tri.inter_ball_eq_halfplane` and `Tri.coord_mul_det` (Dissection.lean).
-- UNAUDITED (label NOTE).  Credit: Laczkovich (DCG 48 (2012), Sect. 4: the half-lines h_i and the angular domains of the triangles).
import Erdos634.Draft.LaczFormalGraphFan
import Erdos634.AngleSumDissection
import Erdos634.VertexSector
import Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.Graph

open Erdos634.Geometry

/-- Plane vectors as coordinate pairs. -/
def toV2 (x : Plane) : V2 := (x 0, x 1)

theorem crs_toV2 (u v : Plane) : crs (toV2 u) (toV2 v) = cross u v := rfl

theorem dt_toV2 (u v : Plane) : dt (toV2 u) (toV2 v) = inner ℝ u v := by
  rw [Erdos634.Geometry.inner_coords]; rfl

theorem toV2_sub (x y : Plane) : toV2 (x - y) = ((x 0 - y 0), (x 1 - y 1)) := rfl

theorem toV2_ne_zero {u : Plane} (hu : u ≠ 0) : toV2 u ≠ 0 := by
  intro h
  apply hu
  have h0 : u 0 = 0 := congrArg Prod.fst h
  have h1 : u 1 = 0 := congrArg Prod.snd h
  ext i; fin_cases i <;> simp [h0, h1]

theorem nsq_toV2 (u : Plane) : nsq (toV2 u) = ‖u‖ ^ 2 := by
  rw [Erdos634.Geometry.norm_sq_coords]; rfl

/-- The width of a sector is the unoriented angle of its two generators (when the sector is oriented counterclockwise). -/
theorem wd_eq_angle {u w : Plane} (hu : u ≠ 0) (hw : w ≠ 0) (hc : 0 ≤ cross u w) :
    wd (toV2 u) (toV2 w) = InnerProductGeometry.angle u w := by
  unfold wd
  have hz : (⟨dt (toV2 u) (toV2 w), crs (toV2 u) (toV2 w)⟩ : ℂ) ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp at h1 h2
    exact toV2_ne_zero hu (eq_zero_of_crs_dt (toV2_ne_zero hw) h2 h1)
  rw [Complex.arg_of_im_nonneg_of_ne_zero (by simpa [crs_toV2] using hc) hz]
  unfold InnerProductGeometry.angle
  congr 1
  have hn : ‖(⟨dt (toV2 u) (toV2 w), crs (toV2 u) (toV2 w)⟩ : ℂ)‖ = ‖u‖ * ‖w‖ := by
    have h1 : ‖(⟨dt (toV2 u) (toV2 w), crs (toV2 u) (toV2 w)⟩ : ℂ)‖ ^ 2 = (‖u‖ * ‖w‖) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_mk, mul_pow, ← nsq_toV2, ← nsq_toV2, ← crs_dt_sq]
      ring
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h1
  rw [hn]
  show dt (toV2 u) (toV2 w) / (‖u‖ * ‖w‖) = _
  rw [dt_toV2]

theorem wd_eq_angle_swap {u w : Plane} (hu : u ≠ 0) (hw : w ≠ 0) (hc : cross u w ≤ 0) :
    wd (toV2 w) (toV2 u) = InnerProductGeometry.angle u w := by
  rw [InnerProductGeometry.angle_comm]
  exact wd_eq_angle hw hu (by rw [cross_swap]; linarith)

/-- The sector `(p, q)` is the local cone of the tile `T` at `V`. -/
def LocalCone (T : Tri) (V : Plane) (p q : V2) : Prop :=
  ∃ r > 0, ∀ y : Plane, dist y V < r → (y ∈ T.carrier ↔ inCone p q (toV2 (y - V)))

/-- Which tile feature produces the sector: a vertex (with the two edge vectors, in the order of the sector) or an interior point of
an edge (straight sector). -/
def SectorSpec (T : Tri) (V : Plane) (p q : V2) : Prop :=
  (∃ k : Fin 3, T.pts k = V ∧
      ((p = toV2 (T.pts (k + 1) - V) ∧ q = toV2 (T.pts (k + 2) - V)) ∨
       (p = toV2 (T.pts (k + 2) - V) ∧ q = toV2 (T.pts (k + 1) - V)))) ∨
  ((∀ k, T.pts k ≠ V) ∧ ∃ m : Fin 3, T.basis.coord m V = 0 ∧ (∀ j, j ≠ m → 0 < T.basis.coord j V) ∧
      q = (-p.1, -p.2) ∧ (p = toV2 (T.pts (m + 2) - T.pts (m + 1)) ∨ p = toV2 (T.pts (m + 1) - T.pts (m + 2))))

theorem vertexCone_iff_pos {u w : Plane} (hc : 0 < cross u w) (z : Plane) :
    z ∈ vertexCone u w ↔ inCone (toV2 u) (toV2 w) (toV2 z) := by
  unfold vertexCone inCone
  simp only [Set.mem_setOf_eq, crs_toV2]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(mul_nonneg_iff_of_pos_right hc).mp h1, (mul_nonneg_iff_of_pos_right hc).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨mul_nonneg h1 hc.le, mul_nonneg h2 hc.le⟩

theorem vertexCone_iff_neg {u w : Plane} (hc : cross u w < 0) (z : Plane) :
    z ∈ vertexCone u w ↔ inCone (toV2 w) (toV2 u) (toV2 z) := by
  unfold vertexCone inCone
  simp only [Set.mem_setOf_eq, crs_toV2]
  have e1 : cross w z = - cross z w := cross_swap w z
  have e2 : cross z u = - cross u z := cross_swap z u
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · rw [e1]; nlinarith
    · rw [e2]; nlinarith
  · rintro ⟨h1, h2⟩
    rw [e1] at h1; rw [e2] at h2
    constructor <;> nlinarith

/-- **Vertex case.** -/
theorem corner_sector (T : Tri) (j : Fin 3) :
    ∃ p q : V2, SecOK p q ∧ LocalCone T (T.pts j) p q ∧ wd p q = T.localAngle (T.pts j) ∧
      SectorSpec T (T.pts j) p q := by
  obtain ⟨r, hr, hEq⟩ := T.inter_ball_eq_vertexCone j
  have hu : T.edgeVec j ≠ 0 := T.edgeVec_ne_zero j
  have hv : T.edgeVec' j ≠ 0 := T.edgeVec'_ne_zero j
  have hD : cross (T.edgeVec j) (T.edgeVec' j) = T.det := T.cross_edgeVec j
  have hdet : T.det ≠ 0 := T.det_ne_zero
  have hang : T.localAngle (T.pts j) = InnerProductGeometry.angle (T.edgeVec j) (T.edgeVec' j) := by
    rw [T.localAngle_vertex, T.cornerAngle_eq_angle]
  have hmem : ∀ y : Plane, dist y (T.pts j) < r →
      (y ∈ T.carrier ↔ y - T.pts j ∈ vertexCone (T.edgeVec j) (T.edgeVec' j)) := by
    intro y hy
    have h : y ∈ T.carrier ∩ Metric.ball (T.pts j) r ↔
        y ∈ {y : Plane | y - T.pts j ∈ vertexCone (T.edgeVec j) (T.edgeVec' j)} ∩ Metric.ball (T.pts j) r := by
      rw [hEq]
    have hb : y ∈ Metric.ball (T.pts j) r := by simpa [Metric.mem_ball] using hy
    simpa [hb] using h
  rcases lt_or_gt_of_ne hdet with hneg | hpos
  · refine ⟨toV2 (T.edgeVec' j), toV2 (T.edgeVec j), Or.inl ?_, ⟨r, hr, fun y hy => ?_⟩, ?_, Or.inl ⟨j, rfl, Or.inr ⟨rfl, rfl⟩⟩⟩
    · rw [crs_toV2, cross_swap, hD]; linarith
    · rw [hmem y hy, vertexCone_iff_neg (by rw [hD]; exact hneg)]
    · rw [hang]
      exact wd_eq_angle_swap hu hv (by rw [hD]; exact hneg.le)
  · refine ⟨toV2 (T.edgeVec j), toV2 (T.edgeVec' j), Or.inl ?_, ⟨r, hr, fun y hy => ?_⟩, ?_, Or.inl ⟨j, rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
    · rw [crs_toV2, hD]; exact hpos
    · rw [hmem y hy, vertexCone_iff_pos (by rw [hD]; exact hpos)]
    · rw [hang]
      exact wd_eq_angle hu hv (by rw [hD]; exact hpos.le)

theorem inCone_straight_iff (p : V2) (z : V2) : inCone p (-p.1, -p.2) z ↔ 0 ≤ crs p z := by
  unfold inCone crs
  constructor
  · rintro ⟨h, _⟩; exact h
  · intro h; exact ⟨h, by nlinarith⟩

theorem fin3_add_ne (j : Fin 3) : j + 1 ≠ j + 2 := by revert j; decide
theorem fin3_ne_one (j : Fin 3) : j + 1 ≠ j := by revert j; decide
theorem fin3_ne_two (j : Fin 3) : j + 2 ≠ j := by revert j; decide
theorem fin3_e1 (m : Fin 3) : (m + 1) + 2 = m := by revert m; decide
theorem fin3_e2 (m : Fin 3) : (m + 1) + 1 = m + 2 := by revert m; decide

theorem localAngle_of_edge_coords (T : Tri) (m : Fin 3) (V : Plane) (h0 : T.basis.coord m V = 0)
    (hpos : ∀ j, j ≠ m → 0 < T.basis.coord j V) : T.localAngle V = Real.pi := by
  classical
  have hv : ¬ ∃ j, V = T.pts j := by
    rintro ⟨j, hj⟩
    have h1 : T.basis.coord (j + 1) V = 0 := by rw [hj]; exact T.basis.coord_apply_ne (fin3_ne_one j)
    have h2 : T.basis.coord (j + 2) V = 0 := by rw [hj]; exact T.basis.coord_apply_ne (fin3_ne_two j)
    by_cases hm1 : j + 1 = m
    · have hm2 : j + 2 ≠ m := fun h => fin3_add_ne j (hm1.trans h.symm)
      exact absurd h2 (hpos _ hm2).ne'
    · exact absurd h1 (hpos _ hm1).ne'
  have hIn : ¬ ∀ j, 0 < T.basis.coord j V := fun h => absurd h0 (ne_of_gt (h m))
  rw [Tri.localAngle, dif_neg hv, if_neg hIn, if_pos ⟨m, h0, hpos⟩]

theorem crs_straight (p : V2) : crs p (-p.1, -p.2) = 0 := by unfold crs; ring

theorem dt_straight_neg {p : V2} (hp : p ≠ 0) : dt p (-p.1, -p.2) < 0 := by
  have := nsq_pos hp
  unfold dt; unfold nsq at this; nlinarith

theorem wd_straight {p : V2} (hp : p ≠ 0) : wd p (-p.1, -p.2) = Real.pi := by
  unfold wd
  rw [Complex.arg_eq_pi_iff]
  exact ⟨dt_straight_neg hp, crs_straight p⟩

theorem wd_ext {a : V2} (ha : a ≠ 0) : wd (-a.1, -a.2) a = Real.pi := by
  have hp : ((-a.1, -a.2) : V2) ≠ 0 := by
    intro h; apply ha
    have h1 : -a.1 = 0 := congrArg Prod.fst h
    have h2 : -a.2 = 0 := congrArg Prod.snd h
    exact Prod.ext (show a.1 = 0 by linarith) (show a.2 = 0 by linarith)
  have := wd_straight hp
  simpa using this

/-- **Edge-interior case**: `V` lies on the edge opposite vertex `m` and is not a vertex; the tile is locally a half-plane. -/
theorem straight_sector (T : Tri) (m : Fin 3) (V : Plane) (h0 : T.basis.coord m V = 0)
    (hpos : ∀ j, j ≠ m → 0 < T.basis.coord j V) :
    ∃ p q : V2, SecOK p q ∧ LocalCone T V p q ∧ wd p q = T.localAngle V ∧ SectorSpec T V p q := by
  classical
  set e : Plane := T.pts (m + 2) - T.pts (m + 1) with hedef
  have he : e ≠ 0 := by
    rw [hedef, sub_ne_zero]
    intro h
    exact (fin3_add_ne m) (T.indep.injective h).symm
  have hdet : T.det ≠ 0 := T.det_ne_zero
  have hcd : ∀ y : Plane, T.basis.coord m y * T.det = cross e (y - T.pts (m + 1)) := by
    intro y
    have := T.coord_mul_det (m + 1) y
    rw [fin3_e1, fin3_e2] at this
    exact this
  have hcdV : cross e (V - T.pts (m + 1)) = 0 := by rw [← hcd V, h0, zero_mul]
  have hcr : ∀ y : Plane, cross e (y - V) = T.basis.coord m y * T.det := by
    intro y
    have : cross e (y - V) = cross e (y - T.pts (m + 1)) - cross e (V - T.pts (m + 1)) := by
      simp only [cross, PiLp.sub_apply]; ring
    rw [this, hcdV, ← hcd y]; ring
  obtain ⟨r, hr, hEq⟩ := T.inter_ball_eq_halfplane m (x := V) (hpos _ (fin3_ne_one m))
    (hpos _ (fin3_ne_two m))
  have hmem : ∀ y : Plane, dist y V < r → (y ∈ T.carrier ↔ 0 ≤ T.basis.coord m y) := by
    intro y hy
    have h : y ∈ T.carrier ∩ Metric.ball V r ↔ y ∈ {y | 0 ≤ T.basis.coord m y} ∩ Metric.ball V r := by
      rw [hEq]
    have hb : y ∈ Metric.ball V r := by simpa [Metric.mem_ball] using hy
    simpa [hb] using h
  have hang : T.localAngle V = Real.pi := localAngle_of_edge_coords T m V h0 hpos
  have hv : ¬ ∃ j, V = T.pts j := by
    rintro ⟨j, hj⟩
    have h1 : T.basis.coord (j + 1) V = 0 := by rw [hj]; exact T.basis.coord_apply_ne (fin3_ne_one j)
    have h2 : T.basis.coord (j + 2) V = 0 := by rw [hj]; exact T.basis.coord_apply_ne (fin3_ne_two j)
    by_cases hm1 : j + 1 = m
    · have hm2 : j + 2 ≠ m := fun h => fin3_add_ne j (hm1.trans h.symm)
      exact absurd h2 (hpos _ hm2).ne'
    · exact absurd h1 (hpos _ hm1).ne'
  have hvne : ∀ k, T.pts k ≠ V := fun k hk => hv ⟨k, hk.symm⟩
  have hpne : toV2 e ≠ 0 := toV2_ne_zero he
  have hcrs0 : ∀ p : V2, crs p (-p.1, -p.2) = 0 := by intro p; unfold crs; ring
  have hdtn : ∀ p : V2, p ≠ 0 → dt p (-p.1, -p.2) < 0 := by
    intro p hp
    have := nsq_pos hp
    unfold dt; unfold nsq at this; nlinarith
  have hwd : ∀ p : V2, p ≠ 0 → wd p (-p.1, -p.2) = Real.pi := by
    intro p hp
    unfold wd
    rw [Complex.arg_eq_pi_iff]
    exact ⟨hdtn p hp, hcrs0 p⟩
  rcases lt_or_gt_of_ne hdet with hneg | hposd
  · set pp : V2 := toV2 (T.pts (m + 1) - T.pts (m + 2)) with hppdef
    have hneg_e : T.pts (m + 1) - T.pts (m + 2) = -e := by rw [hedef, neg_sub]
    have hpp : pp ≠ 0 := by rw [hppdef, hneg_e]; exact toV2_ne_zero (neg_ne_zero.mpr he)
    refine ⟨pp, (-pp.1, -pp.2), Or.inr ⟨hcrs0 pp, hdtn pp hpp⟩, ⟨r, hr, fun y hy => ?_⟩, ?_,
      Or.inr ⟨hvne, m, h0, hpos, rfl, Or.inr rfl⟩⟩
    · rw [hmem y hy, inCone_straight_iff, hppdef, crs_toV2, hneg_e, cross_neg_left, hcr y]
      constructor
      · intro h; nlinarith [mul_nonneg h (neg_nonneg.mpr hneg.le)]
      · intro h; by_contra hc; push_neg at hc; nlinarith [mul_pos_of_neg_of_neg hc hneg]
    · rw [hang]; exact hwd pp hpp
  · set pp : V2 := toV2 e with hppdef
    have hpp : pp ≠ 0 := hpne
    refine ⟨pp, (-pp.1, -pp.2), Or.inr ⟨hcrs0 pp, hdtn pp hpp⟩, ⟨r, hr, fun y hy => ?_⟩, ?_,
      Or.inr ⟨hvne, m, h0, hpos, rfl, Or.inl rfl⟩⟩
    · rw [hmem y hy, inCone_straight_iff, hppdef, crs_toV2, hcr y]
      constructor
      · intro h; nlinarith [mul_nonneg h hposd.le]
      · intro h; by_contra hc; push_neg at hc; nlinarith [mul_neg_of_neg_of_pos hc hposd]
    · rw [hang]; exact hwd pp hpp

/-! ## Local angle outside the tile; the sector of any tile point that is not interior -/

theorem Tri.localAngle_eq_zero_of_not_mem (T : Tri) {V : Plane} (h : V ∉ T.carrier) : T.localAngle V = 0 := by
  classical
  rw [Tri.localAngle]
  split
  · rename_i hv
    have hvmem : V ∈ Set.range T.pts := ⟨hv.choose, hv.choose_spec.symm⟩
    exact absurd (subset_convexHull ℝ _ hvmem) h
  · split
    · rename_i hall
      have hint : V ∈ interior T.carrier := (T.mem_interior_iff_coord_pos _).mpr hall
      exact absurd (interior_subset hint) h
    · split
      · rename_i hedge
        obtain ⟨kk, hkk1, hkk2⟩ := hedge
        have hmem : V ∈ T.carrier := by
          rw [T.carrier_eq_nonneg_coord]
          intro j
          rcases eq_or_ne j kk with rfl | hne
          · exact hkk1.ge
          · exact (hkk2 j hne).le
        exact absurd hmem h
      · rfl

theorem local_sector (T : Tri) {V : Plane} (hV : V ∈ T.carrier) (hint : V ∉ interior T.carrier) :
    ∃ p q : V2, SecOK p q ∧ LocalCone T V p q ∧ wd p q = T.localAngle V ∧ SectorSpec T V p q := by
  classical
  by_cases hvert : ∃ j, V = T.pts j
  · obtain ⟨j, rfl⟩ := hvert; exact corner_sector T j
  · push_neg at hvert
    rcases T.classify (fun k h => hvert k h) with hpos | ⟨k, hk0, hk⟩ | ⟨k, hkneg⟩
    · exact absurd ((T.mem_interior_iff_coord_pos V).mpr hpos) hint
    · exact straight_sector T k V hk0 hk
    · rw [T.carrier_eq_nonneg_coord] at hV; exact absurd (hV k) (not_le.mpr hkneg)

/-! ## Several tiles at one point -/

variable {N : ℕ}

/-- A point of the interior of one tile lies on no other tile. -/
theorem not_interior_of_mem_other (D : Dissection N) {i j : Fin N} (hij : i ≠ j) {V : Plane}
    (hi : V ∈ (D.tile i).carrier) : V ∉ interior (D.tile j).carrier := by
  intro hj
  have hcl : V ∈ closure (interior (D.tile i).carrier) := by
    rw [(D.tile i).convex.closure_interior_eq_closure_of_nonempty_interior (D.tile i).interior_nonempty,
      (D.tile i).isCompact.isClosed.closure_eq]
    exact hi
  obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.mp hcl _ isOpen_interior hj
  exact Set.disjoint_left.mp (D.interiors_disjoint hij) hy2 hy1

/-- A vertex of some tile lies in the interior of no tile. -/
theorem not_interior_of_vertex (D : Dissection N) {V : Plane} (hv : ∃ i k, (D.tile i).pts k = V)
    (j : Fin N) : V ∉ interior (D.tile j).carrier := by
  obtain ⟨i, k, hk⟩ := hv
  have hmem : V ∈ (D.tile i).carrier := hk ▸ subset_convexHull ℝ _ ⟨k, rfl⟩
  by_cases hij : i = j
  · subst hij
    intro hint
    have h1 := (D.tile i).mem_interior_iff_coord_pos V |>.mp hint
    have h2 : (D.tile i).basis.coord (k + 1) V = 0 := by
      rw [← hk]; exact (D.tile i).basis.coord_apply_ne (fin3_ne_one k)
    exact absurd h2 (h1 _).ne'
  · exact not_interior_of_mem_other D hij hmem

theorem inCone_smul_iff {p q z : V2} {c : ℝ} (hc : 0 < c) :
    inCone p q (c * z.1, c * z.2) ↔ inCone p q z := by
  unfold inCone crs
  simp only
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · by_contra h; push_neg at h; nlinarith [mul_pos hc (neg_pos.mpr h)]
    · by_contra h; push_neg at h; nlinarith [mul_pos hc (neg_pos.mpr h)]
  · rintro ⟨h1, h2⟩
    constructor <;> nlinarith [mul_nonneg hc.le h1, mul_nonneg hc.le h2]

open Erdos634.CertCoord in
/-- The point `V + ε z` as a plane point. -/
noncomputable def ptOf (V : Plane) (z : V2) (ε : ℝ) : Plane := V + ε • mkPt z.1 z.2

open Erdos634.CertCoord in
theorem toV2_ptOf (V : Plane) (z : V2) (ε : ℝ) : toV2 (ptOf V z ε - V) = (ε * z.1, ε * z.2) := by
  simp [toV2, ptOf]

open Erdos634.CertCoord in
theorem exists_ptOf_small (V : Plane) (z : V2) {r : ℝ} (hr : 0 < r) :
    ∃ ε > 0, dist (ptOf V z ε) V < r := by
  refine ⟨r / (2 * (‖mkPt z.1 z.2‖ + 1)), by positivity, ?_⟩
  rw [dist_eq_norm]
  have : ptOf V z (r / (2 * (‖mkPt z.1 z.2‖ + 1))) - V = (r / (2 * (‖mkPt z.1 z.2‖ + 1))) • mkPt z.1 z.2 := by
    simp [ptOf]
  rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hn := norm_nonneg (mkPt z.1 z.2)
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

/-! ## The family of sectors at a point -/

/-- The tiles through `V`. -/
def AtV (D : Dissection N) (V : Plane) : Type := {i : Fin N // V ∈ (D.tile i).carrier}

noncomputable instance (D : Dissection N) (V : Plane) : Fintype (AtV D V) := by
  classical unfold AtV; exact Subtype.fintype _

theorem exists_min_pos {ι : Type*} [Finite ι] (r : ι → ℝ) (hr : ∀ i, 0 < r i) : ∃ r0 > 0, ∀ i, r0 ≤ r i := by
  by_cases hne : Nonempty ι
  · obtain ⟨i0, hi0⟩ := Finite.exists_min r
    exact ⟨r i0, hr i0, hi0⟩
  · exact ⟨1, one_pos, fun i => absurd ⟨i⟩ hne⟩

theorem mem_interior_of_inInt {T : Tri} {V : Plane} {p q : V2} {r : ℝ}
    (hr : ∀ y : Plane, dist y V < r → (y ∈ T.carrier ↔ inCone p q (toV2 (y - V))))
    {y : Plane} (hy : dist y V < r) (hi : inInt p q (toV2 (y - V))) : y ∈ interior T.carrier := by
  have c0 : Continuous (fun y : Plane => y 0) := by fun_prop
  have c1 : Continuous (fun y : Plane => y 1) := by fun_prop
  have hc1 : Continuous (fun y : Plane => crs p (toV2 (y - V))) := by
    unfold crs toV2; simp only [PiLp.sub_apply]; fun_prop
  have hc2 : Continuous (fun y : Plane => crs (toV2 (y - V)) q) := by
    unfold crs toV2; simp only [PiLp.sub_apply]; fun_prop
  have hopen : IsOpen {y : Plane | dist y V < r ∧ (0 < crs p (toV2 (y - V)) ∧ 0 < crs (toV2 (y - V)) q)} :=
    (isOpen_lt (continuous_id.dist continuous_const) continuous_const).inter
      ((isOpen_lt continuous_const hc1).inter (isOpen_lt continuous_const hc2))
  refine interior_maximal ?_ hopen ⟨hy, hi.1, hi.2⟩
  intro y ⟨hy1, hy2, hy3⟩
  exact (hr y hy1).mpr ⟨hy2.le, hy3.le⟩

theorem common_radius (D : Dissection N) (V : Plane) (p q : AtV D V → V2)
    (hloc : ∀ s : AtV D V, LocalCone (D.tile s.1) V (p s) (q s)) :
    ∃ r > 0, (∀ s : AtV D V, ∀ y : Plane, dist y V < r →
        (y ∈ (D.tile s.1).carrier ↔ inCone (p s) (q s) (toV2 (y - V)))) ∧
      (∀ i : Fin N, V ∉ (D.tile i).carrier → ∀ y : Plane, dist y V < r → y ∉ (D.tile i).carrier) := by
  classical
  choose rs hrs hiff using hloc
  have hρ : ∀ i : Fin N, ∃ ρ > 0, V ∉ (D.tile i).carrier →
      ∀ y : Plane, dist y V < ρ → y ∉ (D.tile i).carrier := by
    intro i
    by_cases h : V ∈ (D.tile i).carrier
    · exact ⟨1, one_pos, fun h' => absurd h h'⟩
    · have hopen : IsOpen ((D.tile i).carrier)ᶜ := (D.tile i).isCompact.isClosed.isOpen_compl
      obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hopen V h
      exact ⟨ρ, hρ, fun _ y hy => hball (by simpa [Metric.mem_ball] using hy)⟩
  choose ρ hρpos hρ' using hρ
  obtain ⟨r1, hr1, hle1⟩ := exists_min_pos rs hrs
  obtain ⟨r2, hr2, hle2⟩ := exists_min_pos ρ hρpos
  exact ⟨min r1 r2, lt_min hr1 hr2,
    fun s y hy => hiff s y (lt_of_lt_of_le hy ((min_le_left _ _).trans (hle1 s))),
    fun i hi y hy => hρ' i hi y (lt_of_lt_of_le hy ((min_le_right _ _).trans (hle2 i)))⟩

/-- Open cones of distinct tiles through `V` are disjoint. -/
theorem tiles_disjoint (D : Dissection N) (V : Plane) (p q : AtV D V → V2)
    (hloc : ∀ s : AtV D V, LocalCone (D.tile s.1) V (p s) (q s)) :
    Disjoint' p q := by
  intro s t hst z ⟨hzs, hzt⟩
  obtain ⟨rs, hrs, hs⟩ := hloc s
  obtain ⟨rt, hrt, ht⟩ := hloc t
  obtain ⟨ε, hε, hd⟩ := exists_ptOf_small V z (lt_min hrs hrt)
  have hds : dist (ptOf V z ε) V < rs := lt_of_lt_of_le hd (min_le_left _ _)
  have hdt : dist (ptOf V z ε) V < rt := lt_of_lt_of_le hd (min_le_right _ _)
  rw [← inInt_smul_iff hε, ← toV2_ptOf V z ε] at hzs hzt
  have h1 := mem_interior_of_inInt hs hds hzs
  have h2 := mem_interior_of_inInt ht hdt hzt
  have hne : s.1 ≠ t.1 := fun h => hst (Subtype.ext h)
  exact Set.disjoint_left.mp (D.interiors_disjoint hne) h1 h2

/-- The closed cones of the tiles through `V` cover the target cone `Tgt` (a cone, locally equal to the target at `V`). -/
theorem tiles_cover (D : Dissection N) (V : Plane) (p q : AtV D V → V2)
    (hloc : ∀ s : AtV D V, LocalCone (D.tile s.1) V (p s) (q s))
    (Tgt : Set V2) (R : ℝ) (hR : 0 < R)
    (hT : ∀ y : Plane, dist y V < R → (y ∈ D.target.carrier ↔ toV2 (y - V) ∈ Tgt))
    (hTs : ∀ z ∈ Tgt, ∀ t : ℝ, 0 < t → ((t * z.1, t * z.2) : V2) ∈ Tgt) :
    ∀ z ∈ Tgt, ∃ s : AtV D V, inCone (p s) (q s) z := by
  intro z hz
  obtain ⟨r, hr, hiff, hout⟩ := common_radius D V p q hloc
  obtain ⟨ε, hε, hd⟩ := exists_ptOf_small V z (lt_min hr hR)
  have hd1 : dist (ptOf V z ε) V < r := lt_of_lt_of_le hd (min_le_left _ _)
  have hd2 : dist (ptOf V z ε) V < R := lt_of_lt_of_le hd (min_le_right _ _)
  have hy : ptOf V z ε ∈ D.target.carrier := by
    rw [hT _ hd2, toV2_ptOf]; exact hTs z hz ε hε
  rw [← D.covers] at hy
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
  have hVi : V ∈ (D.tile i).carrier := by
    by_contra hnot
    exact hout i hnot _ hd1 hi
  refine ⟨⟨i, hVi⟩, ?_⟩
  have := (hiff ⟨i, hVi⟩ _ hd1).mp hi
  rw [toV2_ptOf] at this
  exact (inCone_smul_iff hε).mp this

/-- The widths of the sectors add up to the total local angle of all the tiles. -/
theorem tiles_angle_sum (D : Dissection N) (V : Plane) (p q : AtV D V → V2)
    (hwd : ∀ s : AtV D V, wd (p s) (q s) = (D.tile s.1).localAngle V) :
    ∑ s : AtV D V, wd (p s) (q s) = ∑ i, (D.tile i).localAngle V := by
  classical
  simp only [hwd]
  have h1 := Finset.sum_subtype (Finset.univ.filter fun i : Fin N => V ∈ (D.tile i).carrier)
    (p := fun i => V ∈ (D.tile i).carrier) (F := (inferInstance : Fintype (AtV D V))) (by simp) (fun i => (D.tile i).localAngle V)
  have h2 : ∑ s : AtV D V, (D.tile s.1).localAngle V
      = ∑ i ∈ Finset.univ.filter (fun i : Fin N => V ∈ (D.tile i).carrier), (D.tile i).localAngle V := h1.symm
  rw [h2]
  apply Finset.sum_filter_of_ne
  intro i _ hne
  by_contra hmem
  exact hne (Tri.localAngle_eq_zero_of_not_mem _ hmem)

/-- **D0, interior vertex.**  Let `V` be a vertex of the tiling lying in the interior of the target.  The tiles through `V` have local
sectors at `V` (corner sectors, or one straight sector for a tile having `V` in the interior of a side), which are admissible, disjoint,
cover the plane, and whose widths (= `localAngle`) add up to `2 pi`; hence they can be listed counterclockwise `e 0, e 1, ..` with the
counterclockwise ray of each equal (up to a positive multiple) to the clockwise ray of the next, cyclically. -/
theorem vertex_fan_interior (D : Dissection N) (V : Plane) (hV : V ∈ interior D.target.carrier)
    (hvert : ∃ i k, (D.tile i).pts k = V) :
    ∃ (p q : AtV D V → V2) (e : ℕ → AtV D V),
      (∀ s, SecOK (p s) (q s)) ∧ (∀ s, LocalCone (D.tile s.1) V (p s) (q s)) ∧
      (∀ s, wd (p s) (q s) = (D.tile s.1).localAngle V) ∧ (∀ s, SectorSpec (D.tile s.1) V (p s) (q s)) ∧
      (∀ n, Par (p (e (n + 1))) (q (e n))) ∧ (∀ n, e (n + Fintype.card (AtV D V)) = e n) ∧
      Set.InjOn e (Set.Iio (Fintype.card (AtV D V))) ∧ (∀ s, ∃ j < Fintype.card (AtV D V), e j = s) := by
  classical
  have hex : ∀ s : AtV D V, ∃ pq : V2 × V2, SecOK pq.1 pq.2 ∧ LocalCone (D.tile s.1) V pq.1 pq.2 ∧
      wd pq.1 pq.2 = (D.tile s.1).localAngle V ∧ SectorSpec (D.tile s.1) V pq.1 pq.2 := by
    intro s
    obtain ⟨p, q, h1, h2, h3, h4⟩ := local_sector (D.tile s.1) s.2 (not_interior_of_vertex D hvert s.1)
    exact ⟨(p, q), h1, h2, h3, h4⟩
  choose pq hok hloc hwd hspec using hex
  set p : AtV D V → V2 := fun s => (pq s).1
  set q : AtV D V → V2 := fun s => (pq s).2
  obtain ⟨i0, k0, hk0⟩ := hvert
  haveI : Nonempty (AtV D V) := ⟨⟨i0, hk0 ▸ subset_convexHull ℝ _ ⟨k0, rfl⟩⟩⟩
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp isOpen_interior V hV
  have hcov : Covers p q := by
    intro z
    obtain ⟨s, hs⟩ := tiles_cover D V p q hloc Set.univ R hR
      (fun y hy => by
        simp only [Set.mem_univ, iff_true]
        exact interior_subset (hball (by simpa [Metric.mem_ball] using hy)))
      (fun _ _ _ _ => Set.mem_univ _) z (Set.mem_univ _)
    exact ⟨s, hs⟩
  have hsum : ∑ s, wd (p s) (q s) = 2 * Real.pi := by
    rw [tiles_angle_sum D V p q hwd, D.sum_localAngle_eq V, D.target.localAngle_interior hV]
  obtain ⟨e, h1, h2, h3, h4⟩ := fan_cycle p q hok hcov (tiles_disjoint D V p q hloc) hsum
  exact ⟨p, q, e, hok, hloc, hwd, hspec, h1, h2, h3, h4⟩

end Erdos634.Draft.LaczFormal.Graph
