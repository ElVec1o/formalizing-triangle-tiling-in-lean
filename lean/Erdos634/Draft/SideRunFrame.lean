/-
Draft/SideRunFrame.lean -- Stage 1 of the formalization of the side theorem of room GAP3: a frame for a side of a
triangular target lying on the x-axis, the target above it.

* `Tg L ax ay`: the target `Q = (0,0)`, `B = (L,0)`, `A = (ax, ay)`, `L, ay > 0`; its three side functionals
  (`Tg_bounds`), its interior (`mem_interior_Tg`, `openSegment_interior_Tg`), the side `QB` in its frontier.
* `Setup D n α β γ L ax ay`: a congruent dissection of `Tg L ax ay` with the tile `(n, n²−1, n²)`, `n ≥ 2`
  (`ModelData`, `AngleData`).  This generalizes `W2E1Frame.Setup` (the target `W_2(1,n)`, `n ≥ 3`).
* base tiles (`W2E1.BaseTile`): their angles (`Setup.angles`), apex (`Setup.apex`), the coordinates of the apex of a
  `c`-tile (`Setup.c1_data`, `Setup.c2_data`), `Setup.baseTile_ne`, `Setup.baseTile_range`;
* `Setup.typed_chain`: the side `QB` is a chain of base tiles, each of one of the six types;
* the corners: `Setup.corner_right_beta`, `Setup.corner_left_beta` (a neighbouring side along the direction of the
  `a`-edge of a `c`-tile makes the angle `β`), `Setup.corner_left_ab` (direction `(1, √(4n²−1))`: angle `α + β`);
  `Setup.corner_tile_beta`: at a corner of angle `β` every tile containing the corner shows `β` there;
* `Setup.three_alpha_lt_beta`: `3α < β` for `n ≥ 3`.

Composite-N work; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.W2E1Frame
import Erdos634.Draft.SideRunTools

namespace Erdos634.Draft.SideRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Set

/-! ## 1. The target -/

theorem Tg_det {L ay : ℝ} (hL : 0 < L) (hay : 0 < ay) (ax : ℝ) : 0 < det3 0 0 L 0 ax ay := by
  have e : det3 0 0 L 0 ax ay = L * ay := by unfold det3; ring
  rw [e]; exact mul_pos hL hay

/-- **The target**: `Q = (0,0)`, `B = (L,0)`, `A = (ax, ay)`. -/
noncomputable def Tg (L ax ay : ℝ) (hL : 0 < L) (hay : 0 < ay) : Tri :=
  mkTri 0 0 L 0 ax ay (Tg_det hL hay ax).ne'

theorem Tg_pts0 {L ax ay : ℝ} (hL : 0 < L) (hay : 0 < ay) : (Tg L ax ay hL hay).pts 0 = mkPt 0 0 := rfl
theorem Tg_pts1 {L ax ay : ℝ} (hL : 0 < L) (hay : 0 < ay) : (Tg L ax ay hL hay).pts 1 = mkPt L 0 := rfl
theorem Tg_pts2 {L ax ay : ℝ} (hL : 0 < L) (hay : 0 < ay) : (Tg L ax ay hL hay).pts 2 = mkPt ax ay := rfl

/-- the functional of the side `QA`, nonnegative on the target -/
def gA (ax ay : ℝ) (p : Plane) : ℝ := ay * p 0 - ax * p 1

/-- the functional of the side `BA`, nonnegative on the target -/
def gB (L ax ay : ℝ) (p : Plane) : ℝ := ay * (L - p 0) - (L - ax) * p 1

theorem gA_mk (ax ay x y : ℝ) : gA ax ay (mkPt x y) = ay * x - ax * y := by
  simp only [gA, mkPt_zero, mkPt_one]

theorem gB_mk (L ax ay x y : ℝ) : gB L ax ay (mkPt x y) = ay * (L - x) - (L - ax) * y := by
  simp only [gB, mkPt_zero, mkPt_one]

theorem gA_combo (ax ay a b : ℝ) (x y : Plane) :
    gA ax ay (a • x + b • y) = a * gA ax ay x + b * gA ax ay y := by
  simp only [gA, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

theorem gB_combo (L ax ay : ℝ) {a b : ℝ} (hab : a + b = 1) (x y : Plane) :
    gB L ax ay (a • x + b • y) = a * gB L ax ay x + b * gB L ax ay y := by
  have hb1 : b = 1 - a := by linarith
  subst hb1
  simp only [gB, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

/-- **The target lies on the inner side of its three side lines.** -/
theorem Tg_bounds {L ax ay : ℝ} (hL : 0 < L) (hay : 0 < ay) {q : Plane}
    (hq : q ∈ (Tg L ax ay hL hay).carrier) : 0 ≤ q 1 ∧ 0 ≤ gA ax ay q ∧ 0 ≤ gB L ax ay q := by
  have hconv : Convex ℝ {q : Plane | 0 ≤ q 1 ∧ 0 ≤ gA ax ay q ∧ 0 ≤ gB L ax ay q} := by
    intro x hx y hy a b ha hb' hab
    obtain ⟨h1, h2, h3⟩ := hx
    obtain ⟨k1, k2, k3⟩ := hy
    have e1 : (a • x + b • y) 1 = a * x 1 + b * y 1 := by simp
    show 0 ≤ (a • x + b • y) 1 ∧ 0 ≤ gA ax ay (a • x + b • y) ∧ 0 ≤ gB L ax ay (a • x + b • y)
    rw [e1, gA_combo, gB_combo L ax ay hab]
    exact ⟨add_nonneg (mul_nonneg ha h1) (mul_nonneg hb' k1),
      add_nonneg (mul_nonneg ha h2) (mul_nonneg hb' k2),
      add_nonneg (mul_nonneg ha h3) (mul_nonneg hb' k3)⟩
  have hLa := mul_pos hay hL
  have hQ : 0 ≤ ((Tg L ax ay hL hay).pts 0) 1 ∧ 0 ≤ gA ax ay ((Tg L ax ay hL hay).pts 0)
      ∧ 0 ≤ gB L ax ay ((Tg L ax ay hL hay).pts 0) := by
    rw [Tg_pts0, gA_mk, gB_mk, mkPt_one]
    refine ⟨le_refl _, ?_, ?_⟩
    · have e : ay * 0 - ax * 0 = 0 := by ring
      exact e.symm.le
    · have e : ay * (L - 0) - (L - ax) * 0 = ay * L := by ring
      rw [e]; exact hLa.le
  have hB : 0 ≤ ((Tg L ax ay hL hay).pts 1) 1 ∧ 0 ≤ gA ax ay ((Tg L ax ay hL hay).pts 1)
      ∧ 0 ≤ gB L ax ay ((Tg L ax ay hL hay).pts 1) := by
    rw [Tg_pts1, gA_mk, gB_mk, mkPt_one]
    refine ⟨le_refl _, ?_, ?_⟩
    · have e : ay * L - ax * 0 = ay * L := by ring
      rw [e]; exact hLa.le
    · have e : ay * (L - L) - (L - ax) * 0 = 0 := by ring
      exact e.symm.le
  have hA : 0 ≤ ((Tg L ax ay hL hay).pts 2) 1 ∧ 0 ≤ gA ax ay ((Tg L ax ay hL hay).pts 2)
      ∧ 0 ≤ gB L ax ay ((Tg L ax ay hL hay).pts 2) := by
    rw [Tg_pts2, gA_mk, gB_mk, mkPt_one]
    refine ⟨hay.le, ?_, ?_⟩
    · have e : ay * ax - ax * ay = 0 := by ring
      exact e.symm.le
    · have e : ay * (L - ax) - (L - ax) * ay = 0 := by ring
      exact e.symm.le
  have hsub : (Tg L ax ay hL hay).carrier
      ⊆ {q : Plane | 0 ≤ q 1 ∧ 0 ≤ gA ax ay q ∧ 0 ≤ gB L ax ay q} := by
    refine convexHull_min ?_ hconv
    rintro _ ⟨k, rfl⟩
    exact forall_pts (T := Tg L ax ay hL hay)
      (P := fun q => 0 ≤ q 1 ∧ 0 ≤ gA ax ay q ∧ 0 ≤ gB L ax ay q) hQ hB hA k
  exact hsub hq

/-- **Strict signs put a point in the interior of the target.** -/
theorem mem_interior_Tg {L ax ay : ℝ} (hL : 0 < L) (hay : 0 < ay) {q : Plane} (h1 : 0 < q 1)
    (h2 : 0 < gA ax ay q) (h3 : 0 < gB L ax ay q) : q ∈ interior (Tg L ax ay hL hay).carrier := by
  have e0 : det3 (q 0) (q 1) L 0 ax ay = gB L ax ay q := by unfold det3 gB; ring
  have e1 : det3 0 0 (q 0) (q 1) ax ay = gA ax ay q := by unfold det3 gA; ring
  have e2 : det3 0 0 L 0 (q 0) (q 1) = L * q 1 := by unfold det3; ring
  have h := Erdos634.ChordChartPlanar.mem_interior_carrier_of_dets_pos (Tg_det hL hay ax) (a := q 0)
    (b := q 1) (by rw [e0]; exact h3) (by rw [e1]; exact h2) (by rw [e2]; exact mul_pos hL h1)
  rw [Erdos634.ChordChartPlanar.mkPt_coords] at h
  exact h

/-- **An open segment between two points of the target that share no side line is interior to the target.** -/
theorem openSegment_interior_Tg {L ax ay : ℝ} (hL : 0 < L) (hay : 0 < ay) {P Q : Plane}
    (hP : P ∈ (Tg L ax ay hL hay).carrier) (hQ : Q ∈ (Tg L ax ay hL hay).carrier)
    (h1 : 0 < P 1 ∨ 0 < Q 1) (h2 : 0 < gA ax ay P ∨ 0 < gA ax ay Q)
    (h3 : 0 < gB L ax ay P ∨ 0 < gB L ax ay Q) :
    openSegment ℝ P Q ⊆ interior (Tg L ax ay hL hay).carrier := by
  obtain ⟨p1, p2, p3⟩ := Tg_bounds hL hay hP
  obtain ⟨q1, q2, q3⟩ := Tg_bounds hL hay hQ
  rintro y ⟨a, b, ha, hb, hab, rfl⟩
  have e1 : (a • P + b • Q) 1 = a * P 1 + b * Q 1 := by simp
  refine mem_interior_Tg hL hay ?_ ?_ ?_
  · rw [e1]; exact pos_combo ha hb p1 q1 h1
  · rw [gA_combo]; exact pos_combo ha hb p2 q2 h2
  · rw [gB_combo L ax ay hab]; exact pos_combo ha hb p3 q3 h3

theorem base_mem_frontier_Tg {L ax ay : ℝ} (hL : 0 < L) (hay : 0 < ay) {v : ℝ} (h0 : 0 ≤ v)
    (hv : v ≤ L) : mkPt v 0 ∈ frontier (Tg L ax ay hL hay).carrier := by
  apply Erdos634.SideWall.edge_subset_frontier (Tg L ax ay hL hay) 0
  show mkPt v 0 ∈ segment ℝ (mkPt 0 0) (mkPt L 0)
  exact (mem_base_segment_iff hL _).mpr
    ⟨mkPt_one _ _, by rw [mkPt_zero]; exact h0, by rw [mkPt_zero]; exact hv⟩

theorem not_vertex_Tg {L ax ay : ℝ} (hL : 0 < L) (hay : 0 < ay) {p : Plane} (h0 : p ≠ mkPt 0 0)
    (h1 : p ≠ mkPt L 0) (h2 : p ≠ mkPt ax ay) : p ∉ Set.range (Tg L ax ay hL hay).pts := by
  rintro ⟨k, hk⟩
  exact forall_pts (T := Tg L ax ay hL hay) (P := fun q => q = p → False) (fun h => h0 h.symm)
    (fun h => h1 h.symm) (fun h => h2 h.symm) k hk

/-! ## 2. The standing hypotheses -/

/-- **The standing hypotheses**: a congruent dissection of the triangle `Q = (0,0)`, `B = (L,0)`, `A = (ax, ay)`
with the tile `(n, n²−1, n²)`, `n ≥ 2`, and its angles. -/
structure Setup {N : ℕ} (D : CongruentDissection N) (n : ℕ) (α β γ L ax ay : ℝ) : Prop where
  hn2 : 2 ≤ n
  hM : ModelData D (n:ℝ) α β γ
  hA : AngleData α β γ
  hL : 0 < L
  hay : 0 < ay
  htgt : ∀ (h1 : 0 < L) (h2 : 0 < ay), D.target = Tg L ax ay h1 h2

namespace Setup

variable {N : ℕ} {D : CongruentDissection N} {n : ℕ} {α β γ L ax ay : ℝ}

theorem f2 (S : Setup D n α β γ L ax ay) : (2:ℝ) ≤ n := by exact_mod_cast S.hn2
theorem f1 (S : Setup D n α β γ L ax ay) : (1:ℝ) < n := by have := S.f2; linarith
theorem f0 (S : Setup D n α β γ L ax ay) : (0:ℝ) < n := by have := S.f2; linarith
theorem b_pos (S : Setup D n α β γ L ax ay) : (0:ℝ) < (n:ℝ) ^ 2 - 1 := by have := S.f2; nlinarith
theorem c_pos (S : Setup D n α β γ L ax ay) : (0:ℝ) < (n:ℝ) ^ 2 := by have := S.f0; positivity
theorem tgt (S : Setup D n α β γ L ax ay) : D.target = Tg L ax ay S.hL S.hay := S.htgt S.hL S.hay

theorem mem (S : Setup D n α β γ L ax ay) {p : Plane} (hp : p ∈ D.target.carrier) :
    0 ≤ p 1 ∧ 0 ≤ gA ax ay p ∧ 0 ≤ gB L ax ay p := by
  rw [S.tgt] at hp; exact Tg_bounds S.hL S.hay hp

theorem pts_mem (S : Setup D n α β γ L ax ay) (i : Fin N) (k : Fin 3) :
    0 ≤ ((D.tile i).pts k) 1 ∧ 0 ≤ gA ax ay ((D.tile i).pts k) ∧ 0 ≤ gB L ax ay ((D.tile i).pts k) :=
  S.mem (pts_mem_target D.toDissection i k)

theorem interior_seg (S : Setup D n α β γ L ax ay) {P Q : Plane} (hP : P ∈ D.target.carrier)
    (hQ : Q ∈ D.target.carrier) (h1 : 0 < P 1 ∨ 0 < Q 1)
    (h2 : 0 < gA ax ay P ∨ 0 < gA ax ay Q) (h3 : 0 < gB L ax ay P ∨ 0 < gB L ax ay Q) :
    openSegment ℝ P Q ⊆ interior D.target.carrier := by
  rw [S.tgt] at hP hQ ⊢; exact openSegment_interior_Tg S.hL S.hay hP hQ h1 h2 h3

/-- a point of the target with a point of the target strictly on its left is off the side `QA` -/
theorem gA_pos_of_left (S : Setup D n α β γ L ax ay) {x y t : ℝ} (ht : 0 < t)
    (h : mkPt (x - t) y ∈ D.target.carrier) : 0 < gA ax ay (mkPt x y) := by
  have h1 := (S.mem h).2.1
  rw [gA_mk] at h1 ⊢
  nlinarith [mul_pos S.hay ht]

/-- a point of the target with a point of the target strictly on its right is off the side `BA` -/
theorem gB_pos_of_right (S : Setup D n α β γ L ax ay) {x y t : ℝ} (ht : 0 < t)
    (h : mkPt (x + t) y ∈ D.target.carrier) : 0 < gB L ax ay (mkPt x y) := by
  have h1 := (S.mem h).2.2
  rw [gB_mk] at h1 ⊢
  nlinarith [mul_pos S.hay ht]

/-- a point of the side line `y = 0` in the target lies between `Q` and `B` -/
theorem base_range (S : Setup D n α β γ L ax ay) {x : ℝ} (h : mkPt x 0 ∈ D.target.carrier) :
    0 ≤ x ∧ x ≤ L := by
  obtain ⟨-, h2, h3⟩ := S.mem h
  rw [gA_mk] at h2
  rw [gB_mk] at h3
  have hay := S.hay
  constructor
  · by_contra hneg
    push Not at hneg
    nlinarith [mul_pos hay (neg_pos.mpr hneg)]
  · by_contra hneg
    push Not at hneg
    nlinarith [mul_pos hay (sub_pos.mpr hneg)]

/-- a line through a base point leaves the target below the base -/
theorem below_out (S : Setup D n α β γ L ax ay) {V G : Plane} (hV : V 1 = 0) (hG : 0 < G 1) :
    ∀ s : ℝ, 0 < s → V + s • (V - G) ∉ D.target.carrier := by
  intro s hs hmem
  have h := (S.mem hmem).1
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, hV] at h
  nlinarith [mul_pos hs hG]

theorem base_frontier (S : Setup D n α β γ L ax ay) {x : ℝ} (hx0 : 0 < x) (hxL : x < L) :
    mkPt x 0 ∈ frontier D.target.carrier ∧ mkPt x 0 ∉ Set.range D.target.pts := by
  rw [S.tgt]
  refine ⟨base_mem_frontier_Tg S.hL S.hay hx0.le hxL.le, not_vertex_Tg S.hL S.hay ?_ ?_ ?_⟩
  · exact mkPt_ne_of_fst hx0.ne'
  · exact mkPt_ne_of_fst hxL.ne
  · exact mkPt_ne_of_snd S.hay.ne

theorem angle_base (S : Setup D n α β γ L ax ay) {x : ℝ} (hx0 : 0 < x) (hxL : x < L) :
    D.target.localAngle (mkPt x 0) = Real.pi :=
  Tri.localAngle_frontier _ (S.base_frontier hx0 hxL).1 (S.base_frontier hx0 hxL).2

theorem beta_eq (S : Setup D n α β γ L ax ay) : β = modelBeta 1 n := beta_eq_modelBeta D S.f2 S.hM

theorem alpha_eq (S : Setup D n α β γ L ax ay) : α = modelAlpha 1 n := by
  have h1 := S.beta_eq
  have h2 := modelAngle_rel 1 (n:ℝ)
  have h3 := S.hA.hrel
  rw [← h1] at h2
  linarith

theorem alpha_lt_beta (S : Setup D n α β γ L ax ay) : α < β := by
  have h2 := modelAlpha_lt_modelBeta S.f2
  rw [← S.alpha_eq, ← S.beta_eq] at h2
  exact h2

theorem cos_gamma (S : Setup D n α β γ L ax ay) : Real.cos γ = -1 / (2 * (n:ℝ)) := by
  obtain ⟨m01, m12, m20⟩ := model_dists D S.hM
  have h := Erdos634.AngleThreshold.cos_gamma_closed (D.model.pts 1) (D.model.pts 2)
    (D.model.pts 0) (n:ℝ) S.f1 m12 (by rw [dist_comm]; exact m20) (by rw [dist_comm]; exact m01)
  have hc : cornerAngle (D.model.pts 1) (D.model.pts 2) (D.model.pts 0) = γ := by
    rw [← S.hM.hγ']; unfold cornerAngle; exact EuclideanGeometry.angle_comm _ _ _
  rw [hc] at h; exact h

/-- **`3α < β` for `n ≥ 3`** (`cos α = 1 − 1/(2n²) ≥ 17/18` and `cos 3α = 4cos³α − 3cos α > 1/2`). -/
theorem three_alpha_lt_beta (S : Setup D n α β γ L ax ay) (hn3 : 3 ≤ n) : 3 * α < β := by
  have hn3' : (3:ℝ) ≤ n := by exact_mod_cast hn3
  have hα := S.hA.hα
  have hβ := S.hA.hβ
  have hrel := S.hA.hrel
  have hπ := Real.pi_pos
  have hcos := cos_modelAlpha (e := 1) (f := (n:ℝ)) one_pos S.f1
  rw [← S.alpha_eq] at hcos
  have hf0 := S.f0
  have h2n : (0:ℝ) < 2 * (n:ℝ) ^ 2 := by positivity
  have hc1 : (17:ℝ) / 18 ≤ Real.cos α := by
    rw [hcos, le_div_iff₀ h2n]
    nlinarith [mul_nonneg (show (0:ℝ) ≤ (n:ℝ) - 3 by linarith) (show (0:ℝ) ≤ (n:ℝ) + 3 by linarith)]
  have hd : 0 ≤ Real.cos α - 17 / 18 := by linarith
  have h3 := Real.cos_three_mul α
  have hlt : 3 * α < Real.pi / 3 := by
    by_contra hge
    push Not at hge
    have h4 := Real.cos_le_cos_of_nonneg_of_le_pi (by positivity : (0:ℝ) ≤ Real.pi / 3)
      (by linarith : 3 * α ≤ Real.pi) hge
    rw [Real.cos_pi_div_three, h3] at h4
    nlinarith [mul_nonneg hd hd, mul_nonneg (mul_nonneg hd hd) hd]
  linarith

end Setup

/-! ## 3. Base tiles -/

namespace Setup

variable {N : ℕ} {D : CongruentDissection N} {n : ℕ} {α β γ L ax ay : ℝ}

/-- **The angles of a base tile at its two ends.** -/
theorem angles (S : Setup D n α β γ L ax ay) {i : Fin N} {t : Ty} {x : ℝ} (h : BaseTile D n i t x) :
    (D.tile i).localAngle (mkPt x 0) = t.aL α β γ ∧
    (D.tile i).localAngle (mkPt (x + t.lenR n) 0) = t.aR α β γ := by
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hsL, hsR⟩ := h
  have hL := angle_at_vertex D S.f2 S.hM i hkm hkj hmj
  have hR := angle_at_vertex D S.f2 S.hM i (Ne.symm hkm) hmj hkj
  rw [hk] at hL
  rw [hm] at hR
  rw [dist_comm] at hsL hsR
  cases t
  · exact ⟨hL.2.1 hsR, hR.2.2 hsL⟩
  · exact ⟨hL.2.2 hsR, hR.2.1 hsL⟩
  · exact ⟨hL.1 hsR, hR.2.2 hsL⟩
  · exact ⟨hL.2.2 hsR, hR.1 hsL⟩
  · exact ⟨hL.1 hsR, hR.2.1 hsL⟩
  · exact ⟨hL.2.1 hsR, hR.1 hsL⟩

/-- **The apex of a base tile**: above the side, at the two prescribed distances; it is the only vertex of the tile
off the side. -/
theorem apex (S : Setup D n α β γ L ax ay) {i : Fin N} {t : Ty} {x : ℝ} (h : BaseTile D n i t x) :
    ∃ p : Plane, p ∈ Set.range (D.tile i).pts ∧ 0 < p 1 ∧
      dist p (mkPt x 0) = t.sL n ∧ dist p (mkPt (x + t.lenR n) 0) = t.sR n ∧
      2 * t.lenR n * (p 0 - x) = t.sL n ^ 2 - t.sR n ^ 2 + t.lenR n ^ 2 ∧
      ∀ q ∈ Set.range (D.tile i).pts, q 1 ≠ 0 → q = p := by
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hsL, hsR⟩ := h
  have hne : ((D.tile i).pts j) 1 ≠ 0 :=
    third_not_on_line (D.tile i) hkm hkj hmj (by rw [hk, mkPt_one]) (by rw [hm, mkPt_one])
  have hpos : 0 < ((D.tile i).pts j) 1 := lt_of_le_of_ne (S.pts_mem i j).1 (Ne.symm hne)
  rw [hk] at hsL
  rw [hm] at hsR
  have e1 := sq_of_dist hsL
  have e2 := sq_of_dist hsR
  refine ⟨(D.tile i).pts j, ⟨j, rfl⟩, hpos, hsL, hsR, by linear_combination e1 - e2, ?_⟩
  rintro q ⟨j', rfl⟩ hq
  rcases fin3_cover k m j hkm hkj hmj j' with h | h | h
  · rw [h, hk, mkPt_one] at hq; exact absurd rfl hq
  · rw [h, hm, mkPt_one] at hq; exact absurd rfl hq
  · rw [h]

/-- **A `C2` tile in coordinates**: `β` at `(x, 0)`, `α` at `(x + c, 0)`, apex `(x + u, h)`. -/
theorem c2_data (S : Setup D n α β γ L ax ay) {i : Fin N} {x : ℝ} (h : BaseTile D n i Ty.C2 x) :
    HasV D i (mkPt (x + (n:ℝ) ^ 2) 0) (mkPt x 0) (mkPt (x + uu n) (hh n)) := by
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hsL, hsR⟩ := h
  have hsL' : dist ((D.tile i).pts j) ((D.tile i).pts k) = (n:ℝ) := hsL
  have hm' : (D.tile i).pts m = mkPt (x + (n:ℝ) ^ 2) 0 := hm
  have hsR' : dist ((D.tile i).pts j) ((D.tile i).pts m) = (n:ℝ) ^ 2 - 1 := hsR
  have hne : ((D.tile i).pts j) 1 ≠ 0 :=
    third_not_on_line (D.tile i) hkm hkj hmj (by rw [hk, mkPt_one]) (by rw [hm', mkPt_one])
  have hpos : 0 < ((D.tile i).pts j) 1 := lt_of_le_of_ne (S.pts_mem i j).1 (Ne.symm hne)
  rw [hk] at hsL'
  rw [hm'] at hsR'
  have e1 := sq_of_dist hsL'
  have e2 := sq_of_dist hsR'
  have hu := uu_spec S.f1
  have hX : ((D.tile i).pts j) 0 - x = uu n := by
    have h1 : 2 * (n:ℝ) ^ 2 * (((D.tile i).pts j) 0 - x) = 3 * (n:ℝ) ^ 2 - 1 := by
      linear_combination e1 - e2
    have h2 : 2 * (n:ℝ) ^ 2 * (((D.tile i).pts j) 0 - x - uu n) = 0 := by
      linear_combination h1 - hu
    have := cancel2 S.f1 h2
    linarith
  have hY : ((D.tile i).pts j) 1 = hh n := by
    have h3 : ((D.tile i).pts j) 1 ^ 2 = hh n ^ 2 := by
      rw [hh_sq S.f1, ← hX]; linear_combination e1
    exact (sq_eq_sq₀ hpos.le (hh_pos S.f1).le).mp h3
  have hGeq : (D.tile i).pts j = mkPt (x + uu n) (hh n) :=
    plane_ext (by rw [mkPt_zero]; linarith) (by rw [mkPt_one]; exact hY)
  exact ⟨m, k, j, Ne.symm hkm, hmj, hkj, hm', hk, hGeq⟩

/-- **A `C1` tile in coordinates**: `α` at `(x, 0)`, `β` at `(x + c, 0)`, apex `(x + c − u, h)`. -/
theorem c1_data (S : Setup D n α β γ L ax ay) {i : Fin N} {x : ℝ} (h : BaseTile D n i Ty.C1 x) :
    HasV D i (mkPt x 0) (mkPt (x + (n:ℝ) ^ 2) 0) (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) := by
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hsL, hsR⟩ := h
  have hsL' : dist ((D.tile i).pts j) ((D.tile i).pts k) = (n:ℝ) ^ 2 - 1 := hsL
  have hm' : (D.tile i).pts m = mkPt (x + (n:ℝ) ^ 2) 0 := hm
  have hsR' : dist ((D.tile i).pts j) ((D.tile i).pts m) = (n:ℝ) := hsR
  have hne : ((D.tile i).pts j) 1 ≠ 0 :=
    third_not_on_line (D.tile i) hkm hkj hmj (by rw [hk, mkPt_one]) (by rw [hm', mkPt_one])
  have hpos : 0 < ((D.tile i).pts j) 1 := lt_of_le_of_ne (S.pts_mem i j).1 (Ne.symm hne)
  rw [hk] at hsL'
  rw [hm'] at hsR'
  have e1 := sq_of_dist hsL'
  have e2 := sq_of_dist hsR'
  have hu := uu_spec S.f1
  have hX : ((D.tile i).pts j) 0 - x = (n:ℝ) ^ 2 - uu n := by
    have h1 : 2 * (n:ℝ) ^ 2 * (((D.tile i).pts j) 0 - x) = 2 * (n:ℝ) ^ 4 - 3 * (n:ℝ) ^ 2 + 1 := by
      linear_combination e1 - e2
    have h2 : 2 * (n:ℝ) ^ 2 * (((D.tile i).pts j) 0 - x - ((n:ℝ) ^ 2 - uu n)) = 0 := by
      linear_combination h1 + hu
    have := cancel2 S.f1 h2
    linarith
  have hY : ((D.tile i).pts j) 1 = hh n := by
    have h3 : ((D.tile i).pts j) 1 ^ 2 = hh n ^ 2 := by
      rw [hh_sq' S.f1, ← hX]; linear_combination e1
    exact (sq_eq_sq₀ hpos.le (hh_pos S.f1).le).mp h3
  have hGeq : (D.tile i).pts j = mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n) :=
    plane_ext (by rw [mkPt_zero]; linarith) (by rw [mkPt_one]; exact hY)
  exact ⟨k, m, j, hkm, hkj, hmj, hk, hm', hGeq⟩

/-- two base tiles at different places are different tiles -/
theorem baseTile_ne (S : Setup D n α β γ L ax ay) {i j : Fin N} {t t' : Ty} {x x' : ℝ}
    (h : BaseTile D n i t x) (h' : BaseTile D n j t' x') (hx : x ≠ x') : i ≠ j := by
  rintro rfl
  obtain ⟨k, m, j₁, hkm, hkj, hmj, hk, hm, -, -⟩ := h
  obtain ⟨k', m', j₁', hkm', -, -, hk', hm', -, -⟩ := h'
  have hl := Ty.lenR_pos S.f2 t
  have hl' := Ty.lenR_pos S.f2 t'
  have hne : ((D.tile i).pts j₁) 1 ≠ 0 :=
    third_not_on_line (D.tile i) hkm hkj hmj (by rw [hk, mkPt_one]) (by rw [hm, mkPt_one])
  have hk'j : k' ≠ j₁ := by
    intro h0
    rw [← h0, hk', mkPt_one] at hne
    exact hne rfl
  have hm'j : m' ≠ j₁ := by
    intro h0
    rw [← h0, hm', mkPt_one] at hne
    exact hne rfl
  rcases fin3_cover k m j₁ hkm hkj hmj k' with h1 | h1 | h1
  · rw [h1, hk] at hk'
    exact hx (mkPt_inj hk').1
  · rcases fin3_cover k m j₁ hkm hkj hmj m' with h2 | h2 | h2
    · rw [h1, hm] at hk'
      rw [h2, hk] at hm'
      have e1 := (mkPt_inj hk').1
      have e2 := (mkPt_inj hm').1
      linarith
    · exact absurd (h1.trans h2.symm) hkm'
    · exact absurd h2 hm'j
  · exact absurd h1 hk'j

/-- a base tile lies over the side `QB` -/
theorem baseTile_range (S : Setup D n α β γ L ax ay) {i : Fin N} {t : Ty} {x : ℝ}
    (h : BaseTile D n i t x) : 0 ≤ x ∧ x + t.lenR n ≤ L := by
  obtain ⟨k, m, j, -, -, -, hk, hm, -, -⟩ := h
  have h1 : mkPt x 0 ∈ D.target.carrier := by rw [← hk]; exact pts_mem_target D.toDissection i k
  have h2 : mkPt (x + t.lenR n) 0 ∈ D.target.carrier := by
    rw [← hm]; exact pts_mem_target D.toDissection i m
  exact ⟨(S.base_range h1).1, (S.base_range h2).2⟩

/-! ## 4. The typed chain -/

/-- **THE TYPED CHAIN ON `QB`.**  The side `QB` of the target is cut into `m ≥ 1` consecutive edges
`[X k, X (k+1)]`, `X 0 = 0`, `X m = L`, each the letter of a base tile `tile k` of type `τ k`. -/
theorem typed_chain (S : Setup D n α β γ L ax ay) :
    ∃ (m : ℕ) (X : ℕ → ℝ) (tile : ℕ → Fin N) (τ : ℕ → Ty), 0 < m ∧ X 0 = 0 ∧ X m = L ∧
      (∀ k, k < m → X (k + 1) = X k + (τ k).lenR n) ∧
      (∀ k, k < m → BaseTile D n (tile k) (τ k) (X k)) := by
  have hf := S.f2
  have hb := S.b_pos
  have hbase : segment ℝ (mkPt 0 0) (mkPt L 0) ⊆ frontier D.target.carrier := by
    intro y hy
    obtain ⟨h1, h0, hL'⟩ := (mem_base_segment_iff S.hL y).mp hy
    rw [S.tgt, eq_mkPt_of_y_zero h1]
    exact base_mem_frontier_Tg S.hL S.hay h0 hL'
  have hface : ∀ y ∈ D.target.carrier, y 1 = 0 → 0 ≤ y 0 ∧ y 0 ≤ L := by
    intro y hy h1
    rw [eq_mkPt_of_y_zero h1] at hy
    exact S.base_range hy
  obtain ⟨m, X, hm0, hX0, hXm, hℓ, htile⟩ :=
    base_chain_gen D S.hM S.hL (fun y hy => (S.mem hy).1) hbase hface
  have hN : 0 < N := D.toDissection.pos
  have key : ∀ k, ∃ (i : Fin N) (t : Ty), k < m →
      (X (k + 1) = X k + t.lenR n ∧ BaseTile D n i t (X k)) := by
    intro k
    by_cases hk : k < m
    · obtain ⟨i, k₁, k₂, hne, h1, h2⟩ := htile k hk
      obtain ⟨j, hj1, hj2⟩ := fin3_third k₁ k₂ hne
      have hpos : 0 ≤ X (k + 1) - X k := by
        rcases hℓ k hk with h | h | h <;> rw [h] <;> nlinarith
      have hd : dist ((D.tile i).pts k₁) ((D.tile i).pts k₂) = X (k + 1) - X k := by
        have h3 := dist_mkPt_base (X k) (X (k + 1) - X k) hpos
        have e : X k + (X (k + 1) - X k) = X (k + 1) := by ring
        rw [e] at h3
        rw [h1, h2]; exact h3
      rcases hℓ k hk with ha | hb' | hc
      · have hX : X (k + 1) = X k + Ty.lenR (n:ℝ) Ty.A1 := by
          show X (k + 1) = X k + (n:ℝ); linarith
        rcases sides_of_a_edge D hf S.hM i hne (Ne.symm hj1) (Ne.symm hj2) (hd.trans ha) with
          ⟨s1, s2⟩ | ⟨s1, s2⟩
        · exact ⟨i, Ty.A1, fun _ => ⟨hX, k₁, k₂, j, hne, Ne.symm hj1, Ne.symm hj2, h1,
            by rw [h2, hX], s1, s2⟩⟩
        · exact ⟨i, Ty.A2, fun _ => ⟨hX, k₁, k₂, j, hne, Ne.symm hj1, Ne.symm hj2, h1,
            by rw [h2, hX]; rfl, s1, s2⟩⟩
      · have hX : X (k + 1) = X k + Ty.lenR (n:ℝ) Ty.B1 := by
          show X (k + 1) = X k + ((n:ℝ) ^ 2 - 1); linarith
        rcases sides_of_b_edge D hf S.hM i hne (Ne.symm hj1) (Ne.symm hj2) (hd.trans hb') with
          ⟨s1, s2⟩ | ⟨s1, s2⟩
        · exact ⟨i, Ty.B2, fun _ => ⟨hX, k₁, k₂, j, hne, Ne.symm hj1, Ne.symm hj2, h1,
            by rw [h2, hX]; rfl, s1, s2⟩⟩
        · exact ⟨i, Ty.B1, fun _ => ⟨hX, k₁, k₂, j, hne, Ne.symm hj1, Ne.symm hj2, h1,
            by rw [h2, hX], s1, s2⟩⟩
      · have hX : X (k + 1) = X k + Ty.lenR (n:ℝ) Ty.C1 := by
          show X (k + 1) = X k + (n:ℝ) ^ 2; linarith
        rcases sides_of_c_edge D hf S.hM i hne (Ne.symm hj1) (Ne.symm hj2) (hd.trans hc) with
          ⟨s1, s2⟩ | ⟨s1, s2⟩
        · exact ⟨i, Ty.C2, fun _ => ⟨hX, k₁, k₂, j, hne, Ne.symm hj1, Ne.symm hj2, h1,
            by rw [h2, hX]; rfl, s1, s2⟩⟩
        · exact ⟨i, Ty.C1, fun _ => ⟨hX, k₁, k₂, j, hne, Ne.symm hj1, Ne.symm hj2, h1,
            by rw [h2, hX], s1, s2⟩⟩
    · exact ⟨⟨0, hN⟩, Ty.A1, fun h => absurd h hk⟩
  choose tile τ hkey using key
  exact ⟨m, X, tile, τ, hm0, hX0, hXm, fun k hk => (hkey k hk).1, fun k hk => (hkey k hk).2⟩

/-! ## 5. The corners -/

/-- the neighbouring side at `B` runs along the `a`-edge of a `C1` tile: the angle of the target at `B` is `β` -/
theorem corner_right_beta (S : Setup D n α β γ L ax ay) {t : ℝ} (ht : 0 < t)
    (hax : ax = L - t * uu n) (hay' : ay = t * hh n) :
    cornerAngle (D.target.pts (1 + 1)) (D.target.pts 1) (D.target.pts (1 + 2)) = β := by
  have hf1 := S.f1
  have hf0 := S.f0
  have hL := S.hL
  have hπ := Real.pi_pos
  have hsq := hh_sq S.f1
  have hu := uu_spec S.f1
  rw [S.tgt, show ((1 : Fin 3) + 1) = 2 by decide, show ((1 : Fin 3) + 2) = 0 by decide, Tg_pts0,
    Tg_pts1, Tg_pts2]
  have h1 : dist (mkPt ax ay) (mkPt L 0) = t * n := by
    refine dist_eq_of_sq_eq ?_ dist_nonneg (by positivity)
    rw [dist_sq_mkPt, hax, hay']
    linear_combination t ^ 2 * hsq
  have h2 : dist (mkPt 0 0) (mkPt L 0) = L := by
    have := dist_mkPt_base 0 L hL.le
    rwa [zero_add] at this
  have hcos := Erdos634.AngleThreshold.cos_of_sides (mkPt ax ay) (mkPt L 0) (mkPt 0 0)
    (by rw [h1]; positivity) (by rw [h2]; exact hL.ne')
  rw [h1, h2, dist_sq_mkPt] at hcos
  rw [S.beta_eq]
  have hmem := modelBeta_mem one_pos hf1
  refine cornerAngle_eq_of_cos hmem.1.le (by linarith) ?_
  rw [hcos, cos_modelBeta one_pos hf1, baseLen_one]
  have hB : 2 * (t * (n:ℝ)) * L ≠ 0 := by positivity
  have hD : 2 * (n:ℝ) ^ 3 ≠ 0 := by positivity
  rw [div_eq_div_iff hB hD, hax, hay']
  linear_combination (2 * t * (n:ℝ) * L) * hu - (2 * (n:ℝ) ^ 3 * t ^ 2) * hsq

/-- the neighbouring side at `Q` runs along the `a`-edge of a `C2` tile: the angle of the target at `Q` is `β` -/
theorem corner_left_beta (S : Setup D n α β γ L ax ay) {t : ℝ} (ht : 0 < t)
    (hax : ax = t * uu n) (hay' : ay = t * hh n) :
    cornerAngle (D.target.pts (0 + 1)) (D.target.pts 0) (D.target.pts (0 + 2)) = β := by
  have hf1 := S.f1
  have hf0 := S.f0
  have hL := S.hL
  have hπ := Real.pi_pos
  have hsq := hh_sq S.f1
  have hu := uu_spec S.f1
  rw [S.tgt, show ((0 : Fin 3) + 1) = 1 by decide, show ((0 : Fin 3) + 2) = 2 by decide, Tg_pts0,
    Tg_pts1, Tg_pts2]
  have h1 : dist (mkPt ax ay) (mkPt 0 0) = t * n := by
    refine dist_eq_of_sq_eq ?_ dist_nonneg (by positivity)
    rw [dist_sq_mkPt, hax, hay']
    linear_combination t ^ 2 * hsq
  have h2 : dist (mkPt L 0) (mkPt 0 0) = L := by
    have := dist_mkPt_base 0 L hL.le
    rw [zero_add] at this
    rw [dist_comm]; exact this
  have hcos := Erdos634.AngleThreshold.cos_of_sides (mkPt L 0) (mkPt 0 0) (mkPt ax ay)
    (by rw [h2]; exact hL.ne') (by rw [h1]; positivity)
  rw [h1, h2, dist_sq_mkPt] at hcos
  rw [S.beta_eq]
  have hmem := modelBeta_mem one_pos hf1
  refine cornerAngle_eq_of_cos hmem.1.le (by linarith) ?_
  rw [hcos, cos_modelBeta one_pos hf1, baseLen_one]
  have hB : 2 * L * (t * (n:ℝ)) ≠ 0 := by positivity
  have hD : 2 * (n:ℝ) ^ 3 ≠ 0 := by positivity
  rw [div_eq_div_iff hB hD, hax, hay']
  linear_combination (2 * t * (n:ℝ) * L) * hu - (2 * (n:ℝ) ^ 3 * t ^ 2) * hsq

/-- the neighbouring side at `Q` has the direction `(1, √(4n²−1))`: the angle of the target at `Q` is `α + β` -/
theorem corner_left_ab (S : Setup D n α β γ L ax ay) {t : ℝ} (ht : 0 < t)
    (hax : ax = t) (hay' : ay = t * rt n) : D.target.localAngle (mkPt 0 0) = α + β := by
  have hf1 := S.f1
  have hf0 := S.f0
  have hL := S.hL
  have hπ := Real.pi_pos
  have hr := rt_sq (f := (n:ℝ)) hf1.le
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hαβ : α + β = Real.pi - γ := by linarith
  have h0 : D.target.localAngle (mkPt 0 0)
      = cornerAngle (mkPt L 0) (mkPt 0 0) (mkPt ax ay) := by
    rw [S.tgt]
    have h := (Tg L ax ay S.hL S.hay).localAngle_vertex 0
    rw [show ((0 : Fin 3) + 1) = 1 by decide, show ((0 : Fin 3) + 2) = 2 by decide] at h
    exact h
  rw [h0]
  have h1 : dist (mkPt ax ay) (mkPt 0 0) = t * (2 * n) := by
    refine dist_eq_of_sq_eq ?_ dist_nonneg (by positivity)
    rw [dist_sq_mkPt, hax, hay']
    linear_combination t ^ 2 * hr
  have h2 : dist (mkPt L 0) (mkPt 0 0) = L := by
    have := dist_mkPt_base 0 L hL.le
    rw [zero_add] at this
    rw [dist_comm]; exact this
  have hcos := Erdos634.AngleThreshold.cos_of_sides (mkPt L 0) (mkPt 0 0) (mkPt ax ay)
    (by rw [h2]; exact hL.ne') (by rw [h1]; positivity)
  rw [h1, h2, dist_sq_mkPt] at hcos
  refine cornerAngle_eq_of_cos (by linarith) (by linarith) ?_
  rw [hcos, hαβ, Real.cos_pi_sub, S.cos_gamma]
  have hB : 2 * L * (t * (2 * (n:ℝ))) ≠ 0 := by positivity
  have hD : 2 * (n:ℝ) ≠ 0 := by positivity
  have e : -(-1 / (2 * (n:ℝ))) = 1 / (2 * (n:ℝ)) := by ring
  rw [e, div_eq_div_iff hB hD, hax, hay']
  linear_combination (-(2 * (n:ℝ) * t ^ 2)) * hr

/-- **At a corner of angle `β` of the target every tile that contains the corner shows `β` there.** -/
theorem corner_tile_beta (S : Setup D n α β γ L ax ay) (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = β)
    {i : Fin N} (hi : D.target.pts k ∈ (D.tile i).carrier) :
    (D.tile i).localAngle (D.target.pts k) = β := by
  obtain ⟨hαβ, hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hβ2π, hγπ, hγ0, hπ0⟩ := distinct_of_angleData S.hA
  obtain ⟨i₀, j₀, hij, hang, huniq⟩ := congruentDissection_base_corner_tile_vertex D α β γ hαβ hαγ
    hαπ hα0 hβγ hβπ hβ0 hβ2π hγπ hγ0 hπ0 S.hA.hγdef S.hA.hrel S.hA.hirr S.hM.hα' S.hM.hβ' S.hM.hγ'
    k hcorner
  rw [huniq i hi]; exact hang

theorem Q_eq (S : Setup D n α β γ L ax ay) : D.target.pts 0 = mkPt 0 0 := by rw [S.tgt]; rfl
theorem B_eq (S : Setup D n α β γ L ax ay) : D.target.pts 1 = mkPt L 0 := by rw [S.tgt]; rfl

end Setup

end Erdos634.Draft.SideRun

#print axioms Erdos634.Draft.SideRun.Tg_bounds
#print axioms Erdos634.Draft.SideRun.Setup.typed_chain
#print axioms Erdos634.Draft.SideRun.Setup.corner_right_beta
#print axioms Erdos634.Draft.SideRun.Setup.corner_left_beta
#print axioms Erdos634.Draft.SideRun.Setup.corner_left_ab
#print axioms Erdos634.Draft.SideRun.Setup.corner_tile_beta
#print axioms Erdos634.Draft.SideRun.Setup.three_alpha_lt_beta
