/-
Draft/W2E1Frame.lean -- Stage 1 of the formalization of `prop:w2e1`: the target `W_2(1,f)` in coordinates and the
typed chain of tiles on its side `QB`.

* `W2 f`: `Q = (0,0)`, `B = (4f²−2, 0)`, `A = (f²−1, (f²−1)√(4f²−1))` (sides `4f²−2`, `2f(f²−1)`, `2f³`); the three
  side functionals (`W2_bounds`), the interior (`mem_interior_W2`, `openSegment_interior_W2`), the frontier.
* `Setup D n α β γ`: a congruent dissection of `W2 n` (`n ≥ 3`) with `ModelData`/`AngleData`.  Its corner angles
  (`Setup.angle_Q`: `α + β` at `Q`; `Setup.corner_B'`: `β` at `B`), `α < β` (`Setup.alpha_lt_beta`).
* `BaseTile D f i t x`: tile `i` lays the letter of the type `t` on `[x, x + len t]`, with the two distances of its
  third vertex prescribed by `t`; its angles at the two ends (`Setup.angles`), its apex (`Setup.apex`), the
  coordinates of the apex of a `c`-tile (`Setup.c1_data`, `Setup.c2_data`).
* `Setup.typed_chain`: the side `QB` is a chain of base tiles `X_1 … X_m`, each of one of the six types.
* the rules that need only vertex figures: `Setup.rule_Q`, `Setup.rule_B`, `Setup.rule_GG`.

Composite-N work; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.W2E1Tools

namespace Erdos634.Draft.W2E1

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Set

/-! ## 1. The target -/

/-- `r = √(4f² − 1)` -/
noncomputable def rt (f : ℝ) : ℝ := Real.sqrt (4 * f ^ 2 - 1)

theorem rt_sq {f : ℝ} (hf : 1 ≤ f) : rt f ^ 2 = 4 * f ^ 2 - 1 := Real.sq_sqrt (by nlinarith)

theorem rt_pos {f : ℝ} (hf : 1 ≤ f) : 0 < rt f := Real.sqrt_pos.mpr (by nlinarith)

/-- the length `4f² − 2` of the side `QB` -/
noncomputable def Lw (f : ℝ) : ℝ := 4 * f ^ 2 - 2

theorem Lw_pos {f : ℝ} (hf : 1 < f) : 0 < Lw f := by unfold Lw; nlinarith

theorem W2_det {f : ℝ} (hf : 1 < f) :
    0 < det3 0 0 (Lw f) 0 (f ^ 2 - 1) ((f ^ 2 - 1) * rt f) := by
  have hr := rt_pos hf.le
  have hb : 0 < f ^ 2 - 1 := by nlinarith
  have hL := Lw_pos hf
  have e : det3 0 0 (Lw f) 0 (f ^ 2 - 1) ((f ^ 2 - 1) * rt f) = Lw f * ((f ^ 2 - 1) * rt f) := by
    unfold det3; ring
  rw [e]; exact mul_pos hL (mul_pos hb hr)

/-- **The target `W_2(1,f)`**: `Q = (0,0)`, `B = (4f²−2, 0)`, `A = (f²−1, (f²−1)√(4f²−1))`. -/
noncomputable def W2 (f : ℝ) (hf : 1 < f) : Tri :=
  mkTri 0 0 (Lw f) 0 (f ^ 2 - 1) ((f ^ 2 - 1) * rt f) (W2_det hf).ne'

theorem W2_pts0 {f : ℝ} (hf : 1 < f) : (W2 f hf).pts 0 = mkPt 0 0 := rfl
theorem W2_pts1 {f : ℝ} (hf : 1 < f) : (W2 f hf).pts 1 = mkPt (Lw f) 0 := rfl
theorem W2_pts2 {f : ℝ} (hf : 1 < f) :
    (W2 f hf).pts 2 = mkPt (f ^ 2 - 1) ((f ^ 2 - 1) * rt f) := rfl

/-- the functional of the side `QA`, positive inside -/
noncomputable def gQA (f : ℝ) (p : Plane) : ℝ := rt f * p 0 - p 1

/-- the functional of the side `BA`, positive inside -/
noncomputable def gBA (f : ℝ) (p : Plane) : ℝ :=
  (f ^ 2 - 1) * rt f * (Lw f - p 0) - (3 * f ^ 2 - 1) * p 1

theorem gQA_mk (f x y : ℝ) : gQA f (mkPt x y) = rt f * x - y := by
  simp only [gQA, mkPt_zero, mkPt_one]

theorem gBA_mk (f x y : ℝ) :
    gBA f (mkPt x y) = (f ^ 2 - 1) * rt f * (Lw f - x) - (3 * f ^ 2 - 1) * y := by
  simp only [gBA, mkPt_zero, mkPt_one]

theorem forall_pts {T : Tri} {P : Plane → Prop} (h0 : P (T.pts 0)) (h1 : P (T.pts 1))
    (h2 : P (T.pts 2)) : ∀ k, P (T.pts k) := by
  intro k
  fin_cases k
  · exact h0
  · exact h1
  · exact h2

theorem gQA_combo (f a b : ℝ) (x y : Plane) :
    gQA f (a • x + b • y) = a * gQA f x + b * gQA f y := by
  simp only [gQA, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

theorem gBA_combo (f : ℝ) {a b : ℝ} (hab : a + b = 1) (x y : Plane) :
    gBA f (a • x + b • y) = a * gBA f x + b * gBA f y := by
  have hb1 : b = 1 - a := by linarith
  subst hb1
  simp only [gBA, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

/-- **The target lies on the inner side of its three side lines.** -/
theorem W2_bounds {f : ℝ} (hf : 1 < f) {q : Plane} (hq : q ∈ (W2 f hf).carrier) :
    0 ≤ q 1 ∧ 0 ≤ gQA f q ∧ 0 ≤ gBA f q := by
  have hr := rt_pos hf.le
  have hb : 0 < f ^ 2 - 1 := by nlinarith
  have hL := Lw_pos hf
  have hconv : Convex ℝ {q : Plane | 0 ≤ q 1 ∧ 0 ≤ gQA f q ∧ 0 ≤ gBA f q} := by
    intro x hx y hy a b ha hb' hab
    obtain ⟨h1, h2, h3⟩ := hx
    obtain ⟨k1, k2, k3⟩ := hy
    have e1 : (a • x + b • y) 1 = a * x 1 + b * y 1 := by simp
    show 0 ≤ (a • x + b • y) 1 ∧ 0 ≤ gQA f (a • x + b • y) ∧ 0 ≤ gBA f (a • x + b • y)
    rw [e1, gQA_combo, gBA_combo f hab]
    exact ⟨add_nonneg (mul_nonneg ha h1) (mul_nonneg hb' k1),
      add_nonneg (mul_nonneg ha h2) (mul_nonneg hb' k2),
      add_nonneg (mul_nonneg ha h3) (mul_nonneg hb' k3)⟩
  have hQ : 0 ≤ ((W2 f hf).pts 0) 1 ∧ 0 ≤ gQA f ((W2 f hf).pts 0) ∧ 0 ≤ gBA f ((W2 f hf).pts 0) := by
    rw [W2_pts0, gQA_mk, gBA_mk, mkPt_one]
    refine ⟨le_refl _, ?_, ?_⟩
    · have e : rt f * 0 - 0 = 0 := by ring
      exact e.symm.le
    · have e : (f ^ 2 - 1) * rt f * (Lw f - 0) - (3 * f ^ 2 - 1) * 0 = (f ^ 2 - 1) * rt f * Lw f := by
        ring
      rw [e]; exact (mul_pos (mul_pos hb hr) hL).le
  have hB : 0 ≤ ((W2 f hf).pts 1) 1 ∧ 0 ≤ gQA f ((W2 f hf).pts 1) ∧ 0 ≤ gBA f ((W2 f hf).pts 1) := by
    rw [W2_pts1, gQA_mk, gBA_mk, mkPt_one]
    refine ⟨le_refl _, ?_, ?_⟩
    · have e : rt f * Lw f - 0 = rt f * Lw f := by ring
      rw [e]; exact (mul_pos hr hL).le
    · have e : (f ^ 2 - 1) * rt f * (Lw f - Lw f) - (3 * f ^ 2 - 1) * 0 = 0 := by ring
      exact e.symm.le
  have hA : 0 ≤ ((W2 f hf).pts 2) 1 ∧ 0 ≤ gQA f ((W2 f hf).pts 2) ∧ 0 ≤ gBA f ((W2 f hf).pts 2) := by
    rw [W2_pts2, gQA_mk, gBA_mk, mkPt_one]
    refine ⟨(mul_pos hb hr).le, ?_, ?_⟩
    · have e : rt f * (f ^ 2 - 1) - (f ^ 2 - 1) * rt f = 0 := by ring
      exact e.symm.le
    · have e : (f ^ 2 - 1) * rt f * (Lw f - (f ^ 2 - 1)) - (3 * f ^ 2 - 1) * ((f ^ 2 - 1) * rt f)
          = 0 := by unfold Lw; ring
      exact e.symm.le
  have hsub : (W2 f hf).carrier ⊆ {q : Plane | 0 ≤ q 1 ∧ 0 ≤ gQA f q ∧ 0 ≤ gBA f q} := by
    refine convexHull_min ?_ hconv
    rintro _ ⟨k, rfl⟩
    exact forall_pts (T := W2 f hf) (P := fun q => 0 ≤ q 1 ∧ 0 ≤ gQA f q ∧ 0 ≤ gBA f q) hQ hB hA k
  exact hsub hq

/-- **Strict signs put a point in the interior of the target.** -/
theorem mem_interior_W2 {f : ℝ} (hf : 1 < f) {q : Plane} (h1 : 0 < q 1) (h2 : 0 < gQA f q)
    (h3 : 0 < gBA f q) : q ∈ interior (W2 f hf).carrier := by
  have hb : 0 < f ^ 2 - 1 := by nlinarith
  have hL := Lw_pos hf
  have e0 : det3 (q 0) (q 1) (Lw f) 0 (f ^ 2 - 1) ((f ^ 2 - 1) * rt f) = gBA f q := by
    unfold det3 gBA Lw; ring
  have e1 : det3 0 0 (q 0) (q 1) (f ^ 2 - 1) ((f ^ 2 - 1) * rt f) = (f ^ 2 - 1) * gQA f q := by
    unfold det3 gQA; ring
  have e2 : det3 0 0 (Lw f) 0 (q 0) (q 1) = Lw f * q 1 := by unfold det3; ring
  have h := Erdos634.ChordChartPlanar.mem_interior_carrier_of_dets_pos (W2_det hf) (a := q 0)
    (b := q 1) (by rw [e0]; exact h3) (by rw [e1]; exact mul_pos hb h2)
    (by rw [e2]; exact mul_pos hL h1)
  rw [Erdos634.ChordChartPlanar.mkPt_coords] at h
  exact h

theorem pos_combo {a b x y : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : 0 < x ∨ 0 < y) : 0 < a * x + b * y := by
  rcases h with h | h
  · have h1 := mul_pos ha h
    have h2 := mul_nonneg hb.le hy
    linarith
  · have h1 := mul_pos hb h
    have h2 := mul_nonneg ha.le hx
    linarith

/-- **An open segment between two points of the target that share no side line is interior to the target.** -/
theorem openSegment_interior_W2 {f : ℝ} (hf : 1 < f) {P Q : Plane} (hP : P ∈ (W2 f hf).carrier)
    (hQ : Q ∈ (W2 f hf).carrier) (h1 : 0 < P 1 ∨ 0 < Q 1) (h2 : 0 < gQA f P ∨ 0 < gQA f Q)
    (h3 : 0 < gBA f P ∨ 0 < gBA f Q) : openSegment ℝ P Q ⊆ interior (W2 f hf).carrier := by
  obtain ⟨p1, p2, p3⟩ := W2_bounds hf hP
  obtain ⟨q1, q2, q3⟩ := W2_bounds hf hQ
  rintro y ⟨a, b, ha, hb, hab, rfl⟩
  have e1 : (a • P + b • Q) 1 = a * P 1 + b * Q 1 := by simp
  refine mem_interior_W2 hf ?_ ?_ ?_
  · rw [e1]; exact pos_combo ha hb p1 q1 h1
  · rw [gQA_combo]; exact pos_combo ha hb p2 q2 h2
  · rw [gBA_combo f hab]; exact pos_combo ha hb p3 q3 h3

theorem base_mem_frontier {f : ℝ} (hf : 1 < f) {v : ℝ} (h0 : 0 ≤ v) (hL : v ≤ Lw f) :
    mkPt v 0 ∈ frontier (W2 f hf).carrier := by
  apply Erdos634.SideWall.edge_subset_frontier (W2 f hf) 0
  show mkPt v 0 ∈ segment ℝ (mkPt 0 0) (mkPt (Lw f) 0)
  exact (mem_base_segment_iff (Lw_pos hf) _).mpr
    ⟨mkPt_one _ _, by rw [mkPt_zero]; exact h0, by rw [mkPt_zero]; exact hL⟩

theorem BA_mem_frontier {f : ℝ} (hf : 1 < f) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    mkPt (Lw f - s * (3 * f ^ 2 - 1)) (s * ((f ^ 2 - 1) * rt f)) ∈ frontier (W2 f hf).carrier := by
  apply Erdos634.SideWall.edge_subset_frontier (W2 f hf) 1
  show mkPt (Lw f - s * (3 * f ^ 2 - 1)) (s * ((f ^ 2 - 1) * rt f))
    ∈ segment ℝ (mkPt (Lw f) 0) (mkPt (f ^ 2 - 1) ((f ^ 2 - 1) * rt f))
  refine ⟨1 - s, s, by linarith, hs0, by ring, ?_⟩
  apply plane_ext <;>
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mkPt_zero, mkPt_one] <;>
    first | (unfold Lw; ring) | ring

theorem not_vertex_W2 {f : ℝ} (hf : 1 < f) {p : Plane} (h0 : p ≠ mkPt 0 0)
    (h1 : p ≠ mkPt (Lw f) 0) (h2 : p ≠ mkPt (f ^ 2 - 1) ((f ^ 2 - 1) * rt f)) :
    p ∉ Set.range (W2 f hf).pts := by
  rintro ⟨k, hk⟩
  exact forall_pts (T := W2 f hf) (P := fun q => q = p → False) (fun h => h0 h.symm)
    (fun h => h1 h.symm) (fun h => h2 h.symm) k hk

theorem dist_QB {f : ℝ} (hf : 1 < f) : dist (mkPt 0 0) (mkPt (Lw f) 0) = Lw f := by
  have := dist_mkPt_base 0 (Lw f) (Lw_pos hf).le
  rwa [zero_add] at this

theorem dist_QA {f : ℝ} (hf : 1 < f) :
    dist (mkPt 0 0) (mkPt (f ^ 2 - 1) ((f ^ 2 - 1) * rt f)) = 2 * f * (f ^ 2 - 1) := by
  have hb : 0 < f ^ 2 - 1 := by nlinarith
  have h := rt_sq (f := f) hf.le
  refine dist_eq_of_sq_eq ?_ dist_nonneg (mul_nonneg (by linarith) hb.le)
  rw [dist_sq_mkPt]
  linear_combination (f ^ 2 - 1) ^ 2 * h

theorem dist_BA {f : ℝ} (hf : 1 < f) :
    dist (mkPt (Lw f) 0) (mkPt (f ^ 2 - 1) ((f ^ 2 - 1) * rt f)) = 2 * f ^ 3 := by
  have hf0 : (0:ℝ) < f := by linarith
  have h := rt_sq (f := f) hf.le
  refine dist_eq_of_sq_eq ?_ dist_nonneg (by positivity)
  rw [dist_sq_mkPt]
  unfold Lw
  linear_combination (f ^ 2 - 1) ^ 2 * h

/-! ## 2. Coordinates of the apex of a `c`-tile -/

/-- the abscissa of the apex of a `c`-tile, from its `β`-end -/
noncomputable def uu (f : ℝ) : ℝ := (3 * f ^ 2 - 1) / (2 * f ^ 2)

/-- the height of the apex of a `c`-tile -/
noncomputable def hh (f : ℝ) : ℝ := (f ^ 2 - 1) * rt f / (2 * f ^ 2)

theorem cancel2 {f X : ℝ} (hf : 1 < f) (h : 2 * f ^ 2 * X = 0) : X = 0 := by
  have h0 : (0:ℝ) < 2 * f ^ 2 := by nlinarith
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd h' h0.ne'
  · exact h'

theorem uu_spec {f : ℝ} (hf : 1 < f) : 2 * f ^ 2 * uu f = 3 * f ^ 2 - 1 := by
  have h0 : (0:ℝ) < 2 * f ^ 2 := by nlinarith
  have := div_mul_cancel₀ (3 * f ^ 2 - 1) h0.ne'
  unfold uu; linear_combination this

theorem hh_spec {f : ℝ} (hf : 1 < f) : 2 * f ^ 2 * hh f = (f ^ 2 - 1) * rt f := by
  have h0 : (0:ℝ) < 2 * f ^ 2 := by nlinarith
  have := div_mul_cancel₀ ((f ^ 2 - 1) * rt f) h0.ne'
  unfold hh; linear_combination this

theorem hh_pos {f : ℝ} (hf : 1 < f) : 0 < hh f := by
  have hb : 0 < f ^ 2 - 1 := by nlinarith
  unfold hh; exact div_pos (mul_pos hb (rt_pos hf.le)) (by nlinarith)

theorem uu_pos {f : ℝ} (hf : 1 < f) : 0 < uu f := by
  unfold uu; exact div_pos (by nlinarith) (by nlinarith)

theorem hh_sq {f : ℝ} (hf : 1 < f) : hh f ^ 2 = f ^ 2 - uu f ^ 2 := by
  have hu := uu_spec hf
  have hh' := hh_spec hf
  have hr := rt_sq (f := f) hf.le
  have hf0 : (0:ℝ) < f := by linarith
  have h0 : (0:ℝ) < (2 * f ^ 2) ^ 2 := by positivity
  have key : (2 * f ^ 2) ^ 2 * (hh f ^ 2 - (f ^ 2 - uu f ^ 2)) = 0 := by
    have e : (2 * f ^ 2) ^ 2 * (hh f ^ 2 - (f ^ 2 - uu f ^ 2))
        = (2 * f ^ 2 * hh f) ^ 2 - (2 * f ^ 2) ^ 2 * f ^ 2 + (2 * f ^ 2 * uu f) ^ 2 := by ring
    rw [e, hu, hh']
    linear_combination (f ^ 2 - 1) ^ 2 * hr
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h h0.ne'
  · linarith

theorem hh_sq' {f : ℝ} (hf : 1 < f) : hh f ^ 2 = (f ^ 2 - 1) ^ 2 - (f ^ 2 - uu f) ^ 2 := by
  have h1 := hh_sq hf
  have hu := uu_spec hf
  linear_combination h1 - hu

/-- `r·u − h = r` -/
theorem ruh {f : ℝ} (hf : 1 < f) : rt f * uu f - hh f = rt f := by
  have hu := uu_spec hf
  have hh' := hh_spec hf
  have := cancel2 hf (X := rt f * uu f - hh f - rt f) (by linear_combination rt f * hu - hh')
  linarith

/-- `2h < b·r` -/
theorem two_hh_lt {f : ℝ} (hf : 1 < f) : 2 * hh f < (f ^ 2 - 1) * rt f := by
  have hh' := hh_spec hf
  have hb : 0 < f ^ 2 - 1 := by nlinarith
  have hr := rt_pos hf.le
  have hf2 : (0:ℝ) < f ^ 2 := by nlinarith
  have e : f ^ 2 * ((f ^ 2 - 1) * rt f - 2 * hh f) = (f ^ 2 - 1) * rt f * (f ^ 2 - 1) := by
    linear_combination (-1 : ℝ) * hh'
  have hpos : 0 < (f ^ 2 - 1) * rt f * (f ^ 2 - 1) := mul_pos (mul_pos hb hr) hb
  by_contra hneg
  push Not at hneg
  nlinarith [mul_nonneg hf2.le (sub_nonneg.mpr hneg)]

/-- `b·r·u = (3f² − 1)·h` -/
theorem bru {f : ℝ} (hf : 1 < f) : (f ^ 2 - 1) * rt f * uu f - (3 * f ^ 2 - 1) * hh f = 0 := by
  have hu := uu_spec hf
  have hh' := hh_spec hf
  exact cancel2 hf (by linear_combination (f ^ 2 - 1) * rt f * hu - (3 * f ^ 2 - 1) * hh')

/-! ## 3. The standing hypotheses -/

/-- **The standing hypotheses**: a congruent dissection of `W_2(1,n)` in normal position, `n ≥ 3`, with the tile
`(n, n²−1, n²)` and its angles. -/
structure Setup {N : ℕ} (D : CongruentDissection N) (n : ℕ) (α β γ : ℝ) : Prop where
  hn3 : 3 ≤ n
  hM : ModelData D (n:ℝ) α β γ
  hA : AngleData α β γ
  htgt : ∀ hf : (1:ℝ) < n, D.target = W2 (n:ℝ) hf

namespace Setup

variable {N : ℕ} {D : CongruentDissection N} {n : ℕ} {α β γ : ℝ}

theorem f3 (S : Setup D n α β γ) : (3:ℝ) ≤ n := by exact_mod_cast S.hn3
theorem f2 (S : Setup D n α β γ) : (2:ℝ) ≤ n := by have := S.f3; linarith
theorem f1 (S : Setup D n α β γ) : (1:ℝ) < n := by have := S.f3; linarith
theorem f0 (S : Setup D n α β γ) : (0:ℝ) < n := by have := S.f3; linarith
theorem b_pos (S : Setup D n α β γ) : (0:ℝ) < (n:ℝ) ^ 2 - 1 := by have := S.f3; nlinarith
theorem tgt (S : Setup D n α β γ) : D.target = W2 (n:ℝ) S.f1 := S.htgt S.f1

theorem mem (S : Setup D n α β γ) {p : Plane} (hp : p ∈ D.target.carrier) :
    0 ≤ p 1 ∧ 0 ≤ gQA n p ∧ 0 ≤ gBA n p := by
  rw [S.tgt] at hp; exact W2_bounds S.f1 hp

theorem pts_mem (S : Setup D n α β γ) (i : Fin N) (k : Fin 3) :
    0 ≤ ((D.tile i).pts k) 1 ∧ 0 ≤ gQA n ((D.tile i).pts k) ∧ 0 ≤ gBA n ((D.tile i).pts k) :=
  S.mem (pts_mem_target D.toDissection i k)

theorem interior_seg (S : Setup D n α β γ) {P Q : Plane} (hP : P ∈ D.target.carrier)
    (hQ : Q ∈ D.target.carrier) (h1 : 0 < P 1 ∨ 0 < Q 1) (h2 : 0 < gQA n P ∨ 0 < gQA n Q)
    (h3 : 0 < gBA n P ∨ 0 < gBA n Q) : openSegment ℝ P Q ⊆ interior D.target.carrier := by
  rw [S.tgt] at hP hQ ⊢; exact openSegment_interior_W2 S.f1 hP hQ h1 h2 h3

/-- a line through a base point leaves the target below the base -/
theorem below_out (S : Setup D n α β γ) {V G : Plane} (hV : V 1 = 0) (hG : 0 < G 1) :
    ∀ s : ℝ, 0 < s → V + s • (V - G) ∉ D.target.carrier := by
  intro s hs hmem
  have h := (S.mem hmem).1
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, hV] at h
  nlinarith [mul_pos hs hG]

/-- a line through a point of `BA` leaves the target beyond it -/
theorem BA_out (S : Setup D n α β γ) {V G : Plane} (hG : gBA n G = 0) (hV : 0 < gBA n V) :
    ∀ s : ℝ, 0 < s → G + s • (G - V) ∉ D.target.carrier := by
  intro s hs hmem
  have h := (S.mem hmem).2.2
  have e : G + s • (G - V) = (1 + s) • G + (-s) • V := by
    apply plane_ext <;>
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] <;> ring
  rw [e, gBA_combo (n:ℝ) (by ring), hG] at h
  nlinarith [mul_pos hs hV]

theorem angle_base (S : Setup D n α β γ) {x : ℝ} (hx0 : 0 < x) (hxL : x < Lw n) :
    D.target.localAngle (mkPt x 0) = Real.pi := by
  rw [S.tgt]
  refine Tri.localAngle_frontier _ (base_mem_frontier S.f1 hx0.le hxL.le)
    (not_vertex_W2 S.f1 ?_ ?_ ?_)
  · exact mkPt_ne_of_fst hx0.ne'
  · exact mkPt_ne_of_fst hxL.ne
  · exact mkPt_ne_of_snd (mul_pos S.b_pos (rt_pos S.f1.le)).ne

theorem base_frontier (S : Setup D n α β γ) {x : ℝ} (hx0 : 0 < x) (hxL : x < Lw n) :
    mkPt x 0 ∈ frontier D.target.carrier ∧ mkPt x 0 ∉ Set.range D.target.pts := by
  rw [S.tgt]
  refine ⟨base_mem_frontier S.f1 hx0.le hxL.le, not_vertex_W2 S.f1 ?_ ?_ ?_⟩
  · exact mkPt_ne_of_fst hx0.ne'
  · exact mkPt_ne_of_fst hxL.ne
  · exact mkPt_ne_of_snd (mul_pos S.b_pos (rt_pos S.f1.le)).ne

/-- at a point of `BA` other than `B` and `A` the target shows a straight angle -/
theorem angle_BA (S : Setup D n α β γ) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    D.target.localAngle (mkPt (Lw n - s * (3 * (n:ℝ) ^ 2 - 1)) (s * (((n:ℝ) ^ 2 - 1) * rt n)))
      = Real.pi := by
  rw [S.tgt]
  have hbr := mul_pos S.b_pos (rt_pos S.f1.le)
  refine Tri.localAngle_frontier _ (BA_mem_frontier S.f1 hs0.le hs1.le)
    (not_vertex_W2 S.f1 ?_ ?_ ?_)
  · exact mkPt_ne_of_snd (mul_pos hs0 hbr).ne'
  · exact mkPt_ne_of_snd (mul_pos hs0 hbr).ne'
  · refine mkPt_ne_of_snd ?_
    intro h
    have := mul_pos (sub_pos.mpr hs1) hbr
    linarith

theorem beta_eq (S : Setup D n α β γ) : β = modelBeta 1 n := beta_eq_modelBeta D S.f2 S.hM

theorem alpha_lt_beta (S : Setup D n α β γ) : α < β := by
  have h1 := S.beta_eq
  have h2 := modelAlpha_lt_modelBeta S.f2
  have h3 := S.hA.hrel
  unfold modelAlpha at h2
  rw [← h1] at h2
  linarith

theorem cos_gamma (S : Setup D n α β γ) : Real.cos γ = -1 / (2 * (n:ℝ)) := by
  obtain ⟨m01, m12, m20⟩ := model_dists D S.hM
  have h := Erdos634.AngleThreshold.cos_gamma_closed (D.model.pts 1) (D.model.pts 2)
    (D.model.pts 0) (n:ℝ) S.f1 m12 (by rw [dist_comm]; exact m20) (by rw [dist_comm]; exact m01)
  have hc : cornerAngle (D.model.pts 1) (D.model.pts 2) (D.model.pts 0) = γ := by
    rw [← S.hM.hγ']; unfold cornerAngle; exact EuclideanGeometry.angle_comm _ _ _
  rw [hc] at h; exact h

/-- the angle of the target at `Q` is `α + β` -/
theorem corner_Q (S : Setup D n α β γ) :
    cornerAngle (mkPt (Lw n) 0) (mkPt 0 0) (mkPt ((n:ℝ) ^ 2 - 1) (((n:ℝ) ^ 2 - 1) * rt n))
      = α + β := by
  have hf1 := S.f1
  have hf0 := S.f0
  have hb := S.b_pos
  have hL := Lw_pos hf1
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hπ := Real.pi_pos
  have hαβ : α + β = Real.pi - γ := by linarith
  have h1 : dist (mkPt (Lw n) 0) (mkPt 0 0) = Lw n := by rw [dist_comm]; exact dist_QB hf1
  have h2 : dist (mkPt ((n:ℝ) ^ 2 - 1) (((n:ℝ) ^ 2 - 1) * rt n)) (mkPt 0 0)
      = 2 * n * ((n:ℝ) ^ 2 - 1) := by rw [dist_comm]; exact dist_QA hf1
  have h3 := dist_BA hf1
  have hcos := Erdos634.AngleThreshold.cos_of_sides (mkPt (Lw n) 0) (mkPt 0 0)
    (mkPt ((n:ℝ) ^ 2 - 1) (((n:ℝ) ^ 2 - 1) * rt n))
    (by rw [h1]; exact hL.ne') (by rw [h2]; exact (mul_pos (mul_pos two_pos hf0) hb).ne')
  rw [h1, h2, h3] at hcos
  refine cornerAngle_eq_of_cos (by linarith) (by linarith) ?_
  rw [hcos, hαβ, Real.cos_pi_sub, S.cos_gamma]
  have hB : 2 * Lw n * (2 * (n:ℝ) * ((n:ℝ) ^ 2 - 1)) ≠ 0 :=
    (mul_pos (mul_pos two_pos hL) (mul_pos (mul_pos two_pos hf0) hb)).ne'
  have hD : 2 * (n:ℝ) ≠ 0 := (mul_pos two_pos hf0).ne'
  have e : -(-1 / (2 * (n:ℝ))) = 1 / (2 * (n:ℝ)) := by ring
  rw [e, div_eq_div_iff hB hD]
  unfold Lw
  ring

/-- the angle of the target at `B` is `β` -/
theorem corner_B (S : Setup D n α β γ) :
    cornerAngle (mkPt ((n:ℝ) ^ 2 - 1) (((n:ℝ) ^ 2 - 1) * rt n)) (mkPt (Lw n) 0) (mkPt 0 0) = β := by
  have hf1 := S.f1
  have hf0 := S.f0
  have hb := S.b_pos
  have hL := Lw_pos hf1
  have hπ := Real.pi_pos
  have h1 : dist (mkPt ((n:ℝ) ^ 2 - 1) (((n:ℝ) ^ 2 - 1) * rt n)) (mkPt (Lw n) 0) = 2 * (n:ℝ) ^ 3 := by
    rw [dist_comm]; exact dist_BA hf1
  have h2 := dist_QB hf1
  have h3 : dist (mkPt ((n:ℝ) ^ 2 - 1) (((n:ℝ) ^ 2 - 1) * rt n)) (mkPt 0 0)
      = 2 * n * ((n:ℝ) ^ 2 - 1) := by rw [dist_comm]; exact dist_QA hf1
  have hcos := Erdos634.AngleThreshold.cos_of_sides
    (mkPt ((n:ℝ) ^ 2 - 1) (((n:ℝ) ^ 2 - 1) * rt n)) (mkPt (Lw n) 0) (mkPt 0 0)
    (by rw [h1]; positivity) (by rw [h2]; exact hL.ne')
  rw [h1, h2, h3] at hcos
  rw [S.beta_eq]
  have hmem := modelBeta_mem one_pos hf1
  refine cornerAngle_eq_of_cos hmem.1.le (by linarith) ?_
  rw [hcos, cos_modelBeta one_pos hf1, baseLen_one]
  have hB : 2 * (2 * (n:ℝ) ^ 3) * Lw n ≠ 0 :=
    (mul_pos (mul_pos two_pos (mul_pos two_pos (pow_pos hf0 3))) hL).ne'
  have hD : 2 * (n:ℝ) ^ 3 ≠ 0 := (mul_pos two_pos (pow_pos hf0 3)).ne'
  rw [div_eq_div_iff hB hD]
  unfold Lw
  ring

theorem angle_Q (S : Setup D n α β γ) : D.target.localAngle (mkPt 0 0) = α + β := by
  rw [S.tgt]
  have h := (W2 (n:ℝ) S.f1).localAngle_vertex 0
  rw [show ((0 : Fin 3) + 1) = 1 by decide, show ((0 : Fin 3) + 2) = 2 by decide] at h
  exact h.trans S.corner_Q

theorem corner_B' (S : Setup D n α β γ) :
    cornerAngle (D.target.pts (1 + 1)) (D.target.pts 1) (D.target.pts (1 + 2)) = β := by
  rw [S.tgt, show ((1 : Fin 3) + 1) = 2 by decide, show ((1 : Fin 3) + 2) = 0 by decide]
  exact S.corner_B

theorem B_eq (S : Setup D n α β γ) : D.target.pts 1 = mkPt (Lw n) 0 := by rw [S.tgt]; rfl

end Setup

/-! ## 4. Base tiles -/

namespace Ty

/-- the length of the letter, as a real -/
noncomputable def lenR (f : ℝ) : Ty → ℝ
  | A1 => f | A2 => f | B1 => f ^ 2 - 1 | B2 => f ^ 2 - 1 | C1 => f ^ 2 | C2 => f ^ 2

/-- the side from the apex to the left end -/
noncomputable def sL (f : ℝ) : Ty → ℝ
  | A1 => f ^ 2 | A2 => f ^ 2 - 1 | B1 => f ^ 2 | B2 => f | C1 => f ^ 2 - 1 | C2 => f

/-- the side from the apex to the right end -/
noncomputable def sR (f : ℝ) : Ty → ℝ
  | A1 => f ^ 2 - 1 | A2 => f ^ 2 | B1 => f | B2 => f ^ 2 | C1 => f | C2 => f ^ 2 - 1

/-- the angle at the left end -/
noncomputable def aL (α β γ : ℝ) : Ty → ℝ
  | A1 => β | A2 => γ | B1 => α | B2 => γ | C1 => α | C2 => β

/-- the angle at the right end -/
noncomputable def aR (α β γ : ℝ) : Ty → ℝ
  | A1 => γ | A2 => β | B1 => γ | B2 => α | C1 => β | C2 => α

theorem lenR_pos {f : ℝ} (hf : 2 ≤ f) (t : Ty) : 0 < t.lenR f := by
  cases t <;> simp only [lenR] <;> nlinarith

theorem len_cast (n : ℕ) (hn : 1 ≤ n) (t : Ty) : ((t.len n : ℕ) : ℝ) = t.lenR n := by
  have h1 : 1 ≤ n * n := Nat.mul_pos hn hn
  have hB : ((n * n - 1 : ℕ) : ℝ) = (n:ℝ) ^ 2 - 1 := by
    rw [Nat.cast_sub h1]; push_cast; ring
  have hC : ((n * n : ℕ) : ℝ) = (n:ℝ) ^ 2 := by push_cast; ring
  cases t
  · rfl
  · rfl
  · exact hB
  · exact hB
  · exact hC
  · exact hC

theorem aR_of_gR (α β γ : ℝ) {t : Ty} (h : t.gR) : t.aR α β γ = γ := by
  rcases h with rfl | rfl <;> rfl

theorem aL_of_gL (α β γ : ℝ) {t : Ty} (h : t.gL) : t.aL α β γ = γ := by
  rcases h with rfl | rfl <;> rfl

theorem aR_eq_beta {α β γ : ℝ} (h1 : α ≠ β) (h2 : β ≠ γ) (t : Ty) (ht : t.aR α β γ = β) :
    t = A2 ∨ t = C1 := by
  cases t
  · exact absurd ht.symm h2
  · exact Or.inl rfl
  · exact absurd ht.symm h2
  · exact absurd ht h1
  · exact Or.inr rfl
  · exact absurd ht h1

theorem aL_eq_beta {α β γ : ℝ} (h1 : α ≠ β) (h2 : β ≠ γ) (t : Ty) (ht : t.aL α β γ = β) :
    t = A1 ∨ t = C2 := by
  cases t
  · exact Or.inl rfl
  · exact absurd ht.symm h2
  · exact absurd ht h1
  · exact absurd ht.symm h2
  · exact absurd ht h1
  · exact Or.inr rfl

end Ty

/-- **Tile `i` is a base tile of type `t` at `x`**: it has the vertices `(x, 0)` and `(x + len t, 0)`, and its
third vertex is at the distances prescribed by the type from these two. -/
def BaseTile {N : ℕ} (D : CongruentDissection N) (f : ℝ) (i : Fin N) (t : Ty) (x : ℝ) : Prop :=
  ∃ k m j : Fin 3, k ≠ m ∧ k ≠ j ∧ m ≠ j ∧ (D.tile i).pts k = mkPt x 0 ∧
    (D.tile i).pts m = mkPt (x + t.lenR f) 0 ∧
    dist ((D.tile i).pts j) ((D.tile i).pts k) = t.sL f ∧
    dist ((D.tile i).pts j) ((D.tile i).pts m) = t.sR f

theorem sq_of_dist {p : Plane} {a d : ℝ} (h : dist p (mkPt a 0) = d) :
    (p 0 - a) ^ 2 + (p 1) ^ 2 = d ^ 2 := by
  have h' := dist_sq_pt_mkPt p a 0
  rw [h] at h'
  linear_combination (-1 : ℝ) * h'

namespace Setup

variable {N : ℕ} {D : CongruentDissection N} {n : ℕ} {α β γ : ℝ}

/-- **The angles of a base tile at its two ends.** -/
theorem angles (S : Setup D n α β γ) {i : Fin N} {t : Ty} {x : ℝ} (h : BaseTile D n i t x) :
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

/-- **The apex of a base tile**: above the side, at the two prescribed distances, with the equation of its
abscissa; it is the only vertex of the tile off the side. -/
theorem apex (S : Setup D n α β γ) {i : Fin N} {t : Ty} {x : ℝ} (h : BaseTile D n i t x) :
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
theorem c2_data (S : Setup D n α β γ) {i : Fin N} {x : ℝ} (h : BaseTile D n i Ty.C2 x) :
    ∃ kb ka kg : Fin 3, kb ≠ ka ∧ kb ≠ kg ∧ ka ≠ kg ∧ (D.tile i).pts kb = mkPt x 0 ∧
      (D.tile i).pts ka = mkPt (x + (n:ℝ) ^ 2) 0 ∧ (D.tile i).pts kg = mkPt (x + uu n) (hh n) ∧
      dist (mkPt (x + uu n) (hh n)) (mkPt x 0) = n ∧
      dist (mkPt (x + (n:ℝ) ^ 2) 0) (mkPt (x + uu n) (hh n)) = (n:ℝ) ^ 2 - 1 := by
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
  refine ⟨k, m, j, hkm, hkj, hmj, hk, hm', hGeq, ?_, ?_⟩
  · rw [← hGeq]; exact hsL'
  · rw [dist_comm, ← hGeq]; exact hsR'

/-- **A `C1` tile in coordinates**: `α` at `(x, 0)`, `β` at `(x + c, 0)`, apex `(x + c − u, h)`. -/
theorem c1_data (S : Setup D n α β γ) {i : Fin N} {x : ℝ} (h : BaseTile D n i Ty.C1 x) :
    ∃ ka kb kg : Fin 3, ka ≠ kb ∧ ka ≠ kg ∧ kb ≠ kg ∧ (D.tile i).pts ka = mkPt x 0 ∧
      (D.tile i).pts kb = mkPt (x + (n:ℝ) ^ 2) 0 ∧
      (D.tile i).pts kg = mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n) ∧
      dist (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) (mkPt (x + (n:ℝ) ^ 2) 0) = n ∧
      dist (mkPt x 0) (mkPt (x + (n:ℝ) ^ 2 - uu n) (hh n)) = (n:ℝ) ^ 2 - 1 := by
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
  refine ⟨k, m, j, hkm, hkj, hmj, hk, hm', hGeq, ?_, ?_⟩
  · rw [← hGeq]; exact hsR'
  · rw [dist_comm, ← hGeq]; exact hsL'

/-- two base tiles at different places are different tiles -/
theorem baseTile_ne (S : Setup D n α β γ) {i j : Fin N} {t t' : Ty} {x x' : ℝ}
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

end Setup

/-! ## 5. The chain of base tiles -/

/-- **The base chain, for a target with the side `[(0,0), (L,0)]` in the upper half-plane.**  This is
`E1BaseWord.base_chain` with the three facts about the target as hypotheses. -/
theorem base_chain_gen {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hM : ModelData D f α β γ)
    {L : ℝ} (hL : 0 < L) (hup : ∀ y ∈ D.target.carrier, 0 ≤ y 1)
    (hbase : segment ℝ (mkPt 0 0) (mkPt L 0) ⊆ frontier D.target.carrier)
    (hface : ∀ y ∈ D.target.carrier, y 1 = 0 → 0 ≤ y 0 ∧ y 0 ≤ L) :
    ∃ (n : ℕ) (X : ℕ → ℝ), 0 < n ∧ X 0 = 0 ∧ X n = L ∧
      (∀ m, m < n → X (m + 1) - X m = f ∨ X (m + 1) - X m = f ^ 2 - 1 ∨
        X (m + 1) - X m = f ^ 2) ∧
      (∀ m, m < n → ∃ (i : Fin N) (k k' : Fin 3), k ≠ k' ∧
        (D.tile i).pts k = mkPt (X m) 0 ∧ (D.tile i).pts k' = mkPt (X (m + 1)) 0) := by
  classical
  have hN : 0 < N := D.toDissection.pos
  have hwall : ∀ y ∈ D.target.carrier, gY y ≤ 0 := by
    intro y hy
    have := hup y hy
    rw [gY_apply]; linarith
  have hab : (mkPt 0 0 : Plane) ≠ mkPt L 0 := mkPt_ne_of_fst hL.ne
  have hdirab : xco (mkPt 0 0) ≤ xco (mkPt L 0) := by
    simp only [xco_apply, mkPt_zero]; exact hL.le
  have hline : ∀ y ∈ segment ℝ (mkPt 0 0) (mkPt L 0), gY y = 0 := by
    intro y hy
    obtain ⟨h1, -, -⟩ := (mem_base_segment_iff hL y).mp hy
    rw [gY_apply, h1, neg_zero]
  have hface' : ∀ y ∈ D.target.carrier, gY y = 0 → y ∈ segment ℝ (mkPt 0 0) (mkPt L 0) := by
    intro y hy hgy
    rw [gY_apply, neg_eq_zero] at hgy
    obtain ⟨h0, h1⟩ := hface y hy hgy
    exact (mem_base_segment_iff hL y).mpr ⟨hgy, h0, h1⟩
  have hthird := hthird_general D.toDissection gY 0 (by rw [gY_linear]; exact negY_ne_zero) hwall
  obtain ⟨E, n, hneq, hn0, hwest, heast, hjunc, hmem, -, -, -, -, -⟩ :=
    chain_endpoints hN D.toDissection gY 0 xco hker_base hwall (mkPt 0 0) (mkPt L 0)
      hab hdirab hbase hline hface' hthird
  have hW0 : ∀ m, m < n → (edgeWest D.toDissection xco (E m)) 1 = 0 ∧
      (edgeEast D.toDissection xco (E m)) 1 = 0 := by
    intro m hm
    obtain ⟨hw1, hw2⟩ := (mem_wallList D.toDissection gY 0 (E m)).mp (hmem m hm)
    rw [gY_apply, neg_eq_zero] at hw1 hw2
    rcases edgeWest_edgeEast_pts D.toDissection xco (E m) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact ⟨hw1, hw2⟩
    · rw [h1, h2]; exact ⟨hw2, hw1⟩
  have hWeq : ∀ m, m < n → edgeWest D.toDissection xco (E m)
      = mkPt (edgePos D.toDissection xco (E m)) 0 := by
    intro m hm
    rw [← dir_edgeWest, xco_apply]
    exact eq_mkPt_of_y_zero (hW0 m hm).1
  have hEeq : ∀ m, m < n → edgeEast D.toDissection xco (E m)
      = mkPt (edgeEnd D.toDissection xco (E m)) 0 := by
    intro m hm
    rw [← dir_edgeEast, xco_apply]
    exact eq_mkPt_of_y_zero (hW0 m hm).2
  have hlen : ∀ m, m < n → edgeEnd D.toDissection xco (E m) - edgePos D.toDissection xco (E m)
      = dist ((D.tile (E m).1).pts (E m).2) ((D.tile (E m).1).pts ((E m).2 + 1)) := by
    intro m hm
    obtain ⟨hw1, hw2⟩ := (mem_wallList D.toDissection gY 0 (E m)).mp (hmem m hm)
    rw [hiso_base _ _ hw1 hw2]
    show _ = |xco ((D.tile (E m).1).pts (E m).2) - xco ((D.tile (E m).1).pts ((E m).2 + 1))|
    unfold edgeEnd edgePos
    rcases le_total (xco ((D.tile (E m).1).pts (E m).2))
        (xco ((D.tile (E m).1).pts ((E m).2 + 1))) with h | h
    · rw [min_eq_left h, max_eq_right h, abs_of_nonpos (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left h, abs_of_nonneg (by linarith)]
  set X : ℕ → ℝ := fun m => if m < n then edgePos D.toDissection xco (E m) else L with hXdef
  have hXlt : ∀ m, m < n → X m = edgePos D.toDissection xco (E m) := fun m hm => if_pos hm
  have hXsucc : ∀ m, m < n → X (m + 1) = edgeEnd D.toDissection xco (E m) := by
    intro m hm
    rcases Nat.lt_or_ge (m + 1) n with h | h
    · rw [hXlt _ h, ← dir_edgeWest, ← hjunc m h, dir_edgeEast]
    · have hmn : m = n - 1 := by omega
      show (if m + 1 < n then _ else L) = _
      rw [if_neg (by omega), ← dir_edgeEast, hmn, heast, xco_apply, mkPt_zero]
  refine ⟨n, X, hn0, ?_, ?_, ?_, ?_⟩
  · rw [hXlt 0 hn0, ← dir_edgeWest, hwest, xco_apply, mkPt_zero]
  · show (if n < n then _ else L) = _
    rw [if_neg (lt_irrefl n)]
  · intro m hm
    rw [hXsucc m hm, hXlt m hm, hlen m hm]
    exact edge_length_cases D hM (E m).1 (E m).2
  · intro m hm
    have hne := fin3_succ_ne (E m).2
    rcases edgeWest_edgeEast_pts D.toDissection xco (E m) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨(E m).1, (E m).2, (E m).2 + 1, hne.2.1.symm, ?_, ?_⟩
      · rw [← h1, hWeq m hm, hXlt m hm]
      · rw [← h2, hEeq m hm, hXsucc m hm]
    · refine ⟨(E m).1, (E m).2 + 1, (E m).2, hne.2.1, ?_, ?_⟩
      · rw [← h1, hWeq m hm, hXlt m hm]
      · rw [← h2, hEeq m hm, hXsucc m hm]

namespace Setup

variable {N : ℕ} {D : CongruentDissection N} {n : ℕ} {α β γ : ℝ}

/-- **THE TYPED CHAIN ON `QB`.**  The side `QB` of the target is cut into `m ≥ 1` consecutive edges
`[X k, X (k+1)]`, `X 0 = 0`, `X m = 4n² − 2`, each the letter of a base tile `tile k` of type `τ k`. -/
theorem typed_chain (S : Setup D n α β γ) :
    ∃ (m : ℕ) (X : ℕ → ℝ) (tile : ℕ → Fin N) (τ : ℕ → Ty), 0 < m ∧ X 0 = 0 ∧ X m = Lw n ∧
      (∀ k, k < m → X (k + 1) = X k + (τ k).lenR n) ∧
      (∀ k, k < m → BaseTile D n (tile k) (τ k) (X k)) := by
  have hf := S.f2
  have hb := S.b_pos
  have hbase : segment ℝ (mkPt 0 0) (mkPt (Lw n) 0) ⊆ frontier D.target.carrier := by
    intro y hy
    obtain ⟨h1, h0, hL'⟩ := (mem_base_segment_iff (Lw_pos S.f1) y).mp hy
    rw [S.tgt, eq_mkPt_of_y_zero h1]
    exact base_mem_frontier S.f1 h0 hL'
  have hface : ∀ y ∈ D.target.carrier, y 1 = 0 → 0 ≤ y 0 ∧ y 0 ≤ Lw n := by
    intro y hy h1
    obtain ⟨-, h2, h3⟩ := S.mem hy
    have hr := rt_pos S.f1.le
    simp only [gQA, gBA, h1] at h2 h3
    constructor
    · by_contra h
      push Not at h
      nlinarith [mul_pos hr (neg_pos.mpr h)]
    · by_contra h
      push Not at h
      nlinarith [mul_pos (mul_pos hb hr) (sub_pos.mpr h)]
  obtain ⟨m, X, hm0, hX0, hXm, hℓ, htile⟩ :=
    base_chain_gen D S.hM (Lw_pos S.f1) (fun y hy => (S.mem hy).1) hbase hface
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

/-! ## 6. The rules that need only vertex figures -/

/-- **R-Q**: the first base tile does not show `γ` at `Q`. -/
theorem rule_Q (S : Setup D n α β γ) {i : Fin N} {t : Ty} (h : BaseTile D n i t 0) :
    t ≠ Ty.A2 ∧ t ≠ Ty.B2 := by
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have ha := (S.angles h).1
  have hle := one_angle_le D.toDissection (mkPt 0 0) i
  rw [S.angle_Q, ha] at hle
  constructor
  · rintro rfl
    have hle' : γ ≤ α + β := hle
    linarith
  · rintro rfl
    have hle' : γ ≤ α + β := hle
    linarith

/-- **R-B**: the last base tile shows `β` at `B`. -/
theorem rule_B (S : Setup D n α β γ) {i : Fin N} {t : Ty} {x : ℝ} (h : BaseTile D n i t x)
    (hx : x + t.lenR n = Lw n) : t = Ty.A2 ∨ t = Ty.C1 := by
  obtain ⟨hαβ, hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hβ2π, hγπ, hγ0, hπ0⟩ := distinct_of_angleData S.hA
  obtain ⟨i₀, j₀, hij, hang, huniq⟩ := congruentDissection_base_corner_tile_vertex D α β γ hαβ hαγ
    hαπ hα0 hβγ hβπ hβ0 hβ2π hγπ hγ0 hπ0 S.hA.hγdef S.hA.hrel S.hA.hirr S.hM.hα' S.hM.hβ' S.hM.hγ'
    1 S.corner_B'
  rw [S.B_eq] at hang huniq
  have ha := (S.angles h).2
  rw [hx] at ha
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, -, -⟩ := h
  rw [hx] at hm
  have hi : i = i₀ := huniq i (by rw [← hm]; exact subset_convexHull ℝ _ ⟨m, rfl⟩)
  rw [hi, hang] at ha
  exact Ty.aR_eq_beta hαβ hβγ t ha.symm

/-- **R-GG**: two `γ` never meet at an interior point of the side. -/
theorem rule_GG (S : Setup D n α β γ) {i j : Fin N} {t t' : Ty} {x : ℝ} (h : BaseTile D n i t x)
    (h' : BaseTile D n j t' (x + t.lenR n)) (hx0 : 0 < x + t.lenR n) (hxL : x + t.lenR n < Lw n)
    (hg : t.gR) : ¬ t'.gL := by
  intro hg'
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hl := Ty.lenR_pos S.f2 t
  have hij : i ≠ j := S.baseTile_ne h h' (by intro h0; linarith)
  have h1 := (S.angles h).2
  have h2 := (S.angles h').1
  rw [Ty.aR_of_gR α β γ hg] at h1
  rw [Ty.aL_of_gL α β γ hg'] at h2
  have h3 := two_angles_le D.toDissection (mkPt (x + t.lenR n) 0) hij
  rw [h1, h2, S.angle_base hx0 hxL] at h3
  linarith

/-- at an interior point of the side, a tile showing `γ` excludes two different tiles showing `α` -/
theorem gamma_alpha_alpha (S : Setup D n α β γ) {x : ℝ} (hx0 : 0 < x) (hxL : x < Lw n)
    {i j j' : Fin N} (hi : (D.tile i).localAngle (mkPt x 0) = γ)
    (hj : (D.tile j).localAngle (mkPt x 0) = α) (hj' : (D.tile j').localAngle (mkPt x 0) = α)
    (hjj : j ≠ j') : False := by
  classical
  obtain ⟨hαβ, hαγ, hαπ, hα0, hβγ, hβπ, hβ0, -, hγπ, hγ0, hπ0⟩ := distinct_of_angleData S.hA
  obtain ⟨hv, hnv⟩ := S.base_frontier hx0 hxL
  have hγpos : 0 < ({m | (D.tile m).localAngle (mkPt x 0) = γ} : Finset (Fin N)).card :=
    Finset.card_pos.mpr ⟨i, by simp [hi]⟩
  have h2 := two_le_card_of_ne (P := fun m => (D.tile m).localAngle (mkPt x 0) = α) hjj hj hj'
  rcases congruentDissection_boundary_figure_cases D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
    S.hA.hγdef S.hA.hrel S.hA.hirr S.hM.hα' S.hM.hβ' S.hM.hγ' hv hnv with
    ⟨_, _, _, hG⟩ | ⟨_, _, hG⟩ | ⟨hAc, _, _⟩
  · omega
  · omega
  · simp only at h2 hAc; omega

end Setup

end Erdos634.Draft.W2E1

#print axioms Erdos634.Draft.W2E1.W2_bounds
#print axioms Erdos634.Draft.W2E1.Setup.corner_Q
#print axioms Erdos634.Draft.W2E1.Setup.corner_B
#print axioms Erdos634.Draft.W2E1.Setup.typed_chain
#print axioms Erdos634.Draft.W2E1.Setup.rule_Q
#print axioms Erdos634.Draft.W2E1.Setup.rule_B
#print axioms Erdos634.Draft.W2E1.Setup.rule_GG
#print axioms Erdos634.Draft.W2E1.Setup.gamma_alpha_alpha
