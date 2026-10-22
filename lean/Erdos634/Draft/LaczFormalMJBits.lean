import Erdos634.Draft.LaczFormalMJAdv

/-!
# Small geometric facts for the stages of `M(j)`

Erdős #634, base-`β` band, rule `M(j)`.  Credit: AI assistant (item 3, band program), Beeson–Roșu, Beeson,
Laczkovich, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.

* `tv_cross_ne`: the three vertices of a tile are not collinear.
* `open_coords`, `edge_unique`: a point in the relative interior of an edge lies in the relative interior of no other
  edge of the same tile.
* `lines_meet_once`: the line `Λ` and the line `l` of direction `v − e0` meet in one point.
* `Dp_eq`, `Dp_not_mem_open`: the points `D_j = J + j(v − e0)` and the open segments between consecutive ones.
-/

namespace Erdos634.LaczMJ

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.TraceCovering Set

variable {N : ℕ}

theorem tv_cross_ne {T : Tri} {A B C : Plane} (h : TileVerts T A B C) :
    cross (B - A) (C - A) ≠ 0 := by
  have F3 : ∀ j : Fin 3, j ≠ j + 1 ∧ j ≠ j + 2 ∧ j + 1 ≠ j + 2 := by decide
  obtain ⟨j, ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩⟩ := h
  · have := tile_cross_ne T j (j + 1) (j + 2) (F3 j).1 (F3 j).2.1 (F3 j).2.2
    rwa [h1, h2, h3] at this
  · have := tile_cross_ne T j (j + 2) (j + 1) (F3 j).2.1 (F3 j).1 (F3 j).2.2.symm
    rwa [h1, h2, h3] at this

/-- Barycentric coordinates of a point in the relative interior of an edge. -/
theorem open_coords (T : Tri) (k : Fin 3) {y : Plane} (hy : y ∈ openSegment ℝ (T.pts k) (T.pts (k + 1))) :
    0 < T.basis.coord k y ∧ 0 < T.basis.coord (k + 1) y ∧ T.basis.coord (k + 2) y = 0 := by
  have n01 : ∀ k : Fin 3, k ≠ k + 1 := by decide
  have n02 : ∀ k : Fin 3, k + 2 ≠ k := by decide
  have n12 : ∀ k : Fin 3, k + 2 ≠ k + 1 := by decide
  have n21 : ∀ k : Fin 3, k + 1 ≠ k := by decide
  obtain ⟨a', b', ha', hb', hab', rfl⟩ := hy
  have c0 : T.basis.coord k (a' • T.pts k + b' • T.pts (k + 1)) = a' := by
    have h := Convex.combo_affine_apply (f := T.basis.coord k) (x := T.pts k) (y := T.pts (k + 1)) hab'
    have e1 : T.basis.coord k (T.pts k) = 1 := T.basis.coord_apply_eq _
    have e2 : T.basis.coord k (T.pts (k + 1)) = 0 := T.basis.coord_apply_ne (n01 k)
    rw [h, e1, e2]; simp
  have c1 : T.basis.coord (k + 1) (a' • T.pts k + b' • T.pts (k + 1)) = b' := by
    have h := Convex.combo_affine_apply (f := T.basis.coord (k + 1)) (x := T.pts k) (y := T.pts (k + 1)) hab'
    have e1 : T.basis.coord (k + 1) (T.pts (k + 1)) = 1 := T.basis.coord_apply_eq _
    have e2 : T.basis.coord (k + 1) (T.pts k) = 0 := T.basis.coord_apply_ne (n21 k)
    rw [h, e1, e2]; simp
  have hz : T.basis.coord (k + 2) (a' • T.pts k + b' • T.pts (k + 1)) = 0 := by
    have h := Convex.combo_affine_apply (f := T.basis.coord (k + 2)) (x := T.pts k) (y := T.pts (k + 1)) hab'
    have e1 : T.basis.coord (k + 2) (T.pts k) = 0 := T.basis.coord_apply_ne (n02 k)
    have e2 : T.basis.coord (k + 2) (T.pts (k + 1)) = 0 := T.basis.coord_apply_ne (n12 k)
    rw [h, e1, e2]; simp
  exact ⟨by rw [c0]; exact ha', by rw [c1]; exact hb', hz⟩

theorem edge_unique (T : Tri) {k k' : Fin 3} {y : Plane}
    (hy : y ∈ openSegment ℝ (T.pts k) (T.pts (k + 1)))
    (hy' : y ∈ openSegment ℝ (T.pts k') (T.pts (k' + 1))) : k = k' := by
  by_contra hne
  obtain ⟨p0, p1, p2⟩ := open_coords T k hy
  obtain ⟨q0, q1, q2⟩ := open_coords T k' hy'
  have hc : ∀ k k' : Fin 3, k ≠ k' → k' + 2 = k ∨ k' + 2 = k + 1 := by decide
  rcases hc k k' hne with h | h
  · rw [h] at q2; linarith
  · rw [h] at q2; linarith

namespace LFrame

variable {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
  (F : LFrame D e f α β γ p q r)

theorem lines_meet_once {P P' : Plane} {c1 c2 : ℝ}
    (h1 : cross (F.v - F.e0) P = c1) (h1' : cross (F.v - F.e0) P' = c1)
    (h2 : cross (-F.e0) P = c2) (h2' : cross (-F.e0) P' = c2) : P = P' := by
  have hd1 : cross (F.v - F.e0) (P' - P) = 0 := by rw [cross_sub_right, h1, h1']; ring
  have hd2 : cross F.e0 (P' - P) = 0 := by
    have : cross (-F.e0) (P' - P) = 0 := by rw [cross_sub_right, h2, h2']; ring
    have e1 : cross (-F.e0) (P' - P) = - cross F.e0 (P' - P) := by
      simp only [cross, PiLp.neg_apply]; ring
    linarith
  obtain ⟨t, ht⟩ := on_line_param F.e0_ne hd2
  rw [ht] at hd1
  have : cross (F.v - F.e0) (t • F.e0) = - t * cross F.e0 F.v := by
    rw [cross_smul_right]
    have : cross (F.v - F.e0) F.e0 = - cross F.e0 F.v := by
      simp only [cross, PiLp.sub_apply]; ring
    rw [this]; ring
  rw [this] at hd1
  have ht0 : t = 0 := by
    have := F.hcr
    rcases mul_eq_zero.mp (by linarith : (-t) * cross F.e0 F.v = 0) with h | h
    · linarith
    · linarith
  rw [ht0, zero_smul] at ht
  exact (sub_eq_zero.mp ht).symm

theorem Dp_eq (j : ℝ) (m lv : ℝ) :
    F.pt (m + 1 - j) (lv + j) = F.pt (m + 1) lv + j • (F.v - F.e0) := by
  simp only [pt]; module

theorem Dp_not_mem_open {m lv : ℝ} (hu0 : F.v - F.e0 ≠ 0) {k s : ℕ} :
    F.pt (m + 1 - s) (lv + s) ∉
      openSegment ℝ (F.pt (m + 1 - k) (lv + k)) (F.pt (m + 1 - (k + 1)) (lv + (k + 1))) := by
  intro h
  rw [F.Dp_eq, F.Dp_eq, F.Dp_eq] at h
  rw [openSegment_param (X := F.pt (m + 1) lv) (u := F.v - F.e0) (by simp)] at h
  obtain ⟨x, hx, hxs⟩ := h
  have := lm_injective hu0 hxs
  rw [min_eq_left (by linarith), max_eq_right (by linarith)] at hx
  have h1 : (k : ℝ) < s := by rw [← this]; exact hx.1
  have h2 : (s : ℝ) < k + 1 := by rw [← this]; exact hx.2
  have h1' : k < s := by exact_mod_cast h1
  have h2' : s < k + 1 := by exact_mod_cast h2
  omega

end LFrame

end Erdos634.LaczMJ
