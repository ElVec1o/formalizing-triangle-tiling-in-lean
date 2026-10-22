import Erdos634.Draft.LaczFormalW2Step1Tok
import Erdos634.Draft.LaczFormalW2Pos
import Erdos634.Draft.LaczFormalJunctionWall

/-!
# Rule W2: chord lemmas in the form used by the proof

Erdős #634, band program, rule W2 (`PROOF_W2.md`).  Credit: AI assistant (item 3, band program), Beeson–Roșu, Beeson,
Laczkovich (fan/chord covers), Paliy.  UNAUDITED.

* `L3_sum_g`, `L3_one_g`, `L3_two_g`: L3 with the far-side chain written `lineChain g c` (tiles with `g ≤ c` on
  their vertices) instead of `lineChain (-f) (-c)`;
* `localAngle_pi_of_openSegment`: a point in the relative interior of a tile edge has local angle `π`;
* `on_line_param`, `target_right_leg`, `angle_sum_le`.
-/

namespace Erdos634.LaczJunction.Walk

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Grammar
open Erdos634.Draft.TraceCovering

variable {N : ℕ}

open Classical in
theorem L3_sum_g (D : Dissection N) {P G : Plane} (hne : P ≠ G) (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hg0 : g ≠ 0)
    (hgP : g P = c) (hgG : g G = c)
    (hint : ∀ t : ℝ, 0 < t → t < 1 → AffineMap.lineMap P G t ∈ interior D.target.carrier)
    (hbef : ∀ t : ℝ, t < 0 → AffineMap.lineMap P G t ∉ D.target.carrier)
    (hnear : ∀ t : ℝ, 0 < t → t < 1 → ∃ (i : Fin N) (k : Fin 3),
      AffineMap.lineMap P G t ∈ (D.tile i).edge k)
    (hGend : ¬ Straddled D g c G) :
    ∑ e ∈ (D.lineChain g c).filter (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ P G),
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = dist P G := by
  have := L3_sum_of_edges D hne (-g) (-c) (neg_ne_zero.mpr hg0) (by simp [hgP]) (by simp [hgG]) hint hbef hnear
    (by simpa using hGend)
  simpa using this

open Classical in
/-- **L3, single edge.** If the only way to write the chord length `n` as `xA + yB + zC` uses exactly one side,
the far side of the chord is one tile edge equal to `[P,G]` (of a tile on the far side). -/
theorem L3_one_g (D : Dissection N) (A B C n : ℕ)
    (hcover : ∀ x y z : ℕ, x * A + y * B + z * C = n → x + y + z = 1)
    (habc : ∀ (i : Fin N) (k : Fin 3),
      dist ((D.tile i).pts k) ((D.tile i).pts (k+1)) = (A : ℝ) ∨
      dist ((D.tile i).pts k) ((D.tile i).pts (k+1)) = (B : ℝ) ∨
      dist ((D.tile i).pts k) ((D.tile i).pts (k+1)) = (C : ℝ))
    {P G : Plane} (hne : P ≠ G) (hPG : dist P G = (n : ℝ)) (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hg0 : g ≠ 0)
    (hgP : g P = c) (hgG : g G = c)
    (hint : ∀ t : ℝ, 0 < t → t < 1 → AffineMap.lineMap P G t ∈ interior D.target.carrier)
    (hbef : ∀ t : ℝ, t < 0 → AffineMap.lineMap P G t ∉ D.target.carrier)
    (hnear : ∀ t : ℝ, 0 < t → t < 1 → ∃ (i : Fin N) (k : Fin 3),
      AffineMap.lineMap P G t ∈ (D.tile i).edge k)
    (hGend : ¬ Straddled D g c G) :
    ∃ (i : Fin N) (k : Fin 3), (((D.tile i).pts k = P ∧ (D.tile i).pts (k + 1) = G) ∨
      ((D.tile i).pts k = G ∧ (D.tile i).pts (k + 1) = P)) ∧ (∀ j, g ((D.tile i).pts j) ≤ c) := by
  have hsum := L3_sum_g D hne g c hg0 hgP hgG hint hbef hnear hGend
  set S := (D.lineChain g c).filter (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ P G) with hS
  obtain ⟨X', Y', Z', hXYZ, hcard⟩ := Erdos634.Geometry.sum_three_values S
    (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) (A : ℝ) (B : ℝ) (C : ℝ)
    (fun e _ => habc e.1 e.2)
  rw [hsum, hPG] at hXYZ
  have hnat : X' * A + Y' * B + Z' * C = n := by
    have : ((X' * A + Y' * B + Z' * C : ℕ) : ℝ) = (n : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have h1 := hcover _ _ _ hnat
  have hc1 : S.card = 1 := by omega
  obtain ⟨e, hSe⟩ := Finset.card_eq_one.mp hc1
  have hem : e ∈ S := by rw [hSe]; simp
  have hm := Finset.mem_filter.mp hem
  have hlen : dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = dist P G := by
    rw [← hsum, hSe, Finset.sum_singleton]
  have hch := Dissection.mem_lineChain.mp hm.1
  have hsub := hm.2
  have h0 : (D.tile e.1).pts e.2 ∈ segment ℝ P G := hsub (left_mem_segment ℝ _ _)
  have h1' : (D.tile e.1).pts (e.2 + 1) ∈ segment ℝ P G := hsub (right_mem_segment ℝ _ _)
  refine ⟨e.1, e.2, ends_of_segment hne h0 h1' hlen, hch.2.2⟩


open Classical in
/-- **L3 for a `2B` chord, far chain `lineChain g c`.** -/
theorem L3_two_g (D : Dissection N) (A B C : ℕ)
    (hcover : ∀ x y z : ℕ, x * A + y * B + z * C = 2 * B → x = 0 ∧ y = 2 ∧ z = 0)
    (habc : ∀ (i : Fin N) (k : Fin 3),
      dist ((D.tile i).pts k) ((D.tile i).pts (k+1)) = (A : ℝ) ∨
      dist ((D.tile i).pts k) ((D.tile i).pts (k+1)) = (B : ℝ) ∨
      dist ((D.tile i).pts k) ((D.tile i).pts (k+1)) = (C : ℝ))
    {P G : Plane} (hne : P ≠ G) (hPG : dist P G = 2 * (B : ℝ))
    (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hg0 : g ≠ 0) (hgP : g P = c) (hgG : g G = c)
    (hint : ∀ t : ℝ, 0 < t → t < 1 → AffineMap.lineMap P G t ∈ interior D.target.carrier)
    (hbef : ∀ t : ℝ, t < 0 → AffineMap.lineMap P G t ∉ D.target.carrier)
    (hwall : ∀ t : ℝ, 0 < t → t < 1 → ∀ i, AffineMap.lineMap P G t ∉ interior (D.tile i).carrier)
    (hGend : ¬ Straddled D g c G) :
    ∃ e₁ e₂ : Fin N × Fin 3, e₁ ≠ e₂ ∧ e₁ ∈ D.lineChain g c ∧ e₂ ∈ D.lineChain g c ∧
      dist ((D.tile e₁.1).pts e₁.2) ((D.tile e₁.1).pts (e₁.2 + 1)) = (B : ℝ) ∧
      dist ((D.tile e₂.1).pts e₂.2) ((D.tile e₂.1).pts (e₂.2 + 1)) = (B : ℝ) ∧
      (((D.tile e₁.1).edge e₁.2 = segment ℝ P (midpoint ℝ P G) ∧
          (D.tile e₂.1).edge e₂.2 = segment ℝ (midpoint ℝ P G) G) ∨
        ((D.tile e₂.1).edge e₂.2 = segment ℝ P (midpoint ℝ P G) ∧
          (D.tile e₁.1).edge e₁.2 = segment ℝ (midpoint ℝ P G) G)) := by
  have := L3_two_b_pos D A B C hcover habc hne hPG (-g) (-c) (neg_ne_zero.mpr hg0) (by simp [hgP])
    (by simp [hgG]) hint hbef hwall (by simpa using hGend)
  simpa using this

/-- A point in the relative interior of an edge of a tile has local angle `π` there. -/
theorem localAngle_pi_of_openSegment (T : Tri) (k : Fin 3) {y : Plane}
    (hy : y ∈ openSegment ℝ (T.pts k) (T.pts (k + 1))) : T.localAngle y = Real.pi := by
  classical
  have n01 : ∀ k : Fin 3, k ≠ k + 1 := by decide
  have n02 : ∀ k : Fin 3, k + 2 ≠ k := by decide
  have n12 : ∀ k : Fin 3, k + 2 ≠ k + 1 := by decide
  have n21 : ∀ k : Fin 3, k + 1 ≠ k := by decide
  have hcov : ∀ k j : Fin 3, j ≠ k + 2 → j = k ∨ j = k + 1 := by decide
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
  set y := a' • T.pts k + b' • T.pts (k + 1) with hydef
  unfold Tri.localAngle
  have hv : ¬ ∃ j, y = T.pts j := by
    rintro ⟨j, hj⟩
    by_cases hjk : k = j
    · have : T.basis.coord (k + 1) y = 0 := by
        rw [hj]; exact T.basis.coord_apply_ne (by rw [← hjk]; exact n21 k)
      linarith
    · have : T.basis.coord k y = 0 := by rw [hj]; exact T.basis.coord_apply_ne hjk
      linarith
  rw [dif_neg hv]
  have h1 : ¬ ∀ j, 0 < T.basis.coord j y := fun h => by have := h (k + 2); linarith
  rw [if_neg h1]
  have h2 : ∃ kk, T.basis.coord kk y = 0 ∧ ∀ j, j ≠ kk → 0 < T.basis.coord j y := by
    refine ⟨k + 2, hz, fun j hj => ?_⟩
    rcases hcov k j hj with rfl | rfl
    · rw [c0]; exact ha'
    · rw [c1]; exact hb'
  rw [if_pos h2]

/-- A vector with zero cross product with `u ≠ 0` is a multiple of `u`. -/
theorem on_line_param {u w : Plane} (hu : u ≠ 0) (h : cross u w = 0) : ∃ s : ℝ, w = s • u := by
  have hn : u 0 ^ 2 + u 1 ^ 2 ≠ 0 := by
    intro h0
    apply hu
    have h1 : u 0 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
    have h2 : u 1 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
    ext i; fin_cases i <;> simp [h1, h2]
  refine ⟨(u 0 * w 0 + u 1 * w 1) / (u 0 ^ 2 + u 1 ^ 2), ?_⟩
  have hc : u 0 * w 1 - u 1 * w 0 = 0 := h
  ext i; fin_cases i
  · simp only [Fin.zero_eta, PiLp.smul_apply, smul_eq_mul]
    field_simp
    linear_combination (-(u 1)) * hc
  · simp only [Fin.mk_one, PiLp.smul_apply, smul_eq_mul]
    field_simp
    linear_combination (u 0) * hc

/-- The target lies on the right of the left leg `A_p → A_r` (oriented target). -/
theorem target_right_leg {D : CongruentDissection N} {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r)
    (hori : 0 < cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p)) :
    ∀ y ∈ D.target.carrier, cross (D.target.pts r - D.target.pts p) (y - D.target.pts p) ≤ 0 := by
  intro y hy
  set P := D.target.pts p
  set w := D.target.pts r - P
  have hconv : Convex ℝ {y : Plane | crossL w y ≤ crossL w P} :=
    convex_halfSpace_le (crossL w).isLinear _
  have key : ∀ y' : Plane, cross w (y' - P) = crossL w y' - crossL w P := by
    intro y'; rw [cross_sub_right]; rfl
  have hsub : Set.range D.target.pts ⊆ {y : Plane | crossL w y ≤ crossL w P} := by
    rintro _ ⟨k, rfl⟩
    simp only [Set.mem_setOf_eq]
    rcases w2_fin3_cov p q r hpq hpr hqr k with h | h | h
    · rw [h]
    · have h0 := key (D.target.pts k)
      rw [h] at h0 ⊢
      have : cross w (D.target.pts q - P) = - cross (D.target.pts q - P) w := cross_swap _ _
      have h3 : 0 < cross (D.target.pts q - P) w := hori
      linarith
    · have h0 := key (D.target.pts k)
      have : cross w (D.target.pts k - P) = 0 := by
        rw [h]; exact Erdos634.Geometry.cross_self _
      linarith
  have := convexHull_min hsub hconv hy
  simp only [Set.mem_setOf_eq] at this
  rw [key]; linarith

/-- Local angles at an interior point of the target of distinct tiles add up to at most `2π`. -/
theorem angle_sum_le (D : Dissection N) {y : Plane} (hy : y ∈ interior D.target.carrier) (s : Finset (Fin N)) :
    ∑ i ∈ s, (D.tile i).localAngle y ≤ 2 * Real.pi := by
  classical
  have h := D.sum_localAngle_eq y
  rw [D.target.localAngle_interior hy] at h
  rw [← h]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
    (fun i _ _ => (D.tile i).localAngle_nonneg y)

end Erdos634.LaczJunction.Walk
