import Erdos634.Draft.LaczFormalW2Step1

/-!
# Rule W2: the far side of a shared edge (interface lemma I3, general form)

Erdős #634, base-`β` band.  Credit: AI assistant (item 3, band program), Beeson–Roșu, Beeson, Laczkovich, Paliy.
UNAUDITED.  Axiom-clean; no `sorry`.

`far_side_of_shared_edge`: two different tiles sharing the whole edge `[P,G]` lie on opposite sides of the line
`PG` (their third vertices have `cross (G−P) (V−P)` of opposite signs).  This is the "same-side overlap lemma"
(`Dissection.sameside_edges_subsingleton`) in the form used to place the tile `T'` opposite to `T₀`.
-/

namespace Erdos634.LaczJunction.Walk

open Erdos634.Geometry Erdos634.TilePlacement

variable {N : ℕ}

theorem tile_halfspace (T : Tri) (φ : Plane →ₗ[ℝ] ℝ) (c : ℝ) (h : ∀ k, φ (T.pts k) ≤ c) :
    ∀ y ∈ T.carrier, φ y ≤ c := by
  have hconv : Convex ℝ {y : Plane | φ y ≤ c} := convex_halfSpace_le φ.isLinear c
  have hsub : Set.range T.pts ⊆ {y : Plane | φ y ≤ c} := by
    rintro _ ⟨k, rfl⟩; exact h k
  exact fun y hy => convexHull_min hsub hconv hy

theorem lin_seg {φ : Plane →ₗ[ℝ] ℝ} {A B y : Plane} {c : ℝ} (hA : φ A = c) (hB : φ B = c)
    (hy : y ∈ segment ℝ A B) : φ y = c := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
  rw [map_add, map_smul, map_smul, hA, hB, smul_eq_mul, smul_eq_mul, ← add_mul, hab, one_mul]

theorem fin3_three_cases (kk m : Fin 3) : kk = m ∨ kk = m + 1 ∨ kk = m + 2 := by
  revert kk m; decide

/-- **Two different tiles sharing the edge `[P,G]` lie on opposite sides of `PG`.** -/
theorem far_side_of_shared_edge (D : Dissection N) {P G V0 H : Plane} (hPG : P ≠ G)
    (i0 i' : Fin N) (hi : i' ≠ i0) (j k : Fin 3)
    (h0 : (D.tile i0).edge j = segment ℝ P G) (hV0 : (D.tile i0).pts (j + 2) = V0)
    (hj : ((D.tile i0).pts j = P ∧ (D.tile i0).pts (j + 1) = G) ∨
      ((D.tile i0).pts j = G ∧ (D.tile i0).pts (j + 1) = P))
    (h' : (D.tile i').edge k = segment ℝ P G) (hH : (D.tile i').pts (k + 2) = H)
    (hk : ((D.tile i').pts k = P ∧ (D.tile i').pts (k + 1) = G) ∨
      ((D.tile i').pts k = G ∧ (D.tile i').pts (k + 1) = P)) :
    cross (G - P) (V0 - P) * cross (G - P) (H - P) < 0 := by
  have hnz0 : cross (G - P) (V0 - P) ≠ 0 := by
    rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := (D.tile i0).det_cyclic j
      rw [h1, h2, hV0] at this
      rw [this]; exact (D.tile i0).det_ne_zero
    · have := (D.tile i0).det_cyclic j
      rw [h1, h2, hV0] at this
      have e : cross (G - P) (V0 - P) = - cross (P - G) (V0 - G) := by
        simp only [cross, PiLp.sub_apply]; ring
      rw [e, this]; exact neg_ne_zero.mpr (D.tile i0).det_ne_zero
  have hdet' : cross (G - P) (H - P) ≠ 0 := by
    rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := (D.tile i').det_cyclic k
      rw [h1, h2, hH] at this
      rw [this]; exact (D.tile i').det_ne_zero
    · have := (D.tile i').det_cyclic k
      rw [h1, h2, hH] at this
      -- cross (P - G) (H - G) = det ; cross (G-P) (H-P) = - that
      have e : cross (G - P) (H - P) = - cross (P - G) (H - G) := by
        simp only [cross, PiLp.sub_apply]; ring
      rw [e, this]; exact neg_ne_zero.mpr (D.tile i').det_ne_zero
  by_contra hnot
  have hnot' : 0 ≤ cross (G - P) (V0 - P) * cross (G - P) (H - P) := not_lt.mp hnot
  have hpos : 0 < cross (G - P) (V0 - P) * cross (G - P) (H - P) :=
    lt_of_le_of_ne hnot' (Ne.symm (mul_ne_zero hnz0 hdet'))
  set s := G - P with hs
  have key : ∀ y : Plane, cross s (y - P) = crossL s y - crossL s P := by
    intro y; rw [cross_sub_right]; rfl
  have hφG : crossL s G = crossL s P := by
    have := key G
    have h0 : cross s (G - P) = 0 := cross_self _
    linarith
  have hf0 : ∀ σ : ℝ, σ ≠ 0 → (σ • crossL s) ≠ 0 := by
    intro σ hσ h
    apply hPG
    have hz : s = 0 := by
      apply eq_zero_of_cross_eq_zero; intro v
      have := congrArg (fun g : Plane →ₗ[ℝ] ℝ => g v) h
      simp only [LinearMap.smul_apply, crossL_apply, LinearMap.zero_apply, smul_eq_mul] at this
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' hσ
      · exact h'
    exact (sub_eq_zero.mp hz).symm
  have hne : ((i', k) : Fin N × Fin 3) ≠ (i0, j) := by
    intro h; exact hi (Prod.mk.inj h).1
  -- the sign
  obtain ⟨σ, hσ, hV, hHs⟩ : ∃ σ : ℝ, σ ≠ 0 ∧ σ * cross s (V0 - P) ≥ 0 ∧ σ * cross s (H - P) ≥ 0 := by
    rcases lt_or_gt_of_ne hnz0 with h | h
    · refine ⟨-1, by norm_num, by linarith, ?_⟩
      have : cross s (H - P) < 0 := by
        by_contra hh; push_neg at hh; nlinarith
      linarith
    · refine ⟨1, by norm_num, by linarith, ?_⟩
      have : 0 < cross s (H - P) := by
        by_contra hh; push_neg at hh; nlinarith
      linarith
  set φ : Plane →ₗ[ℝ] ℝ := -(σ • crossL s) with hφ
  set c : ℝ := φ P with hc
  have hφv : ∀ y : Plane, φ y - c = -(σ * cross s (y - P)) := by
    intro y; rw [hc, hφ]; simp only [LinearMap.neg_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [key]; ring
  have hle_of : ∀ (T : Tri) (m : Fin 3), (∀ y, (T.pts m = y ∨ T.pts (m+1) = y ∨ T.pts (m+2) = y) → φ y ≤ c) →
      ∀ y ∈ T.carrier, φ y ≤ c := by
    intro T m h
    apply tile_halfspace T φ c
    intro kk
    rcases fin3_three_cases kk m with rfl | rfl | rfl
    · exact h _ (Or.inl rfl)
    · exact h _ (Or.inr (Or.inl rfl))
    · exact h _ (Or.inr (Or.inr rfl))
  have hφP : φ P = c := rfl
  have hφG' : φ G = c := by
    have := hφv G
    have h0 : cross s (G - P) = 0 := cross_self _
    rw [h0] at this; linarith
  have hT0 : ∀ y ∈ (D.tile i0).carrier, φ y ≤ c := by
    apply hle_of _ j
    intro y hy
    rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases hy with h | h | h
      · rw [h1] at h; subst h; exact le_of_eq hφP
      · rw [h2] at h; subst h; exact le_of_eq hφG'
      · rw [hV0] at h; subst h; have := hφv V0; linarith
    · rcases hy with h | h | h
      · rw [h1] at h; subst h; exact le_of_eq hφG'
      · rw [h2] at h; subst h; exact le_of_eq hφP
      · rw [hV0] at h; subst h; have := hφv V0; linarith
  have hT' : ∀ y ∈ (D.tile i').carrier, φ y ≤ c := by
    apply hle_of _ k
    intro y hy
    rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases hy with h | h | h
      · rw [h1] at h; subst h; exact le_of_eq hφP
      · rw [h2] at h; subst h; exact le_of_eq hφG'
      · rw [hH] at h; subst h; have := hφv H; linarith
    · rcases hy with h | h | h
      · rw [h1] at h; subst h; exact le_of_eq hφG'
      · rw [h2] at h; subst h; exact le_of_eq hφP
      · rw [hH] at h; subst h; have := hφv H; linarith
  have hE : ∀ (i : Fin N) (m : Fin 3), (D.tile i).edge m = segment ℝ P G → ∀ y ∈ (D.tile i).edge m, φ y = c := by
    intro i m he y hy
    rw [he] at hy
    exact lin_seg (φ := φ) hφP hφG' hy
  have hsub := D.sameside_edges_subsingleton φ c (by
      rw [hφ]; exact neg_ne_zero.mpr (hf0 σ hσ)) (e₁ := (i', k)) (e₂ := (i0, j)) hne
    (fun y hy => hT' y hy) (fun y hy => hT0 y hy) (hE i' k h') (hE i0 j h0)
  have hPm : P ∈ (D.tile i').edge k ∩ (D.tile i0).edge j := by
    rw [h', h0]; exact ⟨left_mem_segment _ _ _, left_mem_segment _ _ _⟩
  have hGm : G ∈ (D.tile i').edge k ∩ (D.tile i0).edge j := by
    rw [h', h0]; exact ⟨right_mem_segment _ _ _, right_mem_segment _ _ _⟩
  exact hPG (hsub hPm hGm)

#print axioms far_side_of_shared_edge

end Erdos634.LaczJunction.Walk
