import Erdos634.Draft.TraceCovering
import Erdos634.Draft.LaczFormalJunctionChord

/-!
# Band junction rules: the far side of a tile-edge chord (D1, the chord step)

Erdős #634, base-`β` band.  Credit: AI assistant (band lemma / item-3 proposal), Beeson–Roșu, Beeson,
Laczkovich, Paliy.

Let `[P,G]` be an edge of a tile `T₁` of a `Dissection` of a triangle, `P` strictly inside side
`[A₀,A₁]`, `G` strictly inside side `[A₀,A₂]`.  Then the line `PG` leaves the target immediately
beyond `P` and `G` (`chord_geometry`), the open chord is a wall (an edge of `T₁`), so the far side of
the chord is covered by whole tile edges whose lengths add up to `|PG|`
(`TraceCovering.wall_sum`).  If every tile edge has length `A`, `B` or `C` and `|PG| = B` with
`xA + yB + zC = B ⇒ (x,y,z) = (0,1,0)`, the far side is a **single tile edge equal to `[P,G]`**,
of a tile different from `T₁`.  This is `far_edge_exists`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.LaczJunction

open Erdos634.Geometry Erdos634.Draft.TraceCovering Set

variable {N : ℕ}

/-- Two points of `[P,G]` at distance `|PG|` are the endpoints. -/
theorem ends_of_segment {P G p q : Plane} (hPG : P ≠ G) (hp : p ∈ segment ℝ P G)
    (hq : q ∈ segment ℝ P G) (hd : dist p q = dist P G) :
    (p = P ∧ q = G) ∨ (p = G ∧ q = P) := by
  rw [segment_eq_image_lineMap] at hp hq
  obtain ⟨s, hs, rfl⟩ := hp
  obtain ⟨t, ht, rfl⟩ := hq
  rw [dist_lineMap_lineMap] at hd
  have hpos : 0 < dist P G := dist_pos.mpr hPG
  have h1 : dist s t = 1 := by
    have := mul_right_cancel₀ hpos.ne' (by rw [hd, one_mul] : dist s t * dist P G = 1 * dist P G)
    exact this
  rw [Real.dist_eq] at h1
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨ht0, ht1⟩ := ht
  rcases abs_cases (s - t) with ⟨h, _⟩ | ⟨h, _⟩
  · have : s = 1 := by linarith
    have : t = 0 := by linarith
    subst_vars; right; simp
  · have : s = 0 := by linarith
    have : t = 1 := by linarith
    subst_vars; left; simp

theorem line_param (P G : Plane) {b : ℝ} (hb : b ≠ 0) (x : ℝ) :
    P + x • (b⁻¹ • (G - P)) = AffineMap.lineMap P G (x / b) := by
  rw [AffineMap.lineMap_apply, smul_smul]
  simp [div_eq_mul_inv, add_comm, mul_comm]

/-- **The far side of a tile-edge chord is a single tile edge.** -/
theorem far_edge_gen (D : Dissection N) (A B C : ℕ)
    (hcover : ∀ x y z : ℕ, x * A + y * B + z * C = B → x = 0 ∧ y = 1 ∧ z = 0)
    (habc : ∀ (i : Fin N) (k : Fin 3),
      dist ((D.tile i).pts k) ((D.tile i).pts (k+1)) = (A : ℝ) ∨
      dist ((D.tile i).pts k) ((D.tile i).pts (k+1)) = (B : ℝ) ∨
      dist ((D.tile i).pts k) ((D.tile i).pts (k+1)) = (C : ℝ))
    {P G : Plane}
    (hint : ∀ t : ℝ, 0 < t → t < 1 → AffineMap.lineMap P G t ∈ interior D.target.carrier)
    (hbef : ∀ t : ℝ, t < 0 → AffineMap.lineMap P G t ∉ D.target.carrier)
    (hPG : dist P G = (B : ℝ)) (hB : 0 < B)
    (i1 : Fin N) (j1 : Fin 3) (hPv : (D.tile i1).pts j1 = P) (hGv : (D.tile i1).pts (j1+1) = G)
    (hGend : ∀ (f : Plane →ₗ[ℝ] ℝ) (c : ℝ), f ≠ 0 → f P = c → f G = c →
      f ((D.tile i1).pts (j1+2)) < c → ¬ Straddled D (-f) (-c) G) :
    ∃ (i' : Fin N) (k : Fin 3), i' ≠ i1 ∧
      dist ((D.tile i').pts k) ((D.tile i').pts (k+1)) = (B : ℝ) ∧
      (((D.tile i').pts k = P ∧ (D.tile i').pts (k+1) = G) ∨
       ((D.tile i').pts k = G ∧ (D.tile i').pts (k+1) = P)) := by
  classical
  have hBr : (0:ℝ) < B := by exact_mod_cast hB
  have hne : P ≠ G := by
    intro h; rw [h, dist_self] at hPG; linarith
  -- the side of the line on which `T₁` lies
  set T1 := D.tile i1 with hT1
  set V := T1.pts (j1+2) with hV
  have hdet : cross (G - P) (V - P) = T1.det := by
    have := T1.det_cyclic j1
    rwa [hPv, hGv] at this
  have hdet0 : T1.det ≠ 0 := T1.det_ne_zero
  obtain ⟨f, c, hf0, hfP, hfG, hfV⟩ : ∃ (f : Plane →ₗ[ℝ] ℝ) (c : ℝ), f ≠ 0 ∧ f P = c ∧ f G = c ∧
      f V < c := by
    have hu0 : G - P ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have hcrossne : crossL (G - P) ≠ 0 := by
      intro h
      apply hu0
      apply eq_zero_of_cross_eq_zero
      intro v
      have := congrArg (fun g : Plane →ₗ[ℝ] ℝ => g v) h
      simpa using this
    have hGP : crossL (G - P) G = crossL (G - P) P := by
      have : cross (G - P) (G - P) = 0 := cross_self _
      rw [cross_sub_right] at this
      simpa using (sub_eq_zero.mp this)
    have hVc : crossL (G - P) V - crossL (G - P) P = T1.det := by
      rw [crossL_apply, crossL_apply, ← cross_sub_right, hdet]
    rcases lt_or_gt_of_ne hdet0 with hneg | hpos
    · exact ⟨crossL (G - P), crossL (G - P) P, hcrossne, rfl, hGP, by linarith⟩
    · refine ⟨-crossL (G - P), -crossL (G - P) P, ?_, rfl, ?_, ?_⟩
      · intro h; apply hcrossne; simpa using h
      · simp [hGP]
      · simp only [LinearMap.neg_apply]; linarith
  have hu0 : (B:ℝ)⁻¹ • (G - P) ≠ 0 := by
    apply smul_ne_zero (inv_ne_zero hBr.ne')
    exact sub_ne_zero.mpr (Ne.symm hne)
  set u : Plane := (B:ℝ)⁻¹ • (G - P) with hu
  have hfu : f u = 0 := by
    rw [hu, map_smul, map_sub, hfG, hfP]; simp
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, Real.norm_of_nonneg hBr.le, ← dist_eq_norm, dist_comm, hPG]
    field_simp
  have hend : P + (B:ℝ) • u = G := by
    rw [hu, smul_smul, mul_inv_cancel₀ hBr.ne', one_smul]; abel
  have hgd : ∀ y, (-f) y = -c ↔ f y = c := neg_iff
  have hnf : (-f : Plane →ₗ[ℝ] ℝ) ≠ 0 := fun h => hf0 (neg_eq_zero.mp h)
  have hseg : ∀ x : ℝ, 0 ≤ x → x ≤ B → P + x • u ∈ segment ℝ P G := by
    intro x hx0 hx1
    rw [hu, line_param P G hBr.ne' x, segment_eq_image_lineMap]
    exact ⟨x / B, ⟨div_nonneg hx0 hBr.le, (div_le_one hBr).mpr hx1⟩, rfl⟩
  have hsum := wall_sum (D := D) (X := P) (u := u) (f := f) (g := -f) (c := c) (d := -c) hnf hgd hf0
    hfP hfu hu1 (s := 0) (t := (B:ℝ)) hBr.le
    (fun x hx => by
      rw [hu, line_param P G hBr.ne' x]
      exact hint _ (div_pos hx.1 hBr) ((div_lt_one hBr).mpr hx.2))
    (fun x hx i => by
      have hmem : P + x • u ∈ (D.tile i1).edge j1 := by
        show P + x • u ∈ segment ℝ ((D.tile i1).pts j1) ((D.tile i1).pts (j1+1))
        rw [hPv, hGv]; exact hseg x hx.1.le hx.2.le
      exact D.edge_point_not_interior hmem i)
    (not_straddled_of_outside_before hgd hf0 hfP hfu hu0 (x₀ := 0) (fun t ht => by
      rw [hu, line_param P G hBr.ne' t]
      exact hbef _ (div_neg_of_neg_of_pos ht hBr)))
    (by rw [hend]; exact hGend f c hf0 hfP hfG hfV)
  -- the filtered far-side chain
  set S := (D.lineChain (-f) (-c)).filter
    (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ (P + (0:ℝ) • u) (P + (B:ℝ) • u)) with hS
  rw [sub_zero] at hsum
  have hsub : ∀ e ∈ S, e ∈ D.lineChain (-f) (-c) ∧ (D.tile e.1).edge e.2 ⊆ segment ℝ P G := by
    intro e he
    have := Finset.mem_filter.mp he
    rw [hend, zero_smul, add_zero] at this
    exact this
  obtain ⟨X', Y', Z', hXYZ, hcard⟩ := Erdos634.Geometry.sum_three_values S
    (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) (A:ℝ) (B:ℝ) (C:ℝ)
    (fun e _ => habc e.1 e.2)
  rw [hsum] at hXYZ
  have hnat : X' * A + Y' * B + Z' * C = B := by
    have : ((X' * A + Y' * B + Z' * C : ℕ) : ℝ) = (B : ℝ) := by push_cast; linarith
    exact_mod_cast this
  obtain ⟨hx0, hy1, hz0⟩ := hcover X' Y' Z' hnat
  have hcard1 : S.card = 1 := by omega
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hcard1
  have heS : e ∈ S := by rw [he]; simp
  obtain ⟨hechain, heseg⟩ := hsub e heS
  have hdistB : dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = (B:ℝ) := by
    have := hsum
    rw [he, Finset.sum_singleton] at this
    linarith
  have hp : (D.tile e.1).pts e.2 ∈ segment ℝ P G :=
    heseg (left_mem_segment ℝ _ _)
  have hq : (D.tile e.1).pts (e.2 + 1) ∈ segment ℝ P G :=
    heseg (right_mem_segment ℝ _ _)
  have hends := ends_of_segment hne hp hq (by rw [hdistB, hPG])
  refine ⟨e.1, e.2, ?_, hdistB, hends⟩
  intro h1
  have hmem := (Dissection.mem_lineChain.mp hechain).2.2 (j1 + 2)
  rw [h1] at hmem
  simp only [LinearMap.neg_apply] at hmem
  linarith

/-- If the line `PG` leaves the target beyond `G`, no far-side edge passes through `G`. -/
theorem nstr_end_outside (D : Dissection N) {P G : Plane} (hne : P ≠ G)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf0 : f ≠ 0) (hfP : f P = c) (hfG : f G = c)
    (hout : ∀ t : ℝ, 1 < t → AffineMap.lineMap P G t ∉ D.target.carrier) :
    ¬ Straddled D (-f) (-c) G := by
  have hB : 0 < dist P G := dist_pos.mpr hne
  set B := dist P G with hBdef
  set u : Plane := B⁻¹ • (G - P) with hu
  have hu0 : u ≠ 0 := smul_ne_zero (inv_ne_zero hB.ne') (sub_ne_zero.mpr (Ne.symm hne))
  have hfu : f u = 0 := by rw [hu, map_smul, map_sub, hfG, hfP]; simp
  have hend : P + B • u = G := by rw [hu, smul_smul, mul_inv_cancel₀ hB.ne', one_smul]; abel
  have hgd : ∀ y, (-f) y = -c ↔ f y = c := neg_iff
  have := not_straddled_of_outside_after (D := D) hgd hf0 hfP hfu hu0 (x₀ := B) (fun t ht => by
    rw [hu, line_param P G hB.ne' t]
    exact hout _ ((one_lt_div hB).mpr ht))
  rwa [hend] at this

/-- If a tile contains `G` and has points strictly on both sides of the line `PG`, no far-side
edge passes through `G`. -/
theorem nstr_end_across (D : Dissection N) {P G : Plane} (hne : P ≠ G)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf0 : f ≠ 0) (hfP : f P = c) (hfG : f G = c)
    (iU : Fin N) (hGU : G ∈ (D.tile iU).carrier) {p' q' : Plane}
    (hp : p' ∈ (D.tile iU).carrier) (hq : q' ∈ (D.tile iU).carrier)
    (hpc : f p' < c) (hqc : c < f q') :
    ¬ Straddled D (-f) (-c) G := by
  have hB : 0 < dist P G := dist_pos.mpr hne
  set B := dist P G with hBdef
  set u : Plane := B⁻¹ • (G - P) with hu
  have hu0 : u ≠ 0 := smul_ne_zero (inv_ne_zero hB.ne') (sub_ne_zero.mpr (Ne.symm hne))
  have hfu : f u = 0 := by rw [hu, map_smul, map_sub, hfG, hfP]; simp
  have hend : P + B • u = G := by rw [hu, smul_smul, mul_inv_cancel₀ hB.ne', one_smul]; abel
  have hgd : ∀ y, (-f) y = -c ↔ f y = c := neg_iff
  have hY : P + B • u ∈ (D.tile iU).carrier := by rwa [hend]
  have hnear := near_interior_of_across (D.tile iU) hf0 hfP hfu hu0 hY hp hq hpc hqc
  have := not_straddled_of_near_interior (D := D) hgd hf0 hfP hfu hu0 (x₀ := B) (fun δ hδ => by
    obtain ⟨x, h1, h2⟩ := hnear δ hδ
    exact ⟨x, h1, iU, h2⟩)
  rwa [hend] at this

/-- **The far side of a tile-edge chord between two target sides** (`G` on a side). -/
theorem far_edge_exists (D : Dissection N) {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) (A B C : ℕ)
    (hcover : ∀ x y z : ℕ, x * A + y * B + z * C = B → x = 0 ∧ y = 1 ∧ z = 0)
    (habc : ∀ (i : Fin N) (k : Fin 3),
      dist ((D.tile i).pts k) ((D.tile i).pts (k+1)) = (A : ℝ) ∨
      dist ((D.tile i).pts k) ((D.tile i).pts (k+1)) = (B : ℝ) ∨
      dist ((D.tile i).pts k) ((D.tile i).pts (k+1)) = (C : ℝ))
    {P G : Plane}
    (hP : P ∈ openSegment ℝ (D.target.pts p) (D.target.pts q))
    (hG : G ∈ openSegment ℝ (D.target.pts p) (D.target.pts r))
    (hPG : dist P G = (B : ℝ)) (hB : 0 < B)
    (i1 : Fin N) (j1 : Fin 3) (hPv : (D.tile i1).pts j1 = P) (hGv : (D.tile i1).pts (j1+1) = G) :
    ∃ (i' : Fin N) (k : Fin 3), i' ≠ i1 ∧
      dist ((D.tile i').pts k) ((D.tile i').pts (k+1)) = (B : ℝ) ∧
      (((D.tile i').pts k = P ∧ (D.tile i').pts (k+1) = G) ∨
       ((D.tile i').pts k = G ∧ (D.tile i').pts (k+1) = P)) := by
  obtain ⟨hint, hbef, haft⟩ := chord_geometry D.target hpq hpr hqr hP hG
  have hBr : (0:ℝ) < B := by exact_mod_cast hB
  have hne : P ≠ G := by
    intro h; rw [h, dist_self] at hPG; linarith
  exact far_edge_gen D A B C hcover habc hint hbef hPG hB i1 j1 hPv hGv
    (fun f c hf0 hfP hfG _ => nstr_end_outside D hne f c hf0 hfP hfG haft)

end Erdos634.LaczJunction
