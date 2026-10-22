import Erdos634.Draft.LaczFormalJunctionWall
import Erdos634.Draft.LaczFormalW2Arith

/-!
# Lemma L3 (covering of the far side of a wall), for a chord of any length

Erdős #634, base-`β` band.  Credit: AI assistant (item 3, band program, the lemma L3 of PROOF_C1), Beeson–Roșu,
Beeson, Laczkovich (fan/chord covers), Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.

`far_edge_gen` (LaczFormalJunctionWall) is L3 for a chord whose length is one side `B`: the far side is
a single `B`-edge.  The proof there first produces the *sum* identity (the far-side tile edges lying in
the chord have total length `|PG|`, `wall_sum`) and only then specialises.  The hand proof of rule W2
(`PROOF_W2.md`) uses L3 for three chords of other lengths (`b`, `2b`, `c`), the `2b` chord `P₂V₂` being the
one with two edges.  This file states L3 exactly in its general form and proves it from `wall_sum`:

* `L3_sum`: if the open chord `(P,G)` is inside the target, the line beyond `P` leaves the target, no
  tile has a chord point in its interior (the near side is a union of tile edges), and no far-side
  edge passes through `G`, then the far-side edges contained in `[P,G]` have total length `|PG|`.
* `L3_sum_of_edges`: the same with the near side given as "every chord point lies on a tile edge".
* `L3_two_b`: for `|PG| = 2B` with `2B = xA + yB + zC ⇒ (x,y,z) = (0,2,0)` (`D2_two_b`), exactly two
  far-side edges lie in the chord and each has length `B` (not an `A`/`C`-edge, not three, not one).
* The single-edge case (`|PG| = B`, or `C` by `D3_c_unique`) is `far_edge_gen` / the same argument with
  `hcover` replaced; for the `c`-chord of W2 only the sum form `L3_sum` is stated here.

What is *not* here: the positions (that the two edges abut at the midpoint `P + B u`), and the
tile-placement part of the W2 proof (forcing `T'=(P₁,G₁,G₂)`, the wedge fillings, the overlap arguments).
-/

namespace Erdos634.LaczJunction

open Erdos634.Geometry Erdos634.Draft.TraceCovering Set

variable {N : ℕ}

open Classical in
/-- **L3, general length (sum form).** -/
theorem L3_sum (D : Dissection N) {P G : Plane} (hne : P ≠ G)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf0 : f ≠ 0) (hfP : f P = c) (hfG : f G = c)
    (hint : ∀ t : ℝ, 0 < t → t < 1 → AffineMap.lineMap P G t ∈ interior D.target.carrier)
    (hbef : ∀ t : ℝ, t < 0 → AffineMap.lineMap P G t ∉ D.target.carrier)
    (hwall : ∀ t : ℝ, 0 < t → t < 1 → ∀ i, AffineMap.lineMap P G t ∉ interior (D.tile i).carrier)
    (hGend : ¬ Straddled D (-f) (-c) G) :
    ∑ e ∈ (D.lineChain (-f) (-c)).filter
        (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ P G),
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = dist P G := by
  have hBr : 0 < dist P G := dist_pos.mpr hne
  set B := dist P G with hBdef
  have hu0 : B⁻¹ • (G - P) ≠ 0 := by
    apply smul_ne_zero (inv_ne_zero hBr.ne')
    exact sub_ne_zero.mpr (Ne.symm hne)
  set u : Plane := B⁻¹ • (G - P) with hu
  have hfu : f u = 0 := by
    rw [hu, map_smul, map_sub, hfG, hfP]; simp
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, Real.norm_of_nonneg hBr.le, ← dist_eq_norm, dist_comm, ← hBdef]
    field_simp
  have hend : P + B • u = G := by
    rw [hu, smul_smul, mul_inv_cancel₀ hBr.ne', one_smul]; abel
  have hgd : ∀ y, (-f) y = -c ↔ f y = c := neg_iff
  have hnf : (-f : Plane →ₗ[ℝ] ℝ) ≠ 0 := fun h => hf0 (neg_eq_zero.mp h)
  have hsum := wall_sum (D := D) (X := P) (u := u) (f := f) (g := -f) (c := c) (d := -c) hnf hgd hf0
    hfP hfu hu1 (s := 0) (t := B) hBr.le
    (fun x hx => by
      rw [hu, line_param P G hBr.ne' x]
      exact hint _ (div_pos hx.1 hBr) ((div_lt_one hBr).mpr hx.2))
    (fun x hx i => by
      rw [hu, line_param P G hBr.ne' x]
      exact hwall _ (div_pos hx.1 hBr) ((div_lt_one hBr).mpr hx.2) i)
    (not_straddled_of_outside_before hgd hf0 hfP hfu hu0 (x₀ := 0) (fun t ht => by
      rw [hu, line_param P G hBr.ne' t]
      exact hbef _ (div_neg_of_neg_of_pos ht hBr)))
    (by rw [hend]; exact hGend)
  rw [sub_zero, hend, zero_smul, add_zero] at hsum
  exact hsum

open Classical in
/-- **L3, near side given by tile edges.** -/
theorem L3_sum_of_edges (D : Dissection N) {P G : Plane} (hne : P ≠ G)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf0 : f ≠ 0) (hfP : f P = c) (hfG : f G = c)
    (hint : ∀ t : ℝ, 0 < t → t < 1 → AffineMap.lineMap P G t ∈ interior D.target.carrier)
    (hbef : ∀ t : ℝ, t < 0 → AffineMap.lineMap P G t ∉ D.target.carrier)
    (hnear : ∀ t : ℝ, 0 < t → t < 1 → ∃ (i : Fin N) (k : Fin 3),
      AffineMap.lineMap P G t ∈ (D.tile i).edge k)
    (hGend : ¬ Straddled D (-f) (-c) G) :
    ∑ e ∈ (D.lineChain (-f) (-c)).filter
        (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ P G),
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = dist P G := by
  refine L3_sum D hne f c hf0 hfP hfG hint hbef (fun t h0 h1 i => ?_) hGend
  obtain ⟨j, k, hmem⟩ := hnear t h0 h1
  exact D.edge_point_not_interior hmem i

open Classical in
/-- **L3 for a `2B` chord**: exactly two far-side edges, both of length `B`. -/
theorem L3_two_b (D : Dissection N) (A B C : ℕ)
    (hcover : ∀ x y z : ℕ, x * A + y * B + z * C = 2 * B → x = 0 ∧ y = 2 ∧ z = 0)
    (habc : ∀ (i : Fin N) (k : Fin 3),
      dist ((D.tile i).pts k) ((D.tile i).pts (k+1)) = (A : ℝ) ∨
      dist ((D.tile i).pts k) ((D.tile i).pts (k+1)) = (B : ℝ) ∨
      dist ((D.tile i).pts k) ((D.tile i).pts (k+1)) = (C : ℝ))
    {P G : Plane} (hne : P ≠ G) (hPG : dist P G = 2 * (B : ℝ))
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf0 : f ≠ 0) (hfP : f P = c) (hfG : f G = c)
    (hint : ∀ t : ℝ, 0 < t → t < 1 → AffineMap.lineMap P G t ∈ interior D.target.carrier)
    (hbef : ∀ t : ℝ, t < 0 → AffineMap.lineMap P G t ∉ D.target.carrier)
    (hwall : ∀ t : ℝ, 0 < t → t < 1 → ∀ i, AffineMap.lineMap P G t ∉ interior (D.tile i).carrier)
    (hGend : ¬ Straddled D (-f) (-c) G) :
    ∃ e₁ e₂ : Fin N × Fin 3, e₁ ≠ e₂ ∧ e₁ ∈ D.lineChain (-f) (-c) ∧ e₂ ∈ D.lineChain (-f) (-c) ∧
      (D.tile e₁.1).edge e₁.2 ⊆ segment ℝ P G ∧ (D.tile e₂.1).edge e₂.2 ⊆ segment ℝ P G ∧
      dist ((D.tile e₁.1).pts e₁.2) ((D.tile e₁.1).pts (e₁.2 + 1)) = (B : ℝ) ∧
      dist ((D.tile e₂.1).pts e₂.2) ((D.tile e₂.1).pts (e₂.2 + 1)) = (B : ℝ) := by
  have hsum := L3_sum D hne f c hf0 hfP hfG hint hbef hwall hGend
  set S := (D.lineChain (-f) (-c)).filter
    (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ P G) with hS
  obtain ⟨X', Y', Z', hXYZ, hcard⟩ := Erdos634.Geometry.sum_three_values S
    (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) (A:ℝ) (B:ℝ) (C:ℝ)
    (fun e _ => habc e.1 e.2)
  rw [hsum, hPG] at hXYZ
  have hnat : X' * A + Y' * B + Z' * C = 2 * B := by
    have : ((X' * A + Y' * B + Z' * C : ℕ) : ℝ) = ((2 * B : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  obtain ⟨hx0, hy2, hz0⟩ := hcover X' Y' Z' hnat
  have hcard2 : S.card = 2 := by omega
  obtain ⟨e₁, e₂, hne12, hSe⟩ := Finset.card_eq_two.mp hcard2
  have h1 : e₁ ∈ S := by rw [hSe]; simp
  have h2 : e₂ ∈ S := by rw [hSe]; simp
  have hsum2 : dist ((D.tile e₁.1).pts e₁.2) ((D.tile e₁.1).pts (e₁.2 + 1)) +
      dist ((D.tile e₂.1).pts e₂.2) ((D.tile e₂.1).pts (e₂.2 + 1)) = 2 * (B : ℝ) := by
    rw [← hPG, ← hsum, hSe, Finset.sum_pair hne12]
  have hnat2 : ∀ x y z : ℕ, ((x * A + y * B + z * C : ℕ) : ℝ) = 2 * (B : ℝ) →
      x = 0 ∧ y = 2 ∧ z = 0 := by
    intro x y z h
    apply hcover
    exact_mod_cast (by push_cast at h ⊢; linarith : ((x * A + y * B + z * C : ℕ) : ℝ) = ((2 * B : ℕ) : ℝ))
  have hkey : ∀ x y : ℝ, (x = A ∨ x = B ∨ x = C) → (y = A ∨ y = B ∨ y = C) →
      x + y = 2 * (B : ℝ) → x = B ∧ y = B := by
    intro x y hx hy hxy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · have := hnat2 2 0 0 (by push_cast; linarith); exfalso; omega
    · have := hnat2 1 1 0 (by push_cast; linarith); exfalso; omega
    · have := hnat2 1 0 1 (by push_cast; linarith); exfalso; omega
    · have := hnat2 1 1 0 (by push_cast; linarith); exfalso; omega
    · exact ⟨rfl, by linarith⟩
    · have := hnat2 0 1 1 (by push_cast; linarith); exfalso; omega
    · have := hnat2 1 0 1 (by push_cast; linarith); exfalso; omega
    · have := hnat2 0 1 1 (by push_cast; linarith); exfalso; omega
    · have := hnat2 0 0 2 (by push_cast; linarith); exfalso; omega
  obtain ⟨k1, k2⟩ := hkey _ _ (habc e₁.1 e₁.2) (habc e₂.1 e₂.2) hsum2
  have hm1 := Finset.mem_filter.mp h1
  have hm2 := Finset.mem_filter.mp h2
  exact ⟨e₁, e₂, hne12, hm1.1, hm2.1, hm1.2, hm2.2, k1, k2⟩

#print axioms L3_sum
#print axioms L3_two_b

end Erdos634.LaczJunction
