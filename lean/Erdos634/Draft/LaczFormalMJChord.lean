import Erdos634.Draft.LaczFormalMJCover

/-!
# Lattice chords: interior, exit from the target, edges of cells

Erdős #634, base-`β` band, rule `M(j)`.  Credit: AI assistant (item 3, band program), Beeson–Roșu, Beeson,
Laczkovich (chord covers), Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.

For lattice points `P = pt x1 y1`, `G = pt x2 y2` of an `LFrame`:
* `pt_lineMap`: `lineMap P G τ` is again a lattice point (affine coordinates);
* `LatOK`: `x, y ≥ 0`, `x/λ + y/μ < 1` (the lattice point is in the target, not on its third side);
  `chord_interior`: an open chord between two `LatOK` points with `x1 + x2 > 0` and `y1 + y2 > 0` lies in the
  interior of the target;
* `pt_not_mem_x`, `pt_not_mem_y`: a lattice point with `x < 0` (or `y < 0`) is outside the target;
  `ns_end_x`, `ns_start_y`: a chord whose line leaves the target immediately beyond its end is not straddled there;
* `TileVerts.edge_AB` etc.: the edges of a tile with three given vertices; `chain_cover`: a polygonal chain of
  tile edges covers the segment it spans.
-/

namespace Erdos634.LaczMJ

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.TraceCovering Set

variable {N : ℕ}

theorem pos_comb {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) (h0 : 0 < t) (h1 : t < 1) :
    0 < a + t * (b - a) := by
  rcases ha.eq_or_lt with h | h
  · subst h
    have : 0 < b := by linarith
    nlinarith [mul_pos h0 this]
  · nlinarith [mul_pos (sub_pos.2 h1) h, mul_nonneg h0.le hb]

namespace LFrame

variable {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
  (F : LFrame D e f α β γ p q r)

theorem pt_lineMap (x1 y1 x2 y2 τ : ℝ) :
    AffineMap.lineMap (F.pt x1 y1) (F.pt x2 y2) τ =
      F.pt (x1 + τ * (x2 - x1)) (y1 + τ * (y2 - y1)) := by
  rw [AffineMap.lineMap_apply]
  simp only [pt, vsub_eq_sub, vadd_eq_add]
  module

/-- A lattice point of the target: `x, y ≥ 0` and `x/λ + y/μ < 1`. -/
def LatOK (x y : ℝ) : Prop := 0 ≤ x ∧ 0 ≤ y ∧ x / F.lam + y / F.mu < 1

theorem pt_not_mem_x {x y : ℝ} (hx : x < 0) : F.pt x y ∉ D.target.carrier := by
  intro h
  rw [D.target.carrier_eq_nonneg_coord] at h
  have := h q
  rw [F.coord_pt] at this
  have hpq := F.S.hpq
  have hqr := F.S.hqr
  simp [coord_vertex, hpq, hpq.symm, hqr] at this
  have : x / F.lam < 0 := div_neg_of_neg_of_pos hx F.hlam
  linarith

theorem pt_not_mem_y {x y : ℝ} (hy : y < 0) : F.pt x y ∉ D.target.carrier := by
  intro h
  rw [D.target.carrier_eq_nonneg_coord] at h
  have := h r
  rw [F.coord_pt] at this
  have hpr := F.S.hpr
  have hqr := F.S.hqr
  simp [coord_vertex, hpr, hpr.symm, hqr.symm] at this
  have : y / F.mu < 0 := div_neg_of_neg_of_pos hy F.hmu
  linarith

/-- Open chords between `LatOK` lattice points lie in the interior of the target. -/
theorem chord_interior {x1 y1 x2 y2 : ℝ} (h1 : F.LatOK x1 y1) (h2 : F.LatOK x2 y2)
    (hx : 0 < x1 + x2) (hy : 0 < y1 + y2) :
    ∀ t : ℝ, 0 < t → t < 1 →
      AffineMap.lineMap (F.pt x1 y1) (F.pt x2 y2) t ∈ interior D.target.carrier := by
  intro t ht0 ht1
  rw [F.pt_lineMap]
  obtain ⟨a1, b1, c1⟩ := h1
  obtain ⟨a2, b2, c2⟩ := h2
  have hl := F.hlam
  have hm := F.hmu
  refine F.pt_interior ?_ ?_ ?_
  · exact pos_comb a1 a2 hx ht0 ht1
  · exact pos_comb b1 b2 hy ht0 ht1
  · have e1 : (x1 + t * (x2 - x1)) / F.lam + (y1 + t * (y2 - y1)) / F.mu =
        (1 - t) * (x1 / F.lam + y1 / F.mu) + t * (x2 / F.lam + y2 / F.mu) := by
      field_simp; ring
    rw [e1]
    nlinarith

/-- `ns_end_x`: the chord `P → G` with `G = pt x2 y2`, `x2 ≤ 0 < x1` and `x2 < x1`: the line leaves the target
immediately beyond `G`, so no edge of any chain passes through `G`. -/
theorem ns_end_x {x1 y1 x2 y2 : ℝ} (hx2 : x2 ≤ 0) (hlt : x2 < x1)
    (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hg0 : g ≠ 0) (hgP : g (F.pt x1 y1) = c) (hgG : g (F.pt x2 y2) = c) :
    ¬ Straddled D.toDissection g c (F.pt x2 y2) := by
  have hne : F.pt x1 y1 ≠ F.pt x2 y2 := by
    intro h
    have := congrArg (fun z => D.target.basis.coord q z) h
    simp only [F.coord_pt] at this
    have hpq := F.S.hpq
    have hqr := F.S.hqr
    simp [coord_vertex, hpq, hpq.symm, hqr] at this
    have := F.hlam
    have : x1 = x2 := by
      field_simp at *
      linarith
    linarith
  have hBr : 0 < dist (F.pt x1 y1) (F.pt x2 y2) := dist_pos.mpr hne
  set P := F.pt x1 y1
  set G := F.pt x2 y2
  set B := dist P G with hBdef
  set u : Plane := B⁻¹ • (G - P) with hu
  have hgu : g u = 0 := by rw [hu, map_smul, map_sub, hgG, hgP]; simp
  have hu0 : u ≠ 0 := smul_ne_zero (inv_ne_zero hBr.ne') (sub_ne_zero.mpr (Ne.symm hne))
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, Real.norm_of_nonneg hBr.le, ← dist_eq_norm, dist_comm, ← hBdef]
    field_simp
  have hend : P + B • u = G := by
    rw [hu, smul_smul, mul_inv_cancel₀ hBr.ne', one_smul]; abel
  have := not_straddled_of_outside_after (D := D.toDissection) (X := P) (u := u) (f := g) (g := g)
    (c := c) (d := c) (fun _ => Iff.rfl) hg0 hgP hgu hu0 (x₀ := B) (by
      intro t ht
      rw [hu, line_param P G hBr.ne' t]
      show AffineMap.lineMap (F.pt x1 y1) (F.pt x2 y2) (t / B) ∉ D.target.carrier
      rw [F.pt_lineMap]
      apply F.pt_not_mem_x
      have h1 : 1 < t / B := (one_lt_div hBr).mpr ht
      nlinarith)
  rwa [hend] at this

theorem ns_start_y {x1 y1 x2 y2 : ℝ} (hy1 : y1 ≤ 0) (hlt : y1 < y2)
    (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hg0 : g ≠ 0) (hgP : g (F.pt x1 y1) = c) (hgG : g (F.pt x2 y2) = c) :
    ¬ Straddled D.toDissection g c (F.pt x1 y1) := by
  have hne : F.pt x1 y1 ≠ F.pt x2 y2 := by
    intro h
    have := congrArg (fun z => D.target.basis.coord r z) h
    simp only [F.coord_pt] at this
    have hpr := F.S.hpr
    have hqr := F.S.hqr
    simp [coord_vertex, hpr, hpr.symm, hqr.symm] at this
    have := F.hmu
    have : y1 = y2 := by
      field_simp at *
      linarith
    linarith
  have hBr : 0 < dist (F.pt x1 y1) (F.pt x2 y2) := dist_pos.mpr hne
  set P := F.pt x1 y1
  set G := F.pt x2 y2
  set B := dist P G with hBdef
  set u : Plane := B⁻¹ • (G - P) with hu
  have hgu : g u = 0 := by rw [hu, map_smul, map_sub, hgG, hgP]; simp
  have hu0 : u ≠ 0 := smul_ne_zero (inv_ne_zero hBr.ne') (sub_ne_zero.mpr (Ne.symm hne))
  have := not_straddled_of_outside_before (D := D.toDissection) (X := P) (u := u) (f := g) (g := g)
    (c := c) (d := c) (fun _ => Iff.rfl) hg0 hgP hgu hu0 (x₀ := 0) (by
      intro t ht
      rw [hu, line_param P G hBr.ne' t]
      show AffineMap.lineMap (F.pt x1 y1) (F.pt x2 y2) (t / B) ∉ D.target.carrier
      rw [F.pt_lineMap]
      apply F.pt_not_mem_y
      have h1 : t / B < 0 := div_neg_of_neg_of_pos ht hBr
      nlinarith)
  simpa using this

end LFrame

/-! ## Edges of tiles with given vertices; chains of edges -/

theorem _root_.Erdos634.LaczJunction.TileVerts.edge_AB {T : Tri} {A B C : Plane} (h : TileVerts T A B C) :
    ∃ k : Fin 3, T.edge k = segment ℝ A B := by
  obtain ⟨j, ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩⟩ := h
  · exact ⟨j, by simp only [Tri.edge, h1, h2]⟩
  · refine ⟨j + 2, ?_⟩
    have : j + 2 + 1 = j := by fin_cases j <;> rfl
    simp only [Tri.edge, this, h1, h3]
    exact segment_symm ℝ _ _

theorem _root_.Erdos634.LaczJunction.TileVerts.edge_BC {T : Tri} {A B C : Plane} (h : TileVerts T A B C) :
    ∃ k : Fin 3, T.edge k = segment ℝ B C := h.rot.edge_AB

theorem _root_.Erdos634.LaczJunction.TileVerts.edge_AC {T : Tri} {A B C : Plane} (h : TileVerts T A B C) :
    ∃ k : Fin 3, T.edge k = segment ℝ A C := h.swap23.edge_AB

/-- A chain of tile edges `[q t, q (t+1)]`, `t < s`, covers the segment of the points `q τ`, `0 ≤ τ ≤ s`. -/
theorem chain_cover (D : Dissection N) (q : ℝ → Plane) (P0 w : Plane) (hq : ∀ τ, q τ = P0 + τ • w) (s : ℕ)
    (hs : 0 < s)
    (hedge : ∀ t : ℕ, t < s → ∃ (i : Fin N) (k : Fin 3), (D.tile i).edge k = segment ℝ (q t) (q (t + 1)))
    {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ s) :
    ∃ (i : Fin N) (k : Fin 3), q τ ∈ (D.tile i).edge k := by
  set t : ℕ := min ⌊τ⌋₊ (s - 1) with ht
  have hts : t < s := by have := min_le_right ⌊τ⌋₊ (s - 1); omega
  obtain ⟨i, k, hik⟩ := hedge t hts
  refine ⟨i, k, ?_⟩
  rw [hik]
  have hfl : (⌊τ⌋₊ : ℝ) ≤ τ := Nat.floor_le h0
  have hlo : (t : ℝ) ≤ τ := le_trans (by exact_mod_cast min_le_left _ _) hfl
  have hhi : τ ≤ (t : ℝ) + 1 := by
    rcases min_choice ⌊τ⌋₊ (s - 1) with h | h
    · have := Nat.lt_floor_add_one τ
      rw [ht, h]; linarith
    · have hs1 : ((s - 1 : ℕ) : ℝ) + 1 = s := by
        rw [Nat.cast_sub hs]; push_cast; ring
      rw [ht, h]; linarith
  refine ⟨1 - (τ - t), τ - t, by linarith, by linarith, by ring, ?_⟩
  rw [hq, hq, hq]
  push_cast
  module

end Erdos634.LaczMJ
