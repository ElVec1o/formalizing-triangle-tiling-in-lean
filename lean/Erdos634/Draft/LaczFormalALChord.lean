import Erdos634.Draft.LaczFormalALCell

/-!
# Lattice chords: interior and exit from the target (a-lattice)

Erdős \#634, base-`β` row, thick analogue of `M(j)` (Lemma A(j)).  Credit: AI assistant (Lemma A(k) proposal), Beeson–Roșu,
Beeson, Laczkovich, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.  Port of `LaczFormalMJChord.lean` to the exchanged frame
`AF` (`e0` of length `a` along the base, `v` of length `c` along the left leg).
-/

namespace Erdos634.LaczAL

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.TraceCovering Erdos634.LaczMJ Set

variable {N : ℕ}

namespace AF

variable {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
  (F : AF D e f α β γ p q r)

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

end AF

end Erdos634.LaczAL
