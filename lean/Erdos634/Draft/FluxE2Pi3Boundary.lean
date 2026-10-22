-- Draft/FluxE2Pi3Boundary.lean — the general 2π/3-grid TRIANGLE-BOUNDARY closed-form lemma, for a
-- triangle whose three angles sit at ARBITRARY named grid coordinates (j₀,k₀), (j₁,k₁), (j₂,k₂) of
-- the paper's own grid Λ = ℤ(π/3) + ℤα (Draft/FluxPaper.lean's `GridChar.rankn 3 … α … `, already
-- VERIFIED there, P45/A25 — NOT rebuilt here).  This is the direct generalization of
-- `Draft/FluxPaper.lean`'s `Tri.TwoPiThreeData` / `data_angles_mem` / `data_tileValue` (which fix
-- the tile's own three angles `(α, π/3−α, 2π/3)`) to an arbitrary named triple of grid angles, which
-- is exactly what a TARGET triangle needs (its three corner angles are not the tile's).
--
-- Task file 1 of 3 (FluxE2Pi3Row7.lean, FluxE2Pi3Row9.lean apply this to the two named targets).
-- Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).  Formalization debt on the prime-case VERIFIED path; not progress on
-- the three /goal outcomes.
--
-- Design note: `Draft/FluxCBoundary.lean` builds a SYMBOLIC boundary lemma (any `GridChar`, value
-- expressed via `paperK`/`edgeSign`, no explicit closed form) for the `3α+2β` grid's consumers. That
-- machinery is grid-agnostic and could be reused for `fAlpha`/`fBeta` too, but it does not by itself
-- produce the paper's explicit `±μ(2a+b−c)`-style formulas — those come from reading off each
-- vertex's own `(j,k)` grid coordinate, exactly as `Draft/FluxPaper.lean`'s `data_tileValue` does for
-- the tile.  This file repeats that SAME technique (cited: `Tri.flux_grid_pm`, `GridChar.rankn_mem`,
-- `GridChar.rankn_chi`, `GridChar.rankn_sq`), generalized from the tile's fixed angle triple to an
-- arbitrary one, so Row7/Row9 need only plug in six integers and three side lengths.
import Erdos634.Draft.FluxPaper

open scoped Classical

namespace Erdos634.Geometry

/-! ## A triangle whose three angles sit at named grid coordinates -/

/-- **A triangle placed at named grid coordinates.**  Under some vertex order `σ`, vertex `i` has
angle `jᵢ·π/3 + kᵢ·α` with opposite side `sᵢ`.  (`Tri.TwoPiThreeData` is the special case
`(j,k) = (0,1), (1,-1), (2,0)`, `s = (a,b,c)`.) -/
def Tri.GridTriData (T : Tri) (α : ℝ) (j0 k0 j1 k1 j2 k2 : ℤ) (s0 s1 s2 : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3),
    T.angleAt (σ 0) = (j0 : ℝ) * (Real.pi / 3) + (k0 : ℝ) * α ∧ T.oppLen (σ 0) = s0 ∧
    T.angleAt (σ 1) = (j1 : ℝ) * (Real.pi / 3) + (k1 : ℝ) * α ∧ T.oppLen (σ 1) = s1 ∧
    T.angleAt (σ 2) = (j2 : ℝ) * (Real.pi / 3) + (k2 : ℝ) * α ∧ T.oppLen (σ 2) = s2

/-- Every angle of a `GridTriData` triangle lies in the paper's `Λ = ℤ(π/3) + ℤα` grid, for any
choice of "which weight" `b'` (`b' = 0` gives `fAlpha`'s grid, `b' = 1` gives `fBeta`'s — both are
the same subgroup `L`, the characters differ only in `chi`). -/
theorem Tri.gridTriData_angles_mem {T : Tri} {α : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {j0 k0 j1 k1 j2 k2 : ℤ} {s0 s1 s2 : ℝ} (h : T.GridTriData α j0 k0 j1 k1 j2 k2 s0 s1 s2)
    (b' : ZMod 2) :
    ∀ i, ((T.angleAt i : ℝ) : Real.Angle)
      ∈ (GridChar.rankn 3 (by norm_num) (by decide) α hα b' 0).L := by
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := h
  intro i
  obtain ⟨m, rfl⟩ := σ.surjective i
  have hm : m = 0 ∨ m = 1 ∨ m = 2 := by fin_cases m <;> simp
  rcases hm with rfl | rfl | rfl
  · rw [h0, show ((j0 : ℝ) * (Real.pi / 3) + (k0 : ℝ) * α : ℝ)
        = (((j0 : ℝ)) * (Real.pi / ((3 : ℕ) : ℝ)) + ((k0 : ℝ)) * α : ℝ) by push_cast; ring]
    exact GridChar.rankn_mem _ _ _ _ _ _ _ _ _
  · rw [h1, show ((j1 : ℝ) * (Real.pi / 3) + (k1 : ℝ) * α : ℝ)
        = (((j1 : ℝ)) * (Real.pi / ((3 : ℕ) : ℝ)) + ((k1 : ℝ)) * α : ℝ) by push_cast; ring]
    exact GridChar.rankn_mem _ _ _ _ _ _ _ _ _
  · rw [h2, show ((j2 : ℝ) * (Real.pi / 3) + (k2 : ℝ) * α : ℝ)
        = (((j2 : ℝ)) * (Real.pi / ((3 : ℕ) : ℝ)) + ((k2 : ℝ)) * α : ℝ) by push_cast; ring]
    exact GridChar.rankn_mem _ _ _ _ _ _ _ _ _

/-- **The closed-form tile value at named grid coordinates.**  Reading the exterior angle
`π − (jπ/3+kα) = (3−j)π/3 + (−k)α` at each vertex, exactly as `Draft/FluxPaper.lean`'s
`data_tileValue` does for the fixed tile triple. -/
theorem Tri.gridTriData_tileValue (T : Tri) {α : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {j0 k0 j1 k1 j2 k2 : ℤ} {s0 s1 s2 : ℝ}
    (h : T.GridTriData α j0 k0 j1 k1 j2 k2 s0 s1 s2) (b' : ZMod 2) :
    (GridChar.rankn 3 (by norm_num) (by decide) α hα b' 0).tileValue T
      = (if ((3 - j0 : ℤ) : ZMod 2) + b' * ((-k0 : ℤ) : ZMod 2) = 0 then 1 else -1) * s0
        + (if ((3 - j1 : ℤ) : ZMod 2) + b' * ((-k1 : ℤ) : ZMod 2) = 0 then 1 else -1) * s1
        + (if ((3 - j2 : ℤ) : ZMod 2) + b' * ((-k2 : ℤ) : ZMod 2) = 0 then 1 else -1) * s2 := by
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  unfold GridChar.tileValue
  rw [← Equiv.sum_comp σ (fun i => (GridChar.rankn 3 (by norm_num) (by decide) α hα b' 0).chi
    ((Real.pi - T.angleAt i : ℝ) : Real.Angle) * T.oppLen i), Fin.sum_univ_three]
  rw [h0, o0, h1, o1, h2, o2,
    show Real.pi - ((j0 : ℝ) * (Real.pi / 3) + (k0 : ℝ) * α)
        = ((3 - j0 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((-k0 : ℤ) : ℝ) * α by push_cast; ring,
    show Real.pi - ((j1 : ℝ) * (Real.pi / 3) + (k1 : ℝ) * α)
        = ((3 - j1 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((-k1 : ℤ) : ℝ) * α by push_cast; ring,
    show Real.pi - ((j2 : ℝ) * (Real.pi / 3) + (k2 : ℝ) * α)
        = ((3 - j2 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((-k2 : ℤ) : ℝ) * α by push_cast; ring,
    GridChar.rankn_chi, GridChar.rankn_chi, GridChar.rankn_chi]

/-- **THE 2π/3-GRID TRIANGLE-BOUNDARY LEMMA.**  A `GridTriData` triangle's flux under either
`fAlpha`-shaped or `fBeta`-shaped weight (`b' = 0` or `1` respectively) is `±` the named closed
form. -/
theorem Tri.gridTriData_flux_pm (T : Tri) {α : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {j0 k0 j1 k1 j2 k2 : ℤ} {s0 s1 s2 : ℝ}
    (h : T.GridTriData α j0 k0 j1 k1 j2 k2 s0 s1 s2) (b' : ZMod 2) :
    T.flux (GridChar.rankn 3 (by norm_num) (by decide) α hα b' 0).weight
        = (if ((3 - j0 : ℤ) : ZMod 2) + b' * ((-k0 : ℤ) : ZMod 2) = 0 then 1 else -1) * s0
          + (if ((3 - j1 : ℤ) : ZMod 2) + b' * ((-k1 : ℤ) : ZMod 2) = 0 then 1 else -1) * s1
          + (if ((3 - j2 : ℤ) : ZMod 2) + b' * ((-k2 : ℤ) : ZMod 2) = 0 then 1 else -1) * s2
      ∨ T.flux (GridChar.rankn 3 (by norm_num) (by decide) α hα b' 0).weight
        = -((if ((3 - j0 : ℤ) : ZMod 2) + b' * ((-k0 : ℤ) : ZMod 2) = 0 then 1 else -1) * s0
          + (if ((3 - j1 : ℤ) : ZMod 2) + b' * ((-k1 : ℤ) : ZMod 2) = 0 then 1 else -1) * s1
          + (if ((3 - j2 : ℤ) : ZMod 2) + b' * ((-k2 : ℤ) : ZMod 2) = 0 then 1 else -1) * s2) := by
  rcases T.flux_grid_pm (GridChar.rankn 3 (by norm_num) (by decide) α hα b' 0)
      (GridChar.rankn_sq _ _ _ _ _ _ _) (T.gridTriData_angles_mem hα h b') with h1 | h1
  · left; rw [h1, T.gridTriData_tileValue hα h b']
  · right; rw [h1, T.gridTriData_tileValue hα h b']

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Tri.gridTriData_angles_mem
#print axioms Erdos634.Geometry.Tri.gridTriData_tileValue
#print axioms Erdos634.Geometry.Tri.gridTriData_flux_pm
