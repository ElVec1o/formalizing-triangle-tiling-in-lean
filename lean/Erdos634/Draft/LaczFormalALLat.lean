import Erdos634.Draft.LaczFormalMJMain
import Erdos634.Draft.LaczFormalASteps

/-!
# The lattice frame at the left corner of a band target (rule `M(j)`, general `j`)

Erdős #634, base-`β` band.  Credit: AI assistant (item 3, band program, rule `M(j)`), Beeson–Roșu (the tile, Lemmas
28–37), Beeson, Laczkovich (fan/chord covers), Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.

`AF` packages the vectors `e0` (length `c`, along the base) and `v` (length `a`, along the left leg) at the
left corner `O = A_p` of an oriented band target, with `|v − e0| = b` and `cross e0 v > 0`.  The lattice point
`F.pt x y = O + x e0 + y v`; the standard up tile (`β` at `(x,y)`, `α` at `(x+1,y)`, `γ` at `(x,y+1)`) and the
standard down tile (`γ` at `(x+1,y)`, `α` at `(x,y+1)`, `β` at `(x+1,y+1)`) of the hand proof have lattice
vertices.  This file proves the position facts about the target: lattice points on the base / left leg are in
the open sides, lattice points `(x,y)` with `x,y > 0`, `x/λ + y/μ < 1` are interior.
-/

namespace Erdos634.LaczAL

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.LaczMJ

variable {N : ℕ}

/-- The lattice frame at the left corner `A_p`: `e0` along the base (`|e0| = c`), `v` along the left leg
(`|v| = a`), the target corner `A_q = A_p + λ e0`, `A_r = A_p + μ v`. -/
structure AF (D : CongruentDissection N) (e f : ℕ) (α β γ : ℝ) (p q r : Fin 3) where
  S : BandSetup D e f α β γ p q r
  e0 : Plane
  v : Plane
  he0 : ‖e0‖ = (ta e f : ℝ)
  hv : ‖v‖ = (tc e f : ℝ)
  hu : ‖v - e0‖ = (tb e f : ℝ)
  hcr : 0 < cross e0 v
  lam : ℝ
  mu : ℝ
  hlam : 0 < lam
  hmu : 0 < mu
  hq : D.target.pts q = D.target.pts p + lam • e0
  hr : D.target.pts r = D.target.pts p + mu • v

namespace AF

variable {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
  (F : AF D e f α β γ p q r)

/-- The lattice point `O + x e0 + y v`. -/
def pt (x y : ℝ) : Plane := D.target.pts p + x • F.e0 + y • F.v

theorem pt_zero : F.pt 0 0 = D.target.pts p := by simp [pt]

/-- Barycentric coordinates of a lattice point. -/
theorem coord_pt (k : Fin 3) (x y : ℝ) :
    D.target.basis.coord k (F.pt x y) =
      D.target.basis.coord k (D.target.pts p) +
        (x / F.lam) * (D.target.basis.coord k (D.target.pts q) - D.target.basis.coord k (D.target.pts p)) +
        (y / F.mu) * (D.target.basis.coord k (D.target.pts r) - D.target.basis.coord k (D.target.pts p)) := by
  have hl := F.hlam.ne'
  have hm := F.hmu.ne'
  set c := D.target.basis.coord k with hc
  have h1 : F.pt x y = (x • F.e0 + y • F.v) +ᵥ D.target.pts p := by
    simp [pt, vadd_eq_add]; abel
  have h2 : c.linear F.e0 = (c (D.target.pts q) - c (D.target.pts p)) / F.lam := by
    have : c.linear (F.lam • F.e0) = c (D.target.pts q) - c (D.target.pts p) := by
      rw [← vsub_eq_sub, ← AffineMap.linearMap_vsub, vsub_eq_sub, F.hq]; congr 1; abel
    rw [map_smul, smul_eq_mul] at this
    field_simp; linarith
  have h3 : c.linear F.v = (c (D.target.pts r) - c (D.target.pts p)) / F.mu := by
    have : c.linear (F.mu • F.v) = c (D.target.pts r) - c (D.target.pts p) := by
      rw [← vsub_eq_sub, ← AffineMap.linearMap_vsub, vsub_eq_sub, F.hr]; congr 1; abel
    rw [map_smul, smul_eq_mul] at this
    field_simp; linarith
  rw [h1, AffineMap.map_vadd, map_add, map_smul, map_smul, h2, h3]
  simp only [smul_eq_mul, vadd_eq_add]
  ring

/-- Lattice points on the base: `(x, 0)`, `0 < x < λ`, lie in the open base side. -/
theorem pt_base_mem {x : ℝ} (h0 : 0 < x) (h1 : x < F.lam) :
    F.pt x 0 ∈ openSegment ℝ (D.target.pts p) (D.target.pts q) := by
  have : F.pt x 0 = D.target.pts p + (x / F.lam) • (D.target.pts q - D.target.pts p) := by
    rw [F.hq]; simp only [pt, zero_smul, add_zero, add_sub_cancel_left, smul_smul]
    rw [div_mul_cancel₀ _ F.hlam.ne']
  rw [this]
  exact mem_open_param (div_pos h0 F.hlam) ((div_lt_one F.hlam).mpr h1)

/-- Lattice points on the left leg: `(0, y)`, `0 < y < μ`, lie in the open left side. -/
theorem pt_leg_mem {y : ℝ} (h0 : 0 < y) (h1 : y < F.mu) :
    F.pt 0 y ∈ openSegment ℝ (D.target.pts p) (D.target.pts r) := by
  have : F.pt 0 y = D.target.pts p + (y / F.mu) • (D.target.pts r - D.target.pts p) := by
    rw [F.hr]; simp only [pt, zero_smul, add_zero, add_sub_cancel_left, smul_smul]
    rw [div_mul_cancel₀ _ F.hmu.ne']
  rw [this]
  exact mem_open_param (div_pos h0 F.hmu) ((div_lt_one F.hmu).mpr h1)

/-- Interior lattice points. -/
theorem pt_interior {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x / F.lam + y / F.mu < 1) :
    F.pt x y ∈ interior D.target.carrier := by
  rw [D.target.mem_interior_iff_coord_pos]
  intro k
  rw [F.coord_pt]
  have hpq := F.S.hpq
  have hpr := F.S.hpr
  have hqr := F.S.hqr
  have hs := div_pos hx F.hlam
  have ht := div_pos hy F.hmu
  rcases fin3_cover p q r k hpq hpr hqr with rfl | rfl | rfl
  · simp [coord_vertex, hpq, hpr]; linarith
  · simp [coord_vertex, hpq.symm, hqr, hpq, hqr.symm]
    nlinarith
  · simp [coord_vertex, hpr.symm, hqr.symm, hpr, hqr]
    nlinarith

end AF

end Erdos634.LaczAL
