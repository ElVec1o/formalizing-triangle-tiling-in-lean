import Erdos634.Draft.LaczFormalColumnWit
import Erdos634.Draft.LaczFormalWallCtl

/-!
# An INTERIOR wall of a real dissection satisfies the wall hypotheses (control for `WFrame`)

Erdős #634, base-`β` row, Column Lemma.  This file proves NOTHING new about #634.  Credit: AI assistant (Column Lemma proposal),
Beeson–Roșu, Beeson, Laczkovich, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.

`WallHyps D O e0 v λ μ` is the part of the data of `WFrame` that is not the band setting `S`: the arena, the wall
(`hside`), the one-sided angle sum.  `WFrame.wallHyps` extracts it.  The grid dissection `gridD` (`k²` copies of the tile of
`(e,f)` in the triangle `kT`, a genuine `CongruentDissection`) with the wall `x = 1` (a straight interior line crossed by
no tile, `grid_wall_side`) satisfies `WallHyps` with `O = pt 1 0`, `λ = μ = k - 1`: `grid_wallHyps`.  The one-sided angle
sum is NOT assumed there: it is `Erdos634.HalfAngle.half_angle_sum` (via `wall_side_sum`) applied to the interior wall.
The negative control for `hside` is `grid_half_not_wall` (`LaczFormalWallCtl`): on the non-wall line `x = 1/2` it is false.

WHAT IS NOT DONE: a single dissection satisfying BOTH `BandSetup` and a nontrivial interior wall (the grid is not a band
target; a band target is tiled only at `M ≥ f`, and `control_wall_207` has the leg of the target as its wall).
-/

namespace Erdos634.LaczCol

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.TraceCovering Erdos634.LaczMJ Erdos634.LaczWall
  Erdos634.VertexFigureReal Erdos634.Subdivision Erdos634.CertCoord Set

variable {N : ℕ}

/-- The wall hypotheses of `WFrame` (everything except the band setting `S` and the norms of the lattice vectors). -/
def WallHyps (D : CongruentDissection N) (O e0 v : Plane) (lam mu : ℝ) : Prop :=
  (∀ x y : ℝ, 0 < x → 0 < y → x / lam + y / mu < 1 → (O + x • e0 + y • v) ∈ interior D.target.carrier) ∧
  (∀ y : ℝ, 0 < y → y < mu → ∀ i : Fin N, (O + y • v) ∈ (D.tile i).carrier →
    (D.tile i).carrier ⊆ {z | (crossL v) z ≤ cross v O} ∨ (D.tile i).carrier ⊆ {z | cross v O ≤ (crossL v) z}) ∧
  (∀ y : ℝ, 0 < y → y < mu →
    ∑ i ∈ Side D.toDissection (crossL v) (cross v O), (D.tile i).localAngle (O + y • v) = Real.pi)

theorem WFrame.wallHyps {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (F : WFrame D e f α β γ p q r) : WallHyps D F.O F.e0 F.v F.lam F.mu := ⟨F.hint, F.hside, F.hsum⟩

/-- The hypotheses `hint`, `hside` of a wall imply `hsum` when the wall points are interior (`half_angle_sum`). -/
theorem hsum_of_interior {D : CongruentDissection N} (O v : Plane) (mu : ℝ) (hv : v ≠ 0)
    (hwint : ∀ y : ℝ, 0 < y → y < mu → (O + y • v) ∈ interior D.target.carrier)
    (hside : ∀ y : ℝ, 0 < y → y < mu → ∀ i : Fin N, (O + y • v) ∈ (D.tile i).carrier →
      (D.tile i).carrier ⊆ {z | (crossL v) z ≤ cross v O} ∨ (D.tile i).carrier ⊆ {z | cross v O ≤ (crossL v) z}) :
    ∀ y : ℝ, 0 < y → y < mu →
      ∑ i ∈ Side D.toDissection (crossL v) (cross v O), (D.tile i).localAngle (O + y • v) = Real.pi := by
  intro y h0 h1
  have hg : (crossL v : Plane →ₗ[ℝ] ℝ) ≠ 0 := by
    intro h
    apply hv
    apply eq_zero_of_cross_eq_zero
    intro w
    have := congrArg (fun g : Plane →ₗ[ℝ] ℝ => g w) h
    simpa using this
  have hx : (crossL v : Plane →ₗ[ℝ] ℝ) (O + y • v) = cross v O := by
    simp only [crossL_apply]
    simp only [cross, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  exact wall_side_sum D.toDissection (crossL v) hg (cross v O) hx (hwint y h0 h1) (hside y h0 h1)

/-- Barycentric coordinates of a lattice point of a triangle `T` with `T.pts 0 = O`, `T.pts 1 = O + λ e0`,
`T.pts 2 = O + μ v`. -/
theorem coord_lat (T : Erdos634.Geometry.Tri) {O e0 v : Plane} {lam mu : ℝ} (hlam : lam ≠ 0) (hmu : mu ≠ 0)
    (h0 : T.pts 0 = O) (h1 : T.pts 1 = O + lam • e0) (h2 : T.pts 2 = O + mu • v) (x y : ℝ) :
    T.basis.coord 0 (O + x • e0 + y • v) = 1 - x / lam - y / mu ∧
    T.basis.coord 1 (O + x • e0 + y • v) = x / lam ∧ T.basis.coord 2 (O + x • e0 + y • v) = y / mu := by
  obtain ⟨a, rfl⟩ : ∃ a, x = a * lam := ⟨x / lam, by field_simp⟩
  obtain ⟨b, rfl⟩ : ∃ b, y = b * mu := ⟨y / mu, by field_simp⟩
  have ha : a * lam / lam = a := mul_div_cancel_right₀ a hlam
  have hb : b * mu / mu = b := mul_div_cancel_right₀ b hmu
  rw [ha, hb]
  have hsum : (1 - a - b) + a + b = 1 := by ring
  have hx : O + (a * lam) • e0 + (b * mu) • v =
      (1 - a - b) • T.pts 0 + a • T.pts 1 + b • T.pts 2 := by
    rw [h0, h1, h2]; module
  have hw : ∀ k : Fin 3, T.basis.coord k (O + (a * lam) • e0 + (b * mu) • v) = (![1 - a - b, a, b] : Fin 3 → ℝ) k := by
    intro k
    exact Tri.coord_eq_of_combo T _ ![1 - a - b, a, b] (by simp; ring) (by simpa using hx) k
  exact ⟨hw 0, hw 1, hw 2⟩

/-! ## The grid -/

section Grid

variable {e f : ℕ} (he : 1 ≤ e) (hef : e < f) {k : ℕ} (hk : 0 < k)

theorem grid_target_pts :
    (gridD he hef k hk).target.pts 0 = ptA ∧
    (gridD he hef k hk).target.pts 1 = ptA + (k : ℝ) • (gridL he hef).e0 ∧
    (gridD he hef k hk).target.pts 2 = ptA + (k : ℝ) • (gridL he hef).v := by
  refine ⟨rfl, ?_, ?_⟩
  · show P ptA (gB e f) (gC e f) k 0 = _
    rw [P_eq he hef, gridL_pt]; simp [gridL]
  · show P ptA (gB e f) (gC e f) 0 k = _
    rw [P_eq he hef, gridL_pt]; simp [gridL]

theorem grid_interior_pt {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s + t < (k : ℝ)) :
    (ptA + s • (gridL he hef).e0 + t • (gridL he hef).v) ∈ interior (gridD he hef k hk).target.carrier := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
  obtain ⟨t0, t1, t2⟩ := grid_target_pts he hef hk
  rw [Tri.mem_interior_iff_coord_pos]
  have hc := coord_lat (gridD he hef k hk).target (O := ptA) (e0 := (gridL he hef).e0)
    (v := (gridL he hef).v) (lam := (k : ℝ)) (mu := (k : ℝ)) hkne hkne t0 t1 t2 s t
  intro j
  rcases (by decide : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2) j with rfl | rfl | rfl
  · rw [hc.1]
    have : (s + t) / (k : ℝ) < 1 := (div_lt_one hkpos).mpr hst
    rw [add_div] at this
    linarith
  · rw [hc.2.1]; positivity
  · rw [hc.2.2]; positivity

/-- **The wall hypotheses on the grid.**  The wall is the lattice line `x = 1` (`O = pt 1 0`, direction `v`); the arena is the
lattice triangle of side `k - 1` to its right. -/
theorem grid_wallHyps (hk2 : 2 ≤ k) :
    WallHyps (gridD he hef k hk) ((gridL he hef).pt 1 0) (gridL he hef).e0 (gridL he hef).v
      ((k : ℝ) - 1) ((k : ℝ) - 1) := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hO : (gridL he hef).pt 1 0 = ptA + (gridL he hef).e0 := by simp [BLat.pt, gridL]
  have hint : ∀ x y : ℝ, 0 < x → 0 < y → x / ((k : ℝ) - 1) + y / ((k : ℝ) - 1) < 1 →
      ((gridL he hef).pt 1 0 + x • (gridL he hef).e0 + y • (gridL he hef).v) ∈
        interior (gridD he hef k hk).target.carrier := by
    intro x y hx hy hxy
    have hxy' : x + y < (k : ℝ) - 1 := by
      have h1 : (x + y) / ((k : ℝ) - 1) < 1 := by rw [add_div]; exact hxy
      exact (div_lt_one hk1).mp h1
    have hE : (gridL he hef).pt 1 0 + x • (gridL he hef).e0 + y • (gridL he hef).v =
        ptA + (1 + x) • (gridL he hef).e0 + y • (gridL he hef).v := by rw [hO]; module
    rw [hE]
    exact grid_interior_pt he hef hk (by linarith) hy (by linarith)
  have hwint : ∀ y : ℝ, 0 < y → y < (k : ℝ) - 1 →
      ((gridL he hef).pt 1 0 + y • (gridL he hef).v) ∈ interior (gridD he hef k hk).target.carrier := by
    intro y hy hy1
    have hE : (gridL he hef).pt 1 0 + y • (gridL he hef).v =
        ptA + (1 : ℝ) • (gridL he hef).e0 + y • (gridL he hef).v := by rw [hO]; module
    rw [hE]
    exact grid_interior_pt he hef hk one_pos hy (by linarith)
  have hside : ∀ y : ℝ, 0 < y → y < (k : ℝ) - 1 → ∀ i : Fin (k * k),
      ((gridL he hef).pt 1 0 + y • (gridL he hef).v) ∈ ((gridD he hef k hk).tile i).carrier →
      ((gridD he hef k hk).tile i).carrier ⊆
          {z | (crossL (gridL he hef).v) z ≤ cross (gridL he hef).v ((gridL he hef).pt 1 0)} ∨
      ((gridD he hef k hk).tile i).carrier ⊆
          {z | cross (gridL he hef).v ((gridL he hef).pt 1 0) ≤ (crossL (gridL he hef).v) z} :=
    fun y _ _ i _ => grid_wall_side he hef hk i
  refine ⟨hint, hside, ?_⟩
  have hv : (gridL he hef).v ≠ 0 := by
    intro h
    have := (gridL he hef).hcr
    rw [h] at this
    simp [cross] at this
  exact hsum_of_interior ((gridL he hef).pt 1 0) (gridL he hef).v ((k : ℝ) - 1) hv hwint hside

end Grid

end Erdos634.LaczCol
