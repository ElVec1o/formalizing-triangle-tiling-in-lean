import Erdos634.Draft.LaczFormalColumnStmt
import Erdos634.Draft.LaczFormalColumnGrid

/-!
# C1 at an interior `β`-wall, stated without frames (the interface of the Column Lemma)

Erdős #634, base-`β` row, Column Lemma.  Credit: AI assistant (Column Lemma proposal, the Wall Lemma proposal), Beeson–Roșu,
Beeson, Laczkovich.  UNAUDITED.  Axiom-clean; no `sorry`.

`BetaWall D O e0 v λ μ` is the GEOMETRIC hypothesis package of an interior `β`-wall `{O + y v}` with the lattice frame
`(O, e0, v)` (`|e0| = c`, `|v| = a`, `|v − e0| = b`, `cross e0 v > 0`):

* `arena`: the lattice points `O + x e0 + y v`, `x, y > 0`, `x/λ + y/μ < 1` are interior to the target;
* `wint`:  the wall points `O + y v`, `0 < y < μ`, are interior to the target;
* `uncrossed`: no tile crosses the wall: every tile through a wall point lies wholly on one closed side.

The one-sided angle sum at the wall points is NOT an hypothesis: it is `half_angle_sum` (`hsum_of_interior`).  The M(j)
induction does not need the earlier "frame constructor `ofWall` (~5000 lines)" that would DERIVE the frame data from a target
corner: for a wall DEFINED as a line crossed by no tile, `WFrame.ofWall` below is a structure with these three geometric fields.
HONEST CAVEAT: the difficulty has moved into the hypotheses `uncrossed` (the wall is crossed by no tile up to height `μ`) and
`arena`; nothing here derives them from wall events or from C2, so `BetaWall` is a hypothesis package, not a Wall Lemma.
`wall_T_rule`: the rules `T(m)` (`m + 1 ≤ e`) at levels `lv ≥ 1` in frame-free form (`m + 1` standard up cells on the standard
ground force the standard down cell); it is `WFrame.MJ_main` unpacked, for a `c`-column at the wall only.
-/

namespace Erdos634.LaczCol

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.TraceCovering Erdos634.LaczMJ Erdos634.LaczWall Set

variable {N : ℕ}

/-- The geometric hypotheses of an interior `β`-wall with its arena. -/
structure BetaWall (D : CongruentDissection N) (O e0 v : Plane) (lam mu : ℝ) : Prop where
  arena : ∀ x y : ℝ, 0 < x → 0 < y → x / lam + y / mu < 1 → (O + x • e0 + y • v) ∈ interior D.target.carrier
  wint : ∀ y : ℝ, 0 < y → y < mu → (O + y • v) ∈ interior D.target.carrier
  uncrossed : ∀ y : ℝ, 0 < y → y < mu → ∀ i : Fin N, (O + y • v) ∈ (D.tile i).carrier →
    (D.tile i).carrier ⊆ {z | (crossL v) z ≤ cross v O} ∨ (D.tile i).carrier ⊆ {z | cross v O ≤ (crossL v) z}

/-- **The wall frame of a `β`-wall**: no construction, only the three geometric fields. -/
noncomputable def WFrame.ofWall {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) (O e0 v : Plane) (he0 : ‖e0‖ = (tc e f : ℝ)) (hv : ‖v‖ = (ta e f : ℝ))
    (hu : ‖v - e0‖ = (tb e f : ℝ)) (hcr : 0 < cross e0 v) (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (W : BetaWall D O e0 v lam mu) : WFrame D e f α β γ p q r where
  S := S
  O := O
  e0 := e0
  v := v
  he0 := he0
  hv := hv
  hu := hu
  hcr := hcr
  lam := lam
  mu := mu
  hlam := hlam
  hmu := hmu
  hint := W.arena
  hside := W.uncrossed
  hsum := hsum_of_interior O v mu (by
    intro h
    rw [h] at hcr
    simp [cross] at hcr) W.wint W.uncrossed

section Cells

variable {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}

/-- **C1 at a `β`-wall, frame-free.**  Let `W` be a `β`-wall with lattice frame `(O, e0, v)` of the tile (norms
`c, a, b`), `S` the band setting.  Let `lv ≥ 1`, `m + 1 ≤ e`, `lv + m + 1 < min(λ, μ)`.  Suppose the cells of the level `lv − 1`
below `lv` are standard over `x ≤ m + 1` (the ground) and the `m + 1` up cells `x = 0, …, m` stand on the level `lv`.  Then the
down cell `m` of the level `lv` exists: `(m+1, lv), (m, lv+1), (m+1, lv+1)` are the vertices of a tile.  (Rule `T(m)`.) -/
theorem wall_T_rule (S : BandSetup D e f α β γ p q r) (O e0 v : Plane) (he0 : ‖e0‖ = (tc e f : ℝ))
    (hv : ‖v‖ = (ta e f : ℝ)) (hu : ‖v - e0‖ = (tb e f : ℝ)) (hcr : 0 < cross e0 v) (lam mu : ℝ)
    (hlam : 0 < lam) (hmu : 0 < mu) (W : BetaWall D O e0 v lam mu) {H : ℕ} (hHl : (H : ℝ) < lam) (hHm : (H : ℝ) < mu)
    {m lv : ℕ} (hlv : 1 ≤ lv) (hH : lv + m + 1 ≤ H) (hme : m + 1 ≤ e)
    (hground : ∀ x : ℕ, x ≤ m + 1 →
      (∃ i, TileVerts (D.tile i) (O + (x : ℝ) • e0 + ((lv - 1 : ℕ) : ℝ) • v)
        (O + ((x : ℝ) + 1) • e0 + ((lv - 1 : ℕ) : ℝ) • v) (O + (x : ℝ) • e0 + (((lv - 1 : ℕ) : ℝ) + 1) • v)) ∧
      (∃ i, TileVerts (D.tile i) (O + ((x : ℝ) + 1) • e0 + ((lv - 1 : ℕ) : ℝ) • v)
        (O + (x : ℝ) • e0 + (((lv - 1 : ℕ) : ℝ) + 1) • v)
        (O + ((x : ℝ) + 1) • e0 + (((lv - 1 : ℕ) : ℝ) + 1) • v)))
    (hups : ∀ x : ℕ, x ≤ m →
      ∃ i, TileVerts (D.tile i) (O + (x : ℝ) • e0 + (lv : ℝ) • v) (O + ((x : ℝ) + 1) • e0 + (lv : ℝ) • v)
        (O + (x : ℝ) • e0 + ((lv : ℝ) + 1) • v)) :
    ∃ i, TileVerts (D.tile i) (O + ((m : ℝ) + 1) • e0 + (lv : ℝ) • v) (O + (m : ℝ) • e0 + ((lv : ℝ) + 1) • v)
      (O + ((m : ℝ) + 1) • e0 + ((lv : ℝ) + 1) • v) := by
  set F : WFrame D e f α β γ p q r := WFrame.ofWall S O e0 v he0 hv hu hcr lam mu hlam hmu W with hF
  have hB : F.Bnd H := ⟨hHl, hHm⟩
  have hT := (F.MJ_main hB m).1
  obtain ⟨ρ', hρ'⟩ : ∃ ρ', lv = ρ' + 1 := ⟨lv - 1, by omega⟩
  have hρc : ((lv - 1 : ℕ) : ℝ) = (ρ' : ℝ) := by rw [show lv - 1 = ρ' by omega]
  refine hT lv hlv hH hme ?_ ?_
  · right
    refine ⟨ρ', hρ', fun x hx => ?_⟩
    obtain ⟨⟨iu, hiu⟩, ⟨id, hid⟩⟩ := hground x (by omega)
    rw [hρc] at hiu hid
    exact ⟨⟨iu, hiu⟩, ⟨id, hid⟩⟩
  · intro x hx
    exact hups x hx

end Cells

section GridWall

variable {e f : ℕ} (he : 1 ≤ e) (hef : e < f) {k : ℕ} (hk : 0 < k)

/-- **The grid satisfies `BetaWall`**: the interior wall `x = 1` of the genuine grid dissection (arena = the lattice triangle
of side `k − 1`).  Together with `control_wall_207` this witnesses the hypotheses of `WFrame.ofWall`: the band setting `S`
(on the 207-tiling) and an interior wall with its arena (on the grid); NOT on one dissection (the grid is not a band
target). -/
theorem grid_betaWall (hk2 : 2 ≤ k) :
    BetaWall (gridD he hef k hk) ((gridL he hef).pt 1 0) (gridL he hef).e0 (gridL he hef).v
      ((k : ℝ) - 1) ((k : ℝ) - 1) := by
  obtain ⟨hint, hside, -⟩ := grid_wallHyps he hef hk hk2
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hO : (gridL he hef).pt 1 0 = ptA + (gridL he hef).e0 := by simp [BLat.pt, gridL]
  refine ⟨hint, ?_, hside⟩
  intro y hy hy1
  have hE : (gridL he hef).pt 1 0 + y • (gridL he hef).v =
      ptA + (1 : ℝ) • (gridL he hef).e0 + y • (gridL he hef).v := by rw [hO]; module
  rw [hE]
  exact grid_interior_pt he hef hk one_pos hy (by linarith)

end GridWall

end Erdos634.LaczCol
