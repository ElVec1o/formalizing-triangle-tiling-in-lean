import Erdos634.Draft.LaczFormalColumnWall

/-!
# C1 at a point of a LEG of the target (boundary wall with an offset origin)

Erdős #634, base-`β` row, Column Lemma.  Credit: AI assistant (Column Lemma and cap-lemma proposals), Beeson–Roșu, Beeson,
Laczkovich.  UNAUDITED.  Axiom-clean; no `sorry`.

`WFrame.ofLFrame` (`LaczFormalColumnWit`) puts the lattice frame at the CORNER of the target.  The cap lemma of the mixed-row
analysis (`ANSWER.md` §2) needs the frame at an INTERIOR POINT `P` of a leg (the foot of a closed chord): the wall is the leg of
the target above `P`, the lattice frame is `(P, e0, v)`.  `BoundaryWall D O e0 v λ μ` packages this: the arena is interior,
the whole target lies in the closed right side of the leg line (so no tile crosses it: `hside` is the trivial alternative), the
leg points are frontier points that are not target vertices (so the one-sided angle sum is the boundary angle sum `π`,
`pin_angle_sum`).  `WFrame.ofBoundaryWall` is then a structure with these three fields, and `boundary_T_rule` is the rule `T(m)` at
a leg point.  `BoundaryWall.of_leg` derives `right` and `front` from the triangle: `O + y v` in the open leg `(p, r)` and the
third vertex on the right.  `grid_boundaryWall`: a genuine instance (the left leg of the grid `kT` with the origin
`pt 0 y0`, `y0 ≥ 1`).

NOT done: the rest of the cap lemma (it needs the closed-chord data at `P` and the Closure Lemma).
-/

namespace Erdos634.LaczCol

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.TraceCovering Erdos634.LaczMJ Erdos634.LaczWall Set

variable {N : ℕ}

/-- A leg of the target as a wall: the lattice frame `(O, e0, v)` is based at a point `O` of the leg line. -/
structure BoundaryWall (D : CongruentDissection N) (O e0 v : Plane) (lam mu : ℝ) : Prop where
  arena : ∀ x y : ℝ, 0 < x → 0 < y → x / lam + y / mu < 1 → (O + x • e0 + y • v) ∈ interior D.target.carrier
  right : D.target.carrier ⊆ {z | (crossL v) z ≤ cross v O}
  front : ∀ y : ℝ, 0 < y → y < mu →
    (O + y • v) ∈ frontier D.target.carrier ∧ (O + y • v) ∉ Set.range D.target.pts

/-- **The wall frame of a leg point.** -/
noncomputable def WFrame.ofBoundaryWall {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) (O e0 v : Plane) (he0 : ‖e0‖ = (tc e f : ℝ)) (hv : ‖v‖ = (ta e f : ℝ))
    (hu : ‖v - e0‖ = (tb e f : ℝ)) (hcr : 0 < cross e0 v) (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (W : BoundaryWall D O e0 v lam mu) : WFrame D e f α β γ p q r where
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
  hside := fun _ _ _ i _ => Or.inl ((tile_subset_target D.toDissection i).trans W.right)
  hsum := by
    intro y h0 h1
    classical
    have hall : Side D.toDissection (crossL v) (cross v O) = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro i
      rw [mem_Side]
      exact (tile_subset_target D.toDissection i).trans W.right
    rw [hall]
    obtain ⟨hfr, hnv⟩ := W.front y h0 h1
    exact Erdos634.PinPlumbing.pin_angle_sum D.toDissection hfr hnv

section Rule

variable {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}

/-- **The rule `T(m)` at a point of a leg** (frame-free, as `wall_T_rule`). -/
theorem boundary_T_rule (S : BandSetup D e f α β γ p q r) (O e0 v : Plane) (he0 : ‖e0‖ = (tc e f : ℝ))
    (hv : ‖v‖ = (ta e f : ℝ)) (hu : ‖v - e0‖ = (tb e f : ℝ)) (hcr : 0 < cross e0 v) (lam mu : ℝ)
    (hlam : 0 < lam) (hmu : 0 < mu) (W : BoundaryWall D O e0 v lam mu) {H : ℕ} (hHl : (H : ℝ) < lam)
    (hHm : (H : ℝ) < mu) {m lv : ℕ} (hlv : 1 ≤ lv) (hH : lv + m + 1 ≤ H) (hme : m + 1 ≤ e)
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
  set F : WFrame D e f α β γ p q r := WFrame.ofBoundaryWall S O e0 v he0 hv hu hcr lam mu hlam hmu W with hF
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

end Rule

theorem fin3_third : ∀ (i p q r : Fin 3), p ≠ q → p ≠ r → q ≠ r → i ≠ p → i ≠ r → i = q := by decide

/-- **A leg of a triangle target is a `BoundaryWall`.**  Let `O + y v`, `0 < y < μ`, lie in the open leg `(p, r)`, let the
vertices `p`, `r` lie on the line `{crossL v = cross v O}` and the third vertex `q` on its right (`≤`).  Then the target lies in
the closed right half-plane and the leg points are frontier points which are not vertices. -/
theorem BoundaryWall.of_leg (D : CongruentDissection N) {O e0 v : Plane} {lam mu : ℝ} {p q r : Fin 3} (hpq : p ≠ q)
    (hpr : p ≠ r) (hqr : q ≠ r)
    (harena : ∀ x y : ℝ, 0 < x → 0 < y → x / lam + y / mu < 1 → (O + x • e0 + y • v) ∈ interior D.target.carrier)
    (hp : (crossL v) (D.target.pts p) = cross v O) (hr : (crossL v) (D.target.pts r) = cross v O)
    (hq : (crossL v) (D.target.pts q) ≤ cross v O)
    (hleg : ∀ y : ℝ, 0 < y → y < mu → (O + y • v) ∈ openSegment ℝ (D.target.pts p) (D.target.pts r)) :
    BoundaryWall D O e0 v lam mu := by
  refine ⟨harena, ?_, ?_⟩
  · intro z hz
    refine Tri.carrier_subset_halfplane D.target (crossL v) (cross v O) (fun i => ?_) z hz
    by_cases h1 : i = p
    · rw [h1, hp]
    by_cases h2 : i = r
    · rw [h2, hr]
    have h3 : i = q := fin3_third i p q r hpq hpr hqr h1 h2
    rw [h3]; exact hq
  · intro y h0 h1
    exact side_frontier D.target hpr hpq hqr.symm (hleg y h0 h1)

section GridLeg

variable {e f : ℕ} (he : 1 ≤ e) (hef : e < f) {k : ℕ} (hk : 0 < k)

/-- **A genuine `BoundaryWall` with an offset origin.**  The left leg of the grid `kT` with the lattice frame based at
`pt 0 y0` (`1 ≤ y0`, `y0 + 1 < k`): the arena is the lattice triangle of side `k − y0` above `y0` (the instance of
`BoundaryWall.of_leg` for `p = 0`, `q = 1`, `r = 2`). -/
theorem grid_boundaryWall (y0 : ℕ) (hy0 : 1 ≤ y0) (hk2 : y0 + 1 < k) :
    BoundaryWall (gridD he hef k hk) ((gridL he hef).pt 0 (y0 : ℝ)) (gridL he hef).e0 (gridL he hef).v
      ((k : ℝ) - y0) ((k : ℝ) - y0) := by
  set L := gridL he hef with hL
  have hκ : 0 < cross L.e0 L.v := L.hcr
  have hkR : (y0 : ℝ) + 1 < k := by exact_mod_cast hk2
  have hkpos : (0 : ℝ) < k := by linarith [(by exact_mod_cast hy0 : (1 : ℝ) ≤ y0)]
  have hmu : (0 : ℝ) < (k : ℝ) - y0 := by linarith
  obtain ⟨t0, t1, t2⟩ := grid_target_pts he hef hk
  rw [← hL] at t1 t2
  have hO : L.pt 0 (y0 : ℝ) = ptA + (y0 : ℝ) • L.v := by simp [BLat.pt, hL, gridL]
  refine BoundaryWall.of_leg (gridD he hef k hk) (p := 0) (q := 1) (r := 2) (by decide) (by decide) (by decide)
    ?_ ?_ ?_ ?_ ?_
  · intro x y hx hy hxy
    have hxy' : x + y < (k : ℝ) - y0 := by
      have h1 : (x + y) / ((k : ℝ) - y0) < 1 := by rw [add_div]; exact hxy
      exact (div_lt_one hmu).mp h1
    have hE : L.pt 0 (y0 : ℝ) + x • L.e0 + y • L.v = ptA + x • L.e0 + ((y0 : ℝ) + y) • L.v := by
      rw [hO]; module
    rw [hE]
    exact grid_interior_pt he hef hk hx (by linarith [(by exact_mod_cast hy0 : (1 : ℝ) ≤ y0)]) (by linarith)
  · rw [t0]
    simp only [crossL_apply]
    rw [hO]
    simp only [cross, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  · rw [t2]
    simp only [crossL_apply]
    rw [hO]
    simp only [cross, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  · rw [t1]
    simp only [crossL_apply]
    rw [hO]
    simp only [cross, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    have hκ' : 0 < L.e0 0 * L.v 1 - L.e0 1 * L.v 0 := by simpa [cross] using hκ
    nlinarith [mul_pos hkpos hκ']
  · intro y h0 h1
    have hE : L.pt 0 (y0 : ℝ) + y • L.v = ptA + ((y0 : ℝ) + y) • L.v := by rw [hO]; module
    rw [hE, t0, t2]
    refine ⟨1 - ((y0 : ℝ) + y) / k, ((y0 : ℝ) + y) / k, ?_, ?_, by ring, ?_⟩
    · rw [sub_pos, div_lt_one hkpos]; linarith
    · positivity
    · have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
      have : ((y0 : ℝ) + y) / k * k = (y0 : ℝ) + y := by field_simp
      calc (1 - ((y0 : ℝ) + y) / k) • ptA + (((y0 : ℝ) + y) / k) • (ptA + (k : ℝ) • L.v)
          = ptA + ((((y0 : ℝ) + y) / k) * k) • L.v := by module
        _ = ptA + ((y0 : ℝ) + y) • L.v := by rw [this]

end GridLeg

#print axioms boundary_T_rule
#print axioms grid_boundaryWall

end Erdos634.LaczCol
