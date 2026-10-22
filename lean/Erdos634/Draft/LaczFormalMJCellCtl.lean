import Erdos634.Draft.LaczFormalMJGrid

/-!
# Non-vacuity control for the cell predicates `UpCell`, `DownCell`, `Ground`, `Std`, `TRule`, `ARule`
(audit room `LEAN_CTRL2_2026-10-21`, gap (a) of `band_gaps_2026-10-21`)

Erdős #634, base-`β` band.  This file proves NOTHING new about #634.  Credit: AI assistant (band program, rule `M(j)`),
Beeson–Roșu, Beeson, Laczkovich, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.

The grid `gridD he hef k hk` (file `LaczFormalMJGrid`) is a genuine `CongruentDissection` of the triangle `kT` by
`k²` copies of the explicit tile `T = (A,B,C)` of the member `(e,f)` (`A = (0,0)`, `B = (c,0)`, `C = (cx,cy)`).
With the lattice `gridL` (`O = A`, `e0 = B−A`, `v = C−A`) its tiles are exactly the standard cells.  This file
proves, for every coprime-or-not `1 ≤ e < f` (so in particular `(2,3)`, `(3,7)`, `(3,8)`), and every `k ≥ 1`:

1. `ModelData` of the grid (so the angle lemmas `up_anglesB`, `down_anglesB`, `third_upB`, `third_downB` apply);
2. `UpCellB`, `DownCellB` at every cell, `GroundB ρ k'` for every level `ρ` and `k'` the grid allows,
   `StdB`, shared edges of adjacent cells;
3. `third_upB`, `third_downB` on the explicit patch;
4. the covering shapes of `h_cover` and `l_cover` (membership in `lineChain`, lattice positions, sum of lengths);
5. `TRuleB`, with its premise satisfied at levels 0 and 1, and the premise of `ARule` (without its last
   hypothesis) satisfied.

WHAT IS NOT DONE: an `LFrame` of a band dissection (none exists: that is the theorem; and the seed tilings have no
standard cell at an integer lattice point of the corner frame).  The bridge `upCell_iff` etc. of
`LaczFormalMJBare` shows that the `LFrame` predicates are `UpCellB D.tile F.toBLat`, so the predicates themselves
are exercised; what is not exercised is the band target's `BandSetup`, whose only use in these lemmas is
`ModelData`.
-/

namespace Erdos634.LaczMJ

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Subdivision Erdos634.CertCoord

/-! ## The numbers -/

section Nums

variable {e f : ℕ}

theorem tri_nat (he : 1 ≤ e) (hef : e < f) :
    tc e f < ta e f + tb e f ∧ ta e f < tb e f + tc e f ∧ tb e f < ta e f + tc e f := by
  unfold ta tb tc
  have h1 : e ^ 2 < e * f := by nlinarith
  have h2 : e * f < f ^ 2 := by nlinarith
  have h3 : 0 < e * f := Nat.mul_pos (by omega) (by omega)
  have h4 : e ^ 2 ≤ f ^ 2 := by nlinarith
  omega

theorem pos_a (he : 1 ≤ e) (hef : e < f) : (0 : ℝ) < ta e f := by
  have := a_pos e f he hef; exact_mod_cast this

theorem pos_b (he : 1 ≤ e) (hef : e < f) : (0 : ℝ) < tb e f := by
  have := b_pos e f he hef; exact_mod_cast this

theorem pos_c (he : 1 ≤ e) (hef : e < f) : (0 : ℝ) < tc e f := by
  have := b_lt_c e f he hef
  have := b_pos e f he hef
  exact_mod_cast (by omega : 0 < tc e f)

theorem hposGrid (he : 1 ≤ e) (hef : e < f) :
    0 < (ta e f : ℝ) ^ 2 - cx (ta e f : ℝ) (tb e f : ℝ) (tc e f : ℝ) ^ 2 := by
  obtain ⟨t1, t2, t3⟩ := tri_nat he hef
  have t1' : (tc e f : ℝ) < ta e f + tb e f := by exact_mod_cast t1
  have t2' : (ta e f : ℝ) < tb e f + tc e f := by exact_mod_cast t2
  have t3' : (tb e f : ℝ) < ta e f + tc e f := by exact_mod_cast t3
  have ha := pos_a he hef
  have hb := pos_b he hef
  have hc := pos_c he hef
  set a : ℝ := (ta e f : ℝ)
  set b : ℝ := (tb e f : ℝ)
  set c : ℝ := (tc e f : ℝ)
  have key : a ^ 2 - cx a b c ^ 2 =
      (a + c - b) * (a + c + b) * (b - a + c) * (b + a - c) / (4 * c ^ 2) := by
    unfold cx; field_simp; ring
  rw [key]
  have h1 : 0 < a + c - b := by linarith
  have h2 : 0 < a + c + b := by linarith
  have h3 : 0 < b - a + c := by linarith
  have h4 : 0 < b + a - c := by linarith
  positivity

end Nums

/-! ## The grid, its lattice and its model data -/

section Setup

variable {e f : ℕ}

/-- The `γ` vertex. -/
noncomputable def gB (e f : ℕ) : Plane := ptB (tc e f : ℝ)
noncomputable def gC (e f : ℕ) : Plane := ptC (ta e f : ℝ) (tb e f : ℝ) (tc e f : ℝ)

theorem gInd (he : 1 ≤ e) (hef : e < f) : AffineIndependent ℝ ![ptA, gB e f, gC e f] :=
  indep_ABC (pos_c he hef) (hposGrid he hef)

theorem gdist_BA (he : 1 ≤ e) (hef : e < f) : dist (gB e f) ptA = (tc e f : ℝ) :=
  dist_BA (pos_c he hef)

theorem gdist_CA (he : 1 ≤ e) (hef : e < f) : dist (gC e f) ptA = (ta e f : ℝ) :=
  dist_CA (pos_a he hef) (pos_c he hef) (hposGrid he hef)

theorem gdist_CB (he : 1 ≤ e) (hef : e < f) : dist (gC e f) (gB e f) = (tb e f : ℝ) :=
  dist_CB (pos_b he hef) (pos_c he hef) (hposGrid he hef)

/-- **The grid**: `kT` cut into `k²` copies of the tile of the member `(e,f)`. -/
noncomputable def gridD (he : 1 ≤ e) (hef : e < f) (k : ℕ) (hk : 0 < k) : CongruentDissection (k * k) :=
  gridDiss ptA (gB e f) (gC e f) (gInd he hef) k hk

/-- **The lattice of the grid**: `O = A`, `e0 = B − A`, `v = C − A`. -/
noncomputable def gridL (he : 1 ≤ e) (hef : e < f) : BLat e f where
  O := ptA
  e0 := gB e f - ptA
  v := gC e f - ptA
  he0 := by rw [← dist_eq_norm]; exact gdist_BA he hef
  hv := by rw [← dist_eq_norm]; exact gdist_CA he hef
  hu := by
    have : (gC e f - ptA) - (gB e f - ptA) = gC e f - gB e f := by abel
    rw [this, ← dist_eq_norm]; exact gdist_CB he hef
  hcr := cross_ABC (pos_c he hef) (hposGrid he hef)

theorem gridL_pt (he : 1 ≤ e) (hef : e < f) (x y : ℝ) :
    (gridL he hef).pt x y = ptA + x • (gB e f - ptA) + y • (gC e f - ptA) := rfl

theorem P_eq (he : 1 ≤ e) (hef : e < f) (i j : ℕ) :
    P ptA (gB e f) (gC e f) i j = (gridL he hef).pt (i : ℝ) (j : ℝ) := rfl

theorem P_succ_l (he : 1 ≤ e) (hef : e < f) (i j : ℕ) :
    P ptA (gB e f) (gC e f) (i + 1) j = (gridL he hef).pt ((i : ℝ) + 1) (j : ℝ) := by
  rw [P_eq he hef]; simp only [gridL_pt]; push_cast; rfl

theorem P_succ_r (he : 1 ≤ e) (hef : e < f) (i j : ℕ) :
    P ptA (gB e f) (gC e f) i (j + 1) = (gridL he hef).pt (i : ℝ) ((j : ℝ) + 1) := by
  rw [P_eq he hef]; simp only [gridL_pt]; push_cast; rfl

theorem P_succ_b (he : 1 ≤ e) (hef : e < f) (i j : ℕ) :
    P ptA (gB e f) (gC e f) (i + 1) (j + 1) = (gridL he hef).pt ((i : ℝ) + 1) ((j : ℝ) + 1) := by
  rw [P_eq he hef]; simp only [gridL_pt]; push_cast; rfl

end Setup

/-! ## The three corner angles of the explicit tile are distinct -/

section Angles

theorem cos_corner (X Y Z : Plane) :
    dist X Z ^ 2 = dist X Y ^ 2 + dist Z Y ^ 2 - 2 * dist X Y * dist Z Y * Real.cos (cornerAngle X Y Z) := by
  have := EuclideanGeometry.law_cos X Y Z
  unfold cornerAngle
  nlinarith [this]

/-- In a triangle `ABC` with `|CA| = a`, `|CB| = b`, `|BA| = c` (strict triangle inequalities, distinct sides), the
corner angles at `B`, `A`, `C` are pairwise distinct. -/
theorem angles_ne (A B C : Plane) {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hCA : dist C A = a) (hCB : dist C B = b) (hBA : dist B A = c)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (t1 : c < a + b) (t2 : a < b + c) (t3 : b < a + c) :
    cornerAngle A B C ≠ cornerAngle C A B ∧ cornerAngle C A B ≠ cornerAngle B C A ∧
      cornerAngle A B C ≠ cornerAngle B C A := by
  have E1 := cos_corner A B C
  have E2 := cos_corner C A B
  have E3 := cos_corner B C A
  rw [dist_comm A C, hCA, dist_comm A B, hBA, hCB] at E1
  rw [hCB, hCA, hBA] at E2
  rw [dist_comm B C, hCB, hBA, dist_comm A C, hCA] at E3
  set x := Real.cos (cornerAngle A B C)
  set y := Real.cos (cornerAngle C A B)
  set z := Real.cos (cornerAngle B C A)
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hx : y = x := by simp only [x, y, h]
    rw [hx] at E2
    have : (a - b) * (c ^ 2 - (a + b) ^ 2) = 0 := by linear_combination (-a) * E1 + b * E2
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hab (by linarith)
    · nlinarith
  · intro h
    have hx : y = z := by simp only [y, z, h]
    rw [hx] at E2
    have : (b - c) * (a ^ 2 - (b + c) ^ 2) = 0 := by linear_combination (-b) * E2 + c * E3
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hbc (by linarith)
    · nlinarith
  · intro h
    have hx : x = z := by simp only [x, z, h]
    rw [← hx] at E3
    have : (a - c) * (b ^ 2 - (a + c) ^ 2) = 0 := by linear_combination (-a) * E1 + c * E3
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hac (by linarith)
    · nlinarith

end Angles

/-! ## `ModelData` of the grid, and the standard cells -/

section Cells

variable {e f : ℕ}

theorem ta_ne_tb (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f) : ta e f ≠ tb e f := by
  intro h
  unfold ta tb at h
  have h1 : e ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left hef.le 2
  have h2 : f ^ 2 = e * (f + e) := by
    have : e * f + e ^ 2 = f ^ 2 := by omega
    nlinarith
  have h3 : e ∣ f ^ 2 := ⟨f + e, h2⟩
  have h4 : e = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right 2 hcop) h3
  subst h4
  have : 2 ≤ f := by omega
  nlinarith

/-- The three corner angles of the explicit tile (at `B`, `A`, `C`): the model's `α`, `β`, `γ`. -/
noncomputable def gα (e f : ℕ) : ℝ := cornerAngle ptA (gB e f) (gC e f)
noncomputable def gβ (e f : ℕ) : ℝ := cornerAngle (gC e f) ptA (gB e f)
noncomputable def gγ (e f : ℕ) : ℝ := cornerAngle (gB e f) (gC e f) ptA

theorem gridD_model (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f) (k : ℕ) (hk : 0 < k) :
    ModelData (gridD he hef k hk) e f (gα e f) (gβ e f) (gγ e f) := by
  obtain ⟨m0, m1, m2⟩ := gridDiss_model_pts ptA (gB e f) (gC e f) (gInd he hef) k hk
  have h0 : (gridD he hef k hk).model.pts 0 = gB e f := m0
  have h1 : (gridD he hef k hk).model.pts 1 = ptA := m1
  have h2 : (gridD he hef k hk).model.pts 2 = gC e f := m2
  obtain ⟨t1, t2, t3⟩ := tri_nat he hef
  have t1' : (tc e f : ℝ) < ta e f + tb e f := by exact_mod_cast t1
  have t2' : (ta e f : ℝ) < tb e f + tc e f := by exact_mod_cast t2
  have t3' : (tb e f : ℝ) < ta e f + tc e f := by exact_mod_cast t3
  have hab : (ta e f : ℝ) ≠ tb e f := fun h => ta_ne_tb he hef hcop (by exact_mod_cast h)
  have hbc : (tb e f : ℝ) ≠ tc e f := fun h => by
    have := b_lt_c e f he hef
    have : tb e f = tc e f := by exact_mod_cast h
    omega
  have hac : (ta e f : ℝ) ≠ tc e f := fun h => by
    have : ta e f = tc e f := by exact_mod_cast h
    unfold ta tc at this
    have : e * f < f * f := Nat.mul_lt_mul_of_pos_right hef (by omega)
    nlinarith
  obtain ⟨n1, n2, n3⟩ := angles_ne ptA (gB e f) (gC e f) (pos_a he hef) (pos_b he hef) (pos_c he hef)
    (gdist_CA he hef) (gdist_CB he hef) (gdist_BA he hef) hab hbc hac t1' t2' t3'
  refine ⟨he, hef, ?_, ?_, ?_, ?_, ?_, ?_, n1, ?_, ?_, hab, hbc, hac⟩
  · show cornerAngle ((gridD he hef k hk).model.pts 1) ((gridD he hef k hk).model.pts 0) ((gridD he hef k hk).model.pts 2) = _
    rw [h1, h0, h2]; rfl
  · rw [h2, h1, h0]; rfl
  · rw [h0, h2, h1]; rfl
  · show dist ((gridD he hef k hk).model.pts 1) ((gridD he hef k hk).model.pts 2) = _
    rw [h1, h2, dist_comm]; exact gdist_CA he hef
  · show dist ((gridD he hef k hk).model.pts 2) ((gridD he hef k hk).model.pts 0) = _
    rw [h2, h0]; exact gdist_CB he hef
  · show dist ((gridD he hef k hk).model.pts 0) ((gridD he hef k hk).model.pts 1) = _
    rw [h0, h1]; exact gdist_BA he hef
  · exact n2
  · exact n3

end Cells

/-! ## The standard cells of the grid -/

section GridCells

variable {e f : ℕ} (he : 1 ≤ e) (hef : e < f) {k : ℕ} (hk : 0 < k)

/-- **Every up cell of the grid is a tile.** -/
theorem grid_up {i j : ℕ} (h : i + j + 1 ≤ k) :
    UpCellB (gridD he hef k hk).tile (gridL he hef) (i : ℝ) (j : ℝ) := by
  obtain ⟨n, hn⟩ := gridDiss_tile_up ptA (gB e f) (gC e f) (gInd he hef) k hk h
  have hn' : (gridD he hef k hk).tile n = cellUp ptA (gB e f) (gC e f) (gInd he hef) i j := hn
  refine ⟨n, 0, Or.inl ⟨?_, ?_, ?_⟩⟩
  · rw [hn']; exact (cellUp_pts0 _ _ _ _ i j).trans (P_eq he hef i j)
  · rw [hn']; exact (cellUp_pts1 _ _ _ _ i j).trans (P_succ_l he hef i j)
  · rw [hn']; exact (cellUp_pts2 _ _ _ _ i j).trans (P_succ_r he hef i j)

/-- **Every down cell of the grid is a tile.** -/
theorem grid_down {i j : ℕ} (h : i + j + 2 ≤ k) :
    DownCellB (gridD he hef k hk).tile (gridL he hef) (i : ℝ) (j : ℝ) := by
  obtain ⟨n, hn⟩ := gridDiss_tile_down ptA (gB e f) (gC e f) (gInd he hef) k hk h
  have hn' : (gridD he hef k hk).tile n = cellDown ptA (gB e f) (gC e f) (gInd he hef) i j := hn
  refine ⟨n, 0, Or.inl ⟨?_, ?_, ?_⟩⟩
  · rw [hn']; exact (cellDown_pts0 _ _ _ _ i j).trans (P_succ_l he hef i j)
  · rw [hn']; exact (cellDown_pts1 _ _ _ _ i j).trans (P_succ_r he hef i j)
  · rw [hn']; exact (cellDown_pts2 _ _ _ _ i j).trans (P_succ_b he hef i j)

/-- Ground at level `0` (trivial) and at level `ρ + 1` over `x ≤ k'`. -/
theorem grid_ground_zero (k' : ℕ) : GroundB (gridD he hef k hk).tile (gridL he hef) 0 k' := Or.inl rfl

theorem grid_ground {ρ k' : ℕ} (h : k' + ρ + 2 ≤ k) :
    GroundB (gridD he hef k hk).tile (gridL he hef) (ρ + 1) k' :=
  Or.inr ⟨ρ, rfl, fun x hx => ⟨grid_up he hef hk (by omega), grid_down he hef hk (by omega)⟩⟩

/-- The rows `r, …, r+s` of the triangle with `m+1` up tiles on level `r` are standard in the grid. -/
theorem grid_std {r m : ℕ} (h : r + m + 1 ≤ k) (s : ℕ) :
    StdB (gridD he hef k hk).tile (gridL he hef) r m s := by
  intro t _
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have := grid_up he hef hk (i := x) (j := r + t) (by omega)
    simpa using this
  · have := grid_down he hef hk (i := x) (j := r + t) (by omega)
    simpa using this

end GridCells

/-! ## Angles, shared edges, third vertices on the explicit patch -/

section GridLemmas

variable {e f : ℕ} (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f) {k : ℕ} (hk : 0 < k)

theorem BLat.pt_ne_x {e f : ℕ} (L : BLat e f) (x y : ℝ) : L.pt x y ≠ L.pt (x + 1) y := by
  intro h
  have h1 := L.pt_sub x y (x + 1) y
  rw [h, sub_self] at h1
  have h2 : L.e0 = 0 := by
    have : (-1 : ℝ) • L.e0 = 0 := by rw [← add_zero ((-1 : ℝ) • L.e0)]; convert h1.symm using 2 <;> simp
    simpa using this
  have := L.hcr
  rw [h2] at this
  simp [cross] at this

theorem BLat.pt_ne_2x_y {e f : ℕ} (L : BLat e f) (x y : ℝ) : L.pt (x + 2) y ≠ L.pt x (y + 1) := by
  intro h
  have h1 := L.pt_sub (x + 2) y x (y + 1)
  rw [h, sub_self] at h1
  have h2 : cross L.e0 (((x + 2) - x) • L.e0 + (y - (y + 1)) • L.v) = 0 := by rw [← h1]; simp [cross]
  have h3 : cross L.e0 (((x + 2) - x) • L.e0 + (y - (y + 1)) • L.v) = - cross L.e0 L.v := by
    simp only [cross, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have := L.hcr
  linarith

include hcop in
/-- **Angles of the standard cells.** -/
theorem grid_up_angles {i j : ℕ} (h : i + j + 1 ≤ k) :
    ∃ n : Fin (k * k), TileVerts ((gridD he hef k hk).tile n) ((gridL he hef).pt (i : ℝ) (j : ℝ))
        ((gridL he hef).pt ((i : ℝ) + 1) (j : ℝ)) ((gridL he hef).pt (i : ℝ) ((j : ℝ) + 1)) ∧
      ((gridD he hef k hk).tile n).localAngle ((gridL he hef).pt (i : ℝ) (j : ℝ)) = gβ e f ∧
      ((gridD he hef k hk).tile n).localAngle ((gridL he hef).pt ((i : ℝ) + 1) (j : ℝ)) = gα e f ∧
      ((gridD he hef k hk).tile n).localAngle ((gridL he hef).pt (i : ℝ) ((j : ℝ) + 1)) = gγ e f := by
  obtain ⟨n, hv⟩ := grid_up he hef hk h
  exact ⟨n, hv, up_anglesB (gridD_model he hef hcop k hk) (gridL he hef) hv⟩

include hcop in
theorem grid_down_angles {i j : ℕ} (h : i + j + 2 ≤ k) :
    ∃ n : Fin (k * k), TileVerts ((gridD he hef k hk).tile n) ((gridL he hef).pt ((i : ℝ) + 1) (j : ℝ))
        ((gridL he hef).pt (i : ℝ) ((j : ℝ) + 1)) ((gridL he hef).pt ((i : ℝ) + 1) ((j : ℝ) + 1)) ∧
      ((gridD he hef k hk).tile n).localAngle ((gridL he hef).pt ((i : ℝ) + 1) (j : ℝ)) = gγ e f ∧
      ((gridD he hef k hk).tile n).localAngle ((gridL he hef).pt (i : ℝ) ((j : ℝ) + 1)) = gα e f ∧
      ((gridD he hef k hk).tile n).localAngle ((gridL he hef).pt ((i : ℝ) + 1) ((j : ℝ) + 1)) = gβ e f := by
  obtain ⟨n, hv⟩ := grid_down he hef hk h
  exact ⟨n, hv, down_anglesB (gridD_model he hef hcop k hk) (gridL he hef) hv⟩

theorem tile_up_pts {n : Fin (k * k)} {i j : ℕ}
    (hn : (gridD he hef k hk).tile n = cellUp ptA (gB e f) (gC e f) (gInd he hef) i j) :
    ((gridD he hef k hk).tile n).pts 0 = (gridL he hef).pt (i : ℝ) (j : ℝ) ∧
    ((gridD he hef k hk).tile n).pts 1 = (gridL he hef).pt ((i : ℝ) + 1) (j : ℝ) ∧
    ((gridD he hef k hk).tile n).pts 2 = (gridL he hef).pt (i : ℝ) ((j : ℝ) + 1) := by
  rw [hn]
  exact ⟨(cellUp_pts0 _ _ _ _ i j).trans (P_eq he hef i j), (cellUp_pts1 _ _ _ _ i j).trans (P_succ_l he hef i j),
    (cellUp_pts2 _ _ _ _ i j).trans (P_succ_r he hef i j)⟩

theorem tile_down_pts {n : Fin (k * k)} {i j : ℕ}
    (hn : (gridD he hef k hk).tile n = cellDown ptA (gB e f) (gC e f) (gInd he hef) i j) :
    ((gridD he hef k hk).tile n).pts 0 = (gridL he hef).pt ((i : ℝ) + 1) (j : ℝ) ∧
    ((gridD he hef k hk).tile n).pts 1 = (gridL he hef).pt (i : ℝ) ((j : ℝ) + 1) ∧
    ((gridD he hef k hk).tile n).pts 2 = (gridL he hef).pt ((i : ℝ) + 1) ((j : ℝ) + 1) := by
  rw [hn]
  exact ⟨(cellDown_pts0 _ _ _ _ i j).trans (P_succ_l he hef i j),
    (cellDown_pts1 _ _ _ _ i j).trans (P_succ_r he hef i j),
    (cellDown_pts2 _ _ _ _ i j).trans (P_succ_b he hef i j)⟩

/-- **Adjacent cells share the expected edges.**  The down cell `(i,j)` shares its `b`-edge with the up cell `(i,j)`,
its `a`-edge with the up cell `(i+1,j)` and its `c`-edge with the up cell `(i,j+1)`; the tiles are distinct, and
the three shared edges have the lengths `b`, `a`, `c`. -/
theorem grid_adjacent {i j : ℕ} (h : i + j + 2 ≤ k) :
    ∃ u1 u2 u3 d : Fin (k * k), u1 ≠ d ∧ u2 ≠ d ∧ u3 ≠ d ∧
      (((gridD he hef k hk).tile u1).pts 1 = ((gridD he hef k hk).tile d).pts 0 ∧
        ((gridD he hef k hk).tile u1).pts 2 = ((gridD he hef k hk).tile d).pts 1 ∧
        dist (((gridD he hef k hk).tile d).pts 0) (((gridD he hef k hk).tile d).pts 1) = (tb e f : ℝ)) ∧
      (((gridD he hef k hk).tile u2).pts 0 = ((gridD he hef k hk).tile d).pts 0 ∧
        ((gridD he hef k hk).tile u2).pts 2 = ((gridD he hef k hk).tile d).pts 2 ∧
        dist (((gridD he hef k hk).tile d).pts 0) (((gridD he hef k hk).tile d).pts 2) = (ta e f : ℝ)) ∧
      (((gridD he hef k hk).tile u3).pts 0 = ((gridD he hef k hk).tile d).pts 1 ∧
        ((gridD he hef k hk).tile u3).pts 1 = ((gridD he hef k hk).tile d).pts 2 ∧
        dist (((gridD he hef k hk).tile d).pts 1) (((gridD he hef k hk).tile d).pts 2) = (tc e f : ℝ)) := by
  obtain ⟨u1, hu1⟩ := gridDiss_tile_up ptA (gB e f) (gC e f) (gInd he hef) k hk (i := i) (j := j) (by omega)
  obtain ⟨u2, hu2⟩ := gridDiss_tile_up ptA (gB e f) (gC e f) (gInd he hef) k hk (i := i + 1) (j := j) (by omega)
  obtain ⟨u3, hu3⟩ := gridDiss_tile_up ptA (gB e f) (gC e f) (gInd he hef) k hk (i := i) (j := j + 1) (by omega)
  obtain ⟨d, hd⟩ := gridDiss_tile_down ptA (gB e f) (gC e f) (gInd he hef) k hk (i := i) (j := j) h
  obtain ⟨a0, a1, a2⟩ := tile_up_pts he hef hk (n := u1) hu1
  obtain ⟨b0, b1, b2⟩ := tile_up_pts he hef hk (n := u2) hu2
  obtain ⟨c0, c1, c2⟩ := tile_up_pts he hef hk (n := u3) hu3
  obtain ⟨d0, d1, d2⟩ := tile_down_pts he hef hk (n := d) hd
  set L := gridL he hef with hL
  have hc1 : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
  have hc2 : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
  rw [hc1] at b0 b1 b2
  rw [hc2] at c0 c1 c2
  refine ⟨u1, u2, u3, d, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · intro hh
    rw [hh] at a0
    exact L.pt_ne_x (i : ℝ) (j : ℝ) (a0.symm.trans d0)
  · intro hh
    rw [hh] at b1
    have : (i : ℝ) + 1 + 1 = (i : ℝ) + 2 := by ring
    rw [this] at b1
    exact L.pt_ne_2x_y (i : ℝ) (j : ℝ) (b1.symm.trans d1)
  · intro hh
    rw [hh] at c1
    exact L.pt_ne_x (i : ℝ) ((j : ℝ) + 1) (d1.symm.trans c1)
  · rw [a1, d0]
  · rw [a2, d1]
  · rw [d0, d1]; exact L.dist_pt_b _ _
  · rw [b0, d0]
  · rw [b2, d2]
  · rw [d0, d2]
    have := L.dist_pt_a ((i : ℝ) + 1) (j : ℝ)
    exact this
  · rw [c0, d1]
  · rw [c1, d2]
  · rw [d1, d2]
    have := L.dist_pt_c (i : ℝ) ((j : ℝ) + 1)
    exact this


include hcop in
/-- **`third_up` on the patch.**  A tile with the `c`-edge `[(x,ρ),(x+1,ρ)]`, `β` at `(x,ρ)` and third vertex above
exists in the grid (hypotheses of `third_upB` hold), and `third_upB` returns the lattice vertex `(x,ρ+1)`. -/
theorem grid_third_up {x ρ : ℕ} (h : x + ρ + 1 ≤ k) :
    ∃ (i : Fin (k * k)) (Z : Plane),
      TileVerts ((gridD he hef k hk).tile i) ((gridL he hef).pt (x : ℝ) (ρ : ℝ))
        ((gridL he hef).pt ((x : ℝ) + 1) (ρ : ℝ)) Z ∧
      ((gridD he hef k hk).tile i).localAngle ((gridL he hef).pt (x : ℝ) (ρ : ℝ)) = gβ e f ∧
      0 < cross (gridL he hef).e0 (Z - (gridL he hef).pt (x : ℝ) (ρ : ℝ)) ∧
      Z = (gridL he hef).pt (x : ℝ) ((ρ : ℝ) + 1) := by
  obtain ⟨i, hv⟩ := grid_up he hef hk h
  have M := gridD_model he hef hcop k hk
  have hβ := (up_anglesB M (gridL he hef) hv).1
  have hup : 0 < cross (gridL he hef).e0
      ((gridL he hef).pt (x : ℝ) ((ρ : ℝ) + 1) - (gridL he hef).pt (x : ℝ) (ρ : ℝ)) := by
    rw [BLat.pt_sub]
    have : ((x : ℝ) - x) • (gridL he hef).e0 + (((ρ : ℝ) + 1) - ρ) • (gridL he hef).v = (gridL he hef).v := by
      module
    rw [this]; exact (gridL he hef).hcr
  exact ⟨i, _, hv, hβ, hup, third_upB M (gridL he hef) hv hβ hup⟩

include hcop in
/-- **`third_down` on the patch.** -/
theorem grid_third_down {x y : ℕ} (h : x + y + 2 ≤ k) :
    ∃ (i : Fin (k * k)) (Z : Plane),
      TileVerts ((gridD he hef k hk).tile i) ((gridL he hef).pt ((x : ℝ) + 1) (y : ℝ))
        ((gridL he hef).pt (x : ℝ) ((y : ℝ) + 1)) Z ∧
      ((gridD he hef k hk).tile i).localAngle ((gridL he hef).pt ((x : ℝ) + 1) (y : ℝ)) = gγ e f ∧
      cross ((gridL he hef).pt (x : ℝ) ((y : ℝ) + 1) - (gridL he hef).pt ((x : ℝ) + 1) (y : ℝ))
        (Z - (gridL he hef).pt ((x : ℝ) + 1) (y : ℝ)) < 0 ∧
      Z = (gridL he hef).pt ((x : ℝ) + 1) ((y : ℝ) + 1) := by
  obtain ⟨i, hv⟩ := grid_down he hef hk h
  have M := gridD_model he hef hcop k hk
  have hγ := (down_anglesB M (gridL he hef) hv).1
  have hside : cross ((gridL he hef).pt (x : ℝ) ((y : ℝ) + 1) - (gridL he hef).pt ((x : ℝ) + 1) (y : ℝ))
      ((gridL he hef).pt ((x : ℝ) + 1) ((y : ℝ) + 1) - (gridL he hef).pt ((x : ℝ) + 1) (y : ℝ)) < 0 := by
    rw [BLat.pt_sub, BLat.pt_sub]
    have e1 : ((x : ℝ) - ((x : ℝ) + 1)) • (gridL he hef).e0 + (((y : ℝ) + 1) - y) • (gridL he hef).v =
        (gridL he hef).v - (gridL he hef).e0 := by module
    have e2 : (((x : ℝ) + 1) - ((x : ℝ) + 1)) • (gridL he hef).e0 + (((y : ℝ) + 1) - y) • (gridL he hef).v =
        (gridL he hef).v := by module
    rw [e1, e2]
    have : cross ((gridL he hef).v - (gridL he hef).e0) (gridL he hef).v = - cross (gridL he hef).e0 (gridL he hef).v := by
      simp only [cross, PiLp.sub_apply]; ring
    rw [this]; linarith [(gridL he hef).hcr]
  exact ⟨i, _, hv, hγ, hside, third_downB M (gridL he hef) hv hγ hside⟩

/-- Negative control: the mirror vertex `(x, ρ−1)` (below the line) does NOT satisfy the side hypothesis of `third_up`. -/
theorem third_up_mirror_rejected (L : BLat e f) (x ρ : ℝ) :
    ¬ 0 < cross L.e0 (L.pt x (ρ - 1) - L.pt x ρ) := by
  rw [BLat.pt_sub]
  have : (x - x) • L.e0 + ((ρ - 1) - ρ) • L.v = -L.v := by module
  rw [this]
  have h2 : cross L.e0 (-L.v) = - cross L.e0 L.v := by simp only [cross, PiLp.neg_apply]; ring
  rw [h2]; linarith [L.hcr]

end GridLemmas

/-! ## The covering configurations of `h_cover` and `l_cover` on the patch -/

section Covers

variable {e f : ℕ}

theorem cross_neg_e0_pt (L : BLat e f) (x y ρ : ℝ) :
    cross (-L.e0) (L.pt x y) = cross (-L.e0) (L.pt 0 ρ) - (y - ρ) * cross L.e0 L.v := by
  simp only [cross, BLat.pt, PiLp.add_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]; ring

theorem cross_hyp_pt (L : BLat e f) (x y x0 y0 : ℝ) :
    cross (L.v - L.e0) (L.pt x y) =
      cross (L.v - L.e0) (L.pt x0 y0) - ((x - x0) + (y - y0)) * cross L.e0 L.v := by
  simp only [cross, BLat.pt, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; ring

theorem fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by revert i; decide

/-- The bottom edge of an up tile lies in the far chain of `Λ_ρ` (the chain of `lineChain (-e0)`). -/
theorem upTile_mem_lineChain {N : ℕ} (D' : Dissection N) (L : BLat e f) {n : Fin N} {x ρ : ℝ}
    (h0 : (D'.tile n).pts 0 = L.pt x ρ) (h1 : (D'.tile n).pts 1 = L.pt (x + 1) ρ)
    (h2 : (D'.tile n).pts 2 = L.pt x (ρ + 1)) :
    (n, (0 : Fin 3)) ∈ D'.lineChain (crossL (-L.e0)) (cross (-L.e0) (L.pt 0 ρ)) := by
  rw [Dissection.mem_lineChain]
  have hX := L.hcr
  refine ⟨?_, ?_, ?_⟩
  · simp only [crossL_apply]; rw [h0, cross_neg_e0_pt L x ρ ρ]; ring
  · have : (0 : Fin 3) + 1 = 1 := rfl
    simp only [crossL_apply]; rw [this, h1, cross_neg_e0_pt L (x + 1) ρ ρ]; ring
  · intro i
    simp only [crossL_apply]
    rcases fin3_cases i with rfl | rfl | rfl
    · rw [h0, cross_neg_e0_pt L x ρ ρ]; nlinarith
    · rw [h1, cross_neg_e0_pt L (x + 1) ρ ρ]; nlinarith
    · rw [h2, cross_neg_e0_pt L x (ρ + 1) ρ]; nlinarith

/-- The hypotenuse of a down tile whose hypotenuse lies on the line `x + y = x0 + y0 - 1 + 1` lies in the chain of
`lineChain (v - e0)`. -/
theorem downTile_mem_lineChain {N : ℕ} (D' : Dissection N) (L : BLat e f) {n : Fin N} {x y x0 y0 : ℝ}
    (hlev : (x + 1) + y = x0 + y0)
    (h0 : (D'.tile n).pts 0 = L.pt (x + 1) y) (h1 : (D'.tile n).pts 1 = L.pt x (y + 1))
    (h2 : (D'.tile n).pts 2 = L.pt (x + 1) (y + 1)) :
    (n, (0 : Fin 3)) ∈ D'.lineChain (crossL (L.v - L.e0)) (cross (L.v - L.e0) (L.pt x0 y0)) := by
  rw [Dissection.mem_lineChain]
  have hX := L.hcr
  refine ⟨?_, ?_, ?_⟩
  · simp only [crossL_apply]; rw [h0, cross_hyp_pt L (x + 1) y x0 y0]
    have : (x + 1 - x0) + (y - y0) = 0 := by linarith
    rw [this]; ring
  · have : (0 : Fin 3) + 1 = 1 := rfl
    simp only [crossL_apply]; rw [this, h1, cross_hyp_pt L x (y + 1) x0 y0]
    have : (x - x0) + (y + 1 - y0) = 0 := by linarith
    rw [this]; ring
  · intro i
    simp only [crossL_apply]
    rcases fin3_cases i with rfl | rfl | rfl
    · rw [h0, cross_hyp_pt L (x + 1) y x0 y0]; nlinarith
    · rw [h1, cross_hyp_pt L x (y + 1) x0 y0]; nlinarith
    · rw [h2, cross_hyp_pt L (x + 1) (y + 1) x0 y0]; nlinarith

variable (he : 1 ≤ e) (hef : e < f) {k : ℕ} (hk : 0 < k)

/-- **The shape of `h_cover` on the patch.**  For the row `Λ_ρ` and `n' + ρ ≤ k`: for each `κ < n'` there is an
edge of the far chain of `Λ_ρ`, with its two ends at the consecutive lattice positions `n' − κ − 1`, `n' − κ`. -/
theorem grid_hcover {ρ n' : ℕ} (h : n' + ρ ≤ k) :
    ∀ κ : ℕ, κ < n' →
      ∃ e' ∈ (gridD he hef k hk).toDissection.lineChain (crossL (-(gridL he hef).e0))
          (cross (-(gridL he hef).e0) ((gridL he hef).pt 0 (ρ : ℝ))),
        ((((gridD he hef k hk).tile e'.1).pts e'.2 = (gridL he hef).pt ((n' : ℝ) - κ) (ρ : ℝ) ∧
          ((gridD he hef k hk).tile e'.1).pts (e'.2 + 1) = (gridL he hef).pt ((n' : ℝ) - κ - 1) (ρ : ℝ)) ∨
         (((gridD he hef k hk).tile e'.1).pts e'.2 = (gridL he hef).pt ((n' : ℝ) - κ - 1) (ρ : ℝ) ∧
          ((gridD he hef k hk).tile e'.1).pts (e'.2 + 1) = (gridL he hef).pt ((n' : ℝ) - κ) (ρ : ℝ))) := by
  intro κ hκ
  obtain ⟨u, hu⟩ := gridDiss_tile_up ptA (gB e f) (gC e f) (gInd he hef) k hk (i := n' - κ - 1) (j := ρ) (by omega)
  obtain ⟨a0, a1, a2⟩ := tile_up_pts he hef hk (n := u) hu
  have hx : ((n' - κ - 1 : ℕ) : ℝ) = (n' : ℝ) - κ - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  rw [hx] at a0 a1 a2
  refine ⟨(u, 0), upTile_mem_lineChain (gridD he hef k hk).toDissection (gridL he hef) a0 a1 a2, Or.inr ⟨?_, ?_⟩⟩
  · exact a0
  · have : (0 : Fin 3) + 1 = 1 := rfl
    show ((gridD he hef k hk).tile u).pts (0 + 1) = _
    rw [this, a1]; congr 1; ring

/-- **The shape of the third clause of `l_cover` on the patch.**  Hypotenuse `x + y = m + r + 1` through
`J = (m+1, r)`: for each `κ < s ≤ m + 1` there is an edge of the chain of `lineChain (v - e0)` from
`(m+1-κ, r+κ)` to `(m-κ, r+κ+1)`, as in `l_cover`; here `m + r + 2 ≤ k`. -/
theorem grid_lcover {m r s : ℕ} (hs : s ≤ m + 1) (h : m + r + 2 ≤ k) :
    ∀ κ : ℕ, κ < s →
      ∃ e' ∈ (gridD he hef k hk).toDissection.lineChain (crossL ((gridL he hef).v - (gridL he hef).e0))
          (cross ((gridL he hef).v - (gridL he hef).e0) ((gridL he hef).pt ((m : ℝ) + 1) (r : ℝ))),
        ((((gridD he hef k hk).tile e'.1).pts e'.2 = (gridL he hef).pt ((m : ℝ) + 1 - κ) ((r : ℝ) + κ) ∧
          ((gridD he hef k hk).tile e'.1).pts (e'.2 + 1) =
            (gridL he hef).pt ((m : ℝ) + 1 - (κ + 1)) ((r : ℝ) + (κ + 1))) ∨
         (((gridD he hef k hk).tile e'.1).pts e'.2 = (gridL he hef).pt ((m : ℝ) + 1 - (κ + 1)) ((r : ℝ) + (κ + 1)) ∧
          ((gridD he hef k hk).tile e'.1).pts (e'.2 + 1) = (gridL he hef).pt ((m : ℝ) + 1 - κ) ((r : ℝ) + κ))) := by
  intro κ hκ
  obtain ⟨d, hd⟩ := gridDiss_tile_down ptA (gB e f) (gC e f) (gInd he hef) k hk (i := m - κ) (j := r + κ) (by omega)
  obtain ⟨a0, a1, a2⟩ := tile_down_pts he hef hk (n := d) hd
  have hx : ((m - κ : ℕ) : ℝ) = (m : ℝ) - κ := by rw [Nat.cast_sub (by omega)]
  have hy : ((r + κ : ℕ) : ℝ) = (r : ℝ) + κ := by push_cast; ring
  rw [hx, hy] at a0 a1 a2
  refine ⟨(d, 0), downTile_mem_lineChain (gridD he hef k hk).toDissection (gridL he hef)
    (x0 := (m : ℝ) + 1) (y0 := (r : ℝ)) (by ring) a0 a1 a2, Or.inl ⟨?_, ?_⟩⟩
  · rw [show (m : ℝ) + 1 - κ = (m : ℝ) - κ + 1 by ring]; exact a0
  · have : (0 : Fin 3) + 1 = 1 := rfl
    show ((gridD he hef k hk).tile d).pts (0 + 1) = _
    rw [this, a1]; congr 1 <;> ring

end Covers

/-! ## The row sum, `TRule`, `ARule` -/

section Rules

variable {e f : ℕ}

/-- **The near-side edges tile the segment**: the `n` consecutive `c`-edges of the row `Λ_ρ` add up to the chord. -/
theorem row_sum (L : BLat e f) (ρ : ℝ) (n : ℕ) :
    ∑ κ ∈ Finset.range n, dist (L.pt ((n : ℝ) - κ - 1) ρ) (L.pt ((n : ℝ) - κ) ρ) =
      dist (L.pt 0 ρ) (L.pt (n : ℝ) ρ) := by
  have h1 : ∀ κ ∈ Finset.range n, dist (L.pt ((n : ℝ) - κ - 1) ρ) (L.pt ((n : ℝ) - κ) ρ) = (tc e f : ℝ) := by
    intro κ _
    have := L.dist_pt_c ((n : ℝ) - κ - 1) ρ
    rwa [show (n : ℝ) - κ - 1 + 1 = (n : ℝ) - κ by ring] at this
  rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, L.dist_pt]
  have : (0 - (n : ℝ)) • L.e0 + (ρ - ρ) • L.v = (-(n : ℝ)) • L.e0 := by module
  rw [this, norm_smul, L.he0]
  simp

variable (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f) {k : ℕ} (hk : 0 < k)

/-- **Premises of `TRule` hold.**  At the level `lv` with `lv + m + 2 ≤ k`: `Ground lv (m+1)`, the `m+1` up tiles
`UpCell 0 … UpCell m` on level `lv`, and (the conclusion) `DownCell m lv`. -/
theorem grid_TRule_premises {m lv : ℕ} (h : lv + m + 2 ≤ k) :
    GroundB (gridD he hef k hk).tile (gridL he hef) lv (m + 1) ∧
    (∀ x : ℕ, x ≤ m → UpCellB (gridD he hef k hk).tile (gridL he hef) (x : ℝ) (lv : ℝ)) ∧
    DownCellB (gridD he hef k hk).tile (gridL he hef) (m : ℝ) (lv : ℝ) := by
  refine ⟨?_, fun x hx => grid_up he hef hk (by omega), grid_down he hef hk (by omega)⟩
  rcases Nat.eq_zero_or_pos lv with rfl | hpos
  · exact grid_ground_zero he hef hk _
  · obtain ⟨ρ, rfl⟩ : ∃ ρ, lv = ρ + 1 := ⟨lv - 1, by omega⟩
    exact grid_ground he hef hk (by omega)

/-- **`TRule` holds in the grid** (for `H + 1 ≤ k`), and its premise is satisfied (previous theorem). -/
theorem grid_TRule (m H : ℕ) (hH : H + 1 ≤ k) :
    TRuleB (gridD he hef k hk).tile (gridL he hef) H m :=
  fun lv hlv _ _ _ => grid_down he hef hk (by omega)

include hcop in
/-- **The premise of `ARule` (all hypotheses but the last) is satisfied**, and the last one is false: the tile
`Y` with the `c`-edge `[J, J + e0]` from `J = (m+1, lv)` and third vertex above has angle `β` at `J`. -/
theorem grid_ARule_premise {m lv : ℕ} (h : lv + m + 2 ≤ k) :
    GroundB (gridD he hef k hk).tile (gridL he hef) lv (m + 1) ∧
    (∀ x : ℕ, x ≤ m → UpCellB (gridD he hef k hk).tile (gridL he hef) (x : ℝ) (lv : ℝ)) ∧
    ∃ (i : Fin (k * k)) (K Z : Plane) (t : ℝ),
      TileVerts ((gridD he hef k hk).tile i) ((gridL he hef).pt ((m : ℝ) + 1) (lv : ℝ)) K Z ∧
      K = (gridL he hef).pt ((m : ℝ) + 1) (lv : ℝ) + t • (gridL he hef).e0 ∧ 0 < t ∧
      (dist ((gridL he hef).pt ((m : ℝ) + 1) (lv : ℝ)) K = (tb e f : ℝ) ∨
        dist ((gridL he hef).pt ((m : ℝ) + 1) (lv : ℝ)) K = (tc e f : ℝ)) ∧
      0 < cross (gridL he hef).e0 (Z - (gridL he hef).pt ((m : ℝ) + 1) (lv : ℝ)) ∧
      ((gridD he hef k hk).tile i).localAngle ((gridL he hef).pt ((m : ℝ) + 1) (lv : ℝ)) = gβ e f := by
  obtain ⟨hG, hU, -⟩ := grid_TRule_premises he hef hk (m := m) (lv := lv) h
  refine ⟨hG, hU, ?_⟩
  obtain ⟨n, hv, hβ, -, -⟩ := grid_up_angles he hef hcop hk (i := m + 1) (j := lv) (by omega)
  have hm : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  rw [hm] at hv hβ
  refine ⟨n, _, _, 1, hv, ?_, one_pos, Or.inr ?_, ?_, hβ⟩
  · simp only [BLat.pt]; module
  · exact (gridL he hef).dist_pt_c _ _
  · rw [BLat.pt_sub]
    have : (((m : ℝ) + 1) - ((m : ℝ) + 1)) • (gridL he hef).e0 + (((lv : ℝ) + 1) - lv) • (gridL he hef).v =
        (gridL he hef).v := by module
    rw [this]; exact (gridL he hef).hcr

end Rules

/-! ## The instances: `(e,f) = (2,3)`, `(3,5)`, `(3,7)`, `(3,8)` with explicit coordinates -/

section Instances

theorem nums_2_3 : (ta 2 3 : ℝ) = 6 ∧ (tb 2 3 : ℝ) = 5 ∧ (tc 2 3 : ℝ) = 9 := by norm_num [ta, tb, tc]
theorem nums_3_5 : (ta 3 5 : ℝ) = 15 ∧ (tb 3 5 : ℝ) = 16 ∧ (tc 3 5 : ℝ) = 25 := by norm_num [ta, tb, tc]
theorem nums_3_7 : (ta 3 7 : ℝ) = 21 ∧ (tb 3 7 : ℝ) = 40 ∧ (tc 3 7 : ℝ) = 49 := by norm_num [ta, tb, tc]
theorem nums_3_8 : (ta 3 8 : ℝ) = 24 ∧ (tb 3 8 : ℝ) = 55 ∧ (tc 3 8 : ℝ) = 64 := by norm_num [ta, tb, tc]

/-- Explicit coordinates of `C` for `(2,3)` (`a,b,c = 6,5,9`): `C = (46/9, 20√2/9)`. -/
theorem coord_2_3 : cx 6 5 9 = 46 / 9 ∧ cy 6 5 9 = 20 * Real.sqrt 2 / 9 := by
  have hx : cx 6 5 9 = 46 / 9 := by unfold cx; norm_num
  refine ⟨hx, ?_⟩
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs := Real.sqrt_nonneg 2
  apply eq_of_sq' (Real.sqrt_nonneg _) (by positivity)
  rw [Real.sq_sqrt (by rw [hx]; norm_num), hx]
  have e : (20 * Real.sqrt 2 / 9) ^ 2 = 400 * Real.sqrt 2 ^ 2 / 81 := by ring
  rw [e, h2]; norm_num

/-- Explicit coordinates of `C` for `(3,7)` (`a,b,c = 21,40,49`): `C = (621/49, 60√187/49)`. -/
theorem coord_3_7 : cx 21 40 49 = 621 / 49 ∧ cy 21 40 49 = 60 * Real.sqrt 187 / 49 := by
  have hx : cx 21 40 49 = 621 / 49 := by unfold cx; norm_num
  refine ⟨hx, ?_⟩
  have h2 : Real.sqrt 187 ^ 2 = 187 := Real.sq_sqrt (by norm_num)
  have hs := Real.sqrt_nonneg 187
  apply eq_of_sq' (Real.sqrt_nonneg _) (by positivity)
  rw [Real.sq_sqrt (by rw [hx]; norm_num), hx]
  have e : (60 * Real.sqrt 187 / 49) ^ 2 = 3600 * Real.sqrt 187 ^ 2 / 2401 := by ring
  rw [e, h2]; norm_num

/-- The bundled statement for the member `(e,f)` and the `4`-fold grid. -/
def CtlStmt (e f : ℕ) (he : 1 ≤ e) (hef : e < f) : Prop :=
  let T := (gridD he hef 4 (by norm_num)).tile
  let L := gridL he hef
  ModelData (gridD he hef 4 (by norm_num)) e f (gα e f) (gβ e f) (gγ e f) ∧
  UpCellB T L 0 0 ∧ UpCellB T L 1 0 ∧ UpCellB T L 0 1 ∧ DownCellB T L 0 0 ∧
  GroundB T L 0 2 ∧ GroundB T L 1 2 ∧
  (∀ x : ℕ, x ≤ 1 → UpCellB T L (x : ℝ) 1) ∧ DownCellB T L 1 1 ∧ DownCellB T L 1 0 ∧
  TRuleB T L 3 1 ∧ StdB T L 0 2 1

theorem ctl_holds (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f) : CtlStmt e f he hef := by
  have hk : 0 < 4 := by norm_num
  have g00 : UpCellB (gridD he hef 4 hk).tile (gridL he hef) ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ) :=
    grid_up he hef hk (by norm_num)
  have g10 : UpCellB (gridD he hef 4 hk).tile (gridL he hef) ((1 : ℕ) : ℝ) ((0 : ℕ) : ℝ) :=
    grid_up he hef hk (by norm_num)
  have g01 : UpCellB (gridD he hef 4 hk).tile (gridL he hef) ((0 : ℕ) : ℝ) ((1 : ℕ) : ℝ) :=
    grid_up he hef hk (by norm_num)
  have d00 : DownCellB (gridD he hef 4 hk).tile (gridL he hef) ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ) :=
    grid_down he hef hk (by norm_num)
  have d11 : DownCellB (gridD he hef 4 hk).tile (gridL he hef) ((1 : ℕ) : ℝ) ((1 : ℕ) : ℝ) :=
    grid_down he hef hk (by norm_num)
  have d10 : DownCellB (gridD he hef 4 hk).tile (gridL he hef) ((1 : ℕ) : ℝ) ((0 : ℕ) : ℝ) :=
    grid_down he hef hk (by norm_num)
  have gr1 : GroundB (gridD he hef 4 hk).tile (gridL he hef) 1 2 := by
    have := grid_ground he hef hk (ρ := 0) (k' := 2) (by norm_num)
    exact this
  refine ⟨gridD_model he hef hcop 4 hk, by simpa using g00, by simpa using g10, by simpa using g01,
    by simpa using d00, grid_ground_zero he hef hk 2, gr1, ?_, by simpa using d11, by simpa using d10,
    grid_TRule he hef hk 1 3 (by norm_num), grid_std he hef hk (r := 0) (m := 2) (by norm_num) 1⟩
  intro x hx
  have := grid_up he hef hk (i := x) (j := 1) (by omega)
  simpa using this

theorem ctl_2_3 : CtlStmt 2 3 (by norm_num) (by norm_num) := ctl_holds 2 3 _ _ (by norm_num)
theorem ctl_3_5 : CtlStmt 3 5 (by norm_num) (by norm_num) := ctl_holds 3 5 _ _ (by norm_num)
theorem ctl_3_7 : CtlStmt 3 7 (by norm_num) (by norm_num) := ctl_holds 3 7 _ _ (by norm_num)
theorem ctl_3_8 : CtlStmt 3 8 (by norm_num) (by norm_num) := ctl_holds 3 8 _ _ (by norm_num)

/-- The explicit vertices of the standard up tile at `(0,0)` for `(2,3)`. -/
theorem upTile_00_2_3 :
    (cellUp ptA (gB 2 3) (gC 2 3) (gInd (by norm_num) (by norm_num)) 0 0).pts 0 = mkPt 0 0 ∧
    (cellUp ptA (gB 2 3) (gC 2 3) (gInd (by norm_num) (by norm_num)) 0 0).pts 1 = mkPt 9 0 ∧
    (cellUp ptA (gB 2 3) (gC 2 3) (gInd (by norm_num) (by norm_num)) 0 0).pts 2 =
      mkPt (46 / 9) (20 * Real.sqrt 2 / 9) := by
  obtain ⟨n1, n2, n3⟩ := nums_2_3
  obtain ⟨cx1, cy1⟩ := coord_2_3
  have h1 : (cellUp ptA (gB 2 3) (gC 2 3) (gInd (by norm_num) (by norm_num)) 0 0).pts 1 = gB 2 3 := by
    show P ptA (gB 2 3) (gC 2 3) (0 + 1) 0 = _
    simp [P]
  have h2 : (cellUp ptA (gB 2 3) (gC 2 3) (gInd (by norm_num) (by norm_num)) 0 0).pts 2 = gC 2 3 := by
    show P ptA (gB 2 3) (gC 2 3) 0 (0 + 1) = _
    simp [P]
  have h0 : (cellUp ptA (gB 2 3) (gC 2 3) (gInd (by norm_num) (by norm_num)) 0 0).pts 0 = ptA := by
    show P ptA (gB 2 3) (gC 2 3) 0 0 = _
    simp [P]
  refine ⟨h0, ?_, ?_⟩
  · rw [h1]; unfold gB ptB; rw [n3]
  · rw [h2]; unfold gC ptC; rw [n1, n2, n3, cx1, cy1]

end Instances

#print axioms third_up_via_bare
#print axioms gridD_model
#print axioms grid_up
#print axioms grid_down
#print axioms grid_ground
#print axioms grid_std
#print axioms grid_adjacent
#print axioms grid_third_up
#print axioms grid_third_down
#print axioms grid_hcover
#print axioms grid_lcover
#print axioms row_sum
#print axioms grid_TRule_premises
#print axioms grid_TRule
#print axioms grid_ARule_premise
#print axioms ctl_2_3
#print axioms ctl_3_5
#print axioms ctl_3_7
#print axioms ctl_3_8
#print axioms upTile_00_2_3

end Erdos634.LaczMJ
