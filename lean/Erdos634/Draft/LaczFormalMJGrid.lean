import Erdos634.Draft.LaczFormalMJBare
import Erdos634.CellCoord
import Erdos634.CertCoord

/-!
# A genuine `CongruentDissection` with standard cells: the `k`-fold grid of the explicit tile (control layer)

Erdős #634, base-`β` band.  Credit: AI assistant (item 3, band program, rule `M(j)`), Beeson–Roșu, Beeson,
Laczkovich, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.

Explicit coordinates.  For the tile with sides `a = ta e f`, `b = tb e f`, `c = tc e f` put
`A = (0,0)` (the `β` vertex), `B = (c,0)` (the `α` vertex), `C = (cx, cy)` (the `γ` vertex), with
`cx = (a²+c²−b²)/(2c)`, `cy = √(a² − cx²)`.  The lattice is `O = A`, `e0 = B−A`, `v = C−A`.
`gridD e f k` is `Subdivision.ladderDissection A B C k` (the triangle `kT` cut into `k²` copies of the tile) as a
`CongruentDissection` whose model is `(B, A, C)` (the `α`-vertex first, as `ModelData` wants).  Its tiles are
`cellUp i j` and `cellDown i j`, i.e. exactly the standard up cell (`β` at `(i,j)`, `α` at `(i+1,j)`, `γ` at
`(i,j+1)`) and the standard down cell of the hand proof.  Hence the predicates `UpCellB`, `DownCellB`, `GroundB`
are satisfied here, on a REAL dissection (of the target `kT`, not of a band target).
-/

namespace Erdos634.LaczMJ

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Subdivision Erdos634.CertCoord

/-! ## Explicit coordinates of the tile -/

section Coord

/-- `x`-coordinate of the `γ` vertex. -/
noncomputable def cx (a b c : ℝ) : ℝ := (a ^ 2 + c ^ 2 - b ^ 2) / (2 * c)
/-- `y`-coordinate of the `γ` vertex. -/
noncomputable def cy (a b c : ℝ) : ℝ := Real.sqrt (a ^ 2 - cx a b c ^ 2)

noncomputable def ptA : Plane := mkPt 0 0
noncomputable def ptB (c : ℝ) : Plane := mkPt c 0
noncomputable def ptC (a b c : ℝ) : Plane := mkPt (cx a b c) (cy a b c)

theorem eq_of_sq' {d c : ℝ} (hd : 0 ≤ d) (hc : 0 ≤ c) (h : d ^ 2 = c ^ 2) : d = c := by
  nlinarith [sq_nonneg (d - c), sq_nonneg (d + c)]

variable {a b c : ℝ}

theorem cy_sq (hpos : 0 < a ^ 2 - cx a b c ^ 2) : cy a b c ^ 2 = a ^ 2 - cx a b c ^ 2 := by
  unfold cy; exact Real.sq_sqrt hpos.le

theorem cy_pos (hpos : 0 < a ^ 2 - cx a b c ^ 2) : 0 < cy a b c := by
  unfold cy; exact Real.sqrt_pos.mpr hpos

theorem dist_BA (hc : 0 < c) : dist (ptB c) ptA = c := by
  apply eq_of_sq' dist_nonneg hc.le
  unfold ptB ptA; rw [dist_sq_mkPt]; ring

theorem dist_CA (ha : 0 < a) (hc : 0 < c) (hpos : 0 < a ^ 2 - cx a b c ^ 2) : dist (ptC a b c) ptA = a := by
  apply eq_of_sq' dist_nonneg ha.le
  unfold ptC ptA; rw [dist_sq_mkPt]; linear_combination cy_sq hpos

theorem dist_CB (hb : 0 < b) (hc : 0 < c) (hpos : 0 < a ^ 2 - cx a b c ^ 2) :
    dist (ptC a b c) (ptB c) = b := by
  apply eq_of_sq' dist_nonneg hb.le
  unfold ptC ptB; rw [dist_sq_mkPt]
  have h := cy_sq hpos
  have hcx : 2 * c * cx a b c = a ^ 2 + c ^ 2 - b ^ 2 := by unfold cx; field_simp
  linear_combination h - hcx

theorem cross_ABC (hc : 0 < c) (hpos : 0 < a ^ 2 - cx a b c ^ 2) :
    0 < cross (ptB c - ptA) (ptC a b c - ptA) := by
  have := cy_pos hpos
  unfold ptB ptA ptC
  simp only [cross, PiLp.sub_apply, mkPt_zero, mkPt_one]
  nlinarith

theorem indep_ABC (hc : 0 < c) (hpos : 0 < a ^ 2 - cx a b c ^ 2) :
    AffineIndependent ℝ ![ptA, ptB c, ptC a b c] := by
  have hcr := cross_ABC (a := a) (b := b) hc hpos
  have hdet : det3 0 0 c 0 (cx a b c) (cy a b c) ≠ 0 := by
    have := cy_pos hpos
    unfold det3
    nlinarith
  have := (mkTri 0 0 c 0 (cx a b c) (cy a b c) hdet).indep
  rw [mkTri_pts] at this
  exact this

end Coord

/-! ## The grid as a `CongruentDissection` -/

section Grid

/-- The `k`-fold grid of the triangle `ABC` (with `β` at `A`, `α` at `B`, `γ` at `C`) as a `CongruentDissection`
with model `(B, A, C)`. -/
noncomputable def gridDiss (A B C : Plane) (hind : AffineIndependent ℝ ![A, B, C]) (k : ℕ) (hk : 0 < k) :
    CongruentDissection (k * k) :=
  CongruentDissection.relabelModel
    { toDissection := ladderDissection A B C hind k hk
      model := (⟨![A, B, C], hind⟩ : Tri)
      tiles_congruent := fun n => (ladderDissection_congruent A B C hind k hk n).symm }
    (Equiv.swap 0 1)

theorem gridDiss_model_pts (A B C : Plane) (hind : AffineIndependent ℝ ![A, B, C]) (k : ℕ) (hk : 0 < k) :
    (gridDiss A B C hind k hk).model.pts 0 = B ∧ (gridDiss A B C hind k hk).model.pts 1 = A ∧
      (gridDiss A B C hind k hk).model.pts 2 = C := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [gridDiss, CongruentDissection.relabelModel_model_pts, Equiv.swap_apply_def]

theorem gridDiss_tile_up (A B C : Plane) (hind : AffineIndependent ℝ ![A, B, C]) (k : ℕ) (hk : 0 < k)
    {i j : ℕ} (h : i + j + 1 ≤ k) :
    ∃ n, (gridDiss A B C hind k hk).tile n = cellUp A B C hind i j := by
  have hmem : ((true, i, j) : Bool × ℕ × ℕ) ∈ cellSet k := by
    simp only [cellSet, Finset.mem_union, Finset.mem_image]
    left; exact ⟨(i, j), mem_upSet.mpr h, rfl⟩
  refine ⟨(cellIdx k).symm ⟨_, hmem⟩, ?_⟩
  show cellOf A B C hind ((cellIdx k ((cellIdx k).symm ⟨_, hmem⟩) : Bool × ℕ × ℕ)) = _
  rw [Equiv.apply_symm_apply]; simp [cellOf]

theorem gridDiss_tile_down (A B C : Plane) (hind : AffineIndependent ℝ ![A, B, C]) (k : ℕ) (hk : 0 < k)
    {i j : ℕ} (h : i + j + 2 ≤ k) :
    ∃ n, (gridDiss A B C hind k hk).tile n = cellDown A B C hind i j := by
  have hmem : ((false, i, j) : Bool × ℕ × ℕ) ∈ cellSet k := by
    simp only [cellSet, Finset.mem_union, Finset.mem_image]
    right; exact ⟨(i, j), mem_downSet.mpr h, rfl⟩
  refine ⟨(cellIdx k).symm ⟨_, hmem⟩, ?_⟩
  show cellOf A B C hind ((cellIdx k ((cellIdx k).symm ⟨_, hmem⟩) : Bool × ℕ × ℕ)) = _
  rw [Equiv.apply_symm_apply]; simp [cellOf]

end Grid

end Erdos634.LaczMJ
