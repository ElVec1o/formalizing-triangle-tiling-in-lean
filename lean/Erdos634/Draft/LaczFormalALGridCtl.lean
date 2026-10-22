import Erdos634.Draft.LaczFormalALControl
import Erdos634.Draft.LaczFormalMJCellCtl

/-!
# Non-vacuity control for the cell predicates of Lemma A(j): a genuine grid with the standard `a`-lattice cells

Erdős #634, base-`β` row.  Credit: AI assistant (Lemma A(k) proposal), Beeson–Roșu, Beeson, Laczkovich, Paliy.  UNAUDITED.
Axiom-clean; no `sorry`.  This file proves NOTHING new about #634.  It is the exchanged-frame counterpart of
`LaczFormalMJBare`/`MJGrid`/`MJCellCtl` (reusing their coordinate and grid machinery with the roles `a ↔ c` of the two
lattice vectors swapped).

The predicates `AF.UpCell`, `AF.DownCell`, `AF.Ground`, `AF.TRule`, `AF.Std` only use `D.tile` and `F.pt`; `ALat e f` is the
lattice without the target (`e0` of length `a`, `v` of length `c`), `UpCellA`... the predicates for a bare tile family
(`Iff.rfl` to the `AF` ones).  The grid `gridA he hef k hk` is `Subdivision.ladderDissection` of the triangle `kT`,
`T = (A, B, C)` with `A = (0,0)` the `β` vertex, `B = (a, 0)` the `γ` vertex, `C` the `α` vertex (`|AC| = c`, `|BC| = b`),
cut into `k²` copies of the tile (a `CongruentDissection`); with `O = A`, `e0 = B − A`, `v = C − A` its tiles are exactly the
standard `aBG` up cells and the standard down cells.  Hence the premises of `TRule` (ground, the run of `m+1` up tiles) are
satisfiable on a REAL dissection, and `TRule` itself holds there (`grid_TRuleA`).  What is NOT exercised: a band target's
`BandSetup`.
-/

namespace Erdos634.LaczAL

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Subdivision Erdos634.CertCoord Erdos634.LaczMJ

variable {N : ℕ}

/-- The lattice vectors of an exchanged frame, without the target. -/
structure ALat (e f : ℕ) where
  O : Plane
  e0 : Plane
  v : Plane
  he0 : ‖e0‖ = (ta e f : ℝ)
  hv : ‖v‖ = (tc e f : ℝ)
  hu : ‖v - e0‖ = (tb e f : ℝ)
  hcr : 0 < cross e0 v

namespace ALat

variable {e f : ℕ} (L : ALat e f)

def pt (x y : ℝ) : Plane := L.O + x • L.e0 + y • L.v

end ALat

/-- The lattice of an `AF` frame. -/
def AF.toALat {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (F : AF D e f α β γ p q r) : ALat e f :=
  ⟨D.target.pts p, F.e0, F.v, F.he0, F.hv, F.hu, F.hcr⟩

section Preds

variable {e f : ℕ}

def UpCellA (T : Fin N → Erdos634.Geometry.Tri) (L : ALat e f) (x y : ℝ) : Prop :=
  ∃ i : Fin N, Erdos634.LaczJunction.TileVerts (T i) (L.pt x y) (L.pt (x + 1) y) (L.pt x (y + 1))

def DownCellA (T : Fin N → Erdos634.Geometry.Tri) (L : ALat e f) (x y : ℝ) : Prop :=
  ∃ i : Fin N, Erdos634.LaczJunction.TileVerts (T i) (L.pt (x + 1) y) (L.pt x (y + 1)) (L.pt (x + 1) (y + 1))

def GroundA (T : Fin N → Erdos634.Geometry.Tri) (L : ALat e f) (ρ k : ℕ) : Prop :=
  ρ = 0 ∨ ∃ ρ' : ℕ, ρ = ρ' + 1 ∧ ∀ x : ℕ, x ≤ k → UpCellA T L (x : ℝ) (ρ' : ℝ) ∧ DownCellA T L (x : ℝ) (ρ' : ℝ)

def TRuleA (T : Fin N → Erdos634.Geometry.Tri) (L : ALat e f) (H m : ℕ) : Prop :=
  ∀ lv : ℕ, lv + m + 1 ≤ H → m + 1 ≤ f - 1 → GroundA T L lv (m + 1) →
    (∀ x : ℕ, x ≤ m → UpCellA T L (x : ℝ) (lv : ℝ)) → DownCellA T L (m : ℝ) (lv : ℝ)

variable {D : CongruentDissection N} {α β γ : ℝ} {p q r : Fin 3} (F : AF D e f α β γ p q r)

theorem upCellA_iff (x y : ℝ) : F.UpCell x y ↔ UpCellA D.tile F.toALat x y := Iff.rfl
theorem downCellA_iff (x y : ℝ) : F.DownCell x y ↔ DownCellA D.tile F.toALat x y := Iff.rfl
theorem groundA_iff (ρ k : ℕ) : F.Ground ρ k ↔ GroundA D.tile F.toALat ρ k := Iff.rfl
theorem TRuleA_iff (H m : ℕ) : F.TRule H m ↔ TRuleA D.tile F.toALat H m := Iff.rfl

end Preds

/-! ## The grid -/

section Grid

variable {e f : ℕ}

theorem hposGridA (he : 1 ≤ e) (hef : e < f) :
    0 < (tc e f : ℝ) ^ 2 - cx (tc e f : ℝ) (tb e f : ℝ) (ta e f : ℝ) ^ 2 := by
  obtain ⟨t1, t2, t3⟩ := tri_nat he hef
  have t1' : (tc e f : ℝ) < ta e f + tb e f := by exact_mod_cast t1
  have t2' : (ta e f : ℝ) < tb e f + tc e f := by exact_mod_cast t2
  have t3' : (tb e f : ℝ) < ta e f + tc e f := by exact_mod_cast t3
  have ha := pos_a he hef
  have hb := pos_b he hef
  have hc := pos_c he hef
  set a : ℝ := (tc e f : ℝ)
  set b : ℝ := (tb e f : ℝ)
  set c : ℝ := (ta e f : ℝ)
  have key : a ^ 2 - cx a b c ^ 2 =
      (a + c - b) * (a + c + b) * (b - a + c) * (b + a - c) / (4 * c ^ 2) := by
    unfold cx; field_simp; ring
  rw [key]
  have h1 : 0 < a + c - b := by linarith
  have h2 : 0 < a + c + b := by linarith
  have h3 : 0 < b - a + c := by linarith
  have h4 : 0 < b + a - c := by linarith
  positivity

/-- The `γ` vertex `B = (a, 0)` and the `α` vertex `C` of the exchanged tile. -/
noncomputable def hB (e f : ℕ) : Plane := ptB (ta e f : ℝ)
noncomputable def hC (e f : ℕ) : Plane := ptC (tc e f : ℝ) (tb e f : ℝ) (ta e f : ℝ)

theorem hInd (he : 1 ≤ e) (hef : e < f) : AffineIndependent ℝ ![ptA, hB e f, hC e f] :=
  indep_ABC (pos_a he hef) (hposGridA he hef)

theorem hdist_BA (he : 1 ≤ e) (hef : e < f) : dist (hB e f) ptA = (ta e f : ℝ) :=
  dist_BA (pos_a he hef)

theorem hdist_CA (he : 1 ≤ e) (hef : e < f) : dist (hC e f) ptA = (tc e f : ℝ) :=
  dist_CA (pos_c he hef) (pos_a he hef) (hposGridA he hef)

theorem hdist_CB (he : 1 ≤ e) (hef : e < f) : dist (hC e f) (hB e f) = (tb e f : ℝ) :=
  dist_CB (pos_b he hef) (pos_a he hef) (hposGridA he hef)

/-- **The grid**: `kT` cut into `k²` copies of the tile of the member `(e,f)`, in the exchanged orientation. -/
noncomputable def gridA (he : 1 ≤ e) (hef : e < f) (k : ℕ) (hk : 0 < k) : CongruentDissection (k * k) :=
  gridDiss ptA (hB e f) (hC e f) (hInd he hef) k hk

/-- **The exchanged lattice of the grid**: `O = A`, `e0 = B − A` (length `a`), `v = C − A` (length `c`). -/
noncomputable def gridLA (he : 1 ≤ e) (hef : e < f) : ALat e f where
  O := ptA
  e0 := hB e f - ptA
  v := hC e f - ptA
  he0 := by rw [← dist_eq_norm]; exact hdist_BA he hef
  hv := by rw [← dist_eq_norm]; exact hdist_CA he hef
  hu := by
    have : (hC e f - ptA) - (hB e f - ptA) = hC e f - hB e f := by abel
    rw [this, ← dist_eq_norm]; exact hdist_CB he hef
  hcr := cross_ABC (pos_a he hef) (hposGridA he hef)

theorem gridLA_pt (he : 1 ≤ e) (hef : e < f) (x y : ℝ) :
    (gridLA he hef).pt x y = ptA + x • (hB e f - ptA) + y • (hC e f - ptA) := rfl

theorem PA_eq (he : 1 ≤ e) (hef : e < f) (i j : ℕ) :
    P ptA (hB e f) (hC e f) i j = (gridLA he hef).pt (i : ℝ) (j : ℝ) := rfl

theorem PA_succ_l (he : 1 ≤ e) (hef : e < f) (i j : ℕ) :
    P ptA (hB e f) (hC e f) (i + 1) j = (gridLA he hef).pt ((i : ℝ) + 1) (j : ℝ) := by
  rw [PA_eq he hef]; simp only [gridLA_pt]; push_cast; rfl

theorem PA_succ_r (he : 1 ≤ e) (hef : e < f) (i j : ℕ) :
    P ptA (hB e f) (hC e f) i (j + 1) = (gridLA he hef).pt (i : ℝ) ((j : ℝ) + 1) := by
  rw [PA_eq he hef]; simp only [gridLA_pt]; push_cast; rfl

theorem PA_succ_b (he : 1 ≤ e) (hef : e < f) (i j : ℕ) :
    P ptA (hB e f) (hC e f) (i + 1) (j + 1) = (gridLA he hef).pt ((i : ℝ) + 1) ((j : ℝ) + 1) := by
  rw [PA_eq he hef]; simp only [gridLA_pt]; push_cast; rfl

variable (he : 1 ≤ e) (hef : e < f) {k : ℕ} (hk : 0 < k)

/-- **Every up cell of the grid is a tile.** -/
theorem grid_upA {i j : ℕ} (h : i + j + 1 ≤ k) :
    UpCellA (gridA he hef k hk).tile (gridLA he hef) (i : ℝ) (j : ℝ) := by
  obtain ⟨n, hn⟩ := gridDiss_tile_up ptA (hB e f) (hC e f) (hInd he hef) k hk h
  have hn' : (gridA he hef k hk).tile n = cellUp ptA (hB e f) (hC e f) (hInd he hef) i j := hn
  refine ⟨n, 0, Or.inl ⟨?_, ?_, ?_⟩⟩
  · rw [hn']; exact (cellUp_pts0 _ _ _ _ i j).trans (PA_eq he hef i j)
  · rw [hn']; exact (cellUp_pts1 _ _ _ _ i j).trans (PA_succ_l he hef i j)
  · rw [hn']; exact (cellUp_pts2 _ _ _ _ i j).trans (PA_succ_r he hef i j)

/-- **Every down cell of the grid is a tile.** -/
theorem grid_downA {i j : ℕ} (h : i + j + 2 ≤ k) :
    DownCellA (gridA he hef k hk).tile (gridLA he hef) (i : ℝ) (j : ℝ) := by
  obtain ⟨n, hn⟩ := gridDiss_tile_down ptA (hB e f) (hC e f) (hInd he hef) k hk h
  have hn' : (gridA he hef k hk).tile n = cellDown ptA (hB e f) (hC e f) (hInd he hef) i j := hn
  refine ⟨n, 0, Or.inl ⟨?_, ?_, ?_⟩⟩
  · rw [hn']; exact (cellDown_pts0 _ _ _ _ i j).trans (PA_succ_l he hef i j)
  · rw [hn']; exact (cellDown_pts1 _ _ _ _ i j).trans (PA_succ_r he hef i j)
  · rw [hn']; exact (cellDown_pts2 _ _ _ _ i j).trans (PA_succ_b he hef i j)

theorem grid_groundA {ρ k' : ℕ} (h : k' + ρ + 2 ≤ k) :
    GroundA (gridA he hef k hk).tile (gridLA he hef) (ρ + 1) k' :=
  Or.inr ⟨ρ, rfl, fun x hx => ⟨grid_upA he hef hk (by omega), grid_downA he hef hk (by omega)⟩⟩

/-- **Premises of `TRule` hold on a real dissection.**  At the level `lv` with `lv + m + 2 ≤ k`: `Ground lv (m+1)`, the
`m+1` up tiles `UpCell 0 … UpCell m` on level `lv` (the `aBG` run), and (the conclusion) `DownCell m lv`. -/
theorem grid_TRule_premisesA {m lv : ℕ} (h : lv + m + 2 ≤ k) :
    GroundA (gridA he hef k hk).tile (gridLA he hef) lv (m + 1) ∧
    (∀ x : ℕ, x ≤ m → UpCellA (gridA he hef k hk).tile (gridLA he hef) (x : ℝ) (lv : ℝ)) ∧
    DownCellA (gridA he hef k hk).tile (gridLA he hef) (m : ℝ) (lv : ℝ) := by
  refine ⟨?_, fun x hx => grid_upA he hef hk (by omega), grid_downA he hef hk (by omega)⟩
  rcases Nat.eq_zero_or_pos lv with rfl | hpos
  · exact Or.inl rfl
  · obtain ⟨ρ, rfl⟩ : ∃ ρ, lv = ρ + 1 := ⟨lv - 1, by omega⟩
    exact grid_groundA he hef hk (by omega)

/-- **`TRule` holds in the grid** (for `H + 1 ≤ k`), with its premise satisfied (previous theorem). -/
theorem grid_TRuleA (m H : ℕ) (hH : H + 1 ≤ k) :
    TRuleA (gridA he hef k hk).tile (gridLA he hef) H m :=
  fun lv hlv _ _ _ => grid_downA he hef hk (by omega)

end Grid

#print axioms Erdos634.LaczAL.grid_upA
#print axioms Erdos634.LaczAL.grid_TRule_premisesA
#print axioms Erdos634.LaczAL.grid_TRuleA

end Erdos634.LaczAL
