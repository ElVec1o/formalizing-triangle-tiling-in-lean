import Erdos634.Draft.LaczFormalColumnWit
import Erdos634.Draft.LaczFormalColumnArith
import Erdos634.Draft.LaczFormalMJBare

/-!
# The Column Lemma (C1–C4) in Lean: exact statements and what is proved

Erdős #634, base-`β` row.  Credit: AI assistant (the Column Lemma proposal, `FABLE_MIXEDROW_2026-10-21/ANSWER.md` §1, items
C1–C4), Beeson–Roșu (the tile, the lattice `K`, Lemmas 28–37), Beeson, Laczkovich (fan/chord covers).  UNAUDITED.
Axiom-clean; no `sorry`.  This file does NOT touch the Closure Lemma (a hand-proof target, probability 0.6, named gap:
multi-event stacks).

Tile `(a,b,c) = (ef, f²−e², f²)`, `1 ≤ e < f`, `gcd(e,f) = 1`; `ec = fa`; `f b = (f−e)(a+c)`.

## The setting (no corner is mentioned)

* `FaultSeg D g c P G`: a horizontal-type fault segment `[P,G]` on the line `{g = c}`: its open segment is interior to
  the target and lies in the interior of no tile (it is a union of tile edges); no chain edge of `{g = c}` passes through
  `P` or `G` (`¬ Straddled`).  The chain is `D.lineChain g c`, the tile edges on the line from the side `g ≤ c`.
* `WallAt D g c x`: `x` lies on a `β`-WALL `{g = c}` (an interior line crossed by no tile at `x`): every tile through `x`
  lies wholly on one closed side.  A wall point is not straddled by any transversal line (`wall_not_straddled`).
* `WFrame` (`LaczFormalColumnLat`): the lattice frame of the standard `c`-cells at a `β`-wall.

## What is established (an honest mapping to C1–C4 of `ANSWER.md`)

* **C1 (narrow columns have pure rows): the RIGID KERNEL.**  `C1_c_row`: a fault segment of length `n c`, `n < e`, has
  upper chain `c^n` at the lattice positions (vacuous for `e = 1`); `C1_a_row`: of length `n a`, `n < f`, `a^n`;
  `C1_between_walls`: the same with the end conditions given by two walls.  Proof: `far_positions` + `MJ_jc_unique`,
  `MJ_ka_unique`.  `C1_c_cells` is `WFrame.MJ_main` under another name: the cell-level rules `T(m)`, `A(m)`, `m + 1 ≤ e`, of a
  `c`-column standing at an uncrossed wall (levels `lv ≥ 1`).  NOT formalized: the decomposition of `Σ(Λ)` into maximal
  columns and the identification of their boundaries as walls or chords: these are HYPOTHESES here (`FaultSeg`, `WallAt`,
  `BetaWall`).  NOT formalized: the cell-level statement for `a`-columns (the `A(k)` induction of the `a`-lattice).
  Row-to-row invariance (the counting form of 'rows cannot switch'): `LaczFormalColumnC2.C1_counts_invariant`: two `b`-free
  fault segments of the same length `w < e c` have the same numbers of `a`- and of `c`-edges (`LaczColumn.bfree_unique_below`);
  only the ARRANGEMENT of the edges can differ.  CAVEAT: a fault segment of mixed width `x a + z c < e c` (`x, z ≥ 1`) is not
  excluded by anything here: C1 says a row whose width is a pure multiple (`n c`, `n < e`, or `n a`, `n < f`) is pure; it does
  not say that every column of width `< e c` has such a width.  `LaczFormalColumnBoundary`: the same wall frame with the
  lattice based at a point of a LEG of the target (`BoundaryWall`, `boundary_T_rule`), the setting of the cap lemma.
* **C2 (walls): the divisibility form only.**  `ColumnArith`: `L_c ∩ L_a = ⟨ec⟩` (`meet_param`); `C2_wall_segment` (file
  `LaczFormalColumnC2`): a straight two-sided fault segment whose one chain is all `a` and the other all `c` has length
  `t · e c`, `t ≥ 1`; `C2_no_common_below`: it is not shorter than `e c`.  The hypotheses `hA`, `hC` (pure edge types on the two
  sides) must be supplied: that a wall between an `a`-column and a `c`-column has these edge types is NOT derived.
* **C3 (chords): purity of a chord cover only.**  `C3_b_row`: a fault segment of length `n b`, `n < f`, has chain `b^n`;
  `LaczColumn.chord_second_cover`: `f b = (f−e)(a+c)` (the chord threshold).  `WFrame.l_cover` is available inside the copied
  frame under the standard-rows hypotheses but is not restated here.  NOT established: the shrinking of a chord column
  to a scaled tile `Δ_j` (the staircase: every row of a `c`-column over `m + 1` ups is standard).
* **C4 (the events): the arithmetic thresholds and the block count.**  `C4_events`, `C4_sharp`, `LaczColumn.bfree_cover_c/a`
  (the `b`-free covers of `n c` and `n a` are the blocks `a^{sf} c^{n−se}`, resp. `a^{n−sf} c^{se}`); `C4_bfree_counts`
  (`LaczFormalColumnC2`): in a `b`-free fault row of length `n c` the number of `a`-edges is `s f` and of `c`-edges `n − s e`:
  the `a`-edges come in blocks of `f`, whatever their arrangement (`a^p c^m a^q`, `p + q = f`).  The structural claim (`Σ(Λ)` is determined by
  `Λ` and the walls except at the events) is NOT formalized.

NOT proved at all: the Closure Lemma.
-/

namespace Erdos634.LaczCol

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.TraceCovering Erdos634.LaczMJ Erdos634.LaczWall Set

variable {N : ℕ}

/-! ## The setting -/

/-- A fault segment: `[P,G]` on the line `{g = c}`, interior to the target, covered by tile edges (no tile interior meets
the open segment), and not straddled at its ends. -/
structure FaultSeg (D : Dissection N) (P G : Plane) (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) : Prop where
  hne : P ≠ G
  hg0 : g ≠ 0
  hgP : g P = c
  hgG : g G = c
  hint : ∀ t : ℝ, 0 < t → t < 1 → AffineMap.lineMap P G t ∈ interior D.target.carrier
  hwall : ∀ t : ℝ, 0 < t → t < 1 → ∀ i, AffineMap.lineMap P G t ∉ interior (D.tile i).carrier
  hP : ¬ Straddled D g c P
  hG : ¬ Straddled D g c G

/-- The far chain of `[P,G]` is `n` edges of length `L` at the lattice positions `k/n`. -/
def PureCover (D : Dissection N) (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) (P G : Plane) (n : ℕ) (L : ℝ) : Prop :=
  (∀ e ∈ D.lineChain g c, (D.tile e.1).edge e.2 ⊆ segment ℝ P G →
    dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = L) ∧
  (∀ e ∈ D.lineChain g c, (D.tile e.1).edge e.2 ⊆ segment ℝ P G → ∃ k : ℕ, k < n ∧
    (((D.tile e.1).pts e.2 = AffineMap.lineMap P G ((k : ℝ) / n) ∧
      (D.tile e.1).pts (e.2 + 1) = AffineMap.lineMap P G (((k : ℝ) + 1) / n)) ∨
     ((D.tile e.1).pts e.2 = AffineMap.lineMap P G (((k : ℝ) + 1) / n) ∧
      (D.tile e.1).pts (e.2 + 1) = AffineMap.lineMap P G ((k : ℝ) / n)))) ∧
  ∀ k : ℕ, k < n → ∃ e ∈ D.lineChain g c,
    (((D.tile e.1).pts e.2 = AffineMap.lineMap P G ((k : ℝ) / n) ∧
      (D.tile e.1).pts (e.2 + 1) = AffineMap.lineMap P G (((k : ℝ) + 1) / n)) ∨
     ((D.tile e.1).pts e.2 = AffineMap.lineMap P G (((k : ℝ) + 1) / n) ∧
      (D.tile e.1).pts (e.2 + 1) = AffineMap.lineMap P G ((k : ℝ) / n)))

/-- `x` is a point of a `β`-wall `{g = c}`: every tile through `x` lies wholly on one closed side. -/
def WallAt (D : Dissection N) (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) (x : Plane) : Prop :=
  g x = c ∧ ∀ i, x ∈ (D.tile i).carrier → (D.tile i).carrier ⊆ {y | g y ≤ c} ∨ (D.tile i).carrier ⊆ {y | c ≤ g y}

/-- A wall point is not straddled by a line transversal to the wall. -/
theorem WallAt.not_straddled {D : Dissection N} {g k : Plane →ₗ[ℝ] ℝ} {c d : ℝ} {x : Plane} (h : WallAt D g c x)
    (htrans : ∀ w, g w = 0 → k w = 0 → w = 0) : ¬ Straddled D k d x :=
  wall_not_straddled D g k c d h.1 htrans h.2

/-! ## C1: pure rows -/

section Rows

variable {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}

/-- The edges of the tiles have the lengths `a`, `b`, `c` (from the model data only). -/
theorem habc_md (M : ModelData D e f α β γ) (i : Fin N) (k : Fin 3) :
    dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = (ta e f : ℝ) ∨
    dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = (tb e f : ℝ) ∨
    dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = (tc e f : ℝ) := by
  rcases edge_length_mem D i k with h | h | h
  · exact Or.inr (Or.inr (by rw [h, M.hsc]))
  · exact Or.inr (Or.inl (by rw [h, M.hsb]))
  · exact Or.inl (by rw [h, M.hsa])

/-- **C1 for `c`-rows** (model data only).  A fault segment of length `n c`, `n < e`, has far chain `c^n` at the lattice
positions. -/
theorem C1_c_row_md (M : ModelData D e f α β γ) (hcop : Nat.Coprime e f) {P G : Plane} {g : Plane →ₗ[ℝ] ℝ} {c : ℝ}
    (hF : FaultSeg D.toDissection P G g c) {n : ℕ} (hn : n < e) (hPG : dist P G = (n : ℝ) * tc e f) :
    PureCover D.toDissection g c P G n (tc e f) :=
  far_positions D.toDissection (ta e f) (tb e f) (tc e f) (tc e f) n
    (fun x y z h => by
      obtain ⟨hx, hy, hz⟩ := MJ_jc_unique e f x y z n M.he M.hef hcop hn h
      exact ⟨Or.inr hx, Or.inr hy, Or.inl rfl⟩)
    (fun i k => habc_md M i k) hF.hne hPG (by exact_mod_cast LaczColumn.tc_pos' e f M.hef) g c hF.hg0 hF.hgP hF.hgG
    hF.hint hF.hwall hF.hP hF.hG

/-- **C1 for `a`-rows** (model data only).  A fault segment of length `n a`, `n < f`, has far chain `a^n`. -/
theorem C1_a_row_md (M : ModelData D e f α β γ) (hcop : Nat.Coprime e f) {P G : Plane} {g : Plane →ₗ[ℝ] ℝ} {c : ℝ}
    (hF : FaultSeg D.toDissection P G g c) {n : ℕ} (hn : n < f) (hPG : dist P G = (n : ℝ) * ta e f) :
    PureCover D.toDissection g c P G n (ta e f) :=
  far_positions D.toDissection (ta e f) (tb e f) (tc e f) (ta e f) n
    (fun x y z h => by
      obtain ⟨hx, hy, hz⟩ := LaczColumn.MJ_ka_unique e f x y z n M.he M.hef hcop hn h
      exact ⟨Or.inl rfl, Or.inr hy, Or.inr hz⟩)
    (fun i k => habc_md M i k) hF.hne hPG (by exact_mod_cast LaczColumn.ta_pos' e f M.he M.hef) g c hF.hg0 hF.hgP
    hF.hgG hF.hint hF.hwall hF.hP hF.hG

/-- **C3 for chords** (model data only).  A fault segment (a chord, any direction) of length `n b`, `n < f`, has far chain
`b^n`. -/
theorem C3_b_row_md (M : ModelData D e f α β γ) (hcop : Nat.Coprime e f) {P G : Plane} {g : Plane →ₗ[ℝ] ℝ} {c : ℝ}
    (hF : FaultSeg D.toDissection P G g c) {n : ℕ} (hn : n < f) (hPG : dist P G = (n : ℝ) * tb e f) :
    PureCover D.toDissection g c P G n (tb e f) :=
  far_positions D.toDissection (ta e f) (tb e f) (tc e f) (tb e f) n
    (fun x y z h => by
      obtain ⟨hx, hy, hz⟩ := MJ_jb_unique e f x y z n M.he M.hef hcop hn h
      exact ⟨Or.inr hx, Or.inl rfl, Or.inr hz⟩)
    (fun i k => habc_md M i k) hF.hne hPG (by exact_mod_cast b_pos e f M.he M.hef) g c hF.hg0 hF.hgP hF.hgG
    hF.hint hF.hwall hF.hP hF.hG

/-- **C1 for `c`-rows** (band setting).  Vacuous for `e = 1` (no `n` with `1 ≤ n < 1`; `P ≠ G` forces `n ≥ 1`). -/
theorem C1_c_row (S : BandSetup D e f α β γ p q r) {P G : Plane} {g : Plane →ₗ[ℝ] ℝ} {c : ℝ}
    (hF : FaultSeg D.toDissection P G g c) {n : ℕ} (hn : n < e) (hPG : dist P G = (n : ℝ) * tc e f) :
    PureCover D.toDissection g c P G n (tc e f) :=
  C1_c_row_md (bandSetup_toModelData S) S.hcop hF hn hPG

/-- **C1 for `a`-rows** (band setting). -/
theorem C1_a_row (S : BandSetup D e f α β γ p q r) {P G : Plane} {g : Plane →ₗ[ℝ] ℝ} {c : ℝ}
    (hF : FaultSeg D.toDissection P G g c) {n : ℕ} (hn : n < f) (hPG : dist P G = (n : ℝ) * ta e f) :
    PureCover D.toDissection g c P G n (ta e f) :=
  C1_a_row_md (bandSetup_toModelData S) S.hcop hF hn hPG

/-- **C3 for chords** (band setting). -/
theorem C3_b_row (S : BandSetup D e f α β γ p q r) {P G : Plane} {g : Plane →ₗ[ℝ] ℝ} {c : ℝ}
    (hF : FaultSeg D.toDissection P G g c) {n : ℕ} (hn : n < f) (hPG : dist P G = (n : ℝ) * tb e f) :
    PureCover D.toDissection g c P G n (tb e f) :=
  C3_b_row_md (bandSetup_toModelData S) S.hcop hF hn hPG

/-- **C1 between two walls.**  Let `P` and `G` be points of two `β`-walls `{gL = cL}`, `{gR = cR}` (transversal to the line
`{g = c}` through them) joined by a fault segment of length `n c`, `n < e` (the open segment interior to the target and
covered by tile edges).  Then the far chain of the segment is `c^n`: a column of width `n c < e c` between two walls has pure
rows.  (`a`-columns: `C1_a_row`, `n < f`.) -/
theorem C1_between_walls (S : BandSetup D e f α β γ p q r) {P G : Plane} {g gL gR : Plane →ₗ[ℝ] ℝ}
    {c cL cR : ℝ} (hne : P ≠ G) (hg0 : g ≠ 0) (hgP : g P = c) (hgG : g G = c)
    (hint : ∀ t : ℝ, 0 < t → t < 1 → AffineMap.lineMap P G t ∈ interior D.target.carrier)
    (hwall : ∀ t : ℝ, 0 < t → t < 1 → ∀ i, AffineMap.lineMap P G t ∉ interior (D.tile i).carrier)
    (hWL : WallAt D.toDissection gL cL P) (hWR : WallAt D.toDissection gR cR G)
    (htL : ∀ w, gL w = 0 → g w = 0 → w = 0) (htR : ∀ w, gR w = 0 → g w = 0 → w = 0)
    {n : ℕ} (hn : n < e) (hPG : dist P G = (n : ℝ) * tc e f) :
    PureCover D.toDissection g c P G n (tc e f) :=
  C1_c_row S ⟨hne, hg0, hgP, hgG, hint, hwall, hWL.not_straddled htL, hWR.not_straddled htR⟩ hn hPG

/-- **C1, cell level** (a `c`-column at a `β`-wall): the rules `T(m)`, `A(m)` for all `m` with `m + 1 ≤ e` at the levels
`lv ≥ 1`; this is `WFrame.MJ_main` (the induction `M(j)` re-parametrised to a wall frame). -/
theorem C1_c_cells {α β γ : ℝ} (F : WFrame D e f α β γ p q r) {H : ℕ} (hB : F.Bnd H) :
    ∀ m, F.TRule H m ∧ F.ARule H m := F.MJ_main hB

end Rows

/-! ## C2: the wall -/

section Wall

variable {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}

/-- The vertices of the standard `c`-cells on the wall are at the heights `y a`. -/
theorem WFrame.wall_vertices_a (F : WFrame D e f α β γ p q r) (y y' : ℝ) :
    dist (F.pt 0 y) (F.pt 0 y') = |y - y'| * (ta e f : ℝ) := by
  have : dist (F.pt 0 y) (F.pt 0 y') = ‖((0 : ℝ) - 0) • F.e0 + (y - y') • F.v‖ := by
    rw [dist_eq_norm]; congr 1; simp only [WFrame.pt]; module
  rw [this]
  simp only [sub_self, zero_smul, zero_add, norm_smul, F.hv, Real.norm_eq_abs]

end Wall

/-! ## C4: the events -/

section Events

/-- **C4.**  Below the thresholds the covers are unique; the thresholds are attained. -/
theorem C4_events (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f) :
    (∀ n x y z : ℕ, n < e → x * ta e f + y * tb e f + z * tc e f = n * tc e f → x = 0 ∧ y = 0 ∧ z = n) ∧
    (∀ n x y z : ℕ, n < f → x * ta e f + y * tb e f + z * tc e f = n * ta e f → x = n ∧ y = 0 ∧ z = 0) ∧
    (∀ n x y z : ℕ, n < f → x * ta e f + y * tb e f + z * tc e f = n * tb e f → x = 0 ∧ y = n ∧ z = 0) ∧
    e * tc e f = f * ta e f ∧ f * tb e f = (f - e) * ta e f + (f - e) * tc e f :=
  ⟨fun n x y z hn h => LaczJunction.MJ_jc_unique e f x y z n he hef hcop hn h,
   fun n x y z hn h => LaczColumn.MJ_ka_unique e f x y z n he hef hcop hn h,
   fun n x y z hn h => LaczJunction.MJ_jb_unique e f x y z n he hef hcop hn h,
   LaczColumn.ec_eq_fa' e f, LaczColumn.chord_second_cover e f hef⟩

/-- **C4, negative control.**  Each threshold statement fails exactly at the threshold: the three uniqueness statements
are false at `n = e`, `n = f`, `n = f`. -/
theorem C4_sharp (e f : ℕ) (he : 1 ≤ e) (hef : e < f) :
    ¬ (∀ x y z : ℕ, x * ta e f + y * tb e f + z * tc e f = e * tc e f → x = 0 ∧ y = 0 ∧ z = e) ∧
    ¬ (∀ x y z : ℕ, x * ta e f + y * tb e f + z * tc e f = f * ta e f → x = f ∧ y = 0 ∧ z = 0) ∧
    ¬ (∀ x y z : ℕ, x * ta e f + y * tb e f + z * tc e f = f * tb e f → x = 0 ∧ y = f ∧ z = 0) :=
  ⟨LaczColumn.col_pure_c_fails_at_e e f he (by omega), LaczColumn.col_pure_a_fails_at_f e f he hef,
   LaczColumn.chord_cover_fails_at_f e f he hef⟩

end Events

end Erdos634.LaczCol
