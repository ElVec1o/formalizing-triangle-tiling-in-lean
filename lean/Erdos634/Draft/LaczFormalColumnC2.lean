import Erdos634.Draft.LaczFormalColumnStmt

/-!
# C2 in Lean: a straight `β`-wall between an `a`-column and a `c`-column has length `t · e c`

Erdős #634, base-`β` row, Column Lemma (C2).  Credit: AI assistant (Column Lemma proposal, C2 / W1–W2), Beeson–Roșu (the lattice
`K`), Beeson, Laczkovich.  UNAUDITED.  Axiom-clean; no `sorry`.

`C2_wall_segment`: let `[P,G]` be a straight segment which is a fault segment for BOTH of its sides
(`FaultSeg D P G g c` for the chain from the side `g ≤ c`, `FaultSeg D P G (−g) (−c)` for the chain from the side `g ≥ c`;
the ends are non-straddled on both sides, e.g. because they lie on transversal walls).  If every edge of the chain on one side
inside `[P,G]` is an `a`-edge and every edge of the chain on the other side is a `c`-edge (the wall between an `a`-column
and a `c`-column: the `c`-column shows its `a`-edges, the `a`-column its `c`-edges), then

  `|PG| = t · (e c)` with `t ≥ 1`

(in particular `|PG| ≥ e c = f a`, and the number of `a`-edges is `t f`, of `c`-edges `t e`).  Proof: `L3_ns` (the lengths of
the chain edges inside `[P,G]` add up to `|PG|`) and `common_height` (`j a = l c ⇒ f ∣ j`).  `C2_no_common_below`: such a
segment is not shorter than `e c` (the 'first common vertex' form of C2: apply it to the sub-segment `[P,R]` up to a point
`R` at which both chains are non-straddled).  NOTE: the hypotheses `hA`, `hC` (pure edge types on the two sides) are
HYPOTHESES; that the wall between an `a`-column and a `c`-column has these edge types is not derived here.

WITNESSES.  The hypotheses `FaultSeg` are witnessed on the grid (`LaczFormalColumnCtl`); the mixed hypothesis
(`a` on one side, `c` on the other) is NOT witnessed on any genuine dissection available here: the grid is a
single lattice (`c`-edges on rows, `a`-edges on columns, on both sides).  So `C2_wall_segment` is unconditional but its
hypothesis package is not exercised as a whole (recorded audit gap).
-/

namespace Erdos634.LaczCol

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczMJ Erdos634.Draft.TraceCovering Set

variable {N : ℕ}

open Classical in
/-- The total length of the chain edges inside the segment is the length of the segment. -/
theorem FaultSeg.sum_eq {D : Dissection N} {P G : Plane} {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hF : FaultSeg D P G g c) :
    ∑ e ∈ (D.lineChain g c).filter (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ P G),
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = dist P G :=
  L3_ns D hF.hne g c hF.hg0 hF.hgP hF.hgG hF.hint hF.hwall hF.hP hF.hG

/-- If all chain edges inside the segment have length `L`, the segment has length `card · L`. -/
theorem FaultSeg.dist_eq_card {D : Dissection N} {P G : Plane} {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hF : FaultSeg D P G g c)
    {L : ℝ} (hL : ∀ e ∈ D.lineChain g c, (D.tile e.1).edge e.2 ⊆ segment ℝ P G →
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = L) :
    ∃ n : ℕ, dist P G = (n : ℝ) * L := by
  classical
  refine ⟨((D.lineChain g c).filter (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ P G)).card, ?_⟩
  rw [← hF.sum_eq, Finset.sum_congr rfl (fun e he => hL e (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp he).2),
    Finset.sum_const, nsmul_eq_mul]

variable {e f : ℕ}

/-- **C2.**  A straight wall between an `a`-column and a `c`-column has length `t · e c`, `t ≥ 1`. -/
theorem C2_wall_segment (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f) {D : Dissection N} {P G : Plane}
    {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hF : FaultSeg D P G g c) (hF' : FaultSeg D P G (-g) (-c))
    (hA : ∀ e' ∈ D.lineChain g c, (D.tile e'.1).edge e'.2 ⊆ segment ℝ P G →
      dist ((D.tile e'.1).pts e'.2) ((D.tile e'.1).pts (e'.2 + 1)) = (ta e f : ℝ))
    (hC : ∀ e' ∈ D.lineChain (-g) (-c), (D.tile e'.1).edge e'.2 ⊆ segment ℝ P G →
      dist ((D.tile e'.1).pts e'.2) ((D.tile e'.1).pts (e'.2 + 1)) = (tc e f : ℝ)) :
    ∃ t : ℕ, 1 ≤ t ∧ dist P G = (t : ℝ) * ((e : ℝ) * (tc e f : ℝ)) := by
  obtain ⟨j, hj⟩ := hF.dist_eq_card hA
  obtain ⟨l, hl⟩ := hF'.dist_eq_card hC
  have hpos : 0 < dist P G := dist_pos.mpr hF.hne
  have hjl : (j : ℝ) * (ta e f : ℝ) = (l : ℝ) * (tc e f : ℝ) := by rw [← hj, ← hl]
  have hjlN : j * ta e f = l * tc e f := by exact_mod_cast hjl
  obtain ⟨t, hjt, hlt⟩ := (LaczColumn.common_height e f j l he hef hcop).mp hjlN
  have hja : (0 : ℝ) < ta e f := by exact_mod_cast LaczColumn.ta_pos' e f he hef
  have hj0 : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · have : dist P G = 0 := by rw [hj, h0]; simp
      linarith
    · exact h0
  have ht : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · rw [h0] at hjt; omega
    · exact h0
  refine ⟨t, ht, ?_⟩
  rw [hj, hjt]
  have h2 : (e : ℝ) * (tc e f : ℝ) = (f : ℝ) * (ta e f : ℝ) := by exact_mod_cast LaczColumn.ec_eq_fa' e f
  rw [h2]; push_cast; ring

/-- **C2, first common vertex.**  Such a segment is not shorter than `e c`. -/
theorem C2_no_common_below (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f) {D : Dissection N} {P G : Plane}
    {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hF : FaultSeg D P G g c) (hF' : FaultSeg D P G (-g) (-c))
    (hA : ∀ e' ∈ D.lineChain g c, (D.tile e'.1).edge e'.2 ⊆ segment ℝ P G →
      dist ((D.tile e'.1).pts e'.2) ((D.tile e'.1).pts (e'.2 + 1)) = (ta e f : ℝ))
    (hC : ∀ e' ∈ D.lineChain (-g) (-c), (D.tile e'.1).edge e'.2 ⊆ segment ℝ P G →
      dist ((D.tile e'.1).pts e'.2) ((D.tile e'.1).pts (e'.2 + 1)) = (tc e f : ℝ)) :
    (e : ℝ) * (tc e f : ℝ) ≤ dist P G := by
  obtain ⟨t, ht, h⟩ := C2_wall_segment he hef hcop hF hF' hA hC
  rw [h]
  have hec : (0 : ℝ) < (e : ℝ) * (tc e f : ℝ) := by
    have : (0 : ℝ) < (tc e f : ℝ) := by exact_mod_cast LaczColumn.tc_pos' e f hef
    have he' : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
    positivity
  have : (1 : ℝ) ≤ t := by exact_mod_cast ht
  nlinarith

open Classical in
/-- **C4, the count of `a`-edges in a `b`-free row.**  Let `[P,G]` be a fault segment of length `n c` whose chain inside the
segment has no `b`-edge.  Then the number of `a`-edges is `s f` and the number of `c`-edges is `n − s e` for some `s ≥ 0`: the
`a`-edges come in blocks of `f` (width `f a = e c`), whatever their arrangement (`a^p c^m a^q`, `p + q = f`, of the
engine survivors is an arrangement of one block).  `s = 0` is the pure row. -/
theorem C4_bfree_counts (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f) {D : Dissection N} {P G : Plane}
    {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hF : FaultSeg D P G g c) {n : ℕ} (hPG : dist P G = (n : ℝ) * (tc e f : ℝ))
    (hbf : ∀ e' ∈ D.lineChain g c, (D.tile e'.1).edge e'.2 ⊆ segment ℝ P G →
      dist ((D.tile e'.1).pts e'.2) ((D.tile e'.1).pts (e'.2 + 1)) = (ta e f : ℝ) ∨
      dist ((D.tile e'.1).pts e'.2) ((D.tile e'.1).pts (e'.2 + 1)) = (tc e f : ℝ)) :
    ∃ s : ℕ, (((D.lineChain g c).filter (fun e' => (D.tile e'.1).edge e'.2 ⊆ segment ℝ P G)).filter
        (fun e' => dist ((D.tile e'.1).pts e'.2) ((D.tile e'.1).pts (e'.2 + 1)) = (ta e f : ℝ))).card = s * f ∧
      (((D.lineChain g c).filter (fun e' => (D.tile e'.1).edge e'.2 ⊆ segment ℝ P G)).filter
        (fun e' => ¬ dist ((D.tile e'.1).pts e'.2) ((D.tile e'.1).pts (e'.2 + 1)) = (ta e f : ℝ))).card + s * e = n := by
  set S := (D.lineChain g c).filter (fun e' => (D.tile e'.1).edge e'.2 ⊆ segment ℝ P G) with hS
  set len : Fin N × Fin 3 → ℝ := fun e' => dist ((D.tile e'.1).pts e'.2) ((D.tile e'.1).pts (e'.2 + 1)) with hlen
  have hsum := hF.sum_eq
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun e' => len e' = (ta e f : ℝ)) len
  have hA : ∑ e' ∈ S.filter (fun e' => len e' = (ta e f : ℝ)), len e' =
      ((S.filter (fun e' => len e' = (ta e f : ℝ))).card : ℝ) * (ta e f : ℝ) := by
    rw [Finset.sum_congr rfl (fun e' he' => (Finset.mem_filter.mp he').2), Finset.sum_const, nsmul_eq_mul]
  have hC : ∑ e' ∈ S.filter (fun e' => ¬ len e' = (ta e f : ℝ)), len e' =
      ((S.filter (fun e' => ¬ len e' = (ta e f : ℝ))).card : ℝ) * (tc e f : ℝ) := by
    have : ∀ e' ∈ S.filter (fun e' => ¬ len e' = (ta e f : ℝ)), len e' = (tc e f : ℝ) := by
      intro e' he'
      obtain ⟨hmem, hne⟩ := Finset.mem_filter.mp he'
      obtain ⟨hch, hsub⟩ := Finset.mem_filter.mp hmem
      rcases hbf e' hch hsub with h | h
      · exact absurd h hne
      · exact h
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
  have hnat : (S.filter (fun e' => len e' = (ta e f : ℝ))).card * ta e f +
      (S.filter (fun e' => ¬ len e' = (ta e f : ℝ))).card * tc e f = n * tc e f := by
    have : ((S.filter (fun e' => len e' = (ta e f : ℝ))).card : ℝ) * (ta e f : ℝ) +
        ((S.filter (fun e' => ¬ len e' = (ta e f : ℝ))).card : ℝ) * (tc e f : ℝ) = (n : ℝ) * (tc e f : ℝ) := by
      rw [← hA, ← hC, hsplit, hsum, hPG]
    exact_mod_cast this
  obtain ⟨s, h1, h2⟩ := LaczColumn.bfree_cover_c e f _ _ n he hef hcop hnat
  exact ⟨s, h1, h2⟩

/-! ## Counts of `a`- and `c`-edges in a `b`-free fault row -/

open Classical in
/-- The chain edges of the line `{g = c}` (from the side `g ≤ c`) inside the segment `[P,G]`. -/
noncomputable def segChain (D : Dissection N) (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) (P G : Plane) : Finset (Fin N × Fin 3) :=
  (D.lineChain g c).filter (fun e' => (D.tile e'.1).edge e'.2 ⊆ segment ℝ P G)

/-- The length of a tile edge. -/
noncomputable def edgeLen (D : Dissection N) (e' : Fin N × Fin 3) : ℝ :=
  dist ((D.tile e'.1).pts e'.2) ((D.tile e'.1).pts (e'.2 + 1))

open Classical in
/-- The number of chain edges inside `[P,G]` of length `l`. -/
noncomputable def lenCount (D : Dissection N) (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) (P G : Plane) (l : ℝ) : ℕ :=
  ((segChain D g c P G).filter (fun e' => edgeLen D e' = l)).card

open Classical in
/-- **The row sum in counts.**  If every chain edge inside the fault segment has length `la` or `lc` (`la ≠ lc`), then
`|PG| = (#la) la + (#lc) lc`. -/
theorem FaultSeg.dist_counts {D : Dissection N} {P G : Plane} {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hF : FaultSeg D P G g c)
    {la lc : ℝ} (hl : la ≠ lc) (hbf : ∀ e' ∈ segChain D g c P G, edgeLen D e' = la ∨ edgeLen D e' = lc) :
    dist P G = (lenCount D g c P G la : ℝ) * la + (lenCount D g c P G lc : ℝ) * lc := by
  have hsum : ∑ e' ∈ segChain D g c P G, edgeLen D e' = dist P G := hF.sum_eq
  have hsplit := Finset.sum_filter_add_sum_filter_not (segChain D g c P G) (fun e' => edgeLen D e' = la) (edgeLen D)
  have hA : ∑ e' ∈ (segChain D g c P G).filter (fun e' => edgeLen D e' = la), edgeLen D e' =
      (lenCount D g c P G la : ℝ) * la := by
    unfold lenCount
    rw [Finset.sum_congr rfl (fun e' he' => (Finset.mem_filter.mp he').2), Finset.sum_const, nsmul_eq_mul]
  have hset : (segChain D g c P G).filter (fun e' => ¬ edgeLen D e' = la) =
      (segChain D g c P G).filter (fun e' => edgeLen D e' = lc) := by
    ext e'
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hm, hne⟩
      exact ⟨hm, (hbf e' hm).resolve_left hne⟩
    · rintro ⟨hm, hlc⟩
      exact ⟨hm, fun hla => hl (hla.symm.trans hlc)⟩
  have hC : ∑ e' ∈ (segChain D g c P G).filter (fun e' => ¬ edgeLen D e' = la), edgeLen D e' =
      (lenCount D g c P G lc : ℝ) * lc := by
    rw [hset]
    unfold lenCount
    rw [Finset.sum_congr rfl (fun e' he' => (Finset.mem_filter.mp he').2), Finset.sum_const, nsmul_eq_mul]
  rw [← hsum, ← hsplit, hA, hC]

variable {e f : ℕ}

/-- **C1, counts: rows cannot switch.**  Two `b`-free fault segments (in any dissections, on any lines) of the same length
`w < e c` have the same numbers of `a`-edges and of `c`-edges.  (Only the ARRANGEMENT of the edges can differ.) -/
theorem C1_counts_invariant (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f) {N' : ℕ} {D : Dissection N}
    {D' : Dissection N'} {P G P' G' : Plane} {g g' : Plane →ₗ[ℝ] ℝ} {c c' : ℝ} (hF : FaultSeg D P G g c)
    (hF' : FaultSeg D' P' G' g' c')
    (hbf : ∀ e' ∈ segChain D g c P G, edgeLen D e' = (ta e f : ℝ) ∨ edgeLen D e' = (tc e f : ℝ))
    (hbf' : ∀ e' ∈ segChain D' g' c' P' G', edgeLen D' e' = (ta e f : ℝ) ∨ edgeLen D' e' = (tc e f : ℝ))
    (hw : dist P G = dist P' G') (hlt : dist P G < (e : ℝ) * (tc e f : ℝ)) :
    lenCount D g c P G (ta e f : ℝ) = lenCount D' g' c' P' G' (ta e f : ℝ) ∧
      lenCount D g c P G (tc e f : ℝ) = lenCount D' g' c' P' G' (tc e f : ℝ) := by
  have hac : (ta e f : ℝ) ≠ (tc e f : ℝ) := by
    have : ta e f < tc e f := by
      unfold ta tc
      have : e * f < f * f := Nat.mul_lt_mul_of_pos_right hef (by omega)
      nlinarith
    have : ta e f ≠ tc e f := by omega
    exact_mod_cast this
  have h1 := hF.dist_counts hac hbf
  have h2 := hF'.dist_counts hac hbf'
  have heq : ((lenCount D g c P G (ta e f : ℝ) : ℝ) * (ta e f : ℝ) + (lenCount D g c P G (tc e f : ℝ) : ℝ) * (tc e f : ℝ)) =
      ((lenCount D' g' c' P' G' (ta e f : ℝ) : ℝ) * (ta e f : ℝ) +
        (lenCount D' g' c' P' G' (tc e f : ℝ) : ℝ) * (tc e f : ℝ)) := by
    rw [← h1, ← h2, hw]
  have hN : lenCount D g c P G (ta e f : ℝ) * ta e f + lenCount D g c P G (tc e f : ℝ) * tc e f =
      lenCount D' g' c' P' G' (ta e f : ℝ) * ta e f + lenCount D' g' c' P' G' (tc e f : ℝ) * tc e f := by
    exact_mod_cast heq
  have hlt' : lenCount D g c P G (ta e f : ℝ) * ta e f + lenCount D g c P G (tc e f : ℝ) * tc e f < e * tc e f := by
    have : ((lenCount D g c P G (ta e f : ℝ) : ℝ) * (ta e f : ℝ) + (lenCount D g c P G (tc e f : ℝ) : ℝ) * (tc e f : ℝ)) <
        (e : ℝ) * (tc e f : ℝ) := by rw [← h1]; exact hlt
    exact_mod_cast this
  exact LaczColumn.bfree_unique_below e f _ _ _ _ he hef hcop hN hlt'

/-- The number of `a`-edges and `c`-edges on such a wall is `t f` and `t e`. -/
theorem C2_counts (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f) (j l : ℕ) (hj : 0 < j)
    (h : j * ta e f = l * tc e f) : ∃ t : ℕ, 1 ≤ t ∧ j = f * t ∧ l = e * t := by
  obtain ⟨t, hjt, hlt⟩ := (LaczColumn.common_height e f j l he hef hcop).mp h
  refine ⟨t, ?_, hjt, hlt⟩
  rcases Nat.eq_zero_or_pos t with h0 | h0
  · rw [h0] at hjt; omega
  · exact h0

end Erdos634.LaczCol
