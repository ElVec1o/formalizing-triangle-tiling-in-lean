/-
Refactored 14 October 2026: `CtxBase` introduced, lemmas that use only the setup moved to it (no statement changed).
Draft/SideRunGChordB.lean -- written 14 October 2026.  UNAUDITED.  In `AllThreshold`.  Module 4 of ten (part B; part A,
`Draft/SideRunGChord.lean`, has the pushes, `CtxG`, `K3G`, `m_nextG`, `N_pushG`).

The two chord principles and the clamp given by (K3), for EVERY member `(e, f)`: the generalization of the second half of
`Draft/SideRunChord.lean`.  Paper: Theorem `thm:siderunall`, "The `ℓ`-chord principle" and "The `m`-chord principle";
(private working notes, not included)

CONTENTS.
* `exists_bR`, `rep_nat_a`, `rep_nat_b`, `first_len_jbG`: the bridge from the real equations of a partition to the natural
  number statements of `SideRunGArith` (`A1`, `Aa`).
* `wall_partitionG`, `wall_firstG`: the partition (P) of a clamped run into edges of the near-side chain, with the three side
  lengths `e f, f² − e², f²`.  `wall_partitionG` works for ANY chain edge contained in the run (the `m`-chord principle needs
  the edge of (K3)(a), not the first one); `wall_firstG` is the generalization of `W2E1.wall_first`.
* `CtxG.chordG` (the `ℓ`-chord principle, Lemma A1, hypothesis (K1)), `CtxG.phiG` (the tile `φ` at `p(0,j)`).
* `SetupG.interior_seg_two_sides`: an open segment of a line that has a tile of Δ strictly on each side is interior to Δ (the
  paper's "its open part is interior to Δ, because Δ is convex and has tiles on both sides"; here proved, by the three
  functionals of the triangle Δ and `no_support_aux`).
* `CtxG.mchordG` (the `m`-chord principle, Lemma Aa, hypothesis (K3) second form), `CtxG.psiG` (the tile `ψ` at `p(s − J, J)`),
  `CtxG.K3G_clamp` (the consumer interface: the conclusion of `SideRun.Ctx.K3_clamp` from `K3G`).
* Specialisation checks at `e = 1` (end of the file): `chord_e1`, `phi_e1`, `K3G_clamp_e1`.

THE STATEMENT OF THE `m`-CHORD PRINCIPLE.  `mchordG` is the contradiction form (conclusion `False`), like `SideRun.Ctx.chord`:
a tile `w` on the side `ρ_s` with an edge `[p(s − η₁, η₁), p(s − η₂, η₂)]` of length `b` or `c` (`η₁ < η₂ ≤ J`), the point
`Z = p(s − η₁, η₁)` clamped from below, `J < f`, the tiles `U(s − 1 − j', j')`, `η₁ ≤ j' < J`, and a clamp of the end
`p(s − J, J)` (no near-side chain edge straddles it): contradiction.  `psiG` is the covering conclusion: a tile `ψ` on the side
`ρ_s` has `p(s − J, J)` in the relative interior of an edge on `m_s` (it shows a straight angle there and contains every short
push into `ρ_s`).  Case `η₂ > J`: `ψ = w`.  Case `η₂ ≤ J`: `mchordG` against the negation, through `straddle_data`.

WHAT THE PAPER LEAVES TO THE READER (found while writing it).
(1) "Its open part is interior to Δ because Δ is convex and has tiles on both sides of the line": a convex set can have an
    open chord on its frontier, and it has tiles on both sides only if the third vertices of the two tiles are strictly on the
    two sides; `interior_seg_two_sides` is this argument made precise (a functional of Δ that vanishes at both ends of the
    chord is proportional to `GS` and is `≥ 0` at two points on opposite sides, so it is `0`).  It needs a third vertex of `w`
    (strictly on `ρ_s`, from the non-degeneracy of the tile) and a third vertex of a tile `U` (strictly on the other side).
(2) "One of which is the edge of (K3)(a)": the edge of (K3)(a) is a partition edge only if it lies in the chord
    `[Z, p(s − j, j)]`, i.e. `η₂ ≤ j`; if `η₂ > j` the point `p(s − j, j)` is in its relative interior and `ψ = w` directly.
    The two cases are in `psiG`.  The partition is used with the edge of (K3)(a) (`wall_partitionG`), not with the first edge
    (so no uniqueness of the tile at `Z` is needed, unlike a reading through `first_edge`).
(3) The hypothesis `j ≤ s'` of the paper's `m`-chord principle is not used; what is used is `j − j_1 ≤ f − 1` (Lemma Aa).
(4) The clamp (K3)(b) is "for the side `ρ_{s'}`"; in the `Straddles` form of `RunPartition` it has to hold for every run
    `[Z, Q]` upward, with one lattice point `P'` below `Z` (`ClampedBelowG`, part A); the two sources of the paper give it.
(5) The `ℓ`-chord principle for `j* = 0` only (the form of `CtxG`); `j* > 0` needs the general (K1).

NON-SPECIALISATION.  `chordG`/`phiG` specialise to `Ctx.chord`/`Ctx.phi` at `e = 1` (`chord_e1`, `phi_e1`, from the general
statements).  `mchordG`/`psiG`/`K3G_clamp` have no e = 1 counterpart in the e = 1 text (there (K3) is the one long edge of
`j a < b`; see the header of part A).  `K3G_clamp_e1` is the e = 1 instance of `K3G_clamp`: the conclusion of `Ctx.K3_clamp`
at `η = j0 + 1`, under `K3G` instead of `K3`, the rows of `U` tiles `U(s − 1 − j', j')`, `j' ≤ j0`, and `j0 + 1 < n`.
`K3_of_K3G_e1`: at `e = 1`, `s + 1 ≤ n`, `K3G` implies `K3`; the converse is not claimed.

WITNESSES.  `chordG`, `mchordG` conclude `False` (they are the contradiction engines of the proof by contradiction, as
`SideRun.Ctx.chord`): their hypotheses are not satisfiable together in a real dissection, and their value is in `phiG`/`psiG`,
whose hypotheses ARE the data of a real dissection when the negated conclusion does not hold.  `psiG` has no standalone
witness theorem; its hypotheses (`CtxG`, a tile `w` with the edge of (K3)(a), the clamp, the rows of `U`) are satisfied, at
`e = 1`, by the context and tiles of `SideRunRules.kill_C1/kill_C2` for runs of a real dissection with `SideRun.Setup`
(`SideRun.side_theorem_witness`); for `e ≥ 2` a `CtxG` is NOT yet available (see part A).

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGChord
import Erdos634.Draft.SideRunGArith

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.SideRunG

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Set

variable {N : ℕ} {D : CongruentDissection N}

/-! ## 1. From real partitions to natural number statements -/

/-- `f² − e²` as a natural number with its real value (`e < f`) -/
theorem exists_bR {e f : ℕ} (hef : e < f) :
    ∃ b : ℕ, f ^ 2 - e ^ 2 = b ∧ (b : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
  refine ⟨f ^ 2 - e ^ 2, rfl, ?_⟩
  rw [Nat.cast_sub (Nat.pow_le_pow_left hef.le 2)]
  push_cast
  try ring

/-- a real partition equation with the right side `j b` is the natural number equation of `A1` -/
theorem rep_nat_b {e f j x y z : ℕ} (hef : e < f)
    (h : (x : ℝ) * ((e : ℝ) * f) + y * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z * (f : ℝ) ^ 2
      = (j : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) :
    x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = j * (f ^ 2 - e ^ 2) := by
  obtain ⟨b, hbN, hbR⟩ := exists_bR hef
  rw [hbN]
  rw [← hbR] at h
  exact_mod_cast h

/-- a real partition equation with the right side `j a` is the natural number equation of `Aa` -/
theorem rep_nat_a {e f j x y z : ℕ} (hef : e < f)
    (h : (x : ℝ) * ((e : ℝ) * f) + y * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z * (f : ℝ) ^ 2
      = (j : ℝ) * ((e : ℝ) * f)) :
    x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = j * (e * f) := by
  obtain ⟨b, hbN, hbR⟩ := exists_bR hef
  rw [hbN]
  rw [← hbR] at h
  exact_mod_cast h

/-- **The first edge of a clamped run of length `j b`, `1 ≤ j ≤ f − 1`, is a `b`-edge** (Lemma A1). -/
theorem first_len_jbG {e f j x y z : ℕ} {ℓ : ℝ} (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f)
    (hj1 : 1 ≤ j) (hj : j ≤ f - 1)
    (hℓ : ℓ = (e : ℝ) * f ∨ ℓ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∨ ℓ = (f : ℝ) ^ 2)
    (h : ℓ + ((x : ℝ) * ((e : ℝ) * f) + y * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z * (f : ℝ) ^ 2)
      = (j : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) : ℓ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
  rcases hℓ with h1 | h1 | h1
  · exfalso
    have := (SideRunGArith.A1 he hef hco hj1 hj (rep_nat_b (x := x + 1) (y := y) (z := z) hef
      (by push_cast; linarith))).1
    omega
  · exact h1
  · exfalso
    have := (SideRunGArith.A1 he hef hco hj1 hj (rep_nat_b (x := x) (y := y) (z := z + 1) hef
      (by push_cast; linarith))).2.2
    omega

/-- the distance between two points of the line `m_s` -/
theorem dist_lineG {e f ε x : ℝ} (he : 0 < e) (hef : e < f) (hε : ε ^ 2 = 1) {s a b : ℝ}
    (hab : a ≤ b) :
    dist (lpG e f ε x (s - a) a) (lpG e f ε x (s - b) b) = (b - a) * (e * f) :=
  dist_lpG he hef hε (mul_nonneg (sub_nonneg.mpr hab) (mul_pos he (he.trans hef)).le)
    (by unfold QfG; ring)

/-! ## 2. The partition (P) of a clamped run, for every member -/

/-- **A chain edge of a clamped run, with the partition sum**: the chain edges contained in the run `[P, Q]` partition it
(`run_partition`), so the length of any one of them plus a combination of the three sides is `|PQ|`. -/
theorem wall_partitionG {N : ℕ} (D : CongruentDissection N) {e f α β γ : ℝ}
    (hM : ModelDataG D e f α β γ) (F : Plane →ₗ[ℝ] ℝ) (hF : F ≠ 0) (c : ℝ) {P Q P' Q' : Plane}
    (hPQ : P ≠ Q) (hfP' : F P' = c) (hfQ' : F Q' = c)
    (hP' : P ∈ openSegment ℝ P' Q) (hQ' : Q ∈ openSegment ℝ P Q')
    (hS : segment ℝ P Q ⊆ {y | F y = c})
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier)
    (hP : ∀ ed ∈ D.lineChain F c, ¬ Straddles ((D.tile ed.1).edge ed.2) P' P Q)
    (hQ : ∀ ed ∈ D.lineChain F c, ¬ Straddles ((D.tile ed.1).edge ed.2) Q' Q P)
    {e0 : Fin N × Fin 3} (he0 : e0 ∈ D.lineChain F c)
    (hsub : (D.tile e0.1).edge e0.2 ⊆ segment ℝ P Q) :
    ∃ x y z : ℕ, dist ((D.tile e0.1).pts e0.2) ((D.tile e0.1).pts (e0.2 + 1)) +
      ((x : ℝ) * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2) = dist P Q := by
  classical
  have hrun := run_partition D.toDissection F hF c hPQ hfP' hfQ' hP' hQ' hS hint hwall hP hQ
  obtain ⟨x, y, z, hxyz⟩ := sum_split_semigroup _ _ (e * f) (f ^ 2 - e ^ 2) (f ^ 2) (dist P Q)
    (fun e' _ => edge_length_casesG D hM e'.1 e'.2) (Finset.mem_filter.mpr ⟨he0, hsub⟩) hrun
  exact ⟨x, y, z, hxyz⟩

/-- **The first edge of a clamped run, with the partition sum**: the generalization of `W2E1.wall_first` to every member. -/
theorem wall_firstG {N : ℕ} (D : CongruentDissection N) {e f α β γ : ℝ}
    (hM : ModelDataG D e f α β γ) (F : Plane →ₗ[ℝ] ℝ) (hF : F ≠ 0) (c : ℝ) {P Q P' Q' : Plane}
    (hPQ : P ≠ Q) (hfP : F P = c) (hfQ : F Q = c) (hfP' : F P' = c) (hfQ' : F Q' = c)
    (hP' : P ∈ openSegment ℝ P' Q) (hQ' : Q ∈ openSegment ℝ P Q')
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier)
    (hP : ∀ ed ∈ D.lineChain F c, ¬ Straddles ((D.tile ed.1).edge ed.2) P' P Q)
    (hQ : ∀ ed ∈ D.lineChain F c, ¬ Straddles ((D.tile ed.1).edge ed.2) Q' Q P) :
    ∃ (i : Fin N) (k m : Fin 3) (x y z : ℕ), k ≠ m ∧ (D.tile i).pts k = P ∧
      (D.tile i).pts m ∈ segment ℝ P Q ∧ (∀ j, F ((D.tile i).pts j) ≤ c) ∧
      dist P ((D.tile i).pts m) + ((x : ℝ) * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2)
        = dist P Q := by
  classical
  have hS := Erdos634.RunPartition.CSlot.segment_subset_level F c hfP hfQ
  obtain ⟨ed, he, hsub, hPe⟩ :=
    first_edge D.toDissection F hF c hPQ hfP hfQ hfP' hfQ' hP' hQ' hint hwall hP hQ
  obtain ⟨x, y, z, hxyz⟩ :=
    wall_partitionG D hM F hF c hPQ hfP' hfQ' hP' hQ' hS hint hwall hP hQ he hsub
  obtain ⟨hp, hq, hle⟩ := Dissection.mem_lineChain.mp he
  have hends : P = (D.tile ed.1).pts ed.2 ∨ P = (D.tile ed.1).pts (ed.2 + 1) :=
    endpoint_of_mem hPQ hsub hPe
  have hne := fin3_succ_ne ed.2
  rcases hends with h | h
  · refine ⟨ed.1, ed.2, ed.2 + 1, x, y, z, hne.2.1.symm, h.symm, ?_, hle, ?_⟩
    · exact hsub (right_mem_segment ℝ _ _)
    · rw [← h] at hxyz; exact hxyz
  · refine ⟨ed.1, ed.2 + 1, ed.2, x, y, z, hne.2.1, h.symm, ?_, hle, ?_⟩
    · exact hsub (left_mem_segment ℝ _ _)
    · rw [← h, dist_comm ((D.tile ed.1).pts ed.2) P] at hxyz; exact hxyz

/-! ## 3. The `ℓ`-chord principle and the tile `φ` -/

namespace CtxG

variable {e f : ℕ} {α β γ L ax ay ε x : ℝ}

/-- **The `ℓ`-chord principle** (paper, with `j* = 0`).  If `U(0,j')` is a tile for `j' < j`, `1 ≤ j < f`, the end `p(0,j)`
of the chord `[P, p(0,j)]` is straddled by an edge of a tile of the side `σ`. -/
theorem chordG (C : CtxG D e f α β γ L ax ay ε x) {j : ℕ} (hj1 : 1 ≤ j) (hjf : j < f)
    (hU : ∀ j' : ℕ, j' < j → UTG D (e : ℝ) (f : ℝ) ε x 0 j') {Q' : Plane}
    (hfQ' : FXG (e : ℝ) (f : ℝ) ε Q' = lvG (e : ℝ) (f : ℝ) ε x 0)
    (hQ' : lpG (e : ℝ) (f : ℝ) ε x 0 j ∈ openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x 0 0) Q')
    (hclamp : ∀ ed ∈ D.lineChain (FXG (e : ℝ) (f : ℝ) ε) (lvG (e : ℝ) (f : ℝ) ε x 0),
      ¬ Straddles ((D.tile ed.1).edge ed.2) Q' (lpG (e : ℝ) (f : ℝ) ε x 0 j)
        (lpG (e : ℝ) (f : ℝ) ε x 0 0)) : False := by
  have S := C.S
  have hε := C.e2
  have he0 := S.e0
  have hefR := S.hef'
  have hb := S.b_pos
  have hhp := hhG_pos he0 hefR
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj1
  have hPE : lpG (e : ℝ) (f : ℝ) ε x 0 0 ≠ lpG (e : ℝ) (f : ℝ) ε x 0 j :=
    lpG_ne_eta he0 hefR hjpos.ne
  have hfP : FXG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x 0 0) = lvG (e : ℝ) (f : ℝ) ε x 0 :=
    FXG_lp hε 0 0
  have hfE : FXG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x 0 j) = lvG (e : ℝ) (f : ℝ) ε x 0 :=
    FXG_lp hε 0 j
  have hEmem : lpG (e : ℝ) (f : ℝ) ε x 0 j ∈ D.target.carrier := by
    obtain ⟨t, ht⟩ := hU (j - 1) (by omega)
    have hc : ((j - 1 : ℕ) : ℝ) + 1 = j := by
      rw [Nat.cast_sub hj1, Nat.cast_one]; ring
    have := ht.mem₃
    rwa [hc] at this
  have hint := C.hch j hj1 hEmem
  have hwall : ∀ y ∈ openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x 0 0) (lpG (e : ℝ) (f : ℝ) ε x 0 j),
      ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    have hy' : y ∈ segment ℝ (lpG (e : ℝ) (f : ℝ) ε x 0 0)
        (lpG (e : ℝ) (f : ℝ) ε x (0 + j * 0) (0 + j * 1)) := by
      rw [show lpG (e : ℝ) (f : ℝ) ε x (0 + (j : ℝ) * 0) (0 + (j : ℝ) * 1)
          = lpG (e : ℝ) (f : ℝ) ε x 0 j from lpG_congr (by ring) (by ring)]
      exact openSegment_subset_segment ℝ _ _ hy
    obtain ⟨i', hi', hyi⟩ := seg_split_lpG hj1 hy'
    obtain ⟨t, k, m, j₃, hkm, hkj, hmj, hk, hm, hj⟩ := hU i' hi'
    refine seg_wall D.toDissection (t := t) hkj ?_
    rw [hk, hj]
    rw [show lpG (e : ℝ) (f : ℝ) ε x (0 + (i' : ℝ) * 0) (0 + (i' : ℝ) * 1)
          = lpG (e : ℝ) (f : ℝ) ε x 0 i' from lpG_congr (by ring) (by ring),
      show lpG (e : ℝ) (f : ℝ) ε x (0 + ((i' : ℝ) + 1) * 0) (0 + ((i' : ℝ) + 1) * 1)
          = lpG (e : ℝ) (f : ℝ) ε x 0 ((i' : ℝ) + 1) from lpG_congr (by ring) (by ring)] at hyi
    exact hyi
  have hP1 : (lpG (e : ℝ) (f : ℝ) ε x 0 0) 1 = 0 := by rw [lpG_snd]; ring
  have hE1 : 0 < (lpG (e : ℝ) (f : ℝ) ε x 0 j) 1 := by rw [lpG_snd]; exact mul_pos hjpos hhp
  obtain ⟨iT, kT, mT, x4, y4, z4, hkmT, hkT, hmT, hleT, hsumT⟩ :=
    wall_firstG D S.hM (FXG (e : ℝ) (f : ℝ) ε) (FXG_ne he0 hefR hε) (lvG (e : ℝ) (f : ℝ) ε x 0)
      hPE hfP hfE (ext_level _ hfP hfE 1) hfQ' (mem_openSegment_ext _ _ one_pos) hQ' hint hwall
      (clamp_out D.toDissection _ _ (S.below_out hP1 hE1)) hclamp
  have hdPE : dist (lpG (e : ℝ) (f : ℝ) ε x 0 0) (lpG (e : ℝ) (f : ℝ) ε x 0 j)
      = (j : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) :=
    dist_lpG he0 hefR hε (mul_nonneg hjpos.le hb.le) (by unfold QfG; ring)
  rw [hdPE] at hsumT
  have hℓ := vertex_dist_casesG D S.hM iT hkmT
  rw [hkT] at hℓ
  have hlen := first_len_jbG S.he S.hef S.hco hj1 (by omega) hℓ hsumT
  have h01 : lpG (e : ℝ) (f : ℝ) ε x 0 1 ∈ segment ℝ (lpG (e : ℝ) (f : ℝ) ε x 0 0)
      (lpG (e : ℝ) (f : ℝ) ε x 0 j) := by
    have h := lp_mem_segG (e := (e : ℝ)) (f := (f : ℝ)) (ε := ε) (x := x) (ξ := 0) (η := 0)
      (ξ' := 0) (η' := j) (τ := 1 / j) (by positivity) (by rw [div_le_one hjpos]; exact_mod_cast hj1)
    rw [show lpG (e : ℝ) (f : ℝ) ε x (0 + 1 / (j : ℝ) * (0 - 0)) (0 + 1 / (j : ℝ) * ((j : ℝ) - 0))
        = lpG (e : ℝ) (f : ℝ) ε x 0 1 from
      lpG_congr (by ring) (by rw [sub_zero, one_div, inv_mul_cancel₀ hjpos.ne', zero_add])] at h
    exact h
  have hd01 : dist (lpG (e : ℝ) (f : ℝ) ε x 0 0) (lpG (e : ℝ) (f : ℝ) ε x 0 1)
      = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have := dist_step_vG (x := x) he0 hefR hε 0 0
    rwa [zero_add] at this
  have hmTeq : (D.tile iT).pts mT = lpG (e : ℝ) (f : ℝ) ε x 0 1 :=
    eq_of_mem_segment_of_dist hPE hmT h01 (by rw [hlen, hd01])
  exact C.hK1 iT kT mT hkmT hkT hmTeq hleT

/-- **The tile `φ`** at the end `p(0,j)` of the chord: it shows a straight angle there and contains every short push from
`p(0,j)` to the side `σ`. -/
theorem phiG (C : CtxG D e f α β γ L ax ay ε x) {j : ℕ} (hj1 : 1 ≤ j) (hjf : j < f)
    (hU : ∀ j' : ℕ, j' < j → UTG D (e : ℝ) (f : ℝ) ε x 0 j') :
    ∃ φ : Fin N, lpG (e : ℝ) (f : ℝ) ε x 0 j ∈ (D.tile φ).carrier ∧
      (D.tile φ).localAngle (lpG (e : ℝ) (f : ℝ) ε x 0 j) = Real.pi ∧
      ∀ w : Plane, FXG (e : ℝ) (f : ℝ) ε w < 0 → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε' : ℝ, 0 < ε' → ε' < ε₀ →
        lpG (e : ℝ) (f : ℝ) ε x 0 j + ε' • w ∈ interior (D.tile φ).carrier := by
  have hε := C.e2
  have he0 := C.S.e0
  have hefR := C.S.hef'
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj1
  have hEP : lpG (e : ℝ) (f : ℝ) ε x 0 j ≠ lpG (e : ℝ) (f : ℝ) ε x 0 0 :=
    lpG_ne_eta he0 hefR hjpos.ne'
  have hfP : FXG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x 0 0) = lvG (e : ℝ) (f : ℝ) ε x 0 :=
    FXG_lp hε 0 0
  have hfE : FXG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x 0 j) = lvG (e : ℝ) (f : ℝ) ε x 0 :=
    FXG_lp hε 0 j
  have hQ' := mem_openSegment_ext (lpG (e : ℝ) (f : ℝ) ε x 0 j) (lpG (e : ℝ) (f : ℝ) ε x 0 0)
    (s := 1) one_pos
  by_contra hno
  refine C.chordG hj1 hjf hU (ext_level (FXG (e : ℝ) (f : ℝ) ε) hfE hfP 1)
    (by rw [openSegment_symm]; exact hQ') (fun ed he hs => hno ?_)
  obtain ⟨h1, h2, h3⟩ := straddle_data D.toDissection (FXG (e : ℝ) (f : ℝ) ε)
    (FXG_ne he0 hefR hε) (lvG (e : ℝ) (f : ℝ) ε x 0) hEP hfE hfP
    (ext_level (FXG (e : ℝ) (f : ℝ) ε) hfE hfP 1) hQ' he hs
  exact ⟨ed.1, h1, h2, h3⟩

end CtxG

/-! ## 4. A chord with a tile strictly on each side is interior -/

/-- **No supporting functional**: two distinct points `Z, E` of the line `G = c`, a functional `g ≥ 0` that vanishes at both,
and two points `Va, Vb` with `G Va < c < G Vb` and `g ≥ 0` at both: impossible when `g` is not constant (`g` is then
proportional to `G` and changes sign across the line). -/
theorem no_support_aux {a b g0 a' b' c z0 z1 e0 e1 va0 va1 vb0 vb1 : ℝ}
    (hab : a ≠ 0 ∨ b ≠ 0) (hab' : a' ≠ 0 ∨ b' ≠ 0) (hZE : z0 ≠ e0 ∨ z1 ≠ e1)
    (hGZ : a' * z0 + b' * z1 = c) (hGE : a' * e0 + b' * e1 = c)
    (hGa : a' * va0 + b' * va1 < c) (hGb : c < a' * vb0 + b' * vb1)
    (hgZ : g0 + a * z0 + b * z1 = 0) (hgE : g0 + a * e0 + b * e1 = 0)
    (hga : 0 ≤ g0 + a * va0 + b * va1) (hgb : 0 ≤ g0 + a * vb0 + b * vb1) : False := by
  have h1 : a' * (z0 - e0) + b' * (z1 - e1) = 0 := by linear_combination hGZ - hGE
  have h2 : a * (z0 - e0) + b * (z1 - e1) = 0 := by linear_combination hgZ - hgE
  have hd0 : (a * b' - a' * b) * (z0 - e0) = 0 := by linear_combination b' * h2 - b * h1
  have hd1 : (a * b' - a' * b) * (z1 - e1) = 0 := by linear_combination a * h1 - a' * h2
  have hdet : a * b' - a' * b = 0 := by
    rcases hZE with h | h
    · exact (mul_eq_zero.mp hd0).resolve_right (sub_ne_zero.mpr h)
    · exact (mul_eq_zero.mp hd1).resolve_right (sub_ne_zero.mpr h)
  have hN : 0 < a' ^ 2 + b' ^ 2 := by
    rcases hab' with h | h
    · have h3 : 0 < a' ^ 2 := by positivity
      have := sq_nonneg b'
      linarith
    · have h3 : 0 < b' ^ 2 := by positivity
      have := sq_nonneg a'
      linarith
  have ha : a * (a' ^ 2 + b' ^ 2) = a' * (a * a' + b * b') := by linear_combination b' * hdet
  have hb : b * (a' ^ 2 + b' ^ 2) = b' * (a * a' + b * b') := by linear_combination (-a') * hdet
  have hA : (a' ^ 2 + b' ^ 2) * (g0 + a * va0 + b * va1)
      = (a * a' + b * b') * (a' * va0 + b' * va1 - c) := by
    linear_combination (a' ^ 2 + b' ^ 2) * hgZ + (va0 - z0) * ha + (va1 - z1) * hb
      - (a * a' + b * b') * hGZ
  have hB : (a' ^ 2 + b' ^ 2) * (g0 + a * vb0 + b * vb1)
      = (a * a' + b * b') * (a' * vb0 + b' * vb1 - c) := by
    linear_combination (a' ^ 2 + b' ^ 2) * hgZ + (vb0 - z0) * ha + (vb1 - z1) * hb
      - (a * a' + b * b') * hGZ
  have hk1 : a * a' + b * b' ≤ 0 := by
    by_contra hpos
    have hpos' := not_le.mp hpos
    have h4 : 0 ≤ (a * a' + b * b') * (a' * va0 + b' * va1 - c) := by
      rw [← hA]; exact mul_nonneg hN.le hga
    nlinarith [mul_pos hpos' (sub_pos.mpr hGa)]
  have hk2 : 0 ≤ a * a' + b * b' := by
    by_contra hneg
    have hneg' := not_le.mp hneg
    have h4 : 0 ≤ (a * a' + b * b') * (a' * vb0 + b' * vb1 - c) := by
      rw [← hB]; exact mul_nonneg hN.le hgb
    nlinarith [mul_pos (neg_pos.mpr hneg') (sub_pos.mpr hGb)]
  have hk0 : a * a' + b * b' = 0 := le_antisymm hk1 hk2
  have ha0 : a = 0 := by
    rw [hk0, mul_zero] at ha
    exact (mul_eq_zero.mp ha).resolve_right hN.ne'
  have hb0 : b = 0 := by
    rw [hk0, mul_zero] at hb
    exact (mul_eq_zero.mp hb).resolve_right hN.ne'
  rcases hab with h | h
  · exact h ha0
  · exact h hb0

namespace SetupG

variable {e f : ℕ} {α β γ L ax ay ε : ℝ}

/-- **An open chord of the line `GS = c` between two points of Δ, with a tile of Δ strictly on each side of the line, is
interior to Δ.**  (Paper: "its open part is interior to Δ, because Δ is convex and has tiles on both sides".) -/
theorem interior_seg_two_sides (S : SetupG D e f α β γ L ax ay) (hε : ε ^ 2 = 1) {c : ℝ}
    {Z E Va Vb : Plane} (hZ : Z ∈ D.target.carrier) (hE : E ∈ D.target.carrier)
    (hVa : Va ∈ D.target.carrier) (hVb : Vb ∈ D.target.carrier) (hZE : Z ≠ E)
    (hGZ : GSG (e : ℝ) (f : ℝ) ε Z = c) (hGE : GSG (e : ℝ) (f : ℝ) ε E = c)
    (hGa : GSG (e : ℝ) (f : ℝ) ε Va < c) (hGb : c < GSG (e : ℝ) (f : ℝ) ε Vb) :
    openSegment ℝ Z E ⊆ interior D.target.carrier := by
  have hu := uuG_pos S.e0 S.hef'
  have hGapp : ∀ p : Plane, GSG (e : ℝ) (f : ℝ) ε p
      = (-(ε * hhG (e : ℝ) (f : ℝ))) * p 0 + (-uuG (e : ℝ) (f : ℝ)) * p 1 := by
    intro p; unfold GSG; rw [lin_apply]
  have hab' : (-(ε * hhG (e : ℝ) (f : ℝ))) ≠ 0 ∨ (-uuG (e : ℝ) (f : ℝ)) ≠ 0 :=
    Or.inr (neg_ne_zero.mpr hu.ne')
  have hZE' : Z 0 ≠ E 0 ∨ Z 1 ≠ E 1 := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    exact hZE (plane_ext hcon.1 hcon.2)
  rw [hGapp] at hGZ hGE hGa hGb
  have hgA : ∀ p : Plane, gA ax ay p = ay * p 0 - ax * p 1 := fun p => rfl
  have hgB : ∀ p : Plane, gB L ax ay p = ay * (L - p 0) - (L - ax) * p 1 := fun p => rfl
  obtain ⟨hZ1, hZA, hZB⟩ := S.mem hZ
  obtain ⟨hE1, hEA, hEB⟩ := S.mem hE
  obtain ⟨hVa1, hVaA, hVaB⟩ := S.mem hVa
  obtain ⟨hVb1, hVbA, hVbB⟩ := S.mem hVb
  rw [hgA] at hZA hEA hVaA hVbA
  rw [hgB] at hZB hEB hVaB hVbB
  refine S.interior_seg hZ hE ?_ ?_ ?_
  · by_contra hcon
    rw [not_or, not_lt, not_lt] at hcon
    exact no_support_aux (g0 := 0) (a := 0) (b := 1) (Or.inr one_ne_zero) hab' hZE' hGZ hGE hGa hGb
      (by linarith [hcon.1]) (by linarith [hcon.2]) (by linarith) (by linarith)
  · by_contra hcon
    rw [not_or, not_lt, not_lt, hgA, hgA] at hcon
    exact no_support_aux (g0 := 0) (a := ay) (b := -ax) (Or.inl S.hay.ne') hab' hZE' hGZ hGE hGa hGb
      (by linarith [hcon.1]) (by linarith [hcon.2]) (by linarith) (by linarith)
  · by_contra hcon
    rw [not_or, not_lt, not_lt, hgB, hgB] at hcon
    exact no_support_aux (g0 := ay * L) (a := -ay) (b := -(L - ax)) (Or.inl (neg_ne_zero.mpr S.hay.ne'))
      hab' hZE' hGZ hGE hGa hGb (by linarith [hcon.1]) (by linarith [hcon.2]) (by linarith)
      (by linarith)

end SetupG

/-! ## 5. The `m`-chord principle, the tile `ψ` and the clamp given by (K3) -/

namespace CtxBase

variable {e f : ℕ} {α β γ L ax ay ε x : ℝ}

/-- **The `m`-chord principle** (paper).  A tile `w` on the side `ρ_s` has an edge `[Z, p(s − η₂, η₂)]` of length `b` or `c`
on `m_s` from `Z = p(s − η₁, η₁)`, `Z` is clamped from below, `η₂ ≤ J < f`, the tiles `U(s − 1 − j', j')`, `η₁ ≤ j' < J`,
are present, and no near-side chain edge straddles the end `p(s − J, J)`: contradiction. -/
theorem mchordG (C : CtxBase D e f α β γ L ax ay ε x) {s : ℝ} {J η₁ : ℕ} {w : Fin N} {k m : Fin 3}
    {η₂ : ℝ} (hkm : k ≠ m) (hη₁ : η₁ < J) (hη₂ : (η₁ : ℝ) < η₂) (hη₂J : η₂ ≤ (J : ℝ))
    (hk : (D.tile w).pts k = lpG (e : ℝ) (f : ℝ) ε x (s - η₁) η₁)
    (hm : (D.tile w).pts m = lpG (e : ℝ) (f : ℝ) ε x (s - η₂) η₂)
    (hlen : (η₂ - η₁) * ((e : ℝ) * f) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∨
      (η₂ - η₁) * ((e : ℝ) * f) = (f : ℝ) ^ 2)
    (hle : ∀ i, GSG (e : ℝ) (f : ℝ) ε ((D.tile w).pts i) ≤ -lvG (e : ℝ) (f : ℝ) ε x s)
    (hcl : ClampedBelowG D (e : ℝ) (f : ℝ) ε x s η₁) (hJf : J < f)
    (hU : ∀ j' : ℕ, η₁ ≤ j' → j' < J → UTG D (e : ℝ) (f : ℝ) ε x (s - 1 - j') j')
    {Q' : Plane} (hfQ' : GSG (e : ℝ) (f : ℝ) ε Q' = -lvG (e : ℝ) (f : ℝ) ε x s)
    (hQ' : lpG (e : ℝ) (f : ℝ) ε x (s - J) J ∈
      openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x (s - η₁) η₁) Q')
    (hclamp : ∀ ed ∈ D.lineChain (GSG (e : ℝ) (f : ℝ) ε) (-lvG (e : ℝ) (f : ℝ) ε x s),
      ¬ Straddles ((D.tile ed.1).edge ed.2) Q' (lpG (e : ℝ) (f : ℝ) ε x (s - J) J)
        (lpG (e : ℝ) (f : ℝ) ε x (s - η₁) η₁)) : False := by
  have S := C.S
  have hε := C.e2
  have he0 := S.e0
  have hefR := S.hef'
  have hη₁J : (η₁ : ℝ) < (J : ℝ) := Nat.cast_lt.mpr hη₁
  have hq : ((J - η₁ : ℕ) : ℝ) = (J : ℝ) - η₁ := by rw [Nat.cast_sub hη₁.le]
  -- levels
  have hfZ : GSG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x (s - η₁) η₁)
      = -lvG (e : ℝ) (f : ℝ) ε x s := by
    rw [GSG_lp hε]; unfold lvG; ring
  have hfE : GSG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x (s - J) J)
      = -lvG (e : ℝ) (f : ℝ) ε x s := by
    rw [GSG_lp hε]; unfold lvG; ring
  have hZE : lpG (e : ℝ) (f : ℝ) ε x (s - η₁) η₁ ≠ lpG (e : ℝ) (f : ℝ) ε x (s - J) J :=
    lpG_ne_eta he0 hefR hη₁J.ne
  -- the end `E` is a vertex of a tile `U`
  have hEmem : lpG (e : ℝ) (f : ℝ) ε x (s - J) J ∈ D.target.carrier := by
    obtain ⟨t, ht⟩ := hU (J - 1) (by omega) (by omega)
    have hJ1 : ((J - 1 : ℕ) : ℝ) = (J : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ J), Nat.cast_one]
    have h3 := ht.mem₃
    rwa [show lpG (e : ℝ) (f : ℝ) ε x (s - 1 - ((J - 1 : ℕ) : ℝ)) (((J - 1 : ℕ) : ℝ) + 1)
        = lpG (e : ℝ) (f : ℝ) ε x (s - J) J from
      lpG_congr (by rw [hJ1]; ring) (by rw [hJ1]; ring)] at h3
  have hZmem : lpG (e : ℝ) (f : ℝ) ε x (s - η₁) η₁ ∈ D.target.carrier := by
    rw [← hk]; exact pts_mem_target D.toDissection w k
  -- a tile strictly on each side
  obtain ⟨j₃, hkj, hmj⟩ : ∃ j : Fin 3, k ≠ j ∧ m ≠ j := by
    have h3 : ∀ k m : Fin 3, k ≠ m → ∃ j : Fin 3, k ≠ j ∧ m ≠ j := by decide
    exact h3 k m hkm
  have hfk : GSG (e : ℝ) (f : ℝ) ε ((D.tile w).pts k) = -lvG (e : ℝ) (f : ℝ) ε x s := by
    rw [hk]; exact hfZ
  have hfm : GSG (e : ℝ) (f : ℝ) ε ((D.tile w).pts m) = -lvG (e : ℝ) (f : ℝ) ε x s := by
    rw [hm, GSG_lp hε]; unfold lvG; ring
  have hVa : GSG (e : ℝ) (f : ℝ) ε ((D.tile w).pts j₃) < -lvG (e : ℝ) (f : ℝ) ε x s :=
    Erdos634.Draft.SideRun.third_strict (D.tile w) hkm hkj hmj (GSG (e : ℝ) (f : ℝ) ε)
      (GSG_ne he0 hefR hε) _ hfk hfm hle
  obtain ⟨tU, hUt⟩ := hU η₁ le_rfl hη₁
  have hVbmem := hUt.mem₁
  have hVb : -lvG (e : ℝ) (f : ℝ) ε x s <
      GSG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x (s - 1 - η₁) η₁) := by
    rw [GSG_lp hε]
    have := lvG_lt (e := (e : ℝ)) (f := (f : ℝ)) (ε := ε) (x := x) he0 hefR
      (show s - 1 - η₁ + η₁ < s by linarith)
    linarith
  have hint := S.interior_seg_two_sides hε hZmem hEmem (pts_mem_target D.toDissection w j₃)
    hVbmem hZE hfZ hfE hVa hVb
  -- the chord is a wall: the union of the `a`-edges of the tiles `U`
  have hwall : ∀ y ∈ openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x (s - η₁) η₁)
      (lpG (e : ℝ) (f : ℝ) ε x (s - J) J), ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    have hy' : y ∈ segment ℝ (lpG (e : ℝ) (f : ℝ) ε x (s - η₁) η₁)
        (lpG (e : ℝ) (f : ℝ) ε x (s - η₁ + ((J - η₁ : ℕ) : ℝ) * (-1))
          (η₁ + ((J - η₁ : ℕ) : ℝ) * 1)) := by
      rw [show lpG (e : ℝ) (f : ℝ) ε x (s - η₁ + ((J - η₁ : ℕ) : ℝ) * (-1))
            (η₁ + ((J - η₁ : ℕ) : ℝ) * 1) = lpG (e : ℝ) (f : ℝ) ε x (s - J) J from
          lpG_congr (by rw [hq]; ring) (by rw [hq]; ring)]
      exact openSegment_subset_segment ℝ _ _ hy
    obtain ⟨i, hi, hyi⟩ := seg_split_lpG (e := (e : ℝ)) (f := (f : ℝ)) (ε := ε) (x := x)
      (ξ := s - η₁) (η := η₁) (dξ := -1) (dη := 1) (q := J - η₁) (by omega) hy'
    obtain ⟨t, k', m', j', hk'm', hk'j', hm'j', hk', hm', hj'⟩ :=
      hU (η₁ + i) (by omega) (by omega)
    refine seg_wall D.toDissection (t := t) hm'j' ?_
    rw [hm', hj']
    rw [show lpG (e : ℝ) (f : ℝ) ε x (s - η₁ + (i : ℝ) * (-1)) (η₁ + (i : ℝ) * 1)
          = lpG (e : ℝ) (f : ℝ) ε x (s - 1 - ((η₁ + i : ℕ) : ℝ) + 1) ((η₁ + i : ℕ) : ℝ) from
        lpG_congr (by push_cast; ring) (by push_cast; ring),
      show lpG (e : ℝ) (f : ℝ) ε x (s - η₁ + ((i : ℝ) + 1) * (-1)) (η₁ + ((i : ℝ) + 1) * 1)
          = lpG (e : ℝ) (f : ℝ) ε x (s - 1 - ((η₁ + i : ℕ) : ℝ)) (((η₁ + i : ℕ) : ℝ) + 1) from
        lpG_congr (by push_cast; ring) (by push_cast; ring)] at hyi
    exact hyi
  -- the clamp at `Z`
  obtain ⟨η', hη', hprop⟩ := hcl
  have hP'mem : lpG (e : ℝ) (f : ℝ) ε x (s - η₁) η₁ ∈
      openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x (s - η') η') (lpG (e : ℝ) (f : ℝ) ε x (s - J) J) :=
    lpG_between hη' hη₁J
  have hfP' : GSG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x (s - η') η')
      = -lvG (e : ℝ) (f : ℝ) ε x s := by
    rw [GSG_lp hε]; unfold lvG; ring
  have hP := hprop _ hfE hP'mem
  have hS := Erdos634.RunPartition.CSlot.segment_subset_level (GSG (e : ℝ) (f : ℝ) ε)
    (-lvG (e : ℝ) (f : ℝ) ε x s) hfZ hfE
  -- the edge of `w`
  obtain ⟨e0, he0mem, he0sub, he0len⟩ : ∃ e0 : Fin N × Fin 3,
      e0 ∈ D.lineChain (GSG (e : ℝ) (f : ℝ) ε) (-lvG (e : ℝ) (f : ℝ) ε x s) ∧
      (D.tile e0.1).edge e0.2 ⊆ segment ℝ (lpG (e : ℝ) (f : ℝ) ε x (s - η₁) η₁)
        (lpG (e : ℝ) (f : ℝ) ε x (s - J) J) ∧
      dist ((D.tile e0.1).pts e0.2) ((D.tile e0.1).pts (e0.2 + 1)) = (η₂ - η₁) * ((e : ℝ) * f) := by
    have hsegsub : segment ℝ ((D.tile w).pts k) ((D.tile w).pts m) ⊆
        segment ℝ (lpG (e : ℝ) (f : ℝ) ε x (s - η₁) η₁) (lpG (e : ℝ) (f : ℝ) ε x (s - J) J) := by
      refine (convex_segment _ _).segment_subset ?_ ?_
      · rw [hk]; exact left_mem_segment ℝ _ _
      · rw [hm]; exact lpG_mem_seg_of_le hη₂ hη₂J
    have hd : dist ((D.tile w).pts k) ((D.tile w).pts m) = (η₂ - η₁) * ((e : ℝ) * f) := by
      rw [hk, hm]; exact dist_lineG he0 hefR hε hη₂.le
    rcases pair_index k m hkm with h | h
    · refine ⟨(w, k), Dissection.mem_lineChain.mpr ⟨hfk, ?_, hle⟩, ?_, ?_⟩
      · show GSG (e : ℝ) (f : ℝ) ε ((D.tile w).pts (k + 1)) = _
        rw [← h]; exact hfm
      · show segment ℝ ((D.tile w).pts k) ((D.tile w).pts (k + 1)) ⊆ _
        rw [← h]; exact hsegsub
      · show dist ((D.tile w).pts k) ((D.tile w).pts (k + 1)) = _
        rw [← h]; exact hd
    · refine ⟨(w, m), Dissection.mem_lineChain.mpr ⟨hfm, ?_, hle⟩, ?_, ?_⟩
      · show GSG (e : ℝ) (f : ℝ) ε ((D.tile w).pts (m + 1)) = _
        rw [← h]; exact hfk
      · show segment ℝ ((D.tile w).pts m) ((D.tile w).pts (m + 1)) ⊆ _
        rw [← h, segment_symm]; exact hsegsub
      · show dist ((D.tile w).pts m) ((D.tile w).pts (m + 1)) = _
        rw [← h, dist_comm]; exact hd
  obtain ⟨x5, y5, z5, hsum⟩ := wall_partitionG D S.hM (GSG (e : ℝ) (f : ℝ) ε)
    (GSG_ne he0 hefR hε) (-lvG (e : ℝ) (f : ℝ) ε x s) hZE hfP' hfQ' hP'mem hQ' hS hint hwall hP
    hclamp he0mem he0sub
  rw [he0len, dist_lineG he0 hefR hε hη₁J.le] at hsum
  rcases hlen with hb | hc
  · have := (SideRunGArith.Aa S.he S.hef S.hco (j := J - η₁) (by omega) (by omega)
      (rep_nat_a S.hef (x := x5) (y := y5 + 1) (z := z5)
        (by push_cast; (try rw [hq]); linarith))).2.1
    omega
  · have := (SideRunGArith.Aa S.he S.hef S.hco (j := J - η₁) (by omega) (by omega)
      (rep_nat_a S.hef (x := x5) (y := y5) (z := z5 + 1)
        (by push_cast; (try rw [hq]); linarith))).2.2
    omega

/-- **The tile `ψ`** at `p(s − J, J)`: some tile on the side `ρ_s` has an edge on `m_s` with `p(s − J, J)` in its relative
interior; it shows a straight angle there and contains every short push from that point into `ρ_s`. -/
theorem psiG (C : CtxBase D e f α β γ L ax ay ε x) {s : ℝ} {J η₁ : ℕ} {w : Fin N} {k m : Fin 3}
    {η₂ : ℝ} (hkm : k ≠ m) (hη₁ : η₁ < J) (hη₂ : (η₁ : ℝ) < η₂)
    (hk : (D.tile w).pts k = lpG (e : ℝ) (f : ℝ) ε x (s - η₁) η₁)
    (hm : (D.tile w).pts m = lpG (e : ℝ) (f : ℝ) ε x (s - η₂) η₂)
    (hlen : (η₂ - η₁) * ((e : ℝ) * f) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∨
      (η₂ - η₁) * ((e : ℝ) * f) = (f : ℝ) ^ 2)
    (hle : ∀ i, GSG (e : ℝ) (f : ℝ) ε ((D.tile w).pts i) ≤ -lvG (e : ℝ) (f : ℝ) ε x s)
    (hcl : ClampedBelowG D (e : ℝ) (f : ℝ) ε x s η₁) (hJf : J < f)
    (hU : ∀ j' : ℕ, η₁ ≤ j' → j' < J → UTG D (e : ℝ) (f : ℝ) ε x (s - 1 - j') j') :
    ∃ ψ : Fin N, lpG (e : ℝ) (f : ℝ) ε x (s - J) J ∈ (D.tile ψ).carrier ∧
      (D.tile ψ).localAngle (lpG (e : ℝ) (f : ℝ) ε x (s - J) J) = Real.pi ∧
      ∀ v : Plane, GSG (e : ℝ) (f : ℝ) ε v < 0 → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε' : ℝ, 0 < ε' → ε' < ε₀ →
        lpG (e : ℝ) (f : ℝ) ε x (s - J) J + ε' • v ∈ interior (D.tile ψ).carrier := by
  have hε := C.e2
  have he0 := C.S.e0
  have hefR := C.S.hef'
  have hη₁J : (η₁ : ℝ) < (J : ℝ) := Nat.cast_lt.mpr hη₁
  rcases lt_or_ge (J : ℝ) η₂ with hJ | hJ
  · have hx : lpG (e : ℝ) (f : ℝ) ε x (s - J) J ∈
        openSegment ℝ ((D.tile w).pts k) ((D.tile w).pts m) := by
      rw [hk, hm]; exact lpG_between hη₁J hJ
    obtain ⟨hpw, hang, hpush⟩ := edge_interior_push (D.tile w) hkm (GSG (e : ℝ) (f : ℝ) ε)
      (GSG_ne he0 hefR hε) (-lvG (e : ℝ) (f : ℝ) ε x s)
      (by rw [hk, GSG_lp hε]; unfold lvG; ring) (by rw [hm, GSG_lp hε]; unfold lvG; ring) hle hx
    exact ⟨w, hpw, hang, hpush⟩
  · by_contra hno
    have hEZ : lpG (e : ℝ) (f : ℝ) ε x (s - J) J ≠ lpG (e : ℝ) (f : ℝ) ε x (s - η₁) η₁ :=
      lpG_ne_eta he0 hefR hη₁J.ne'
    have hfE : GSG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x (s - J) J)
        = -lvG (e : ℝ) (f : ℝ) ε x s := by
      rw [GSG_lp hε]; unfold lvG; ring
    have hfZ : GSG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x (s - η₁) η₁)
        = -lvG (e : ℝ) (f : ℝ) ε x s := by
      rw [GSG_lp hε]; unfold lvG; ring
    have hQ' := mem_openSegment_ext (lpG (e : ℝ) (f : ℝ) ε x (s - J) J)
      (lpG (e : ℝ) (f : ℝ) ε x (s - η₁) η₁) (s := 1) one_pos
    refine C.mchordG hkm hη₁ hη₂ hJ hk hm hlen hle hcl hJf hU
      (ext_level (GSG (e : ℝ) (f : ℝ) ε) hfE hfZ 1) (by rw [openSegment_symm]; exact hQ')
      (fun ed hed hs => hno ?_)
    obtain ⟨h1, h2, h3⟩ := straddle_data D.toDissection (GSG (e : ℝ) (f : ℝ) ε)
      (GSG_ne he0 hefR hε) (-lvG (e : ℝ) (f : ℝ) ε x s) hEZ hfE hfZ
      (ext_level (GSG (e : ℝ) (f : ℝ) ε) hfE hfZ 1) hQ' hed hs
    exact ⟨ed.1, h1, h2, h3⟩

/-- **The clamp given by (K3)** at the lattice point `p(s − J, J)`, `J = j0 + 1 < f`, for a wall `[p, Q]` on a line `{F = c}`
that reaches `p` from the side away from `ρ_s`: the conclusion of `SideRun.Ctx.K3_clamp`, from `K3G` and the tiles `U(s − 1 − j', j')`,
`j' ≤ j0`, of the row sequence on `m_s` (part of (K2)). -/
theorem K3G_clamp (C : CtxBase D e f α β γ L ax ay ε x) {s : ℝ} {j0 J : ℕ} (hJ : J = j0 + 1)
    (hK : K3G D (e : ℝ) (f : ℝ) ε x s (j0 : ℝ)) (hJf : J < f)
    (hU : ∀ j' : ℕ, j' ≤ j0 → UTG D (e : ℝ) (f : ℝ) ε x (s - 1 - j') j')
    (F : Plane →ₗ[ℝ] ℝ) (c : ℝ) {Q : Plane}
    (hFp : F (lpG (e : ℝ) (f : ℝ) ε x (s - J) J) = c) (hFQ : F Q = c)
    (hdir : GSG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x (s - J) J - Q) < 0) :
    ∃ Q' : Plane, F Q' = c ∧ lpG (e : ℝ) (f : ℝ) ε x (s - J) J ∈ openSegment ℝ Q' Q ∧
      ∀ ed ∈ D.lineChain F c, ¬ Straddles ((D.tile ed.1).edge ed.2) Q'
        (lpG (e : ℝ) (f : ℝ) ε x (s - J) J) Q := by
  have hε := C.e2
  have hGp : GSG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x (s - J) J)
      = -lvG (e : ℝ) (f : ℝ) ε x s := by
    rw [GSG_lp hε]; unfold lvG; ring
  rcases hK with hout | ⟨w, k, m, η₁, η₂, hkm, h1, h2, hk, hm, hl, hle, hcl⟩
  · refine ⟨lpG (e : ℝ) (f : ℝ) ε x (s - J) J + (1 : ℝ) • (lpG (e : ℝ) (f : ℝ) ε x (s - J) J - Q),
      ext_level F hFp hFQ 1, mem_openSegment_ext _ Q one_pos, ?_⟩
    refine clamp_out D.toDissection F c (fun r hr hmem => ?_)
    have h3 := hout _ hmem
    rw [map_add, map_smul, smul_eq_mul, hGp] at h3
    nlinarith [mul_pos hr (neg_pos.mpr hdir)]
  · have hη₁ : η₁ < J := by
      have : η₁ ≤ j0 := by exact_mod_cast h1
      omega
    obtain ⟨ψ, hpψ, -, hpush⟩ := C.psiG hkm hη₁ h2 hk hm hl hle hcl hJf
      (fun j' hj' hjJ => hU j' (by omega))
    obtain ⟨Q', h1', h2', h3'⟩ := ext_point_of_push F hFp hFQ hpψ (hpush _ hdir)
    exact ⟨Q', h1', h2', fun ed _ => not_straddles_of_interior D.toDissection h3' ed.1 ed.2⟩

end CtxBase

/-! The full names `CtxG.mchordG`, `CtxG.K3G_clamp` (cited in `PAPER_MAP.md`) are kept alive as corollaries over `CtxG`. -/

namespace CtxG

variable {e f : ℕ} {α β γ L ax ay ε x : ℝ}

/-- `CtxBase.mchordG` for a `CtxG` (the old full name) -/
theorem mchordG (C : CtxG D e f α β γ L ax ay ε x) {s : ℝ} {J η₁ : ℕ} {w : Fin N} {k m : Fin 3}
    {η₂ : ℝ} (hkm : k ≠ m) (hη₁ : η₁ < J) (hη₂ : (η₁ : ℝ) < η₂) (hη₂J : η₂ ≤ (J : ℝ))
    (hk : (D.tile w).pts k = lpG (e : ℝ) (f : ℝ) ε x (s - η₁) η₁)
    (hm : (D.tile w).pts m = lpG (e : ℝ) (f : ℝ) ε x (s - η₂) η₂)
    (hlen : (η₂ - η₁) * ((e : ℝ) * f) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∨
      (η₂ - η₁) * ((e : ℝ) * f) = (f : ℝ) ^ 2)
    (hle : ∀ i, GSG (e : ℝ) (f : ℝ) ε ((D.tile w).pts i) ≤ -lvG (e : ℝ) (f : ℝ) ε x s)
    (hcl : ClampedBelowG D (e : ℝ) (f : ℝ) ε x s η₁) (hJf : J < f)
    (hU : ∀ j' : ℕ, η₁ ≤ j' → j' < J → UTG D (e : ℝ) (f : ℝ) ε x (s - 1 - j') j')
    {Q' : Plane} (hfQ' : GSG (e : ℝ) (f : ℝ) ε Q' = -lvG (e : ℝ) (f : ℝ) ε x s)
    (hQ' : lpG (e : ℝ) (f : ℝ) ε x (s - J) J ∈
      openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x (s - η₁) η₁) Q')
    (hclamp : ∀ ed ∈ D.lineChain (GSG (e : ℝ) (f : ℝ) ε) (-lvG (e : ℝ) (f : ℝ) ε x s),
      ¬ Straddles ((D.tile ed.1).edge ed.2) Q' (lpG (e : ℝ) (f : ℝ) ε x (s - J) J)
        (lpG (e : ℝ) (f : ℝ) ε x (s - η₁) η₁)) : False :=
  C.toCtxBase.mchordG hkm hη₁ hη₂ hη₂J hk hm hlen hle hcl hJf hU hfQ' hQ' hclamp

/-- `CtxBase.K3G_clamp` for a `CtxG` (the old full name) -/
theorem K3G_clamp (C : CtxG D e f α β γ L ax ay ε x) {s : ℝ} {j0 J : ℕ} (hJ : J = j0 + 1)
    (hK : K3G D (e : ℝ) (f : ℝ) ε x s (j0 : ℝ)) (hJf : J < f)
    (hU : ∀ j' : ℕ, j' ≤ j0 → UTG D (e : ℝ) (f : ℝ) ε x (s - 1 - j') j')
    (F : Plane →ₗ[ℝ] ℝ) (c : ℝ) {Q : Plane}
    (hFp : F (lpG (e : ℝ) (f : ℝ) ε x (s - J) J) = c) (hFQ : F Q = c)
    (hdir : GSG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x (s - J) J - Q) < 0) :
    ∃ Q' : Plane, F Q' = c ∧ lpG (e : ℝ) (f : ℝ) ε x (s - J) J ∈ openSegment ℝ Q' Q ∧
      ∀ ed ∈ D.lineChain F c, ¬ Straddles ((D.tile ed.1).edge ed.2) Q'
        (lpG (e : ℝ) (f : ℝ) ε x (s - J) J) Q :=
  C.toCtxBase.K3G_clamp hJ hK hJf hU F c hFp hFQ hdir

end CtxG

/-! ## 6. Specialisation to `e = 1` -/

section e_one

variable {n : ℕ} {α β γ L ax ay ε x : ℝ}

/-- `U(ξ,η)` is a tile: `UTG` at `e = 1` is `UT` -/
theorem UTG_one_iff {ξ η : ℝ} :
    UTG D ((1 : ℕ) : ℝ) (n : ℝ) ε x ξ η ↔ UT D n ε x ξ η := by
  unfold UTG UT
  constructor <;> intro h <;> simpa only [Nat.cast_one, lpG_one] using h

/-- **`CtxG.chordG` at `e = 1` is `Ctx.chord`**, derived from the general statement -/
theorem chord_e1 (C : Ctx D n α β γ L ax ay ε x) {j : ℕ} (hj1 : 1 ≤ j) (hjn : j < n)
    (hU : ∀ j' : ℕ, j' < j → UT D n ε x 0 j') {Q' : Plane} (hfQ' : FX n ε Q' = lv n ε x 0)
    (hQ' : lp n ε x 0 j ∈ openSegment ℝ (lp n ε x 0 0) Q')
    (hclamp : ∀ ed ∈ D.lineChain (FX n ε) (lv n ε x 0),
      ¬ Straddles ((D.tile ed.1).edge ed.2) Q' (lp n ε x 0 j) (lp n ε x 0 0)) : False := by
  have CG := ctxG_one_iff.mpr C
  exact CG.chordG hj1 hjn (fun j' hj' => UTG_one_iff.mpr (hU j' hj'))
    (by rw [Nat.cast_one, FXG_one, lvG_one]; exact hfQ')
    (by simpa only [Nat.cast_one, lpG_one] using hQ')
    (by simpa only [Nat.cast_one, FXG_one, lvG_one, lpG_one] using hclamp)

/-- **`CtxG.phiG` at `e = 1` is `Ctx.phi`**, derived from the general statement -/
theorem phi_e1 (C : Ctx D n α β γ L ax ay ε x) {j : ℕ} (hj1 : 1 ≤ j) (hjn : j < n)
    (hU : ∀ j' : ℕ, j' < j → UT D n ε x 0 j') :
    ∃ φ : Fin N, lp n ε x 0 j ∈ (D.tile φ).carrier ∧
      (D.tile φ).localAngle (lp n ε x 0 j) = Real.pi ∧
      ∀ w : Plane, FX n ε w < 0 → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε' : ℝ, 0 < ε' → ε' < ε₀ →
        lp n ε x 0 j + ε' • w ∈ interior (D.tile φ).carrier := by
  have CG := ctxG_one_iff.mpr C
  obtain ⟨φ, h1, h2, h3⟩ := CG.phiG hj1 hjn (fun j' hj' => UTG_one_iff.mpr (hU j' hj'))
  refine ⟨φ, ?_, ?_, ?_⟩
  · simpa only [Nat.cast_one, lpG_one] using h1
  · simpa only [Nat.cast_one, lpG_one] using h2
  · simpa only [Nat.cast_one, lpG_one, FXG_one] using h3

/-- **`CtxG.K3G_clamp` at `e = 1`**: the conclusion of `Ctx.K3_clamp` at `η = j0 + 1`, under `K3G` (not `K3`) and the rows of
`U` tiles `U(s − 1 − j', j')`, `j' ≤ j0` -/
theorem K3G_clamp_e1 (C : Ctx D n α β γ L ax ay ε x) {s : ℝ} {j0 J : ℕ} (hJ : J = j0 + 1)
    (hK : K3G D ((1 : ℕ) : ℝ) (n : ℝ) ε x s (j0 : ℝ)) (hJf : J < n)
    (hU : ∀ j' : ℕ, j' ≤ j0 → UT D n ε x (s - 1 - j') j')
    (F : Plane →ₗ[ℝ] ℝ) (c : ℝ) {Q : Plane} (hFp : F (lp n ε x (s - J) J) = c) (hFQ : F Q = c)
    (hdir : GS n ε (lp n ε x (s - J) J - Q) < 0) :
    ∃ Q' : Plane, F Q' = c ∧ lp n ε x (s - J) J ∈ openSegment ℝ Q' Q ∧
      ∀ ed ∈ D.lineChain F c, ¬ Straddles ((D.tile ed.1).edge ed.2) Q' (lp n ε x (s - J) J) Q := by
  have CG := ctxG_one_iff.mpr C
  have h := CG.K3G_clamp hJ hK hJf (fun j' hj' => UTG_one_iff.mpr (hU j' hj')) F c
    (by simpa only [Nat.cast_one, lpG_one] using hFp) hFQ
    (by rw [Nat.cast_one, lpG_one, GSG_one]; exact hdir)
  simpa only [Nat.cast_one, lpG_one] using h

/-- **`K3G` implies `K3` at `e = 1`** for `s + 1 ≤ n`: an edge of length `b = n² − 1` or `c = n²` from a lattice point at height
`η₁ ≥ 0` reaches the height `η₁ + n − 1/n` resp. `η₁ + n`, which exceeds `s ≤ n − 1`.  The converse is not claimed (the edge of `K3`
need not start at a lattice point, nor be clamped, nor have the length `b` or `c`). -/
theorem K3_of_K3G_e1 {s j0 : ℝ} (hn : 2 ≤ n) (hs : s + 1 ≤ (n : ℝ))
    (h : K3G D ((1 : ℕ) : ℝ) (n : ℝ) ε x s j0) : K3 D n ε x s j0 := by
  rcases h with hout | ⟨w, k, m, η₁, η₂, hkm, h1, h2, hk, hm, hl, hle, -⟩
  · exact K3_of_outG hout
  · have hη₁0 : (0 : ℝ) ≤ (η₁ : ℝ) := Nat.cast_nonneg η₁
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hsη₂ : s < η₂ := by
      by_contra hc
      rw [not_lt] at hc
      have hd : η₂ - (η₁ : ℝ) ≤ (n : ℝ) - 1 := by linarith
      have hmul := mul_le_mul_of_nonneg_right hd (by linarith : (0 : ℝ) ≤ (n : ℝ))
      rcases hl with hl | hl <;> rw [Nat.cast_one] at hl <;> nlinarith
    refine Or.inr ⟨w, k, m, (η₁ : ℝ), η₂, hkm, ?_, ?_, h1, hsη₂, ?_⟩
    · rw [Nat.cast_one, lpG_one] at hk; exact hk
    · rw [Nat.cast_one, lpG_one] at hm; exact hm
    · intro i
      have := hle i
      rw [Nat.cast_one, GSG_one, lvG_one] at this
      exact this

end e_one

end Erdos634.Draft.SideRunG

#print axioms Erdos634.Draft.SideRunG.first_len_jbG
#print axioms Erdos634.Draft.SideRunG.wall_partitionG
#print axioms Erdos634.Draft.SideRunG.wall_firstG
#print axioms Erdos634.Draft.SideRunG.CtxG.chordG
#print axioms Erdos634.Draft.SideRunG.CtxG.phiG
#print axioms Erdos634.Draft.SideRunG.no_support_aux
#print axioms Erdos634.Draft.SideRunG.SetupG.interior_seg_two_sides
#print axioms Erdos634.Draft.SideRunG.CtxBase.mchordG
#print axioms Erdos634.Draft.SideRunG.CtxG.mchordG
#print axioms Erdos634.Draft.SideRunG.CtxBase.psiG
#print axioms Erdos634.Draft.SideRunG.CtxBase.K3G_clamp
#print axioms Erdos634.Draft.SideRunG.CtxG.K3G_clamp
#print axioms Erdos634.Draft.SideRunG.chord_e1
#print axioms Erdos634.Draft.SideRunG.phi_e1
#print axioms Erdos634.Draft.SideRunG.K3G_clamp_e1
#print axioms Erdos634.Draft.SideRunG.K3_of_K3G_e1
