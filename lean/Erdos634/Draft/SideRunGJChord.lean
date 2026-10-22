/-
Draft/SideRunGJChord.lean -- written 14 October 2026.  UNAUDITED.  In `AllThreshold`.  Module J1 of the
plan for `thm:cornerrun` (piece 1): the ℓ-CHORD PRINCIPLE WITH (K1) AT AN ARBITRARY ROW `j*`.

Paper: Theorem `thm:cornerrun`; the proof uses the statement `K(s', j0)` with (K1) at `0 ≤ j* ≤ j0` ("the general form is needed for
Theorem `thm:cornerrun`, and the proof is the same"); (private working notes, not included), Section on Theorem C.

====================================================================================================================================
STEP 0.  PLAN FOR `thm:cornerrun` AND `cor:thickw` (written after reading the whole paper proof of both, lines 3940-4400 of
`paper/erdos-634.tex`, and every `CtxG`-typed declaration of `SideRunG*`).
====================================================================================================================================

FINDINGS THAT DECIDE THE PLAN.
(1) (K1) is used at exactly THREE call sites of `SideRunG*`: `rowG` (the tile `φ` at `p(0, j+1)`: `C.phiG`), `noNG` (the same) and
    `K_allG` (size 1: `C.chordG`).  Every other `CtxG`-typed declaration (21 in all: `seg_intG`, `m_clamp_baseG`, `m_clamp_tileG`,
    `m_next_casesG`, `m_nextG`, `mchordG`, `psiG`, `K3G_clamp`, `m_nextGr`, `row_stepG`, `row_bad0G`, `row_sixG`, `row_badG`,
    `m_clamp_natG`, `D_ofG`, `N_fiveG`, `K3G_clamp_row`, ...) uses `C` only through `C.S`, `C.e2`, `C.seg_intG` (checked by grep).
(2) In the proof of `thm:cornerrun` the general (K1) enters only through the statement M(s', j0): there `K(s'', j0)` is called, in the
    lattice with origin `p(i+1, 0)` (a point of the side) with `j* = j0`, and `K(., j0+1)` with `j* = j0+1`, in the original lattice
    and in shifted ones.  Inside `K`, `j*` stays fixed while `j0` grows (Lemma Row, Lemma N, step (2a)): so `K(s', j0)` is needed for
    all pairs with `j* <= j0`, at every origin on the side.  The main theorem itself (steps (1)-(3)) uses `K(k, 0)` with `j* = 0`.
(3) THE ℓ-CHORD PRINCIPLE CAN START AT THE POINT `P` OF THE SIDE instead of `p(0, j*)`.  In every use all the tiles `U(0, j')`,
    `j' < j`, are present by (K2) (K2 asks for the rows `<= j0` of the column `0`), so `[P, p(0,j)]` is the union of the `b`-edges of
    the `U(0, j')`; its end `P` is clamped by the side (the line is outside Δ below `P`); if no tile of the side `σ` had `p(0,j)` in
    the relative interior of an edge, (P) would partition `[P, p(0,j)]` into edges of tiles of `σ`, and the edge of `T` from
    `p(0,j*)` (length `a` or `c`) would be one of the pieces, against Lemma A1.  So the clamp of (K1) is NOT used, and the
    hypothesis `hch` (open chord interior to Δ) is the same as for `j* = 0`.  This is `chordJ` below.

DECISION ON HOW (K1) WITH `j* > 0` ENTERS.  Option (b) of the coordinator's list, with the interface made abstract:
    `CtxJ D e f α β γ L ax ay ε x js` := `CtxBase` (= `SetupG` + orientation) + the ℓ-chord principle for `j > js` as a field (`hchord`,
    the `False`-form of `chordG`).  `CtxJ.of_ctxG : CtxG → CtxJ (js = 0)` and `CtxJ.of_K1J : (K1 at js, in the paper's form) → CtxJ js`.
    The three call sites are re-proved for `CtxJ` with the extra hypothesis `js <= j` (and the recursion threads `js` through).
DECISION ON DUPLICATION (taken 14 October 2026 by the coordinator): option (R).  The 21 lemmas that use only `C.S`, `C.e2`,
    `C.seg_intG` were moved from `namespace CtxG` to `namespace CtxBase` (`structure CtxBase := (S, hε)`, `CtxG extends CtxBase`,
    `CtxJ extends CtxBase`) in the files `SideRunGChord/ChordB/Row/RowB/K` without changing any statement; the call sites `C.row_stepG`
    need no change (dot notation finds the parent namespace).  So only `rowG`, `noNG`, `K_allG`, `run_diesG` are re-proved over
    `CtxJ` (modules J3, J4), with the `js = 0` statements re-derived as corollaries.

MODULES (estimated lines; each built by (private working notes, not included), ~5 min).
  J1  SideRunGJChord      ~330   THIS FILE: `K1J`, `chordJ`, `CtxJ`, `phiJ`, `of_K1J`, `of_ctxG`.
  J2  (not needed under (R))
  J3  SideRunGJRow        ~280   `AGJ`, `rowJ` (js <= j), `rowG_via_J`.
  J4  SideRunGJK          ~420   `noNJ`, `K_allGJ`, `run_diesJ`, and the corollaries `noNG_via_J`, `K_allG_via_J`, `run_diesG_via_J`.
  C1  SideRunGCornerA     ~450   the side from a corner `A'` (2α or 3α, left) to a corner `Q'` (β or α+β, right): `CornersA`, corner figures (F)
                                 at 2α, 3α, `hch` at the corner, (K1) at `A'` from "T lays c" (-> `CtxJ 0`), normal form of the side.
  C2  SideRunGCornerRun   ~500   run lemma `L_k` at the corner start: (K3) at `R` for the corner `α+β` on the right, `kill` lemmas for the
                                 two cases (T lays c / T lays b = mirror).
  M1  SideRunGMirror      ~400   the mirror tile `T` of `U(0,j0)` in `ℓ` (sector `(γ, π+α)` at `p(0, j0+1)`), shifted-origin contexts
                                 (`ctxJ_shift`: the lattice with origin `p(c0, 0)`), the statement `MG(s', j0)`, size 1.
  M2  SideRunGMStep       ~650   `MG`, size `n >= 2`: step (a) (`D(i,j0)` tiles; `S_i = N_i` gives `E`: K with `j* = j0` or MG), step (b) (the
                                 row `Λ`, `j0+1`), step (c) (`T^+`).
  M3  SideRunGMStepB      ~600   continuation (Lemma-Row/N analogues for the mirror: `N_i(j0)` with `K` at `j* = j0`).
  M4  SideRunGMo          ~500   `M°(e+1)` (a < b, corner 2α, the case `a^f`: types A1/A2 along Λ, the vertex `V` on the second side).
  R1  SideRunGCornerWords ~450   rules for the word on `s` from `A'`: no tile of type R; the first tile is `C1`; the maximal run `C1^k`.
  R2  SideRunGCornerMain  ~500   `thm_cornerrun` in normal position, for an arbitrary `CongruentDissection` (HasSides and corner angles),
                                 the addendum, the members `(f-1, f)`.
  W1  SideRunGThick       ~700   normal form of the side `AQ` of `W_M(e,f)`, the count (`SideRunGArith.C_AQ` is reused), `cor:thickw` (a), (b)
                                 (existence: `Draft.Residue.wTilable_ge`), (c) `W_2(3,5)` (enumeration of the representations of 160).
  Total about 6,500 lines in 14 modules (about 5,200 with (R)).  These estimates are not commitments.

WHAT IS REUSED AND WHAT IS NEW, STEP BY STEP.
  (P) partition ................ reused: `RunPartition.run_partition/edge_clamped`, `wall_partitionG`, `wall_firstG`.
  (F) figures .................. reused: `fig_bg`; new: the lists at the corners 2α and 3α (C1).
  A1, A5, Aa, (R0), C_AQ ....... reused: `SideRunGArith`.
  lattice, U/D/N ............... reused: `lpG`, `UTG`, `DTG`, `N_anglesG`, `N_pushG`, `dist_N_*G`.
  ℓ-chord principle ............ NEW: `chordJ` (this file).     m-chord principle: reused through J2 (copy over `CtxJ`).
  K(s', j0), Lemma Row, Lemma N  re-proved over `CtxJ` (J2-J4), `js` threaded.
  run lemma `L_k` .............. reused for `js = 0` (`kill_C1G` pattern); new at the corner start (C2).
  M(s', j0), M°(e+1) ........... new (M1-M4).      Theorem steps (1)-(3), rules ........ new (R1-R2).      `cor:thickw` ........ new (W1).

====================================================================================================================================
THIS MODULE.
====================================================================================================================================
* `K1J D e f ε x js`: hypothesis (K1) of the paper at the row `js`, WITHOUT its clamp: a tile `T` of the side σ (`FXG <= lv`) has an
  edge on `ℓ` from `p(0, js)` upward of length `a` or `c`.
* `chordJ`: **the ℓ-chord principle with (K1) at `js`** (conclusion `False`, like `chordG`): the hypotheses of `chordG` with `hK1` replaced
  by `K1J` and `js < j`.
* `CtxJ`: the standing hypotheses of the run lemma with (K1) at `js`, in the form the consumers need; `CtxJ.of_K1J`, `CtxJ.of_ctxG`
  (`js = 0` from the old context), `CtxJ.e2`, `phiJ` (the tile `φ` at `p(0, j)`, `js < j`), `ctxJ_of_ctx_e1` (check at `e = 1`).

WHICH OBJECT SATISFIES THE PREDICATES.  `K1J` is a property of a dissection and of `(x, js)`: it holds whenever a tile of the side σ lays
`a` or `c` on `ℓ` from `p(0, js)`; it is produced in the proof of M (the tile `E` / `T^+` laying `c` or `a`) and in the proof of the
main theorem (the tile beside `X_0` laying `c`), where it is a case of a proof by contradiction; no real dissection is exhibited in this
module (the real dissections available, `setupG_witness_member`, do not specify tiles at a given lattice point).  `chordJ` and the field
`hchord` of `CtxJ` conclude `False` (they are contradiction engines of the proof by contradiction, like `chordG`): their hypotheses
are not satisfiable together in a real dissection, and the value is in `phiJ`.  `CtxJ.of_ctxG` makes every `CtxG` (at `e = 1`: every
`Ctx`) a `CtxJ` with `js = 0`.

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGChordB

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.SideRunGJ

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG Set

variable {N : ℕ} {D : CongruentDissection N}

/-! ## 1. Two small lemmas on the lattice line and on a tile -/

/-- a point of the line `ℓ` between two lattice points of `ℓ`, in lattice coordinates -/
theorem lpG_eta_mem_seg {e f ε x ξ a b c : ℝ} (hab : a < b) (hac : a ≤ c) (hcb : c ≤ b) :
    lpG e f ε x ξ c ∈ segment ℝ (lpG e f ε x ξ a) (lpG e f ε x ξ b) := by
  have hd : 0 < b - a := by linarith
  have hne : b - a ≠ 0 := hd.ne'
  have h := lp_mem_segG (e := e) (f := f) (ε := ε) (x := x) (ξ := ξ) (η := a) (ξ' := ξ) (η' := b)
    (τ := (c - a) / (b - a)) (div_nonneg (by linarith) hd.le) (by rw [div_le_one hd]; linarith)
  rw [show lpG e f ε x (ξ + (c - a) / (b - a) * (ξ - ξ)) (a + (c - a) / (b - a) * (b - a))
      = lpG e f ε x ξ c from lpG_congr (by ring) (by rw [div_mul_cancel₀ _ hne]; ring)] at h
  exact h

/-- two vertices of a tile are the two ends of one of its edges -/
theorem tile_edge_of_pair (T : Erdos634.Geometry.Tri) {k m : Fin 3} (hkm : k ≠ m) :
    ∃ i : Fin 3, (T.pts i = T.pts k ∧ T.pts (i + 1) = T.pts m) ∨
      (T.pts i = T.pts m ∧ T.pts (i + 1) = T.pts k) := by
  have hcov : ∀ a b : Fin 3, a ≠ b → b = a + 1 ∨ a = b + 1 := by decide
  rcases hcov k m hkm with h | h
  · exact ⟨k, Or.inl ⟨rfl, by rw [h]⟩⟩
  · exact ⟨m, Or.inr ⟨rfl, by rw [h]⟩⟩

/-! ## 2. Hypothesis (K1) at the row `js`, and the ℓ-chord principle -/

/-- **Hypothesis (K1) of the paper, at the row `js`, without its clamp**: a tile `T` of the side σ of `ℓ` (all its vertices have
`FXG <= lv`) has an edge on `ℓ` that starts at `p(0, js)`, runs upward, and has length `a` or `c` (the point at the distance
`t · b` above `p(0, js)` is `p(0, js + t)`). -/
def K1J (D : CongruentDissection N) (e f ε x : ℝ) (js : ℕ) : Prop :=
  ∃ (iT : Fin N) (k m : Fin 3) (t : ℝ), k ≠ m ∧ (D.tile iT).pts k = lpG e f ε x 0 (js : ℝ) ∧
    (D.tile iT).pts m = lpG e f ε x 0 ((js : ℝ) + t) ∧ 0 < t ∧
    (t * (f ^ 2 - e ^ 2) = e * f ∨ t * (f ^ 2 - e ^ 2) = f ^ 2) ∧
    ∀ i, FXG e f ε ((D.tile iT).pts i) ≤ lvG e f ε x 0

/-- **THE ℓ-CHORD PRINCIPLE WITH (K1) AT `js`** (paper, "the ℓ-chord principle"; the `False` form of `CtxG.chordG`).  Let `U(0, j')` be
tiles for `j' < j`, `js < j < f`, and (K1) hold at `js`.  Then the end `p(0, j)` of the chord `[P, p(0, j)]` is straddled by an edge of
a tile of the side σ.  (Conclusion `False` under the hypothesis `hclamp` that no chain edge straddles `p(0,j)`.) -/
theorem chordJ {e f : ℕ} {α β γ L ax ay ε x : ℝ} (S : SetupG D e f α β γ L ax ay) (hε : ε ^ 2 = 1)
    (hch : ∀ j : ℕ, 1 ≤ j → lpG (e : ℝ) (f : ℝ) ε x 0 j ∈ D.target.carrier →
      openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x 0 0) (lpG (e : ℝ) (f : ℝ) ε x 0 j) ⊆
        interior D.target.carrier)
    {js : ℕ} (hK1 : K1J D (e : ℝ) (f : ℝ) ε x js) {j : ℕ} (hjs : js < j) (hjf : j < f)
    (hU : ∀ j' : ℕ, j' < j → UTG D (e : ℝ) (f : ℝ) ε x 0 j') {Q' : Plane}
    (hfQ' : FXG (e : ℝ) (f : ℝ) ε Q' = lvG (e : ℝ) (f : ℝ) ε x 0)
    (hQ' : lpG (e : ℝ) (f : ℝ) ε x 0 j ∈ openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x 0 0) Q')
    (hclamp : ∀ ed ∈ D.lineChain (FXG (e : ℝ) (f : ℝ) ε) (lvG (e : ℝ) (f : ℝ) ε x 0),
      ¬ Straddles ((D.tile ed.1).edge ed.2) Q' (lpG (e : ℝ) (f : ℝ) ε x 0 j)
        (lpG (e : ℝ) (f : ℝ) ε x 0 0)) : False := by
  have hj1 : 1 ≤ j := by omega
  have he0 := S.e0
  have hefR := S.hef'
  have hb := S.b_pos
  have hhp := hhG_pos he0 hefR
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj1
  have hjsR : (js : ℝ) < j := by exact_mod_cast hjs
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
  have hint := hch j hj1 hEmem
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
  have hclampP := clamp_out D.toDissection (FXG (e : ℝ) (f : ℝ) ε) (lvG (e : ℝ) (f : ℝ) ε x 0)
    (S.below_out hP1 hE1)
  have hS : segment ℝ (lpG (e : ℝ) (f : ℝ) ε x 0 0) (lpG (e : ℝ) (f : ℝ) ε x 0 j) ⊆
      {y | FXG (e : ℝ) (f : ℝ) ε y = lvG (e : ℝ) (f : ℝ) ε x 0} :=
    Erdos634.RunPartition.CSlot.segment_subset_level _ _ hfP hfE
  -- the tile `T` of (K1) and its edge on `ℓ`
  obtain ⟨iT, kT, mT, t, hkmT, hkT, hmT, htpos, hlen, hleT⟩ := hK1
  obtain ⟨i0, hi0⟩ := tile_edge_of_pair (D.tile iT) hkmT
  have hF1 : FXG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x 0 (js : ℝ)) = lvG (e : ℝ) (f : ℝ) ε x 0 :=
    FXG_lp hε 0 (js : ℝ)
  have hF2 : FXG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x 0 ((js : ℝ) + t))
      = lvG (e : ℝ) (f : ℝ) ε x 0 := FXG_lp hε 0 ((js : ℝ) + t)
  have hed : (iT, i0) ∈ D.lineChain (FXG (e : ℝ) (f : ℝ) ε) (lvG (e : ℝ) (f : ℝ) ε x 0) := by
    refine Dissection.mem_lineChain.mpr ⟨?_, ?_, hleT⟩
    · show FXG (e : ℝ) (f : ℝ) ε ((D.tile iT).pts i0) = lvG (e : ℝ) (f : ℝ) ε x 0
      rcases hi0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, hkT]; exact hF1
      · rw [h1, hmT]; exact hF2
    · show FXG (e : ℝ) (f : ℝ) ε ((D.tile iT).pts (i0 + 1)) = lvG (e : ℝ) (f : ℝ) ε x 0
      rcases hi0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h2, hmT]; exact hF2
      · rw [h2, hkT]; exact hF1
  have hedge : (D.tile iT).edge i0 = segment ℝ (lpG (e : ℝ) (f : ℝ) ε x 0 (js : ℝ))
      (lpG (e : ℝ) (f : ℝ) ε x 0 ((js : ℝ) + t)) := by
    show segment ℝ ((D.tile iT).pts i0) ((D.tile iT).pts (i0 + 1)) = _
    rcases hi0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, hkT, hmT]
    · rw [h1, h2, hkT, hmT]; exact segment_symm ℝ _ _
  have hnoP : ¬ Straddles (segment ℝ (lpG (e : ℝ) (f : ℝ) ε x 0 (js : ℝ))
      (lpG (e : ℝ) (f : ℝ) ε x 0 ((js : ℝ) + t)))
      (lpG (e : ℝ) (f : ℝ) ε x 0 0 + (1 : ℝ) • (lpG (e : ℝ) (f : ℝ) ε x 0 0 - lpG (e : ℝ) (f : ℝ) ε x 0 j))
      (lpG (e : ℝ) (f : ℝ) ε x 0 0) (lpG (e : ℝ) (f : ℝ) ε x 0 j) := by
    have h : ¬ Straddles ((D.tile iT).edge i0)
        (lpG (e : ℝ) (f : ℝ) ε x 0 0 + (1 : ℝ) • (lpG (e : ℝ) (f : ℝ) ε x 0 0 - lpG (e : ℝ) (f : ℝ) ε x 0 j))
        (lpG (e : ℝ) (f : ℝ) ε x 0 0) (lpG (e : ℝ) (f : ℝ) ε x 0 j) := hclampP (iT, i0) hed
    rwa [hedge] at h
  have hnoQ : ¬ Straddles (segment ℝ (lpG (e : ℝ) (f : ℝ) ε x 0 (js : ℝ))
      (lpG (e : ℝ) (f : ℝ) ε x 0 ((js : ℝ) + t))) Q' (lpG (e : ℝ) (f : ℝ) ε x 0 j)
      (lpG (e : ℝ) (f : ℝ) ε x 0 0) := by
    have h : ¬ Straddles ((D.tile iT).edge i0) Q' (lpG (e : ℝ) (f : ℝ) ε x 0 j)
        (lpG (e : ℝ) (f : ℝ) ε x 0 0) := hclamp (iT, i0) hed
    rwa [hedge] at h
  -- the edge of `T` lies in `[P, p(0,j)]`
  have hdich := Erdos634.RunPartition.edge_clamped (FXG (e : ℝ) (f : ℝ) ε)
    (FXG_ne he0 hefR hε) (lvG (e : ℝ) (f : ℝ) ε x 0) hPE hfP hfE (ext_level _ hfP hfE 1) hfQ'
    (mem_openSegment_ext _ _ one_pos) hQ' hF1 hF2 hnoP hnoQ
  have hsub : (D.tile iT).edge i0 ⊆ segment ℝ (lpG (e : ℝ) (f : ℝ) ε x 0 0)
      (lpG (e : ℝ) (f : ℝ) ε x 0 j) := by
    rcases hdich with hss | hss
    · exfalso
      have hδ : 0 < min t ((j : ℝ) - js) := lt_min htpos (by linarith)
      have hδt : min t ((j : ℝ) - js) ≤ t := min_le_left _ _
      have hδj : min t ((j : ℝ) - js) ≤ (j : ℝ) - js := min_le_right _ _
      have hjs0 : (0 : ℝ) ≤ js := Nat.cast_nonneg js
      have p3_mem : lpG (e : ℝ) (f : ℝ) ε x 0 ((js : ℝ) + min t ((j : ℝ) - js)) ∈
          segment ℝ (lpG (e : ℝ) (f : ℝ) ε x 0 (js : ℝ)) (lpG (e : ℝ) (f : ℝ) ε x 0 ((js : ℝ) + t)) :=
        lpG_eta_mem_seg (by linarith) (by linarith) (by linarith)
      have p1_mem : lpG (e : ℝ) (f : ℝ) ε x 0 (js : ℝ) ∈
          segment ℝ (lpG (e : ℝ) (f : ℝ) ε x 0 (js : ℝ)) (lpG (e : ℝ) (f : ℝ) ε x 0 ((js : ℝ) + t)) :=
        left_mem_segment ℝ _ _
      have q1 : lpG (e : ℝ) (f : ℝ) ε x 0 (js : ℝ) ∈
          segment ℝ (lpG (e : ℝ) (f : ℝ) ε x 0 0) (lpG (e : ℝ) (f : ℝ) ε x 0 j) :=
        lpG_eta_mem_seg (by linarith) hjs0 hjsR.le
      have q3 : lpG (e : ℝ) (f : ℝ) ε x 0 ((js : ℝ) + min t ((j : ℝ) - js)) ∈
          segment ℝ (lpG (e : ℝ) (f : ℝ) ε x 0 0) (lpG (e : ℝ) (f : ℝ) ε x 0 j) :=
        lpG_eta_mem_seg (by linarith) (by linarith) (by linarith)
      have hne : lpG (e : ℝ) (f : ℝ) ε x 0 (js : ℝ)
          ≠ lpG (e : ℝ) (f : ℝ) ε x 0 ((js : ℝ) + min t ((j : ℝ) - js)) :=
        lpG_ne_eta he0 hefR (by intro h; linarith)
      exact hne (hss ⟨p1_mem, q1⟩ ⟨p3_mem, q3⟩)
    · rw [hedge]; exact hss
  obtain ⟨x4, y4, z4, hsum⟩ := wall_partitionG D S.hM (FXG (e : ℝ) (f : ℝ) ε)
    (FXG_ne he0 hefR hε) (lvG (e : ℝ) (f : ℝ) ε x 0) hPE (ext_level _ hfP hfE 1) hfQ'
    (mem_openSegment_ext _ _ one_pos) hQ' hS hint hwall hclampP hclamp hed hsub
  have hℓ : dist ((D.tile iT).pts i0) ((D.tile iT).pts (i0 + 1))
      = t * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
    have hd : dist (lpG (e : ℝ) (f : ℝ) ε x 0 (js : ℝ)) (lpG (e : ℝ) (f : ℝ) ε x 0 ((js : ℝ) + t))
        = t * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) :=
      dist_lpG he0 hefR hε (mul_nonneg htpos.le hb.le) (by unfold QfG; ring)
    rcases hi0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, hkT, hmT]; exact hd
    · rw [h1, h2, hkT, hmT, dist_comm]; exact hd
  have hdPE : dist (lpG (e : ℝ) (f : ℝ) ε x 0 0) (lpG (e : ℝ) (f : ℝ) ε x 0 j)
      = (j : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) :=
    dist_lpG he0 hefR hε (mul_nonneg hjpos.le hb.le) (by unfold QfG; ring)
  have hsum' : t * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + ((x4 : ℝ) * ((e : ℝ) * f)
      + y4 * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z4 * (f : ℝ) ^ 2) = (j : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
    have h : dist ((D.tile iT).pts i0) ((D.tile iT).pts (i0 + 1)) + ((x4 : ℝ) * ((e : ℝ) * f)
        + y4 * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z4 * (f : ℝ) ^ 2)
        = dist (lpG (e : ℝ) (f : ℝ) ε x 0 0) (lpG (e : ℝ) (f : ℝ) ε x 0 j) := hsum
    rw [hℓ, hdPE] at h
    exact h
  have hlen' : t * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) = (e : ℝ) * f ∨
      t * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∨
      t * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) = (f : ℝ) ^ 2 := by
    rcases hlen with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  have hl := first_len_jbG S.he S.hef S.hco hj1 (by omega) hlen' hsum'
  rcases hlen with h | h
  · exact S.tile.hab (h.symm.trans hl)
  · have h2 : (f : ℝ) ^ 2 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := h.symm.trans hl
    nlinarith [mul_pos he0 he0]

/-! ## 3. The context `CtxJ` -/

/-- **The standing hypotheses of the run lemma with (K1) at the row `js`**: a `SetupG`, an orientation, and the ℓ-chord principle for
`j > js` (the `False` form of `CtxG.chordG`).  `CtxJ.of_K1J` builds it from the paper's (K1) at `js`; `CtxJ.of_ctxG` from the
`j* = 0` context of `SideRunG*`. -/
structure CtxJ (D : CongruentDissection N) (e f : ℕ) (α β γ L ax ay ε x : ℝ) (js : ℕ) : Prop
    extends CtxBase D e f α β γ L ax ay ε x where
  hchord : ∀ j : ℕ, js < j → j < f → (∀ j' : ℕ, j' < j → UTG D (e : ℝ) (f : ℝ) ε x 0 j') →
    ∀ Q' : Plane, FXG (e : ℝ) (f : ℝ) ε Q' = lvG (e : ℝ) (f : ℝ) ε x 0 →
    lpG (e : ℝ) (f : ℝ) ε x 0 j ∈ openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x 0 0) Q' →
    (∀ ed ∈ D.lineChain (FXG (e : ℝ) (f : ℝ) ε) (lvG (e : ℝ) (f : ℝ) ε x 0),
      ¬ Straddles ((D.tile ed.1).edge ed.2) Q' (lpG (e : ℝ) (f : ℝ) ε x 0 j)
        (lpG (e : ℝ) (f : ℝ) ε x 0 0)) → False

namespace CtxJ

variable {e f : ℕ} {α β γ L ax ay ε x : ℝ} {js : ℕ}

/-- **the context from the paper's (K1) at the row `js`** (and the interior of the chords from the point `P` of the side) -/
theorem of_K1J (S : SetupG D e f α β γ L ax ay) (hε : ε = 1 ∨ ε = -1)
    (hch : ∀ j : ℕ, 1 ≤ j → lpG (e : ℝ) (f : ℝ) ε x 0 j ∈ D.target.carrier →
      openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x 0 0) (lpG (e : ℝ) (f : ℝ) ε x 0 j) ⊆
        interior D.target.carrier)
    (hK1 : K1J D (e : ℝ) (f : ℝ) ε x js) : CtxJ D e f α β γ L ax ay ε x js := by
  refine ⟨⟨S, hε⟩, fun j hjs hjf hU Q' hfQ' hQ' hcl => ?_⟩
  have he2 : ε ^ 2 = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  exact chordJ S he2 hch hK1 hjs hjf hU hfQ' hQ' hcl

/-- **the `j* = 0` context of `SideRunG*` is a `CtxJ` with `js = 0`** (the old statements are the special case) -/
theorem of_ctxG (C : CtxG D e f α β γ L ax ay ε x) : CtxJ D e f α β γ L ax ay ε x 0 :=
  ⟨C.toCtxBase, fun j hj hjf hU Q' hfQ' hQ' hcl => C.chordG (by omega) hjf hU hfQ' hQ' hcl⟩

/-- **The tile `φ`** at the end `p(0,j)` of the chord, `js < j < f`: it shows a straight angle there and contains every short push
from `p(0,j)` to the side σ (the generalization of `CtxG.phiG`). -/
theorem phiJ (C : CtxJ D e f α β γ L ax ay ε x js) {j : ℕ} (hjs : js < j) (hjf : j < f)
    (hU : ∀ j' : ℕ, j' < j → UTG D (e : ℝ) (f : ℝ) ε x 0 j') :
    ∃ φ : Fin N, lpG (e : ℝ) (f : ℝ) ε x 0 j ∈ (D.tile φ).carrier ∧
      (D.tile φ).localAngle (lpG (e : ℝ) (f : ℝ) ε x 0 j) = Real.pi ∧
      ∀ w : Plane, FXG (e : ℝ) (f : ℝ) ε w < 0 → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε' : ℝ, 0 < ε' → ε' < ε₀ →
        lpG (e : ℝ) (f : ℝ) ε x 0 j + ε' • w ∈ interior (D.tile φ).carrier := by
  have hε := C.e2
  have he0 := C.S.e0
  have hefR := C.S.hef'
  have hj1 : 1 ≤ j := by omega
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
  refine C.hchord j hjs hjf hU _ (ext_level (FXG (e : ℝ) (f : ℝ) ε) hfE hfP 1)
    (by rw [openSegment_symm]; exact hQ') (fun ed he hs => hno ?_)
  obtain ⟨h1, h2, h3⟩ := straddle_data D.toDissection (FXG (e : ℝ) (f : ℝ) ε)
    (FXG_ne he0 hefR hε) (lvG (e : ℝ) (f : ℝ) ε x 0) hEP hfE hfP
    (ext_level (FXG (e : ℝ) (f : ℝ) ε) hfE hfP 1) hQ' he hs
  exact ⟨ed.1, h1, h2, h3⟩

end CtxJ

/-! ## 4. Check at `e = 1` -/

section e_one

variable {n : ℕ} {α β γ L ax ay ε x : ℝ}

/-- at `e = 1` every `Ctx` of `SideRun` is a `CtxJ` with `js = 0` -/
theorem ctxJ_of_ctx_e1 (C : Ctx D n α β γ L ax ay ε x) : CtxJ D 1 n α β γ L ax ay ε x 0 :=
  CtxJ.of_ctxG (ctxG_one_iff.mpr C)

end e_one

end Erdos634.Draft.SideRunGJ

#print axioms Erdos634.Draft.SideRunGJ.chordJ
#print axioms Erdos634.Draft.SideRunGJ.CtxJ.of_K1J
#print axioms Erdos634.Draft.SideRunGJ.CtxJ.of_ctxG
#print axioms Erdos634.Draft.SideRunGJ.CtxJ.phiJ
#print axioms Erdos634.Draft.SideRunGJ.ctxJ_of_ctx_e1
