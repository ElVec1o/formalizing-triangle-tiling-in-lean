-- Draft/RowWallInduction.lean — RW(j), THE ROW-WALL LEMMA, for real `m = 1` dissections: the
-- hypothesis `C(j,m)` exactly as the paper states it ((private working notes, not included) S1;
-- proof_H_empty.md §5.5), and its impossibility by strong induction on `j` and induction on `m`,
-- assembled from the local steps of Draft/RowWallLocal.lean.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- Build (scratch oleans; never .lake): RowWallLocal olean in $S, then
--   lake env bash -c 'LEAN_PATH=$S:$LEAN_PATH lean Erdos634/Draft/RowWallInduction.lean'
import Erdos634.Draft.RowWallLocal

namespace Erdos634.Draft.RowWallReal

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.HalfTurnR3R4
open Erdos634.Draft.HalfTurnR3R4Glue Erdos634.Draft.CornerAdjacency
open Erdos634.Draft.HalfTurnR3R4Order Erdos634.Draft.MirrorStripR2Real
open Erdos634.Draft.HalfTurnR4Real

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ}

/-- **Hypothesis `C(j, m)`** (report_exact_forms.md S1; proof_H_empty.md §5.5), in the apex frame
`F` of a dissection, `Λ(x, y) = A + x·(P′ − A) + y·c·uL`, strip `s` = the cells `Up (s−1) t`,
`Dn (s−1) t`:
* (i) every `Λ₃` cell of strips `1..j` above row `m` is a tile, and so is every down cell of strips
  `1..j` in band `B_m` — i.e. `Up i t` and `Dn i t` for `i < j`, `i + t + 1 ≤ m`;
* (ii) the right-side covering of `L_j` by whole edges starts at `jP′` — no right-side edge of `L_j`
  has `jP′` in its relative interior (the line-relative reading, record correction 2 / review2_RW
  W1) — and contains a `b`-edge whose upper end `Λ(j, s)` is at or above row `m` (`0 ≤ s ≤ m − j`),
  the edge running down `L_j` to `Λ(j, s + b/c)`. -/
structure CH (F : HFrame D e f α β γ) (j m : ℕ) : Prop where
  cells : ∀ i t, i < j → i + t + 1 ≤ m → Present D (Up F i t) ∧ Present D (Dn F i t)
  start : ¬ RStr F j (Lam F j 0)
  seed : ∃ ε ∈ rightChain F j, ∃ s : ℝ, 0 ≤ s ∧ s ≤ (m : ℝ) - j ∧
    EdgeIs D ε (Lam F j s) (Lam F j (s + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2))

variable (F : HFrame D e f α β γ)

/-- Under `C(j'+1, m)`, the point `Λ(j'+1, m − j')` of `L_{j'+1}` (row `m + 1`) is straddled from
the right, if it is inside the target (`junc_kill`: Lemma A, **m = 1**). -/
theorem junc_str (L : LFrame F) {j' m : ℕ} (hC : CH F (j' + 1) m) (T : ℕ) (hT : j' + T = m)
    (hTf : j' + 1 + T ≤ f) : RStr F ((j' : ℝ) + 1) (Lam F ((j' : ℝ) + 1) T) := by
  by_contra hn
  have hstart : ¬ RStr F ((j' : ℝ) + 1) (Lam F ((j' : ℝ) + 1) 0) := by
    have := hC.start; push_cast at this; exact this
  obtain ⟨ε, hε, s, hs0, hsm, hE⟩ := hC.seed
  push_cast at hε hsm hE
  have hTR : (j' : ℝ) + T = m := by exact_mod_cast hT
  obtain ⟨-, hb0, hc0, hbc, -⟩ := consts F
  have hq : ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 < 1 := by rw [div_lt_one hc0]; exact hbc
  exact junc_kill F L j' T hTf (fun s hs => (hC.cells j' s (by omega) (by omega)).2) hstart
    ⟨ε, hε, s, hs0, by linarith, hE⟩ hn

/-- **(C), the base**: `C(j, f − 1)` is impossible — `L_j` meets the base at `Λ(j, f − j)`, where the
right-side covering must end (`base_nstr`), and Lemma A forbids the word (`junc_str`). -/
theorem rw_base (L : LFrame F) (j' : ℕ) (hj : j' + 2 ≤ f) (hC : CH F (j' + 1) (f - 1)) : False := by
  have hs := junc_str F L hC (f - 1 - j') (by omega) (by omega)
  apply base_nstr F L ((j' : ℝ) + 1)
  have : ((f - 1 - j' : ℕ) : ℝ) = (f : ℝ) - ((j' : ℝ) + 1) := by
    rw [Nat.cast_sub (show j' ≤ f - 1 by omega), Nat.cast_sub (show 1 ≤ f by omega), Nat.cast_one]
    ring
  rwa [this] at hs

/-- **(A) + (B): `C(j, m) ⇒ C(j, m+1)`, given `RW(i)` for every `i < j`** (`m + 2 ≤ f`).
(A) every up cell of band `B_m` is a tile: the leg slot by `slot_leg` (**m = 1**: leg `b`-free);
an interior slot `1 ≤ i ≤ j − 2` by `slot_int`, its swap giving `C(i, m)` (`start_of_up`,
`seed_of_Xs`), killed by `RW(i)`; the last slot `i = j − 1` by `slot_int`, its swap killed by
`cross_kill` at the Lemma-A straddle `junc_str`.  (B) the down cells of band `B_{m+1}` by
`row_step` (**m = 1**: the row word `a^j`). -/
theorem rw_step (L : LFrame F) (j' m : ℕ) (hm : m + 2 ≤ f) (hjm : j' + 1 ≤ m)
    (IH : ∀ i, 1 ≤ i → i < j' + 1 → ∀ m', i ≤ m' → m' + 1 ≤ f → ¬ CH F i m')
    (hC : CH F (j' + 1) m) : CH F (j' + 1) (m + 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, m = j' + 1 + d := ⟨m - (j' + 1), by omega⟩
  have hX0 : RStr F ((j' : ℝ) + 1) (Lam F ((j' : ℝ) + 1) ((d : ℝ) + 1)) := by
    have := junc_str F L hC (d + 1) (by omega) (by omega)
    push_cast at this; exact this
  -- (A) the up cells of band `B_m`
  have hUpNew : ∀ i t, i < j' + 1 → i + t = j' + 1 + d → Present D (Up F i t) := by
    intro i t hi hit
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      exact slot_leg F L t' (by omega) (hC.cells 0 t' (by omega) (by omega)).1
        (hC.cells 0 t' (by omega) (by omega)).2
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      rcases slot_int F L i' t' (by omega) (hC.cells i' t' (by omega) (by omega)).2
          (hC.cells (i' + 1) t' (by omega) (by omega)).1
          (hC.cells i' (t' + 1) (by omega) (by omega)).2
          (hC.cells i' (t' + 1) (by omega) (by omega)).1
          (hC.cells (i' + 1) t' (by omega) (by omega)).2 with h | hXs
      · exact h
      · exfalso
        rcases Nat.lt_or_ge (i' + 1) j' with hlt | hge
        · -- an interior slot: the swap seeds `C(i'+1, m)`, killed by `RW(i'+1)`
          apply IH (i' + 1) (by omega) (by omega) (j' + 1 + d) (by omega) (by omega)
          refine ⟨fun i t hi ht => hC.cells i t (by omega) ht, ?_, ?_⟩
          · exact start_of_up F L (i' + 1) (hC.cells (i' + 1) 0 (by omega) (by omega)).1
          · obtain ⟨ε, hε, hE⟩ := seed_of_Xs F L _ _ hXs
            refine ⟨ε, by push_cast; exact hε, (t' : ℝ) + 1, by positivity, ?_, by
              push_cast; exact hE⟩
            have : ((i' + 1 + (t' + 1) : ℕ) : ℝ) = ((j' + 1 + d : ℕ) : ℝ) := by rw [hit]
            push_cast at this ⊢; linarith
        · -- the last slot: the swap's `c`-edge crosses the straddled point of `L_{j'+1}`
          have hij : i' + 1 = j' := by omega
          have ht' : t' = d := by omega
          have hXs' : Present D (Xs F j' ((t' : ℝ) + 1)) := by
            have : ((i' : ℝ) + 1) = (j' : ℝ) := by rw [← hij]; push_cast; ring
            rw [this] at hXs; exact hXs
          have hX0' : RStr F ((j' : ℝ) + 1) (Lam F ((j' : ℝ) + 1) ((t' : ℝ) + 1)) := by
            rw [ht']; exact hX0
          exact cross_kill F L j' t' (by omega) hXs'
            (hC.cells j' t' (by omega) (by omega)).2 hX0'
  -- (B) the down cells of band `B_{m+1}`
  have hDnNew := row_step F L j' d (by omega)
    (fun i t hi hit => hUpNew i t (by omega) hit)
    (fun i t hi hit => (hC.cells i t (by omega) (by omega)).2) hX0
  refine ⟨fun i t hi ht => ?_, hC.start, ?_⟩
  · rcases Nat.lt_or_ge (i + t + 1) (j' + 1 + d + 1) with hlt | hge
    · exact hC.cells i t hi (by omega)
    · exact ⟨hUpNew i t hi (by omega), hDnNew i t (by omega) (by omega)⟩
  · obtain ⟨ε, hε, s, hs0, hsm, hE⟩ := hC.seed
    refine ⟨ε, hε, s, hs0, ?_, hE⟩
    push_cast at hsm ⊢; linarith

/-- **RW(j) — THE ROW-WALL LEMMA, frame form — PROVED.**  In the apex frame of a dissection
satisfying `LFrame` (cone coordinates + `b`-free leg), no `C(j, m)`, `1 ≤ j ≤ m ≤ f − 1`, holds.
Strong induction on `j`; for fixed `j`, induction on `f − 1 − m` (`rw_base`, `rw_step`).
The `m = 1` inputs, and nothing else: Lemma A (`Inflation.c_side_no_b`, in `junc_kill`), the row
word `a^j` (`Inflation.a_side_no_b`, `a_side_rigid`, in `row_all_a`), the `b`-free leg
(`lem:sidenob`, in `slot_leg`); each needs a line of fewer than `f` cells, which fails at `m ≥ 2`
(N = 44: `2c = a + 2b`, `2a = c`, leg word `c c a a a a` with `c + 4b` legal). -/
theorem rw_frame (L : LFrame F) : ∀ j m : ℕ, 1 ≤ j → j ≤ m → m + 1 ≤ f → ¬ CH F j m := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j IH =>
  intro m hj hjm hmf hC
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have key : ∀ k, ∀ m, m + 1 + k = f → j' + 1 ≤ m → CH F (j' + 1) m → False := by
    intro k
    induction k with
    | zero =>
      intro m hm hjm hC
      have hm' : m = f - 1 := by omega
      subst hm'
      exact rw_base F L j' (by omega) hC
    | succ k ihk =>
      intro m hm hjm hC
      exact ihk (m + 1) (by omega) (by omega)
        (rw_step F L j' m (by omega) hjm (fun i hi1 hij m' him hm'f => IH i hij m' hi1 him hm'f) hC)
  exact key (f - 1 - m) m (by omega) hjm hC

/-! ## For real dissections -/

/-- **`LFrame` holds in every apex frame (with cone coordinates) of every real `m = 1` dissection**:
the leg is `b`-free by `lem:sidenob` (`MirrorStripR2Real.leg_nob_real`, from
`ApexLegWord.leg_no_b`). -/
theorem lframe_real {k : Fin 3} (h : ApexFrameReal.M1Data D e f α β γ k)
    (FC : ApexPlacement.FrameCoords F) : LFrame F :=
  ⟨FC, leg_nob_real h F.huL F.htarget F.hlegR⟩

/-- **RW(j) for every apex frame of a real `m = 1` dissection — PROVED.**  For every congruent
dissection of the `m = 1` base-β target (coprime `2 ≤ e ≤ f − 2`, `M1Data`) and every apex frame
`F` of it with cone coordinates: no `C(j, m)`, `1 ≤ j ≤ m ≤ f − 1`. -/
theorem rw_real_all {k : Fin 3} (h : ApexFrameReal.M1Data D e f α β γ k)
    (FC : ApexPlacement.FrameCoords F) :
    ∀ j m : ℕ, 1 ≤ j → j ≤ m → m + 1 ≤ f → ¬ CH F j m :=
  rw_frame F (lframe_real F h FC)

/-- **RW(j) — THE ROW-WALL LEMMA FOR EVERY REAL `m = 1` DISSECTION — PROVED.**  Every congruent
dissection of the `m = 1` base-β target (coprime `2 ≤ e ≤ f − 2`, `M1Data`) carries its apex frame
`F` (`ApexLegWord.exists_hframe_coords_m1`), and in it no `C(j, m)`, `1 ≤ j ≤ m ≤ f − 1`, holds. -/
theorem rw_real {k : Fin 3} (h : ApexFrameReal.M1Data D e f α β γ k) :
    ∃ F : Erdos634.Draft.HalfTurnR3R4Glue.HFrame D e f α β γ, ApexPlacement.FrameCoords F ∧
      ∀ j m : ℕ, 1 ≤ j → j ≤ m → m + 1 ≤ f → ¬ CH F j m := by
  obtain ⟨F, FC⟩ := ApexLegWord.exists_hframe_coords_m1 D h.hco h.he h.hef h.hM h.hAng k
    h.hcorner h.hβ1 h.hβ2 h.hleg1 h.hleg2 h.hbase
  exact ⟨F, FC, rw_real_all F h FC⟩

end Erdos634.Draft.RowWallReal

#print axioms Erdos634.Draft.RowWallReal.junc_str
#print axioms Erdos634.Draft.RowWallReal.rw_base
#print axioms Erdos634.Draft.RowWallReal.rw_step
#print axioms Erdos634.Draft.RowWallReal.rw_frame
#print axioms Erdos634.Draft.RowWallReal.lframe_real
#print axioms Erdos634.Draft.RowWallReal.rw_real_all
#print axioms Erdos634.Draft.RowWallReal.rw_real
#print axioms Erdos634.Draft.RowWallReal.slot_int
#print axioms Erdos634.Draft.RowWallReal.slot_leg
#print axioms Erdos634.Draft.RowWallReal.junc_kill
#print axioms Erdos634.Draft.RowWallReal.cross_kill
#print axioms Erdos634.Draft.RowWallReal.row_all_a
#print axioms Erdos634.Draft.RowWallReal.row_one
#print axioms Erdos634.Draft.RowWallReal.row_step
#print axioms Erdos634.Draft.RowWallReal.start_of_up
#print axioms Erdos634.Draft.RowWallReal.seed_of_Xs
#print axioms Erdos634.Draft.RowWallReal.base_nstr
