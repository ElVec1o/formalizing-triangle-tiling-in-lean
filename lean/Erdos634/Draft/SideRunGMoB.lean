/-
Draft/SideRunGMoB.lean -- written 14 October 2026.  UNAUDITED.  In `AllThreshold`.  Second file of module M4 of the plan for
`thm:cornerrun` (the statement `M°(e+1)`; first file `Draft/SideRunGMoA.lean`, third file `Draft/SideRunGMo.lean`).

**The steps (a), (b), (c) of the proof of `M(s', j0)` at size `n = e + 1`, in the case where the row `Λ` is cut as `c^e`.**  Paper: Theorem `thm:cornerrun`, proof of `M°(e+1)`: "Steps (a), (b), (c) are as above; the
statements `M` that they call have sizes at most `e`. The only new point is in (b): the row `Λ = [p(0,1), p(e,1)]` has `e` edges and can be cut as `c^e` or as `a^f`.  For `c^e` the proof of (b) and (c) goes through ((c) calls
`K(e+1,1)` and `M(e+1,1)`, of size `e`)."

Every statement here repeats a statement of M2/M3/StepC for `StepCtxO` (size `≤ e + 1`) and, where the row is used, with the hypothesis `hall : RowLenAll .. (f^2)` (all edges on `Λ` are `c`) in place of `lambda_edges`:
`row_noBO`, `row_tilesO` (`row_noB`, `row_tiles` of M3), `noN_MO`, `stepAO` (`noN_M`, `stepA` of M2), `k2_shift_rowO`, `k3_shift_rowO`, `bad_mid_falseO`, `stepBO`, `k2_nextO`, `stepCO` (the same names of StepC),
with `right_end_false` replaced by `right_end_ang` (`Draft/SideRunGMoA.lean`).  The conclusion `cE_false` is: **the conditions (M1), (K2), (K3) for a pair of size `≤ e + 1` with all edges of `Λ` equal to `c` cannot hold together**
(given step (a) and the statements `M` below the size).

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGMoA

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.SideRunGA

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Set

variable {N : ℕ} {D : CongruentDissection N}

/-! ## 0. Step (a) at size `e + 1` -/

section stepaO

variable {e f : ℕ} {α β γ L ax ay x : ℝ}

/-- **`N_i(j0)` is not a tile** (paper, step (a): "Suppose `S_i = N_i(j0)`. It shows `β` at `p(i+1, j0)`, and the rest of the wedge has the angle `2α`: two tiles showing `α` (F).
Let `E` be the one beside the `b`-edge of `U(i+1, j0)`; it lays `b` or `c` on `ℓ_{i+1}` from `p(i+1, j0)`.  Take the lattice with origin `p(i+1, 0)` ... If `E` lays `c`, then (K1)
holds for it with `j* = j0`, against `K(s − i − 1, j0)`.  If `E` lays `b`, then `E` is the mirror image of `U(i+1, j0)` in `ℓ_{i+1}`, against `M(s − i − 1, j0)`").
`IH m` is `M` for the sizes `m` below the size `s − j0` of the pair.  (Conclusion `False`.) -/
theorem noN_MO (S : SetupG D e f α β γ L ax ay) (hε1 : (1 : ℝ) ^ 2 = 1) {s j0 i : ℕ}
    (hK2 : K2G D (e : ℝ) (f : ℝ) 1 x s j0) (hK3 : K3G D (e : ℝ) (f : ℝ) 1 x (s : ℝ) (j0 : ℝ))
    (hsf : s < f) (hne : s - j0 ≤ e + 1) (hi : i + 2 ≤ s - j0)
    (IH : ∀ m, 1 ≤ m → m < s - j0 → MGh D e f 1 m) :
    ∀ tN, HasV D tN (lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) (j0 : ℝ))
      (lpG (e : ℝ) (f : ℝ) 1 x (i : ℝ) ((j0 : ℝ) + 1))
      (lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) - nuG (e : ℝ) (f : ℝ)) ((j0 : ℝ) + 2 + nuG (e : ℝ) (f : ℝ))) →
      False := by
  intro tN hN
  have C : CtxBase D e f α β γ L ax ay 1 x := ⟨S, Or.inl rfl⟩
  have he0 := S.e0
  have hef := S.hef'
  obtain ⟨tUi, hUi⟩ := hK2.1 i j0 le_rfl (by omega)
  obtain ⟨tU2, hU2⟩ := hK2.1 (i + 1) j0 le_rfl (by omega)
  rw [Nat.cast_add, Nat.cast_one] at hU2
  have hch' := chordsAt_shift_K2 S hK2 (n := i + 1) (by omega) (by omega)
  have hs' : s - (i + 1) + (i + 1) = s := by omega
  have hK2' : K2G D (e : ℝ) (f : ℝ) 1 x (s - (i + 1) + (i + 1)) j0 := by rw [hs']; exact hK2
  have hK3' : K3G D (e : ℝ) (f : ℝ) 1 x ((s - (i + 1) + (i + 1) : ℕ) : ℝ) (j0 : ℝ) := by
    rw [hs']; exact hK3
  have hL : lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1 - 1) (j0 : ℝ) ∈ D.target.carrier := by
    rw [show lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1 - 1) (j0 : ℝ) = lpG (e : ℝ) (f : ℝ) 1 x (i : ℝ) (j0 : ℝ)
      from lpG_congr (by ring) rfl]
    exact hUi.mem₁
  have hint := bedge_interior C (Nat.cast_nonneg j0) hU2 hL
  have hcl : ∃ P' : Plane, FXG (e : ℝ) (f : ℝ) 1 P' = lvG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) ∧
      lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) (j0 : ℝ) ∈
        openSegment ℝ P' (lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) ((j0 : ℝ) + 1)) ∧
      ∀ ed ∈ D.lineChain (FXG (e : ℝ) (f : ℝ) 1) (lvG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1)),
        ¬ Straddles ((D.tile ed.1).edge ed.2) P' (lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) (j0 : ℝ))
          (lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) ((j0 : ℝ) + 1)) := by
    rcases Nat.eq_zero_or_pos j0 with hj0 | hj0
    · exact clamp_side S hε1 _ _ (by rw [hj0]; simp)
    · obtain ⟨j', rfl⟩ : ∃ j', j0 = j' + 1 := ⟨j0 - 1, by omega⟩
      obtain ⟨tD, hD⟩ := hK2.2 i j' (by omega) (by omega)
      have hle : ∀ i', FXG (e : ℝ) (f : ℝ) 1 ((D.tile tD).pts i') ≤ lvG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) := by
        refine hD.all (P := fun p => FXG (e : ℝ) (f : ℝ) 1 p ≤ lvG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1))
          (le_of_eq (FXG_lp hε1 _ _)) ?_ (le_of_eq (FXG_lp hε1 _ _))
        dsimp only
        rw [FXG_lp hε1]
        exact lvG_le he0 hef (by linarith)
      obtain ⟨k, m, j₃, hkm, hkj, hmj, hk, hm, hj⟩ := hD
      rw [Nat.cast_add, Nat.cast_one]
      exact clamp_tile S hε1 hkj hk hj hle
  have hE := col_next S hε1 hU2 hint hcl
  have hnγ : ∀ (iT : Fin N) (k m' : Fin 3), k ≠ m' →
      (D.tile iT).pts k = lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) (j0 : ℝ) →
      (D.tile iT).pts m' = lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) ((j0 : ℝ) + 1) →
      (∀ i', FXG (e : ℝ) (f : ℝ) 1 ((D.tile iT).pts i') ≤ lvG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1)) →
      (D.tile iT).localAngle (lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) (j0 : ℝ)) ≠ γ := by
    intro iT k m' hkm hk hm' hle hγ0
    rcases Nat.eq_zero_or_pos j0 with hj0 | hj0
    · -- the point `p(i+1, 0)` is on the side
      subst hj0
      obtain ⟨hx0, hxL, -⟩ := open_shift_K2 S hK2 (n := i + 1) (by omega) (by omega)
      have hfr := S.base_frontier hx0 hxL
      have hpt : mkPt (shiftX (f : ℝ) 1 x (i + 1)) 0 = lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) 0 := by
        unfold lpG shiftX; exact mkPt_congr (by push_cast; ring) (by ring)
      rw [hpt] at hfr
      simp only [Nat.cast_zero] at hUi hN hγ0
      exact noN_gamma_bdry S hε1 hUi hN hγ0 hfr
    · obtain ⟨j', rfl⟩ : ∃ j', j0 = j' + 1 := ⟨j0 - 1, by omega⟩
      obtain ⟨tDL, hDL⟩ := hK2.2 i j' (by omega) (by omega)
      obtain ⟨tUl, hUl⟩ := hK2.1 (i + 1) j' (by omega) (by omega)
      obtain ⟨tDl, hDl⟩ := hK2.2 (i + 1) j' (by omega) (by omega)
      obtain ⟨tUr, hUr⟩ := hK2.1 (i + 1) (j' + 1) le_rfl (by omega)
      simp only [Nat.cast_add, Nat.cast_one] at hUl hDl hUr hUi hN hγ0 hle hk hm'
      exact noN_gamma_int S hε1 hDL hUl hDl hUr hUi hN hle hγ0
  exact beside_contra S (Or.inl rfl) (n := i + 1) (s' := s - (i + 1)) (j := j0)
    (m := s - (i + 1) - j0) (c := (i : ℝ) + 1) (η := (j0 : ℝ)) (by norm_num) rfl hch' hK2' hK3'
    (by omega) (by omega) (IH _ (by omega) (by omega)) rfl (by omega) hE hnγ

/-- **STEP (a)**: `D(i, j0)` is a tile for `0 ≤ i ≤ n − 2` (`n = s − j0`).  (Paper: "As in step (2) of the proof of `K`, the free wedge at `p(i+1, j0)` is `(α, π − β)`.  Let `S_i`
be the tile in it beside the `a`-edge of `U(i, j0)`.  If `S_i` lays `b` or `c` there, the conditions of `M(i+1+j0, j0)` hold ... So `S_i` lays `a` and is `D(i, j0)` or `N_i(j0)`.
Suppose `S_i = N_i(j0)`: ...": `D_ofG` with `hR` from `MGh (i+1)` and `hNo` from `noN_M`.) -/
theorem stepAO (S : SetupG D e f α β γ L ax ay) (hch : ChordsAt D (e : ℝ) (f : ℝ) 1 x) {s j0 : ℕ}
    (hM : MirrorAt D (e : ℝ) (f : ℝ) 1 x (j0 : ℝ)) (hK2 : K2G D (e : ℝ) (f : ℝ) 1 x s j0)
    (hK3 : K3G D (e : ℝ) (f : ℝ) 1 x (s : ℝ) (j0 : ℝ)) (hsf : s < f) (hne : s - j0 ≤ e + 1)
    (IH : ∀ m, 1 ≤ m → m < s - j0 → MGh D e f 1 m) :
    ∀ i, i + 2 ≤ s - j0 → DTG D (e : ℝ) (f : ℝ) 1 x i j0 := by
  intro i hi
  have C : CtxBase D e f α β γ L ax ay 1 x := ⟨S, Or.inl rfl⟩
  have hU1 := hK2.1 i j0 le_rfl (by omega)
  have hU2 : UTG D (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) j0 := by
    have h := hK2.1 (i + 1) j0 le_rfl (by omega)
    rwa [Nat.cast_add, Nat.cast_one] at h
  refine C.D_ofG hU1 hU2 ?_ ?_ (noN_MO S (by norm_num) hK2 hK3 hsf hne hi IH)
  · rcases Nat.eq_zero_or_pos j0 with hj | hj
    · exact Or.inl hj
    · exact Or.inr ⟨hj, hK2.2 (i + 1) (j0 - 1) (by omega) (by omega)⟩
  · intro w hw
    refine IH (i + 1) (by omega) (by omega) x (i + j0 + 1) j0 hch (by omega) (by omega) (by omega)
      (by omega) hM ⟨fun a b hb hab => hK2.1 a b hb (by omega),
        fun a b hb hab => hK2.2 a b hb (by omega)⟩ ?_
    have e1 : ((i + j0 + 1 : ℕ) : ℝ) = (i : ℝ) + j0 + 1 := by push_cast; ring
    rw [e1]
    exact Or.inr ⟨w, hw⟩

end stepaO

/-! ## 1. Step (b): the tiles above `Λ` when the edges are `c` -/

section rowO

variable {e f : ℕ} {α β γ L ax ay x : ℝ} {s j0 : ℕ}

local notation "LV" => -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j0 : ℝ) + 1))

/-- no `b`-edge in a unit segment of `Λ` (the hypothesis `hnob` of `row_stepG`) -/
theorem row_noBO (W : StepCtxO D e f α β γ L ax ay x s j0) {q : ℕ} (hq1 : 1 ≤ q)
    (hall : RowLenAll D (e : ℝ) (f : ℝ) x j0 q ((f : ℝ) ^ 2)) :
    ∀ ρ : ℝ, 0 ≤ ρ → ρ + 1 ≤ q → ∀ ed ∈ D.lineChain (GHG (f : ℝ)) LV,
      (D.tile ed.1).edge ed.2 ⊆ segment ℝ (lpG (e : ℝ) (f : ℝ) 1 x ρ ((j0 : ℝ) + 1))
        (lpG (e : ℝ) (f : ℝ) 1 x (ρ + 1) ((j0 : ℝ) + 1)) →
      dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1)) ≠ (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
  intro ρ h0 h1 ed he hsub hb
  have he0 := W.S.e0
  obtain ⟨hp, hq', hle⟩ := Dissection.mem_lineChain.mp he
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  have hseg : segment ℝ (lpG (e : ℝ) (f : ℝ) 1 x ρ ((j0 : ℝ) + 1)) (lpG (e : ℝ) (f : ℝ) 1 x (ρ + 1) ((j0 : ℝ) + 1))
      ⊆ segment ℝ (lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1)) (lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1)) :=
    (convex_segment _ _).segment_subset
      (lpG_row_mem_seg (e : ℝ) (f : ℝ) 1 x _ hqpos h0 (by linarith))
      (lpG_row_mem_seg (e : ℝ) (f : ℝ) 1 x _ hqpos (by linarith) h1)
  have hE : (D.tile ed.1).edge ed.2 = segment ℝ ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1)) :=
    rfl
  have hkS := hseg (hsub (by rw [hE]; exact left_mem_segment ℝ _ _))
  have hmS := hseg (hsub (by rw [hE]; exact right_mem_segment ℝ _ _))
  have hne : ed.2 ≠ ed.2 + 1 := (fin3_succ_ne ed.2).2.1.symm
  have h := hall ed.1 ed.2 (ed.2 + 1) hne hp hq' hle hkS hmS
  rw [hb] at h
  have : (e : ℝ) ^ 2 = 0 := by linarith
  exact absurd this (pow_pos he0 2).ne'

/-- **ABOVE EACH SEGMENT `[p(r, j0+1), p(r+1, j0+1)]` OF `Λ` LIES A TILE `V_r`**: it is `U(r, j0+1)`, or it is a `c`-tile showing `β` at the left end and `α` at the right end (paper: "above each segment lies a tile
`V_r` with `α` and `β` at its ends").  The tiles are found from the left, one after the other: the first edge at `p(r, j0+1)` (`CtxBase.row_stepG`), clamped by the previous tile (`clamp_b`); `lambda_edges` says that
its edge is a `c`-edge. -/
theorem row_tilesO (W : StepCtxO D e f α β γ L ax ay x s j0) {q : ℕ} (hq : q + j0 + 1 = s) (hq1 : 1 ≤ q)
    (hall : RowLenAll D (e : ℝ) (f : ℝ) x j0 q ((f : ℝ) ^ 2)) :
    ∀ r : ℕ, r + 1 ≤ q →
      (UTG D (e : ℝ) (f : ℝ) 1 x (r : ℝ) ((j0 : ℝ) + 1) ∨ VBad D α (e : ℝ) (f : ℝ) x j0 (r : ℝ)) := by
  have S := W.S
  have C : CtxBase D e f α β γ L ax ay 1 x := ⟨S, Or.inl rfl⟩
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have he0 := S.e0
  have hef := S.hef'
  have hf0 := S.f0
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  obtain ⟨hαβ, hαγ, -, -, -, -, -, -, -, -⟩ :=
    distinct_of_pos_ne S.hA.hα S.hA.hβ S.hA.hαβ S.hA.hγdef S.hA.hrel
  have hea : (e : ℝ) * (f : ℝ) < (f : ℝ) ^ 2 := by nlinarith [mul_pos hf0 (sub_pos.mpr hef)]
  have heb : (f : ℝ) ^ 2 - (e : ℝ) ^ 2 < (f : ℝ) ^ 2 := by nlinarith [mul_pos he0 he0]
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hr
    obtain ⟨tD, hDt⟩ := W.hA r (by omega)
    have hcl : ∃ P' : Plane, GHG (f : ℝ) P' = LV ∧
        lpG (e : ℝ) (f : ℝ) 1 x (r : ℝ) ((j0 : ℝ) + 1) ∈
          openSegment ℝ P' (lpG (e : ℝ) (f : ℝ) 1 x ((r : ℝ) + 1) ((j0 : ℝ) + 1)) ∧
        ∀ ed ∈ D.lineChain (GHG (f : ℝ)) LV,
          ¬ Straddles ((D.tile ed.1).edge ed.2) P' (lpG (e : ℝ) (f : ℝ) 1 x (r : ℝ) ((j0 : ℝ) + 1))
            (lpG (e : ℝ) (f : ℝ) 1 x ((r : ℝ) + 1) ((j0 : ℝ) + 1)) := by
      rcases Nat.eq_zero_or_pos r with hr0 | hrpos
      · subst hr0
        rw [Nat.cast_zero]
        exact row_clamp_leftO W (ρ := 0 + 1) (by norm_num)
      · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        obtain ⟨tV, k, m, hkm, hk, hm, hle⟩ := vedge_of_vex S (ih r' (by omega) (by omega))
        rw [Nat.cast_add, Nat.cast_one]
        have hmid := lpG_row_mid (e : ℝ) (f : ℝ) 1 x ((j0 : ℝ) + 1) (a := (r' : ℝ)) (b := (r' : ℝ) + 1)
          (c := (r' : ℝ) + 1 + 1) (by linarith) (by linarith)
        exact ⟨lpG (e : ℝ) (f : ℝ) 1 x (r' : ℝ) ((j0 : ℝ) + 1), GHG_lp _ _ _ _ _ _, hmid,
          clamp_b D.toDissection (GHG (f : ℝ)) (GHG_ne he0 hef) _
            (lpG_ne_xi he0 hef hε (by linarith)) (GHG_lp _ _ _ _ _ _) (GHG_lp _ _ _ _ _ _)
            (GHG_lp _ _ _ _ _ _) hmid hkm hk hm hle⟩
    rcases C.row_stepG hDt (Nat.cast_nonneg j0) hcl
        (row_noBO W hq1 hall (r : ℝ) (Nat.cast_nonneg r) (by exact_mod_cast hr)) with
      hU | ⟨ix, k, m, j₃, t, hkm, hkj, hmj, hk, ht, hm, hle, hθ, -⟩
    · exact Or.inl hU
    · right
      have hd : dist ((D.tile ix).pts k) ((D.tile ix).pts m) = t * (f : ℝ) ^ 2 := by
        rw [hk, hm, dist_rowG he0 hef hε (by linarith)]; ring
      have ht1 : t ≤ 1 := by
        by_contra hgt
        rw [not_le] at hgt
        have h1 : (f : ℝ) ^ 2 < t * (f : ℝ) ^ 2 := by nlinarith [mul_pos (sub_pos.mpr hgt) (pow_pos hf0 2)]
        rcases vertex_dist_casesG D S.hM ix hkm with h | h | h <;> rw [hd] at h <;> linarith
      have hrq : (r : ℝ) + 1 ≤ q := by exact_mod_cast hr
      have hkS := lpG_row_mem_seg (e : ℝ) (f : ℝ) 1 x ((j0 : ℝ) + 1) hqpos (Nat.cast_nonneg r)
        (by linarith)
      have hmS := lpG_row_mem_seg (e : ℝ) (f : ℝ) 1 x ((j0 : ℝ) + 1) (ρ := (r : ℝ) + t) hqpos
        (by positivity) (by linarith)
      have hc := hall ix k m hkm (by rw [hk]; exact GHG_lp _ _ _ _ _ _)
        (by rw [hm]; exact GHG_lp _ _ _ _ _ _) hle (by rw [hk]; exact hkS) (by rw [hm]; exact hmS)
      have ht1' : t = 1 := by
        have h1 : t * (f : ℝ) ^ 2 = 1 * (f : ℝ) ^ 2 := by rw [one_mul, ← hd, hc]
        exact mul_right_cancel₀ (pow_pos hf0 2).ne' h1
      subst ht1'
      rcases sides_of_c_edgeG D S.tile S.hM ix hkm hkj hmj hc with ⟨s1, s2⟩ | ⟨s1, s2⟩
      · have hAm := angle_at_vertexG D S.tile S.hM ix hkm.symm hmj hkj
        exact ⟨ix, k, m, j₃, hkm, hkj, hmj, hk, hm, hle, by
          rw [← hm]; exact hAm.1 (by rw [dist_comm]; exact s1)⟩
      · exfalso
        have hAk := angle_at_vertexG D S.tile S.hM ix hkm hkj hmj
        have hαk : (D.tile ix).localAngle ((D.tile ix).pts k) = α :=
          hAk.1 (by rw [dist_comm]; exact s2)
        rw [hk] at hαk
        rcases hθ with h | h
        · exact hαβ (hαk.symm.trans h)
        · exact hαγ (hαk.symm.trans h)

end rowO

/-! ## 2. Steps (b) (downward induction) and (c) -/

section stepbcO

variable {e f : ℕ} {α β γ L ax ay x : ℝ} {s j0 : ℕ}

/-- (K2) of the lattice with origin `p(r+1, 0)` at the level `j0 + 1`: the rows `≤ j0` are given, the row `j0 + 1` is `U(c, j0+1)`, `c ≥ r+1`, and `D(i, j0)`, `i ≥ r+1`, is step (a) -/
theorem k2_shift_rowO (W : StepCtxO D e f α β γ L ax ay x s j0) {r : ℕ}
    (hU : ∀ c : ℕ, r + 1 ≤ c → c + 2 ≤ s - j0 → UTG D (e : ℝ) (f : ℝ) 1 x (c : ℝ) ((j0 : ℝ) + 1)) :
    K2G D (e : ℝ) (f : ℝ) 1 (shiftX (f : ℝ) 1 x (r + 1)) (s - (r + 1)) (j0 + 1) := by
  refine ⟨fun i j hj hij => ?_, fun i j hj hij => ?_⟩
  · rw [UTG_shift]
    rcases Nat.lt_or_ge j (j0 + 1) with h | h
    · have h' := W.hK2.1 (i + (r + 1)) j (by omega) (by omega)
      rwa [Nat.cast_add] at h'
    · obtain rfl : j = j0 + 1 := by omega
      have h' := hU (i + (r + 1)) (by omega) (by omega)
      push_cast at h' ⊢
      exact h'
  · rw [DTG_shift]
    rcases Nat.lt_or_ge j j0 with h | h
    · have h' := W.hK2.2 (i + (r + 1)) j h (by omega)
      rwa [Nat.cast_add] at h'
    · obtain rfl : j = j0 := by omega
      have h' := W.hA (i + (r + 1)) (by omega)
      rwa [Nat.cast_add] at h'

/-- (K3) of the lattice with origin `p(r+1, 0)` at the level `j0 + 1` is the given one (`K3G.mono`, `K3G_shift_nat`) -/
theorem k3_shift_rowO (W : StepCtxO D e f α β γ L ax ay x s j0) {r : ℕ} (hr : r + 1 ≤ s) :
    K3G D (e : ℝ) (f : ℝ) 1 (shiftX (f : ℝ) 1 x (r + 1)) ((s - (r + 1) : ℕ) : ℝ) ((j0 + 1 : ℕ) : ℝ) := by
  have h3 : K3G D (e : ℝ) (f : ℝ) 1 x (((s - (r + 1)) + (r + 1) : ℕ) : ℝ) ((j0 + 1 : ℕ) : ℝ) := by
    rw [Nat.sub_add_cancel hr]
    exact W.hK3.mono (by push_cast; linarith)
  exact K3G_shift_nat (by norm_num) h3

/-- **`V_r` is not a tile showing `α` at `p(r+1, j0+1)`, if `V_{r+1}, ..., V_{n−2}` are lattice tiles** (paper: "Let `r ≤ n − 3`, let `V_{r+1}, ..., V_{n−2}` be lattice tiles, and suppose that `V_r`
shows `α` at `p(r+1, j0+1)`.  Above `Λ` at that point `V_r` takes `(π − α, π)` and `U(r+1, j0+1)` takes `(0, α)`; the three tiles between show `α, β, β` (F).  Let `E` be the one beside the `b`-edge of
`U(r+1, j0+1)`. ..."; here `n = q + 1`).  `bad_gamma_free` is the counting at `p(r+1, j0+1)` (the paper's "`α, β, β`": the tile `E` does not show `γ`); `bad_colnext` is "`E` lays `a` or `c` (K1) / the whole
`b`-edge", the clamp of `p(r+1, j0+1)` from below being the `b`-edge of `D(r, j0)`; `beside_core` is the two-line argument "against `K(s' − r − 1, j0 + 1)` / `M(s' − r − 1, j0 + 1)`, of size `n − r − 2 < n`" at the
lattice with origin `p(r+1, 0)` (`k2_shift_row`, `k3_shift_row`, `chordsAt_shift_K2`).  (Conclusion `False`.) -/
theorem bad_mid_falseO (W : StepCtxO D e f α β γ L ax ay x s j0) {q : ℕ} (hq : q + j0 + 1 = s) (hq1 : 1 ≤ q)
    {r : ℕ} (hr : r + 2 ≤ q)
    (hU : ∀ c : ℕ, r + 1 ≤ c → c + 1 ≤ q → UTG D (e : ℝ) (f : ℝ) 1 x (c : ℝ) ((j0 : ℝ) + 1))
    (hbad : VBad D α (e : ℝ) (f : ℝ) x j0 (r : ℝ)) : False := by
  have S := W.S
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have he0 := S.e0
  have hef := S.hef'
  have hsf := W.hsf
  have hne := W.hne
  -- the four lattice tiles at `p(r+1, j0+1)`
  obtain ⟨tDL, hDL⟩ := W.hA r (by omega)
  have hUl' : UTG D (e : ℝ) (f : ℝ) 1 x (((r + 1 : ℕ)) : ℝ) (j0 : ℝ) :=
    W.hK2.1 (r + 1) j0 le_rfl (by omega)
  have hDl' : DTG D (e : ℝ) (f : ℝ) 1 x (((r + 1 : ℕ)) : ℝ) (j0 : ℝ) := W.hA (r + 1) (by omega)
  have hUr' := hU (r + 1) (by omega) (by omega)
  push_cast at hUl' hDl' hUr'
  obtain ⟨tUl, hUl⟩ := hUl'
  obtain ⟨tDl, hDl⟩ := hDl'
  obtain ⟨tUr, hUr⟩ := hUr'
  obtain ⟨tV, k, m, j₃, hkm, hkj, hmj, hk, hm, hle, hαV⟩ := hbad
  have ntVDL : tV ≠ tDL := by
    obtain ⟨kd, hkd⟩ := hDL.idx₁
    exact ne_of_F (GHG (f : ℝ)) hle (i := kd) (by rw [hkd]; exact GHG_gt he0 hef (by linarith))
  have ntVUr : tV ≠ tUr := by
    refine HasV.ne_of_vertex hUr hk ?_ ?_ ?_
    · exact lpG_ne_xi he0 hef hε (by intro h; linarith)
    · exact lpG_ne_xi he0 hef hε (by intro h; linarith)
    · exact lpG_ne_eta he0 hef (by intro h; linarith)
  have hnγ := bad_gamma_free S hDL hUl hDl hUr hαV ntVDL ntVUr
  have hVmem : lpG (e : ℝ) (f : ℝ) 1 x (r : ℝ) ((j0 : ℝ) + 1) ∈ D.target.carrier := by
    rw [← hk]; exact pts_mem_target D.toDissection tV k
  have hE := bad_colnext S (η := (j0 : ℝ)) (by positivity) hDL hUr hVmem
  exact beside_core S (Or.inl rfl) (n := r + 1) (s' := s - (r + 1)) (j := j0 + 1)
    (m := s - (r + 1) - (j0 + 1)) (c := (r : ℝ) + 1) (η := (j0 : ℝ) + 1)
    (by push_cast; ring) (by push_cast; ring)
    (chordsAt_shift_K2 S W.hK2 (by omega) (by omega))
    (k2_shift_rowO W (fun c h1 h2 => hU c h1 (by omega))) (k3_shift_rowO W (by omega))
    (by omega) (by omega) (W.IH _ (by omega) (by omega)) rfl (by omega) hE hnγ

/-- **STEP (b): `U(r, j0+1)` is a tile for `0 ≤ r ≤ n − 2`** (`n = q + 1 = s − j0`; paper: "So `V_r` shows `β` at `p(r+1, j0+1)`: `V_r = U(r, j0+1)`"; the downward induction from `r = n − 2`,
which is `right_end_false`, to `r = 0`).  The tiles `V_r` are those of `row_tiles`. -/
theorem stepBO (W : StepCtxO D e f α β γ L ax ay x s j0) {q : ℕ} (hq : q + j0 + 1 = s) (hq1 : 1 ≤ q)
    (hall : RowLenAll D (e : ℝ) (f : ℝ) x j0 q ((f : ℝ) ^ 2)) :
    ∀ r : ℕ, r + 1 ≤ q → UTG D (e : ℝ) (f : ℝ) 1 x (r : ℝ) ((j0 : ℝ) + 1) := by
  have key : ∀ d r : ℕ, r + 1 + d = q → UTG D (e : ℝ) (f : ℝ) 1 x (r : ℝ) ((j0 : ℝ) + 1) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro r hrd
      rcases row_tilesO W hq hq1 hall r (by omega) with hU | hbad
      · exact hU
      · exfalso
        rcases Nat.eq_zero_or_pos d with hd0 | hdpos
        · subst hd0
          obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
          have hrq : r = q' := by omega
          subst hrq
          obtain ⟨tV, k, m, j₃, hkm, hkj, hmj, hk, hm, hle, hαV⟩ := hbad
          exact right_end_ang W hq (Or.inl rfl) hle hαV
        · exact bad_mid_falseO W hq hq1 (r := r) (by omega)
            (fun c hc1 hc2 => ih (q - 1 - c) (by omega) c (by omega)) hbad
  intro r hr
  exact key (q - 1 - r) r (by omega)

/-- **"Now (K2) holds for `(s', j0+1)`"**: the row `j0 + 1` is `U(r, j0+1)`, `r ≤ n − 2` (step (b)); the tiles `D(i, j0)` are step (a) -/
theorem k2_nextO (W : StepCtxO D e f α β γ L ax ay x s j0) {q : ℕ} (hq : q + j0 + 1 = s)
    (hU : ∀ r : ℕ, r + 1 ≤ q → UTG D (e : ℝ) (f : ℝ) 1 x (r : ℝ) ((j0 : ℝ) + 1)) :
    K2G D (e : ℝ) (f : ℝ) 1 x s (j0 + 1) := by
  refine ⟨fun i j hj hij => ?_, fun i j hj hij => ?_⟩
  · rcases Nat.lt_or_ge j (j0 + 1) with h | h
    · exact W.hK2.1 i j (by omega) hij
    · obtain rfl : j = j0 + 1 := by omega
      have h' := hU i (by omega)
      push_cast
      exact h'
  · rcases Nat.lt_or_ge j j0 with h | h
    · exact W.hK2.2 i j h hij
    · obtain rfl : j = j0 := by omega
      exact W.hA i (by omega)

/-- **STEP (c)** (paper: "At `p(0, j0+1)` the tiles `T` and `U(0, j0+1)` leave on the side σ the wedge `(α, γ)`, of angle `α + β`: one tile showing `α` and one showing `β`.  Let `T⁺` be the one beside `ℓ`.
If `T⁺` lays `a` or `c` on `ℓ`, then (K1) holds with `j* = j0 + 1` (clamped from below by the edge of `T`), against `K(s', j0+1)`.  If `T⁺` lays `b`, it shows `α` at `p(0, j0+1)` and is the mirror image of
`U(0, j0+1)` in `ℓ`, against `M(s', j0+1)`, of size `n − 1`").  The tile `T⁺` does not show `γ` at `p(0, j0+1)`: that point is interior to Δ (a sub-chord), and the tiles `U(0, j0)`, `T`, `T⁺` would show
`γ` three times while `U(0, j0+1)` shows `α`, against (F) (`fig_int`).  (Conclusion `False`.) -/
theorem stepCO (W : StepCtxO D e f α β γ L ax ay x s j0) {q : ℕ} (hq : q + j0 + 1 = s) (hq1 : 1 ≤ q)
    (hU : ∀ r : ℕ, r + 1 ≤ q → UTG D (e : ℝ) (f : ℝ) 1 x (r : ℝ) ((j0 : ℝ) + 1)) : False := by
  have S := W.S
  have C : CtxBase D e f α β γ L ax ay 1 x := ⟨S, Or.inl rfl⟩
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have he0 := S.e0
  have hef := S.hef'
  have hne := W.hne
  have hsf := W.hsf
  have hK2n := k2_nextO W hq hU
  have hU0' : UTG D (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1) := by
    have h := hU 0 (by omega)
    rwa [Nat.cast_zero] at h
  obtain ⟨tU0, hU0⟩ := hU0'
  obtain ⟨tT, hT⟩ := W.hM
  have hT' : HasV D tT (lpG (e : ℝ) (f : ℝ) 1 x 0 (j0 : ℝ)) (lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1))
      (lpG (e : ℝ) (f : ℝ) 1 x (-1) ((j0 : ℝ) + mirK (e : ℝ) (f : ℝ))) := hT
  obtain ⟨hTle, -⟩ := mirror_side S hε hT'
  obtain ⟨-, hTγ, -⟩ := mirror_angles S hε hT'
  -- the chord through `p(0, j0+1)`
  have hmem : lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 + 2 : ℕ) : ℝ) ∈ D.target.carrier := by
    have h := hU0.mem₃
    rwa [show ((j0 + 2 : ℕ) : ℝ) = (j0 : ℝ) + 1 + 1 by push_cast; ring]
  have hint := col_sub_interior W.hch (j := j0 + 2) (by omega) hmem (a := (j0 : ℝ) + 1)
    (b := (j0 : ℝ) + 1 + 1) (by positivity) (by linarith) (by push_cast; linarith)
  have hQint : lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1) ∈ interior D.target.carrier :=
    W.hch (j0 + 2) (by omega) hmem
      (lpG_col_mem (e : ℝ) (f : ℝ) 1 x 0 (a := 0) (by positivity) (by push_cast; linarith))
  -- the clamp from below: the `b`-edge of `T`
  have hT'' := hT'
  obtain ⟨kT, mT, jT, hkm, hkj, hmj, hkT, hmT, hjT⟩ := hT''
  have hcl := clamp_tile S hε (c := 0) (η := (j0 : ℝ)) hkm hkT hmT hTle
  have hE : ColNext D (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1) := col_next S hε hU0 hint hcl
  -- `T⁺` does not show `γ`
  have hnγ : ∀ (iT : Fin N) (k' m' : Fin 3), k' ≠ m' →
      (D.tile iT).pts k' = lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1) →
      (D.tile iT).pts m' = lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1 + 1) →
      (∀ i, FXG (e : ℝ) (f : ℝ) 1 ((D.tile iT).pts i) ≤ lvG (e : ℝ) (f : ℝ) 1 x 0) →
      (D.tile iT).localAngle (lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1)) ≠ γ := by
    intro iT k' m' hk'm' hk' hm' hle' hγ
    have hUj' : UTG D (e : ℝ) (f : ℝ) 1 x 0 (j0 : ℝ) := by
      have h := W.hK2.1 0 j0 le_rfl (by omega)
      rwa [Nat.cast_zero] at h
    obtain ⟨tUj, hUj⟩ := hUj'
    have aUj := (U_anglesG S hε hUj).2.2
    have aU0 := (U_anglesG S hε hU0).1
    obtain ⟨k2, hk2⟩ := hUj.idx₂
    have hlt : lvG (e : ℝ) (f : ℝ) 1 x 0 < FXG (e : ℝ) (f : ℝ) 1 ((D.tile tUj).pts k2) := by
      rw [hk2, FXG_lp hε]; exact lvG_lt he0 hef (by linarith)
    have nTU : tT ≠ tUj := ne_of_F (FXG (e : ℝ) (f : ℝ) 1) hTle (i := k2) hlt
    have nIU : iT ≠ tUj := ne_of_F (FXG (e : ℝ) (f : ℝ) 1) hle' (i := k2) hlt
    have nIT : iT ≠ tT := by
      refine HasV.ne_of_vertex hT' hm' ?_ ?_ ?_
      · exact lpG_ne_eta he0 hef (by intro h; linarith)
      · exact lpG_ne_eta he0 hef (by intro h; linarith)
      · exact lpG_ne_xi he0 hef hε (by norm_num)
    have hγs : ∀ i ∈ ({tUj, tT, iT} : Finset (Fin N)),
        (D.tile i).localAngle (lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1)) = γ :=
      forall_mem3 (P := fun i => (D.tile i).localAngle
        (lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1)) = γ) aUj hTγ hγ
    have hαs : ∀ i ∈ ({tU0} : Finset (Fin N)),
        (D.tile i).localAngle (lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1)) = α := by
      intro i hi
      rw [Finset.mem_singleton.mp hi]; exact aU0
    have c1 := card_le_angle _ γ hγs
    have c2 := card_le_angle _ α hαs
    rw [card3 nTU.symm nIU.symm nIT.symm] at c1
    rw [Finset.card_singleton] at c2
    obtain ⟨k0, hk0⟩ := hU0.idx₁
    exact fig_contra_a1g3 (fig_int S hQint hk0) c2 c1
  exact beside_core S (Or.inl rfl) (n := 0) (s' := s) (j := j0 + 1) (m := s - (j0 + 1))
    (c := 0) (η := (j0 : ℝ) + 1) (by simp) (by push_cast; ring)
    (by rw [shiftX_zero]; exact W.hch) (by rw [shiftX_zero]; exact hK2n)
    (by rw [shiftX_zero]; push_cast; exact W.hK3.mono (by linarith))
    (by omega) W.hsf (W.IH _ (by omega) (by omega)) rfl (by omega) hE hnγ

/-- **THE CASE `c^e` OF `M°(e+1)`**: the conditions (M1), (K2), (K3) for a pair of size `≤ e + 1`, with step (a) and all edges of `Λ` equal to `c`, cannot hold together (paper: "For `c^e` the proof of (b) and (c) goes through").  (Conclusion `False`.) -/
theorem cE_false (W : StepCtxO D e f α β γ L ax ay x s j0) {q : ℕ} (hq : q + j0 + 1 = s) (hq1 : 1 ≤ q)
    (hall : RowLenAll D (e : ℝ) (f : ℝ) x j0 q ((f : ℝ) ^ 2)) : False :=
  stepCO W hq hq1 (stepBO W hq hq1 hall)

end stepbcO

end Erdos634.Draft.SideRunGA

#print axioms Erdos634.Draft.SideRunGA.noN_MO
#print axioms Erdos634.Draft.SideRunGA.stepAO
#print axioms Erdos634.Draft.SideRunGA.row_noBO
#print axioms Erdos634.Draft.SideRunGA.row_tilesO
#print axioms Erdos634.Draft.SideRunGA.k2_shift_rowO
#print axioms Erdos634.Draft.SideRunGA.k3_shift_rowO
#print axioms Erdos634.Draft.SideRunGA.bad_mid_falseO
#print axioms Erdos634.Draft.SideRunGA.stepBO
#print axioms Erdos634.Draft.SideRunGA.k2_nextO
#print axioms Erdos634.Draft.SideRunGA.stepCO
#print axioms Erdos634.Draft.SideRunGA.cE_false
