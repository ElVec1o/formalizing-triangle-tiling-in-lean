/-
Draft/SideRunGMStepC.lean -- written 14 October 2026.  UNAUDITED.  In `AllThreshold`.  Third file of the induction for the statement `M` in the plan for
`thm:cornerrun` (M1 `Draft/SideRunGMirror.lean`, M2 `Draft/SideRunGMStep.lean`, M3 `Draft/SideRunGMStepB.lean`; the statement `M°` of the plan, module M4, is NOT in this file).

**The induction for `M(s', j0)`: the downward induction of step (b), step (c), the statement `MG_all`, and the corollary for a short `C1`-run at the corner.**
Paper: Theorem `thm:cornerrun`, "Proof of `M(s', j0)`", size `n ≥ 2`, steps (b) (second half) and (c); (private working notes, not included) Section 4.

CONTENTS.
0. Tools: `lpG_col_mem`, `col_sub_interior` (a sub-segment of an interior chord is interior), `k2_shift_row`, `k3_shift_row` ((K2), (K3) of the lattice with origin `p(r+1, 0)` at the level
   `j0 + 1`: **"its (K2) holds (rows up to `j0`: given; row `j0+1`: the tiles `U(r+1, j0+1), ..., U(n−2, j0+1)`; and `D(i, j0)`, `i ≥ r+1`, by (a)), and its (K3) is the given one"**),
   `D_left_le`.
1. STEP (b), the downward induction: `fig_contra_a3g2`, `fig_contra_a1g3` (the counting of (F)), `bad_gamma_free` (the tile `E` does not show `γ`: the paper's "`α, β, β`"), `bad_colnext` (`E` lays `a`/`c`, or has
   the whole `b`-edge), `bad_mid_false` (**"Let `r ≤ n − 3`, let `V_{r+1}, ..., V_{n−2}` be lattice tiles, and suppose that `V_r` shows `α` at `p(r+1, j0+1)` ... Let `E` be the one beside the
   `b`-edge of `U(r+1, j0+1)`. ... If `E` lays `a` or `c`, then (K1) holds with `j* = j0 + 1` (clamped from below by the `b`-edge of `D(r, j0)`), against `K(s' − r − 1, j0 + 1)`.  If `E` lays `b`,
   it shows `α` and is the mirror image of `U(r+1, j0+1)` in `ℓ_{r+1}`, against `M(s' − r − 1, j0 + 1)`, of size `n − r − 2 < n`.  So `V_r` shows `β`"**: `col_next`, `beside_core`, `lower_half`),
   `stepB` (**`U(r, j0+1)` is a tile for `0 ≤ r ≤ n − 2`**).
2. STEP (c): `k2_next` (**"Now (K2) holds for `(s', j0+1)`"**), `stepC` (**"At `p(0, j0+1)` the tiles `T` and `U(0, j0+1)` leave on the side σ the wedge `(α, γ)`. ... Let `T⁺` be the one beside `ℓ`.
   If `T⁺` lays `a` or `c` on `ℓ`, then (K1) holds with `j* = j0+1` (clamped from below by the edge of `T`), against `K(s', j0+1)`.  If `T⁺` lays `b`, it shows `α` ... and is the mirror image of `U(0, j0+1)`
   in `ℓ`, against `M(s', j0+1)`, of size `n − 1`"**: `col_next` at the column `0`, `clamp_tile` from `T`, `beside_core`).
3. The induction: `MGh_succ`, **`MG_all`** (`M(s', j0)` for every size `n ≥ 1`, every origin `x` with interior chords (`ChordsAt`), `ε = 1`), and **`corner_run_short`**: a run of `k` tiles `C1` from the corner `A'`
   with `1 ≤ k ≤ e` that ends at `Q'` or before a tile other than `B1`, `C1` is impossible (with `corner_run_mirror` and `MG_all`: the bound `k ≥ e + 1` of alternative (ii) of the theorem).

WHICH CONTEXT IS NEEDED.  `SetupG` (the setup: the model, the side, the angles) with `ε = 1`, and for each lattice origin `x` used the open chords `ChordsAt D e f 1 x` -- the Lean form of the standing
hypothesis of `K` that `ℓ` leaves Δ into its interior at `P = p(0,0)`.  For the origin `p(0,0)` of the final application this is `hch_cornerA` (the corner `2α` or `3α`); for the origins `p(n,0)` of the
induction it is `chordsAt_shift_K2` (they are open points of the side).  `CtxBase` alone is the context of size 1 (`MGn_one`); sizes `≥ 2` need `ChordsAt` because (K1) is derived, via `CtxJ.of_K1J`, from it.

WITNESSES.  As in `Draft/SideRunGMirror.lean`: the statements conclude `False` under the conditions (M1), (K2), (K3) of the paper; no real tiling is known to satisfy `MirrorAt` (see `Draft/SideRunGMirror.lean`).

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGMStepB

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

/-! ## 0. Tools -/

section tools

variable {e f : ℕ} {α β γ L ax ay x : ℝ} {s j0 : ℕ}

theorem lpG_col_mem (e f ε x c : ℝ) {a b d : ℝ} (h1 : a < b) (h2 : b < d) :
    lpG e f ε x c b ∈ openSegment ℝ (lpG e f ε x c a) (lpG e f ε x c d) := by
  have hd : 0 < d - a := by linarith
  have hab : (d - b) / (d - a) + (b - a) / (d - a) = 1 := by
    rw [← add_div, show d - b + (b - a) = d - a by ring]
    exact div_self hd.ne'
  refine ⟨(d - b) / (d - a), (b - a) / (d - a), div_pos (by linarith) hd, div_pos (by linarith) hd,
    hab, ?_⟩
  unfold lpG
  apply plane_ext <;>
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mkPt_zero, mkPt_one] <;>
    field_simp <;> ring

/-- **a sub-segment of an interior chord along `ℓ` is interior** -/
theorem col_sub_interior (hch : ChordsAt D (e : ℝ) (f : ℝ) 1 x) {j : ℕ} (hj : 1 ≤ j)
    (hmem : lpG (e : ℝ) (f : ℝ) 1 x 0 (j : ℝ) ∈ D.target.carrier) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b ≤ (j : ℝ)) :
    openSegment ℝ (lpG (e : ℝ) (f : ℝ) 1 x 0 a) (lpG (e : ℝ) (f : ℝ) 1 x 0 b)
      ⊆ interior D.target.carrier := by
  intro y hy
  rw [openSegment_eq_image_lineMap] at hy
  obtain ⟨τ, ⟨h0, h1⟩, rfl⟩ := hy
  rw [lineMap_lpG]
  have hη0 : 0 < a + τ * (b - a) := by nlinarith [mul_pos h0 (sub_pos.mpr hab)]
  have hηj : a + τ * (b - a) < (j : ℝ) := by nlinarith [mul_pos (sub_pos.mpr h1) (sub_pos.mpr hab)]
  have hξ : lpG (e : ℝ) (f : ℝ) 1 x (0 + τ * (0 - 0)) (a + τ * (b - a))
      = lpG (e : ℝ) (f : ℝ) 1 x 0 (a + τ * (b - a)) := lpG_congr (by ring) rfl
  rw [hξ]
  exact hch j hj hmem (lpG_col_mem (e : ℝ) (f : ℝ) 1 x 0 (a := 0) hη0 hηj)

/-- (K2) of the lattice with origin `p(r+1, 0)` at the level `j0 + 1`: the rows `≤ j0` are given, the row `j0 + 1` is `U(c, j0+1)`, `c ≥ r+1`, and `D(i, j0)`, `i ≥ r+1`, is step (a) -/
theorem k2_shift_row (W : StepCtx D e f α β γ L ax ay x s j0) {r : ℕ}
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
theorem k3_shift_row (W : StepCtx D e f α β γ L ax ay x s j0) {r : ℕ} (hr : r + 1 ≤ s) :
    K3G D (e : ℝ) (f : ℝ) 1 (shiftX (f : ℝ) 1 x (r + 1)) ((s - (r + 1) : ℕ) : ℝ) ((j0 + 1 : ℕ) : ℝ) := by
  have h3 : K3G D (e : ℝ) (f : ℝ) 1 x (((s - (r + 1)) + (r + 1) : ℕ) : ℝ) ((j0 + 1 : ℕ) : ℝ) := by
    rw [Nat.sub_add_cancel hr]
    exact W.hK3.mono (by push_cast; linarith)
  exact K3G_shift_nat (by norm_num) h3

/-- the tile `D(a, η)` lies on the σ side of `ℓ_{a+1}` -/
theorem D_left_le (S : SetupG D e f α β γ L ax ay) {a η : ℝ} {t : Fin N}
    (hDL : HasV D t (lpG (e : ℝ) (f : ℝ) 1 x (a + 1) η) (lpG (e : ℝ) (f : ℝ) 1 x a (η + 1))
      (lpG (e : ℝ) (f : ℝ) 1 x (a + 1) (η + 1))) :
    ∀ i, FXG (e : ℝ) (f : ℝ) 1 ((D.tile t).pts i) ≤ lvG (e : ℝ) (f : ℝ) 1 x (a + 1) := by
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  refine hDL.all (P := fun p => FXG (e : ℝ) (f : ℝ) 1 p ≤ lvG (e : ℝ) (f : ℝ) 1 x (a + 1))
    (le_of_eq (FXG_lp hε _ _)) ?_ (le_of_eq (FXG_lp hε _ _))
  dsimp only
  rw [FXG_lp hε]
  exact lvG_le S.e0 S.hef' (by linarith)

end tools

/-! ## 1. Step (b): the downward induction -/

section stepb

variable {e f : ℕ} {α β γ L ax ay x : ℝ} {s j0 : ℕ}

/-- the counting of (F) at an interior point: three tiles showing `α` and two showing `γ` do not occur -/
theorem fig_contra_a3g2 {p a b g : ℕ} (F : FigI p a b g) (ha : 3 ≤ a) (hg : 2 ≤ g) : False := by
  unfold FigI at F
  omega

/-- the counting of (F) at an interior point: a tile showing `α` and three tiles showing `γ` do not occur -/
theorem fig_contra_a1g3 {p a b g : ℕ} (F : FigI p a b g) (ha : 1 ≤ a) (hg : 3 ≤ g) : False := by
  unfold FigI at F
  omega

/-- **the tile `E` beside the `b`-edge of `U(a+1, η+1)` does not show `γ` at `p(a+1, η+1)`, if a tile `V` other than the lattice tiles shows `α` there** (paper: "the three tiles between show
`α, β, β` (F)"): the four lattice tiles at `p(a+1, η+1)` are `lower_half` (angles `α, γ, β, α`; interior point); with `V` there are three tiles showing `α` and, with `E`, two showing `γ`, against (F)
(`fig_int`). -/
theorem bad_gamma_free (S : SetupG D e f α β γ L ax ay) {a η : ℝ} {tDL tUl tDl tUr tV : Fin N}
    (hDL : HasV D tDL (lpG (e : ℝ) (f : ℝ) 1 x (a + 1) η) (lpG (e : ℝ) (f : ℝ) 1 x a (η + 1))
      (lpG (e : ℝ) (f : ℝ) 1 x (a + 1) (η + 1)))
    (hUl : HasV D tUl (lpG (e : ℝ) (f : ℝ) 1 x (a + 1) η) (lpG (e : ℝ) (f : ℝ) 1 x (a + 1 + 1) η)
      (lpG (e : ℝ) (f : ℝ) 1 x (a + 1) (η + 1)))
    (hDl : HasV D tDl (lpG (e : ℝ) (f : ℝ) 1 x (a + 1 + 1) η) (lpG (e : ℝ) (f : ℝ) 1 x (a + 1) (η + 1))
      (lpG (e : ℝ) (f : ℝ) 1 x (a + 1 + 1) (η + 1)))
    (hUr : HasV D tUr (lpG (e : ℝ) (f : ℝ) 1 x (a + 1) (η + 1))
      (lpG (e : ℝ) (f : ℝ) 1 x (a + 1 + 1) (η + 1)) (lpG (e : ℝ) (f : ℝ) 1 x (a + 1) (η + 1 + 1)))
    (hVα : (D.tile tV).localAngle (lpG (e : ℝ) (f : ℝ) 1 x (a + 1) (η + 1)) = α)
    (ntVDL : tV ≠ tDL) (ntVUr : tV ≠ tUr) :
    ∀ (iT : Fin N) (k' m' : Fin 3), k' ≠ m' →
      (D.tile iT).pts k' = lpG (e : ℝ) (f : ℝ) 1 x (a + 1) (η + 1) →
      (D.tile iT).pts m' = lpG (e : ℝ) (f : ℝ) 1 x (a + 1) (η + 1 + 1) →
      (∀ i, FXG (e : ℝ) (f : ℝ) 1 ((D.tile iT).pts i) ≤ lvG (e : ℝ) (f : ℝ) 1 x (a + 1)) →
      (D.tile iT).localAngle (lpG (e : ℝ) (f : ℝ) 1 x (a + 1) (η + 1)) ≠ γ := by
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have he0 := S.e0
  have hef := S.hef'
  obtain ⟨a1, a2, a3, a4, hintZ, n12, n13, n14, n23, n24, n34⟩ := lower_half S hε hDL hUl hDl hUr
  intro iT k' m' hk'm' hk' hm' hle' hγ
  obtain ⟨k2, hk2⟩ := hUl.idx₂
  have nIU : iT ≠ tUl := ne_of_F (FXG (e : ℝ) (f : ℝ) 1) hle' (i := k2)
    (by rw [hk2, FXG_lp hε]; exact lvG_lt he0 hef (by linarith))
  have hαs : ∀ i ∈ ({tV, tDL, tUr} : Finset (Fin N)),
      (D.tile i).localAngle (lpG (e : ℝ) (f : ℝ) 1 x (a + 1) (η + 1)) = α :=
    forall_mem3 (P := fun i => (D.tile i).localAngle
      (lpG (e : ℝ) (f : ℝ) 1 x (a + 1) (η + 1)) = α) hVα a1 a4
  have hγs : ∀ i ∈ ({tUl, iT} : Finset (Fin N)),
      (D.tile i).localAngle (lpG (e : ℝ) (f : ℝ) 1 x (a + 1) (η + 1)) = γ :=
    forall_mem2 (P := fun i => (D.tile i).localAngle
      (lpG (e : ℝ) (f : ℝ) 1 x (a + 1) (η + 1)) = γ) a2 hγ
  have c1 := card_le_angle _ α hαs
  have c2 := card_le_angle _ γ hγs
  rw [card3 ntVDL ntVUr n14] at c1
  rw [card2 nIU.symm] at c2
  obtain ⟨kd3, hkd3⟩ := hDL.idx₃
  exact fig_contra_a3g2 (fig_int S hintZ hkd3) c1 c2

/-- **the tile beside the `b`-edge of `U(a+1, η+1)`** (a lattice tile, with the lattice point `p(a, η+1)` in Δ): (K1) at the level `η + 1`, clamped from below by the `b`-edge of `D(a, η)`, or the whole `b`-edge
(`bedge_interior`, `clamp_tile`, `col_next`) -/
theorem bad_colnext (S : SetupG D e f α β γ L ax ay) {a η : ℝ} (hη : 0 ≤ η) {tDL tUr : Fin N}
    (hDL : HasV D tDL (lpG (e : ℝ) (f : ℝ) 1 x (a + 1) η) (lpG (e : ℝ) (f : ℝ) 1 x a (η + 1))
      (lpG (e : ℝ) (f : ℝ) 1 x (a + 1) (η + 1)))
    (hUr : HasV D tUr (lpG (e : ℝ) (f : ℝ) 1 x (a + 1) (η + 1))
      (lpG (e : ℝ) (f : ℝ) 1 x (a + 1 + 1) (η + 1)) (lpG (e : ℝ) (f : ℝ) 1 x (a + 1) (η + 1 + 1)))
    (hL : lpG (e : ℝ) (f : ℝ) 1 x a (η + 1) ∈ D.target.carrier) :
    ColNext D (e : ℝ) (f : ℝ) 1 x (a + 1) (η + 1) := by
  have C : CtxBase D e f α β γ L ax ay 1 x := ⟨S, Or.inl rfl⟩
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have hL' : lpG (e : ℝ) (f : ℝ) 1 x (a + 1 - 1) (η + 1) ∈ D.target.carrier := by
    rw [add_sub_cancel_right]; exact hL
  have hint := bedge_interior C (c := a + 1) (η := η + 1) (by linarith) hUr hL'
  have hDL' := hDL
  obtain ⟨k1, m1, j1, h12, h13, h23, p1, p2, p3⟩ := hDL'
  have hcl := clamp_tile S hε (c := a + 1) (η := η) h13 p1 p3 (D_left_le S hDL)
  exact col_next S hε hUr hint hcl

/-- **`V_r` is not a tile showing `α` at `p(r+1, j0+1)`, if `V_{r+1}, ..., V_{n−2}` are lattice tiles** (paper: "Let `r ≤ n − 3`, let `V_{r+1}, ..., V_{n−2}` be lattice tiles, and suppose that `V_r`
shows `α` at `p(r+1, j0+1)`.  Above `Λ` at that point `V_r` takes `(π − α, π)` and `U(r+1, j0+1)` takes `(0, α)`; the three tiles between show `α, β, β` (F).  Let `E` be the one beside the `b`-edge of
`U(r+1, j0+1)`. ..."; here `n = q + 1`).  `bad_gamma_free` is the counting at `p(r+1, j0+1)` (the paper's "`α, β, β`": the tile `E` does not show `γ`); `bad_colnext` is "`E` lays `a` or `c` (K1) / the whole
`b`-edge", the clamp of `p(r+1, j0+1)` from below being the `b`-edge of `D(r, j0)`; `beside_core` is the two-line argument "against `K(s' − r − 1, j0 + 1)` / `M(s' − r − 1, j0 + 1)`, of size `n − r − 2 < n`" at the
lattice with origin `p(r+1, 0)` (`k2_shift_row`, `k3_shift_row`, `chordsAt_shift_K2`).  (Conclusion `False`.) -/
theorem bad_mid_false (W : StepCtx D e f α β γ L ax ay x s j0) {q : ℕ} (hq : q + j0 + 1 = s) (hq1 : 1 ≤ q)
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
    (k2_shift_row W (fun c h1 h2 => hU c h1 (by omega))) (k3_shift_row W (by omega))
    (by omega) (by omega) (W.IH _ (by omega) (by omega)) rfl (by omega) hE hnγ

/-- **STEP (b): `U(r, j0+1)` is a tile for `0 ≤ r ≤ n − 2`** (`n = q + 1 = s − j0`; paper: "So `V_r` shows `β` at `p(r+1, j0+1)`: `V_r = U(r, j0+1)`"; the downward induction from `r = n − 2`,
which is `right_end_false`, to `r = 0`).  The tiles `V_r` are those of `row_tiles`. -/
theorem stepB (W : StepCtx D e f α β γ L ax ay x s j0) {q : ℕ} (hq : q + j0 + 1 = s) (hq1 : 1 ≤ q) :
    ∀ r : ℕ, r + 1 ≤ q → UTG D (e : ℝ) (f : ℝ) 1 x (r : ℝ) ((j0 : ℝ) + 1) := by
  have key : ∀ d r : ℕ, r + 1 + d = q → UTG D (e : ℝ) (f : ℝ) 1 x (r : ℝ) ((j0 : ℝ) + 1) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro r hrd
      rcases row_tiles W hq hq1 r (by omega) with hU | hbad
      · exact hU
      · exfalso
        rcases Nat.eq_zero_or_pos d with hd0 | hdpos
        · subst hd0
          obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
          have hrq : r = q' := by omega
          subst hrq
          exact right_end_false W hq hbad
        · exact bad_mid_false W hq hq1 (r := r) (by omega)
            (fun c hc1 hc2 => ih (q - 1 - c) (by omega) c (by omega)) hbad
  intro r hr
  exact key (q - 1 - r) r (by omega)

end stepb

/-! ## 2. Step (c) -/

section stepc

variable {e f : ℕ} {α β γ L ax ay x : ℝ} {s j0 : ℕ}

/-- **"Now (K2) holds for `(s', j0+1)`"**: the row `j0 + 1` is `U(r, j0+1)`, `r ≤ n − 2` (step (b)); the tiles `D(i, j0)` are step (a) -/
theorem k2_next (W : StepCtx D e f α β γ L ax ay x s j0) {q : ℕ} (hq : q + j0 + 1 = s)
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
theorem stepC (W : StepCtx D e f α β γ L ax ay x s j0) {q : ℕ} (hq : q + j0 + 1 = s) (hq1 : 1 ≤ q)
    (hU : ∀ r : ℕ, r + 1 ≤ q → UTG D (e : ℝ) (f : ℝ) 1 x (r : ℝ) ((j0 : ℝ) + 1)) : False := by
  have S := W.S
  have C : CtxBase D e f α β γ L ax ay 1 x := ⟨S, Or.inl rfl⟩
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have he0 := S.e0
  have hef := S.hef'
  have hne := W.hne
  have hsf := W.hsf
  have hK2n := k2_next W hq hU
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

end stepc

/-! ## 3. The induction, `MG_all`, and the corollary at the corner -/

section induction

variable {e f : ℕ} {α β γ L ax ay x : ℝ}

/-- **the induction step**: `M` of size `n ≥ 2` from `M` of the smaller sizes (steps (a), (b), (c)) -/
theorem MGh_succ (S : SetupG D e f α β γ L ax ay) (n : ℕ) (hn : 2 ≤ n)
    (IH : ∀ m, 1 ≤ m → m < n → MGh D e f 1 m) : MGh D e f 1 n := by
  intro x s j0 hch hsz hjs hsf hne hM hK2 hK3
  have IH' : ∀ m, 1 ≤ m → m < s - j0 → MGh D e f 1 m := fun m h1 h2 => IH m h1 (by omega)
  have hA := stepA S hch hM hK2 hK3 hsf hne IH'
  have W : StepCtx D e f α β γ L ax ay x s j0 :=
    ⟨S, hch, hM, hK2, hK3, hsf, hne, by omega, IH', hA⟩
  have hq : (s - j0 - 1) + j0 + 1 = s := by omega
  exact stepC W hq (by omega) (stepB W hq (by omega))

/-- **`MG_all`: THE STATEMENT `M(s', j0)` OF THE PAPER, for every size `n ≥ 1`** (`0 ≤ j0 < s' ≤ f − 1`, `s' − j0 = n ≤ e`): for every lattice origin `x` whose chords along `ℓ` are interior
(`ChordsAt`), the conditions (M1) `MirrorAt`, (K2) `K2G`, (K3) `K3G` cannot hold together.  Context: `SetupG`, `ε = 1`. -/
theorem MG_all (S : SetupG D e f α β γ L ax ay) : ∀ n : ℕ, 1 ≤ n → MGh D e f 1 n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      exact MGh_one S (Or.inl rfl)
    · exact MGh_succ S n h (fun m h1 h2 => ih m h2 h1)

/-- the same for all origins at once, when every origin has interior chords -/
theorem MGn_all_of_chords (S : SetupG D e f α β γ L ax ay)
    (hch : ∀ x : ℝ, ChordsAt D (e : ℝ) (f : ℝ) 1 x) : ∀ n : ℕ, 1 ≤ n → MGn D e f 1 n :=
  fun n hn x s j0 hsz => MG_all S n hn x s j0 (hch x) hsz

variable {m : ℕ} {X : ℕ → ℝ} {tile : ℕ → Fin N} {τ : ℕ → Ty}

/-- **A RUN OF `C1` FROM THE CORNER `A'` OF LENGTH `k ≤ e` IS IMPOSSIBLE** (the bound `k ≥ e + 1` of alternative (ii) of `thm:cornerrun`): a run of `k` tiles `C1` from `A'`, `1 ≤ k ≤ e`, that ends
at the right corner `Q'` or before a tile other than `B1`, `C1`.  `corner_run_mirror` gives the mirror tile `MirrorAt D e f 1 0 0` (the case (K1) is `False` by `CtxJ.run_diesJ`); the conditions (K2) (row `0`
of `Δ_k`: the `k` tiles `C1`) and (K3) (`K3G_run_end`) are those of the run; `MG_all` of size `k ≤ e` says that they cannot hold together with the mirror tile. -/
theorem corner_run_short (S : SetupG D e f α β γ L ax ay) (Co : CornersA e f L ax ay)
    (Ch : ChainG D e f L m X tile τ) {k : ℕ} (hk1 : 1 ≤ k) (hke : k ≤ e)
    (hrun : ∀ j, j < k → τ j = Ty.C1)
    (hsucc : k = m ∨ (k < m ∧ τ k ≠ Ty.B1 ∧ τ k ≠ Ty.C1)) : False := by
  have hkf : k < f := lt_of_le_of_lt hke S.hef
  have hkm : k ≤ m := by rcases hsucc with h | ⟨h, -, -⟩ <;> omega
  have hM := corner_run_mirror S Co Ch hk1 hkf hrun hsucc
  have hpos := run_positions S Ch hkm hrun
  have hUT : ∀ i : ℕ, i < k → UTG D (e : ℝ) (f : ℝ) 1 0 (i : ℝ) 0 := by
    intro i hi
    have h := Ch.htile i (by omega)
    rw [hrun i hi] at h
    exact ⟨tile i, S.c1_lpG (x := 0) (ξ := (i : ℝ)) h (by rw [hpos i hi.le]; ring)⟩
  have hP : mkPt 0 0 ∈ D.target.carrier := by
    have := Ch.mem (k := 0) Ch.hm0
    rwa [Ch.hX0] at this
  have hch := hch_cornerA S Co hP
  have hK3 := K3G_run_end S Co Ch hk1 hkm hrun hsucc
  refine MG_all S k hk1 0 k 0 hch (by omega) (by omega) hkf (by omega) ?_ ?_ ?_
  · rw [Nat.cast_zero]; exact hM
  · refine ⟨fun i j hj hij => ?_, fun i j hj _ => absurd hj (Nat.not_lt_zero _)⟩
    obtain rfl : j = 0 := by omega
    rw [Nat.cast_zero]
    exact hUT i (by omega)
  · rw [Nat.cast_zero]; exact hK3

end induction

end Erdos634.Draft.SideRunGA

#print axioms Erdos634.Draft.SideRunGA.lpG_col_mem
#print axioms Erdos634.Draft.SideRunGA.col_sub_interior
#print axioms Erdos634.Draft.SideRunGA.k2_shift_row
#print axioms Erdos634.Draft.SideRunGA.k3_shift_row
#print axioms Erdos634.Draft.SideRunGA.D_left_le
#print axioms Erdos634.Draft.SideRunGA.fig_contra_a3g2
#print axioms Erdos634.Draft.SideRunGA.fig_contra_a1g3
#print axioms Erdos634.Draft.SideRunGA.bad_gamma_free
#print axioms Erdos634.Draft.SideRunGA.bad_colnext
#print axioms Erdos634.Draft.SideRunGA.bad_mid_false
#print axioms Erdos634.Draft.SideRunGA.stepB
#print axioms Erdos634.Draft.SideRunGA.k2_next
#print axioms Erdos634.Draft.SideRunGA.stepC
#print axioms Erdos634.Draft.SideRunGA.MGh_succ
#print axioms Erdos634.Draft.SideRunGA.MG_all
#print axioms Erdos634.Draft.SideRunGA.MGn_all_of_chords
#print axioms Erdos634.Draft.SideRunGA.corner_run_short
