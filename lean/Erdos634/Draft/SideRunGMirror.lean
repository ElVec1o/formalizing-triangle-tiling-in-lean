/-
Draft/SideRunGMirror.lean -- written 14 October 2026.  UNAUDITED.  In `AllThreshold`.  Module M1 of the plan for
`thm:cornerrun` (see the header of `Draft/SideRunGJChord.lean`; C1, C2 are `Draft/SideRunGCornerA.lean`, `Draft/SideRunGCornerRun.lean`).

**The mirror tile `T`, the shifted lattice, the statement `MG(s', j0)` and its size 1.**  Paper: Theorem `thm:cornerrun`, "Statement
`M(s', j0)`" and the proof of its size `n = 1`; (private working notes, not included) Section 4.

CONTENTS.
1. THE SHIFT (`shiftX f ε x n = x + ε n f²`, the origin `p(n, 0)` of the lattice of origin `x`).  `lpG_shift`
   (`lpG (shiftX n) ξ η = lpG ξ+n η`), `lvG_shift` (`lvG (shiftX n) s = lvG (s + n)`, needs `ε² = 1`), `UTG_shift`, `DTG_shift`,
   `K2G_shift` (`K2G x (s + n) j0 → K2G (shiftX n) s j0`: the (K2) of the shifted lattice is part of the given one), `ClampedBelowG_shift`,
   `RhoEdgeG_shift`, `K3G_shift` (`K3G (shiftX n) (s − n) j0 ↔ K3G x s j0`: (K3) is the same data, re-indexed), `K1J_shift` ((K1) at the
   shifted origin in the OLD coordinates: a tile of the side σ of `ℓ_n = ℓ + n u` with an edge from `p(n, js)` of length `a` or `c`),
   `shift_open_point` (`p(n, 0)` is an open point of the side when `p(n+1, 0)` lies in Δ), `ctxJ_shift` (**the context `CtxJ` at the
   shifted origin**: `CtxJ.of_K1J` with the chords of `SetupG.hch_pos`) and `K_at_shift` (**the paper's call "against `K(s − n, j0)`"**).
   Checks at the shift `0`: `shift_check_zero`, `K2G_shift_zero`, `ctxJ_shift_zero`.
   WHERE (K1) AT THE ROW `j*` OF THE SHIFTED LATTICE COMES FROM.  In step (a) of the paper it is the tile `E` beside the `b`-edge of
   `U(i+1, j0)` that "lays `c`" on `ℓ_{i+1}` from `p(i+1, j0)`: `E` lies on the side σ of `ℓ_{i+1}`, has the vertices `p(i+1, j0)` and
   `p(i+1, j0 + t)` with `t b ∈ {a, c}`.  That is exactly `K1J D e f ε (shiftX f ε x (i+1)) j0` (`K1J_shift` reads it in the old
   coordinates).  The clamp of the paper's (K1) is not part of `K1J`: the chord `chordJ` starts at the point `p(i+1, 0)` of the side,
   which is an open point (`shift_open_point`), and `clamp_out` clamps it.  So the data the paper gives at the shifted origin are: the
   tile `E` (-> `K1J`), the open point of the side (-> `hch`, `hP`), and `K2G`, `K3G` (-> `K2G_shift`, `K3G_shift`).
2. TWO GENERAL TOOLS on a tile with three named vertices: `hasV_bary` (positive barycentric combinations are interior points),
   `hasV_push` (the cone of the two edge vectors at a vertex: `A + ε'(θ1 (B − A) + θ2 (C − A))` is interior for small `ε'`).
3. THE MIRROR TILE `T` of `MirrorAt` (`Draft/SideRunGCornerRun.lean`).  Notation: `P = p(0, j0)`, `Q = p(0, j0+1)`, `M = p(−1, j0 + K/b)`,
   `K = 2f² − e²`, `b = f² − e²`, `mirK = K/b`.  Proved:
   * `mirK_mul`, `mirK_gt_two` (`K/b > 2`, because `K − 2b = e²`), `mirK_not_int` (**`K/b` is not an integer for coprime `1 ≤ e < f`**: `K/b = 1 + f²/b`,
     `b ∣ f²` and `b ∣ e²` force `b = 1`, impossible), `mirror_vertex_not_lattice` (**the vertex `M` of `T` is no point `p(ξ', m)` with integer `m`**:
     `lpG_eta_eq` and `mirK_not_int`).
   * `mirror_dists`: `|PQ| = b`, `|MP| = c = f²`, `|MQ| = a = ef` (the sides of `T`).
   * `mirror_angles`: `T` shows `α` at `P`, `γ` at `Q`, `β` at `M`.
   * `mirror_side`: `T` lies on the side σ of `ℓ` (`FXG ≤ lv` on its three vertices; strictly at `M`).
   * `mirror_ray_up`, `mirror_ray_M`: the edge vectors at `Q`: `P − Q = −(ε (f² − uu), hh)` (the ray `ℓ` downwards, direction `e(π + α)`
     for `ε = 1`) and `M − Q = (−ε e²/2, e √(4f²−e²)/2)` (`= a · (ε cos γ, sin γ)`, direction `e(γ)`).  With `mirror_push_Q`
     (the cone of these two vectors at `Q` is covered by `T`: **`T` covers `(γ, π + α)` at `Q = p(0, j0+1)`**) and `mirror_push_P` (the cone at `P`:
     `(α, 2α)`; at the corner `A'` of angle `2α` the tiles `X₀` and `T` fill it).
   * `mirror_row_left`: **the points `p(−δ, j0+1)`, `0 < δ`, `δ K/b < 1` are interior to `T`** (the paper's "the direction `d(π)` is interior
     to `T`", used to clamp the left end of the row `Λ` in step (b)); the weights are `δ f²/b`, `1 − δ K/b`, `δ`.
4. THE STATEMENT `MG D e f ε x s j0` (the paper's `M(s', j0)` for the lattice of origin `x`, stated in the form `¬ (M1 ∧ K2 ∧ K3)` with its
   range `0 ≤ j0 < s' ≤ f−1`, `s' − j0 ≤ e`), `MGn` (all origins and all pairs of size `n`), and its SIZE 1: `psi_or_out` (the `m`-chord principle:
   ρ_s is outside Δ or a tile ψ has `p(s − J, J)` in the relative interior of an edge), `overlap_contra` (T covers a direction pointing into
   ρ_s at `Q`, ψ covers all of them, the angles differ: a contradiction), `MG_size_one` (context `CtxBase` only: **no (K1) is needed**), `MGn_one`.

WHAT IS NOT HERE.  The induction (sizes `n ≥ 2`, steps (a), (b), (c)): modules M2, M3.  `M°(e+1)`: M4.  The words on `s`: R1, R2.

WITNESSES.  `MG` is a contradiction statement (`MirrorAt`, `K2G`, `K3G` cannot hold together); its hypotheses are the configuration to be
refuted.  The facts about `T` (`mirror_*`) have as hypothesis a tile with the three vertices of `MirrorAt`.  NO real tiling is known that
satisfies `MirrorAt` at a corner `2α` (or `3α`): the paper (`rem:siderunall`, "Checks") records that alternative (ii) of `thm:cornerrun` does not
occur in 34 side readings of the first session and in 78 side readings of 41 tilings (31 with `e ≥ 2`) of the second, and that in the exact
enumerations every root of `M(k, 0)` with `P` a corner `2α` is dead at every size tested; the seed tilings of `W_f(e, f)` were NOT read here.  So
these hypotheses have no real witness; they are satisfiable as a configuration of the plane (the three points exist, with the three distances), not
as part of a tiling.  The shift lemmas are identities / equivalences and need no such hypothesis.  `ctxJ_shift` and `K_at_shift` take `K1J` at the
shifted origin; `CtxJ` is satisfied by every `CtxG` at `js = 0` (`CtxJ.of_ctxG`).

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGCornerRun

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

/-! ## 1. The shifted lattice -/

/-- the origin `p(n, 0)` of the lattice of origin `x` (`n` steps `ε c` along the side), `c = f²` -/
noncomputable def shiftX (f ε x : ℝ) (n : ℕ) : ℝ := x + ε * (n : ℝ) * f ^ 2

theorem shiftX_zero (f ε x : ℝ) : shiftX f ε x 0 = x := by
  unfold shiftX; rw [Nat.cast_zero]; ring

theorem shiftX_add (f ε x : ℝ) (n m : ℕ) :
    shiftX f ε (shiftX f ε x n) m = shiftX f ε x (n + m) := by
  unfold shiftX; push_cast; ring

/-- **the lattice with origin `p(n, 0)` is the same lattice re-indexed**: `p'(ξ, η) = p(ξ + n, η)` -/
theorem lpG_shift (e f ε x : ℝ) (n : ℕ) (ξ η : ℝ) :
    lpG e f ε (shiftX f ε x n) ξ η = lpG e f ε x (ξ + n) η := by
  unfold lpG shiftX
  exact mkPt_congr (by ring) rfl

/-- the level of the line `m_{s'}` of the shifted lattice is the level of `m_{s' + n}` of the old one -/
theorem lvG_shift {e f ε : ℝ} (hε : ε ^ 2 = 1) (x : ℝ) (n : ℕ) (s : ℝ) :
    lvG e f ε (shiftX f ε x n) s = lvG e f ε x (s + n) := by
  unfold lvG shiftX
  linear_combination (hhG e f * (n : ℝ) * f ^ 2) * hε

theorem UTG_shift (e f ε x : ℝ) (n : ℕ) (ξ η : ℝ) :
    UTG D e f ε (shiftX f ε x n) ξ η ↔ UTG D e f ε x (ξ + n) η := by
  have h1 : lpG e f ε (shiftX f ε x n) (ξ + 1) η = lpG e f ε x (ξ + n + 1) η := by
    rw [lpG_shift]; exact lpG_congr (by ring) rfl
  constructor
  · rintro ⟨t, h⟩
    exact ⟨t, h.congr (lpG_shift e f ε x n ξ η) h1 (lpG_shift e f ε x n ξ (η + 1))⟩
  · rintro ⟨t, h⟩
    exact ⟨t, h.congr (lpG_shift e f ε x n ξ η).symm h1.symm
      (lpG_shift e f ε x n ξ (η + 1)).symm⟩

theorem DTG_shift (e f ε x : ℝ) (n : ℕ) (ξ η : ℝ) :
    DTG D e f ε (shiftX f ε x n) ξ η ↔ DTG D e f ε x (ξ + n) η := by
  have h1 : lpG e f ε (shiftX f ε x n) (ξ + 1) η = lpG e f ε x (ξ + n + 1) η := by
    rw [lpG_shift]; exact lpG_congr (by ring) rfl
  have h3 : lpG e f ε (shiftX f ε x n) (ξ + 1) (η + 1) = lpG e f ε x (ξ + n + 1) (η + 1) := by
    rw [lpG_shift]; exact lpG_congr (by ring) rfl
  constructor
  · rintro ⟨t, h⟩
    exact ⟨t, h.congr h1 (lpG_shift e f ε x n ξ (η + 1)) h3⟩
  · rintro ⟨t, h⟩
    exact ⟨t, h.congr h1.symm (lpG_shift e f ε x n ξ (η + 1)).symm h3.symm⟩

/-- **(K2) of the shifted lattice is part of (K2) of the given one** -/
theorem K2G_shift {e f ε x : ℝ} {s j0 n : ℕ} (h : K2G D e f ε x (s + n) j0) :
    K2G D e f ε (shiftX f ε x n) s j0 := by
  refine ⟨fun i j hj hij => ?_, fun i j hj hij => ?_⟩
  · rw [UTG_shift]
    have h' := h.1 (i + n) j hj (by omega)
    rwa [Nat.cast_add] at h'
  · rw [DTG_shift]
    have h' := h.2 (i + n) j hj (by omega)
    rwa [Nat.cast_add] at h'

theorem ClampedBelowG_shift {e f ε : ℝ} (hε : ε ^ 2 = 1) (x : ℝ) (n : ℕ) (s η₁ : ℝ) :
    ClampedBelowG D e f ε (shiftX f ε x n) (s - n) η₁ ↔ ClampedBelowG D e f ε x s η₁ := by
  have hP : ∀ η : ℝ, lpG e f ε (shiftX f ε x n) (s - n - η) η = lpG e f ε x (s - η) η := fun η => by
    rw [lpG_shift]; exact lpG_congr (by ring) rfl
  have hL : lvG e f ε (shiftX f ε x n) (s - n) = lvG e f ε x s := by
    rw [lvG_shift hε]; congr 1; ring
  unfold ClampedBelowG
  simp only [hP, hL]

theorem RhoEdgeG_shift {e f ε : ℝ} (hε : ε ^ 2 = 1) (x : ℝ) (n : ℕ) (w : Fin N) (s j0 : ℝ) :
    RhoEdgeG D e f ε (shiftX f ε x n) w (s - n) j0 ↔ RhoEdgeG D e f ε x w s j0 := by
  have hP : ∀ η : ℝ, lpG e f ε (shiftX f ε x n) (s - n - η) η = lpG e f ε x (s - η) η := fun η => by
    rw [lpG_shift]; exact lpG_congr (by ring) rfl
  have hL : lvG e f ε (shiftX f ε x n) (s - n) = lvG e f ε x s := by
    rw [lvG_shift hε]; congr 1; ring
  unfold RhoEdgeG
  simp only [hP, hL, ClampedBelowG_shift hε]

/-- **(K3) is the same data in the shifted lattice**: the first form is the same inequality, the second has the same tile `w`, with
the vertices re-indexed -/
theorem K3G_shift {e f ε : ℝ} (hε : ε ^ 2 = 1) (x : ℝ) (n : ℕ) (s j0 : ℝ) :
    K3G D e f ε (shiftX f ε x n) (s - n) j0 ↔ K3G D e f ε x s j0 := by
  have hL : lvG e f ε (shiftX f ε x n) (s - n) = lvG e f ε x s := by
    rw [lvG_shift hε]; congr 1; ring
  unfold K3G
  simp only [hL, RhoEdgeG_shift hε]

/-- **(K1) at the shifted origin, in the old coordinates**: a tile of the side σ of `ℓ_n = ℓ + n u` (all its vertices have `FXG ≤ lv n`) has
an edge on `ℓ_n` from `p(n, js)` upward of length `a` or `c` -/
theorem K1J_shift {e f ε : ℝ} (hε : ε ^ 2 = 1) (x : ℝ) (n js : ℕ) :
    K1J D e f ε (shiftX f ε x n) js ↔
    ∃ (iT : Fin N) (k m : Fin 3) (t : ℝ), k ≠ m ∧ (D.tile iT).pts k = lpG e f ε x (n : ℝ) (js : ℝ) ∧
      (D.tile iT).pts m = lpG e f ε x (n : ℝ) ((js : ℝ) + t) ∧ 0 < t ∧
      (t * (f ^ 2 - e ^ 2) = e * f ∨ t * (f ^ 2 - e ^ 2) = f ^ 2) ∧
      ∀ i, FXG e f ε ((D.tile iT).pts i) ≤ lvG e f ε x (n : ℝ) := by
  unfold K1J
  simp only [lpG_shift, lvG_shift hε, zero_add]

/-- the points `p(n, 0)`, `n ≥ 1`, of the lattice (`ε = 1`) of origin `x` are open points of the side when `p(0,0)` and `p(n+1, 0)` lie in Δ -/
theorem shift_open_point {e f : ℕ} {α β γ L ax ay : ℝ} (S : SetupG D e f α β γ L ax ay) {x : ℝ} {n : ℕ}
    (hn : 1 ≤ n) (h0 : mkPt x 0 ∈ D.target.carrier)
    (h1 : mkPt (x + ((n : ℝ) + 1) * (f : ℝ) ^ 2) 0 ∈ D.target.carrier) :
    0 < shiftX (f : ℝ) 1 x n ∧ shiftX (f : ℝ) 1 x n < L := by
  have hm0 := (S.mem h0).2.1
  have hm1 := (S.mem h1).2.2
  rw [gA_mk] at hm0
  rw [gB_mk] at hm1
  have hc := S.c_pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : 0 ≤ x := by
    by_contra hneg
    push_neg at hneg
    nlinarith [mul_pos S.hay (neg_pos.mpr hneg)]
  have hX : x + ((n : ℝ) + 1) * (f : ℝ) ^ 2 ≤ L := by
    by_contra hneg
    push_neg at hneg
    nlinarith [mul_pos S.hay (sub_pos.mpr hneg)]
  have hnf : 0 < (n : ℝ) * (f : ℝ) ^ 2 := mul_pos (by linarith) hc
  unfold shiftX
  constructor <;> nlinarith

/-- **THE CONTEXT AT THE SHIFTED ORIGIN**: the shifted origin is an open point of the side (`hx0`, `hxL`, `hP`: `SetupG.hch_pos` gives the chords), and
(K1) holds there at the row `js` (`K1J`: the tile `E` of the paper's step (a), (b)) -/
theorem ctxJ_shift {e f : ℕ} {α β γ L ax ay ε : ℝ} (S : SetupG D e f α β γ L ax ay) (hε : ε = 1 ∨ ε = -1)
    {x : ℝ} {n js : ℕ} (hx0 : 0 < shiftX (f : ℝ) ε x n) (hxL : shiftX (f : ℝ) ε x n < L)
    (hP : mkPt (shiftX (f : ℝ) ε x n) 0 ∈ D.target.carrier)
    (hK1 : K1J D (e : ℝ) (f : ℝ) ε (shiftX (f : ℝ) ε x n) js) :
    CtxJ D e f α β γ L ax ay ε (shiftX (f : ℝ) ε x n) js :=
  CtxJ.of_K1J S hε (S.hch_pos hx0 hxL hP) hK1

/-- **THE PAPER'S CALL "against `K(s − n, j0)`" at the shifted origin**: (K1) at the row `js ≤ j0` of the lattice with origin `p(n, 0)`, and (K2),
(K3) of the given lattice with first index `s + n`, are contradictory (`s < f`, `j0 < s`).  (The call of step (a) with `n = i + 1`, `js = j0`.) -/
theorem K_at_shift {e f : ℕ} {α β γ L ax ay ε : ℝ} (S : SetupG D e f α β γ L ax ay) (hε : ε = 1 ∨ ε = -1)
    {x : ℝ} {n s j0 js : ℕ} (hx0 : 0 < shiftX (f : ℝ) ε x n) (hxL : shiftX (f : ℝ) ε x n < L)
    (hP : mkPt (shiftX (f : ℝ) ε x n) 0 ∈ D.target.carrier)
    (hK1 : K1J D (e : ℝ) (f : ℝ) ε (shiftX (f : ℝ) ε x n) js)
    (hjs : js ≤ j0) (hj0 : j0 < s) (hsf : s < f)
    (hK2 : K2G D (e : ℝ) (f : ℝ) ε x (s + n) j0)
    (hK3 : K3G D (e : ℝ) (f : ℝ) ε x ((s + n : ℕ) : ℝ) (j0 : ℝ)) : False := by
  have he2 : ε ^ 2 = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have Cj := ctxJ_shift S hε hx0 hxL hP hK1
  have hK3' : K3G D (e : ℝ) (f : ℝ) ε (shiftX (f : ℝ) ε x n) (s : ℝ) (j0 : ℝ) := by
    have h := (K3G_shift (D := D) he2 x n ((s + n : ℕ) : ℝ) (j0 : ℝ)).mpr hK3
    rwa [show ((s + n : ℕ) : ℝ) - n = s by push_cast; ring] at h
  exact Cj.K_allGJ (s - j0) (by omega) s j0 hjs hj0 hsf rfl (K2G_shift hK2) hK3'

/-! ### Checks at the shift `0`: every shift lemma is the identity -/

/-- **CHECK**: at the shift `0` the shift lemmas read `lpG`, `lvG`, `UTG`, `DTG`, `K3G` of the same lattice -/
theorem shift_check_zero {e f ε : ℝ} (hε : ε ^ 2 = 1) (x ξ η s j0 : ℝ) :
    shiftX f ε x 0 = x ∧
    lpG e f ε (shiftX f ε x 0) ξ η = lpG e f ε x ξ η ∧
    lvG e f ε (shiftX f ε x 0) s = lvG e f ε x s ∧
    (UTG D e f ε (shiftX f ε x 0) ξ η ↔ UTG D e f ε x ξ η) ∧
    (DTG D e f ε (shiftX f ε x 0) ξ η ↔ DTG D e f ε x ξ η) ∧
    (K3G D e f ε (shiftX f ε x 0) (s - ((0 : ℕ) : ℝ)) j0 ↔ K3G D e f ε x s j0) ∧
    (ClampedBelowG D e f ε (shiftX f ε x 0) (s - ((0 : ℕ) : ℝ)) η ↔ ClampedBelowG D e f ε x s η) := by
  refine ⟨shiftX_zero f ε x, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [lpG_shift, Nat.cast_zero, add_zero]
  · rw [lvG_shift hε, Nat.cast_zero, add_zero]
  · rw [UTG_shift, Nat.cast_zero, add_zero]
  · rw [DTG_shift, Nat.cast_zero, add_zero]
  · rw [shiftX_zero, Nat.cast_zero, sub_zero]
  · rw [shiftX_zero, Nat.cast_zero, sub_zero]

theorem K2G_shift_zero {e f ε x : ℝ} {s j0 : ℕ} (h : K2G D e f ε x s j0) : K2G D e f ε x s j0 := by
  have h' := K2G_shift (D := D) (n := 0) (s := s) (by simpa using h)
  rwa [shiftX_zero] at h'

/-- **CHECK**: `ctxJ_shift` at the shift `0` is `CtxJ.of_K1J` with the chords of `hch_pos` -/
theorem ctxJ_shift_zero {e f : ℕ} {α β γ L ax ay ε : ℝ} (S : SetupG D e f α β γ L ax ay) (hε : ε = 1 ∨ ε = -1)
    {x : ℝ} {js : ℕ} (hx0 : 0 < x) (hxL : x < L) (hP : mkPt x 0 ∈ D.target.carrier)
    (hK1 : K1J D (e : ℝ) (f : ℝ) ε x js) : CtxJ D e f α β γ L ax ay ε x js := by
  have h := ctxJ_shift S hε (n := 0) (x := x) (js := js) (by rwa [shiftX_zero]) (by rwa [shiftX_zero])
    (by rwa [shiftX_zero]) (by rwa [shiftX_zero])
  rwa [shiftX_zero] at h

/-! ## 2. Tiles with three named vertices -/

/-- **a positive barycentric combination of the three vertices of a tile is an interior point** -/
theorem hasV_bary {t : Fin N} {A B C : Plane} (h : HasV D t A B C) {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (habc : a + b + c = 1) : a • A + b • B + c • C ∈ interior (D.tile t).carrier := by
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := h
  have h' := abc_interior (D.tile t) hkm hkj hmj ha hb hc habc
  rwa [hk, hm, hj] at h'

/-- **the cone of the two edge vectors at a vertex**: `A + ε' (θ1 (B − A) + θ2 (C − A))` is interior to the tile for small `ε' > 0` -/
theorem hasV_push {t : Fin N} {A B C : Plane} (h : HasV D t A B C) {θ1 θ2 : ℝ} (h1 : 0 < θ1) (h2 : 0 < θ2) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε' : ℝ, 0 < ε' → ε' < ε₀ →
      A + ε' • (θ1 • (B - A) + θ2 • (C - A)) ∈ interior (D.tile t).carrier := by
  have hp : 0 < θ1 + θ2 := by linarith
  refine ⟨1 / (θ1 + θ2), one_div_pos.mpr hp, fun ε' hε'0 hε'1 => ?_⟩
  have hsum : ε' * (θ1 + θ2) < 1 := by
    calc ε' * (θ1 + θ2) < 1 / (θ1 + θ2) * (θ1 + θ2) := mul_lt_mul_of_pos_right hε'1 hp
      _ = 1 := one_div_mul_cancel hp.ne'
  have e' : A + ε' • (θ1 • (B - A) + θ2 • (C - A))
      = (1 - ε' * θ1 - ε' * θ2) • A + (ε' * θ1) • B + (ε' * θ2) • C := by
    apply plane_ext <;>
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] <;> ring
  rw [e']
  exact hasV_bary h (by nlinarith [hsum]) (mul_pos hε'0 h1) (mul_pos hε'0 h2) (by ring)

/-- the cone at `Q` of a tile `(P, Q, M)`: `T` covers `(γ, π + α)` at `Q = p(0, j0+1)` -/
theorem mirror_push_Q {t : Fin N} {P Q M : Plane} (h : HasV D t P Q M) {θ1 θ2 : ℝ} (h1 : 0 < θ1) (h2 : 0 < θ2) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε' : ℝ, 0 < ε' → ε' < ε₀ →
      Q + ε' • (θ1 • (M - Q) + θ2 • (P - Q)) ∈ interior (D.tile t).carrier :=
  hasV_push h.rot h1 h2

/-- the cone at `P` of a tile `(P, Q, M)`: `T` covers `(α, 2α)` at `P = p(0, j0)` -/
theorem mirror_push_P {t : Fin N} {P Q M : Plane} (h : HasV D t P Q M) {θ1 θ2 : ℝ} (h1 : 0 < θ1) (h2 : 0 < θ2) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε' : ℝ, 0 < ε' → ε' < ε₀ →
      P + ε' • (θ1 • (Q - P) + θ2 • (M - P)) ∈ interior (D.tile t).carrier :=
  hasV_push h h1 h2

/-! ## 3. The mirror tile -/

/-- the constant `K/b = (2f² − e²)/(f² − e²)` of the third vertex of the mirror tile -/
noncomputable def mirK (e f : ℝ) : ℝ := (2 * f ^ 2 - e ^ 2) / (f ^ 2 - e ^ 2)

theorem MirrorAt_iff (e f ε x j₀ : ℝ) :
    MirrorAt D e f ε x j₀ ↔ ∃ t : Fin N, HasV D t (lpG e f ε x 0 j₀) (lpG e f ε x 0 (j₀ + 1))
      (lpG e f ε x (-1) (j₀ + mirK e f)) := Iff.rfl

section mirror

variable {e f : ℕ} {α β γ L ax ay : ℝ}

theorem mirK_mul (S : SetupG D e f α β γ L ax ay) :
    mirK (e : ℝ) (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) = 2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
  unfold mirK
  exact div_mul_cancel₀ _ S.b_pos.ne'

/-- `K/b > 2` (`K − 2b = e²`) -/
theorem mirK_gt_two (S : SetupG D e f α β γ L ax ay) : 2 < mirK (e : ℝ) (f : ℝ) := by
  have hb := S.b_pos
  have hs := mirK_mul S
  by_contra h
  push_neg at h
  have h2 := mul_le_mul_of_nonneg_right h hb.le
  rw [hs] at h2
  nlinarith [pow_pos S.e0 2]

/-- **`K/b` is not an integer** for coprime `1 ≤ e < f` -/
theorem mirK_not_int {e f : ℕ} (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) :
    ¬ ∃ n : ℤ, mirK (e : ℝ) (f : ℝ) = (n : ℝ) := by
  rintro ⟨n, hn⟩
  have hb : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have h1 : (e : ℝ) < f := by exact_mod_cast hef
    have h2 : (0 : ℝ) < e := by exact_mod_cast he
    nlinarith
  unfold mirK at hn
  rw [div_eq_iff hb.ne'] at hn
  have hZ : 2 * (f : ℤ) ^ 2 - (e : ℤ) ^ 2 = n * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) := by exact_mod_cast hn
  have hdf : ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) ∣ (f : ℤ) ^ 2 := ⟨n - 1, by linear_combination hZ⟩
  have hde : ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) ∣ (e : ℤ) ^ 2 := ⟨n - 2, by linear_combination hZ⟩
  have hc : IsCoprime ((e : ℤ) ^ 2) ((f : ℤ) ^ 2) := (Nat.isCoprime_iff_coprime.mpr hco).pow
  have hu : IsUnit ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) := hc.isUnit_of_dvd' hde hdf
  have hbZ : (0 : ℤ) < (f : ℤ) ^ 2 - (e : ℤ) ^ 2 := by
    have h1 : (e : ℤ) < f := by exact_mod_cast hef
    have h2 : (0 : ℤ) < e := by exact_mod_cast he
    nlinarith
  have h1 : (e : ℤ) + 1 ≤ f := by exact_mod_cast hef
  have h2 : (1 : ℤ) ≤ e := by exact_mod_cast he
  rcases Int.isUnit_iff.mp hu with h | h
  · nlinarith [mul_nonneg (sub_nonneg.mpr h1) (show (0 : ℤ) ≤ f + e + 1 by linarith)]
  · linarith

/-- **the vertex `M` of the mirror tile is not a point `p(ξ', m)` of the lattice with integer height `m`** -/
theorem mirror_vertex_not_lattice (S : SetupG D e f α β γ L ax ay) (j₀ : ℕ) (ε x ξ' : ℝ) (m : ℤ) :
    lpG (e : ℝ) (f : ℝ) ε x (-1) ((j₀ : ℝ) + mirK (e : ℝ) (f : ℝ))
      ≠ lpG (e : ℝ) (f : ℝ) ε x ξ' (m : ℝ) := by
  intro h
  have h' := lpG_eta_eq S.e0 S.hef' h
  exact mirK_not_int S.he S.hef S.hco ⟨m - j₀, by push_cast; linarith⟩

variable {ε : ℝ}

/-- **the sides of the mirror tile**: `|PQ| = b`, `|MP| = c`, `|MQ| = a` -/
theorem mirror_dists (S : SetupG D e f α β γ L ax ay) (hε : ε ^ 2 = 1) (x j₀ : ℝ) :
    dist (lpG (e : ℝ) (f : ℝ) ε x 0 j₀) (lpG (e : ℝ) (f : ℝ) ε x 0 (j₀ + 1)) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧
    dist (lpG (e : ℝ) (f : ℝ) ε x (-1) (j₀ + mirK (e : ℝ) (f : ℝ))) (lpG (e : ℝ) (f : ℝ) ε x 0 j₀)
      = (f : ℝ) ^ 2 ∧
    dist (lpG (e : ℝ) (f : ℝ) ε x (-1) (j₀ + mirK (e : ℝ) (f : ℝ))) (lpG (e : ℝ) (f : ℝ) ε x 0 (j₀ + 1))
      = (e : ℝ) * f :=
  ⟨dist_step_vG S.e0 S.hef' hε 0 j₀, dist_mirrorP S.e0 S.hef' hε j₀ _ (mirK_mul S),
    dist_mirrorQ S.e0 S.hef' hε j₀ _ (mirK_mul S)⟩

/-- **the angles of the mirror tile**: `α` at `P`, `γ` at `Q`, `β` at `M` -/
theorem mirror_angles (S : SetupG D e f α β γ L ax ay) (hε : ε ^ 2 = 1) {x j₀ : ℝ} {t : Fin N}
    (h : HasV D t (lpG (e : ℝ) (f : ℝ) ε x 0 j₀) (lpG (e : ℝ) (f : ℝ) ε x 0 (j₀ + 1))
      (lpG (e : ℝ) (f : ℝ) ε x (-1) (j₀ + mirK (e : ℝ) (f : ℝ)))) :
    (D.tile t).localAngle (lpG (e : ℝ) (f : ℝ) ε x 0 j₀) = α ∧
    (D.tile t).localAngle (lpG (e : ℝ) (f : ℝ) ε x 0 (j₀ + 1)) = γ ∧
    (D.tile t).localAngle (lpG (e : ℝ) (f : ℝ) ε x (-1) (j₀ + mirK (e : ℝ) (f : ℝ))) = β := by
  obtain ⟨dPQ, dMP, dMQ⟩ := mirror_dists S hε x j₀
  exact ⟨(h.anglesG S.tile S.hM).1 (by rw [dist_comm]; exact dMQ),
    (h.rot.anglesG S.tile S.hM).2.2 dMP, (h.rot.rot.anglesG S.tile S.hM).2.1 dPQ⟩

/-- **the mirror tile lies on the side σ of `ℓ`** (`FXG ≤ lv` on its vertices), strictly at `M` -/
theorem mirror_side (S : SetupG D e f α β γ L ax ay) (hε : ε ^ 2 = 1) {x j₀ : ℝ} {t : Fin N}
    (h : HasV D t (lpG (e : ℝ) (f : ℝ) ε x 0 j₀) (lpG (e : ℝ) (f : ℝ) ε x 0 (j₀ + 1))
      (lpG (e : ℝ) (f : ℝ) ε x (-1) (j₀ + mirK (e : ℝ) (f : ℝ)))) :
    (∀ i, FXG (e : ℝ) (f : ℝ) ε ((D.tile t).pts i) ≤ lvG (e : ℝ) (f : ℝ) ε x 0) ∧
    FXG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x (-1) (j₀ + mirK (e : ℝ) (f : ℝ)))
      < lvG (e : ℝ) (f : ℝ) ε x 0 := by
  have hP : FXG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x 0 j₀) = lvG (e : ℝ) (f : ℝ) ε x 0 :=
    FXG_lp hε 0 j₀
  have hQ : FXG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x 0 (j₀ + 1)) = lvG (e : ℝ) (f : ℝ) ε x 0 :=
    FXG_lp hε 0 (j₀ + 1)
  have hM : FXG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x (-1) (j₀ + mirK (e : ℝ) (f : ℝ)))
      < lvG (e : ℝ) (f : ℝ) ε x 0 := by
    rw [FXG_lp hε]
    exact lvG_lt S.e0 S.hef' (by norm_num)
  exact ⟨h.all (P := fun p => FXG (e : ℝ) (f : ℝ) ε p ≤ lvG (e : ℝ) (f : ℝ) ε x 0) hP.le hQ.le hM.le, hM⟩

/-- **the edge vector `Q − P` along `ℓ`** (`= b · (ε cos α, sin α)`) -/
theorem mirror_ray_up (e f ε x η : ℝ) :
    lpG e f ε x 0 (η + 1) - lpG e f ε x 0 η = mkPt (ε * (f ^ 2 - uuG e f)) (hhG e f) := by
  unfold lpG
  apply plane_ext <;> simp only [PiLp.sub_apply, mkPt_zero, mkPt_one] <;> ring

/-- **the edge vector `M − Q`** (`= a · (ε cos γ, sin γ)`, direction `e(γ)` for `ε = 1`) -/
theorem mirror_ray_M (S : SetupG D e f α β γ L ax ay) (x j₀ : ℝ) :
    lpG (e : ℝ) (f : ℝ) ε x (-1) (j₀ + mirK (e : ℝ) (f : ℝ)) - lpG (e : ℝ) (f : ℝ) ε x 0 (j₀ + 1)
      = mkPt (ε * (-((e : ℝ) ^ 2) / 2)) ((e : ℝ) * rtG (e : ℝ) (f : ℝ) / 2) := by
  have he0 := S.e0
  have hef := S.hef'
  have hs := mirK_mul S
  have hu := uuG_spec he0 hef
  have hhs := hhG_spec he0 hef
  have hne : 2 * (f : ℝ) ^ 2 * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ≠ 0 :=
    (mul_pos (two_f2_pos he0 hef) S.b_pos).ne'
  have hX : (mirK (e : ℝ) (f : ℝ) - 2) * (f : ℝ) ^ 2 - (mirK (e : ℝ) (f : ℝ) - 1) * uuG (e : ℝ) (f : ℝ)
      = -((e : ℝ) ^ 2) / 2 := by
    apply mul_left_cancel₀ hne
    linear_combination (2 * (f : ℝ) ^ 4 - 2 * (f : ℝ) ^ 2 * uuG (e : ℝ) (f : ℝ)) * hs - (f : ℝ) ^ 2 * hu
  have hY : (mirK (e : ℝ) (f : ℝ) - 1) * hhG (e : ℝ) (f : ℝ) = (e : ℝ) * rtG (e : ℝ) (f : ℝ) / 2 := by
    apply mul_left_cancel₀ hne
    linear_combination (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * (mirK (e : ℝ) (f : ℝ) - 1)) * hhs
      + ((e : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * rtG (e : ℝ) (f : ℝ)) * hs
  unfold lpG
  apply plane_ext
  · simp only [PiLp.sub_apply, mkPt_zero]
    linear_combination ε * hX
  · simp only [PiLp.sub_apply, mkPt_one]
    linear_combination hY

/-- **the points `p(−δ, j0+1)` to the left of `Q` are interior to the mirror tile** (the paper: "the direction `d(π)` is interior to `T`"):
for `0 < δ`, `δ s₀ < 1` (`s₀ = K/b > 1`); weights `δ (s₀ − 1)`, `1 − δ s₀`, `δ` -/
theorem mirror_row_left {e f ε x j₀ s₀ δ : ℝ} {t : Fin N}
    (h : HasV D t (lpG e f ε x 0 j₀) (lpG e f ε x 0 (j₀ + 1)) (lpG e f ε x (-1) (j₀ + s₀)))
    (hs₀ : 1 < s₀) (hδ : 0 < δ) (hδs : δ * s₀ < 1) :
    lpG e f ε x (-δ) (j₀ + 1) ∈ interior (D.tile t).carrier := by
  have e' : lpG e f ε x (-δ) (j₀ + 1)
      = (δ * (s₀ - 1)) • lpG e f ε x 0 j₀ + (1 - δ * s₀) • lpG e f ε x 0 (j₀ + 1)
        + δ • lpG e f ε x (-1) (j₀ + s₀) := by
    unfold lpG
    apply plane_ext <;>
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mkPt_zero, mkPt_one] <;> ring
  rw [e']
  exact hasV_bary h (mul_pos hδ (by linarith)) (by linarith) hδ (by ring)

end mirror

/-! ## 4. The statement `MG(s', j0)` and its size 1 -/

/-- **THE STATEMENT `M(s', j0)` of the paper**, for the lattice with origin `x` (the paper: "the same statement is made for the lattice with
origin `p(c0, 0)`": `x` is arbitrary), `0 ≤ j0 < s' ≤ f − 1`, `s' − j0 ≤ e`: the following three conditions cannot hold together.
(M1) the mirror image `T` of `U(0, j0)` in the line `ℓ` is a tile (`MirrorAt`); (K2) the rows `≤ j0` of `Δ_{s'}` are lattice (`K2G`);
(K3) the side `ρ_{s'}` is outside Δ or a tile has an edge of length `b` or `c` on `m_{s'}` from a clamped point `Z` (`K3G`). -/
def MG (D : CongruentDissection N) (e f : ℕ) (ε x : ℝ) (s j0 : ℕ) : Prop :=
  j0 < s → s < f → s - j0 ≤ e → MirrorAt D (e : ℝ) (f : ℝ) ε x (j0 : ℝ) →
    K2G D (e : ℝ) (f : ℝ) ε x s j0 → K3G D (e : ℝ) (f : ℝ) ε x (s : ℝ) (j0 : ℝ) → False

/-- `M` for all origins and all pairs of size `n` (the induction hypothesis of the paper: "for all pairs and all origins at once") -/
def MGn (D : CongruentDissection N) (e f : ℕ) (ε : ℝ) (n : ℕ) : Prop :=
  ∀ (x : ℝ) (s j0 : ℕ), s - j0 = n → MG D e f ε x s j0

section size_one

variable {e f : ℕ} {α β γ L ax ay ε x : ℝ}

/-- **the `m`-chord principle in the form the size 1 needs**: either `ρ_s` is outside Δ (first form of (K3)), or a tile `ψ` has `p(s − J, J)` in
the relative interior of an edge on `m_s` (it shows a straight angle there and contains every short push into `ρ_s`) -/
theorem psi_or_out (C : CtxBase D e f α β γ L ax ay ε x) {s : ℝ} {j0 J : ℕ} (hJ : J = j0 + 1)
    (hK : K3G D (e : ℝ) (f : ℝ) ε x s (j0 : ℝ)) (hJf : J < f)
    (hU : ∀ j' : ℕ, j' ≤ j0 → UTG D (e : ℝ) (f : ℝ) ε x (s - 1 - j') j') :
    (∀ q ∈ D.target.carrier, -lvG (e : ℝ) (f : ℝ) ε x s ≤ GSG (e : ℝ) (f : ℝ) ε q) ∨
    ∃ ψ : Fin N, lpG (e : ℝ) (f : ℝ) ε x (s - J) J ∈ (D.tile ψ).carrier ∧
      (D.tile ψ).localAngle (lpG (e : ℝ) (f : ℝ) ε x (s - J) J) = Real.pi ∧
      ∀ v : Plane, GSG (e : ℝ) (f : ℝ) ε v < 0 → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε' : ℝ, 0 < ε' → ε' < ε₀ →
        lpG (e : ℝ) (f : ℝ) ε x (s - J) J + ε' • v ∈ interior (D.tile ψ).carrier := by
  rcases hK with hout | ⟨w, k, m, η₁, η₂, hkm, h1, h2, hk, hm, hl, hle, hcl⟩
  · exact Or.inl hout
  · have hη₁ : η₁ < J := by
      have : η₁ ≤ j0 := by exact_mod_cast h1
      omega
    exact Or.inr (C.psiG hkm hη₁ h2 hk hm hl hle hcl hJf (fun j' hj' hjJ => hU j' (by omega)))

/-- **the overlap of the sectors at `Q = p(0, j0+1)`** (size 1): a tile `T = (P, Q, M)` showing `γ` at `Q`, whose cone at `Q` contains a direction
`v = (M − Q) + θ (P − Q)` that points into `ρ_s` (`GS v < 0`), and (K2), (K3) for `(j0 + 1, j0)`: a contradiction.  `ψ` of the `m`-chord principle
covers all the directions into `ρ_s` at `Q`; `T ≠ ψ` because their angles at `Q` are `γ < π` and `π`; two distinct tiles do not share interior points.
(Conclusion `False`.) -/
theorem overlap_contra (C : CtxBase D e f α β γ L ax ay ε x) {j0 : ℕ} (hsf : j0 + 1 < f)
    {t : Fin N} {P Q M : Plane} (hT : HasV D t P Q M)
    (hQ : Q = lpG (e : ℝ) (f : ℝ) ε x 0 ((j0 : ℝ) + 1)) (hγ : (D.tile t).localAngle Q = γ)
    {θ : ℝ} (hθ : 0 < θ) (hv : GSG (e : ℝ) (f : ℝ) ε ((1 : ℝ) • (M - Q) + θ • (P - Q)) < 0)
    (hK2 : K2G D (e : ℝ) (f : ℝ) ε x (j0 + 1) j0)
    (hK3 : K3G D (e : ℝ) (f : ℝ) ε x ((j0 + 1 : ℕ) : ℝ) (j0 : ℝ)) : False := by
  have S := C.S
  have hε := C.e2
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hUrow : ∀ j' : ℕ, j' ≤ j0 →
      UTG D (e : ℝ) (f : ℝ) ε x (((j0 + 1 : ℕ) : ℝ) - 1 - j') j' := by
    intro j' hj'
    have h := hK2.1 (j0 + 1 - 1 - j') j' hj' (by omega)
    have hc : ((j0 + 1 - 1 - j' : ℕ) : ℝ) = ((j0 + 1 : ℕ) : ℝ) - 1 - j' := by
      rw [Nat.cast_sub (show j' ≤ j0 + 1 - 1 by omega), Nat.cast_sub (show 1 ≤ j0 + 1 by omega),
        Nat.cast_one]
    rwa [hc] at h
  obtain ⟨ε₀, hε₀, hTpush⟩ := hasV_push hT.rot one_pos hθ
  have hpsi := psi_or_out C (s := ((j0 + 1 : ℕ) : ℝ)) (j0 := j0) (J := j0 + 1) rfl hK3 hsf hUrow
  have hQeq : lpG (e : ℝ) (f : ℝ) ε x (((j0 + 1 : ℕ) : ℝ) - ((j0 + 1 : ℕ) : ℝ)) ((j0 + 1 : ℕ) : ℝ)
      = Q := by
    rw [hQ]; exact lpG_congr (sub_self _) (by norm_num)
  have hGQ : GSG (e : ℝ) (f : ℝ) ε Q = -lvG (e : ℝ) (f : ℝ) ε x ((j0 + 1 : ℕ) : ℝ) := by
    rw [hQ, GSG_lp hε]
    have : (0 : ℝ) + ((j0 : ℝ) + 1) = ((j0 + 1 : ℕ) : ℝ) := by norm_num
    rw [this]
  rcases hpsi with hout | ⟨ψ, hψc, hψπ, hψpush⟩
  · -- `ρ_s` is outside Δ, but `T` has interior points there
    have hz := interior_subset (hTpush (ε₀ / 2) (by linarith) (by linarith))
    have hzt := Erdos634.BaseSelection.tile_subset_target D.toDissection t hz
    have h3 := hout _ hzt
    rw [map_add, map_smul, smul_eq_mul, hGQ] at h3
    nlinarith [mul_pos (show 0 < ε₀ / 2 by linarith) (neg_pos.mpr hv)]
  · rw [hQeq] at hψc hψπ hψpush
    obtain ⟨ε₁, hε₁, hψ'⟩ := hψpush _ hv
    have hm := lt_min hε₀ hε₁
    have hm0 : 0 < min ε₀ ε₁ / 2 := by linarith
    have h1 := hTpush (min ε₀ ε₁ / 2) hm0 (by linarith [min_le_left ε₀ ε₁])
    have h2 := hψ' (min ε₀ ε₁ / 2) hm0 (by linarith [min_le_right ε₀ ε₁])
    have hne : t ≠ ψ := ne_of_angle (p := Q) (by rw [hγ, hψπ]; exact hγπ.ne)
    exact Set.disjoint_left.mp (D.toDissection.interiors_disjoint hne) h1 h2

/-- **`M(j0 + 1, j0)`, SIZE 1** (paper: "the `m`-chord principle with `j = s' = j0 + 1` gives ψ, covering `(−β, π − β)` at `p(0, s')`, or says that
these directions point out of Δ.  They meet the sector of `T` in `(γ, π − β)`: a contradiction"): context `CtxBase` only, no (K1) -/
theorem MG_size_one (C : CtxBase D e f α β γ L ax ay ε x) (j0 : ℕ) : MG D e f ε x (j0 + 1) j0 := by
  intro _ hsf _ hM hK2 hK3
  have S := C.S
  have hε := C.e2
  obtain ⟨t, hT⟩ := hM
  have hT' : HasV D t (lpG (e : ℝ) (f : ℝ) ε x 0 (j0 : ℝ)) (lpG (e : ℝ) (f : ℝ) ε x 0 ((j0 : ℝ) + 1))
      (lpG (e : ℝ) (f : ℝ) ε x (-1) ((j0 : ℝ) + mirK (e : ℝ) (f : ℝ))) := hT
  obtain ⟨-, hγ, -⟩ := mirror_angles S hε hT'
  have hs₀ := mirK_gt_two S
  have hθ : 0 < (mirK (e : ℝ) (f : ℝ) - 2) / 2 := by linarith
  have hfh := nhG_pos S.e0 S.hef'
  refine overlap_contra C hsf hT' rfl hγ hθ ?_ hK2 hK3
  have e1 : GSG (e : ℝ) (f : ℝ) ε ((1 : ℝ) • (lpG (e : ℝ) (f : ℝ) ε x (-1) ((j0 : ℝ) + mirK (e : ℝ) (f : ℝ))
        - lpG (e : ℝ) (f : ℝ) ε x 0 ((j0 : ℝ) + 1))
      + ((mirK (e : ℝ) (f : ℝ) - 2) / 2) • (lpG (e : ℝ) (f : ℝ) ε x 0 (j0 : ℝ)
        - lpG (e : ℝ) (f : ℝ) ε x 0 ((j0 : ℝ) + 1)))
      = -((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((mirK (e : ℝ) (f : ℝ) - 2) / 2) := by
    simp only [map_add, map_smul, map_sub, GSG_lp hε, smul_eq_mul, lvG]
    ring
  refine lt_of_eq_of_lt e1 ?_
  nlinarith [mul_pos hfh hθ]

/-- **`M` of size 1 for all origins** -/
theorem MGn_one (S : SetupG D e f α β γ L ax ay) (hε : ε = 1 ∨ ε = -1) : MGn D e f ε 1 := by
  intro x s j0 hsz
  obtain rfl : s = j0 + 1 := by omega
  exact MG_size_one ⟨S, hε⟩ j0

end size_one

end Erdos634.Draft.SideRunGA

#print axioms Erdos634.Draft.SideRunGA.lpG_shift
#print axioms Erdos634.Draft.SideRunGA.lvG_shift
#print axioms Erdos634.Draft.SideRunGA.UTG_shift
#print axioms Erdos634.Draft.SideRunGA.DTG_shift
#print axioms Erdos634.Draft.SideRunGA.K2G_shift
#print axioms Erdos634.Draft.SideRunGA.ClampedBelowG_shift
#print axioms Erdos634.Draft.SideRunGA.RhoEdgeG_shift
#print axioms Erdos634.Draft.SideRunGA.K3G_shift
#print axioms Erdos634.Draft.SideRunGA.K1J_shift
#print axioms Erdos634.Draft.SideRunGA.shift_open_point
#print axioms Erdos634.Draft.SideRunGA.ctxJ_shift
#print axioms Erdos634.Draft.SideRunGA.K_at_shift
#print axioms Erdos634.Draft.SideRunGA.shift_check_zero
#print axioms Erdos634.Draft.SideRunGA.K2G_shift_zero
#print axioms Erdos634.Draft.SideRunGA.ctxJ_shift_zero
#print axioms Erdos634.Draft.SideRunGA.hasV_bary
#print axioms Erdos634.Draft.SideRunGA.hasV_push
#print axioms Erdos634.Draft.SideRunGA.mirK_not_int
#print axioms Erdos634.Draft.SideRunGA.mirror_vertex_not_lattice
#print axioms Erdos634.Draft.SideRunGA.mirror_dists
#print axioms Erdos634.Draft.SideRunGA.mirror_angles
#print axioms Erdos634.Draft.SideRunGA.mirror_side
#print axioms Erdos634.Draft.SideRunGA.mirror_ray_up
#print axioms Erdos634.Draft.SideRunGA.mirror_ray_M
#print axioms Erdos634.Draft.SideRunGA.mirror_row_left
#print axioms Erdos634.Draft.SideRunGA.psi_or_out
#print axioms Erdos634.Draft.SideRunGA.overlap_contra
#print axioms Erdos634.Draft.SideRunGA.MG_size_one
#print axioms Erdos634.Draft.SideRunGA.MGn_one
