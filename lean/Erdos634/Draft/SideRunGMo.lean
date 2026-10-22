/-
Draft/SideRunGMo.lean -- written 14 October 2026.  UNAUDITED.  In `AllThreshold`.  Third file of module M4 of the plan for
`thm:cornerrun`: **THE STATEMENT `M°(e+1)`** and the corollary for a run of `C1` of length `k ≤ e + 1` at a corner `2α` when `a < b`
(first file `Draft/SideRunGMoA.lean`, second file `Draft/SideRunGMoB.lean`).

THE PAPER'S STATEMENT.  "*Statement `M°(e+1)`*, for the members with `a < b` and `e + 1 ≤ f − 1`: the conditions (M1), (K2), (K3) for `(s', j0) = (e + 1, 0)` cannot hold together when `P` is a corner of Δ of angle `2α`."
"*Proof.* Steps (a), (b), (c) are as above; the statements `M` that they call have sizes at most `e`.  The only new point is in (b): the row `Λ = [p(0,1), p(e,1)]` has `e` edges and can be cut as `c^e` or as `a^f`.  For `c^e` the proof
of (b) and (c) goes through ((c) calls `K(e+1,1)` and `M(e+1,1)`, of size `e`).  For `a^f`: the `f` tiles above `Λ` have an `a`-edge on it, so they are of type `A_1` or `A_2` with respect to `Λ`; the last one shows `β` at
`p(e,1)` (the wedge there is `β`, as in (b)), so it is `A_2`; an `A_1` followed by an `A_2` would show two `γ` at a point of `Λ`, where the tiles above `Λ` fill a straight angle; so all are `A_2`.  The first one, `Y`, has its vertex `γ` at `p(0,1)`,
where it fills the wedge `(0, γ)`; its `b`-edge leaves `p(0,1)` in the direction `d(γ)`, along the `a`-edge of `T`, which ends at `V = P + c d(2α)`.  Since `b > a`, `V` is in the relative interior of the `b`-edge of `Y`.  But `V` lies on the
second side of Δ at `P` (direction `d(2α)`), and `p(0,1)` lies strictly inside the corner, so the `b`-edge of `Y` leaves Δ at `V`: a contradiction."

CONTENTS of this file.
0. Tools: `lpG_seg_mem`, `lpG_row_sub`, `row_not_subsingleton`, `hasV_localAngle_pi` (a point in the open edge `(B, C)` of a tile `(A, B, C)` has the local angle `π`: `RouteOne.openSegment_localAngle_pi`).
1. The `a^f` row: `Zp` (the points `Z_k = p(k e/f, j0+1)` of `Λ` that the `a`-edges cut), `ATile` (**a tile above `Λ` with the `a`-edge `[Z_k, Z_{k+1}]`: type `A_1` (`β` at `Z_k`, `γ` at `Z_{k+1}`) or `A_2` (`γ`, `β`)**),
   `a_edge`, `a_step`, `a_chain` (**"the `f` tiles above `Λ` have an `a`-edge on it, so they are of type `A_1` or `A_2`"**: the first edge at `Z_k`, clamped by the previous tile), `A1_right_angle`, `A2_left_angle`,
   `a_two_false` (**"an `A_1` followed by an `A_2` would show two `γ` at a point of `Λ`, where the tiles above `Λ` fill a straight angle"**: the tile `D(i, j0)` below has the angle `π` there, `π + 2γ > 2π`),
   `a_all_A2` (**"the last one shows `β` at `p(e,1)`, so it is `A_2`" (`right_end_ang` with `θ = γ`); "so all are `A_2`"**).
2. `a_geom`: **the geometry of the first tile `Y`** ("its `b`-edge ... leaves Δ at `V`"): the third vertex `W` of an `A_2` tile with its `a`-edge `[p(0,1), p(0,1) + (a, 0)]` is at `p(0,1) + (−e b / 2f, b √(4f² − e²) / 2f)`, which is outside the
   corner `2α` of Δ when `a < b`: the linear form `g_A` of the side `A'A` has, at `W`, the value `t b √(4f²−e²) f (a − b) < 0` (`t` the scale of the apex `(ax, ay)`).  The tile `T` is not needed for this inequality (it is the collinearity of
   the `b`-edge of `Y` with the `a`-edge of `T` that the paper uses to see it: `V = W (a/b)`-th of the way).
3. `MO_main` (**`M°(e+1)`, coordinates of the corner**) and `MO_corner` (**`M°(e+1)` as the paper states it: `Co : CornersA` and the angle of Δ at `A'` is `2α`**), `corner_run_data`, `corner_run_short_o` (**the corollary
   R2 consumes: a run of `k` tiles `C1` from the corner `A'` of angle `2α`, `1 ≤ k ≤ e + 1`, `a < b`, `e + 1 < f`, that ends at `Q'` or before a tile other than `B1`, `C1`, is impossible: the addendum `k ≥ e + 2`**).

WITNESSES.  As in `Draft/SideRunGMStep.lean`: the statements conclude `False` under the conditions (M1), (K2), (K3) of the paper.

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGMoB
import Erdos634.RouteOneThroughEdge

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

section toolsO

variable {e f : ℕ} {α β γ L ax ay x : ℝ} {s j0 : ℕ}

/-- a point of the row between two lattice points of the row lies on the segment -/
theorem lpG_seg_mem (e f ε x η : ℝ) {a b c : ℝ} (hab : a < b) (hac : a ≤ c) (hcb : c ≤ b) :
    lpG e f ε x c η ∈ segment ℝ (lpG e f ε x a η) (lpG e f ε x b η) := by
  have hba : 0 < b - a := by linarith
  have h := lp_mem_segG (e := e) (f := f) (ε := ε) (x := x) (ξ := a) (η := η) (ξ' := b) (η' := η)
    (τ := (c - a) / (b - a)) (div_nonneg (by linarith) hba.le) (by rw [div_le_one hba]; linarith)
  rw [show lpG e f ε x (a + (c - a) / (b - a) * (b - a)) (η + (c - a) / (b - a) * (η - η))
      = lpG e f ε x c η from lpG_congr (by rw [div_mul_cancel₀ _ hba.ne']; ring) (by ring)] at h
  exact h

/-- the open segment between two points `a < b` of the row lies in the open segment `(0, q)` -/
theorem lpG_row_sub (e f ε x η : ℝ) {q a b : ℝ} (hq : 0 < q) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ q) :
    openSegment ℝ (lpG e f ε x a η) (lpG e f ε x b η)
      ⊆ openSegment ℝ (lpG e f ε x 0 η) (lpG e f ε x q η) := by
  intro y hy
  rw [openSegment_eq_image_lineMap] at hy
  obtain ⟨τ, ⟨h0, h1⟩, rfl⟩ := hy
  rw [lineMap_lpG, show lpG e f ε x (a + τ * (b - a)) (η + τ * (η - η))
      = lpG e f ε x (a + τ * (b - a)) η from lpG_congr rfl (by ring)]
  exact lpG_row_mid e f ε x η (a := 0) (by nlinarith [mul_pos h0 (sub_pos.mpr hab)])
    (by nlinarith [mul_pos (sub_pos.mpr h1) (sub_pos.mpr hab)])

/-- **a segment of the row from a point of the row, to the right, meets the row `[0, q]` in more than a point** -/
theorem row_not_subsingleton (e f ε x η : ℝ) (he : 0 < e) (hef : e < f) (hε : ε ^ 2 = 1) {ρ q t : ℝ}
    (hq : 0 < q) (hρ0 : 0 ≤ ρ) (hρq : ρ < q) (ht : 0 < t) :
    ¬ (segment ℝ (lpG e f ε x ρ η) (lpG e f ε x (ρ + t * (q - ρ)) η) ∩
        segment ℝ (lpG e f ε x 0 η) (lpG e f ε x q η)).Subsingleton := by
  intro hss
  have hqk : 0 < q - ρ := by linarith
  have hm1 : 0 < min t 1 := lt_min ht one_pos
  have hτ0 : 0 < min t 1 / 2 := half_pos hm1
  have hτt : min t 1 / 2 ≤ t := by have := min_le_left t 1; linarith
  have hτ1 : min t 1 / 2 ≤ 1 := by have := min_le_right t 1; linarith
  have hu1 : lpG e f ε x (ρ + min t 1 / 2 * (q - ρ)) η ∈
      segment ℝ (lpG e f ε x ρ η) (lpG e f ε x (ρ + t * (q - ρ)) η) :=
    lpG_seg_mem e f ε x η (by nlinarith [mul_pos ht hqk]) (by nlinarith [mul_pos hτ0 hqk])
      (by nlinarith [mul_nonneg (sub_nonneg.mpr hτt) hqk.le])
  have hu2 : lpG e f ε x (ρ + min t 1 / 2 * (q - ρ)) η ∈
      segment ℝ (lpG e f ε x 0 η) (lpG e f ε x q η) :=
    lpG_seg_mem e f ε x η hq (by nlinarith [mul_pos hτ0 hqk])
      (by nlinarith [mul_nonneg (sub_nonneg.mpr hτ1) hqk.le])
  have hP2 : lpG e f ε x ρ η ∈ segment ℝ (lpG e f ε x 0 η) (lpG e f ε x q η) :=
    lpG_seg_mem e f ε x η hq hρ0 hρq.le
  have heq := hss ⟨left_mem_segment ℝ _ _, hP2⟩ ⟨hu1, hu2⟩
  exact lpG_ne_xi he hef hε (by intro h; nlinarith [mul_pos hτ0 hqk]) heq

/-- **a point in the open edge `(B, C)` of a tile `(A, B, C)` has the local angle `π`** -/
theorem hasV_localAngle_pi {t : Fin N} {A B C W : Plane} (h : HasV D t A B C)
    (hW : W ∈ openSegment ℝ B C) : (D.tile t).localAngle W = Real.pi := by
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := h
  have hcases : ∀ k m j : Fin 3, k ≠ m → k ≠ j → m ≠ j →
      (m = k + 1 ∧ j = k + 2) ∨ (m = k + 2 ∧ j = k + 1) := by decide
  rcases hcases k m j hkm hkj hmj with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Erdos634.RouteOne.openSegment_localAngle_pi (D.tile t) k ?_
    rw [← h1, ← h2, hm, hj]
    exact hW
  · refine Erdos634.RouteOne.openSegment_localAngle_pi (D.tile t) k ?_
    rw [← h1, ← h2, hm, hj, openSegment_symm]
    exact hW

end toolsO

/-! ## 1. The row `Λ` cut as `a^f` -/

/-- **the points `Z_k = p(k e / f, j0+1)` of `Λ`** (the ends of the `a`-edges when `Λ` is cut as `a^f`; `Z_0 = p(0, j0+1)`, `Z_f = p(e, j0+1)`) -/
noncomputable abbrev Zp (e f x : ℝ) (j0 k : ℕ) : Plane :=
  lpG e f 1 x ((k : ℝ) * (e / f)) ((j0 : ℝ) + 1)

/-- **a tile above `Λ` with the `a`-edge `[Z_k, Z_{k+1}]`** and the third vertex `W` at the distances `d1` from `Z_k`, `d2` from `Z_{k+1}`: type `A_1` (`d1 = c`, `d2 = b`: `β` at `Z_k`, `γ` at `Z_{k+1}`) or type `A_2`
(`d1 = b`, `d2 = c`: `γ` at `Z_k`, `β` at `Z_{k+1}`) -/
def ATile (D : CongruentDissection N) (e f x : ℝ) (j0 k : ℕ) (d1 d2 : ℝ) : Prop :=
  ∃ (t : Fin N) (W : Plane), HasV D t (Zp e f x j0 k) (Zp e f x j0 (k + 1)) W ∧
    GHG f W < -((f ^ 2 * hhG e f) * ((j0 : ℝ) + 1)) ∧
    (∀ i, GHG f ((D.tile t).pts i) ≤ -((f ^ 2 * hhG e f) * ((j0 : ℝ) + 1))) ∧
    dist W (Zp e f x j0 k) = d1 ∧ dist W (Zp e f x j0 (k + 1)) = d2

section chainO

variable {e f : ℕ} {α β γ L ax ay x : ℝ} {s j0 : ℕ}

local notation "LV" => -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j0 : ℝ) + 1))

/-- **THE FIRST EDGE AT `Z_k` IS THE `a`-EDGE `[Z_k, Z_{k+1}]` OF `Λ`** (the tiles above `Λ` are found from the left): the first edge at `Z_k` of the tiles above `Λ`, given a clamp of `Z_k` from the left, is an edge of `Λ`
(`edge_clamped`: it meets `Λ` in more than a point), so by `RowLenAll` it has the length `a`, so it is `[Z_k, Z_{k+1}]`. -/
theorem a_edge (W : StepCtxO D e f α β γ L ax ay x s j0) {q : ℕ} (hq : q + j0 + 1 = s) (hqe : q = e)
    (hall : RowLenAll D (e : ℝ) (f : ℝ) x j0 q ((e : ℝ) * f)) {k : ℕ} (hk : k < f)
    {P'' : Plane} (hfP'' : GHG (f : ℝ) P'' = LV)
    (hP'' : Zp (e : ℝ) (f : ℝ) x j0 k ∈
      openSegment ℝ P'' (lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1)))
    (hL'' : ∀ ed ∈ D.lineChain (GHG (f : ℝ)) LV,
      ¬ Straddles ((D.tile ed.1).edge ed.2) P'' (Zp (e : ℝ) (f : ℝ) x j0 k)
        (lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1))) :
    ∃ (tt : Fin N) (kk mm : Fin 3), kk ≠ mm ∧ (D.tile tt).pts kk = Zp (e : ℝ) (f : ℝ) x j0 k ∧
      (D.tile tt).pts mm = Zp (e : ℝ) (f : ℝ) x j0 (k + 1) ∧
      (∀ i, GHG (f : ℝ) ((D.tile tt).pts i) ≤ LV) ∧
      dist ((D.tile tt).pts kk) ((D.tile tt).pts mm) = (e : ℝ) * f := by
  have S := W.S
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have he0 := S.e0
  have hef := S.hef'
  have hf0 := S.f0
  have hq1 : 1 ≤ q := by rw [hqe]; exact S.he
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  have hσ : (0 : ℝ) < (e : ℝ) / f := div_pos he0 hf0
  have hσf : (e : ℝ) / f * (f : ℝ) ^ 2 = e * f := by field_simp
  have hqσ : (q : ℝ) = (f : ℝ) * ((e : ℝ) / f) := by rw [hqe]; field_simp
  have hkf : (k : ℝ) < f := by exact_mod_cast hk
  have hkσ : (k : ℝ) * ((e : ℝ) / f) < q := by rw [hqσ]; exact mul_lt_mul_of_pos_right hkf hσ
  have hk0 : 0 ≤ (k : ℝ) * ((e : ℝ) / f) := by positivity
  have hqk : 0 < (q : ℝ) - (k : ℝ) * ((e : ℝ) / f) := by linarith
  obtain ⟨hint, hwall⟩ := lambda_wallO W hq hq1
  obtain ⟨P', hfP', hP', hLeft⟩ := row_clamp_leftO W (ρ := (q : ℝ)) hqpos
  obtain ⟨Q', hfQ', hQ', hQc⟩ := row_clamp_rightO W hq
  have hA0q : lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1) ≠ lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1) :=
    lpG_ne_xi he0 hef hε hqpos.ne
  have hfA0 : GHG (f : ℝ) (lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1)) = LV := GHG_lp _ _ _ _ _ _
  have hfAq : GHG (f : ℝ) (lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1)) = LV := GHG_lp _ _ _ _ _ _
  have hfP : GHG (f : ℝ) (Zp (e : ℝ) (f : ℝ) x j0 k) = LV := GHG_lp _ _ _ _ _ _
  have hPQ : Zp (e : ℝ) (f : ℝ) x j0 k ≠ lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1) :=
    lpG_ne_xi he0 hef hε hkσ.ne
  have hsubΛ := lpG_row_sub (e : ℝ) (f : ℝ) 1 x ((j0 : ℝ) + 1) hqpos hk0 hkσ le_rfl
  have hint' : openSegment ℝ (Zp (e : ℝ) (f : ℝ) x j0 k)
      (lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1)) ⊆ interior D.target.carrier :=
    fun y hy => hint (hsubΛ hy)
  have hwall' : ∀ y ∈ openSegment ℝ (Zp (e : ℝ) (f : ℝ) x j0 k)
      (lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1)), ∀ i, y ∉ interior (D.tile i).carrier :=
    fun y hy => hwall y (hsubΛ hy)
  obtain ⟨ed, he, kk, mm, t, hkm, hkk, ht, hmm, hle, hedge, hdist⟩ :=
    next_tile D.toDissection (GHG (f : ℝ)) (GHG_ne he0 hef) LV hPQ hfP hfAq hfP'' hP'' hint' hwall' hL''
  have hE' : AffineMap.lineMap (Zp (e : ℝ) (f : ℝ) x j0 k)
      (lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1)) t
      = lpG (e : ℝ) (f : ℝ) 1 x ((k : ℝ) * ((e : ℝ) / f) + t * ((q : ℝ) - (k : ℝ) * ((e : ℝ) / f)))
          ((j0 : ℝ) + 1) := by
    rw [lineMap_lpG]
    exact lpG_congr (by ring) (by ring)
  rw [hE'] at hmm hedge
  have hnoP : ¬ Straddles (segment ℝ (Zp (e : ℝ) (f : ℝ) x j0 k)
      (lpG (e : ℝ) (f : ℝ) 1 x ((k : ℝ) * ((e : ℝ) / f) + t * ((q : ℝ) - (k : ℝ) * ((e : ℝ) / f)))
        ((j0 : ℝ) + 1))) P' (lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1))
        (lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1)) := by
    rw [← hedge]; exact hLeft ed he
  have hnoQ : ¬ Straddles (segment ℝ (Zp (e : ℝ) (f : ℝ) x j0 k)
      (lpG (e : ℝ) (f : ℝ) 1 x ((k : ℝ) * ((e : ℝ) / f) + t * ((q : ℝ) - (k : ℝ) * ((e : ℝ) / f)))
        ((j0 : ℝ) + 1))) Q' (lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1))
        (lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1)) := by
    rw [← hedge]; exact hQc ed he
  have hcl := edge_clamped (GHG (f : ℝ)) (GHG_ne he0 hef) LV hA0q hfA0 hfAq hfP' hfQ' hP' hQ'
    (p₁ := Zp (e : ℝ) (f : ℝ) x j0 k)
    (p₂ := lpG (e : ℝ) (f : ℝ) 1 x ((k : ℝ) * ((e : ℝ) / f) + t * ((q : ℝ) - (k : ℝ) * ((e : ℝ) / f)))
      ((j0 : ℝ) + 1)) hfP (GHG_lp _ _ _ _ _ _) hnoP hnoQ
  have hPmem : Zp (e : ℝ) (f : ℝ) x j0 k ∈ segment ℝ (lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1))
      (lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1)) :=
    lpG_seg_mem (e : ℝ) (f : ℝ) 1 x ((j0 : ℝ) + 1) hqpos hk0 hkσ.le
  have hsub : segment ℝ (Zp (e : ℝ) (f : ℝ) x j0 k)
      (lpG (e : ℝ) (f : ℝ) 1 x ((k : ℝ) * ((e : ℝ) / f) + t * ((q : ℝ) - (k : ℝ) * ((e : ℝ) / f)))
        ((j0 : ℝ) + 1)) ⊆ segment ℝ (lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1))
          (lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1)) := by
    rcases hcl with hss | hsub
    · exact absurd hss (row_not_subsingleton (e : ℝ) (f : ℝ) 1 x ((j0 : ℝ) + 1) he0 hef hε hqpos hk0 hkσ ht)
    · exact hsub
  have hE'mem := hsub (right_mem_segment ℝ _ _)
  have hfkk : GHG (f : ℝ) ((D.tile ed.1).pts kk) = LV := by rw [hkk]; exact hfP
  have hfmm : GHG (f : ℝ) ((D.tile ed.1).pts mm) = LV := by rw [hmm]; exact GHG_lp _ _ _ _ _ _
  have hda := hall ed.1 kk mm hkm hfkk hfmm hle (by rw [hkk]; exact hPmem) (by rw [hmm]; exact hE'mem)
  have hρge : (k : ℝ) * ((e : ℝ) / f) ≤ (k : ℝ) * ((e : ℝ) / f) + t * ((q : ℝ) - (k : ℝ) * ((e : ℝ) / f)) := by
    nlinarith [mul_pos ht hqk]
  have hdd : dist ((D.tile ed.1).pts kk) ((D.tile ed.1).pts mm)
      = (t * ((q : ℝ) - (k : ℝ) * ((e : ℝ) / f))) * (f : ℝ) ^ 2 := by
    rw [hkk, hmm, dist_rowG he0 hef hε hρge]; ring
  have hρeq : t * ((q : ℝ) - (k : ℝ) * ((e : ℝ) / f)) = (e : ℝ) / f := by
    have h1 : (t * ((q : ℝ) - (k : ℝ) * ((e : ℝ) / f))) * (f : ℝ) ^ 2 = ((e : ℝ) / f) * (f : ℝ) ^ 2 := by
      rw [← hdd, hda, hσf]
    exact mul_right_cancel₀ (pow_pos hf0 2).ne' h1
  have hZ1 : Zp (e : ℝ) (f : ℝ) x j0 (k + 1)
      = lpG (e : ℝ) (f : ℝ) 1 x ((k : ℝ) * ((e : ℝ) / f) + t * ((q : ℝ) - (k : ℝ) * ((e : ℝ) / f)))
          ((j0 : ℝ) + 1) :=
    lpG_congr (by rw [hρeq]; push_cast; ring) rfl
  have hmmZ : (D.tile ed.1).pts mm = Zp (e : ℝ) (f : ℝ) x j0 (k + 1) := by rw [hmm, hZ1]
  exact ⟨ed.1, kk, mm, hkm, hkk, hmmZ, hle, hda⟩

/-- **THE TILE ABOVE `Λ` AT `Z_k`** (paper: "the `f` tiles above `Λ` have an `a`-edge on it, so they are of type `A_1` or `A_2`"): the edge of `a_edge` is `[Z_k, Z_{k+1}]`, and its tile is `A_1` or `A_2` (`sides_of_a_edgeG`). -/
theorem a_step (W : StepCtxO D e f α β γ L ax ay x s j0) {q : ℕ} (hq : q + j0 + 1 = s) (hqe : q = e)
    (hall : RowLenAll D (e : ℝ) (f : ℝ) x j0 q ((e : ℝ) * f)) {k : ℕ} (hk : k < f)
    {P'' : Plane} (hfP'' : GHG (f : ℝ) P'' = LV)
    (hP'' : Zp (e : ℝ) (f : ℝ) x j0 k ∈
      openSegment ℝ P'' (lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1)))
    (hL'' : ∀ ed ∈ D.lineChain (GHG (f : ℝ)) LV,
      ¬ Straddles ((D.tile ed.1).edge ed.2) P'' (Zp (e : ℝ) (f : ℝ) x j0 k)
        (lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1))) :
    ATile D (e : ℝ) (f : ℝ) x j0 k ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2) ∨
    ATile D (e : ℝ) (f : ℝ) x j0 k ((f : ℝ) ^ 2) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
  have S := W.S
  have he0 := S.e0
  have hef := S.hef'
  obtain ⟨tt, kk, mm, hkm, hkk, hmmZ, hle, hda⟩ := a_edge W hq hqe hall hk hfP'' hP'' hL''
  have hfkk : GHG (f : ℝ) ((D.tile tt).pts kk) = LV := by rw [hkk]; exact GHG_lp _ _ _ _ _ _
  have hfmm : GHG (f : ℝ) ((D.tile tt).pts mm) = LV := by rw [hmmZ]; exact GHG_lp _ _ _ _ _ _
  obtain ⟨n, hnk, hnm⟩ := fin3_third kk mm hkm
  have hkn : kk ≠ n := Ne.symm hnk
  have hmn : mm ≠ n := Ne.symm hnm
  have hlt := third_strict (D.tile tt) hkm hkn hmn (GHG (f : ℝ)) (GHG_ne he0 hef) LV hfkk hfmm hle
  have hHV : HasV D tt (Zp (e : ℝ) (f : ℝ) x j0 k) (Zp (e : ℝ) (f : ℝ) x j0 (k + 1))
      ((D.tile tt).pts n) := ⟨kk, mm, n, hkm, hkn, hmn, hkk, hmmZ, rfl⟩
  rcases sides_of_a_edgeG D S.tile S.hM tt hkm hkn hmn hda with ⟨s1, s2⟩ | ⟨s1, s2⟩
  · right
    exact ⟨tt, _, hHV, hlt, hle, by rw [← hkk]; exact s1, by rw [← hmmZ]; exact s2⟩
  · left
    exact ⟨tt, _, hHV, hlt, hle, by rw [← hkk]; exact s1, by rw [← hmmZ]; exact s2⟩

/-- **THE `f` TILES ABOVE `Λ`** (`a^f`): for each `k < f` a tile of type `A_2` or `A_1` with the `a`-edge `[Z_k, Z_{k+1}]`, found from the left, each clamped by the previous one (`clamp_b`) -/
theorem a_chain (W : StepCtxO D e f α β γ L ax ay x s j0) {q : ℕ} (hq : q + j0 + 1 = s) (hqe : q = e)
    (hall : RowLenAll D (e : ℝ) (f : ℝ) x j0 q ((e : ℝ) * f)) :
    ∀ k : ℕ, k < f →
      ATile D (e : ℝ) (f : ℝ) x j0 k ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2) ∨
      ATile D (e : ℝ) (f : ℝ) x j0 k ((f : ℝ) ^ 2) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
  have S := W.S
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have he0 := S.e0
  have hef := S.hef'
  have hf0 := S.f0
  have hq1 : 1 ≤ q := by rw [hqe]; exact S.he
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  have hσ : (0 : ℝ) < (e : ℝ) / f := div_pos he0 hf0
  have hqσ : (q : ℝ) = (f : ℝ) * ((e : ℝ) / f) := by rw [hqe]; field_simp
  obtain ⟨P', hfP', hP', hLeft⟩ := row_clamp_leftO W (ρ := (q : ℝ)) hqpos
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      have hZ0 : Zp (e : ℝ) (f : ℝ) x j0 0 = lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1) :=
        lpG_congr (by simp) rfl
      refine a_step W hq hqe hall hk hfP' ?_ ?_
      · rw [hZ0]; exact hP'
      · rw [hZ0]; exact hLeft
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hprev := ih k' (by omega) (by omega)
      obtain ⟨t, Wp, hHV, hmle⟩ : ∃ (t : Fin N) (Wp : Plane),
          HasV D t (Zp (e : ℝ) (f : ℝ) x j0 k') (Zp (e : ℝ) (f : ℝ) x j0 (k' + 1)) Wp ∧
          ∀ i, GHG (f : ℝ) ((D.tile t).pts i) ≤ LV := by
        rcases hprev with ⟨t, Wp, h1, -, h3, -, -⟩ | ⟨t, Wp, h1, -, h3, -, -⟩ <;>
          exact ⟨t, Wp, h1, h3⟩
      obtain ⟨k1, m1, j1, h12, h13, h23, p1, p2, p3⟩ := hHV
      have hkf : ((k' + 1 : ℕ) : ℝ) < f := by exact_mod_cast hk
      have hk'σ : (k' : ℝ) * ((e : ℝ) / f) < ((k' + 1 : ℕ) : ℝ) * ((e : ℝ) / f) := by
        push_cast; nlinarith
      have hk1σ : ((k' + 1 : ℕ) : ℝ) * ((e : ℝ) / f) < q := by
        rw [hqσ]; exact mul_lt_mul_of_pos_right hkf hσ
      have hmid : Zp (e : ℝ) (f : ℝ) x j0 (k' + 1) ∈
          openSegment ℝ (Zp (e : ℝ) (f : ℝ) x j0 k')
            (lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1)) :=
        lpG_row_mid (e : ℝ) (f : ℝ) 1 x ((j0 : ℝ) + 1) hk'σ hk1σ
      refine a_step W hq hqe hall hk (GHG_lp _ _ _ _ _ _) hmid ?_
      exact clamp_b D.toDissection (GHG (f : ℝ)) (GHG_ne he0 hef) _
        (lpG_ne_xi he0 hef hε hk1σ.ne) (GHG_lp _ _ _ _ _ _) (GHG_lp _ _ _ _ _ _) (GHG_lp _ _ _ _ _ _)
        hmid h12 p1 p2 hmle

/-- the angle `γ` at the right end `Z_{k+1}` of a tile of type `A_1` -/
theorem A1_right_angle (S : SetupG D e f α β γ L ax ay) {k : ℕ}
    (h : ATile D (e : ℝ) (f : ℝ) x j0 k ((f : ℝ) ^ 2) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) :
    ∃ (t : Fin N) (Wp : Plane), HasV D t (Zp (e : ℝ) (f : ℝ) x j0 k) (Zp (e : ℝ) (f : ℝ) x j0 (k + 1)) Wp ∧
      GHG (f : ℝ) Wp < LV ∧ (∀ i, GHG (f : ℝ) ((D.tile t).pts i) ≤ LV) ∧
      (D.tile t).localAngle (Zp (e : ℝ) (f : ℝ) x j0 (k + 1)) = γ := by
  obtain ⟨t, Wp, hHV, hlt, hle, d1, d2⟩ := h
  refine ⟨t, Wp, hHV, hlt, hle, ?_⟩
  obtain ⟨kk, mm, jj, hkm, hkj, hmj, hk, hm, hj⟩ := hHV
  have hA := angle_at_vertexG D S.tile S.hM t hkm.symm hmj hkj
  rw [← hm]
  exact hA.2.2 (by rw [hk, hj, dist_comm]; exact d1)

/-- the angle `γ` at the left end `Z_k` of a tile of type `A_2` -/
theorem A2_left_angle (S : SetupG D e f α β γ L ax ay) {k : ℕ}
    (h : ATile D (e : ℝ) (f : ℝ) x j0 k ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) :
    ∃ (t : Fin N) (Wp : Plane), HasV D t (Zp (e : ℝ) (f : ℝ) x j0 k) (Zp (e : ℝ) (f : ℝ) x j0 (k + 1)) Wp ∧
      GHG (f : ℝ) Wp < LV ∧ (∀ i, GHG (f : ℝ) ((D.tile t).pts i) ≤ LV) ∧
      (D.tile t).localAngle (Zp (e : ℝ) (f : ℝ) x j0 k) = γ := by
  obtain ⟨t, Wp, hHV, hlt, hle, d1, d2⟩ := h
  refine ⟨t, Wp, hHV, hlt, hle, ?_⟩
  obtain ⟨kk, mm, jj, hkm, hkj, hmj, hk, hm, hj⟩ := hHV
  have hA := angle_at_vertexG D S.tile S.hM t hkm hkj hmj
  rw [← hk]
  exact hA.2.2 (by rw [hm, hj, dist_comm]; exact d2)

/-- **AN `A_1` FOLLOWED BY AN `A_2` IS IMPOSSIBLE** (paper: "an `A_1` followed by an `A_2` would show two `γ` at a point of `Λ`, where the tiles above `Λ` fill a straight angle"): at `Z_{k+1}`, an interior point of the `c`-edge of a tile
`D(i, j0)` below `Λ` (`(k+1) e / f` is not an integer, `0 < k + 1 < f`), the tile `D(i, j0)` has the angle `π`, so `π + γ + γ ≤ 2π`, against `2γ > π`.  (Conclusion `False`.) -/
theorem a_two_false (W : StepCtxO D e f α β γ L ax ay x s j0) {q : ℕ} (hq : q + j0 + 1 = s) (hqe : q = e)
    {k : ℕ} (hk : k + 2 ≤ f)
    (h1 : ATile D (e : ℝ) (f : ℝ) x j0 k ((f : ℝ) ^ 2) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
    (h2 : ATile D (e : ℝ) (f : ℝ) x j0 (k + 1) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) : False := by
  have S := W.S
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have he0 := S.e0
  have hef := S.hef'
  have hf0 := S.f0
  have hσ : (0 : ℝ) < (e : ℝ) / f := div_pos he0 hf0
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  obtain ⟨t1, W1, hHV1, hlt1, hle1, hang1⟩ := A1_right_angle S h1
  obtain ⟨t2, W2, hHV2, hlt2, hle2, hang2⟩ := A2_left_angle S h2
  -- the position `ρ = (k+1) e / f` of the common vertex and the tile `D(i, j0)` below
  have hkf : ((k + 1 : ℕ) : ℝ) < f := by exact_mod_cast (by omega : k + 1 < f)
  have hk1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hρ0 : 0 ≤ ((k + 1 : ℕ) : ℝ) * ((e : ℝ) / f) := by positivity
  have hρe : ((k + 1 : ℕ) : ℝ) * ((e : ℝ) / f) < e := by
    have := mul_lt_mul_of_pos_right hkf hσ
    have h' : (f : ℝ) * ((e : ℝ) / f) = e := by field_simp
    linarith
  obtain ⟨i, hi⟩ : ∃ i : ℕ, i = ⌊((k + 1 : ℕ) : ℝ) * ((e : ℝ) / f)⌋₊ := ⟨_, rfl⟩
  have hile : (i : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * ((e : ℝ) / f) := by rw [hi]; exact Nat.floor_le hρ0
  have hilt : ((k + 1 : ℕ) : ℝ) * ((e : ℝ) / f) < (i : ℝ) + 1 := by rw [hi]; exact Nat.lt_floor_add_one _
  have hine : (i : ℝ) ≠ ((k + 1 : ℕ) : ℝ) * ((e : ℝ) / f) := by
    intro hieq
    have h3 : (i : ℝ) * f = ((k + 1 : ℕ) : ℝ) * e := by rw [hieq]; field_simp
    have h4 : i * f = (k + 1) * e := by exact_mod_cast h3
    have h5 : f ∣ (k + 1) * e := ⟨i, by rw [← h4]; ring⟩
    have h6 : f ∣ k + 1 := Nat.Coprime.dvd_of_dvd_mul_right S.hco.symm h5
    have h7 := Nat.le_of_dvd (by omega) h6
    omega
  have hipos : (i : ℝ) < ((k + 1 : ℕ) : ℝ) * ((e : ℝ) / f) := lt_of_le_of_ne hile hine
  have hie : i < e := by
    have : (i : ℝ) < e := by linarith
    exact_mod_cast this
  obtain ⟨tD, hD⟩ := W.hA i (by omega)
  have hZmem : Zp (e : ℝ) (f : ℝ) x j0 (k + 1) ∈ openSegment ℝ
      (lpG (e : ℝ) (f : ℝ) 1 x (i : ℝ) ((j0 : ℝ) + 1))
      (lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) ((j0 : ℝ) + 1)) :=
    lpG_row_mid (e : ℝ) (f : ℝ) 1 x ((j0 : ℝ) + 1) hipos hilt
  have hDangle := hasV_localAngle_pi hD hZmem
  -- the three tiles are distinct
  obtain ⟨kd, hkd⟩ := hD.idx₁
  have hDgt : LV < GHG (f : ℝ) ((D.tile tD).pts kd) := by
    rw [hkd]; exact GHG_gt he0 hef (by linarith)
  have n1 : t1 ≠ tD := ne_of_F (GHG (f : ℝ)) hle1 hDgt
  have n2 : t2 ≠ tD := ne_of_F (GHG (f : ℝ)) hle2 hDgt
  have n12 : t1 ≠ t2 := by
    obtain ⟨m2, hm2⟩ := hHV2.idx₂
    refine (HasV.ne_of_vertex hHV1 hm2 ?_ ?_ ?_).symm
    · exact lpG_ne_xi he0 hef hε (by
        intro h; have := mul_right_cancel₀ hσ.ne' h; have h' : k + 1 + 1 = k := by exact_mod_cast this
        omega)
    · exact lpG_ne_xi he0 hef hε (by
        intro h; have := mul_right_cancel₀ hσ.ne' h; have h' : k + 1 + 1 = k + 1 := by exact_mod_cast this
        omega)
    · intro h
      have h' := hlt1
      rw [← h] at h'
      rw [GHG_lp] at h'
      exact lt_irrefl _ h'
  have h3 := three_angles_le D.toDissection (Zp (e : ℝ) (f : ℝ) x j0 (k + 1)) n1.symm n2.symm n12
  rw [hDangle, hang1, hang2] at h3
  -- the first term of `h3` is `tD`, then `t1`, `t2`
  have h4 := localAngle_le_two_pi D.target (Zp (e : ℝ) (f : ℝ) x j0 (k + 1))
  linarith

/-- **ALL THE TILES ABOVE `Λ` ARE OF TYPE `A_2`** (paper: "the last one shows `β` at `p(e,1)`, so it is `A_2`; an `A_1` followed by an `A_2` would show two `γ` ...; so all are `A_2`"). -/
theorem a_all_A2 (W : StepCtxO D e f α β γ L ax ay x s j0) {q : ℕ} (hq : q + j0 + 1 = s) (hqe : q = e)
    (hall : RowLenAll D (e : ℝ) (f : ℝ) x j0 q ((e : ℝ) * f)) :
    ∀ d k : ℕ, k + 1 + d = f →
      ATile D (e : ℝ) (f : ℝ) x j0 k ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2) := by
  have S := W.S
  intro d
  induction d with
  | zero =>
    intro k hk
    rcases a_chain W hq hqe hall k (by omega) with hA2 | hA1
    · exact hA2
    · exfalso
      obtain ⟨t, Wp, hHV, -, hle, hang⟩ := A1_right_angle S hA1
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by have := S.he; omega⟩
      have hkf : ((k + 1 : ℕ) : ℝ) = (f : ℝ) := by exact_mod_cast (by omega : k + 1 = f)
      have hZ : Zp (e : ℝ) (f : ℝ) x j0 (k + 1)
          = lpG (e : ℝ) (f : ℝ) 1 x ((q' : ℝ) + 1) ((j0 : ℝ) + 1) := by
        refine lpG_congr ?_ rfl
        rw [hkf]
        have hqe' : ((q' : ℝ) + 1) = e := by exact_mod_cast hqe
        rw [hqe']
        have hf0' : (f : ℝ) ≠ 0 := S.f0.ne'
        field_simp
      exact right_end_ang W hq (Or.inr rfl) hle (by rw [← hZ]; exact hang)
  | succ d ih =>
    intro k hk
    rcases a_chain W hq hqe hall k (by omega) with hA2 | hA1
    · exact hA2
    · exfalso
      exact a_two_false W hq hqe (k := k) (by omega) hA1 (ih (k + 1) (by omega))

end chainO

/-! ## 2. The geometry of the first tile -/

section geom

variable {e f : ℕ} {α β γ L ax ay : ℝ}

/-- **THE FIRST TILE `Y` ABOVE `Λ` LEAVES Δ** (paper: "Since `b > a`, `V` is in the relative interior of the `b`-edge of `Y`.  But `V` lies on the second side of Δ at `P` ... so the `b`-edge of `Y` leaves Δ at `V`: a contradiction"):
at the corner `A' = (0,0)` of angle `2α` (the apex `(ax, ay) = t (X2, Y2)`), `x = 0`, `j0 = 0`, `Q = p(0,1)`, `Z_1 = Q + (a, 0)`, a point `W` above the row with `|WQ| = b` and `|WZ_1| = c` is
`Q + (−e b / 2f, b √(4f² − e²) / 2f)`; the form `g_A (p) = ay p_0 − ax p_1` of the side `A'A` has the value `t b √(4f²−e²) f (a − b)` there, which is `< 0` when `a < b`, so `W` is not in Δ. (Conclusion `False`.) -/
theorem a_geom (S : SetupG D e f α β γ L ax ay)
    (hab : (e : ℝ) * f < (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (hA2 : ∃ t : ℝ, 0 < t ∧ ax = t * ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - 2 * (f : ℝ) ^ 4) ∧
      ay = t * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) * rtG (e : ℝ) (f : ℝ)))
    {tY : Fin N} {Wp : Plane}
    (hY : HasV D tY (Zp (e : ℝ) (f : ℝ) 0 0 0) (Zp (e : ℝ) (f : ℝ) 0 0 1) Wp)
    (hlt : GHG (f : ℝ) Wp < -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * (((0 : ℕ) : ℝ) + 1)))
    (dQ : dist Wp (Zp (e : ℝ) (f : ℝ) 0 0 0) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (dZ : dist Wp (Zp (e : ℝ) (f : ℝ) 0 0 1) = (f : ℝ) ^ 2) : False := by
  obtain ⟨t, ht, hax, hay'⟩ := hA2
  have he0 := S.e0
  have hef := S.hef'
  have hf0 := S.f0
  have hb := S.b_pos
  have hr0 := rtG_pos he0 hef
  have hr2 := rtG_sq he0 hef
  have hf0' : (f : ℝ) ≠ 0 := hf0.ne'
  -- the coordinates of `Q` and `Z_1`
  have hQ : Zp (e : ℝ) (f : ℝ) 0 0 0 = mkPt ((f : ℝ) ^ 2 - uuG (e : ℝ) (f : ℝ)) (hhG (e : ℝ) (f : ℝ)) := by
    unfold Zp lpG
    exact mkPt_congr (by push_cast; ring) (by push_cast; ring)
  have hZ : Zp (e : ℝ) (f : ℝ) 0 0 1
      = mkPt ((f : ℝ) ^ 2 - uuG (e : ℝ) (f : ℝ) + (e : ℝ) * f) (hhG (e : ℝ) (f : ℝ)) := by
    unfold Zp lpG
    exact mkPt_congr (by push_cast; field_simp; ring) (by push_cast; ring)
  have hW : Wp = mkPt (Wp 0) (Wp 1) := plane_ext (by simp) (by simp)
  have E1 := dist_sq_mkPt (Wp 0) (Wp 1) ((f : ℝ) ^ 2 - uuG (e : ℝ) (f : ℝ)) (hhG (e : ℝ) (f : ℝ))
  rw [← hW, ← hQ, dQ] at E1
  have E2 := dist_sq_mkPt (Wp 0) (Wp 1) ((f : ℝ) ^ 2 - uuG (e : ℝ) (f : ℝ) + (e : ℝ) * f) (hhG (e : ℝ) (f : ℝ))
  rw [← hW, ← hZ, dZ] at E2
  -- solve
  obtain ⟨X, hXdef⟩ : ∃ X, X = Wp 0 := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = Wp 1 := ⟨_, rfl⟩
  rw [← hXdef, ← hYdef] at E1 E2
  obtain ⟨qx, hqx⟩ : ∃ qx, qx = (f : ℝ) ^ 2 - uuG (e : ℝ) (f : ℝ) := ⟨_, rfl⟩
  obtain ⟨qy, hqy⟩ : ∃ qy, qy = hhG (e : ℝ) (f : ℝ) := ⟨_, rfl⟩
  rw [← hqx, ← hqy] at E1 E2
  have hx : 2 * (e : ℝ) * f * (X - qx) = -((e : ℝ) ^ 2 * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := by
    linear_combination E2 - E1
  have hx' : (X - qx) * (2 * f) = -((e : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := by
    apply mul_left_cancel₀ he0.ne'
    linear_combination hx
  -- the height
  have hy2 : (2 * (f : ℝ) * (Y - qy)) ^ 2 = (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * rtG (e : ℝ) (f : ℝ)) ^ 2 := by
    linear_combination (-(4 * (f : ℝ) ^ 2)) * E1
      - (2 * f * (X - qx) - e * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) * hx'
      - ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 * hr2
  have hYgt : qy < Y := by
    have h1 := hlt
    rw [GHG_apply, ← hYdef] at h1
    have hz : ((0 : ℕ) : ℝ) = 0 := Nat.cast_zero
    rw [hz] at h1
    have h2 : (f : ℝ) ^ 2 * qy < (f : ℝ) ^ 2 * Y := by
      rw [hqy]
      linarith [h1]
    exact lt_of_mul_lt_mul_left h2 (pow_pos hf0 2).le
  have hy : 2 * (f : ℝ) * (Y - qy) = ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * rtG (e : ℝ) (f : ℝ) := by
    have hu : 0 < 2 * (f : ℝ) * (Y - qy) := mul_pos (mul_pos two_pos hf0) (sub_pos.mpr hYgt)
    have hv : 0 < ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * rtG (e : ℝ) (f : ℝ) := mul_pos hb hr0
    have h0 : (2 * (f : ℝ) * (Y - qy) - ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * rtG (e : ℝ) (f : ℝ)) *
        (2 * (f : ℝ) * (Y - qy) + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * rtG (e : ℝ) (f : ℝ)) = 0 := by
      linear_combination hy2
    rcases mul_eq_zero.mp h0 with h | h
    · linarith
    · linarith
  -- the value of the form of the side `A'A`
  have hWmem : Wp ∈ D.target.carrier := hY.mem₃
  have hpos := (S.mem hWmem).2.1
  unfold gA at hpos
  rw [← hXdef, ← hYdef] at hpos
  have h2f : (2 * (f : ℝ)) ≠ 0 := (mul_pos two_pos hf0).ne'
  have hdx : X - qx = -((e : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) / (2 * f) := by
    rw [eq_div_iff h2f]; exact hx'
  have hdy : Y - qy = ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * rtG (e : ℝ) (f : ℝ) / (2 * f) := by
    rw [eq_div_iff h2f]; linarith [hy]
  have hXe : X = qx + -((e : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) / (2 * f) := by linarith [hdx]
  have hYe : Y = qy + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * rtG (e : ℝ) (f : ℝ) / (2 * f) := by linarith [hdy]
  have hval : ay * X - ax * Y
      = t * (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * rtG (e : ℝ) (f : ℝ) * f * ((e : ℝ) * f - ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))) := by
    rw [hXe, hYe, hax, hay', hqx, hqy]
    unfold uuG hhG
    field_simp
    ring
  rw [hval] at hpos
  have hneg : (e : ℝ) * f - ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) < 0 := by linarith
  have : t * (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * rtG (e : ℝ) (f : ℝ) * f * ((e : ℝ) * f - ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))) < 0 :=
    mul_neg_of_pos_of_neg ht (mul_neg_of_pos_of_neg (by positivity) hneg)
  linarith

end geom

/-! ## 3. `M°(e+1)` -/

section mo

variable {e f : ℕ} {α β γ L ax ay : ℝ}

/-- **THE CASE `a^f` OF `M°(e+1)`** (the conditions (M1), (K2), (K3) at `(e + 1, 0)` with step (a) and all edges of `Λ` equal to `a`): the first tile is of type `A_2` (`a_all_A2`) and leaves Δ (`a_geom`).  (Conclusion `False`.) -/
theorem aF_false (S : SetupG D e f α β γ L ax ay) (W : StepCtxO D e f α β γ L ax ay 0 (e + 1) 0)
    (hab : (e : ℝ) * f < (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (hA2 : ∃ t : ℝ, 0 < t ∧ ax = t * ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - 2 * (f : ℝ) ^ 4) ∧
      ay = t * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) * rtG (e : ℝ) (f : ℝ)))
    (hall : RowLenAll D (e : ℝ) (f : ℝ) 0 0 e ((e : ℝ) * f)) : False := by
  have hq : e + 0 + 1 = e + 1 := rfl
  have h0 := a_all_A2 W (q := e) hq rfl hall (f - 1) 0 (by have := S.hef; omega)
  obtain ⟨t, Wp, hY, hlt, -, dQ, dZ⟩ := h0
  exact a_geom S hab hA2 hY hlt dQ dZ

/-- **`M°(e+1)`, WITH THE COORDINATES OF THE CORNER**: let `a < b`, `e + 1 < f`, the target a triangle with the corner `A' = (0, 0)` of angle `2α` (the apex `(ax, ay)` is `t ((2f²−e²)² − 2f⁴, e (2f²−e²) √(4f²−e²))`), the chords from `A'` along `ℓ`
interior (`ChordsAt`).  Then (M1) the mirror image of `U(0,0)` in `ℓ` is a tile (`MirrorAt`), (K2) the row `0` of `Δ_{e+1}` is lattice (`K2G`) and (K3) the side `ρ_{e+1}` is outside Δ or a tile has an edge `b` or `c` on `m_{e+1}`
from a clamped point (`K3G`) cannot hold together.  (Conclusion `False`.) -/
theorem MO_main (S : SetupG D e f α β γ L ax ay) (hab : (e : ℝ) * f < (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (hA2 : ∃ t : ℝ, 0 < t ∧ ax = t * ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - 2 * (f : ℝ) ^ 4) ∧
      ay = t * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) * rtG (e : ℝ) (f : ℝ)))
    (hef2 : e + 1 < f) (hch : ChordsAt D (e : ℝ) (f : ℝ) 1 0)
    (hM : MirrorAt D (e : ℝ) (f : ℝ) 1 0 ((0 : ℕ) : ℝ))
    (hK2 : K2G D (e : ℝ) (f : ℝ) 1 0 (e + 1) 0)
    (hK3 : K3G D (e : ℝ) (f : ℝ) 1 0 ((e + 1 : ℕ) : ℝ) ((0 : ℕ) : ℝ)) : False := by
  have IH : ∀ m, 1 ≤ m → m < e + 1 - 0 → MGh D e f 1 m := fun m h1 _ => MG_all S m h1
  have hA := stepAO S hch hM hK2 hK3 hef2 (by omega) IH
  have he1 := S.he
  have W : StepCtxO D e f α β γ L ax ay 0 (e + 1) 0 :=
    ⟨S, hch, hM, hK2, hK3, hef2, by omega, by omega, IH, hA⟩
  have hq : e + 0 + 1 = e + 1 := rfl
  rcases lambda_dich W (q := e) hq rfl with hc | ha
  · exact cE_false W (q := e) hq he1 hc
  · exact aF_false S W hab hA2 ha

/-- the coordinates of the apex from the angle `2α` at `A'` (the second form of `CornersA` gives `3α`) -/
theorem cornersA_two_of_angle (S : SetupG D e f α β γ L ax ay) (Co : CornersA e f L ax ay)
    (h : D.target.localAngle (mkPt 0 0) = 2 * α) :
    ∃ t : ℝ, 0 < t ∧ ax = t * ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - 2 * (f : ℝ) ^ 4) ∧
      ay = t * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) * rtG (e : ℝ) (f : ℝ)) := by
  rcases Co.hA with ⟨t, ht, hax, hay'⟩ | ⟨t, ht, hax, hay'⟩
  · exact ⟨t, ht, hax, hay'⟩
  · exfalso
    have h3 := corner_left_three S ht hax hay'
    have hα := S.hA.hα
    linarith

/-- **`M°(e+1)` AS THE PAPER STATES IT**: `a < b`, `e + 1 < f` (`e + 1 ≤ f − 1`), `P = A'` a corner of Δ of angle `2α`; (M1), (K2), (K3) for `(s', j0) = (e + 1, 0)` cannot hold together.  (Conclusion `False`.) -/
theorem MO_corner (S : SetupG D e f α β γ L ax ay) (Co : CornersA e f L ax ay)
    (hab : (e : ℝ) * f < (f : ℝ) ^ 2 - (e : ℝ) ^ 2) (hef2 : e + 1 < f)
    (h2 : D.target.localAngle (mkPt 0 0) = 2 * α) (hch : ChordsAt D (e : ℝ) (f : ℝ) 1 0)
    (hM : MirrorAt D (e : ℝ) (f : ℝ) 1 0 ((0 : ℕ) : ℝ))
    (hK2 : K2G D (e : ℝ) (f : ℝ) 1 0 (e + 1) 0)
    (hK3 : K3G D (e : ℝ) (f : ℝ) 1 0 ((e + 1 : ℕ) : ℝ) ((0 : ℕ) : ℝ)) : False :=
  MO_main S hab (cornersA_two_of_angle S Co h2) hef2 hch hM hK2 hK3

section runO

variable {m : ℕ} {X : ℕ → ℝ} {tile : ℕ → Fin N} {τ : ℕ → Ty}

/-- the data of a run of `k` tiles `C1` from the corner `A'` that `M` consumes (copied from `corner_run_short`): the chords, the mirror tile (`corner_run_mirror`), (K2) for `(k, 0)`, (K3) at the right end -/
theorem corner_run_data (S : SetupG D e f α β γ L ax ay) (Co : CornersA e f L ax ay)
    (Ch : ChainG D e f L m X tile τ) {k : ℕ} (hk1 : 1 ≤ k) (hkf : k < f)
    (hrun : ∀ j, j < k → τ j = Ty.C1)
    (hsucc : k = m ∨ (k < m ∧ τ k ≠ Ty.B1 ∧ τ k ≠ Ty.C1)) :
    ChordsAt D (e : ℝ) (f : ℝ) 1 0 ∧ MirrorAt D (e : ℝ) (f : ℝ) 1 0 ((0 : ℕ) : ℝ) ∧
      K2G D (e : ℝ) (f : ℝ) 1 0 k 0 ∧ K3G D (e : ℝ) (f : ℝ) 1 0 (k : ℝ) ((0 : ℕ) : ℝ) := by
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
  refine ⟨hch, ?_, ?_, ?_⟩
  · rw [Nat.cast_zero]; exact hM
  · refine ⟨fun i j hj hij => ?_, fun i j hj _ => absurd hj (Nat.not_lt_zero _)⟩
    obtain rfl : j = 0 := by omega
    rw [Nat.cast_zero]
    exact hUT i (by omega)
  · rw [Nat.cast_zero]; exact hK3

/-- **A RUN OF `C1` FROM A CORNER `2α` OF LENGTH `k ≤ e + 1` IS IMPOSSIBLE WHEN `a < b`** (the addendum of `thm:cornerrun`: "if `a < b` and `A'` has the angle `2α`, then `k ≥ e + 2` in (ii)"): for `k ≤ e` this is
`corner_run_short`; for `k = e + 1` the run gives (M1), (K2), (K3) for `(e + 1, 0)` (`corner_run_data`), against `MO_corner`.  (Conclusion `False`.) -/
theorem corner_run_short_o (S : SetupG D e f α β γ L ax ay) (Co : CornersA e f L ax ay)
    (hab : (e : ℝ) * f < (f : ℝ) ^ 2 - (e : ℝ) ^ 2) (hef2 : e + 1 < f)
    (h2 : D.target.localAngle (mkPt 0 0) = 2 * α)
    (Ch : ChainG D e f L m X tile τ) {k : ℕ} (hk1 : 1 ≤ k) (hke : k ≤ e + 1)
    (hrun : ∀ j, j < k → τ j = Ty.C1)
    (hsucc : k = m ∨ (k < m ∧ τ k ≠ Ty.B1 ∧ τ k ≠ Ty.C1)) : False := by
  rcases Nat.lt_or_ge e k with h | h
  · obtain rfl : k = e + 1 := by omega
    obtain ⟨hch, hM, hK2, hK3⟩ := corner_run_data S Co Ch hk1 hef2 hrun hsucc
    exact MO_corner S Co hab hef2 h2 hch hM hK2 hK3
  · exact corner_run_short S Co Ch hk1 h hrun hsucc

end runO

end mo

end Erdos634.Draft.SideRunGA

#print axioms Erdos634.Draft.SideRunGA.lpG_seg_mem
#print axioms Erdos634.Draft.SideRunGA.lpG_row_sub
#print axioms Erdos634.Draft.SideRunGA.hasV_localAngle_pi
#print axioms Erdos634.Draft.SideRunGA.a_step
#print axioms Erdos634.Draft.SideRunGA.a_chain
#print axioms Erdos634.Draft.SideRunGA.A1_right_angle
#print axioms Erdos634.Draft.SideRunGA.A2_left_angle
#print axioms Erdos634.Draft.SideRunGA.a_two_false
#print axioms Erdos634.Draft.SideRunGA.a_all_A2
#print axioms Erdos634.Draft.SideRunGA.a_geom
#print axioms Erdos634.Draft.SideRunGA.aF_false
#print axioms Erdos634.Draft.SideRunGA.MO_main
#print axioms Erdos634.Draft.SideRunGA.cornersA_two_of_angle
#print axioms Erdos634.Draft.SideRunGA.MO_corner
#print axioms Erdos634.Draft.SideRunGA.corner_run_data
#print axioms Erdos634.Draft.SideRunGA.corner_run_short_o
