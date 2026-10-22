/-
Draft/SideRunGMStepB.lean -- written 14 October 2026.  UNAUDITED.  In `AllThreshold`.  Module M3 of the plan for
`thm:cornerrun` (M1 `Draft/SideRunGMirror.lean`, M2 `Draft/SideRunGMStep.lean`; step (c), `MG_all` and the corollary are in `Draft/SideRunGMStepC.lean`).

**The induction for `M(s', j0)`: STEP (b), the row `Λ = [p(0, j0+1), p(n−1, j0+1)]` above the tiles `D(i, j0)`.**  Paper: Theorem `thm:cornerrun`, "Proof of `M(s', j0)`,
size `n ≥ 2`", step (b); (private working notes, not included) Section 4.

CONTENTS.
0. `StepCtx`: the standing hypotheses of the induction step for the pair `(s, j0)` of size `n = s − j0 ≥ 2` (the setup, interior chords at the origin, the mirror tile (M1), (K2),
   (K3), `M` for the smaller sizes, and step (a): the tiles `D(i, j0)`).  Small tools: `lpG_row_mid`, `no_a_row` (the arithmetic fact "since `n − 1 < e`, all the edges of
   `Λ` are `c`", `ec = fa`), `target_angle_sum`, `not_interior_of_out`, `out_corner_B`.
1. The clamps of `Λ`: `row_clamp_left` (the left end: "the direction `d(π)` is interior to `T`", `mirror_row_left`), `row_clamp_right` (the right end: the `m`-chord principle, `CtxBase.K3G_clamp_row`),
   and `lambda_edges` (**by (P) and Lemma A5 the edges above `Λ` have the length `c`**: `run_partition`, `SideRunGArith.A5`, `no_a_row`).
2. The tiles above `Λ`: `VEx`, `VBad`, `row_tiles` (**above each segment `[p(r, j0+1), p(r+1, j0+1)]` lies a tile `V_r` with `α` and `β` at its ends: it is `U(r, j0+1)` or it shows `β` at the
   left end and `α` at the right end**: `CtxBase.row_stepG`).
3. The right end: `right_end_false` (**`V_{n−2}` shows `β` at `p(n−1, j0+1)`**: the tiles `D(n−2, j0)` (`α`), `U(n−1, j0)` (`γ`) and `ψ` leave the wedge `(π−β, π)`, or `ρ_{s'}` is outside
   Δ; the vertex figures `fig_int`, `fig_bdry` and the corner `B` of angle `β`).

CORRESPONDENCE with the paper's step (b): "Λ is the union of the `c`-edges of the tiles `D(i, j0)`" is `hD`/`hwall`/`hint` in `lambda_edges` (as in `CtxJ.rowJ`); "Its left end is clamped (the direction `d(π)` is interior
to `T`), its right end by the `m`-chord principle" is `row_clamp_left`, `row_clamp_right`; "By (P) and Lemma A5 the edges above `Λ` partition it into lengths `a` and `c`; since `n − 1 < e` ... all of them are `c`" is
`lambda_edges`; "above each segment lies a tile `V_r` with `α` and `β` at its ends" is `row_tiles`; "At `p(n−1, j0+1)` the tiles `D(n−2, j0)`, `U(n−1, j0)` and `ψ` leave the wedge `(π−β, π)`: `V_{n−2}` shows `β` there" is
`right_end_false`.  The downward induction on `r` (the tile `E`) is in `Draft/SideRunGMStepC.lean`.

WHAT THE PAPER LEAVES TO THE READER (found while writing it).  (1) "The same wedge is left when (K3) holds in its corner form ... it is not the third corner of Δ": in `K3G` the first form is only "`ρ_{s'}` is outside Δ"
(not the corner of angle `β`); `out_corner_B` derives the corner `B = p(s, 0)` and its angle `≥ β` from (K2) and the first form, and `right_end_false` excludes the third corner by the angle sum `π`.
(2) The partition of `Λ` gives the edges as a multiset; the tiles `V_r` at the lattice points come from the first edge at each point (`row_stepG`, clamped by the previous tile), not from the counting alone.

WITNESSES.  As in `Draft/SideRunGMStep.lean`: the statements conclude `False` or the existence of tiles under the hypotheses of the induction.

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGMStep

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

/-! ## 0. The standing hypotheses; small tools -/

/-- **the standing hypotheses of the induction step** for the pair `(s, j0)` of size `n = s − j0 ≥ 2` (the lattice has the origin `x`, `ε = 1`) -/
structure StepCtx (D : CongruentDissection N) (e f : ℕ) (α β γ L ax ay x : ℝ) (s j0 : ℕ) : Prop where
  S : SetupG D e f α β γ L ax ay
  hch : ChordsAt D (e : ℝ) (f : ℝ) 1 x
  hM : MirrorAt D (e : ℝ) (f : ℝ) 1 x (j0 : ℝ)
  hK2 : K2G D (e : ℝ) (f : ℝ) 1 x s j0
  hK3 : K3G D (e : ℝ) (f : ℝ) 1 x (s : ℝ) (j0 : ℝ)
  hsf : s < f
  hne : s - j0 ≤ e
  hn2 : 2 ≤ s - j0
  IH : ∀ m, 1 ≤ m → m < s - j0 → MGh D e f 1 m
  hA : ∀ i, i + 2 ≤ s - j0 → DTG D (e : ℝ) (f : ℝ) 1 x i j0

section tools

variable {e f : ℕ} {α β γ L ax ay ε x : ℝ}

theorem lpG_row_mid (e f ε x η : ℝ) {a b c : ℝ} (h1 : a < b) (h2 : b < c) :
    lpG e f ε x b η ∈ openSegment ℝ (lpG e f ε x a η) (lpG e f ε x c η) := by
  have hd : 0 < c - a := by linarith
  have hne : c - a ≠ 0 := hd.ne'
  have hab : (c - b) / (c - a) + (b - a) / (c - a) = 1 := by
    rw [← add_div, show c - b + (b - a) = c - a by ring]
    exact div_self hne
  refine ⟨(c - b) / (c - a), (b - a) / (c - a), div_pos (by linarith) hd, div_pos (by linarith) hd,
    hab, ?_⟩
  unfold lpG
  apply plane_ext
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mkPt_zero]
    field_simp
    ring
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mkPt_one]
    linear_combination (η * hhG e f) * hab

/-- a row of `q < e` lattice edges `c` cannot be cut with an edge `a` (`e c = f a`) -/
theorem no_a_row {e f q x z : ℕ} (hco : Nat.Coprime e f) (hf : 0 < f) (hq : q < e) (hx : 1 ≤ x)
    (h : x * (e * f) + z * f ^ 2 = q * f ^ 2) : False := by
  have h1 : x * e + z * f = q * f := by
    apply Nat.eq_of_mul_eq_mul_left hf
    calc f * (x * e + z * f) = x * (e * f) + z * f ^ 2 := by ring
      _ = q * f ^ 2 := h
      _ = f * (q * f) := by ring
  have hd : f ∣ x * e := by
    have h2 : (f : ℤ) ∣ ((x * e : ℕ) : ℤ) := ⟨(q : ℤ) - z, by
      have h1' := congrArg (Nat.cast : ℕ → ℤ) h1
      push_cast at h1' ⊢
      linear_combination h1'⟩
    exact_mod_cast h2
  have hdx : f ∣ x := Nat.Coprime.dvd_of_dvd_mul_right hco.symm hd
  have hfx : f ≤ x := Nat.le_of_dvd (by omega) hdx
  nlinarith [Nat.mul_le_mul_right e hfx, hq, hf, h1]

/-- the three corner angles of a triangle sum to `π` -/
theorem target_angle_sum (T : Erdos634.Geometry.Tri) :
    T.localAngle (T.pts 0) + T.localAngle (T.pts 1) + T.localAngle (T.pts 2) = Real.pi := by
  have h0 := Tri.localAngle_vertex T 0
  have h1 := Tri.localAngle_vertex T 1
  have h2 := Tri.localAngle_vertex T 2
  rw [show ((0 : Fin 3) + 1) = 1 by decide, show ((0 : Fin 3) + 2) = 2 by decide] at h0
  rw [show ((1 : Fin 3) + 1) = 2 by decide, show ((1 : Fin 3) + 2) = 0 by decide] at h1
  rw [show ((2 : Fin 3) + 1) = 0 by decide, show ((2 : Fin 3) + 2) = 1 by decide] at h2
  rw [h0, h1, h2]
  exact cornerAngle_sum T

/-- a point of Δ on a line `{GS = c}` such that all of Δ lies in `{GS ≥ c}` is not an interior point -/
theorem not_interior_of_out {R v : Plane} {c : ℝ} (hv : GSG (e : ℝ) (f : ℝ) ε v < 0)
    (hR : GSG (e : ℝ) (f : ℝ) ε R = c)
    (hout : ∀ q ∈ D.target.carrier, c ≤ GSG (e : ℝ) (f : ℝ) ε q) :
    R ∉ interior D.target.carrier := by
  intro h
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior R h
  have hn : 0 < ‖v‖ + 1 := by positivity
  have ht0 : 0 < r / (2 * (‖v‖ + 1)) := by positivity
  have ht2 : r / (2 * (‖v‖ + 1)) * (2 * (‖v‖ + 1)) = r := div_mul_cancel₀ _ (by positivity)
  have hmem : R + (r / (2 * (‖v‖ + 1))) • v ∈ Metric.ball R r := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht0]
    nlinarith [mul_pos ht0 hn, norm_nonneg v, mul_nonneg ht0.le (norm_nonneg v)]
  have h1 := interior_subset (hball hmem)
  have h2 := hout _ h1
  rw [map_add, map_smul, smul_eq_mul, hR] at h2
  nlinarith [mul_pos ht0 (neg_pos.mpr hv)]

end tools

/-! ## 0b. The corner `B` when `ρ_s` is outside Δ -/

section corner

variable {e f : ℕ} {α β γ L ax ay x : ℝ} {s j0 : ℕ}

/-- **when `ρ_s` is outside Δ, the corner of Δ at `p(s, 0)` has the angle `≥ β`**: `p(s, 0)` is a vertex of `U(s − 1, 0)` (angle `β`) and is the right end `B` of the side
(first form of (K3)) -/
theorem out_corner_B (W : StepCtx D e f α β γ L ax ay x s j0)
    (hout : ∀ q ∈ D.target.carrier, -lvG (e : ℝ) (f : ℝ) 1 x (s : ℝ) ≤ GSG (e : ℝ) (f : ℝ) 1 q) :
    β ≤ D.target.localAngle (D.target.pts 1) := by
  have S := W.S
  have he0 := S.e0
  have hef := S.hef'
  have hhp := hhG_pos he0 hef
  have hε1 : (1 : ℝ) ^ 2 = 1 := by norm_num
  have hn2 := W.hn2
  obtain ⟨tU, hU⟩ := W.hK2.1 (s - 1) 0 (Nat.zero_le _) (by omega)
  have hc1 : ((s - 1 : ℕ) : ℝ) + 1 = (s : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]; ring
  have hBp : lpG (e : ℝ) (f : ℝ) 1 x (((s - 1 : ℕ) : ℝ) + 1) ((0 : ℕ) : ℝ)
      = mkPt (x + (s : ℝ) * (f : ℝ) ^ 2) 0 := by
    rw [hc1, Nat.cast_zero]; unfold lpG; exact mkPt_congr (by ring) (by ring)
  have hmem := (S.mem hU.mem₂).2.2
  rw [hBp, gB_mk] at hmem
  have hX : x + (s : ℝ) * (f : ℝ) ^ 2 ≤ L := by
    by_contra hneg
    rw [not_le] at hneg
    nlinarith [mul_pos S.hay (sub_pos.mpr hneg)]
  have hBc : D.target.pts 1 ∈ D.target.carrier := subset_convexHull ℝ _ ⟨1, rfl⟩
  have h1 := hout _ hBc
  rw [S.B_eq] at h1
  unfold lvG GSG at h1
  rw [lin_mk] at h1
  have hL : L ≤ x + (s : ℝ) * (f : ℝ) ^ 2 := by
    have h2 : hhG (e : ℝ) (f : ℝ) * L ≤ hhG (e : ℝ) (f : ℝ) * (x + (s : ℝ) * (f : ℝ) ^ 2) := by
      nlinarith [h1]
    exact le_of_mul_le_mul_left h2 hhp
  have hLeq : mkPt L 0 = lpG (e : ℝ) (f : ℝ) 1 x (((s - 1 : ℕ) : ℝ) + 1) ((0 : ℕ) : ℝ) := by
    rw [hBp]; exact mkPt_congr (le_antisymm hL hX) rfl
  have hang := (U_anglesG S hε1 hU).2.1
  have hone := one_angle_le D.toDissection (D.target.pts 1) tU
  rw [S.B_eq] at hone
  rw [← hLeq] at hang
  rw [S.B_eq]
  linarith

end corner

/-! ## 1. The clamps of `Λ` and its edges -/

section lambda

variable {e f : ℕ} {α β γ L ax ay x : ℝ} {s j0 : ℕ}

local notation "LV" => -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j0 : ℝ) + 1))

theorem lpG_row_mem_seg (e f ε x η : ℝ) {q ρ : ℝ} (hq : 0 < q) (h0 : 0 ≤ ρ) (h1 : ρ ≤ q) :
    lpG e f ε x ρ η ∈ segment ℝ (lpG e f ε x 0 η) (lpG e f ε x q η) := by
  have h := lp_mem_segG (e := e) (f := f) (ε := ε) (x := x) (ξ := 0) (η := η) (ξ' := q) (η' := η)
    (τ := ρ / q) (div_nonneg h0 hq.le) (by rw [div_le_one hq]; exact h1)
  rw [show lpG e f ε x (0 + ρ / q * (q - 0)) (η + ρ / q * (η - η)) = lpG e f ε x ρ η from
    lpG_congr (by rw [sub_zero, div_mul_cancel₀ _ hq.ne', zero_add]) (by ring)] at h
  exact h

/-- **the left end of `Λ` is clamped by the mirror tile** (paper: "Its left end is clamped (the direction `d(π)` is interior to `T`)") -/
theorem row_clamp_left (W : StepCtx D e f α β γ L ax ay x s j0) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ P' : Plane, GHG (f : ℝ) P' = LV ∧
      lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1) ∈
        openSegment ℝ P' (lpG (e : ℝ) (f : ℝ) 1 x ρ ((j0 : ℝ) + 1)) ∧
      ∀ ed ∈ D.lineChain (GHG (f : ℝ)) LV,
        ¬ Straddles ((D.tile ed.1).edge ed.2) P' (lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1))
          (lpG (e : ℝ) (f : ℝ) 1 x ρ ((j0 : ℝ) + 1)) := by
  have S := W.S
  obtain ⟨t, hT⟩ := W.hM
  have hT' : HasV D t (lpG (e : ℝ) (f : ℝ) 1 x 0 (j0 : ℝ)) (lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1))
      (lpG (e : ℝ) (f : ℝ) 1 x (-1) ((j0 : ℝ) + mirK (e : ℝ) (f : ℝ))) := hT
  have hs1 : 2 < mirK (e : ℝ) (f : ℝ) := mirK_gt_two S
  have hm0 : 0 < mirK (e : ℝ) (f : ℝ) := by linarith
  obtain ⟨δ, hδ0, hδs⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * mirK (e : ℝ) (f : ℝ) < 1 :=
    ⟨1 / (2 * mirK (e : ℝ) (f : ℝ)), by positivity, by
      rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]; linarith⟩
  refine ⟨lpG (e : ℝ) (f : ℝ) 1 x (-δ) ((j0 : ℝ) + 1), GHG_lp _ _ _ _ _ _,
    lpG_row_mid (e : ℝ) (f : ℝ) 1 x _ (by linarith) hρ, fun ed _ =>
      not_straddles_of_interior D.toDissection (j := t) ?_ ed.1 ed.2⟩
  intro y hy
  rw [openSegment_eq_image_lineMap] at hy
  obtain ⟨τ, ⟨h0, h1⟩, rfl⟩ := hy
  rw [lineMap_lpG, show lpG (e : ℝ) (f : ℝ) 1 x (-δ + τ * (0 - -δ))
      ((j0 : ℝ) + 1 + τ * ((j0 : ℝ) + 1 - ((j0 : ℝ) + 1)))
    = lpG (e : ℝ) (f : ℝ) 1 x (-(δ * (1 - τ))) ((j0 : ℝ) + 1) from lpG_congr (by ring) (by ring)]
  exact mirror_row_left hT' (by linarith) (mul_pos hδ0 (by linarith))
    (by nlinarith [mul_pos (mul_pos hδ0 hm0) h0])

/-- **the right end of `Λ` is clamped by the `m`-chord principle** (paper: "its right end by the `m`-chord principle with `j = j0 + 1`") -/
theorem row_clamp_right (W : StepCtx D e f α β γ L ax ay x s j0) {q : ℕ} (hq : q + j0 + 1 = s) :
    ∃ Q' : Plane, GHG (f : ℝ) Q' = LV ∧
      lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1) ∈
        openSegment ℝ (lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1)) Q' ∧
      ∀ ed ∈ D.lineChain (GHG (f : ℝ)) LV,
        ¬ Straddles ((D.tile ed.1).edge ed.2) Q' (lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1))
          (lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1)) := by
  have S := W.S
  have C : CtxBase D e f α β γ L ax ay 1 x := ⟨S, Or.inl rfl⟩
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have he0 := S.e0
  have hef := S.hef'
  have hsf := W.hsf
  have hn2 := W.hn2
  have hUrow : ∀ j' : ℕ, j' ≤ j0 → UTG D (e : ℝ) (f : ℝ) 1 x ((s : ℝ) - 1 - j') j' := by
    intro j' hj'
    have h := W.hK2.1 (s - 1 - j') j' hj' (by omega)
    have hc : ((s - 1 - j' : ℕ) : ℝ) = (s : ℝ) - 1 - j' := by
      rw [Nat.cast_sub (show j' ≤ s - 1 by omega), Nat.cast_sub (show 1 ≤ s by omega), Nat.cast_one]
    rwa [hc] at h
  have hcm : (q : ℝ) = (s : ℝ) - ((j0 : ℝ) + 1) := by rw [← hq]; push_cast; ring
  have hsj1 : (j0 : ℝ) + 1 < s := by
    have h' : j0 + 1 < s := by omega
    exact_mod_cast h'
  have hFp : GHG (f : ℝ) (lpG (e : ℝ) (f : ℝ) 1 x ((s : ℝ) - ((j0 : ℝ) + 1)) ((j0 : ℝ) + 1)) = LV :=
    GHG_lp _ _ _ _ _ _
  have hdir : GSG (e : ℝ) (f : ℝ) 1 (lpG (e : ℝ) (f : ℝ) 1 x ((s : ℝ) - ((j0 : ℝ) + 1)) ((j0 : ℝ) + 1)
      - lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1)) < 0 := by
    rw [map_sub, GSG_lp hε, GSG_lp hε]
    have := lvG_lt (e := (e : ℝ)) (f := (f : ℝ)) (ε := 1) (x := x) he0 hef
      (show (0 : ℝ) + ((j0 : ℝ) + 1) < (s : ℝ) - ((j0 : ℝ) + 1) + ((j0 : ℝ) + 1) by linarith)
    linarith
  obtain ⟨Q', hfQ', hQ', hQc⟩ := C.K3G_clamp_row W.hK3 (j0 := j0) (by omega) hUrow (GHG (f : ℝ)) _
    (Q := lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1)) hFp (GHG_lp _ _ _ _ _ _) hdir
  rw [← hcm] at hQ' hQc
  exact ⟨Q', hfQ', by rw [openSegment_symm]; exact hQ', hQc⟩

/-- **BY (P) AND LEMMA A5 THE EDGES ABOVE `Λ` ARE `c`-EDGES** (paper: "By (P) and Lemma A5 the edges above `Λ` partition it into lengths `a` and `c`; since `n − 1 < e` and the representations of `(n − 1) c`
without `b` are `(n − 1 − et) c + (ft) a`, all of them are `c`"): a tile above the row with two vertices on the segment `Λ = [p(0, j0+1), p(q, j0+1)]` (`q = n − 1`) has an edge of length `c`
between them.  The hypotheses of `CtxJ.rowJ` are those of `run_partition`: the tiles `D(i, j0)`, `i < q`, below, the clamps of both ends. -/
theorem lambda_edges (W : StepCtx D e f α β γ L ax ay x s j0) {q : ℕ} (hq : q + j0 + 1 = s) (hq1 : 1 ≤ q) :
    ∀ (tt : Fin N) (k m : Fin 3), k ≠ m → GHG (f : ℝ) ((D.tile tt).pts k) = LV →
      GHG (f : ℝ) ((D.tile tt).pts m) = LV → (∀ i, GHG (f : ℝ) ((D.tile tt).pts i) ≤ LV) →
      (D.tile tt).pts k ∈ segment ℝ (lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1))
        (lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1)) →
      (D.tile tt).pts m ∈ segment ℝ (lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1))
        (lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1)) →
      dist ((D.tile tt).pts k) ((D.tile tt).pts m) = (f : ℝ) ^ 2 := by
  have S := W.S
  have C : CtxBase D e f α β γ L ax ay 1 x := ⟨S, Or.inl rfl⟩
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have he0 := S.e0
  have hef := S.hef'
  have hsf := W.hsf
  have hne := W.hne
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  have hD : ∀ i' : ℕ, i' < q → DTG D (e : ℝ) (f : ℝ) 1 x i' j0 := fun i' hi' => W.hA i' (by omega)
  have hA0q : lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1) ≠ lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1) :=
    lpG_ne_xi he0 hef hε hqpos.ne
  have hfA0 : GHG (f : ℝ) (lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1)) = LV := GHG_lp _ _ _ _ _ _
  have hfAq : GHG (f : ℝ) (lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1)) = LV := GHG_lp _ _ _ _ _ _
  obtain ⟨tD0, hD0⟩ := hD 0 (by omega)
  rw [Nat.cast_zero] at hD0
  obtain ⟨tDq, hDq⟩ := hD (q - 1) (by omega)
  have hcq : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by rw [Nat.cast_sub hq1, Nat.cast_one]
  rw [hcq] at hDq
  have hAq_mem : lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1) ∈ D.target.carrier := by
    have := hDq.mem₃
    rwa [show (q : ℝ) - 1 + 1 = q by ring] at this
  have hint : openSegment ℝ (lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1))
      (lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1)) ⊆ interior D.target.carrier :=
    C.seg_intG hD0.mem₂ hAq_mem (Or.inl (by linarith)) (Or.inl ⟨1, one_pos, hD0.mem₃⟩)
      (Or.inr ⟨1, one_pos, hDq.mem₂⟩)
  have hwall : ∀ y ∈ openSegment ℝ (lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1))
      (lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1)), ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    have hy' : y ∈ segment ℝ (lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1))
        (lpG (e : ℝ) (f : ℝ) 1 x (0 + (q : ℝ) * 1) ((j0 : ℝ) + 1 + (q : ℝ) * 0)) := by
      rw [show lpG (e : ℝ) (f : ℝ) 1 x (0 + (q : ℝ) * 1) ((j0 : ℝ) + 1 + (q : ℝ) * 0)
        = lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1) from lpG_congr (by ring) (by ring)]
      exact openSegment_subset_segment ℝ _ _ hy
    obtain ⟨i', hi', hyi⟩ := seg_split_lpG hq1 hy'
    obtain ⟨t, k, m, j₃, hkm, hkj, hmj, hk, hm, hj⟩ := hD i' hi'
    refine seg_wall D.toDissection (t := t) hmj ?_
    rw [hm, hj]
    rw [show lpG (e : ℝ) (f : ℝ) 1 x (0 + (i' : ℝ) * 1) ((j0 : ℝ) + 1 + (i' : ℝ) * 0)
        = lpG (e : ℝ) (f : ℝ) 1 x (i' : ℝ) ((j0 : ℝ) + 1) from lpG_congr (by ring) (by ring),
      show lpG (e : ℝ) (f : ℝ) 1 x (0 + ((i' : ℝ) + 1) * 1) ((j0 : ℝ) + 1 + ((i' : ℝ) + 1) * 0)
        = lpG (e : ℝ) (f : ℝ) 1 x ((i' : ℝ) + 1) ((j0 : ℝ) + 1) from lpG_congr (by ring) (by ring)]
      at hyi
    exact hyi
  obtain ⟨P', hfP', hP', hLeft⟩ := row_clamp_left W (ρ := (q : ℝ)) hqpos
  obtain ⟨Q', hfQ', hQ', hQc⟩ := row_clamp_right W hq
  have hpart := run_partition D.toDissection (GHG (f : ℝ)) (GHG_ne he0 hef) _ hA0q hfP' hfQ' hP' hQ'
    (CSlot.segment_subset_level (GHG (f : ℝ)) _ hfA0 hfAq) hint hwall hLeft hQc
  have hdq : dist (lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1)) (lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1))
      = (q : ℝ) * (f : ℝ) ^ 2 := by
    rw [dist_rowG he0 hef hε (by linarith : (0 : ℝ) ≤ q)]; ring
  intro tt k m hkm hfk hfm hle hkS hmS
  obtain ⟨i0, hi0⟩ := tile_edge_of_pair (D.tile tt) hkm
  have hed : (tt, i0) ∈ D.lineChain (GHG (f : ℝ)) LV := by
    refine Dissection.mem_lineChain.mpr ⟨?_, ?_, hle⟩
    · show GHG (f : ℝ) ((D.tile tt).pts i0) = LV
      rcases hi0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1]; exact hfk
      · rw [h1]; exact hfm
    · show GHG (f : ℝ) ((D.tile tt).pts (i0 + 1)) = LV
      rcases hi0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h2]; exact hfm
      · rw [h2]; exact hfk
  have hsub : (D.tile tt).edge i0 ⊆ segment ℝ (lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1))
      (lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1)) := by
    show segment ℝ ((D.tile tt).pts i0) ((D.tile tt).pts (i0 + 1)) ⊆ _
    rcases hi0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact (convex_segment _ _).segment_subset hkS hmS
    · rw [h1, h2]; exact (convex_segment _ _).segment_subset hmS hkS
  have hdd : dist ((D.tile tt).pts i0) ((D.tile tt).pts (i0 + 1))
      = dist ((D.tile tt).pts k) ((D.tile tt).pts m) := by
    rcases hi0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, dist_comm]
  rw [← hdd]
  obtain ⟨x', y', z', hxyz⟩ := sum_split_semigroup _ _ ((e : ℝ) * (f : ℝ))
    ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2) _
    (fun e' _ => edge_length_casesG D S.hM e'.1 e'.2) (Finset.mem_filter.mpr ⟨hed, hsub⟩) hpart
  rw [hdq] at hxyz
  have hqe : q < e := by omega
  have hqf : q ≤ f - 1 := by omega
  rcases edge_length_casesG D S.hM tt i0 with h | h | h
  · exfalso
    rw [h] at hxyz
    have hn := rep_nat_c S.hef (x := x' + 1) (y := y') (z := z') (j := q) (by push_cast; linarith)
    have hy := SideRunGArith.A5 S.he S.hef S.hco hq1 hqf hn
    rw [hy] at hn
    have hn' : (x' + 1) * (e * f) + z' * f ^ 2 = q * f ^ 2 := by simpa using hn
    exact no_a_row S.hco (by omega) hqe (by omega) hn'
  · exfalso
    rw [h] at hxyz
    have hn := rep_nat_c S.hef (x := x') (y := y' + 1) (z := z') (j := q) (by push_cast; linarith)
    have hy := SideRunGArith.A5 S.he S.hef S.hco hq1 hqf hn
    omega
  · exact h

/-- no `b`-edge in a unit segment of `Λ` (the hypothesis `hnob` of `row_stepG`) -/
theorem row_noB (W : StepCtx D e f α β γ L ax ay x s j0) {q : ℕ} (hq : q + j0 + 1 = s) (hq1 : 1 ≤ q) :
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
  have h := lambda_edges W hq hq1 ed.1 ed.2 (ed.2 + 1) hne hp hq' hle hkS hmS
  rw [hb] at h
  have : (e : ℝ) ^ 2 = 0 := by linarith
  exact absurd this (pow_pos he0 2).ne'

end lambda

/-! ## 2. The tiles above `Λ` -/

section rowtiles

variable {e f : ℕ} {α β γ L ax ay x : ℝ} {s j0 : ℕ}

local notation "LV" => -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j0 : ℝ) + 1))

/-- a tile above the row with the `c`-edge `[p(r, j0+1), p(r+1, j0+1)]` that shows `α` at its RIGHT end (so `β` at the left end: the tile is not `U(r, j0+1)`) -/
def VBad (D : CongruentDissection N) (α : ℝ) (e f x : ℝ) (j0 : ℕ) (r : ℝ) : Prop :=
  ∃ (tV : Fin N) (k m j₃ : Fin 3), k ≠ m ∧ k ≠ j₃ ∧ m ≠ j₃ ∧
    (D.tile tV).pts k = lpG e f 1 x r ((j0 : ℝ) + 1) ∧
    (D.tile tV).pts m = lpG e f 1 x (r + 1) ((j0 : ℝ) + 1) ∧
    (∀ i, GHG f ((D.tile tV).pts i) ≤ -((f ^ 2 * hhG e f) * ((j0 : ℝ) + 1))) ∧
    (D.tile tV).localAngle (lpG e f 1 x (r + 1) ((j0 : ℝ) + 1)) = α

/-- a tile above the row with the edge `[p(r, j0+1), p(r+1, j0+1)]` -/
def VEdge (D : CongruentDissection N) (e f x : ℝ) (j0 : ℕ) (r : ℝ) : Prop :=
  ∃ (tV : Fin N) (k m : Fin 3), k ≠ m ∧ (D.tile tV).pts k = lpG e f 1 x r ((j0 : ℝ) + 1) ∧
    (D.tile tV).pts m = lpG e f 1 x (r + 1) ((j0 : ℝ) + 1) ∧
    ∀ i, GHG f ((D.tile tV).pts i) ≤ -((f ^ 2 * hhG e f) * ((j0 : ℝ) + 1))

theorem vedge_of_vex (S : SetupG D e f α β γ L ax ay) {r : ℝ}
    (h : UTG D (e : ℝ) (f : ℝ) 1 x r ((j0 : ℝ) + 1) ∨ VBad D α (e : ℝ) (f : ℝ) x j0 r) :
    VEdge D (e : ℝ) (f : ℝ) x j0 r := by
  rcases h with ⟨t, hU⟩ | ⟨tV, k, m, j₃, hkm, hkj, hmj, hk, hm, hle, hα⟩
  · have he0 := S.e0
    have hef := S.hef'
    have hle := hU.all (P := fun p => GHG (f : ℝ) p ≤ LV) (GHG_le he0 hef le_rfl)
      (GHG_le he0 hef le_rfl) (GHG_le he0 hef (by linarith))
    obtain ⟨k, m, j₃, hkm, hkj, hmj, hk, hm, hj⟩ := hU
    exact ⟨t, k, m, hkm, hk, hm, hle⟩
  · exact ⟨tV, k, m, hkm, hk, hm, hle⟩

/-- **ABOVE EACH SEGMENT `[p(r, j0+1), p(r+1, j0+1)]` OF `Λ` LIES A TILE `V_r`**: it is `U(r, j0+1)`, or it is a `c`-tile showing `β` at the left end and `α` at the right end (paper: "above each segment lies a tile
`V_r` with `α` and `β` at its ends").  The tiles are found from the left, one after the other: the first edge at `p(r, j0+1)` (`CtxBase.row_stepG`), clamped by the previous tile (`clamp_b`); `lambda_edges` says that
its edge is a `c`-edge. -/
theorem row_tiles (W : StepCtx D e f α β γ L ax ay x s j0) {q : ℕ} (hq : q + j0 + 1 = s) (hq1 : 1 ≤ q) :
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
        exact row_clamp_left W (ρ := 0 + 1) (by norm_num)
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
        (row_noB W hq hq1 (r : ℝ) (Nat.cast_nonneg r) (by exact_mod_cast hr)) with
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
      have hc := lambda_edges W hq hq1 ix k m hkm (by rw [hk]; exact GHG_lp _ _ _ _ _ _)
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

end rowtiles

/-! ## 3. The right end of `Λ` -/

section rightend

variable {e f : ℕ} {α β γ L ax ay x : ℝ} {s j0 : ℕ}

local notation "LV" => -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j0 : ℝ) + 1))

/-- **`V_{n−2}` shows `β` at `p(n−1, j0+1)`** (paper: "At `p(n−1, j0+1)` the tiles `D(n−2, j0)`, `U(n−1, j0)` and `ψ` leave the wedge `(π−β, π)`.  The same wedge is left when (K3) holds in its corner form ...
Hence `V_{n−2}` shows `β`"): the last tile `V` above `Λ` (with `n − 1 = q' + 1`) does not show `α` at the right end `R = p(q'+1, j0+1)`.  At `R` the tiles `D(q', j0)` (`α`), `U(q'+1, j0)` (`γ`), `V` (`α`) meet;
if a tile `ψ` has a straight angle there, the figure (F) at `R` (interior, or boundary point that is not a vertex of Δ) has at most one tile showing `α`, or no `γ`; and `R` is not a vertex of Δ (angle `< π`); if `ρ_s` is outside Δ,
`R` is a boundary point, not an interior point, and not the third corner of Δ: the corner `B = p(s, 0)` has the angle `≥ β` (`out_corner_B`) and `α + γ + α + β > π`.  (Conclusion `False`.) -/
theorem right_end_false (W : StepCtx D e f α β γ L ax ay x s j0) {q' : ℕ} (hq : q' + 1 + j0 + 1 = s)
    (hbad : VBad D α (e : ℝ) (f : ℝ) x j0 (q' : ℝ)) : False := by
  have S := W.S
  have C : CtxBase D e f α β γ L ax ay 1 x := ⟨S, Or.inl rfl⟩
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have he0 := S.e0
  have hef := S.hef'
  have hsf := W.hsf
  have hhp := hhG_pos he0 hef
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  obtain ⟨hαβ, hαγ, hαπ, -, hβγ, -, -, -, -, -⟩ :=
    distinct_of_pos_ne S.hA.hα S.hA.hβ S.hA.hαβ S.hA.hγdef S.hA.hrel
  obtain ⟨tV, k, m, j₃, hkm, hkj, hmj, hk, hm, hle, hαV⟩ := hbad
  obtain ⟨tD, hD⟩ := W.hA q' (by omega)
  have aD := (D_anglesG S hε hD).2.2
  obtain ⟨tU, hU⟩ := W.hK2.1 (q' + 1) j0 le_rfl (by omega)
  rw [Nat.cast_add, Nat.cast_one] at hU
  have aU := (U_anglesG S hε hU).2.2
  have ntVD : tV ≠ tD := by
    obtain ⟨kd, hkd⟩ := hD.idx₁
    exact ne_of_F (GHG (f : ℝ)) hle (i := kd) (by rw [hkd]; exact GHG_gt he0 hef (by linarith))
  have ntDU : tD ≠ tU := ne_of_angle (by rw [aD, aU]; exact hαγ)
  have ntVU : tV ≠ tU := ne_of_angle (by rw [hαV, aU]; exact hαγ)
  have hαs := forall_mem2
    (P := fun i => (D.tile i).localAngle (lpG (e : ℝ) (f : ℝ) 1 x ((q' : ℝ) + 1) ((j0 : ℝ) + 1)) = α)
    aD hαV
  have hγs : ∀ i ∈ ({tU} : Finset (Fin N)),
      (D.tile i).localAngle (lpG (e : ℝ) (f : ℝ) 1 x ((q' : ℝ) + 1) ((j0 : ℝ) + 1)) = γ := by
    intro i hi
    rw [Finset.mem_singleton.mp hi]; exact aU
  have c1 := card_le_angle _ α hαs
  have c2 := card_le_angle _ γ hγs
  rw [card2 ntVD.symm] at c1
  rw [Finset.card_singleton] at c2
  have hRm : lpG (e : ℝ) (f : ℝ) 1 x ((q' : ℝ) + 1) ((j0 : ℝ) + 1) ∈ D.target.carrier := hD.mem₃
  have hUrow : ∀ j' : ℕ, j' ≤ j0 → UTG D (e : ℝ) (f : ℝ) 1 x ((s : ℝ) - 1 - j') j' := by
    intro j' hj'
    have h := W.hK2.1 (s - 1 - j') j' hj' (by omega)
    have hc : ((s - 1 - j' : ℕ) : ℝ) = (s : ℝ) - 1 - j' := by
      rw [Nat.cast_sub (show j' ≤ s - 1 by omega), Nat.cast_sub (show 1 ≤ s by omega), Nat.cast_one]
    rwa [hc] at h
  have hpsi := psi_or_out C (s := (s : ℝ)) (j0 := j0) (J := j0 + 1) rfl W.hK3 (by omega) hUrow
  have hRR : lpG (e : ℝ) (f : ℝ) 1 x ((s : ℝ) - ((j0 + 1 : ℕ) : ℝ)) ((j0 + 1 : ℕ) : ℝ)
      = lpG (e : ℝ) (f : ℝ) 1 x ((q' : ℝ) + 1) ((j0 : ℝ) + 1) :=
    lpG_congr (by rw [← hq]; push_cast; ring) (by push_cast; ring)
  have hs' : ((q' : ℝ) + 1) + ((j0 : ℝ) + 1) = (s : ℝ) := by rw [← hq]; push_cast; ring
  -- a boundary point of Δ that is not a vertex: the figure `{3α, 2β}`, `{α, β, γ}`, `{π}` has no two `α` and a `γ`
  have hbd : lpG (e : ℝ) (f : ℝ) 1 x ((q' : ℝ) + 1) ((j0 : ℝ) + 1) ∈ frontier D.target.carrier →
      lpG (e : ℝ) (f : ℝ) 1 x ((q' : ℝ) + 1) ((j0 : ℝ) + 1) ∉ Set.range D.target.pts → False := by
    intro hfr hnv
    have F := fig_bdry S hfr hnv
    unfold FigB at F
    omega
  obtain ⟨kD3, hkD3⟩ := hD.idx₃
  rcases hpsi with hout | ⟨ψ, hψc, hψπ, hψpush⟩
  · -- `ρ_s` is outside Δ
    have hv : GSG (e : ℝ) (f : ℝ) 1 (lpG (e : ℝ) (f : ℝ) 1 x 1 0 - lpG (e : ℝ) (f : ℝ) 1 x 0 0) < 0 := by
      rw [map_sub, GSG_lp hε, GSG_lp hε]
      have := lvG_lt (e := (e : ℝ)) (f := (f : ℝ)) (ε := 1) (x := x) he0 hef
        (show (0 : ℝ) + 0 < 1 + 0 by norm_num)
      linarith
    have hR : GSG (e : ℝ) (f : ℝ) 1 (lpG (e : ℝ) (f : ℝ) 1 x ((q' : ℝ) + 1) ((j0 : ℝ) + 1))
        = -lvG (e : ℝ) (f : ℝ) 1 x (s : ℝ) := by rw [GSG_lp hε, hs']
    have hnint := not_interior_of_out hv hR hout
    have hfr : lpG (e : ℝ) (f : ℝ) 1 x ((q' : ℝ) + 1) ((j0 : ℝ) + 1) ∈ frontier D.target.carrier :=
      ⟨subset_closure hRm, hnint⟩
    by_cases hvert : lpG (e : ℝ) (f : ℝ) 1 x ((q' : ℝ) + 1) ((j0 : ℝ) + 1) ∈ Set.range D.target.pts
    · obtain ⟨k', hk'⟩ := hvert
      have hB := out_corner_B W hout
      have hsumT := target_angle_sum D.target
      have h3 := three_angles_le D.toDissection
        (lpG (e : ℝ) (f : ℝ) 1 x ((q' : ℝ) + 1) ((j0 : ℝ) + 1)) ntDU
        ntVD.symm ntVU.symm
      rw [aD, aU, hαV] at h3
      have hy : (lpG (e : ℝ) (f : ℝ) 1 x ((q' : ℝ) + 1) ((j0 : ℝ) + 1)) 1
          = ((j0 : ℝ) + 1) * hhG (e : ℝ) (f : ℝ) := by rw [lpG_snd]
      have hypos : 0 < ((j0 : ℝ) + 1) * hhG (e : ℝ) (f : ℝ) := mul_pos (by positivity) hhp
      rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) k' with rfl | rfl | rfl
      · have h1 := congrArg (fun p : Plane => p 1) hk'
        simp only [S.Q_eq, mkPt_one] at h1
        linarith
      · have h1 := congrArg (fun p : Plane => p 1) hk'
        simp only [S.B_eq, mkPt_one] at h1
        linarith
      · rw [hk'] at hsumT
        have hA0 := (D.target.localAngle_nonneg (D.target.pts 0))
        rw [S.hA.hγdef] at h3
        have hrel := S.hA.hrel
        linarith [hsumT, hA0, hB, h3, hrel]
    · exact hbd hfr hvert
  · -- a tile `ψ` has a straight angle at `R`
    rw [hRR] at hψπ
    have hψD : ψ ≠ tD := ne_of_angle (p := lpG (e : ℝ) (f : ℝ) 1 x ((q' : ℝ) + 1) ((j0 : ℝ) + 1))
      (by rw [hψπ, aD]; exact hαπ.symm)
    have hψs : ∀ i ∈ ({ψ} : Finset (Fin N)),
        (D.tile i).localAngle (lpG (e : ℝ) (f : ℝ) 1 x ((q' : ℝ) + 1) ((j0 : ℝ) + 1)) = Real.pi := by
      intro i hi
      rw [Finset.mem_singleton.mp hi]; exact hψπ
    have c3 := card_le_angle _ Real.pi hψs
    rw [Finset.card_singleton] at c3
    by_cases hint : lpG (e : ℝ) (f : ℝ) 1 x ((q' : ℝ) + 1) ((j0 : ℝ) + 1) ∈ interior D.target.carrier
    · have F := fig_int S hint hkD3
      unfold FigI at F
      omega
    · have hfr : lpG (e : ℝ) (f : ℝ) 1 x ((q' : ℝ) + 1) ((j0 : ℝ) + 1) ∈ frontier D.target.carrier :=
        ⟨subset_closure hRm, hint⟩
      by_cases hvert : lpG (e : ℝ) (f : ℝ) 1 x ((q' : ℝ) + 1) ((j0 : ℝ) + 1) ∈ Set.range D.target.pts
      · obtain ⟨k', hk'⟩ := hvert
        have h2 := two_angles_le D.toDissection
          (lpG (e : ℝ) (f : ℝ) 1 x ((q' : ℝ) + 1) ((j0 : ℝ) + 1)) hψD
        rw [hψπ, aD] at h2
        have hb := (Erdos634.Draft.E60Second.localAngle_vertex_bounds D.target k').2
        rw [hk'] at hb
        linarith
      · exact hbd hfr hvert

end rightend

end Erdos634.Draft.SideRunGA

#print axioms Erdos634.Draft.SideRunGA.no_a_row
#print axioms Erdos634.Draft.SideRunGA.target_angle_sum
#print axioms Erdos634.Draft.SideRunGA.not_interior_of_out
#print axioms Erdos634.Draft.SideRunGA.out_corner_B
#print axioms Erdos634.Draft.SideRunGA.row_clamp_left
#print axioms Erdos634.Draft.SideRunGA.row_clamp_right
#print axioms Erdos634.Draft.SideRunGA.lambda_edges
#print axioms Erdos634.Draft.SideRunGA.row_noB
#print axioms Erdos634.Draft.SideRunGA.vedge_of_vex
#print axioms Erdos634.Draft.SideRunGA.row_tiles
#print axioms Erdos634.Draft.SideRunGA.right_end_false
