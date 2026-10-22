/-
Draft/SideRunGMoA.lean -- written 14 October 2026.  UNAUDITED.  In `AllThreshold`.  First file of module M4 of the plan for
`thm:cornerrun` (the statement `M°(e+1)`; M1 `Draft/SideRunGMirror.lean`, M2 `Draft/SideRunGMStep.lean`, M3 `Draft/SideRunGMStepB.lean`, `Draft/SideRunGMStepC.lean`;
the other files of M4 are `Draft/SideRunGMoB.lean` and `Draft/SideRunGMo.lean`).

**Why these files repeat part of M2/M3/StepC.**  The induction of `Draft/SideRunGMStep*.lean` is for pairs `(s', j0)` of size `n = s' - j0 ≤ e`; the field `hne : s - j0 ≤ e` of `StepCtx` and the hypothesis
`hne` of `noN_M`, `stepA` are used only to bound the sizes of the statements `M` that the steps call (they are `< n`), and, in `lambda_edges`, to forbid an edge `a` on `Λ` (`q < e`).  For `M°(e+1)` the size
is `n = e + 1`.  The files are NOT allowed to edit M2/M3/StepC (new files only), so the steps are repeated here with `hne : s - j0 ≤ e + 1` (`StepCtxO`) and with the row condition `RowLenAll` (every tile edge between
two points of `Λ` has the length `len`) in place of `lambda_edges`.  Each repeated statement says which statement of M2/M3/StepC it repeats.

CONTENTS of this file.
0. `StepCtxO` (the standing hypotheses of the induction step, size `≤ e + 1`), `RowLenAll`.
1. Arithmetic: `sum_counts` (the partition sum as a count of the edges of each length), `dich_nat` (`A e + C f = e f` forces `(A, C) = (0, e)` or `(f, 0)`), `figI_contra`, `figB_contra` (the counting of (F) used below).
2. `out_corner_BO`, `row_clamp_leftO`, `row_clamp_rightO` (copies of `out_corner_B`, `row_clamp_left`, `row_clamp_right` of M3 for `StepCtxO`).
3. **The row `Λ` of `e` edges**: `lambda_wallO` (the open segment `Λ` is interior and a wall), `lambda_dich` (**paper, proof of `M°(e+1)`: "the row `Λ = [p(0,1), p(e,1)]` has `e` edges and can be cut as `c^e` or as `a^f`"**:
   by (P) and Lemma A5 no edge `b`, and `x e + z f = e f` gives `(x, z) = (0, e)` or `(f, 0)`).
4. `right_end_ang`: **the generalization of `right_end_false` (M3)**: a tile `V` above `Λ` with a vertex at the right end `R = p(q'+1, j0+1)` does not show `α` (the paper's step (b), "`V_{n−2}` shows `β`") and does not show `γ`
   (needed for the case `a^f`: "the last one shows `β` at `p(e,1)`, so it is `A_2`").

WITNESSES.  As in `Draft/SideRunGMStep.lean`: the statements conclude `False` under the conditions (M1), (K2), (K3) of the paper.

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGMStepC

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

/-! ## 0. The standing hypotheses at size `≤ e + 1` -/

/-- **the standing hypotheses of the induction step at size `n = s - j0 ≤ e + 1`** (`StepCtx` of M3 with `hne : s - j0 ≤ e + 1`; the steps use `M` only below `n`, so the sizes called are `≤ e`) -/
structure StepCtxO (D : CongruentDissection N) (e f : ℕ) (α β γ L ax ay x : ℝ) (s j0 : ℕ) : Prop where
  S : SetupG D e f α β γ L ax ay
  hch : ChordsAt D (e : ℝ) (f : ℝ) 1 x
  hM : MirrorAt D (e : ℝ) (f : ℝ) 1 x (j0 : ℝ)
  hK2 : K2G D (e : ℝ) (f : ℝ) 1 x s j0
  hK3 : K3G D (e : ℝ) (f : ℝ) 1 x (s : ℝ) (j0 : ℝ)
  hsf : s < f
  hne : s - j0 ≤ e + 1
  hn2 : 2 ≤ s - j0
  IH : ∀ m, 1 ≤ m → m < s - j0 → MGh D e f 1 m
  hA : ∀ i, i + 2 ≤ s - j0 → DTG D (e : ℝ) (f : ℝ) 1 x i j0

/-- **every tile edge between two points of `Λ = [p(0, j0+1), p(q, j0+1)]` has the length `len`** (the tiles lie above the row) -/
def RowLenAll (D : CongruentDissection N) (e f x : ℝ) (j0 q : ℕ) (len : ℝ) : Prop :=
  ∀ (tt : Fin N) (k m : Fin 3), k ≠ m →
    GHG f ((D.tile tt).pts k) = -((f ^ 2 * hhG e f) * ((j0 : ℝ) + 1)) →
    GHG f ((D.tile tt).pts m) = -((f ^ 2 * hhG e f) * ((j0 : ℝ) + 1)) →
    (∀ i, GHG f ((D.tile tt).pts i) ≤ -((f ^ 2 * hhG e f) * ((j0 : ℝ) + 1))) →
    (D.tile tt).pts k ∈ segment ℝ (lpG e f 1 x 0 ((j0 : ℝ) + 1)) (lpG e f 1 x (q : ℝ) ((j0 : ℝ) + 1)) →
    (D.tile tt).pts m ∈ segment ℝ (lpG e f 1 x 0 ((j0 : ℝ) + 1)) (lpG e f 1 x (q : ℝ) ((j0 : ℝ) + 1)) →
    dist ((D.tile tt).pts k) ((D.tile tt).pts m) = len

/-! ## 1. Arithmetic -/

/-- **the partition sum as a count**: a finite family of reals each equal to `a`, `b` or `c` (`a ≠ c`) sums to `(#a) a + (#neither) b + (#c) c` -/
theorem sum_counts {ι : Type*} (s : Finset ι) (g : ι → ℝ) {a b c : ℝ} (hac : a ≠ c)
    (h : ∀ i ∈ s, g i = a ∨ g i = b ∨ g i = c) :
    ∑ i ∈ s, g i = ((s.filter (fun i => g i = a)).card : ℝ) * a
      + ((s.filter (fun i => ¬ g i = a ∧ ¬ g i = c)).card : ℝ) * b
      + ((s.filter (fun i => g i = c)).card : ℝ) * c := by
  have key : ∀ i ∈ s, g i = (if g i = a then a else 0)
      + (if (¬ g i = a ∧ ¬ g i = c) then b else 0) + (if g i = c then c else 0) := by
    intro i hi
    by_cases h1 : g i = a
    · have h2 : ¬ g i = c := by rw [h1]; exact hac
      have h3 : ¬ (¬ g i = a ∧ ¬ g i = c) := fun hh => hh.1 h1
      rw [if_pos h1, if_neg h3, if_neg h2]
      linarith
    · by_cases h2 : g i = c
      · have h3 : ¬ (¬ g i = a ∧ ¬ g i = c) := fun hh => hh.2 h2
        rw [if_neg h1, if_neg h3, if_pos h2]
        linarith
      · have h3 : g i = b := by
          rcases h i hi with h' | h' | h'
          · exact absurd h' h1
          · exact h'
          · exact absurd h' h2
        rw [if_neg h1, if_pos ⟨h1, h2⟩, if_neg h2]
        linarith
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]

/-- `A e + C f = e f` for coprime `e < f`: `(A, C) = (0, e)` or `(f, 0)` -/
theorem dich_nat {e f A C : ℕ} (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (h : A * e + C * f = e * f) : (A = 0 ∧ C = e) ∨ (A = f ∧ C = 0) := by
  by_cases hA : A = 0
  · left
    refine ⟨hA, ?_⟩
    rw [hA] at h
    have h' : C * f = e * f := by simpa using h
    exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < f) h'
  · right
    have hd : f ∣ A * e := by
      have h2 : (f : ℤ) ∣ ((A * e : ℕ) : ℤ) := ⟨(e : ℤ) - C, by
        have h1' := congrArg (Nat.cast : ℕ → ℤ) h
        push_cast at h1' ⊢
        linear_combination h1'⟩
      exact_mod_cast h2
    have hdx : f ∣ A := Nat.Coprime.dvd_of_dvd_mul_right hco.symm hd
    have hfA : f ≤ A := Nat.le_of_dvd (by omega) hdx
    have hAf : A ≤ f := by
      by_contra hc
      replace hc := not_le.mp hc
      have h5 := Nat.mul_le_mul_right e (Nat.succ_le_of_lt hc)
      nlinarith [h5, h, Nat.zero_le (C * f)]
    have hAeq : A = f := le_antisymm hAf hfA
    refine ⟨hAeq, ?_⟩
    rw [hAeq] at h
    have h6 : C * f = 0 := by nlinarith [h]
    rcases Nat.mul_eq_zero.mp h6 with h0 | h0
    · exact h0
    · omega

/-- the counting of (F) at an interior vertex: a straight angle, a tile showing `α`, a tile showing `γ`, and three in all among `α` and `γ` do not occur -/
theorem figI_contra {p a b g : ℕ} (F : FigI p a b g) (hp : 1 ≤ p) (ha : 1 ≤ a) (hg : 1 ≤ g)
    (h3 : 3 ≤ a + g) : False := by
  unfold FigI at F
  omega

/-- the same at a boundary point of Δ that is not a vertex -/
theorem figB_contra {p a b g : ℕ} (F : FigB p a b g) (ha : 1 ≤ a) (hg : 1 ≤ g)
    (h3 : 3 ≤ a + g) : False := by
  unfold FigB at F
  omega

/-! ## 2. Copies of M3 for `StepCtxO` -/

section copies

variable {e f : ℕ} {α β γ L ax ay x : ℝ} {s j0 : ℕ}

local notation "LV" => -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j0 : ℝ) + 1))

/-- **when `ρ_s` is outside Δ, the corner of Δ at `p(s, 0)` has the angle `≥ β`**: `p(s, 0)` is a vertex of `U(s − 1, 0)` (angle `β`) and is the right end `B` of the side
(first form of (K3)) -/
theorem out_corner_BO (W : StepCtxO D e f α β γ L ax ay x s j0)
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

/-- **the left end of `Λ` is clamped by the mirror tile** (paper: "Its left end is clamped (the direction `d(π)` is interior to `T`)") -/
theorem row_clamp_leftO (W : StepCtxO D e f α β γ L ax ay x s j0) {ρ : ℝ} (hρ : 0 < ρ) :
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
theorem row_clamp_rightO (W : StepCtxO D e f α β γ L ax ay x s j0) {q : ℕ} (hq : q + j0 + 1 = s) :
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

end copies

/-! ## 3. The row `Λ` of `e` edges -/

section lambdaO

variable {e f : ℕ} {α β γ L ax ay x : ℝ} {s j0 : ℕ}

local notation "LV" => -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j0 : ℝ) + 1))

/-- **the open segment `Λ = (p(0, j0+1), p(q, j0+1))` is interior to Δ and meets no interior of a tile** (the `hint`, `hwall` of `lambda_edges`, M3: `Λ` is the union of the `c`-edges of the tiles `D(i, j0)`) -/
theorem lambda_wallO (W : StepCtxO D e f α β γ L ax ay x s j0) {q : ℕ} (hq : q + j0 + 1 = s) (hq1 : 1 ≤ q) :
    openSegment ℝ (lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1)) (lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1))
      ⊆ interior D.target.carrier ∧
    ∀ y ∈ openSegment ℝ (lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1)) (lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1)),
      ∀ i, y ∉ interior (D.tile i).carrier := by
  have S := W.S
  have C : CtxBase D e f α β γ L ax ay 1 x := ⟨S, Or.inl rfl⟩
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have he0 := S.e0
  have hef := S.hef'
  have hsf := W.hsf
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
  exact ⟨hint, hwall⟩

/-- **THE ROW `Λ` OF `e` EDGES IS CUT AS `c^e` OR AS `a^f`** (paper, proof of `M°(e+1)`: "the row `Λ = [p(0,1), p(e,1)]` has `e` edges and can be cut as `c^e` or as `a^f`"): by (P) (`run_partition`) the tile edges
in `Λ` sum to `e c`; by Lemma A5 none has the length `b`; `x e + z f = e f` gives `(x, z) = (0, e)` or `(f, 0)` (`dich_nat`).  Then every tile edge between two points of `Λ` has the length `c`, or every one has the length `a`. -/
theorem lambda_dich (W : StepCtxO D e f α β γ L ax ay x s j0) {q : ℕ} (hq : q + j0 + 1 = s) (hqe : q = e) :
    RowLenAll D (e : ℝ) (f : ℝ) x j0 q ((f : ℝ) ^ 2) ∨ RowLenAll D (e : ℝ) (f : ℝ) x j0 q ((e : ℝ) * f) := by
  have S := W.S
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have he0 := S.e0
  have hef := S.hef'
  have hq1 : 1 ≤ q := by rw [hqe]; exact S.he
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  have hqf : q ≤ f - 1 := by have := S.hef; omega
  obtain ⟨hint, hwall⟩ := lambda_wallO W hq hq1
  have hA0q : lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1) ≠ lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1) :=
    lpG_ne_xi he0 hef hε hqpos.ne
  have hfA0 : GHG (f : ℝ) (lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1)) = LV := GHG_lp _ _ _ _ _ _
  have hfAq : GHG (f : ℝ) (lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1)) = LV := GHG_lp _ _ _ _ _ _
  obtain ⟨P', hfP', hP', hLeft⟩ := row_clamp_leftO W (ρ := (q : ℝ)) hqpos
  obtain ⟨Q', hfQ', hQ', hQc⟩ := row_clamp_rightO W hq
  have hpart := run_partition D.toDissection (GHG (f : ℝ)) (GHG_ne he0 hef) _ hA0q hfP' hfQ' hP' hQ'
    (CSlot.segment_subset_level (GHG (f : ℝ)) _ hfA0 hfAq) hint hwall hLeft hQc
  have hdq : dist (lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1)) (lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1))
      = (q : ℝ) * (f : ℝ) ^ 2 := by
    rw [dist_rowG he0 hef hε (by linarith : (0 : ℝ) ≤ q)]; ring
  rw [hdq] at hpart
  obtain ⟨Sf, hSf⟩ : ∃ Sf : Finset (Fin N × Fin 3), Sf = (D.lineChain (GHG (f : ℝ)) LV).filter
      (fun ed => (D.tile ed.1).edge ed.2 ⊆ segment ℝ (lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1))
        (lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1))) := ⟨_, rfl⟩
  have hpart' : ∑ ed ∈ Sf, dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1))
      = (q : ℝ) * (f : ℝ) ^ 2 := by
    rw [hSf]
    exact hpart
  have hlen : ∀ ed ∈ Sf, dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1)) = (e : ℝ) * f ∨
      dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1)) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∨
      dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1)) = (f : ℝ) ^ 2 :=
    fun ed _ => edge_length_casesG D S.hM ed.1 ed.2
  have hac : (e : ℝ) * f ≠ (f : ℝ) ^ 2 := by
    intro h
    nlinarith [mul_pos S.f0 (sub_pos.mpr hef)]
  obtain ⟨A, hAdef⟩ : ∃ A : Finset (Fin N × Fin 3), A = Sf.filter
      (fun ed => dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1)) = (e : ℝ) * f) := ⟨_, rfl⟩
  obtain ⟨Rr, hRdef⟩ : ∃ Rr : Finset (Fin N × Fin 3), Rr = Sf.filter
      (fun ed => ¬ dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1)) = (e : ℝ) * f ∧
        ¬ dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1)) = (f : ℝ) ^ 2) := ⟨_, rfl⟩
  obtain ⟨Cc, hCdef⟩ : ∃ Cc : Finset (Fin N × Fin 3), Cc = Sf.filter
      (fun ed => dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1)) = (f : ℝ) ^ 2) := ⟨_, rfl⟩
  have hcnt : ∑ ed ∈ Sf, dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1))
      = (A.card : ℝ) * ((e : ℝ) * f) + (Rr.card : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)
        + (Cc.card : ℝ) * (f : ℝ) ^ 2 := by
    rw [hAdef, hRdef, hCdef]
    exact sum_counts Sf (fun ed => dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1))) hac hlen
  have heq := hpart'.symm.trans hcnt
  have hnat := rep_nat_c S.hef (x := A.card) (y := Rr.card) (z := Cc.card) (j := q) heq.symm
  have hy := SideRunGArith.A5 S.he S.hef S.hco hq1 hqf hnat
  rw [hy] at hnat
  have h1 : A.card * e + Cc.card * f = e * f := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < f by have := S.hef; omega)
    have h2 : f * (A.card * e + Cc.card * f) = A.card * (e * f) + 0 * (f ^ 2 - e ^ 2) + Cc.card * f ^ 2 := by
      ring
    rw [h2, hnat, hqe]
    ring
  have hdich := dich_nat S.hco S.he S.hef h1
  -- every tile edge between two points of `Λ` is an edge of `Sf`
  have hmem : ∀ (tt : Fin N) (k m : Fin 3), k ≠ m →
      GHG (f : ℝ) ((D.tile tt).pts k) = LV → GHG (f : ℝ) ((D.tile tt).pts m) = LV →
      (∀ i, GHG (f : ℝ) ((D.tile tt).pts i) ≤ LV) →
      (D.tile tt).pts k ∈ segment ℝ (lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1))
        (lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1)) →
      (D.tile tt).pts m ∈ segment ℝ (lpG (e : ℝ) (f : ℝ) 1 x 0 ((j0 : ℝ) + 1))
        (lpG (e : ℝ) (f : ℝ) 1 x (q : ℝ) ((j0 : ℝ) + 1)) →
      ∃ ed ∈ Sf, dist ((D.tile tt).pts k) ((D.tile tt).pts m) =
        dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1)) := by
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
    exact ⟨(tt, i0), by rw [hSf, Finset.mem_filter]; exact ⟨hed, hsub⟩, hdd.symm⟩
  rcases hdich with ⟨hA0, hC0⟩ | ⟨hAf, hC0⟩
  · -- no edge `a`: every edge is `c`
    left
    intro tt k m hkm hfk hfm hle hkS hmS
    obtain ⟨ed, hed, hd⟩ := hmem tt k m hkm hfk hfm hle hkS hmS
    rw [hd]
    have hA' : ed ∉ A := by rw [Finset.card_eq_zero.mp hA0]; simp
    have hR' : ed ∉ Rr := by rw [Finset.card_eq_zero.mp hy]; simp
    by_cases hga : dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1)) = (e : ℝ) * f
    · exact absurd (by rw [hAdef, Finset.mem_filter]; exact ⟨hed, hga⟩) hA'
    · by_contra hgc
      exact hR' (by rw [hRdef, Finset.mem_filter]; exact ⟨hed, hga, hgc⟩)
  · -- no edge `c`: every edge is `a`
    right
    intro tt k m hkm hfk hfm hle hkS hmS
    obtain ⟨ed, hed, hd⟩ := hmem tt k m hkm hfk hfm hle hkS hmS
    rw [hd]
    have hC' : ed ∉ Cc := by rw [Finset.card_eq_zero.mp hC0]; simp
    have hR' : ed ∉ Rr := by rw [Finset.card_eq_zero.mp hy]; simp
    by_cases hgc : dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1)) = (f : ℝ) ^ 2
    · exact absurd (by rw [hCdef, Finset.mem_filter]; exact ⟨hed, hgc⟩) hC'
    · by_contra hga
      exact hR' (by rw [hRdef, Finset.mem_filter]; exact ⟨hed, hga, hgc⟩)

end lambdaO

/-! ## 4. The right end of `Λ` -/

section rightendO

variable {e f : ℕ} {α β γ L ax ay x : ℝ} {s j0 : ℕ}

local notation "LV" => -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j0 : ℝ) + 1))

/-- **A TILE ABOVE `Λ` THAT SHOWS `α` OR `γ` AT THE RIGHT END `R = p(q'+1, j0+1)` DOES NOT EXIST** (the generalization of `right_end_false` of M3, whose `V` shows `α`; paper, step (b): "At `p(n−1, j0+1)` the tiles
`D(n−2, j0)`, `U(n−1, j0)` and `ψ` leave the wedge `(π−β, π)` ... Hence `V_{n−2}` shows `β`"; and, for the case `a^f` of `M°(e+1)`: "the last one shows `β` at `p(e,1)`").  At `R` the tiles `D(q', j0)` (`α`), `U(q'+1, j0)` (`γ`) and `V`
(`θ ∈ {α, γ}`) meet; if a tile `ψ` has a straight angle there, the figure (F) at `R` has at most one tile showing `α`, or no `γ`, or fewer than three among `α`, `γ`; `R` is not a vertex of Δ then (angle `< π`); if `ρ_s` is outside Δ,
`R` is a boundary point, not an interior point, and not the third corner of Δ (the corner `B` has the angle `≥ β`, `out_corner_BO`, and `α + γ + θ + β > π`).  (Conclusion `False`.) -/
theorem right_end_ang (W : StepCtxO D e f α β γ L ax ay x s j0) {q' : ℕ} (hq : q' + 1 + j0 + 1 = s)
    {tV : Fin N} {θ : ℝ} (hθ : θ = α ∨ θ = γ)
    (hVle : ∀ i, GHG (f : ℝ) ((D.tile tV).pts i) ≤ LV)
    (hVang : (D.tile tV).localAngle (lpG (e : ℝ) (f : ℝ) 1 x ((q' : ℝ) + 1) ((j0 : ℝ) + 1)) = θ) :
    False := by
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
  obtain ⟨tD, hD⟩ := W.hA q' (by omega)
  have aD := (D_anglesG S hε hD).2.2
  obtain ⟨tU, hU⟩ := W.hK2.1 (q' + 1) j0 le_rfl (by omega)
  rw [Nat.cast_add, Nat.cast_one] at hU
  have aU := (U_anglesG S hε hU).2.2
  have ntVD : tV ≠ tD := by
    obtain ⟨kd, hkd⟩ := hD.idx₁
    exact ne_of_F (GHG (f : ℝ)) hVle (i := kd) (by rw [hkd]; exact GHG_gt he0 hef (by linarith))
  have ntVU : tV ≠ tU := by
    obtain ⟨ku, hku⟩ := hU.idx₁
    exact ne_of_F (GHG (f : ℝ)) hVle (i := ku) (by rw [hku]; exact GHG_gt he0 hef (by linarith))
  have ntDU : tD ≠ tU := ne_of_angle (by rw [aD, aU]; exact hαγ)
  have hθpos : 0 < θ := by
    rcases hθ with h | h
    · rw [h]; exact hα
    · rw [h]; have := Real.pi_pos; linarith
  have hRm : lpG (e : ℝ) (f : ℝ) 1 x ((q' : ℝ) + 1) ((j0 : ℝ) + 1) ∈ D.target.carrier := hD.mem₃
  -- the counts of (F) at `R`: one `α`, one `γ`, and three in all
  have hcnt : 1 ≤ ({i | (D.tile i).localAngle (lpG (e : ℝ) (f : ℝ) 1 x ((q' : ℝ) + 1) ((j0 : ℝ) + 1)) = α} :
        Finset (Fin N)).card ∧
      1 ≤ ({i | (D.tile i).localAngle (lpG (e : ℝ) (f : ℝ) 1 x ((q' : ℝ) + 1) ((j0 : ℝ) + 1)) = γ} :
        Finset (Fin N)).card ∧
      3 ≤ ({i | (D.tile i).localAngle (lpG (e : ℝ) (f : ℝ) 1 x ((q' : ℝ) + 1) ((j0 : ℝ) + 1)) = α} :
        Finset (Fin N)).card +
        ({i | (D.tile i).localAngle (lpG (e : ℝ) (f : ℝ) 1 x ((q' : ℝ) + 1) ((j0 : ℝ) + 1)) = γ} :
        Finset (Fin N)).card := by
    rcases hθ with h | h
    · rw [h] at hVang
      have hαs := forall_mem2
        (P := fun i => (D.tile i).localAngle (lpG (e : ℝ) (f : ℝ) 1 x ((q' : ℝ) + 1) ((j0 : ℝ) + 1)) = α)
        aD hVang
      have hγs : ∀ i ∈ ({tU} : Finset (Fin N)),
          (D.tile i).localAngle (lpG (e : ℝ) (f : ℝ) 1 x ((q' : ℝ) + 1) ((j0 : ℝ) + 1)) = γ := by
        intro i hi
        rw [Finset.mem_singleton.mp hi]; exact aU
      have c1 := card_le_angle _ α hαs
      have c2 := card_le_angle _ γ hγs
      rw [card2 ntVD.symm] at c1
      rw [Finset.card_singleton] at c2
      omega
    · rw [h] at hVang
      have hαs : ∀ i ∈ ({tD} : Finset (Fin N)),
          (D.tile i).localAngle (lpG (e : ℝ) (f : ℝ) 1 x ((q' : ℝ) + 1) ((j0 : ℝ) + 1)) = α := by
        intro i hi
        rw [Finset.mem_singleton.mp hi]; exact aD
      have hγs := forall_mem2
        (P := fun i => (D.tile i).localAngle (lpG (e : ℝ) (f : ℝ) 1 x ((q' : ℝ) + 1) ((j0 : ℝ) + 1)) = γ)
        aU hVang
      have c1 := card_le_angle _ α hαs
      have c2 := card_le_angle _ γ hγs
      rw [Finset.card_singleton] at c1
      rw [card2 ntVU.symm] at c2
      omega
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
  -- a boundary point of Δ that is not a vertex
  have hbd : lpG (e : ℝ) (f : ℝ) 1 x ((q' : ℝ) + 1) ((j0 : ℝ) + 1) ∈ frontier D.target.carrier →
      lpG (e : ℝ) (f : ℝ) 1 x ((q' : ℝ) + 1) ((j0 : ℝ) + 1) ∉ Set.range D.target.pts → False := by
    intro hfr hnv
    exact figB_contra (fig_bdry S hfr hnv) hcnt.1 hcnt.2.1 hcnt.2.2
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
      have hB := out_corner_BO W hout
      have hsumT := target_angle_sum D.target
      have h3 := three_angles_le D.toDissection
        (lpG (e : ℝ) (f : ℝ) 1 x ((q' : ℝ) + 1) ((j0 : ℝ) + 1)) ntDU
        ntVD.symm ntVU.symm
      rw [aD, aU, hVang] at h3
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
        linarith [hsumT, hA0, hB, h3, hsum, hθpos]
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
    · exact figI_contra (fig_int S hint hkD3) c3 hcnt.1 hcnt.2.1 hcnt.2.2
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

end rightendO

end Erdos634.Draft.SideRunGA

#print axioms Erdos634.Draft.SideRunGA.sum_counts
#print axioms Erdos634.Draft.SideRunGA.dich_nat
#print axioms Erdos634.Draft.SideRunGA.figI_contra
#print axioms Erdos634.Draft.SideRunGA.figB_contra
#print axioms Erdos634.Draft.SideRunGA.out_corner_BO
#print axioms Erdos634.Draft.SideRunGA.row_clamp_leftO
#print axioms Erdos634.Draft.SideRunGA.row_clamp_rightO
#print axioms Erdos634.Draft.SideRunGA.lambda_wallO
#print axioms Erdos634.Draft.SideRunGA.lambda_dich
#print axioms Erdos634.Draft.SideRunGA.right_end_ang
