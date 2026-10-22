/-
Draft/SideRunGCornerMainB.lean -- written 14 October 2026.  UNAUDITED.  In `AllThreshold`.  Module R2 (second file) of the plan for
`thm:cornerrun`: **THE THEOREM, for an arbitrary congruent dissection.**

PAPER.  `thm:cornerrun`: "Let `1 ≤ e < f` be coprime integers and `(a, b, c) = (ef, f² − e², f²)`.  Let `s` be a side of a triangle `Δ` that is cut into congruent triangles with sides `(a, b, c)`, from a corner `A'` of angle `2α` or `3α` to a corner
`Q'` of angle `β` or `α + β`, and read the types of the tiles on `s` with `A'` on the left.  Then one of the following holds.  (i) `s` carries `f` consecutive tiles of type `C1` or `f` consecutive tiles of type `C2`.  (ii) `s` begins at `A'` with a
maximal run `C1^k` with `e + 1 ≤ k ≤ f − 1`, whose first tile and the tile beside it at `A'` are mirror images in their common `b`-edge, and which is followed by the corner `Q'` or by a tile `A2`, `B2` or `C2`.  In particular, for the members
`(f − 1, f)` every such side carries `f` consecutive equal `c`-tiles.  Addendum: if `a < b` and `A'` has the angle `2α`, then `k ≥ e + 2` in (ii)."

WHAT IS PROVED HERE.
* `MirrorBeside D₀ e f A' i₀ T` (in `Draft/SideRunGCornerMirror.lean`): the mirror condition of (ii), stated for the ORIGINAL dissection `D₀`: the first tile `i₀` has the vertices `A'`, `E`, `W` with `|W A'| = b`; the tile `T` has the vertices `A'`, `W` (the
  `b`-edge of `i₀` at `A'`) and a third vertex `R` which is the reflection of `E` in the line `A' W`.
* `mirrorDist_of_mirrorAt`, `mirrorBeside_of_mirrorAt`: `MirrorAt D e f 1 0 0` (the output of `corner_run_mirror`, in the normal form) is `MirrorDist` and `MirrorBeside` for the original dissection.
* `cornerrun_core`: the theorem, with the addendum as an extra conjunct of (ii).
* `thm_cornerrun`: **the theorem as stated in the paper** (alternatives (i) and (ii), `e + 1 ≤ k ≤ f − 1`, the follower, the mirror tile).
* `thm_cornerrun_thick`: the members `(f − 1, f)` (`e + 1 = f`): alternative (i) always.
* `thm_cornerrun_addendum`: `a < b` and `A'` of angle exactly `2α`: `k ≥ e + 2` in (ii).

HOW.  `setup_of_corners` (`Draft/SideRunGCornerMain.lean`) moves `D₀` to the normal form (a `SetupG` with `CornersA`); the typed chain of base tiles of the side from `A'` is `S.exists_chainG`; `corner_side_theorem` gives (i) or the
maximal run (ii) before the run lemma; `corner_run_short` gives `k ≥ e + 1`, `corner_run_short_o` gives `k ≥ e + 2`, `corner_run_mirror` gives the mirror tile; `laysOn_of_baseTile` pulls back the types and `hasV_pullback` the tile `T`.

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGCornerMain
import Erdos634.Draft.SideRunGCornerSide
import Erdos634.Draft.SideRunGCornerMirror

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.SideRunGA

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.FDBBaseBetaE1 Set

variable {N : ℕ}

/-! ## 1. The mirror condition for the original dissection -/

/-- the vertices of a tile of the normal form, pulled back to the original dissection -/
theorem hasV_pullback {D₀ D : CongruentDissection N} {g : Plane ≃ᵢ Plane}
    (hD : ∀ i m, (D.tile i).pts m = g ((D₀.tile i).pts m)) {t : Fin N} {A B C : Plane}
    (h : HasV D t A B C) : HasV D₀ t (g.symm A) (g.symm B) (g.symm C) := by
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := h
  refine ⟨k, m, j, hkm, hkj, hmj, ?_, ?_, ?_⟩
  · rw [← hk, hD, g.symm_apply_apply]
  · rw [← hm, hD, g.symm_apply_apply]
  · rw [← hj, hD, g.symm_apply_apply]

/-- **`MirrorAt D e f 1 0 0` is the mirror condition in distances, `MirrorDist`, for the original dissection**: the first tile `t₀` (a tile `C1` at the origin) is the lattice triangle `U(0, 0)` with the vertices `p(0,0) = A'`, `p(1,0)`, `p(0,1)`; the tile
`T` of `MirrorAt` has the vertices `p(0,0)`, `p(0,1)`, `p(−1, (2f² − e²)/(f² − e²))`, which is at the distances `c` from `p(0,0)` and `a` from `p(0,1)` (`dist_mirrorP`, `dist_mirrorQ`), as `p(1,0)` is (`dist_step_uG`, `dist_step_aG`), and is different from
`p(1,0)` (the functional `FXG` takes the values `lv(−1) < lv(1)`). -/
theorem mirrorDist_of_mirrorAt {e f : ℕ} {α β γ L ax ay : ℝ} {D₀ D : CongruentDissection N}
    {g : Plane ≃ᵢ Plane} {A' : Plane}
    (hD : ∀ i m, (D.tile i).pts m = g ((D₀.tile i).pts m)) (hP : g A' = mkPt 0 0)
    (S : SetupG D e f α β γ L ax ay) {t₀ : Fin N}
    (hU : BaseTileG D (e : ℝ) (f : ℝ) t₀ Ty.C1 0) (hM : MirrorAt D (e : ℝ) (f : ℝ) 1 0 0) :
    ∃ T, MirrorDist D₀ (e : ℝ) (f : ℝ) A' t₀ T := by
  have he0 := S.e0
  have hef := S.hef'
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have hb : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := b_posG he0 hef
  obtain ⟨T, hT⟩ := hM
  have hU' := S.c1_lpG (x := 0) (ξ := 0) hU (by ring)
  have hV0 := hasV_pullback hD hU'
  have hT0 := hasV_pullback hD hT
  have hA' : g.symm (lpG (e : ℝ) (f : ℝ) 1 0 0 0) = A' := by
    rw [lpG_zero, ← hP, g.symm_apply_apply]
  rw [hA'] at hV0 hT0
  refine ⟨T, g.symm (lpG (e : ℝ) (f : ℝ) 1 0 (0 + 1) 0), g.symm (lpG (e : ℝ) (f : ℝ) 1 0 0 (0 + 1)),
    g.symm (lpG (e : ℝ) (f : ℝ) 1 0 (-1)
      (0 + (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))), hV0, ?_, ?_, ?_, hT0, ?_, ?_, ?_⟩
  · rw [← hA', g.symm.dist_eq, dist_comm]
    exact dist_step_uG he0 hef hε 0 0
  · rw [← hA', g.symm.dist_eq, dist_comm]
    exact dist_step_vG he0 hef hε 0 0
  · rw [g.symm.dist_eq]
    exact dist_step_aG he0 hef hε 0 0
  · intro hRE
    have h1 := g.symm.injective hRE
    have h2 := congrArg (FXG (e : ℝ) (f : ℝ) 1) h1
    rw [FXG_lp hε, FXG_lp hε] at h2
    have h3 : lvG (e : ℝ) (f : ℝ) 1 0 (-1) < lvG (e : ℝ) (f : ℝ) 1 0 (0 + 1) :=
      lvG_lt he0 hef (by norm_num)
    exact absurd h2 h3.ne
  · rw [← hA', g.symm.dist_eq, g.symm.dist_eq]
    have hs : (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) *
        ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) = 2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by have := hb.ne'; field_simp
    rw [dist_mirrorP he0 hef hε 0 _ hs, dist_comm, dist_step_uG he0 hef hε 0 0]
  · rw [g.symm.dist_eq, g.symm.dist_eq]
    have hs : (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) *
        ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) = 2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by have := hb.ne'; field_simp
    rw [dist_mirrorQ he0 hef hε 0 _ hs, dist_step_aG he0 hef hε 0 0]

/-- **`MirrorAt D e f 1 0 0` is the mirror condition `MirrorBeside` (reflection) for the original dissection** -/
theorem mirrorBeside_of_mirrorAt {e f : ℕ} {α β γ L ax ay : ℝ} {D₀ D : CongruentDissection N}
    {g : Plane ≃ᵢ Plane} {A' : Plane}
    (hD : ∀ i m, (D.tile i).pts m = g ((D₀.tile i).pts m)) (hP : g A' = mkPt 0 0)
    (S : SetupG D e f α β γ L ax ay) {t₀ : Fin N}
    (hU : BaseTileG D (e : ℝ) (f : ℝ) t₀ Ty.C1 0) (hM : MirrorAt D (e : ℝ) (f : ℝ) 1 0 0) :
    ∃ T, MirrorBeside D₀ (e : ℝ) (f : ℝ) A' t₀ T := by
  obtain ⟨T, hT⟩ := mirrorDist_of_mirrorAt hD hP S hU hM
  exact ⟨T, mirrorBeside_of_dist S.e0 S.hef' hT⟩

/-! ## 2. The theorem -/

/-- **THEOREM `thm:cornerrun`, core**: the theorem with the addendum as the last conjunct of (ii). -/
theorem cornerrun_core (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f)
    (D₀ : CongruentDissection N)
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2))
    (τ : Equiv.Perm (Fin 3))
    (hA : cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
        2 * modelAlpha (e : ℝ) (f : ℝ) ∨
      cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
        3 * modelAlpha (e : ℝ) (f : ℝ))
    (hQ : cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
        modelBeta (e : ℝ) (f : ℝ) ∨
      cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
        modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ)) :
    (∃ (x₀ : ℝ) (t : ℕ → Fin N), 0 ≤ x₀ ∧
      x₀ + (f : ℝ) * (f : ℝ) ^ 2 ≤ dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) ∧
      ((∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (t j)
          Ty.C1 (x₀ + j * (f : ℝ) ^ 2)) ∨
       (∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (t j)
          Ty.C2 (x₀ + j * (f : ℝ) ^ 2)))) ∨
    (∃ (k : ℕ) (t : ℕ → Fin N), e + 1 ≤ k ∧ k ≤ f - 1 ∧
      (∀ j, j < k → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (t j)
          Ty.C1 ((j : ℝ) * (f : ℝ) ^ 2)) ∧
      ((k : ℝ) * (f : ℝ) ^ 2 = dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) ∨
        (∃ i, LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) i Ty.A2
          ((k : ℝ) * (f : ℝ) ^ 2)) ∨
        (∃ i, LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) i Ty.B2
          ((k : ℝ) * (f : ℝ) ^ 2)) ∨
        (∃ i, LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) i Ty.C2
          ((k : ℝ) * (f : ℝ) ^ 2))) ∧
      (∃ T, MirrorBeside D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (t 0) T) ∧
      ((e : ℝ) * f < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 →
        cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
          2 * modelAlpha (e : ℝ) (f : ℝ) → e + 2 ≤ k)) := by
  obtain ⟨D, g, L, ax, ay, hL, hLd, hD, hP, hB, S, Co, h2⟩ :=
    setup_of_corners e f he hef hco D₀ hMod τ hA hQ
  obtain ⟨m, X, tile, τc, Ch⟩ := S.exists_chainG
  rcases corner_side_theorem S Co Ch with ⟨i, him, hrun⟩ | ⟨k, hk1, hkf, hkm, hrun, hsucc⟩
  · -- alternative (i)
    left
    have hf2 := S.hf2
    have hx0 := Ch.nonneg S (k := i) (by omega)
    have hend : X (i + f) ≤ L := by
      have h1 := (S.baseTile_range (Ch.htile (i + f - 1) (by omega))).2
      have h2 := Ch.hstep (i + f - 1) (by omega)
      rw [show i + f - 1 + 1 = i + f by omega] at h2
      linarith
    rcases hrun with hrun | hrun
    · have hpos := Ch.run_pos (T := Ty.C1) (c := (f : ℝ) ^ 2) rfl him hrun
      have hXf : X (i + f) = X i + f * (f : ℝ) ^ 2 := hpos f le_rfl
      refine ⟨X i, fun j => tile (i + j), hx0, by rw [hLd]; linarith, Or.inl (fun j hj => ?_)⟩
      have h := Ch.htile (i + j) (by omega)
      rw [hrun j hj, hpos j hj.le] at h
      exact laysOn_of_baseTile hL hD hP hB h
    · have hpos := Ch.run_pos (T := Ty.C2) (c := (f : ℝ) ^ 2) rfl him hrun
      have hXf : X (i + f) = X i + f * (f : ℝ) ^ 2 := hpos f le_rfl
      refine ⟨X i, fun j => tile (i + j), hx0, by rw [hLd]; linarith, Or.inr (fun j hj => ?_)⟩
      have h := Ch.htile (i + j) (by omega)
      rw [hrun j hj, hpos j hj.le] at h
      exact laysOn_of_baseTile hL hD hP hB h
  · -- alternative (ii)
    right
    have hsucc' : k = m ∨ (k < m ∧ τc k ≠ Ty.B1 ∧ τc k ≠ Ty.C1) := by
      rcases hsucc with h | ⟨h, h'⟩
      · exact Or.inl h
      · refine Or.inr ⟨h, ?_, ?_⟩ <;> rcases h' with h' | h' | h' <;> rw [h'] <;> decide
    have hpos := run_positions S Ch hkm hrun
    have hek : e + 1 ≤ k := by
      by_contra hlt
      exact corner_run_short S Co Ch hk1 (by omega) hrun hsucc'
    refine ⟨k, tile, hek, by omega, fun j hj => ?_, ?_, ?_, ?_⟩
    · have h := Ch.htile j (by omega)
      rw [hrun j hj, hpos j hj.le] at h
      exact laysOn_of_baseTile hL hD hP hB h
    · rcases hsucc with h | ⟨h, h'⟩
      · left
        calc (k : ℝ) * (f : ℝ) ^ 2 = X k := (hpos k le_rfl).symm
          _ = X m := by rw [h]
          _ = L := Ch.hXm
          _ = dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) := hLd.symm
      · right
        have hb := Ch.htile k h
        rw [hpos k le_rfl] at hb
        rcases h' with h' | h' | h'
        · rw [h'] at hb
          exact Or.inl ⟨tile k, laysOn_of_baseTile hL hD hP hB hb⟩
        · rw [h'] at hb
          exact Or.inr (Or.inl ⟨tile k, laysOn_of_baseTile hL hD hP hB hb⟩)
        · rw [h'] at hb
          exact Or.inr (Or.inr ⟨tile k, laysOn_of_baseTile hL hD hP hB hb⟩)
    · have hM := corner_run_mirror S Co Ch hk1 hkf hrun hsucc'
      have hU := Ch.htile 0 (by omega)
      rw [hrun 0 (by omega), Ch.hX0] at hU
      exact mirrorBeside_of_mirrorAt hD hP S hU hM
    · intro hab h2'
      by_contra hlt
      have hef2 : e + 1 < f := by omega
      exact corner_run_short_o S Co hab hef2 (h2 h2') Ch hk1 (by omega) hrun hsucc'

/-- **THEOREM `thm:cornerrun`** (paper, verbatim in the module header), for an arbitrary congruent dissection `D₀` (any number of tiles, reflections allowed) whose model has the sides `ef, f² − e², f²`.  The side `s = [A', Q']` is the side of the
target from `A' = target.pts (τ 0)` to `Q' = target.pts (τ 1)`; the corner angles are `cornerAngle … = 2α` or `3α` at `A'` and `β` or `α + β` at `Q'`.  The types are read with `A'` on the left (`LaysBaseOn` with `P = A'`, `B = Q'`: `C1` shows `α`
at the end nearer to `A'`, `C2` at the end nearer to `Q'`).  (i) `f` consecutive tiles `C1` or `C2` (at `x₀, x₀ + c, …`); (ii) the run `C1^k` from `A'` (positions `0, c, …, (k − 1) c`), `e + 1 ≤ k ≤ f − 1`, followed by `Q'`
(`k c = |A' Q'|`) or by a tile `A2`, `B2` or `C2` at `k c`, with the mirror tile beside the first tile at `A'` (`MirrorBeside`). -/
theorem thm_cornerrun (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f)
    (D₀ : CongruentDissection N)
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2))
    (τ : Equiv.Perm (Fin 3))
    (hA : cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
        2 * modelAlpha (e : ℝ) (f : ℝ) ∨
      cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
        3 * modelAlpha (e : ℝ) (f : ℝ))
    (hQ : cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
        modelBeta (e : ℝ) (f : ℝ) ∨
      cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
        modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ)) :
    (∃ (x₀ : ℝ) (t : ℕ → Fin N), 0 ≤ x₀ ∧
      x₀ + (f : ℝ) * (f : ℝ) ^ 2 ≤ dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) ∧
      ((∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (t j)
          Ty.C1 (x₀ + j * (f : ℝ) ^ 2)) ∨
       (∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (t j)
          Ty.C2 (x₀ + j * (f : ℝ) ^ 2)))) ∨
    (∃ (k : ℕ) (t : ℕ → Fin N), e + 1 ≤ k ∧ k ≤ f - 1 ∧
      (∀ j, j < k → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (t j)
          Ty.C1 ((j : ℝ) * (f : ℝ) ^ 2)) ∧
      ((k : ℝ) * (f : ℝ) ^ 2 = dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) ∨
        (∃ i, LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) i Ty.A2
          ((k : ℝ) * (f : ℝ) ^ 2)) ∨
        (∃ i, LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) i Ty.B2
          ((k : ℝ) * (f : ℝ) ^ 2)) ∨
        (∃ i, LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) i Ty.C2
          ((k : ℝ) * (f : ℝ) ^ 2))) ∧
      (∃ T, MirrorBeside D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (t 0) T)) := by
  rcases cornerrun_core e f he hef hco D₀ hMod τ hA hQ with h | ⟨k, t, h1, h2, h3, h4, h5, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨k, t, h1, h2, h3, h4, h5⟩

/-- **THEOREM `thm:cornerrun`, "in particular"**: for the members `(f − 1, f)` (`e + 1 = f`) every such side carries `f` consecutive tiles `C1` or `f` consecutive tiles `C2` (alternative (ii) would need `e + 1 ≤ k ≤ f − 1 = e`). -/
theorem thm_cornerrun_thick (e f : ℕ) (he : 1 ≤ e) (hthick : e + 1 = f)
    (D₀ : CongruentDissection N)
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2))
    (τ : Equiv.Perm (Fin 3))
    (hA : cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
        2 * modelAlpha (e : ℝ) (f : ℝ) ∨
      cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
        3 * modelAlpha (e : ℝ) (f : ℝ))
    (hQ : cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
        modelBeta (e : ℝ) (f : ℝ) ∨
      cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
        modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ)) :
    ∃ (x₀ : ℝ) (t : ℕ → Fin N), 0 ≤ x₀ ∧
      x₀ + (f : ℝ) * (f : ℝ) ^ 2 ≤ dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) ∧
      ((∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (t j)
          Ty.C1 (x₀ + j * (f : ℝ) ^ 2)) ∨
       (∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (t j)
          Ty.C2 (x₀ + j * (f : ℝ) ^ 2))) := by
  have hef : e < f := by omega
  have hco : Nat.Coprime e f := by
    rw [← hthick]; exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right e)
  rcases thm_cornerrun e f he hef hco D₀ hMod τ hA hQ with h | ⟨k, t, h1, h2, -⟩
  · exact h
  · omega

/-- **THEOREM `thm:cornerrun`, addendum**: if `a < b` (`e f < f² − e²`) and `A'` has the angle `2α`, then `k ≥ e + 2` in (ii). -/
theorem thm_cornerrun_addendum (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f)
    (hab : (e : ℝ) * f < (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (D₀ : CongruentDissection N)
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2))
    (τ : Equiv.Perm (Fin 3))
    (hA : cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
        2 * modelAlpha (e : ℝ) (f : ℝ))
    (hQ : cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
        modelBeta (e : ℝ) (f : ℝ) ∨
      cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
        modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ)) :
    (∃ (x₀ : ℝ) (t : ℕ → Fin N), 0 ≤ x₀ ∧
      x₀ + (f : ℝ) * (f : ℝ) ^ 2 ≤ dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) ∧
      ((∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (t j)
          Ty.C1 (x₀ + j * (f : ℝ) ^ 2)) ∨
       (∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (t j)
          Ty.C2 (x₀ + j * (f : ℝ) ^ 2)))) ∨
    (∃ (k : ℕ) (t : ℕ → Fin N), e + 2 ≤ k ∧ k ≤ f - 1 ∧
      (∀ j, j < k → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (t j)
          Ty.C1 ((j : ℝ) * (f : ℝ) ^ 2)) ∧
      ((k : ℝ) * (f : ℝ) ^ 2 = dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) ∨
        (∃ i, LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) i Ty.A2
          ((k : ℝ) * (f : ℝ) ^ 2)) ∨
        (∃ i, LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) i Ty.B2
          ((k : ℝ) * (f : ℝ) ^ 2)) ∨
        (∃ i, LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) i Ty.C2
          ((k : ℝ) * (f : ℝ) ^ 2))) ∧
      (∃ T, MirrorBeside D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (t 0) T)) := by
  rcases cornerrun_core e f he hef hco D₀ hMod τ (Or.inl hA) hQ with
    h | ⟨k, t, h1, h2, h3, h4, h5, h6⟩
  · exact Or.inl h
  · exact Or.inr ⟨k, t, h6 hab hA, h2, h3, h4, h5⟩

end Erdos634.Draft.SideRunGA

#print axioms Erdos634.Draft.SideRunGA.hasV_pullback
#print axioms Erdos634.Draft.SideRunGA.mirrorDist_of_mirrorAt
#print axioms Erdos634.Draft.SideRunGA.mirrorBeside_of_mirrorAt
#print axioms Erdos634.Draft.SideRunGA.cornerrun_core
#print axioms Erdos634.Draft.SideRunGA.thm_cornerrun
#print axioms Erdos634.Draft.SideRunGA.thm_cornerrun_thick
#print axioms Erdos634.Draft.SideRunGA.thm_cornerrun_addendum
