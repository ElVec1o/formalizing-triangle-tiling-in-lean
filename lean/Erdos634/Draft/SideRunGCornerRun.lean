/-
Draft/SideRunGCornerRun.lean -- written 14 October 2026.  UNAUDITED.  In `AllThreshold`.  Module C2 of the plan for
`thm:cornerrun` (see the header of `Draft/SideRunGJChord.lean`; C1 is `Draft/SideRunGCornerA.lean`).

**The run lemma for a `C1`-run that starts at a corner `A'` of angle `2α` or `3α`** (the side `s` from `A'` to a corner `Q'` of angle
`β` or `α + β`, `CornersA`), and the mirror case it leaves.  Paper: Theorem `thm:cornerrun`, step (3) of the proof: "the tile `T`
beside `X₀` across its `b`-edge lays `c` or `b` (it shows `α` at `A'`, by (F))".

CONTENTS.
* `MirrorAt D e f ε x j₀` -- **THE MIRROR CASE, handed to M1**: a tile of the dissection has the three vertices
  `p(0, j₀)`, `p(0, j₀ + 1)`, `p(−1, j₀ + (2f² − e²)/(f² − e²))`.  In words: the tile `T` beside the first tile `X₀ = U(0, j₀)` across
  its `b`-edge `[p(0,j₀), p(0,j₀+1)]` has that whole `b`-edge and is the REFLECTION OF `X₀` IN THE LINE `ℓ` of that edge (a tile with
  the vertices `p(0,j₀)`, `p(0,j₀+1)` and a third vertex at the distance `c = f²` from `p(0,j₀)` and `a = ef` from `p(0,j₀+1)`, on the
  σ side of `ℓ`: the reflection of `p(1, j₀)`); its third vertex is the lattice point `p(−1, j₀ + K/b)`, `K = 2f² − e²`, `b = f² − e²`
  (not a point of the integer lattice: `K/b` is an integer only if `b ∣ K`, i.e. `(f² − e²) ∣ f²`, impossible for coprime `e < f`
  with `e ≥ 1`).  `mirror_third` is the uniqueness of that vertex; `cross_vG` the identity
  `cross (p(0,η+1) − p(0,η)) y = −ε · FXG y`; `dist_mirrorP`, `dist_mirrorQ` the two distances.  (At the corner `A'` the only data are the
  whole `b`-edge `[A', p(0,1)]` and "`T` shows `α` at `A'`".)
* `corner_mirror`: **if the tile beside `X₀` has the `b`-edge `[A', p(0,1)]` of `X₀` (the second alternative of `corner_K1J_or_b`)
  then `MirrorAt D e f 1 0 0`**: the case `T` shows `γ` at `A'` is excluded by (F) (`figure_alpha`: every tile at `A'` shows `α`).
* `K3G_run_end`: **hypothesis (K3) at the right end `R` of a `C1`-run from `A'`** -- for the right corner `β` (`K3G_out_right`), for the
  right corner `α + β` (new: `bad_corner_right` and `hint_right_ab`), and before a tile other than `B1`, `C1` (`bad_nb`).
* `corner_run_mirror`: **the run lemma at a corner**: a run of `k` tiles `C1` from `A'` (`1 ≤ k ≤ f − 1`) that ends at `Q'` or before a
  tile other than `B1`, `C1` forces `MirrorAt D e f 1 0 0`.  If the tile `T` beside `X₀` lays `a` or `c`, (K1) holds (`K1J`),
  `CtxJ.of_K1J` and `CtxJ.run_diesJ` give `False`; otherwise `corner_mirror`.

CHECKS.  (i) `corner_run_mirror` is `kill_C1G` (`Draft/SideRunGSourcesB.lean`) with the hypothesis (K1) at `A'` replaced by the dichotomy
"`T` lays `a`/`c`, or `MirrorAt`": the old statement assumed (K1) (`hK1`), here (K1) is derived (`corner_K1J_or_b`) unless the mirror
case holds.  The right ends are the same as in `kill_C1G` (corner `β`: `K3G_out_right`; before a non-`B1`/`C1` tile: `bad_nb`), plus the
corner `α + β` which `CornersG` has not (`bad_corner_right` is the right-hand counterpart of `bad_corner`).  (ii) At `e = 1` the
mirror vertex is `p(−1, (2f² − 1)/(f² − 1))` and there is no Lean counterpart; the note of the coordinator is right: for the members
`(f − 1, f)`, which include `(1, 2)`, alternative (ii) of the theorem needs `e + 1 ≤ k ≤ f − 1` with `e + 1 = f`, which is empty;
that deduction belongs to the final case analysis of the theorem (module M1/R2), not to this module.  (iii) The first tile `B1`
(a corner tile that shows `α` and `γ`) is NOT treated here: `first_tile_alpha` of C1 says only that the first tile is `B1` or
`C1`; `corner_run_mirror` takes a run of `C1` tiles from `A'` as hypothesis.

WITNESSES.  `MirrorAt` is a statement about a dissection; no dissection satisfies the hypotheses of `corner_run_mirror` yet (they need
a `SetupG` with the side `AQ` on the `x`-axis, i.e. the setup theorem of R2, not built).  The mirror tile is NOT excluded: it is the
case handed to M1.

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGCornerA

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

/-! ## 1. The mirror case -/

/-- **THE MIRROR CASE** (the predicate handed to M1): a tile has the vertices `p(0, j₀)`, `p(0, j₀ + 1)` and
`p(−1, j₀ + (2f² − e²)/(f² − e²))` of the lattice `lpG e f ε x`.  The first two are the ends of the `b`-edge of the first tile
`U(0, j₀)` on `ℓ = {ξ = 0}`; the third is on the σ side of `ℓ` (`ξ = −1`), at the distance `c = f²` from `p(0, j₀)` and `a = e f`
from `p(0, j₀ + 1)` (`dist_mirrorP`, `dist_mirrorQ`). -/
def MirrorAt (D : CongruentDissection N) (e f ε x j₀ : ℝ) : Prop :=
  ∃ t : Fin N, HasV D t (lpG e f ε x 0 j₀) (lpG e f ε x 0 (j₀ + 1))
    (lpG e f ε x (-1) (j₀ + (2 * f ^ 2 - e ^ 2) / (f ^ 2 - e ^ 2)))

/-- the cross product with the step `p(0,η+1) − p(0,η)` is a multiple of the functional `FXG` of `ℓ` -/
theorem cross_vG {e f ε x : ℝ} (hε : ε ^ 2 = 1) (η : ℝ) (y : Plane) :
    cross (lpG e f ε x 0 (η + 1) - lpG e f ε x 0 η) y = (-ε) * FXG e f ε y := by
  unfold FXG lpG
  rw [lin_apply]
  simp only [cross, PiLp.sub_apply, mkPt_zero, mkPt_one]
  linear_combination (hhG e f * y 0) * hε

/-- the mirror vertex is at the distance `c = f²` from `p(0, η)` (`s · b = K`, `K = 2f² − e²`, `b = f² − e²`) -/
theorem dist_mirrorP {e f ε x : ℝ} (he : 0 < e) (hef : e < f) (hε : ε ^ 2 = 1) (η s : ℝ)
    (hs : s * (f ^ 2 - e ^ 2) = 2 * f ^ 2 - e ^ 2) :
    dist (lpG e f ε x (-1) (η + s)) (lpG e f ε x 0 η) = f ^ 2 :=
  dist_lpG he hef hε (by positivity)
    (by unfold QfG; linear_combination (s * (f ^ 2 - e ^ 2)) * hs)

/-- the mirror vertex is at the distance `a = e f` from `p(0, η + 1)` -/
theorem dist_mirrorQ {e f ε x : ℝ} (he : 0 < e) (hef : e < f) (hε : ε ^ 2 = 1) (η s : ℝ)
    (hs : s * (f ^ 2 - e ^ 2) = 2 * f ^ 2 - e ^ 2) :
    dist (lpG e f ε x (-1) (η + s)) (lpG e f ε x 0 (η + 1)) = e * f :=
  dist_lpG he hef hε (mul_pos he (he.trans hef)).le
    (by unfold QfG; linear_combination (s * (f ^ 2 - e ^ 2) - 2 * (f ^ 2 - e ^ 2)) * hs)

/-- **The third vertex of the mirror tile** (uniqueness): a point `R` on the σ side of `ℓ` (`FXG R < lv`) at the distance `f²` from
`p(0, η)` and `e f` from `p(0, η + 1)` is the lattice point `p(−1, η + s)` -/
theorem mirror_third {e f ε x : ℝ} (he : 0 < e) (hef : e < f) (hε : ε ^ 2 = 1) (η s : ℝ)
    (hs : s * (f ^ 2 - e ^ 2) = 2 * f ^ 2 - e ^ 2) {R : Plane}
    (hRP : dist R (lpG e f ε x 0 η) = f ^ 2) (hRQ : dist R (lpG e f ε x 0 (η + 1)) = e * f)
    (hR : FXG e f ε R < lvG e f ε x 0) : R = lpG e f ε x (-1) (η + s) := by
  refine third_unique_F (FXG e f ε) (P := lpG e f ε x 0 η) (Q := lpG e f ε x 0 (η + 1))
    (c := lvG e f ε x 0) (κ := -ε) (neg_ne_zero.mpr (eps_neG hε)) (fun y => cross_vG hε η y)
    (FXG_lp hε 0 η) ?_ ?_ hR ?_
  · rw [hRP, dist_mirrorP he hef hε η s hs]
  · rw [hRQ, dist_mirrorQ he hef hε η s hs]
  · rw [FXG_lp hε]
    exact lvG_lt he hef (by norm_num)

/-! ## 2. The tile beside the first tile has the whole `b`-edge: the mirror case -/

section mirror

variable {e f : ℕ} {α β γ L ax ay : ℝ}

/-- **If the tile `T` beside `X₀` has the `b`-edge `[A', p(0,1)]` of `X₀`, then `MirrorAt D e f 1 0 0`**: `T` shows `α` at `A'` (every
tile at `A'` shows `α` or `0`, by (F)), so its edges at `A'` are `b` (along `ℓ`) and `c`, and its third vertex is the mirror vertex. -/
theorem corner_mirror (S : SetupG D e f α β γ L ax ay) (Co : CornersA e f L ax ay)
    {iT : Fin N} {k m : Fin 3} (hkm : k ≠ m)
    (hk : (D.tile iT).pts k = lpG (e : ℝ) (f : ℝ) 1 0 0 0)
    (hm : (D.tile iT).pts m = lpG (e : ℝ) (f : ℝ) 1 0 0 1)
    (hle : ∀ i, FXG (e : ℝ) (f : ℝ) 1 ((D.tile iT).pts i) ≤ lvG (e : ℝ) (f : ℝ) 1 0 0) :
    MirrorAt D (e : ℝ) (f : ℝ) 1 0 0 := by
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have he0 := S.e0
  have hef := S.hef'
  have hb := S.b_pos
  obtain ⟨hαβ, hαγ, -, -, -, -, -, -, hγ0, -⟩ :=
    distinct_of_pos_ne S.hA.hα S.hA.hβ S.hA.hαβ S.hA.hγdef S.hA.hrel
  obtain ⟨n, hnk, hnm⟩ := fin3_third k m hkm
  have hkn : k ≠ n := Ne.symm hnk
  have hmn : m ≠ n := Ne.symm hnm
  have hd : dist ((D.tile iT).pts k) ((D.tile iT).pts m) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rw [hk, hm]
    have := dist_step_vG (x := (0 : ℝ)) he0 hef hε 0 0
    rwa [zero_add] at this
  obtain ⟨n', -, hn'⟩ := corner_A_angle S Co
  have hfig := figure_alpha S 0 n' (by rw [S.Q_eq]; exact hn') iT
  rw [S.Q_eq] at hfig
  have hfk : FXG (e : ℝ) (f : ℝ) 1 ((D.tile iT).pts k) = lvG (e : ℝ) (f : ℝ) 1 0 0 := by
    rw [hk]; exact FXG_lp hε 0 0
  have hfm : FXG (e : ℝ) (f : ℝ) 1 ((D.tile iT).pts m) = lvG (e : ℝ) (f : ℝ) 1 0 0 := by
    rw [hm]; exact FXG_lp hε 0 1
  have hRlt := third_strict (D.tile iT) hkm hkn hmn (FXG (e : ℝ) (f : ℝ) 1)
    (FXG_ne he0 hef hε) (lvG (e : ℝ) (f : ℝ) 1 0 0) hfk hfm hle
  rcases sides_of_b_edgeG D S.tile S.hM iT hkm hkn hmn hd with ⟨s1, s2⟩ | ⟨s1, s2⟩
  · -- `T` shows `γ` at `A'`: excluded by (F)
    exfalso
    have hang := (angle_at_vertexG D S.tile S.hM iT hkm hkn hmn).2.2 (by rw [dist_comm]; exact s2)
    rw [hk, lpG_zero] at hang
    rcases hfig with h | h
    · exact hαγ (h.symm.trans hang)
    · exact hγ0 (h.symm.trans hang).symm
  · -- `T` shows `α` at `A'`: its third vertex is at `c` from `A'` and `a` from `p(0,1)`
    have hs : ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)
        = 2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := div_mul_cancel₀ _ hb.ne'
    have hRP : dist ((D.tile iT).pts n) (lpG (e : ℝ) (f : ℝ) 1 0 0 0) = (f : ℝ) ^ 2 := by
      rw [← hk]; exact s1
    have hRQ : dist ((D.tile iT).pts n) (lpG (e : ℝ) (f : ℝ) 1 0 0 (0 + 1)) = (e : ℝ) * f := by
      rw [zero_add, ← hm]; exact s2
    have hR3 := mirror_third he0 hef hε 0 _ hs hRP hRQ hRlt
    refine ⟨iT, k, m, n, hkm, hkn, hmn, hk, ?_, hR3⟩
    rw [zero_add]; exact hm

end mirror

/-! ## 3. Hypothesis (K3) at the right end of a run from `A'` -/

section k3

variable {e f : ℕ} {α β γ L ax ay : ℝ} {m : ℕ} {X : ℕ → ℝ} {tile : ℕ → Fin N} {τ : ℕ → Ty}

/-- the positions along a `C1` run that starts at `X 0 = 0` -/
theorem run_positions (S : SetupG D e f α β γ L ax ay) (Ch : ChainG D e f L m X tile τ) {k : ℕ} (hkm : k ≤ m)
    (hrun : ∀ j, j < k → τ j = Ty.C1) : ∀ j, j ≤ k → X j = (j : ℝ) * (f : ℝ) ^ 2 := by
  intro j hj
  have h := Ch.run_pos (T := Ty.C1) (c := (f : ℝ) ^ 2) rfl (i := 0) (k := k) (by omega)
    (fun j' hj' => by rw [Nat.zero_add]; exact hrun j' hj') j hj
  rw [Nat.zero_add, Ch.hX0] at h
  linarith

/-- **(K3) at the right end `R` of a run of `k` tiles `C1` from `A'`** (`X 0 = 0`, `x = 0`): the right corner is `β` (`K3G_out_right`)
or `α + β` (new), or the next tile of the chain is not `B1`, `C1` (`bad_nb`).  (The copy of the (K3) part of `kill_C1G`, over
`CtxBase`, with the corner `α + β`.) -/
theorem K3G_run_end (S : SetupG D e f α β γ L ax ay) (Co : CornersA e f L ax ay)
    (Ch : ChainG D e f L m X tile τ) {k : ℕ} (hk1 : 1 ≤ k) (hkm : k ≤ m)
    (hrun : ∀ j, j < k → τ j = Ty.C1)
    (hsucc : k = m ∨ (k < m ∧ τ k ≠ Ty.B1 ∧ τ k ≠ Ty.C1)) :
    K3G D (e : ℝ) (f : ℝ) 1 0 (k : ℝ) 0 := by
  have C : CtxBase D e f α β γ L ax ay 1 0 := ⟨S, Or.inl rfl⟩
  have he0 := S.e0
  have hef := S.hef'
  have hhp := hhG_pos he0 hef
  have hc := S.c_pos
  have hpos := run_positions S Ch hkm hrun
  have hxR : X k = (k : ℝ) * (f : ℝ) ^ 2 := hpos k le_rfl
  have hk0 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk1, Nat.cast_one]
  have hlast := Ch.htile (k - 1) (by omega)
  rw [hrun (k - 1) (by omega)] at hlast
  have hposl := hpos (k - 1) (by omega)
  rw [hk0] at hposl
  have hU := S.c1_lpG (x := 0) (ξ := (k : ℝ) - 1) hlast (by rw [hposl]; ring)
  have hG1 : 0 < (lpG (e : ℝ) (f : ℝ) 1 0 ((k : ℝ) - 1) (0 + 1)) 1 := by
    rw [lpG_snd]; linarith
  have hA₀ : (lpG (e : ℝ) (f : ℝ) 1 0 ((k : ℝ) - 1) 0) 1 = 0 := by rw [lpG_snd]; ring
  have eV : lpG (e : ℝ) (f : ℝ) 1 0 ((k : ℝ) - 1 + 1) 0 = mkPt (X k) 0 := by
    unfold lpG; exact mkPt_congr (by rw [hxR]; ring) (by ring)
  have eA : lpG (e : ℝ) (f : ℝ) 1 0 ((k : ℝ) - 1) 0 = mkPt (X k - (f : ℝ) ^ 2) 0 := by
    unfold lpG; exact mkPt_congr (by rw [hxR]; ring) (by ring)
  have eG : lpG (e : ℝ) (f : ℝ) 1 0 ((k : ℝ) - 1) (0 + 1)
      = mkPt (X k - uuG (e : ℝ) (f : ℝ)) (hhG (e : ℝ) (f : ℝ)) := by
    unfold lpG; exact mkPt_congr (by rw [hxR]; ring) (by ring)
  have hβ0 : (D.tile (tile (k - 1))).localAngle (mkPt (X k) 0) = β := by
    have e' : X (k - 1) + Ty.lenG (e : ℝ) (f : ℝ) Ty.C1 = X k := by
      show X (k - 1) + (f : ℝ) ^ 2 = _
      rw [hposl, hxR]; ring
    have h := (S.angles hlast).2
    rw [e'] at h
    exact h
  have hU' := hU
  rw [eV] at hU'
  rcases hsucc with hend | ⟨hlt, hZ1, hZ2⟩
  · -- the run ends at the corner `Q'`
    have hXL : X k = L := by rw [hend]; exact Ch.hXm
    rcases Co.hQ with ⟨t, ht, hax, hay⟩ | ⟨t, ht, hax, hay⟩
    · -- the right corner is `β`
      exact S.K3G_out_right ht hax hay (by linarith)
    · -- the right corner is `α + β`
      have hQ := corner_right_ab S ht hax hay
      have hRmem : mkPt L 0 ∈ D.target.carrier := by
        rw [← hXL, ← eV]; exact hU.mem₂
      have hGmem : mkPt (L - uuG (e : ℝ) (f : ℝ)) (hhG (e : ℝ) (f : ℝ)) ∈ D.target.carrier := by
        rw [← hXL, ← eG]; exact hU.mem₃
      have hint : openSegment ℝ (lpG (e : ℝ) (f : ℝ) 1 0 ((k : ℝ) - 1 + 1) 0)
          (lpG (e : ℝ) (f : ℝ) 1 0 ((k : ℝ) - 1) (0 + 1)) ⊆ interior D.target.carrier := by
        rw [eV, eG, hXL]
        exact hint_right_ab S ht hax hay hRmem hGmem
      refine C.K3G_of_next hU hint (fun W Z hW hθ hZ => ?_)
      rw [eV, hXL] at hW hθ
      rw [hXL] at hU' hβ0
      exact bad_corner_right S hQ hG1 hU' hA₀ hβ0 hW hθ hZ
  · -- the run ends before a tile other than `B1`, `C1`
    have hx0 : 0 < X k := Ch.pos S (by omega) (by omega)
    have hxL : X k < L := Ch.lt_L S hlt
    have hint : openSegment ℝ (lpG (e : ℝ) (f : ℝ) 1 0 ((k : ℝ) - 1 + 1) 0)
        (lpG (e : ℝ) (f : ℝ) 1 0 ((k : ℝ) - 1) (0 + 1)) ⊆ interior D.target.carrier := by
      rw [eV]
      refine S.interior_seg (Ch.mem hlt) hU.mem₃ (Or.inr hG1) (Or.inl ?_) (Or.inl ?_)
      · rw [gA_mk]; nlinarith [mul_pos S.hay hx0]
      · rw [gB_mk]; nlinarith [mul_pos S.hay (sub_pos.mpr hxL)]
    have hj := Ch.htile k hlt
    have hjang := (S.angles hj).1
    have hlenpos := Ty.lenG_pos he0 hef (τ k)
    obtain ⟨T, hT⟩ : ∃ T, τ k = T := ⟨_, rfl⟩
    rw [hT] at hZ1 hZ2 hjang
    have hθj : (D.tile (tile k)).localAngle (mkPt (X k) 0) = γ ∨
        (D.tile (tile k)).localAngle (mkPt (X k) 0) = β := by
      rw [hjang]
      cases T
      · exact Or.inr rfl
      · exact Or.inl rfl
      · exact absurd rfl hZ1
      · exact Or.inl rfl
      · exact absurd rfl hZ2
      · exact Or.inr rfl
    obtain ⟨kj, mj, jj, -, -, -, -, hmj, -, -⟩ := hj
    refine C.K3G_of_next hU hint (fun W Z hW hθ hZ => ?_)
    rw [eV] at hW hθ
    refine S.bad_nb hx0 hxL hG1 hU' hA₀ hβ0 hmj (mkPt_one _ _)
      (mkPt_ne_of_fst (by linarith)) ?_ hθj hW hθ hZ
    rw [eA]; exact mkPt_ne_of_fst (by linarith)

end k3

/-! ## 4. The run lemma at a corner -/

section run

variable {e f : ℕ} {α β γ L ax ay : ℝ} {m : ℕ} {X : ℕ → ℝ} {tile : ℕ → Fin N} {τ : ℕ → Ty}

/-- **THE RUN LEMMA AT A CORNER `2α` or `3α`** (paper, `thm:cornerrun`, step (3)).  A run of `k` tiles `C1` from the corner `A'`
(`1 ≤ k ≤ f − 1`), ending at the right corner `Q'` (of angle `β` or `α + β`) or before a tile other than `B1`, `C1`: the tile `T`
beside the first tile across its `b`-edge cannot lay `a` or `c` (that gives (K1), and `CtxJ.run_diesJ` gives `False`), so it has the
whole `b`-edge: `MirrorAt D e f 1 0 0`. -/
theorem corner_run_mirror (S : SetupG D e f α β γ L ax ay) (Co : CornersA e f L ax ay)
    (Ch : ChainG D e f L m X tile τ) {k : ℕ} (hk1 : 1 ≤ k) (hkf : k < f)
    (hrun : ∀ j, j < k → τ j = Ty.C1)
    (hsucc : k = m ∨ (k < m ∧ τ k ≠ Ty.B1 ∧ τ k ≠ Ty.C1)) :
    MirrorAt D (e : ℝ) (f : ℝ) 1 0 0 := by
  have hkm : k ≤ m := by rcases hsucc with h | ⟨h, -, -⟩ <;> omega
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
  obtain ⟨t₀, ht₀⟩ := hUT 0 (by omega)
  rw [Nat.cast_zero] at ht₀
  have hQmem : lpG (e : ℝ) (f : ℝ) 1 0 0 1 ∈ D.target.carrier := by
    have := ht₀.mem₃
    rwa [zero_add] at this
  have hch1 : openSegment ℝ (lpG (e : ℝ) (f : ℝ) 1 0 0 0) (lpG (e : ℝ) (f : ℝ) 1 0 0 1) ⊆
      interior D.target.carrier := by
    have h := hch 1 le_rfl (by rw [Nat.cast_one]; exact hQmem)
    rwa [Nat.cast_one] at h
  rcases corner_K1J_or_b S ht₀ hch1 with hK1 | ⟨iT, k', m', hkm', hk', hm', hle'⟩
  · exfalso
    have Cj : CtxJ D e f α β γ L ax ay 1 0 0 := CtxJ.of_K1J S (Or.inl rfl) hch hK1
    exact Cj.run_diesJ hk1 hkf hUT (K3G_run_end S Co Ch hk1 hkm hrun hsucc)
  · exact corner_mirror S Co hkm' hk' hm' hle'

end run

end Erdos634.Draft.SideRunGA

#print axioms Erdos634.Draft.SideRunGA.cross_vG
#print axioms Erdos634.Draft.SideRunGA.dist_mirrorP
#print axioms Erdos634.Draft.SideRunGA.dist_mirrorQ
#print axioms Erdos634.Draft.SideRunGA.mirror_third
#print axioms Erdos634.Draft.SideRunGA.corner_mirror
#print axioms Erdos634.Draft.SideRunGA.run_positions
#print axioms Erdos634.Draft.SideRunGA.K3G_run_end
#print axioms Erdos634.Draft.SideRunGA.corner_run_mirror
