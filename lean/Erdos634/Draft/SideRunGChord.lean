/-
Refactored 14 October 2026: `CtxBase` introduced, lemmas that use only the setup moved to it (no statement changed).
Draft/SideRunGChord.lean -- written 14 October 2026.  UNAUDITED.  In `AllThreshold`.  Module 4 of ten (part A; the
chord principles and `K3G_clamp` are in `Draft/SideRunGChordB.lean`).

The standing hypotheses of the run lemma for EVERY member `(e, f)`, hypothesis (K3) in the form the paper states for a
general member, the tile across an `a`-edge, and the mirror tile `N(ξ,η)`: the generalization of the first half of
`Draft/SideRunChord.lean`.  Paper: Theorem `thm:siderunall`, "Statement K(s', j0)" and the proof of the size-`n` step
(items (2), (2a)-(2d)); (private working notes, not included)

CONTENTS.
* `SetupG.fwd1G`, `bwd1G`, `fwdm G`, `bwdmG` (the four pushes), `CtxG` (setup, orientation `ε = ±1`, (K1) at `P`, the
  chords from `P`), `CtxG.e2`, `CtxG.seg_intG`.
* `ClampedBelowG D e f ε x s η₁`: the point `Z = p(s − η₁, η₁)` of the line `m_s` is clamped from below for the side
  `ρ_s = {GS ≤ −lv s}`, in the Straddles form of `RunPartition` and for EVERY run `[Z, Q]` upward: there is a lattice point
  `P' = p(s − η', η')`, `η' < η₁`, such that no near-side chain edge straddles `Z` with respect to `P'` and `Q`.  The
  paper's two sources are `clampedBelowG_of_outside` ("`m_s` just beyond `Z` is outside Δ"; `m_clamp_baseG` is the case
  `η₁ = 0`, `Z` on the side) and `clampedBelowG_of_edge` ("an edge ending at `Z` of a tile on the side `ρ_s`";
  `m_clamp_tileG`).
* `RhoEdgeG D e f ε x w s j0` and `K3G D e f ε x s j0`: hypothesis (K3) of the paper, general form.  Either `ρ_s` is
  outside Δ, or a tile `w` on the side `ρ_s` has an edge on `m_s` that starts at `Z = p(s − η₁, η₁)`, `η₁ ∈ ℕ`,
  `η₁ ≤ j0`, runs upward, has length `b` or `c`, and `Z` is clamped from below (`ClampedBelowG`).  `K3G.mono`.
* `m_next_casesG`, `m_nextG`: the tile across the `a`-edge of `U(ξ,η)` at `p(ξ+1,η)` is `D(ξ,η)`, or `N(ξ,η)`, or it lays
  `b` or `c` on `m_{ξ+η+1}` from `p(ξ+1,η)`, which is `RhoEdgeG` for the run `(ξ+η+1, η)` (step (2a) of the proof).
* `N_pushG`.
* Specialisation checks at `e = 1` (end of the file).

WHAT DIFFERS FROM THE e = 1 TEXT, AND WHY IT DOES NOT SPECIALISE (precisely).
(i)  `K3` (e = 1, `SideRunChord`) says that ONE edge of a tile on `ρ_s` contains the points `p(s − j, j)`, `j0 < j ≤ s`, in
     its relative interior (the covering that the paper obtains from one long edge and `j a < b`).  `K3G` is the paper's
     general hypothesis: an edge of length `b` or `c` starting at a lattice point `Z`, with `Z` clamped from below; the
     covering is then a CONCLUSION (the `m`-chord principle `psiG`, `Draft/SideRunGChordB.lean`).  At `e = 1`, for `s + 1 ≤ f`,
     `K3G` IMPLIES `K3` (`K3_of_K3G_e1`, part B: the edge of length `b = f² − 1` or `c = f²` from the height `η₁ ≥ 0` reaches
     the height `η₁ + f − 1/f` resp. `η₁ + f`, which exceeds `s`).  The converse is NOT claimed and has no proof here: the edge of
     `K3` is not required to start at a lattice point, nor to be clamped from below, nor to have the length `b` or `c`
     (so `K3` does not give `K3G`).  The two agree on the first alternative (`ρ_s` outside Δ;
     `K3G_of_out`, `K3_of_outG`, `K3G_of_out_e1`).  The consumer interface `K3G_clamp` (part B) has the conclusion of `K3_clamp`
     at `η = j0 + 1`, under the hypotheses `K3G`, the `U` tiles of the row sequence on `m_s` (part of (K2)) and `j0 + 1 < f`.
(ii) `m_next_casesG`, `m_nextG` have no hypothesis `ξ + 2 ≤ n` (the old `j a < b` range) and take the clamp of `Z` as a
     hypothesis of the paper's form (`ClampedBelowG`), because (K3)(b) asks for it; the e = 1 text takes only the clamp
     relative to the one run `[p(ξ+1,η), p(ξ,η+1)]`.
(iii) `CtxG` keeps (K1) in the `j* = 0` form of `Ctx` ("no tile of the side `σ` has both `P` and `p(0,1)` as vertices"), which
     the paper's (K1) with `j* = 0` gives by uniqueness of the tile with an edge starting at `P`; the general `j*` form
     needed for `thm:cornerrun` is not here.

THE CONSTANT OF `N_pushG`: it is `δ ≤ 1/3`, the SAME as for `e = 1`.  It is not an e = 1 computation: the proof uses the
barycentric coordinates `δ(1+ν)`, `1 − δ(2+ν)`, `δ` of `p(ξ+δ, η+1)` in the triangle `N(ξ,η)` (the identity holds in the
affine lattice coordinates, for every `e, f`) and only `ν = b/c < 1` (`nuG_lt_one`), so `δ(2+ν) < 1` for `δ ≤ 1/3`.

WITNESSES.  Which object satisfies `CtxG`?  For `e = 1`: every `Ctx` (`ctxG_one_iff`); such contexts occur inside
`SideRunRules.kill_C1/kill_C2` for runs of a real dissection with `Setup` (`SideRun.side_theorem_witness`), but there is no
standalone theorem exhibiting one.  For `e ≥ 2`: NOT AVAILABLE yet.  It needs a `SetupG` for a real dissection
(`setup_of_sides` for general `e`, piece SideRunGMain) and the sources of (K1) and of the chords (`K1_of_gamma`,
`K1_of_corner`, `hch_pos`, `hch_corner` for general `e`, piece SideRunGSources).  `RhoEdgeG`/`K3G`: satisfied by the
outside alternative whenever `ρ_s` is outside Δ (`K3G_of_out`); the second alternative is produced by `m_nextG`.

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGLattice
import Erdos634.Draft.SideRunChord

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.SideRunG

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Set

variable {N : ℕ} {D : CongruentDissection N}

/-! ## 1. Coordinates, the four pushes, `CtxG` -/

theorem lpG_snd (e f ε x ξ η : ℝ) : (lpG e f ε x ξ η) 1 = η * hhG e f := by
  unfold lpG; rw [mkPt_one]

theorem lpG_fst (e f ε x ξ η : ℝ) :
    (lpG e f ε x ξ η) 0 = x + ε * ((ξ + η) * f ^ 2 - η * uuG e f) := by
  unfold lpG; rw [mkPt_zero]

namespace SetupG

variable {e f : ℕ} {α β γ L ax ay x : ℝ}

theorem fwd1G (S : SetupG D e f α β γ L ax ay) {ξ η δ : ℝ} (hδ : 0 < δ)
    (h : lpG (e : ℝ) (f : ℝ) 1 x (ξ + δ) η ∈ D.target.carrier) :
    0 < gB L ax ay (lpG (e : ℝ) (f : ℝ) 1 x ξ η) := by
  have e' : lpG (e : ℝ) (f : ℝ) 1 x (ξ + δ) η
      = mkPt (x + 1 * ((ξ + η) * (f : ℝ) ^ 2 - η * uuG (e : ℝ) (f : ℝ)) + δ * (f : ℝ) ^ 2)
          (η * hhG (e : ℝ) (f : ℝ)) := by
    unfold lpG; exact mkPt_congr (by ring) rfl
  rw [e'] at h
  exact S.gB_pos_of_right (mul_pos hδ S.c_pos) h

theorem bwd1G (S : SetupG D e f α β γ L ax ay) {ξ η δ : ℝ} (hδ : 0 < δ)
    (h : lpG (e : ℝ) (f : ℝ) 1 x (ξ - δ) η ∈ D.target.carrier) :
    0 < gA ax ay (lpG (e : ℝ) (f : ℝ) 1 x ξ η) := by
  have e' : lpG (e : ℝ) (f : ℝ) 1 x (ξ - δ) η
      = mkPt (x + 1 * ((ξ + η) * (f : ℝ) ^ 2 - η * uuG (e : ℝ) (f : ℝ)) - δ * (f : ℝ) ^ 2)
          (η * hhG (e : ℝ) (f : ℝ)) := by
    unfold lpG; exact mkPt_congr (by ring) rfl
  rw [e'] at h
  exact S.gA_pos_of_left (mul_pos hδ S.c_pos) h

theorem fwdmG (S : SetupG D e f α β γ L ax ay) {ξ η δ : ℝ} (hδ : 0 < δ)
    (h : lpG (e : ℝ) (f : ℝ) (-1) x (ξ + δ) η ∈ D.target.carrier) :
    0 < gA ax ay (lpG (e : ℝ) (f : ℝ) (-1) x ξ η) := by
  have e' : lpG (e : ℝ) (f : ℝ) (-1) x (ξ + δ) η
      = mkPt (x + (-1) * ((ξ + η) * (f : ℝ) ^ 2 - η * uuG (e : ℝ) (f : ℝ)) - δ * (f : ℝ) ^ 2)
          (η * hhG (e : ℝ) (f : ℝ)) := by
    unfold lpG; exact mkPt_congr (by ring) rfl
  rw [e'] at h
  exact S.gA_pos_of_left (mul_pos hδ S.c_pos) h

theorem bwdmG (S : SetupG D e f α β γ L ax ay) {ξ η δ : ℝ} (hδ : 0 < δ)
    (h : lpG (e : ℝ) (f : ℝ) (-1) x (ξ - δ) η ∈ D.target.carrier) :
    0 < gB L ax ay (lpG (e : ℝ) (f : ℝ) (-1) x ξ η) := by
  have e' : lpG (e : ℝ) (f : ℝ) (-1) x (ξ - δ) η
      = mkPt (x + (-1) * ((ξ + η) * (f : ℝ) ^ 2 - η * uuG (e : ℝ) (f : ℝ)) + δ * (f : ℝ) ^ 2)
          (η * hhG (e : ℝ) (f : ℝ)) := by
    unfold lpG; exact mkPt_congr (by ring) rfl
  rw [e'] at h
  exact S.gB_pos_of_right (mul_pos hδ S.c_pos) h

end SetupG

/-- **The setup part of the standing hypotheses of the run lemma**: a `SetupG` and an orientation.  Every lemma of the chain
that does not use (K1) is stated for it (`CtxBase`), and holds for `CtxG` by the parent projection. -/
structure CtxBase (D : CongruentDissection N) (e f : ℕ) (α β γ L ax ay ε x : ℝ) : Prop where
  S : SetupG D e f α β γ L ax ay
  hε : ε = 1 ∨ ε = -1

/-- **The standing hypotheses of the run lemma**: a `CtxBase` (a `SetupG` and an orientation), and (K1) at `P = (x, 0)`, in the
form of `SideRun.Ctx`. -/
structure CtxG (D : CongruentDissection N) (e f : ℕ) (α β γ L ax ay ε x : ℝ) : Prop
    extends CtxBase D e f α β γ L ax ay ε x where
  hK1 : ∀ (t' : Fin N) (k m : Fin 3), k ≠ m → (D.tile t').pts k = lpG (e : ℝ) (f : ℝ) ε x 0 0 →
    (D.tile t').pts m = lpG (e : ℝ) (f : ℝ) ε x 0 1 →
    (∀ i, FXG (e : ℝ) (f : ℝ) ε ((D.tile t').pts i) ≤ lvG (e : ℝ) (f : ℝ) ε x 0) → False
  hch : ∀ j : ℕ, 1 ≤ j → lpG (e : ℝ) (f : ℝ) ε x 0 j ∈ D.target.carrier →
    openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x 0 0) (lpG (e : ℝ) (f : ℝ) ε x 0 j) ⊆
      interior D.target.carrier

namespace CtxBase

variable {e f : ℕ} {α β γ L ax ay ε x : ℝ}

theorem e2 (C : CtxBase D e f α β γ L ax ay ε x) : ε ^ 2 = 1 := by
  rcases C.hε with h | h <;> rw [h] <;> norm_num

/-- **Interior segments between lattice points.** -/
theorem seg_intG (C : CtxBase D e f α β γ L ax ay ε x) {ξ η ξ' η' : ℝ}
    (hA : lpG (e : ℝ) (f : ℝ) ε x ξ η ∈ D.target.carrier)
    (hB : lpG (e : ℝ) (f : ℝ) ε x ξ' η' ∈ D.target.carrier)
    (hh' : 0 < η ∨ 0 < η')
    (hF : (∃ δ : ℝ, 0 < δ ∧ lpG (e : ℝ) (f : ℝ) ε x (ξ + δ) η ∈ D.target.carrier) ∨
      (∃ δ : ℝ, 0 < δ ∧ lpG (e : ℝ) (f : ℝ) ε x (ξ' + δ) η' ∈ D.target.carrier))
    (hBk : (∃ δ : ℝ, 0 < δ ∧ lpG (e : ℝ) (f : ℝ) ε x (ξ - δ) η ∈ D.target.carrier) ∨
      (∃ δ : ℝ, 0 < δ ∧ lpG (e : ℝ) (f : ℝ) ε x (ξ' - δ) η' ∈ D.target.carrier)) :
    openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x ξ η) (lpG (e : ℝ) (f : ℝ) ε x ξ' η') ⊆
      interior D.target.carrier := by
  have hhp := hhG_pos C.S.e0 C.S.hef'
  have h1 : 0 < (lpG (e : ℝ) (f : ℝ) ε x ξ η) 1 ∨ 0 < (lpG (e : ℝ) (f : ℝ) ε x ξ' η') 1 := by
    rcases hh' with h | h
    · left; rw [lpG_snd]; exact mul_pos h hhp
    · right; rw [lpG_snd]; exact mul_pos h hhp
  have S := C.S
  rcases C.hε with rfl | rfl
  · refine S.interior_seg hA hB h1 ?_ ?_
    · rcases hBk with ⟨δ, hδ, h⟩ | ⟨δ, hδ, h⟩
      · exact Or.inl (S.bwd1G hδ h)
      · exact Or.inr (S.bwd1G hδ h)
    · rcases hF with ⟨δ, hδ, h⟩ | ⟨δ, hδ, h⟩
      · exact Or.inl (S.fwd1G hδ h)
      · exact Or.inr (S.fwd1G hδ h)
  · refine S.interior_seg hA hB h1 ?_ ?_
    · rcases hF with ⟨δ, hδ, h⟩ | ⟨δ, hδ, h⟩
      · exact Or.inl (S.fwdmG hδ h)
      · exact Or.inr (S.fwdmG hδ h)
    · rcases hBk with ⟨δ, hδ, h⟩ | ⟨δ, hδ, h⟩
      · exact Or.inl (S.bwdmG hδ h)
      · exact Or.inr (S.bwdmG hδ h)

end CtxBase

/-! ## 2. Points between lattice points of the line `m_s` -/

/-- the point `p(s − η, η)` is strictly between `p(s − η', η')` and `p(s − η'', η'')` for `η' < η < η''` -/
theorem lpG_between {e f ε x s η' η η'' : ℝ} (h1 : η' < η) (h2 : η < η'') :
    lpG e f ε x (s - η) η ∈
      openSegment ℝ (lpG e f ε x (s - η') η') (lpG e f ε x (s - η'') η'') := by
  have hd : 0 < η'' - η' := by linarith
  have hab : (η'' - η) / (η'' - η') + (η - η') / (η'' - η') = 1 := by
    rw [← add_div, show η'' - η + (η - η') = η'' - η' by ring]
    exact div_self hd.ne'
  have hb : (η - η') / (η'' - η') * (η'' - η') = η - η' := div_mul_cancel₀ _ hd.ne'
  have hη : (η'' - η) / (η'' - η') * η' + (η - η') / (η'' - η') * η'' = η := by
    linear_combination hb + η' * hab
  refine ⟨(η'' - η) / (η'' - η'), (η - η') / (η'' - η'), div_pos (by linarith) hd,
    div_pos (by linarith) hd, hab, ?_⟩
  unfold lpG
  apply plane_ext
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mkPt_zero]
    linear_combination (x + ε * s * f ^ 2) * hab - (ε * uuG e f) * hη
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mkPt_one]
    linear_combination (hhG e f) * hη

/-- the point `p(s − η₂, η₂)`, `η₁ < η₂ ≤ η₃`, lies on the segment `[p(s − η₁, η₁), p(s − η₃, η₃)]` -/
theorem lpG_mem_seg_of_le {e f ε x s η₁ η₂ η₃ : ℝ} (h1 : η₁ < η₂) (h2 : η₂ ≤ η₃) :
    lpG e f ε x (s - η₂) η₂ ∈
      segment ℝ (lpG e f ε x (s - η₁) η₁) (lpG e f ε x (s - η₃) η₃) := by
  have hd : η₃ - η₁ ≠ 0 := by intro h; linarith
  have hd0 : 0 < η₃ - η₁ := by linarith
  have hτ : (η₂ - η₁) / (η₃ - η₁) * (η₃ - η₁) = η₂ - η₁ := div_mul_cancel₀ _ hd
  have hτ1 : (η₂ - η₁) / (η₃ - η₁) ≤ 1 := by rw [div_le_one hd0]; linarith
  have hτ0 : 0 ≤ (η₂ - η₁) / (η₃ - η₁) := div_nonneg (by linarith) hd0.le
  have h := lp_mem_segG (e := e) (f := f) (ε := ε) (x := x) (ξ := s - η₁) (η := η₁)
    (ξ' := s - η₃) (η' := η₃) (τ := (η₂ - η₁) / (η₃ - η₁)) hτ0 hτ1
  rw [show lpG e f ε x (s - η₁ + (η₂ - η₁) / (η₃ - η₁) * (s - η₃ - (s - η₁)))
        (η₁ + (η₂ - η₁) / (η₃ - η₁) * (η₃ - η₁)) = lpG e f ε x (s - η₂) η₂ from
      lpG_congr (by linear_combination (-1 : ℝ) * hτ) (by linear_combination hτ)] at h
  exact h

/-! ## 3. Clamps from below, `RhoEdgeG`, `K3G` -/

/-- **`Z = p(s − η₁, η₁)` is clamped from below on the line `m_s` for the side `ρ_s`** (paper, (K3)(b)): there is a point
`P' = p(s − η', η')` of the line below `Z` such that, for every run `[Z, Q]` of the line above `Z`, no near-side chain edge
straddles `Z` with respect to `P'` and `Q`.  (The paper's two sources: the line just beyond `Z` is outside Δ, or an edge
of a tile on the side `ρ_s` ends at `Z`.) -/
def ClampedBelowG (D : CongruentDissection N) (e f ε x s η₁ : ℝ) : Prop :=
  ∃ η' : ℝ, η' < η₁ ∧ ∀ Q : Plane, GSG e f ε Q = -lvG e f ε x s →
    lpG e f ε x (s - η₁) η₁ ∈ openSegment ℝ (lpG e f ε x (s - η') η') Q →
    ∀ ed ∈ D.lineChain (GSG e f ε) (-lvG e f ε x s),
      ¬ Straddles ((D.tile ed.1).edge ed.2) (lpG e f ε x (s - η') η') (lpG e f ε x (s - η₁) η₁) Q

/-- **source 1: the line just below `Z` is outside Δ** -/
theorem clampedBelowG_of_outside {e f ε x s η₁ η' : ℝ} (hη : η' < η₁)
    (hout : ∀ y ∈ openSegment ℝ (lpG e f ε x (s - η') η') (lpG e f ε x (s - η₁) η₁),
      y ∉ D.target.carrier) : ClampedBelowG D e f ε x s η₁ :=
  ⟨η', hη, fun Q _ _ ed _ => not_straddles_of_outside D.toDissection hout ed.1 ed.2⟩

/-- **source 2: a tile on the side `ρ_s` has an edge `[p(s − η', η'), Z]` ending at `Z`** -/
theorem clampedBelowG_of_edge {e f ε x s η₁ η' : ℝ} (he : 0 < e) (hef : e < f) (hε : ε ^ 2 = 1)
    (hη : η' < η₁) {t : Fin N} {k m : Fin 3} (hkm : k ≠ m)
    (hk : (D.tile t).pts k = lpG e f ε x (s - η') η')
    (hm : (D.tile t).pts m = lpG e f ε x (s - η₁) η₁)
    (hle : ∀ i, GSG e f ε ((D.tile t).pts i) ≤ -lvG e f ε x s) :
    ClampedBelowG D e f ε x s η₁ := by
  refine ⟨η', hη, fun Q hQ hmem ed hed => ?_⟩
  have hfP' : GSG e f ε (lpG e f ε x (s - η') η') = -lvG e f ε x s := by
    rw [GSG_lp hε]; unfold lvG; ring
  have hfP : GSG e f ε (lpG e f ε x (s - η₁) η₁) = -lvG e f ε x s := by
    rw [GSG_lp hε]; unfold lvG; ring
  have hPQ : lpG e f ε x (s - η₁) η₁ ≠ Q := by
    intro h
    rw [← h] at hmem
    exact lpG_ne_eta he hef (by linarith : η' ≠ η₁) (right_mem_openSegment_iff.mp hmem)
  exact clamp_b D.toDissection (GSG e f ε) (GSG_ne he hef hε) _ hPQ hfP hQ hfP' hmem hkm hk hm hle
    ed hed

/-- **A tile on the side `ρ_s` has an edge on `m_s` that starts at `Z = p(s − η₁, η₁)` (`η₁ ∈ ℕ`, `η₁ ≤ j0`), runs upward,
has length `b` or `c`, and `Z` is clamped from below** (paper, (K3)(a) and (b); the length of the edge from the height
`η₁` to the height `η₂` is `(η₂ − η₁) a`). -/
def RhoEdgeG (D : CongruentDissection N) (e f ε x : ℝ) (w : Fin N) (s j0 : ℝ) : Prop :=
  ∃ (k m : Fin 3) (η₁ : ℕ) (η₂ : ℝ), k ≠ m ∧ (η₁ : ℝ) ≤ j0 ∧ (η₁ : ℝ) < η₂ ∧
    (D.tile w).pts k = lpG e f ε x (s - η₁) η₁ ∧ (D.tile w).pts m = lpG e f ε x (s - η₂) η₂ ∧
    ((η₂ - η₁) * (e * f) = f ^ 2 - e ^ 2 ∨ (η₂ - η₁) * (e * f) = f ^ 2) ∧
    (∀ i, GSG e f ε ((D.tile w).pts i) ≤ -lvG e f ε x s) ∧
    ClampedBelowG D e f ε x s η₁

/-- **Hypothesis (K3), general member** (paper, "Statement `K(s', j0)`"): the side `ρ_s` is outside Δ (the first form: the
corner of Δ at `p(s,0)` has the angle `β`), or a tile has a `RhoEdgeG` for `(s, j0)`. -/
def K3G (D : CongruentDissection N) (e f ε x : ℝ) (s j0 : ℝ) : Prop :=
  (∀ q ∈ D.target.carrier, -lvG e f ε x s ≤ GSG e f ε q) ∨ ∃ w, RhoEdgeG D e f ε x w s j0

theorem K3G.mono {e f ε x s j0 j0' : ℝ} (h : K3G D e f ε x s j0) (hj : j0 ≤ j0') :
    K3G D e f ε x s j0' := by
  rcases h with h | ⟨w, k, m, η₁, η₂, hkm, h1, h2, hk, hm, hl, hle, hc⟩
  · exact Or.inl h
  · exact Or.inr ⟨w, k, m, η₁, η₂, hkm, le_trans h1 hj, h2, hk, hm, hl, hle, hc⟩

theorem K3G_of_out {e f ε x s j0 : ℝ}
    (h : ∀ q ∈ D.target.carrier, -lvG e f ε x s ≤ GSG e f ε q) : K3G D e f ε x s j0 := Or.inl h

/-! ## 4. The tile across an `a`-edge -/

/-- every segment between two vertices of a tile has one of the three lengths -/
theorem vertex_dist_casesG {N : ℕ} (D : CongruentDissection N) {e f α β γ : ℝ}
    (hM : ModelDataG D e f α β γ) (i : Fin N) {k m : Fin 3} (hkm : k ≠ m) :
    dist ((D.tile i).pts k) ((D.tile i).pts m) = e * f ∨
    dist ((D.tile i).pts k) ((D.tile i).pts m) = f ^ 2 - e ^ 2 ∨
    dist ((D.tile i).pts k) ((D.tile i).pts m) = f ^ 2 := by
  have hcov : ∀ a b : Fin 3, a ≠ b → b = a + 1 ∨ a = b + 1 := by decide
  rcases hcov k m hkm with h | h
  · rw [h]; exact edge_length_casesG D hM i k
  · rw [h, dist_comm]; exact edge_length_casesG D hM i m

namespace CtxBase

variable {e f : ℕ} {α β γ L ax ay ε x : ℝ}

/-- the clamp of an `a`-edge at a point of the side (`η₁ = 0`, `Z` on the side): the line below the side is outside Δ -/
theorem m_clamp_baseG (C : CtxBase D e f α β γ L ax ay ε x) (ξ : ℝ) :
    ClampedBelowG D (e : ℝ) (f : ℝ) ε x (ξ + 0 + 1) 0 := by
  refine clampedBelowG_of_outside (η' := -1) (by norm_num) (fun y hy hmem => ?_)
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
  have h0 := (C.S.mem hmem).1
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, lpG_snd] at h0
  have hh := hhG_pos C.S.e0 C.S.hef'
  nlinarith [mul_pos ha hh]

/-- the clamp of an `a`-edge at `p(ξ+1,η)` by a tile of the side `ρ` with the edge `[p(ξ+2,η−1), p(ξ+1,η)]` -/
theorem m_clamp_tileG (C : CtxBase D e f α β γ L ax ay ε x) {ξ η : ℝ} {t₁ : Fin N} {k m : Fin 3}
    (hkm : k ≠ m) (hk : (D.tile t₁).pts k = lpG (e : ℝ) (f : ℝ) ε x (ξ + 2) (η - 1))
    (hm : (D.tile t₁).pts m = lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η)
    (hle : ∀ i, GSG (e : ℝ) (f : ℝ) ε ((D.tile t₁).pts i) ≤ -lvG (e : ℝ) (f : ℝ) ε x (ξ + η + 1)) :
    ClampedBelowG D (e : ℝ) (f : ℝ) ε x (ξ + η + 1) η :=
  clampedBelowG_of_edge C.S.e0 C.S.hef' C.e2 (by linarith : η - 1 < η) hkm
    (by rw [hk]; exact lpG_congr (by ring) rfl) (by rw [hm]; exact lpG_congr (by ring) rfl) hle

/-- the tile found across an `a`-edge lays exactly `a`, or it gives (K3) for the run that ends there: its edge from
`p(ξ+1,η)` has length `b` or `c` (step (2a) of the proof) -/
theorem m_next_casesG (C : CtxBase D e f α β γ L ax ay ε x) {i : Fin N} {k m : Fin 3} (hkm : k ≠ m)
    {ξ : ℝ} {η : ℕ} {t : ℝ}
    (hk : (D.tile i).pts k = lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η) (ht : 0 < t)
    (hm : (D.tile i).pts m = AffineMap.lineMap (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η)
      (lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1)) t)
    (hle : ∀ j, GSG (e : ℝ) (f : ℝ) ε ((D.tile i).pts j) ≤ -lvG (e : ℝ) (f : ℝ) ε x (ξ + η + 1))
    (hcl : ClampedBelowG D (e : ℝ) (f : ℝ) ε x (ξ + η + 1) η) :
    (D.tile i).pts m = lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1) ∨
      RhoEdgeG D (e : ℝ) (f : ℝ) ε x i (ξ + η + 1) η := by
  have hε := C.e2
  have he0 := C.S.e0
  have hef := C.S.hef'
  have hf0 := C.S.f0
  rw [lineMap_lpG] at hm
  have hd : dist ((D.tile i).pts k) ((D.tile i).pts m) = t * ((e : ℝ) * f) := by
    rw [hk, hm]
    exact dist_lpG he0 hef hε (by positivity) (by unfold QfG; ring)
  have hk' : (D.tile i).pts k = lpG (e : ℝ) (f : ℝ) ε x (ξ + η + 1 - η) η := by
    rw [hk]; exact lpG_congr (by ring) rfl
  have hm' : (D.tile i).pts m = lpG (e : ℝ) (f : ℝ) ε x (ξ + η + 1 - (η + t)) (η + t) := by
    rw [hm]; exact lpG_congr (by ring) (by ring)
  rcases vertex_dist_casesG D C.S.hM i hkm with h | h | h
  · left
    have h1 : t * ((e : ℝ) * f) = 1 * ((e : ℝ) * f) := by rw [one_mul, ← hd, h]
    have ht1 : t = 1 := mul_right_cancel₀ C.S.a_pos.ne' h1
    rw [hm, ht1]
    exact lpG_congr (by ring) (by ring)
  · right
    refine ⟨k, m, η, η + t, hkm, le_refl _, by linarith, hk', hm', Or.inl ?_, hle, hcl⟩
    rw [show (η : ℝ) + t - η = t by ring, ← hd, h]
  · right
    refine ⟨k, m, η, η + t, hkm, le_refl _, by linarith, hk', hm', Or.inr ?_, hle, hcl⟩
    rw [show (η : ℝ) + t - η = t by ring, ← hd, h]

/-- **The tile across the `a`-edge of `U(ξ,η)` at `p(ξ+1,η)`**: it is `D(ξ,η)`, or `N(ξ,η)`, or it lays `b` or `c` on
the line `m_{ξ+η+1}` from `p(ξ+1,η)` and gives (K3) for the run of length `ξ+η+1` at height `η`.  The clamp of
`p(ξ+1,η)` from below is a hypothesis (sources: `m_clamp_baseG`, `m_clamp_tileG`). -/
theorem m_nextG (C : CtxBase D e f α β γ L ax ay ε x) {ξ : ℝ} {η : ℕ} {t₀ : Fin N}
    (hU : HasV D t₀ (lpG (e : ℝ) (f : ℝ) ε x ξ η) (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η)
      (lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1)))
    (hFw : ∃ δ : ℝ, 0 < δ ∧ lpG (e : ℝ) (f : ℝ) ε x (ξ + 1 + δ) η ∈ D.target.carrier)
    (hcl : ClampedBelowG D (e : ℝ) (f : ℝ) ε x (ξ + η + 1) η) :
    (∃ t, HasV D t (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η) (lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1))
      (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) (η + 1))) ∨
    (∃ t, HasV D t (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η) (lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1))
      (lpG (e : ℝ) (f : ℝ) ε x (ξ - nuG (e : ℝ) (f : ℝ)) (η + 2 + nuG (e : ℝ) (f : ℝ)))) ∨
    (∃ w, RhoEdgeG D (e : ℝ) (f : ℝ) ε x w (ξ + η + 1) η) := by
  have hε := C.e2
  have he0 := C.S.e0
  have hef := C.S.hef'
  have hηpos : (0 : ℝ) ≤ η := Nat.cast_nonneg η
  have hVG : lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η ≠ lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1) :=
    lpG_ne_eta he0 hef (by linarith)
  have hfV : GSG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η)
      = -lvG (e : ℝ) (f : ℝ) ε x (ξ + η + 1) := by
    rw [GSG_lp hε]; unfold lvG; ring
  have hfG : GSG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1))
      = -lvG (e : ℝ) (f : ℝ) ε x (ξ + η + 1) := by
    rw [GSG_lp hε]; unfold lvG; ring
  have hint : openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η) (lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1))
      ⊆ interior D.target.carrier := by
    refine C.seg_intG hU.mem₂ hU.mem₃ (Or.inr (by linarith)) (Or.inl hFw) (Or.inl ⟨1, one_pos, ?_⟩)
    rw [show ξ + 1 - 1 = ξ by ring]; exact hU.mem₁
  have hwall : ∀ y ∈ openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η)
      (lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1)), ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := hU
    refine seg_wall D.toDissection (t := t₀) hmj ?_
    rw [hm, hj]; exact openSegment_subset_segment ℝ _ _ hy
  obtain ⟨η', hη', hprop⟩ := hcl
  have hZ : lpG (e : ℝ) (f : ℝ) ε x (ξ + η + 1 - η) η = lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η :=
    lpG_congr (by ring) rfl
  have hP'mem : lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η ∈
      openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x (ξ + η + 1 - η') η')
        (lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1)) := by
    have h := lpG_between (e := (e : ℝ)) (f := (f : ℝ)) (ε := ε) (x := x) (s := ξ + η + 1)
      (η' := η') (η := η) (η'' := η + 1) hη' (by linarith)
    rw [hZ, show lpG (e : ℝ) (f : ℝ) ε x (ξ + η + 1 - (η + 1)) (η + 1)
        = lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1) from lpG_congr (by ring) rfl] at h
    exact h
  have hfP' : GSG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x (ξ + η + 1 - η') η')
      = -lvG (e : ℝ) (f : ℝ) ε x (ξ + η + 1) := by
    rw [GSG_lp hε]; unfold lvG; ring
  have hP : ∀ ed ∈ D.lineChain (GSG (e : ℝ) (f : ℝ) ε) (-lvG (e : ℝ) (f : ℝ) ε x (ξ + η + 1)),
      ¬ Straddles ((D.tile ed.1).edge ed.2) (lpG (e : ℝ) (f : ℝ) ε x (ξ + η + 1 - η') η')
        (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η) (lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1)) := by
    have h := hprop (lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1)) hfG (by rw [hZ]; exact hP'mem)
    rw [hZ] at h
    exact h
  have hcl' : ClampedBelowG D (e : ℝ) (f : ℝ) ε x (ξ + η + 1) η := ⟨η', hη', hprop⟩
  obtain ⟨ed, hed, k', m', t, hk'm', hk', ht, hm', hle, -, -⟩ :=
    next_tile D.toDissection (GSG (e : ℝ) (f : ℝ) ε) (GSG_ne he0 hef hε)
      (-lvG (e : ℝ) (f : ℝ) ε x (ξ + η + 1)) hVG hfV hfG hfP' hP'mem hint hwall hP
  rcases C.m_next_casesG hk'm' hk' ht hm' hle hcl' with hG | hR
  · rcases m_edge_casesG C.S hε hk'm' hk' hG hle with h | h
    · exact Or.inl ⟨ed.1, h⟩
    · exact Or.inr (Or.inl ⟨ed.1, h⟩)
  · exact Or.inr (Or.inr ⟨ed.1, hR⟩)

end CtxBase

/-! ## 5. The mirror tile `N(ξ,η)` -/

/-- **The points `p(ξ+δ, η+1)`, `0 < δ ≤ 1/3`, are interior to `N(ξ,η)`.**  The constant `1/3` is that of `e = 1`; the proof
uses only `ν = b/c < 1`. -/
theorem N_pushG {e f : ℕ} {α β γ L ax ay ε x : ℝ} (S : SetupG D e f α β γ L ax ay) {t : Fin N}
    {ξ η δ : ℝ}
    (h : HasV D t (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η) (lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1))
      (lpG (e : ℝ) (f : ℝ) ε x (ξ - nuG (e : ℝ) (f : ℝ)) (η + 2 + nuG (e : ℝ) (f : ℝ))))
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 3) :
    lpG (e : ℝ) (f : ℝ) ε x (ξ + δ) (η + 1) ∈ interior (D.tile t).carrier := by
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := h
  have hν0 := nuG_pos S.e0 S.hef'
  have hν1 := nuG_lt_one S.e0 S.hef'
  have e' : lpG (e : ℝ) (f : ℝ) ε x (ξ + δ) (η + 1)
      = (δ * (1 + nuG (e : ℝ) (f : ℝ))) • (D.tile t).pts k
        + (1 - δ * (2 + nuG (e : ℝ) (f : ℝ))) • (D.tile t).pts m + δ • (D.tile t).pts j := by
    rw [hk, hm, hj]
    unfold lpG
    apply plane_ext <;>
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mkPt_zero, mkPt_one] <;> ring
  rw [e']
  exact abc_interior (D.tile t) hkm hkj hmj (mul_pos hδ0 (by linarith))
    (by nlinarith [mul_le_mul_of_nonneg_right hδ1 (show (0 : ℝ) ≤ 2 + nuG (e : ℝ) (f : ℝ) by linarith)])
    hδ0 (by ring)

/-! ## 6. Specialisation to `e = 1` -/

section e_one

variable {n : ℕ} {α β γ L ax ay ε x : ℝ}

/-- **`CtxG` at `e = 1` is `Ctx`** -/
theorem ctxG_one_iff : CtxG D 1 n α β γ L ax ay ε x ↔ Ctx D n α β γ L ax ay ε x := by
  constructor
  · intro C
    refine ⟨setupG_one_iff.mp C.S, C.hε, ?_, ?_⟩
    · intro t' k m hkm hk hm hle
      refine C.hK1 t' k m hkm (by rw [Nat.cast_one, lpG_one]; exact hk)
        (by rw [Nat.cast_one, lpG_one]; exact hm) ?_
      intro i
      have h1 := hle i
      rw [Nat.cast_one, FXG_one, lvG_one]; exact h1
    · intro j hj hmem
      have h := C.hch j hj (by rw [Nat.cast_one, lpG_one]; exact hmem)
      simpa only [Nat.cast_one, lpG_one] using h
  · intro C
    refine ⟨⟨setupG_one_iff.mpr C.S, C.hε⟩, ?_, ?_⟩
    · intro t' k m hkm hk hm hle
      rw [Nat.cast_one, lpG_one] at hk hm
      refine C.hK1 t' k m hkm hk hm ?_
      intro i
      have h1 := hle i
      rw [Nat.cast_one, FXG_one, lvG_one] at h1; exact h1
    · intro j hj hmem
      rw [Nat.cast_one, lpG_one] at hmem
      have h := C.hch j hj hmem
      simpa only [Nat.cast_one, lpG_one] using h

/-- the first alternative of `K3` and of `K3G` coincide at `e = 1` (the second alternatives differ: see the header) -/
theorem K3_of_outG {s j0 : ℝ}
    (h : ∀ q ∈ D.target.carrier, -lvG ((1 : ℕ) : ℝ) (n : ℝ) ε x s ≤ GSG ((1 : ℕ) : ℝ) (n : ℝ) ε q) :
    K3 D n ε x s j0 := by
  refine Or.inl ?_
  intro q hq
  have h1 := h q hq
  rw [Nat.cast_one, lvG_one, GSG_one] at h1; exact h1

theorem K3G_of_out_e1 {s j0 : ℝ} (h : ∀ q ∈ D.target.carrier, -lv n ε x s ≤ GS n ε q) :
    K3G D ((1 : ℕ) : ℝ) (n : ℝ) ε x s j0 := by
  refine Or.inl ?_
  intro q hq
  rw [Nat.cast_one, lvG_one, GSG_one]; exact h q hq

/-- `seg_intG` at `e = 1` is `Ctx.seg_int` -/
theorem seg_int_e1 (C : Ctx D n α β γ L ax ay ε x) {ξ η ξ' η' : ℝ}
    (hA : lp n ε x ξ η ∈ D.target.carrier) (hB : lp n ε x ξ' η' ∈ D.target.carrier)
    (hh' : 0 < η ∨ 0 < η')
    (hF : (∃ δ : ℝ, 0 < δ ∧ lp n ε x (ξ + δ) η ∈ D.target.carrier) ∨
      (∃ δ : ℝ, 0 < δ ∧ lp n ε x (ξ' + δ) η' ∈ D.target.carrier))
    (hBk : (∃ δ : ℝ, 0 < δ ∧ lp n ε x (ξ - δ) η ∈ D.target.carrier) ∨
      (∃ δ : ℝ, 0 < δ ∧ lp n ε x (ξ' - δ) η' ∈ D.target.carrier)) :
    openSegment ℝ (lp n ε x ξ η) (lp n ε x ξ' η') ⊆ interior D.target.carrier := by
  have CG := ctxG_one_iff.mpr C
  have h := CG.seg_intG (ξ := ξ) (η := η) (ξ' := ξ') (η' := η')
    (by rw [Nat.cast_one, lpG_one]; exact hA) (by rw [Nat.cast_one, lpG_one]; exact hB) hh'
    (by simpa only [Nat.cast_one, lpG_one] using hF) (by simpa only [Nat.cast_one, lpG_one] using hBk)
  simpa only [Nat.cast_one, lpG_one] using h

/-- `N_pushG` at `e = 1` is `SideRun.N_push` -/
theorem N_push_e1 (S : Setup D n α β γ L ax ay) {t : Fin N} {ξ η δ : ℝ}
    (h : HasV D t (lp n ε x (ξ + 1) η) (lp n ε x ξ (η + 1)) (lp n ε x (ξ - nu n) (η + 2 + nu n)))
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 3) : lp n ε x (ξ + δ) (η + 1) ∈ interior (D.tile t).carrier := by
  have SG := setupG_one_iff.mpr S
  have h' := N_pushG (ε := ε) (x := x) SG (t := t) (ξ := ξ) (η := η) (δ := δ)
    (by simpa only [Nat.cast_one, lpG_one, nuG_one] using h) hδ0 hδ1
  simpa only [Nat.cast_one, lpG_one] using h'

end e_one

end Erdos634.Draft.SideRunG

#print axioms Erdos634.Draft.SideRunG.CtxBase.seg_intG
#print axioms Erdos634.Draft.SideRunG.lpG_between
#print axioms Erdos634.Draft.SideRunG.clampedBelowG_of_edge
#print axioms Erdos634.Draft.SideRunG.K3G.mono
#print axioms Erdos634.Draft.SideRunG.CtxBase.m_clamp_baseG
#print axioms Erdos634.Draft.SideRunG.CtxBase.m_clamp_tileG
#print axioms Erdos634.Draft.SideRunG.CtxBase.m_next_casesG
#print axioms Erdos634.Draft.SideRunG.CtxBase.m_nextG
#print axioms Erdos634.Draft.SideRunG.N_pushG
#print axioms Erdos634.Draft.SideRunG.ctxG_one_iff
#print axioms Erdos634.Draft.SideRunG.seg_int_e1
#print axioms Erdos634.Draft.SideRunG.N_push_e1
