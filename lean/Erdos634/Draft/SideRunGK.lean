/-
Refactored 14 October 2026: `CtxBase` introduced, lemmas that use only the setup moved to it (no statement changed).
Draft/SideRunGK.lean -- written 14 October 2026.  UNAUDITED.  In `AllThreshold`.  Module 6 of ten.

The general-member counterpart of the second half of `Draft/SideRunK.lean`: **the claim `K(s', j0)` for every coprime member
`(e, f)`**, by induction on the size `s' − j0`, and the run lemma `L_k`.  Paper: Theorem `thm:siderunall`, "Statement
`K(s', j0)`", "Proof of `K(s', j0)`" (sizes 1 and `n ≥ 2`, items (1)-(4)) and the "Run lemma `L_k`";
(private working notes, not included)

CONTENTS.
* `CtxG.K3G_clamp_row`: `K3G_clamp` at the height `j0 + 1` written with the real `(j0 : ℝ) + 1`.
* `CtxG.K_allG`: **the claim `K(s, j0)`**, for all pairs `j0 < s < f`: (K1) (in `CtxG`), (K2) (`K2G`) and (K3) (`K3G`) are
  contradictory.  In the form `∀ m ≥ 1, AG D e f ε x m`.
* `CtxG.run_diesG`: **the run lemma `L_k`**, `1 ≤ k < f`: a run of `k` tiles `U(0,0), …, U(k−1,0)` on the side, with (K1) at its
  first end and `K3G` for `(k, 0)`, does not exist.

THE PROOF.  Size 1 (`s = j0 + 1`): `K3G_clamp` at the height `s`, for the chord line `ℓ` (the level `FXG = lvG 0`) and the point
`p(0,s)`, says that `ℓ` just beyond `p(0,s)` is clamped for the tiles of the side `σ` (it lies in the interior of the tile `ψ`
of (K3), or outside Δ); `chordG` (the `ℓ`-chord principle, Lemma A1) says that an edge of a tile of the side `σ` straddles
`p(0,s)`: contradiction.  This is the paper's "`φ` is not `ψ`" in the form used by `SideRunK.K_all`.  Size `n ≥ 2`: (2) the tiles
`D(i, j0)` (`D_ofG`, with the induction for the sizes `i + 1 < n` and Lemma N `noNG`); (3) the row `j0 + 1` (`rowG`, with the
clamp of its right end by `K3G_clamp` at the height `j0 + 1` for the line `GHG`); (4) the pair `(s, j0 + 1)`, of size
`n − 1`, with the same `K3G` (`K3G.mono`).

WHAT DIFFERS FROM THE e = 1 TEXT.
(i)   The hypothesis (K3) is `K3G` (an edge of length `b` or `c` from a lattice point `Z`, clamped from below), and the covering
      by one tile `ψ` is a conclusion (`psiG`, inside `K3G_clamp`); the e = 1 text has the one long edge and `j a < b`.
(ii)  The bounds are the paper's: `s < f`, the multipliers of Lemma A1 at most `s`, of Lemma Aa at most `s`, of Lemma A5 at most
      `s − 1` (the e = 1 text has `3 ≤ n` and `3 α < β` in `row`; neither is used here).
(iii) (K1) is the case `j* = 0` (the field `hK1` of `CtxG`).  The run lemma `L_k` uses (K1) with `j* = 0` (paper: "this is (K1)
      with `j* = 0`"); the general `j*` form is needed only for `thm:cornerrun` ("the general form is needed for Theorem
      `thm:cornerrun`, and the proof is the same") and is not here.
(iv)  The paper proves `K` "for all pairs `(s', j0)` and all origins at once".  Here the origin `x` is a parameter of `CtxG`, and
      every call of the induction hypothesis (`D_ofG`, `rowG`, `noNG`) is at the same origin; `K_allG` holds for every `CtxG`, i.e.
      for every origin.

WHAT DOES NOT REDUCE AT `e = 1`.  `K_allG` at `e = 1` says `AG`: (K2) and `K3G` are contradictory.  The e = 1 theorem
`SideRunK.Ctx.K_all` says `Aprop`: (K2) and `K3` are contradictory, and `K3G` implies `K3` at `e = 1` (`K3_of_K3G_e1`), so
`Aprop → AG` (`AG_of_Aprop_e1`), not the converse.  So `K_allG` at `e = 1` is a consequence of `SideRunK.Ctx.K_all` and does not
re-derive it; `K_all` (e = 1) and `run_dies` (e = 1) are therefore NOT re-derived from the general ones.  (`K_allG_e1` states
the e = 1 instance, and `K_allG_e1_of_K_all` that it follows from the e = 1 theorem.)

WITNESSES.  `K_allG` and `run_diesG` conclude `False` from (K2) and (K3G), i.e. they say that no dissection has a context
`CtxG` together with these data: contradiction engines of the proof of `thm:siderunall` (the statement `K` is the negation of a
configuration).  The hypotheses are satisfiable separately: `CtxG` by every e = 1 `Ctx` (`ctxG_one_iff`); `K2G` is a property of the rows
of the dissection (at `e = 1` it is `K2`, `K2G_one_iff`; at `(s, j0) = (1, 0)` it asks only that `U(0,0)` be a tile); `K3G` by its
first alternative (`ρ_s` outside Δ).  There is no standalone witness theorem.  For `e ≥ 2` NO `CtxG` exists yet (it needs
`setup_of_sides` for general `e` and the sources of (K1) and of the chords).

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGRowB

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

namespace CtxBase

variable {e f : ℕ} {α β γ L ax ay ε x : ℝ}

/-- `K3G_clamp` at the height `j0 + 1`, with the height written `(j0 : ℝ) + 1` -/
theorem K3G_clamp_row (C : CtxBase D e f α β γ L ax ay ε x) {s : ℝ} {j0 : ℕ}
    (hK : K3G D (e : ℝ) (f : ℝ) ε x s (j0 : ℝ)) (hJf : j0 + 1 < f)
    (hU : ∀ j' : ℕ, j' ≤ j0 → UTG D (e : ℝ) (f : ℝ) ε x (s - 1 - j') j')
    (F : Plane →ₗ[ℝ] ℝ) (c : ℝ) {Q : Plane}
    (hFp : F (lpG (e : ℝ) (f : ℝ) ε x (s - ((j0 : ℝ) + 1)) ((j0 : ℝ) + 1)) = c) (hFQ : F Q = c)
    (hdir : GSG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x (s - ((j0 : ℝ) + 1)) ((j0 : ℝ) + 1) - Q) < 0) :
    ∃ Q' : Plane, F Q' = c ∧ lpG (e : ℝ) (f : ℝ) ε x (s - ((j0 : ℝ) + 1)) ((j0 : ℝ) + 1) ∈ openSegment ℝ Q' Q ∧
      ∀ ed ∈ D.lineChain F c, ¬ Straddles ((D.tile ed.1).edge ed.2) Q'
        (lpG (e : ℝ) (f : ℝ) ε x (s - ((j0 : ℝ) + 1)) ((j0 : ℝ) + 1)) Q := by
  have h := C.K3G_clamp (J := j0 + 1) (j0 := j0) rfl hK hJf hU F c (Q := Q)
    (by simpa only [Nat.cast_add, Nat.cast_one] using hFp) hFQ
    (by simpa only [Nat.cast_add, Nat.cast_one] using hdir)
  simpa only [Nat.cast_add, Nat.cast_one] using h

end CtxBase

namespace CtxG

variable {e f : ℕ} {α β γ L ax ay ε x : ℝ}

/-- **THE CLAIM `K(s, j0)`**, for all pairs `j0 < s < f`: (K1) (in `CtxG`), (K2) and (K3) are contradictory. -/
theorem K_allG (C : CtxG D e f α β γ L ax ay ε x) : ∀ m : ℕ, 1 ≤ m → AG D e f ε x m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro hm1 s j0 hj0s hsn hsz hK2 hK3
    obtain ⟨hKU, hKD⟩ := hK2
    have S := C.S
    have hε := C.e2
    have he0 := S.e0
    have hef := S.hef'
    have hsj : (j0 : ℝ) < s := by exact_mod_cast hj0s
    -- the rows `j' ≤ j0` of the line `m_s`, as the tiles `U(s − 1 − j', j')`
    have hUrow : ∀ j' : ℕ, j' ≤ j0 → UTG D (e : ℝ) (f : ℝ) ε x ((s : ℝ) - 1 - j') j' := by
      intro j' hj'
      have h := hKU (s - 1 - j') j' hj' (by omega)
      have hc : ((s - 1 - j' : ℕ) : ℝ) = (s : ℝ) - 1 - j' := by
        rw [Nat.cast_sub (show j' ≤ s - 1 by omega), Nat.cast_sub (show 1 ≤ s by omega),
          Nat.cast_one]
      rwa [hc] at h
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · -- size `1`: the chord `[P, p(0,s)]`
      have hs : s = j0 + 1 := by omega
      have hspos : (0 : ℝ) < s := by linarith [Nat.cast_nonneg (α := ℝ) j0]
      have hFp : FXG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x ((s : ℝ) - s) s) = lvG (e : ℝ) (f : ℝ) ε x 0 := by
        rw [FXG_lp hε]; unfold lvG; ring
      have hdir : GSG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x ((s : ℝ) - s) s - lpG (e : ℝ) (f : ℝ) ε x 0 0) < 0 := by
        rw [map_sub, GSG_lp hε, GSG_lp hε]
        have := lvG_lt (e := (e : ℝ)) (f := (f : ℝ)) (ε := ε) (x := x) he0 hef
          (show (0 : ℝ) + 0 < (s : ℝ) - s + s by linarith)
        linarith
      obtain ⟨Q', hfQ', hQ', hQc⟩ := C.K3G_clamp (J := s) (j0 := j0) hs hK3 hsn hUrow
        (FXG (e : ℝ) (f : ℝ) ε) (lvG (e : ℝ) (f : ℝ) ε x 0) (Q := lpG (e : ℝ) (f : ℝ) ε x 0 0) hFp (FXG_lp hε 0 0) hdir
      rw [show lpG (e : ℝ) (f : ℝ) ε x ((s : ℝ) - s) s = lpG (e : ℝ) (f : ℝ) ε x 0 s from lpG_congr (by ring) rfl] at hQ' hQc
      refine C.chordG (j := s) (by omega) hsn (fun j' hj' => ?_) hfQ'
        (by rw [openSegment_symm]; exact hQ') hQc
      have h := hKU 0 j' (by omega) (by omega)
      rwa [Nat.cast_zero] at h
    · -- size `≥ 2`
      -- (2) the tiles `D(i, j0)`
      have hDall : ∀ i : ℕ, i + j0 + 2 ≤ s → DTG D (e : ℝ) (f : ℝ) ε x i j0 := by
        intro i hi
        refine C.D_ofG (i := i) (j := j0) (hKU i j0 le_rfl (by omega))
          (by
            have h := hKU (i + 1) j0 le_rfl (by omega)
            rwa [Nat.cast_add, Nat.cast_one] at h) ?_ ?_ ?_
        · rcases Nat.eq_zero_or_pos j0 with hj | hj
          · exact Or.inl hj
          · exact Or.inr ⟨hj, hKD (i + 1) (j0 - 1) (by omega) (by omega)⟩
        · intro w hw
          refine IH (i + 1) (by omega) (by omega) (i + j0 + 1) j0 (by omega) (by omega) (by omega)
            ⟨fun a b hb hab => hKU a b hb (by omega), fun a b hb hab => hKD a b hb (by omega)⟩ ?_
          have e1 : (((i + j0 + 1 : ℕ)) : ℝ) = (i : ℝ) + j0 + 1 := by push_cast; ring
          rw [e1]
          exact Or.inr ⟨w, hw⟩
        · exact C.noNG i j0 (by omega) (fun a b hb hab => hKU a b hb (by omega))
            (fun a b hb hab => hKD a b hb (by omega))
            (fun m' h1 h2 => IH m' (by omega) h1)
      -- (3) the row `j0 + 1`
      have hm1' : 1 ≤ m - 1 := by omega
      have hcm : ((m - 1 : ℕ) : ℝ) = (s : ℝ) - ((j0 : ℝ) + 1) := by
        have h1 : m - 1 = s - (j0 + 1) := by omega
        rw [h1, Nat.cast_sub (show j0 + 1 ≤ s by omega), Nat.cast_add, Nat.cast_one]
      have hFp : GHG (f : ℝ) (lpG (e : ℝ) (f : ℝ) ε x ((s : ℝ) - ((j0 : ℝ) + 1)) ((j0 : ℝ) + 1))
          = -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j0 : ℝ) + 1)) := GHG_lp _ _ _ _ _ _
      have hsj1 : (j0 : ℝ) + 1 < s := by
        have h' : j0 + 1 < s := by omega
        exact_mod_cast h'
      have hdir : GSG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x ((s : ℝ) - ((j0 : ℝ) + 1)) ((j0 : ℝ) + 1) - lpG (e : ℝ) (f : ℝ) ε x 0 ((j0 : ℝ) + 1)) < 0 := by
        rw [map_sub, GSG_lp hε, GSG_lp hε]
        have := lvG_lt (e := (e : ℝ)) (f := (f : ℝ)) (ε := ε) (x := x) he0 hef
          (show (0 : ℝ) + ((j0 : ℝ) + 1) < (s : ℝ) - ((j0 : ℝ) + 1) + ((j0 : ℝ) + 1) by linarith)
        linarith
      obtain ⟨Q', hfQ', hQ', hQc⟩ := C.K3G_clamp_row hK3 (by omega) hUrow (GHG (f : ℝ))
        (-(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j0 : ℝ) + 1))) (Q := lpG (e : ℝ) (f : ℝ) ε x 0 ((j0 : ℝ) + 1)) hFp (GHG_lp _ _ _ _ _ _) hdir
      rw [← hcm] at hQ' hQc
      have hrow := C.rowG (j := j0) (q := m - 1) hm1' (by omega)
        (fun a b hb hab => hKU a b hb (by omega)) (fun a b hb hab => hKD a b hb (by omega))
        (fun a ha => hDall a (by omega)) ⟨Q', hfQ', by rw [openSegment_symm]; exact hQ', hQc⟩
        (fun m' h1 h2 => IH m' (by omega) h1)
      -- (4) the pair `(s, j0 + 1)`
      refine IH (m - 1) (by omega) hm1' s (j0 + 1) (by omega) hsn (by omega) ⟨?_, ?_⟩ ?_
      · intro a b hb hab
        rcases Nat.lt_or_ge b (j0 + 1) with hlt | hge
        · exact hKU a b (by omega) hab
        · have hbe : b = j0 + 1 := by omega
          subst hbe
          have h := hrow a (by omega)
          rw [Nat.cast_add, Nat.cast_one]
          exact h
      · intro a b hb hab
        rcases Nat.lt_or_ge b j0 with hlt | hge
        · exact hKD a b hlt hab
        · have hbe : b = j0 := by omega
          subst hbe
          exact hDall a (by omega)
      · exact hK3.mono (by push_cast; linarith)

/-- **THE RUN LEMMA `L_k`**, `1 ≤ k < f`.  A run of `k` tiles `U(0,0), …, U(k−1,0)` on the side, with (K1) at its first end `P`
(in `CtxG`) and `K3G` for `(k, 0)` at its last end, does not exist. -/
theorem run_diesG (C : CtxG D e f α β γ L ax ay ε x) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k < f)
    (hrun : ∀ i : ℕ, i < k → UTG D (e : ℝ) (f : ℝ) ε x i 0) (hK3 : K3G D (e : ℝ) (f : ℝ) ε x (k : ℝ) 0) : False := by
  refine C.K_allG k hk1 k 0 (by omega) hkn (by omega) ⟨?_, ?_⟩ (by rw [Nat.cast_zero]; exact hK3)
  · intro i j hj hij
    have hj0 : j = 0 := by omega
    subst hj0
    rw [Nat.cast_zero]
    exact hrun i (by omega)
  · intro i j hj _
    exact absurd hj (Nat.not_lt_zero j)

end CtxG

/-! ## Checks at `e = 1` -/

section e_one

variable {n : ℕ} {α β γ L ax ay ε x : ℝ}

/-- the claim `K` of the general proof, at `e = 1` -/
theorem K_allG_e1 (C : Ctx D n α β γ L ax ay ε x) (m : ℕ) (hm : 1 ≤ m) : AG D 1 n ε x m :=
  (ctxG_one_iff.mpr C).K_allG m hm

/-- the e = 1 theorem `SideRunK.Ctx.K_all` implies the e = 1 instance of the general claim (not conversely) -/
theorem K_allG_e1_of_K_all (C : Ctx D n α β γ L ax ay ε x) (m : ℕ) (hm : 1 ≤ m) : AG D 1 n ε x m :=
  AG_of_Aprop_e1 (C.K_all m hm)

/-- the run lemma of the general proof at `e = 1` -/
theorem run_diesG_e1 (C : Ctx D n α β γ L ax ay ε x) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k < n)
    (hrun : ∀ i : ℕ, i < k → UT D n ε x i 0) (hK3 : K3G D ((1 : ℕ) : ℝ) (n : ℝ) ε x (k : ℝ) 0) :
    False :=
  (ctxG_one_iff.mpr C).run_diesG hk1 hkn (fun i hi => UTG_one_iff.mpr (hrun i hi)) hK3

/-- the e = 1 run lemma `SideRunK.Ctx.run_dies` gives the general one at `e = 1` (when `K3G` implies `K3`) -/
theorem run_diesG_e1_of_run_dies (C : Ctx D n α β γ L ax ay ε x) {k : ℕ} (hk1 : 1 ≤ k)
    (hkn : k < n) (hrun : ∀ i : ℕ, i < k → UT D n ε x i 0)
    (hK3 : K3G D ((1 : ℕ) : ℝ) (n : ℝ) ε x (k : ℝ) 0) : False :=
  C.run_dies hk1 hkn hrun
    (K3_of_K3G_e1 (by omega) (by have h : k + 1 ≤ n := hkn; exact_mod_cast h) hK3)

end e_one

end Erdos634.Draft.SideRunG

#print axioms Erdos634.Draft.SideRunG.CtxBase.K3G_clamp_row
#print axioms Erdos634.Draft.SideRunG.CtxG.K_allG
#print axioms Erdos634.Draft.SideRunG.CtxG.run_diesG
#print axioms Erdos634.Draft.SideRunG.K_allG_e1
#print axioms Erdos634.Draft.SideRunG.K_allG_e1_of_K_all
#print axioms Erdos634.Draft.SideRunG.run_diesG_e1
#print axioms Erdos634.Draft.SideRunG.run_diesG_e1_of_run_dies
