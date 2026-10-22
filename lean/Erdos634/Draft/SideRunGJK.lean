/-
Draft/SideRunGJK.lean -- written 14 October 2026.  UNAUDITED.  In `AllThreshold`.  Module J4 of the plan for
`thm:cornerrun` (see the header of `Draft/SideRunGJChord.lean`).

**LEMMA N, THE CLAIM `K(s, j0)` AND THE RUN LEMMA with (K1) at an arbitrary row `js`.**
* `CtxJ.noNJ`: Lemma N over `CtxJ`: `N_i(j)` is not a tile, for `js ≤ j` (the proof of `CtxG.noNG`; changes: context, `js ≤ j`
  threaded through the induction, `phiJ` for `phiG`, `rowJ` for `rowG`, the claim `AGJ`).
* `CtxJ.K_allGJ`: **the claim `K(s, j0)` for all pairs `js ≤ j0 < s < f`**, (K1) at the row `js`, (K2), (K3) contradictory (the proof of
  `CtxG.K_allG`; size 1 uses the field `hchord` of `CtxJ`, i.e. `chordJ`).
* `CtxJ.run_diesJ`: the run lemma `L_k` over `CtxJ` at `js = 0`.
* The CHECK that the general versions are the right ones: `noNG_via_J`, `K_allG_via_J`, `run_diesG_via_J` re-derive the three
  statements of `SideRunGRowB`, `SideRunGK` (`CtxG.noNG`, `CtxG.K_allG`, `CtxG.run_diesG`) from the general ones through `CtxJ.of_ctxG`
  (`js = 0`); with `rowG_via_J` of `SideRunGJRow` the four statements that used (K1) are corollaries.

WITNESSES.  The statements conclude `False` (`K_allGJ`, `run_diesJ`: the contradiction engines of the proof of `thm:siderunall` and of
`thm:cornerrun`; `noNJ`: `N_i(j)` is not a tile).  Their hypotheses are the hypotheses of the paper's `K`/Lemma N; `CtxJ` is satisfied
by every `CtxG` at `js = 0` (at `e = 1`: every `Ctx`) and by the paper's (K1) at `js` (`CtxJ.of_K1J`); `K2G`/`K3G` are properties
of the dissection (see the header of `SideRunGK`).

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGJRow
import Erdos634.Draft.SideRunGRowB
import Erdos634.Draft.SideRunGK

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.SideRunGJ

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG Set

variable {N : ℕ} {D : CongruentDissection N}

namespace CtxJ

variable {e f : ℕ} {α β γ L ax ay ε x : ℝ} {js : ℕ}

/-- **LEMMA N, with (K1) at the row `js ≤ j`.**  If the rows `≤ j` of `Δ_{i+j+1}` are lattice and the claim holds for the sizes `≤ i`, the mirror image
`N_i(j)` of `U(i,j)` in its `a`-edge is not a tile. -/
theorem noNJ (C : CtxJ D e f α β γ L ax ay ε x js) : ∀ i j : ℕ, js ≤ j → i + j + 2 ≤ f →
    (∀ i' j' : ℕ, j' ≤ j → i' + j' ≤ i + j → UTG D (e : ℝ) (f : ℝ) ε x i' j') →
    (∀ i' j' : ℕ, j' < j → i' + j' + 1 ≤ i + j → DTG D (e : ℝ) (f : ℝ) ε x i' j') →
    (∀ m' : ℕ, 1 ≤ m' → m' ≤ i → AGJ D e f ε x js m') →
    ∀ t, HasV D t (lpG (e : ℝ) (f : ℝ) ε x ((i : ℝ) + 1) j) (lpG (e : ℝ) (f : ℝ) ε x i ((j : ℝ) + 1))
      (lpG (e : ℝ) (f : ℝ) ε x ((i : ℝ) - nuG (e : ℝ) (f : ℝ)) ((j : ℝ) + 2 + nuG (e : ℝ) (f : ℝ))) → False := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro j hjs hij rowsU rowsD hA tN hN
    have S := C.S
    have hε := C.e2
    have he0 := S.e0
    have hef := S.hef'
    obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · -- `i = 0`: `U(0,j)`, `N_0(j)` and `φ_j` at `p(0,j+1)`
      subst hi0
      rw [Nat.cast_zero] at hN
      obtain ⟨tU, hUt⟩ := rowsU 0 j le_rfl le_rfl
      rw [Nat.cast_zero] at hUt
      obtain ⟨φ, hφc, hφπ, hφpush⟩ := C.phiJ (j := j + 1) (by omega) (by omega)
        (fun j' hj' => by
          have h := rowsU 0 j' (by omega) (by omega)
          rwa [Nat.cast_zero] at h)
      simp only [Nat.cast_add, Nat.cast_one] at hφπ
      have aU := (U_anglesG S hε hUt).2.2
      have aN := (N_anglesG S hε hN).2
      have hleN := hN.all (P := fun p => GSG (e : ℝ) (f : ℝ) ε p ≤ -lvG (e : ℝ) (f : ℝ) ε x (0 + (j : ℝ) + 1))
        (GSG_le he0 hef hε (by linarith)) (GSG_le he0 hef hε (by linarith))
        (GSG_le he0 hef hε (by linarith))
      have hφU : φ ≠ tU := ne_of_angle (by rw [hφπ, aU]; exact hγπ.ne')
      have hφN : φ ≠ tN := ne_of_angle (by rw [hφπ, aN]; exact hγπ.ne')
      have hUN : tU ≠ tN := by
        obtain ⟨k, hk⟩ := hUt.idx₁
        exact (ne_of_F (GSG (e : ℝ) (f : ℝ) ε) hleN (i := k)
          (by rw [hk]; exact GSG_gt he0 hef hε (by linarith))).symm
      have h3 := three_angles_le D.toDissection (lpG (e : ℝ) (f : ℝ) ε x 0 ((j : ℝ) + 1)) hφU hφN hUN
      have h2π := localAngle_le_two_pi D.target (lpG (e : ℝ) (f : ℝ) ε x 0 ((j : ℝ) + 1))
      rw [hφπ, aU, aN] at h3
      linarith
    · -- `i = i' + 1`
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      have hN0 := hN
      rw [Nat.cast_add, Nat.cast_one] at hN
      -- (a) the tiles `D(a, j)`, `a ≤ i'`
      have hDa : ∀ a : ℕ, a ≤ i' → DTG D (e : ℝ) (f : ℝ) ε x a j := by
        intro a ha
        refine C.D_ofG (i := a) (j := j) (rowsU a j le_rfl (by omega))
          (by
            have h := rowsU (a + 1) j le_rfl (by omega)
            rwa [Nat.cast_add, Nat.cast_one] at h) ?_ ?_ ?_
        · rcases Nat.eq_zero_or_pos j with hj | hj
          · exact Or.inl hj
          · exact Or.inr ⟨hj, rowsD (a + 1) (j - 1) (by omega) (by omega)⟩
        · intro w hw
          refine hA (a + 1) (by omega) (by omega) (a + j + 1) j hjs (by omega) (by omega) (by omega)
            ⟨fun a' b hb hab => rowsU a' b hb (by omega),
              fun a' b hb hab => rowsD a' b hb (by omega)⟩ ?_
          have e1 : (((a + j + 1 : ℕ)) : ℝ) = (a : ℝ) + j + 1 := by push_cast; ring
          rw [e1]
          exact Or.inr ⟨w, hw⟩
        · exact ih a (by omega) j hjs (by omega) (fun a' b hb hab => rowsU a' b hb (by omega))
            (fun a' b hb hab => rowsD a' b hb (by omega)) (fun m' h1 h2 => hA m' h1 (by omega))
      -- (b) the row above
      have hqpos : (0 : ℝ) < ((i' + 1 : ℕ) : ℝ) := by positivity
      have hclR : ∃ Q' : Plane, GHG (f : ℝ) Q' = -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j : ℝ) + 1)) ∧
          lpG (e : ℝ) (f : ℝ) ε x ((i' + 1 : ℕ) : ℝ) ((j : ℝ) + 1) ∈ openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x 0 ((j : ℝ) + 1)) Q' ∧
          ∀ ed ∈ D.lineChain (GHG (f : ℝ)) (-(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j : ℝ) + 1))),
            ¬ Straddles ((D.tile ed.1).edge ed.2) Q' (lpG (e : ℝ) (f : ℝ) ε x ((i' + 1 : ℕ) : ℝ) ((j : ℝ) + 1))
              (lpG (e : ℝ) (f : ℝ) ε x 0 ((j : ℝ) + 1)) := by
        have hQeq : lpG (e : ℝ) (f : ℝ) ε x ((i' + 1 : ℕ) : ℝ) ((j : ℝ) + 1)
            + ((1 / 3 : ℝ) / ((i' + 1 : ℕ) : ℝ))
              • (lpG (e : ℝ) (f : ℝ) ε x ((i' + 1 : ℕ) : ℝ) ((j : ℝ) + 1) - lpG (e : ℝ) (f : ℝ) ε x 0 ((j : ℝ) + 1))
            = lpG (e : ℝ) (f : ℝ) ε x (((i' + 1 : ℕ) : ℝ) + 1 / 3) ((j : ℝ) + 1) := by
          rw [lp_extG]
          exact lpG_congr (by rw [sub_zero, div_mul_cancel₀ _ hqpos.ne']) (by ring)
        have hmemQ := mem_openSegment_ext (lpG (e : ℝ) (f : ℝ) ε x ((i' + 1 : ℕ) : ℝ) ((j : ℝ) + 1))
          (lpG (e : ℝ) (f : ℝ) ε x 0 ((j : ℝ) + 1)) (s := (1 / 3 : ℝ) / ((i' + 1 : ℕ) : ℝ)) (by positivity)
        rw [hQeq] at hmemQ
        refine ⟨lpG (e : ℝ) (f : ℝ) ε x (((i' + 1 : ℕ) : ℝ) + 1 / 3) ((j : ℝ) + 1), GHG_lp _ _ _ _ _ _,
          by rw [openSegment_symm]; exact hmemQ,
          fun ed _ => not_straddles_of_interior D.toDissection (j := tN) ?_ ed.1 ed.2⟩
        intro y hy
        rw [openSegment_eq_image_lineMap] at hy
        obtain ⟨τ, ⟨h0, h1⟩, rfl⟩ := hy
        rw [lineMap_lpG]
        have h := N_pushG S hN0 (δ := (1 - τ) / 3) (by linarith) (by linarith)
        rw [show lpG (e : ℝ) (f : ℝ) ε x (((i' + 1 : ℕ) : ℝ) + 1 / 3
              + τ * (((i' + 1 : ℕ) : ℝ) - (((i' + 1 : ℕ) : ℝ) + 1 / 3)))
              ((j : ℝ) + 1 + τ * ((j : ℝ) + 1 - ((j : ℝ) + 1)))
            = lpG (e : ℝ) (f : ℝ) ε x (((i' + 1 : ℕ) : ℝ) + (1 - τ) / 3) ((j : ℝ) + 1) from
          lpG_congr (by ring) (by ring)]
        exact h
      have hrow := C.rowJ (j := j) (q := i' + 1) hjs (by omega) (by omega) rowsU rowsD
        (fun a ha => hDa a (by omega)) hclR (fun m' h1 h2 => hA m' h1 (by omega))
      -- (c) the tile across the `a`-edge of `U(i', j+1)` at `p(i'+1, j+1)`
      obtain ⟨t₄, h4⟩ := hrow i' (by omega)
      obtain ⟨t₁, h1⟩ := hDa i' le_rfl
      obtain ⟨t₂, h2⟩ := rowsU (i' + 1) j le_rfl le_rfl
      rw [Nat.cast_add, Nat.cast_one] at h2
      have hFw : ∃ δ : ℝ, 0 < δ ∧ lpG (e : ℝ) (f : ℝ) ε x ((i' : ℝ) + 1 + δ) ((j : ℝ) + 1) ∈ D.target.carrier :=
        ⟨1 / 3, by norm_num, Erdos634.BaseSelection.tile_subset_target D.toDissection tN
          (interior_subset (N_pushG S hN (δ := 1 / 3) (by norm_num) le_rfl))⟩
      have hclS : ClampedBelowG D (e : ℝ) (f : ℝ) ε x ((i' : ℝ) + ((j : ℝ) + 1) + 1) ((j : ℝ) + 1) := by
        have hleN := hN.all (P := fun p => GSG (e : ℝ) (f : ℝ) ε p ≤ -lvG (e : ℝ) (f : ℝ) ε x ((i' : ℝ) + ((j : ℝ) + 1) + 1))
          (GSG_le he0 hef hε (by linarith)) (GSG_le he0 hef hε (by linarith))
          (GSG_le he0 hef hε (by linarith))
        obtain ⟨k, m, j₃, hkm, -, -, hk, hm, -⟩ := hN
        exact C.m_clamp_tileG hkm (by rw [hk]; exact lpG_congr (by ring) (by ring)) hm hleN
      have hηn : ∃ n : ℕ, (j : ℝ) + 1 = n := ⟨j + 1, (Nat.cast_succ j).symm⟩
      rcases C.m_nextGr hηn h4 hFw hclS with ⟨t₆, h6⟩ | ⟨t₆, h6⟩ | ⟨w, hw⟩
      · exact C.N_fiveG h1 h2 hN h4 h6
      · -- (d) `N_{i'}(j+1)` is not a tile
        refine ih i' (by omega) (j + 1) (by omega) (by omega) ?_ ?_ (fun m' h1 h2 => hA m' h1 (by omega)) t₆
          (h6.congr (lpG_congr rfl (by rw [Nat.cast_add, Nat.cast_one]))
            (lpG_congr rfl (by rw [Nat.cast_add, Nat.cast_one]))
            (lpG_congr rfl (by rw [Nat.cast_add, Nat.cast_one])))
        · intro a b hb' hab
          rcases Nat.lt_or_ge b (j + 1) with hlt | hge
          · exact rowsU a b (by omega) (by omega)
          · have hbe : b = j + 1 := by omega
            subst hbe
            have h := hrow a (by omega)
            rw [Nat.cast_add, Nat.cast_one]
            exact h
        · intro a b hb' hab
          rcases Nat.lt_or_ge b j with hlt | hge
          · exact rowsD a b hlt (by omega)
          · have hbe : b = j := by omega
            subst hbe
            exact hDa a (by omega)
      · -- the tile lays more than `a`: (K3G) for the run `(i'+j+2, j+1)`, of size `i'+1`
        refine hA (i' + 1) (by omega) le_rfl (i' + 1 + j + 1) (j + 1) (by omega) (by omega)
          (by omega) (by omega) ⟨?_, ?_⟩ ?_
        · intro a b hb' hab
          rcases Nat.lt_or_ge b (j + 1) with hlt | hge
          · exact rowsU a b (by omega) (by omega)
          · have hbe : b = j + 1 := by omega
            subst hbe
            have h := hrow a (by omega)
            rw [Nat.cast_add, Nat.cast_one]
            exact h
        · intro a b hb' hab
          rcases Nat.lt_or_ge b j with hlt | hge
          · exact rowsD a b hlt (by omega)
          · have hbe : b = j := by omega
            subst hbe
            exact hDa a (by omega)
        · have e1 : (((i' + 1 + j + 1 : ℕ)) : ℝ) = (i' : ℝ) + ((j : ℝ) + 1) + 1 := by
            push_cast; ring
          have e2 : (((j + 1 : ℕ)) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
          rw [e1, e2]
          exact Or.inr ⟨w, hw⟩


/-- **THE CLAIM `K(s, j0)`, (K1) at the row `js`**, for all pairs `js ≤ j0 < s < f`: (K1) (in `CtxJ`), (K2) and (K3) are contradictory. -/
theorem K_allGJ (C : CtxJ D e f α β γ L ax ay ε x js) : ∀ m : ℕ, 1 ≤ m → AGJ D e f ε x js m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro hm1 s j0 hjs hj0s hsn hsz hK2 hK3
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
      refine C.hchord s (by omega) hsn (fun j' hj' => ?_) _ hfQ'
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
          refine IH (i + 1) (by omega) (by omega) (i + j0 + 1) j0 hjs (by omega) (by omega) (by omega)
            ⟨fun a b hb hab => hKU a b hb (by omega), fun a b hb hab => hKD a b hb (by omega)⟩ ?_
          have e1 : (((i + j0 + 1 : ℕ)) : ℝ) = (i : ℝ) + j0 + 1 := by push_cast; ring
          rw [e1]
          exact Or.inr ⟨w, hw⟩
        · exact C.noNJ i j0 hjs (by omega) (fun a b hb hab => hKU a b hb (by omega))
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
      have hrow := C.rowJ (j := j0) (q := m - 1) hjs hm1' (by omega)
        (fun a b hb hab => hKU a b hb (by omega)) (fun a b hb hab => hKD a b hb (by omega))
        (fun a ha => hDall a (by omega)) ⟨Q', hfQ', by rw [openSegment_symm]; exact hQ', hQc⟩
        (fun m' h1 h2 => IH m' (by omega) h1)
      -- (4) the pair `(s, j0 + 1)`
      refine IH (m - 1) (by omega) hm1' s (j0 + 1) (by omega) (by omega) hsn (by omega) ⟨?_, ?_⟩ ?_
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


/-- **THE RUN LEMMA `L_k`, over `CtxJ` at `js = 0`**, `1 ≤ k < f`.  A run of `k` tiles `U(0,0), …, U(k−1,0)` on the side, with (K1) at its first end `P`
(in `CtxG`) and `K3G` for `(k, 0)` at its last end, does not exist. -/
theorem run_diesJ (C : CtxJ D e f α β γ L ax ay ε x 0) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k < f)
    (hrun : ∀ i : ℕ, i < k → UTG D (e : ℝ) (f : ℝ) ε x i 0) (hK3 : K3G D (e : ℝ) (f : ℝ) ε x (k : ℝ) 0) : False := by
  refine C.K_allGJ k hk1 k 0 le_rfl (by omega) hkn (by omega) ⟨?_, ?_⟩ (by rw [Nat.cast_zero]; exact hK3)
  · intro i j hj hij
    have hj0 : j = 0 := by omega
    subst hj0
    rw [Nat.cast_zero]
    exact hrun i (by omega)
  · intro i j hj _
    exact absurd hj (Nat.not_lt_zero j)


end CtxJ

section via

variable {e f : ℕ} {α β γ L ax ay ε x : ℝ}

/-- **LEMMA N** (`CtxG.noNG`) as a corollary of `noNJ` at `js = 0`.  If the rows `≤ j` of `Δ_{i+j+1}` are lattice and the claim holds for the sizes `≤ i`, the mirror image
`N_i(j)` of `U(i,j)` in its `a`-edge is not a tile. -/
theorem noNG_via_J (C : CtxG D e f α β γ L ax ay ε x) : ∀ i j : ℕ, i + j + 2 ≤ f →
    (∀ i' j' : ℕ, j' ≤ j → i' + j' ≤ i + j → UTG D (e : ℝ) (f : ℝ) ε x i' j') →
    (∀ i' j' : ℕ, j' < j → i' + j' + 1 ≤ i + j → DTG D (e : ℝ) (f : ℝ) ε x i' j') →
    (∀ m' : ℕ, 1 ≤ m' → m' ≤ i → AG D e f ε x m') →
    ∀ t, HasV D t (lpG (e : ℝ) (f : ℝ) ε x ((i : ℝ) + 1) j) (lpG (e : ℝ) (f : ℝ) ε x i ((j : ℝ) + 1))
      (lpG (e : ℝ) (f : ℝ) ε x ((i : ℝ) - nuG (e : ℝ) (f : ℝ)) ((j : ℝ) + 2 + nuG (e : ℝ) (f : ℝ))) → False :=
  fun i j hij rowsU rowsD hA => (CtxJ.of_ctxG C).noNJ i j (Nat.zero_le j) hij rowsU rowsD
    (fun m' h1 h2 => (AGJ_zero_iff).2 (hA m' h1 h2))

/-- **THE CLAIM `K(s, j0)`** (`CtxG.K_allG`) as a corollary of `K_allGJ` at `js = 0`. -/
theorem K_allG_via_J (C : CtxG D e f α β γ L ax ay ε x) : ∀ m : ℕ, 1 ≤ m → AG D e f ε x m :=
  fun m hm => AGJ_zero_iff.1 ((CtxJ.of_ctxG C).K_allGJ m hm)

/-- **THE RUN LEMMA `L_k`** (`CtxG.run_diesG`) as a corollary of `run_diesJ`, `1 ≤ k < f`.  A run of `k` tiles `U(0,0), …, U(k−1,0)` on the side, with (K1) at its first end `P`
(in `CtxG`) and `K3G` for `(k, 0)` at its last end, does not exist. -/
theorem run_diesG_via_J (C : CtxG D e f α β γ L ax ay ε x) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k < f)
    (hrun : ∀ i : ℕ, i < k → UTG D (e : ℝ) (f : ℝ) ε x i 0) (hK3 : K3G D (e : ℝ) (f : ℝ) ε x (k : ℝ) 0) : False :=
  (CtxJ.of_ctxG C).run_diesJ hk1 hkn hrun hK3

end via

end Erdos634.Draft.SideRunGJ

#print axioms Erdos634.Draft.SideRunGJ.CtxJ.noNJ
#print axioms Erdos634.Draft.SideRunGJ.CtxJ.K_allGJ
#print axioms Erdos634.Draft.SideRunGJ.CtxJ.run_diesJ
#print axioms Erdos634.Draft.SideRunGJ.noNG_via_J
#print axioms Erdos634.Draft.SideRunGJ.K_allG_via_J
#print axioms Erdos634.Draft.SideRunGJ.run_diesG_via_J
