/-
Refactored 14 October 2026: `CtxBase` introduced, lemmas that use only the setup moved to it (no statement changed).
Draft/SideRunGRowB.lean -- written 14 October 2026.  UNAUDITED.  In `AllThreshold`.  Module 5 of ten
(part B; part A, `Draft/SideRunGRow.lean`, has `K2G`, `AG`, the vertex figure `fig_bg`, and Lemma Row).

The general-member counterpart of the first half of `Draft/SideRunK.lean`: the tile across an `a`-edge is `D`, the five
tiles at a vertex with `N`, and **Lemma N**: the mirror image `N_i(j)` of `U(i,j)` in its `a`-edge is not a tile.  Paper:
Theorem `thm:siderunall`, "Lemma N" and items (2)-(2d); (private working notes, not included)

CONTENTS.
* `CtxG.m_clamp_natG`: the clamp of `p(i+1, j)` from below (by the side, `j = 0`, or by the `a`-edge of `D(i+1, j−1)`).
* `CtxG.D_ofG`: steps (2a), (2b): the tile across the `a`-edge of `U(i,j)` is `D(i,j)` if no tile gives (K3) for the run
  `(i+j+1, j)` and `N_i(j)` is not a tile.
* `CtxG.N_fiveG`: the five tiles `D(ξ,ζ)`, `U(ξ+1,ζ)`, `N(ξ+1,ζ)`, `U(ξ,ζ+1)`, `D(ξ,ζ+1)` do not meet at `p(ξ+1, ζ+1)`.
* `CtxG.noNG`: **Lemma N**, by induction on `i` for all `j` at once.  Step (a) is `D_ofG`; step (b) is `rowG` with the right
  end of the row clamped by `N` (`N_pushG`); step (c) is `m_nextGr` and `N_fiveG` or (K3G); step (d) is the induction.
* Checks at `e = 1`: `DTG_one_iff`, `K2G_one_iff`, `AG_of_Aprop_e1`, `row_step_e1`, `row_bad0_e1`, `row_e1`, `noN_e1`.

WHAT DIFFERS FROM THE e = 1 TEXT.
(i)   The five-tile contradiction `N_fiveG` is the angle sum `α + β + 3γ > 2π` (from `π < 2γ`, true for every member:
      `cos γ = −e/(2f) < 0`); it does not use `3α < β` (which is false for members such as `(2,3)`).  Likewise the case
      `i = 0` of Lemma N (`π + γ + γ`).
(ii)  The hypothesis `ξ + 2 ≤ n` of `m_next` is gone; `D_ofG` has no hypothesis `i + 2 ≤ n`.  The claim for the smaller
      sizes is `AG` (with `K3G`).
(iii) The paper's step (2d) ("for `1 ≤ i ≤ n − 2`, `S_i` is not `N_i(j_0)`, by Lemma N") is `noNG`; step (2c) is its case
      `i = 0` (the tiles `φ`, `U(0,j)`, `N_0(j)` at `p(0, j+1)`).

CHECKS AT `e = 1` AND WHAT DOES NOT REDUCE.
* `K2G_one_iff`: `K2G` at `e = 1` is `K2`.  `AG_of_Aprop_e1`: `Aprop m → AG m` (not the converse: `AG` is the weaker claim,
  with `K3G` in place of `K3`; `K3_of_K3G_e1`).
* `row_step_e1`, `row_bad0_e1`, `row_e1`, `noN_e1` are the e = 1 statements (`SideRunRow.Ctx.row_step`, `row_bad0`, `row`,
  `SideRunK.Ctx.noN`) derived from the general ones; the e = 1 bound `q + j + 2 ≤ n` of `row` is stronger than the general
  `q + j + 1 ≤ n` (`rowG`), and `noN` has the same bound `i + j + 2 ≤ n` as `noNG`.
* NOT re-derived: `SideRunRow.row_six`/`row_bad` (the e = 1 `row_bad` has `RhoEdge`, not `RhoEdgeG`, and `hb : ξ + 2 ≤ n`; a
  `RhoEdge` hypothesis does not give a `RhoEdgeG` one without the extra bound `ξ + ζ + 3 ≤ n`), `SideRunK.D_of` (same
  reason), `N_five` (it is `N_fiveG`'s e = 1 instance and was not repeated).

WITNESSES.  Everything is stated under `CtxG` (see `Draft/SideRunGChord.lean`: satisfied at `e = 1` by every `Ctx`; NO
`CtxG` for `e ≥ 2` exists yet) and, for `noNG`, with the inductive hypothesis `AG` for the sizes `≤ i`.  `N_fiveG` and the
`False`-conclusions of `noNG` are contradiction engines (the hypotheses of `noNG` are those of a tile `N_i(j)` that the
proof shows does not exist); the non-vacuity of the hypotheses is that of the e = 1 text and of `rowG`.

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGRow
import Erdos634.Draft.SideRunK

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

/-- the clamp of the `a`-edge of `U(i,j)` at `p(i+1,j)` from below: the side of the target (`j = 0`) or `D(i+1,j−1)` -/
theorem m_clamp_natG (C : CtxBase D e f α β γ L ax ay ε x) (i j : ℕ)
    (h : j = 0 ∨ (1 ≤ j ∧ DTG D (e : ℝ) (f : ℝ) ε x ((i + 1 : ℕ) : ℝ) ((j - 1 : ℕ) : ℝ))) :
    ClampedBelowG D (e : ℝ) (f : ℝ) ε x ((i : ℝ) + j + 1) j := by
  have hε := C.e2
  have he0 := C.S.e0
  have hef := C.S.hef'
  rcases h with rfl | ⟨hj1, t, hD⟩
  · simp only [Nat.cast_zero]
    exact C.m_clamp_baseG i
  · have hc1 : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by rw [Nat.cast_sub hj1, Nat.cast_one]
    rw [Nat.cast_add, Nat.cast_one, hc1] at hD
    have hle := hD.all (P := fun p => GSG (e : ℝ) (f : ℝ) ε p ≤ -lvG (e : ℝ) (f : ℝ) ε x ((i : ℝ) + j + 1))
      (GSG_le he0 hef hε (by linarith)) (GSG_le he0 hef hε (by linarith))
      (GSG_le he0 hef hε (by linarith))
    obtain ⟨k, m, j₃, hkm, -, -, hk, hm, -⟩ := hD
    exact C.m_clamp_tileG hkm (by rw [hk]; exact lpG_congr (by ring) rfl)
      (by rw [hm]; exact lpG_congr rfl (by ring)) hle

/-- **Steps (2a), (2b)**: the tile across the `a`-edge of `U(i,j)` at `p(i+1,j)` is `D(i,j)`, if no tile gives (K3) for the
run `(i+j+1, j)` and `N_i(j)` is not a tile. -/
theorem D_ofG (C : CtxBase D e f α β γ L ax ay ε x) {i j : ℕ}
    (hU1 : UTG D (e : ℝ) (f : ℝ) ε x i j) (hU2 : UTG D (e : ℝ) (f : ℝ) ε x ((i : ℝ) + 1) j)
    (hcl : j = 0 ∨ (1 ≤ j ∧ DTG D (e : ℝ) (f : ℝ) ε x ((i + 1 : ℕ) : ℝ) ((j - 1 : ℕ) : ℝ)))
    (hR : ∀ w, RhoEdgeG D (e : ℝ) (f : ℝ) ε x w ((i : ℝ) + j + 1) j → False)
    (hNo : ∀ t, HasV D t (lpG (e : ℝ) (f : ℝ) ε x ((i : ℝ) + 1) j) (lpG (e : ℝ) (f : ℝ) ε x i ((j : ℝ) + 1))
      (lpG (e : ℝ) (f : ℝ) ε x ((i : ℝ) - nuG (e : ℝ) (f : ℝ)) ((j : ℝ) + 2 + nuG (e : ℝ) (f : ℝ))) → False) : DTG D (e : ℝ) (f : ℝ) ε x i j := by
  obtain ⟨t₀, hU⟩ := hU1
  obtain ⟨t₂, hU2'⟩ := hU2
  rcases C.m_nextG hU ⟨1, one_pos, hU2'.mem₂⟩ (C.m_clamp_natG i j hcl) with
    ⟨t, h⟩ | ⟨t, h⟩ | ⟨w, hw⟩
  · exact ⟨t, h⟩
  · exact (hNo t h).elim
  · exact (hR w hw).elim

/-- five tiles at `p(ξ+1, ζ+1)`: `D(ξ,ζ)`, `U(ξ+1,ζ)`, `N(ξ+1,ζ)`, `U(ξ,ζ+1)`, `D(ξ,ζ+1)` cannot meet -/
theorem N_fiveG (C : CtxBase D e f α β γ L ax ay ε x) {ξ ζ : ℝ} {t₁ t₂ tN t₄ t₆ : Fin N}
    (h1 : HasV D t₁ (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) ζ) (lpG (e : ℝ) (f : ℝ) ε x ξ (ζ + 1)) (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) (ζ + 1)))
    (h2 : HasV D t₂ (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) ζ) (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1 + 1) ζ) (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) (ζ + 1)))
    (hN : HasV D tN (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1 + 1) ζ) (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) (ζ + 1))
      (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1 - nuG (e : ℝ) (f : ℝ)) (ζ + 2 + nuG (e : ℝ) (f : ℝ))))
    (h4 : HasV D t₄ (lpG (e : ℝ) (f : ℝ) ε x ξ (ζ + 1)) (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) (ζ + 1)) (lpG (e : ℝ) (f : ℝ) ε x ξ (ζ + 1 + 1)))
    (h6 : HasV D t₆ (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) (ζ + 1)) (lpG (e : ℝ) (f : ℝ) ε x ξ (ζ + 1 + 1)) (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) (ζ + 1 + 1))) : False := by
  have S := C.S
  have hε := C.e2
  have he0 := S.e0
  have hef := S.hef'
  have hν0 := nuG_pos he0 hef
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hγdef := S.hA.hγdef
  have hβγ : β < γ := by linarith
  have hαγ : α < γ := by linarith
  have hαβ : α ≠ β := S.hA.hαβ
  have a1 := (D_anglesG S hε h1).2.2
  have a2 := (U_anglesG S hε h2).2.2
  have aN := (N_anglesG S hε hN).2
  have a4 := (U_anglesG S hε h4).2.1
  have a6 := (D_anglesG S hε h6).1
  have hleN := hN.all (P := fun p => GSG (e : ℝ) (f : ℝ) ε p ≤ -lvG (e : ℝ) (f : ℝ) ε x (ξ + 1 + ζ + 1))
    (GSG_le he0 hef hε (by linarith)) (GSG_le he0 hef hε (by linarith))
    (GSG_le he0 hef hε (by linarith))
  have hle6 := h6.all (P := fun p => GSG (e : ℝ) (f : ℝ) ε p ≤ -lvG (e : ℝ) (f : ℝ) ε x (ξ + 1 + ζ + 1))
    (GSG_le he0 hef hε (by linarith)) (GSG_le he0 hef hε (by linarith))
    (GSG_le he0 hef hε (by linarith))
  have n12 : t₁ ≠ t₂ := ne_of_angle (by rw [a1, a2]; exact hαγ.ne)
  have n1N : t₁ ≠ tN := ne_of_angle (by rw [a1, aN]; exact hαγ.ne)
  have n14 : t₁ ≠ t₄ := ne_of_angle (by rw [a1, a4]; exact hαβ)
  have n16 : t₁ ≠ t₆ := ne_of_angle (by rw [a1, a6]; exact hαγ.ne)
  have n2N : t₂ ≠ tN := by
    obtain ⟨k, hk⟩ := h2.idx₁
    exact (ne_of_F (GSG (e : ℝ) (f : ℝ) ε) hleN (i := k) (by rw [hk]; exact GSG_gt he0 hef hε (by linarith))).symm
  have n24 : t₂ ≠ t₄ := ne_of_angle (by rw [a2, a4]; exact hβγ.ne')
  have n26 : t₂ ≠ t₆ := by
    obtain ⟨k, hk⟩ := h2.idx₁
    exact (ne_of_F (GSG (e : ℝ) (f : ℝ) ε) hle6 (i := k) (by rw [hk]; exact GSG_gt he0 hef hε (by linarith))).symm
  have nN4 : tN ≠ t₄ := ne_of_angle (by rw [aN, a4]; exact hβγ.ne')
  have nN6 : tN ≠ t₆ := by
    obtain ⟨k, hk⟩ := h6.idx₂
    exact (hN.ne_of_vertex hk (lpG_ne_eta he0 hef (by linarith)) (lpG_ne_eta he0 hef (by linarith))
      (lpG_ne_eta he0 hef (by linarith))).symm
  have n46 : t₄ ≠ t₆ := ne_of_angle (by rw [a4, a6]; exact hβγ.ne)
  have h5 := five_angles_le D.toDissection (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) (ζ + 1)) n12 n1N n14 n16 n2N n24 n26
    nN4 nN6 n46
  have h2π := localAngle_le_two_pi D.target (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) (ζ + 1))
  rw [a1, a2, aN, a4, a6] at h5
  linarith

end CtxBase

namespace CtxG

variable {e f : ℕ} {α β γ L ax ay ε x : ℝ}

/-- **LEMMA N.**  If the rows `≤ j` of `Δ_{i+j+1}` are lattice and the claim holds for the sizes `≤ i`, the mirror image
`N_i(j)` of `U(i,j)` in its `a`-edge is not a tile. -/
theorem noNG (C : CtxG D e f α β γ L ax ay ε x) : ∀ i j : ℕ, i + j + 2 ≤ f →
    (∀ i' j' : ℕ, j' ≤ j → i' + j' ≤ i + j → UTG D (e : ℝ) (f : ℝ) ε x i' j') →
    (∀ i' j' : ℕ, j' < j → i' + j' + 1 ≤ i + j → DTG D (e : ℝ) (f : ℝ) ε x i' j') →
    (∀ m' : ℕ, 1 ≤ m' → m' ≤ i → AG D e f ε x m') →
    ∀ t, HasV D t (lpG (e : ℝ) (f : ℝ) ε x ((i : ℝ) + 1) j) (lpG (e : ℝ) (f : ℝ) ε x i ((j : ℝ) + 1))
      (lpG (e : ℝ) (f : ℝ) ε x ((i : ℝ) - nuG (e : ℝ) (f : ℝ)) ((j : ℝ) + 2 + nuG (e : ℝ) (f : ℝ))) → False := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro j hij rowsU rowsD hA tN hN
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
      obtain ⟨φ, hφc, hφπ, hφpush⟩ := C.phiG (j := j + 1) (by omega) (by omega)
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
          refine hA (a + 1) (by omega) (by omega) (a + j + 1) j (by omega) (by omega) (by omega)
            ⟨fun a' b hb hab => rowsU a' b hb (by omega),
              fun a' b hb hab => rowsD a' b hb (by omega)⟩ ?_
          have e1 : (((a + j + 1 : ℕ)) : ℝ) = (a : ℝ) + j + 1 := by push_cast; ring
          rw [e1]
          exact Or.inr ⟨w, hw⟩
        · exact ih a (by omega) j (by omega) (fun a' b hb hab => rowsU a' b hb (by omega))
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
      have hrow := C.rowG (j := j) (q := i' + 1) (by omega) (by omega) rowsU rowsD
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
        refine ih i' (by omega) (j + 1) (by omega) ?_ ?_ (fun m' h1 h2 => hA m' h1 (by omega)) t₆
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
          (by omega) ⟨?_, ?_⟩ ?_
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

end CtxG

/-! ## Checks at `e = 1` -/

section e_one

variable {n : ℕ} {α β γ L ax ay ε x : ℝ}

/-- `D(ξ,η)` is a tile: `DTG` at `e = 1` is `DT` -/
theorem DTG_one_iff {ξ η : ℝ} :
    DTG D ((1 : ℕ) : ℝ) (n : ℝ) ε x ξ η ↔ DT D n ε x ξ η := by
  unfold DTG DT
  constructor <;> intro h <;> simpa only [Nat.cast_one, lpG_one] using h

/-- **`K2G` at `e = 1` is `K2`** -/
theorem K2G_one_iff {s j0 : ℕ} :
    K2G D ((1 : ℕ) : ℝ) (n : ℝ) ε x s j0 ↔ K2 D n ε x s j0 := by
  unfold K2G K2
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j hj hij => UTG_one_iff.mp (h1 i j hj hij),
      fun i j hj hij => DTG_one_iff.mp (h2 i j hj hij)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j hj hij => UTG_one_iff.mpr (h1 i j hj hij),
      fun i j hj hij => DTG_one_iff.mpr (h2 i j hj hij)⟩

/-- **`Aprop` implies `AG` at `e = 1`**: the general claim (with `K3G`) is weaker than the e = 1 one (with `K3`).  The
converse is not claimed. -/
theorem AG_of_Aprop_e1 {m : ℕ} (hA : Aprop D n ε x m) : AG D 1 n ε x m := by
  intro s j0 h1 h2 h3 hK2 hK3
  have hn : 2 ≤ n := by omega
  have hs : (s : ℝ) + 1 ≤ (n : ℝ) := by
    have h' : s + 1 ≤ n := h2
    exact_mod_cast h'
  exact hA s j0 h1 h2 h3 (K2G_one_iff.mp hK2) (K3_of_K3G_e1 hn hs hK3)

/-- **`CtxG.row_stepG` at `e = 1` is `Ctx.row_step`** -/
theorem row_step_e1 (C : Ctx D n α β γ L ax ay ε x) {ρ ζ : ℝ} {tD : Fin N}
    (hDt : HasV D tD (lp n ε x (ρ + 1) ζ) (lp n ε x ρ (ζ + 1)) (lp n ε x (ρ + 1) (ζ + 1)))
    (hζ : 0 ≤ ζ)
    (hcl : ∃ P' : Plane, GH n P' = -((n : ℝ) ^ 2 * hh n * (ζ + 1)) ∧
      lp n ε x ρ (ζ + 1) ∈ openSegment ℝ P' (lp n ε x (ρ + 1) (ζ + 1)) ∧
      ∀ ed ∈ D.lineChain (GH n) (-((n : ℝ) ^ 2 * hh n * (ζ + 1))),
        ¬ Straddles ((D.tile ed.1).edge ed.2) P' (lp n ε x ρ (ζ + 1)) (lp n ε x (ρ + 1) (ζ + 1)))
    (hnob : ∀ ed ∈ D.lineChain (GH n) (-((n : ℝ) ^ 2 * hh n * (ζ + 1))),
      (D.tile ed.1).edge ed.2 ⊆ segment ℝ (lp n ε x ρ (ζ + 1)) (lp n ε x (ρ + 1) (ζ + 1)) →
      dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1)) ≠ (n : ℝ) ^ 2 - 1) :
    UT D n ε x ρ (ζ + 1) ∨
    ∃ (ix : Fin N) (k m j₃ : Fin 3) (t : ℝ), k ≠ m ∧ k ≠ j₃ ∧ m ≠ j₃ ∧
      (D.tile ix).pts k = lp n ε x ρ (ζ + 1) ∧ 0 < t ∧ (D.tile ix).pts m = lp n ε x (ρ + t) (ζ + 1) ∧
      (∀ i, GH n ((D.tile ix).pts i) ≤ -((n : ℝ) ^ 2 * hh n * (ζ + 1))) ∧
      ((D.tile ix).localAngle (lp n ε x ρ (ζ + 1)) = β ∨
        (D.tile ix).localAngle (lp n ε x ρ (ζ + 1)) = γ) ∧
      (∀ i, (D.tile ix).pts i = lp n ε x (ρ - 1) (ζ + 1 + 1) → False) := by
  have CG := ctxG_one_iff.mpr C
  have h := CG.row_stepG (ρ := ρ) (ζ := ζ) (tD := tD)
    (by simpa only [Nat.cast_one, lpG_one] using hDt) hζ
    (by simpa only [Nat.cast_one, lpG_one, hhG_one, GHG_eq] using hcl)
    (by simpa only [Nat.cast_one, lpG_one, hhG_one, GHG_eq, one_pow] using hnob)
  exact h.imp UTG_one_iff.mp (fun h2 => by simpa only [Nat.cast_one, lpG_one, hhG_one, GHG_eq] using h2)

/-- **`CtxG.row_bad0G` at `e = 1` is `Ctx.row_bad0`** (the e = 1 proof uses `α < β`; the general one does not) -/
theorem row_bad0_e1 (C : Ctx D n α β γ L ax ay ε x) {ζ : ℝ} {φ tU tD ix : Fin N}
    (hφπ : (D.tile φ).localAngle (lp n ε x 0 (ζ + 1)) = Real.pi)
    (hU : HasV D tU (lp n ε x 0 ζ) (lp n ε x (0 + 1) ζ) (lp n ε x 0 (ζ + 1)))
    (hDt : HasV D tD (lp n ε x (0 + 1) ζ) (lp n ε x 0 (ζ + 1)) (lp n ε x (0 + 1) (ζ + 1)))
    (hle : ∀ i, GH n ((D.tile ix).pts i) ≤ -((n : ℝ) ^ 2 * hh n * (ζ + 1)))
    (hθ : (D.tile ix).localAngle (lp n ε x 0 (ζ + 1)) = β ∨
      (D.tile ix).localAngle (lp n ε x 0 (ζ + 1)) = γ) : False := by
  have CG := ctxG_one_iff.mpr C
  exact CG.row_bad0G (by simpa only [Nat.cast_one, lpG_one] using hφπ)
    (by simpa only [Nat.cast_one, lpG_one] using hU)
    (by simpa only [Nat.cast_one, lpG_one] using hDt)
    (by simpa only [Nat.cast_one, lpG_one, hhG_one, GHG_eq] using hle)
    (by simpa only [Nat.cast_one, lpG_one] using hθ)

/-- **`CtxG.rowG` at `e = 1` is `Ctx.row`**, with the bound `q + j + 2 ≤ n` and the claim `Aprop` -/
theorem row_e1 (C : Ctx D n α β γ L ax ay ε x) {j q : ℕ} (hq : 1 ≤ q) (hqj : q + j + 2 ≤ n)
    (hUr : ∀ i' j' : ℕ, j' ≤ j → i' + j' ≤ q + j → UT D n ε x i' j')
    (hDr : ∀ i' j' : ℕ, j' < j → i' + j' + 1 ≤ q + j → DT D n ε x i' j')
    (hD : ∀ i' : ℕ, i' < q → DT D n ε x i' j)
    (hcl : ∃ Q' : Plane, GH n Q' = -((n : ℝ) ^ 2 * hh n * ((j : ℝ) + 1)) ∧
      lp n ε x q ((j : ℝ) + 1) ∈ openSegment ℝ (lp n ε x 0 ((j : ℝ) + 1)) Q' ∧
      ∀ ed ∈ D.lineChain (GH n) (-((n : ℝ) ^ 2 * hh n * ((j : ℝ) + 1))),
        ¬ Straddles ((D.tile ed.1).edge ed.2) Q' (lp n ε x q ((j : ℝ) + 1))
          (lp n ε x 0 ((j : ℝ) + 1)))
    (hA : ∀ m' : ℕ, 1 ≤ m' → m' < q → Aprop D n ε x m') :
    ∀ r : ℕ, r < q → UT D n ε x r ((j : ℝ) + 1) := by
  have CG := ctxG_one_iff.mpr C
  intro r hr
  have h := CG.rowG hq (by omega) (fun i' j' hj hij => UTG_one_iff.mpr (hUr i' j' hj hij))
    (fun i' j' hj hij => DTG_one_iff.mpr (hDr i' j' hj hij))
    (fun i' hi => DTG_one_iff.mpr (hD i' hi))
    (by simpa only [Nat.cast_one, lpG_one, hhG_one, GHG_eq] using hcl)
    (fun m' h1 h2 => AG_of_Aprop_e1 (hA m' h1 h2)) r hr
  exact UTG_one_iff.mp h

/-- **`CtxG.noNG` at `e = 1` is `Ctx.noN`** (SideRunK), with the claim `Aprop` -/
theorem noN_e1 (C : Ctx D n α β γ L ax ay ε x) (i j : ℕ) (hij : i + j + 2 ≤ n)
    (rowsU : ∀ i' j' : ℕ, j' ≤ j → i' + j' ≤ i + j → UT D n ε x i' j')
    (rowsD : ∀ i' j' : ℕ, j' < j → i' + j' + 1 ≤ i + j → DT D n ε x i' j')
    (hA : ∀ m' : ℕ, 1 ≤ m' → m' ≤ i → Aprop D n ε x m') (t : Fin N)
    (hN : HasV D t (lp n ε x ((i : ℝ) + 1) j) (lp n ε x i ((j : ℝ) + 1))
      (lp n ε x ((i : ℝ) - nu n) ((j : ℝ) + 2 + nu n))) : False := by
  have CG := ctxG_one_iff.mpr C
  exact CG.noNG i j hij (fun i' j' hj hij' => UTG_one_iff.mpr (rowsU i' j' hj hij'))
    (fun i' j' hj hij' => DTG_one_iff.mpr (rowsD i' j' hj hij'))
    (fun m' h1 h2 => AG_of_Aprop_e1 (hA m' h1 h2)) t
    (by simpa only [Nat.cast_one, lpG_one, nuG_one] using hN)

end e_one

end Erdos634.Draft.SideRunG

#print axioms Erdos634.Draft.SideRunG.CtxBase.m_clamp_natG
#print axioms Erdos634.Draft.SideRunG.CtxBase.D_ofG
#print axioms Erdos634.Draft.SideRunG.CtxBase.N_fiveG
#print axioms Erdos634.Draft.SideRunG.CtxG.noNG
#print axioms Erdos634.Draft.SideRunG.K2G_one_iff
#print axioms Erdos634.Draft.SideRunG.AG_of_Aprop_e1
#print axioms Erdos634.Draft.SideRunG.row_step_e1
#print axioms Erdos634.Draft.SideRunG.row_bad0_e1
#print axioms Erdos634.Draft.SideRunG.row_e1
#print axioms Erdos634.Draft.SideRunG.noN_e1
