/-
Draft/SideRunGCornerSide.lean -- written 14 October 2026.  UNAUDITED.  In `AllThreshold`.  Module R1 (geometry, second file) of the plan for
`thm:cornerrun`: **the rules of the side from a corner `A'` of angle `2α` or `3α`, and the side theorem for it** (steps (1) and (2) of the proof of `thm:cornerrun`).
Word part: `Draft/SideRunGCornerWords.lean` (`SideRulesA`, `corner_word`); tools: `Draft/SideRunGCornerRules.lean`.

CONTENTS.
* `kill_C2A_core`, `kill_C2A`, `kill_C2A_end`: **the mirror run lemma `L'_k`** (paper: "Mirror statement `L'_k`, for runs of `C_2` on `[P, R]`: not both (i') the tile beside the last tile across its `b`-edge at `R` shows `β`, and
  (ii') `P` is the left end of `s` and a corner `β`, or the tile beside the first tile across its `a`-edge at `P` shows `α`.  Condition (ii') holds ... if the tile of `s` on the left of `P` shows `γ` or `β` at `P`.  Condition (i') holds if the tile of
  `s` on the right of `R` shows `γ` at `R`, and if `R` is the right end of `s` and a corner `α + β` (the second tile there shows `β`)").  The run follows a tile showing `γ` at its right end (type `R`).
* `side_rulesA`: **the typed word of the side from `A'` satisfies `SideRulesA f m τ`**: `rQ` (`first_tile_alpha`: all tiles at `A'` show `α`), `rB_A` (the last tile does not show `γ`: the right corner is `β` or `α + β`), `rGG_A` (two `γ` never
  meet), `ra_A`, `rb_A`, `rc_A` (the rules (a), (b), (c) for the runs that follow a tile of type `R`; "A maximal run of `C_2` that follows a tile of type `R` is not followed by a tile of type `L`" and, at a right corner `α + β`, does not end the side).
  The geometric proofs are those of `side_rulesG` (`Draft/SideRunGRules.lean`), case "the tile before the run shows `γ`", with `kill_C1A`, `kill_C2A` for `kill_C1G`, `kill_C2G`.
* `corner_side_theorem`: **steps (1) and (2)**: the side carries `f` consecutive tiles `C1` or `f` consecutive tiles `C2`, or it begins at `A'` with a maximal run `C1^k`, `1 ≤ k ≤ f − 1`, followed by `Q'` (the end of the chain) or
  by `A2`, `B2` or `C2`.  `corner_side_theorem_chain`: with the chain of the dissection.

WITNESSES.  As in `Draft/SideRunGRules.lean`: `SetupG`, `CornersA`, `ChainG` are satisfied by the real dissections of `W_M(e,f)` (`Draft/SideRunGMain.lean`, `setupG_witness_member`) -- the side `AB`, corners `2α`, `β`;
`SideRulesA` is satisfiable (`exRulesA`).  The conclusion is a disjunction that real tilings realise on both sides ((private working notes, not included): `C1^7` after `B1^9`; a side that begins `C1^3 A2^4 C1`).

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGCornerRules

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

/-! ## 1. The mirror run lemma `L'_k` for a run of `C2` that follows a tile showing `γ` -/

section runc2

variable {e f : ℕ} {α β γ L ax ay : ℝ} {m : ℕ} {X : ℕ → ℝ} {tile : ℕ → Fin N} {τ : ℕ → Ty}

/-- **`L'_k` for `C_2`, the common part**: a run of `k < f` tiles `C2` ending at `(X (i+k), 0)`, with (K1) and the interior chords there (`C : CtxG` for `ε = -1`), that follows a tile showing `γ` at its right end, does not exist
(condition (ii'): the tile of `s` on the left of `P` shows `γ` at `P`).  (Conclusion `False`.) -/
theorem kill_C2A_core (S : SetupG D e f α β γ L ax ay) (Ch : ChainG D e f L m X tile τ) {i k : ℕ}
    (hk1 : 1 ≤ k) (hkf : k < f) (hik : i + k ≤ m) (hrun : ∀ j, j < k → τ (i + j) = Ty.C2)
    (hi1 : 1 ≤ i) (hg : (τ (i - 1)).gR) (C : CtxG D e f α β γ L ax ay (-1) (X (i + k))) : False := by
  have he0 := S.e0
  have hef := S.hef'
  have hhp := hhG_pos he0 hef
  have hc := S.c_pos
  have hpos := Ch.run_pos (T := Ty.C2) (c := (f : ℝ) ^ 2) rfl hik hrun
  have hx : X (i + k) = X i + (k : ℝ) * (f : ℝ) ^ 2 := hpos k le_rfl
  have hUT : ∀ j : ℕ, j < k → UTG D (e : ℝ) (f : ℝ) (-1) (X (i + k)) j 0 := by
    intro j hj
    have h := Ch.htile (i + (k - 1 - j)) (by omega)
    rw [hrun (k - 1 - j) (by omega)] at h
    have hcj : ((k - 1 - j : ℕ) : ℝ) = (k : ℝ) - 1 - j := by
      rw [Nat.cast_sub (show j ≤ k - 1 by omega), Nat.cast_sub hk1, Nat.cast_one]
    refine ⟨tile (i + (k - 1 - j)), S.c2_lpG h ?_⟩
    rw [hpos (k - 1 - j) (by omega), hcj, hx]; ring
  refine C.run_diesG hk1 hkf hUT ?_
  have hτi : τ i = Ty.C2 := by
    have h := hrun 0 (by omega)
    rwa [Nat.add_zero] at h
  have hC2 := Ch.htile i (by omega)
  rw [hτi] at hC2
  have hU := S.c2_lpG (x := X (i + k)) (ξ := (k : ℝ) - 1) hC2 (by rw [hx]; ring)
  have hG1 : 0 < (lpG (e : ℝ) (f : ℝ) (-1) (X (i + k)) ((k : ℝ) - 1) (0 + 1)) 1 := by
    rw [lpG_snd]; linarith
  have hA1 : (lpG (e : ℝ) (f : ℝ) (-1) (X (i + k)) ((k : ℝ) - 1) 0) 1 = 0 := by rw [lpG_snd]; ring
  have eV : lpG (e : ℝ) (f : ℝ) (-1) (X (i + k)) ((k : ℝ) - 1 + 1) 0 = mkPt (X i) 0 := by
    unfold lpG; exact mkPt_congr (by rw [hx]; ring) (by ring)
  have eA : lpG (e : ℝ) (f : ℝ) (-1) (X (i + k)) ((k : ℝ) - 1) 0 = mkPt (X i + (f : ℝ) ^ 2) 0 := by
    unfold lpG; exact mkPt_congr (by rw [hx]; ring) (by ring)
  have hβ0 : (D.tile (tile i)).localAngle (mkPt (X i) 0) = β := (S.angles hC2).1
  have hU' := hU
  rw [eV] at hU'
  have hxi0 : 0 < X i := Ch.pos S hi1 (by omega)
  have hxiL : X i < L := Ch.lt_L S (by omega)
  have hp := Ch.htile (i - 1) (by omega)
  have e' := Ch.prev hi1 (by omega : i ≤ m)
  have hlenpos := Ty.lenG_pos he0 hef (τ (i - 1))
  have hγj : (D.tile (tile (i - 1))).localAngle (mkPt (X i) 0) = γ := by
    have h := (S.angles hp).2
    rw [e', Ty.aR_of_gR α β γ hg] at h
    exact h
  obtain ⟨kj, mj, jj, -, -, -, hkj, -, -, -⟩ := hp
  have hint : openSegment ℝ (lpG (e : ℝ) (f : ℝ) (-1) (X (i + k)) ((k : ℝ) - 1 + 1) 0)
      (lpG (e : ℝ) (f : ℝ) (-1) (X (i + k)) ((k : ℝ) - 1) (0 + 1)) ⊆ interior D.target.carrier := by
    rw [eV]
    refine S.interior_seg (Ch.mem (by omega)) hU.mem₃ (Or.inr hG1) (Or.inl ?_) (Or.inl ?_)
    · rw [gA_mk]; nlinarith [mul_pos S.hay hxi0]
    · rw [gB_mk]; nlinarith [mul_pos S.hay (sub_pos.mpr hxiL)]
  refine C.K3G_of_next hU hint (fun W Z hW hθ hZ => ?_)
  rw [eV] at hW hθ
  refine S.bad_nb hxi0 hxiL hG1 hU' hA1 hβ0 hkj (mkPt_one _ _)
    (mkPt_ne_of_fst (by linarith)) ?_ (Or.inl hγj) hW hθ hZ
  rw [eA]; exact mkPt_ne_of_fst (by linarith)

/-- **`L'_k` for `C_2`**, the run ends before a tile of the chain (the point `X (i+k)` is an open point of the side) -/
theorem kill_C2A (S : SetupG D e f α β γ L ax ay) (Ch : ChainG D e f L m X tile τ) {i k : ℕ}
    (hk1 : 1 ≤ k) (hkf : k < f) (hik : i + k < m) (hrun : ∀ j, j < k → τ (i + j) = Ty.C2)
    (hi1 : 1 ≤ i) (hg : (τ (i - 1)).gR)
    (hK1 : ∀ (t' : Fin N) (k' m' : Fin 3), k' ≠ m' →
      (D.tile t').pts k' = lpG (e : ℝ) (f : ℝ) (-1) (X (i + k)) 0 0 →
      (D.tile t').pts m' = lpG (e : ℝ) (f : ℝ) (-1) (X (i + k)) 0 1 →
      (∀ i', FXG (e : ℝ) (f : ℝ) (-1) ((D.tile t').pts i') ≤ lvG (e : ℝ) (f : ℝ) (-1) (X (i + k)) 0) →
        False) : False := by
  have hx0 : 0 < X (i + k) := Ch.pos S (by omega) (by omega)
  have hxL : X (i + k) < L := Ch.lt_L S hik
  exact kill_C2A_core S Ch hk1 hkf hik.le hrun hi1 hg
    ⟨⟨S, Or.inr rfl⟩, hK1, S.hch_pos hx0 hxL (Ch.mem hik)⟩

/-- **`L'_k` for `C_2`, the run ends the side** (condition (i') at the right end `Q'`): a run of `k < f` tiles `C2` that follows a tile showing `γ` does not end at the right corner `Q'`, of angle `β` (the last tile shows `α`, a corner `β` is filled
by one tile showing `β`) or `α + β` (the last tile shows `α`; (K1) at `Q'`: `K1_of_cornerR`; the chords: `hch_cornerR`). -/
theorem kill_C2A_end (S : SetupG D e f α β γ L ax ay) (Co : CornersA e f L ax ay)
    (Ch : ChainG D e f L m X tile τ) {i k : ℕ} (hk1 : 1 ≤ k) (hkf : k < f) (hik : i + k = m)
    (hrun : ∀ j, j < k → τ (i + j) = Ty.C2) (hi1 : 1 ≤ i) (hg : (τ (i - 1)).gR) : False := by
  have he0 := S.e0
  have hef := S.hef'
  have hXL : X (i + k) = L := by rw [hik]; exact Ch.hXm
  have hpos := Ch.run_pos (T := Ty.C2) (c := (f : ℝ) ^ 2) rfl (by omega : i + k ≤ m) hrun
  have hxk : X (i + k) = X i + (k : ℝ) * (f : ℝ) ^ 2 := hpos k le_rfl
  have hk0 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk1, Nat.cast_one]
  have hposl := hpos (k - 1) (by omega)
  rw [hk0] at hposl
  have hlast := Ch.htile (i + (k - 1)) (by omega)
  rw [hrun (k - 1) (by omega)] at hlast
  have e' : X (i + (k - 1)) + Ty.lenG (e : ℝ) (f : ℝ) Ty.C2 = L := by
    show X (i + (k - 1)) + (f : ℝ) ^ 2 = _
    rw [← hXL, hxk, hposl]; ring
  have hα0 : (D.tile (tile (i + (k - 1)))).localAngle (mkPt L 0) = α := by
    have h := (S.angles hlast).2
    rw [e'] at h
    exact h
  have hmem : mkPt L 0 ∈ D.target.carrier := by
    obtain ⟨k', m', j', -, -, -, -, hm', -, -⟩ := hlast
    rw [e'] at hm'
    rw [← hm']; exact pts_mem_target D.toDissection (tile (i + (k - 1))) m'
  rcases Co.hQ with ⟨t, ht, hax, hay⟩ | ⟨t, ht, hax, hay⟩
  · -- the right corner is `β`: one tile fills it, and it shows `β`, not `α`
    exfalso
    have hmem' : D.target.pts 1 ∈ (D.tile (tile (i + (k - 1)))).carrier := by
      obtain ⟨k', m', j', -, -, -, -, hm', -, -⟩ := hlast
      rw [e'] at hm'
      rw [S.B_eq, ← hm']; exact subset_convexHull ℝ _ ⟨m', rfl⟩
    have hang := S.corner_tile_beta 1 (S.corner_right_beta ht hax hay) hmem'
    rw [S.B_eq, hα0] at hang
    exact S.hA.hαβ hang
  · -- the right corner is `α + β`
    have hQ := corner_right_ab S ht hax hay
    have hxL' : X (i + (k - 1)) = L - (0 + 1) * (f : ℝ) ^ 2 := by
      rw [← hXL, hxk, hposl]; ring
    have h0 := S.c2_lpG (x := L) (ξ := 0) hlast hxL'
    have hK1 := K1_of_cornerR S hQ h0
    have hch := hch_cornerR S ht hax hay hmem
    rw [← hXL] at hK1 hch
    exact kill_C2A_core S Ch hk1 hkf (by omega) hrun hi1 hg ⟨⟨S, Or.inr rfl⟩, hK1, hch⟩

end runc2

/-! ## 2. The rules of the side from `A'` -/

section rules

variable {e f : ℕ} {α β γ L ax ay : ℝ} {m : ℕ} {X : ℕ → ℝ} {tile : ℕ → Fin N} {τ : ℕ → Ty}

/-- the last tile of the side does not show `γ` at its right end: the right corner is `β` or `α + β`, and `γ > α + β` -/
theorem rB_A (S : SetupG D e f α β γ L ax ay) (Co : CornersA e f L ax ay)
    (Ch : ChainG D e f L m X tile τ) : ¬ (τ (m - 1)).gR := by
  intro hg
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hγdef := S.hA.hγdef
  have hm0 := Ch.hm0
  have h := Ch.htile (m - 1) (by omega)
  have hx := Ch.prev hm0 le_rfl
  rw [Ch.hXm] at hx
  have ha := (S.angles h).2
  rw [hx, Ty.aR_of_gR α β γ hg] at ha
  have hle := one_angle_le D.toDissection (mkPt L 0) (tile (m - 1))
  rw [ha] at hle
  have hcorner : D.target.localAngle (mkPt L 0) ≤ α + β := by
    rcases Co.hQ with ⟨t, ht, hax, hay⟩ | ⟨t, ht, hax, hay⟩
    · have h1 := (D.target).localAngle_vertex 1
      rw [S.corner_right_beta ht hax hay, S.B_eq] at h1
      rw [h1]; linarith
    · exact (corner_right_ab S ht hax hay).le
  linarith

/-- two tiles showing `γ` never meet on the side -/
theorem rGG_A (S : SetupG D e f α β γ L ax ay) (Ch : ChainG D e f L m X tile τ) :
    ∀ k, k + 1 < m → (τ k).gR → ¬ (τ (k + 1)).gL := by
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have he0 := S.e0
  have hef := S.hef'
  intro k hk hg hg'
  have h := Ch.htile k (by omega)
  have h' := Ch.htile (k + 1) hk
  have hs := Ch.hstep k (by omega)
  have hl := Ty.lenG_pos he0 hef (τ k)
  have hij : tile k ≠ tile (k + 1) := S.baseTile_ne h h' (by rw [hs]; linarith)
  have h1 := (S.angles h).2
  have h2 := (S.angles h').1
  rw [← hs, Ty.aR_of_gR α β γ hg] at h1
  rw [Ty.aL_of_gL α β γ hg'] at h2
  have h3 := two_angles_le D.toDissection (mkPt (X (k + 1)) 0) hij
  rw [h1, h2, S.angle_base (Ch.pos S (by omega) (by omega)) (Ch.lt_L S hk)] at h3
  linarith

/-- **rule (a)**: a maximal run of `C1`, shorter than `f`, that follows a tile of type `R` is followed by `B1` (or `C1`) -/
theorem ra_A (S : SetupG D e f α β γ L ax ay) (Co : CornersA e f L ax ay)
    (Ch : ChainG D e f L m X tile τ) :
    ∀ i k, 1 ≤ i → 1 ≤ k → k < f → i + k ≤ m → (∀ j, j < k → τ (i + j) = Ty.C1) → (τ (i - 1)).gR →
      i + k < m ∧ (τ (i + k) = Ty.B1 ∨ τ (i + k) = Ty.C1) := by
  have he0 := S.e0
  have hef := S.hef'
  intro i k hi1 hk1 hkn hik hrun hg
  by_contra hcon
  have hsucc : i + k = m ∨ (i + k < m ∧ τ (i + k) ≠ Ty.B1 ∧ τ (i + k) ≠ Ty.C1) := by
    rcases Nat.lt_or_ge (i + k) m with h | h
    · exact Or.inr ⟨h, fun hB => hcon ⟨h, Or.inl hB⟩, fun hC => hcon ⟨h, Or.inr hC⟩⟩
    · exact Or.inl (by omega)
  have hτi : τ i = Ty.C1 := by
    have h := hrun 0 (by omega)
    rwa [Nat.add_zero] at h
  have h00 := Ch.htile i (by omega)
  rw [hτi] at h00
  have hx0 : 0 < X i := Ch.pos S hi1 (by omega)
  have hxL : X i < L := Ch.lt_L S (by omega)
  have hU0 := S.c1_lpG (x := X i) (ξ := 0) h00 (by ring)
  have hpj := Ch.htile (i - 1) (by omega)
  have e' := Ch.prev hi1 (by omega : i ≤ m)
  have hγj : (D.tile (tile (i - 1))).localAngle (mkPt (X i) 0) = γ := by
    have h := (S.angles hpj).2
    rw [e', Ty.aR_of_gR α β γ hg] at h
    exact h
  have hlam : (τ (i - 1)).lenG (e : ℝ) (f : ℝ) = (e : ℝ) * (f : ℝ) ∨
      (τ (i - 1)).lenG (e : ℝ) (f : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rcases hg with h | h
    · rw [h]; exact Or.inl rfl
    · rw [h]; exact Or.inr rfl
  obtain ⟨kj, mj, jj, hkmj, -, -, hkj, hmj, -, -⟩ := hpj
  rw [e'] at hmj
  have hkj' : (D.tile (tile (i - 1))).pts kj
      = mkPt (X i - 1 * (τ (i - 1)).lenG (e : ℝ) (f : ℝ)) 0 := by
    rw [hkj]; exact mkPt_congr (by rw [← e']; ring) rfl
  exact kill_C1A S Co Ch hk1 hkn hik hrun rfl
    (S.K1_of_gamma (by norm_num) hx0 hxL hU0 (Ne.symm hkmj) hmj hkj' hlam hγj)
    (S.hch_pos hx0 hxL (Ch.mem (by omega))) hsucc

/-- **rule (b)**: a maximal run of `C2`, shorter than `f`, that follows a tile of type `R` is followed by a tile (it does not end the side) that is not of type `L` -/
theorem rb_A (S : SetupG D e f α β γ L ax ay) (Co : CornersA e f L ax ay)
    (Ch : ChainG D e f L m X tile τ) :
    ∀ i k, 1 ≤ i → 1 ≤ k → k < f → i + k ≤ m → (∀ j, j < k → τ (i + j) = Ty.C2) → (τ (i - 1)).gR →
      i + k < m ∧ ¬ (τ (i + k)).gL := by
  have he0 := S.e0
  have hef := S.hef'
  intro i k hi1 hk1 hkn hik hrun hg
  rcases Nat.lt_or_ge (i + k) m with hlt | hge
  · refine ⟨hlt, fun hgL => ?_⟩
    have hx0 : 0 < X (i + k) := Ch.pos S (by omega) (by omega)
    have hxL : X (i + k) < L := Ch.lt_L S hlt
    have hlast := Ch.htile (i + (k - 1)) (by omega)
    rw [hrun (k - 1) (by omega)] at hlast
    have hstep := Ch.hstep (i + (k - 1)) (by omega)
    rw [hrun (k - 1) (by omega), show i + (k - 1) + 1 = i + k by omega] at hstep
    have hU0 := S.c2_lpG (x := X (i + k)) (ξ := 0) hlast (by
      have h' : X (i + k) = X (i + (k - 1)) + (f : ℝ) ^ 2 := hstep
      rw [h']; ring)
    have hj := Ch.htile (i + k) hlt
    have hγj : (D.tile (tile (i + k))).localAngle (mkPt (X (i + k)) 0) = γ := by
      have h := (S.angles hj).1
      rw [Ty.aL_of_gL α β γ hgL] at h
      exact h
    have hlam : (τ (i + k)).lenG (e : ℝ) (f : ℝ) = (e : ℝ) * (f : ℝ) ∨
        (τ (i + k)).lenG (e : ℝ) (f : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
      rcases hgL with h | h
      · rw [h]; exact Or.inl rfl
      · rw [h]; exact Or.inr rfl
    obtain ⟨kj, mj, jj, hkmj, -, -, hkj, hmj, -, -⟩ := hj
    have hmj' : (D.tile (tile (i + k))).pts mj
        = mkPt (X (i + k) - (-1) * (τ (i + k)).lenG (e : ℝ) (f : ℝ)) 0 := by
      rw [hmj]; exact mkPt_congr (by ring) rfl
    exact kill_C2A S Ch hk1 hkn hlt hrun hi1 hg
      (S.K1_of_gamma (by norm_num) hx0 hxL hU0 hkmj hkj hmj' hlam hγj)
  · exact (kill_C2A_end S Co Ch hk1 hkn (by omega) hrun hi1 hg).elim

/-- **rule (c)**: runs `C2^s C1^r`, shorter than `f`, that follow a tile of type `R`, are followed by `B1` (or `C1`) -/
theorem rc_A (S : SetupG D e f α β γ L ax ay) (Co : CornersA e f L ax ay)
    (Ch : ChainG D e f L m X tile τ) :
    ∀ i s r, 1 ≤ i → 1 ≤ s → s < f → 1 ≤ r → r < f → i + s + r ≤ m →
      (∀ j, j < s → τ (i + j) = Ty.C2) → (∀ j, j < r → τ (i + s + j) = Ty.C1) → (τ (i - 1)).gR →
      i + s + r < m ∧ (τ (i + s + r) = Ty.B1 ∨ τ (i + s + r) = Ty.C1) := by
  have he0 := S.e0
  have hef := S.hef'
  intro i s r hi1 hs1 hsn hr1 hrn hisr hrun2 hrun1 hg
  have hJ0 : 0 < X (i + s) := Ch.pos S (by omega) (by omega)
  have hJL : X (i + s) < L := Ch.lt_L S (by omega)
  have hτ1 : τ (i + s) = Ty.C1 := by
    have h := hrun1 0 (by omega)
    rwa [Nat.add_zero] at h
  have h1 := Ch.htile (i + s) (by omega)
  rw [hτ1] at h1
  have hU1 := S.c1_lpG (x := X (i + s)) (ξ := 0) h1 (by ring)
  have hlast := Ch.htile (i + (s - 1)) (by omega)
  rw [hrun2 (s - 1) (by omega)] at hlast
  have hstep := Ch.hstep (i + (s - 1)) (by omega)
  rw [hrun2 (s - 1) (by omega), show i + (s - 1) + 1 = i + s by omega] at hstep
  have hU2 := S.c2_lpG (x := X (i + s)) (ξ := 0) hlast (by
    have h' : X (i + s) = X (i + (s - 1)) + (f : ℝ) ^ 2 := hstep
    rw [h']; ring)
  rcases S.junction hJ0 hJL hU1 hU2 with hK | hK
  · by_contra hcon
    have hsucc : i + s + r = m ∨
        (i + s + r < m ∧ τ (i + s + r) ≠ Ty.B1 ∧ τ (i + s + r) ≠ Ty.C1) := by
      rcases Nat.lt_or_ge (i + s + r) m with h | h
      · exact Or.inr ⟨h, fun hB => hcon ⟨h, Or.inl hB⟩, fun hC => hcon ⟨h, Or.inr hC⟩⟩
      · exact Or.inl (by omega)
    exact kill_C1A S Co Ch hr1 hrn hisr hrun1 rfl hK
      (S.hch_pos hJ0 hJL (Ch.mem (by omega))) hsucc
  · exact (kill_C2A S Ch hs1 hsn (by omega) hrun2 hi1 hg hK).elim

/-- **THE TYPED WORD OF THE SIDE FROM `A'` SATISFIES THE RULES `SideRulesA`** -/
theorem side_rulesA (S : SetupG D e f α β γ L ax ay) (Co : CornersA e f L ax ay)
    (Ch : ChainG D e f L m X tile τ) : SideRulesA f m τ := by
  refine ⟨?_, rB_A S Co Ch, rGG_A S Ch, ra_A S Co Ch, rb_A S Co Ch, rc_A S Co Ch⟩
  obtain ⟨n, -, hn⟩ := corner_A_angle S Co
  exact first_tile_alpha S Ch n hn

/-- **STEPS (1) AND (2) OF THE PROOF OF `thm:cornerrun`**: the side from `A'` carries `f` consecutive tiles `C1` or `f` consecutive tiles `C2` (alternative (i)), or it begins at `A'` with a maximal run `C1^k`, `1 ≤ k ≤ f − 1`, followed by `Q'`
or by `A2`, `B2` or `C2` (alternative (ii), before the run lemma, which gives `k ≥ e + 1`, `corner_run_mirror`). -/
theorem corner_side_theorem (S : SetupG D e f α β γ L ax ay) (Co : CornersA e f L ax ay)
    (Ch : ChainG D e f L m X tile τ) :
    (∃ i, i + f ≤ m ∧ ((∀ j, j < f → τ (i + j) = Ty.C1) ∨ (∀ j, j < f → τ (i + j) = Ty.C2))) ∨
    (∃ k, 1 ≤ k ∧ k < f ∧ k ≤ m ∧ (∀ j, j < k → τ j = Ty.C1) ∧
      (k = m ∨ (k < m ∧ (τ k = Ty.A2 ∨ τ k = Ty.B2 ∨ τ k = Ty.C2)))) :=
  corner_word f m τ Ch.hm0 (side_rulesA S Co Ch)

/-- the same with the chain of the dissection -/
theorem corner_side_theorem_chain (S : SetupG D e f α β γ L ax ay) (Co : CornersA e f L ax ay) :
    ∃ (m : ℕ) (X : ℕ → ℝ) (tile : ℕ → Fin N) (τ : ℕ → Ty), ChainG D e f L m X tile τ ∧
      ((∃ i, i + f ≤ m ∧ ((∀ j, j < f → τ (i + j) = Ty.C1) ∨ (∀ j, j < f → τ (i + j) = Ty.C2))) ∨
      (∃ k, 1 ≤ k ∧ k < f ∧ k ≤ m ∧ (∀ j, j < k → τ j = Ty.C1) ∧
        (k = m ∨ (k < m ∧ (τ k = Ty.A2 ∨ τ k = Ty.B2 ∨ τ k = Ty.C2))))) := by
  obtain ⟨m, X, tile, τ, Ch⟩ := S.exists_chainG
  exact ⟨m, X, tile, τ, Ch, corner_side_theorem S Co Ch⟩

end rules

end Erdos634.Draft.SideRunGA

#print axioms Erdos634.Draft.SideRunGA.kill_C2A_core
#print axioms Erdos634.Draft.SideRunGA.kill_C2A
#print axioms Erdos634.Draft.SideRunGA.kill_C2A_end
#print axioms Erdos634.Draft.SideRunGA.rB_A
#print axioms Erdos634.Draft.SideRunGA.rGG_A
#print axioms Erdos634.Draft.SideRunGA.ra_A
#print axioms Erdos634.Draft.SideRunGA.rb_A
#print axioms Erdos634.Draft.SideRunGA.rc_A
#print axioms Erdos634.Draft.SideRunGA.side_rulesA
#print axioms Erdos634.Draft.SideRunGA.corner_side_theorem
#print axioms Erdos634.Draft.SideRunGA.corner_side_theorem_chain
