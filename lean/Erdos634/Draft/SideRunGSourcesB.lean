/-
Refactored 14 October 2026: `CtxBase` introduced, lemmas that use only the setup moved to it (no statement changed).
Draft/SideRunGSourcesB.lean -- written 14 October 2026.  UNAUDITED.  In `AllThreshold`.  Module 8 of ten
(part B; part A, `Draft/SideRunGSources.lean`, has the figures, (K1), the chords, (K3G); the checks at `e = 1` are in
`Draft/SideRunGSourcesC.lean`).

**The run lemma `L_k` in the paper's form, for every member**, and the structures it is stated over.  Paper: Theorem
`thm:siderunall`, "Run lemma `L_k`" (`1 ≤ k ≤ f − 1`: the side cannot carry consecutive tiles `X_0, …, X_{k−1}` of type `C_1` on
`[P, R]` such that (i) the tile beside `X_0` across its `b`-edge at `P` shows `β` at `P`, and (ii) `R` is the right end of `s` and a
corner of angle `β`, or the tile beside `X_{k−1}` across its `a`-edge at `R` shows `α` at `R`) and its mirror `L'_k` for `C_2`.

CONTENTS.
* `CornersG L ax ay` (the corners of the side `QB` of the target: `β` at `B`; `β` or `α + β` at `Q`) and `ChainG` (a typed chain of
  base tiles on `QB`; `SetupG.typed_chain` gives one): the general-member counterparts of `SideRun.Corners` and `SideRun.Chain`
  (`SideRunRules.lean`), with the constants `uuG`, `hhG`, `rtG`, `(τ k).lenG`.  `ChainG.nonneg`, `lt_L`, `prev`, `pos`, `mem`, `run_pos`.
* `SetupG.exists_chainG` (a typed chain exists for every `SetupG`); `SetupG.c1_lpG`, `c2_lpG`: a `C1` (`C2`) base tile is the lattice triangle `U(ξ, 0)` of the run to the right (left) from `(x, 0)`
  — **the run hypothesis `∀ i < k, UTG … i 0`** of `run_diesG` from typed tiles.
* `SetupG.kill_C1G`: **`L_k` for `C_1`.**  A run of `k` tiles `C_1`, `1 ≤ k ≤ f − 1`, with (K1) at its first end (the field `hK1`) and
  the chord hypothesis `hch`, does not end at `B`, nor before a tile other than `B_1` and `C_1`.
* `SetupG.kill_C2G`: **`L'_k` for `C_2`** (the mirror): a run of `k` tiles `C_2` ending at `(X (i + k), 0)`, with (K1) there, does not
  start at `Q`, nor after a tile showing `γ`.

The proofs: the run hypothesis (`c1_lpG`), `run_diesG` (module 6) reduces the claim to `K3G` for `(k, 0)`, which is `K3G_out_right` at
`B`, and otherwise `K3G_of_next`, whose hypothesis `hbad` is `bad_nb` (a side tile beyond the end shows `γ` or `β`) or `bad_corner`
(the end is a corner `α + β`); for `L'_k`, the chord hypothesis is `hch_pos`, and the start at `Q` is `K3G_out_left` (corner `β`) or
`bad_corner` (corner `α + β`; the interior of the `a`-edge from the corner uses `rtG · uuG − e · hhG = rtG · e²`, and the angle of the
corner is `corner_left_ab`, for the direction `(e, √(4f² − e²))`).

WHAT DIFFERS FROM THE e = 1 TEXT.  `Corners` has the second form `ax = t e`, `ay = t rtG e f` (e = 1: `ax = t`, `ay = t rt`).  The
bound is `k < f` (paper: `k ≤ f − 1`).  Nothing else changes in the statements of `kill_C1`/`kill_C2`; the proofs use `bad_nb` and
`bad_corner` of part A, which do not use `α < β`.

WITNESSES.  `CornersG`, `ChainG`: structures about the target and the dissection; `SetupG.exists_chainG` gives a `ChainG` for every
`SetupG` (from `SetupG.typed_chain`); at `e = 1` `CornersG` is `SideRun.Corners` up to the cast (see part C).  NO `SetupG` for `e ≥ 2` is exhibited yet, so no
`ChainG` for `e ≥ 2` either.  `kill_C1G`, `kill_C2G` conclude `False`: they are contradiction engines of the proof of the side theorem
(the run lemma says the configuration does not exist).

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGSources

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

/-- **The corners of the side `QB`**: angle `β` at `B`; angle `β` or `α + β` at `Q`. -/
structure CornersG (e f : ℕ) (L ax ay : ℝ) : Prop where
  hB : ∃ t : ℝ, 0 < t ∧ ax = L - t * uuG (e : ℝ) (f : ℝ) ∧ ay = t * hhG (e : ℝ) (f : ℝ)
  hQ : (∃ t : ℝ, 0 < t ∧ ax = t * uuG (e : ℝ) (f : ℝ) ∧ ay = t * hhG (e : ℝ) (f : ℝ)) ∨
    (∃ t : ℝ, 0 < t ∧ ax = t * (e : ℝ) ∧ ay = t * rtG (e : ℝ) (f : ℝ))

/-- **A typed chain of base tiles on the side `QB`.** -/
structure ChainG (D : CongruentDissection N) (e f : ℕ) (L : ℝ) (m : ℕ) (X : ℕ → ℝ)
    (tile : ℕ → Fin N) (τ : ℕ → Ty) : Prop where
  hm0 : 0 < m
  hX0 : X 0 = 0
  hXm : X m = L
  hstep : ∀ k, k < m → X (k + 1) = X k + (τ k).lenG (e : ℝ) (f : ℝ)
  htile : ∀ k, k < m → BaseTileG D (e : ℝ) (f : ℝ) (tile k) (τ k) (X k)

namespace ChainG

variable {e f : ℕ} {α β γ L ax ay : ℝ} {m : ℕ} {X : ℕ → ℝ} {tile : ℕ → Fin N} {τ : ℕ → Ty}

theorem nonneg (Ch : ChainG D e f L m X tile τ) (S : SetupG D e f α β γ L ax ay) {k : ℕ} (hk : k < m) :
    0 ≤ X k := (S.baseTile_range (Ch.htile k hk)).1

theorem lt_L (Ch : ChainG D e f L m X tile τ) (S : SetupG D e f α β γ L ax ay) {k : ℕ} (hk : k < m) :
    X k < L := by
  have h1 := (S.baseTile_range (Ch.htile k hk)).2
  have h2 := Ty.lenG_pos S.e0 S.hef' (τ k)
  linarith

theorem prev (Ch : ChainG D e f L m X tile τ) {k : ℕ} (hk0 : 0 < k) (hk : k ≤ m) :
    X (k - 1) + (τ (k - 1)).lenG (e : ℝ) (f : ℝ) = X k := by
  have h1 := Ch.hstep (k - 1) (by omega)
  rw [Nat.sub_add_cancel hk0] at h1
  exact h1.symm

theorem pos (Ch : ChainG D e f L m X tile τ) (S : SetupG D e f α β γ L ax ay) {k : ℕ} (hk0 : 0 < k)
    (hk : k ≤ m) : 0 < X k := by
  have h1 := Ch.prev hk0 hk
  have h2 := Ch.nonneg S (k := k - 1) (by omega)
  have h3 := Ty.lenG_pos S.e0 S.hef' (τ (k - 1))
  linarith

theorem mem (Ch : ChainG D e f L m X tile τ) {k : ℕ} (hk : k < m) :
    mkPt (X k) 0 ∈ D.target.carrier := by
  obtain ⟨k', m', j', -, -, -, hk', -, -, -⟩ := Ch.htile k hk
  rw [← hk']; exact pts_mem_target D.toDissection (tile k) k'

/-- the positions along a run of tiles of one type -/
theorem run_pos (Ch : ChainG D e f L m X tile τ) {T : Ty} {c : ℝ}
    (hc : T.lenG (e : ℝ) (f : ℝ) = c) {i k : ℕ}
    (hik : i + k ≤ m) (hrun : ∀ j, j < k → τ (i + j) = T) :
    ∀ j, j ≤ k → X (i + j) = X i + j * c := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have h := Ch.hstep (i + j) (by omega)
    rw [hrun j (by omega), hc] at h
    rw [← Nat.add_assoc, h, ih (by omega)]
    push_cast
    ring

end ChainG

namespace SetupG

variable {e f : ℕ} {α β γ L ax ay : ℝ} {m : ℕ} {X : ℕ → ℝ} {tile : ℕ → Fin N} {τ : ℕ → Ty}

/-- **A typed chain exists** for every `SetupG`: `typed_chain` as a `ChainG` -/
theorem exists_chainG (S : SetupG D e f α β γ L ax ay) :
    ∃ (m : ℕ) (X : ℕ → ℝ) (tile : ℕ → Fin N) (τ : ℕ → Ty), ChainG D e f L m X tile τ := by
  obtain ⟨m, X, tile, τ, hm, h0, hmL, hstep, hbt⟩ := S.typed_chain
  exact ⟨m, X, tile, τ, ⟨hm, h0, hmL, hstep, hbt⟩⟩

/-- a `C1` tile as the lattice triangle `U(ξ, 0)` of the run to the right from `(x, 0)` -/
theorem c1_lpG (S : SetupG D e f α β γ L ax ay) {t : Fin N} {x' x ξ : ℝ}
    (h : BaseTileG D (e : ℝ) (f : ℝ) t Ty.C1 x') (hx : x' = x + ξ * (f : ℝ) ^ 2) :
    HasV D t (lpG (e : ℝ) (f : ℝ) 1 x ξ 0) (lpG (e : ℝ) (f : ℝ) 1 x (ξ + 1) 0)
      (lpG (e : ℝ) (f : ℝ) 1 x ξ (0 + 1)) := by
  refine (S.c1_data h).congr ?_ ?_ ?_
  · unfold lpG; exact mkPt_congr (by rw [hx]; ring) (by ring)
  · unfold lpG; exact mkPt_congr (by rw [hx]; ring) (by ring)
  · unfold lpG; exact mkPt_congr (by rw [hx]; ring) (by ring)

/-- a `C2` tile as the lattice triangle `U(ξ, 0)` of the run to the left from `(x, 0)` -/
theorem c2_lpG (S : SetupG D e f α β γ L ax ay) {t : Fin N} {x' x ξ : ℝ}
    (h : BaseTileG D (e : ℝ) (f : ℝ) t Ty.C2 x') (hx : x' = x - (ξ + 1) * (f : ℝ) ^ 2) :
    HasV D t (lpG (e : ℝ) (f : ℝ) (-1) x ξ 0) (lpG (e : ℝ) (f : ℝ) (-1) x (ξ + 1) 0)
      (lpG (e : ℝ) (f : ℝ) (-1) x ξ (0 + 1)) := by
  refine (S.c2_data h).congr ?_ ?_ ?_
  · unfold lpG; exact mkPt_congr (by rw [hx]; ring) (by ring)
  · unfold lpG; exact mkPt_congr (by rw [hx]; ring) (by ring)
  · unfold lpG; exact mkPt_congr (by rw [hx]; ring) (by ring)

/-- **`L_k` for `C_1`: a run of `k < f` tiles `C1`** from `(x, 0)`, with (K1) there, does not end at `B` nor before a tile other
than `B1` and `C1`. -/
theorem kill_C1G (S : SetupG D e f α β γ L ax ay) (Co : CornersG e f L ax ay)
    (Ch : ChainG D e f L m X tile τ) {i k : ℕ} (hk1 : 1 ≤ k) (hkf : k < f) (hik : i + k ≤ m)
    (hrun : ∀ j, j < k → τ (i + j) = Ty.C1) {x : ℝ} (hxi : X i = x)
    (hK1 : ∀ (t' : Fin N) (k' m' : Fin 3), k' ≠ m' → (D.tile t').pts k' = lpG (e : ℝ) (f : ℝ) 1 x 0 0 →
      (D.tile t').pts m' = lpG (e : ℝ) (f : ℝ) 1 x 0 1 →
      (∀ i', FXG (e : ℝ) (f : ℝ) 1 ((D.tile t').pts i') ≤ lvG (e : ℝ) (f : ℝ) 1 x 0) → False)
    (hch : ∀ j : ℕ, 1 ≤ j → lpG (e : ℝ) (f : ℝ) 1 x 0 j ∈ D.target.carrier →
      openSegment ℝ (lpG (e : ℝ) (f : ℝ) 1 x 0 0) (lpG (e : ℝ) (f : ℝ) 1 x 0 j) ⊆ interior D.target.carrier)
    (hsucc : i + k = m ∨ (i + k < m ∧ τ (i + k) ≠ Ty.B1 ∧ τ (i + k) ≠ Ty.C1)) : False := by
  subst hxi
  have he0 := S.e0
  have hef := S.hef'
  have hhp := hhG_pos he0 hef
  have hc := S.c_pos
  have C : CtxG D e f α β γ L ax ay 1 (X i) := ⟨⟨S, Or.inl rfl⟩, hK1, hch⟩
  have hpos := Ch.run_pos (T := Ty.C1) (c := (f : ℝ) ^ 2) rfl hik hrun
  have hUT : ∀ j : ℕ, j < k → UTG D (e : ℝ) (f : ℝ) 1 (X i) j 0 := by
    intro j hj
    have h := Ch.htile (i + j) (by omega)
    rw [hrun j hj] at h
    exact ⟨tile (i + j), S.c1_lpG h (hpos j hj.le)⟩
  refine C.run_diesG hk1 hkf hUT ?_
  have hxR : X (i + k) = X i + k * (f : ℝ) ^ 2 := hpos k le_rfl
  rcases hsucc with hend | ⟨hlt, hZ1, hZ2⟩
  · obtain ⟨t, ht, hax, hay⟩ := Co.hB
    refine S.K3G_out_right ht hax hay ?_
    rw [← hxR, hend, Ch.hXm]
  · have hk0 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk1, Nat.cast_one]
    have hlast := Ch.htile (i + (k - 1)) (by omega)
    rw [hrun (k - 1) (by omega)] at hlast
    have hposl := hpos (k - 1) (by omega)
    rw [hk0] at hposl
    have hU := S.c1_lpG hlast hposl
    have hx0 : 0 < X (i + k) := Ch.pos S (by omega) (by omega)
    have hxL : X (i + k) < L := Ch.lt_L S hlt
    have eV : lpG (e : ℝ) (f : ℝ) 1 (X i) ((k : ℝ) - 1 + 1) 0 = mkPt (X (i + k)) 0 := by
      unfold lpG; exact mkPt_congr (by rw [hxR]; ring) (by ring)
    have eA : lpG (e : ℝ) (f : ℝ) 1 (X i) ((k : ℝ) - 1) 0 = mkPt (X (i + k) - (f : ℝ) ^ 2) 0 := by
      unfold lpG; exact mkPt_congr (by rw [hxR]; ring) (by ring)
    have hG1 : 0 < (lpG (e : ℝ) (f : ℝ) 1 (X i) ((k : ℝ) - 1) (0 + 1)) 1 := by rw [lpG_snd]; linarith
    have hint : openSegment ℝ (lpG (e : ℝ) (f : ℝ) 1 (X i) ((k : ℝ) - 1 + 1) 0)
        (lpG (e : ℝ) (f : ℝ) 1 (X i) ((k : ℝ) - 1) (0 + 1)) ⊆ interior D.target.carrier := by
      rw [eV]
      refine S.interior_seg (Ch.mem hlt) hU.mem₃ (Or.inr hG1) (Or.inl ?_) (Or.inl ?_)
      · rw [gA_mk]; nlinarith [mul_pos S.hay hx0]
      · rw [gB_mk]; nlinarith [mul_pos S.hay (sub_pos.mpr hxL)]
    have hβ0 : (D.tile (tile (i + (k - 1)))).localAngle (mkPt (X (i + k)) 0) = β := by
      have e' : X (i + (k - 1)) + Ty.lenG (e : ℝ) (f : ℝ) Ty.C1 = X (i + k) := by
        show X (i + (k - 1)) + (f : ℝ) ^ 2 = _
        rw [hposl, hxR]; ring
      have h := (S.angles hlast).2
      rw [e'] at h
      exact h
    have hj := Ch.htile (i + k) hlt
    have hjang := (S.angles hj).1
    have hlenpos := Ty.lenG_pos he0 hef (τ (i + k))
    obtain ⟨T, hT⟩ : ∃ T, τ (i + k) = T := ⟨_, rfl⟩
    rw [hT] at hZ1 hZ2 hjang
    have hθj : (D.tile (tile (i + k))).localAngle (mkPt (X (i + k)) 0) = γ ∨
        (D.tile (tile (i + k))).localAngle (mkPt (X (i + k)) 0) = β := by
      rw [hjang]
      cases T
      · exact Or.inr rfl
      · exact Or.inl rfl
      · exact absurd rfl hZ1
      · exact Or.inl rfl
      · exact absurd rfl hZ2
      · exact Or.inr rfl
    obtain ⟨kj, mj, jj, -, -, -, -, hmj, -, -⟩ := hj
    have hU' := hU
    rw [eV] at hU'
    refine C.K3G_of_next hU hint (fun W Z hW hθ hZ => ?_)
    rw [eV] at hW hθ
    refine S.bad_nb hx0 hxL hG1 hU' (by rw [lpG_snd]; ring) hβ0 hmj (mkPt_one _ _)
      (mkPt_ne_of_fst (by linarith)) ?_ hθj hW hθ hZ
    rw [eA]; exact mkPt_ne_of_fst (by linarith)

/-- **`L'_k` for `C_2`: a run of `k < f` tiles `C2`** ending at `(X (i+k), 0)`, with (K1) there, does not start at `Q` nor after a tile
showing `γ`. -/
theorem kill_C2G (S : SetupG D e f α β γ L ax ay) (Co : CornersG e f L ax ay)
    (Ch : ChainG D e f L m X tile τ) {i k : ℕ} (hk1 : 1 ≤ k) (hkf : k < f) (hik : i + k < m)
    (hrun : ∀ j, j < k → τ (i + j) = Ty.C2)
    (hK1 : ∀ (t' : Fin N) (k' m' : Fin 3), k' ≠ m' →
      (D.tile t').pts k' = lpG (e : ℝ) (f : ℝ) (-1) (X (i + k)) 0 0 →
      (D.tile t').pts m' = lpG (e : ℝ) (f : ℝ) (-1) (X (i + k)) 0 1 →
      (∀ i', FXG (e : ℝ) (f : ℝ) (-1) ((D.tile t').pts i') ≤ lvG (e : ℝ) (f : ℝ) (-1) (X (i + k)) 0) → False)
    (hpred : i = 0 ∨ (τ (i - 1)).gR) : False := by
  have he0 := S.e0
  have hef := S.hef'
  have hhp := hhG_pos he0 hef
  have hc := S.c_pos
  have hx0 : 0 < X (i + k) := Ch.pos S (by omega) (by omega)
  have hxL : X (i + k) < L := Ch.lt_L S hik
  have C : CtxG D e f α β γ L ax ay (-1) (X (i + k)) :=
    ⟨⟨S, Or.inr rfl⟩, hK1, S.hch_pos hx0 hxL (Ch.mem hik)⟩
  have hpos := Ch.run_pos (T := Ty.C2) (c := (f : ℝ) ^ 2) rfl hik.le hrun
  have hx : X (i + k) = X i + k * (f : ℝ) ^ 2 := hpos k le_rfl
  have hUT : ∀ j : ℕ, j < k → UTG D (e : ℝ) (f : ℝ) (-1) (X (i + k)) j 0 := by
    intro j hj
    have h := Ch.htile (i + (k - 1 - j)) (by omega)
    rw [hrun (k - 1 - j) (by omega)] at h
    have hcj : ((k - 1 - j : ℕ) : ℝ) = (k : ℝ) - 1 - j := by
      rw [Nat.cast_sub (show j ≤ k - 1 by omega), Nat.cast_sub hk1, Nat.cast_one]
    refine ⟨tile (i + (k - 1 - j)), S.c2_lpG h ?_⟩
    rw [hpos (k - 1 - j) (by omega), hcj, hx]; ring
  refine C.run_diesG hk1 hkf hUT ?_
  -- the first tile of the run, `U(k−1, 0)`
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
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · -- the run starts at `Q`
    have hXi : X i = 0 := by rw [hi0]; exact Ch.hX0
    rcases Co.hQ with ⟨t, ht, hax, hay⟩ | ⟨t, ht, hax, hay⟩
    · exact S.K3G_out_left ht hax hay (by rw [hx, hXi]; ring)
    · have hQ := S.corner_left_ab ht hax hay
      rw [hXi] at eV hβ0 hU'
      have eG : lpG (e : ℝ) (f : ℝ) (-1) (X (i + k)) ((k : ℝ) - 1) (0 + 1) = mkPt (uuG (e : ℝ) (f : ℝ)) (hhG (e : ℝ) (f : ℝ)) := by
        unfold lpG; exact mkPt_congr (by rw [hx, hXi]; ring) (by ring)
      have hGmem : mkPt (uuG (e : ℝ) (f : ℝ)) (hhG (e : ℝ) (f : ℝ)) ∈ D.target.carrier := by
        rw [← eG]; exact hU.mem₃
      have hQmem : mkPt 0 0 ∈ D.target.carrier := by
        have := Ch.mem (k := i) (by omega)
        rwa [hXi] at this
      have hint : openSegment ℝ (lpG (e : ℝ) (f : ℝ) (-1) (X (i + k)) ((k : ℝ) - 1 + 1) 0)
          (lpG (e : ℝ) (f : ℝ) (-1) (X (i + k)) ((k : ℝ) - 1) (0 + 1)) ⊆ interior D.target.carrier := by
        rw [eV, eG]
        have hu := uuG_spec he0 hef
        have hh' := hhG_spec he0 hef
        have hrt := rtG_pos he0 hef
        have key : 2 * (f : ℝ) ^ 2 * (rtG (e : ℝ) (f : ℝ) * uuG (e : ℝ) (f : ℝ) - (e : ℝ) * hhG (e : ℝ) (f : ℝ))
            = 2 * (f : ℝ) ^ 2 * (rtG (e : ℝ) (f : ℝ) * (e : ℝ) ^ 2) := by
          linear_combination (rtG (e : ℝ) (f : ℝ)) * hu - (e : ℝ) * hh'
        have hX : rtG (e : ℝ) (f : ℝ) * uuG (e : ℝ) (f : ℝ) - (e : ℝ) * hhG (e : ℝ) (f : ℝ) = rtG (e : ℝ) (f : ℝ) * (e : ℝ) ^ 2 :=
          mul_left_cancel₀ (two_f2_pos he0 hef).ne' key
        refine S.interior_seg hQmem hGmem (Or.inr (by rw [mkPt_one]; exact hhp)) (Or.inr ?_)
          (Or.inl ?_)
        · rw [gA_mk, hax, hay]
          have e' : t * rtG (e : ℝ) (f : ℝ) * uuG (e : ℝ) (f : ℝ) - t * (e : ℝ) * hhG (e : ℝ) (f : ℝ)
              = t * (rtG (e : ℝ) (f : ℝ) * (e : ℝ) ^ 2) := by
            linear_combination t * hX
          rw [e']; positivity
        · rw [gB_mk]; nlinarith [mul_pos S.hay S.hL]
      refine C.K3G_of_next hU hint (fun W Z hW hθ hZ => ?_)
      rw [eV] at hW hθ
      exact S.bad_corner hQ hG1 hU' hA1 hβ0 hW hθ hZ
  · -- the tile before the run shows `γ`
    have hg : (τ (i - 1)).gR := by
      rcases hpred with h | h
      · omega
      · exact h
    have hxi0 : 0 < X i := Ch.pos S hipos (by omega)
    have hxiL : X i < L := Ch.lt_L S (by omega)
    have hp := Ch.htile (i - 1) (by omega)
    have e' := Ch.prev hipos (by omega : i ≤ m)
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

end SetupG

end Erdos634.Draft.SideRunG

#print axioms Erdos634.Draft.SideRunG.ChainG.run_pos
#print axioms Erdos634.Draft.SideRunG.SetupG.exists_chainG
#print axioms Erdos634.Draft.SideRunG.SetupG.c1_lpG
#print axioms Erdos634.Draft.SideRunG.SetupG.c2_lpG
#print axioms Erdos634.Draft.SideRunG.SetupG.kill_C1G
#print axioms Erdos634.Draft.SideRunG.SetupG.kill_C2G
