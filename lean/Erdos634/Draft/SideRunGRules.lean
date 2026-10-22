/-
Draft/SideRunGRules.lean -- written 14 October 2026.  UNAUDITED.  In `AllThreshold`.  Module 9 of ten.

**The side theorem for every member**, under `SetupG` and `CornersG` (the target in normal position): the typed word of the side
`QB` satisfies the rules of the word theorem, hence the side carries `f` consecutive tiles of type `C_1` or `f` consecutive tiles of
type `C_2`, and `L ≥ f³`.  Paper: Theorem `thm:siderunall` ("The side", rules (a), (b), (c), end conditions) and Corollary
`cor:ebelow` (the counts on the side).

THE WORD THEOREM IS REUSED, NOT COPIED.  `SideRunWords.SideRules n m τ` and `SideRunWords.side_word` are stated for a natural
number `n` that is only the bound on the runs (`k < n` in the rules `ra`, `rb`, `rc`) and for the six letters `Ty`; they contain no
e = 1 arithmetic.  They are used here with `n := f`.  (The e = 1 arithmetic of that file, `rep_jb`, `rep_qc`, `rep_side`,
`no_side_word`, is replaced by `SideRunGArith.C_QB`, `C_base` and the counting lemmas of this file.)  So there is no
`SideRunGWords.lean`.

CONTENTS.
* `SetupG.angleQ_leG`: the angle of the target at `Q` is `≤ α + β`.
* `SetupG.side_rulesG`: **the typed word of the side satisfies `SideRules f m τ`**: `rQ` (the first tile is not of type `L`), `rB` (the
  last is `A2` or `C1`), `rGG` (two `γ` never meet: `2 γ > π`), and the run rules `ra`, `rb`, `rc`, from `kill_C1G`, `kill_C2G`,
  `junction`, `K1_of_gamma` (fed from the base data of the left tile: its base edge has length `a` or `b` because it shows `γ`
  at its right end), `K1_of_corner`, `hch_pos`, `hch_corner`.
* `SetupG.side_theoremG`: the run of `f` tiles `C1` or `C2` in the chain; `side_theoremG_chain`: with the chain of the dissection.
* `SetupG.side_theorem_paperG`: **the paper form**: there are `x₀ ≥ 0` and tiles `t 0, …, t (f−1)` with
  `BaseTileG D e f (t j) Ty.C1 (x₀ + j f²)` for all `j < f`, or the same with `Ty.C2`, and `x₀ + f·f² ≤ L`; in particular `f³ ≤ L`.
  (`BaseTileG D e f i C1 x`: the tile `i` has the vertices `(x, 0)` and `(x + f², 0)` on the side and its third vertex at the distances
  `b` from the first and `a` from the second, i.e. it lays its side `c` on `s` and shows `α` at the left end; `C2`: at the right end.)
* The counts: `lenN`, `lenG_cast`, `SetupG.sideG_counts` (a typed chain of total length `L` gives naturals `x, y, z` with
  `x a + y b + z c = L` and, if the chain has a run of `f` tiles `C1` or `C2`, `f ≤ z`), `SetupG.no_tiling_QB`,
  `SetupG.no_tiling_base` (`cor:ebelow` for the targets in normal position: `L = M e (2f² − e²)` with `M e < f`, resp.
  `L = M e (3f² − e²)` with `2 M e < f`).
* Checks at `e = 1`: `side_rules_e1`, `side_theorem_e1`.

WHAT DIFFERS FROM THE e = 1 TEXT.  (i) `α < β` is not used (the e = 1 text obtains `S.alpha_lt_beta` in `side_rules` and does not need it
there; in `ra` the corner tile showing `β` and `α` is excluded by `α ≠ β`).  (ii) `Corners`' second form is `ax = t e`,
`ay = t rtG e f`.  (iii) The counts use `C_QB`, `C_base` (`y ≡ M e (mod f)`, `z ≤ M e`, `z ≤ 2 M e`), not `rep_side`.

WITNESSES.  `SideRules f m τ` is satisfiable: `SideRunWords.exRules f` (the word `C1^f`).  The hypotheses `SetupG`, `CornersG`, `ChainG`
of `side_theoremG` are satisfied by a real dissection with `e ≥ 2`: see `Draft/SideRunGMain.lean` (`setupG_witness_member`, `setupG_witness_e2`, `siderunall_seed`; the import closure of that file contains no `Refl.M*` module, so no separate witness file is needed);
at `e = 1` by every `Setup`, `Corners`, `Chain` (parts A-C of the Sources).  `no_tiling_QB`/`no_tiling_base` conclude `False` (the
statement of `cor:ebelow`); their hypotheses are satisfiable (a dissection of `W_f(e, f)`, where `M e = f e ≥ f`, exists: the bound
`M e < f` is sharp).

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGSourcesC

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

namespace SetupG

variable {e f : ℕ} {α β γ L ax ay : ℝ} {m : ℕ} {X : ℕ → ℝ} {tile : ℕ → Fin N} {τ : ℕ → Ty}

theorem angleQ_leG (S : SetupG D e f α β γ L ax ay) (Co : CornersG e f L ax ay) :
    D.target.localAngle (mkPt 0 0) ≤ α + β := by
  have hα := S.hA.hα
  rcases Co.hQ with ⟨t, ht, hax, hay⟩ | ⟨t, ht, hax, hay⟩
  · have h := (D.target).localAngle_vertex 0
    rw [S.corner_left_beta ht hax hay, S.Q_eq] at h
    rw [h]; linarith
  · exact (S.corner_left_ab ht hax hay).le

/-- **The typed word of the side satisfies the rules of the side theorem** (with the run bound `f`). -/
theorem side_rulesG (S : SetupG D e f α β γ L ax ay) (Co : CornersG e f L ax ay)
    (Ch : ChainG D e f L m X tile τ) : SideRules f m τ := by
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have he0 := S.e0
  have hef := S.hef'
  have hc := S.c_pos
  have hm0 := Ch.hm0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- rQ
    have h := Ch.htile 0 hm0
    rw [Ch.hX0] at h
    have ha := (S.angles h).1
    have hle := one_angle_le D.toDissection (mkPt 0 0) (tile 0)
    have hQ := S.angleQ_leG Co
    have hγdef := S.hA.hγdef
    constructor
    · intro hT
      rw [hT] at ha
      have ha' : (D.tile (tile 0)).localAngle (mkPt 0 0) = γ := ha
      rw [ha'] at hle
      linarith
    · intro hT
      rw [hT] at ha
      have ha' : (D.tile (tile 0)).localAngle (mkPt 0 0) = γ := ha
      rw [ha'] at hle
      linarith
  · -- rB
    obtain ⟨hαβ', hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hβ2π, hγπ', hγ0, hπ0⟩ := distinct_of_angleData S.hA
    obtain ⟨t, ht, hax, hay⟩ := Co.hB
    have h := Ch.htile (m - 1) (by omega)
    have hx := Ch.prev hm0 le_rfl
    rw [Ch.hXm] at hx
    have ha := (S.angles h).2
    rw [hx] at ha
    obtain ⟨k', m', j', -, -, -, -, hm', -, -⟩ := h
    rw [hx] at hm'
    have hmem : D.target.pts 1 ∈ (D.tile (tile (m - 1))).carrier := by
      rw [S.B_eq, ← hm']; exact subset_convexHull ℝ _ ⟨m', rfl⟩
    have hang := S.corner_tile_beta 1 (S.corner_right_beta ht hax hay) hmem
    rw [S.B_eq, ha] at hang
    exact Ty.aR_eq_beta hαβ' hβγ _ hang
  · -- rGG
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
  · -- ra
    intro i k hk1 hkn hik hrun hp
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
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · have hXi : X i = 0 := by rw [hi0]; exact Ch.hX0
      have hQmem : mkPt 0 0 ∈ D.target.carrier := by
        have := Ch.mem (k := i) (by omega)
        rwa [hXi] at this
      rcases Co.hQ with ⟨t, ht, hax, hay⟩ | ⟨t, ht, hax, hay⟩
      · -- a corner of angle `β`: its tile shows `β`, not `α`
        have ha := (S.angles h00).1
        rw [hXi] at ha
        obtain ⟨k', m', j', -, -, -, hk', -, -, -⟩ := h00
        rw [hXi] at hk'
        have hmem : D.target.pts 0 ∈ (D.tile (tile i)).carrier := by
          rw [S.Q_eq, ← hk']; exact subset_convexHull ℝ _ ⟨k', rfl⟩
        have hang := S.corner_tile_beta 0 (S.corner_left_beta ht hax hay) hmem
        rw [S.Q_eq, ha] at hang
        have hang' : α = β := hang
        exact S.hA.hαβ hang'
      · have hQ := S.corner_left_ab ht hax hay
        have hU0 := S.c1_lpG (x := (0 : ℝ)) (ξ := 0) h00 (by rw [hXi]; ring)
        exact S.kill_C1G Co Ch hk1 hkn hik hrun hXi (S.K1_of_corner (by norm_num) hQ hU0)
          (S.hch_corner ht hax hay hQmem) hsucc
    · have hg : (τ (i - 1)).gR := by
        rcases hp with h | h
        · omega
        · exact h
      have hx0 : 0 < X i := Ch.pos S hipos (by omega)
      have hxL : X i < L := Ch.lt_L S (by omega)
      have hU0 := S.c1_lpG (x := X i) (ξ := 0) h00 (by ring)
      have hpj := Ch.htile (i - 1) (by omega)
      have e' := Ch.prev hipos (by omega : i ≤ m)
      have hγj : (D.tile (tile (i - 1))).localAngle (mkPt (X i) 0) = γ := by
        have h := (S.angles hpj).2
        rw [e', Ty.aR_of_gR α β γ hg] at h
        exact h
      have hlam : (τ (i - 1)).lenG (e : ℝ) (f : ℝ) = (e : ℝ) * (f : ℝ) ∨ (τ (i - 1)).lenG (e : ℝ) (f : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
        rcases hg with h | h
        · rw [h]; exact Or.inl rfl
        · rw [h]; exact Or.inr rfl
      obtain ⟨kj, mj, jj, hkmj, -, -, hkj, hmj, -, -⟩ := hpj
      rw [e'] at hmj
      have hkj' : (D.tile (tile (i - 1))).pts kj
          = mkPt (X i - 1 * (τ (i - 1)).lenG (e : ℝ) (f : ℝ)) 0 := by
        rw [hkj]; exact mkPt_congr (by rw [← e']; ring) rfl
      exact S.kill_C1G Co Ch hk1 hkn hik hrun rfl
        (S.K1_of_gamma (by norm_num) hx0 hxL hU0 (Ne.symm hkmj) hmj hkj' hlam hγj)
        (S.hch_pos hx0 hxL (Ch.mem (by omega))) hsucc
  · -- rb
    intro i k hk1 hkn hik hrun hp hgL
    have hx0 : 0 < X (i + k) := Ch.pos S (by omega) (by omega)
    have hxL : X (i + k) < L := Ch.lt_L S hik
    have hlast := Ch.htile (i + (k - 1)) (by omega)
    rw [hrun (k - 1) (by omega)] at hlast
    have hstep := Ch.hstep (i + (k - 1)) (by omega)
    rw [hrun (k - 1) (by omega), show i + (k - 1) + 1 = i + k by omega] at hstep
    have hU0 := S.c2_lpG (x := X (i + k)) (ξ := 0) hlast (by
      have h' : X (i + k) = X (i + (k - 1)) + (f : ℝ) ^ 2 := hstep
      rw [h']; ring)
    have hj := Ch.htile (i + k) hik
    have hγj : (D.tile (tile (i + k))).localAngle (mkPt (X (i + k)) 0) = γ := by
      have h := (S.angles hj).1
      rw [Ty.aL_of_gL α β γ hgL] at h
      exact h
    have hlam : (τ (i + k)).lenG (e : ℝ) (f : ℝ) = (e : ℝ) * (f : ℝ) ∨ (τ (i + k)).lenG (e : ℝ) (f : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
      rcases hgL with h | h
      · rw [h]; exact Or.inl rfl
      · rw [h]; exact Or.inr rfl
    obtain ⟨kj, mj, jj, hkmj, -, -, hkj, hmj, -, -⟩ := hj
    have hmj' : (D.tile (tile (i + k))).pts mj
        = mkPt (X (i + k) - (-1) * (τ (i + k)).lenG (e : ℝ) (f : ℝ)) 0 := by
      rw [hmj]; exact mkPt_congr (by ring) rfl
    exact S.kill_C2G Co Ch hk1 hkn hik hrun
      (S.K1_of_gamma (by norm_num) hx0 hxL hU0 hkmj hkj hmj' hlam hγj) hp
  · -- rc
    intro i s r hs1 hsn hr1 hrn hisr hrun2 hrun1 hp
    have hJ0 : 0 < X (i + s) := Ch.pos S (by omega) (by omega)
    have hJL : X (i + s) < L := Ch.lt_L S (by omega)
    -- the first `C1` and the last `C2`
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
      exact S.kill_C1G Co Ch hr1 hrn hisr hrun1 rfl hK
        (S.hch_pos hJ0 hJL (Ch.mem (by omega))) hsucc
    · exact (S.kill_C2G Co Ch hs1 hsn (by omega) hrun2 hK hp).elim

/-- **THE SIDE THEOREM, every member** (chain form): the side `QB` carries `f` consecutive tiles of type `C1` or `f` consecutive
tiles of type `C2`. -/
theorem side_theoremG (S : SetupG D e f α β γ L ax ay) (Co : CornersG e f L ax ay)
    (Ch : ChainG D e f L m X tile τ) :
    ∃ i, i + f ≤ m ∧ ((∀ j, j < f → τ (i + j) = Ty.C1) ∨ (∀ j, j < f → τ (i + j) = Ty.C2)) :=
  side_word f m τ Ch.hm0 (S.side_rulesG Co Ch)

/-- the side theorem, with the chain of the dissection -/
theorem side_theoremG_chain (S : SetupG D e f α β γ L ax ay) (Co : CornersG e f L ax ay) :
    ∃ (m : ℕ) (X : ℕ → ℝ) (tile : ℕ → Fin N) (τ : ℕ → Ty), ChainG D e f L m X tile τ ∧
      ∃ i, i + f ≤ m ∧ ((∀ j, j < f → τ (i + j) = Ty.C1) ∨ (∀ j, j < f → τ (i + j) = Ty.C2)) := by
  obtain ⟨m, X, tile, τ, Ch⟩ := S.exists_chainG
  exact ⟨m, X, tile, τ, Ch, S.side_theoremG Co Ch⟩

/-- **THE SIDE THEOREM, paper form** (`thm:siderunall`, normal position): there are `x₀ ≥ 0` and `f` tiles `t 0, …, t (f−1)` that
lay their side `c` on the side `s = [Q, B]` at `x₀, x₀ + c, …` and show `α` at the same end of it (all at the left end: type `C1`,
`BaseTileG … C1`; all at the right end: type `C2`), with `x₀ + f·f² ≤ L`; in particular `f³ ≤ L`. -/
theorem side_theorem_paperG (S : SetupG D e f α β γ L ax ay) (Co : CornersG e f L ax ay) :
    ∃ (x₀ : ℝ) (t : ℕ → Fin N), 0 ≤ x₀ ∧ x₀ + (f : ℝ) * (f : ℝ) ^ 2 ≤ L ∧
      ((∀ j, j < f → BaseTileG D (e : ℝ) (f : ℝ) (t j) Ty.C1 (x₀ + j * (f : ℝ) ^ 2)) ∨
       (∀ j, j < f → BaseTileG D (e : ℝ) (f : ℝ) (t j) Ty.C2 (x₀ + j * (f : ℝ) ^ 2))) ∧
      (f : ℝ) ^ 3 ≤ L := by
  obtain ⟨m, X, tile, τ, Ch, i, him, hrun⟩ := S.side_theoremG_chain Co
  have hf2 := S.hf2
  have hx0 := Ch.nonneg S (k := i) (by omega)
  have hend : X (i + f) ≤ L := by
    have h1 := (S.baseTile_range (Ch.htile (i + f - 1) (by omega))).2
    have h2 := Ch.hstep (i + f - 1) (by omega)
    rw [show i + f - 1 + 1 = i + f by omega] at h2
    linarith
  have hfc : (f : ℝ) * (f : ℝ) ^ 2 = (f : ℝ) ^ 3 := by ring
  rcases hrun with hrun | hrun
  · have hpos := Ch.run_pos (T := Ty.C1) (c := (f : ℝ) ^ 2) rfl him hrun
    have hXf : X (i + f) = X i + f * (f : ℝ) ^ 2 := hpos f le_rfl
    refine ⟨X i, fun j => tile (i + j), hx0, by linarith, Or.inl (fun j hj => ?_), by linarith⟩
    have h := Ch.htile (i + j) (by omega)
    rw [hrun j hj, hpos j hj.le] at h
    exact h
  · have hpos := Ch.run_pos (T := Ty.C2) (c := (f : ℝ) ^ 2) rfl him hrun
    have hXf : X (i + f) = X i + f * (f : ℝ) ^ 2 := hpos f le_rfl
    refine ⟨X i, fun j => tile (i + j), hx0, by linarith, Or.inr (fun j hj => ?_), by linarith⟩
    have h := Ch.htile (i + j) (by omega)
    rw [hrun j hj, hpos j hj.le] at h
    exact h

/-! ## The counts on the side -/

end SetupG

/-- the length of a letter, as a natural number: `x a + y b + z c` -/
def lenN (e f : ℕ) (t : Ty) : ℕ := t.cA * (e * f) + t.cB * (f ^ 2 - e ^ 2) + t.cC * f ^ 2

theorem lenG_cast {e f : ℕ} (hef : e < f) (t : Ty) : t.lenG (e : ℝ) (f : ℝ) = (lenN e f t : ℝ) := by
  obtain ⟨b, hbN, hbR⟩ := exists_bR hef
  have h : lenN e f t = t.cA * (e * f) + t.cB * b + t.cC * f ^ 2 := by
    unfold lenN; rw [hbN]
  rw [h]
  cases t <;> simp [Ty.lenG, Ty.cA, Ty.cB, Ty.cC, hbR]

namespace SetupG

variable {e f : ℕ} {α β γ L ax ay : ℝ} {m : ℕ} {X : ℕ → ℝ} {tile : ℕ → Fin N} {τ : ℕ → Ty}

/-- **The counts on the side**: a typed chain of length `L` has `x, y, z` letters of lengths `a, b, c` with
`x a + y b + z c = L`, and a run of `f` tiles `C1` or of `f` tiles `C2` gives `f ≤ z`. -/
theorem sideG_counts (S : SetupG D e f α β γ L ax ay) (Ch : ChainG D e f L m X tile τ) :
    ∃ x y z : ℕ, (x : ℝ) * ((e : ℝ) * f) + y * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z * (f : ℝ) ^ 2 = L ∧
      ((∃ i, i + f ≤ m ∧ ((∀ j, j < f → τ (i + j) = Ty.C1) ∨ (∀ j, j < f → τ (i + j) = Ty.C2))) →
        f ≤ z) := by
  have hsub : (((f ^ 2 - e ^ 2 : ℕ)) : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rw [Nat.cast_sub (Nat.pow_le_pow_left S.hef.le 2)]; push_cast; ring
  have hN : ∑ k ∈ Finset.range m, lenN e f (τ k)
      = (∑ k ∈ Finset.range m, (τ k).cA) * (e * f) + (∑ k ∈ Finset.range m, (τ k).cB) * (f ^ 2 - e ^ 2)
        + (∑ k ∈ Finset.range m, (τ k).cC) * f ^ 2 := by
    simp only [lenN, Finset.sum_add_distrib, Finset.sum_mul]
  have h1 : ∀ k ∈ Finset.range m, (τ k).lenG (e : ℝ) (f : ℝ) = X (k + 1) - X k := by
    intro k hk
    rw [Ch.hstep k (Finset.mem_range.mp hk)]; ring
  have h2 : L = ∑ k ∈ Finset.range m, (τ k).lenG (e : ℝ) (f : ℝ) := by
    rw [Finset.sum_congr rfl h1, Finset.sum_range_sub, Ch.hXm, Ch.hX0, sub_zero]
  have h3 : ∑ k ∈ Finset.range m, (τ k).lenG (e : ℝ) (f : ℝ)
      = ((∑ k ∈ Finset.range m, lenN e f (τ k) : ℕ) : ℝ) := by
    rw [Nat.cast_sum]; exact Finset.sum_congr rfl (fun k _ => lenG_cast S.hef (τ k))
  refine ⟨∑ k ∈ Finset.range m, (τ k).cA, ∑ k ∈ Finset.range m, (τ k).cB,
    ∑ k ∈ Finset.range m, (τ k).cC, ?_, ?_⟩
  · rw [h2, h3, hN]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, hsub]
  · rintro ⟨i, him, hrun⟩
    exact cC_run τ i f m him hrun

end SetupG

/-- a real equation `x a + y b + z c = M e (κ f² − e²)` is the natural number equation of `C_QB` (`κ = 2`) / `C_base` (`κ = 3`) -/
theorem rep_nat_len {e f x y z M κ : ℕ} (hef : e < f) (hκ : 1 ≤ κ)
    (h : (x : ℝ) * ((e : ℝ) * f) + y * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z * (f : ℝ) ^ 2
      = (M : ℝ) * (e : ℝ) * ((κ : ℝ) * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) :
    x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = M * e * (κ * f ^ 2 - e ^ 2) := by
  obtain ⟨b, hbN, hbR⟩ := exists_bR hef
  have hle : e ^ 2 ≤ κ * f ^ 2 :=
    (Nat.pow_le_pow_left hef.le 2).trans (Nat.le_mul_of_pos_left _ hκ)
  obtain ⟨b', hb'N, hb'R⟩ : ∃ b' : ℕ, κ * f ^ 2 - e ^ 2 = b' ∧ (b' : ℝ) = (κ : ℝ) * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    refine ⟨κ * f ^ 2 - e ^ 2, rfl, ?_⟩
    rw [Nat.cast_sub hle]; push_cast; ring
  rw [hbN, hb'N]
  rw [← hbR, ← hb'R] at h
  exact_mod_cast h

namespace SetupG

variable {e f : ℕ} {α β γ L ax ay : ℝ}

/-- **`cor:ebelow` (a), normal position**: the side `QB` of `W_M(e, f)`, of length `M e (2 f² − e²)`, `M e < f`, cannot be the
side `QB` of a `SetupG` with `CornersG`. -/
theorem no_tiling_QB (S : SetupG D e f α β γ L ax ay) (Co : CornersG e f L ax ay) {M : ℕ}
    (hMe : M * e < f) (hL : L = (M : ℝ) * (e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) : False := by
  obtain ⟨m, X, tile, τ, Ch, hrun⟩ := S.side_theoremG_chain Co
  obtain ⟨x, y, z, hxyz, hz⟩ := S.sideG_counts Ch
  have hfz := hz hrun
  have hnat := rep_nat_len (M := M) (κ := 2) S.hef (by norm_num) (by rw [hxyz, hL]; norm_num)
  have hC := (SideRunGArith.C_QB S.he S.hef S.hco hnat).2 hMe
  exact absurd (hfz.trans hC.2) (not_le.mpr hMe)

/-- **`cor:ebelow` (b), normal position**: the base of `T_M(e, f)`, of length `M e (3 f² − e²)`, `2 M e < f`. -/
theorem no_tiling_base (S : SetupG D e f α β γ L ax ay) (Co : CornersG e f L ax ay) {M : ℕ}
    (hMe : 2 * (M * e) < f) (hL : L = (M : ℝ) * (e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) : False := by
  obtain ⟨m, X, tile, τ, Ch, hrun⟩ := S.side_theoremG_chain Co
  obtain ⟨x, y, z, hxyz, hz⟩ := S.sideG_counts Ch
  have hfz := hz hrun
  have hnat := rep_nat_len (M := M) (κ := 3) S.hef (by norm_num) (by rw [hxyz, hL]; norm_num)
  have hC := (SideRunGArith.C_base S.he S.hef S.hco hnat).2 (by omega)
  exact absurd (hfz.trans hC.2) (not_le.mpr hMe)

end SetupG

/-! ## Checks at `e = 1` -/

section e_one

variable {n : ℕ} {α β γ L ax ay : ℝ} {m : ℕ} {X : ℕ → ℝ} {tile : ℕ → Fin N} {τ : ℕ → Ty}

/-- **`side_rulesG` at `e = 1` is `SideRun.Setup.side_rules`** -/
theorem side_rules_e1 (S : Setup D n α β γ L ax ay) (Co : Corners n L ax ay)
    (Ch : Chain D n L m X tile τ) : SideRules n m τ :=
  (setupG_one_iff.mpr S).side_rulesG (cornersG_of Co) (chainG_of Ch)

/-- **`side_theoremG` at `e = 1` is `SideRun.Setup.side_theorem`** -/
theorem side_theorem_e1 (S : Setup D n α β γ L ax ay) (Co : Corners n L ax ay)
    (Ch : Chain D n L m X tile τ) :
    ∃ i, i + n ≤ m ∧ ((∀ j, j < n → τ (i + j) = Ty.C1) ∨ (∀ j, j < n → τ (i + j) = Ty.C2)) :=
  (setupG_one_iff.mpr S).side_theoremG (cornersG_of Co) (chainG_of Ch)

end e_one

end Erdos634.Draft.SideRunG

#print axioms Erdos634.Draft.SideRunG.SetupG.side_rulesG
#print axioms Erdos634.Draft.SideRunG.SetupG.side_theoremG
#print axioms Erdos634.Draft.SideRunG.SetupG.side_theoremG_chain
#print axioms Erdos634.Draft.SideRunG.SetupG.side_theorem_paperG
#print axioms Erdos634.Draft.SideRunG.SetupG.sideG_counts
#print axioms Erdos634.Draft.SideRunG.SetupG.no_tiling_QB
#print axioms Erdos634.Draft.SideRunG.SetupG.no_tiling_base
#print axioms Erdos634.Draft.SideRunG.side_rules_e1
#print axioms Erdos634.Draft.SideRunG.side_theorem_e1
