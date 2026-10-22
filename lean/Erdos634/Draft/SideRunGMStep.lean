/-
Draft/SideRunGMStep.lean -- written 14 October 2026.  UNAUDITED.  In `AllThreshold`.  Module M2 of the plan for
`thm:cornerrun` (see the header of `Draft/SideRunGJChord.lean`; M1 is `Draft/SideRunGMirror.lean`).

**The induction for the statement `M(s', j0)`: the tools and STEP (a).**  Paper: Theorem `thm:cornerrun`, "Proof of `M(s', j0)`, size `n ≥ 2`", step
(a); (private working notes, not included) Section 4.  Steps (b) and (c), the induction `MG_all` and the corollary are in `Draft/SideRunGMStepB.lean`,
`Draft/SideRunGMStepC.lean`.

CONTENTS.
1. `ChordsAt D e f ε x`: the open chords `(p(0,0), p(0,j))` are interior to Δ (the paper's "`P` is a point of `s` at which `ℓ` leaves Δ", as `CtxJ` needs it);
   `MGh D e f ε n`: **the induction predicate**: `MG` for all origins `x` with `ChordsAt x` and all pairs of size `n`.  `MGh_one`.
   `chordsAt_shift_K2`: the origin `p(n, 0)`, `1 ≤ n`, `n + 1 ≤ s`, of a lattice satisfying (K2) is an open point of the side, so its chords are interior
   (`SetupG.hch_pos`).
2. The vertex figures as counting statements (`fig_int`, `fig_bdry`: the multiplicities at an interior / boundary point of the target, from
   `CornerAnglePerm.congruentDissection_interior_figure_at_corner`, `TileAt.congruentDissection_boundary_figure_cases`: this is the paper's fact (F)),
   and `card_le_angle`.
3. The tile beside a `b`-edge on a line `ℓ_c`: `col_next` (the tile `E` of the side σ with an edge on `ℓ_c` from `p(c, η)`: it lays `a` or `c` -- (K1) -- or it has the
   whole `b`-edge), the clamps (`clamp_side`: `p(c, 0)` lies on the side; `clamp_tile`: the `b`-edge of a tile of the side σ ends at `p(c, η + 1)`),
   `bedge_interior`, `mirror_of_b0`/`mirror_of_b_n` (a tile with the `b`-edge and an angle `≠ γ` at `P` is the mirror tile).
4. `beside_contra`: **the paper's two-line argument "If `E` lays `a` or `c`, (K1) holds against `K(s − n, j)`; if `E` lays `b`, it is the mirror image of `U(n, j)` in `ℓ_n`,
   against `M(s − n, j)`"**, at a shifted origin: from `ColNext` and the angle `≠ γ`, `False`.
5. `lower_half`: the four lattice tiles `D(a, η)`, `U(a+1, η)`, `D(a+1, η)`, `U(a+1, η+1)` at `p(a+1, η+1)` (angles `α, γ, β, α`; the point is interior).
6. STEP (a): `noN_gamma_int`, `noN_gamma_bdry` (the tile `E` beside the `b`-edge of `U(i+1, j0)` does not show `γ` at `p(i+1, j0)` when `N_i(j0)` is a tile),
   `noN_M` (**`N_i(j0)` is not a tile**, the paper's "Suppose `S_i = N_i(j0)`. ... against `K(s − i − 1, j0)` / `M(s − i − 1, j0)`"),
   `stepA` (**`D(i, j0)` is a tile for `0 ≤ i ≤ n − 2`**: `CtxBase.D_ofG`).

CORRESPONDENCE with the paper's step (a): "free wedge at `p(i+1, j0)`", "`S_i`", "if `S_i` lays `b` or `c` ... `M(i+1+j0, j0)`" is `D_ofG` (module `SideRunGRowB`, steps
(2a)-(2b) of `K`) with the hypothesis `hR` from `MGh (i+1)`; "`S_i = N_i(j0)`" is `noN_M`; "the rest of the wedge, `(α, π − 2β)`, has the angle `2α`: two tiles
showing `α` (F)" is replaced by the counting `fig_int` / `fig_bdry` at the point `p(i+1, j0)` (the tile `E` beside the `b`-edge of `U(i+1, j0)` lays `a`, `b` or `c` on `ℓ_{i+1}`;
`b` with `γ` is excluded by the figure; `b` with `α` is the mirror image; `a` and `c` are (K1)): `col_next`, `noN_gamma_*`, `beside_contra`.

WITNESSES.  The statements conclude `False` or the existence of tiles under the hypotheses of the induction; they are about configurations that the proof shows do not
occur together; the non-vacuity of the hypotheses is that of `MG` (see `Draft/SideRunGMirror.lean`).

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGMirror

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

/-! ## 1. The chords, the induction predicate -/

/-- the open chords from `p(0,0)` along `ℓ` are interior to the target -/
def ChordsAt (D : CongruentDissection N) (e f ε x : ℝ) : Prop :=
  ∀ j : ℕ, 1 ≤ j → lpG e f ε x 0 j ∈ D.target.carrier →
    openSegment ℝ (lpG e f ε x 0 0) (lpG e f ε x 0 j) ⊆ interior D.target.carrier

/-- **THE INDUCTION PREDICATE**: `M` for all origins with interior chords, for the pairs of size `n` -/
def MGh (D : CongruentDissection N) (e f : ℕ) (ε : ℝ) (n : ℕ) : Prop :=
  ∀ (x : ℝ) (s j0 : ℕ), ChordsAt D (e : ℝ) (f : ℝ) ε x → s - j0 = n → MG D e f ε x s j0

section defs

variable {e f : ℕ} {α β γ L ax ay ε x : ℝ}

theorem MGh_one (S : SetupG D e f α β γ L ax ay) (hε : ε = 1 ∨ ε = -1) : MGh D e f ε 1 :=
  fun x s j0 _ hsz => MGn_one S hε x s j0 hsz

/-- the origin `p(n, 0)`, `1 ≤ n`, `n + 1 ≤ s`, of a lattice with (K2) is an open point of the side -/
theorem open_shift_K2 (S : SetupG D e f α β γ L ax ay) {s j0 n : ℕ}
    (hK2 : K2G D (e : ℝ) (f : ℝ) 1 x s j0) (hn : 1 ≤ n) (hns : n + 1 ≤ s) :
    0 < shiftX (f : ℝ) 1 x n ∧ shiftX (f : ℝ) 1 x n < L ∧
      mkPt (shiftX (f : ℝ) 1 x n) 0 ∈ D.target.carrier := by
  obtain ⟨t0, h0⟩ := hK2.1 0 0 (Nat.zero_le _) (by omega)
  obtain ⟨tn, hn1⟩ := hK2.1 n 0 (Nat.zero_le _) (by omega)
  have hm0 : mkPt x 0 ∈ D.target.carrier := by
    have := h0.mem₁
    rwa [Nat.cast_zero, lpG_zero] at this
  have h1 : mkPt (x + ((n : ℝ) + 1) * (f : ℝ) ^ 2) 0 ∈ D.target.carrier := by
    have := hn1.mem₂
    rwa [Nat.cast_zero, show lpG (e : ℝ) (f : ℝ) 1 x ((n : ℝ) + 1) 0
      = mkPt (x + ((n : ℝ) + 1) * (f : ℝ) ^ 2) 0 from by unfold lpG; exact mkPt_congr (by ring) (by ring)]
      at this
  have hP : mkPt (shiftX (f : ℝ) 1 x n) 0 ∈ D.target.carrier := by
    have := hn1.mem₁
    rwa [Nat.cast_zero, show lpG (e : ℝ) (f : ℝ) 1 x (n : ℝ) 0 = mkPt (shiftX (f : ℝ) 1 x n) 0 from by
      unfold lpG shiftX; exact mkPt_congr (by ring) (by ring)] at this
  obtain ⟨hx0, hxL⟩ := shift_open_point S hn hm0 h1
  exact ⟨hx0, hxL, hP⟩

/-- the origin `p(n, 0)` of a lattice with (K2) is an open point of the side: its chords are interior -/
theorem chordsAt_shift_K2 (S : SetupG D e f α β γ L ax ay) {s j0 n : ℕ}
    (hK2 : K2G D (e : ℝ) (f : ℝ) 1 x s j0) (hn : 1 ≤ n) (hns : n + 1 ≤ s) :
    ChordsAt D (e : ℝ) (f : ℝ) 1 (shiftX (f : ℝ) 1 x n) := by
  obtain ⟨hx0, hxL, hP⟩ := open_shift_K2 S hK2 hn hns
  exact S.hch_pos hx0 hxL hP

end defs

/-! ## 2. Vertex figures as counting statements -/

section fig

variable {e f : ℕ} {α β γ L ax ay : ℝ}

/-- the multiplicities (straight angles, `α`, `β`, `γ`) at an interior vertex of a tile -/
def FigI (p a b g : ℕ) : Prop :=
  (p = 1 ∧ ((a = 3 ∧ b = 2 ∧ g = 0) ∨ (a = 1 ∧ b = 1 ∧ g = 1))) ∨
  (p = 0 ∧ ((a = 6 ∧ b = 4 ∧ g = 0) ∨ (a = 4 ∧ b = 3 ∧ g = 1) ∨ (a = 2 ∧ b = 2 ∧ g = 2) ∨
    (a = 0 ∧ b = 1 ∧ g = 3)))

/-- the multiplicities at a boundary point of the target that is not a vertex of the target -/
def FigB (p a b g : ℕ) : Prop :=
  (p = 1 ∧ a = 0 ∧ b = 0 ∧ g = 0) ∨ (a = 3 ∧ b = 2 ∧ g = 0) ∨ (a = 1 ∧ b = 1 ∧ g = 1)

theorem fig_int (S : SetupG D e f α β γ L ax ay) {v : Plane} (hv : v ∈ interior D.target.carrier)
    {j : Fin N} {m : Fin 3} (hjm : (D.tile j).pts m = v) :
    FigI ({i | (D.tile i).localAngle v = Real.pi} : Finset (Fin N)).card
      ({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card
      ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card
      ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card := by
  have hA := S.hA
  obtain ⟨hαβ, hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hγπ, hγ0, hπ0⟩ :=
    distinct_of_pos_ne hA.hα hA.hβ hA.hαβ hA.hγdef hA.hrel
  have hpi := Real.pi_pos
  have hrel := hA.hrel
  have hγdef := hA.hγdef
  have hα2π : α ≠ 2 * Real.pi := by intro h; linarith [hA.hβ]
  have hβ2π : β ≠ 2 * Real.pi := by intro h; linarith [hA.hα]
  have hγ2π : γ ≠ 2 * Real.pi := by intro h; linarith [hA.hα, hA.hβ]
  have hπ2π : Real.pi ≠ 2 * Real.pi := by intro h; linarith
  have h2π0 : 2 * Real.pi ≠ 0 := by positivity
  exact congruentDissection_interior_figure_at_corner D α β γ hαβ hαγ hαπ hα2π hα0 hβγ hβπ
    hβ2π hβ0 hγπ hγ2π hγ0 hπ2π hπ0 h2π0 S.hM.hα' S.hM.hβ' S.hM.hγ' hA.hγdef hA.hrel hA.hirr hv j m hjm

theorem fig_bdry (S : SetupG D e f α β γ L ax ay) {v : Plane} (hv : v ∈ frontier D.target.carrier)
    (hnv : v ∉ Set.range D.target.pts) :
    FigB ({i | (D.tile i).localAngle v = Real.pi} : Finset (Fin N)).card
      ({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card
      ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card
      ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card := by
  have hA := S.hA
  obtain ⟨hαβ, hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hγπ, hγ0, hπ0⟩ :=
    distinct_of_pos_ne hA.hα hA.hβ hA.hαβ hA.hγdef hA.hrel
  exact congruentDissection_boundary_figure_cases D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
    hA.hγdef hA.hrel hA.hirr S.hM.hα' S.hM.hβ' S.hM.hγ' hv hnv

theorem card_le_angle {v : Plane} (s : Finset (Fin N)) (a : ℝ)
    (h : ∀ i ∈ s, (D.tile i).localAngle v = a) :
    s.card ≤ ({i | (D.tile i).localAngle v = a} : Finset (Fin N)).card :=
  Finset.card_le_card (fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ i, h i hi⟩)

theorem forall_mem2 {P : Fin N → Prop} {a b : Fin N} (ha : P a) (hb : P b) :
    ∀ i ∈ ({a, b} : Finset (Fin N)), P i := by
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl <;> assumption

theorem forall_mem3 {P : Fin N → Prop} {a b c : Fin N} (ha : P a) (hb : P b) (hc : P c) :
    ∀ i ∈ ({a, b, c} : Finset (Fin N)), P i := by
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl <;> assumption

theorem card2 {a b : Fin N} (hab : a ≠ b) : ({a, b} : Finset (Fin N)).card = 2 :=
  Finset.card_pair hab

theorem card3 {a b c : Fin N} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Finset (Fin N)).card = 3 :=
  Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩

end fig

/-! ## 3. The tile beside a `b`-edge of a line `ℓ_c` -/

section col

variable {e f : ℕ} {α β γ L ax ay ε x : ℝ}

theorem lpG_mid_eta (e f ε x c η : ℝ) :
    lpG e f ε x c (η + 1) ∈ openSegment ℝ (lpG e f ε x c η) (lpG e f ε x c (η + 1 + 1)) := by
  refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
  unfold lpG
  apply plane_ext <;>
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mkPt_zero, mkPt_one] <;> ring

/-- **the clamp of `p(c, 0)`, a point of the side**, in the form `next_tile` wants -/
theorem clamp_side (S : SetupG D e f α β γ L ax ay) (hε : ε ^ 2 = 1) (c η : ℝ) (hη : η = 0) :
    ∃ P' : Plane, FXG (e : ℝ) (f : ℝ) ε P' = lvG (e : ℝ) (f : ℝ) ε x c ∧
      lpG (e : ℝ) (f : ℝ) ε x c η ∈ openSegment ℝ P' (lpG (e : ℝ) (f : ℝ) ε x c (η + 1)) ∧
      ∀ ed ∈ D.lineChain (FXG (e : ℝ) (f : ℝ) ε) (lvG (e : ℝ) (f : ℝ) ε x c),
        ¬ Straddles ((D.tile ed.1).edge ed.2) P' (lpG (e : ℝ) (f : ℝ) ε x c η)
          (lpG (e : ℝ) (f : ℝ) ε x c (η + 1)) := by
  have hhp := hhG_pos S.e0 S.hef'
  have hP1 : (lpG (e : ℝ) (f : ℝ) ε x c η) 1 = 0 := by rw [lpG_snd, hη]; ring
  have hQ1 : 0 < (lpG (e : ℝ) (f : ℝ) ε x c (η + 1)) 1 := by rw [lpG_snd, hη]; linarith
  have hfP : FXG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x c η) = lvG (e : ℝ) (f : ℝ) ε x c :=
    FXG_lp hε c η
  have hfQ : FXG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x c (η + 1)) = lvG (e : ℝ) (f : ℝ) ε x c :=
    FXG_lp hε c (η + 1)
  exact ⟨_, ext_level (FXG (e : ℝ) (f : ℝ) ε) hfP hfQ 1, mem_openSegment_ext _ _ one_pos,
    clamp_out D.toDissection (FXG (e : ℝ) (f : ℝ) ε) _ (S.below_out hP1 hQ1)⟩

/-- **the clamp of `p(c, η + 1)` by the `b`-edge `[p(c, η), p(c, η + 1)]` of a tile of the side σ** -/
theorem clamp_tile (S : SetupG D e f α β γ L ax ay) (hε : ε ^ 2 = 1) {c η : ℝ} {t : Fin N} {k m : Fin 3}
    (hkm : k ≠ m) (hk : (D.tile t).pts k = lpG (e : ℝ) (f : ℝ) ε x c η)
    (hm : (D.tile t).pts m = lpG (e : ℝ) (f : ℝ) ε x c (η + 1))
    (hle : ∀ i, FXG (e : ℝ) (f : ℝ) ε ((D.tile t).pts i) ≤ lvG (e : ℝ) (f : ℝ) ε x c) :
    ∃ P' : Plane, FXG (e : ℝ) (f : ℝ) ε P' = lvG (e : ℝ) (f : ℝ) ε x c ∧
      lpG (e : ℝ) (f : ℝ) ε x c (η + 1) ∈ openSegment ℝ P' (lpG (e : ℝ) (f : ℝ) ε x c (η + 1 + 1)) ∧
      ∀ ed ∈ D.lineChain (FXG (e : ℝ) (f : ℝ) ε) (lvG (e : ℝ) (f : ℝ) ε x c),
        ¬ Straddles ((D.tile ed.1).edge ed.2) P' (lpG (e : ℝ) (f : ℝ) ε x c (η + 1))
          (lpG (e : ℝ) (f : ℝ) ε x c (η + 1 + 1)) := by
  have he0 := S.e0
  have hef := S.hef'
  have hPQ : lpG (e : ℝ) (f : ℝ) ε x c (η + 1) ≠ lpG (e : ℝ) (f : ℝ) ε x c (η + 1 + 1) :=
    lpG_ne_eta he0 hef (by intro h; linarith)
  have hf1 : FXG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x c η) = lvG (e : ℝ) (f : ℝ) ε x c :=
    FXG_lp hε c η
  have hf2 : FXG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x c (η + 1)) = lvG (e : ℝ) (f : ℝ) ε x c :=
    FXG_lp hε c (η + 1)
  have hf3 : FXG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x c (η + 1 + 1)) = lvG (e : ℝ) (f : ℝ) ε x c :=
    FXG_lp hε c (η + 1 + 1)
  have hmid := lpG_mid_eta (e : ℝ) (f : ℝ) ε x c η
  exact ⟨_, hf1, hmid, clamp_b D.toDissection (FXG (e : ℝ) (f : ℝ) ε) (FXG_ne he0 hef hε) _ hPQ hf2 hf3
    hf1 hmid hkm hk hm hle⟩

/-- **the `b`-edge of `U(c, η)` on `ℓ_c` is interior to Δ**, if a lattice point to its left, on the level of its lower end, lies in Δ -/
theorem bedge_interior (C : CtxBase D e f α β γ L ax ay ε x) {c η : ℝ} (hη : 0 ≤ η) {t₀ : Fin N}
    (h0 : HasV D t₀ (lpG (e : ℝ) (f : ℝ) ε x c η) (lpG (e : ℝ) (f : ℝ) ε x (c + 1) η)
      (lpG (e : ℝ) (f : ℝ) ε x c (η + 1)))
    (hL : lpG (e : ℝ) (f : ℝ) ε x (c - 1) η ∈ D.target.carrier) :
    openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x c η) (lpG (e : ℝ) (f : ℝ) ε x c (η + 1))
      ⊆ interior D.target.carrier :=
  C.seg_intG h0.mem₁ h0.mem₃ (Or.inr (by linarith)) (Or.inl ⟨1, one_pos, h0.mem₂⟩)
    (Or.inl ⟨1, one_pos, hL⟩)

/-- **what is found beside the `b`-edge `[p(c, η), p(c, η+1)]` of `U(c, η)` on the side σ of `ℓ_c`**: a tile of the side σ with an edge on `ℓ_c` from `p(c, η)`
upward of length `a` or `c` -- (K1) at the row `η` --, or a tile of the side σ with the whole `b`-edge -/
def ColNext (D : CongruentDissection N) (e f ε x c η : ℝ) : Prop :=
  (∃ (iT : Fin N) (k m : Fin 3) (t : ℝ), k ≠ m ∧ (D.tile iT).pts k = lpG e f ε x c η ∧
      (D.tile iT).pts m = lpG e f ε x c (η + t) ∧ 0 < t ∧
      (t * (f ^ 2 - e ^ 2) = e * f ∨ t * (f ^ 2 - e ^ 2) = f ^ 2) ∧
      ∀ i, FXG e f ε ((D.tile iT).pts i) ≤ lvG e f ε x c) ∨
  (∃ (iT : Fin N) (k m : Fin 3), k ≠ m ∧ (D.tile iT).pts k = lpG e f ε x c η ∧
      (D.tile iT).pts m = lpG e f ε x c (η + 1) ∧
      ∀ i, FXG e f ε ((D.tile iT).pts i) ≤ lvG e f ε x c)

/-- **THE TILE BESIDE THE `b`-EDGE** (the generalization of `corner_nextT`, `corner_K1J_or_b` to any column `c`, any level `η`, any clamp from below) -/
theorem col_next (S : SetupG D e f α β γ L ax ay) (hε : ε ^ 2 = 1) {c η : ℝ} {t₀ : Fin N}
    (h0 : HasV D t₀ (lpG (e : ℝ) (f : ℝ) ε x c η) (lpG (e : ℝ) (f : ℝ) ε x (c + 1) η)
      (lpG (e : ℝ) (f : ℝ) ε x c (η + 1)))
    (hint : openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x c η) (lpG (e : ℝ) (f : ℝ) ε x c (η + 1))
      ⊆ interior D.target.carrier)
    (hcl : ∃ P' : Plane, FXG (e : ℝ) (f : ℝ) ε P' = lvG (e : ℝ) (f : ℝ) ε x c ∧
      lpG (e : ℝ) (f : ℝ) ε x c η ∈ openSegment ℝ P' (lpG (e : ℝ) (f : ℝ) ε x c (η + 1)) ∧
      ∀ ed ∈ D.lineChain (FXG (e : ℝ) (f : ℝ) ε) (lvG (e : ℝ) (f : ℝ) ε x c),
        ¬ Straddles ((D.tile ed.1).edge ed.2) P' (lpG (e : ℝ) (f : ℝ) ε x c η)
          (lpG (e : ℝ) (f : ℝ) ε x c (η + 1))) :
    ColNext D (e : ℝ) (f : ℝ) ε x c η := by
  have he0 := S.e0
  have hef := S.hef'
  have hb := S.b_pos
  have hPQ : lpG (e : ℝ) (f : ℝ) ε x c η ≠ lpG (e : ℝ) (f : ℝ) ε x c (η + 1) :=
    lpG_ne_eta he0 hef (by intro h; linarith)
  have hfP : FXG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x c η) = lvG (e : ℝ) (f : ℝ) ε x c :=
    FXG_lp hε c η
  have hfQ : FXG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x c (η + 1)) = lvG (e : ℝ) (f : ℝ) ε x c :=
    FXG_lp hε c (η + 1)
  have hwall : ∀ y ∈ openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x c η) (lpG (e : ℝ) (f : ℝ) ε x c (η + 1)),
      ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    obtain ⟨k0, m0, j0, hkm0, hkj0, hmj0, hk0, hm0, hj0⟩ := h0
    refine seg_wall D.toDissection (t := t₀) hkj0 ?_
    rw [hk0, hj0]
    exact openSegment_subset_segment ℝ _ _ hy
  obtain ⟨P', hfP', hP', hP⟩ := hcl
  obtain ⟨ed, hed, k, m, t, hkm, hk, ht, hm, hle, -, hdist⟩ :=
    next_tile D.toDissection (FXG (e : ℝ) (f : ℝ) ε) (FXG_ne he0 hef hε) (lvG (e : ℝ) (f : ℝ) ε x c)
      hPQ hfP hfQ hfP' hP' hint hwall hP
  have hl : AffineMap.lineMap (lpG (e : ℝ) (f : ℝ) ε x c η) (lpG (e : ℝ) (f : ℝ) ε x c (η + 1)) t
      = lpG (e : ℝ) (f : ℝ) ε x c (η + t) := by
    rw [lineMap_lpG]
    exact lpG_congr (by ring) (by ring)
  rw [hl] at hm hdist
  have hd : dist (lpG (e : ℝ) (f : ℝ) ε x c η) (lpG (e : ℝ) (f : ℝ) ε x c (η + t))
      = t * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) :=
    dist_lpG he0 hef hε (mul_nonneg ht.le hb.le) (by unfold QfG; ring)
  have hlen := edge_length_casesG D S.hM ed.1 ed.2
  rw [hdist, hd] at hlen
  rcases hlen with h | h | h
  · exact Or.inl ⟨ed.1, k, m, t, hkm, hk, hm, ht, Or.inl h, hle⟩
  · right
    have ht1 : t = 1 := by
      have h2 : (t - 1) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) = 0 := by linarith
      rcases mul_eq_zero.mp h2 with h3 | h3
      · linarith
      · exact absurd h3 hb.ne'
    subst ht1
    exact ⟨ed.1, k, m, hkm, hk, hm, hle⟩
  · exact Or.inl ⟨ed.1, k, m, t, hkm, hk, hm, ht, Or.inr h, hle⟩

/-- **a tile of the side σ with the `b`-edge `[P, Q]` of `ℓ` and an angle `≠ γ` at `P` is the mirror tile** (the generalization of `corner_mirror`) -/
theorem mirror_of_b0 (S : SetupG D e f α β γ L ax ay) (hε : ε ^ 2 = 1) {η : ℝ} {iT : Fin N} {k m : Fin 3}
    (hkm : k ≠ m) (hk : (D.tile iT).pts k = lpG (e : ℝ) (f : ℝ) ε x 0 η)
    (hm : (D.tile iT).pts m = lpG (e : ℝ) (f : ℝ) ε x 0 (η + 1))
    (hle : ∀ i, FXG (e : ℝ) (f : ℝ) ε ((D.tile iT).pts i) ≤ lvG (e : ℝ) (f : ℝ) ε x 0)
    (hnγ : (D.tile iT).localAngle (lpG (e : ℝ) (f : ℝ) ε x 0 η) ≠ γ) :
    MirrorAt D (e : ℝ) (f : ℝ) ε x η := by
  have he0 := S.e0
  have hef := S.hef'
  obtain ⟨n, hnk, hnm⟩ := fin3_third k m hkm
  have hkn : k ≠ n := Ne.symm hnk
  have hmn : m ≠ n := Ne.symm hnm
  have hd : dist ((D.tile iT).pts k) ((D.tile iT).pts m) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rw [hk, hm]; exact dist_step_vG he0 hef hε 0 η
  have hfk : FXG (e : ℝ) (f : ℝ) ε ((D.tile iT).pts k) = lvG (e : ℝ) (f : ℝ) ε x 0 := by
    rw [hk]; exact FXG_lp hε 0 η
  have hfm : FXG (e : ℝ) (f : ℝ) ε ((D.tile iT).pts m) = lvG (e : ℝ) (f : ℝ) ε x 0 := by
    rw [hm]; exact FXG_lp hε 0 (η + 1)
  have hRlt := third_strict (D.tile iT) hkm hkn hmn (FXG (e : ℝ) (f : ℝ) ε)
    (FXG_ne he0 hef hε) (lvG (e : ℝ) (f : ℝ) ε x 0) hfk hfm hle
  rcases sides_of_b_edgeG D S.tile S.hM iT hkm hkn hmn hd with ⟨s1, s2⟩ | ⟨s1, s2⟩
  · exfalso
    have hang := (angle_at_vertexG D S.tile S.hM iT hkm hkn hmn).2.2 (by rw [dist_comm]; exact s2)
    rw [hk] at hang
    exact hnγ hang
  · have hs := mirK_mul S
    have hRP : dist ((D.tile iT).pts n) (lpG (e : ℝ) (f : ℝ) ε x 0 η) = (f : ℝ) ^ 2 := by
      rw [← hk]; exact s1
    have hRQ : dist ((D.tile iT).pts n) (lpG (e : ℝ) (f : ℝ) ε x 0 (η + 1)) = (e : ℝ) * f := by
      rw [← hm]; exact s2
    have hR3 := mirror_third he0 hef hε η _ hs hRP hRQ hRlt
    exact ⟨iT, k, m, n, hkm, hkn, hmn, hk, hm, hR3⟩

/-- the same at the shifted origin `p(n, 0)`: the hypotheses are read in the coordinates of the lattice of origin `x` -/
theorem mirror_of_b_n (S : SetupG D e f α β γ L ax ay) (hε : ε ^ 2 = 1) {n : ℕ} {η : ℝ} {iT : Fin N}
    {k m : Fin 3} (hkm : k ≠ m) (hk : (D.tile iT).pts k = lpG (e : ℝ) (f : ℝ) ε x (n : ℝ) η)
    (hm : (D.tile iT).pts m = lpG (e : ℝ) (f : ℝ) ε x (n : ℝ) (η + 1))
    (hle : ∀ i, FXG (e : ℝ) (f : ℝ) ε ((D.tile iT).pts i) ≤ lvG (e : ℝ) (f : ℝ) ε x (n : ℝ))
    (hnγ : (D.tile iT).localAngle (lpG (e : ℝ) (f : ℝ) ε x (n : ℝ) η) ≠ γ) :
    MirrorAt D (e : ℝ) (f : ℝ) ε (shiftX (f : ℝ) ε x n) η := by
  have hP : lpG (e : ℝ) (f : ℝ) ε (shiftX (f : ℝ) ε x n) 0 η = lpG (e : ℝ) (f : ℝ) ε x (n : ℝ) η := by
    rw [lpG_shift]; exact lpG_congr (zero_add _) rfl
  have hQ : lpG (e : ℝ) (f : ℝ) ε (shiftX (f : ℝ) ε x n) 0 (η + 1)
      = lpG (e : ℝ) (f : ℝ) ε x (n : ℝ) (η + 1) := by
    rw [lpG_shift]; exact lpG_congr (zero_add _) rfl
  have hL : lvG (e : ℝ) (f : ℝ) ε (shiftX (f : ℝ) ε x n) 0 = lvG (e : ℝ) (f : ℝ) ε x (n : ℝ) := by
    rw [lvG_shift hε, zero_add]
  exact mirror_of_b0 S hε hkm (hk.trans hP.symm) (hm.trans hQ.symm) (fun i => by rw [hL]; exact hle i)
    (by rw [hP]; exact hnγ)

end col

/-! ## 4. The two-line argument of the paper at a shifted origin -/

section beside

variable {e f : ℕ} {α β γ L ax ay ε x : ℝ}

/-- (K3) at the shifted origin, for natural first indices -/
theorem K3G_shift_nat (hε : ε ^ 2 = 1) {n s j : ℕ}
    (hK3 : K3G D (e : ℝ) (f : ℝ) ε x ((s + n : ℕ) : ℝ) (j : ℝ)) :
    K3G D (e : ℝ) (f : ℝ) ε (shiftX (f : ℝ) ε x n) (s : ℝ) (j : ℝ) := by
  have h := (K3G_shift (D := D) hε x n ((s + n : ℕ) : ℝ) (j : ℝ)).mpr hK3
  rwa [show ((s + n : ℕ) : ℝ) - n = s by push_cast; ring] at h

/-- **THE PAPER'S ARGUMENT AT THE TILE `E` BESIDE `U(n, j)`, with (K2), (K3) given in the shifted lattice** ("If `E` lays `a` or `c`, then (K1) holds for it, against
`K(s − n, j)`.  If `E` lays `b`, then `E` is the mirror image of `U(n, j)` in `ℓ_n`, against `M(s − n, j)`"): the column is `c = n` and the level `η = j` in the coordinates of the
lattice of origin `x`; the shifted lattice has the origin `shiftX n x`, the first index `s'`, interior chords; `hnγ` says that the tile `E`, if it has the whole `b`-edge, does not show
`γ` at `p(n, j)` (the vertex figure).  (Conclusion `False`.) -/
theorem beside_core (S : SetupG D e f α β γ L ax ay) (hε : ε = 1 ∨ ε = -1) {n s' j m : ℕ} {c η : ℝ}
    (hc : c = (n : ℝ)) (hη : η = (j : ℝ))
    (hch : ChordsAt D (e : ℝ) (f : ℝ) ε (shiftX (f : ℝ) ε x n))
    (hK2' : K2G D (e : ℝ) (f : ℝ) ε (shiftX (f : ℝ) ε x n) s' j)
    (hK3' : K3G D (e : ℝ) (f : ℝ) ε (shiftX (f : ℝ) ε x n) (s' : ℝ) (j : ℝ))
    (hjs : j < s') (hsf : s' < f) (IH : MGh D e f ε m) (hm : s' - j = m) (hme : s' - j ≤ e)
    (hE : ColNext D (e : ℝ) (f : ℝ) ε x c η)
    (hnγ : ∀ (iT : Fin N) (k m' : Fin 3), k ≠ m' → (D.tile iT).pts k = lpG (e : ℝ) (f : ℝ) ε x c η →
      (D.tile iT).pts m' = lpG (e : ℝ) (f : ℝ) ε x c (η + 1) →
      (∀ i, FXG (e : ℝ) (f : ℝ) ε ((D.tile iT).pts i) ≤ lvG (e : ℝ) (f : ℝ) ε x c) →
      (D.tile iT).localAngle (lpG (e : ℝ) (f : ℝ) ε x c η) ≠ γ) : False := by
  subst hc
  subst hη
  have he2 : ε ^ 2 = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  rcases hE with ⟨iT, k, m', t, hkm, hk, hm', ht, hlen, hle⟩ | ⟨iT, k, m', hkm, hk, hm', hle⟩
  · have hK1 : K1J D (e : ℝ) (f : ℝ) ε (shiftX (f : ℝ) ε x n) j := by
      rw [K1J_shift he2]
      exact ⟨iT, k, m', t, hkm, hk, hm', ht, hlen, hle⟩
    have Cj := CtxJ.of_K1J S hε hch hK1
    exact Cj.K_allGJ (s' - j) (by omega) s' j le_rfl hjs hsf rfl hK2' hK3'
  · have hmirror := mirror_of_b_n S he2 hkm hk hm' hle (hnγ iT k m' hkm hk hm' hle)
    exact IH (shiftX (f : ℝ) ε x n) s' j hch hm hjs hsf hme hmirror hK2' hK3'

/-- **the same, with (K2) and (K3) of the given (unshifted) lattice** (`K2G_shift`, `K3G_shift_nat`) -/
theorem beside_contra (S : SetupG D e f α β γ L ax ay) (hε : ε = 1 ∨ ε = -1) {n s' j m : ℕ} {c η : ℝ}
    (hc : c = (n : ℝ)) (hη : η = (j : ℝ))
    (hch : ChordsAt D (e : ℝ) (f : ℝ) ε (shiftX (f : ℝ) ε x n))
    (hK2 : K2G D (e : ℝ) (f : ℝ) ε x (s' + n) j)
    (hK3 : K3G D (e : ℝ) (f : ℝ) ε x ((s' + n : ℕ) : ℝ) (j : ℝ))
    (hjs : j < s') (hsf : s' < f) (IH : MGh D e f ε m) (hm : s' - j = m) (hme : s' - j ≤ e)
    (hE : ColNext D (e : ℝ) (f : ℝ) ε x c η)
    (hnγ : ∀ (iT : Fin N) (k m' : Fin 3), k ≠ m' → (D.tile iT).pts k = lpG (e : ℝ) (f : ℝ) ε x c η →
      (D.tile iT).pts m' = lpG (e : ℝ) (f : ℝ) ε x c (η + 1) →
      (∀ i, FXG (e : ℝ) (f : ℝ) ε ((D.tile iT).pts i) ≤ lvG (e : ℝ) (f : ℝ) ε x c) →
      (D.tile iT).localAngle (lpG (e : ℝ) (f : ℝ) ε x c η) ≠ γ) : False := by
  have he2 : ε ^ 2 = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  exact beside_core S hε hc hη hch (K2G_shift hK2) (K3G_shift_nat (D := D) he2 hK3) hjs hsf IH hm hme hE
    hnγ

end beside

/-! ## 5. The four lattice tiles below and to the right of `p(a+1, η+1)` -/

section lower

variable {e f : ℕ} {α β γ L ax ay ε x : ℝ}

theorem lower_half (S : SetupG D e f α β γ L ax ay) (hε : ε ^ 2 = 1) {a η : ℝ}
    {tDL tUl tDl tUr : Fin N}
    (hDL : HasV D tDL (lpG (e : ℝ) (f : ℝ) ε x (a + 1) η) (lpG (e : ℝ) (f : ℝ) ε x a (η + 1))
      (lpG (e : ℝ) (f : ℝ) ε x (a + 1) (η + 1)))
    (hUl : HasV D tUl (lpG (e : ℝ) (f : ℝ) ε x (a + 1) η) (lpG (e : ℝ) (f : ℝ) ε x (a + 1 + 1) η)
      (lpG (e : ℝ) (f : ℝ) ε x (a + 1) (η + 1)))
    (hDl : HasV D tDl (lpG (e : ℝ) (f : ℝ) ε x (a + 1 + 1) η) (lpG (e : ℝ) (f : ℝ) ε x (a + 1) (η + 1))
      (lpG (e : ℝ) (f : ℝ) ε x (a + 1 + 1) (η + 1)))
    (hUr : HasV D tUr (lpG (e : ℝ) (f : ℝ) ε x (a + 1) (η + 1))
      (lpG (e : ℝ) (f : ℝ) ε x (a + 1 + 1) (η + 1)) (lpG (e : ℝ) (f : ℝ) ε x (a + 1) (η + 1 + 1))) :
    (D.tile tDL).localAngle (lpG (e : ℝ) (f : ℝ) ε x (a + 1) (η + 1)) = α ∧
    (D.tile tUl).localAngle (lpG (e : ℝ) (f : ℝ) ε x (a + 1) (η + 1)) = γ ∧
    (D.tile tDl).localAngle (lpG (e : ℝ) (f : ℝ) ε x (a + 1) (η + 1)) = β ∧
    (D.tile tUr).localAngle (lpG (e : ℝ) (f : ℝ) ε x (a + 1) (η + 1)) = α ∧
    lpG (e : ℝ) (f : ℝ) ε x (a + 1) (η + 1) ∈ interior D.target.carrier ∧
    tDL ≠ tUl ∧ tDL ≠ tDl ∧ tDL ≠ tUr ∧ tUl ≠ tDl ∧ tUl ≠ tUr ∧ tDl ≠ tUr := by
  have he0 := S.e0
  have hef := S.hef'
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  obtain ⟨hαβ, hαγ, -, -, hβγ, -, -, -, -, -⟩ :=
    distinct_of_pos_ne S.hA.hα S.hA.hβ S.hA.hαβ S.hA.hγdef S.hA.hrel
  have a1 := (D_anglesG S hε hDL).2.2
  have a2 := (U_anglesG S hε hUl).2.2
  have a3 := (D_anglesG S hε hDl).2.1
  have a4 := (U_anglesG S hε hUr).1
  have n12 : tDL ≠ tUl := ne_of_angle (by rw [a1, a2]; exact hαγ)
  have n13 : tDL ≠ tDl := ne_of_angle (by rw [a1, a3]; exact hαβ)
  have n23 : tUl ≠ tDl := ne_of_angle (by rw [a2, a3]; exact hβγ.symm)
  have n24 : tUl ≠ tUr := ne_of_angle (by rw [a2, a4]; exact hαγ.symm)
  have n34 : tDl ≠ tUr := ne_of_angle (by rw [a3, a4]; exact hαβ.symm)
  have hleDL : ∀ i, FXG (e : ℝ) (f : ℝ) ε ((D.tile tDL).pts i) ≤ lvG (e : ℝ) (f : ℝ) ε x (a + 1) := by
    refine hDL.all (P := fun p => FXG (e : ℝ) (f : ℝ) ε p ≤ lvG (e : ℝ) (f : ℝ) ε x (a + 1))
      (le_of_eq (FXG_lp hε _ _)) ?_ (le_of_eq (FXG_lp hε _ _))
    dsimp only
    rw [FXG_lp hε]
    exact lvG_le he0 hef (by linarith)
  have n14 : tDL ≠ tUr := by
    obtain ⟨k2, hk2⟩ := hUr.idx₂
    exact ne_of_F (FXG (e : ℝ) (f : ℝ) ε) hleDL (i := k2)
      (by rw [hk2, FXG_lp hε]; exact lvG_lt he0 hef (by linarith))
  refine ⟨a1, a2, a3, a4, ?_, n12, n13, n14, n23, n24, n34⟩
  refine interior_of_four D n12 n13 n14 n23 n24 n34 ?_
  rw [a1, a2, a3, a4]
  linarith

end lower

/-! ## 6. Step (a): `D(i, j0)` is a tile -/

section stepa

variable {e f : ℕ} {α β γ L ax ay ε x : ℝ}

theorem lpG_y_le {e f ε x ξ η c : ℝ} (he : 0 < e) (hef : e < f) (h : η ≤ c) :
    (lpG e f ε x ξ η) 1 ≤ c * hhG e f := by
  rw [lpG_snd]; exact mul_le_mul_of_nonneg_right h (hhG_pos he hef).le

theorem lpG_y_gt {e f ε x ξ η c : ℝ} (he : 0 < e) (hef : e < f) (h : c < η) :
    c * hhG e f < (lpG e f ε x ξ η) 1 := by
  rw [lpG_snd]; exact mul_lt_mul_of_pos_right h (hhG_pos he hef)

/-- **the tile `E` beside `U(a+1, η+1)` does not show `γ` at `p(a+1, η+1)` when `N(a, η+1)` is a tile** (interior case, `η + 1 ≥ 1`): the vertex figure at that point
has at least three tiles showing `β` (`U(a, η+1)`, `N`, `D(a+1, η)`) and at least two showing `γ` (`U(a+1, η)`, `E`), and no figure of (F) does.  (Conclusion `False`.) -/
theorem noN_gamma_int (S : SetupG D e f α β γ L ax ay) (hε : ε ^ 2 = 1) {a η : ℝ}
    {tDL tUl tDl tUr tUi tN iT : Fin N}
    (hDL : HasV D tDL (lpG (e : ℝ) (f : ℝ) ε x (a + 1) η) (lpG (e : ℝ) (f : ℝ) ε x a (η + 1))
      (lpG (e : ℝ) (f : ℝ) ε x (a + 1) (η + 1)))
    (hUl : HasV D tUl (lpG (e : ℝ) (f : ℝ) ε x (a + 1) η) (lpG (e : ℝ) (f : ℝ) ε x (a + 1 + 1) η)
      (lpG (e : ℝ) (f : ℝ) ε x (a + 1) (η + 1)))
    (hDl : HasV D tDl (lpG (e : ℝ) (f : ℝ) ε x (a + 1 + 1) η) (lpG (e : ℝ) (f : ℝ) ε x (a + 1) (η + 1))
      (lpG (e : ℝ) (f : ℝ) ε x (a + 1 + 1) (η + 1)))
    (hUr : HasV D tUr (lpG (e : ℝ) (f : ℝ) ε x (a + 1) (η + 1))
      (lpG (e : ℝ) (f : ℝ) ε x (a + 1 + 1) (η + 1)) (lpG (e : ℝ) (f : ℝ) ε x (a + 1) (η + 1 + 1)))
    (hUi : HasV D tUi (lpG (e : ℝ) (f : ℝ) ε x a (η + 1)) (lpG (e : ℝ) (f : ℝ) ε x (a + 1) (η + 1))
      (lpG (e : ℝ) (f : ℝ) ε x a (η + 1 + 1)))
    (hN : HasV D tN (lpG (e : ℝ) (f : ℝ) ε x (a + 1) (η + 1)) (lpG (e : ℝ) (f : ℝ) ε x a (η + 1 + 1))
      (lpG (e : ℝ) (f : ℝ) ε x (a - nuG (e : ℝ) (f : ℝ)) (η + 1 + 2 + nuG (e : ℝ) (f : ℝ))))
    (hEle : ∀ i, FXG (e : ℝ) (f : ℝ) ε ((D.tile iT).pts i) ≤ lvG (e : ℝ) (f : ℝ) ε x (a + 1))
    (hEγ : (D.tile iT).localAngle (lpG (e : ℝ) (f : ℝ) ε x (a + 1) (η + 1)) = γ) : False := by
  have he0 := S.e0
  have hef := S.hef'
  obtain ⟨a1, a2, a3, a4, hint, n12, n13, n14, n23, n24, n34⟩ := lower_half S hε hDL hUl hDl hUr
  have aUi := (U_anglesG S hε hUi).2.1
  have aN := (N_anglesG S hε hN).1
  have hleN := hN.all (P := fun p => GSG (e : ℝ) (f : ℝ) ε p ≤ -lvG (e : ℝ) (f : ℝ) ε x (a + (η + 1) + 1))
    (GSG_le he0 hef hε (by linarith)) (GSG_le he0 hef hε (by linarith))
    (GSG_le he0 hef hε (by linarith))
  have nUiN : tUi ≠ tN := by
    obtain ⟨k, hk⟩ := hUi.idx₁
    exact (ne_of_F (GSG (e : ℝ) (f : ℝ) ε) hleN (i := k)
      (by rw [hk]; exact GSG_gt he0 hef hε (by linarith))).symm
  have hyDl : ∀ i, ((D.tile tDl).pts i) 1 ≤ (η + 1) * hhG (e : ℝ) (f : ℝ) :=
    hDl.all (P := fun p => p 1 ≤ (η + 1) * hhG (e : ℝ) (f : ℝ))
      (lpG_y_le he0 hef (by linarith)) (lpG_y_le he0 hef le_rfl) (lpG_y_le he0 hef le_rfl)
  have nUiDl : tUi ≠ tDl := by
    obtain ⟨k, hk⟩ := hUi.idx₃
    exact (ne_of_F (fun p : Plane => p 1) hyDl (i := k)
      (by rw [hk]; exact lpG_y_gt he0 hef (by linarith))).symm
  have nNDl : tN ≠ tDl := by
    obtain ⟨k, hk⟩ := hN.idx₂
    exact (ne_of_F (fun p : Plane => p 1) hyDl (i := k)
      (by rw [hk]; exact lpG_y_gt he0 hef (by linarith))).symm
  have nUlE : tUl ≠ iT := by
    obtain ⟨k, hk⟩ := hUl.idx₂
    exact (ne_of_F (FXG (e : ℝ) (f : ℝ) ε) hEle (i := k)
      (by rw [hk, FXG_lp hε]; exact lvG_lt he0 hef (by linarith))).symm
  have hβ' := forall_mem3
    (P := fun i => (D.tile i).localAngle (lpG (e : ℝ) (f : ℝ) ε x (a + 1) (η + 1)) = β) aUi aN a3
  have hγ' := forall_mem2
    (P := fun i => (D.tile i).localAngle (lpG (e : ℝ) (f : ℝ) ε x (a + 1) (η + 1)) = γ) a2 hEγ
  have c1 := card_le_angle _ β hβ'
  have c2 := card_le_angle _ γ hγ'
  rw [card3 nUiN nUiDl nNDl] at c1
  rw [card2 nUlE] at c2
  obtain ⟨k0, hk0⟩ := hUr.idx₁
  have F := fig_int S hint hk0
  unfold FigI at F
  omega

/-- the same on the side (`η = 0`): the point `p(a+1, 0)` is a boundary point of Δ that is not a vertex; the figure `{3α, 2β}`, `{α, β, γ}`, `{π}` has at most two tiles
showing `β` and none showing both two `β` and a `γ`.  (Conclusion `False`.) -/
theorem noN_gamma_bdry (S : SetupG D e f α β γ L ax ay) (hε : ε ^ 2 = 1) {a : ℝ} {tUi tN iT : Fin N}
    (hUi : HasV D tUi (lpG (e : ℝ) (f : ℝ) ε x a 0) (lpG (e : ℝ) (f : ℝ) ε x (a + 1) 0)
      (lpG (e : ℝ) (f : ℝ) ε x a (0 + 1)))
    (hN : HasV D tN (lpG (e : ℝ) (f : ℝ) ε x (a + 1) 0) (lpG (e : ℝ) (f : ℝ) ε x a (0 + 1))
      (lpG (e : ℝ) (f : ℝ) ε x (a - nuG (e : ℝ) (f : ℝ)) (0 + 2 + nuG (e : ℝ) (f : ℝ))))
    (hEγ : (D.tile iT).localAngle (lpG (e : ℝ) (f : ℝ) ε x (a + 1) 0) = γ)
    (hfront : lpG (e : ℝ) (f : ℝ) ε x (a + 1) 0 ∈ frontier D.target.carrier ∧
      lpG (e : ℝ) (f : ℝ) ε x (a + 1) 0 ∉ Set.range D.target.pts) : False := by
  have he0 := S.e0
  have hef := S.hef'
  have aUi := (U_anglesG S hε hUi).2.1
  have aN := (N_anglesG S hε hN).1
  have hleN := hN.all (P := fun p => GSG (e : ℝ) (f : ℝ) ε p ≤ -lvG (e : ℝ) (f : ℝ) ε x (a + 0 + 1))
    (GSG_le he0 hef hε (by linarith)) (GSG_le he0 hef hε (by linarith))
    (GSG_le he0 hef hε (by linarith))
  have nUiN : tUi ≠ tN := by
    obtain ⟨k, hk⟩ := hUi.idx₁
    exact (ne_of_F (GSG (e : ℝ) (f : ℝ) ε) hleN (i := k)
      (by rw [hk]; exact GSG_gt he0 hef hε (by linarith))).symm
  have hβ' := forall_mem2
    (P := fun i => (D.tile i).localAngle (lpG (e : ℝ) (f : ℝ) ε x (a + 1) 0) = β) aUi aN
  have hγ' : ∀ i ∈ ({iT} : Finset (Fin N)),
      (D.tile i).localAngle (lpG (e : ℝ) (f : ℝ) ε x (a + 1) 0) = γ := by
    intro i hi
    rw [Finset.mem_singleton.mp hi]; exact hEγ
  have c1 := card_le_angle _ β hβ'
  have c2 := card_le_angle _ γ hγ'
  rw [card2 nUiN] at c1
  rw [Finset.card_singleton] at c2
  have F := fig_bdry S hfront.1 hfront.2
  unfold FigB at F
  omega

/-- **`N_i(j0)` is not a tile** (paper, step (a): "Suppose `S_i = N_i(j0)`. It shows `β` at `p(i+1, j0)`, and the rest of the wedge has the angle `2α`: two tiles showing `α` (F).
Let `E` be the one beside the `b`-edge of `U(i+1, j0)`; it lays `b` or `c` on `ℓ_{i+1}` from `p(i+1, j0)`.  Take the lattice with origin `p(i+1, 0)` ... If `E` lays `c`, then (K1)
holds for it with `j* = j0`, against `K(s − i − 1, j0)`.  If `E` lays `b`, then `E` is the mirror image of `U(i+1, j0)` in `ℓ_{i+1}`, against `M(s − i − 1, j0)`").
`IH m` is `M` for the sizes `m` below the size `s − j0` of the pair.  (Conclusion `False`.) -/
theorem noN_M (S : SetupG D e f α β γ L ax ay) (hε1 : (1 : ℝ) ^ 2 = 1) {s j0 i : ℕ}
    (hK2 : K2G D (e : ℝ) (f : ℝ) 1 x s j0) (hK3 : K3G D (e : ℝ) (f : ℝ) 1 x (s : ℝ) (j0 : ℝ))
    (hsf : s < f) (hne : s - j0 ≤ e) (hi : i + 2 ≤ s - j0)
    (IH : ∀ m, 1 ≤ m → m < s - j0 → MGh D e f 1 m) :
    ∀ tN, HasV D tN (lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) (j0 : ℝ))
      (lpG (e : ℝ) (f : ℝ) 1 x (i : ℝ) ((j0 : ℝ) + 1))
      (lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) - nuG (e : ℝ) (f : ℝ)) ((j0 : ℝ) + 2 + nuG (e : ℝ) (f : ℝ))) →
      False := by
  intro tN hN
  have C : CtxBase D e f α β γ L ax ay 1 x := ⟨S, Or.inl rfl⟩
  have he0 := S.e0
  have hef := S.hef'
  obtain ⟨tUi, hUi⟩ := hK2.1 i j0 le_rfl (by omega)
  obtain ⟨tU2, hU2⟩ := hK2.1 (i + 1) j0 le_rfl (by omega)
  rw [Nat.cast_add, Nat.cast_one] at hU2
  have hch' := chordsAt_shift_K2 S hK2 (n := i + 1) (by omega) (by omega)
  have hs' : s - (i + 1) + (i + 1) = s := by omega
  have hK2' : K2G D (e : ℝ) (f : ℝ) 1 x (s - (i + 1) + (i + 1)) j0 := by rw [hs']; exact hK2
  have hK3' : K3G D (e : ℝ) (f : ℝ) 1 x ((s - (i + 1) + (i + 1) : ℕ) : ℝ) (j0 : ℝ) := by
    rw [hs']; exact hK3
  have hL : lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1 - 1) (j0 : ℝ) ∈ D.target.carrier := by
    rw [show lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1 - 1) (j0 : ℝ) = lpG (e : ℝ) (f : ℝ) 1 x (i : ℝ) (j0 : ℝ)
      from lpG_congr (by ring) rfl]
    exact hUi.mem₁
  have hint := bedge_interior C (Nat.cast_nonneg j0) hU2 hL
  have hcl : ∃ P' : Plane, FXG (e : ℝ) (f : ℝ) 1 P' = lvG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) ∧
      lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) (j0 : ℝ) ∈
        openSegment ℝ P' (lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) ((j0 : ℝ) + 1)) ∧
      ∀ ed ∈ D.lineChain (FXG (e : ℝ) (f : ℝ) 1) (lvG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1)),
        ¬ Straddles ((D.tile ed.1).edge ed.2) P' (lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) (j0 : ℝ))
          (lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) ((j0 : ℝ) + 1)) := by
    rcases Nat.eq_zero_or_pos j0 with hj0 | hj0
    · exact clamp_side S hε1 _ _ (by rw [hj0]; simp)
    · obtain ⟨j', rfl⟩ : ∃ j', j0 = j' + 1 := ⟨j0 - 1, by omega⟩
      obtain ⟨tD, hD⟩ := hK2.2 i j' (by omega) (by omega)
      have hle : ∀ i', FXG (e : ℝ) (f : ℝ) 1 ((D.tile tD).pts i') ≤ lvG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) := by
        refine hD.all (P := fun p => FXG (e : ℝ) (f : ℝ) 1 p ≤ lvG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1))
          (le_of_eq (FXG_lp hε1 _ _)) ?_ (le_of_eq (FXG_lp hε1 _ _))
        dsimp only
        rw [FXG_lp hε1]
        exact lvG_le he0 hef (by linarith)
      obtain ⟨k, m, j₃, hkm, hkj, hmj, hk, hm, hj⟩ := hD
      rw [Nat.cast_add, Nat.cast_one]
      exact clamp_tile S hε1 hkj hk hj hle
  have hE := col_next S hε1 hU2 hint hcl
  have hnγ : ∀ (iT : Fin N) (k m' : Fin 3), k ≠ m' →
      (D.tile iT).pts k = lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) (j0 : ℝ) →
      (D.tile iT).pts m' = lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) ((j0 : ℝ) + 1) →
      (∀ i', FXG (e : ℝ) (f : ℝ) 1 ((D.tile iT).pts i') ≤ lvG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1)) →
      (D.tile iT).localAngle (lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) (j0 : ℝ)) ≠ γ := by
    intro iT k m' hkm hk hm' hle hγ0
    rcases Nat.eq_zero_or_pos j0 with hj0 | hj0
    · -- the point `p(i+1, 0)` is on the side
      subst hj0
      obtain ⟨hx0, hxL, -⟩ := open_shift_K2 S hK2 (n := i + 1) (by omega) (by omega)
      have hfr := S.base_frontier hx0 hxL
      have hpt : mkPt (shiftX (f : ℝ) 1 x (i + 1)) 0 = lpG (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) 0 := by
        unfold lpG shiftX; exact mkPt_congr (by push_cast; ring) (by ring)
      rw [hpt] at hfr
      simp only [Nat.cast_zero] at hUi hN hγ0
      exact noN_gamma_bdry S hε1 hUi hN hγ0 hfr
    · obtain ⟨j', rfl⟩ : ∃ j', j0 = j' + 1 := ⟨j0 - 1, by omega⟩
      obtain ⟨tDL, hDL⟩ := hK2.2 i j' (by omega) (by omega)
      obtain ⟨tUl, hUl⟩ := hK2.1 (i + 1) j' (by omega) (by omega)
      obtain ⟨tDl, hDl⟩ := hK2.2 (i + 1) j' (by omega) (by omega)
      obtain ⟨tUr, hUr⟩ := hK2.1 (i + 1) (j' + 1) le_rfl (by omega)
      simp only [Nat.cast_add, Nat.cast_one] at hUl hDl hUr hUi hN hγ0 hle hk hm'
      exact noN_gamma_int S hε1 hDL hUl hDl hUr hUi hN hle hγ0
  exact beside_contra S (Or.inl rfl) (n := i + 1) (s' := s - (i + 1)) (j := j0)
    (m := s - (i + 1) - j0) (c := (i : ℝ) + 1) (η := (j0 : ℝ)) (by norm_num) rfl hch' hK2' hK3'
    (by omega) (by omega) (IH _ (by omega) (by omega)) rfl (by omega) hE hnγ

/-- **STEP (a)**: `D(i, j0)` is a tile for `0 ≤ i ≤ n − 2` (`n = s − j0`).  (Paper: "As in step (2) of the proof of `K`, the free wedge at `p(i+1, j0)` is `(α, π − β)`.  Let `S_i`
be the tile in it beside the `a`-edge of `U(i, j0)`.  If `S_i` lays `b` or `c` there, the conditions of `M(i+1+j0, j0)` hold ... So `S_i` lays `a` and is `D(i, j0)` or `N_i(j0)`.
Suppose `S_i = N_i(j0)`: ...": `D_ofG` with `hR` from `MGh (i+1)` and `hNo` from `noN_M`.) -/
theorem stepA (S : SetupG D e f α β γ L ax ay) (hch : ChordsAt D (e : ℝ) (f : ℝ) 1 x) {s j0 : ℕ}
    (hM : MirrorAt D (e : ℝ) (f : ℝ) 1 x (j0 : ℝ)) (hK2 : K2G D (e : ℝ) (f : ℝ) 1 x s j0)
    (hK3 : K3G D (e : ℝ) (f : ℝ) 1 x (s : ℝ) (j0 : ℝ)) (hsf : s < f) (hne : s - j0 ≤ e)
    (IH : ∀ m, 1 ≤ m → m < s - j0 → MGh D e f 1 m) :
    ∀ i, i + 2 ≤ s - j0 → DTG D (e : ℝ) (f : ℝ) 1 x i j0 := by
  intro i hi
  have C : CtxBase D e f α β γ L ax ay 1 x := ⟨S, Or.inl rfl⟩
  have hU1 := hK2.1 i j0 le_rfl (by omega)
  have hU2 : UTG D (e : ℝ) (f : ℝ) 1 x ((i : ℝ) + 1) j0 := by
    have h := hK2.1 (i + 1) j0 le_rfl (by omega)
    rwa [Nat.cast_add, Nat.cast_one] at h
  refine C.D_ofG hU1 hU2 ?_ ?_ (noN_M S (by norm_num) hK2 hK3 hsf hne hi IH)
  · rcases Nat.eq_zero_or_pos j0 with hj | hj
    · exact Or.inl hj
    · exact Or.inr ⟨hj, hK2.2 (i + 1) (j0 - 1) (by omega) (by omega)⟩
  · intro w hw
    refine IH (i + 1) (by omega) (by omega) x (i + j0 + 1) j0 hch (by omega) (by omega) (by omega)
      (by omega) hM ⟨fun a b hb hab => hK2.1 a b hb (by omega),
        fun a b hb hab => hK2.2 a b hb (by omega)⟩ ?_
    have e1 : ((i + j0 + 1 : ℕ) : ℝ) = (i : ℝ) + j0 + 1 := by push_cast; ring
    rw [e1]
    exact Or.inr ⟨w, hw⟩

end stepa

end Erdos634.Draft.SideRunGA

#print axioms Erdos634.Draft.SideRunGA.chordsAt_shift_K2
#print axioms Erdos634.Draft.SideRunGA.col_next
#print axioms Erdos634.Draft.SideRunGA.mirror_of_b_n
#print axioms Erdos634.Draft.SideRunGA.beside_core
#print axioms Erdos634.Draft.SideRunGA.beside_contra
#print axioms Erdos634.Draft.SideRunGA.lower_half
#print axioms Erdos634.Draft.SideRunGA.noN_gamma_int
#print axioms Erdos634.Draft.SideRunGA.noN_gamma_bdry
#print axioms Erdos634.Draft.SideRunGA.noN_M
#print axioms Erdos634.Draft.SideRunGA.stepA
