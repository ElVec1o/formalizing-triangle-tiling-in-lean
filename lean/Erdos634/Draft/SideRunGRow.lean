/-
Refactored 14 October 2026: `CtxBase` introduced, lemmas that use only the setup moved to it (no statement changed).
Draft/SideRunGRow.lean -- written 14 October 2026.  UNAUDITED.  In `AllThreshold`.  Module 5 of ten
(part A; Lemma N, `D_ofG`, `noNG` and the checks at `e = 1` are in `Draft/SideRunGRowB.lean`).

The general-member counterpart of `Draft/SideRunRow.lean`: the predicates (K2) and "the claim `K` for all pairs of size `m`",
the tile above a row, and **Lemma Row**, for every coprime `1 ≤ e < f` with the tile `(e f, f² − e², f²)`.  Paper: Theorem
`thm:siderunall`, "Lemma Row" and items (2), (2a)-(2d); (private working notes, not included)

CONTENTS.
* `GSG_le`, `GSG_gt`, `GHG_le`, `GHG_gt` (levels of lattice points), `rep_nat_c`, `dist_rowG`, `run_partition_semigroupG` (the sum-only
  form of the run partition: the length of a clamped run is `x a + y b + z c`).
* `fig_bg`: **the vertex figure of a real dissection, as counting statements.**  At an interior point `v` that is a vertex of a
  tile, (i) at most 4 distinct tiles show `β` or `γ`; (ii) if one tile shows `π` at `v`, at most 2 do; (iii) three distinct
  tiles showing `γ` leave no tile showing `α`.  (From `CornerAnglePerm.congruentDissection_interior_figure_at_corner`, i.e.
  from fact (F): the multiplicities at an interior vertex are `(6,4,0)`, `(4,3,1)`, `(2,2,2)`, `(0,1,3)`, or with one
  straight angle `(3,2,0)`, `(1,1,1)`.)  `interior_of_four`: four tiles with angles summing to more than `π` meet at an
  interior point.
* `K2G`, `AG`: (K2) and "the claim `K(s, j0)` holds for all pairs with `s − j0 = m`" (contradiction between (K2) and `K3G`).
* `CtxG.m_nextGr`: `m_nextG` with a real height that is a natural number.
* `CtxG.row_stepG`, `row_bad0G`, `row_sixG`, `row_badG`, `rowG`: **Lemma Row** and its pieces.

WHAT DIFFERS FROM THE e = 1 TEXT.
(i)   `SideRunRow.row_bad0` and `row_six` close by the inequality `3 α < β` (`Setup.three_alpha_lt_beta`).  That inequality is
      `α < π/9`, i.e. `e/(2f) < sin(π/18)`, i.e. `f/e > 1/(2 sin(π/18)) ≈ 2.88`; it holds for `e = 1`, `f ≥ 3`, and fails for
      members such as `(2,3)`, `(2,5)`, `(3,4)` (for `(2,3)` one even has `β < α`).  Here they close by the counting
      statements `fig_bg` at an interior vertex, i.e. by (F), as the paper does ("the rest of the wedge has the angle `3α` or
      `α` and is filled by tiles showing `α` (F)").  The interior-ness of the vertex is proved from the angle sum
      (`interior_of_four`, `E60Second.interior_of_through_and_vertex`).
(ii)  The edges on a clamped row of length `q c`, `q ≤ f − 1`, are `a`- and `c`-edges by Lemma A5 (`SideRunGArith.A5`), not
      by `y b ≤ q c < f b` (which fails for `(2, 3)`).
(iii) `rowG` uses the paper's bound `q + j ≤ f − 1`; the e = 1 text has the stronger `q + j + 2 ≤ n`, and `m_nextG` needs no
      bound `ξ + 2 ≤ n`.  The claim for the smaller sizes is `AG` (with `K3G`), not `Aprop` (with `K3`).
(iv)  `row_badG` takes the heights as `ζ = j` with `j` a natural number (the lattice points of `m_nextG`).

WITNESSES.  `K2G`, `AG` are predicates on a dissection; there is no standalone witness theorem for them.  `K2G` at `e = 1` is
`K2` (`K2G_one_iff`, part B).  `AG` at `e = 1` is implied by `Aprop` (`AG_of_Aprop_e1`, part B).  Every lemma here is stated
under `CtxG` (see `Draft/SideRunGChord.lean`: satisfied at `e = 1` by every `Ctx`; NO `CtxG` for `e ≥ 2` exists yet).  `rowG`
has the hypothesis `AG` for the sizes `< q` (an inductive hypothesis; vacuous for `q = 1`).  `row_bad0G`, `row_sixG`,
`row_badG` conclude `False` (contradiction engines of the proof, like `SideRun.Ctx.row_bad`); their value is in `rowG`.

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGChordB
import Erdos634.Draft.SideRunRow
import Erdos634.Draft.E60Second

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

/-! ## 1. Levels of lattice points, and small arithmetic -/

theorem GSG_le {e f ε x a b s : ℝ} (he : 0 < e) (hef : e < f) (hε : ε ^ 2 = 1) (h : s ≤ a + b) :
    GSG e f ε (lpG e f ε x a b) ≤ -lvG e f ε x s := by
  rw [GSG_lp hε]; exact neg_le_neg (lvG_le he hef h)

theorem GSG_gt {e f ε x a b s : ℝ} (he : 0 < e) (hef : e < f) (hε : ε ^ 2 = 1) (h : a + b < s) :
    -lvG e f ε x s < GSG e f ε (lpG e f ε x a b) := by
  rw [GSG_lp hε]; exact neg_lt_neg (lvG_lt he hef h)

theorem GHG_le {e f ε x a b η : ℝ} (he : 0 < e) (hef : e < f) (h : η ≤ b) :
    GHG f (lpG e f ε x a b) ≤ -(f ^ 2 * hhG e f * η) := by
  rw [GHG_lp]; exact neg_le_neg (mul_le_mul_of_nonneg_left h (nhG_pos he hef).le)

theorem GHG_gt {e f ε x a b η : ℝ} (he : 0 < e) (hef : e < f) (h : b < η) :
    -(f ^ 2 * hhG e f * η) < GHG f (lpG e f ε x a b) := by
  rw [GHG_lp]; exact neg_lt_neg (mul_lt_mul_of_pos_left h (nhG_pos he hef))

/-- a real partition equation with the right side `j c` is the natural number equation of `A5` -/
theorem rep_nat_c {e f j x y z : ℕ} (hef : e < f)
    (h : (x : ℝ) * ((e : ℝ) * f) + y * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z * (f : ℝ) ^ 2
      = (j : ℝ) * (f : ℝ) ^ 2) :
    x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = j * f ^ 2 := by
  obtain ⟨b, hbN, hbR⟩ := exists_bR hef
  rw [hbN]
  rw [← hbR] at h
  exact_mod_cast h

/-- the distance along a row -/
theorem dist_rowG {e f ε x : ℝ} (he : 0 < e) (hef : e < f) (hε : ε ^ 2 = 1) {a b η : ℝ} (hab : a ≤ b) :
    dist (lpG e f ε x a η) (lpG e f ε x b η) = (b - a) * f ^ 2 :=
  dist_lpG he hef hε (mul_nonneg (sub_nonneg.mpr hab) (by have := he.trans hef; positivity))
    (by unfold QfG; ring)

/-- **The run partition, arithmetic form**: for a `CongruentDissection` with the tile `(e f, f² − e², f²)`, a clamped run's
length is a nonnegative integer combination of the three sides (the generalization of `RunPartition.run_partition_semigroup`;
`wall_partitionG`, `Draft/SideRunGChordB.lean`, gives the same with a prescribed edge singled out). -/
theorem run_partition_semigroupG {N : ℕ} (D : CongruentDissection N) {e f α β γ : ℝ}
    (hM : ModelDataG D e f α β γ) (F : Plane →ₗ[ℝ] ℝ) (hF : F ≠ 0) (c : ℝ)
    {P Q P' Q' : Plane} (hPQ : P ≠ Q) (hfP' : F P' = c) (hfQ' : F Q' = c)
    (hP' : P ∈ openSegment ℝ P' Q) (hQ' : Q ∈ openSegment ℝ P Q')
    (hS : segment ℝ P Q ⊆ {y | F y = c})
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier)
    (hP : ∀ ed ∈ D.lineChain F c, ¬ Straddles ((D.tile ed.1).edge ed.2) P' P Q)
    (hQ : ∀ ed ∈ D.lineChain F c, ¬ Straddles ((D.tile ed.1).edge ed.2) Q' Q P) :
    ∃ x y z : ℕ, (x : ℝ) * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = dist P Q := by
  classical
  have h := run_partition D.toDissection F hF c hPQ hfP' hfQ' hP' hQ' hS hint hwall hP hQ
  rw [← h]
  exact sum_mem_semigroup _ _ (e * f) (f ^ 2 - e ^ 2) (f ^ 2)
    (fun ed _ => edge_length_casesG D hM ed.1 ed.2)

/-! ## 2. The vertex figure as counting statements -/

section figure

variable {e f α β γ : ℝ}

/-- **The figure at an interior vertex.**  Let `v` be an interior point of the target that is a vertex of some tile.
(i) At most 4 distinct tiles show `β` or `γ` at `v`.  (ii) If a tile shows `π` at `v`, at most 2 distinct tiles show `β` or `γ`.
(iii) If three distinct tiles show `γ`, no tile shows `α`. -/
theorem fig_bg (D : CongruentDissection N) (hM : ModelDataG D e f α β γ) (hA : AngleData α β γ)
    {v : Plane} (hv : v ∈ interior D.target.carrier) {j : Fin N} {m : Fin 3}
    (hjm : (D.tile j).pts m = v) :
    (∀ l : List (Fin N), l.Nodup →
      (∀ i ∈ l, (D.tile i).localAngle v = β ∨ (D.tile i).localAngle v = γ) → l.length ≤ 4) ∧
    ((∃ φ : Fin N, (D.tile φ).localAngle v = Real.pi) → ∀ l : List (Fin N), l.Nodup →
      (∀ i ∈ l, (D.tile i).localAngle v = β ∨ (D.tile i).localAngle v = γ) → l.length ≤ 2) ∧
    (∀ l : List (Fin N), l.Nodup → (∀ i ∈ l, (D.tile i).localAngle v = γ) → 3 ≤ l.length →
      ∀ i : Fin N, (D.tile i).localAngle v ≠ α) := by
  classical
  obtain ⟨hαβ, hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hγπ, hγ0, hπ0⟩ :=
    distinct_of_pos_ne hA.hα hA.hβ hA.hαβ hA.hγdef hA.hrel
  obtain ⟨-, -, -, -, hγlt⟩ := angle_facts hA
  have hpi := Real.pi_pos
  have hrel := hA.hrel
  have hα2π : α ≠ 2 * Real.pi := by intro h; linarith [hA.hβ]
  have hβ2π : β ≠ 2 * Real.pi := by intro h; linarith [hA.hα]
  have hγ2π : γ ≠ 2 * Real.pi := by intro h; linarith
  have hπ2π : Real.pi ≠ 2 * Real.pi := by intro h; linarith
  have h2π0 : 2 * Real.pi ≠ 0 := by positivity
  have fig := congruentDissection_interior_figure_at_corner D α β γ hαβ hαγ hαπ hα2π hα0 hβγ hβπ
    hβ2π hβ0 hγπ hγ2π hγ0 hπ2π hπ0 h2π0 hM.hα' hM.hβ' hM.hγ' hA.hγdef hA.hrel hA.hirr hv j m hjm
  have key : ∀ (P : Fin N → Prop) [DecidablePred P] (l : List (Fin N)), l.Nodup → (∀ i ∈ l, P i) →
      l.length ≤ (Finset.univ.filter P).card := by
    intro P _ l hl hP
    rw [← List.toFinset_card_of_nodup hl]
    exact Finset.card_le_card (fun i hi => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hP i (List.mem_toFinset.mp hi))
  have hbg : ∀ l : List (Fin N), l.Nodup →
      (∀ i ∈ l, (D.tile i).localAngle v = β ∨ (D.tile i).localAngle v = γ) →
      l.length ≤ ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card
        + ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card := by
    intro l hl h
    have h1 := key (fun i => (D.tile i).localAngle v = β ∨ (D.tile i).localAngle v = γ) l hl h
    have h2 : (Finset.univ.filter
        (fun i => (D.tile i).localAngle v = β ∨ (D.tile i).localAngle v = γ)).card
        ≤ ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card
          + ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card := by
      rw [Finset.filter_or]
      exact Finset.card_union_le _ _
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro l hl h
    have := hbg l hl h
    rcases fig with ⟨-, hc⟩ | ⟨-, hc⟩
    · rcases hc with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> omega
    · rcases hc with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> omega
  · rintro ⟨φ, hφ⟩ l hl h
    have := hbg l hl h
    have hπpos : 0 < ({i | (D.tile i).localAngle v = Real.pi} : Finset (Fin N)).card :=
      Finset.card_pos.mpr ⟨φ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hφ⟩⟩
    rcases fig with ⟨hπ1, hc⟩ | ⟨hπ0', hc⟩
    · rcases hc with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> omega
    · omega
  · intro l hl h hlen i hi
    have h3 : 3 ≤ ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card :=
      le_trans hlen (key (fun i => (D.tile i).localAngle v = γ) l hl h)
    have hαpos : 0 < ({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card :=
      Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    rcases fig with ⟨-, hc⟩ | ⟨-, hc⟩
    · rcases hc with ⟨h1, h2, h4⟩ | ⟨h1, h2, h4⟩ <;> omega
    · rcases hc with ⟨h1, h2, h4⟩ | ⟨h1, h2, h4⟩ | ⟨h1, h2, h4⟩ | ⟨h1, h2, h4⟩ <;> omega

end figure

/-- four tiles whose angles at `p` sum to more than `π`: `p` is interior to the target -/
theorem interior_of_four (D : CongruentDissection N) {p : Plane} {i j k l : Fin N}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (h : Real.pi < (D.tile i).localAngle p + (D.tile j).localAngle p + (D.tile k).localAngle p
      + (D.tile l).localAngle p) : p ∈ interior D.target.carrier :=
  Erdos634.Draft.E60Second.interior_of_sum_gt_pi D.toDissection (by
    rw [D.toDissection.sum_localAngle_eq p]
    exact lt_of_lt_of_le h (four_angles_le D.toDissection p hij hik hil hjk hjl hkl))

/-! ## 3. (K2) and the claim `K` for all pairs of a given size -/

/-- **(K2)**: the rows `≤ j0` of `Δ_s` are lattice -/
def K2G (D : CongruentDissection N) (e f ε x : ℝ) (s j0 : ℕ) : Prop :=
  (∀ i j : ℕ, j ≤ j0 → i + j + 1 ≤ s → UTG D e f ε x i j) ∧
  (∀ i j : ℕ, j < j0 → i + j + 2 ≤ s → DTG D e f ε x i j)

/-- **The claim `K(s, j0)` for all pairs of size `m`**: (K2) and (K3) (in the general form `K3G`) are contradictory.  (K1) is in
`CtxG`. -/
def AG (D : CongruentDissection N) (e f : ℕ) (ε x : ℝ) (m : ℕ) : Prop :=
  ∀ s j0 : ℕ, j0 < s → s < f → s - j0 = m → K2G D (e : ℝ) (f : ℝ) ε x s j0 →
    K3G D (e : ℝ) (f : ℝ) ε x (s : ℝ) (j0 : ℝ) → False

/-! ## 4. The tile above a row -/

namespace CtxBase

variable {e f : ℕ} {α β γ L ax ay ε x : ℝ}

/-- `m_nextG` at a real height that is a natural number -/
theorem m_nextGr (C : CtxBase D e f α β γ L ax ay ε x) {ξ η : ℝ} (hη : ∃ n : ℕ, η = n) {t₀ : Fin N}
    (hU : HasV D t₀ (lpG (e : ℝ) (f : ℝ) ε x ξ η) (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η) (lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1)))
    (hFw : ∃ δ : ℝ, 0 < δ ∧ lpG (e : ℝ) (f : ℝ) ε x (ξ + 1 + δ) η ∈ D.target.carrier)
    (hcl : ClampedBelowG D (e : ℝ) (f : ℝ) ε x (ξ + η + 1) η) :
    (∃ t, HasV D t (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η) (lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1)) (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) (η + 1))) ∨
    (∃ t, HasV D t (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η) (lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1))
      (lpG (e : ℝ) (f : ℝ) ε x (ξ - nuG (e : ℝ) (f : ℝ)) (η + 2 + nuG (e : ℝ) (f : ℝ)))) ∨
    (∃ w, RhoEdgeG D (e : ℝ) (f : ℝ) ε x w (ξ + η + 1) η) := by
  obtain ⟨n, rfl⟩ := hη
  exact C.m_nextG hU hFw hcl

/-- **The tile above a row** at `p(ρ, ζ+1)`, next to the `c`-edge of `D(ρ, ζ)`: it is `U(ρ, ζ+1)`, or it shows `β` or `γ` at
`p(ρ, ζ+1)` and has no vertex at `p(ρ−1, ζ+2)`. -/
theorem row_stepG (C : CtxBase D e f α β γ L ax ay ε x) {ρ ζ : ℝ} {tD : Fin N}
    (hDt : HasV D tD (lpG (e : ℝ) (f : ℝ) ε x (ρ + 1) ζ) (lpG (e : ℝ) (f : ℝ) ε x ρ (ζ + 1)) (lpG (e : ℝ) (f : ℝ) ε x (ρ + 1) (ζ + 1)))
    (hζ : 0 ≤ ζ)
    (hcl : ∃ P' : Plane, GHG (f : ℝ) P' = -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * (ζ + 1)) ∧
      lpG (e : ℝ) (f : ℝ) ε x ρ (ζ + 1) ∈ openSegment ℝ P' (lpG (e : ℝ) (f : ℝ) ε x (ρ + 1) (ζ + 1)) ∧
      ∀ ed ∈ D.lineChain (GHG (f : ℝ)) (-(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * (ζ + 1))),
        ¬ Straddles ((D.tile ed.1).edge ed.2) P' (lpG (e : ℝ) (f : ℝ) ε x ρ (ζ + 1)) (lpG (e : ℝ) (f : ℝ) ε x (ρ + 1) (ζ + 1)))
    (hnob : ∀ ed ∈ D.lineChain (GHG (f : ℝ)) (-(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * (ζ + 1))),
      (D.tile ed.1).edge ed.2 ⊆ segment ℝ (lpG (e : ℝ) (f : ℝ) ε x ρ (ζ + 1)) (lpG (e : ℝ) (f : ℝ) ε x (ρ + 1) (ζ + 1)) →
      dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1)) ≠ (f : ℝ) ^ 2 - (e : ℝ) ^ 2) :
    UTG D (e : ℝ) (f : ℝ) ε x ρ (ζ + 1) ∨
    ∃ (ix : Fin N) (k m j₃ : Fin 3) (t : ℝ), k ≠ m ∧ k ≠ j₃ ∧ m ≠ j₃ ∧
      (D.tile ix).pts k = lpG (e : ℝ) (f : ℝ) ε x ρ (ζ + 1) ∧ 0 < t ∧ (D.tile ix).pts m = lpG (e : ℝ) (f : ℝ) ε x (ρ + t) (ζ + 1) ∧
      (∀ i, GHG (f : ℝ) ((D.tile ix).pts i) ≤ -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * (ζ + 1))) ∧
      ((D.tile ix).localAngle (lpG (e : ℝ) (f : ℝ) ε x ρ (ζ + 1)) = β ∨ (D.tile ix).localAngle (lpG (e : ℝ) (f : ℝ) ε x ρ (ζ + 1)) = γ) ∧
      (∀ i, (D.tile ix).pts i = lpG (e : ℝ) (f : ℝ) ε x (ρ - 1) (ζ + 1 + 1) → False) := by
  have S := C.S
  have hε := C.e2
  have he0 := S.e0
  have hef := S.hef'
  have hf0 := S.f0
  have hc := S.c_pos
  have hVW : lpG (e : ℝ) (f : ℝ) ε x ρ (ζ + 1) ≠ lpG (e : ℝ) (f : ℝ) ε x (ρ + 1) (ζ + 1) := lpG_ne_xi he0 hef hε (by linarith)
  have hfV : GHG (f : ℝ) (lpG (e : ℝ) (f : ℝ) ε x ρ (ζ + 1)) = -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * (ζ + 1)) := GHG_lp _ _ _ _ _ _
  have hfW : GHG (f : ℝ) (lpG (e : ℝ) (f : ℝ) ε x (ρ + 1) (ζ + 1)) = -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * (ζ + 1)) := GHG_lp _ _ _ _ _ _
  have hint : openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x ρ (ζ + 1)) (lpG (e : ℝ) (f : ℝ) ε x (ρ + 1) (ζ + 1)) ⊆ interior D.target.carrier := by
    refine C.seg_intG hDt.mem₂ hDt.mem₃ (Or.inl (by linarith)) (Or.inl ⟨1, one_pos, hDt.mem₃⟩)
      (Or.inr ⟨1, one_pos, ?_⟩)
    rw [show ρ + 1 - 1 = ρ by ring]; exact hDt.mem₂
  have hwall : ∀ y ∈ openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x ρ (ζ + 1)) (lpG (e : ℝ) (f : ℝ) ε x (ρ + 1) (ζ + 1)),
      ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := hDt
    refine seg_wall D.toDissection (t := tD) hmj ?_
    rw [hm, hj]; exact openSegment_subset_segment ℝ _ _ hy
  obtain ⟨P', hfP', hP', hP⟩ := hcl
  obtain ⟨ed, he, k, m, t, hkm, hk, ht, hm0, hle, hedge, hdist⟩ :=
    next_tile D.toDissection (GHG (f : ℝ)) (GHG_ne he0 hef) _ hVW hfV hfW hfP' hP' hint hwall hP
  have hm : (D.tile ed.1).pts m = lpG (e : ℝ) (f : ℝ) ε x (ρ + t) (ζ + 1) := by
    rw [hm0, lineMap_lpG]; exact lpG_congr (by ring) (by ring)
  have hd : dist ((D.tile ed.1).pts k) ((D.tile ed.1).pts m) = t * (f : ℝ) ^ 2 := by
    rw [hk, hm]
    exact dist_lpG he0 hef hε (by positivity) (by unfold QfG; ring)
  have hlam := vertex_dist_casesG D S.hM ed.1 hkm
  have hea : (e : ℝ) * (f : ℝ) < (f : ℝ) ^ 2 := by nlinarith [mul_pos hf0 (sub_pos.mpr hef)]
  have heb : (f : ℝ) ^ 2 - (e : ℝ) ^ 2 < (f : ℝ) ^ 2 := by nlinarith [mul_pos he0 he0]
  have ht1 : t ≤ 1 := by
    by_contra hgt
    rw [not_le] at hgt
    have h1 : (f : ℝ) ^ 2 < t * (f : ℝ) ^ 2 := by nlinarith [mul_pos (sub_pos.mpr hgt) hc]
    rcases hlam with h | h | h <;> rw [hd] at h <;> linarith
  have hsub : (D.tile ed.1).edge ed.2
      ⊆ segment ℝ (lpG (e : ℝ) (f : ℝ) ε x ρ (ζ + 1)) (lpG (e : ℝ) (f : ℝ) ε x (ρ + 1) (ζ + 1)) := by
    rw [hedge]
    refine (convex_segment _ _).segment_subset (left_mem_segment ℝ _ _) ?_
    rw [segment_eq_image_lineMap]
    exact ⟨t, ⟨ht.le, ht1⟩, rfl⟩
  have hlamb : dist ((D.tile ed.1).pts k) ((D.tile ed.1).pts m) ≠ (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have h1 := hnob ed he hsub
    rw [hdist] at h1
    rw [hk, hm0]; exact h1
  obtain ⟨j₃, hjk, hjm⟩ := fin3_third k m hkm
  have hkj : k ≠ j₃ := Ne.symm hjk
  have hmj : m ≠ j₃ := Ne.symm hjm
  have hGV : dist (lpG (e : ℝ) (f : ℝ) ε x (ρ - 1) (ζ + 1 + 1)) (lpG (e : ℝ) (f : ℝ) ε x ρ (ζ + 1)) = (e : ℝ) * (f : ℝ) :=
    dist_lpG he0 hef hε (mul_pos he0 hf0).le (by unfold QfG; ring)
  have hGW : dist (lpG (e : ℝ) (f : ℝ) ε x (ρ - 1) (ζ + 1 + 1)) (lpG (e : ℝ) (f : ℝ) ε x (ρ + 1) (ζ + 1)) ^ 2
      = (f : ℝ) ^ 4 + 4 * (f : ℝ) ^ 2 * (e : ℝ) ^ 2 - (e : ℝ) ^ 4 := by
    rw [dist_lpG_sq he0 hef hε]; unfold QfG; ring
  have hA := angle_at_vertexG D S.tile S.hM ed.1 hkm hkj hmj
  rw [hk] at hA
  have hno_km : ∀ i, i = k ∨ i = m → (D.tile ed.1).pts i = lpG (e : ℝ) (f : ℝ) ε x (ρ - 1) (ζ + 1 + 1) → False := by
    intro i hi hpi
    rcases hi with rfl | rfl
    · rw [hk] at hpi
      have := lpG_eta_eq he0 hef hpi
      linarith
    · rw [hm] at hpi
      have := lpG_eta_eq he0 hef hpi
      linarith
  rcases hlam with h | h | h
  · -- an `a`-edge
    right
    rcases sides_of_a_edgeG D S.tile S.hM ed.1 hkm hkj hmj h with ⟨s1, s2⟩ | ⟨s1, s2⟩
    · refine ⟨ed.1, k, m, j₃, t, hkm, hkj, hmj, hk, ht, hm, hle,
        Or.inl (hA.2.1 (by rw [dist_comm]; exact s2)), fun i hpi => ?_⟩
      rcases fin3_cover k m j₃ hkm hkj hmj i with hi | hi | hi
      · exact hno_km i (Or.inl hi) hpi
      · exact hno_km i (Or.inr hi) hpi
      · rw [hi] at hpi
        rw [hpi, hk, hGV] at s1
        exact S.tile.ac s1
    · refine ⟨ed.1, k, m, j₃, t, hkm, hkj, hmj, hk, ht, hm, hle,
        Or.inr (hA.2.2 (by rw [dist_comm]; exact s2)), fun i hpi => ?_⟩
      rcases fin3_cover k m j₃ hkm hkj hmj i with hi | hi | hi
      · exact hno_km i (Or.inl hi) hpi
      · exact hno_km i (Or.inr hi) hpi
      · rw [hi] at hpi
        rw [hpi, hk, hGV] at s1
        exact S.tile.hab s1
  · exact absurd h hlamb
  · -- a `c`-edge
    have ht1' : t = 1 := by
      have h1 : t * (f : ℝ) ^ 2 = 1 * (f : ℝ) ^ 2 := by rw [one_mul, ← hd, h]
      exact mul_right_cancel₀ hc.ne' h1
    have hmW : (D.tile ed.1).pts m = lpG (e : ℝ) (f : ℝ) ε x (ρ + 1) (ζ + 1) := by rw [hm, ht1']
    rcases sides_of_c_edgeG D S.tile S.hM ed.1 hkm hkj hmj h with ⟨s1, s2⟩ | ⟨s1, s2⟩
    · right
      refine ⟨ed.1, k, m, j₃, t, hkm, hkj, hmj, hk, ht, hm, hle,
        Or.inl (hA.2.1 (by rw [dist_comm]; exact s2)), fun i hpi => ?_⟩
      rcases fin3_cover k m j₃ hkm hkj hmj i with hi | hi | hi
      · exact hno_km i (Or.inl hi) hpi
      · exact hno_km i (Or.inr hi) hpi
      · rw [hi] at hpi
        rw [hpi, hmW] at s2
        rw [s2] at hGW
        have h3 : (e : ℝ) ^ 2 * ((e : ℝ) ^ 2 - 3 * (f : ℝ) ^ 2) = 0 := by linear_combination (1 / 2 : ℝ) * hGW
        have h4 : (e : ℝ) ^ 2 - 3 * (f : ℝ) ^ 2 = 0 :=
          (mul_eq_zero.mp h3).resolve_left (pow_pos he0 2).ne'
        nlinarith [mul_pos (sub_pos.mpr hef) (add_pos he0 hf0), mul_pos hf0 hf0]
    · left
      exact ⟨ed.1, row_edge_UG S hε hkm hkj hmj hk hmW hle s1 s2⟩

/-- **The tile above the row at `p(0, ζ+1)` shows less than `β` or `γ`**: the tiles `φ` (straight), `U(0,ζ)` (`γ`), `D(0,ζ)`
(`β`) and a fourth showing `β` or `γ` cannot meet at an interior vertex (`fig_bg`). -/
theorem row_bad0G (C : CtxBase D e f α β γ L ax ay ε x) {ζ : ℝ} {φ tU tD ix : Fin N}
    (hφπ : (D.tile φ).localAngle (lpG (e : ℝ) (f : ℝ) ε x 0 (ζ + 1)) = Real.pi)
    (hU : HasV D tU (lpG (e : ℝ) (f : ℝ) ε x 0 ζ) (lpG (e : ℝ) (f : ℝ) ε x (0 + 1) ζ) (lpG (e : ℝ) (f : ℝ) ε x 0 (ζ + 1)))
    (hDt : HasV D tD (lpG (e : ℝ) (f : ℝ) ε x (0 + 1) ζ) (lpG (e : ℝ) (f : ℝ) ε x 0 (ζ + 1)) (lpG (e : ℝ) (f : ℝ) ε x (0 + 1) (ζ + 1)))
    (hle : ∀ i, GHG (f : ℝ) ((D.tile ix).pts i) ≤ -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * (ζ + 1)))
    (hθ : (D.tile ix).localAngle (lpG (e : ℝ) (f : ℝ) ε x 0 (ζ + 1)) = β ∨
      (D.tile ix).localAngle (lpG (e : ℝ) (f : ℝ) ε x 0 (ζ + 1)) = γ) : False := by
  have S := C.S
  have hε := C.e2
  have he0 := S.e0
  have hef := S.hef'
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hγdef := S.hA.hγdef
  have hβπ : β < Real.pi := by linarith
  have hβγ : β < γ := by linarith
  have hUγ := (U_anglesG S hε hU).2.2
  have hDβ := (D_anglesG S hε hDt).2.1
  have hφU : φ ≠ tU := ne_of_angle (by rw [hφπ, hUγ]; exact hγπ.ne')
  have hφD : φ ≠ tD := ne_of_angle (by rw [hφπ, hDβ]; exact hβπ.ne')
  have hUD : tU ≠ tD := ne_of_angle (by rw [hUγ, hDβ]; exact hβγ.ne')
  have hxU : ix ≠ tU := by
    obtain ⟨k, hk⟩ := hU.idx₁
    exact ne_of_F (GHG (f : ℝ)) hle (i := k) (by rw [hk]; exact GHG_gt he0 hef (by linarith))
  have hxD : ix ≠ tD := by
    obtain ⟨k, hk⟩ := hDt.idx₁
    exact ne_of_F (GHG (f : ℝ)) hle (i := k) (by rw [hk]; exact GHG_gt he0 hef (by linarith))
  have hint0 : lpG (e : ℝ) (f : ℝ) ε x 0 (ζ + 1) ∈ interior D.target.carrier :=
    Erdos634.Draft.E60Second.interior_of_through_and_vertex D.toDissection hφU hφπ
      (by rw [hUγ]; linarith)
  obtain ⟨m3, hm3⟩ := hU.idx₃
  have hfig := fig_bg D S.hM S.hA hint0 hm3
  have hnd : [tU, tD, ix].Nodup := by
    simp [hUD, Ne.symm hxU, Ne.symm hxD]
  have hall : ∀ i ∈ [tU, tD, ix],
      (D.tile i).localAngle (lpG (e : ℝ) (f : ℝ) ε x 0 (ζ + 1)) = β ∨ (D.tile i).localAngle (lpG (e : ℝ) (f : ℝ) ε x 0 (ζ + 1)) = γ := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact Or.inr hUγ
    · exact Or.inl hDβ
    · exact hθ
  have h3 := hfig.2.1 ⟨φ, hφπ⟩ [tU, tD, ix] hnd hall
  simp at h3

/-- **Six tiles at `p(ξ+1, ζ+1)`**: `D(ξ,ζ)` (`α`), `U(ξ+1,ζ)` (`γ`), `D(ξ+1,ζ)` (`β`), `U(ξ,ζ+1)` (`β`), the tile above the
row and the tile across the `a`-edge of `U(ξ,ζ+1)`, the last two showing `β` or `γ`: five tiles showing `β` or `γ` at an
interior vertex, against `fig_bg`. -/
theorem row_sixG (C : CtxBase D e f α β γ L ax ay ε x) {ξ ζ : ℝ}
    {t₁ t₂ t₃ t₄ ix t₆ : Fin N}
    (h1 : HasV D t₁ (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) ζ) (lpG (e : ℝ) (f : ℝ) ε x ξ (ζ + 1)) (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) (ζ + 1)))
    (h2 : HasV D t₂ (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) ζ) (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1 + 1) ζ) (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) (ζ + 1)))
    (h3 : HasV D t₃ (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1 + 1) ζ) (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) (ζ + 1)) (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1 + 1) (ζ + 1)))
    (h4 : HasV D t₄ (lpG (e : ℝ) (f : ℝ) ε x ξ (ζ + 1)) (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) (ζ + 1)) (lpG (e : ℝ) (f : ℝ) ε x ξ (ζ + 1 + 1)))
    {m : Fin 3} {t : ℝ} (ht : 0 < t) (hm : (D.tile ix).pts m = lpG (e : ℝ) (f : ℝ) ε x (ξ + 1 + t) (ζ + 1))
    (hle : ∀ i, GHG (f : ℝ) ((D.tile ix).pts i) ≤ -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * (ζ + 1)))
    (hθ : (D.tile ix).localAngle (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) (ζ + 1)) = β ∨
      (D.tile ix).localAngle (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) (ζ + 1)) = γ)
    (hno : ∀ i, (D.tile ix).pts i = lpG (e : ℝ) (f : ℝ) ε x ξ (ζ + 1 + 1) → False) {X : Plane}
    (h6 : HasV D t₆ (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) (ζ + 1)) (lpG (e : ℝ) (f : ℝ) ε x ξ (ζ + 1 + 1)) X)
    (hθ' : (D.tile t₆).localAngle (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) (ζ + 1)) = β ∨
      (D.tile t₆).localAngle (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) (ζ + 1)) = γ)
    (hle6 : ∀ i, GSG (e : ℝ) (f : ℝ) ε ((D.tile t₆).pts i) ≤ -lvG (e : ℝ) (f : ℝ) ε x (ξ + (ζ + 1) + 1)) : False := by
  have S := C.S
  have hε := C.e2
  have he0 := S.e0
  have hef := S.hef'
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hγdef := S.hA.hγdef
  have hβγ : β < γ := by linarith
  have hαγ : α < γ := by linarith
  have hαβ : α ≠ β := S.hA.hαβ
  have a1 := (D_anglesG S hε h1).2.2
  have a2 := (U_anglesG S hε h2).2.2
  have a3 := (D_anglesG S hε h3).2.1
  have a4 := (U_anglesG S hε h4).2.1
  have n12 : t₁ ≠ t₂ := ne_of_angle (by rw [a1, a2]; exact hαγ.ne)
  have n13 : t₁ ≠ t₃ := ne_of_angle (by rw [a1, a3]; exact hαβ)
  have n14 : t₁ ≠ t₄ := ne_of_angle (by rw [a1, a4]; exact hαβ)
  have n23 : t₂ ≠ t₃ := ne_of_angle (by rw [a2, a3]; exact hβγ.ne')
  have n24 : t₂ ≠ t₄ := ne_of_angle (by rw [a2, a4]; exact hβγ.ne')
  have n25 : t₂ ≠ ix := by
    obtain ⟨k, hk⟩ := h2.idx₁
    exact (ne_of_F (GHG (f : ℝ)) hle (i := k) (by rw [hk]; exact GHG_gt he0 hef (by linarith))).symm
  have n26 : t₂ ≠ t₆ := by
    obtain ⟨k, hk⟩ := h2.idx₁
    exact (ne_of_F (GSG (e : ℝ) (f : ℝ) ε) hle6 (i := k)
      (by rw [hk]; exact GSG_gt he0 hef hε (by linarith))).symm
  have hle3 := h3.all (P := fun p => GSG (e : ℝ) (f : ℝ) ε p ≤ -lvG (e : ℝ) (f : ℝ) ε x (ξ + (ζ + 1) + 1))
    (GSG_le he0 hef hε (by linarith)) (GSG_le he0 hef hε (by linarith))
    (GSG_le he0 hef hε (by linarith))
  have n34 : t₃ ≠ t₄ := by
    obtain ⟨k, hk⟩ := h4.idx₁
    exact ne_of_F (GSG (e : ℝ) (f : ℝ) ε) hle3 (i := k) (by rw [hk]; exact GSG_gt he0 hef hε (by linarith))
  have n35 : t₃ ≠ ix := by
    obtain ⟨k, hk⟩ := h3.idx₁
    exact (ne_of_F (GHG (f : ℝ)) hle (i := k) (by rw [hk]; exact GHG_gt he0 hef (by linarith))).symm
  have n36 : t₃ ≠ t₆ := by
    obtain ⟨k, hk⟩ := h6.idx₂
    exact (h3.ne_of_vertex hk (lpG_ne_eta he0 hef (by linarith)) (lpG_ne_eta he0 hef (by linarith))
      (lpG_ne_eta he0 hef (by linarith))).symm
  have n45 : t₄ ≠ ix :=
    (h4.ne_of_vertex hm (lpG_ne_xi he0 hef hε (by linarith)) (lpG_ne_xi he0 hef hε (by linarith))
      (lpG_ne_eta he0 hef (by linarith))).symm
  have n46 : t₄ ≠ t₆ := by
    obtain ⟨k, hk⟩ := h4.idx₁
    exact (ne_of_F (GSG (e : ℝ) (f : ℝ) ε) hle6 (i := k)
      (by rw [hk]; exact GSG_gt he0 hef hε (by linarith))).symm
  have n56 : ix ≠ t₆ := by
    rintro rfl
    obtain ⟨k, hk⟩ := h6.idx₂
    exact hno k hk
  have hint : lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) (ζ + 1) ∈ interior D.target.carrier :=
    interior_of_four D n12 n13 n14 n23 n24 n34 (by rw [a1, a2, a3, a4]; linarith)
  obtain ⟨m1, hm1⟩ := h1.idx₃
  have hfig := fig_bg D S.hM S.hA hint hm1
  have hnd : [t₂, t₃, t₄, ix, t₆].Nodup := by
    simp [n23, n24, n25, n26, n34, n35, n36, n45, n46, n56]
  have hall : ∀ i ∈ [t₂, t₃, t₄, ix, t₆], (D.tile i).localAngle (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) (ζ + 1)) = β ∨
      (D.tile i).localAngle (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) (ζ + 1)) = γ := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · exact Or.inr a2
    · exact Or.inl a3
    · exact Or.inl a4
    · exact hθ
    · exact hθ'
  have h5 := hfig.1 [t₂, t₃, t₄, ix, t₆] hnd hall
  simp at h5

/-- **The tile above the row at `p(ξ+1, ζ+1)` shows less than `β`** if no tile gives (K3) for the run `(ξ+ζ+2, ζ+1)`; here
`ζ` is a natural number. -/
theorem row_badG (C : CtxBase D e f α β γ L ax ay ε x) {ξ : ℝ} {j : ℕ}
    {t₁ t₂ t₃ t₄ ix : Fin N}
    (h1 : HasV D t₁ (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) j) (lpG (e : ℝ) (f : ℝ) ε x ξ ((j : ℝ) + 1)) (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) ((j : ℝ) + 1)))
    (h2 : HasV D t₂ (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) j) (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1 + 1) j) (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) ((j : ℝ) + 1)))
    (h3 : HasV D t₃ (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1 + 1) j) (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) ((j : ℝ) + 1))
      (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1 + 1) ((j : ℝ) + 1)))
    (h4 : HasV D t₄ (lpG (e : ℝ) (f : ℝ) ε x ξ ((j : ℝ) + 1)) (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) ((j : ℝ) + 1)) (lpG (e : ℝ) (f : ℝ) ε x ξ ((j : ℝ) + 1 + 1)))
    {m : Fin 3} {t : ℝ} (ht : 0 < t)
    (hm : (D.tile ix).pts m = lpG (e : ℝ) (f : ℝ) ε x (ξ + 1 + t) ((j : ℝ) + 1))
    (hle : ∀ i, GHG (f : ℝ) ((D.tile ix).pts i) ≤ -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j : ℝ) + 1)))
    (hθ : (D.tile ix).localAngle (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) ((j : ℝ) + 1)) = β ∨
      (D.tile ix).localAngle (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) ((j : ℝ) + 1)) = γ)
    (hno : ∀ i, (D.tile ix).pts i = lpG (e : ℝ) (f : ℝ) ε x ξ ((j : ℝ) + 1 + 1) → False)
    (hRho : ∀ w, RhoEdgeG D (e : ℝ) (f : ℝ) ε x w (ξ + ((j : ℝ) + 1) + 1) ((j : ℝ) + 1) → False) : False := by
  have S := C.S
  have hε := C.e2
  have he0 := S.e0
  have hef := S.hef'
  have hcl : ClampedBelowG D (e : ℝ) (f : ℝ) ε x (ξ + ((j : ℝ) + 1) + 1) ((j : ℝ) + 1) := by
    have hle3 := h3.all (P := fun p => GSG (e : ℝ) (f : ℝ) ε p ≤ -lvG (e : ℝ) (f : ℝ) ε x (ξ + ((j : ℝ) + 1) + 1))
      (GSG_le he0 hef hε (by linarith)) (GSG_le he0 hef hε (by linarith))
      (GSG_le he0 hef hε (by linarith))
    obtain ⟨k, m', j', hkm, hkj, hmj, hk, hm', hj⟩ := h3
    exact C.m_clamp_tileG hkm (by rw [hk]; exact lpG_congr (by ring) (by ring)) hm' hle3
  have hηn : ∃ n : ℕ, (j : ℝ) + 1 = n := ⟨j + 1, (Nat.cast_succ j).symm⟩
  rcases C.m_nextGr hηn h4 ⟨1, one_pos, h3.mem₃⟩ hcl with ⟨t₆, h6⟩ | ⟨t₆, h6⟩ | ⟨w, hw⟩
  · exact C.row_sixG h1 h2 h3 h4 ht hm hle hθ hno h6 (Or.inr (D_anglesG S hε h6).1)
      (h6.all (P := fun p => GSG (e : ℝ) (f : ℝ) ε p ≤ -lvG (e : ℝ) (f : ℝ) ε x (ξ + ((j : ℝ) + 1) + 1))
        (GSG_le he0 hef hε (by linarith)) (GSG_le he0 hef hε (by linarith))
        (GSG_le he0 hef hε (by linarith)))
  · exact C.row_sixG h1 h2 h3 h4 ht hm hle hθ hno h6 (Or.inl (N_anglesG S hε h6).1)
      (h6.all (P := fun p => GSG (e : ℝ) (f : ℝ) ε p ≤ -lvG (e : ℝ) (f : ℝ) ε x (ξ + ((j : ℝ) + 1) + 1))
        (GSG_le he0 hef hε (by linarith)) (GSG_le he0 hef hε (by linarith))
        (GSG_le he0 hef hε (by linarith)))
  · exact hRho w hw

/-! ## 5. Lemma Row -/

end CtxBase

namespace CtxG

variable {e f : ℕ} {α β γ L ax ay ε x : ℝ}

/-- **LEMMA ROW.**  Let `j ≥ 0`, `q ≥ 1`, `q + j ≤ f − 1`; the rows `≤ j` of `Δ_{q+j+1}` be lattice, `D(0,j), …, D(q−1,j)`
be tiles, the right end of the row segment `[p(0,j+1), p(q,j+1)]` be clamped for the tiles above it, and the claim `K` hold
for the sizes `< q`.  Then `U(0,j+1), …, U(q−1,j+1)` are tiles. -/
theorem rowG (C : CtxG D e f α β γ L ax ay ε x) {j q : ℕ} (hq : 1 ≤ q) (hqj : q + j + 1 ≤ f)
    (hUr : ∀ i' j' : ℕ, j' ≤ j → i' + j' ≤ q + j → UTG D (e : ℝ) (f : ℝ) ε x i' j')
    (hDr : ∀ i' j' : ℕ, j' < j → i' + j' + 1 ≤ q + j → DTG D (e : ℝ) (f : ℝ) ε x i' j')
    (hD : ∀ i' : ℕ, i' < q → DTG D (e : ℝ) (f : ℝ) ε x i' j)
    (hcl : ∃ Q' : Plane, GHG (f : ℝ) Q' = -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j : ℝ) + 1)) ∧
      lpG (e : ℝ) (f : ℝ) ε x q ((j : ℝ) + 1) ∈ openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x 0 ((j : ℝ) + 1)) Q' ∧
      ∀ ed ∈ D.lineChain (GHG (f : ℝ)) (-(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j : ℝ) + 1))),
        ¬ Straddles ((D.tile ed.1).edge ed.2) Q' (lpG (e : ℝ) (f : ℝ) ε x q ((j : ℝ) + 1)) (lpG (e : ℝ) (f : ℝ) ε x 0 ((j : ℝ) + 1)))
    (hA : ∀ m' : ℕ, 1 ≤ m' → m' < q → AG D e f ε x m') :
    ∀ r : ℕ, r < q → UTG D (e : ℝ) (f : ℝ) ε x r ((j : ℝ) + 1) := by
  classical
  have S := C.S
  have hε := C.e2
  have he0 := S.e0
  have hef := S.hef'
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  -- the tile `φ_j` at `p(0, j+1)`
  obtain ⟨φ, hφc, hφπ, hφpush⟩ := C.phiG (j := j + 1) (by omega) (by omega)
    (fun j' hj' => by
      have h := hUr 0 j' (by omega) (by omega)
      rwa [Nat.cast_zero] at h)
  simp only [Nat.cast_add, Nat.cast_one] at hφc hφπ hφpush
  -- the row segment
  have hA0q : lpG (e : ℝ) (f : ℝ) ε x 0 ((j : ℝ) + 1) ≠ lpG (e : ℝ) (f : ℝ) ε x q ((j : ℝ) + 1) := lpG_ne_xi he0 hef hε hqpos.ne
  have hfA0 : GHG (f : ℝ) (lpG (e : ℝ) (f : ℝ) ε x 0 ((j : ℝ) + 1)) = -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j : ℝ) + 1)) := GHG_lp _ _ _ _ _ _
  have hfAq : GHG (f : ℝ) (lpG (e : ℝ) (f : ℝ) ε x q ((j : ℝ) + 1)) = -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j : ℝ) + 1)) := GHG_lp _ _ _ _ _ _
  have hdir : FXG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x 0 ((j : ℝ) + 1) - lpG (e : ℝ) (f : ℝ) ε x q ((j : ℝ) + 1)) < 0 := by
    rw [map_sub, FXG_lp hε, FXG_lp hε]
    linarith [lvG_lt (e := (e : ℝ)) (f := (f : ℝ)) (ε := ε) (x := x) he0 hef hqpos]
  obtain ⟨P', hfP', hP', hsubφ⟩ := ext_point_of_push (GHG (f : ℝ)) hfA0 hfAq hφc (hφpush _ hdir)
  obtain ⟨tD0, hD0⟩ := hD 0 (by omega)
  rw [Nat.cast_zero] at hD0
  obtain ⟨tDq, hDq⟩ := hD (q - 1) (by omega)
  have hcq : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by rw [Nat.cast_sub hq, Nat.cast_one]
  rw [hcq] at hDq
  have hAq_mem : lpG (e : ℝ) (f : ℝ) ε x q ((j : ℝ) + 1) ∈ D.target.carrier := by
    have := hDq.mem₃
    rwa [show (q : ℝ) - 1 + 1 = q by ring] at this
  have hint : openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x 0 ((j : ℝ) + 1)) (lpG (e : ℝ) (f : ℝ) ε x q ((j : ℝ) + 1))
      ⊆ interior D.target.carrier :=
    C.seg_intG hD0.mem₂ hAq_mem (Or.inl (by linarith)) (Or.inl ⟨1, one_pos, hD0.mem₃⟩)
      (Or.inr ⟨1, one_pos, hDq.mem₂⟩)
  have hwall : ∀ y ∈ openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x 0 ((j : ℝ) + 1)) (lpG (e : ℝ) (f : ℝ) ε x q ((j : ℝ) + 1)),
      ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    have hy' : y ∈ segment ℝ (lpG (e : ℝ) (f : ℝ) ε x 0 ((j : ℝ) + 1))
        (lpG (e : ℝ) (f : ℝ) ε x (0 + (q : ℝ) * 1) ((j : ℝ) + 1 + (q : ℝ) * 0)) := by
      rw [show lpG (e : ℝ) (f : ℝ) ε x (0 + (q : ℝ) * 1) ((j : ℝ) + 1 + (q : ℝ) * 0) = lpG (e : ℝ) (f : ℝ) ε x q ((j : ℝ) + 1) from
        lpG_congr (by ring) (by ring)]
      exact openSegment_subset_segment ℝ _ _ hy
    obtain ⟨i', hi', hyi⟩ := seg_split_lpG hq hy'
    obtain ⟨t, k, m, j₃, hkm, hkj, hmj, hk, hm, hj⟩ := hD i' hi'
    refine seg_wall D.toDissection (t := t) hmj ?_
    rw [hm, hj]
    rw [show lpG (e : ℝ) (f : ℝ) ε x (0 + (i' : ℝ) * 1) ((j : ℝ) + 1 + (i' : ℝ) * 0) = lpG (e : ℝ) (f : ℝ) ε x i' ((j : ℝ) + 1) from
      lpG_congr (by ring) (by ring),
      show lpG (e : ℝ) (f : ℝ) ε x (0 + ((i' : ℝ) + 1) * 1) ((j : ℝ) + 1 + ((i' : ℝ) + 1) * 0)
        = lpG (e : ℝ) (f : ℝ) ε x ((i' : ℝ) + 1) ((j : ℝ) + 1) from lpG_congr (by ring) (by ring)] at hyi
    exact hyi
  obtain ⟨Q', hfQ', hQ', hQc⟩ := hcl
  have hpart := run_partition D.toDissection (GHG (f : ℝ)) (GHG_ne he0 hef) _ hA0q hfP' hfQ' hP' hQ'
    (CSlot.segment_subset_level (GHG (f : ℝ)) _ hfA0 hfAq) hint hwall
    (fun ed _ => not_straddles_of_interior D.toDissection hsubφ ed.1 ed.2) hQc
  have hdq : dist (lpG (e : ℝ) (f : ℝ) ε x 0 ((j : ℝ) + 1)) (lpG (e : ℝ) (f : ℝ) ε x q ((j : ℝ) + 1)) = (q : ℝ) * (f : ℝ) ^ 2 := by
    rw [dist_rowG he0 hef hε (by linarith : (0 : ℝ) ≤ q)]; ring
  have hnobΛ : ∀ ed ∈ D.lineChain (GHG (f : ℝ)) (-(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j : ℝ) + 1))),
      (D.tile ed.1).edge ed.2 ⊆ segment ℝ (lpG (e : ℝ) (f : ℝ) ε x 0 ((j : ℝ) + 1)) (lpG (e : ℝ) (f : ℝ) ε x q ((j : ℝ) + 1)) →
      dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1)) ≠ (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    intro ed he hsub hb
    obtain ⟨x', y', z', hxyz⟩ := sum_split_semigroup _ _ ((e : ℝ) * (f : ℝ)) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2) _
      (fun e' _ => edge_length_casesG D S.hM e'.1 e'.2) (Finset.mem_filter.mpr ⟨he, hsub⟩) hpart
    rw [hdq, hb] at hxyz
    have := SideRunGArith.A5 S.he S.hef S.hco hq (by omega)
      (rep_nat_c S.hef (x := x') (y := y' + 1) (z := z') (by push_cast; linarith))
    omega
  have hrowmem : ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ q →
      lpG (e : ℝ) (f : ℝ) ε x ρ ((j : ℝ) + 1) ∈ segment ℝ (lpG (e : ℝ) (f : ℝ) ε x 0 ((j : ℝ) + 1)) (lpG (e : ℝ) (f : ℝ) ε x q ((j : ℝ) + 1)) := by
    intro ρ h0 h1
    have h := lp_mem_segG (e := (e : ℝ)) (f := (f : ℝ)) (ε := ε) (x := x) (ξ := 0) (η := (j : ℝ) + 1)
      (ξ' := q) (η' := (j : ℝ) + 1) (τ := ρ / q) (div_nonneg h0 hqpos.le)
      (by rw [div_le_one hqpos]; exact h1)
    rw [show lpG (e : ℝ) (f : ℝ) ε x (0 + ρ / (q : ℝ) * ((q : ℝ) - 0))
          ((j : ℝ) + 1 + ρ / (q : ℝ) * ((j : ℝ) + 1 - ((j : ℝ) + 1)))
        = lpG (e : ℝ) (f : ℝ) ε x ρ ((j : ℝ) + 1) from
      lpG_congr (by rw [sub_zero, div_mul_cancel₀ _ hqpos.ne', zero_add]) (by ring)] at h
    exact h
  have hnobstep : ∀ ρ : ℝ, 0 ≤ ρ → ρ + 1 ≤ q →
      ∀ ed ∈ D.lineChain (GHG (f : ℝ)) (-(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j : ℝ) + 1))),
      (D.tile ed.1).edge ed.2 ⊆ segment ℝ (lpG (e : ℝ) (f : ℝ) ε x ρ ((j : ℝ) + 1)) (lpG (e : ℝ) (f : ℝ) ε x (ρ + 1) ((j : ℝ) + 1)) →
      dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1)) ≠ (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    intro ρ h0 h1 ed he hsub
    exact hnobΛ ed he (hsub.trans ((convex_segment _ _).segment_subset
      (hrowmem ρ h0 (by linarith)) (hrowmem (ρ + 1) (by linarith) h1)))
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hr
    rcases Nat.eq_zero_or_pos r with hr0 | hrpos
    · subst hr0
      rw [Nat.cast_zero]
      obtain ⟨tU, hUt⟩ := hUr 0 j le_rfl (by omega)
      rw [Nat.cast_zero] at hUt
      have hdir0 : FXG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x 0 ((j : ℝ) + 1) - lpG (e : ℝ) (f : ℝ) ε x (0 + 1) ((j : ℝ) + 1)) < 0 := by
        rw [map_sub, FXG_lp hε, FXG_lp hε]
        linarith [lvG_lt (e := (e : ℝ)) (f := (f : ℝ)) (ε := ε) (x := x) he0 hef
          (show (0 : ℝ) < 0 + 1 by norm_num)]
      obtain ⟨P₀, hfP₀, hP₀, hsub₀⟩ := ext_point_of_push (GHG (f : ℝ)) hfA0
        (GHG_lp (e : ℝ) (f : ℝ) ε x (0 + 1) ((j : ℝ) + 1)) hφc (hφpush _ hdir0)
      rcases C.row_stepG hD0 hj0
          ⟨P₀, hfP₀, hP₀, fun ed _ => not_straddles_of_interior D.toDissection hsub₀ ed.1 ed.2⟩
          (hnobstep 0 le_rfl (by linarith)) with
        hU | ⟨ix, k, m, j₃, t, hkm, hkj, hmj, hk, ht, hm, hle, hθ, hno⟩
      · exact hU
      · exact (C.row_bad0G hφπ hUt hD0 hle hθ).elim
    · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      rw [Nat.cast_add, Nat.cast_one]
      obtain ⟨t₃, h3⟩ := hD (r' + 1) hr
      rw [Nat.cast_add, Nat.cast_one] at h3
      obtain ⟨t₁, h1⟩ := hD r' (by omega)
      obtain ⟨t₂, h2⟩ := hUr (r' + 1) j le_rfl (by omega)
      rw [Nat.cast_add, Nat.cast_one] at h2
      obtain ⟨t₄, h4⟩ := ih r' (by omega) (by omega)
      have hr'0 : (0 : ℝ) ≤ r' := Nat.cast_nonneg r'
      have hr'q : (r' : ℝ) + 1 + 1 ≤ q := by
        have h' : r' + 1 + 1 ≤ q := hr
        exact_mod_cast h'
      have hclV : ∃ P'' : Plane, GHG (f : ℝ) P'' = -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j : ℝ) + 1)) ∧
          lpG (e : ℝ) (f : ℝ) ε x ((r' : ℝ) + 1) ((j : ℝ) + 1) ∈ openSegment ℝ P'' (lpG (e : ℝ) (f : ℝ) ε x ((r' : ℝ) + 1 + 1) ((j : ℝ) + 1)) ∧
          ∀ ed ∈ D.lineChain (GHG (f : ℝ)) (-(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j : ℝ) + 1))),
            ¬ Straddles ((D.tile ed.1).edge ed.2) P'' (lpG (e : ℝ) (f : ℝ) ε x ((r' : ℝ) + 1) ((j : ℝ) + 1))
              (lpG (e : ℝ) (f : ℝ) ε x ((r' : ℝ) + 1 + 1) ((j : ℝ) + 1)) := by
        have hle4 := h4.all (P := fun p => GHG (f : ℝ) p ≤ -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * ((j : ℝ) + 1)))
          (GHG_le he0 hef le_rfl) (GHG_le he0 hef le_rfl) (GHG_le he0 hef (by linarith))
        obtain ⟨k4, m4, j4, hkm4, -, -, hk4, hm4, -⟩ := h4
        have hVW : lpG (e : ℝ) (f : ℝ) ε x ((r' : ℝ) + 1) ((j : ℝ) + 1) ≠ lpG (e : ℝ) (f : ℝ) ε x ((r' : ℝ) + 1 + 1) ((j : ℝ) + 1) :=
          lpG_ne_xi he0 hef hε (by linarith)
        have hP'' : lpG (e : ℝ) (f : ℝ) ε x ((r' : ℝ) + 1) ((j : ℝ) + 1)
            ∈ openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x r' ((j : ℝ) + 1)) (lpG (e : ℝ) (f : ℝ) ε x ((r' : ℝ) + 1 + 1) ((j : ℝ) + 1)) := by
          refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
          unfold lpG
          apply plane_ext <;>
            simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mkPt_zero, mkPt_one] <;> ring
        exact ⟨_, GHG_lp _ _ _ _ _ _, hP'', clamp_b D.toDissection (GHG (f : ℝ)) (GHG_ne he0 hef) _ hVW
          (GHG_lp _ _ _ _ _ _) (GHG_lp _ _ _ _ _ _) (GHG_lp _ _ _ _ _ _) hP'' hkm4 hk4 hm4 hle4⟩
      rcases C.row_stepG h3 hj0 hclV (hnobstep ((r' : ℝ) + 1) (by linarith) hr'q) with
        hU | ⟨ix, k, m, j₃, t, hkm, hkj, hmj, hk, ht, hm, hle, hθ, hno⟩
      · exact hU
      · exfalso
        refine C.row_badG h1 h2 h3 h4 ht hm hle hθ
          (fun i hi => hno i (by rw [hi]; exact lpG_congr (by ring) rfl)) (fun w hw => ?_)
        refine hA (r' + 1) (by omega) hr (r' + 1 + j + 1) (j + 1) (by omega) (by omega) (by omega)
          ⟨?_, ?_⟩ ?_
        · intro i' j' hj' hij'
          rcases Nat.lt_or_ge j' (j + 1) with hlt | hge
          · exact hUr i' j' (by omega) (by omega)
          · have hje : j' = j + 1 := by omega
            subst hje
            have h := ih i' (by omega) (by omega)
            rw [Nat.cast_add, Nat.cast_one]
            exact h
        · intro i' j' hj' hij'
          rcases Nat.lt_or_ge j' j with hlt | hge
          · exact hDr i' j' hlt (by omega)
          · have hje : j' = j := by omega
            subst hje
            exact hD i' (by omega)
        · have e1 : (((r' + 1 + j + 1 : ℕ)) : ℝ) = (r' : ℝ) + ((j : ℝ) + 1) + 1 := by
            push_cast; ring
          have e2 : (((j + 1 : ℕ)) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
          rw [e1, e2]
          exact Or.inr ⟨w, hw⟩

end CtxG

end Erdos634.Draft.SideRunG

#print axioms Erdos634.Draft.SideRunG.run_partition_semigroupG
#print axioms Erdos634.Draft.SideRunG.fig_bg
#print axioms Erdos634.Draft.SideRunG.interior_of_four
#print axioms Erdos634.Draft.SideRunG.CtxBase.row_stepG
#print axioms Erdos634.Draft.SideRunG.CtxBase.row_bad0G
#print axioms Erdos634.Draft.SideRunG.CtxBase.row_sixG
#print axioms Erdos634.Draft.SideRunG.CtxBase.row_badG
#print axioms Erdos634.Draft.SideRunG.CtxG.rowG
