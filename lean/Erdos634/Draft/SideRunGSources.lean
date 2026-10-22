/-
Refactored 14 October 2026: `CtxBase` introduced, lemmas that use only the setup moved to it (no statement changed).
Draft/SideRunGSources.lean -- written 14 October 2026.  UNAUDITED.  In `AllThreshold`.  Module 7 of ten
(part A; the run lemma `L_k` in the paper's form is in `Draft/SideRunGSourcesB.lean`, the checks at `e = 1` in
`Draft/SideRunGSourcesC.lean`).

The general-member counterpart of `Draft/SideRunSources.lean`: where the hypotheses (K1) and (K3) of the run lemma come from,
for every coprime `1 ≤ e < f` with the tile `(e f, f² − e², f²)`.  Paper: Theorem `thm:siderunall`, "Run lemma `L_k`" and its
conditions (i), (ii), (i'), (ii'), fact (F); (private working notes, not included)  Every statement is under `SetupG` (a hypothesis;
`setup_of_sides` for general `e` is the next piece) and, where it is about a run, `CtxG`.

CONTENTS.
* Figures at the side: `gamma_alpha_alpha`, `four_alpha` (an open point of the side; from `MarchKillsFan`'s generic
  `straight_point_*`, which need only `AngleData`, not an order of `α, β`); `two_bg`: **at an open point of the side at most two
  distinct tiles show `β` or `γ`** (from the generic `congruentDissection_boundary_figure_cases`: the figures there are
  `{π}`, `{3α,2β}`, `{α,β,γ}`), and its corollary `three_beta`; `corner_two_alpha`, `corner_two_beta`: a corner of angle
  `α + β` carries neither two tiles showing `α` nor two showing `β` (the rest of the corner would be a multiple of `α`, resp.
  of `β`, against the irrationality of `α/π`).
* (K1), in the form of the field `hK1` of `CtxG` ("no tile of the side `σ` has both `P` and `p(0,1)` as vertices"):
  `K1_of_gamma` (`P` an open point of the side, the side tile beyond `P` shows `γ`), `K1_of_corner` (`P` a corner of angle
  `α + β`), `junction` (at the common end of a run to the right and a run to the left one of them has (K1)).
* The chords: `hch_pos` (from an open point), `hch_corner` (from a corner of angle `α + β`, whose second side has the direction
  `(e, √(4f² − e²))`); the field `hch` of `CtxG`.
* (K3G): `out_right`, `out_left` (the run ends at a corner of angle `β`: the side `ρ_s` is outside Δ), `K3G_out_right`,
  `K3G_out_left` (the first alternative of `K3G`);
  `m_next_intGr`, `K3G_of_next` (the tile across the last `a`-edge of the run lays `b` or `c` on `m_k`, unless it shows `γ` or
  `β` at the end of the run: the second alternative, through `m_clamp_baseG`); `bad_nb`, `bad_corner` (it does not show them).

WHAT DIFFERS FROM THE e = 1 TEXT.
(i)   `SideRunSources.Setup.bad_nb` and `bad_corner` close by angle sums that use `α < β` (`2 β + γ > π`; `2 β > α + β`).
      For a member with `β ≤ α` (e.g. `(2,3)`) those sums do not exceed `π`, `α + β`.  Here `bad_nb` uses `two_bg` (the
      figure at an open point: at most two tiles show `β` or `γ`) and `bad_corner` uses `corner_two_beta`; both are the paper's
      (F).  The figures used are available from the generic classification for EVERY member: the classification
      (`congruentDissection_boundary_figure_cases`, `…_interior_figure_cases`) assumes only `AngleData`, which contains
      `α ≠ β` and no order.
(ii)  `hch_corner`, `K3G_out_*` and the corner `α + β` have the general constants: the second side at the corner `Q` has the
      direction `(e, √(4f² − e²))` (`corner_left_ab`), the sides at the corners `B`, `Q` of angle `β` run along the `a`-edge of a
      `C1`, `C2` tile (`ax = L − t uuG`, `ay = t hhG`; `ax = t uuG`, `ay = t hhG`).
(iii) `K3G_of_next` ends in `K3G` (the second alternative `RhoEdgeG` with `η₁ = 0`, `Z` on the side, clamped by
      `m_clamp_baseG`), not in `K3`; `m_next_intGr` is `m_nextG` with the interior of the `a`-edge as a hypothesis (the e = 1
      `m_next_int`).
(iv)  `K1_of_gamma` for the general member: the side tile beyond `P` has an edge of length `λ ∈ {a, b}` on the side; if it is the
      tile `t'` itself (vertices `P`, `p(0,1)`, `(x − ε λ, 0)`) the sides at `P` are `λ` and `b`, and the third side would have
      to be `c`; its square is `f⁴ + 2 f (f + e)(e f − u)` with `u = uuG`, and `e f − u = e (f − e)² (2 f + e)/(2 f²) > 0`, so it is
      larger than `c²` (for `e = 1` this is the positive polynomial `2 n³ − 3 n² + 1 = (n − 1)² (2 n + 1)` of the e = 1 text, up
      to a factor).

WITNESSES.  `SetupG` (satisfied at `e = 1` by every `Setup`, `setupG_one_iff`; NO `SetupG` for `e ≥ 2` is exhibited yet, it
needs `setup_of_sides` for general `e`).  `K1_of_gamma`, `K1_of_corner`, `junction`, `bad_nb`, `bad_corner`, `gamma_alpha_alpha`,
`four_alpha`, `two_bg`, `three_beta`, `corner_two_*` are statements whose conclusion is `False` or a negation: contradiction
engines of the proof (like `SideRun.Setup.K1_of_gamma`); their hypotheses are those of a configuration the proof excludes.
`hch_pos`, `hch_corner`, `K3G_out_*`, `K3G_of_next` conclude positive statements.

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGK

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

/-! ## 0. Small tools -/

theorem sum_val_or_zero {ι : Type*} (s : Finset ι) (g : ι → ℝ) (a : ℝ)
    (h : ∀ i ∈ s, g i = a ∨ g i = 0) : ∃ c : ℕ, ∑ i ∈ s, g i = c * a := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert i s hi ih =>
    obtain ⟨c, hc⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    rw [Finset.sum_insert hi, hc]
    rcases h i (Finset.mem_insert_self i s) with hg | hg
    · exact ⟨c + 1, by rw [hg]; push_cast; ring⟩
    · exact ⟨c, by rw [hg]; ring⟩

/-- a tile with the `b`-edge `[pts k, pts m]` shows `γ` or `α` at `pts k` -/
theorem b_edge_angleG {e f α β γ : ℝ} (T : TileOK e f) (hM : ModelDataG D e f α β γ) {t : Fin N}
    {k m : Fin 3} (hkm : k ≠ m) (hd : dist ((D.tile t).pts k) ((D.tile t).pts m) = f ^ 2 - e ^ 2) :
    (D.tile t).localAngle ((D.tile t).pts k) = γ ∨ (D.tile t).localAngle ((D.tile t).pts k) = α := by
  obtain ⟨j, hjk, hjm⟩ := fin3_third k m hkm
  have hA := angle_at_vertexG D T hM t hkm (Ne.symm hjk) (Ne.symm hjm)
  rcases sides_of_b_edgeG D T hM t hkm (Ne.symm hjk) (Ne.symm hjm) hd with ⟨s1, s2⟩ | ⟨s1, s2⟩
  · left; exact hA.2.2 (by rw [dist_comm]; exact s2)
  · right; exact hA.1 (by rw [dist_comm]; exact s2)

theorem lpG_step_u (e f ε x : ℝ) : lpG e f ε x (0 + 1) 0 = mkPt (x + ε * f ^ 2) 0 := by
  unfold lpG; exact mkPt_congr (by ring) (by ring)

theorem lpG_step_v (e f ε x : ℝ) :
    lpG e f ε x 0 (0 + 1) = mkPt (x + ε * (f ^ 2 - uuG e f)) (hhG e f) := by
  unfold lpG; exact mkPt_congr (by ring) (by ring)

/-! ## 1. Figures -/

namespace SetupG

variable {e f : ℕ} {α β γ L ax ay x ε : ℝ}

theorem gamma_alpha_alpha (S : SetupG D e f α β γ L ax ay) {v : ℝ} (hv0 : 0 < v) (hvL : v < L)
    {i j l : Fin N} (hil : i ≠ l) (hi : (D.tile i).localAngle (mkPt v 0) = α)
    (hj : (D.tile j).localAngle (mkPt v 0) = γ) (hl : (D.tile l).localAngle (mkPt v 0) = α) :
    False :=
  straight_point_gamma_no_second_alpha D S.hA.hα S.hA.hβ S.hA.hαβ S.hA.hγdef S.hA.hrel S.hA.hirr
    S.hM.hα' S.hM.hβ' S.hM.hγ' (S.base_frontier hv0 hvL).1 (S.base_frontier hv0 hvL).2 hil hi hj hl

theorem four_alpha (S : SetupG D e f α β γ L ax ay) {v : ℝ} (hv0 : 0 < v) (hvL : v < L)
    {i k₁ k₂ l : Fin N} (h12 : i ≠ k₁) (h13 : i ≠ k₂) (h14 : i ≠ l) (h23 : k₁ ≠ k₂)
    (h24 : k₁ ≠ l) (h34 : k₂ ≠ l) (hi : (D.tile i).localAngle (mkPt v 0) = α)
    (hk₁ : (D.tile k₁).localAngle (mkPt v 0) = α) (hk₂ : (D.tile k₂).localAngle (mkPt v 0) = α)
    (hl : (D.tile l).localAngle (mkPt v 0) = α) : False :=
  straight_point_no_fourth_alpha D S.hA.hα S.hA.hβ S.hA.hαβ S.hA.hγdef S.hA.hrel S.hA.hirr
    S.hM.hα' S.hM.hβ' S.hM.hγ' (S.base_frontier hv0 hvL).1 (S.base_frontier hv0 hvL).2 h12 h13 h14
    h23 h24 h34 hi hk₁ hk₂ hl

/-- **At an open point of the side at most two distinct tiles show `β` or `γ`.**  (The figures of an open boundary point
are `{π}`, `{3α, 2β}`, `{α, β, γ}`.) -/
theorem two_bg (S : SetupG D e f α β γ L ax ay) {v : ℝ} (hv0 : 0 < v) (hvL : v < L)
    (l : List (Fin N)) (hl : l.Nodup)
    (h : ∀ i ∈ l, (D.tile i).localAngle (mkPt v 0) = β ∨ (D.tile i).localAngle (mkPt v 0) = γ) :
    l.length ≤ 2 := by
  classical
  obtain ⟨hαβ, hαγ, hαπ, hα0, hβγ, hβπ, hβ0, -, hγπ, hγ0, hπ0⟩ := distinct_of_angleData S.hA
  obtain ⟨hv, hnv⟩ := S.base_frontier hv0 hvL
  have hsub : l.toFinset ⊆ ({m | (D.tile m).localAngle (mkPt v 0) = β} : Finset (Fin N))
      ∪ ({m | (D.tile m).localAngle (mkPt v 0) = γ} : Finset (Fin N)) := by
    intro m hm
    rw [List.mem_toFinset] at hm
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h m hm
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le ({m | (D.tile m).localAngle (mkPt v 0) = β} : Finset (Fin N))
    ({m | (D.tile m).localAngle (mkPt v 0) = γ} : Finset (Fin N))
  rw [List.toFinset_card_of_nodup hl] at h1
  rcases congruentDissection_boundary_figure_cases D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
    S.hA.hγdef S.hA.hrel S.hA.hirr S.hM.hα' S.hM.hβ' S.hM.hγ' hv hnv with
    ⟨-, -, hB, hG⟩ | ⟨-, hB, hG⟩ | ⟨-, hB, hG⟩ <;> omega

/-- an open point of the side does not carry three tiles showing `β` -/
theorem three_beta (S : SetupG D e f α β γ L ax ay) {v : ℝ} (hv0 : 0 < v) (hvL : v < L)
    {i j l : Fin N} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hi : (D.tile i).localAngle (mkPt v 0) = β) (hj : (D.tile j).localAngle (mkPt v 0) = β)
    (hl : (D.tile l).localAngle (mkPt v 0) = β) : False := by
  have h := S.two_bg hv0 hvL [i, j, l] (by simp [hij, hil, hjl]) (by
    intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · exact Or.inl hi
    · exact Or.inl hj
    · exact Or.inl hl)
  simp at h

/-- **A corner of angle `α + β` does not carry two tiles showing `α`.** -/
theorem corner_two_alpha (S : SetupG D e f α β γ L ax ay)
    (hQ : D.target.localAngle (mkPt 0 0) = α + β) {i j : Fin N} (hij : i ≠ j)
    (hi : (D.tile i).localAngle (mkPt 0 0) = α) (hj : (D.tile j).localAngle (mkPt 0 0) = α) :
    False := by
  classical
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hγdef := S.hA.hγdef
  have hrel := S.hA.hrel
  have hπ := Real.pi_pos
  have hs := D.toDissection.sum_localAngle_eq (mkPt 0 0)
  rw [hQ] at hs
  have h1 : (D.tile i).localAngle (mkPt 0 0)
      + ∑ m ∈ Finset.univ.erase i, (D.tile m).localAngle (mkPt 0 0)
      = ∑ m, (D.tile m).localAngle (mkPt 0 0) :=
    Finset.add_sum_erase Finset.univ (fun m => (D.tile m).localAngle (mkPt 0 0))
      (Finset.mem_univ i)
  have h2 : (D.tile j).localAngle (mkPt 0 0)
      + ∑ m ∈ (Finset.univ.erase i).erase j, (D.tile m).localAngle (mkPt 0 0)
      = ∑ m ∈ Finset.univ.erase i, (D.tile m).localAngle (mkPt 0 0) :=
    Finset.add_sum_erase (Finset.univ.erase i) (fun m => (D.tile m).localAngle (mkPt 0 0))
      (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)
  rw [hi] at h1
  rw [hj] at h2
  have hrest : ∑ m ∈ (Finset.univ.erase i).erase j, (D.tile m).localAngle (mkPt 0 0) = β - α := by
    linarith
  have hvals : ∀ m ∈ (Finset.univ.erase i).erase j,
      (D.tile m).localAngle (mkPt 0 0) = α ∨ (D.tile m).localAngle (mkPt 0 0) = 0 := by
    intro m hm
    have hmem := congruentDissection_localAngle_mem D α β γ S.hM.hα' S.hM.hβ' S.hM.hγ' 0 m
    rw [S.Q_eq] at hmem
    have hle : (D.tile m).localAngle (mkPt 0 0) ≤ β - α := by
      rw [← hrest]
      exact Finset.single_le_sum (f := fun m => (D.tile m).localAngle (mkPt 0 0))
        (fun a _ => (D.tile a).localAngle_nonneg _) hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h | h
    · exact Or.inl h
    · exfalso; rw [h] at hle; linarith
    · exfalso; rw [h] at hle; linarith
    · exfalso; rw [h] at hle; linarith
    · exact Or.inr h
  obtain ⟨c, hc⟩ := sum_val_or_zero _ _ α hvals
  rw [hrest] at hc
  have h5 : (((2 * c + 5 : ℕ)) : ℝ) * α = Real.pi := by
    push_cast
    linarith
  have hne : (((2 * c + 5 : ℕ)) : ℝ) ≠ 0 := by positivity
  apply S.hA.hirr
  refine ⟨((2 * c + 5 : ℕ) : ℚ)⁻¹, ?_⟩
  rw [Rat.cast_inv, Rat.cast_natCast, ← h5, inv_mul_cancel_left₀ hne]

/-- **A corner of angle `α + β` does not carry two tiles showing `β`.**  (The rest of the corner, of angle `α − β`, would be a
multiple of `β`, so `α/π` would be rational; no order of `α` and `β` is used.) -/
theorem corner_two_beta (S : SetupG D e f α β γ L ax ay)
    (hQ : D.target.localAngle (mkPt 0 0) = α + β) {i j : Fin N} (hij : i ≠ j)
    (hi : (D.tile i).localAngle (mkPt 0 0) = β) (hj : (D.tile j).localAngle (mkPt 0 0) = β) :
    False := by
  classical
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hγdef := S.hA.hγdef
  have hrel := S.hA.hrel
  have hπ := Real.pi_pos
  have hs := D.toDissection.sum_localAngle_eq (mkPt 0 0)
  rw [hQ] at hs
  have h1 : (D.tile i).localAngle (mkPt 0 0)
      + ∑ m ∈ Finset.univ.erase i, (D.tile m).localAngle (mkPt 0 0)
      = ∑ m, (D.tile m).localAngle (mkPt 0 0) :=
    Finset.add_sum_erase Finset.univ (fun m => (D.tile m).localAngle (mkPt 0 0))
      (Finset.mem_univ i)
  have h2 : (D.tile j).localAngle (mkPt 0 0)
      + ∑ m ∈ (Finset.univ.erase i).erase j, (D.tile m).localAngle (mkPt 0 0)
      = ∑ m ∈ Finset.univ.erase i, (D.tile m).localAngle (mkPt 0 0) :=
    Finset.add_sum_erase (Finset.univ.erase i) (fun m => (D.tile m).localAngle (mkPt 0 0))
      (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)
  rw [hi] at h1
  rw [hj] at h2
  have hrest : ∑ m ∈ (Finset.univ.erase i).erase j, (D.tile m).localAngle (mkPt 0 0) = α - β := by
    linarith
  have hvals : ∀ m ∈ (Finset.univ.erase i).erase j,
      (D.tile m).localAngle (mkPt 0 0) = β ∨ (D.tile m).localAngle (mkPt 0 0) = 0 := by
    intro m hm
    have hmem := congruentDissection_localAngle_mem D α β γ S.hM.hα' S.hM.hβ' S.hM.hγ' 0 m
    rw [S.Q_eq] at hmem
    have hle : (D.tile m).localAngle (mkPt 0 0) ≤ α - β := by
      rw [← hrest]
      exact Finset.single_le_sum (f := fun m => (D.tile m).localAngle (mkPt 0 0))
        (fun a _ => (D.tile a).localAngle_nonneg _) hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h | h
    · exfalso; rw [h] at hle; linarith
    · exact Or.inl h
    · exfalso; rw [h] at hle; linarith
    · exfalso; rw [h] at hle; linarith
    · exact Or.inr h
  obtain ⟨c, hc⟩ := sum_val_or_zero _ _ β hvals
  rw [hrest] at hc
  have h5 : (((3 * c + 5 : ℕ)) : ℝ) * β = Real.pi := by
    push_cast
    linarith
  have hαβ' : α = (((c + 1 : ℕ)) : ℝ) * β := by
    push_cast
    linarith
  have hne : (((3 * c + 5 : ℕ)) : ℝ) ≠ 0 := by positivity
  apply S.hA.hirr
  refine ⟨((c + 1 : ℕ) : ℚ) / ((3 * c + 5 : ℕ) : ℚ), ?_⟩
  rw [Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast, ← h5, hαβ']
  field_simp

/-! ## 2. The chords -/

/-- the chords from an open point of the side are interior to the target -/
theorem hch_pos (S : SetupG D e f α β γ L ax ay) (hx0 : 0 < x) (hxL : x < L)
    (hP : mkPt x 0 ∈ D.target.carrier) :
    ∀ j : ℕ, 1 ≤ j → lpG (e : ℝ) (f : ℝ) ε x 0 j ∈ D.target.carrier →
      openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x 0 0) (lpG (e : ℝ) (f : ℝ) ε x 0 j) ⊆ interior D.target.carrier := by
  intro j hj hmem
  rw [lpG_zero]
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  refine S.interior_seg hP hmem (Or.inr ?_) (Or.inl ?_) (Or.inl ?_)
  · rw [lpG_snd]; exact mul_pos hjpos (hhG_pos S.e0 S.hef')
  · rw [gA_mk]; nlinarith [mul_pos S.hay hx0]
  · rw [gB_mk]; nlinarith [mul_pos S.hay (sub_pos.mpr hxL)]

/-- the chords from a corner of angle `α + β` at `Q` are interior to the target -/
theorem hch_corner (S : SetupG D e f α β γ L ax ay) {t : ℝ} (ht : 0 < t) (hax : ax = t * (e : ℝ))
    (hay' : ay = t * rtG (e : ℝ) (f : ℝ)) (hP : mkPt 0 0 ∈ D.target.carrier) :
    ∀ j : ℕ, 1 ≤ j → lpG (e : ℝ) (f : ℝ) 1 0 0 j ∈ D.target.carrier →
      openSegment ℝ (lpG (e : ℝ) (f : ℝ) 1 0 0 0) (lpG (e : ℝ) (f : ℝ) 1 0 0 j)
        ⊆ interior D.target.carrier := by
  intro j hj hmem
  rw [lpG_zero]
  have he0 := S.e0
  have hef := S.hef'
  have hf0 := S.f0
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  have hhp := hhG_pos he0 hef
  have hu := uuG_spec he0 hef
  have hh' := hhG_spec he0 hef
  have hrt := rtG_pos he0 hef
  have hb := S.b_pos
  have key : 2 * (f : ℝ) ^ 2 * (rtG (e : ℝ) (f : ℝ) * ((f : ℝ) ^ 2 - uuG (e : ℝ) (f : ℝ))
      - (e : ℝ) * hhG (e : ℝ) (f : ℝ))
      = 2 * rtG (e : ℝ) (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 := by
    linear_combination (-(rtG (e : ℝ) (f : ℝ))) * hu - (e : ℝ) * hh'
  have hX : 0 < rtG (e : ℝ) (f : ℝ) * ((f : ℝ) ^ 2 - uuG (e : ℝ) (f : ℝ))
      - (e : ℝ) * hhG (e : ℝ) (f : ℝ) := by
    have h2 : 0 < 2 * rtG (e : ℝ) (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 := by positivity
    rw [← key] at h2
    have h2f := two_f2_pos he0 hef
    by_contra hneg
    rw [not_lt] at hneg
    nlinarith [mul_nonneg h2f.le (neg_nonneg.mpr hneg)]
  refine S.interior_seg hP hmem (Or.inr ?_) (Or.inr ?_) (Or.inl ?_)
  · rw [lpG_snd]; exact mul_pos hjpos hhp
  · unfold lpG
    rw [gA_mk, hax, hay']
    have hpos := mul_pos (mul_pos ht hjpos) hX
    nlinarith [hpos]
  · rw [gB_mk]; nlinarith [mul_pos S.hay S.hL]

/-! ## 3. Hypothesis (K1) -/

/-- **(K1) from a side tile showing `γ` at `P`.**  `P = (x, 0)` is an open point of the side; a tile `j` has the vertices `P`
and `(x − ε λ, 0)`, `λ ∈ {a, b}`, and shows `γ` at `P`. -/
theorem K1_of_gamma (S : SetupG D e f α β γ L ax ay) (hε : ε ^ 2 = 1) (hx0 : 0 < x) (hxL : x < L)
    {t₀ : Fin N} (h0 : HasV D t₀ (lpG (e : ℝ) (f : ℝ) ε x 0 0) (lpG (e : ℝ) (f : ℝ) ε x (0 + 1) 0) (lpG (e : ℝ) (f : ℝ) ε x 0 (0 + 1)))
    {j : Fin N} {kj mj : Fin 3} {lam : ℝ} (hkmj : kj ≠ mj) (hkj : (D.tile j).pts kj = mkPt x 0)
    (hmj : (D.tile j).pts mj = mkPt (x - ε * lam) 0) (hlam : lam = (e : ℝ) * (f : ℝ) ∨ lam = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (hγj : (D.tile j).localAngle (mkPt x 0) = γ) :
    ∀ (t' : Fin N) (k m : Fin 3), k ≠ m → (D.tile t').pts k = lpG (e : ℝ) (f : ℝ) ε x 0 0 →
      (D.tile t').pts m = lpG (e : ℝ) (f : ℝ) ε x 0 1 → (∀ i, FXG (e : ℝ) (f : ℝ) ε ((D.tile t').pts i) ≤ lvG (e : ℝ) (f : ℝ) ε x 0) → False := by
  intro t' k m hkm hk hm hle
  have he0 := S.e0
  have hef := S.hef'
  have hf0 := S.f0
  have hb := S.b_pos
  have hhp := hhG_pos he0 hef
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hP : lpG (e : ℝ) (f : ℝ) ε x 0 0 = mkPt x 0 := lpG_zero _ _ _ _
  have ht0 : t' ≠ t₀ := by
    obtain ⟨i, hi⟩ := h0.idx₂
    refine ne_of_F (FXG (e : ℝ) (f : ℝ) ε) hle (i := i) ?_
    rw [hi, FXG_lp hε]
    exact lvG_lt he0 hef (by norm_num)
  have hd : dist ((D.tile t').pts k) ((D.tile t').pts m) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rw [hk, hm]
    have := dist_step_vG (x := x) he0 hef hε 0 0
    rwa [zero_add] at this
  have hG1 : (lpG (e : ℝ) (f : ℝ) ε x 0 1) 1 = hhG (e : ℝ) (f : ℝ) := by rw [lpG_snd]; ring
  have hang := b_edge_angleG S.tile S.hM hkm hd
  rw [hk, hP] at hang
  rcases hang with hγ' | hα'
  · -- two `γ` at `P`
    have hne : t' ≠ j := by
      rintro rfl
      have hmk : m ≠ kj := by
        intro h
        rw [h, hkj] at hm
        have := congrArg (fun p : Plane => p 1) hm
        simp only [mkPt_one] at this
        rw [hG1] at this
        linarith
      have hmm : m ≠ mj := by
        intro h
        rw [h, hmj] at hm
        have := congrArg (fun p : Plane => p 1) hm
        simp only [mkPt_one] at this
        rw [hG1] at this
        linarith
      have hlampos : 0 < lam := by
        rcases hlam with h | h
        · rw [h]; exact mul_pos he0 hf0
        · rw [h]; exact hb
      have hdj : dist ((D.tile t').pts kj) ((D.tile t').pts mj) = lam := by
        rw [hkj, hmj]
        refine dist_eq_of_sq_eq ?_ dist_nonneg hlampos.le
        rw [dist_sq_mkPt]
        linear_combination (lam ^ 2) * hε
      have hdG : dist ((D.tile t').pts m) ((D.tile t').pts kj) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
        rw [dist_comm, hkj, ← hP, ← hk]; exact hd
      rcases hlam with h | h
      · -- an `A`-tile: its third vertex would be at distance `c` from `(x − ε a, 0)`
        rw [h] at hdj hmj
        rcases sides_of_a_edgeG D S.tile S.hM t' hkmj (Ne.symm hmk) (Ne.symm hmm) hdj with
          ⟨s1, -⟩ | ⟨-, s2⟩
        · rw [hdG] at s1; exact S.tile.bc s1
        · rw [hm, hmj] at s2
          have hsq : dist (lpG (e : ℝ) (f : ℝ) ε x 0 1) (mkPt (x - ε * ((e : ℝ) * (f : ℝ))) 0) ^ 2
              = ((f : ℝ) ^ 2 - uuG (e : ℝ) (f : ℝ) + (e : ℝ) * (f : ℝ)) ^ 2 + hhG (e : ℝ) (f : ℝ) ^ 2 := by
            unfold lpG
            rw [dist_sq_mkPt]
            linear_combination (((f : ℝ) ^ 2 - uuG (e : ℝ) (f : ℝ) + (e : ℝ) * (f : ℝ)) ^ 2) * hε
          rw [s2] at hsq
          have hu := uuG_spec he0 hef
          have hhs := hhG_sq he0 hef
          have hG : 2 * (f : ℝ) * ((f : ℝ) + (e : ℝ)) * ((e : ℝ) * (f : ℝ) - uuG (e : ℝ) (f : ℝ)) = 0 := by
            linear_combination (-1 : ℝ) * hsq - hhs
          have hfe : 2 * (f : ℝ) * ((f : ℝ) + (e : ℝ)) ≠ 0 := by positivity
          have hEq : (e : ℝ) * (f : ℝ) = uuG (e : ℝ) (f : ℝ) := by
            have := (mul_eq_zero.mp hG).resolve_left hfe
            linarith
          rw [← hEq] at hu
          have hz : (e : ℝ) * (((f : ℝ) - (e : ℝ)) ^ 2 * (2 * (f : ℝ) + (e : ℝ))) = 0 := by linear_combination hu
          have hpos : 0 < (e : ℝ) * (((f : ℝ) - (e : ℝ)) ^ 2 * (2 * (f : ℝ) + (e : ℝ))) :=
            mul_pos he0 (mul_pos (pow_pos (sub_pos.mpr hef) 2) (by linarith))
          linarith
      · -- a `B`-tile: two sides `b`
        rw [h] at hdj
        rcases sides_of_b_edgeG D S.tile S.hM t' hkmj (Ne.symm hmk) (Ne.symm hmm) hdj with
          ⟨s1, -⟩ | ⟨s1, -⟩
        · rw [hdG] at s1; exact S.tile.hab s1.symm
        · rw [hdG] at s1; exact S.tile.bc s1
    have h2 := two_angles_le D.toDissection (mkPt x 0) hne
    rw [hγ', hγj, S.angle_base hx0 hxL] at h2
    linarith
  · -- `γ`, `α`, `α` at `P`
    have ha0 := (U_anglesG S hε h0).1
    rw [hP] at ha0
    exact S.gamma_alpha_alpha hx0 hxL ht0 hα' hγj ha0

/-- **(K1) at a corner of angle `α + β`.** -/
theorem K1_of_corner (S : SetupG D e f α β γ L ax ay) (hε : ε ^ 2 = 1)
    (hQ : D.target.localAngle (mkPt 0 0) = α + β) {t₀ : Fin N}
    (h0 : HasV D t₀ (lpG (e : ℝ) (f : ℝ) ε 0 0 0) (lpG (e : ℝ) (f : ℝ) ε 0 (0 + 1) 0) (lpG (e : ℝ) (f : ℝ) ε 0 0 (0 + 1))) :
    ∀ (t' : Fin N) (k m : Fin 3), k ≠ m → (D.tile t').pts k = lpG (e : ℝ) (f : ℝ) ε 0 0 0 →
      (D.tile t').pts m = lpG (e : ℝ) (f : ℝ) ε 0 0 1 →
      (∀ i, FXG (e : ℝ) (f : ℝ) ε ((D.tile t').pts i) ≤ lvG (e : ℝ) (f : ℝ) ε 0 0) → False := by
  intro t' k m hkm hk hm hle
  have he0 := S.e0
  have hef := S.hef'
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hγdef := S.hA.hγdef
  have hP : lpG (e : ℝ) (f : ℝ) ε 0 0 0 = mkPt 0 0 := lpG_zero _ _ _ _
  have ht0 : t' ≠ t₀ := by
    obtain ⟨i, hi⟩ := h0.idx₂
    refine ne_of_F (FXG (e : ℝ) (f : ℝ) ε) hle (i := i) ?_
    rw [hi, FXG_lp hε]
    exact lvG_lt he0 hef (by norm_num)
  have hd : dist ((D.tile t').pts k) ((D.tile t').pts m) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rw [hk, hm]
    have := dist_step_vG (x := (0 : ℝ)) he0 hef hε 0 0
    rwa [zero_add] at this
  have hang := b_edge_angleG S.tile S.hM hkm hd
  rw [hk, hP] at hang
  rcases hang with hγ' | hα'
  · have h1 := one_angle_le D.toDissection (mkPt 0 0) t'
    rw [hγ', hQ] at h1
    linarith
  · have ha0 := (U_anglesG S hε h0).1
    rw [hP] at ha0
    exact S.corner_two_alpha hQ ht0 hα' ha0

/-- **(K1) at a junction.**  At the common end `J = (x, 0)` of a run to the right and a run to the left, an open point of the
side, at least one of the two runs has (K1): otherwise four tiles show `α` at `J`. -/
theorem junction (S : SetupG D e f α β γ L ax ay) (hx0 : 0 < x) (hxL : x < L) {t₁ t₂ : Fin N}
    (h1 : HasV D t₁ (lpG (e : ℝ) (f : ℝ) 1 x 0 0) (lpG (e : ℝ) (f : ℝ) 1 x (0 + 1) 0) (lpG (e : ℝ) (f : ℝ) 1 x 0 (0 + 1)))
    (h2 : HasV D t₂ (lpG (e : ℝ) (f : ℝ) (-1) x 0 0) (lpG (e : ℝ) (f : ℝ) (-1) x (0 + 1) 0)
      (lpG (e : ℝ) (f : ℝ) (-1) x 0 (0 + 1))) :
    (∀ (t' : Fin N) (k m : Fin 3), k ≠ m → (D.tile t').pts k = lpG (e : ℝ) (f : ℝ) 1 x 0 0 →
      (D.tile t').pts m = lpG (e : ℝ) (f : ℝ) 1 x 0 1 →
      (∀ i, FXG (e : ℝ) (f : ℝ) 1 ((D.tile t').pts i) ≤ lvG (e : ℝ) (f : ℝ) 1 x 0) → False) ∨
    (∀ (t' : Fin N) (k m : Fin 3), k ≠ m → (D.tile t').pts k = lpG (e : ℝ) (f : ℝ) (-1) x 0 0 →
      (D.tile t').pts m = lpG (e : ℝ) (f : ℝ) (-1) x 0 1 →
      (∀ i, FXG (e : ℝ) (f : ℝ) (-1) ((D.tile t').pts i) ≤ lvG (e : ℝ) (f : ℝ) (-1) x 0) → False) := by
  refine or_iff_not_imp_left.mpr (fun hA => ?_)
  intro tb kb mb hkmb hkb hmb hleb
  apply hA
  intro ta ka ma hkma hka hma hlea
  have he0 := S.e0
  have hef := S.hef'
  have hf0 := S.f0
  have hb := S.b_pos
  have hc := S.c_pos
  have hhp := hhG_pos he0 hef
  have hu := uuG_spec he0 hef
  have huc : uuG (e : ℝ) (f : ℝ) < (f : ℝ) ^ 2 := by
    by_contra hge
    rw [not_lt] at hge
    have h1' := mul_le_mul_of_nonneg_left hge (by positivity : (0 : ℝ) ≤ 2 * (f : ℝ) ^ 2)
    nlinarith [mul_pos (show (0 : ℝ) < 2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 by linarith) hb]
  have e1 : (1 : ℝ) ^ 2 = 1 := by norm_num
  have em : (-1 : ℝ) ^ 2 = 1 := by norm_num
  have hP1 : lpG (e : ℝ) (f : ℝ) 1 x 0 0 = mkPt x 0 := lpG_zero _ _ _ _
  have hPm : lpG (e : ℝ) (f : ℝ) (-1) x 0 0 = mkPt x 0 := lpG_zero _ _ _ _
  have hB1 : lpG (e : ℝ) (f : ℝ) 1 x (0 + 1) 0 = mkPt (x + (f : ℝ) ^ 2) 0 := by
    rw [lpG_step_u]; exact mkPt_congr (by ring) rfl
  have hBm : lpG (e : ℝ) (f : ℝ) (-1) x (0 + 1) 0 = mkPt (x - (f : ℝ) ^ 2) 0 := by
    rw [lpG_step_u]; exact mkPt_congr (by ring) rfl
  have hG1 : lpG (e : ℝ) (f : ℝ) 1 x 0 (0 + 1) = mkPt (x + ((f : ℝ) ^ 2 - uuG (e : ℝ) (f : ℝ))) (hhG (e : ℝ) (f : ℝ)) := by
    rw [lpG_step_v]; exact mkPt_congr (by ring) rfl
  have hGm : lpG (e : ℝ) (f : ℝ) (-1) x 0 (0 + 1) = mkPt (x - ((f : ℝ) ^ 2 - uuG (e : ℝ) (f : ℝ))) (hhG (e : ℝ) (f : ℝ)) := by
    rw [lpG_step_v]; exact mkPt_congr (by ring) rfl
  have hG1' : lpG (e : ℝ) (f : ℝ) 1 x 0 1 = mkPt (x + ((f : ℝ) ^ 2 - uuG (e : ℝ) (f : ℝ))) (hhG (e : ℝ) (f : ℝ)) := by
    rw [← hG1]; exact lpG_congr rfl (by ring)
  have hGm' : lpG (e : ℝ) (f : ℝ) (-1) x 0 1 = mkPt (x - ((f : ℝ) ^ 2 - uuG (e : ℝ) (f : ℝ))) (hhG (e : ℝ) (f : ℝ)) := by
    rw [← hGm]; exact lpG_congr rfl (by ring)
  -- the angles at `J`
  have a1 := (U_anglesG S e1 h1).1
  have a2 := (U_anglesG S em h2).1
  rw [hP1] at a1
  rw [hPm] at a2
  have hda : dist ((D.tile ta).pts ka) ((D.tile ta).pts ma) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rw [hka, hma]
    have := dist_step_vG (x := x) he0 hef e1 0 0
    rwa [zero_add] at this
  have hdb : dist ((D.tile tb).pts kb) ((D.tile tb).pts mb) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rw [hkb, hmb]
    have := dist_step_vG (x := x) he0 hef em 0 0
    rwa [zero_add] at this
  have hanga := b_edge_angleG S.tile S.hM hkma hda
  have hangb := b_edge_angleG S.tile S.hM hkmb hdb
  rw [hka, hP1] at hanga
  rw [hkb, hPm] at hangb
  rw [hP1] at hka
  rw [hPm] at hkb
  rw [hG1'] at hma
  rw [hGm'] at hmb
  rw [hP1, hB1, hG1] at h1
  rw [hPm, hBm, hGm] at h2
  -- distinctness
  have n12 : t₁ ≠ t₂ := by
    obtain ⟨i, hi⟩ := h1.idx₂
    exact h2.ne_of_vertex hi (mkPt_ne_of_fst (by linarith)) (mkPt_ne_of_fst (by linarith))
      (mkPt_ne_of_snd hhp.ne)
  have n1a : t₁ ≠ ta := by
    obtain ⟨i, hi⟩ := h1.idx₂
    refine (ne_of_F (FXG (e : ℝ) (f : ℝ) 1) hlea (i := i) ?_).symm
    rw [hi, ← hB1, FXG_lp e1]
    exact lvG_lt he0 hef (by norm_num)
  have n2b : t₂ ≠ tb := by
    obtain ⟨i, hi⟩ := h2.idx₂
    refine (ne_of_F (FXG (e : ℝ) (f : ℝ) (-1)) hleb (i := i) ?_).symm
    rw [hi, ← hBm, FXG_lp em]
    exact lvG_lt he0 hef (by norm_num)
  have n1b : t₁ ≠ tb :=
    (h1.ne_of_vertex hmb (mkPt_ne_of_snd hhp.ne') (mkPt_ne_of_snd hhp.ne')
      (mkPt_ne_of_fst (by linarith))).symm
  have n2a : t₂ ≠ ta :=
    (h2.ne_of_vertex hma (mkPt_ne_of_snd hhp.ne') (mkPt_ne_of_snd hhp.ne')
      (mkPt_ne_of_fst (by linarith))).symm
  rcases hanga with hγa | hαa
  · exact S.gamma_alpha_alpha hx0 hxL n12 a1 hγa a2
  rcases hangb with hγb | hαb
  · exact S.gamma_alpha_alpha hx0 hxL n12 a1 hγb a2
  have nab : ta ≠ tb := by
    rintro rfl
    have hkk : kb = ka := (D.tile ta).indep.injective (hkb.trans hka.symm)
    have hmm : ma ≠ mb := by
      intro h
      rw [h, hmb] at hma
      have := (mkPt_inj hma).1
      linarith
    have hkm' : ka ≠ mb := by rw [← hkk]; exact hkmb
    rcases sides_of_b_edgeG D S.tile S.hM ta hkma hkm' hmm hda with ⟨s1, -⟩ | ⟨s1, -⟩
    · rw [dist_comm, ← hkk, hdb] at s1; exact S.tile.hab s1.symm
    · rw [dist_comm, ← hkk, hdb] at s1; exact S.tile.bc s1
  exact S.four_alpha hx0 hxL n12 n1a n1b n2a n2b nab a1 a2 hαa hαb

/-! ## 4. Hypothesis (K3G) -/

/-- a run to the right that ends at the corner `B`, of angle `β`: the side `ρ_k` is outside the target -/
theorem out_right (S : SetupG D e f α β γ L ax ay) {t : ℝ} (ht : 0 < t)
    (hax : ax = L - t * uuG (e : ℝ) (f : ℝ)) (hay' : ay = t * hhG (e : ℝ) (f : ℝ)) {k : ℝ}
    (hx : x + k * (f : ℝ) ^ 2 = L) : ∀ q ∈ D.target.carrier, -lvG (e : ℝ) (f : ℝ) 1 x k ≤ GSG (e : ℝ) (f : ℝ) 1 q := by
  intro q hq
  have h := (S.mem hq).2.2
  unfold gB at h
  rw [hax, hay'] at h
  have h' : 0 ≤ hhG (e : ℝ) (f : ℝ) * (L - q 0) - uuG (e : ℝ) (f : ℝ) * q 1 := by
    by_contra hneg
    rw [not_le] at hneg
    nlinarith [mul_pos ht (neg_pos.mpr hneg)]
  have e : hhG (e : ℝ) (f : ℝ) * x + (f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ) * k = hhG (e : ℝ) (f : ℝ) * L := by rw [← hx]; ring
  unfold GSG lvG
  rw [lin_apply]
  linarith

theorem K3G_out_right (S : SetupG D e f α β γ L ax ay) {t : ℝ} (ht : 0 < t)
    (hax : ax = L - t * uuG (e : ℝ) (f : ℝ)) (hay' : ay = t * hhG (e : ℝ) (f : ℝ)) {k : ℝ}
    (hx : x + k * (f : ℝ) ^ 2 = L) : K3G D (e : ℝ) (f : ℝ) 1 x k 0 :=
  Or.inl (S.out_right ht hax hay' hx)

/-- a run to the left that ends at the corner `Q`, of angle `β` -/
theorem out_left (S : SetupG D e f α β γ L ax ay) {t : ℝ} (ht : 0 < t)
    (hax : ax = t * uuG (e : ℝ) (f : ℝ)) (hay' : ay = t * hhG (e : ℝ) (f : ℝ)) {k : ℝ}
    (hx : x - k * (f : ℝ) ^ 2 = 0) : ∀ q ∈ D.target.carrier, -lvG (e : ℝ) (f : ℝ) (-1) x k ≤ GSG (e : ℝ) (f : ℝ) (-1) q := by
  intro q hq
  have h := (S.mem hq).2.1
  unfold gA at h
  rw [hax, hay'] at h
  have h' : 0 ≤ hhG (e : ℝ) (f : ℝ) * q 0 - uuG (e : ℝ) (f : ℝ) * q 1 := by
    by_contra hneg
    rw [not_le] at hneg
    nlinarith [mul_pos ht (neg_pos.mpr hneg)]
  have e : hhG (e : ℝ) (f : ℝ) * x - (f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ) * k = 0 := by
    have : hhG (e : ℝ) (f : ℝ) * x - (f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ) * k = hhG (e : ℝ) (f : ℝ) * (x - k * (f : ℝ) ^ 2) := by ring
    rw [this, hx, mul_zero]
  unfold GSG lvG
  rw [lin_apply]
  linarith

theorem K3G_out_left (S : SetupG D e f α β γ L ax ay) {t : ℝ} (ht : 0 < t)
    (hax : ax = t * uuG (e : ℝ) (f : ℝ)) (hay' : ay = t * hhG (e : ℝ) (f : ℝ)) {k : ℝ}
    (hx : x - k * (f : ℝ) ^ 2 = 0) : K3G D (e : ℝ) (f : ℝ) (-1) x k 0 :=
  Or.inl (S.out_left ht hax hay' hx)

/-- the tile across the last `a`-edge of a run does not show `γ` or `β` at the end `V` of the run, an open point of the
side, if the side tile beyond `V` shows `γ` or `β` there -/
theorem bad_nb (S : SetupG D e f α β γ L ax ay) {xR : ℝ} (hx0 : 0 < xR) (hxL : xR < L)
    {G A₀ Rp Z : Plane} (hG1 : 0 < G 1) {t₀ : Fin N} (h0 : HasV D t₀ A₀ (mkPt xR 0) G)
    (hA₀ : A₀ 1 = 0) (hβ0 : (D.tile t₀).localAngle (mkPt xR 0) = β)
    {j : Fin N} {mj : Fin 3} (hmj : (D.tile j).pts mj = Rp) (hRp1 : Rp 1 = 0)
    (hRpV : Rp ≠ mkPt xR 0) (hRpA : Rp ≠ A₀)
    (hθj : (D.tile j).localAngle (mkPt xR 0) = γ ∨ (D.tile j).localAngle (mkPt xR 0) = β)
    {W : Fin N} (hW : HasV D W (mkPt xR 0) G Z)
    (hθW : (D.tile W).localAngle (mkPt xR 0) = γ ∨ (D.tile W).localAngle (mkPt xR 0) = β)
    (hZ1 : 0 < Z 1) : False := by
  have hne1 : ∀ {P Q : Plane}, P 1 = 0 → 0 < Q 1 → P ≠ Q := by
    intro P Q hP hQ h
    rw [h] at hP
    linarith
  have hjW : j ≠ W := hW.ne_of_vertex hmj hRpV (hne1 hRp1 hG1) (hne1 hRp1 hZ1)
  have hjt : j ≠ t₀ := h0.ne_of_vertex hmj hRpA hRpV (hne1 hRp1 hG1)
  have htW : t₀ ≠ W := by
    obtain ⟨k0, m0, j0, hkm0, -, -, hk0, hm0, -⟩ := h0
    have hAV : A₀ ≠ mkPt xR 0 := fun h =>
      hkm0 ((D.tile t₀).indep.injective (hk0.trans (h.trans hm0.symm)))
    exact hW.ne_of_vertex hk0 hAV (hne1 hA₀ hG1) (hne1 hA₀ hZ1)
  have h3 := S.two_bg hx0 hxL [t₀, j, W] (by simp [htW, hjt.symm, hjW]) (by
    intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · exact Or.inl hβ0
    · exact hθj.symm
    · exact hθW.symm)
  simp at h3

/-- the same at a corner of angle `α + β` of the target -/
theorem bad_corner (S : SetupG D e f α β γ L ax ay) (hQ : D.target.localAngle (mkPt 0 0) = α + β)
    {G A₀ Z : Plane} (hG1 : 0 < G 1) {t₀ : Fin N} (h0 : HasV D t₀ A₀ (mkPt 0 0) G)
    (hA₀ : A₀ 1 = 0) (hβ0 : (D.tile t₀).localAngle (mkPt 0 0) = β)
    {W : Fin N} (hW : HasV D W (mkPt 0 0) G Z)
    (hθW : (D.tile W).localAngle (mkPt 0 0) = γ ∨ (D.tile W).localAngle (mkPt 0 0) = β)
    (hZ1 : 0 < Z 1) : False := by
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hγdef := S.hA.hγdef
  have hne1 : ∀ {P Q : Plane}, P 1 = 0 → 0 < Q 1 → P ≠ Q := by
    intro P Q hP hQ h
    rw [h] at hP
    linarith
  have htW : t₀ ≠ W := by
    obtain ⟨k0, m0, j0, hkm0, -, -, hk0, hm0, -⟩ := h0
    have hAV : A₀ ≠ mkPt 0 0 := fun h =>
      hkm0 ((D.tile t₀).indep.injective (hk0.trans (h.trans hm0.symm)))
    exact hW.ne_of_vertex hk0 hAV (hne1 hA₀ hG1) (hne1 hA₀ hZ1)
  rcases hθW with hw | hw
  · have h1 := one_angle_le D.toDissection (mkPt 0 0) W
    rw [hw, hQ] at h1
    linarith
  · exact S.corner_two_beta hQ htW hβ0 hw

end SetupG

/-! ## 5. The tile across the last `a`-edge of a run -/

namespace CtxBase

variable {e f : ℕ} {α β γ L ax ay ε x : ℝ}

/-- `m_nextG` with the interior of the `a`-edge as a hypothesis (instead of a target point beyond the edge), at a real height
that is a natural number (the e = 1 `m_next_int`) -/
theorem m_next_intGr (C : CtxBase D e f α β γ L ax ay ε x) {ξ η : ℝ} (hη : ∃ n : ℕ, η = n)
    {t₀ : Fin N} (hU : HasV D t₀ (lpG (e : ℝ) (f : ℝ) ε x ξ η) (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η) (lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1)))
    (hint : openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η) (lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1)) ⊆ interior D.target.carrier)
    (hcl : ClampedBelowG D (e : ℝ) (f : ℝ) ε x (ξ + η + 1) η) :
    (∃ t, HasV D t (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η) (lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1)) (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) (η + 1))) ∨
    (∃ t, HasV D t (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η) (lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1))
      (lpG (e : ℝ) (f : ℝ) ε x (ξ - nuG (e : ℝ) (f : ℝ)) (η + 2 + nuG (e : ℝ) (f : ℝ)))) ∨
    (∃ w, RhoEdgeG D (e : ℝ) (f : ℝ) ε x w (ξ + η + 1) η) := by
  obtain ⟨n, rfl⟩ := hη
  have hε := C.e2
  have he0 := C.S.e0
  have hef := C.S.hef'
  have hηpos : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hVG : lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) n ≠ lpG (e : ℝ) (f : ℝ) ε x ξ (n + 1) := lpG_ne_eta he0 hef (by linarith)
  have hfV : GSG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) n) = -lvG (e : ℝ) (f : ℝ) ε x (ξ + n + 1) := by
    rw [GSG_lp hε]; unfold lvG; ring
  have hfG : GSG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x ξ (n + 1)) = -lvG (e : ℝ) (f : ℝ) ε x (ξ + n + 1) := by
    rw [GSG_lp hε]; unfold lvG; ring
  have hwall : ∀ y ∈ openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) n) (lpG (e : ℝ) (f : ℝ) ε x ξ (n + 1)),
      ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := hU
    refine seg_wall D.toDissection (t := t₀) hmj ?_
    rw [hm, hj]; exact openSegment_subset_segment ℝ _ _ hy
  obtain ⟨η', hη', hprop⟩ := hcl
  have hZ : lpG (e : ℝ) (f : ℝ) ε x (ξ + n + 1 - n) n = lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) n := lpG_congr (by ring) rfl
  have hP'mem : lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) n ∈ openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x (ξ + n + 1 - η') η') (lpG (e : ℝ) (f : ℝ) ε x ξ (n + 1)) := by
    have h := lpG_between (e := (e : ℝ)) (f := (f : ℝ)) (ε := ε) (x := x) (s := ξ + n + 1)
      (η' := η') (η := n) (η'' := n + 1) hη' (by linarith)
    rw [hZ, show lpG (e : ℝ) (f : ℝ) ε x (ξ + n + 1 - (n + 1)) (n + 1) = lpG (e : ℝ) (f : ℝ) ε x ξ (n + 1) from lpG_congr (by ring) rfl] at h
    exact h
  have hfP' : GSG (e : ℝ) (f : ℝ) ε (lpG (e : ℝ) (f : ℝ) ε x (ξ + n + 1 - η') η') = -lvG (e : ℝ) (f : ℝ) ε x (ξ + n + 1) := by
    rw [GSG_lp hε]; unfold lvG; ring
  have hP : ∀ ed ∈ D.lineChain (GSG (e : ℝ) (f : ℝ) ε) (-lvG (e : ℝ) (f : ℝ) ε x (ξ + n + 1)),
      ¬ Straddles ((D.tile ed.1).edge ed.2) (lpG (e : ℝ) (f : ℝ) ε x (ξ + n + 1 - η') η') (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) n)
        (lpG (e : ℝ) (f : ℝ) ε x ξ (n + 1)) := by
    have h := hprop (lpG (e : ℝ) (f : ℝ) ε x ξ (n + 1)) hfG (by rw [hZ]; exact hP'mem)
    rw [hZ] at h
    exact h
  have hcl' : ClampedBelowG D (e : ℝ) (f : ℝ) ε x (ξ + n + 1) n := ⟨η', hη', hprop⟩
  obtain ⟨ed, hed, k', m', t, hk'm', hk', ht, hm', hle, -, -⟩ :=
    next_tile D.toDissection (GSG (e : ℝ) (f : ℝ) ε) (GSG_ne he0 hef hε) (-lvG (e : ℝ) (f : ℝ) ε x (ξ + n + 1)) hVG hfV hfG hfP'
      hP'mem hint hwall hP
  rcases C.m_next_casesG hk'm' hk' ht hm' hle hcl' with hG | hR
  · rcases m_edge_casesG C.S hε hk'm' hk' hG hle with h | h
    · exact Or.inl ⟨ed.1, h⟩
    · exact Or.inr (Or.inl ⟨ed.1, h⟩)
  · exact Or.inr (Or.inr ⟨ed.1, hR⟩)

/-- **(K3G) from the tile across the last `a`-edge of the run**: it lays `b` or `c` on the line `m_k` from `p(k, 0)`, unless it has
that `a`-edge and shows `γ` or `β` at the end of the run. -/
theorem K3G_of_next (C : CtxBase D e f α β γ L ax ay ε x) {k : ℕ} {t₀ : Fin N}
    (hU : HasV D t₀ (lpG (e : ℝ) (f : ℝ) ε x ((k : ℝ) - 1) 0) (lpG (e : ℝ) (f : ℝ) ε x ((k : ℝ) - 1 + 1) 0) (lpG (e : ℝ) (f : ℝ) ε x ((k : ℝ) - 1) (0 + 1)))
    (hint : openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x ((k : ℝ) - 1 + 1) 0) (lpG (e : ℝ) (f : ℝ) ε x ((k : ℝ) - 1) (0 + 1))
      ⊆ interior D.target.carrier)
    (hbad : ∀ (W : Fin N) (Z : Plane),
      HasV D W (lpG (e : ℝ) (f : ℝ) ε x ((k : ℝ) - 1 + 1) 0) (lpG (e : ℝ) (f : ℝ) ε x ((k : ℝ) - 1) (0 + 1)) Z →
      ((D.tile W).localAngle (lpG (e : ℝ) (f : ℝ) ε x ((k : ℝ) - 1 + 1) 0) = γ ∨
        (D.tile W).localAngle (lpG (e : ℝ) (f : ℝ) ε x ((k : ℝ) - 1 + 1) 0) = β) → 0 < Z 1 → False) :
    K3G D (e : ℝ) (f : ℝ) ε x (k : ℝ) 0 := by
  have hε := C.e2
  have he0 := C.S.e0
  have hef := C.S.hef'
  have hhp := hhG_pos he0 hef
  have hν0 := nuG_pos he0 hef
  rcases C.m_next_intGr (η := 0) ⟨0, Nat.cast_zero.symm⟩ hU hint (C.m_clamp_baseG _) with
    ⟨W, h⟩ | ⟨W, h⟩ | ⟨w, hw⟩
  · exfalso
    refine hbad W _ h (Or.inl (D_anglesG C.S hε h).1) ?_
    rw [lpG_snd]; linarith
  · exfalso
    refine hbad W _ h (Or.inr (N_anglesG C.S hε h).1) ?_
    rw [lpG_snd]; nlinarith [mul_pos hν0 hhp]
  · have e' : (k : ℝ) - 1 + 0 + 1 = k := by ring
    rw [e'] at hw
    exact Or.inr ⟨w, hw⟩

end CtxBase

/-! The full names `CtxG.m_next_intGr`, `CtxG.K3G_of_next` (cited in `PAPER_MAP.md`) are kept alive as corollaries over `CtxG`. -/

namespace CtxG

variable {e f : ℕ} {α β γ L ax ay ε x : ℝ}

/-- `CtxBase.m_next_intGr` for a `CtxG` (the old full name) -/
theorem m_next_intGr (C : CtxG D e f α β γ L ax ay ε x) {ξ η : ℝ} (hη : ∃ n : ℕ, η = n)
    {t₀ : Fin N} (hU : HasV D t₀ (lpG (e : ℝ) (f : ℝ) ε x ξ η) (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η) (lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1)))
    (hint : openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η) (lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1)) ⊆ interior D.target.carrier)
    (hcl : ClampedBelowG D (e : ℝ) (f : ℝ) ε x (ξ + η + 1) η) :
    (∃ t, HasV D t (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η) (lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1)) (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) (η + 1))) ∨
    (∃ t, HasV D t (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η) (lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1))
      (lpG (e : ℝ) (f : ℝ) ε x (ξ - nuG (e : ℝ) (f : ℝ)) (η + 2 + nuG (e : ℝ) (f : ℝ)))) ∨
    (∃ w, RhoEdgeG D (e : ℝ) (f : ℝ) ε x w (ξ + η + 1) η) :=
  C.toCtxBase.m_next_intGr hη hU hint hcl

/-- `CtxBase.K3G_of_next` for a `CtxG` (the old full name) -/
theorem K3G_of_next (C : CtxG D e f α β γ L ax ay ε x) {k : ℕ} {t₀ : Fin N}
    (hU : HasV D t₀ (lpG (e : ℝ) (f : ℝ) ε x ((k : ℝ) - 1) 0) (lpG (e : ℝ) (f : ℝ) ε x ((k : ℝ) - 1 + 1) 0) (lpG (e : ℝ) (f : ℝ) ε x ((k : ℝ) - 1) (0 + 1)))
    (hint : openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x ((k : ℝ) - 1 + 1) 0) (lpG (e : ℝ) (f : ℝ) ε x ((k : ℝ) - 1) (0 + 1))
      ⊆ interior D.target.carrier)
    (hbad : ∀ (W : Fin N) (Z : Plane),
      HasV D W (lpG (e : ℝ) (f : ℝ) ε x ((k : ℝ) - 1 + 1) 0) (lpG (e : ℝ) (f : ℝ) ε x ((k : ℝ) - 1) (0 + 1)) Z →
      ((D.tile W).localAngle (lpG (e : ℝ) (f : ℝ) ε x ((k : ℝ) - 1 + 1) 0) = γ ∨
        (D.tile W).localAngle (lpG (e : ℝ) (f : ℝ) ε x ((k : ℝ) - 1 + 1) 0) = β) → 0 < Z 1 → False) :
    K3G D (e : ℝ) (f : ℝ) ε x (k : ℝ) 0 :=
  C.toCtxBase.K3G_of_next hU hint hbad

end CtxG

end Erdos634.Draft.SideRunG

#print axioms Erdos634.Draft.SideRunG.SetupG.two_bg
#print axioms Erdos634.Draft.SideRunG.SetupG.three_beta
#print axioms Erdos634.Draft.SideRunG.SetupG.corner_two_alpha
#print axioms Erdos634.Draft.SideRunG.SetupG.corner_two_beta
#print axioms Erdos634.Draft.SideRunG.SetupG.hch_pos
#print axioms Erdos634.Draft.SideRunG.SetupG.hch_corner
#print axioms Erdos634.Draft.SideRunG.SetupG.K1_of_gamma
#print axioms Erdos634.Draft.SideRunG.SetupG.K1_of_corner
#print axioms Erdos634.Draft.SideRunG.SetupG.junction
#print axioms Erdos634.Draft.SideRunG.SetupG.out_right
#print axioms Erdos634.Draft.SideRunG.SetupG.K3G_out_right
#print axioms Erdos634.Draft.SideRunG.SetupG.K3G_out_left
#print axioms Erdos634.Draft.SideRunG.SetupG.bad_nb
#print axioms Erdos634.Draft.SideRunG.SetupG.bad_corner
#print axioms Erdos634.Draft.SideRunG.CtxBase.m_next_intGr
#print axioms Erdos634.Draft.SideRunG.CtxG.m_next_intGr
#print axioms Erdos634.Draft.SideRunG.CtxBase.K3G_of_next
#print axioms Erdos634.Draft.SideRunG.CtxG.K3G_of_next
