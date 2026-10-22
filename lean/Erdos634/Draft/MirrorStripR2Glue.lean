-- Draft/MirrorStripR2Glue.lean — R2 ((private working notes, not included)), part (B): the geometric
-- NOTE 2026-09-30 (audit): the `sorry`s in this file (see below) are NOT in the dependency cone of
-- `theorem_H_real`/`theoremP_6`; the chain uses the `*Real` re-proofs (kernel-checked: no sorryAx).
-- Statements below that say 'inherits sorryAx' refer to the glue-based versions only.
-- glue specific to R2, STATED.  G1, G2 are `sorry`-bodied; G4 (`base_is_junction`) is PROVED; G3
-- (`band_junction_rep`) is PROVED 2026-09-24 from `Draft/TraceCovering.wall_sum` (trace covering,
-- one side) + `near_interior_of_across` (no band edge through P′: `T₂` lies across `L`).
-- Build: scratch olean for Draft/TraceCovering, then
--   lake env bash -c 'LEAN_PATH=$S:$LEAN_PATH lean Erdos634/Draft/MirrorStripR2Glue.lean'
-- `mirror_impossible` is the ASSEMBLY: it is proved from G1–G4 and Lemma A
-- (`Inflation.c_side_no_b`), so it checks that the four glue statements compose to R2's
-- conclusion, and its `#print axioms` shows `sorryAx` (inherited from G1–G4) — it is NOT a proof of R2.
-- Not imported by All.lean.
--
-- The metric hypotheses of `R2Frame` are exactly the facts `Draft/MirrorStripR2.lean` proves for its
-- coordinate points (`pP`, `pV`, `pJ`, `pQ`, `pAstar`, `sides_of_L`, `pQ_on_base_iff`, ...), which is
-- the witness that the metric part of the frame is satisfiable.  The presence fields `hT2`, `hT3`,
-- `hMir` are the (M)-branch assumption; R2's content is that they are jointly impossible at m = 1.
import Erdos634.MarchSlots
import Erdos634.LineParam
import Erdos634.Inflation
import Erdos634.Draft.TraceCovering

namespace Erdos634.Draft.MirrorStripR2Glue

open Erdos634.Geometry Erdos634.TilePlacement

/-- Some tile of `D` has exactly the vertex set `S`. -/
def Present {N : ℕ} (D : CongruentDissection N) (S : Set Plane) : Prop :=
  ∃ i, Set.range (D.tile i).pts = S

/-- General-`e` model data (`MarchKillsFan.ModelData` is the `e = 1` case, sides `f, f²−1, f²`). -/
structure ModelDataE {N : ℕ} (D : CongruentDissection N) (e f α β γ : ℝ) : Prop where
  hs0 : sideOpp D.model 0 = e * f
  hs1 : sideOpp D.model 1 = f ^ 2 - e ^ 2
  hs2 : sideOpp D.model 2 = f ^ 2
  hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α
  hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β
  hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ

/-- Every tile edge of `D` has length `a`, `b` or `c` (congruence to the model; `sideOpp` values). -/
theorem edge_len_mem {N : ℕ} (D : CongruentDissection N) {a b c : ℝ}
    (hs0 : sideOpp D.model 0 = a) (hs1 : sideOpp D.model 1 = b) (hs2 : sideOpp D.model 2 = c)
    (i : Fin N) (k : Fin 3) :
    dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = a ∨
    dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = b ∨
    dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = c := by
  obtain ⟨j, -, hd⟩ :=
    Erdos634.CornerBaseEdgesReal.congruent_opposite_side (D.tiles_congruent i).symm (k + 2)
  have h1 : k + 2 + 1 = k := by fin_cases k <;> rfl
  have h2 : k + 2 + 2 = k + 1 := by fin_cases k <;> rfl
  rw [h1, h2] at hd
  have hd' : sideOpp D.model j = dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) := hd
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
  rcases hj with rfl | rfl | rfl
  · left; rw [← hd', hs0]
  · right; left; rw [← hd', hs1]
  · right; right; rw [← hd', hs2]


/-- **The (M) configuration at the pierced corner, m = 1.**  `A` apex, `uL` the unit direction of
the leg on `T₃`'s side (downward), `J k = A + k·c·uL` the leg points (`J f` the base corner),
`P = P′` (distance `b` from `A` on the inner ray next to that leg), `Q k = P′ + k·c·uL` the points of
the line `L`, `A* = P′ + b·uL`.  `g` is a normal functional of `L`: the strip (leg) side is
`{g < g P′}`, the band side (containing `V`, hence `M`) is `{g > g P′}`. -/
structure R2Frame {N : ℕ} (D : CongruentDissection N) (e f : ℕ) (α β γ : ℝ) where
  A : Plane
  P : Plane
  V : Plane
  R : Plane
  uL : Plane
  g : Plane →ₗ[ℝ] ℝ
  -- the member
  hco : Nat.Coprime e f
  he : 1 ≤ e
  hef : e < f
  hM : ModelDataE D e f α β γ
  hA : MarchSlots.AngleData α β γ
  -- the target: apex `A`, base corners `J f = A + f³·uL` and `R`, legs `f³`
  htarget : Set.range D.target.pts = {A, A + ((f : ℝ) ^ 3) • uL, R}
  hlegR : dist A R = (f : ℝ) ^ 3
  -- metric frame (witnessed by `Draft.MirrorStripR2`)
  huL : ‖uL‖ = 1
  hAP : dist A P = (f : ℝ) ^ 2 - (e : ℝ) ^ 2
  hAV : dist A V = (f : ℝ) ^ 2
  hVP : dist V P = (e : ℝ) * f
  hPJ1 : dist P (A + ((f : ℝ) ^ 2) • uL) = (e : ℝ) * f
  hg0 : g ≠ 0
  hguL : g uL = 0
  hgV : g P < g V
  hgA : g A < g P
  -- `L` leaves the target at `Q (f−1)` (`MirrorStripR2.pQ_on_base_iff`, `Qbase_on_base`)
  hbase : ∀ t : ℝ, 0 < t → P + (((f : ℝ) - 1) * (f : ℝ) ^ 2 + t) • uL ∉ D.target.carrier
  -- the open segment `(P′, Q (f−1))` is interior to the target (it runs at horizontal distance `a`
  -- from the leg, `MirrorStripR2.pQ_eq_pJ_add`, and above the base)
  hLint : ∀ t : ℝ, 0 < t → t < ((f : ℝ) - 1) * (f : ℝ) ^ 2 → P + t • uL ∈ interior D.target.carrier
  -- the apex tiles and the mirror branch (M)
  hT2 : Present D {A, V, P}
  hT3 : Present D {A, P, A + ((f : ℝ) ^ 2) • uL}
  hMir : Present D {V, P, P + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • uL}

namespace R2Frame

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ}

/-- Leg point `J k = A + k·c·uL`. -/
noncomputable def J (F : R2Frame D e f α β γ) (k : ℕ) : Plane := F.A + ((k : ℝ) * (f : ℝ) ^ 2) • F.uL
/-- Point `Q k = P′ + k·c·uL` of the line `L`. -/
noncomputable def Q (F : R2Frame D e f α β γ) (k : ℕ) : Plane := F.P + ((k : ℝ) * (f : ℝ) ^ 2) • F.uL
/-- Strip cell `Z k = (Q k, J (k+1), Q (k+1))`: `β` at `Q k`, `γ` at `J (k+1)`, `α` at `Q (k+1)`. -/
noncomputable def Z (F : R2Frame D e f α β γ) (k : ℕ) : Set Plane := {F.Q k, F.J (k + 1), F.Q (k + 1)}
/-- Strip cell `Z′ k = (J (k+1), J (k+2), Q (k+1))`: `α`, `β`, `γ`. -/
noncomputable def Z' (F : R2Frame D e f α β γ) (k : ℕ) : Set Plane := {F.J (k + 1), F.J (k + 2), F.Q (k + 1)}
/-- The band-side chain of `L`: tile edges on `L` whose tile lies in `{g ≥ g P′}`. -/
noncomputable def band (F : R2Frame D e f α β γ) : Finset (Fin N × Fin 3) :=
  D.toDissection.lineChain (-F.g) (-(F.g F.P))

/-- `X` lies in the relative interior of the chain edge `ε`. -/
def Straddles (X : Plane) (ε : Fin N × Fin 3) : Prop :=
  X ∈ openSegment ℝ ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1))

/-! ## The glue (STATED) -/

-- [G5SORRY 2026-10-01] removed sorry-bodied glue statement `strip_base` (unused; real proof in the *Real/primed files).

-- [G5SORRY 2026-10-01] removed sorry-bodied glue statement `strip_step` (unused; real proof in the *Real/primed files).

/-- **G3 — the band-side trace covering of `[P′, Q k]`.**  **PROVED 2026-09-24** (no `sorry`):
`TraceCovering.wall_sum` on `L` from `P′` to `Q k` (wall: the strip cells' `c`-edges; start: `T₂`
has `A`, `V` strictly on the two sides of `L`, `TraceCovering.near_interior_of_across`; end: `hjunc`),
`M`'s `b`-edge in the band chain, edge lengths in `{a,b,c}` (`edge_len_mem`), `sum_three_values`.
Original note:  With the strip present below `Q k`, the
open segment `(P′, Q k)` is a wall (each point is on an edge of some `Z j`), the band-side chain covers
it exactly once, it starts at `P′` with `M`'s `b`-edge `[P′, A*]` (no band edge straddles `P′`: `L`
above `P′` runs inside `T₂`), and if `Q k` is a band junction (no band edge straddles it) the band
edges inside `[P′, Q k]` are whole, of lengths in `{a, b, c}`, summing to `k·c`, with at least one `b`.
Corpus: `LineParam.lineChain_param_sum` on `(u, v) = (P′, Q k)` for the band chain
`lineChain (−g) (−g P′)` (its hypotheses: `hS` from `g uL = 0`; `hwall` from the strip — each point of
`(P′, Q k)` is on `Z j`'s `c`-edge, `SideWall.edge_subset_frontier` + `interiors_disjoint`; `hint`
from the field `hLint`), `edgeParam_spec`, `Dissection.contact_is_edge`,
`IntervalChain.chain_of_cover` (ordering, if wanted), congruent edge lengths (`CongruentAngles` /
`sideOpp`).  NO BLOCKER: with neither end straddled, each band edge's trace on `[P′, Q k]` is the whole
edge or at most one point (collinear 1-D dichotomy), so `lineChain_param_sum` itself gives
`Σ (lengths of the edges inside) = k·c`; `M`'s `b`-edge `[P′, A*]` is one of them (`g V > g P′`).
Estimate 220–320 lines of plumbing (wall-from-strip ≈ 40, trace dichotomy ≈ 80, M's edge in the chain
≈ 40, real sum → `(n_a, n_b, n_c)` ≈ 40).  Shared with R1's G1
(`ThickEFminus1Glue.far_edge_through_V`), whose "MISSING" note is the contrapositive of the same
dichotomy. -/
theorem band_junction_rep (F : R2Frame D e f α β γ) (k : ℕ) (hk1 : 1 ≤ k) (hkf : k ≤ f - 1)
    (hprev : ∀ j < k, Present D (F.Z j) ∧ Present D (F.Z' j))
    (hjunc : ∀ ε ∈ F.band, ¬ Straddles (D := D) (F.Q k) ε) :
    ∃ na nb nc : ℕ, 1 ≤ nb ∧ na * (e * f) + nb * (f ^ 2 - e ^ 2) + nc * f ^ 2 = k * f ^ 2 := by
  classical
  have hef := F.hef
  have hu1 : ‖F.uL‖ = 1 := F.huL
  have hu0 : F.uL ≠ 0 := TraceCovering.ne_zero_of_norm hu1
  have hg' : (-F.g : Plane →ₗ[ℝ] ℝ) ≠ 0 := fun h => F.hg0 (neg_eq_zero.mp h)
  have hgd : ∀ y, (-F.g) y = -(F.g F.P) ↔ F.g y = F.g F.P := TraceCovering.neg_iff
  have hcR : (0 : ℝ) < (f : ℝ) ^ 2 := by
    have : (0 : ℝ) < f := by exact_mod_cast (show 0 < f by omega)
    positivity
  set t : ℝ := (k : ℝ) * (f : ℝ) ^ 2 with ht
  have hkfR : (k : ℝ) ≤ (f : ℝ) - 1 := by
    have h1 : k + 1 ≤ f := by omega
    have h2 : ((k + 1 : ℕ) : ℝ) ≤ f := by exact_mod_cast h1
    push_cast at h2; linarith
  have ht0 : 0 ≤ t := by positivity
  have hP0 : F.P + (0 : ℝ) • F.uL = F.P := by rw [zero_smul, add_zero]
  have hQ : ∀ j : ℕ, F.Q j = F.P + ((j : ℝ) * (f : ℝ) ^ 2) • F.uL := fun j => rfl
  -- (i) the open stretch `(P′, Q k)` is interior to the target
  have hint : ∀ x ∈ Set.Ioo 0 t, F.P + x • F.uL ∈ interior D.target.carrier := fun x hx =>
    F.hLint x hx.1 (lt_of_lt_of_le hx.2 (mul_le_mul_of_nonneg_right hkfR hcR.le))
  -- (ii) it is a wall: each point lies on the `c`-edge `[Q j, Q (j+1)]` of the strip cell `Z j`
  have hwall : ∀ x ∈ Set.Ioo 0 t, ∀ i, F.P + x • F.uL ∉ interior (D.tile i).carrier := by
    intro x hx i
    set j := ⌊x / (f : ℝ) ^ 2⌋₊ with hj
    have hq0 : 0 ≤ x / (f : ℝ) ^ 2 := div_nonneg hx.1.le hcR.le
    have hj1 : (j : ℝ) ≤ x / (f : ℝ) ^ 2 := Nat.floor_le hq0
    have hj2 : x / (f : ℝ) ^ 2 < (j : ℝ) + 1 := Nat.lt_floor_add_one _
    have hjx : (j : ℝ) * (f : ℝ) ^ 2 ≤ x := by rwa [le_div_iff₀ hcR] at hj1
    have hxj : x < ((j : ℝ) + 1) * (f : ℝ) ^ 2 := by rwa [div_lt_iff₀ hcR] at hj2
    have hjk : j < k := by
      have h1 : (j : ℝ) * (f : ℝ) ^ 2 < (k : ℝ) * (f : ℝ) ^ 2 := lt_of_le_of_lt hjx hx.2
      exact_mod_cast lt_of_mul_lt_mul_right h1 hcR.le
    obtain ⟨iz, hiz⟩ := (hprev j hjk).1
    obtain ⟨k0, hk0⟩ := MarchInduction.mem_range_of_eq hiz
      (show F.Q j ∈ F.Z j by simp [R2Frame.Z])
    obtain ⟨k1, hk1'⟩ := MarchInduction.mem_range_of_eq hiz
      (show F.Q (j + 1) ∈ F.Z j by simp [R2Frame.Z])
    have hQne : F.Q j ≠ F.Q (j + 1) := by
      rw [hQ, hQ]; intro h
      have h' := TraceCovering.lm_injective hu0 h
      push_cast at h'
      nlinarith
    have hkne : k0 ≠ k1 := by rintro rfl; exact hQne (hk0.symm.trans hk1')
    obtain ⟨m, hm⟩ := (D.tile iz).pair_eq_edge hkne
    have hmem : F.P + x • F.uL ∈ (D.tile iz).edge m := by
      rw [← hm, hk0, hk1', hQ, hQ, TraceCovering.segment_param]
      refine ⟨x, ⟨?_, ?_⟩, rfl⟩
      · push_cast; exact le_trans (min_le_left _ _) hjx
      · push_cast; exact le_trans hxj.le (le_max_right _ _)
    exact D.toDissection.edge_point_not_interior hmem i
  -- (iii) no band edge passes through `P′`: `T₂` has `A` and `V` strictly on the two sides of `L`
  have hs : ¬ TraceCovering.Straddled D.toDissection (-F.g) (-(F.g F.P))
      (F.P + (0 : ℝ) • F.uL) := by
    obtain ⟨i2, h2⟩ := F.hT2
    have hmemT : ∀ y ∈ ({F.A, F.V, F.P} : Set Plane), y ∈ (D.tile i2).carrier := by
      intro y hy; rw [← h2] at hy; obtain ⟨k, rfl⟩ := hy
      exact subset_convexHull ℝ _ ⟨k, rfl⟩
    refine TraceCovering.not_straddled_of_near_interior hgd F.hg0 rfl F.hguL hu0 ?_
    intro δ hδ
    obtain ⟨x, hx, hxi⟩ := TraceCovering.near_interior_of_across (D.tile i2) F.hg0 rfl F.hguL hu0
      (by rw [hP0]; exact hmemT _ (by simp)) (hmemT F.A (by simp)) (hmemT F.V (by simp))
      F.hgA F.hgV δ hδ
    exact ⟨x, hx, i2, hxi⟩
  -- (iv) no band edge passes through `Q k` (hypothesis)
  have ht' : ¬ TraceCovering.Straddled D.toDissection (-F.g) (-(F.g F.P)) (F.P + t • F.uL) := by
    rintro ⟨ε, hε, hstr⟩; exact hjunc ε hε hstr
  -- TRACE COVERING, one side: the whole band edges in `[P′, Q k]` sum to `k·c`
  have hsum := TraceCovering.wall_sum (D := D.toDissection) hg' hgd F.hg0 rfl F.hguL hu1 ht0
    hint hwall hs ht'
  -- (v) `M`'s `b`-edge `[P′, P′ + b·uL]` is one of them
  obtain ⟨iM, hiM⟩ := F.hMir
  set Bp := F.P + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uL with hBp
  have hr' : Set.range (D.tile iM).pts = {F.P, F.V, Bp} := by
    rw [hiM]; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  obtain ⟨kP, hkP⟩ := MarchInduction.mem_range_of_eq hr' (Set.mem_insert _ _)
  have hfin1 : kP + 2 + 1 = kP := by fin_cases kP <;> rfl
  have hfin2 : kP + 2 + 2 = kP + 1 := by fin_cases kP <;> rfl
  obtain ⟨m, hm01, hm2⟩ : ∃ m : Fin 3,
      (((D.tile iM).pts m = F.P ∧ (D.tile iM).pts (m + 1) = Bp) ∨
        ((D.tile iM).pts m = Bp ∧ (D.tile iM).pts (m + 1) = F.P)) ∧
      (D.tile iM).pts (m + 2) = F.V := by
    rcases MarchInduction.vertex_data_of_range hr' hkP with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨kP + 2, Or.inr ⟨h2, by rw [hfin1, hkP]⟩, by rw [hfin2, h1]⟩
    · exact ⟨kP, Or.inl ⟨hkP, h1⟩, h2⟩
  have hgB : F.g Bp = F.g F.P := TraceCovering.f_param rfl F.hguL _
  have hb0 : (0 : ℝ) ≤ (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have : (e : ℝ) ≤ f := by exact_mod_cast hef.le
    nlinarith [(Nat.cast_nonneg e : (0 : ℝ) ≤ e)]
  have hbt : (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ≤ t := by
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    nlinarith [sq_nonneg (e : ℝ)]
  have heM : (iM, m) ∈ D.toDissection.lineChain (-F.g) (-(F.g F.P)) := by
    rw [Dissection.mem_lineChain]
    have h3 : ∀ i m : Fin 3, i = m ∨ i = m + 1 ∨ i = m + 2 := by decide
    have hPl : ∀ y, y = F.P ∨ y = Bp → (-F.g) y = -(F.g F.P) := by
      rintro y (rfl | rfl) <;> simp [hgB]
    refine ⟨?_, ?_, fun i => ?_⟩
    · rcases hm01 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> simp [hgB]
    · rcases hm01 with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> simp [hgB]
    · rcases h3 i m with rfl | rfl | rfl
      · rcases hm01 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> simp [hgB]
      · rcases hm01 with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> simp [hgB]
      · rw [hm2]; simp only [LinearMap.neg_apply, neg_le_neg_iff]; exact F.hgV.le
  have hSeg : ∀ y, y = F.P ∨ y = Bp →
      y ∈ segment ℝ (F.P + (0 : ℝ) • F.uL) (F.P + t • F.uL) := by
    rintro y (rfl | rfl)
    · convert left_mem_segment ℝ (F.P + (0 : ℝ) • F.uL) (F.P + t • F.uL) using 1
      exact hP0.symm
    · rw [TraceCovering.segment_param, min_eq_left ht0, max_eq_right ht0]
      exact ⟨_, ⟨hb0, hbt⟩, rfl⟩
  have hin : (D.tile iM).edge m ⊆ segment ℝ (F.P + (0 : ℝ) • F.uL) (F.P + t • F.uL) := by
    rw [Tri.edge]
    rcases hm01 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
      exact (convex_segment _ _).segment_subset (hSeg _ (by simp)) (hSeg _ (by simp))
  have hdM : dist ((D.tile iM).pts m) ((D.tile iM).pts (m + 1)) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have hdb : dist F.P Bp = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
      rw [hBp, dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, hu1, mul_one,
        Real.norm_of_nonneg hb0]
    rcases hm01 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact hdb
    · rw [dist_comm]; exact hdb
  set s := (D.toDissection.lineChain (-F.g) (-(F.g F.P))).filter
    (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ (F.P + (0 : ℝ) • F.uL) (F.P + t • F.uL)) with hs_def
  have hmemS : (iM, m) ∈ s := Finset.mem_filter.mpr ⟨heM, hin⟩
  rw [← Finset.add_sum_erase s _ hmemS] at hsum
  obtain ⟨P', Q', R', hPQR, -⟩ := sum_three_values (s.erase (iM, m))
    (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
    ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)
    (fun ε _ => edge_len_mem D F.hM.hs0 F.hM.hs1 F.hM.hs2 ε.1 ε.2)
  refine ⟨P', Q' + 1, R', by omega, ?_⟩
  have hee : e ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left hef.le 2
  have hreal : ((P' * (e * f) + (Q' + 1) * (f ^ 2 - e ^ 2) + R' * f ^ 2 : ℕ) : ℝ)
      = ((k * f ^ 2 : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hee]
    simp only at hsum hdM
    rw [hdM] at hsum
    linarith
  exact_mod_cast hreal

/-- **G4 — step 4: `Q (f−1)` is on the base, so no edge on `L` straddles it.**  An edge of `L` with
`Q (f−1)` in its relative interior has an endpoint `Q (f−1) + t·uL`, `t > 0`, outside the target
(`hbase`), against `Dissection.tile_subset_target`.  Corpus: `tile_subset_target`,
`lineChain_edge_subset`, collinear parametrization (`LineParam.lineMap_injective_of_ne`).  Estimate
40–80 lines; no blocker. -/
theorem base_is_junction (F : R2Frame D e f α β γ) :
    ∀ ε ∈ F.band, ¬ Straddles (D := D) (F.Q (f - 1)) ε := by
  intro ε hε hstr
  have hε' : ε ∈ D.toDissection.lineChain (-F.g) (-(F.g F.P)) := hε
  obtain ⟨h0, h1, -⟩ := Dissection.mem_lineChain.mp hε'
  have hmem : ∀ k, (D.tile ε.1).pts k ∈ D.target.carrier := fun k =>
    tile_subset_target D.toDissection ε.1 (subset_convexHull ℝ _ (Set.mem_range_self k))
  have hne : (D.tile ε.1).pts ε.2 ≠ (D.tile ε.1).pts (ε.2 + 1) :=
    pts_ne _ (by have : ∀ x : Fin 3, x ≠ x + 1 := by decide
                 exact this _)
  unfold Straddles at hstr
  generalize hp0 : (D.tile ε.1).pts ε.2 = p0 at h0 hstr hne
  generalize hp1 : (D.tile ε.1).pts (ε.2 + 1) = p1 at h1 hstr hne
  rw [LinearMap.neg_apply] at h0 h1
  have hg0 : F.g p0 = F.g F.P := by linarith
  have hg1 : F.g p1 = F.g F.P := by linarith
  -- `ker g` is the line spanned by `uL`
  have huL0 : F.uL ≠ 0 := by
    intro h; have := F.huL; rw [h, norm_zero] at this; exact zero_ne_one this
  have hker : ∀ w, F.g w = 0 → ∃ s : ℝ, s • F.uL = w := by
    have hrank := LinearMap.finrank_range_add_finrank_ker F.g
    have hdim : Module.finrank ℝ Plane = 2 := finrank_euclideanSpace_fin
    have hrange : Module.finrank ℝ (LinearMap.range F.g) = 1 := by
      have htop : LinearMap.range F.g = ⊤ := by
        obtain ⟨v, hv⟩ : ∃ v, F.g v ≠ 0 := by
          by_contra h; push_neg at h; exact F.hg0 (LinearMap.ext h)
        rw [eq_top_iff]; intro r _
        exact ⟨(r / F.g v) • v, by simp [hv]⟩
      rw [htop, finrank_top, Module.finrank_self]
    have hk1 : Module.finrank ℝ (LinearMap.ker F.g) = 1 := by omega
    intro w hw
    obtain ⟨s, hs⟩ := (finrank_eq_one_iff_of_nonzero'
      (⟨F.uL, LinearMap.mem_ker.mpr F.hguL⟩ : LinearMap.ker F.g)
      (by simpa using huL0)).mp hk1 ⟨w, LinearMap.mem_ker.mpr hw⟩
    exact ⟨s, by simpa using congrArg Subtype.val hs⟩
  have hline : ∀ y, F.g y = F.g F.P → ∃ s : ℝ, y = F.P + s • F.uL := by
    intro y hy
    obtain ⟨s, hs⟩ := hker (y - F.P) (by rw [map_sub, hy, sub_self])
    exact ⟨s, by rw [hs]; abel⟩
  obtain ⟨s0, hs0⟩ := hline p0 hg0
  obtain ⟨s1, hs1⟩ := hline p1 hg1
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = ((f - 1 : ℕ) : ℝ) * (f : ℝ) ^ 2 := ⟨_, rfl⟩
  obtain ⟨a, b, ha, hb, hab, hQ⟩ := hstr
  unfold R2Frame.Q at hQ
  rw [← hqdef, hs0, hs1] at hQ
  have hq : a * s0 + b * s1 = q := by
    have e1 : a • (F.P + s0 • F.uL) + b • (F.P + s1 • F.uL)
        = (a + b) • F.P + (a * s0 + b * s1) • F.uL := by module
    rw [e1, hab, one_smul] at hQ
    exact smul_left_injective ℝ huL0 (add_left_cancel hQ)
  have hs01 : s0 ≠ s1 := fun h => hne (by rw [hs0, hs1, h])
  have hf1 : 1 ≤ f := by have := F.hef; omega
  have hqv : q = ((f : ℝ) - 1) * (f : ℝ) ^ 2 := by
    rw [hqdef, Nat.cast_sub hf1, Nat.cast_one]
  have hbeyond : q < s0 ∨ q < s1 := by
    by_contra hc
    push_neg at hc
    obtain ⟨hc0, hc1⟩ := hc
    rcases lt_or_gt_of_ne hs01 with h | h
    · have k1 := mul_lt_mul_of_pos_left h ha
      have k2 : a * s1 + b * s1 = s1 := by rw [← add_mul, hab, one_mul]
      linarith
    · have k1 := mul_lt_mul_of_pos_left h hb
      have k2 : a * s0 + b * s0 = s0 := by rw [← add_mul, hab, one_mul]
      linarith
  rcases hbeyond with h | h
  · apply F.hbase (s0 - q) (by linarith)
    have : F.P + (((f : ℝ) - 1) * (f : ℝ) ^ 2 + (s0 - q)) • F.uL = p0 := by
      rw [hs0, ← hqv]; congr 2; ring
    rw [this, ← hp0]; exact hmem ε.2
  · apply F.hbase (s1 - q) (by linarith)
    have : F.P + (((f : ℝ) - 1) * (f : ℝ) ^ 2 + (s1 - q)) • F.uL = p1 := by
      rw [hs1, ← hqv]; congr 2; ring
    rw [this, ← hp1]; exact hmem (ε.2 + 1)

/-! ## The assembly (proved from G1–G4 and Lemma A) -/

-- [G5SORRY 2026-10-01] removed sorry-bodied glue statement `mirror_impossible` (unused; real proof in the *Real/primed files).

end R2Frame

end Erdos634.Draft.MirrorStripR2Glue

#print axioms Erdos634.Draft.MirrorStripR2Glue.edge_len_mem
#print axioms Erdos634.Draft.MirrorStripR2Glue.R2Frame.band_junction_rep
#print axioms Erdos634.Draft.MirrorStripR2Glue.R2Frame.base_is_junction
