-- Draft/HalfTurnR3R4Glue.lean — the GEOMETRIC glue of room HB's R3 and R4, STATED.
-- NOTE 2026-09-30 (audit): the `sorry`s in this file (see below) are NOT in the dependency cone of
-- `theorem_H_real`/`theoremP_6`; the chain uses the `*Real` re-proofs (kernel-checked: no sorryAx).
-- Statements below that say 'inherits sorryAx' refer to the glue-based versions only.
-- `ray_whole_edge_runs` (G-R3) is PROVED 2026-09-24 from `Draft/TraceCovering.trace_covering`
-- (two-sided trace covering to the first common junction), so `r3_assembly` is now sorry-free.
-- Every other `G-*` theorem below is `sorry`-bodied EXCEPT `corners_at_pprime` (PROVED 2026-09-24, with
-- the general-`e` plumbing `localAngle_of_oppSideE`, `localAngle_of_rangeE`, `sides_distinct`,
-- `dist_self_add_unit`); nothing else in them is claimed proved.  The two ASSEMBLY
-- theorems (`r3_assembly`, `r4_figure_at_pprime`) are proved from the glue + the arithmetic of
-- Draft/HalfTurnR3R4.lean + corpus; their `#print axioms` shows `sorryAx` inherited from the glue —
-- they check that the glue composes to the room's conclusions, and are NOT proofs of R3 / R4.
-- Not imported by All.lean.
--
-- Build: Draft/HalfTurnR3R4 and Draft/TraceCovering have no olean in .lake; compile them to scratch
-- oleans first (`$S` = a full scratch copy of the corpus oleans, never .lake):
--   lake env lean -o $S/Erdos634/Draft/HalfTurnR3R4.olean Erdos634/Draft/HalfTurnR3R4.lean
--   lake env lean -o $S/Erdos634/Draft/TraceCovering.olean Erdos634/Draft/TraceCovering.lean
--   lake env bash -c 'LEAN_PATH=$S:$LEAN_PATH lean Erdos634/Draft/HalfTurnR3R4Glue.lean'
--
-- Frame conventions follow Draft/MirrorStripR2Glue.lean (`Present`, `ModelDataE`, the R2 metric
-- fields, whose satisfiability is witnessed by the coordinates of Draft/MirrorStripR2.lean).  The
-- presence fields (`hT1`, `hT2`, `hT3`) are the output of apex placement (`thm:pierce(i)`, the
-- PAPER_MAP "tile-placement layer" blocker); `Present D K` is the branch (H) assumption.  A frame
-- contains an m = 1 dissection, so it cannot be witnessed outright: that impossibility is the goal.
import Erdos634.MarchSlots
import Erdos634.LineParam
import Erdos634.Inflation
import Erdos634.WallChain
import Erdos634.VertexFigureReal
import Erdos634.CornerAnglePerm
import Erdos634.Draft.HalfTurnR3R4
import Erdos634.Draft.TraceCovering

namespace Erdos634.Draft.HalfTurnR3R4Glue

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.HalfTurnR3R4

/-- Some tile of `D` has exactly the vertex set `S` (as in `MirrorStripR2Glue`). -/
def Present {N : ℕ} (D : CongruentDissection N) (S : Set Plane) : Prop :=
  ∃ i, Set.range (D.tile i).pts = S

/-- General-`e` model data (as in `MirrorStripR2Glue`). -/
structure ModelDataE {N : ℕ} (D : CongruentDissection N) (e f α β γ : ℝ) : Prop where
  hs0 : sideOpp D.model 0 = e * f
  hs1 : sideOpp D.model 1 = f ^ 2 - e ^ 2
  hs2 : sideOpp D.model 2 = f ^ 2
  hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α
  hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β
  hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ

/-- The chain edge `ε` has endpoints `p`, `q`. -/
def EdgeIs {N : ℕ} (D : CongruentDissection N) (ε : Fin N × Fin 3) (p q : Plane) : Prop :=
  ({(D.tile ε.1).pts ε.2, (D.tile ε.1).pts (ε.2 + 1)} : Set Plane) = {p, q}

/-- `M` is the mirror image of `V` across the line `XY` (the other point at the same distances). -/
def IsMirror (V X Y M : Plane) : Prop := M ≠ V ∧ dist M X = dist V X ∧ dist M Y = dist V Y

/-- **The apex frame of branch (H), m = 1.**  `A` apex; `uL` the unit direction of `T₃`'s leg
(base corner `A + f³·uL`), `R` the other base corner; `uR` the unit direction of the mismatch ray
`r`; `V = A + c·uR` (end of `T₂`'s `c`-edge on `r`); `P = P′` (end of the `b`-edges of `T₂`, `T₃` on
the inner ray `ρ₁`); `h` a normal functional of `r` with `T₂`'s side (near side) `{h < h A}` and
`T₁`'s side (far side, containing `R`) `{h > h A}`.  `r` meets the base at distance `f·b`. -/
structure HFrame {N : ℕ} (D : CongruentDissection N) (e f : ℕ) (α β γ : ℝ) where
  A : Plane
  V : Plane
  P : Plane
  R : Plane
  uL : Plane
  uR : Plane
  h : Plane →ₗ[ℝ] ℝ
  -- the member: m = 1, coprime 2 ≤ e ≤ f − 2
  hco : Nat.Coprime e f
  he : 2 ≤ e
  hef : e + 2 ≤ f
  hM : ModelDataE D e f α β γ
  hAng : MarchSlots.AngleData α β γ
  -- the target
  htarget : Set.range D.target.pts = {A, A + ((f : ℝ) ^ 3) • uL, R}
  hlegR : dist A R = (f : ℝ) ^ 3
  -- metric frame (R2's, witnessed by `Draft.MirrorStripR2`)
  huL : ‖uL‖ = 1
  huR : ‖uR‖ = 1
  hV : V = A + ((f : ℝ) ^ 2) • uR
  hAP : dist A P = (f : ℝ) ^ 2 - (e : ℝ) ^ 2
  hVP : dist V P = (e : ℝ) * f
  hPJ1 : dist P (A + ((f : ℝ) ^ 2) • uL) = (e : ℝ) * f
  hh0 : h ≠ 0
  hhuR : h uR = 0
  hhP : h P < h A
  hhR : h A < h R
  -- `r` leaves the target at distance `f·b` and runs inside it before that
  hrbase : ∀ t : ℝ, 0 < t →
    A + ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + t) • uR ∉ D.target.carrier
  hrint : ∀ t : ℝ, 0 < t → t < (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) →
    A + t • uR ∈ interior D.target.carrier
  hPint : P ∈ interior D.target.carrier
  -- the apex tiles (thm:pierce(i) placement)
  hT1 : Present D {A, A + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • uR, A + (1 / (f : ℝ)) • (R - A)}
  hT2 : Present D {A, V, P}
  hT3 : Present D {A, P, A + ((f : ℝ) ^ 2) • uL}

/-! ## Plumbing for `corners_at_pprime` (added 2026-09-24; PROVED, no `sorry`)

General-side-value ports of `MarchKillsFan.localAngle_of_oppSide` / `MarchSlots.localAngle_of_range`
(which are stated for `e = 1`, sides `f, f²−1, f²`): with the model's opposite sides `a, b, c`
pairwise distinct, a tile's local angle at a vertex is read off the opposite side. -/

theorem localAngle_of_oppSideE {N : ℕ} (D : CongruentDissection N) {a b c α β γ : ℝ}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hs0 : sideOpp D.model 0 = a) (hs1 : sideOpp D.model 1 = b) (hs2 : sideOpp D.model 2 = c)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (i : Fin N) (j : Fin 3) :
    (dist ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 2)) = a →
      (D.tile i).localAngle ((D.tile i).pts j) = α) ∧
    (dist ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 2)) = b →
      (D.tile i).localAngle ((D.tile i).pts j) = β) ∧
    (dist ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 2)) = c →
      (D.tile i).localAngle ((D.tile i).pts j) = γ) := by
  rw [Tri.localAngle_vertex]
  obtain ⟨k, hk, hd⟩ :=
    Erdos634.CornerBaseEdgesReal.congruent_opposite_side (D.tiles_congruent i).symm j
  rw [hk]
  simp only [sideOpp] at hs0 hs1 hs2
  fin_cases k <;> simp at hd hs0 hs1 hs2 ⊢
  · refine ⟨fun _ => hα', fun h => ?_, fun h => ?_⟩
    · exact absurd (hs0.symm.trans (hd.trans h)) hab
    · exact absurd (hs0.symm.trans (hd.trans h)) hac
  · refine ⟨fun h => ?_, fun _ => hβ', fun h => ?_⟩
    · exact absurd (hs1.symm.trans (hd.trans h)) hab.symm
    · exact absurd (hs1.symm.trans (hd.trans h)) hbc
  · refine ⟨fun h => ?_, fun h => ?_, fun _ => hγ'⟩
    · exact absurd (hs2.symm.trans (hd.trans h)) hac.symm
    · exact absurd (hs2.symm.trans (hd.trans h)) hbc.symm

/-- **Local angle read off a vertex set** (general side values). -/
theorem localAngle_of_rangeE {N : ℕ} (D : CongruentDissection N) {a b c α β γ : ℝ}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hs0 : sideOpp D.model 0 = a) (hs1 : sideOpp D.model 1 = b) (hs2 : sideOpp D.model 2 = c)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    {i : Fin N} {P Q R : Plane} (hr : Set.range (D.tile i).pts = {P, Q, R}) :
    (dist Q R = a → (D.tile i).localAngle P = α) ∧
    (dist Q R = b → (D.tile i).localAngle P = β) ∧
    (dist Q R = c → (D.tile i).localAngle P = γ) := by
  obtain ⟨k, hk⟩ := Erdos634.MarchInduction.mem_range_of_eq hr (Set.mem_insert P _)
  rw [← hk]
  have h := localAngle_of_oppSideE D hab hac hbc hs0 hs1 hs2 hα' hβ' hγ' i k
  have hd : dist ((D.tile i).pts (k + 1)) ((D.tile i).pts (k + 2)) = dist Q R := by
    rcases Erdos634.MarchInduction.vertex_data_of_range hr hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, dist_comm]
  rw [hd] at h
  exact h

/-- The base-β side values are pairwise distinct at a coprime member `2 ≤ e < f` (`a = b` would
be `e² + ef = f²`, forcing `e ∣ f²`, so `e = 1`). -/
theorem sides_distinct {e f : ℕ} (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e < f) :
    ((e : ℝ) * f ≠ (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ∧ ((e : ℝ) * f ≠ (f : ℝ) ^ 2) ∧
      ((f : ℝ) ^ 2 - (e : ℝ) ^ 2 ≠ (f : ℝ) ^ 2) := by
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast he
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have hN : e * f + e ^ 2 = f ^ 2 := by
      have : ((e * f + e ^ 2 : ℕ) : ℝ) = ((f ^ 2 : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have hdvd : e ∣ f ^ 2 := ⟨f + e, by rw [← hN]; ring⟩
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right 2 hco) hdvd
    omega
  · have hf : (0 : ℝ) < f := by linarith
    have : (e : ℝ) = f := by
      have h' : (e : ℝ) * f = f * f := by rw [h]; ring
      exact mul_right_cancel₀ hf.ne' h'
    linarith
  · have : (e : ℝ) ^ 2 = 0 := by linarith
    have : (e : ℝ) = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith

theorem dist_self_add_unit {A u : Plane} (hu : ‖u‖ = 1) {s : ℝ} (hs : 0 ≤ s) :
    dist A (A + s • u) = s := by
  rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, hu, mul_one,
    Real.norm_of_nonneg hs]


/-- Every tile edge of `D` has length `a`, `b` or `c` (congruence to the model; `sideOpp` values).
(Same as `MirrorStripR2Glue.edge_len_mem`; duplicated to keep the Draft files independent.) -/
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

/-- An `EdgeIs` edge is the segment between the named points, with the same length. -/
theorem edgeIs_data {N : ℕ} {D : CongruentDissection N} {ε : Fin N × Fin 3} {p q : Plane}
    (h : EdgeIs D ε p q) :
    (D.tile ε.1).edge ε.2 = segment ℝ p q ∧
    openSegment ℝ ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1)) = openSegment ℝ p q ∧
    dist ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1)) = dist p q := by
  unfold EdgeIs at h
  rw [Set.pair_eq_pair_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨by rw [Tri.edge, h1, h2], by rw [h1, h2], by rw [h1, h2]⟩
  · exact ⟨by rw [Tri.edge, h1, h2, segment_symm], by rw [h1, h2, openSegment_symm],
      by rw [h1, h2, dist_comm]⟩

namespace HFrame

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ}

/-- The point of `r` at distance `t` from the apex. -/
noncomputable def rpt (F : HFrame D e f α β γ) (t : ℝ) : Plane := F.A + t • F.uR
/-- Near-side chain of `r` (`T₂`'s side). -/
noncomputable def near (F : HFrame D e f α β γ) : Finset (Fin N × Fin 3) :=
  D.toDissection.lineChain F.h (F.h F.A)
/-- Far-side chain of `r` (`T₁`'s side). -/
noncomputable def far (F : HFrame D e f α β γ) : Finset (Fin N × Fin 3) :=
  D.toDissection.lineChain (-F.h) (-(F.h F.A))
/-- Band-side chain of `ℓ` (the line through `P′` parallel to `r`; band side = `T₃`'s residual wedge,
`{h ≤ h P′}`). -/
noncomputable def band (F : HFrame D e f α β γ) : Finset (Fin N × Fin 3) :=
  D.toDissection.lineChain F.h (F.h F.P)
/-- `K`, the half-turn of `T₂` across `VP′` (branch (H)); `Q₁ = V + P′ − A`. -/
def K (F : HFrame D e f α β γ) : Set Plane := {F.V, F.P, F.V + F.P - F.A}
/-- `T₂ + P′`. -/
def T2P (F : HFrame D e f α β γ) : Set Plane := {F.P, F.V + F.P - F.A, F.P + F.P - F.A}
/-- `L = T₂ + V`, the first `L_c` step. -/
def L (F : HFrame D e f α β γ) : Set Plane := {F.V, F.V + F.V - F.A, F.V + F.P - F.A}
/-- `K + V`. -/
def KV (F : HFrame D e f α β γ) : Set Plane :=
  {F.V + F.V - F.A, F.V + F.P - F.A, F.V + F.V + F.P - F.A - F.A}

/-! ## R3 glue -/

/-- **G-R3 — both sides of `r` are whole-edge runs up to the first common junction.**
**PROVED 2026-09-24** (no `sorry`): `TraceCovering.trace_covering` on `r` from the apex `A` (start: `A`
is a target vertex, `vertex_ray_out`; end: the base point, `hrbase`; seed: `T₁`'s `b`-edge), then the
near word read off the pure `c`-chain (`x₀ = q·c` if the first common junction falls inside it, else
`c^n` + the rest), the far word containing `T₁`'s `b`, lengths in `{a,b,c}` (`edge_len_mem`).
Original note:
Hypothesis (R3's case): the near side of `r` reads `c^n` from `A`, `n = ⌊f·b/c⌋`, i.e. the near chain
contains the `c`-edges `[kc, (k+1)c]`, `k < n` (the pure `L_c` chain `T₂ + kV`).  Conclusion: there is
a first common junction `x₀ ≤ f·b` on `r`; the near edges in `[0, x₀]` are `c^j` then a word `t`, with
`t` empty unless `j = n`; the far edges in `[0, x₀]` form a word with `≥ 1` `b` (`T₁`'s `b` at `A`).

Proof plan.  (i) `T₁`'s `b`-edge `[A, A+b·uR]` is in `far`, `T₂`'s `c`-edge `[A, V]` in `near`
(`hT1`, `hT2`, `hhR`, `hhP`; `lineChain` membership, ≈ 40 lines).  (ii) Induction on the covered
prefix `[A, X_k]`, `X_k` the larger of the two sides' current ends: the prefix is a wall (each point
lies on a chain edge; `Dissection.edge_point_not_interior`), so **`Dissection.wall_two_sided`**
(WallChain, proved) covers it exactly once from each side; if the shorter side's end `Y` is not a
junction of the other side, the covering edge through `Y⁺` starts at `Y` (collinear 1-D dichotomy +
`sameside_edges_subsingleton`).  (iii) The base point `rpt (f·b)` is a junction of both sides (port of
`MirrorStripR2Glue.base_is_junction`, proved there, ≈ 70 lines); finiteness of the chains ends the
induction, giving `x₀ ≤ f·b`.  (iv) Edge lengths ∈ `{a,b,c}` (congruence, `sideOpp`) and the real sum
`= x₀` become the `ℕ` words (≈ 40 lines, as `MirrorStripR2Glue.band_junction_rep`).
**Can `WallChain.edge_two_sided` discharge it?**  Only step (ii)'s per-step covering: `edge_two_sided`
/ `wall_two_sided` give "each side covers a KNOWN wall exactly once in `μH¹`", not "the next edge
starts at the previous junction" nor "the first common junction exists".  The missing piece is the
1-D straddle dichotomy recorded as MISSING in `ThickEFminus1Glue.far_edge_through_V` (G1) and
`vp_single_a_edge`, and as "trace dichotomy ≈ 80" in `MirrorStripR2Glue.band_junction_rep` (G3).
BLOCKER: **trace covering** (iterated, one line, both sides) — named in the Draft glue files (R1 G1 /
G-VP′, R2 G3), NOT a PAPER_MAP row.  Frame fields `hT1`, `hT2` carry the PAPER_MAP `thm:pierce`
"tile-placement layer" blocker.  Estimate 250–400 lines. -/
theorem ray_whole_edge_runs (F : HFrame D e f α β γ) (n : ℕ) (hn : n = nStar f (f ^ 2 - e ^ 2))
    (hpure : ∀ k < n, ∃ ε ∈ F.near,
      EdgeIs D ε (F.rpt ((k : ℝ) * (f : ℝ) ^ 2)) (F.rpt (((k : ℝ) + 1) * (f : ℝ) ^ 2))) :
    ∃ x0 j ta tb tc na nb nc : ℕ, j ≤ n ∧ (j < n → ta = 0 ∧ tb = 0 ∧ tc = 0) ∧
      j * f ^ 2 + (ta * (e * f) + tb * (f ^ 2 - e ^ 2) + tc * f ^ 2) = x0 ∧
      na * (e * f) + nb * (f ^ 2 - e ^ 2) + nc * f ^ 2 = x0 ∧ 1 ≤ nb ∧
      x0 ≤ f * (f ^ 2 - e ^ 2) := by
  classical
  have hef := F.hef
  have he := F.he
  have hu1 : ‖F.uR‖ = 1 := F.huR
  have hu0 : F.uR ≠ 0 := TraceCovering.ne_zero_of_norm hu1
  have hgd₁ : ∀ y, F.h y = F.h F.A ↔ F.h y = F.h F.A := fun _ => Iff.rfl
  have hgd₂ : ∀ y, (-F.h) y = -(F.h F.A) ↔ F.h y = F.h F.A := TraceCovering.neg_iff
  have hfR : (0 : ℝ) < f := by exact_mod_cast (show 0 < f by omega)
  have heR : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  have hefR : (e : ℝ) < f := by exact_mod_cast (show e < f by omega)
  have hb_pos : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hc_pos : (0 : ℝ) < (f : ℝ) ^ 2 := by positivity
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast (show 1 ≤ f by omega)
  have hbL : (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ≤ (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by nlinarith
  have hA0 : F.A + (0 : ℝ) • F.uR = F.A := by rw [zero_smul, add_zero]
  have hrpt : ∀ t : ℝ, F.rpt t = F.A + t • F.uR := fun t => rfl
  -- (i) the open ray `(A, fb)` is interior
  have hint : ∀ x ∈ Set.Ioo 0 ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)),
      F.A + x • F.uR ∈ interior D.target.carrier := fun x hx => F.hrint x hx.1 hx.2
  -- (ii) no edge on `r` passes through the apex `A` (a target vertex: the ray behind it is outside)
  have hback : ∀ t : ℝ, t < 0 → F.A + t • F.uR ∉ D.target.carrier := by
    intro t ht
    obtain ⟨kA, hkA⟩ := MarchInduction.mem_range_of_eq F.htarget (Set.mem_insert _ _)
    set s0 : ℝ := (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / 2 with hs0
    have hs0pos : 0 < s0 := by positivity
    have hv : s0 • F.uR ≠ 0 := smul_ne_zero hs0pos.ne' hu0
    have hin : D.target.pts kA + s0 • F.uR ∈ D.target.carrier := by
      rw [hkA]; exact interior_subset (hint s0 ⟨hs0pos, by rw [hs0]; linarith [mul_pos hfR hb_pos]⟩)
    have := TraceCovering.vertex_ray_out D.target kA hv hin
      (t := t / s0) (div_neg_of_neg_of_pos ht hs0pos)
    rwa [hkA, smul_smul, div_mul_cancel₀ _ hs0pos.ne'] at this
  have hstart : ¬ TraceCovering.Straddled D.toDissection F.h (F.h F.A) F.A ∧
      ¬ TraceCovering.Straddled D.toDissection (-F.h) (-(F.h F.A)) F.A := by
    have h1 := TraceCovering.not_straddled_of_outside_before (D := D.toDissection) (g := F.h)
      (d := F.h F.A) hgd₁ F.hh0 rfl F.hhuR hu0 (x₀ := 0) hback
    have h2 := TraceCovering.not_straddled_of_outside_before (D := D.toDissection) (g := -F.h)
      (d := -(F.h F.A)) hgd₂ F.hh0 rfl F.hhuR hu0 (x₀ := 0) hback
    rw [hA0] at h1 h2
    exact ⟨h1, h2⟩
  -- (iii) nor through the base point `A + fb·uR` (the ray leaves the target there)
  have hfwd : ∀ t : ℝ, (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) < t → F.A + t • F.uR ∉ D.target.carrier := by
    intro t ht
    have := F.hrbase (t - (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) (by linarith)
    rwa [show (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + (t - (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
      = t by ring] at this
  have hend := And.intro
    (TraceCovering.not_straddled_of_outside_after (D := D.toDissection) (g := F.h)
      (d := F.h F.A) hgd₁ F.hh0 rfl F.hhuR hu0 hfwd)
    (TraceCovering.not_straddled_of_outside_after (D := D.toDissection) (g := -F.h)
      (d := -(F.h F.A)) hgd₂ F.hh0 rfl F.hhuR hu0 hfwd)
  -- (iv) the seed: `T₁`'s `b`-edge `[A, A + b·uR]`, a far-side edge
  obtain ⟨i1, hi1⟩ := F.hT1
  set Bp := F.A + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR with hBp
  set Rf := F.A + (1 / (f : ℝ)) • (F.R - F.A) with hRf
  obtain ⟨kA1, hkA1⟩ := MarchInduction.mem_range_of_eq hi1 (Set.mem_insert _ _)
  have hfin1 : kA1 + 2 + 1 = kA1 := by fin_cases kA1 <;> rfl
  have hfin2 : kA1 + 2 + 2 = kA1 + 1 := by fin_cases kA1 <;> rfl
  obtain ⟨m, hm01, hm2⟩ : ∃ m : Fin 3,
      (((D.tile i1).pts m = F.A ∧ (D.tile i1).pts (m + 1) = Bp) ∨
        ((D.tile i1).pts m = Bp ∧ (D.tile i1).pts (m + 1) = F.A)) ∧
      (D.tile i1).pts (m + 2) = Rf := by
    rcases MarchInduction.vertex_data_of_range hi1 hkA1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨kA1, Or.inl ⟨hkA1, h1⟩, h2⟩
    · exact ⟨kA1 + 2, Or.inr ⟨h2, by rw [hfin1, hkA1]⟩, by rw [hfin2, h1]⟩
  have hhB : F.h Bp = F.h F.A := TraceCovering.f_param rfl F.hhuR _
  have hhRf : F.h F.A < F.h Rf := by
    rw [hRf, map_add, map_smul, map_sub, smul_eq_mul]
    have := F.hhR
    have : 0 < 1 / (f : ℝ) * (F.h F.R - F.h F.A) := mul_pos (by positivity) (by linarith)
    linarith
  have he1 : (i1, m) ∈ F.far := by
    show (i1, m) ∈ D.toDissection.lineChain (-F.h) (-(F.h F.A))
    rw [Dissection.mem_lineChain]
    have h3 : ∀ i m : Fin 3, i = m ∨ i = m + 1 ∨ i = m + 2 := by decide
    refine ⟨?_, ?_, fun i => ?_⟩
    · rcases hm01 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> simp [hhB]
    · rcases hm01 with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> simp [hhB]
    · rcases h3 i m with rfl | rfl | rfl
      · rcases hm01 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> simp [hhB]
      · rcases hm01 with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> simp [hhB]
      · rw [hm2]; simp only [LinearMap.neg_apply, neg_le_neg_iff]; exact hhRf.le
  have hedge1 : (D.tile i1).edge m = segment ℝ F.A Bp := by
    rw [Tri.edge]
    rcases hm01 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    exact segment_symm ℝ _ _
  have hdist1 : dist ((D.tile i1).pts m) ((D.tile i1).pts (m + 1)) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have hdb : dist F.A Bp = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
      rw [hBp, dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, hu1, mul_one,
        Real.norm_of_nonneg hb_pos.le]
    rcases hm01 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact hdb
    · rw [dist_comm]; exact hdb
  -- TRACE COVERING, both sides, from `A` to the first common junction `x₀`
  obtain ⟨x₀, hbx, hxL, hn₁, -, -, hsum₁, hsum₂⟩ :=
    TraceCovering.trace_covering (D := D.toDissection) F.hh0 rfl F.hhuR hu1 hb_pos hbL hint
      hstart hend ⟨(i1, m), Finset.mem_union_right _ he1, hedge1⟩
  have hx0 : 0 ≤ x₀ := hb_pos.le.trans hbx
  -- points of `r` inside `[A, A + x₀·uR]`
  have hSeg : ∀ s : ℝ, 0 ≤ s → s ≤ x₀ → F.A + s • F.uR ∈ segment ℝ F.A (F.A + x₀ • F.uR) := by
    intro s hs1 hs2
    have h1 : segment ℝ F.A (F.A + x₀ • F.uR) = segment ℝ (F.A + (0 : ℝ) • F.uR) (F.A + x₀ • F.uR) := by
      rw [hA0]
    rw [h1, TraceCovering.segment_param, min_eq_left hx0, max_eq_right hx0]
    exact ⟨s, ⟨hs1, hs2⟩, rfl⟩
  -- the far word: `T₁`'s `b` plus the rest
  set sF := (D.toDissection.lineChain (-F.h) (-(F.h F.A))).filter
    (fun e => (D.toDissection.tile e.1).edge e.2 ⊆ segment ℝ F.A (F.A + x₀ • F.uR)) with hsF
  have hmemF : (i1, m) ∈ sF := by
    refine Finset.mem_filter.mpr ⟨he1, ?_⟩
    show (D.tile i1).edge m ⊆ _
    rw [hedge1]
    exact (convex_segment _ _).segment_subset (left_mem_segment ℝ _ _) (hSeg _ hb_pos.le hbx)
  rw [← Finset.add_sum_erase sF _ hmemF] at hsum₂
  obtain ⟨P', Q', R', hPQR, -⟩ := sum_three_values (sF.erase (i1, m))
    (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
    ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)
    (fun ε _ => edge_len_mem D F.hM.hs0 F.hM.hs1 F.hM.hs2 ε.1 ε.2)
  have hee : e ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left (by omega) 2
  set x0n : ℕ := P' * (e * f) + (Q' + 1) * (f ^ 2 - e ^ 2) + R' * f ^ 2 with hx0n
  have hx0cast : (x0n : ℝ) = x₀ := by
    rw [hx0n]; push_cast [Nat.cast_sub hee]
    simp only at hsum₂ hdist1
    rw [hdist1] at hsum₂
    linarith
  have hx0le : x0n ≤ f * (f ^ 2 - e ^ 2) := by
    have : (x0n : ℝ) ≤ ((f * (f ^ 2 - e ^ 2) : ℕ) : ℝ) := by
      rw [hx0cast]; push_cast [Nat.cast_sub hee]; exact hxL
    exact_mod_cast this
  -- the near word: the `c`-chain `[k c, (k+1) c]`, `k < n`, then the rest
  haveI : Nonempty (Fin N × Fin 3) := ⟨(⟨0, D.toDissection.pos⟩, 0)⟩
  choose! εf hεf hεE using hpure
  have hEd : ∀ k < n, (D.tile (εf k).1).edge (εf k).2 =
        segment ℝ (F.A + ((k : ℝ) * (f : ℝ) ^ 2) • F.uR) (F.A + (((k : ℝ) + 1) * (f : ℝ) ^ 2) • F.uR) ∧
      openSegment ℝ ((D.tile (εf k).1).pts (εf k).2) ((D.tile (εf k).1).pts ((εf k).2 + 1)) =
        openSegment ℝ (F.A + ((k : ℝ) * (f : ℝ) ^ 2) • F.uR)
          (F.A + (((k : ℝ) + 1) * (f : ℝ) ^ 2) • F.uR) ∧
      dist ((D.tile (εf k).1).pts (εf k).2) ((D.tile (εf k).1).pts ((εf k).2 + 1)) = (f : ℝ) ^ 2 := by
    intro k hk
    obtain ⟨h1, h2, h3⟩ := edgeIs_data (hεE k hk)
    refine ⟨h1, h2, ?_⟩
    have hlt2 : (k : ℝ) * (f : ℝ) ^ 2 < ((k : ℝ) + 1) * (f : ℝ) ^ 2 := by linarith
    rw [h3, hrpt, hrpt, TraceCovering.dist_param hu1, max_eq_right hlt2.le, min_eq_left hlt2.le]
    ring
  set q := ⌊x₀ / (f : ℝ) ^ 2⌋₊ with hq
  have hq0 : 0 ≤ x₀ / (f : ℝ) ^ 2 := div_nonneg hx0 hc_pos.le
  have hq1 : (q : ℝ) * (f : ℝ) ^ 2 ≤ x₀ := by
    have := Nat.floor_le hq0; rwa [le_div_iff₀ hc_pos] at this
  have hq2 : x₀ < ((q : ℝ) + 1) * (f : ℝ) ^ 2 := by
    have := Nat.lt_floor_add_one (x₀ / (f : ℝ) ^ 2); rwa [div_lt_iff₀ hc_pos] at this
  by_cases hqn : q < n
  · -- the first common junction falls inside the `c`-chain: `x₀ = q·c`
    have hxq : x₀ = (q : ℝ) * (f : ℝ) ^ 2 := by
      by_contra hne
      have hlt : (q : ℝ) * (f : ℝ) ^ 2 < x₀ := lt_of_le_of_ne hq1 (Ne.symm hne)
      apply hn₁
      refine ⟨εf q, hεf q hqn, ?_⟩
      have hlt2 : (q : ℝ) * (f : ℝ) ^ 2 < ((q : ℝ) + 1) * (f : ℝ) ^ 2 := by linarith
      rw [(hEd q hqn).2.1, TraceCovering.openSegment_param hlt2.ne, min_eq_left hlt2.le,
        max_eq_right hlt2.le]
      exact ⟨x₀, ⟨hlt, hq2⟩, rfl⟩
    have hx0q : x0n = q * f ^ 2 := by
      have : (x0n : ℝ) = ((q * f ^ 2 : ℕ) : ℝ) := by rw [hx0cast, hxq]; push_cast; ring
      exact_mod_cast this
    exact ⟨x0n, q, 0, 0, 0, P', Q' + 1, R', hqn.le, fun _ => ⟨rfl, rfl, rfl⟩,
      by rw [hx0q]; ring, rfl, by omega, hx0le⟩
  · -- the whole `c`-chain lies before `x₀`: near word `c^n` then a word `t`
    have hnq : (n : ℝ) * (f : ℝ) ^ 2 ≤ x₀ := by
      have : (n : ℝ) ≤ q := by exact_mod_cast (not_lt.mp hqn)
      exact le_trans (mul_le_mul_of_nonneg_right this hc_pos.le) hq1
    set sN := (D.toDissection.lineChain F.h (F.h F.A)).filter
      (fun e => (D.toDissection.tile e.1).edge e.2 ⊆ segment ℝ F.A (F.A + x₀ • F.uR)) with hsN
    obtain ⟨C, hC⟩ : ∃ C : Finset (Fin N × Fin 3), C = (Finset.range n).image εf := ⟨_, rfl⟩
    have hinj : Set.InjOn εf (Finset.range n : Set ℕ) := by
      intro k hk k' hk' heq
      have hk1 : k < n := Finset.mem_range.mp hk
      have hk1' : k' < n := Finset.mem_range.mp hk'
      have hE := hεE k hk1
      rw [heq] at hE
      have hE' := hεE k' hk1'
      unfold EdgeIs at hE hE'
      rw [hE] at hE'
      rw [Set.pair_eq_pair_iff, hrpt, hrpt, hrpt, hrpt] at hE'
      rcases hE' with ⟨h1, -⟩ | ⟨h1, h2⟩
      · have := TraceCovering.lm_injective hu0 h1
        have : (k : ℝ) = k' := mul_right_cancel₀ hc_pos.ne' this
        exact_mod_cast this
      · have e1 := TraceCovering.lm_injective hu0 h1
        have e2 := TraceCovering.lm_injective hu0 h2
        simp only at e1 e2
        linarith
    have hCsub : C ⊆ sN := by
      intro ε hε
      rw [hC] at hε
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hε
      have hk' := Finset.mem_range.mp hk
      refine Finset.mem_filter.mpr ⟨hεf k hk', ?_⟩
      show (D.tile (εf k).1).edge (εf k).2 ⊆ _
      rw [(hEd k hk').1]
      have hkR : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk'
      have hk0 : (0 : ℝ) ≤ (k : ℝ) * (f : ℝ) ^ 2 := by positivity
      have hk1 : ((k : ℝ) + 1) * (f : ℝ) ^ 2 ≤ x₀ :=
        le_trans (mul_le_mul_of_nonneg_right hkR hc_pos.le) hnq
      exact (convex_segment _ _).segment_subset (hSeg _ hk0 (by linarith))
        (hSeg _ (by positivity) hk1)
    have hsumC : ∑ ε ∈ C, dist ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1))
        = (n : ℝ) * (f : ℝ) ^ 2 := by
      rw [hC, Finset.sum_image hinj]
      rw [Finset.sum_congr rfl (fun k hk => (hEd k (Finset.mem_range.mp hk)).2.2)]
      simp
    rw [← Finset.sum_sdiff hCsub, hsumC] at hsum₁
    obtain ⟨ta, tb, tc, hT, -⟩ := sum_three_values (sN \ C)
      (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
      ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)
      (fun ε _ => edge_len_mem D F.hM.hs0 F.hM.hs1 F.hM.hs2 ε.1 ε.2)
    have hnear : n * f ^ 2 + (ta * (e * f) + tb * (f ^ 2 - e ^ 2) + tc * f ^ 2) = x0n := by
      have : ((n * f ^ 2 + (ta * (e * f) + tb * (f ^ 2 - e ^ 2) + tc * f ^ 2) : ℕ) : ℝ)
          = (x0n : ℝ) := by
        rw [hx0cast]; push_cast [Nat.cast_sub hee]
        linarith
      exact_mod_cast this
    exact ⟨x0n, n, ta, tb, tc, P', Q' + 1, R', le_rfl, fun h => absurd h (lt_irrefl n),
      hnear, rfl, by omega, hx0le⟩

/-- **R4 Step 2 / PRC(iii), formal: every chain point is pierced.**  (`proof_H_empty.md` §5.3 Step 2,
used by Lemma G step 1 at `k = 1` and at every chain point.)  If the near side of `r` carries the
`c`-edges `[i c, (i+1) c]`, `i < k`, and `k c < f b`, then a far-side edge of `r` passes through
`kV = A + kc·uR`.  Proof: otherwise `kV` is a far junction; the stretch `(A, kV)` is a wall (the near
`c`-edges), no edge passes through the apex, so by TRACE COVERING (`TraceCovering.wall_sum`) the far
edges in `[A, kV]` are a word of value `kc` containing `T₁`'s `b` — which Lemma A
(`Inflation.c_side_no_b`, `k < f`) forbids.  At `k = 1` this is `V` pierced (`thm:pierce(iii)`). -/
theorem chain_point_pierced (F : HFrame D e f α β γ) (k : ℕ) (hk1 : 1 ≤ k)
    (hkL : (k : ℝ) * (f : ℝ) ^ 2 < (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
    (hpure : ∀ i < k, ∃ ε ∈ F.near,
      EdgeIs D ε (F.rpt ((i : ℝ) * (f : ℝ) ^ 2)) (F.rpt (((i : ℝ) + 1) * (f : ℝ) ^ 2))) :
    TraceCovering.Straddled D.toDissection (-F.h) (-(F.h F.A))
      (F.A + ((k : ℝ) * (f : ℝ) ^ 2) • F.uR) := by
  classical
  by_contra hns
  have hef := F.hef
  have he := F.he
  have hu1 : ‖F.uR‖ = 1 := F.huR
  have hu0 : F.uR ≠ 0 := TraceCovering.ne_zero_of_norm hu1
  have hgd₂ : ∀ y, (-F.h) y = -(F.h F.A) ↔ F.h y = F.h F.A := TraceCovering.neg_iff
  have hh' : (-F.h : Plane →ₗ[ℝ] ℝ) ≠ 0 := fun h => F.hh0 (neg_eq_zero.mp h)
  have hfR : (0 : ℝ) < f := by exact_mod_cast (show 0 < f by omega)
  have hefR : (e : ℝ) < f := by exact_mod_cast (show e < f by omega)
  have heR : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  have hb_pos : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hc_pos : (0 : ℝ) < (f : ℝ) ^ 2 := by positivity
  have hA0 : F.A + (0 : ℝ) • F.uR = F.A := by rw [zero_smul, add_zero]
  have hrpt : ∀ t : ℝ, F.rpt t = F.A + t • F.uR := fun t => rfl
  set t : ℝ := (k : ℝ) * (f : ℝ) ^ 2 with ht
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have ht0 : 0 ≤ t := by positivity
  -- (i) interior
  have hint : ∀ x ∈ Set.Ioo 0 t, F.A + x • F.uR ∈ interior D.target.carrier := fun x hx =>
    F.hrint x hx.1 (lt_trans hx.2 hkL)
  -- (ii) the wall: the near `c`-edges
  haveI : Nonempty (Fin N × Fin 3) := ⟨(⟨0, D.toDissection.pos⟩, 0)⟩
  choose! εf hεf hεE using hpure
  have hwall : ∀ x ∈ Set.Ioo 0 t, ∀ i, F.A + x • F.uR ∉ interior (D.tile i).carrier := by
    intro x hx i
    set q := ⌊x / (f : ℝ) ^ 2⌋₊ with hq
    have hq0 : 0 ≤ x / (f : ℝ) ^ 2 := div_nonneg hx.1.le hc_pos.le
    have hq1 : (q : ℝ) * (f : ℝ) ^ 2 ≤ x := by
      have := Nat.floor_le hq0; rwa [le_div_iff₀ hc_pos] at this
    have hq2 : x < ((q : ℝ) + 1) * (f : ℝ) ^ 2 := by
      have := Nat.lt_floor_add_one (x / (f : ℝ) ^ 2); rwa [div_lt_iff₀ hc_pos] at this
    have hqk : q < k := by
      have h1 : (q : ℝ) * (f : ℝ) ^ 2 < (k : ℝ) * (f : ℝ) ^ 2 := lt_of_le_of_lt hq1 hx.2
      exact_mod_cast lt_of_mul_lt_mul_right h1 hc_pos.le
    obtain ⟨hE1, -, -⟩ := edgeIs_data (hεE q hqk)
    have hmem : F.A + x • F.uR ∈ (D.tile (εf q).1).edge (εf q).2 := by
      rw [hE1, hrpt, hrpt, TraceCovering.segment_param]
      have hlt2 : (q : ℝ) * (f : ℝ) ^ 2 < ((q : ℝ) + 1) * (f : ℝ) ^ 2 := by linarith
      rw [min_eq_left hlt2.le, max_eq_right hlt2.le]
      exact ⟨x, ⟨hq1, hq2.le⟩, rfl⟩
    exact D.toDissection.edge_point_not_interior hmem i
  -- (iii) no far edge passes through the apex
  have hback : ∀ s : ℝ, s < 0 → F.A + s • F.uR ∉ D.target.carrier := by
    intro s hs
    obtain ⟨kA, hkA⟩ := MarchInduction.mem_range_of_eq F.htarget (Set.mem_insert _ _)
    have htpos' : 0 < t := by rw [ht]; exact mul_pos (by linarith) hc_pos
    have hv : (t / 2) • F.uR ≠ 0 := smul_ne_zero (by positivity) hu0
    have hin : D.target.pts kA + (t / 2) • F.uR ∈ D.target.carrier := by
      have htpos : 0 < t := by rw [ht]; exact mul_pos (by linarith) hc_pos
      rw [hkA]; exact interior_subset (hint (t / 2) ⟨by positivity, by linarith⟩)
    have := TraceCovering.vertex_ray_out D.target kA hv hin (t := s / (t / 2))
      (div_neg_of_neg_of_pos hs (by positivity))
    rwa [hkA, smul_smul, div_mul_cancel₀ _ (by positivity)] at this
  have hstart := TraceCovering.not_straddled_of_outside_before (D := D.toDissection) (g := -F.h)
    (d := -(F.h F.A)) hgd₂ F.hh0 rfl F.hhuR hu0 (x₀ := 0) hback
  -- TRACE COVERING, far side, on `[A, kV]`
  have hsum := TraceCovering.wall_sum (D := D.toDissection) hh' hgd₂ F.hh0 rfl F.hhuR hu1 ht0
    hint hwall hstart hns
  -- `T₁`'s `b`-edge is one of them
  obtain ⟨i1, hi1⟩ := F.hT1
  set Bp := F.A + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR with hBp
  set Rf := F.A + (1 / (f : ℝ)) • (F.R - F.A) with hRf
  obtain ⟨kA1, hkA1⟩ := MarchInduction.mem_range_of_eq hi1 (Set.mem_insert _ _)
  have hfin1 : kA1 + 2 + 1 = kA1 := by fin_cases kA1 <;> rfl
  have hfin2 : kA1 + 2 + 2 = kA1 + 1 := by fin_cases kA1 <;> rfl
  obtain ⟨m, hm01, hm2⟩ : ∃ m : Fin 3,
      (((D.tile i1).pts m = F.A ∧ (D.tile i1).pts (m + 1) = Bp) ∨
        ((D.tile i1).pts m = Bp ∧ (D.tile i1).pts (m + 1) = F.A)) ∧
      (D.tile i1).pts (m + 2) = Rf := by
    rcases MarchInduction.vertex_data_of_range hi1 hkA1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨kA1, Or.inl ⟨hkA1, h1⟩, h2⟩
    · exact ⟨kA1 + 2, Or.inr ⟨h2, by rw [hfin1, hkA1]⟩, by rw [hfin2, h1]⟩
  have hhB : F.h Bp = F.h F.A := TraceCovering.f_param rfl F.hhuR _
  have hhRf : F.h F.A < F.h Rf := by
    rw [hRf, map_add, map_smul, map_sub, smul_eq_mul]
    have := F.hhR
    have : 0 < 1 / (f : ℝ) * (F.h F.R - F.h F.A) := mul_pos (by positivity) (by linarith)
    linarith
  have he1 : (i1, m) ∈ D.toDissection.lineChain (-F.h) (-(F.h F.A)) := by
    rw [Dissection.mem_lineChain]
    have h3 : ∀ i m : Fin 3, i = m ∨ i = m + 1 ∨ i = m + 2 := by decide
    refine ⟨?_, ?_, fun i => ?_⟩
    · rcases hm01 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> simp [hhB]
    · rcases hm01 with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> simp [hhB]
    · rcases h3 i m with rfl | rfl | rfl
      · rcases hm01 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> simp [hhB]
      · rcases hm01 with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> simp [hhB]
      · rw [hm2]; simp only [LinearMap.neg_apply, neg_le_neg_iff]; exact hhRf.le
  have hedge1 : (D.tile i1).edge m = segment ℝ F.A Bp := by
    rw [Tri.edge]
    rcases hm01 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    exact segment_symm ℝ _ _
  have hdist1 : dist ((D.tile i1).pts m) ((D.tile i1).pts (m + 1)) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have hdb : dist F.A Bp = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
      rw [hBp, dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, hu1, mul_one,
        Real.norm_of_nonneg hb_pos.le]
    rcases hm01 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact hdb
    · rw [dist_comm]; exact hdb
  have hbt : (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ≤ t := by nlinarith
  have hBseg : Bp ∈ segment ℝ (F.A + (0 : ℝ) • F.uR) (F.A + t • F.uR) := by
    rw [TraceCovering.segment_param, min_eq_left ht0, max_eq_right ht0]
    exact ⟨_, ⟨hb_pos.le, hbt⟩, rfl⟩
  have hAseg : F.A ∈ segment ℝ (F.A + (0 : ℝ) • F.uR) (F.A + t • F.uR) := by
    convert left_mem_segment ℝ (F.A + (0 : ℝ) • F.uR) (F.A + t • F.uR) using 1
    exact hA0.symm
  set sF := (D.toDissection.lineChain (-F.h) (-(F.h F.A))).filter
    (fun e => (D.toDissection.tile e.1).edge e.2 ⊆
      segment ℝ (F.A + (0 : ℝ) • F.uR) (F.A + t • F.uR)) with hsF
  have hmemF : (i1, m) ∈ sF := by
    refine Finset.mem_filter.mpr ⟨he1, ?_⟩
    show (D.tile i1).edge m ⊆ _
    rw [hedge1]
    exact (convex_segment _ _).segment_subset hAseg hBseg
  rw [← Finset.add_sum_erase sF _ hmemF] at hsum
  obtain ⟨P', Q', R', hPQR, -⟩ := sum_three_values (sF.erase (i1, m))
    (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
    ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)
    (fun ε _ => edge_len_mem D F.hM.hs0 F.hM.hs1 F.hM.hs2 ε.1 ε.2)
  have hee : e ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hnat : P' * (e * f) + (Q' + 1) * (f ^ 2 - e ^ 2) + R' * f ^ 2 = k * f ^ 2 := by
    have : ((P' * (e * f) + (Q' + 1) * (f ^ 2 - e ^ 2) + R' * f ^ 2 : ℕ) : ℝ)
        = ((k * f ^ 2 : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub hee]
      simp only at hsum hdist1
      rw [hdist1] at hsum
      linarith
    exact_mod_cast this
  -- `k < f`: `k c < f b < f c`
  have hkf : k < f := by
    have h1 : (k : ℝ) * (f : ℝ) ^ 2 < (f : ℝ) * (f : ℝ) ^ 2 := by nlinarith
    exact_mod_cast lt_of_mul_lt_mul_right h1 hc_pos.le
  have := Inflation.c_side_no_b e f (f ^ 2 - e ^ 2) k P' (Q' + 1) R' (by omega) (by omega) F.hco
    (by omega) hkf hnat
  omega

/-- **`thm:pierce(iii)`, formal: `V` is pierced.**  In an `HFrame`, a far-side edge of `r` passes
through `V` (`chain_point_pierced` at `k = 1`, with `T₂`'s `c`-edge `[A, V]` as the near chain and
`c < f·b` at `2 ≤ e ≤ f − 2`). -/
theorem V_pierced (F : HFrame D e f α β γ) :
    TraceCovering.Straddled D.toDissection (-F.h) (-(F.h F.A)) F.V := by
  classical
  have hef := F.hef
  have he := F.he
  obtain ⟨i2, hi2⟩ := F.hT2
  obtain ⟨kA, hkA⟩ := MarchInduction.mem_range_of_eq hi2 (Set.mem_insert _ _)
  have hfin1 : kA + 2 + 1 = kA := by fin_cases kA <;> rfl
  have hfin2 : kA + 2 + 2 = kA + 1 := by fin_cases kA <;> rfl
  obtain ⟨m, hm01, hm2⟩ : ∃ m : Fin 3,
      (((D.tile i2).pts m = F.A ∧ (D.tile i2).pts (m + 1) = F.V) ∨
        ((D.tile i2).pts m = F.V ∧ (D.tile i2).pts (m + 1) = F.A)) ∧
      (D.tile i2).pts (m + 2) = F.P := by
    rcases MarchInduction.vertex_data_of_range hi2 hkA with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨kA, Or.inl ⟨hkA, h1⟩, h2⟩
    · exact ⟨kA + 2, Or.inr ⟨h2, by rw [hfin1, hkA]⟩, by rw [hfin2, h1]⟩
  have hhV : F.h F.V = F.h F.A := by rw [F.hV]; exact TraceCovering.f_param rfl F.hhuR _
  have hnear : (i2, m) ∈ F.near := by
    show (i2, m) ∈ D.toDissection.lineChain F.h (F.h F.A)
    rw [Dissection.mem_lineChain]
    have h3 : ∀ i m : Fin 3, i = m ∨ i = m + 1 ∨ i = m + 2 := by decide
    refine ⟨?_, ?_, fun i => ?_⟩
    · rcases hm01 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> simp [hhV]
    · rcases hm01 with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> simp [hhV]
    · rcases h3 i m with rfl | rfl | rfl
      · rcases hm01 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> simp [hhV]
      · rcases hm01 with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> simp [hhV]
      · rw [hm2]; exact F.hhP.le
  have hpure : ∀ i : ℕ, i < 1 → ∃ ε ∈ F.near,
      EdgeIs D ε (F.rpt ((i : ℝ) * (f : ℝ) ^ 2)) (F.rpt (((i : ℝ) + 1) * (f : ℝ) ^ 2)) := by
    intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    refine ⟨(i2, m), hnear, ?_⟩
    have e0 : F.rpt (((0 : ℕ) : ℝ) * (f : ℝ) ^ 2) = F.A := by
      show F.A + (((0 : ℕ) : ℝ) * (f : ℝ) ^ 2) • F.uR = F.A; simp
    have e1 : F.rpt ((((0 : ℕ) : ℝ) + 1) * (f : ℝ) ^ 2) = F.V := by
      show F.A + ((((0 : ℕ) : ℝ) + 1) * (f : ℝ) ^ 2) • F.uR = F.V; rw [F.hV]; simp
    unfold EdgeIs
    rw [e0, e1]
    rcases hm01 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    exact Set.pair_comm _ _
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast he
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast hef
  have hkL : ((1 : ℕ) : ℝ) * (f : ℝ) ^ 2 < (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
    have h1 : (f : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
    have hf0 : (0 : ℝ) < f := by linarith
    push_cast
    nlinarith
  have := chain_point_pierced F 1 le_rfl hkL hpure
  rwa [show F.A + (((1 : ℕ) : ℝ) * (f : ℝ) ^ 2) • F.uR = F.V by rw [F.hV]; simp] at this

/-- **R3, assembled.**  In an `m = 1` frame (coprime `2 ≤ e ≤ f − 2`) whose near side of `r` reads
`c^n`, `d* < b` is impossible.  Proved from G-R3 and `HalfTurnR3R4.r3_arith` (b-pinning below `f·b`,
`d* ∉ S` at `f·b`, Lemma A for early stops).  G-R3 is now PROVED, so this is sorry-free
(conditional on the `HFrame`, i.e. on apex placement + branch (H)). -/
theorem r3_assembly (F : HFrame D e f α β γ) (n : ℕ) (hn : n = nStar f (f ^ 2 - e ^ 2))
    (hpure : ∀ k < n, ∃ ε ∈ F.near,
      EdgeIs D ε (F.rpt ((k : ℝ) * (f : ℝ) ^ 2)) (F.rpt (((k : ℝ) + 1) * (f : ℝ) ^ 2)))
    (hd : dStar f (f ^ 2 - e ^ 2) < f ^ 2 - e ^ 2) : False := by
  obtain ⟨x0, j, ta, tb, tc, na, nb, nc, hj, hshort, hnear, hfar, hnb, hx0⟩ :=
    ray_whole_edge_runs F n hn hpure
  have hee : e ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left (by have := F.hef; omega) 2
  subst hn
  exact r3_arith F.hco F.he F.hef (by omega) hj hshort hnear hfar hnb hx0 hd

/-! ## R4 glue -/

/-- **G-corners — the three known corners at `P′` in (H).**  `T₂` and `T₃` (distinct tiles) present
`γ` at `P′` (the angle opposite their `c`-edges `AV`, `AJ₁`), `K` presents `β` (opposite `K`'s
`b`-edge `V Q₁`).  Plumbing: congruence + side lengths ⇒ corner angle (`sideOpp`, `cornerAngle`;
`MarchSlots.beta_corner_data` / `alpha_corner_data'` are the `e = 1` versions — the general-`e`
`ModelDataE` port noted in `MirrorStripR2Glue.strip_base`).  No new blocker; estimate 100–150 lines.
**PROVED 2026-09-24** (no `sorry`): `localAngle_of_rangeE` (the general-`e` port above) with the
opposite sides `|AV| = |AJ₁| = c`, `|V Q₁| = |AP′| = b`; `T₂ ≠ T₃` because `V = J₁` would force
`uR = uL`, putting the target vertex `A + f³·uL` on `r` beyond `f·b` (`hrbase`). Not a corner-order
statement: no angular order at `P′` is used. -/
theorem corners_at_pprime (F : HFrame D e f α β γ) (hK : Present D F.K) :
    ∃ i2 i3 k : Fin N, i2 ≠ i3 ∧ (D.tile i2).localAngle F.P = γ ∧
      (D.tile i3).localAngle F.P = γ ∧ (D.tile k).localAngle F.P = β := by
  obtain ⟨hab, hac, hbc⟩ := sides_distinct F.hco F.he (by have := F.hef; omega)
  have hloc := fun {i : Fin N} {P Q R : Plane} (hr : Set.range (D.tile i).pts = {P, Q, R}) =>
    localAngle_of_rangeE D hab hac hbc F.hM.hs0 F.hM.hs1 F.hM.hs2 F.hM.hα' F.hM.hβ' F.hM.hγ' hr
  have hf2 : (0 : ℝ) ≤ (f : ℝ) ^ 2 := by positivity
  have hAV : dist F.A F.V = (f : ℝ) ^ 2 := by rw [F.hV]; exact dist_self_add_unit F.huR hf2
  have hAJ : dist F.A (F.A + ((f : ℝ) ^ 2) • F.uL) = (f : ℝ) ^ 2 := dist_self_add_unit F.huL hf2
  obtain ⟨i2, h2⟩ := F.hT2
  obtain ⟨i3, h3⟩ := F.hT3
  obtain ⟨k, hk⟩ := hK
  have h2' : Set.range (D.tile i2).pts = {F.P, F.A, F.V} := by
    rw [h2]; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have h3' : Set.range (D.tile i3).pts = {F.P, F.A, F.A + ((f : ℝ) ^ 2) • F.uL} := by
    rw [h3]; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hk' : Set.range (D.tile k).pts = {F.P, F.V, F.V + F.P - F.A} := by
    rw [hk]; unfold K; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hVQ : dist F.V (F.V + F.P - F.A) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rw [← F.hAP, dist_comm F.V, dist_comm F.A F.P, dist_eq_norm, dist_eq_norm]
    congr 1; abel
  refine ⟨i2, i3, k, ?_, (hloc h2').2.2 hAV, (hloc h3').2.2 hAJ, (hloc hk').2.1 hVQ⟩
  -- T₂ ≠ T₃
  intro heq
  subst heq
  have hVmem : F.V ∈ ({F.A, F.P, F.A + ((f : ℝ) ^ 2) • F.uL} : Set Plane) := by
    rw [← h3, h2]; simp
  have hef := F.hef
  have he := F.he
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast he
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast hef
  have hfpos : (0 : ℝ) < f := by linarith
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hVmem
  rcases hVmem with hVA | hVP | hVJ
  · rw [hVA, dist_self] at hAV; nlinarith
  · have := F.hVP; rw [hVP, dist_self] at this; nlinarith
  · -- `uR = uL`, so the target vertex `A + f³·uL` lies on `r` at distance `f³ > f·b`
    have huRL : F.uR = F.uL := by
      have h' : ((f : ℝ) ^ 2) • F.uR = ((f : ℝ) ^ 2) • F.uL := by
        have := hVJ; rw [F.hV] at this; exact add_left_cancel this
      exact smul_right_injective _ (by positivity : ((f : ℝ) ^ 2) ≠ 0) h'
    have hJ3 : F.A + ((f : ℝ) ^ 3) • F.uL ∈ D.target.carrier := by
      apply subset_convexHull ℝ _
      rw [F.htarget]; simp
    apply F.hrbase ((f : ℝ) * (e : ℝ) ^ 2) (by positivity)
    have : F.A + ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + (f : ℝ) * (e : ℝ) ^ 2) • F.uR
        = F.A + ((f : ℝ) ^ 3) • F.uL := by
      rw [huRL]; congr 2; ring
    rw [this]; exact hJ3

-- [G5SORRY 2026-10-01] removed sorry-bodied glue statement `pprime_order` (unused; real proof in the *Real/primed files).

-- [G5SORRY 2026-10-01] removed sorry-bodied glue statement `t2pprime_forced` (unused; real proof in the *Real/primed files).

-- [G5SORRY 2026-10-01] removed sorry-bodied glue statement `level2_lemmaG` (unused; real proof in the *Real/primed files).

-- [G5SORRY 2026-10-01] removed sorry-bodied glue statement `r4_figure_at_pprime` (unused; real proof in the *Real/primed files).

end HFrame

end Erdos634.Draft.HalfTurnR3R4Glue

#print axioms Erdos634.Draft.HalfTurnR3R4Glue.HFrame.ray_whole_edge_runs
#print axioms Erdos634.Draft.HalfTurnR3R4Glue.HFrame.chain_point_pierced
#print axioms Erdos634.Draft.HalfTurnR3R4Glue.HFrame.V_pierced
#print axioms Erdos634.Draft.HalfTurnR3R4Glue.HFrame.r3_assembly
#print axioms Erdos634.Draft.HalfTurnR3R4Glue.HFrame.corners_at_pprime
