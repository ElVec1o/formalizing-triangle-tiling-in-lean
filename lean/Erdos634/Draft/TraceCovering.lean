-- Draft/TraceCovering.lean — TRACE COVERING (blocker F2) as a general theorem over a `Dissection`.
-- Imported by All.lean (All.lean line 416: import Erdos634.Draft.TraceCovering).  Imports corpus modules only (no Draft imports), so it builds with
--   lake env lean -o $S/Erdos634/Draft/TraceCovering.olean Erdos634/Draft/TraceCovering.lean
-- where `$S` is a scratch olean directory (never `.lake`).
import Mathlib.Tactic
import Erdos634.WallChain

/-!
# Trace covering: the ordered whole-edge covering of a line from a point

Erdős #634, the geometric layer of Theorem H ((private working notes, not included) §2.5, §4 row TC;
blocker F2).  Statement (the reviewer's form, `review_H_1/REVIEW.md` §5, repair R-5): let `ℓ` be a
line, `X ∈ ℓ` a point through which **no edge on `ℓ` passes** (no tile edge lying on `ℓ` has `X` in its
relative interior).  If the ray of `ℓ` from `X` starts with a tile edge (of either side), then both
sides of `ℓ` are covered by whole tile edges from `X` up to the **first common junction** `x₀`
(or the target boundary), the junction positions of each side are the partial sums of its edge
lengths, and no point strictly between `X` and `x₀` is a junction of both sides.

What the corpus already had (cited, not re-proved): `WallChain.wall_cover` (a non-vertex point of an
interior wall lies on a chain edge of each side), `EdgeChain.sameside_edges_subsingleton` (same-side
chain edges overlap in at most a point), `WallChain.edge_point_not_interior` (edge points are walls),
`IntervalChain` (the order theory of an interval cover of `[0, L]` whose ends are given), and
`TP_erdos.chain_edge_lengths_sum` (one side of a chord CLAMPED BY THE TARGET BOUNDARY at both ends sums
to the chord).  What was missing (recorded as "the ORDER extraction ... not yet formalized" in
`RogueChord.lean`, `ChordInterface.lean`, `Dissection.lean` G3 note, and as blocker F2): the covering
between two points that are merely NOT STRADDLED (interior junctions), and the iterated two-sided run
to the first common junction.  This file supplies both.

Overlaps (cited, not claimed): `exists_param` re-derives `ChordTraceReal.ker_finrank_one` inline;
`near_interior_of_across` is the one-point-on-the-line variant of
`ChordOpenSegmentInterior.Tri.straddle_openSegment_interior` (two points on the line); the pure 1-D
covering order is `IntervalChain` (whose `Cover` needs both ends given, which is what `sum_inside_eq`
supplies from "not straddled").  The mathematics of TC is the paper's `prop:chorddecomp` (a)/(b)
argument, `W/proof_S2.md`'s supplement and `review_H_1/REVIEW.md` §5: known, PROVED; new here is the
Lean.

* §1 — pure 1-D: `sum_inside_eq` (intervals with pairwise ≤ 1-point overlaps covering `(s, t)` up to a
  finite set, none straddling `s` or `t`: the ones inside `[s, t]` have lengths summing to `t − s`);
  `first_common_junction_1d` (the two-sided run).
* §2–§4 — the line parametrization `X + x • u` and the dictionary edge ↔ parameter interval.
* §5 — the geometric theorems: `wall_sum` (one side, between two non-straddled points of a wall) and
  `trace_covering` (both sides, from a non-straddled seed point to the first common junction).
* §7 — `junction_partial_sum`: every endpoint of a same-side edge in the stretch is at distance from
  `X` equal to the total length of that side's edges before it — the junction positions are the
  partial sums (the ordered-word form).
* §6 — discharging the start condition: `not_straddled_of_outside_after/_before` (target boundary),
  `not_straddled_of_tile_across` (a tile containing the point with points strictly on both sides of
  the line — e.g. `T₂` at `P′` for the line `L ∥` leg).

Axiom-clean; no `sorry`.
-/

namespace Erdos634.Draft.TraceCovering

open Erdos634.Geometry Set MeasureTheory

/-! ## §1 One-dimensional bookkeeping -/

section OneD

variable {ι : Type*}

/-- `x` is straddled by the parameter intervals `[lo i, hi i]`, `i ∈ S`. -/
def PStr (S : Finset ι) (lo hi : ι → ℝ) (x : ℝ) : Prop := ∃ i ∈ S, lo i < x ∧ x < hi i

/-- `x` is covered by the parameter intervals `[lo i, hi i]`, `i ∈ S`. -/
def PCov (S : Finset ι) (lo hi : ι → ℝ) (x : ℝ) : Prop := ∃ i ∈ S, lo i ≤ x ∧ x ≤ hi i

theorem pstr_iff_mem_iUnion (S : Finset ι) (lo hi : ι → ℝ) (x : ℝ) :
    PStr S lo hi x ↔ x ∈ ⋃ i ∈ S, Ioo (lo i) (hi i) := by
  simp only [PStr, Set.mem_iUnion, Set.mem_Ioo, exists_prop]

theorem isClosed_not_pstr (S : Finset ι) (lo hi : ι → ℝ) :
    IsClosed {x | ¬ PStr S lo hi x} := by
  have : {x | ¬ PStr S lo hi x} = (⋃ i ∈ S, Ioo (lo i) (hi i))ᶜ := by
    ext x; rw [Set.mem_setOf_eq, Set.mem_compl_iff, ← pstr_iff_mem_iUnion]
  rw [this, isClosed_compl_iff]
  exact isOpen_biUnion fun i _ => isOpen_Ioo

open Classical in
/-- **The one-sided sum.**  A finite family of intervals meeting pairwise in at most a point, covering
`(s, t)` outside a finite set, none of which straddles `s` or `t`: the intervals inside `[s, t]` have
total length `t − s`. -/
theorem sum_inside_eq (S : Finset ι) (lo hi : ι → ℝ) (hle : ∀ i ∈ S, lo i ≤ hi i)
    (hmeet : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (Icc (lo i) (hi i) ∩ Icc (lo j) (hi j)).Subsingleton)
    {s t : ℝ} (hst : s ≤ t) (F : Set ℝ) (hF : F.Finite)
    (hcov : ∀ x ∈ Ioo s t, x ∉ F → PCov S lo hi x)
    (hs : ¬ PStr S lo hi s) (ht : ¬ PStr S lo hi t) :
    ∑ i ∈ S.filter (fun i => s ≤ lo i ∧ hi i ≤ t), (hi i - lo i) = t - s := by
  set I := S.filter (fun i => s ≤ lo i ∧ hi i ≤ t) with hI
  set U : Set ℝ := ⋃ i ∈ I, Icc (lo i) (hi i) with hU
  have hmeas : volume U = ∑ i ∈ I, volume (Icc (lo i) (hi i)) := by
    refine measure_biUnion_finset₀ ?_ (fun i _ => measurableSet_Icc.nullMeasurableSet)
    intro i hi j hj hij
    exact (hmeet i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hij).measure_zero volume
  have hsub : U ⊆ Icc s t := by
    intro x hx
    obtain ⟨i, hiI, hxi⟩ := Set.mem_iUnion₂.mp hx
    have := (Finset.mem_filter.mp hiI).2
    exact ⟨this.1.trans hxi.1, hxi.2.trans this.2⟩
  have hsup : Icc s t ⊆ U ∪ (F ∪ {s, t}) := by
    intro x hx
    by_cases hxs : x = s
    · exact Or.inr (Or.inr (by simp [hxs]))
    by_cases hxt : x = t
    · exact Or.inr (Or.inr (by simp [hxt]))
    by_cases hxF : x ∈ F
    · exact Or.inr (Or.inl hxF)
    left
    have hxo : x ∈ Ioo s t := ⟨lt_of_le_of_ne hx.1 (Ne.symm hxs), lt_of_le_of_ne hx.2 hxt⟩
    obtain ⟨i, hiS, h1, h2⟩ := hcov x hxo hxF
    refine Set.mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨hiS, ?_, ?_⟩, h1, h2⟩
    · by_contra hc
      push Not at hc
      exact hs ⟨i, hiS, hc, lt_of_lt_of_le hxo.1 h2⟩
    · by_contra hc
      push Not at hc
      exact ht ⟨i, hiS, lt_of_le_of_lt h1 hxo.2, hc⟩
  have hnull : volume (F ∪ {s, t}) = 0 :=
    (hF.union ((Set.finite_singleton t).insert s)).measure_zero volume
  have hU_eq : volume U = ENNReal.ofReal (t - s) := by
    apply le_antisymm
    · rw [← Real.volume_Icc]; exact measure_mono hsub
    · rw [← Real.volume_Icc]
      calc volume (Icc s t) ≤ volume (U ∪ (F ∪ {s, t})) := measure_mono hsup
        _ ≤ volume U + volume (F ∪ {s, t}) := measure_union_le _ _
        _ = volume U := by rw [hnull, add_zero]
  rw [hmeas] at hU_eq
  simp only [Real.volume_Icc] at hU_eq
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i hi =>
    sub_nonneg.mpr (hle i (Finset.mem_filter.mp hi).1))] at hU_eq
  exact (ENNReal.ofReal_eq_ofReal_iff (Finset.sum_nonneg fun i hi =>
    sub_nonneg.mpr (hle i (Finset.mem_filter.mp hi).1)) (sub_nonneg.mpr hst)).mp hU_eq

open Classical in
/-- **The two-sided run to the first common junction (1-D).**  Two interval families (the two sides
of a line) on `[0, L]`, neither straddling `0` or `L`; the points of `(0, ℓ)` are straddled (a seed
edge); and wherever a stretch `(a, b)` is entirely straddled by one side or the other it is covered by
BOTH sides outside a finite set (the wall property).  Then there is a first common junction
`x₀ ∈ [ℓ, L]`: straddled by neither side, every point of `(0, x₀)` straddled by some side, and each
side's intervals inside `[0, x₀]` have total length `x₀`. -/
theorem first_common_junction_1d (S₁ S₂ : Finset ι) (lo hi : ι → ℝ)
    (hle₁ : ∀ i ∈ S₁, lo i ≤ hi i) (hle₂ : ∀ i ∈ S₂, lo i ≤ hi i)
    (hmeet₁ : ∀ i ∈ S₁, ∀ j ∈ S₁, i ≠ j → (Icc (lo i) (hi i) ∩ Icc (lo j) (hi j)).Subsingleton)
    (hmeet₂ : ∀ i ∈ S₂, ∀ j ∈ S₂, i ≠ j → (Icc (lo i) (hi i) ∩ Icc (lo j) (hi j)).Subsingleton)
    {ℓ L : ℝ} (hℓ : 0 < ℓ) (hℓL : ℓ ≤ L)
    (hseed : ∀ y ∈ Ioo 0 ℓ, PStr S₁ lo hi y ∨ PStr S₂ lo hi y)
    (h0 : ¬ PStr S₁ lo hi 0 ∧ ¬ PStr S₂ lo hi 0)
    (hL : ¬ PStr S₁ lo hi L ∧ ¬ PStr S₂ lo hi L)
    (F : Set ℝ) (hF : F.Finite)
    (hwall : ∀ a b, 0 ≤ a → b ≤ L → (∀ y ∈ Ioo a b, PStr S₁ lo hi y ∨ PStr S₂ lo hi y) →
      ∀ x ∈ Ioo a b, x ∉ F → PCov S₁ lo hi x ∧ PCov S₂ lo hi x) :
    ∃ x₀, ℓ ≤ x₀ ∧ x₀ ≤ L ∧ ¬ PStr S₁ lo hi x₀ ∧ ¬ PStr S₂ lo hi x₀ ∧
      (∀ y ∈ Ioo 0 x₀, PStr S₁ lo hi y ∨ PStr S₂ lo hi y) ∧
      ∑ i ∈ S₁.filter (fun i => 0 ≤ lo i ∧ hi i ≤ x₀), (hi i - lo i) = x₀ ∧
      ∑ i ∈ S₂.filter (fun i => 0 ≤ lo i ∧ hi i ≤ x₀), (hi i - lo i) = x₀ := by
  set G : Set ℝ := Icc ℓ L ∩ ({x | ¬ PStr S₁ lo hi x} ∩ {x | ¬ PStr S₂ lo hi x}) with hG
  have hGc : IsCompact G :=
    isCompact_Icc.inter_right ((isClosed_not_pstr S₁ lo hi).inter (isClosed_not_pstr S₂ lo hi))
  have hLG : L ∈ G := ⟨⟨hℓL, le_rfl⟩, hL.1, hL.2⟩
  have hGne : G.Nonempty := ⟨L, hLG⟩
  set x₀ := sInf G with hx₀
  have hx₀G : x₀ ∈ G := hGc.sInf_mem hGne
  have hbdd : BddBelow G := hGc.bddBelow
  obtain ⟨⟨hℓx, hxL⟩, hn₁, hn₂⟩ := hx₀G
  have hmin : ∀ y ∈ Ioo 0 x₀, PStr S₁ lo hi y ∨ PStr S₂ lo hi y := by
    intro y hy
    by_cases hyℓ : y < ℓ
    · exact hseed y ⟨hy.1, hyℓ⟩
    · by_contra hc
      push Not at hc
      have hyG : y ∈ G := ⟨⟨not_lt.mp hyℓ, (le_of_lt hy.2).trans hxL⟩, hc.1, hc.2⟩
      exact absurd (csInf_le hbdd hyG) (not_le.mpr hy.2)
  have hx0pos : 0 < x₀ := lt_of_lt_of_le hℓ hℓx
  have hcov := hwall 0 x₀ le_rfl hxL hmin
  refine ⟨x₀, hℓx, hxL, hn₁, hn₂, hmin, ?_, ?_⟩
  · have := sum_inside_eq S₁ lo hi hle₁ hmeet₁ hx0pos.le F hF (fun x hx hxF => (hcov x hx hxF).1)
      h0.1 hn₁
    rwa [sub_zero] at this
  · have := sum_inside_eq S₂ lo hi hle₂ hmeet₂ hx0pos.le F hF (fun x hx hxF => (hcov x hx hxF).2)
      h0.2 hn₂
    rwa [sub_zero] at this

end OneD

/-! ## §2 The line parametrization `x ↦ X + x • u` -/

section Line

variable {N : ℕ} {f : Plane →ₗ[ℝ] ℝ} {c : ℝ} {X u : Plane}

/-- Every point of the line `{f = c}` is `X + s • u` (the kernel of `f ≠ 0` is the line `ℝu`). -/
theorem exists_param (hf : f ≠ 0) (hX : f X = c) (hu : f u = 0) (hu0 : u ≠ 0)
    {y : Plane} (hy : f y = c) : ∃ s : ℝ, y = X + s • u := by
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  have hdim : Module.finrank ℝ Plane = 2 := finrank_euclideanSpace_fin
  have hrange : Module.finrank ℝ (LinearMap.range f) = 1 := by
    have htop : LinearMap.range f = ⊤ := by
      obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
        by_contra h; push Not at h; exact hf (LinearMap.ext h)
      rw [eq_top_iff]; intro r _
      exact ⟨(r / f v) • v, by simp [hv]⟩
    rw [htop, finrank_top, Module.finrank_self]
  have hk1 : Module.finrank ℝ (LinearMap.ker f) = 1 := by omega
  obtain ⟨s, hs⟩ := (finrank_eq_one_iff_of_nonzero'
      (⟨u, LinearMap.mem_ker.mpr hu⟩ : LinearMap.ker f) (by simpa using hu0)).mp hk1
      ⟨y - X, LinearMap.mem_ker.mpr (by rw [map_sub, hy, hX, sub_self])⟩
  have h2 : s • u = y - X := by simpa using congrArg Subtype.val hs
  exact ⟨s, by rw [h2]; abel⟩

open Classical in
/-- The parameter of a point of the line (junk `0` off the line). -/
noncomputable def par (X u y : Plane) : ℝ := if h : ∃ s : ℝ, y = X + s • u then h.choose else 0

theorem par_spec {y : Plane} (h : ∃ s : ℝ, y = X + s • u) : y = X + par X u y • u := by
  unfold par; rw [dif_pos h]; exact h.choose_spec

theorem par_add (hu0 : u ≠ 0) (s : ℝ) : par X u (X + s • u) = s := by
  have h : ∃ t : ℝ, X + s • u = X + t • u := ⟨s, rfl⟩
  have := add_left_cancel (par_spec h)
  exact (smul_left_injective ℝ hu0 this).symm

/-- The line as an affine map `ℝ → Plane`. -/
noncomputable def lm (X u : Plane) : ℝ →ᵃ[ℝ] Plane := AffineMap.lineMap X (X + u)

theorem lm_apply (s : ℝ) : lm X u s = X + s • u := by
  simp only [lm, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_sub_cancel_left]
  abel

theorem lm_injective (hu0 : u ≠ 0) : Function.Injective (fun s : ℝ => X + s • u) := by
  intro s t h
  exact smul_left_injective ℝ hu0 (add_left_cancel h)

theorem segment_param (s t : ℝ) :
    segment ℝ (X + s • u) (X + t • u) = (fun x : ℝ => X + x • u) '' Icc (min s t) (max s t) := by
  have h := image_segment ℝ (lm X u) s t
  simp only [lm_apply] at h
  rw [← h, segment_eq_Icc']

theorem openSegment_param {s t : ℝ} (hst : s ≠ t) :
    openSegment ℝ (X + s • u) (X + t • u) =
      (fun x : ℝ => X + x • u) '' Ioo (min s t) (max s t) := by
  have h := image_openSegment ℝ (lm X u) s t
  simp only [lm_apply] at h
  rw [← h, openSegment_eq_Ioo' hst]

theorem dist_param (hu1 : ‖u‖ = 1) (s t : ℝ) :
    dist (X + s • u) (X + t • u) = max s t - min s t := by
  rw [dist_eq_norm, show X + s • u - (X + t • u) = (s - t) • u by module, norm_smul, hu1,
    mul_one, Real.norm_eq_abs, max_sub_min_eq_abs']

end Line

/-! ## §3 Chain edges as parameter intervals -/

theorem fin3_succ_ne : ∀ x : Fin 3, x ≠ x + 1 := by decide

section Edges

variable {N : ℕ} (D : Dissection N) (X u : Plane)

/-- Lower parameter of the edge `e` (the smaller of its two endpoints' parameters). -/
noncomputable def lo (e : Fin N × Fin 3) : ℝ :=
  min (par X u ((D.tile e.1).pts e.2)) (par X u ((D.tile e.1).pts (e.2 + 1)))

/-- Upper parameter of the edge `e`. -/
noncomputable def hi (e : Fin N × Fin 3) : ℝ :=
  max (par X u ((D.tile e.1).pts e.2)) (par X u ((D.tile e.1).pts (e.2 + 1)))

/-- `y` is straddled from the side `lineChain f c`: an edge of that chain has `y` in its relative
interior ("an edge on the line passes through `y`"). -/
def Straddled (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (y : Plane) : Prop :=
  ∃ e ∈ D.lineChain f c, y ∈ openSegment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))

variable {D X u} {f : Plane →ₗ[ℝ] ℝ} {c : ℝ}

/-- The data of a chain edge on the line `{f = c}` read in the parametrization. -/
theorem edge_data (hf : f ≠ 0) (hX : f X = c) (hu : f u = 0) (hu0 : u ≠ 0)
    {e : Fin N × Fin 3}
    (h0 : f ((D.tile e.1).pts e.2) = c) (h1 : f ((D.tile e.1).pts (e.2 + 1)) = c) :
    lo D X u e < hi D X u e ∧
    (D.tile e.1).edge e.2 = (fun x : ℝ => X + x • u) '' Icc (lo D X u e) (hi D X u e) ∧
    openSegment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) =
      (fun x : ℝ => X + x • u) '' Ioo (lo D X u e) (hi D X u e) ∧
    (‖u‖ = 1 → dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) =
      hi D X u e - lo D X u e) := by
  have e0 := par_spec (exists_param hf hX hu hu0 h0)
  have e1 := par_spec (exists_param hf hX hu hu0 h1)
  have hne : (D.tile e.1).pts e.2 ≠ (D.tile e.1).pts (e.2 + 1) :=
    (D.tile e.1).indep.injective.ne (fin3_succ_ne e.2)
  have hpne : par X u ((D.tile e.1).pts e.2) ≠ par X u ((D.tile e.1).pts (e.2 + 1)) := by
    intro h; apply hne; rw [e0, e1, h]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [lo, hi]; exact min_lt_max.mpr hpne
  · rw [Tri.edge, e0, e1, segment_param]; rfl
  · rw [e0, e1, openSegment_param hpne]; rfl
  · intro hu1
    rw [e0, e1, dist_param hu1]; rfl

end Edges

/-! ## §4 The dictionary: straddle, cover, overlap, inclusion -/

section Dictionary

variable {N : ℕ} {D : Dissection N} {X u : Plane} {f g : Plane →ₗ[ℝ] ℝ} {c d : ℝ}

theorem f_param (hX : f X = c) (hu : f u = 0) (s : ℝ) : f (X + s • u) = c := by
  rw [map_add, map_smul, hX, hu, smul_zero, add_zero]

theorem ne_zero_of_norm (hu1 : ‖u‖ = 1) : u ≠ 0 := by
  intro h; rw [h, norm_zero] at hu1; exact zero_ne_one hu1

/-- Edges of the chain `lineChain g d` of the line `{g = d} = {f = c}` have both ends on `{f = c}`. -/
theorem onLine (hgd : ∀ y, g y = d ↔ f y = c) {e : Fin N × Fin 3} (he : e ∈ D.lineChain g d) :
    f ((D.tile e.1).pts e.2) = c ∧ f ((D.tile e.1).pts (e.2 + 1)) = c := by
  obtain ⟨h0, h1, -⟩ := Dissection.mem_lineChain.mp he
  exact ⟨(hgd _).mp h0, (hgd _).mp h1⟩

theorem str_iff (hgd : ∀ y, g y = d ↔ f y = c) (hf : f ≠ 0) (hX : f X = c) (hu : f u = 0)
    (hu0 : u ≠ 0) (x : ℝ) :
    Straddled D g d (X + x • u) ↔ PStr (D.lineChain g d) (lo D X u) (hi D X u) x := by
  constructor
  · rintro ⟨e, he, hx⟩
    obtain ⟨h0, h1⟩ := onLine hgd he
    rw [(edge_data hf hX hu hu0 h0 h1).2.2.1, (lm_injective hu0).mem_set_image] at hx
    exact ⟨e, he, hx.1, hx.2⟩
  · rintro ⟨e, he, hx1, hx2⟩
    obtain ⟨h0, h1⟩ := onLine hgd he
    refine ⟨e, he, ?_⟩
    rw [(edge_data hf hX hu hu0 h0 h1).2.2.1, (lm_injective hu0).mem_set_image]
    exact ⟨hx1, hx2⟩

theorem mem_edge_iff (hgd : ∀ y, g y = d ↔ f y = c) (hf : f ≠ 0) (hX : f X = c) (hu : f u = 0)
    (hu0 : u ≠ 0) {e : Fin N × Fin 3} (he : e ∈ D.lineChain g d) (x : ℝ) :
    X + x • u ∈ (D.tile e.1).edge e.2 ↔ lo D X u e ≤ x ∧ x ≤ hi D X u e := by
  obtain ⟨h0, h1⟩ := onLine hgd he
  rw [(edge_data hf hX hu hu0 h0 h1).2.1, (lm_injective hu0).mem_set_image]
  rfl

theorem meet (hg : g ≠ 0) (hgd : ∀ y, g y = d ↔ f y = c) (hf : f ≠ 0) (hX : f X = c)
    (hu : f u = 0) (hu0 : u ≠ 0) :
    ∀ e ∈ D.lineChain g d, ∀ e' ∈ D.lineChain g d, e ≠ e' →
      (Icc (lo D X u e) (hi D X u e) ∩ Icc (lo D X u e') (hi D X u e')).Subsingleton := by
  intro e he e' he' hne x hx y hy
  have hle : ∀ {e : Fin N × Fin 3}, e ∈ D.lineChain g d → ∀ z ∈ (D.tile e.1).carrier, g z ≤ d :=
    fun he => (D.tile _).carrier_subset_halfplane g d (Dissection.mem_lineChain.mp he).2.2
  have hsub := D.sameside_edges_subsingleton g d hg hne (hle he) (hle he')
    (D.lineChain_edge_subset he) (D.lineChain_edge_subset he')
  have hmx : X + x • u ∈ (D.tile e.1).edge e.2 ∩ (D.tile e'.1).edge e'.2 :=
    ⟨(mem_edge_iff hgd hf hX hu hu0 he x).mpr hx.1, (mem_edge_iff hgd hf hX hu hu0 he' x).mpr hx.2⟩
  have hmy : X + y • u ∈ (D.tile e.1).edge e.2 ∩ (D.tile e'.1).edge e'.2 :=
    ⟨(mem_edge_iff hgd hf hX hu hu0 he y).mpr hy.1, (mem_edge_iff hgd hf hX hu hu0 he' y).mpr hy.2⟩
  exact lm_injective hu0 (hsub hmx hmy)

theorem inside_iff (hgd : ∀ y, g y = d ↔ f y = c) (hf : f ≠ 0) (hX : f X = c) (hu : f u = 0)
    (hu0 : u ≠ 0) {e : Fin N × Fin 3} (he : e ∈ D.lineChain g d) {s t : ℝ} (hst : s ≤ t) :
    (D.tile e.1).edge e.2 ⊆ segment ℝ (X + s • u) (X + t • u) ↔
      s ≤ lo D X u e ∧ hi D X u e ≤ t := by
  obtain ⟨h0, h1⟩ := onLine hgd he
  obtain ⟨hlt, hedge, -, -⟩ := edge_data hf hX hu hu0 h0 h1
  rw [hedge, segment_param, min_eq_left hst, max_eq_right hst,
    Set.image_subset_image_iff (lm_injective hu0), Set.Icc_subset_Icc_iff hlt.le]

/-- **Wall cover in the parametrization** (`WallChain.wall_cover` on a sub-segment). -/
theorem wall_cover_param (hg : g ≠ 0) (hgd : ∀ y, g y = d ↔ f y = c) (hf : f ≠ 0)
    (hX : f X = c) (hu : f u = 0) (hu0 : u ≠ 0) {a b : ℝ} (hab : a < b)
    (hint : ∀ x ∈ Ioo a b, X + x • u ∈ interior D.target.carrier)
    (hwall : ∀ x ∈ Ioo a b, ∀ i, X + x • u ∉ interior (D.tile i).carrier)
    {x : ℝ} (hx : x ∈ Ioo a b) (hxv : X + x • u ∉ D.vertexSet) :
    PCov (D.lineChain g d) (lo D X u) (hi D X u) x := by
  have hne : X + a • u ≠ X + b • u := fun h => hab.ne (lm_injective hu0 h)
  have hopen := openSegment_param (X := X) (u := u) hab.ne
  rw [min_eq_left hab.le, max_eq_right hab.le] at hopen
  have hS : segment ℝ (X + a • u) (X + b • u) ⊆ {y | g y = d} := by
    intro y hy
    rw [segment_param] at hy
    obtain ⟨s, -, rfl⟩ := hy
    exact (hgd _).mpr (f_param hX hu s)
  have hint' : openSegment ℝ (X + a • u) (X + b • u) ⊆ interior D.target.carrier := by
    rw [hopen]; rintro y ⟨s, hs, rfl⟩; exact hint s hs
  have hwall' : ∀ y ∈ openSegment ℝ (X + a • u) (X + b • u), ∀ i,
      y ∉ interior (D.tile i).carrier := by
    rw [hopen]; rintro y ⟨s, hs, rfl⟩; exact hwall s hs
  have hx' : X + x • u ∈ openSegment ℝ (X + a • u) (X + b • u) := by
    rw [hopen]; exact ⟨x, hx, rfl⟩
  obtain ⟨e, he, hxe⟩ := D.wall_cover g d hg hne hS hint' hwall' hx' hxv
  exact ⟨e, he, (mem_edge_iff hgd hf hX hu hu0 he x).mp hxe⟩

theorem finite_vertex_params (hu0 : u ≠ 0) :
    {x : ℝ | X + x • u ∈ D.vertexSet}.Finite :=
  D.vertexSet_finite.preimage (lm_injective hu0).injOn

end Dictionary

/-! ## §5 Trace covering -/

section Main

variable {N : ℕ} {D : Dissection N} {X u : Plane} {f g : Plane →ₗ[ℝ] ℝ} {c d : ℝ}

open Classical in
/-- **Trace covering, one side (TC-1).**  Let `[X + s•u, X + t•u]` be a stretch of the line
`{f = c}` whose open part is inside the target and meets no tile interior (a wall), and let neither
end be straddled from the side `lineChain g d` (`{g = d} = {f = c}`; `g = f` for the side `{f ≤ c}`,
`g = −f` for the other).  Then the edges of that side lying in the stretch are whole edges with total
length `t − s`.  (Generalizes `TP_erdos.chain_edge_lengths_sum`, whose ends are clamped by the target
boundary, to ends that are merely junctions.) -/
theorem wall_sum (hg : g ≠ 0) (hgd : ∀ y, g y = d ↔ f y = c) (hf : f ≠ 0) (hX : f X = c)
    (hu : f u = 0) (hu1 : ‖u‖ = 1) {s t : ℝ} (hst : s ≤ t)
    (hint : ∀ x ∈ Ioo s t, X + x • u ∈ interior D.target.carrier)
    (hwall : ∀ x ∈ Ioo s t, ∀ i, X + x • u ∉ interior (D.tile i).carrier)
    (hs : ¬ Straddled D g d (X + s • u)) (ht : ¬ Straddled D g d (X + t • u)) :
    ∑ e ∈ (D.lineChain g d).filter
        (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ (X + s • u) (X + t • u)),
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = t - s := by
  have hu0 := ne_zero_of_norm hu1
  have hle : ∀ e ∈ D.lineChain g d, lo D X u e ≤ hi D X u e := fun e he =>
    (edge_data hf hX hu hu0 (onLine hgd he).1 (onLine hgd he).2).1.le
  have key := sum_inside_eq (D.lineChain g d) (lo D X u) (hi D X u) hle
    (meet hg hgd hf hX hu hu0) hst _ (finite_vertex_params hu0)
    (fun x hx hxv => wall_cover_param hg hgd hf hX hu hu0 (lt_trans hx.1 hx.2) hint hwall hx hxv)
    ((str_iff hgd hf hX hu hu0 s).not.mp hs) ((str_iff hgd hf hX hu hu0 t).not.mp ht)
  rw [← key]
  rw [Finset.filter_congr (fun e he => inside_iff hgd hf hX hu hu0 he hst)]
  refine Finset.sum_congr rfl fun e he => ?_
  have he' := (Finset.mem_filter.mp he).1
  exact (edge_data hf hX hu hu0 (onLine hgd he').1 (onLine hgd he').2).2.2.2 hu1

theorem neg_iff (y : Plane) : (-f) y = -c ↔ f y = c := by
  rw [LinearMap.neg_apply, neg_inj]

open Classical in
/-- **TRACE COVERING (TC), two-sided, to the first common junction.**  On the line `{f = c}`,
parametrized by `X + x•u` (`‖u‖ = 1`): suppose the open stretch `(X, X + L•u)` is inside the target,
**no edge on the line passes through `X` or `X + L•u`** (from either side), and the ray starts with a
tile edge `[X, X + ℓ•u]` of either side.  Then there is a first common junction `X + x₀•u`,
`ℓ ≤ x₀ ≤ L`: no edge of either side passes through it; every point strictly between `X` and it is
passed through by an edge of one side (so no common junction occurs before it); and on EACH side the
whole edges lying in `[X, X + x₀•u]` have total length `x₀` — i.e. both sides are whole-edge words of
the same value `x₀`. -/
theorem trace_covering (hf : f ≠ 0) (hX : f X = c) (hu : f u = 0) (hu1 : ‖u‖ = 1)
    {ℓ L : ℝ} (hℓ : 0 < ℓ) (hℓL : ℓ ≤ L)
    (hint : ∀ x ∈ Ioo 0 L, X + x • u ∈ interior D.target.carrier)
    (hstart : ¬ Straddled D f c X ∧ ¬ Straddled D (-f) (-c) X)
    (hend : ¬ Straddled D f c (X + L • u) ∧ ¬ Straddled D (-f) (-c) (X + L • u))
    (hseed : ∃ e ∈ D.lineChain f c ∪ D.lineChain (-f) (-c),
      (D.tile e.1).edge e.2 = segment ℝ X (X + ℓ • u)) :
    ∃ x₀, ℓ ≤ x₀ ∧ x₀ ≤ L ∧
      ¬ Straddled D f c (X + x₀ • u) ∧ ¬ Straddled D (-f) (-c) (X + x₀ • u) ∧
      (∀ y ∈ Ioo 0 x₀, Straddled D f c (X + y • u) ∨ Straddled D (-f) (-c) (X + y • u)) ∧
      ∑ e ∈ (D.lineChain f c).filter
          (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ X (X + x₀ • u)),
        dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = x₀ ∧
      ∑ e ∈ (D.lineChain (-f) (-c)).filter
          (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ X (X + x₀ • u)),
        dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = x₀ := by
  have hu0 := ne_zero_of_norm hu1
  have hf' : (-f : Plane →ₗ[ℝ] ℝ) ≠ 0 := fun h => hf (neg_eq_zero.mp h)
  have hgd₁ : ∀ y, f y = c ↔ f y = c := fun _ => Iff.rfl
  have hgd₂ : ∀ y, (-f) y = -c ↔ f y = c := neg_iff
  have hX0 : X = X + (0 : ℝ) • u := by rw [zero_smul, add_zero]
  set S₁ := D.lineChain f c
  set S₂ := D.lineChain (-f) (-c)
  have hs₁ := str_iff (D := D) hgd₁ hf hX hu hu0
  have hs₂ := str_iff (D := D) hgd₂ hf hX hu hu0
  have hle₁ : ∀ e ∈ S₁, lo D X u e ≤ hi D X u e := fun e he =>
    (edge_data hf hX hu hu0 (onLine hgd₁ he).1 (onLine hgd₁ he).2).1.le
  have hle₂ : ∀ e ∈ S₂, lo D X u e ≤ hi D X u e := fun e he =>
    (edge_data hf hX hu hu0 (onLine hgd₂ he).1 (onLine hgd₂ he).2).1.le
  -- the seed edge is the parameter interval `[0, ℓ]`
  have hseed' : ∀ y ∈ Ioo 0 ℓ, PStr S₁ (lo D X u) (hi D X u) y ∨ PStr S₂ (lo D X u) (hi D X u) y := by
    obtain ⟨e, he, hedge⟩ := hseed
    have hseg : segment ℝ X (X + ℓ • u) = (fun x : ℝ => X + x • u) '' Icc 0 ℓ := by
      have h1 : segment ℝ X (X + ℓ • u) = segment ℝ (X + (0 : ℝ) • u) (X + ℓ • u) := by
        rw [zero_smul, add_zero]
      rw [h1, segment_param, min_eq_left hℓ.le, max_eq_right hℓ.le]
    intro y hy
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨h0, h1⟩ := onLine hgd₁ he
      obtain ⟨hlt, hE, -, -⟩ := edge_data hf hX hu hu0 h0 h1
      rw [hE, hseg, Set.image_eq_image (lm_injective hu0), Set.Icc_eq_Icc_iff hlt.le] at hedge
      exact Or.inl ⟨e, he, by rw [hedge.1]; exact hy.1, by rw [hedge.2]; exact hy.2⟩
    · obtain ⟨h0, h1⟩ := onLine hgd₂ he
      obtain ⟨hlt, hE, -, -⟩ := edge_data hf hX hu hu0 h0 h1
      rw [hE, hseg, Set.image_eq_image (lm_injective hu0), Set.Icc_eq_Icc_iff hlt.le] at hedge
      exact Or.inr ⟨e, he, by rw [hedge.1]; exact hy.1, by rw [hedge.2]; exact hy.2⟩
  have h0 : ¬ PStr S₁ (lo D X u) (hi D X u) 0 ∧ ¬ PStr S₂ (lo D X u) (hi D X u) 0 := by
    rw [← (hs₁ 0).not, ← (hs₂ 0).not, ← hX0]; exact hstart
  have hL : ¬ PStr S₁ (lo D X u) (hi D X u) L ∧ ¬ PStr S₂ (lo D X u) (hi D X u) L := by
    rw [← (hs₁ L).not, ← (hs₂ L).not]; exact hend
  -- the wall property: a stretch straddled throughout is covered by both sides
  have hwall : ∀ a b, 0 ≤ a → b ≤ L →
      (∀ y ∈ Ioo a b, PStr S₁ (lo D X u) (hi D X u) y ∨ PStr S₂ (lo D X u) (hi D X u) y) →
      ∀ x ∈ Ioo a b, x ∉ {x : ℝ | X + x • u ∈ D.vertexSet} →
        PCov S₁ (lo D X u) (hi D X u) x ∧ PCov S₂ (lo D X u) (hi D X u) x := by
    intro a b ha hb hstr x hx hxv
    have hint' : ∀ y ∈ Ioo a b, X + y • u ∈ interior D.target.carrier := fun y hy =>
      hint y ⟨lt_of_le_of_lt ha hy.1, lt_of_lt_of_le hy.2 hb⟩
    have hwall' : ∀ y ∈ Ioo a b, ∀ i, X + y • u ∉ interior (D.tile i).carrier := by
      intro y hy
      rcases hstr y hy with h | h
      · obtain ⟨e, he, hy'⟩ := (hs₁ y).mpr h
        exact D.edge_point_not_interior (openSegment_subset_segment ℝ _ _ hy')
      · obtain ⟨e, he, hy'⟩ := (hs₂ y).mpr h
        exact D.edge_point_not_interior (openSegment_subset_segment ℝ _ _ hy')
    exact ⟨wall_cover_param hf hgd₁ hf hX hu hu0 (lt_trans hx.1 hx.2) hint' hwall' hx hxv,
      wall_cover_param hf' hgd₂ hf hX hu hu0 (lt_trans hx.1 hx.2) hint' hwall' hx hxv⟩
  obtain ⟨x₀, hℓx, hxL, hn₁, hn₂, hmin, hsum₁, hsum₂⟩ :=
    first_common_junction_1d S₁ S₂ (lo D X u) (hi D X u) hle₁ hle₂
      (meet hf hgd₁ hf hX hu hu0) (meet hf' hgd₂ hf hX hu hu0) hℓ hℓL hseed' h0 hL
      _ (finite_vertex_params hu0) hwall
  have hx0 : (0 : ℝ) ≤ x₀ := hℓ.le.trans hℓx
  have conv : ∀ {g : Plane →ₗ[ℝ] ℝ} {d : ℝ} (hgd : ∀ y, g y = d ↔ f y = c),
      ∑ e ∈ (D.lineChain g d).filter (fun e => 0 ≤ lo D X u e ∧ hi D X u e ≤ x₀),
        (hi D X u e - lo D X u e) = x₀ →
      ∑ e ∈ (D.lineChain g d).filter
          (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ X (X + x₀ • u)),
        dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = x₀ := by
    intro g d hgd hsum
    have hfil : (D.lineChain g d).filter
          (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ X (X + x₀ • u)) =
        (D.lineChain g d).filter (fun e => 0 ≤ lo D X u e ∧ hi D X u e ≤ x₀) := by
      refine Finset.filter_congr (fun e he => ?_)
      have := inside_iff hgd hf hX hu hu0 he hx0
      rwa [← hX0] at this
    rw [hfil]
    refine Eq.trans (Finset.sum_congr rfl fun e he => ?_) hsum
    have he' := (Finset.mem_filter.mp he).1
    exact (edge_data hf hX hu hu0 (onLine hgd he').1 (onLine hgd he').2).2.2.2 hu1
  refine ⟨x₀, hℓx, hxL, (hs₁ x₀).not.mpr hn₁, (hs₂ x₀).not.mpr hn₂, fun y hy => ?_,
    conv hgd₁ hsum₁, conv hgd₂ hsum₂⟩
  rcases hmin y hy with h | h
  · exact Or.inl ((hs₁ y).mpr h)
  · exact Or.inr ((hs₂ y).mpr h)

end Main

/-! ## §6 Discharging the start condition ("no edge on the line passes through the point") -/

section Start

variable {N : ℕ} {D : Dissection N} {X u : Plane} {f g : Plane →ₗ[ℝ] ℝ} {c d : ℝ}

/-- **Boundary end, forward.**  If the line leaves the target just after `X + x₀•u`, no edge on the
line passes through that point. -/
theorem not_straddled_of_outside_after (hgd : ∀ y, g y = d ↔ f y = c) (hf : f ≠ 0) (hX : f X = c)
    (hu : f u = 0) (hu0 : u ≠ 0) {x₀ : ℝ}
    (hout : ∀ t, x₀ < t → X + t • u ∉ D.target.carrier) :
    ¬ Straddled D g d (X + x₀ • u) := by
  rw [str_iff hgd hf hX hu hu0]
  rintro ⟨e, he, h1, h2⟩
  apply hout ((x₀ + hi D X u e) / 2) (by linarith)
  have hm : X + ((x₀ + hi D X u e) / 2) • u ∈ (D.tile e.1).edge e.2 :=
    (mem_edge_iff hgd hf hX hu hu0 he _).mpr ⟨by linarith, by linarith⟩
  exact tile_subset_target D e.1 ((D.tile e.1).edge_subset_carrier e.2 hm)

/-- **Boundary end, backward.** -/
theorem not_straddled_of_outside_before (hgd : ∀ y, g y = d ↔ f y = c) (hf : f ≠ 0)
    (hX : f X = c) (hu : f u = 0) (hu0 : u ≠ 0) {x₀ : ℝ}
    (hout : ∀ t, t < x₀ → X + t • u ∉ D.target.carrier) :
    ¬ Straddled D g d (X + x₀ • u) := by
  rw [str_iff hgd hf hX hu hu0]
  rintro ⟨e, he, h1, h2⟩
  apply hout ((x₀ + lo D X u e) / 2) (by linarith)
  have hm : X + ((x₀ + lo D X u e) / 2) • u ∈ (D.tile e.1).edge e.2 :=
    (mem_edge_iff hgd hf hX hu hu0 he _).mpr ⟨by linarith, by linarith⟩
  exact tile_subset_target D e.1 ((D.tile e.1).edge_subset_carrier e.2 hm)

/-- **Tile interiors accumulating on the point.**  If points of the line arbitrarily close to
`X + x₀•u` are interior to tiles, no edge on the line passes through it. -/
theorem not_straddled_of_near_interior (hgd : ∀ y, g y = d ↔ f y = c) (hf : f ≠ 0)
    (hX : f X = c) (hu : f u = 0) (hu0 : u ≠ 0) {x₀ : ℝ}
    (hnear : ∀ δ > 0, ∃ x, |x - x₀| < δ ∧ ∃ i, X + x • u ∈ interior (D.tile i).carrier) :
    ¬ Straddled D g d (X + x₀ • u) := by
  rw [str_iff hgd hf hX hu hu0]
  rintro ⟨e, he, h1, h2⟩
  obtain ⟨x, hx, i, hi⟩ := hnear (min (x₀ - lo D X u e) (hi D X u e - x₀))
    (lt_min (by linarith) (by linarith))
  have hx1 := lt_of_lt_of_le hx (min_le_left _ _)
  have hx2 := lt_of_lt_of_le hx (min_le_right _ _)
  rw [abs_lt] at hx1 hx2
  have hm : X + x • u ∈ (D.tile e.1).edge e.2 :=
    (mem_edge_iff hgd hf hX hu hu0 he _).mpr ⟨by linarith, by linarith⟩
  exact D.edge_point_not_interior hm i hi

/-- **A tile across the line.**  If a triangle contains `X + x₀•u` and has points strictly on both
sides of the line `{f = c}`, then points of the line arbitrarily close to `X + x₀•u` are interior to
it.  (Its interior is convex and meets both open half-planes, hence meets the line at some `W`; the
open segment from `X + x₀•u` to `W` is interior.) -/
theorem near_interior_of_across (T : Tri) (hf : f ≠ 0) (hX : f X = c) (hu : f u = 0) (hu0 : u ≠ 0)
    {x₀ : ℝ} (hY : X + x₀ • u ∈ T.carrier) {p q : Plane} (hp : p ∈ T.carrier) (hq : q ∈ T.carrier)
    (hpc : f p < c) (hqc : c < f q) :
    ∀ δ > 0, ∃ x, |x - x₀| < δ ∧ X + x • u ∈ interior T.carrier := by
  intro δ hδ
  have hcl : closure (interior T.carrier) = T.carrier := by
    rw [T.convex.closure_interior_eq_closure_of_nonempty_interior T.interior_nonempty,
      T.isCompact.isClosed.closure_eq]
  have hfc : Continuous f := LinearMap.continuous_of_finiteDimensional f
  obtain ⟨p', hp'1, hp'2⟩ := mem_closure_iff.mp (hcl.symm ▸ hp : p ∈ closure (interior T.carrier))
    {y | f y < c} (isOpen_lt hfc continuous_const) hpc
  obtain ⟨q', hq'1, hq'2⟩ := mem_closure_iff.mp (hcl.symm ▸ hq : q ∈ closure (interior T.carrier))
    {y | c < f y} (isOpen_lt continuous_const hfc) hqc
  simp only [Set.mem_setOf_eq] at hp'1 hq'1
  set l := (c - f p') / (f q' - f p') with hl
  have hden : 0 < f q' - f p' := by linarith
  have hl0 : 0 < l := div_pos (by linarith) hden
  have hl1 : l < 1 := (div_lt_one hden).mpr (by linarith)
  set W := (1 - l) • p' + l • q' with hW
  have hWint : W ∈ interior T.carrier :=
    T.convex.interior hp'2 hq'2 (by linarith) hl0.le (by ring)
  have hfW : f W = c := by
    rw [hW, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hl]
    field_simp
    ring
  obtain ⟨w, hw⟩ := exists_param hf hX hu hu0 hfW
  by_cases hwx : w = x₀
  · exact ⟨x₀, by simp [hδ], by rw [← hwx, ← hw]; exact hWint⟩
  · have hseg := T.convex.openSegment_closure_interior_subset_interior (subset_closure hY) hWint
    have hwpos : 0 < |w - x₀| := abs_pos.mpr (sub_ne_zero.mpr hwx)
    set r := min (1 / 2) (δ / (2 * |w - x₀|)) with hr
    have hr0 : 0 < r := lt_min (by norm_num) (div_pos hδ (by positivity))
    have hr1 : r < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    refine ⟨x₀ + r * (w - x₀), ?_, hseg ⟨1 - r, r, by linarith, hr0, by ring, ?_⟩⟩
    · rw [add_sub_cancel_left, abs_mul, abs_of_pos hr0]
      have : r * |w - x₀| ≤ δ / 2 := by
        calc r * |w - x₀| ≤ δ / (2 * |w - x₀|) * |w - x₀| :=
              mul_le_mul_of_nonneg_right (min_le_right _ _) hwpos.le
          _ = δ / 2 := by field_simp
      linarith
    · rw [hw]; module

/-- **A vertex is extreme.**  If `pts k + v` lies in a triangle (`v ≠ 0`), then `pts k + t•v` does not
for `t < 0` (barycentric coordinate `k` equals `1` only at `pts k`).  Used for the target's apex. -/
theorem vertex_ray_out (T : Tri) (k : Fin 3) {v : Plane} (hv : v ≠ 0)
    (hin : T.pts k + v ∈ T.carrier) {t : ℝ} (ht : t < 0) : T.pts k + t • v ∉ T.carrier := by
  intro hy
  have hnn : ∀ y ∈ T.carrier, ∀ i, 0 ≤ T.basis.coord i y := by
    intro y hy' i; rw [T.carrier_eq_nonneg_coord] at hy'; exact hy' i
  have hsplit : ∀ y, T.basis.coord k y + ∑ i ∈ Finset.univ.erase k, T.basis.coord i y = 1 := by
    intro y
    rw [Finset.add_sum_erase _ (fun i => T.basis.coord i y) (Finset.mem_univ k)]
    exact T.basis.sum_coord_apply_eq_one y
  have hle1 : ∀ y ∈ T.carrier, T.basis.coord k y ≤ 1 := by
    intro y hy'
    have := hsplit y
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ.erase k) => hnn y hy' i)
    linarith
  have hgk : T.basis.coord k (T.pts k) = 1 := T.basis.coord_apply_eq k
  set a := 1 / (1 - t) with ha
  set b := -t / (1 - t) with hb
  have h1t : 0 < 1 - t := by linarith
  have hab : a + b = 1 := by rw [ha, hb]; field_simp; ring
  have ha0 : 0 < a := by positivity
  have hb0 : 0 < b := div_pos (by linarith) h1t
  have hcomb : a • (T.pts k + t • v) + b • (T.pts k + v) = T.pts k := by
    have e1 : a • (T.pts k + t • v) + b • (T.pts k + v) = (a + b) • T.pts k + (a * t + b) • v := by
      module
    have e2 : a * t + b = 0 := by rw [ha, hb]; field_simp; ring
    rw [e1, hab, e2, one_smul, zero_smul, add_zero]
  have hval := Convex.combo_affine_apply (f := T.basis.coord k) (x := T.pts k + t • v)
    (y := T.pts k + v) hab
  rw [hcomb, hgk] at hval
  simp only [smul_eq_mul] at hval
  have hy1 := hle1 _ hy
  have hz1 := hle1 _ hin
  have hz : T.basis.coord k (T.pts k + v) = 1 := by nlinarith
  have hz0 : ∑ i ∈ Finset.univ.erase k, T.basis.coord i (T.pts k + v) = 0 := by
    have := hsplit (T.pts k + v); linarith
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn _ hin i)).mp hz0
  obtain ⟨j, m, hjk, hmk, hjm⟩ : ∃ j m : Fin 3, j ≠ k ∧ m ≠ k ∧ j ≠ m := by
    fin_cases k <;> decide
  obtain ⟨m', hm'⟩ := T.eq_vertex_of_two_coords_zero hjm
    (hzero j (Finset.mem_erase.mpr ⟨hjk, Finset.mem_univ j⟩))
    (hzero m (Finset.mem_erase.mpr ⟨hmk, Finset.mem_univ m⟩))
  have hc : T.basis.coord k (T.basis m') = 1 := by
    have hbm : T.basis m' = T.pts m' := rfl
    rw [hbm, ← hm']; exact hz
  rw [AffineBasis.coord_apply] at hc
  split_ifs at hc with hkm
  · subst hkm
    exact hv (by simpa using hm')
  · norm_num at hc

end Start

/-! ## §7 Junction positions are partial sums -/

section Prefix

variable {N : ℕ} {D : Dissection N} {X u : Plane} {f g : Plane →ₗ[ℝ] ℝ} {c d : ℝ}

open Classical in
/-- **Every junction is a partial sum (ordered form of TC).**  On a wall stretch `(X, X + x₀•u)` from a
point `X` through which no edge of the side `lineChain g d` passes, let `e` be an edge of that side
lying in `[X, X + x₀•u]` and `p` either endpoint of `e`.  Then the edges of that side lying in
`[X, p]` have total length `|Xp|`: the junction positions of each side are exactly the partial sums
of its word read from `X`. -/
theorem junction_partial_sum (hg : g ≠ 0) (hgd : ∀ y, g y = d ↔ f y = c) (hf : f ≠ 0)
    (hX : f X = c) (hu : f u = 0) (hu1 : ‖u‖ = 1) {x₀ : ℝ} (hx0 : 0 ≤ x₀)
    (hint : ∀ x ∈ Ioo 0 x₀, X + x • u ∈ interior D.target.carrier)
    (hwall : ∀ x ∈ Ioo 0 x₀, ∀ i, X + x • u ∉ interior (D.tile i).carrier)
    (h0 : ¬ Straddled D g d X) {e : Fin N × Fin 3} (he : e ∈ D.lineChain g d)
    (hin : (D.tile e.1).edge e.2 ⊆ segment ℝ X (X + x₀ • u)) {p : Plane}
    (hp : p = (D.tile e.1).pts e.2 ∨ p = (D.tile e.1).pts (e.2 + 1)) :
    ∑ e' ∈ (D.lineChain g d).filter (fun e' => (D.tile e'.1).edge e'.2 ⊆ segment ℝ X p),
      dist ((D.tile e'.1).pts e'.2) ((D.tile e'.1).pts (e'.2 + 1)) = dist X p := by
  have hu0 := ne_zero_of_norm hu1
  have hX0 : X + (0 : ℝ) • u = X := by rw [zero_smul, add_zero]
  obtain ⟨h0e, h1e⟩ := onLine hgd he
  obtain ⟨hlt, hedge, -, -⟩ := edge_data hf hX hu hu0 h0e h1e
  -- `p` is the point of parameter `t ∈ {lo e, hi e}`
  have hpline : f p = c := by rcases hp with rfl | rfl <;> assumption
  have hpe := par_spec (exists_param hf hX hu hu0 hpline)
  set t := par X u p with ht
  have htlo : t = lo D X u e ∨ t = hi D X u e := by
    have e0 := par_spec (exists_param hf hX hu hu0 h0e)
    have e1 := par_spec (exists_param hf hX hu hu0 h1e)
    rcases hp with rfl | rfl
    · rcases le_total (par X u ((D.tile e.1).pts e.2)) (par X u ((D.tile e.1).pts (e.2 + 1))) with
        h | h
      · left; simp only [lo, ht]; rw [min_eq_left h]
      · right; simp only [hi, ht]; rw [max_eq_left h]
    · rcases le_total (par X u ((D.tile e.1).pts e.2)) (par X u ((D.tile e.1).pts (e.2 + 1))) with
        h | h
      · right; simp only [hi, ht]; rw [max_eq_right h]
      · left; simp only [lo, ht]; rw [min_eq_right h]
  have hin' := (inside_iff hgd hf hX hu hu0 he hx0).mp (by rwa [hX0])
  have ht0 : 0 ≤ t := by rcases htlo with h | h <;> rw [h] <;> linarith [hin'.1]
  have htx : t ≤ x₀ := by rcases htlo with h | h <;> rw [h] <;> linarith [hin'.2]
  -- `p` is not straddled from its own side (an edge through it would overlap `e`)
  have hpns : ¬ Straddled D g d (X + t • u) := by
    rw [str_iff hgd hf hX hu hu0]
    rintro ⟨e', he', h1, h2⟩
    have hne : e ≠ e' := by
      rintro rfl; rcases htlo with h | h <;> rw [h] at h1 h2 <;> linarith
    have hm := meet hg hgd hf hX hu hu0 e he e' he' hne
    rcases htlo with h | h
    · -- `t = lo e`: both intervals contain `t` and `min (hi e) (hi e')`
      have hq : t < min (hi D X u e) (hi D X u e') := lt_min (by rw [h]; exact hlt) h2
      have ht1 : t ∈ Icc (lo D X u e) (hi D X u e) ∩ Icc (lo D X u e') (hi D X u e') :=
        ⟨⟨by rw [h], by rw [h]; exact hlt.le⟩, h1.le, h2.le⟩
      have hq1 : min (hi D X u e) (hi D X u e') ∈
          Icc (lo D X u e) (hi D X u e) ∩ Icc (lo D X u e') (hi D X u e') :=
        ⟨⟨by linarith, min_le_left _ _⟩, by linarith, min_le_right _ _⟩
      exact absurd (hm ht1 hq1) (ne_of_lt hq)
    · -- `t = hi e`: both intervals contain `t` and `max (lo e) (lo e')`
      have hq : max (lo D X u e) (lo D X u e') < t := max_lt (by rw [h]; exact hlt) h1
      have ht1 : t ∈ Icc (lo D X u e) (hi D X u e) ∩ Icc (lo D X u e') (hi D X u e') :=
        ⟨⟨by rw [h]; exact hlt.le, by rw [h]⟩, h1.le, h2.le⟩
      have hq1 : max (lo D X u e) (lo D X u e') ∈
          Icc (lo D X u e) (hi D X u e) ∩ Icc (lo D X u e') (hi D X u e') :=
        ⟨⟨le_max_left _ _, by linarith⟩, le_max_right _ _, by linarith⟩
      exact absurd (hm ht1 hq1).symm (ne_of_lt hq)
  have hwall' : ∀ x ∈ Ioo 0 t, ∀ i, X + x • u ∉ interior (D.tile i).carrier := fun x hx =>
    hwall x ⟨hx.1, lt_of_lt_of_le hx.2 htx⟩
  have hint' : ∀ x ∈ Ioo 0 t, X + x • u ∈ interior D.target.carrier := fun x hx =>
    hint x ⟨hx.1, lt_of_lt_of_le hx.2 htx⟩
  have key := wall_sum hg hgd hf hX hu hu1 ht0 hint' hwall' (by rwa [hX0]) hpns
  rw [hX0, ← hpe] at key
  rw [key, sub_zero, hpe, dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, hu1, mul_one,
    Real.norm_of_nonneg ht0]

end Prefix

end Erdos634.Draft.TraceCovering

#print axioms Erdos634.Draft.TraceCovering.sum_inside_eq
#print axioms Erdos634.Draft.TraceCovering.first_common_junction_1d
#print axioms Erdos634.Draft.TraceCovering.wall_sum
#print axioms Erdos634.Draft.TraceCovering.trace_covering
#print axioms Erdos634.Draft.TraceCovering.not_straddled_of_outside_after
#print axioms Erdos634.Draft.TraceCovering.not_straddled_of_outside_before
#print axioms Erdos634.Draft.TraceCovering.not_straddled_of_near_interior
#print axioms Erdos634.Draft.TraceCovering.near_interior_of_across
#print axioms Erdos634.Draft.TraceCovering.vertex_ray_out
#print axioms Erdos634.Draft.TraceCovering.junction_partial_sum
