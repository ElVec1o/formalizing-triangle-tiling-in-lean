-- Draft/NearBaseVertex.lean — R5, the GEOMETRIC near-base vertex lemma NB
-- ((private working notes, not included) §2, (private working notes, not included) steps (a)–(f)).
-- Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- STRUCTURE.
--   * `LocalFan` — the local cone structure at a point `x` of height `h`: the tiles having `x` as a
--     corner (edge vectors `u`, `w` from `x`) and the tiles having `x` in the relative interior of an
--     edge (unit inward normal `n`, third vertex `x + v`), with (cover) every direction lies in the
--     closed wedge of a corner tile or the closed half-plane of an edge tile, and (disj) the open
--     cones are pairwise disjoint; plus each tile's metric data (sides ≥ ℓ, ≤ L; corner cosines
--     ≥ −c₀, i.e. angles ≤ γ with c₀ = −cos γ; altitudes ≥ H; vertices in the upper half-plane).
--   * `nb_of_fan` — **NB from the local fan: PROVED** (no `sorry`).  0 < h, `c₀ ≥ 0` (γ ≥ π/2),
--     (1) `2h² < ℓ²(1 − c₀)` [= `h < ℓ cos(γ/2)`], (2) `h²((ℓ+L)² + H²) < H²ℓ²` [= `h < h₂`,
--     `NearBase.cond2_of_sq` / `sq_of_cond2`] ⟹ False.  The proof is the report's steps (a)–(f):
--     F = directions below the base-parallel at angle > θ₀ (`K·d₁ < −h·|d₀|`, `K = √(ℓ²−h²)`); no
--     corner wedge meets F (`corner_not_F`: a wedge whose flanks avoid F and whose angle is < π − 2θ₀);
--     straight down is covered by an edge tile; that edge tile's tilt is ≤ θ₀ (else a second edge
--     tile covers the directions just across it, the two normals are opposite, and the corner tile at
--     `x` has nowhere to go); its third vertex is then below the base (`third_vertex_below`).
--   * `localFan_of_tiles` — **PROVED** (was the one missing lemma): a finite family of triangles
--     with disjoint interiors covering a ball at `x` yields a `LocalFan` at `x`.  This is "the corner
--     wedges at a point partition the directions" (the PAPER_MAP `prop:Uplacements` blocker WITHOUT the
--     cyclic order, which NB never needs), proved from `Tri.coord_mul_det`, `Tri.classify`,
--     `Tri.inter_ball_eq_halfplane`, `Tri.ball_subset_of_pos`, `exists_common_radius`, `infDist`.
--   * `nb_tiles` — **NB for a finite family of triangles: PROVED** (`nb_of_fan ∘ localFan_of_tiles`).
--   * `fan_example` — witness that `LocalFan`'s hypotheses are jointly satisfiable (vacuity rule);
--     `tiles_witness` — four right triangles around (0,5) satisfy `localFan_of_tiles`' hypotheses
--     (geometric ones jointly; metric ones at weak constants ℓ = 0, H = 0, c₀ = 1).
-- Hypotheses in coordinates (`p 0`, `p 1`; height = `p 1`), so the proof is polynomial arithmetic.
import Erdos634.Dissection
import Erdos634.CertCoord

namespace Erdos634.Draft.NearBaseVertex

open Erdos634.Geometry Erdos634.CertCoord

/-- **The local cone structure at a point of height `h`** (see the file header).  Coordinates of
the corner tiles' edge vectors `u = (u0,u1)`, `w = (w0,w1)` with lengths `lu`, `lw`; edge tiles' unit
inward normal `n = (n0,n1)`, third vertex offset `v = (v0,v1)` with length `lv`. -/
structure LocalFan (h ℓ L H c₀ : ℝ) where
  C : Type
  E : Type
  c₁ : C
  u0 : C → ℝ
  u1 : C → ℝ
  w0 : C → ℝ
  w1 : C → ℝ
  lu : C → ℝ
  lw : C → ℝ
  n0 : E → ℝ
  n1 : E → ℝ
  v0 : E → ℝ
  v1 : E → ℝ
  lv : E → ℝ
  -- corner tiles
  hlu : ∀ c, lu c ^ 2 = u0 c ^ 2 + u1 c ^ 2 ∧ 0 ≤ lu c
  hlw : ∀ c, lw c ^ 2 = w0 c ^ 2 + w1 c ^ 2 ∧ 0 ≤ lw c
  hℓu : ∀ c, ℓ ≤ lu c
  hℓw : ∀ c, ℓ ≤ lw c
  hhu : ∀ c, 0 ≤ h + u1 c
  hhw : ∀ c, 0 ≤ h + w1 c
  hang : ∀ c, -c₀ * lu c * lw c ≤ u0 c * w0 c + u1 c * w1 c
  hind : ∀ c, u0 c * w1 c - u1 c * w0 c ≠ 0
  -- edge tiles
  hn : ∀ k, n0 k ^ 2 + n1 k ^ 2 = 1
  hlv : ∀ k, lv k ^ 2 = v0 k ^ 2 + v1 k ^ 2 ∧ 0 ≤ lv k
  hH : ∀ k, H ≤ n0 k * v0 k + n1 k * v1 k
  hL : ∀ k, lv k ≤ L
  hhv : ∀ k, 0 ≤ h + v1 k
  -- the cone structure
  cover : ∀ d0 d1 : ℝ,
    (∃ c, ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ d0 = s * u0 c + t * w0 c ∧ d1 = s * u1 c + t * w1 c) ∨
    (∃ k, 0 ≤ n0 k * d0 + n1 k * d1)
  disjEE : ∀ k k', k ≠ k' → ∀ d0 d1 : ℝ,
    ¬ (0 < n0 k * d0 + n1 k * d1 ∧ 0 < n0 k' * d0 + n1 k' * d1)
  disjCE : ∀ c k (s t : ℝ), 0 < s → 0 < t →
    n0 k * (s * u0 c + t * w0 c) + n1 k * (s * u1 c + t * w1 c) ≤ 0

/-! ## Step (b)–(c): no corner wedge meets the forbidden fan F -/

/-- A corner flank (length `≥ ℓ`, endpoint at height `≥ 0`) avoids `F`:
`K·u₁ + h·u₀ ≥ 0` or `K·u₁ − h·u₀ ≥ 0` (`K² = ℓ² − h²`). -/
theorem flank_P {h ℓ K u0 u1 lu : ℝ} (hh : 0 < h) (hK : K ^ 2 = ℓ ^ 2 - h ^ 2) (hK0 : 0 < K)
    (hlu : lu ^ 2 = u0 ^ 2 + u1 ^ 2) (hlu0 : 0 ≤ lu) (hℓ : ℓ ≤ lu) (hℓ0 : 0 < ℓ)
    (hhu : 0 ≤ h + u1) : 0 ≤ K * u1 + h * u0 ∨ 0 ≤ K * u1 - h * u0 := by
  by_contra hc; push Not at hc
  obtain ⟨h1, h2⟩ := hc
  have hu1 : u1 < 0 := by nlinarith
  -- K²u₁² > h²u₀², so ℓ²u₁² > h²·lu² ≥ h²ℓ², so u₁² > h²
  have k1 : h ^ 2 * u0 ^ 2 < K ^ 2 * u1 ^ 2 := by
    have : h * |u0| < -(K * u1) := by
      rcases abs_cases u0 with ⟨ha, _⟩ | ⟨ha, _⟩ <;> rw [ha] <;> linarith
    have h0 : 0 ≤ h * |u0| := by positivity
    have := mul_self_lt_mul_self h0 this
    have e1 : h * |u0| * (h * |u0|) = h ^ 2 * u0 ^ 2 := by
      rw [show h * |u0| * (h * |u0|) = h ^ 2 * (|u0| * |u0|) by ring, abs_mul_abs_self]; ring
    nlinarith
  have k2 : h ^ 2 * ℓ ^ 2 ≤ h ^ 2 * lu ^ 2 := by
    have : ℓ ^ 2 ≤ lu ^ 2 := pow_le_pow_left₀ hℓ0.le hℓ 2
    exact mul_le_mul_of_nonneg_left this (sq_nonneg h)
  rw [hK] at k1
  have hl2 : h ^ 2 * lu ^ 2 = h ^ 2 * u0 ^ 2 + h ^ 2 * u1 ^ 2 := by rw [hlu]; ring
  have k3 : h ^ 2 < u1 ^ 2 := by
    have : ℓ ^ 2 * u1 ^ 2 > h ^ 2 * ℓ ^ 2 := by nlinarith
    have hℓ2 : 0 < ℓ ^ 2 := by positivity
    nlinarith
  nlinarith

set_option maxHeartbeats 400000 in
/-- The mixed case: `u ∈ P₁ ∖ P₂`, `w ∈ P₂ ∖ P₁` forces the wedge angle to be `≥ π − 2θ₀`, which
(1) forbids: contradiction. -/
theorem mixed_false {h ℓ K c₀ u0 u1 w0 w1 lu lw : ℝ} (hh : 0 < h) (hℓ0 : 0 < ℓ)
    (hK : K ^ 2 = ℓ ^ 2 - h ^ 2) (hK0 : 0 < K) (hc₀ : 0 ≤ c₀) (h1 : 2 * h ^ 2 < ℓ ^ 2 * (1 - c₀))
    (hlu : lu ^ 2 = u0 ^ 2 + u1 ^ 2) (hlu0 : 0 ≤ lu) (hℓu : ℓ ≤ lu)
    (hlw : lw ^ 2 = w0 ^ 2 + w1 ^ 2) (hlw0 : 0 ≤ lw) (hℓw : ℓ ≤ lw)
    (hang : -c₀ * lu * lw ≤ u0 * w0 + u1 * w1)
    (hu1 : 0 ≤ K * u1 + h * u0) (hu2 : K * u1 - h * u0 < 0)
    (hw2 : 0 ≤ K * w1 - h * w0) (hw1 : K * w1 + h * w0 < 0) : False := by
  have hu0 : 0 < u0 := by
    have : 0 < h * u0 := by linarith
    exact pos_of_mul_pos_right this hh.le
  have hw0 : w0 < 0 := by
    have : 0 < h * (-w0) := by linarith
    have := pos_of_mul_pos_right this hh.le
    linarith
  -- K|u₁| ≤ h·u₀ and K|w₁| ≤ h·(−w₀)
  have au : K * |u1| ≤ h * u0 := by
    rcases abs_cases u1 with ⟨ha, _⟩ | ⟨ha, _⟩ <;> rw [ha] <;> linarith
  have aw : K * |w1| ≤ h * (-w0) := by
    rcases abs_cases w1 with ⟨ha, _⟩ | ⟨ha, _⟩ <;> rw [ha] <;> linarith
  have a1 : K ^ 2 * (u1 * w1) ≤ h ^ 2 * (u0 * (-w0)) := by
    have p1 : 0 ≤ K * |u1| := by positivity
    have p2 : 0 ≤ K * |w1| := by positivity
    have := mul_le_mul au aw p2 (by positivity)
    have e : K * |u1| * (K * |w1|) = K ^ 2 * |u1 * w1| := by rw [abs_mul]; ring
    have h3 : u1 * w1 ≤ |u1 * w1| := le_abs_self _
    have h4 := mul_le_mul_of_nonneg_left h3 (sq_nonneg K)
    linarith
  -- ℓ·u₀ ≥ K·lu and ℓ·(−w₀) ≥ K·lw
  have bu : K * lu ≤ ℓ * u0 := by
    have hsq : (K * lu) ^ 2 ≤ (ℓ * u0) ^ 2 := by
      have : K ^ 2 * u1 ^ 2 ≤ h ^ 2 * u0 ^ 2 := by
        have := mul_le_mul au au (by positivity) (by positivity)
        have e : K * |u1| * (K * |u1|) = K ^ 2 * u1 ^ 2 := by
          rw [show K * |u1| * (K * |u1|) = K ^ 2 * (|u1| * |u1|) by ring, abs_mul_abs_self]; ring
        linarith
      have this' : (ℓ ^ 2 - h ^ 2) * u1 ^ 2 ≤ h ^ 2 * u0 ^ 2 := by rw [← hK]; exact this
      rw [mul_pow, mul_pow, hlu, hK]; linarith
    exact (pow_le_pow_iff_left₀ (by positivity) (mul_pos hℓ0 hu0).le two_ne_zero).mp hsq
  have bw : K * lw ≤ ℓ * (-w0) := by
    have hsq : (K * lw) ^ 2 ≤ (ℓ * (-w0)) ^ 2 := by
      have : K ^ 2 * w1 ^ 2 ≤ h ^ 2 * w0 ^ 2 := by
        have := mul_le_mul aw aw (by positivity) (mul_pos hh (neg_pos.mpr hw0)).le
        have e : K * |w1| * (K * |w1|) = K ^ 2 * w1 ^ 2 := by
          rw [show K * |w1| * (K * |w1|) = K ^ 2 * (|w1| * |w1|) by ring, abs_mul_abs_self]; ring
        linarith
      have this' : (ℓ ^ 2 - h ^ 2) * w1 ^ 2 ≤ h ^ 2 * w0 ^ 2 := by rw [← hK]; exact this
      rw [mul_pow, mul_pow, hlw, hK]; linarith
    exact (pow_le_pow_iff_left₀ (by positivity) (mul_pos hℓ0 (neg_pos.mpr hw0)).le
      two_ne_zero).mp hsq
  have d1 : K ^ 2 * (lu * lw) ≤ ℓ ^ 2 * (u0 * (-w0)) := by
    have := mul_le_mul bu bw (by positivity) (mul_pos hℓ0 hu0).le
    linarith
  -- K²·(u·w) ≤ −(K² − h²)·u₀(−w₀)
  have c1 : K ^ 2 * (u0 * w0 + u1 * w1) ≤ -(K ^ 2 - h ^ 2) * (u0 * (-w0)) := by linarith
  have hKh : 0 < K ^ 2 - h ^ 2 := by
    have := mul_nonneg (sq_nonneg ℓ) hc₀
    linarith
  -- ℓ²K²(u·w) ≤ −(K² − h²)K²·lu·lw
  have c2 : ℓ ^ 2 * (u0 * w0 + u1 * w1) ≤ -(K ^ 2 - h ^ 2) * (lu * lw) := by
    have hK2 : 0 < K ^ 2 := by positivity
    have e1 : ℓ ^ 2 * (K ^ 2 * (u0 * w0 + u1 * w1)) ≤ ℓ ^ 2 * (-(K ^ 2 - h ^ 2) * (u0 * (-w0))) :=
      mul_le_mul_of_nonneg_left c1 (by positivity)
    have e2 : (K ^ 2 - h ^ 2) * (K ^ 2 * (lu * lw)) ≤ (K ^ 2 - h ^ 2) * (ℓ ^ 2 * (u0 * (-w0))) :=
      mul_le_mul_of_nonneg_left d1 hKh.le
    have e3 : K ^ 2 * (ℓ ^ 2 * (u0 * w0 + u1 * w1)) ≤ K ^ 2 * (-(K ^ 2 - h ^ 2) * (lu * lw)) := by
      linarith
    exact le_of_mul_le_mul_left e3 hK2
  have hlulw : 0 < lu * lw := by
    have : 0 < lu := lt_of_lt_of_le hℓ0 hℓu
    have : 0 < lw := lt_of_lt_of_le hℓ0 hℓw
    positivity
  have c3 : ℓ ^ 2 * (-c₀ * lu * lw) ≤ ℓ ^ 2 * (u0 * w0 + u1 * w1) :=
    mul_le_mul_of_nonneg_left hang (by positivity)
  rw [hK] at c2
  have : (ℓ ^ 2 - 2 * h ^ 2 - c₀ * ℓ ^ 2) * (lu * lw) ≤ 0 := by linarith
  have hpos : 0 < ℓ ^ 2 - 2 * h ^ 2 - c₀ * ℓ ^ 2 := by linarith
  linarith [mul_pos hpos hlulw]

/-- **No corner wedge meets F** (report steps (b)–(c)).  If `d = s·u + t·w` (`s, t ≥ 0`) with the
flanks of length `≥ ℓ` ending at height `≥ 0` and wedge cosine `≥ −c₀`, then `d ∉ F`, where
`d ∈ F ⟺ K·d₁ + h·d₀ < 0 ∧ K·d₁ − h·d₀ < 0` (`d` points below the base-parallel at angle `> θ₀`). -/
theorem corner_not_F {h ℓ K c₀ u0 u1 w0 w1 lu lw s t : ℝ} (hh : 0 < h) (hℓ0 : 0 < ℓ)
    (hK : K ^ 2 = ℓ ^ 2 - h ^ 2) (hK0 : 0 < K) (hc₀ : 0 ≤ c₀) (h1 : 2 * h ^ 2 < ℓ ^ 2 * (1 - c₀))
    (hlu : lu ^ 2 = u0 ^ 2 + u1 ^ 2) (hlu0 : 0 ≤ lu) (hℓu : ℓ ≤ lu)
    (hlw : lw ^ 2 = w0 ^ 2 + w1 ^ 2) (hlw0 : 0 ≤ lw) (hℓw : ℓ ≤ lw)
    (hhu : 0 ≤ h + u1) (hhw : 0 ≤ h + w1)
    (hang : -c₀ * lu * lw ≤ u0 * w0 + u1 * w1) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hF1 : K * (s * u1 + t * w1) + h * (s * u0 + t * w0) < 0)
    (hF2 : K * (s * u1 + t * w1) - h * (s * u0 + t * w0) < 0) : False := by
  have Pu := flank_P hh hK hK0 hlu hlu0 hℓu hℓ0 hhu
  have Pw := flank_P hh hK hK0 hlw hlw0 hℓw hℓ0 hhw
  have hang' : -c₀ * lw * lu ≤ w0 * u0 + w1 * u1 := by linarith [hang]
  -- a common half-plane is closed under nonnegative combinations
  have lin1 : 0 ≤ K * u1 + h * u0 → 0 ≤ K * w1 + h * w0 → False := fun a b => by
    have := add_nonneg (mul_nonneg hs a) (mul_nonneg ht b); nlinarith
  have lin2 : 0 ≤ K * u1 - h * u0 → 0 ≤ K * w1 - h * w0 → False := fun a b => by
    have := add_nonneg (mul_nonneg hs a) (mul_nonneg ht b); nlinarith
  rcases Pu with a | a <;> rcases Pw with b | b
  · exact lin1 a b
  · by_cases a2 : 0 ≤ K * u1 - h * u0
    · exact lin2 a2 b
    by_cases b1 : 0 ≤ K * w1 + h * w0
    · exact lin1 a b1
    push Not at a2 b1
    exact mixed_false hh hℓ0 hK hK0 hc₀ h1 hlu hlu0 hℓu hlw hlw0 hℓw hang a a2 b b1
  · by_cases a1 : 0 ≤ K * u1 + h * u0
    · exact lin1 a1 b
    by_cases b2 : 0 ≤ K * w1 - h * w0
    · exact lin2 a b2
    push Not at a1 b2
    exact mixed_false hh hℓ0 hK hK0 hc₀ h1 hlw hlw0 hℓw hlu hlu0 hℓu hang' b b2 a a1
  · exact lin2 a b

/-! ## Step (d): a steep edge tile leaves a direction of F uncovered by it -/

/-- If the unit normal `n` (with `n₁ ≤ 0`) is tilted more than `θ₀` (`ℓ²n₀² > h²`), some direction
`d ∈ F` has `n·d < 0` (just across the edge line from the tile). -/
theorem exists_F_across {h ℓ K n0 n1 : ℝ} (hh : 0 < h) (hK : K ^ 2 = ℓ ^ 2 - h ^ 2) (hK0 : 0 < K)
    (hn : n0 ^ 2 + n1 ^ 2 = 1) (hn1 : n1 ≤ 0) (hsteep : h ^ 2 < ℓ ^ 2 * n0 ^ 2) :
    ∃ d0 d1 : ℝ, K * d1 + h * d0 < 0 ∧ K * d1 - h * d0 < 0 ∧ n0 * d0 + n1 * d1 < 0 := by
  -- the gap g = K|n₀| − h|n₁| > 0, since K²n₀² − h²n₁² = ℓ²n₀² − h² > 0
  have hn0 : n0 ≠ 0 := by rintro rfl; nlinarith
  have hbd0 : n0 ^ 2 ≤ 1 := by nlinarith
  have hbd1 : n1 ^ 2 ≤ 1 := by nlinarith
  have habs0 : |n0| ≤ 1 := by rw [← sq_le_one_iff_abs_le_one]; exact hbd0
  have habs1 : |n1| ≤ 1 := by rw [← sq_le_one_iff_abs_le_one]; exact hbd1
  have hgap : h * (-n1) < K * |n0| := by
    have hsq : (h * (-n1)) ^ 2 < (K * |n0|) ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs, hK]; nlinarith
    have : 0 ≤ K * |n0| := by positivity
    exact lt_of_pow_lt_pow_left₀ 2 this hsq
  set g := K * |n0| - h * (-n1) with hg
  have hg0 : 0 < g := by linarith
  set δ := g / (2 * (K + h)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδg : δ * (K + h) < g := by
    rw [hδ, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
  -- the perturbation term is at most δ·(K + h)
  have hpert : δ * (K * (-n1) + h * |n0|) ≤ δ * (K + h) := by
    apply mul_le_mul_of_nonneg_left _ hδ0.le
    have : -n1 ≤ 1 := by have := neg_le_abs n1; linarith
    nlinarith [mul_le_mul_of_nonneg_left this hK0.le, mul_le_mul_of_nonneg_left habs0 hh.le]
  rcases lt_or_gt_of_ne hn0 with hneg | hpos
  · -- n₀ < 0: d = (−n₁ − δn₀, n₀ − δn₁)
    have ha : |n0| = -n0 := abs_of_neg hneg
    refine ⟨-n1 - δ * n0, n0 - δ * n1, ?_, ?_, ?_⟩
    · rw [ha] at hg hpert; nlinarith [mul_pos hh hδ0]
    · rw [ha] at hg hpert; nlinarith [mul_pos hh hδ0]
    · have : n0 * (-n1 - δ * n0) + n1 * (n0 - δ * n1) = -δ := by linear_combination (-δ) * hn
      linarith
  · -- n₀ > 0: d = (n₁ − δn₀, −n₀ − δn₁)
    have ha : |n0| = n0 := abs_of_pos hpos
    refine ⟨n1 - δ * n0, -n0 - δ * n1, ?_, ?_, ?_⟩
    · rw [ha] at hg hpert; nlinarith [mul_pos hh hδ0]
    · rw [ha] at hg hpert; nlinarith [mul_pos hh hδ0]
    · have : n0 * (n1 - δ * n0) + n1 * (-n0 - δ * n1) = -δ := by linear_combination (-δ) * hn
      linarith

/-! ## Steps (e)–(f): the covering edge tile's third vertex is below the base -/

/-- With `n` a unit normal, `n₁ ≤ 0`, tilt `ℓ²n₀² ≤ h²`, the third vertex offset `v` with `n·v ≥ H`,
`|v| ≤ L`, and (2) `h²((ℓ+L)² + H²) < H²ℓ²`: the vertex is below the base, `h + v₁ < 0`. -/
theorem third_vertex_below {h ℓ L H n0 n1 v0 v1 lv : ℝ} (hh : 0 < h) (hℓ0 : 0 < ℓ) (hH0 : 0 ≤ H)
    (hL0 : 0 ≤ L) (hn : n0 ^ 2 + n1 ^ 2 = 1) (hn1 : n1 ≤ 0) (htilt : ℓ ^ 2 * n0 ^ 2 ≤ h ^ 2)
    (hlv : lv ^ 2 = v0 ^ 2 + v1 ^ 2) (hlv0 : 0 ≤ lv) (hLv : lv ≤ L) (hHv : H ≤ n0 * v0 + n1 * v1)
    (h2 : h ^ 2 * ((ℓ + L) ^ 2 + H ^ 2) < H ^ 2 * ℓ ^ 2) : h + v1 < 0 := by
  set a := -n1 * v0 + n0 * v1 with ha
  set b := n0 * v0 + n1 * v1 with hb
  have hv1 : v1 = a * n0 + b * n1 := by rw [ha, hb]; linear_combination (-v1) * hn
  have hab : a ^ 2 + b ^ 2 = lv ^ 2 := by rw [ha, hb, hlv]; linear_combination (v0 ^ 2 + v1 ^ 2) * hn
  -- |a| ≤ L and ℓ|n₀| ≤ h
  have haL : |a| ≤ L := by
    have : a ^ 2 ≤ L ^ 2 := by nlinarith [pow_le_pow_left₀ hlv0 hLv 2, sq_nonneg b]
    exact (pow_le_pow_iff_left₀ (abs_nonneg a) hL0 two_ne_zero).mp (by rw [sq_abs]; exact this)
  have hn0h : ℓ * |n0| ≤ h := by
    have : (ℓ * |n0|) ^ 2 ≤ h ^ 2 := by rw [mul_pow, sq_abs]; exact htilt
    exact (pow_le_pow_iff_left₀ (by positivity) hh.le two_ne_zero).mp this
  -- ℓ·a·n₀ ≤ L·h
  have t1 : ℓ * (a * n0) ≤ L * h := by
    have : ℓ * (a * n0) ≤ |a| * (ℓ * |n0|) := by
      have : a * n0 ≤ |a| * |n0| := by rw [← abs_mul]; exact le_abs_self _
      nlinarith
    have : |a| * (ℓ * |n0|) ≤ L * h := mul_le_mul haL hn0h (by positivity) hL0
    linarith
  -- b·n₁ ≤ H·n₁
  have t2 : b * n1 ≤ H * n1 := by nlinarith
  -- ℓ²n₁² ≥ ℓ² − h², so ℓ·H·(−n₁) > h(ℓ + L)
  have t3 : h * (ℓ + L) < ℓ * H * (-n1) := by
    have hn1sq : ℓ ^ 2 - h ^ 2 ≤ ℓ ^ 2 * n1 ^ 2 := by nlinarith
    have hsq : (h * (ℓ + L)) ^ 2 < (ℓ * H * (-n1)) ^ 2 := by
      have : H ^ 2 * (ℓ ^ 2 - h ^ 2) ≤ H ^ 2 * (ℓ ^ 2 * n1 ^ 2) :=
        mul_le_mul_of_nonneg_left hn1sq (sq_nonneg H)
      nlinarith
    have : 0 ≤ ℓ * H * (-n1) := by
      have : 0 ≤ -n1 := by linarith
      positivity
    exact lt_of_pow_lt_pow_left₀ 2 this hsq
  have : ℓ * (h + v1) < 0 := by
    rw [hv1]; nlinarith
  by_contra hc; push Not at hc
  nlinarith

/-! ## NB from the local fan (PROVED) -/

set_option maxHeartbeats 400000 in
/-- **NB (near-base vertex lemma), from the local cone structure — PROVED.**  `x` at height
`h > 0` is a corner of a tile (`c₁`); the tiles at `x` have sides in `[ℓ, L]`, wedge cosines
`≥ −c₀` (`c₀ = −cos γ ≥ 0`), altitudes `≥ H`, vertices at height `≥ 0`.  If (1) `2h² < ℓ²(1 − c₀)`
and (2) `h²((ℓ+L)² + H²) < H²ℓ²`, contradiction. -/
theorem nb_of_fan {h ℓ L H c₀ : ℝ} (F : LocalFan h ℓ L H c₀) (hh : 0 < h) (hℓ0 : 0 < ℓ)
    (hH0 : 0 ≤ H) (hL0 : 0 ≤ L) (hc₀ : 0 ≤ c₀) (h1 : 2 * h ^ 2 < ℓ ^ 2 * (1 - c₀))
    (h2 : h ^ 2 * ((ℓ + L) ^ 2 + H ^ 2) < H ^ 2 * ℓ ^ 2) : False := by
  have hhℓ : h ^ 2 < ℓ ^ 2 := by nlinarith
  obtain ⟨K, hK0, hK⟩ : ∃ K : ℝ, 0 < K ∧ K ^ 2 = ℓ ^ 2 - h ^ 2 :=
    ⟨√(ℓ ^ 2 - h ^ 2), Real.sqrt_pos.mpr (by linarith), Real.sq_sqrt (by linarith)⟩
  -- no corner wedge contains a direction of F
  have noC : ∀ c (s t d0 d1 : ℝ), 0 ≤ s → 0 ≤ t → d0 = s * F.u0 c + t * F.w0 c →
      d1 = s * F.u1 c + t * F.w1 c → K * d1 + h * d0 < 0 → K * d1 - h * d0 < 0 → False := by
    intro c s t d0 d1 hs ht e0 e1 hF1 hF2
    subst e0 e1
    exact corner_not_F hh hℓ0 hK hK0 hc₀ h1 (F.hlu c).1 (F.hlu c).2 (F.hℓu c) (F.hlw c).1
      (F.hlw c).2 (F.hℓw c) (F.hhu c) (F.hhw c) (F.hang c) hs ht hF1 hF2
  -- every direction of F is covered by an edge tile
  have edgeF : ∀ d0 d1 : ℝ, K * d1 + h * d0 < 0 → K * d1 - h * d0 < 0 →
      ∃ k, 0 ≤ F.n0 k * d0 + F.n1 k * d1 := by
    intro d0 d1 hF1 hF2
    rcases F.cover d0 d1 with ⟨c, s, t, hs, ht, e0, e1⟩ | hk
    · exact (noC c s t d0 d1 hs ht e0 e1 hF1 hF2).elim
    · exact hk
  -- (c) straight down is covered by an edge tile k₁: n₁ ≤ 0
  obtain ⟨k₁, hk₁⟩ := edgeF 0 (-1) (by nlinarith) (by nlinarith)
  have hn1 : F.n1 k₁ ≤ 0 := by linarith
  -- (d) its tilt is ≤ θ₀
  have htilt : ℓ ^ 2 * F.n0 k₁ ^ 2 ≤ h ^ 2 := by
    by_contra hsteep; push Not at hsteep
    obtain ⟨d0, d1, hF1, hF2, hneg⟩ := exists_F_across hh hK hK0 (F.hn k₁) hn1 hsteep
    obtain ⟨k₂, hk₂⟩ := edgeF d0 d1 hF1 hF2
    have hne : k₁ ≠ k₂ := by rintro rfl; linarith
    -- disjoint open half-planes ⟹ opposite normals
    have hopp : F.n0 k₁ * F.n0 k₂ + F.n1 k₁ * F.n1 k₂ ≤ -1 := by
      by_contra hc; push Not at hc
      apply F.disjEE k₁ k₂ hne (F.n0 k₁ + F.n0 k₂) (F.n1 k₁ + F.n1 k₂)
      have e1 := F.hn k₁; have e2 := F.hn k₂
      constructor <;> nlinarith
    have hsum0 : F.n0 k₁ + F.n0 k₂ = 0 ∧ F.n1 k₁ + F.n1 k₂ = 0 := by
      have e1 := F.hn k₁; have e2 := F.hn k₂
      have : (F.n0 k₁ + F.n0 k₂) ^ 2 + (F.n1 k₁ + F.n1 k₂) ^ 2 ≤ 0 := by nlinarith
      constructor <;> nlinarith [sq_nonneg (F.n0 k₁ + F.n0 k₂), sq_nonneg (F.n1 k₁ + F.n1 k₂)]
    -- the corner tile c₁ has its open wedge on the line: n·u = n·w = 0, so u ∥ w
    have q1 := F.disjCE F.c₁ k₁ 1 1 one_pos one_pos
    have q2 := F.disjCE F.c₁ k₂ 1 1 one_pos one_pos
    have q3 := F.disjCE F.c₁ k₁ 2 1 two_pos one_pos
    have q4 := F.disjCE F.c₁ k₂ 2 1 two_pos one_pos
    have e0 : F.n0 k₂ = -F.n0 k₁ := by linarith [hsum0.1]
    have e1' : F.n1 k₂ = -F.n1 k₁ := by linarith [hsum0.2]
    rw [e0, e1'] at q2 q4
    have hu : F.n0 k₁ * F.u0 F.c₁ + F.n1 k₁ * F.u1 F.c₁ = 0 := by linarith
    have hw : F.n0 k₁ * F.w0 F.c₁ + F.n1 k₁ * F.w1 F.c₁ = 0 := by linarith
    apply F.hind F.c₁
    have hn := F.hn k₁
    have x0 : F.n0 k₁ * (F.u0 F.c₁ * F.w1 F.c₁ - F.u1 F.c₁ * F.w0 F.c₁) = 0 := by
      linear_combination F.w1 F.c₁ * hu - F.u1 F.c₁ * hw
    have x1 : F.n1 k₁ * (F.u0 F.c₁ * F.w1 F.c₁ - F.u1 F.c₁ * F.w0 F.c₁) = 0 := by
      linear_combination -(F.w0 F.c₁) * hu + F.u0 F.c₁ * hw
    linear_combination (-(F.u0 F.c₁ * F.w1 F.c₁ - F.u1 F.c₁ * F.w0 F.c₁)) * hn
      + F.n0 k₁ * x0 + F.n1 k₁ * x1
  -- (e)–(f) its third vertex is below the base
  have hb := third_vertex_below hh hℓ0 hH0 hL0 (F.hn k₁) hn1 htilt (F.hlv k₁).1 (F.hlv k₁).2
    (F.hL k₁) (F.hH k₁) h2
  linarith [F.hhv k₁]

/-! ## Vacuity rule: `LocalFan`'s hypotheses are jointly satisfiable -/

/-- A concrete local fan: two right-angle corner tiles in the upper half-plane (quadrants I, II) and
one edge tile below (`n = (0,−1)`, third vertex straight down at depth `h`), with `h = ℓ = L = H = 1`,
`c₀ = 0`.  (NB's (1) fails here, `2 < 1` — as it must: the fan is a real vertex figure.) -/
def fan_example : LocalFan 1 1 1 1 0 where
  C := Bool
  E := Unit
  c₁ := true
  u0 := fun c => if c then 1 else 0
  u1 := fun c => if c then 0 else 1
  w0 := fun c => if c then 0 else -1
  w1 := fun c => if c then 1 else 0
  lu := fun _ => 1
  lw := fun _ => 1
  n0 := fun _ => 0
  n1 := fun _ => -1
  v0 := fun _ => 0
  v1 := fun _ => -1
  lv := fun _ => 1
  hlu := by intro c; cases c <;> norm_num
  hlw := by intro c; cases c <;> norm_num
  hℓu := by intro c; norm_num
  hℓw := by intro c; norm_num
  hhu := by intro c; cases c <;> norm_num
  hhw := by intro c; cases c <;> norm_num
  hang := by intro c; cases c <;> norm_num
  hind := by intro c; cases c <;> norm_num
  hn := by intro k; norm_num
  hlv := by intro k; norm_num
  hH := by intro k; norm_num
  hL := by intro k; norm_num
  hhv := by intro k; norm_num
  cover := by
    intro d0 d1
    by_cases hd1 : d1 ≤ 0
    · right; exact ⟨(), by show (0:ℝ) ≤ 0 * d0 + -1 * d1; linarith⟩
    · left
      push Not at hd1
      by_cases hd0 : 0 ≤ d0
      · exact ⟨true, d0, d1, hd0, hd1.le, by simp, by simp⟩
      · push Not at hd0
        exact ⟨false, d1, -d0, hd1.le, by linarith, by simp, by simp⟩
  disjEE := by intro k k' hkk'; exact absurd (Subsingleton.elim k k') hkk'
  disjCE := by
    intro c k s t hs ht
    cases c
    · show (0:ℝ) * (s * 0 + t * -1) + -1 * (s * 1 + t * 0) ≤ 0
      linarith
    · show (0:ℝ) * (s * 1 + t * 0) + -1 * (s * 0 + t * 1) ≤ 0
      linarith

/-! ## NB for tiles -/

/-! ## The local cone structure at a point of a triangle family (PROVED)

Single-tile facts at a point `x` through the barycentric coordinates as cross products
(`Tri.coord_mul_det`): the tangent cone at a vertex is the wedge (`corner_cone`), the open wedge is
interior (`corner_interior`; cf. `PlacementCompleteness.wedge_interior`, the vertex-0 version with a
perturbation), at a relative-interior edge point the cone is the closed half-plane (`edge_cone_dir`)
and the open half-plane is interior (`edge_open_interior`, from `Tri.inter_ball_eq_halfplane`); a
direction from `x` lies in a tile containing `x` (`cover_tile`, via `exists_common_radius` and
`infDist`). -/

theorem cross_apply (u v : Plane) : cross u v = u 0 * v 1 - u 1 * v 0 := rfl

theorem dist_sq' (x y : Plane) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

theorem basis_apply (T : Tri) (j : Fin 3) : T.basis j = T.pts j := rfl

theorem coord_self (T : Tri) (j : Fin 3) : T.basis.coord j (T.pts j) = 1 := by
  rw [← basis_apply]; exact T.basis.coord_apply_eq j

theorem coord_other (T : Tri) {i j : Fin 3} (h : i ≠ j) : T.basis.coord i (T.pts j) = 0 := by
  rw [← basis_apply]; exact T.basis.coord_apply_ne h

/-- `coord_m(y)·det = cross(p_{m+2} − p_{m+1}, y − p_{m+1})` (`Tri.coord_mul_det` reindexed). -/
theorem coord_det (T : Tri) (m : Fin 3) (y : Plane) :
    T.basis.coord m y * T.det = cross (T.pts (m + 2) - T.pts (m + 1)) (y - T.pts (m + 1)) := by
  have h := T.coord_mul_det (m + 1) y
  have e1 : m + 1 + 2 = m := by fin_cases m <;> rfl
  have e2 : m + 1 + 1 = m + 2 := by fin_cases m <;> rfl
  rw [e1, e2] at h; exact h

theorem mem_interior_of_pos (T : Tri) {z : Plane} (h : ∀ i, 0 < T.basis.coord i z) :
    z ∈ interior T.carrier := by
  obtain ⟨r, hr, hsub⟩ := T.ball_subset_of_pos h
  exact mem_interior.mpr ⟨_, hsub, Metric.isOpen_ball, Metric.mem_ball_self hr⟩

theorem mem_carrier_iff (T : Tri) (y : Plane) : y ∈ T.carrier ↔ ∀ i, 0 ≤ T.basis.coord i y := by
  rw [T.carrier_eq_nonneg_coord]; rfl

/-- The sign of the orientation. -/
noncomputable def sgn (T : Tri) : ℝ := if 0 < T.det then 1 else -1

theorem sgn_mul_det_pos (T : Tri) : 0 < sgn T * T.det := by
  unfold sgn; split_ifs with h
  · linarith
  · have := T.det_ne_zero
    have : T.det < 0 := lt_of_le_of_ne (not_lt.mp h) this
    linarith

theorem sgn_sq (T : Tri) : sgn T ^ 2 = 1 := by unfold sgn; split_ifs <;> norm_num

/-- Edge point: a nearby point with `coord m > 0` is interior. -/
theorem edge_interior (T : Tri) (m : Fin 3) {x : Plane} (h1 : 0 < T.basis.coord (m + 1) x)
    (h2 : 0 < T.basis.coord (m + 2) x) :
    ∃ ρ > 0, ∀ z, dist z x < ρ → 0 < T.basis.coord m z → z ∈ interior T.carrier := by
  obtain ⟨ρ, hρ, heq⟩ := T.inter_ball_eq_halfplane m h1 h2
  refine ⟨ρ, hρ, fun z hz hm => ?_⟩
  have hopen : IsOpen ({y | 0 < T.basis.coord m y} ∩ Metric.ball x ρ) :=
    (isOpen_lt continuous_const (AffineMap.continuous_of_finiteDimensional _)).inter
      Metric.isOpen_ball
  refine mem_interior.mpr ⟨_, fun y hy => ?_, hopen, ⟨hm, hz⟩⟩
  have : y ∈ {y | 0 ≤ T.basis.coord m y} ∩ Metric.ball x ρ :=
    ⟨(show 0 < T.basis.coord m y from hy.1).le, hy.2⟩
  rw [← heq] at this; exact this.1

/-- `coord_m(x + ε·D)·det = coord_m(x)·det + ε·cross(e_m, D)`. -/
theorem coord_det_shift (T : Tri) (m : Fin 3) (x D : Plane) (ε : ℝ) :
    T.basis.coord m (x + ε • D) * T.det
      = T.basis.coord m x * T.det + ε * cross (T.pts (m + 2) - T.pts (m + 1)) D := by
  rw [coord_det, coord_det]
  simp only [cross_apply, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- Vertex tile, the wedge: if `x = p_k` and `x + ε·D` is in the tile, then
`D = s·(p_{k+1} − x) + t·(p_{k+2} − x)` with `s, t ≥ 0`. -/
theorem corner_cone (T : Tri) (k : Fin 3) {x D : Plane} (hx : T.pts k = x) {ε : ℝ} (hε : 0 < ε)
    (hy : x + ε • D ∈ T.carrier) :
    ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧
      D 0 = s * (T.pts (k + 1) 0 - x 0) + t * (T.pts (k + 2) 0 - x 0) ∧
      D 1 = s * (T.pts (k + 1) 1 - x 1) + t * (T.pts (k + 2) 1 - x 1) := by
  have hc := (mem_carrier_iff T _).mp hy
  have hΔ : cross (T.pts (k + 1) - T.pts k) (T.pts (k + 2) - T.pts k) = T.det := T.det_cyclic k
  have hdet := T.det_ne_zero
  have h1 := coord_det_shift T (k + 1) x D ε
  have h2 := coord_det_shift T (k + 2) x D ε
  have e1 : k + 1 + 2 = k := by fin_cases k <;> rfl
  have e2 : k + 1 + 1 = k + 2 := by fin_cases k <;> rfl
  have e3 : k + 2 + 2 = k + 1 := by fin_cases k <;> rfl
  have e4 : k + 2 + 1 = k := by fin_cases k <;> rfl
  rw [e1, e2] at h1
  rw [e3, e4] at h2
  have hx1 : T.basis.coord (k + 1) x = 0 := by
    rw [← hx]; exact coord_other T (by fin_cases k <;> decide)
  have hx2 : T.basis.coord (k + 2) x = 0 := by
    rw [← hx]; exact coord_other T (by fin_cases k <;> decide)
  rw [hx1, zero_mul, zero_add] at h1
  rw [hx2, zero_mul, zero_add] at h2
  set c1 := T.basis.coord (k + 1) (x + ε • D)
  set c2 := T.basis.coord (k + 2) (x + ε • D)
  refine ⟨c1 / ε, c2 / ε, div_nonneg (hc _) hε.le, div_nonneg (hc _) hε.le, ?_, ?_⟩
  · rw [← hx]
    simp only [cross_apply, PiLp.sub_apply] at hΔ h1 h2
    have key : (D 0 * ε) * T.det
        = (c1 * (T.pts (k + 1) 0 - T.pts k 0) + c2 * (T.pts (k + 2) 0 - T.pts k 0)) * T.det := by
      rw [← hΔ] at h1 h2 ⊢
      linear_combination (-(T.pts (k + 1) 0 - T.pts k 0)) * h1 + (-(T.pts (k + 2) 0 - T.pts k 0)) * h2
    have := mul_right_cancel₀ hdet key
    field_simp
    linarith
  · rw [← hx]
    simp only [cross_apply, PiLp.sub_apply] at hΔ h1 h2
    have key : (D 1 * ε) * T.det
        = (c1 * (T.pts (k + 1) 1 - T.pts k 1) + c2 * (T.pts (k + 2) 1 - T.pts k 1)) * T.det := by
      rw [← hΔ] at h1 h2 ⊢
      linear_combination (-(T.pts (k + 1) 1 - T.pts k 1)) * h1 + (-(T.pts (k + 2) 1 - T.pts k 1)) * h2
    have := mul_right_cancel₀ hdet key
    field_simp
    linarith


/-- Vertex tile, the open wedge: for `s, t > 0` and small `ε > 0`, `x + ε(s·a + t·b)` is interior. -/
theorem corner_interior (T : Tri) (k : Fin 3) {x : Plane} (hx : T.pts k = x) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) {ε : ℝ} (hε : 0 < ε) (hε1 : ε * (s + t) < 1) :
    x + ε • (s • (T.pts (k + 1) - x) + t • (T.pts (k + 2) - x)) ∈ interior T.carrier := by
  set D := s • (T.pts (k + 1) - x) + t • (T.pts (k + 2) - x) with hD
  have hΔ : cross (T.pts (k + 1) - T.pts k) (T.pts (k + 2) - T.pts k) = T.det := T.det_cyclic k
  have hdet := T.det_ne_zero
  have h0 := coord_det_shift T k x D ε
  have h1 := coord_det_shift T (k + 1) x D ε
  have h2 := coord_det_shift T (k + 2) x D ε
  have e1 : k + 1 + 2 = k := by fin_cases k <;> rfl
  have e2 : k + 1 + 1 = k + 2 := by fin_cases k <;> rfl
  have e3 : k + 2 + 2 = k + 1 := by fin_cases k <;> rfl
  have e4 : k + 2 + 1 = k := by fin_cases k <;> rfl
  rw [e1, e2] at h1
  rw [e3, e4] at h2
  have hx0 : T.basis.coord k x = 1 := by rw [← hx]; exact coord_self T k
  have hx1 : T.basis.coord (k + 1) x = 0 := by
    rw [← hx]; exact coord_other T (by fin_cases k <;> decide)
  have hx2 : T.basis.coord (k + 2) x = 0 := by
    rw [← hx]; exact coord_other T (by fin_cases k <;> decide)
  rw [hx0] at h0; rw [hx1] at h1; rw [hx2] at h2
  rw [← hx] at hD
  subst hx
  simp only [hD, cross_apply, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    at h0 h1 h2 hΔ
  have c0 : T.basis.coord k (T.pts k + ε • D) * T.det = (1 - ε * (s + t)) * T.det := by
    rw [h0, ← hΔ]; ring
  have c1 : T.basis.coord (k + 1) (T.pts k + ε • D) * T.det = (ε * s) * T.det := by
    rw [h1, ← hΔ]; ring
  have c2 : T.basis.coord (k + 2) (T.pts k + ε • D) * T.det = (ε * t) * T.det := by
    rw [h2, ← hΔ]; ring
  have q0 := mul_right_cancel₀ hdet c0
  have q1 := mul_right_cancel₀ hdet c1
  have q2 := mul_right_cancel₀ hdet c2
  apply mem_interior_of_pos
  have hfin : ∀ i : Fin 3, i = k ∨ i = k + 1 ∨ i = k + 2 := by
    intro i; fin_cases k <;> fin_cases i <;> decide
  intro i
  rcases hfin i with rfl | rfl | rfl
  · rw [q0]; linarith
  · rw [q1]; positivity
  · rw [q2]; positivity

/-- A direction from `x` lies in some tile containing `x` (finite closed cover of a ball). -/
theorem cover_tile {n : ℕ} (T : Fin n → Tri) (x : Plane) {r : ℝ} (hr : 0 < r)
    (hcov : Metric.ball x r ⊆ ⋃ i, (T i).carrier) (hn : 0 < n) {D : Plane} (hD : D ≠ 0) :
    ∃ (i : Fin n) (ε : ℝ), 0 < ε ∧ x ∈ (T i).carrier ∧ x + ε • D ∈ (T i).carrier := by
  classical
  let f : Fin n → ℝ := fun i => if x ∈ (T i).carrier then 1 else Metric.infDist x (T i).carrier
  have hf : ∀ i, 0 < f i := by
    intro i
    by_cases h : x ∈ (T i).carrier
    · simp [f, h]
    · simp only [f, h, if_false]
      exact ((T i).isCompact.isClosed.notMem_iff_infDist_pos
        ⟨(T i).pts 0, subset_convexHull ℝ _ (Set.mem_range_self 0)⟩).mp h
  obtain ⟨ρ, hρ, hle⟩ := exists_common_radius hn f hf
  have hDn : 0 < ‖D‖ := norm_pos_iff.mpr hD
  set δ := min ρ r / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδρ : δ < ρ := by have := min_le_left ρ r; linarith
  have hδr : δ < r := by have := min_le_right ρ r; linarith
  set ε := δ / ‖D‖ with hεdef
  have hε : 0 < ε := by positivity
  have hdist : dist (x + ε • D) x = δ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hε.le, hεdef,
      div_mul_cancel₀ _ hDn.ne']
  have hy : x + ε • D ∈ Metric.ball x r := by rw [Metric.mem_ball, hdist]; exact hδr
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hy)
  refine ⟨i, ε, hε, ?_, hi⟩
  by_contra hxi
  have h1 : Metric.infDist x (T i).carrier ≤ dist x (x + ε • D) := Metric.infDist_le_dist_of_mem hi
  have h2 : ρ ≤ Metric.infDist x (T i).carrier := by
    have := hle i; simp only [f, hxi, if_false] at this; exact this
  rw [dist_comm, hdist] at h1
  linarith

theorem dist_add_smul (x V : Plane) {ε : ℝ} (hε : 0 ≤ ε) : dist (x + ε • V) x = ε * ‖V‖ := by
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hε]

theorem small_eps (V : Plane) {ρ B : ℝ} (hρ : 0 < ρ) (hB : 0 < B) :
    ∃ ε : ℝ, 0 < ε ∧ ε < B ∧ ε * ‖V‖ < ρ := by
  have hN := norm_nonneg V
  refine ⟨min (B / 2) (ρ / (2 * (‖V‖ + 1))), by positivity, ?_, ?_⟩
  · have := min_le_left (B / 2) (ρ / (2 * (‖V‖ + 1))); linarith
  · have h1 := min_le_right (B / 2) (ρ / (2 * (‖V‖ + 1)))
    have h2 : min (B / 2) (ρ / (2 * (‖V‖ + 1))) * ‖V‖ ≤ ρ / (2 * (‖V‖ + 1)) * ‖V‖ :=
      mul_le_mul_of_nonneg_right h1 hN
    have h3 : ρ / (2 * (‖V‖ + 1)) * ‖V‖ < ρ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
    linarith

theorem abs_det (T : Tri) : |T.det| = sgn T * T.det := by
  unfold sgn; split_ifs with h
  · rw [abs_of_pos h]; ring
  · have : T.det < 0 := lt_of_le_of_ne (not_lt.mp h) T.det_ne_zero
    rw [abs_of_neg this]; ring

theorem normal_dot (T : Tri) (m : Fin 3) (el : ℝ) (D : Plane) :
    (-(sgn T) * (T.pts (m + 2) 1 - T.pts (m + 1) 1) / el) * D 0
      + (sgn T * (T.pts (m + 2) 0 - T.pts (m + 1) 0) / el) * D 1
      = sgn T * cross (T.pts (m + 2) - T.pts (m + 1)) D / el := by
  simp only [cross_apply, PiLp.sub_apply]; ring

theorem el_pos (T : Tri) (m : Fin 3) : 0 < dist (T.pts (m + 2)) (T.pts (m + 1)) :=
  dist_pos.mpr (T.indep.injective.ne (by fin_cases m <;> decide))

theorem hn_h (T : Tri) (m : Fin 3) :
    (-(sgn T) * (T.pts (m + 2) 1 - T.pts (m + 1) 1) / dist (T.pts (m + 2)) (T.pts (m + 1))) ^ 2
      + (sgn T * (T.pts (m + 2) 0 - T.pts (m + 1) 0) / dist (T.pts (m + 2)) (T.pts (m + 1))) ^ 2
      = 1 := by
  have hel := el_pos T m
  have hsq := dist_sq' (T.pts (m + 2)) (T.pts (m + 1))
  have hs := sgn_sq T
  rw [div_pow, div_pow, ← add_div, div_eq_one_iff_eq (by positivity), hsq]
  linear_combination ((T.pts (m + 2) 0 - T.pts (m + 1) 0) ^ 2
    + (T.pts (m + 2) 1 - T.pts (m + 1) 1) ^ 2) * hs

theorem hind_h (T : Tri) (k : Fin 3) {x : Plane} (hk : T.pts k = x) :
    (T.pts (k + 1) 0 - x 0) * (T.pts (k + 2) 1 - x 1)
      - (T.pts (k + 1) 1 - x 1) * (T.pts (k + 2) 0 - x 0) ≠ 0 := by
  have h := T.det_cyclic k
  rw [hk] at h
  simp only [cross_apply, PiLp.sub_apply] at h
  rw [h]; exact T.det_ne_zero

theorem hH_h (T : Tri) (m : Fin 3) {x : Plane} {H : ℝ} (hx0 : T.basis.coord m x = 0)
    (halt : H * dist (T.pts (m + 1)) (T.pts (m + 2))
      ≤ |cross (T.pts (m + 1) - T.pts m) (T.pts (m + 2) - T.pts m)|) :
    H ≤ (-(sgn T) * (T.pts (m + 2) 1 - T.pts (m + 1) 1) / dist (T.pts (m + 2)) (T.pts (m + 1)))
          * (T.pts m 0 - x 0)
      + (sgn T * (T.pts (m + 2) 0 - T.pts (m + 1) 0) / dist (T.pts (m + 2)) (T.pts (m + 1)))
          * (T.pts m 1 - x 1) := by
  have hel := el_pos T m
  have hd := normal_dot T m (dist (T.pts (m + 2)) (T.pts (m + 1))) (T.pts m - x)
  simp only [PiLp.sub_apply] at hd
  rw [hd]
  have c1 := coord_det T m (T.pts m)
  have c2 := coord_det T m x
  rw [coord_self] at c1
  rw [hx0] at c2
  have hcr : cross (T.pts (m + 2) - T.pts (m + 1)) (T.pts m - x) = T.det := by
    simp only [cross_apply, PiLp.sub_apply] at c1 c2 ⊢
    linear_combination -c1 + c2
  rw [hcr, le_div_iff₀ hel, ← abs_det]
  rw [T.det_cyclic m, dist_comm] at halt
  exact halt

theorem hL_h (T : Tri) (m : Fin 3) {x : Plane} {L : ℝ} (hx : x ∈ T.carrier)
    (hlong : ∀ j k, dist (T.pts j) (T.pts k) ≤ L) : dist (T.pts m) x ≤ L := by
  have hsub : Set.range T.pts ⊆ Metric.closedBall (T.pts m) L := by
    rintro _ ⟨j, rfl⟩; rw [Metric.mem_closedBall]; exact hlong j m
  have := convexHull_min hsub (convex_closedBall _ _) hx
  rw [Metric.mem_closedBall, dist_comm] at this; exact this

theorem edge_cone_dir (T : Tri) (m : Fin 3) {x D : Plane} (hx0 : T.basis.coord m x = 0)
    {ε : ℝ} (hε : 0 < ε) (hy : x + ε • D ∈ T.carrier) :
    0 ≤ sgn T * cross (T.pts (m + 2) - T.pts (m + 1)) D := by
  have hc := ((mem_carrier_iff T _).mp hy) m
  have h := coord_det_shift T m x D ε
  rw [hx0, zero_mul, zero_add] at h
  have hp := sgn_mul_det_pos T
  have : 0 ≤ ε * (sgn T * cross (T.pts (m + 2) - T.pts (m + 1)) D) := by
    have : ε * (sgn T * cross (T.pts (m + 2) - T.pts (m + 1)) D)
        = T.basis.coord m (x + ε • D) * (sgn T * T.det) := by linear_combination (sgn T) * h.symm
    rw [this]; positivity
  by_contra hneg; push Not at hneg
  have := mul_neg_of_pos_of_neg hε hneg
  linarith

theorem edge_open_interior (T : Tri) (m : Fin 3) {x : Plane} (hx0 : T.basis.coord m x = 0)
    (hpos : ∀ j, j ≠ m → 0 < T.basis.coord j x) :
    ∃ ρ > 0, ∀ (D : Plane) (ε : ℝ), 0 < ε → ε * ‖D‖ < ρ →
      0 < sgn T * cross (T.pts (m + 2) - T.pts (m + 1)) D → x + ε • D ∈ interior T.carrier := by
  obtain ⟨ρ, hρ, hint⟩ := edge_interior T m (hpos _ (by fin_cases m <;> decide))
    (hpos _ (by fin_cases m <;> decide))
  refine ⟨ρ, hρ, fun D ε hε hεD hc => hint _ (by rw [dist_add_smul x D hε.le]; exact hεD) ?_⟩
  have h := coord_det_shift T m x D ε
  rw [hx0, zero_mul, zero_add] at h
  have hp := sgn_mul_det_pos T
  have e : T.basis.coord m (x + ε • D) * (sgn T * T.det)
      = ε * (sgn T * cross (T.pts (m + 2) - T.pts (m + 1)) D) := by linear_combination (sgn T) * h
  have : 0 < T.basis.coord m (x + ε • D) * (sgn T * T.det) := by rw [e]; positivity
  exact pos_of_mul_pos_left this hp.le

theorem vertex_not_edge (T : Tri) (k : Fin 3) {x : Plane} (hk : T.pts k = x) (m : Fin 3)
    (hpos : ∀ j, j ≠ m → 0 < T.basis.coord j x) : False := by
  have h1 : T.basis.coord (k + 1) x = 0 := by
    rw [← hk]; exact coord_other T (by fin_cases k <;> decide)
  have h2 : T.basis.coord (k + 2) x = 0 := by
    rw [← hk]; exact coord_other T (by fin_cases k <;> decide)
  by_cases hm : k + 1 = m
  · have := hpos (k + 2) (by rw [← hm]; fin_cases k <;> decide)
    linarith
  · have := hpos (k + 1) hm
    linarith

theorem succ_ne' (k : Fin 3) : k + 1 ≠ k := by fin_cases k <;> decide
theorem succ_succ_ne' (k : Fin 3) : k + 2 ≠ k := by fin_cases k <;> decide

/-- **The local cone structure at a point of a triangle family — PROVED** (formerly the one
missing lemma, "the corner wedges at a point partition the directions"; NB never needs the cyclic
order).  A finite family of triangles with pairwise disjoint interiors covering a ball around `x`,
all vertices in the closed upper half-plane, `x` a corner of some tile, and metric bounds per tile
(sides in `[ℓ, L]`, corner cosines `≥ −c₀`, altitudes `≥ H`), yields a `LocalFan` at `x` (height
`x 1`): corner tiles = `(i,k)` with `pts k = x`; edge tiles = `(i,m)` with `coord_m x = 0` and the
other two coordinates positive, inward unit normal `sgn(det)·(−e₁, e₀)/|e|`; an interior tile at `x`
is excluded against the corner tile. -/
theorem localFan_of_tiles {n : ℕ} (T : Fin n → Tri) (x : Plane) {r : ℝ} (hr : 0 < r)
    (hcov : Metric.ball x r ⊆ ⋃ i, (T i).carrier)
    (hdisj : Pairwise fun i j => Disjoint (interior (T i).carrier) (interior (T j).carrier))
    (hup : ∀ i k, 0 ≤ (T i).pts k 1) (hcorner : ∃ i k, (T i).pts k = x)
    {ℓ L H c₀ : ℝ}
    (hside : ∀ i j k, j ≠ k → ℓ ≤ dist ((T i).pts j) ((T i).pts k))
    (hlong : ∀ i j k, dist ((T i).pts j) ((T i).pts k) ≤ L)
    (hcos : ∀ i (j : Fin 3), -c₀ * dist ((T i).pts (j + 1)) ((T i).pts j)
        * dist ((T i).pts (j + 2)) ((T i).pts j)
      ≤ ((T i).pts (j + 1) 0 - (T i).pts j 0) * ((T i).pts (j + 2) 0 - (T i).pts j 0)
        + ((T i).pts (j + 1) 1 - (T i).pts j 1) * ((T i).pts (j + 2) 1 - (T i).pts j 1))
    (halt : ∀ i (j : Fin 3), H * dist ((T i).pts (j + 1)) ((T i).pts (j + 2))
      ≤ |cross ((T i).pts (j + 1) - (T i).pts j) ((T i).pts (j + 2) - (T i).pts j)|) :
    Nonempty (LocalFan (x 1) ℓ L H c₀) := by
  classical
  obtain ⟨i₀, k₀, hk₀⟩ := hcorner
  have hn : 0 < n := Fin.pos i₀
  exact ⟨{
    C := {p : Fin n × Fin 3 // (T p.1).pts p.2 = x}
    E := {p : Fin n × Fin 3 //
      (T p.1).basis.coord p.2 x = 0 ∧ ∀ j, j ≠ p.2 → 0 < (T p.1).basis.coord j x}
    c₁ := ⟨(i₀, k₀), hk₀⟩
    u0 := fun c => (T c.1.1).pts (c.1.2 + 1) 0 - x 0
    u1 := fun c => (T c.1.1).pts (c.1.2 + 1) 1 - x 1
    w0 := fun c => (T c.1.1).pts (c.1.2 + 2) 0 - x 0
    w1 := fun c => (T c.1.1).pts (c.1.2 + 2) 1 - x 1
    lu := fun c => dist ((T c.1.1).pts (c.1.2 + 1)) x
    lw := fun c => dist ((T c.1.1).pts (c.1.2 + 2)) x
    n0 := fun p => -(sgn (T p.1.1)) * ((T p.1.1).pts (p.1.2 + 2) 1 - (T p.1.1).pts (p.1.2 + 1) 1)
      / dist ((T p.1.1).pts (p.1.2 + 2)) ((T p.1.1).pts (p.1.2 + 1))
    n1 := fun p => sgn (T p.1.1) * ((T p.1.1).pts (p.1.2 + 2) 0 - (T p.1.1).pts (p.1.2 + 1) 0)
      / dist ((T p.1.1).pts (p.1.2 + 2)) ((T p.1.1).pts (p.1.2 + 1))
    v0 := fun p => (T p.1.1).pts p.1.2 0 - x 0
    v1 := fun p => (T p.1.1).pts p.1.2 1 - x 1
    lv := fun p => dist ((T p.1.1).pts p.1.2) x
    hlu := fun c => ⟨dist_sq' _ _, dist_nonneg⟩
    hlw := fun c => ⟨dist_sq' _ _, dist_nonneg⟩
    hℓu := fun c => by
      have := hside c.1.1 (c.1.2 + 1) c.1.2 (succ_ne' _)
      rw [c.2] at this; exact this
    hℓw := fun c => by
      have := hside c.1.1 (c.1.2 + 2) c.1.2 (succ_succ_ne' _)
      rw [c.2] at this; exact this
    hhu := fun c => by
      have := hup c.1.1 (c.1.2 + 1)
      show 0 ≤ x 1 + ((T c.1.1).pts (c.1.2 + 1) 1 - x 1); linarith
    hhw := fun c => by
      have := hup c.1.1 (c.1.2 + 2)
      show 0 ≤ x 1 + ((T c.1.1).pts (c.1.2 + 2) 1 - x 1); linarith
    hang := fun c => by
      have := hcos c.1.1 c.1.2
      rw [c.2] at this; exact this
    hind := fun c => hind_h (T c.1.1) c.1.2 c.2
    hn := fun p => hn_h (T p.1.1) p.1.2
    hlv := fun p => ⟨dist_sq' _ _, dist_nonneg⟩
    hH := fun p => hH_h (T p.1.1) p.1.2 p.2.1 (halt p.1.1 p.1.2)
    hL := fun p => by
      apply hL_h (T p.1.1) p.1.2 _ (hlong p.1.1)
      rw [mem_carrier_iff]
      intro j
      by_cases hj : j = p.1.2
      · rw [hj, p.2.1]
      · exact (p.2.2 j hj).le
    hhv := fun p => by
      have := hup p.1.1 p.1.2
      show 0 ≤ x 1 + ((T p.1.1).pts p.1.2 1 - x 1); linarith
    cover := by
      intro d0 d1
      by_cases hd : d0 = 0 ∧ d1 = 0
      · left
        refine ⟨⟨(i₀, k₀), hk₀⟩, 0, 0, le_rfl, le_rfl, ?_, ?_⟩
        · simp [hd.1]
        · simp [hd.2]
      · have hD : mkPt d0 d1 ≠ 0 := by
          intro h; apply hd
          have h0 := congrArg (fun v : Plane => v 0) h
          have h1 := congrArg (fun v : Plane => v 1) h
          simp only [mkPt_zero, mkPt_one] at h0 h1
          exact ⟨by simpa using h0, by simpa using h1⟩
        obtain ⟨i, ε, hε, hxi, hyi⟩ := cover_tile T x hr hcov hn hD
        by_cases hv : ∃ k, (T i).pts k = x
        · obtain ⟨k, hk⟩ := hv
          obtain ⟨s, t, hs, ht, h0, h1⟩ := corner_cone (T i) k hk hε hyi
          left
          refine ⟨⟨(i, k), hk⟩, s, t, hs, ht, ?_, ?_⟩
          · simpa using h0
          · simpa using h1
        · push Not at hv
          rcases (T i).classify (fun k h => hv k h.symm) with hall | ⟨m, hm0, hmpos⟩ | ⟨k, hneg⟩
          · exfalso
            have hne : i ≠ i₀ := by rintro rfl; exact hv k₀ hk₀
            obtain ⟨ρ, hρ, hsub⟩ := (T i).ball_subset_of_pos hall
            obtain ⟨τ, hτ, hτB, hτV⟩ := small_eps ((1 : ℝ) • ((T i₀).pts (k₀ + 1) - x)
              + (1 : ℝ) • ((T i₀).pts (k₀ + 2) - x)) hρ (B := 1 / 2) (by norm_num)
            have hz1 := corner_interior (T i₀) k₀ hk₀ one_pos one_pos hτ (by linarith)
            have hz2 : x + τ • ((1 : ℝ) • ((T i₀).pts (k₀ + 1) - x)
                + (1 : ℝ) • ((T i₀).pts (k₀ + 2) - x)) ∈ interior (T i).carrier := by
              apply interior_maximal hsub Metric.isOpen_ball
              rw [Metric.mem_ball, dist_add_smul _ _ hτ.le]; exact hτV
            exact Set.disjoint_left.mp (hdisj hne) hz2 hz1
          · right
            refine ⟨⟨(i, m), hm0, hmpos⟩, ?_⟩
            have hc := edge_cone_dir (T i) m hm0 hε hyi
            have hd' := normal_dot (T i) m (dist ((T i).pts (m + 2)) ((T i).pts (m + 1))) (mkPt d0 d1)
            simp only [mkPt_zero, mkPt_one] at hd'
            have hel := el_pos (T i) m
            have : 0 ≤ sgn (T i) * cross ((T i).pts (m + 2) - (T i).pts (m + 1)) (mkPt d0 d1)
                / dist ((T i).pts (m + 2)) ((T i).pts (m + 1)) := div_nonneg hc hel.le
            beta_reduce
            linarith
          · exfalso
            have := ((mem_carrier_iff _ _).mp hxi) k
            linarith
    disjEE := by
      rintro ⟨⟨i, m⟩, hm0, hmpos⟩ ⟨⟨i', m'⟩, hm0', hmpos'⟩ hpp' d0 d1 ⟨h, h'⟩
      beta_reduce at h h'
      by_cases hii : i = i'
      · subst hii
        by_cases hmm : m = m'
        · subst hmm; exact hpp' rfl
        · have := hmpos m' (Ne.symm hmm)
          linarith
      · have hd1 := normal_dot (T i) m (dist ((T i).pts (m + 2)) ((T i).pts (m + 1))) (mkPt d0 d1)
        have hd2 := normal_dot (T i') m' (dist ((T i').pts (m' + 2)) ((T i').pts (m' + 1)))
          (mkPt d0 d1)
        simp only [mkPt_zero, mkPt_one] at hd1 hd2
        have hel1 := el_pos (T i) m
        have hel2 := el_pos (T i') m'
        have hc1 : 0 < sgn (T i) * cross ((T i).pts (m + 2) - (T i).pts (m + 1)) (mkPt d0 d1) := by
          have : 0 < sgn (T i) * cross ((T i).pts (m + 2) - (T i).pts (m + 1)) (mkPt d0 d1)
              / dist ((T i).pts (m + 2)) ((T i).pts (m + 1)) := by linarith
          exact (div_pos_iff_of_pos_right hel1).mp this
        have hc2 : 0 < sgn (T i') * cross ((T i').pts (m' + 2) - (T i').pts (m' + 1))
            (mkPt d0 d1) := by
          have : 0 < sgn (T i') * cross ((T i').pts (m' + 2) - (T i').pts (m' + 1)) (mkPt d0 d1)
              / dist ((T i').pts (m' + 2)) ((T i').pts (m' + 1)) := by linarith
          exact (div_pos_iff_of_pos_right hel2).mp this
        obtain ⟨ρ, hρ, hint⟩ := edge_open_interior (T i) m hm0 hmpos
        obtain ⟨ρ', hρ', hint'⟩ := edge_open_interior (T i') m' hm0' hmpos'
        obtain ⟨ε, hε, -, hεD⟩ := small_eps (mkPt d0 d1) (lt_min hρ hρ') one_pos
        exact Set.disjoint_left.mp (hdisj hii)
          (hint _ ε hε (lt_of_lt_of_le hεD (min_le_left _ _)) hc1)
          (hint' _ ε hε (lt_of_lt_of_le hεD (min_le_right _ _)) hc2)
    disjCE := by
      rintro ⟨⟨j, k⟩, hk⟩ ⟨⟨i, m⟩, hm0, hmpos⟩ s t hs ht
      beta_reduce
      by_contra hcon; push Not at hcon
      have hij : i ≠ j := by
        intro hh; subst hh; exact vertex_not_edge _ k hk m hmpos
      have hV0 : (s • ((T j).pts (k + 1) - x) + t • ((T j).pts (k + 2) - x)) 0
          = s * ((T j).pts (k + 1) 0 - x 0) + t * ((T j).pts (k + 2) 0 - x 0) := by simp
      have hV1 : (s • ((T j).pts (k + 1) - x) + t • ((T j).pts (k + 2) - x)) 1
          = s * ((T j).pts (k + 1) 1 - x 1) + t * ((T j).pts (k + 2) 1 - x 1) := by simp
      have hd := normal_dot (T i) m (dist ((T i).pts (m + 2)) ((T i).pts (m + 1)))
        (s • ((T j).pts (k + 1) - x) + t • ((T j).pts (k + 2) - x))
      rw [hV0, hV1] at hd
      have hel := el_pos (T i) m
      have hc : 0 < sgn (T i) * cross ((T i).pts (m + 2) - (T i).pts (m + 1))
          (s • ((T j).pts (k + 1) - x) + t • ((T j).pts (k + 2) - x)) := by
        have : 0 < sgn (T i) * cross ((T i).pts (m + 2) - (T i).pts (m + 1))
            (s • ((T j).pts (k + 1) - x) + t • ((T j).pts (k + 2) - x))
            / dist ((T i).pts (m + 2)) ((T i).pts (m + 1)) := by linarith
        exact (div_pos_iff_of_pos_right hel).mp this
      obtain ⟨ρ, hρ, hint⟩ := edge_open_interior (T i) m hm0 hmpos
      obtain ⟨ε, hε, hεB, hεV⟩ := small_eps
        (s • ((T j).pts (k + 1) - x) + t • ((T j).pts (k + 2) - x)) hρ (B := 1 / (s + t))
        (by positivity)
      have hst : 0 < s + t := by linarith
      have hz1 := corner_interior (T j) k hk hs ht hε (by
        rw [lt_div_iff₀ hst] at hεB; linarith)
      have hz2 := hint _ ε hε hεV hc
      exact Set.disjoint_left.mp (hdisj hij) hz2 hz1 }⟩



/-- **NB for a finite family of triangles** (the report's statement): a point `x` at height
`0 < h = x 1` that is a corner of some tile, with a ball around it covered, cannot exist when (1) and
(2) hold.  `nb_of_fan` ∘ `localFan_of_tiles`, both PROVED: no `sorry`.  For tiles congruent to the base-β tile
at m = 1: `ℓ = min(ef, f²−e²)`, `L = f²`, `c₀ = −cos γ = e/(2f)`, `H = (f²−e²)·sin α`, and (1), (2)
are `NearBase.cond1_iff_sq` / `cond2_of_sq` with `cos²(γ/2) = (1 − c₀)/2 = (2f−e)/(4f)`. -/
theorem nb_tiles {n : ℕ} (T : Fin n → Tri) (x : Plane) {r : ℝ} (hr : 0 < r)
    (hcov : Metric.ball x r ⊆ ⋃ i, (T i).carrier)
    (hdisj : Pairwise fun i j => Disjoint (interior (T i).carrier) (interior (T j).carrier))
    (hup : ∀ i k, 0 ≤ (T i).pts k 1) (hcorner : ∃ i k, (T i).pts k = x)
    {ℓ L H c₀ : ℝ}
    (hside : ∀ i j k, j ≠ k → ℓ ≤ dist ((T i).pts j) ((T i).pts k))
    (hlong : ∀ i j k, dist ((T i).pts j) ((T i).pts k) ≤ L)
    (hcos : ∀ i (j : Fin 3), -c₀ * dist ((T i).pts (j + 1)) ((T i).pts j)
        * dist ((T i).pts (j + 2)) ((T i).pts j)
      ≤ ((T i).pts (j + 1) 0 - (T i).pts j 0) * ((T i).pts (j + 2) 0 - (T i).pts j 0)
        + ((T i).pts (j + 1) 1 - (T i).pts j 1) * ((T i).pts (j + 2) 1 - (T i).pts j 1))
    (halt : ∀ i (j : Fin 3), H * dist ((T i).pts (j + 1)) ((T i).pts (j + 2))
      ≤ |cross ((T i).pts (j + 1) - (T i).pts j) ((T i).pts (j + 2) - (T i).pts j)|)
    (hh : 0 < x 1) (hℓ0 : 0 < ℓ) (hH0 : 0 ≤ H) (hL0 : 0 ≤ L) (hc₀ : 0 ≤ c₀)
    (h1 : 2 * x 1 ^ 2 < ℓ ^ 2 * (1 - c₀))
    (h2 : x 1 ^ 2 * ((ℓ + L) ^ 2 + H ^ 2) < H ^ 2 * ℓ ^ 2) : False := by
  obtain ⟨F⟩ := localFan_of_tiles T x hr hcov hdisj hup hcorner hside hlong hcos halt
  exact nb_of_fan F hh hℓ0 hH0 hL0 hc₀ h1 h2

/-! ## Vacuity rule at the tile level: a genuine tile family satisfying `localFan_of_tiles`' hypotheses -/

theorem plane_ext'' {p q : Plane} (h0 : p 0 = q 0) (h1 : p 1 = q 1) : p = q := by
  ext i; fin_cases i <;> simpa

/-- A triangle whose vertices satisfy a linear inequality lies in that half-plane. -/
theorem carrier_sub {T : Tri} {a b c : ℝ} (hv : ∀ i, c ≤ a * T.pts i 0 + b * T.pts i 1) :
    ∀ y ∈ T.carrier, c ≤ a * y 0 + b * y 1 := by
  have hconv : Convex ℝ {p : Plane | c ≤ a * p 0 + b * p 1} := by
    intro p hp q hq s t hs ht hst
    simp only [Set.mem_setOf_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hp hq ⊢
    have e : c = s * c + t * c := by rw [← add_mul, hst, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left hp hs, mul_le_mul_of_nonneg_left hq ht]
  have hsub : Set.range T.pts ⊆ {p : Plane | c ≤ a * p 0 + b * p 1} := by
    rintro _ ⟨i, rfl⟩; exact hv i
  exact fun y hy => convexHull_min hsub hconv hy

/-- Two tiles on opposite closed sides of a line have disjoint interiors. -/
theorem disjoint_of_sides {T T' : Tri} {a b c : ℝ} (hab : 0 < a ^ 2 + b ^ 2)
    (h1 : ∀ y ∈ T.carrier, c ≤ a * y 0 + b * y 1)
    (h2 : ∀ y ∈ T'.carrier, a * y 0 + b * y 1 ≤ c) :
    Disjoint (interior T.carrier) (interior T'.carrier) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  have e1 := h1 z (interior_subset hz)
  have e2 := h2 z (interior_subset hz')
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
  set v := mkPt a b
  set ε := δ / (2 * (‖v‖ + 1)) with hε
  have hε0 : 0 < ε := by positivity
  have hin : z - ε • v ∈ Metric.ball z δ := by
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
      Real.norm_of_nonneg hε0.le, hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg v]
  have := h1 _ (interior_subset (hball hin))
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, v, mkPt_zero, mkPt_one] at this
  nlinarith

noncomputable def Q0 : Tri := mkTri 0 5 1 5 0 6 (by norm_num [det3])
noncomputable def Q1 : Tri := mkTri 0 5 0 6 (-1) 5 (by norm_num [det3])
noncomputable def Q2 : Tri := mkTri 0 5 (-1) 5 0 4 (by norm_num [det3])
noncomputable def Q3 : Tri := mkTri 0 5 0 4 1 5 (by norm_num [det3])
noncomputable def QT : Fin 4 → Tri := ![Q0, Q1, Q2, Q3]

/-- Cauchy–Schwarz in coordinates: every corner cosine is `≥ −1`. -/
theorem cos_ge_neg_one (p q r : Plane) :
    -1 * dist p q * dist r q ≤ (p 0 - q 0) * (r 0 - q 0) + (p 1 - q 1) * (r 1 - q 1) := by
  have h1 := dist_sq' p q
  have h2 := dist_sq' r q
  have hd1 := dist_nonneg (x := p) (y := q)
  have hd2 := dist_nonneg (x := r) (y := q)
  set u0 := p 0 - q 0; set u1 := p 1 - q 1; set w0 := r 0 - q 0; set w1 := r 1 - q 1
  have hsq : (u0 * w0 + u1 * w1) ^ 2 ≤ (dist p q * dist r q) ^ 2 := by
    rw [mul_pow, h1, h2]; nlinarith [sq_nonneg (u0 * w1 - u1 * w0)]
  have := abs_le_of_sq_le_sq' hsq (by positivity)
  linarith [this.1]

/-- **Vacuity witness for `localFan_of_tiles`' hypotheses**: four right isosceles triangles around
`x = (0,5)` (ball radius `1/2`) satisfy the geometric hypotheses (cover, disjoint interiors, vertices
in the upper half-plane, `x` a corner) jointly with the metric ones at weak constants (`ℓ = 0`,
`H = 0`, `c₀ = 1`, `L` = the sum of all vertex distances); `localFan_of_tiles` then produces a
`LocalFan` from a genuine tile family. -/
theorem tiles_witness :
    Nonempty (LocalFan ((mkPt 0 5) 1) 0
      (∑ i : Fin 4, ∑ j : Fin 3, ∑ k : Fin 3, dist ((QT i).pts j) ((QT i).pts k)) 0 1) := by
  apply localFan_of_tiles QT (mkPt 0 5) (r := 1 / 2) (by norm_num)
  · -- cover
    intro y hy
    rw [Metric.mem_ball] at hy
    have hy2 : dist y (mkPt 0 5) ^ 2 < (1 / 2) ^ 2 := pow_lt_pow_left₀ hy dist_nonneg two_ne_zero
    rw [dist_sq'] at hy2
    simp only [mkPt_zero, mkPt_one] at hy2
    have ha1 : y 0 < 1 / 2 := by nlinarith [sq_nonneg (y 1 - 5)]
    have ha2 : -(1 / 2) < y 0 := by nlinarith [sq_nonneg (y 1 - 5)]
    have hb1 : y 1 - 5 < 1 / 2 := by nlinarith [sq_nonneg (y 0)]
    have hb2 : -(1 / 2) < y 1 - 5 := by nlinarith [sq_nonneg (y 0)]
    have hy' : y = mkPt (y 0) (y 1) := plane_ext'' (by simp) (by simp)
    rw [Set.mem_iUnion]
    rcases le_total 0 (y 0) with h0 | h0 <;> rcases le_total 5 (y 1) with h1 | h1
    · refine ⟨0, ?_⟩; rw [hy']
      exact mem_carrier_of_dets (x₀ := 0) (y₀ := 5) (x₁ := 1) (y₁ := 5) (x₂ := 0) (y₂ := 6)
        (by norm_num [det3]) (by simp only [det3]; nlinarith) (by simp only [det3]; nlinarith)
        (by simp only [det3]; nlinarith)
    · refine ⟨3, ?_⟩; rw [hy']
      exact mem_carrier_of_dets (x₀ := 0) (y₀ := 5) (x₁ := 0) (y₁ := 4) (x₂ := 1) (y₂ := 5)
        (by norm_num [det3]) (by simp only [det3]; nlinarith) (by simp only [det3]; nlinarith)
        (by simp only [det3]; nlinarith)
    · refine ⟨1, ?_⟩; rw [hy']
      exact mem_carrier_of_dets (x₀ := 0) (y₀ := 5) (x₁ := 0) (y₁ := 6) (x₂ := -1) (y₂ := 5)
        (by norm_num [det3]) (by simp only [det3]; nlinarith) (by simp only [det3]; nlinarith)
        (by simp only [det3]; nlinarith)
    · refine ⟨2, ?_⟩; rw [hy']
      exact mem_carrier_of_dets (x₀ := 0) (y₀ := 5) (x₁ := -1) (y₁ := 5) (x₂ := 0) (y₂ := 4)
        (by norm_num [det3]) (by simp only [det3]; nlinarith) (by simp only [det3]; nlinarith)
        (by simp only [det3]; nlinarith)
  · -- disjoint interiors
    have s0x : ∀ y ∈ Q0.carrier, 0 ≤ 1 * y 0 + 0 * y 1 := carrier_sub (by
      intro j; fin_cases j <;> norm_num [Q0, mkTri])
    have s0y : ∀ y ∈ Q0.carrier, 5 ≤ 0 * y 0 + 1 * y 1 := carrier_sub (by
      intro j; fin_cases j <;> norm_num [Q0, mkTri])
    have s1x : ∀ y ∈ Q1.carrier, 0 ≤ (-1) * y 0 + 0 * y 1 := carrier_sub (by
      intro j; fin_cases j <;> norm_num [Q1, mkTri])
    have s1y : ∀ y ∈ Q1.carrier, 5 ≤ 0 * y 0 + 1 * y 1 := carrier_sub (by
      intro j; fin_cases j <;> norm_num [Q1, mkTri])
    have s2x : ∀ y ∈ Q2.carrier, 0 ≤ (-1) * y 0 + 0 * y 1 := carrier_sub (by
      intro j; fin_cases j <;> norm_num [Q2, mkTri])
    have s2y : ∀ y ∈ Q2.carrier, -5 ≤ 0 * y 0 + (-1) * y 1 := carrier_sub (by
      intro j; fin_cases j <;> norm_num [Q2, mkTri])
    have s3x : ∀ y ∈ Q3.carrier, 0 ≤ 1 * y 0 + 0 * y 1 := carrier_sub (by
      intro j; fin_cases j <;> norm_num [Q3, mkTri])
    have s3y : ∀ y ∈ Q3.carrier, -5 ≤ 0 * y 0 + (-1) * y 1 := carrier_sub (by
      intro j; fin_cases j <;> norm_num [Q3, mkTri])
    have lx : ∀ T T' : Tri, (∀ y ∈ T.carrier, 0 ≤ 1 * y 0 + 0 * y 1) →
        (∀ y ∈ T'.carrier, 0 ≤ (-1) * y 0 + 0 * y 1) →
        Disjoint (interior T.carrier) (interior T'.carrier) := by
      intro T T' hi hj
      exact disjoint_of_sides (a := 1) (b := 0) (c := 0) (by norm_num) hi
        (fun y hy => by have := hj y hy; linarith)
    have ly : ∀ T T' : Tri, (∀ y ∈ T.carrier, 5 ≤ 0 * y 0 + 1 * y 1) →
        (∀ y ∈ T'.carrier, -5 ≤ 0 * y 0 + (-1) * y 1) →
        Disjoint (interior T.carrier) (interior T'.carrier) := by
      intro T T' hi hj
      exact disjoint_of_sides (a := 0) (b := 1) (c := 5) (by norm_num) hi
        (fun y hy => by have := hj y hy; linarith)
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij
      | exact lx _ _ s0x s1x | exact lx _ _ s0x s2x | exact lx _ _ s3x s1x | exact lx _ _ s3x s2x
      | exact (lx _ _ s0x s1x).symm | exact (lx _ _ s0x s2x).symm
      | exact (lx _ _ s3x s1x).symm | exact (lx _ _ s3x s2x).symm
      | exact ly _ _ s0y s3y | exact ly _ _ s1y s2y | exact (ly _ _ s0y s3y).symm
      | exact (ly _ _ s1y s2y).symm
  · intro i k
    fin_cases i <;> fin_cases k <;> norm_num [QT, Q0, Q1, Q2, Q3, mkTri]
  · exact ⟨0, 0, rfl⟩
  · intro i j k _; exact dist_nonneg
  · intro i j k
    exact (Finset.single_le_sum (f := fun k => dist ((QT i).pts j) ((QT i).pts k))
      (fun _ _ => dist_nonneg) (Finset.mem_univ k)).trans
      ((Finset.single_le_sum (f := fun j => ∑ k : Fin 3, dist ((QT i).pts j) ((QT i).pts k))
        (fun _ _ => Finset.sum_nonneg (fun _ _ => dist_nonneg)) (Finset.mem_univ j)).trans
        (Finset.single_le_sum
          (f := fun i => ∑ j : Fin 3, ∑ k : Fin 3, dist ((QT i).pts j) ((QT i).pts k))
          (fun _ _ => Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => dist_nonneg)))
          (Finset.mem_univ i)))
  · intro i j; exact cos_ge_neg_one _ _ _
  · intro i j; rw [zero_mul]; exact abs_nonneg _

end Erdos634.Draft.NearBaseVertex

#print axioms Erdos634.Draft.NearBaseVertex.flank_P
#print axioms Erdos634.Draft.NearBaseVertex.mixed_false
#print axioms Erdos634.Draft.NearBaseVertex.corner_not_F
#print axioms Erdos634.Draft.NearBaseVertex.exists_F_across
#print axioms Erdos634.Draft.NearBaseVertex.third_vertex_below
#print axioms Erdos634.Draft.NearBaseVertex.nb_of_fan
#print axioms Erdos634.Draft.NearBaseVertex.fan_example
#print axioms Erdos634.Draft.NearBaseVertex.corner_cone
#print axioms Erdos634.Draft.NearBaseVertex.corner_interior
#print axioms Erdos634.Draft.NearBaseVertex.edge_cone_dir
#print axioms Erdos634.Draft.NearBaseVertex.edge_open_interior
#print axioms Erdos634.Draft.NearBaseVertex.cover_tile
#print axioms Erdos634.Draft.NearBaseVertex.localFan_of_tiles
#print axioms Erdos634.Draft.NearBaseVertex.nb_tiles
#print axioms Erdos634.Draft.NearBaseVertex.tiles_witness
