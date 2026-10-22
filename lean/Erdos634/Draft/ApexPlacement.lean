-- Draft/ApexPlacement.lean — APEX PLACEMENT for a real congruent dissection of a base-β target
-- (thm:pierce(i) / lem:apex / thm:apexconfig / cor:noTP, the gate of Theorem H).  NOT imported
-- into All.lean.  See the section headers for what is proved; `#print axioms` at the foot.
--
-- PROVED (no `sorry`, axioms propext/Classical.choice/Quot.sound):
--   §0 `cover_tile_dir`, `flank_neighbour_gen` — CornerAdjacency.flank_neighbour with its ball
--      hypothesis replaced by per-direction covering (works at a TARGET VERTEX).
--   §1 `apex_three_tiles` — exactly three tiles contain the apex, each α, apex a vertex of each.
--   §2 `ApexCone`, `leg_tile` (a tile has a corner at A with a flank along each leg),
--      `inner_neighbour` (the tile across an inner flank).
--   §4 `apex_config` — thm:apexconfig / lem:apex clauses 3–5, GIVEN clause (2) `LegFlanksC`
--      (discharged at m = 1 in Draft/ApexLegWord.lean, every coprime member).
--   §5 `coeff_alg`, `coeff_sum` (the rays ρ₁, r leave the target at f·b: cone coordinates sum 1/f),
--      `exists_hframe_coords` / `exists_hframe` — the HFrame from a real dissection.
-- REDISCOVERY LEDGER: the apex census is `TileAt.congruentDissection_apex_counts` (VERIFIED); the
-- flank lengths {b, c} are `ApexEdgesReal.congruentDissection_apex_edges` (VERIFIED); the ray/strip
-- metric (r meets the base at distance f·b; L at Q_{f−1}) is `MirrorStripR2` §2 in fixed coordinates
-- (`pQ_on_base_iff`, `Qbase_on_base`) — here re-derived coordinate-free for a real dissection's frame.
-- NEW: the wedge ORDER at the apex (which tile lies across which flank) for a real dissection.
--
-- Build (scratch oleans; never .lake): as Draft/HalfTurnR3R4Order.lean, then
--   lake env bash -c 'LEAN_PATH=$S:$LEAN_PATH lean Erdos634/Draft/ApexPlacement.lean'
import Erdos634.Draft.CornerAdjacency
import Erdos634.Draft.HalfTurnR3R4Glue
import Erdos634.ApexEdgesReal
import Erdos634.TileAt
import Erdos634.MarchFlank
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

namespace Erdos634.Draft.ApexPlacement

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.NearBaseVertex
open Erdos634.Draft.CornerAdjacency Erdos634.TilePlacement

/-! ## §0 Generic: the flank neighbour at a point NOT interior to the target

`CornerAdjacency.flank_neighbour` needs a covered ball around `x`; at a target vertex there is none.
Its proof only ever uses (i) that the approach directions `U − W/(n+K)` are covered by a tile
containing `x`, and (ii) that no tile covering an approach direction contains the "open wedge"
points `x + τ(sU + tW)` in its interior.  `flank_neighbour_gen` takes exactly these two facts as
hypotheses (and a reference pair `U, W` with `cross U W ≠ 0`, not necessarily a tile's flanks). -/

/-- A direction from `x` whose short initial segment is covered lies in a tile containing `x`
(`NearBaseVertex.cover_tile` with a one-direction covering hypothesis). -/
theorem cover_tile_dir {n : ℕ} (T : Fin n → Tri) (x : Plane) (hn : 0 < n) {D : Plane}
    (hD : D ≠ 0) {τ₀ : ℝ} (hτ₀ : 0 < τ₀)
    (hcov : ∀ τ : ℝ, 0 < τ → τ ≤ τ₀ → x + τ • D ∈ ⋃ i, (T i).carrier) :
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
  obtain ⟨ρ, hρ, hle⟩ := Erdos634.Geometry.exists_common_radius hn f hf
  have hDn : 0 < ‖D‖ := norm_pos_iff.mpr hD
  set δ := min ρ (τ₀ * ‖D‖) / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδρ : δ < ρ := by have := min_le_left ρ (τ₀ * ‖D‖); linarith
  have hδτ : δ < τ₀ * ‖D‖ := by
    have := min_le_right ρ (τ₀ * ‖D‖); have : 0 < τ₀ * ‖D‖ := by positivity
    linarith
  set ε := δ / ‖D‖ with hεdef
  have hε : 0 < ε := by positivity
  have hετ : ε ≤ τ₀ := by rw [hεdef, div_le_iff₀ hDn]; linarith
  have hdist : dist (x + ε • D) x = δ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hε.le, hεdef,
      div_mul_cancel₀ _ hDn.ne']
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov ε hε hετ)
  refine ⟨i, ε, hε, ?_, hi⟩
  by_contra hxi
  have h1 : Metric.infDist x (T i).carrier ≤ dist x (x + ε • D) := Metric.infDist_le_dist_of_mem hi
  have h2 : ρ ≤ Metric.infDist x (T i).carrier := by
    have := hle i; simp only [f, hxi, if_false] at this; exact this
  rw [dist_comm, hdist] at h1
  linarith

/-- `lim_nonneg` with the step `1/(n+K)`. -/
theorem lim_nonneg_K {a b : ℝ} {S : Set ℕ} {K : ℕ} (hK : 1 ≤ K) (hS : S.Infinite)
    (h : ∀ n ∈ S, 0 ≤ a - (1 / ((n : ℝ) + K)) * b) : 0 ≤ a := by
  by_contra ha; push Not at ha
  obtain ⟨n, hnS, hn⟩ := hS.exists_gt ⌈|b| / (-a)⌉₊
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have h1 : |b| / (-a) < (n : ℝ) + K := by
    have := Nat.le_ceil (|b| / (-a))
    have : (⌈|b| / (-a)⌉₊ : ℝ) < n := by exact_mod_cast hn
    linarith
  have hpos : (0 : ℝ) < (n : ℝ) + K := by positivity
  have h2 : |b| < -a * ((n : ℝ) + K) := by rw [div_lt_iff₀ (by linarith)] at h1; linarith
  have h3 : (1 / ((n : ℝ) + K)) * b ≥ -(|b| / ((n : ℝ) + K)) := by
    rw [one_div_mul_eq_div, ge_iff_le, neg_le, ← neg_div]
    exact div_le_div_of_nonneg_right (by linarith [neg_abs_le b]) hpos.le
  have h4 : |b| / ((n : ℝ) + K) < -a := by rwa [div_lt_iff₀ hpos]
  have := h n hnS
  linarith

theorem invK_pos {K : ℕ} (hK : 1 ≤ K) (n : ℕ) : (0 : ℝ) < 1 / ((n : ℝ) + K) := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have : (0 : ℝ) < (n : ℝ) + K := by positivity
  positivity

set_option maxHeartbeats 1000000 in
/-- **The flank neighbour, generic form — PROVED.**  `U, W` independent; every approach direction
`U − W/(n+K)` is covered by some tile containing `x`; no tile covering an approach direction has a
point `x + τ(sU + tW)` (`s, t, τ > 0`, `τ(s+t) < 1`) in its interior.  Then some tile `j` containing
`x` and covering an approach direction lies across `U`: either `x` is a corner of `j` with a flank
`U'`, `U = S·U'` (`S > 0`), and `j`'s other flank `W'` strictly on the other side of `ℝU` from `W`;
or `x` is in the relative interior of an edge of `j` parallel to `U`.  (The proof is
`CornerAdjacency.flank_neighbour`'s, with its two uses of the ball replaced by the hypotheses.) -/
theorem flank_neighbour_gen {N : ℕ} (T : Fin N → Tri) (x : Plane) {U W : Plane}
    (hΔi : cross U W ≠ 0) (K : ℕ) (hK : 1 ≤ K)
    (hcovn : ∀ n : ℕ, ∃ (j : Fin N) (ε : ℝ), 0 < ε ∧ x ∈ (T j).carrier ∧
      x + ε • (U - (1 / ((n : ℝ) + K)) • W) ∈ (T j).carrier)
    (hopen : ∀ j : Fin N, (∃ (n : ℕ) (ε : ℝ), 0 < ε ∧
        x + ε • (U - (1 / ((n : ℝ) + K)) • W) ∈ (T j).carrier) →
      ∀ s t τ : ℝ, 0 < s → 0 < t → 0 < τ → τ * (s + t) < 1 →
        x + τ • (s • U + t • W) ∉ interior (T j).carrier) :
    ∃ j, x ∈ (T j).carrier ∧ (∃ (n : ℕ) (ε : ℝ), 0 < ε ∧
        x + ε • (U - (1 / ((n : ℝ) + K)) • W) ∈ (T j).carrier) ∧
      ((∃ m : Fin 3, (T j).pts m = x ∧ ∃ U' W' : Plane, IsFlankPair (T j) m x U' W' ∧
          ∃ S : ℝ, 0 < S ∧ U = S • U' ∧ cross U W' * cross U W < 0) ∨
       (∃ m : Fin 3, (T j).basis.coord m x = 0 ∧ (∀ l, l ≠ m → 0 < (T j).basis.coord l x) ∧
          cross ((T j).pts (m + 2) - (T j).pts (m + 1)) U = 0 ∧
          sgn (T j) * cross ((T j).pts (m + 2) - (T j).pts (m + 1)) W < 0)) := by
  classical
  have hU0 : U ≠ 0 := by rintro rfl; apply hΔi; simp [cross_apply]
  -- the approach directions
  set Dn : ℕ → Plane := fun n => U - (1 / ((n : ℝ) + K)) • W with hDn
  choose J ε hε hxJ hyJ using hcovn
  obtain ⟨j, hjinf0⟩ := Finite.exists_infinite_fiber J
  set S := J ⁻¹' {j} with hSdef
  have hjinf : S.Infinite := Set.infinite_coe_iff.mp hjinf0
  have hS : ∀ n ∈ S, J n = j := fun n hn => hn
  obtain ⟨n0, hn0⟩ := hjinf.nonempty
  have hxj : x ∈ (T j).carrier := by rw [← hS n0 hn0]; exact hxJ n0
  have hcovj : ∃ (n : ℕ) (ε : ℝ), 0 < ε ∧ x + ε • (U - (1 / ((n : ℝ) + K)) • W) ∈ (T j).carrier :=
    ⟨n0, ε n0, hε n0, by have := hyJ n0; rw [hS n0 hn0] at this; exact this⟩
  have hop := hopen j hcovj
  refine ⟨j, hxj, hcovj, ?_⟩
  by_cases hv : ∃ m, (T j).pts m = x
  · -- vertex case
    left
    obtain ⟨m, hm⟩ := hv
    refine ⟨m, hm, ?_⟩
    set F1 := (T j).pts (m + 1) - x with hF1
    set F2 := (T j).pts (m + 2) - x with hF2
    have hΔj : cross F1 F2 ≠ 0 := by
      have h := hind_h (T j) m hm
      simpa [hF1, hF2, cross_apply] using h
    have hA : ∀ n ∈ S, 0 ≤ cross F1 (Dn n) * cross F1 F2 ∧ 0 ≤ cross (Dn n) F2 * cross F1 F2 := by
      intro n hnS
      have hy := hyJ n; rw [hS n hnS] at hy
      obtain ⟨s, t, hs, ht, hD⟩ := corner_cone_vec (T j) m hm (hε n) hy
      exact cone_cross hs ht hD
    have hL1 : 0 ≤ cross F1 U * cross F1 F2 := by
      apply lim_nonneg_K (b := cross F1 W * cross F1 F2) hK hjinf
      intro n hnS
      have := (hA n hnS).1
      simp only [hDn, cross_sub_right', cross_smul_right] at this
      linarith
    have hL2 : 0 ≤ cross U F2 * cross F1 F2 := by
      apply lim_nonneg_K (b := cross W F2 * cross F1 F2) hK hjinf
      intro n hnS
      have := (hA n hnS).2
      simp only [hDn] at this
      rw [sub_eq_add_neg, cross_add_left', ← neg_smul, cross_smul_left'] at this
      linarith
    -- `U` is not in `j`'s OPEN wedge
    have hnot : ¬ (0 < cross F1 U * cross F1 F2 ∧ 0 < cross U F2 * cross F1 F2) := by
      rintro ⟨h1, h2⟩
      set p := cross U F2 * cross F1 F2
      set q := cross F1 U * cross F1 F2
      set p' := cross W F2 * cross F1 F2
      set q' := cross F1 W * cross F1 F2
      set δ := min p q / (2 * (|p'| + |q'| + 1)) with hδ
      have hδ0 : 0 < δ := by
        have : 0 < min p q := lt_min h2 h1
        positivity
      have hmin1 : min p q ≤ p := min_le_left _ _
      have hmin2 : min p q ≤ q := min_le_right _ _
      have hδp : δ * |p'| < p := by
        have hden : 0 < 2 * (|p'| + |q'| + 1) := by positivity
        have : δ * (2 * (|p'| + |q'| + 1)) = min p q := by
          rw [hδ]; field_simp
        nlinarith [abs_nonneg p', abs_nonneg q']
      have hδq : δ * |q'| < q := by
        have hden : 0 < 2 * (|p'| + |q'| + 1) := by positivity
        have : δ * (2 * (|p'| + |q'| + 1)) = min p q := by
          rw [hδ]; field_simp
        nlinarith [abs_nonneg p', abs_nonneg q']
      set Dp := U + δ • W with hDp
      have hs' : 0 < cross Dp F2 * cross F1 F2 := by
        have : cross Dp F2 * cross F1 F2 = p + δ * p' := by
          simp only [hDp, cross_add_left', cross_smul_left', p, p']; ring
        rw [this]; nlinarith [neg_abs_le p']
      have ht' : 0 < cross F1 Dp * cross F1 F2 := by
        have : cross F1 Dp * cross F1 F2 = q + δ * q' := by
          simp only [hDp, cross_add_right, cross_smul_right, q, q']; ring
        rw [this]; nlinarith [neg_abs_le q']
      have hΔ2 : 0 < cross F1 F2 ^ 2 := by positivity
      have hs'' : 0 < cross Dp F2 / cross F1 F2 := by
        rw [show cross Dp F2 / cross F1 F2 = cross Dp F2 * cross F1 F2 / cross F1 F2 ^ 2 by
          field_simp]
        positivity
      have ht'' : 0 < cross F1 Dp / cross F1 F2 := by
        rw [show cross F1 Dp / cross F1 F2 = cross F1 Dp * cross F1 F2 / cross F1 F2 ^ 2 by
          field_simp]
        positivity
      have heq : (1 : ℝ) • U + δ • W
          = (cross Dp F2 / cross F1 F2) • F1 + (cross F1 Dp / cross F1 F2) • F2 := by
        have hc := cramer F1 F2 Dp
        rw [one_smul, ← hDp]
        rw [div_eq_inv_mul, div_eq_inv_mul, mul_smul, mul_smul, ← smul_add, ← hc, smul_smul,
          inv_mul_cancel₀ hΔj, one_smul]
      -- a common point: interior to `j` (its wedge), and excluded by `hopen`
      set s2 := cross Dp F2 / cross F1 F2
      set t2 := cross F1 Dp / cross F1 F2
      set τ := 1 / (2 * (1 + δ + s2 + t2) + 1) with hτdef
      have hτ : 0 < τ := by positivity
      have hsum : 0 < 2 * (1 + δ + s2 + t2) + 1 := by positivity
      have hτ1 : τ * (1 + δ) < 1 := by
        rw [hτdef, one_div_mul_eq_div, div_lt_one hsum]; linarith
      have hτ2 : τ * (s2 + t2) < 1 := by
        rw [hτdef, one_div_mul_eq_div, div_lt_one hsum]; linarith
      have z2 := open_dir_interior (T j) m hm (Or.inl ⟨rfl, rfl⟩) hs'' ht'' hτ hτ2
      rw [← heq] at z2
      exact hop 1 δ τ one_pos hδ0 hτ hτ1 z2
    -- so `U` lies on a flank of `j`
    rcases not_and_or.mp hnot with h | h
    · -- `cross F1 U = 0`: `U` is along `F1`
      have h0 : cross F1 U = 0 := by
        have := le_antisymm (not_lt.mp h) hL1
        rcases mul_eq_zero.mp this with h' | h'
        · exact h'
        · exact absurd h' hΔj
      have hUe := smul_of_cross_zero hΔj F2 rfl h0
      set S0 := cross U F2 / cross F1 F2 with hS0
      have hS0ne : S0 ≠ 0 := by
        intro h'; rw [h', zero_smul] at hUe; exact hU0 hUe
      have hS0pos : 0 < S0 := by
        have : 0 ≤ S0 := by
          rw [hS0, show cross U F2 / cross F1 F2 = cross U F2 * cross F1 F2 / cross F1 F2 ^ 2 by
            field_simp]
          positivity
        exact lt_of_le_of_ne this (Ne.symm hS0ne)
      refine ⟨F1, F2, Or.inl ⟨rfl, rfl⟩, S0, hS0pos, hUe, ?_⟩
      have hW : cross F1 W * cross F1 F2 ≤ 0 := by
        have key : ∀ n ∈ S, 0 ≤ -(1 / ((n : ℝ) + K)) * (cross F1 W * cross F1 F2) := by
          intro n hnS
          have := (hA n hnS).1
          simp only [hDn, cross_sub_right', cross_smul_right, h0] at this
          linarith
        by_contra hc; push Not at hc
        obtain ⟨n, hnS⟩ := hjinf.nonempty
        have := key n hnS
        have hp : (0 : ℝ) < 1 / ((n : ℝ) + K) := invK_pos hK n
        nlinarith
      have hW' : cross F1 W ≠ 0 := by
        intro h'
        apply hΔi
        rw [hUe, cross_smul_left', h', mul_zero]
      have e1 : cross U F2 = S0 * cross F1 F2 := by rw [hUe, cross_smul_left']
      have e2 : cross U W = S0 * cross F1 W := by rw [hUe, cross_smul_left']
      rw [e1, e2]
      have hlt : cross F1 W * cross F1 F2 < 0 :=
        lt_of_le_of_ne hW (mul_ne_zero hW' hΔj)
      have e3 : S0 * cross F1 F2 * (S0 * cross F1 W)
          = (S0 * S0) * (cross F1 W * cross F1 F2) := by ring
      rw [e3]; exact mul_neg_of_pos_of_neg (mul_pos hS0pos hS0pos) hlt
    · -- `cross U F2 = 0`: `U` is along `F2`
      have h0 : cross U F2 = 0 := by
        have := le_antisymm (not_lt.mp h) hL2
        rcases mul_eq_zero.mp this with h' | h'
        · exact h'
        · exact absurd h' hΔj
      have h0' : cross F2 U = 0 := by rw [cross_anti, h0, neg_zero]
      have hΔj' : cross F2 F1 ≠ 0 := by rw [cross_anti]; exact neg_ne_zero.mpr hΔj
      have hUe := smul_of_cross_zero hΔj' F1 rfl h0'
      set S0 := cross U F1 / cross F2 F1 with hS0
      have hS0ne : S0 ≠ 0 := by
        intro h'; rw [h', zero_smul] at hUe; exact hU0 hUe
      have hS0pos : 0 < S0 := by
        have : 0 ≤ S0 := by
          have e : S0 = cross F1 U * cross F1 F2 / cross F1 F2 ^ 2 := by
            rw [hS0, cross_anti F2 F1, cross_anti U F1]; field_simp
          rw [e]; positivity
        exact lt_of_le_of_ne this (Ne.symm hS0ne)
      refine ⟨F2, F1, Or.inr ⟨rfl, rfl⟩, S0, hS0pos, hUe, ?_⟩
      have hW : cross W F2 * cross F1 F2 ≤ 0 := by
        have key : ∀ n ∈ S, 0 ≤ -(1 / ((n : ℝ) + K)) * (cross W F2 * cross F1 F2) := by
          intro n hnS
          have := (hA n hnS).2
          simp only [hDn] at this
          rw [sub_eq_add_neg, cross_add_left', ← neg_smul, cross_smul_left', h0] at this
          linarith
        by_contra hc; push Not at hc
        obtain ⟨n, hnS⟩ := hjinf.nonempty
        have := key n hnS
        have hp : (0 : ℝ) < 1 / ((n : ℝ) + K) := invK_pos hK n
        nlinarith
      have hW' : cross W F2 ≠ 0 := by
        intro h'
        apply hΔi
        rw [hUe, cross_smul_left', cross_anti, h', neg_zero, mul_zero]
      have e1 : cross U F1 = S0 * cross F2 F1 := by rw [hUe, cross_smul_left']
      have e2 : cross U W = S0 * cross F2 W := by rw [hUe, cross_smul_left']
      rw [e1, e2, cross_anti F1 F2, cross_anti W F2]
      have hlt : cross W F2 * cross F1 F2 < 0 :=
        lt_of_le_of_ne hW (mul_ne_zero hW' hΔj)
      have e3 : S0 * -cross F1 F2 * (S0 * -cross W F2)
          = (S0 * S0) * (cross W F2 * cross F1 F2) := by ring
      rw [e3]; exact mul_neg_of_pos_of_neg (mul_pos hS0pos hS0pos) hlt
  · -- `x` is not a vertex of `j`
    right
    push Not at hv
    rcases (T j).classify (fun m h => hv m h.symm) with hall | ⟨m, hm0, hmpos⟩ | ⟨m, hneg⟩
    · exfalso
      obtain ⟨ρ, hρ, hsub⟩ := (T j).ball_subset_of_pos hall
      obtain ⟨τ, hτ, hτB, hτV⟩ := small_eps ((1 : ℝ) • U + (1 : ℝ) • W) hρ (B := 1 / 2)
        (by norm_num)
      have hz2 : x + τ • ((1 : ℝ) • U + (1 : ℝ) • W) ∈ interior (T j).carrier := by
        apply interior_maximal hsub Metric.isOpen_ball
        rw [Metric.mem_ball, dist_add_smul _ _ hτ.le]; exact hτV
      exact hop 1 1 τ one_pos one_pos hτ (by linarith) hz2
    · refine ⟨m, hm0, hmpos, ?_⟩
      set E := (T j).pts (m + 2) - (T j).pts (m + 1) with hE
      have hA : ∀ n ∈ S, 0 ≤ sgn (T j) * cross E (Dn n) := by
        intro n hnS
        have hy := hyJ n; rw [hS n hnS] at hy
        exact edge_cone_dir (T j) m hm0 (hε n) hy
      have hL : 0 ≤ sgn (T j) * cross E U := by
        apply lim_nonneg_K (b := sgn (T j) * cross E W) hK hjinf
        intro n hnS
        have := hA n hnS
        simp only [hDn, cross_sub_right', cross_smul_right] at this
        linarith
      have hnot : ¬ 0 < sgn (T j) * cross E U := by
        intro hpos
        set p := sgn (T j) * cross E U
        set p' := sgn (T j) * cross E W
        set δ := p / (2 * (|p'| + 1)) with hδ
        have hδ0 : 0 < δ := by positivity
        have hδp : δ * |p'| < p := by
          have : δ * (2 * (|p'| + 1)) = p := by rw [hδ]; field_simp
          nlinarith [abs_nonneg p']
        obtain ⟨ρ, hρ, hint⟩ := edge_open_interior (T j) m hm0 hmpos
        obtain ⟨τ, hτ, hτB, hτV⟩ := small_eps ((1 : ℝ) • U + δ • W) hρ (B := 1 / (1 + δ))
          (by positivity)
        have hc : 0 < sgn (T j) * cross E ((1 : ℝ) • U + δ • W) := by
          have : sgn (T j) * cross E ((1 : ℝ) • U + δ • W) = p + δ * p' := by
            simp only [cross_add_right, cross_smul_right, p, p']; ring
          rw [this]; nlinarith [neg_abs_le p']
        have z2 := hint _ τ hτ hτV hc
        have hτ1 : τ * (1 + δ) < 1 := by
          rw [lt_div_iff₀ (by positivity)] at hτB; linarith
        exact hop 1 δ τ one_pos hδ0 hτ hτ1 z2
      have h0 : sgn (T j) * cross E U = 0 := le_antisymm (not_lt.mp hnot) hL
      have hsgn : sgn (T j) ≠ 0 := by
        have := sgn_sq (T j); intro h; rw [h] at this; norm_num at this
      have hEU : cross E U = 0 := by
        rcases mul_eq_zero.mp h0 with h | h
        · exact absurd h hsgn
        · exact h
      refine ⟨hEU, ?_⟩
      have hW : sgn (T j) * cross E W ≤ 0 := by
        by_contra hc; push Not at hc
        obtain ⟨n, hnS⟩ := hjinf.nonempty
        have := hA n hnS
        simp only [hDn, cross_sub_right', cross_smul_right, hEU] at this
        have hp : (0 : ℝ) < 1 / ((n : ℝ) + K) := invK_pos hK n
        nlinarith
      have hEne : E ≠ 0 := by
        intro h
        have := el_pos (T j) m
        rw [dist_eq_norm, ← hE, h, norm_zero] at this
        exact lt_irrefl _ this
      have hEW : cross E W ≠ 0 := by
        intro h'
        apply hΔi
        have hE2 : E 0 ^ 2 + E 1 ^ 2 ≠ 0 := by
          intro h2
          apply hEne
          have h0' : E 0 = 0 := by nlinarith [sq_nonneg (E 0), sq_nonneg (E 1)]
          have h1' : E 1 = 0 := by nlinarith [sq_nonneg (E 0), sq_nonneg (E 1)]
          ext l; fin_cases l <;> simp [h0', h1']
        simp only [cross_apply] at hEU h' ⊢
        have : (U 0 * W 1 - U 1 * W 0) * (E 0 ^ 2 + E 1 ^ 2) = 0 := by
          linear_combination -(W 1 * E 1 + W 0 * E 0) * hEU + (U 1 * E 1 + U 0 * E 0) * h'
        rcases mul_eq_zero.mp this with h3 | h3
        · exact h3
        · exact absurd h3 hE2
      exact lt_of_le_of_ne hW (mul_ne_zero hsgn hEW)
    · exfalso
      have := ((mem_carrier_iff _ _).mp hxj) m
      linarith


/-! ## §1 The apex: exactly three tiles, each presenting `α` there (`lem:apex`, clause 2)

`TileAt.congruentDissection_apex_counts` (VERIFIED, in All) is the census: three tiles present `α`
at the apex and none presents `β`, `γ` or `π`.  Here that census is turned into CARRIER membership
(a tile contains the apex iff it is one of the three) and each of the three has the apex as a
vertex (`ApexEdgesReal.isVertex_of_localAngle_ne`).  Rediscovery note: the census itself is the
corpus theorem; the carrier form is a few lines on top of it. -/

theorem angle_facts {α β γ : ℝ} (hA : MarchSlots.AngleData α β γ) :
    α ≠ β ∧ α ≠ γ ∧ α ≠ Real.pi ∧ α ≠ 0 ∧ β ≠ γ ∧ β ≠ Real.pi ∧ β ≠ 0 ∧ γ ≠ Real.pi ∧ γ ≠ 0 ∧
      α ≠ 2 * Real.pi ∧ 3 * α < Real.pi ∧ 0 < α := by
  obtain ⟨hα, hβ, hαβ, hγ, hrel, -⟩ := hA
  have hpi := Real.pi_pos
  refine ⟨hαβ, fun h => ?_, fun h => ?_, hα.ne', fun h => ?_, fun h => ?_, hβ.ne', fun h => ?_,
    fun h => ?_, fun h => ?_, by linarith, hα⟩
  · rw [hγ] at h; linarith
  · linarith
  · rw [hγ] at h; linarith
  · linarith
  · rw [hγ] at h; linarith
  · rw [hγ] at h; linarith
  · linarith

theorem tile_sub_target {N : ℕ} (D : Dissection N) (i : Fin N) :
    (D.tile i).carrier ⊆ D.target.carrier := by
  rw [← D.covers]; exact Set.subset_iUnion (fun j => (D.tile j).carrier) i

/-- **`apex_three_tiles` — PROVED.**  At the apex `A = D.target.pts k` (corner angle `3α`) of a
real congruent dissection, exactly three distinct tiles contain `A`; each presents `α` there and
has `A` as a vertex. -/
theorem apex_three_tiles {N : ℕ} (D : CongruentDissection N) {α β γ : ℝ}
    (hAng : MarchSlots.AngleData α β γ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
      = 3 * α) :
    ∃ i₁ i₂ i₃ : Fin N, i₁ ≠ i₂ ∧ i₁ ≠ i₃ ∧ i₂ ≠ i₃ ∧
      (∀ i, D.target.pts k ∈ (D.tile i).carrier ↔ (i = i₁ ∨ i = i₂ ∨ i = i₃)) ∧
      (∀ i, D.target.pts k ∈ (D.tile i).carrier →
        (D.tile i).localAngle (D.target.pts k) = α ∧ ∃ j, (D.tile i).pts j = D.target.pts k) := by
  classical
  obtain ⟨hαβ, hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hγπ, hγ0, hα2π, -, -⟩ := angle_facts hAng
  obtain ⟨-, -, -, hγdef, hrel, hirr⟩ := hAng
  obtain ⟨hcα, hcβ, hcγ, hcπ⟩ := Erdos634.Geometry.Dissection.congruentDissection_apex_counts D α β γ
    hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 Real.pi_ne_zero hγdef hrel hirr hα' hβ' hγ' k hcorner
  set A := D.target.pts k with hAdef
  -- a tile containing `A` presents `α`
  have hmemα : ∀ i, A ∈ (D.tile i).carrier → (D.tile i).localAngle A = α := by
    intro i hi
    have hv := Erdos634.Geometry.Dissection.congruentDissection_localAngle_mem D α β γ hα' hβ' hγ' k i
    have hne := Erdos634.MarchFlank.localAngle_ne_zero_of_mem (D.tile i) hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with h | h | h | h | h
    · exact h
    · exfalso
      have : i ∈ ({i | (D.tile i).localAngle A = β} : Finset (Fin N)) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h
      rw [Finset.card_eq_zero] at hcβ; rw [hcβ] at this; simp at this
    · exfalso
      have : i ∈ ({i | (D.tile i).localAngle A = γ} : Finset (Fin N)) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h
      rw [Finset.card_eq_zero] at hcγ; rw [hcγ] at this; simp at this
    · exfalso
      have : i ∈ ({i | (D.tile i).localAngle A = Real.pi} : Finset (Fin N)) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h
      rw [Finset.card_eq_zero] at hcπ; rw [hcπ] at this; simp at this
    · exact absurd h hne
  have hvertα : ∀ i, (D.tile i).localAngle A = α → ∃ j, (D.tile i).pts j = A := by
    intro i hi
    obtain ⟨j, hj⟩ := Erdos634.ApexEdgesReal.isVertex_of_localAngle_ne (D.tile i) hα2π hαπ hα0 hi
    exact ⟨j, hj.symm⟩
  have hαmem : ∀ i, (D.tile i).localAngle A = α → A ∈ (D.tile i).carrier := by
    intro i hi
    obtain ⟨j, hj⟩ := hvertα i hi
    rw [← hj]; exact subset_convexHull ℝ _ (Set.mem_range_self j)
  obtain ⟨x, y, z, hxy, hxz, hyz, hset⟩ := Finset.card_eq_three.mp hcα
  refine ⟨x, y, z, hxy, hxz, hyz, fun i => ?_, fun i hi => ⟨hmemα i hi, hvertα i (hmemα i hi)⟩⟩
  constructor
  · intro hi
    have hmem : i ∈ ({i | (D.tile i).localAngle A = α} : Finset (Fin N)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hmemα i hi
    rw [hset] at hmem
    simpa using hmem
  · intro hi
    apply hαmem
    have hmem : i ∈ ({x, y, z} : Finset (Fin N)) := by
      rcases hi with rfl | rfl | rfl <;> simp
    rw [← hset] at hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact hmem

/-! ## §2 The apex cone, the leg tiles and the inner neighbours

`ApexCone T A Q Q'`: `A` is a corner of the target `T` with legs towards `Q`, `Q'`; directions into
`T` from `A` are the nonnegative combinations of `Q − A`, `Q' − A`, and positive combinations enter
the interior.  Both orders hold at every target vertex (`apexCone_target`, `.swap`). -/

structure ApexCone (T : Tri) (A Q Q' : Plane) : Prop where
  cone : ∀ (D : Plane) (ε : ℝ), 0 < ε → A + ε • D ∈ T.carrier →
    ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ D = s • (Q - A) + t • (Q' - A)
  inter : ∀ s t ε : ℝ, 0 < s → 0 < t → 0 < ε → ε * (s + t) < 1 →
    A + ε • (s • (Q - A) + t • (Q' - A)) ∈ interior T.carrier
  det : cross (Q - A) (Q' - A) ≠ 0

theorem apexCone_target (T : Tri) (k : Fin 3) :
    ApexCone T (T.pts k) (T.pts (k + 1)) (T.pts (k + 2)) where
  cone D ε hε hy := corner_cone_vec T k rfl hε hy
  inter s t ε hs ht hε h1 := corner_interior T k rfl hs ht hε h1
  det := by rw [T.det_cyclic k]; exact T.det_ne_zero

theorem ApexCone.swap {T : Tri} {A Q Q' : Plane} (h : ApexCone T A Q Q') : ApexCone T A Q' Q where
  cone D ε hε hy := by
    obtain ⟨s, t, hs, ht, hD⟩ := h.cone D ε hε hy
    exact ⟨t, s, ht, hs, by rw [hD, add_comm]⟩
  inter s t ε hs ht hε h1 := by
    have := h.inter t s ε ht hs hε (by rw [add_comm]; exact h1)
    rwa [add_comm (t • _)] at this
  det := by rw [cross_anti]; exact neg_ne_zero.mpr h.det

/-- Points `A + ε(s(Q−A) − t(Q'−A))`, `t > 0`, are outside the target. -/
theorem ApexCone.outside {T : Tri} {A Q Q' : Plane} (h : ApexCone T A Q Q') {s t ε : ℝ}
    (ht : 0 < t) (hε : 0 < ε) : A + ε • (s • (Q - A) + t • (-(Q' - A))) ∉ T.carrier := by
  intro hy
  obtain ⟨s', t', -, ht', hD⟩ := h.cone _ ε hε hy
  have hc := congrArg (cross (Q - A)) hD
  simp only [cross_add_right, cross_smul_right, cross_self'] at hc
  have e : cross (Q - A) (-(Q' - A)) = -cross (Q - A) (Q' - A) := by
    simp only [cross_apply, PiLp.neg_apply, PiLp.sub_apply]; ring
  rw [e] at hc
  have : (t + t') * cross (Q - A) (Q' - A) = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h1
  · linarith
  · exact h.det h1

/-- Two flanks of a tile corner are independent. -/
theorem flank_cross_ne {T : Tri} {m : Fin 3} {x U W : Plane} (hm : T.pts m = x)
    (hUW : IsFlankPair T m x U W) : cross U W ≠ 0 := by
  have h := hind_h T m hm
  rcases hUW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · intro h0; apply h; simp only [cross_apply, PiLp.sub_apply] at h0; linarith
  · intro h0; apply h; simp only [cross_apply, PiLp.sub_apply] at h0; linarith

/-- A tile does not cover its own "beyond-the-flank" directions `U − ηW`, `η > 0`. -/
theorem not_cover_own {T : Tri} {m : Fin 3} {x U W : Plane} (hm : T.pts m = x)
    (hUW : IsFlankPair T m x U W) {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    x + ε • (U - η • W) ∉ T.carrier := by
  intro hy
  have hΔ := flank_cross_ne hm hUW
  obtain ⟨s, t, hs, ht, hD⟩ := corner_cone_vec T m hm hε hy
  have hD' : U - η • W = s • U + t • W ∨ U - η • W = t • U + s • W := by
    rcases hUW with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; rw [hD, ← h1, ← h2]
    · right; rw [hD, ← h1, ← h2, add_comm]
  have key : ∀ p q : ℝ, 0 ≤ q → U - η • W = p • U + q • W → False := by
    intro p q hq h
    have hc := congrArg (cross U) h
    simp only [cross_sub_right', cross_add_right, cross_smul_right, cross_self'] at hc
    have : (q + η) * cross U W = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · linarith
    · exact hΔ h1
  rcases hD' with h | h
  · exact key s t ht h
  · exact key t s hs h

/-- In the edge case of the flank neighbour at a point that is a vertex of every tile containing
it, there is nothing: the edge case is impossible. -/
theorem no_edge_case {T : Tri} {x : Plane} (hv : ∃ j, T.pts j = x) {m : Fin 3}
    (hmpos : ∀ l, l ≠ m → 0 < T.basis.coord l x) : False := by
  obtain ⟨j, hj⟩ := hv
  exact vertex_not_edge T j hj m hmpos

/-- **The leg tile — PROVED.**  At a target corner `A` (cone `ApexCone T A Q Q'`), if every tile
containing `A` has `A` as a vertex, some tile has a corner at `A` with a flank along the leg
`Q − A` (a positive multiple). -/
theorem leg_tile {N : ℕ} (D : Dissection N) {A Q Q' : Plane} (hC : ApexCone D.target A Q Q')
    (hvert : ∀ i, A ∈ (D.tile i).carrier → ∃ j, (D.tile i).pts j = A) :
    ∃ i m, (D.tile i).pts m = A ∧ ∃ U' W' : Plane, IsFlankPair (D.tile i) m A U' W' ∧
      ∃ S : ℝ, 0 < S ∧ Q - A = S • U' ∧ cross (Q - A) W' * cross (Q - A) (-(Q' - A)) < 0 := by
  classical
  have hΔ : cross (Q - A) (-(Q' - A)) ≠ 0 := by
    have e : cross (Q - A) (-(Q' - A)) = -cross (Q - A) (Q' - A) := by
      simp only [cross_apply, PiLp.neg_apply, PiLp.sub_apply]; ring
    rw [e]; exact neg_ne_zero.mpr hC.det
  have hdir : ∀ n : ℕ, (Q - A) - (1 / ((n : ℝ) + ((1 : ℕ) : ℝ))) • (-(Q' - A))
      = (1 : ℝ) • (Q - A) + (1 / ((n : ℝ) + 1)) • (Q' - A) := by
    intro n; rw [smul_neg, sub_neg_eq_add, one_smul, Nat.cast_one]
  have hin : ∀ (n : ℕ) (τ : ℝ), 0 < τ → τ ≤ 1 / 4 →
      A + τ • ((1 : ℝ) • (Q - A) + (1 / ((n : ℝ) + 1)) • (Q' - A)) ∈ interior D.target.carrier := by
    intro n τ hτ hτ4
    have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hp1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
    exact hC.inter 1 _ τ one_pos hp hτ (by nlinarith)
  have hN : 0 < N := by
    have h := hin 0 (1 / 4) (by norm_num) le_rfl
    rw [← D.covers] at h
    obtain ⟨i, -⟩ := Set.mem_iUnion.mp (interior_subset h)
    exact Fin.pos i
  have hcovn : ∀ n : ℕ, ∃ (j : Fin N) (ε : ℝ), 0 < ε ∧ A ∈ (D.tile j).carrier ∧
      A + ε • ((Q - A) - (1 / ((n : ℝ) + ((1 : ℕ) : ℝ))) • (-(Q' - A))) ∈ (D.tile j).carrier := by
    intro n
    rw [hdir n]
    have hD0 : (1 : ℝ) • (Q - A) + (1 / ((n : ℝ) + 1)) • (Q' - A) ≠ 0 := by
      intro h0
      have hc := congrArg (cross (Q - A)) h0
      simp only [cross_add_right, cross_smul_right, cross_self'] at hc
      have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have : cross (Q - A) (0 : Plane) = 0 := by simp [cross_apply]
      rw [this] at hc
      rcases mul_eq_zero.mp (by linarith : 1 / ((n : ℝ) + 1) * cross (Q - A) (Q' - A) = 0) with
        h1 | h1
      · linarith
      · exact hC.det h1
    exact cover_tile_dir D.tile A hN hD0 (by norm_num : (0 : ℝ) < 1 / 4) (fun τ hτ hτ4 => by
      rw [D.covers]; exact interior_subset (hin n τ hτ hτ4))
  have hopen : ∀ j : Fin N, (∃ (n : ℕ) (ε : ℝ), 0 < ε ∧
        A + ε • ((Q - A) - (1 / ((n : ℝ) + ((1 : ℕ) : ℝ))) • (-(Q' - A))) ∈ (D.tile j).carrier) →
      ∀ s t τ : ℝ, 0 < s → 0 < t → 0 < τ → τ * (s + t) < 1 →
        A + τ • (s • (Q - A) + t • (-(Q' - A))) ∉ interior (D.tile j).carrier := by
    intro j _ s t τ _ ht hτ _ hz
    exact hC.outside ht hτ (tile_sub_target D j (interior_subset hz))
  obtain ⟨j, hAj, -, hcase⟩ := flank_neighbour_gen D.tile A hΔ 1 le_rfl hcovn hopen
  rcases hcase with ⟨m, hm, U', W', hUW', S, hS, hU, hside⟩ | ⟨m, -, hmpos, -, -⟩
  · exact ⟨j, m, hm, U', W', hUW', S, hS, hU, hside⟩
  · exact (no_edge_case (hvert j hAj) hmpos).elim

/-- **The inner neighbour — PROVED.**  Tile `i` has a corner at the target corner `A` with flanks
`G` (inner, strictly inside the cone) and `F` (along the leg `Q − A`).  Then a different tile `j`
has a corner at `A` with a flank `U'` along `G` (`G = S'·U'`, `S' > 0`) and its other flank `W'`
strictly on the other side of `ℝG` from `F`. -/
theorem inner_neighbour {N : ℕ} (D : Dissection N) {A Q Q' : Plane}
    (hC : ApexCone D.target A Q Q')
    (hvert : ∀ i, A ∈ (D.tile i).carrier → ∃ j, (D.tile i).pts j = A)
    {i : Fin N} {m : Fin 3} (hm : (D.tile i).pts m = A) {G F : Plane}
    (hGF : IsFlankPair (D.tile i) m A G F) {S s t : ℝ} (hS : 0 < S) (hF : Q - A = S • F)
    (hs : 0 < s) (ht : 0 < t) (hG : G = s • (Q - A) + t • (Q' - A)) :
    ∃ j, j ≠ i ∧ ∃ m', (D.tile j).pts m' = A ∧ ∃ U' W' : Plane,
      IsFlankPair (D.tile j) m' A U' W' ∧
      ∃ S' : ℝ, 0 < S' ∧ G = S' • U' ∧ cross G W' * cross G F < 0 := by
  classical
  have hΔ : cross G F ≠ 0 := flank_cross_ne hm hGF
  have hF' : F = S⁻¹ • (Q - A) := by rw [hF, smul_smul, inv_mul_cancel₀ hS.ne', one_smul]
  set K : ℕ := ⌈1 / (s * S)⌉₊ + 1 with hKdef
  have hK : 1 ≤ K := by omega
  have hKgt : 1 / (s * S) < (K : ℝ) := by
    have := Nat.le_ceil (1 / (s * S))
    have e : ((⌈1 / (s * S)⌉₊ + 1 : ℕ) : ℝ) = (⌈1 / (s * S)⌉₊ : ℝ) + 1 := by push_cast; ring
    rw [hKdef, e]; linarith
  -- the approach directions are `(s − η/S)(Q−A) + t(Q'−A)` with `s − η/S > 0`
  have hcoef : ∀ n : ℕ, 0 < s - (1 / ((n : ℝ) + K)) * S⁻¹ := by
    intro n
    have hnK : (0 : ℝ) < (n : ℝ) + K := by
      have : (1 : ℝ) ≤ K := by exact_mod_cast hK
      positivity
    have h1 : 1 / (s * S) < (n : ℝ) + K := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    have hsS : 0 < s * S := mul_pos hs hS
    rw [div_lt_iff₀ hsS] at h1
    have : (1 / ((n : ℝ) + K)) * S⁻¹ < s := by
      rw [one_div, ← mul_inv, inv_lt_comm₀ (by positivity) hs]
      rw [inv_eq_one_div, div_lt_iff₀ hs]; nlinarith
    linarith
  have hdir : ∀ n : ℕ, G - (1 / ((n : ℝ) + K)) • F
      = (s - (1 / ((n : ℝ) + K)) * S⁻¹) • (Q - A) + t • (Q' - A) := by
    intro n; rw [hG, hF', smul_smul, sub_smul]; abel
  have hN : 0 < N := Fin.pos i
  have hcovn : ∀ n : ℕ, ∃ (j : Fin N) (ε : ℝ), 0 < ε ∧ A ∈ (D.tile j).carrier ∧
      A + ε • (G - (1 / ((n : ℝ) + K)) • F) ∈ (D.tile j).carrier := by
    intro n
    rw [hdir n]
    have hc := hcoef n
    have hD0 : (s - (1 / ((n : ℝ) + K)) * S⁻¹) • (Q - A) + t • (Q' - A) ≠ 0 := by
      intro h0
      have hcr := congrArg (cross (Q - A)) h0
      simp only [cross_add_right, cross_smul_right, cross_self'] at hcr
      have : cross (Q - A) (0 : Plane) = 0 := by simp [cross_apply]
      rw [this] at hcr
      rcases mul_eq_zero.mp (by linarith : t * cross (Q - A) (Q' - A) = 0) with h1 | h1
      · linarith
      · exact hC.det h1
    refine cover_tile_dir D.tile A hN hD0 (τ₀ := 1 / (s + t + 1)) (by positivity)
      (fun τ hτ hτ1 => ?_)
    rw [D.covers]
    apply interior_subset
    apply hC.inter _ t τ hc ht hτ
    have hle : τ * (s - (1 / ((n : ℝ) + K)) * S⁻¹ + t) ≤ τ * (s + t) := by
      have : 0 ≤ (1 / ((n : ℝ) + K)) * S⁻¹ := by
        have := invK_pos hK n; positivity
      nlinarith
    have : τ * (s + t) < 1 := by
      rw [le_div_iff₀ (by positivity)] at hτ1; nlinarith
    linarith
  have hopen : ∀ j : Fin N, (∃ (n : ℕ) (ε : ℝ), 0 < ε ∧
        A + ε • (G - (1 / ((n : ℝ) + K)) • F) ∈ (D.tile j).carrier) →
      ∀ s t τ : ℝ, 0 < s → 0 < t → 0 < τ → τ * (s + t) < 1 →
        A + τ • (s • G + t • F) ∉ interior (D.tile j).carrier := by
    intro j ⟨n, ε, hε, hy⟩ s' t' τ hs' ht' hτ hτ1 hz
    by_cases hji : j = i
    · subst hji
      exact not_cover_own hm hGF (invK_pos hK n) hε hy
    · have z1 := open_dir_interior (D.tile i) m hm hGF hs' ht' hτ hτ1
      exact Set.disjoint_left.mp (D.interiors_disjoint (Ne.symm hji)) z1 hz
  obtain ⟨j, hAj, ⟨n, ε, hε, hy⟩, hcase⟩ := flank_neighbour_gen D.tile A hΔ K hK hcovn hopen
  have hji : j ≠ i := by
    rintro rfl; exact not_cover_own hm hGF (invK_pos hK n) hε hy
  rcases hcase with ⟨m', hm', U', W', hUW', S', hS', hU, hside⟩ | ⟨m', -, hmpos, -, -⟩
  · exact ⟨j, hji, m', hm', U', W', hUW', S', hS', hU, hside⟩
  · exact (no_edge_case (hvert j hAj) hmpos).elim


/-! ## §3 Flank bookkeeping -/

theorem flank_swap {T : Tri} {m : Fin 3} {x U W : Plane} (h : IsFlankPair T m x U W) :
    IsFlankPair T m x W U := by
  rcases h with h | h
  · exact Or.inr ⟨h.2, h.1⟩
  · exact Or.inl ⟨h.2, h.1⟩

theorem flank_cases {T : Tri} {m : Fin 3} {x U W U' W' : Plane}
    (h1 : IsFlankPair T m x U W) (h2 : IsFlankPair T m x U' W') :
    (U' = U ∧ W' = W) ∨ (U' = W ∧ W' = U) := by
  rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

theorem range_of_flank {T : Tri} {m : Fin 3} {x U W : Plane} (hm : T.pts m = x)
    (h : IsFlankPair T m x U W) : Set.range T.pts = {x, x + U, x + W} := by
  rw [range_pts_eq T m, hm]
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have e1 : x + (T.pts (m + 1) - x) = T.pts (m + 1) := by abel
    have e2 : x + (T.pts (m + 2) - x) = T.pts (m + 2) := by abel
    rw [e1, e2]; exact Set.insert_comm _ _ _
  · have e1 : x + (T.pts (m + 1) - x) = T.pts (m + 1) := by abel
    have e2 : x + (T.pts (m + 2) - x) = T.pts (m + 2) := by abel
    rw [e1, e2]; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

/-- The local angle of a corner tile is the (unoriented) angle between its flanks. -/
theorem flank_angle {T : Tri} {m : Fin 3} {x U W : Plane} (hm : T.pts m = x)
    (h : IsFlankPair T m x U W) : T.localAngle x = InnerProductGeometry.angle U W := by
  subst hm
  rw [Tri.localAngle_vertex]
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · rw [InnerProductGeometry.angle_comm]; rfl

theorem no_double_alpha {X Y G : Plane} {α : ℝ} (hα : 0 < α)
    (h3 : InnerProductGeometry.angle X Y = 3 * α) (h1 : InnerProductGeometry.angle X G = α)
    (h2 : InnerProductGeometry.angle Y G = α) : False := by
  have := InnerProductGeometry.angle_le_angle_add_angle X G Y
  rw [InnerProductGeometry.angle_comm G Y] at this
  linarith

theorem eq_smul_of_norms {X Y : Plane} {S p q : ℝ} (hS : 0 < S) (hX : X = S • Y)
    (hXn : ‖X‖ = p) (hYn : ‖Y‖ = q) (hp : 0 < p) : Y = (q / p) • X := by
  have hpq : p = S * q := by rw [← hXn, ← hYn, hX, norm_smul, Real.norm_of_nonneg hS.le]
  have hq : q ≠ 0 := by rintro rfl; rw [mul_zero] at hpq; linarith
  rw [hX, smul_smul, hpq, show q / (S * q) * S = 1 by field_simp, one_smul]

/-- **The flank lengths at the apex are `{b, c}`** (`ApexEdgesReal.congruentDissection_apex_edges`,
VERIFIED, restated for a flank pair). -/
theorem flank_norms_bc {N : ℕ} (D : CongruentDissection N) {a b c α β γ : ℝ}
    (hs0 : sideOpp D.model 0 = a) (hs1 : sideOpp D.model 1 = b) (hs2 : sideOpp D.model 2 = c)
    (ha0 : a ≠ 0) (hAng : MarchSlots.AngleData α β γ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
      = 3 * α)
    {i : Fin N} {m : Fin 3} {U W : Plane} (hm : (D.tile i).pts m = D.target.pts k)
    (hUW : IsFlankPair (D.tile i) m (D.target.pts k) U W)
    (hi : (D.tile i).localAngle (D.target.pts k) = α) :
    (‖U‖ = b ∧ ‖W‖ = c) ∨ (‖U‖ = c ∧ ‖W‖ = b) := by
  obtain ⟨hαβ, hαγ, hαπ, hα0, hβγ, -, -, -, -, hα2π, -, -⟩ := angle_facts hAng
  obtain ⟨j, hj, hcase⟩ := Erdos634.ApexEdgesReal.congruentDissection_apex_edges D α β γ hαβ hαγ
    hαπ hα0 hα2π hβγ hAng.hγdef hAng.hrel hα' hβ' hγ' (by rw [hs0]; exact ha0) k hcorner i hi
  have hjm : j = m := (D.tile i).indep.injective (hj.symm.trans hm.symm)
  subst hjm
  have e1 : ‖(D.tile i).pts (j + 1) - D.target.pts k‖
      = dist ((D.tile i).pts j) ((D.tile i).pts (j + 1)) := by
    rw [← dist_eq_norm, dist_comm, hj]
  have e2 : ‖(D.tile i).pts (j + 2) - D.target.pts k‖
      = dist ((D.tile i).pts (j + 2)) ((D.tile i).pts j) := by
    rw [← dist_eq_norm, hj]
  rw [hs1, hs2] at hcase
  rcases hUW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [e1, e2]; tauto
  · rw [e1, e2]; tauto

/-- **The side opposite the apex corner is `a`.** -/
theorem opp_side_a {N : ℕ} (D : CongruentDissection N) {a α β γ : ℝ}
    (hs0 : sideOpp D.model 0 = a) (hAng : MarchSlots.AngleData α β γ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    {i : Fin N} {m : Fin 3} {x U W : Plane} (hm : (D.tile i).pts m = x)
    (hUW : IsFlankPair (D.tile i) m x U W) (hi : (D.tile i).localAngle x = α) :
    dist (x + U) (x + W) = a := by
  obtain ⟨hαβ, hαγ, -, -, -, -, -, -, -, -, -, -⟩ := angle_facts hAng
  obtain ⟨k0, hk0angle, hk0side⟩ :=
    Erdos634.CornerBaseEdgesReal.congruent_opposite_side (D.tiles_congruent i).symm m
  have hcorner_tile : cornerAngle ((D.tile i).pts (m + 1)) ((D.tile i).pts m)
      ((D.tile i).pts (m + 2)) = α := by rw [← Tri.localAngle_vertex, hm]; exact hi
  rw [hcorner_tile] at hk0angle
  have hk0eq : k0 = 0 := by
    fin_cases k0
    · rfl
    · exact absurd (hk0angle.trans hβ') hαβ
    · exact absurd (hk0angle.trans hγ') hαγ
  subst hk0eq
  have hopp : dist ((D.tile i).pts (m + 1)) ((D.tile i).pts (m + 2)) = a := by
    rw [← hk0side, ← hs0]; rfl
  have e1 : x + ((D.tile i).pts (m + 1) - x) = (D.tile i).pts (m + 1) := by abel
  have e2 : x + ((D.tile i).pts (m + 2) - x) = (D.tile i).pts (m + 2) := by abel
  rcases hUW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [e1, e2]; exact hopp
  · rw [e1, e2, dist_comm]; exact hopp

/-! ## §4 The apex configuration (`thm:apexconfig`, `lem:apex` clauses 3–5)

`LegFlanksC D k c` is clause (2) of the task: a tile with a corner at the apex and a flank along a
leg lays a `c` there.  At `m = 1` it is `lem:sidenob` + the γ-trap on the leg word; it is a
HYPOTHESIS of `apex_config` and is discharged separately (§6). -/

/-- Clause (2): every apex-corner flank lying along a leg has length `c`. -/
def LegFlanksC {N : ℕ} (D : CongruentDissection N) (k : Fin 3) (c : ℝ) : Prop :=
  ∀ (i : Fin N) (m : Fin 3) (U W : Plane) (l : Fin 3) (S : ℝ),
    (D.tile i).pts m = D.target.pts k → IsFlankPair (D.tile i) m (D.target.pts k) U W →
    l ≠ k → 0 < S → D.target.pts l - D.target.pts k = S • U → ‖U‖ = c

/-- The apex configuration, as facts about the tiles of `D`.  `L` is the leg of `T₃`, `R` the leg of
`T₁`; `G₃` is the common `b`-ray `ρ₁` of `T₃` and `T₂` (so `P′ = A + G₃`), `G₁` the mismatch ray `r`
(`T₁`'s `b`, `T₂`'s `c`). -/
structure ApexConfig {N : ℕ} (D : CongruentDissection N) (A L R G1 G3 : Plane) (a b c α : ℝ) :
    Prop where
  hT3 : ∃ i, Set.range (D.tile i).pts = {A, A + (c / ‖L - A‖) • (L - A), A + G3}
  hT2 : ∃ i, Set.range (D.tile i).pts = {A, A + G3, A + (c / b) • G1}
  hT1 : ∃ i, Set.range (D.tile i).pts = {A, A + G1, A + (c / ‖R - A‖) • (R - A)}
  hG1 : ‖G1‖ = b
  hG3 : ‖G3‖ = b
  hside : cross G1 G3 * cross G1 (R - A) < 0
  hG1cone : ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ G1 = s • (L - A) + t • (R - A)
  hG3cone : ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ G3 = s • (L - A) + t • (R - A)
  hangR : InnerProductGeometry.angle (R - A) G1 = α
  hangL : InnerProductGeometry.angle (L - A) G3 = α
  hT3a : dist (A + (c / ‖L - A‖) • (L - A)) (A + G3) = a
  hT2a : dist (A + G3) (A + (c / b) • G1) = a
  hT1a : dist (A + G1) (A + (c / ‖R - A‖) • (R - A)) = a

theorem leg_tile_facts {N : ℕ} (D : CongruentDissection N) {A Q Q' : Plane}
    (hC : ApexCone D.target A Q Q') {α : ℝ} (hαpos : 0 < α)
    (h3 : InnerProductGeometry.angle (Q - A) (Q' - A) = 3 * α)
    {j : Fin N} {m : Fin 3} {U W : Plane} {S : ℝ} (hm : (D.tile j).pts m = A)
    (hUW : IsFlankPair (D.tile j) m A U W) (hS : 0 < S) (hU : Q - A = S • U)
    (hside : cross (Q - A) W * cross (Q - A) (-(Q' - A)) < 0)
    (hαj : (D.tile j).localAngle A = α) :
    InnerProductGeometry.angle (Q - A) W = α ∧
      ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ W = s • (Q - A) + t • (Q' - A) := by
  have hang : InnerProductGeometry.angle (Q - A) W = α := by
    rw [hU, InnerProductGeometry.angle_smul_left_of_pos _ _ hS, ← flank_angle hm hUW, hαj]
  refine ⟨hang, ?_⟩
  have hvW : A + W ∈ D.target.carrier := by
    apply tile_sub_target D.toDissection j
    have : A + W = (D.tile j).pts (m + 1) ∨ A + W = (D.tile j).pts (m + 2) := by
      rcases hUW with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · right; abel
      · left; abel
    rcases this with h | h <;> rw [h] <;> exact subset_convexHull ℝ _ (Set.mem_range_self _)
  obtain ⟨s, t, hs, ht, hW⟩ := hC.cone W 1 one_pos (by rw [one_smul]; exact hvW)
  have ht0 : 0 < t := by
    rcases lt_or_eq_of_le ht with h | h
    · exact h
    · exfalso
      rw [← h, zero_smul, add_zero] at hW
      have hz : cross (Q - A) W = 0 := by rw [hW, cross_smul_right, cross_self', mul_zero]
      rw [hz, zero_mul] at hside
      exact lt_irrefl _ hside
  have hs0 : 0 < s := by
    rcases lt_or_eq_of_le hs with h | h
    · exact h
    · exfalso
      rw [← h, zero_smul, zero_add] at hW
      rw [hW, InnerProductGeometry.angle_smul_right_of_pos _ _ ht0, h3] at hang
      linarith
  exact ⟨s, t, hs0, ht0, hW⟩

set_option maxHeartbeats 1000000 in
/-- **`apex_config` — the apex configuration of a real congruent dissection — PROVED, given
clause (2) (`LegFlanksC`).**  At the apex `A` (corner `3α`) there are exactly three tiles
(`apex_three_tiles`); up to naming the two legs `L`, `R`:
`T₃ = {A, J₁, P′}` lays `c` on the leg `L` and `b` along `ρ₁ = G₃`;
`T₂ = {A, P′, V}` lays `b` along `ρ₁` (the SAME point `P′ = A + G₃`) and `c` along the mismatch ray
`r = G₁`;  `T₁ = {A, A + G₁, …}` lays `b` along `r` and `c` on the leg `R`;
`T₂`'s `c` on `r` faces `T₁`'s `b` (the mismatch); `P′` and `R` lie on opposite sides of `r`;
`T₃`'s and `T₂`'s third sides are `a` (`P′J₁` and `P′V`). -/
theorem apex_config {N : ℕ} (D : CongruentDissection N) {a b c α β γ : ℝ}
    (hs0 : sideOpp D.model 0 = a) (hs1 : sideOpp D.model 1 = b) (hs2 : sideOpp D.model 2 = c)
    (ha0 : a ≠ 0) (hb0 : 0 < b) (hc0 : 0 < c) (hbc : b ≠ c)
    (hAng : MarchSlots.AngleData α β γ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
      = 3 * α)
    (hlegc : LegFlanksC D k c) :
    ∃ L R G1 G3 : Plane,
      ((L = D.target.pts (k + 1) ∧ R = D.target.pts (k + 2)) ∨
        (L = D.target.pts (k + 2) ∧ R = D.target.pts (k + 1))) ∧
      ApexConfig D (D.target.pts k) L R G1 G3 a b c α := by
  classical
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hαpos⟩ := angle_facts hAng
  obtain ⟨i₁, i₂, i₃, -, -, -, hmem3, hAt⟩ := apex_three_tiles D hAng hα' hβ' hγ' k hcorner
  have hvert : ∀ i, D.target.pts k ∈ (D.tile i).carrier → ∃ j, (D.tile i).pts j = D.target.pts k :=
    fun i hi => (hAt i hi).2
  have hC : ApexCone D.target (D.target.pts k) (D.target.pts (k + 1)) (D.target.pts (k + 2)) :=
    apexCone_target D.target k
  have hC' := hC.swap
  have h3 : InnerProductGeometry.angle (D.target.pts (k + 1) - D.target.pts k)
      (D.target.pts (k + 2) - D.target.pts k) = 3 * α := hcorner
  have h3' : InnerProductGeometry.angle (D.target.pts (k + 2) - D.target.pts k)
      (D.target.pts (k + 1) - D.target.pts k) = 3 * α := by
    rw [InnerProductGeometry.angle_comm]; exact h3
  set A := D.target.pts k with hAdef
  set P1 := D.target.pts (k + 1) with hP1
  set P2 := D.target.pts (k + 2) with hP2
  have hAmem : ∀ i m, (D.tile i).pts m = A → A ∈ (D.tile i).carrier := fun i m hm => by
    rw [← hm]; exact subset_convexHull ℝ _ (Set.mem_range_self m)
  have hαof : ∀ i m, (D.tile i).pts m = A → (D.tile i).localAngle A = α := fun i m hm =>
    (hAt i (hAmem i m hm)).1
  have hnorms : ∀ i m U W, (D.tile i).pts m = A → IsFlankPair (D.tile i) m A U W →
      (‖U‖ = b ∧ ‖W‖ = c) ∨ (‖U‖ = c ∧ ‖W‖ = b) := fun i m U W hm hUW =>
    flank_norms_bc D hs0 hs1 hs2 ha0 hAng hα' hβ' hγ' k hcorner hm hUW (hαof i m hm)
  have hP1A : 0 < ‖P1 - A‖ := norm_pos_iff.mpr (sub_ne_zero.mpr
    (D.target.indep.injective.ne (NearBaseVertex.succ_ne' k)))
  have hP2A : 0 < ‖P2 - A‖ := norm_pos_iff.mpr (sub_ne_zero.mpr
    (D.target.indep.injective.ne (NearBaseVertex.succ_succ_ne' k)))
  -- the two leg tiles
  obtain ⟨j1, m1, hm1, U1, W1, hUW1, S1, hS1, hU1, hside1⟩ := leg_tile D.toDissection hC hvert
  obtain ⟨j2, m2, hm2, U2, W2, hUW2, S2, hS2, hU2, hside2⟩ := leg_tile D.toDissection hC' hvert
  obtain ⟨hang1, s1, t1, hs1', ht1', hW1⟩ :=
    leg_tile_facts D hC hαpos h3 hm1 hUW1 hS1 hU1 hside1 (hαof j1 m1 hm1)
  obtain ⟨hang2, s2, t2, hs2', ht2', hW2⟩ :=
    leg_tile_facts D hC' hαpos h3' hm2 hUW2 hS2 hU2 hside2 (hαof j2 m2 hm2)
  have hU1n : ‖U1‖ = c := hlegc j1 m1 U1 W1 (k + 1) S1 hm1 hUW1 (NearBaseVertex.succ_ne' k) hS1 hU1
  have hU2n : ‖U2‖ = c :=
    hlegc j2 m2 U2 W2 (k + 2) S2 hm2 hUW2 (NearBaseVertex.succ_succ_ne' k) hS2 hU2
  have hW1n : ‖W1‖ = b := by
    rcases hnorms j1 m1 U1 W1 hm1 hUW1 with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd (h.symm.trans hU1n) hbc
    · exact h
  have hW2n : ‖W2‖ = b := by
    rcases hnorms j2 m2 U2 W2 hm2 hUW2 with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd (h.symm.trans hU2n) hbc
    · exact h
  -- the inner neighbours
  obtain ⟨j, hj1, m', hm', U', W', hUW', S', hS', hU', hsideA⟩ :=
    inner_neighbour D.toDissection hC hvert hm1 (flank_swap hUW1) hS1 hU1 hs1' ht1' hW1
  obtain ⟨j', hj2, m'', hm'', U'', W'', hUW'', S'', hS'', hU'', hsideB⟩ :=
    inner_neighbour D.toDissection hC' hvert hm2 (flank_swap hUW2) hS2 hU2 hs2' ht2' hW2
  -- `j1 ≠ j2`
  have h12 : j1 ≠ j2 := by
    intro heq
    subst heq
    have hmm : m2 = m1 := (D.tile j1).indep.injective (hm2.trans hm1.symm)
    subst hmm
    rcases flank_cases hUW1 hUW2 with ⟨hUe, -⟩ | ⟨hUe, -⟩
    · have hU10 : U1 ≠ 0 := by intro h0; rw [h0, norm_zero] at hU1n; linarith
      have e : InnerProductGeometry.angle (P1 - A) (P2 - A) = 0 := by
        rw [hU1, hU2, hUe, InnerProductGeometry.angle_smul_left_of_pos _ _ hS1,
          InnerProductGeometry.angle_smul_right_of_pos _ _ hS2, InnerProductGeometry.angle_self hU10]
      linarith
    · have e : InnerProductGeometry.angle (P1 - A) (P2 - A) = α := by
        rw [hU2, hUe, InnerProductGeometry.angle_smul_right_of_pos _ _ hS2]; exact hang1
      linarith
  -- `j ≠ j2`, `j' ≠ j1`
  have hjj2 : j ≠ j2 := by
    intro heq
    subst heq
    have hmm : m' = m2 := (D.tile j).indep.injective (hm'.trans hm2.symm)
    subst hmm
    rcases flank_cases hUW2 hUW' with ⟨hUe, -⟩ | ⟨hUe, -⟩
    · have e : InnerProductGeometry.angle (P1 - A) (P2 - A) = α := by
        rw [hU2, InnerProductGeometry.angle_smul_right_of_pos _ _ hS2, ← hUe,
          ← InnerProductGeometry.angle_smul_right_of_pos (P1 - A) U' hS', ← hU']
        exact hang1
      linarith
    · have e : InnerProductGeometry.angle (P2 - A) W1 = α := by
        rw [hU', hUe, InnerProductGeometry.angle_smul_right_of_pos _ _ hS']; exact hang2
      exact no_double_alpha hαpos h3 hang1 e
  have hj'1 : j' ≠ j1 := by
    intro heq
    subst heq
    have hmm : m'' = m1 := (D.tile j').indep.injective (hm''.trans hm1.symm)
    subst hmm
    rcases flank_cases hUW1 hUW'' with ⟨hUe, -⟩ | ⟨hUe, -⟩
    · have e : InnerProductGeometry.angle (P2 - A) (P1 - A) = α := by
        rw [hU1, InnerProductGeometry.angle_smul_right_of_pos _ _ hS1, ← hUe,
          ← InnerProductGeometry.angle_smul_right_of_pos (P2 - A) U'' hS'', ← hU'']
        exact hang2
      linarith
    · have e : InnerProductGeometry.angle (P1 - A) W2 = α := by
        rw [hU'', hUe, InnerProductGeometry.angle_smul_right_of_pos _ _ hS'']; exact hang1
      exact no_double_alpha hαpos h3' hang2 e
  -- `j = j'`: four tiles at `A` among three
  have hjj' : j = j' := by
    by_contra hne
    have hsub : ({j1, j2, j, j'} : Finset (Fin N)) ⊆ {i₁, i₂, i₃} := by
      intro x hx
      have hxA : A ∈ (D.tile x).carrier := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact hAmem _ _ hm1
        · exact hAmem _ _ hm2
        · exact hAmem _ _ hm'
        · exact hAmem _ _ hm''
      have := (hmem3 x).mp hxA
      simp only [Finset.mem_insert, Finset.mem_singleton]; exact this
    have hcard := Finset.card_le_card hsub
    have h4 : ({j1, j2, j, j'} : Finset (Fin N)).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hne]
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hjj2.symm, hj2.symm⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨h12, hj1.symm, hj'1.symm⟩
    have h3c : ({i₁, i₂, i₃} : Finset (Fin N)).card ≤ 3 := Finset.card_le_three
    omega
  subst hjj'
  have hmm : m' = m'' := (D.tile j).indep.injective (hm'.trans hm''.symm)
  subst hmm
  have hflank : U'' = W' ∧ W'' = U' := by
    rcases flank_cases hUW' hUW'' with ⟨hUe, -⟩ | h
    · exfalso
      have e : InnerProductGeometry.angle (P1 - A) W2 = α := by
        rw [hU'', hUe, InnerProductGeometry.angle_smul_right_of_pos _ _ hS'',
          ← InnerProductGeometry.angle_smul_right_of_pos (P1 - A) U' hS', ← hU']
        exact hang1
      exact no_double_alpha hαpos h3' hang2 e
    · exact h
  obtain ⟨hU''e, hW''e⟩ := hflank
  have hopp1 := opp_side_a D hs0 hAng hα' hβ' hγ' hm1 hUW1 (hαof j1 m1 hm1)
  have hopp2 := opp_side_a D hs0 hAng hα' hβ' hγ' hm2 hUW2 (hαof j2 m2 hm2)
  have hoppT := opp_side_a D hs0 hAng hα' hβ' hγ' hm' hUW' (hαof j m' hm')
  have hU1e : U1 = (c / ‖P1 - A‖) • (P1 - A) := eq_smul_of_norms hS1 hU1 rfl hU1n hP1A
  have hU2e : U2 = (c / ‖P2 - A‖) • (P2 - A) := eq_smul_of_norms hS2 hU2 rfl hU2n hP2A
  have hr1 := range_of_flank hm1 hUW1
  have hr2 := range_of_flank hm2 hUW2
  have hrT := range_of_flank hm' hUW'
  rcases hnorms j m' U' W' hm' hUW' with ⟨hU'n, hW'n⟩ | ⟨hU'n, hW'n⟩
  · -- Case A: `T₂`'s `b` along `W1`: `L = P1`
    have hU'W1 : U' = W1 := by
      have := eq_smul_of_norms hS' hU' hW1n hU'n hb0
      rw [this, div_self hb0.ne', one_smul]
    have hW'W2 : W' = (c / b) • W2 := by
      rw [hU''e] at hU''; exact eq_smul_of_norms hS'' hU'' hW2n hW'n hb0
    refine ⟨P1, P2, W2, W1, Or.inl ⟨rfl, rfl⟩, ?_⟩
    exact {
      hT3 := ⟨j1, by rw [hr1, hU1e]⟩
      hT2 := ⟨j, by rw [hrT, hU'W1, hW'W2]⟩
      hT1 := ⟨j2, by rw [hr2, hU2e]; exact congrArg (insert A) (Set.pair_comm _ _)⟩
      hG1 := hW2n
      hG3 := hW1n
      hside := by
        rw [hW''e, hU'W1] at hsideB
        rw [hU2, cross_smul_right]
        have : cross W2 W1 * (S2 * cross W2 U2) = S2 * (cross W2 W1 * cross W2 U2) := by ring
        rw [this]; exact mul_neg_of_pos_of_neg hS2 hsideB
      hG1cone := ⟨t2, s2, ht2', hs2', by rw [hW2, add_comm]⟩
      hG3cone := ⟨s1, t1, hs1', ht1', hW1⟩
      hangR := hang2
      hangL := hang1
      hT3a := by rw [← hU1e]; exact hopp1
      hT2a := by rw [← hU'W1, ← hW'W2]; exact hoppT
      hT1a := by rw [← hU2e, dist_comm]; exact hopp2 }
  · -- Case B: `T₂`'s `b` along `W2`: `L = P2`
    have hW'W2 : W' = W2 := by
      rw [hU''e] at hU''
      have := eq_smul_of_norms hS'' hU'' hW2n hW'n hb0
      rw [this, div_self hb0.ne', one_smul]
    have hU'W1 : U' = (c / b) • W1 := eq_smul_of_norms hS' hU' hW1n hU'n hb0
    refine ⟨P2, P1, W1, W2, Or.inr ⟨rfl, rfl⟩, ?_⟩
    exact {
      hT3 := ⟨j2, by rw [hr2, hU2e]⟩
      hT2 := ⟨j, by rw [hrT, hU'W1, hW'W2]; exact congrArg (insert A) (Set.pair_comm _ _)⟩
      hT1 := ⟨j1, by rw [hr1, hU1e]; exact congrArg (insert A) (Set.pair_comm _ _)⟩
      hG1 := hW1n
      hG3 := hW2n
      hside := by
        rw [hW'W2] at hsideA
        rw [hU1, cross_smul_right]
        have : cross W1 W2 * (S1 * cross W1 U1) = S1 * (cross W1 W2 * cross W1 U1) := by ring
        rw [this]; exact mul_neg_of_pos_of_neg hS1 hsideA
      hG1cone := ⟨t1, s1, ht1', hs1', by rw [hW1, add_comm]⟩
      hG3cone := ⟨s2, t2, hs2', ht2', hW2⟩
      hangR := hang1
      hangL := hang2
      hT3a := by rw [← hU2e]; exact hopp2
      hT2a := by rw [← hW'W2, ← hU'W1, dist_comm]; exact hoppT
      hT1a := by rw [← hU1e, dist_comm]; exact hopp1 }


/-! ## §5 The metric of the rays, and the frame `HFrame` from a real dissection

`coeff_sum`: at the `m = 1` target (legs `f³`, base `e(3f²−e²)`), a vector `G = s(L−A) + t(R−A)`,
`s > 0`, of length `b` whose tip is at distance `a` from `A + (R−A)/f` (i.e. the third side of the tile
`{A, A + G, A + c·û_R}`) has `s + t = 1/f`: the ray `A + ℝ₊G` leaves the target at distance `f·b`.
Pure algebra (`coeff_alg`); the key identity `s²(f¹² − P²) = b²f⁶ − q²` has no linear term. -/

theorem coeff_alg {e f s t P : ℝ} (he : 0 < e) (hef : e < f) (hs : 0 < s)
    (hP : P = f ^ 6 - (e * (3 * f ^ 2 - e ^ 2)) ^ 2 / 2)
    (hG2 : s ^ 2 * f ^ 6 + 2 * s * t * P + t ^ 2 * f ^ 6 = (f ^ 2 - e ^ 2) ^ 2)
    (hq : s * P + t * f ^ 6 = f * ((f ^ 2 - e ^ 2) ^ 2 + (f ^ 2) ^ 2 - (e * f) ^ 2) / 2) :
    s * (3 * f ^ 2 - e ^ 2) = f ∧ s + t = 1 / f := by
  have hf : 0 < f := by linarith
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = f * ((f ^ 2 - e ^ 2) ^ 2 + (f ^ 2) ^ 2 - (e * f) ^ 2) / 2 :=
    ⟨_, rfl⟩
  rw [← hqdef] at hq
  have hkey : s ^ 2 * (f ^ 12 - P ^ 2) = (f ^ 2 - e ^ 2) ^ 2 * f ^ 6 - q ^ 2 := by
    linear_combination f ^ 6 * hG2 - (2 * q + (s * P + t * f ^ 6 - q)) * hq
  have hK1 : f ^ 12 - P ^ 2
      = e ^ 2 * (4 * f ^ 2 - e ^ 2) * (f ^ 2 - e ^ 2) ^ 2 * (3 * f ^ 2 - e ^ 2) ^ 2 / 4 := by
    rw [hP]; ring
  have hK2 : (f ^ 2 - e ^ 2) ^ 2 * f ^ 6 - q ^ 2
      = e ^ 2 * f ^ 2 * (4 * f ^ 2 - e ^ 2) * (f ^ 2 - e ^ 2) ^ 2 / 4 := by
    rw [hqdef]; ring
  rw [hK1, hK2] at hkey
  have h4 : 0 < 4 * f ^ 2 - e ^ 2 := by nlinarith
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith
  have h3 : 0 < 3 * f ^ 2 - e ^ 2 := by nlinarith
  have hpos : 0 < e ^ 2 * (4 * f ^ 2 - e ^ 2) * (f ^ 2 - e ^ 2) ^ 2 / 4 := by positivity
  have hX2 : (s * (3 * f ^ 2 - e ^ 2)) ^ 2 = f ^ 2 := by
    have : (s * (3 * f ^ 2 - e ^ 2)) ^ 2 * (e ^ 2 * (4 * f ^ 2 - e ^ 2) * (f ^ 2 - e ^ 2) ^ 2 / 4)
        = f ^ 2 * (e ^ 2 * (4 * f ^ 2 - e ^ 2) * (f ^ 2 - e ^ 2) ^ 2 / 4) := by
      linear_combination hkey
    exact mul_right_cancel₀ hpos.ne' this
  have hX : s * (3 * f ^ 2 - e ^ 2) = f :=
    (pow_left_inj₀ (mul_pos hs h3).le hf.le two_ne_zero).mp hX2
  have ht6 : t * f ^ 6 = q - s * P := by linarith [hq]
  have hmain : (3 * f ^ 2 - e ^ 2) * f ^ 6 * ((s + t) * f - 1) = 0 := by
    linear_combination (f ^ 7 - f * P) * hX + (3 * f ^ 2 - e ^ 2) * f * ht6 - f ^ 2 * hP
      + (3 * f ^ 2 - e ^ 2) * f * hqdef
  have hne : (3 * f ^ 2 - e ^ 2) * f ^ 6 ≠ 0 := by positivity
  have := (mul_eq_zero.mp hmain).resolve_left hne
  refine ⟨hX, ?_⟩
  rw [eq_div_iff hf.ne']; linarith

theorem coeff_sum {A L R : Plane} {e f s t : ℝ} (he : 0 < e) (hef : e < f) (hs : 0 < s)
    (hL : dist A L = f ^ 3) (hR : dist A R = f ^ 3)
    (hLR : dist L R = e * (3 * f ^ 2 - e ^ 2))
    (hG : dist A (A + (s • (L - A) + t • (R - A))) = f ^ 2 - e ^ 2)
    (hGa : dist (A + (s • (L - A) + t • (R - A))) (A + (1 / f) • (R - A)) = e * f) :
    s * (3 * f ^ 2 - e ^ 2) = f ∧ s + t = 1 / f := by
  have hf : 0 < f := by linarith
  have e1 := dist_sq' A L
  have e2 := dist_sq' A R
  have e3 := dist_sq' L R
  have e4 := dist_sq' A (A + (s • (L - A) + t • (R - A)))
  have e5 := dist_sq' (A + (s • (L - A) + t • (R - A))) (A + (1 / f) • (R - A))
  rw [hL] at e1; rw [hR] at e2; rw [hLR] at e3; rw [hG] at e4; rw [hGa] at e5
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at e4 e5
  apply coeff_alg he hef hs (P := (L 0 - A 0) * (R 0 - A 0) + (L 1 - A 1) * (R 1 - A 1))
  · linear_combination (-1 / 2 : ℝ) * e1 + (-1 / 2 : ℝ) * e2 + (1 / 2 : ℝ) * e3
  · linear_combination s ^ 2 * e1 + t ^ 2 * e2 - e4
  · linear_combination (norm := skip) (f / 2) * e5 - (f / 2) * e4 + (t - 1 / (2 * f)) * e2
    field_simp
    ring

/-- The barycentric coordinate of the apex vertex along the cone. -/
theorem target_coord_k (T : Tri) (k : Fin 3) (x y : ℝ) :
    T.basis.coord k (T.pts k + (x • (T.pts (k + 1) - T.pts k) + y • (T.pts (k + 2) - T.pts k)))
      = 1 - x - y := by
  have h := coord_det T k
    (T.pts k + (x • (T.pts (k + 1) - T.pts k) + y • (T.pts (k + 2) - T.pts k)))
  have hd := T.det_cyclic k
  have hne := T.det_ne_zero
  rw [← hd] at h hne
  apply mul_right_cancel₀ hne
  rw [h]
  simp only [cross_apply, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem coord_LR {T : Tri} {k : Fin 3} {L R : Plane}
    (hLR : (L = T.pts (k + 1) ∧ R = T.pts (k + 2)) ∨ (L = T.pts (k + 2) ∧ R = T.pts (k + 1)))
    (x y : ℝ) :
    T.basis.coord k (T.pts k + (x • (L - T.pts k) + y • (R - T.pts k))) = 1 - x - y := by
  rcases hLR with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact target_coord_k T k x y
  · rw [add_comm (x • _), target_coord_k T k y x]; ring

theorem cone_LR {T : Tri} {k : Fin 3} {L R : Plane}
    (hLR : (L = T.pts (k + 1) ∧ R = T.pts (k + 2)) ∨ (L = T.pts (k + 2) ∧ R = T.pts (k + 1))) :
    ApexCone T (T.pts k) L R := by
  rcases hLR with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact apexCone_target T k
  · exact (apexCone_target T k).swap

/-- The cone coordinates of `P′` and of the mismatch ray in an `HFrame` (legs `v = f³·uL`,
`u = R − A`), with their exact values, the target's apex cone, its exterior, and its base. -/
structure FrameCoords {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ}
    (F : HalfTurnR3R4Glue.HFrame D e f α β γ) : Prop where
  hP : ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ F.P - F.A = s • (((f : ℝ) ^ 3) • F.uL) + t • (F.R - F.A) ∧
    t * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) = f ∧ s + t = 1 / (f : ℝ)
  hV : ∃ s t : ℝ, 0 < s ∧ 0 < t ∧
    ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR = s • (((f : ℝ) ^ 3) • F.uL) + t • (F.R - F.A) ∧
    s * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) = f ∧ s + t = 1 / (f : ℝ)
  hcone : ApexCone D.target F.A (F.A + ((f : ℝ) ^ 3) • F.uL) F.R
  hout : ∀ x y : ℝ, 1 < x + y →
    F.A + (x • (((f : ℝ) ^ 3) • F.uL) + y • (F.R - F.A)) ∉ D.target.carrier
  hbaseLen : dist (F.A + ((f : ℝ) ^ 3) • F.uL) F.R = (e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)

set_option maxHeartbeats 1000000 in
/-- **`exists_hframe` — THE FRAME FROM A REAL DISSECTION — PROVED, given clause (2)
(`LegFlanksC`).**  For a congruent dissection `D` of the `m = 1` base-β target (apex `k` with
corner `3α`, legs `f³`, base `e(3f²−e²)`) by the tile with sides `(ef, f²−e², f²)` (`ModelDataE`,
`AngleData`), at a coprime member `2 ≤ e ≤ f − 2`, the apex frame `HFrame` of branch (H) exists:
every field — the target, the metric of `V`, `P′`, `J₁`, the normal functional `h` of the mismatch
ray `r` with its two sides, `r`'s exit from the target at distance exactly `f·b`, `P′` interior, and
the presence of `T₁`, `T₂`, `T₃` — is DERIVED from `D`. -/
theorem exists_hframe_coords {N : ℕ} (D : CongruentDissection N) {e f : ℕ} {α β γ : ℝ}
    (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e + 2 ≤ f)
    (hM : HalfTurnR3R4Glue.ModelDataE D e f α β γ) (hAng : MarchSlots.AngleData α β γ)
    (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
      = 3 * α)
    (hleg1 : dist (D.target.pts k) (D.target.pts (k + 1)) = (f : ℝ) ^ 3)
    (hleg2 : dist (D.target.pts k) (D.target.pts (k + 2)) = (f : ℝ) ^ 3)
    (hbase : dist (D.target.pts (k + 1)) (D.target.pts (k + 2))
      = (e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))
    (hlegc : LegFlanksC D k ((f : ℝ) ^ 2)) :
    ∃ F : HalfTurnR3R4Glue.HFrame D e f α β γ, FrameCoords F := by
  classical
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast he
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast hef
  have he0 : (0 : ℝ) < e := by linarith
  have hf0 : (0 : ℝ) < f := by linarith
  have hlt : (e : ℝ) < f := by linarith
  set a : ℝ := (e : ℝ) * f with ha
  set b : ℝ := (f : ℝ) ^ 2 - (e : ℝ) ^ 2 with hb
  set c : ℝ := (f : ℝ) ^ 2 with hc
  have ha0 : a ≠ 0 := by rw [ha]; exact mul_ne_zero he0.ne' hf0.ne'
  have hb0 : 0 < b := by rw [hb]; nlinarith
  have hc0 : 0 < c := by positivity
  have hbc : b ≠ c := by rw [hb, hc]; intro h; nlinarith
  obtain ⟨L, R, G1, G3, hLR, cfg⟩ := apex_config D hM.hs0 hM.hs1 hM.hs2 ha0 hb0 hc0 hbc hAng
    hM.hα' hM.hβ' hM.hγ' k hcorner hlegc
  set A := D.target.pts k with hAdef
  have hC : ApexCone D.target A L R := cone_LR hLR
  have hLA : dist A L = (f : ℝ) ^ 3 := by
    rcases hLR with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hleg1
    · exact hleg2
  have hRA : dist A R = (f : ℝ) ^ 3 := by
    rcases hLR with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hleg2
    · exact hleg1
  have hLRd : dist L R = (e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
    rcases hLR with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hbase
    · rw [dist_comm]; exact hbase
  have hLn : ‖L - A‖ = (f : ℝ) ^ 3 := by rw [← dist_eq_norm, dist_comm]; exact hLA
  have hRn : ‖R - A‖ = (f : ℝ) ^ 3 := by rw [← dist_eq_norm, dist_comm]; exact hRA
  have hcf : c / (f : ℝ) ^ 3 = 1 / (f : ℝ) := by rw [hc]; field_simp
  have hdistA : ∀ G : Plane, dist A (A + G) = ‖G‖ := fun G => by
    rw [dist_comm, dist_eq_norm, add_sub_cancel_left]
  -- the two rays leave the target at `1/f` of the cone
  obtain ⟨s1, t1, hs1, ht1, hG1⟩ := cfg.hG1cone
  obtain ⟨s3, t3, hs3, ht3, hG3⟩ := cfg.hG3cone
  have hc1 : s1 * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) = f ∧ s1 + t1 = 1 / (f : ℝ) := by
    apply coeff_sum he0 hlt hs1 hLA hRA hLRd
    · rw [← hG1, hdistA, cfg.hG1]
    · rw [← hG1, ← hcf, ← hRn]; exact cfg.hT1a
  have hc3 : t3 * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) = f ∧ t3 + s3 = 1 / (f : ℝ) := by
    apply coeff_sum he0 hlt ht3 hRA hLA (by rw [dist_comm]; exact hLRd)
    · rw [add_comm (t3 • _), ← hG3, hdistA, cfg.hG3]
    · rw [add_comm (t3 • _), ← hG3, ← hcf, ← hLn, dist_comm]; exact cfg.hT3a
  have hsum1 := hc1.2
  have hsum3 := hc3.2
  have hvL : ((f : ℝ) ^ 3) • ((1 / (f : ℝ) ^ 3) • (L - A)) = L - A := by
    rw [smul_smul, mul_one_div_cancel (by positivity), one_smul]
  -- the normal functional of `r`
  have hside := cfg.hside
  have hcr : cross G1 (R - A) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hside; exact lt_irrefl _ hside
  set h : Plane →ₗ[ℝ] ℝ := (cross G1 (R - A)) • Erdos634.Geometry.crossL G1 with hhdef
  have happ : ∀ v, h v = cross G1 (R - A) * cross G1 v := fun v => by
    rw [hhdef, LinearMap.smul_apply, Erdos634.Geometry.crossL_apply, smul_eq_mul]
  have hG3neg : h G3 < 0 := by rw [happ, mul_comm]; exact hside
  have hRpos : 0 < h (R - A) := by
    rw [happ]; exact mul_self_pos.mpr hcr
  refine ⟨{
    A := A
    V := A + ((f : ℝ) ^ 2) • ((1 / b) • G1)
    P := A + G3
    R := R
    uL := (1 / (f : ℝ) ^ 3) • (L - A)
    uR := (1 / b) • G1
    h := h
    hco := hco
    he := he
    hef := hef
    hM := hM
    hAng := hAng
    htarget := ?_
    hlegR := hRA
    huL := ?_
    huR := ?_
    hV := rfl
    hAP := ?_
    hVP := ?_
    hPJ1 := ?_
    hh0 := ?_
    hhuR := ?_
    hhP := ?_
    hhR := ?_
    hrbase := ?_
    hrint := ?_
    hPint := ?_
    hT1 := ?_
    hT2 := ?_
    hT3 := ?_ }, ?_⟩
  · -- htarget
    have hL' : A + ((f : ℝ) ^ 3) • ((1 / (f : ℝ) ^ 3) • (L - A)) = L := by
      rw [smul_smul, mul_one_div_cancel (by positivity), one_smul]; abel
    rw [hL', range_pts_eq D.target k]
    rcases hLR with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Set.insert_comm _ _ _
    · ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  · rw [norm_smul, hLn, Real.norm_of_nonneg (by positivity), one_div_mul_cancel (by positivity)]
  · rw [norm_smul, cfg.hG1, Real.norm_of_nonneg (by positivity), one_div_mul_cancel hb0.ne']
  · rw [hdistA, cfg.hG3]
  · rw [smul_smul, show (f : ℝ) ^ 2 * (1 / b) = c / b by rw [hc]; ring, dist_comm]
    exact cfg.hT2a
  · rw [smul_smul, show (f : ℝ) ^ 2 * (1 / (f : ℝ) ^ 3) = c / ‖L - A‖ by rw [hLn, hc]; ring,
      dist_comm]
    exact cfg.hT3a
  · intro h0
    have := congrArg (fun φ : Plane →ₗ[ℝ] ℝ => φ G3) h0
    simp only [LinearMap.zero_apply] at this
    rw [this] at hG3neg; exact lt_irrefl _ hG3neg
  · rw [happ, cross_smul_right, cross_self', mul_zero, mul_zero]
  · rw [map_add]; linarith
  · have : h R = h A + h (R - A) := by rw [← map_add]; congr 1; abel
    rw [this]; linarith
  · -- `r` leaves the target at `f·b`
    intro τ hτ hmem
    have hpt : A + ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + τ) • ((1 / b) • G1)
        = A + ((((f : ℝ) * b + τ) / b * s1) • (L - A) + (((f : ℝ) * b + τ) / b * t1) • (R - A)) := by
      rw [hG1, smul_smul, smul_add, smul_smul, smul_smul, ← hb]; congr 2 <;> ring_nf
    rw [hpt] at hmem
    have hco' := ((mem_carrier_iff _ _).mp hmem) k
    rw [coord_LR hLR] at hco'
    have hbne := hb0.ne'
    have hfne := hf0.ne'
    have hx : ((f : ℝ) * b + τ) / b * s1 + ((f : ℝ) * b + τ) / b * t1 = 1 + τ / (b * f) := by
      rw [← mul_add, hsum1]; field_simp
    have : 0 < τ / (b * f) := div_pos hτ (mul_pos hb0 hf0)
    linarith
  · -- and runs inside before that
    intro τ hτ hτ2
    have hpt : A + τ • ((1 / b) • G1) = A + (τ / b) • (s1 • (L - A) + t1 • (R - A)) := by
      rw [hG1, smul_smul]; ring_nf
    rw [hpt]
    apply hC.inter s1 t1 (τ / b) hs1 ht1 (div_pos hτ hb0)
    rw [hsum1, div_mul_div_comm, mul_one, div_lt_one (mul_pos hb0 hf0)]
    rw [← hb] at hτ2
    have : (f : ℝ) * b = b * f := mul_comm _ _
    linarith
  · -- `P′` is interior
    rw [hG3, add_comm (s3 • _)]
    have hC' : ApexCone D.target A R L := hC.swap
    have := hC'.inter t3 s3 1 ht3 hs3 one_pos (by
      rw [one_mul, hsum3, div_lt_one hf0]; linarith)
    rwa [one_smul] at this
  · -- `T₁`
    obtain ⟨i, hi⟩ := cfg.hT1
    refine ⟨i, ?_⟩
    rw [hi, smul_smul, ← hb, mul_one_div_cancel hb0.ne', one_smul, hRn, hcf]
  · -- `T₂`
    obtain ⟨i, hi⟩ := cfg.hT2
    refine ⟨i, ?_⟩
    rw [hi, smul_smul, show (f : ℝ) ^ 2 * (1 / b) = c / b by rw [hc]; ring]
    exact congrArg (insert A) (Set.pair_comm _ _)
  · -- `T₃`
    obtain ⟨i, hi⟩ := cfg.hT3
    refine ⟨i, ?_⟩
    rw [hi, smul_smul, show (f : ℝ) ^ 2 * (1 / (f : ℝ) ^ 3) = c / ‖L - A‖ by rw [hLn, hc]; ring]
    exact congrArg (insert A) (Set.pair_comm _ _)
  · -- the cone coordinates
    have hLpt : A + ((f : ℝ) ^ 3) • ((1 / (f : ℝ) ^ 3) • (L - A)) = L := by rw [hvL]; abel
    refine ⟨⟨s3, t3, hs3, ht3, ?_, hc3.1, by linarith⟩, ⟨s1, t1, hs1, ht1, ?_, hc1.1, hsum1⟩,
      ?_, ?_, ?_⟩
    · show A + G3 - A = s3 • (((f : ℝ) ^ 3) • ((1 / (f : ℝ) ^ 3) • (L - A))) + t3 • (R - A)
      rw [hvL, add_sub_cancel_left]; exact hG3
    · show ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • ((1 / b) • G1)
        = s1 • (((f : ℝ) ^ 3) • ((1 / (f : ℝ) ^ 3) • (L - A))) + t1 • (R - A)
      rw [hvL, smul_smul, ← hb, mul_one_div_cancel hb0.ne', one_smul]; exact hG1
    · show ApexCone D.target A (A + ((f : ℝ) ^ 3) • ((1 / (f : ℝ) ^ 3) • (L - A))) R
      rw [hLpt]; exact hC
    · intro x y hxy hmem
      change A + (x • (((f : ℝ) ^ 3) • ((1 / (f : ℝ) ^ 3) • (L - A))) + y • (R - A))
        ∈ D.target.carrier at hmem
      rw [hvL] at hmem
      have hco' := ((mem_carrier_iff _ _).mp hmem) k
      rw [coord_LR hLR] at hco'
      linarith
    · show dist (A + ((f : ℝ) ^ 3) • ((1 / (f : ℝ) ^ 3) • (L - A))) R = _
      rw [hLpt]; exact hLRd

/-- `exists_hframe_coords`, forgetting the coordinates. -/
theorem exists_hframe {N : ℕ} (D : CongruentDissection N) {e f : ℕ} {α β γ : ℝ}
    (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e + 2 ≤ f)
    (hM : HalfTurnR3R4Glue.ModelDataE D e f α β γ) (hAng : MarchSlots.AngleData α β γ)
    (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
      = 3 * α)
    (hleg1 : dist (D.target.pts k) (D.target.pts (k + 1)) = (f : ℝ) ^ 3)
    (hleg2 : dist (D.target.pts k) (D.target.pts (k + 2)) = (f : ℝ) ^ 3)
    (hbase : dist (D.target.pts (k + 1)) (D.target.pts (k + 2))
      = (e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))
    (hlegc : LegFlanksC D k ((f : ℝ) ^ 2)) :
    Nonempty (HalfTurnR3R4Glue.HFrame D e f α β γ) :=
  let ⟨F, _⟩ := exists_hframe_coords D hco he hef hM hAng k hcorner hleg1 hleg2 hbase hlegc
  ⟨F⟩

end Erdos634.Draft.ApexPlacement

#print axioms Erdos634.Draft.ApexPlacement.cover_tile_dir
#print axioms Erdos634.Draft.ApexPlacement.flank_neighbour_gen
#print axioms Erdos634.Draft.ApexPlacement.apex_three_tiles
#print axioms Erdos634.Draft.ApexPlacement.leg_tile
#print axioms Erdos634.Draft.ApexPlacement.inner_neighbour
#print axioms Erdos634.Draft.ApexPlacement.apex_config
#print axioms Erdos634.Draft.ApexPlacement.coeff_sum
#print axioms Erdos634.Draft.ApexPlacement.exists_hframe_coords
#print axioms Erdos634.Draft.ApexPlacement.exists_hframe
