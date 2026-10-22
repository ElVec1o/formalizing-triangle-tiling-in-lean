-- Draft/CornerAdjacency.lean — the FLANK-NEIGHBOUR lemma at one vertex (corner adjacency).
-- Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
--
-- `NearBaseVertex.localFan_of_tiles` proves that the corner wedges / edge half-planes at a point
-- PARTITION the directions (cover + disjoint open cones).  It does not say WHICH tile lies across a
-- given flank.  This file proves that missing adjacency step, for one point `x` of a finite family of
-- triangles with disjoint interiors covering a ball at `x`:
--
--   `flank_neighbour` — PROVED (no `sorry`).  If tile `i` has a corner at `x` with flanks `U` (the
--   flank in question) and `W`, there is a tile `j ≠ i` containing `x` that lies across `U`:
--   either (vertex case) `x` is a corner of `j`, one flank of `j` is a POSITIVE multiple of `U`, and
--   `j`'s other flank lies strictly on the other side of the line `ℝU` from `W`; or (edge case) `x`
--   is in the relative interior of an edge of `j` lying along the line `ℝU`.
--
-- Proof: the directions `D_n = U − W/(n+1)` are covered (`cover_tile`); one tile `j` covers
-- infinitely many (pigeonhole); `j ≠ i` (they are outside `i`'s wedge); `j`'s closed cone is cut out
-- by linear inequalities, so it contains the limit `U`; `U` is not in `j`'s OPEN cone, since then
-- `U + δW` would be interior to both `i` and `j`.
--
-- Build: scratch olean for Draft/NearBaseVertex, then
--   lake env bash -c 'LEAN_PATH=$S:$LEAN_PATH lean Erdos634/Draft/CornerAdjacency.lean'
import Erdos634.Draft.NearBaseVertex

namespace Erdos634.Draft.CornerAdjacency

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.NearBaseVertex

/-! ## Cross-product algebra -/

theorem cross_self' (u : Plane) : cross u u = 0 := by rw [cross_apply]; ring

theorem cross_anti (u v : Plane) : cross v u = -cross u v := by rw [cross_apply, cross_apply]; ring

theorem cross_add_left' (u v w : Plane) : cross (u + v) w = cross u w + cross v w := by
  simp only [cross_apply, PiLp.add_apply]; ring

theorem cross_smul_left' (a : ℝ) (u w : Plane) : cross (a • u) w = a * cross u w := by
  simp only [cross_apply, PiLp.smul_apply, smul_eq_mul]; ring

theorem cross_sub_right' (u v w : Plane) : cross u (v - w) = cross u v - cross u w := by
  simp only [cross_apply, PiLp.sub_apply]; ring

/-- **Cramer in the plane**: `Δ·D = cross(D, F₂)·F₁ + cross(F₁, D)·F₂`, `Δ = cross(F₁, F₂)`. -/
theorem cramer (F1 F2 D : Plane) :
    cross F1 F2 • D = cross D F2 • F1 + cross F1 D • F2 := by
  ext l; fin_cases l <;> simp only [cross_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;>
    simp <;> ring

/-- A vector with zero cross product against a nonzero `F` is a multiple of it. -/
theorem smul_of_cross_zero {F U : Plane} {Δ : ℝ} (hΔ : Δ ≠ 0) (G : Plane)
    (hFG : cross F G = Δ) (h : cross F U = 0) : U = (cross U G / Δ) • F := by
  have hc := cramer F G U
  rw [hFG, h, zero_smul, add_zero] at hc
  rw [div_eq_inv_mul, mul_smul, ← hc, smul_smul, inv_mul_cancel₀ hΔ, one_smul]

/-- `a − t·b ≥ 0` along `t = 1/(n+1)`, `n` in an infinite set, forces `a ≥ 0`. -/
theorem lim_nonneg {a b : ℝ} {S : Set ℕ} (hS : S.Infinite)
    (h : ∀ n ∈ S, 0 ≤ a - (1 / ((n : ℝ) + 1)) * b) : 0 ≤ a := by
  by_contra ha; push Not at ha
  obtain ⟨n, hnS, hn⟩ := hS.exists_gt ⌈|b| / (-a)⌉₊
  have h1 : |b| / (-a) < (n : ℝ) + 1 := by
    have := Nat.le_ceil (|b| / (-a))
    have : (⌈|b| / (-a)⌉₊ : ℝ) < n := by exact_mod_cast hn
    linarith
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2 : |b| < -a * ((n : ℝ) + 1) := by rw [div_lt_iff₀ (by linarith)] at h1; linarith
  have h3 : (1 / ((n : ℝ) + 1)) * b ≥ -(|b| / ((n : ℝ) + 1)) := by
    rw [one_div_mul_eq_div, ge_iff_le, neg_le, ← neg_div]
    exact div_le_div_of_nonneg_right (by linarith [neg_abs_le b]) hpos.le
  have h4 : |b| / ((n : ℝ) + 1) < -a := by rwa [div_lt_iff₀ hpos]
  have := h n hnS
  linarith

/-! ## Two open cones cannot share a direction -/

/-- A corner tile's flank pair, in either order. -/
def IsFlankPair (T : Tri) (k : Fin 3) (x U W : Plane) : Prop :=
  (U = T.pts (k + 1) - x ∧ W = T.pts (k + 2) - x) ∨ (U = T.pts (k + 2) - x ∧ W = T.pts (k + 1) - x)

theorem open_dir_interior (T : Tri) (k : Fin 3) {x U W : Plane} (hk : T.pts k = x)
    (hUW : IsFlankPair T k x U W) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε * (s + t) < 1) : x + ε • (s • U + t • W) ∈ interior T.carrier := by
  rcases hUW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact corner_interior T k hk hs ht hε hε1
  · have := corner_interior T k hk ht hs hε (by linarith)
    rwa [add_comm (t • _)] at this

/-- **Two corner tiles at `x` with a common open direction coincide.** -/
theorem no_common_open {N : ℕ} (T : Fin N → Tri) {x : Plane}
    (hdisj : Pairwise fun i j => Disjoint (interior (T i).carrier) (interior (T j).carrier))
    {i j : Fin N} (hij : i ≠ j) {k m : Fin 3} {U W U' W' : Plane} (hk : (T i).pts k = x)
    (hm : (T j).pts m = x) (hUW : IsFlankPair (T i) k x U W) (hUW' : IsFlankPair (T j) m x U' W')
    {s t s' t' : ℝ} (hs : 0 < s) (ht : 0 < t) (hs' : 0 < s') (ht' : 0 < t')
    (heq : s • U + t • W = s' • U' + t' • W') : False := by
  set ε := 1 / (2 * (s + t + s' + t') + 1) with hεdef
  have hε : 0 < ε := by positivity
  have hsum : 0 < 2 * (s + t + s' + t') + 1 := by positivity
  have hε1 : ε * (s + t) < 1 := by
    rw [hεdef, one_div_mul_eq_div, div_lt_one hsum]; linarith
  have hε2 : ε * (s' + t') < 1 := by
    rw [hεdef, one_div_mul_eq_div, div_lt_one hsum]; linarith
  have z1 := open_dir_interior (T i) k hk hUW hs ht hε hε1
  have z2 := open_dir_interior (T j) m hm hUW' hs' ht' hε hε2
  rw [heq] at z1
  exact Set.disjoint_left.mp (hdisj hij) z1 z2

/-- **A corner tile and an edge tile at `x` share no open direction.** -/
theorem no_common_open_edge {N : ℕ} (T : Fin N → Tri) {x : Plane}
    (hdisj : Pairwise fun i j => Disjoint (interior (T i).carrier) (interior (T j).carrier))
    {i j : Fin N} (hij : i ≠ j) {k m : Fin 3} {U W : Plane} (hk : (T i).pts k = x)
    (hUW : IsFlankPair (T i) k x U W) (hm0 : (T j).basis.coord m x = 0)
    (hmpos : ∀ l, l ≠ m → 0 < (T j).basis.coord l x) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hc : 0 < sgn (T j) * cross ((T j).pts (m + 2) - (T j).pts (m + 1)) (s • U + t • W)) :
    False := by
  obtain ⟨ρ, hρ, hint⟩ := edge_open_interior (T j) m hm0 hmpos
  obtain ⟨ε, hε, hεB, hεV⟩ := small_eps (s • U + t • W) hρ (B := 1 / (s + t)) (by positivity)
  have hst : 0 < s + t := by linarith
  have z1 := open_dir_interior (T i) k hk hUW hs ht hε (by rw [lt_div_iff₀ hst] at hεB; linarith)
  have z2 := hint _ ε hε hεV hc
  exact Set.disjoint_left.mp (hdisj hij) z1 z2

/-! ## The closed corner cone, in cross-product form -/

theorem corner_cone_vec (T : Tri) (k : Fin 3) {x D : Plane} (hx : T.pts k = x) {ε : ℝ}
    (hε : 0 < ε) (hy : x + ε • D ∈ T.carrier) :
    ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ D = s • (T.pts (k + 1) - x) + t • (T.pts (k + 2) - x) := by
  obtain ⟨s, t, hs, ht, h0, h1⟩ := corner_cone T k hx hε hy
  refine ⟨s, t, hs, ht, ?_⟩
  ext l; fin_cases l
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; simpa using h0
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; simpa using h1

theorem cone_cross {F1 F2 D : Plane} {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hD : D = s • F1 + t • F2) :
    0 ≤ cross F1 D * cross F1 F2 ∧ 0 ≤ cross D F2 * cross F1 F2 := by
  subst hD
  have e1 : cross F1 (s • F1 + t • F2) * cross F1 F2 = t * cross F1 F2 ^ 2 := by
    rw [cross_add_right, cross_smul_right, cross_smul_right, cross_self']; ring
  have e2 : cross (s • F1 + t • F2) F2 * cross F1 F2 = s * cross F1 F2 ^ 2 := by
    rw [cross_add_left', cross_smul_left', cross_smul_left', cross_self']; ring
  rw [e1, e2]; exact ⟨by positivity, by positivity⟩

/-! ## The flank-neighbour lemma -/

set_option maxHeartbeats 1000000 in
/-- **The flank neighbour (corner adjacency at one point) — PROVED.**  `T` a finite family of
triangles with pairwise disjoint interiors covering a ball at `x`; tile `i` has a corner at `x` with
flanks `U`, `W` (`IsFlankPair`, either order).  Then some tile `j ≠ i` containing `x` lies across
`U`: either `x` is a corner of `j` with one flank `U'` a positive multiple of... (precisely: `U` is a
positive multiple of one flank `U'` of `j`) and `j`'s other flank `W'` strictly on the other side of
`ℝU` from `W` (`cross(U,W')·cross(U,W) < 0`); or `x` lies in the relative interior of an edge of `j`
parallel to `U`, with `j` on the other side of `ℝU` from `W`. -/
theorem flank_neighbour {N : ℕ} (T : Fin N → Tri) (x : Plane) {r : ℝ} (hr : 0 < r)
    (hcov : Metric.ball x r ⊆ ⋃ i, (T i).carrier)
    (hdisj : Pairwise fun i j => Disjoint (interior (T i).carrier) (interior (T j).carrier))
    {i : Fin N} {k : Fin 3} (hk : (T i).pts k = x) {U W : Plane}
    (hUW : IsFlankPair (T i) k x U W) :
    ∃ j, j ≠ i ∧ x ∈ (T j).carrier ∧
      ((∃ m : Fin 3, (T j).pts m = x ∧ ∃ U' W' : Plane, IsFlankPair (T j) m x U' W' ∧
          ∃ S : ℝ, 0 < S ∧ U = S • U' ∧ cross U W' * cross U W < 0) ∨
       (∃ m : Fin 3, (T j).basis.coord m x = 0 ∧ (∀ l, l ≠ m → 0 < (T j).basis.coord l x) ∧
          cross ((T j).pts (m + 2) - (T j).pts (m + 1)) U = 0 ∧
          sgn (T j) * cross ((T j).pts (m + 2) - (T j).pts (m + 1)) W < 0)) := by
  classical
  have hn : 0 < N := Fin.pos i
  -- the two flanks of `i` are independent
  have hΔi : cross U W ≠ 0 := by
    have h := hind_h (T i) k hk
    rcases hUW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · intro h0; apply h; simp only [cross_apply, PiLp.sub_apply] at h0; linarith
    · intro h0; apply h; simp only [cross_apply, PiLp.sub_apply] at h0; linarith
  have hU0 : U ≠ 0 := by rintro rfl; apply hΔi; simp [cross_apply]
  -- the approach directions
  set Dn : ℕ → Plane := fun n => U - (1 / ((n : ℝ) + 1)) • W with hDn
  have hDn0 : ∀ n, Dn n ≠ 0 := by
    intro n h
    apply hΔi
    have : cross (Dn n) W = cross U W := by
      simp only [hDn, cross_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [← this, h]; simp [cross_apply]
  have hcovn : ∀ n, ∃ j : Fin N, ∃ ε : ℝ, 0 < ε ∧ x ∈ (T j).carrier ∧ x + ε • Dn n ∈ (T j).carrier :=
    fun n => cover_tile T x hr hcov hn (hDn0 n)
  choose J ε hε hxJ hyJ using hcovn
  obtain ⟨j, hjinf0⟩ := Finite.exists_infinite_fiber J
  set S := J ⁻¹' {j} with hSdef
  have hjinf : S.Infinite := Set.infinite_coe_iff.mp hjinf0
  have hS : ∀ n ∈ S, J n = j := fun n hn => hn
  obtain ⟨n0, hn0⟩ := hjinf.nonempty
  have hxj : x ∈ (T j).carrier := by rw [← hS n0 hn0]; exact hxJ n0
  -- no approach direction is in `i`'s closed wedge, so `j ≠ i`
  have hji : j ≠ i := by
    rintro rfl
    have hy := hyJ n0; rw [hS n0 hn0] at hy
    obtain ⟨s, t, hs, ht, hD⟩ := corner_cone_vec (T j) k hk (hε n0) hy
    have hD' : Dn n0 = s • U + t • W ∨ Dn n0 = t • U + s • W := by
      rcases hUW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl hD
      · exact Or.inr (by rw [hD, add_comm])
    have hc : cross U (Dn n0) = -(1 / ((n0 : ℝ) + 1)) * cross U W := by
      simp only [hDn, cross_sub_right', cross_smul_right, cross_self']; ring
    have hpos : (0 : ℝ) < 1 / ((n0 : ℝ) + 1) := by positivity
    rcases hD' with h | h
    · rw [h, cross_add_right, cross_smul_right, cross_smul_right, cross_self'] at hc
      have : (t + 1 / ((n0 : ℝ) + 1)) * cross U W = 0 := by linarith
      rcases mul_eq_zero.mp this with h1 | h1
      · linarith
      · exact hΔi h1
    · rw [h, cross_add_right, cross_smul_right, cross_smul_right, cross_self'] at hc
      have : (s + 1 / ((n0 : ℝ) + 1)) * cross U W = 0 := by linarith
      rcases mul_eq_zero.mp this with h1 | h1
      · linarith
      · exact hΔi h1
  refine ⟨j, hji, hxj, ?_⟩
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
    -- the approach directions lie in `j`'s closed wedge; pass to the limit
    have hA : ∀ n ∈ S, 0 ≤ cross F1 (Dn n) * cross F1 F2 ∧ 0 ≤ cross (Dn n) F2 * cross F1 F2 := by
      intro n hnS
      have hy := hyJ n; rw [hS n hnS] at hy
      obtain ⟨s, t, hs, ht, hD⟩ := corner_cone_vec (T j) m hm (hε n) hy
      exact cone_cross hs ht hD
    have hL1 : 0 ≤ cross F1 U * cross F1 F2 := by
      apply lim_nonneg (b := cross F1 W * cross F1 F2) hjinf
      intro n hnS
      have := (hA n hnS).1
      simp only [hDn, cross_sub_right', cross_smul_right] at this
      linarith
    have hL2 : 0 ≤ cross U F2 * cross F1 F2 := by
      apply lim_nonneg (b := cross W F2 * cross F1 F2) hjinf
      intro n hnS
      have := (hA n hnS).2
      simp only [hDn] at this
      rw [sub_eq_add_neg, cross_add_left', ← neg_smul, cross_smul_left'] at this
      linarith
    -- `U` is not in `j`'s OPEN wedge
    have hnot : ¬ (0 < cross F1 U * cross F1 F2 ∧ 0 < cross U F2 * cross F1 F2) := by
      rintro ⟨h1, h2⟩
      -- `U + δW` is in both open wedges for small `δ`
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
      exact no_common_open T hdisj hji.symm hk hm hUW (Or.inl ⟨rfl, rfl⟩) one_pos hδ0 hs'' ht''
        heq
    -- so `U` lies on a flank of `j`
    have hF1pos : ∀ {a : ℝ}, 0 < a * cross F1 F2 ^ 2 → 0 < a := fun h =>
      pos_of_mul_pos_left h (by positivity)
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
      -- `W` and `F2` on opposite sides of `ℝU`
      have hW : cross F1 W * cross F1 F2 ≤ 0 := by
        have key : ∀ n ∈ S, 0 ≤ -(1 / ((n : ℝ) + 1)) * (cross F1 W * cross F1 F2) := by
          intro n hnS
          have := (hA n hnS).1
          simp only [hDn, cross_sub_right', cross_smul_right, h0] at this
          linarith
        by_contra hc; push Not at hc
        obtain ⟨n, hnS⟩ := hjinf.nonempty
        have := key n hnS
        have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
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
        have key : ∀ n ∈ S, 0 ≤ -(1 / ((n : ℝ) + 1)) * (cross W F2 * cross F1 F2) := by
          intro n hnS
          have := (hA n hnS).2
          simp only [hDn] at this
          rw [sub_eq_add_neg, cross_add_left', ← neg_smul, cross_smul_left', h0] at this
          linarith
        by_contra hc; push Not at hc
        obtain ⟨n, hnS⟩ := hjinf.nonempty
        have := key n hnS
        have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
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
      have hz1 := open_dir_interior (T i) k hk hUW one_pos one_pos hτ (by linarith)
      have hz2 : x + τ • ((1 : ℝ) • U + (1 : ℝ) • W) ∈ interior (T j).carrier := by
        apply interior_maximal hsub Metric.isOpen_ball
        rw [Metric.mem_ball, dist_add_smul _ _ hτ.le]; exact hτV
      exact Set.disjoint_left.mp (hdisj hji.symm) hz1 hz2
    · refine ⟨m, hm0, hmpos, ?_⟩
      set E := (T j).pts (m + 2) - (T j).pts (m + 1) with hE
      have hA : ∀ n ∈ S, 0 ≤ sgn (T j) * cross E (Dn n) := by
        intro n hnS
        have hy := hyJ n; rw [hS n hnS] at hy
        exact edge_cone_dir (T j) m hm0 (hε n) hy
      have hL : 0 ≤ sgn (T j) * cross E U := by
        apply lim_nonneg (b := sgn (T j) * cross E W) hjinf
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
        apply no_common_open_edge T hdisj hji.symm hk hUW hm0 hmpos one_pos hδ0
        have : sgn (T j) * cross E ((1 : ℝ) • U + δ • W) = p + δ * p' := by
          simp only [cross_add_right, cross_smul_right, p, p']; ring
        rw [this]; nlinarith [neg_abs_le p']
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
        have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        nlinarith
      have hEne : E ≠ 0 := by
        intro h
        have := el_pos (T j) m
        rw [dist_eq_norm, ← hE, h, norm_zero] at this
        exact lt_irrefl _ this
      have hEW : cross E W ≠ 0 := by
        intro h'
        -- `U`, `W` both parallel to `E ≠ 0`, so `cross U W = 0`
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

/-- **`flank_neighbour` for a dissection**, at a point interior to the target. -/
theorem flank_neighbour_dissection {N : ℕ} (D : Dissection N) {x : Plane}
    (hx : x ∈ interior D.target.carrier) {i : Fin N} {k : Fin 3} (hk : (D.tile i).pts k = x)
    {U W : Plane} (hUW : IsFlankPair (D.tile i) k x U W) :
    ∃ j, j ≠ i ∧ x ∈ (D.tile j).carrier ∧
      ((∃ m : Fin 3, (D.tile j).pts m = x ∧ ∃ U' W' : Plane, IsFlankPair (D.tile j) m x U' W' ∧
          ∃ S : ℝ, 0 < S ∧ U = S • U' ∧ cross U W' * cross U W < 0) ∨
       (∃ m : Fin 3, (D.tile j).basis.coord m x = 0 ∧
          (∀ l, l ≠ m → 0 < (D.tile j).basis.coord l x) ∧
          cross ((D.tile j).pts (m + 2) - (D.tile j).pts (m + 1)) U = 0 ∧
          sgn (D.tile j) * cross ((D.tile j).pts (m + 2) - (D.tile j).pts (m + 1)) W < 0)) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  have hcov : Metric.ball x r ⊆ ⋃ i, (D.tile i).carrier := by rw [D.covers]; exact hball
  exact flank_neighbour D.tile x hr hcov D.interiors_disjoint hk hUW

end Erdos634.Draft.CornerAdjacency

#print axioms Erdos634.Draft.CornerAdjacency.cramer
#print axioms Erdos634.Draft.CornerAdjacency.lim_nonneg
#print axioms Erdos634.Draft.CornerAdjacency.no_common_open
#print axioms Erdos634.Draft.CornerAdjacency.no_common_open_edge
#print axioms Erdos634.Draft.CornerAdjacency.flank_neighbour
#print axioms Erdos634.Draft.CornerAdjacency.flank_neighbour_dissection
