-- Draft/NearBaseBridge.lean — the BRIDGE from a real `CongruentDissection` to NB (R5).
-- `NearBaseVertex.nb_tiles` / `localFan_of_tiles` take a finite triangle family with explicit metric
-- hypotheses (sides in `[ℓ, L]`, corner cosines `≥ −c₀`, altitudes `≥ H`, vertices at height `≥ 0`, a
-- covered ball).  This file DERIVES all of them for the tiles of a `CongruentDissection` whose model
-- has sides `(ef, f²−e², f²)` (`ModelDataE`'s `hs0`–`hs2`), placed by an isometry `g` so that the
-- target lies in the closed upper half-plane, at any tile vertex interior to the target.
-- Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- CONTENTS (all PROVED, no `sorry`):
--   * `Perm3`, `model_triple`, `tile_triple` — a tile congruent to the model presents, at each corner
--     `j`, a permutation of `(a,b,c)` as (flank, flank, opposite side).
--   * `perm3_cos`, `perm3_heron`, `tile_metrics` — the four metric hypotheses of `localFan_of_tiles`
--     at `ℓ = min(a,b)`, `L = c`, `c₀ = e/(2f)` (`= −cos γ`, EQUALITY at the `γ` corner), any
--     `0 ≤ H` with `4H²f⁴ ≤ b²e²(4f²−e²)` (the least altitude, `H = b sin α`, attains it).
--   * `localFan_of_dissection` — THE BRIDGE: a `LocalFan` at `g x` for every tile vertex `x` interior
--     to the target.
--   * `nb_dissection` — NB for an actual dissection; `nb_baseBeta` — the same for a target merely
--     CONGRUENT to the m = 1 base-β target `BaseBetaTargetCoord.baseBetaTarget e f` (height = second
--     coordinate after the congruence, i.e. the distance to the base line).
--   * `family_point_killed_dissection` — R5's family kill `(f+1) ∣ e²` for an actual dissection
--     (`NearBaseKill.family_point_killed` ∘ the bridge).
--   * `witness63` — VACUITY RULE: every hypothesis of `localFan_of_dissection` holds jointly for a
--     REAL dissection, `CevianTiling63Bridge.dissection` (63 copies of the `(2,3,4)` tile = the
--     `(ef, f²−e², f²)` tile at `e = 2√2, f = 4√2` after scaling by 8), at its interior vertex
--     `(14, 2√15)`, with `H = 3√15` (the tile's exact least altitude).
--
-- Build (Draft-to-Draft imports; scratch oleans, never .lake):
--   lake env lean -o $S/Erdos634/Draft/NearBaseVertex.olean Erdos634/Draft/NearBaseVertex.lean
--   lake env lean -o $S/Erdos634/Draft/NearBase.olean Erdos634/Draft/NearBase.lean
--   lake env bash -c 'LEAN_PATH=$S:$LEAN_PATH lean -o $S/Erdos634/Draft/NearBaseKill.olean Erdos634/Draft/NearBaseKill.lean'
--   lake env bash -c 'LEAN_PATH=$S:$LEAN_PATH lean Erdos634/Draft/NearBaseBridge.lean'
import Erdos634.Draft.NearBaseVertex
import Erdos634.Draft.NearBaseKill
import Erdos634.NormalPosition
import Erdos634.TilePlacement
import Erdos634.CevianTiling63Bridge
import Erdos634.ChordChartPlanar

namespace Erdos634.Draft.NearBaseBridge

open Real Erdos634.Geometry Erdos634.CertCoord Erdos634.DissectionMap Erdos634.Ladder
open Erdos634.TilePlacement Erdos634.Draft.NearBaseVertex

/-! ## §1 The side triple at a corner of a tile congruent to the model -/

/-- `(x, y, z)` is a permutation of `(a, b, c)` (`x, y` the flanks at a corner, `z` opposite). -/
def Perm3 (x y z a b c : ℝ) : Prop :=
  (x = a ∧ y = b ∧ z = c) ∨ (x = b ∧ y = a ∧ z = c) ∨ (x = a ∧ y = c ∧ z = b) ∨
  (x = c ∧ y = a ∧ z = b) ∨ (x = b ∧ y = c ∧ z = a) ∨ (x = c ∧ y = b ∧ z = a)

theorem model_dist_mem (M : Tri) {a b c : ℝ} (h0 : sideOpp M 0 = a) (h1 : sideOpp M 1 = b)
    (h2 : sideOpp M 2 = c) (p q : Fin 3) (hpq : p ≠ q) :
    dist (M.pts p) (M.pts q) = a ∨ dist (M.pts p) (M.pts q) = b ∨
      dist (M.pts p) (M.pts q) = c := by
  have e12 : dist (M.pts 1) (M.pts 2) = a := h0
  have e20 : dist (M.pts 2) (M.pts 0) = b := h1
  have e01 : dist (M.pts 0) (M.pts 1) = c := h2
  have e21 : dist (M.pts 2) (M.pts 1) = a := by rw [dist_comm]; exact e12
  have e02 : dist (M.pts 0) (M.pts 2) = b := by rw [dist_comm]; exact e20
  have e10 : dist (M.pts 1) (M.pts 0) = c := by rw [dist_comm]; exact e01
  fin_cases p <;> fin_cases q <;> simp_all

theorem model_triple (M : Tri) {a b c : ℝ} (h0 : sideOpp M 0 = a) (h1 : sideOpp M 1 = b)
    (h2 : sideOpp M 2 = c) (p q r : Fin 3) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    Perm3 (dist (M.pts q) (M.pts p)) (dist (M.pts r) (M.pts p)) (dist (M.pts q) (M.pts r))
      a b c := by
  have e12 : dist (M.pts 1) (M.pts 2) = a := h0
  have e20 : dist (M.pts 2) (M.pts 0) = b := h1
  have e01 : dist (M.pts 0) (M.pts 1) = c := h2
  have e21 : dist (M.pts 2) (M.pts 1) = a := by rw [dist_comm]; exact e12
  have e02 : dist (M.pts 0) (M.pts 2) = b := by rw [dist_comm]; exact e20
  have e10 : dist (M.pts 1) (M.pts 0) = c := by rw [dist_comm]; exact e01
  unfold Perm3
  fin_cases p <;> fin_cases q <;> fin_cases r <;> simp_all

theorem fin3_succ_ne_succ_succ (j : Fin 3) : j + 1 ≠ j + 2 := by fin_cases j <;> decide

/-- **The corner triple of a congruent tile.**  At every corner `j` of a tile congruent to a model
with sides `sideOpp = (a, b, c)`, (flank to `j+1`, flank to `j+2`, opposite side) is a permutation of
`(a, b, c)`. -/
theorem tile_triple {T M : Tri} (hT : T.Congruent M) {a b c : ℝ} (h0 : sideOpp M 0 = a)
    (h1 : sideOpp M 1 = b) (h2 : sideOpp M 2 = c) (j : Fin 3) :
    Perm3 (dist (T.pts (j + 1)) (T.pts j)) (dist (T.pts (j + 2)) (T.pts j))
      (dist (T.pts (j + 1)) (T.pts (j + 2))) a b c := by
  obtain ⟨σ, hσ⟩ := hT.dist_eq
  rw [hσ, hσ, hσ]
  exact model_triple M h0 h1 h2 _ _ _ (σ.injective.ne (succ_ne' j).symm)
    (σ.injective.ne (succ_succ_ne' j).symm) (σ.injective.ne (fin3_succ_ne_succ_succ j))

theorem tile_dist_mem {T M : Tri} (hT : T.Congruent M) {a b c : ℝ} (h0 : sideOpp M 0 = a)
    (h1 : sideOpp M 1 = b) (h2 : sideOpp M 2 = c) (j k : Fin 3) (hjk : j ≠ k) :
    dist (T.pts j) (T.pts k) = a ∨ dist (T.pts j) (T.pts k) = b ∨
      dist (T.pts j) (T.pts k) = c := by
  obtain ⟨σ, hσ⟩ := hT.dist_eq
  rw [hσ]
  exact model_dist_mem M h0 h1 h2 _ _ (σ.injective.ne hjk)

/-! ## §2 The base-β tile `(ef, f²−e², f²)`: the metric data at a corner -/

/-- **The cosine bound**, `c₀ = e/(2f) = −cos γ`: equality at the `γ` corner (`z = c`), and the
`α`, `β` corners are acute (`c` is the longest side). -/
theorem perm3_cos {e f x y z : ℝ} (he : 0 < e) (hef : e < f)
    (hP : Perm3 x y z (e * f) (f ^ 2 - e ^ 2) (f ^ 2)) :
    -(e / (2 * f)) * x * y ≤ (x ^ 2 + y ^ 2 - z ^ 2) / 2 := by
  have hf : 0 < f := lt_trans he hef
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith
  have hc0 : 0 ≤ e / (2 * f) := by positivity
  have hkey : -(e / (2 * f)) * (e * f) * (f ^ 2 - e ^ 2)
      = ((e * f) ^ 2 + (f ^ 2 - e ^ 2) ^ 2 - (f ^ 2) ^ 2) / 2 := by
    field_simp; ring
  have hkey' : -(e / (2 * f)) * (f ^ 2 - e ^ 2) * (e * f)
      = ((f ^ 2 - e ^ 2) ^ 2 + (e * f) ^ 2 - (f ^ 2) ^ 2) / 2 := by
    field_simp; ring
  have hab : e * f ≤ f ^ 2 := by nlinarith
  have hbc : f ^ 2 - e ^ 2 ≤ f ^ 2 := by nlinarith
  rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact hkey.le
  · exact hkey'.le
  · have : 0 ≤ -(-(e / (2 * f)) * (e * f) * f ^ 2) := by
      have := mul_nonneg (mul_nonneg hc0 (by positivity : (0:ℝ) ≤ e * f)) (sq_nonneg f)
      linarith
    nlinarith [pow_le_pow_left₀ hb.le hbc 2]
  · have : 0 ≤ -(-(e / (2 * f)) * f ^ 2 * (e * f)) := by
      have := mul_nonneg (mul_nonneg hc0 (sq_nonneg f)) (by positivity : (0:ℝ) ≤ e * f)
      linarith
    nlinarith [pow_le_pow_left₀ hb.le hbc 2]
  · have : 0 ≤ -(-(e / (2 * f)) * (f ^ 2 - e ^ 2) * f ^ 2) := by
      have := mul_nonneg (mul_nonneg hc0 hb.le) (sq_nonneg f)
      linarith
    nlinarith [pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ e * f) hab 2]
  · have : 0 ≤ -(-(e / (2 * f)) * f ^ 2 * (f ^ 2 - e ^ 2)) := by
      have := mul_nonneg (mul_nonneg hc0 (sq_nonneg f)) hb.le
      linarith
    nlinarith [pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ e * f) hab 2]

/-- **Heron, at every corner**: `x²y² − ((x²+y²−z²)/2)² = b²e²(4f²−e²)/4` (`= (2·Area)²`). -/
theorem perm3_heron {e f x y z : ℝ} (hP : Perm3 x y z (e * f) (f ^ 2 - e ^ 2) (f ^ 2)) :
    x ^ 2 * y ^ 2 - ((x ^ 2 + y ^ 2 - z ^ 2) / 2) ^ 2
      = (f ^ 2 - e ^ 2) ^ 2 * e ^ 2 * (4 * f ^ 2 - e ^ 2) / 4 := by
  rcases hP with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> ring

theorem perm3_le_c {e f x y z : ℝ} (he : 0 < e) (hef : e < f)
    (hP : Perm3 x y z (e * f) (f ^ 2 - e ^ 2) (f ^ 2)) : z ≤ f ^ 2 := by
  have hf : 0 < f := lt_trans he hef
  rcases hP with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
  all_goals nlinarith

/-- **The four metric hypotheses of `localFan_of_tiles`, for one tile congruent to the base-β model
tile `(ef, f²−e², f²)`.** -/
theorem tile_metrics {T M : Tri} (hT : T.Congruent M) {e f H : ℝ} (he : 0 < e) (hef : e < f)
    (h0 : sideOpp M 0 = e * f) (h1 : sideOpp M 1 = f ^ 2 - e ^ 2) (h2 : sideOpp M 2 = f ^ 2)
    (hH0 : 0 ≤ H) (hH : 4 * H ^ 2 * f ^ 4 ≤ (f ^ 2 - e ^ 2) ^ 2 * e ^ 2 * (4 * f ^ 2 - e ^ 2)) :
    (∀ j k, j ≠ k → min (e * f) (f ^ 2 - e ^ 2) ≤ dist (T.pts j) (T.pts k)) ∧
    (∀ j k, dist (T.pts j) (T.pts k) ≤ f ^ 2) ∧
    (∀ j : Fin 3, -(e / (2 * f)) * dist (T.pts (j + 1)) (T.pts j) * dist (T.pts (j + 2)) (T.pts j)
      ≤ (T.pts (j + 1) 0 - T.pts j 0) * (T.pts (j + 2) 0 - T.pts j 0)
        + (T.pts (j + 1) 1 - T.pts j 1) * (T.pts (j + 2) 1 - T.pts j 1)) ∧
    (∀ j : Fin 3, H * dist (T.pts (j + 1)) (T.pts (j + 2))
      ≤ |cross (T.pts (j + 1) - T.pts j) (T.pts (j + 2) - T.pts j)|) := by
  have hf : 0 < f := lt_trans he hef
  have hab : e * f ≤ f ^ 2 := by nlinarith
  have hbc : f ^ 2 - e ^ 2 ≤ f ^ 2 := by nlinarith
  refine ⟨fun j k hjk => ?_, fun j k => ?_, fun j => ?_, fun j => ?_⟩
  · rcases tile_dist_mem hT h0 h1 h2 j k hjk with h | h | h <;> rw [h]
    · exact min_le_left _ _
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans hab
  · by_cases hjk : j = k
    · rw [hjk, dist_self]; positivity
    · rcases tile_dist_mem hT h0 h1 h2 j k hjk with h | h | h <;> rw [h]
      · exact hab
      · exact hbc
  · have hP := tile_triple hT h0 h1 h2 j
    have hc := perm3_cos he hef hP
    have dx := dist_sq' (T.pts (j + 1)) (T.pts j)
    have dy := dist_sq' (T.pts (j + 2)) (T.pts j)
    have dz := dist_sq' (T.pts (j + 1)) (T.pts (j + 2))
    have : (dist (T.pts (j + 1)) (T.pts j) ^ 2 + dist (T.pts (j + 2)) (T.pts j) ^ 2
        - dist (T.pts (j + 1)) (T.pts (j + 2)) ^ 2) / 2
        = (T.pts (j + 1) 0 - T.pts j 0) * (T.pts (j + 2) 0 - T.pts j 0)
          + (T.pts (j + 1) 1 - T.pts j 1) * (T.pts (j + 2) 1 - T.pts j 1) := by
      rw [dx, dy, dz]; ring
    linarith
  · have hP := tile_triple hT h0 h1 h2 j
    have hz := perm3_le_c he hef hP
    have hHe := perm3_heron hP
    have dx := dist_sq' (T.pts (j + 1)) (T.pts j)
    have dy := dist_sq' (T.pts (j + 2)) (T.pts j)
    have dz := dist_sq' (T.pts (j + 1)) (T.pts (j + 2))
    set C := cross (T.pts (j + 1) - T.pts j) (T.pts (j + 2) - T.pts j) with hCdef
    have hC : C ^ 2 = (f ^ 2 - e ^ 2) ^ 2 * e ^ 2 * (4 * f ^ 2 - e ^ 2) / 4 := by
      rw [← hHe, dx, dy, dz, hCdef, cross_apply]
      simp only [PiLp.sub_apply]
      ring
    have h1' : H * dist (T.pts (j + 1)) (T.pts (j + 2)) ≤ H * f ^ 2 :=
      mul_le_mul_of_nonneg_left hz hH0
    have h2' : (H * f ^ 2) ^ 2 ≤ |C| ^ 2 := by
      rw [sq_abs, hC]; nlinarith
    have h3' : H * f ^ 2 ≤ |C| :=
      (pow_le_pow_iff_left₀ (by positivity) (abs_nonneg C) two_ne_zero).mp h2'
    linarith

/-! ## §3 THE BRIDGE: a `LocalFan` at every interior tile vertex of a real dissection -/

/-- **The bridge (NB's hypotheses from a real dissection).**  `D` a `CongruentDissection` whose model
has sides `sideOpp = (ef, f²−e², f²)`, `0 < e < f`; `g` an isometry placing the target in the closed
upper half-plane (`hup`; for the base-β target, the congruence onto `baseBetaTarget`, whose base is
on `y = 0`); `x` a vertex of some tile, interior to the target.  Then the tiles, read through `g`,
carry a `LocalFan` at `g x` of height `(g x) 1` with `ℓ = min(ef, f²−e²)`, `L = f²`, `c₀ = e/(2f)`,
and any altitude bound `H ≥ 0` with `4H²f⁴ ≤ b²e²(4f²−e²)`. -/
theorem localFan_of_dissection {N : ℕ} (D : CongruentDissection N) {e f H : ℝ} (he : 0 < e)
    (hef : e < f) (hs0 : sideOpp D.model 0 = e * f) (hs1 : sideOpp D.model 1 = f ^ 2 - e ^ 2)
    (hs2 : sideOpp D.model 2 = f ^ 2) (hH0 : 0 ≤ H)
    (hH : 4 * H ^ 2 * f ^ 4 ≤ (f ^ 2 - e ^ 2) ^ 2 * e ^ 2 * (4 * f ^ 2 - e ^ 2))
    (g : Plane ≃ᵢ Plane) (hup : ∀ k, 0 ≤ g (D.target.pts k) 1)
    {x : Plane} (hxv : ∃ i k, (D.tile i).pts k = x) (hxint : x ∈ interior D.target.carrier) :
    Nonempty (LocalFan (g x 1) (min (e * f) (f ^ 2 - e ^ 2)) (f ^ 2) H (e / (2 * f))) := by
  set T : Fin N → Tri := fun i => mapTri (isoAff g) (D.tile i) with hTdef
  have hTpts : ∀ i k, (T i).pts k = g ((D.tile i).pts k) := fun _ _ => rfl
  have hTc : ∀ i, (T i).Congruent D.model := fun i =>
    (congruent_mapTri g (D.tile i)).symm.trans (D.tiles_congruent i)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hxint)
  have hcov : Metric.ball (g x) r ⊆ ⋃ i, (T i).carrier := by
    intro y hy
    have hy' : g.symm y ∈ Metric.ball x r := by
      rw [Metric.mem_ball] at hy ⊢
      rw [← g.dist_eq (g.symm y) x, g.apply_symm_apply]; exact hy
    have hmem := hball hy'
    rw [← D.covers] at hmem
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    rw [hTdef]; simp only
    rw [mapTri_carrier]
    exact ⟨g.symm y, hi, by simp⟩
  have hdisj : Pairwise fun i j => Disjoint (interior (T i).carrier) (interior (T j).carrier) :=
    fun i j hij => mapTri_interiors_disjoint _ (D.interiors_disjoint hij)
  have hupT : ∀ i k, 0 ≤ (T i).pts k 1 := by
    intro i k
    have hsub : ∀ y ∈ (mapTri (isoAff g) D.target).carrier, 0 ≤ 0 * y 0 + 1 * y 1 :=
      carrier_sub (fun m => by
        show 0 ≤ 0 * g (D.target.pts m) 0 + 1 * g (D.target.pts m) 1
        have := hup m; linarith)
    have hin : (T i).pts k ∈ (mapTri (isoAff g) D.target).carrier := by
      rw [mapTri_carrier, hTpts]
      exact ⟨_, tile_subset_target D.toDissection i
        (subset_convexHull ℝ _ (Set.mem_range_self k)), by simp⟩
    have := hsub _ hin; linarith
  have hcorner : ∃ i k, (T i).pts k = g x := by
    obtain ⟨i, k, hk⟩ := hxv; exact ⟨i, k, by rw [hTpts, hk]⟩
  exact localFan_of_tiles T (g x) hr hcov hdisj hupT hcorner
    (fun i => (tile_metrics (hTc i) he hef hs0 hs1 hs2 hH0 hH).1)
    (fun i => (tile_metrics (hTc i) he hef hs0 hs1 hs2 hH0 hH).2.1)
    (fun i => (tile_metrics (hTc i) he hef hs0 hs1 hs2 hH0 hH).2.2.1)
    (fun i => (tile_metrics (hTc i) he hef hs0 hs1 hs2 hH0 hH).2.2.2)

/-! ## §4 NB for an actual dissection -/

/-- **NB for a real dissection** (R5's near-base vertex lemma).  With the bridge's data, no tile
vertex interior to the target sits at height `0 < h` with (1) `2h² < ℓ²(1 − e/(2f))` and
(2) `h²((ℓ + f²)² + H²) < H²ℓ²`. -/
theorem nb_dissection {N : ℕ} (D : CongruentDissection N) {e f H : ℝ} (he : 0 < e)
    (hef : e < f) (hs0 : sideOpp D.model 0 = e * f) (hs1 : sideOpp D.model 1 = f ^ 2 - e ^ 2)
    (hs2 : sideOpp D.model 2 = f ^ 2) (hH0 : 0 ≤ H)
    (hH : 4 * H ^ 2 * f ^ 4 ≤ (f ^ 2 - e ^ 2) ^ 2 * e ^ 2 * (4 * f ^ 2 - e ^ 2))
    (g : Plane ≃ᵢ Plane) (hup : ∀ k, 0 ≤ g (D.target.pts k) 1)
    {x : Plane} (hxv : ∃ i k, (D.tile i).pts k = x) (hxint : x ∈ interior D.target.carrier)
    (hh : 0 < g x 1)
    (h1 : 2 * g x 1 ^ 2 < min (e * f) (f ^ 2 - e ^ 2) ^ 2 * (1 - e / (2 * f)))
    (h2 : g x 1 ^ 2 * ((min (e * f) (f ^ 2 - e ^ 2) + f ^ 2) ^ 2 + H ^ 2)
      < H ^ 2 * min (e * f) (f ^ 2 - e ^ 2) ^ 2) : False := by
  obtain ⟨F⟩ := localFan_of_dissection D he hef hs0 hs1 hs2 hH0 hH g hup hxv hxint
  have hf : 0 < f := lt_trans he hef
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith
  exact nb_of_fan F hh (lt_min (by positivity) hb) hH0 (by positivity) (by positivity) h1 h2

/-- `H₀² = b²e²(4f²−e²)/(4f⁴)`, the square of the base-β tile's least altitude `b·sin α`. -/
noncomputable def Hsq (e f : ℝ) : ℝ := (f ^ 2 - e ^ 2) ^ 2 * e ^ 2 * (4 * f ^ 2 - e ^ 2) / (4 * f ^ 4)

theorem Hsq_nonneg {e f : ℝ} (he : 0 < e) (hef : e < f) : 0 ≤ Hsq e f := by
  have hf : 0 < f := lt_trans he hef
  unfold Hsq
  have : 0 ≤ 4 * f ^ 2 - e ^ 2 := by nlinarith
  positivity

theorem four_Hsq {e f : ℝ} (he : 0 < e) (hef : e < f) :
    4 * √(Hsq e f) ^ 2 * f ^ 4 = (f ^ 2 - e ^ 2) ^ 2 * e ^ 2 * (4 * f ^ 2 - e ^ 2) := by
  have hf : 0 < f := lt_trans he hef
  rw [Real.sq_sqrt (Hsq_nonneg he hef)]
  unfold Hsq; field_simp

/-- **NB for a dissection of the m = 1 base-β target** (target merely CONGRUENT to
`baseBetaTarget e f`, by the isometry `g` and relabelling `σ`; the height of `x` above the base line
is `(g x) 1`).  No tile vertex interior to the target lies at height `0 < h` with (1) and (2), the
latter at the exact least altitude `H² = Hsq e f`. -/
theorem nb_baseBeta {N : ℕ} (D : CongruentDissection N) {e f : ℝ} (he : 0 < e) (hef : e < f)
    (hs0 : sideOpp D.model 0 = e * f) (hs1 : sideOpp D.model 1 = f ^ 2 - e ^ 2)
    (hs2 : sideOpp D.model 2 = f ^ 2) {g : Plane ≃ᵢ Plane} {σ : Equiv.Perm (Fin 3)}
    (hg : ∀ k, g (D.target.pts k) = (BaseBetaTargetCoord.baseBetaTarget e f he hef).pts (σ k))
    {x : Plane} (hxv : ∃ i k, (D.tile i).pts k = x) (hxint : x ∈ interior D.target.carrier)
    (hh : 0 < g x 1)
    (h1 : 2 * g x 1 ^ 2 < min (e * f) (f ^ 2 - e ^ 2) ^ 2 * (1 - e / (2 * f)))
    (h2 : g x 1 ^ 2 * ((min (e * f) (f ^ 2 - e ^ 2) + f ^ 2) ^ 2 + Hsq e f)
      < Hsq e f * min (e * f) (f ^ 2 - e ^ 2) ^ 2) : False := by
  have hup : ∀ k, 0 ≤ g (D.target.pts k) 1 := by
    intro k
    rw [hg k]
    generalize σ k = m
    have hH := BaseBetaTargetCoord.height_pos he hef
    fin_cases m <;> simp [BaseBetaTargetCoord.baseBetaTarget, mkTri] <;> linarith
  have hS := Real.sq_sqrt (Hsq_nonneg he hef)
  exact nb_dissection D he hef hs0 hs1 hs2 (Real.sqrt_nonneg _) (four_Hsq he hef).le g hup hxv
    hxint hh h1 (by rw [hS]; exact h2)

/-! ## §5 R5's family kill for an actual dissection -/

/-- **R5's family point, killed in a real dissection.**  For a coprime member `2 ≤ e ≤ f − 2` with
`(f+1) ∣ e²`, no tile vertex interior to the target sits at height `(e²/(f+1))·cos(α/2)` (`sin(α/2)
= e/(2f)`; the point at distance `δ = e²/(f+1)` along `r`).  `NearBaseKill.family_point_killed`
(PROVED) ∘ `localFan_of_dissection` (the bridge). -/
theorem family_point_killed_dissection {e f : ℕ} (hcop : Nat.Coprime e f) (he : 2 ≤ e)
    (hef : e + 2 ≤ f) (hdvd : (f + 1) ∣ e ^ 2) {α : ℝ} (hs : sin α = e / (2 * f)) (hx0 : 0 < α)
    (hx1 : α < π / 2) {N : ℕ} (D : CongruentDissection N)
    (hs0 : sideOpp D.model 0 = (e : ℝ) * f) (hs1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (hs2 : sideOpp D.model 2 = (f : ℝ) ^ 2)
    (g : Plane ≃ᵢ Plane) (hup : ∀ k, 0 ≤ g (D.target.pts k) 1)
    {x : Plane} (hxv : ∃ i k, (D.tile i).pts k = x) (hxint : x ∈ interior D.target.carrier)
    (hx : g x 1 = (e : ℝ) ^ 2 / (f + 1) * cos α) : False := by
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast he
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast hef
  have he0 : (0 : ℝ) < e := by linarith
  have hlt : (e : ℝ) < f := by linarith
  have hf0 : (0 : ℝ) < f := by linarith
  have hc : 0 < cos α := cos_pos_of_mem_Ioo ⟨by linarith, hx1⟩
  have hsin : 0 < sin α := by rw [hs]; positivity
  have hb0 : 0 ≤ (f : ℝ) ^ 2 - e ^ 2 := by nlinarith
  have hH0 : 0 ≤ ((f : ℝ) ^ 2 - e ^ 2) * sin (2 * α) := by
    rw [sin_two_mul]; positivity
  have hH : 4 * (((f : ℝ) ^ 2 - e ^ 2) * sin (2 * α)) ^ 2 * (f : ℝ) ^ 4
      ≤ ((f : ℝ) ^ 2 - e ^ 2) ^ 2 * e ^ 2 * (4 * f ^ 2 - e ^ 2) := by
    have hcs : cos α ^ 2 = 1 - sin α ^ 2 := by rw [← sin_sq_add_cos_sq α]; ring
    rw [sin_two_mul]
    have : 4 * (((f : ℝ) ^ 2 - e ^ 2) * (2 * sin α * cos α)) ^ 2 * (f : ℝ) ^ 4
        = ((f : ℝ) ^ 2 - e ^ 2) ^ 2 * e ^ 2 * (4 * f ^ 2 - e ^ 2) := by
      have e1 : 4 * (((f : ℝ) ^ 2 - e ^ 2) * (2 * sin α * cos α)) ^ 2 * (f : ℝ) ^ 4
          = 16 * ((f : ℝ) ^ 2 - e ^ 2) ^ 2 * sin α ^ 2 * cos α ^ 2 * (f : ℝ) ^ 4 := by ring
      rw [e1, hcs, hs]; field_simp; ring
    exact this.le
  obtain ⟨F⟩ := localFan_of_dissection D he0 hlt hs0 hs1 hs2 hH0 hH g hup hxv hxint
  rw [hx] at F
  exact NearBaseKill.family_point_killed hcop he hef hdvd hs hx0 hx1 F

/-! ## §6 Vacuity rule: the bridge's hypotheses hold jointly for a REAL dissection -/

section Witness

open Erdos634.Z15Real Erdos634.CevianTiling63Bridge

/-- The 63-tiling with its model relabelled so that `sideOpp = (16, 24, 32) = (ef, f²−e², f²)` at
`e = 2√2`, `f = 4√2` (the `(2,3,4)` tile scaled by 8). -/
noncomputable def D63 : CongruentDissection CevianTiling63.tiles.length :=
  CevianTiling63Bridge.dissection.relabelModel (Equiv.swap 1 2)

theorem sqrt2_sq : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
theorem sqrt15_sq : √(15 : ℝ) ^ 2 = 15 := Real.sq_sqrt (by norm_num)

theorem dist_of_sq {p q : Plane} {v s : ℝ} (hv : 0 ≤ v) (h : dist p q ^ 2 = s) (hs : s = v ^ 2) :
    dist p q = v := by
  have h0 := dist_nonneg (x := p) (y := q)
  rw [hs] at h
  nlinarith [sq_nonneg (dist p q - v), sq_nonneg (dist p q + v)]

theorem model63_d01 : dist ((pieceTri headI_mem_tiles).pts 0) ((pieceTri headI_mem_tiles).pts 1)
    = 24 := by
  have e01 : CevianTiling63.dist2 (vertexOf CevianTiling63.tiles.headI 0)
      (vertexOf CevianTiling63.tiles.headI 1) = ((576:ℤ),(0:ℤ)) := by decide
  exact dist_of_sq (by norm_num) (by rw [pieceTri_dist_sq _ headI_mem_tiles 0 1, e01]) (by
    simp [toR]; norm_num)

theorem model63_d12 : dist ((pieceTri headI_mem_tiles).pts 1) ((pieceTri headI_mem_tiles).pts 2)
    = 16 := by
  have e12 : CevianTiling63.dist2 (vertexOf CevianTiling63.tiles.headI 1)
      (vertexOf CevianTiling63.tiles.headI 2) = ((256:ℤ),(0:ℤ)) := by decide
  exact dist_of_sq (by norm_num) (by rw [pieceTri_dist_sq _ headI_mem_tiles 1 2, e12]) (by
    simp [toR]; norm_num)

theorem model63_d20 : dist ((pieceTri headI_mem_tiles).pts 2) ((pieceTri headI_mem_tiles).pts 0)
    = 32 := by
  have e20 : CevianTiling63.dist2 (vertexOf CevianTiling63.tiles.headI 2)
      (vertexOf CevianTiling63.tiles.headI 0) = ((1024:ℤ),(0:ℤ)) := by decide
  exact dist_of_sq (by norm_num) (by rw [pieceTri_dist_sq _ headI_mem_tiles 2 0, e20]) (by
    simp [toR]; norm_num)

theorem ef63 : (2 * √2) * (4 * √2) = (16 : ℝ) := by nlinarith [sqrt2_sq]
theorem b63 : (4 * √2) ^ 2 - (2 * √2) ^ 2 = (24 : ℝ) := by nlinarith [sqrt2_sq]
theorem c63 : (4 * √2) ^ 2 = (32 : ℝ) := by nlinarith [sqrt2_sq]

theorem hs0_63 : sideOpp D63.model 0 = (2 * √2) * (4 * √2) := by
  rw [ef63]
  show dist ((pieceTri headI_mem_tiles).pts (Equiv.swap 1 2 (0 + 1)))
    ((pieceTri headI_mem_tiles).pts (Equiv.swap 1 2 (0 + 2))) = 16
  have e1 : Equiv.swap (1 : Fin 3) 2 (0 + 1) = 2 := by decide
  have e2 : Equiv.swap (1 : Fin 3) 2 (0 + 2) = 1 := by decide
  rw [e1, e2, dist_comm]; exact model63_d12

theorem hs1_63 : sideOpp D63.model 1 = (4 * √2) ^ 2 - (2 * √2) ^ 2 := by
  rw [b63]
  show dist ((pieceTri headI_mem_tiles).pts (Equiv.swap 1 2 (1 + 1)))
    ((pieceTri headI_mem_tiles).pts (Equiv.swap 1 2 (1 + 2))) = 24
  have e1 : Equiv.swap (1 : Fin 3) 2 (1 + 1) = 1 := by decide
  have e2 : Equiv.swap (1 : Fin 3) 2 (1 + 2) = 0 := by decide
  rw [e1, e2, dist_comm]; exact model63_d01

theorem hs2_63 : sideOpp D63.model 2 = (4 * √2) ^ 2 := by
  rw [c63]
  show dist ((pieceTri headI_mem_tiles).pts (Equiv.swap 1 2 (2 + 1)))
    ((pieceTri headI_mem_tiles).pts (Equiv.swap 1 2 (2 + 2))) = 32
  have e1 : Equiv.swap (1 : Fin 3) 2 (2 + 1) = 0 := by decide
  have e2 : Equiv.swap (1 : Fin 3) 2 (2 + 2) = 2 := by decide
  rw [e1, e2, dist_comm]; exact model63_d20

/-- The witness vertex `(14, 2√15)`: vertex `1` of piece `1` of the 63-tiling. -/
noncomputable def x63 : Plane := mkPt 14 (2 * √15)

theorem tiles_length_pos : 1 < CevianTiling63.tiles.length := by decide

theorem x63_vertex : ∃ i k, (D63.tile i).pts k = x63 := by
  refine ⟨⟨1, tiles_length_pos⟩, 1, ?_⟩
  show (pieceAt ⟨1, tiles_length_pos⟩).pts 1 = x63
  unfold pieceAt pieceTri x63
  simp [mkTri, CevianTiling63.tiles, CevianTiling63.t2, toZPt, zx, zy, toR]

theorem x63_interior : x63 ∈ interior D63.target.carrier := by
  show x63 ∈ interior targetTri.carrier
  rw [targetTri_eq_mkTri]
  have hx : x63 = mkPt 14 (2 * √15) := rfl
  have hs := sqrt15_sq
  have hs0 : 0 < √(15 : ℝ) := by positivity
  have hq : (toR (zx (toZPt (CevianTiling63.t1 target))) = 0) ∧
      (toR (zy (toZPt (CevianTiling63.t1 target))) = 0) ∧
      (toR (zx (toZPt (CevianTiling63.t2 target))) = 168) ∧
      (toR (zy (toZPt (CevianTiling63.t2 target))) = 0) ∧
      (toR (zx (toZPt (CevianTiling63.t3 target))) = 36) ∧
      (toR (zy (toZPt (CevianTiling63.t3 target))) = 36 * √15) := by
    simp [target, CevianTiling63.t1, CevianTiling63.t2, CevianTiling63.t3, CevianTiling63.q1,
      CevianTiling63.q2, CevianTiling63.q3, toZPt, zx, zy, toR]
  obtain ⟨q0, q1, q2, q3, q4, q5⟩ := hq
  have key := ChordChartPlanar.mem_interior_carrier_of_dets_pos (a := 14) (b := 2 * √15)
    target_det_pos (by simp only [q0, q1, q2, q3, q4, q5, det3]; nlinarith)
    (by simp only [q0, q1, q2, q3, q4, q5, det3]; nlinarith)
    (by simp only [q0, q1, q2, q3, q4, q5, det3]; nlinarith)
  rw [hx]; exact key

theorem hup63 : ∀ k, 0 ≤ (IsometryEquiv.refl Plane) (D63.target.pts k) 1 := by
  intro k
  show 0 ≤ targetTri.pts k 1
  rw [targetTri_pts_eq k]
  have hs0 : 0 ≤ √(15 : ℝ) := Real.sqrt_nonneg _
  fin_cases k <;> simp [target, CevianTiling63.t1, CevianTiling63.t2, CevianTiling63.t3,
    CevianTiling63.q1, CevianTiling63.q2, CevianTiling63.q3, toZPt, zy, toR]

theorem H63 : 4 * (3 * √15) ^ 2 * (4 * √2 : ℝ) ^ 4
    ≤ ((4 * √2) ^ 2 - (2 * √2) ^ 2) ^ 2 * (2 * √2) ^ 2 * (4 * (4 * √2) ^ 2 - (2 * √2) ^ 2) := by
  have h2 := sqrt2_sq; have h15 := sqrt15_sq
  have e1 : (4 * √2 : ℝ) ^ 4 = 1024 := by
    have : (4 * √2 : ℝ) ^ 4 = 256 * (√2 ^ 2) ^ 2 := by ring
    rw [this, h2]; norm_num
  have e2 : (2 * √2 : ℝ) ^ 2 = 8 := by nlinarith
  have e3 : (4 * √2 : ℝ) ^ 2 = 32 := by nlinarith
  have e4 : (3 * √15 : ℝ) ^ 2 = 135 := by nlinarith
  rw [e1, e2, e3, e4]; norm_num

/-- **Vacuity witness for `localFan_of_dissection`** (and hence for every hypothesis of
`nb_dissection` except (1)–(2), which are the conclusion's negation): the REAL 63-piece dissection by
the `(2,3,4)`-shaped tile (`CevianTiling63Bridge.dissection`, model relabelled), `e = 2√2`,
`f = 4√2`, exact least altitude `H = 3√15`, `g = id`, interior vertex `(14, 2√15)` — all hypotheses
discharged jointly, so the bridge produces a genuine `LocalFan`. -/
theorem witness63 :
    Nonempty (LocalFan ((IsometryEquiv.refl Plane) x63 1)
      (min ((2 * √2) * (4 * √2)) ((4 * √2) ^ 2 - (2 * √2) ^ 2)) ((4 * √2) ^ 2) (3 * √15)
      ((2 * √2) / (2 * (4 * √2)))) :=
  localFan_of_dissection D63 (by positivity) (by nlinarith [Real.sqrt_pos.mpr (two_pos (α := ℝ))])
    hs0_63 hs1_63 hs2_63 (by positivity) H63 (IsometryEquiv.refl Plane) hup63 x63_vertex
    x63_interior

end Witness

end Erdos634.Draft.NearBaseBridge

#print axioms Erdos634.Draft.NearBaseBridge.model_triple
#print axioms Erdos634.Draft.NearBaseBridge.tile_triple
#print axioms Erdos634.Draft.NearBaseBridge.perm3_cos
#print axioms Erdos634.Draft.NearBaseBridge.perm3_heron
#print axioms Erdos634.Draft.NearBaseBridge.tile_metrics
#print axioms Erdos634.Draft.NearBaseBridge.localFan_of_dissection
#print axioms Erdos634.Draft.NearBaseBridge.nb_dissection
#print axioms Erdos634.Draft.NearBaseBridge.nb_baseBeta
#print axioms Erdos634.Draft.NearBaseBridge.family_point_killed_dissection
#print axioms Erdos634.Draft.NearBaseBridge.witness63
