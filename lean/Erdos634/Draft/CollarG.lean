/-
Draft/CollarG.lean -- the +u collar of EVERY member `(u, v)`, `1 ≤ u < v`, and the scales it reaches.

    theorem collar_real    : a tiling of `W_t` by `n₀` tiles gives a dissection of `W_{t+u}`   (reals, `t > v − u`)
    theorem collar_nat     : WTilable u (u + g) (g + s) → WTilable u (u + g) (g + s + u)       (`s ≥ 1`)
    theorem wTilable_lin   : WTilable u v (j v + i u)                                          (`j ≥ 1`)
    theorem betaTilable_lin   : BetaTilable u v (j v + i u)                                    (`j ≥ 1`)
    theorem betaTilable_large : BetaTilable u v M  for coprime `u, v` and `M ≥ (u − 1)(v − 1) + v`

Parameters `u, e, σ > 0`: `v = u + e`, `t = e + σ`.  Tile `a = uv`, `b = v² − u²`, `c = v²`.  Frame `Φ_F`, `F = v/u`.
Layout and all linear bounds: `Draft.CollarGGeom` (generated).  Here: the model, the cells of the three lattices, the
tilings of the nine regions (four scaled triangles, two brick rectangles, two lattice parallelograms carried by
isometries, the given tiling of `W_t`), the packing lemma with the area identity, the passage between the frame and
dissections given by side lengths, the beta lift `W_T → T_T`, and the induction.
The tools (`mapped_grid`, …) are those of `Draft.CollarE1`, which is the case `u = 1`.

SCOPE.  For `u = 1` this is every scale `M ≥ v` (`CollarE1.betaTilable_e1`, proved again here).  For `u ≥ 2` the scales
reached are exactly `v + ⟨u, v⟩`: every `M ≥ (u − 1)(v − 1) + v`, and NOT every `M ≥ v` (for `(2, 3)` the scale `4` is
missing; for `(3, 4)` the scales `5, 6, 9`).  The missing scales need other seeds (announced by D. Paliy, not
formalized).  Nothing here says anything about the scales `M < v`.

THE CONSTRUCTION IS NOT OURS: D. Paliy's exterior collar and beta lift ("A six-block cap for every primitive W and beta
tile", 3 October 2026, unrefereed), on the seed he credits to M. Beeson.  What is added is a formal proof.
Constructive side of the composite problem; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.CollarGGeom
import Erdos634.Draft.CollarE1

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Rect RTiling.cast RTiling.castN interior_disj_snd)

namespace Erdos634.Draft.CollarG
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling
open Erdos634.Draft.S2G (triC triC_pts carrier_triC brickL brickU brick_rt cong_U_cell grid scaledRT baseTri
  baseTri_cong vol_triC sq_Phi' dPhi' disjoint_image' f_ne)
open Erdos634.Draft.BrickGridF (shift_rect)
open Erdos634.Draft.WAddF (Wt)
open Erdos634.Draft.WtoDeltaF (WS QS DS DS_eq hull_QS DTriR carrier_DTriR WS_eq)
open Erdos634.Draft.WClosedBase (WTriR carrier_WTriR WTriR_sq hull_WS)
open Erdos634.Draft.CollarE1 (mapped_grid dPhi2 cong_swap cnt sum_cnt)
open Erdos634.Draft.FDBBaseBetaE1 (HasSides hasSides_rot hasSides_swap congruent_of_hasSides')
open Erdos634.Draft.UniformThreshold (BetaTilable ThresholdAt hasSides_congr)

/-- push casts, then `ring` on what is left -/
local macro "pc_ring" : tactic => `(tactic| (push_cast <;> ring))

/-- the frame parameter `F = v/u` -/
noncomputable def gF (u e : ℝ) : ℝ := (u + e) / u

/-- the frame in which the cell `a × c` has a diagonal of length `b` -/
noncomputable def φβ (u e : ℝ) : ℝ := -(u + e) ^ 3 / (u * (3 * (u + e) ^ 2 - u ^ 2))

/-- `C = u (3v² − u²)`: the base of the base-β target at scale one -/
def cC (u e : ℝ) : ℝ := u * (3 * (u + e) ^ 2 - u ^ 2)

/-! ## The frame, the model, the cells -/
section frame
variable {u e : ℝ} (hu : 0 < u) (he : 0 < e)
include hu he

theorem hF1 : 1 < gF u e := by
  simp only [gF]
  rw [lt_div_iff₀ hu]; linarith

theorem hfr : 1 < 4 * gF u e ^ 2 := by
  have h := hF1 hu he
  nlinarith [mul_pos (sub_pos.mpr h) (sub_pos.mpr h)]

theorem hvpos : (0 : ℝ) < u + e := by positivity
theorem hapos : 0 < ca u e := by simp only [ca]; positivity
theorem hbpos : 0 < cb u e := by
  have hE : cb u e = e * (2 * u + e) := by simp only [cb]; ring
  rw [hE]; positivity
theorem cApos : 0 < cA u e := by
  have hE : cA u e = (u + e) * (e * (2 * u + e)) := by simp only [cA]; ring
  rw [hE]; positivity
theorem cBpos : 0 < cB u e := by
  have hE : cB u e = u * (u ^ 2 + 4 * u * e + 2 * e ^ 2) := by simp only [cB]; ring
  rw [hE]; positivity
theorem hPpos : (0 : ℝ) < 3 * (u + e) ^ 2 - u ^ 2 := by
  have hE : 3 * (u + e) ^ 2 - u ^ 2 = 2 * u ^ 2 + 6 * u * e + 3 * e ^ 2 := by ring
  rw [hE]; positivity

/-- the model tile: edges `01, 12, 20` of lengths `a, b, c` -/
noncomputable def Mod : Erdos634.Geometry.Tri :=
  brickL (gF u e) (hfr hu he) (ca u e) (cb u e) (hapos hu he) (hbpos hu he)

theorem hab_id : ca u e ^ 2 + cb u e ^ 2 + ca u e * cb u e / gF u e = ((u + e) ^ 2) ^ 2 := by
  have h1 : u ≠ 0 := hu.ne'
  have h2 : u + e ≠ 0 := (hvpos hu he).ne'
  simp only [ca, cb, gF]; field_simp; ring

/-- the cell `a × b` -/
noncomputable def cellB : RTiling (Phi (gF u e) '' Rect 0 (ca u e) 0 (cb u e)) (Mod hu he) 2 :=
  brick_rt (gF u e) (hfr hu he) (ca u e) (cb u e) (hapos hu he) (hbpos hu he) _
    (Erdos634.Geometry.Tri.Congruent.refl _) (cong_U_cell (hfr hu he) _ _ _ _)

/-- the cell `b × a` -/
noncomputable def cellA : RTiling (Phi (gF u e) '' Rect 0 (cb u e) 0 (ca u e)) (Mod hu he) 2 :=
  brick_rt (gF u e) (hfr hu he) (cb u e) (ca u e) (hbpos hu he) (hapos hu he) _
    (cong_swap (hfr hu he) _ _ _ _) ((cong_U_cell (hfr hu he) _ _ _ _).trans (cong_swap (hfr hu he) _ _ _ _))

theorem hφβ : 1 < 4 * φβ u e ^ 2 := by
  have hP := hPpos hu he
  have hden : 0 < u * (3 * (u + e) ^ 2 - u ^ 2) := mul_pos hu hP
  have hE : φβ u e ^ 2 = ((u + e) ^ 3) ^ 2 / (u * (3 * (u + e) ^ 2 - u ^ 2)) ^ 2 := by
    simp only [φβ]; rw [neg_div, neg_sq, div_pow]
  rw [hE, ← mul_div_assoc, lt_div_iff₀ (pow_pos hden 2)]
  have k : 4 * ((u + e) ^ 3) ^ 2 - 1 * (u * (3 * (u + e) ^ 2 - u ^ 2)) ^ 2
      = e ^ 2 * (3 * u + 2 * e) * (2 * (u + e) ^ 3 + u * (3 * (u + e) ^ 2 - u ^ 2)) := by ring
  have pos : 0 < e ^ 2 * (3 * u + 2 * e) * (2 * (u + e) ^ 3 + u * (3 * (u + e) ^ 2 - u ^ 2)) :=
    mul_pos (by positivity) (add_pos (by positivity) hden)
  linarith

theorem cong_β : (brickL (φβ u e) (hφβ hu he) (ca u e) ((u + e) ^ 2) (hapos hu he)
    (pow_pos (hvpos hu he) 2)).Congruent (Mod hu he) := by
  have h1 : u ≠ 0 := hu.ne'
  have h2 : u + e ≠ 0 := (hvpos hu he).ne'
  have h3 : 3 * (u + e) ^ 2 - u ^ 2 ≠ 0 := (hPpos hu he).ne'
  refine ((brickL _ _ _ _ _ _).congruent_relabel (Equiv.swap (0 : Fin 3) 1)).trans ?_
  refine Erdos634.SssCongruent.congruent_of_dist_three ?_ ?_ ?_ <;>
    simp only [Erdos634.Geometry.Tri.relabel, Mod, brickL, triC_pts] <;>
    (refine dPhi2 _ _ _ _ ?_; rw [sq_Phi' (hφβ hu he), sq_Phi' (hfr hu he)]; simp only [φβ, gF, ca, cb]
     field_simp; ring)

/-- the cell `a × c` of the frame `φβ` -/
noncomputable def cellC : RTiling (Phi (φβ u e) '' Rect 0 (ca u e) 0 ((u + e) ^ 2)) (Mod hu he) 2 :=
  brick_rt (φβ u e) (hφβ hu he) (ca u e) ((u + e) ^ 2) (hapos hu he) (pow_pos (hvpos hu he) 2) _
    (cong_β hu he) ((cong_U_cell (hφβ hu he) _ _ _ _).trans (cong_β hu he))

theorem Mod_sides : dist ((Mod hu he).pts 0) ((Mod hu he).pts 1) = ca u e ∧
    dist ((Mod hu he).pts 1) ((Mod hu he).pts 2) = cb u e ∧
    dist ((Mod hu he).pts 0) ((Mod hu he).pts 2) = (u + e) ^ 2 := by
  have hf := hfr hu he
  have h1 : u ≠ 0 := hu.ne'
  have h2 : u + e ≠ 0 := (hvpos hu he).ne'
  simp only [Mod, brickL, triC_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  refine ⟨?_, ?_, ?_⟩
  · refine (sq_eq_sq₀ dist_nonneg (hapos hu he).le).mp ?_
    rw [sq_Phi' hf]; ring
  · refine (sq_eq_sq₀ dist_nonneg (hbpos hu he).le).mp ?_
    rw [sq_Phi' hf]; ring
  · refine (sq_eq_sq₀ dist_nonneg (by positivity)).mp ?_
    rw [sq_Phi' hf]; simp only [ca, cb, gF]; field_simp; ring

/-- the model has the sides `(b, c, a)` on the edges `12, 20, 01` -/
theorem Mod_hasSides : HasSides (Mod hu he) (cb u e) ((u + e) ^ 2) (ca u e) := by
  obtain ⟨m1, m2, m3⟩ := Mod_sides hu he
  exact ⟨Equiv.refl _, by simp only [Equiv.refl_apply]; exact m2,
    by simp only [Equiv.refl_apply]; rw [dist_comm]; exact m3, by simp only [Equiv.refl_apply]; exact m1⟩

open MeasureTheory in
theorem volMod : volume (Mod hu he).carrier
    = ENNReal.ofReal (|sD (gF u e) / (2 * gF u e)| * (ca u e * cb u e))
      * volume Erdos634.AreaDet.stdCarrier := by
  unfold Mod Erdos634.Draft.S2G.brickL
  rw [vol_triC]
  congr 2
  rw [abs_mul]
  congr 1
  have hE : ((ca u e, (0 : ℝ)).1 - ((0 : ℝ), (0 : ℝ)).1) * ((ca u e, cb u e).2 - ((0 : ℝ), (0 : ℝ)).2)
      - ((ca u e, cb u e).1 - ((0 : ℝ), (0 : ℝ)).1) * ((ca u e, (0 : ℝ)).2 - ((0 : ℝ), (0 : ℝ)).2)
      = ca u e * cb u e := by ring
  rw [hE, abs_of_pos (mul_pos (hapos hu he) (hbpos hu he))]

end frame

/-! ## The tilings of the regions -/
section pieces
variable {u e σ : ℝ} (hu : 0 < u) (he : 0 < e) (hσ : 0 < σ)
include hu he hσ

/-- `Z1`: `a` columns of width `b`, `v t` rows of height `a` -/
noncomputable def RT1 (k l : ℕ) (hk : (k : ℝ) + 1 = ca u e) (hl : (l : ℝ) + 1 = (u + e) * ct e σ) :
    RTiling (Phi (gF u e) '' Z1 u e σ) (Mod hu he) (2 * (k + 1) * (l + 1)) :=
  shift_rect (grid (hfr hu he) (hbpos hu he) (hapos hu he) (cellA hu he) k l) (cA u e * ct e σ)
    (cB u e * u + cL u e) (cA u e * ct e σ + cA u e * u)
    (cB u e * u + cL u e + ca u e * (u + e) * ct e σ)
    (by rw [hk]; simp only [cA, ca, cb]; ring) (by rw [hl]; ring)

/-- `Z2`: `b` columns of width `a`, `u σ` rows of height `b` -/
noncomputable def RT2 (k l : ℕ) (hk : (k : ℝ) + 1 = cb u e) (hl : (l : ℝ) + 1 = u * σ) :
    RTiling (Phi (gF u e) '' Z2 u e σ) (Mod hu he) (2 * (k + 1) * (l + 1)) :=
  shift_rect (grid (hfr hu he) (hapos hu he) (hbpos hu he) (cellB hu he) k l) (cA u e * ct e σ)
    (cB u e * u + cL u e + ca u e * (u + e) * ct e σ) (cA u e * ct e σ + cA u e * u)
    (cB u e * (ct e σ + u))
    (by rw [hk]; simp only [cA, ca, cb]; ring) (by rw [hl]; simp only [cB, cL, ca, cb, ct]; ring)

theorem det3 : ((qR u e σ).1 - (qK u e σ).1) * ((qO u e σ).2 - (qK u e σ).2)
    - ((qO u e σ).1 - (qK u e σ).1) * ((qR u e σ).2 - (qK u e σ).2) ≠ 0 := by
  have h2 : u + e ≠ 0 := (hvpos hu he).ne'
  have hE : ((qR u e σ).1 - (qK u e σ).1) * ((qO u e σ).2 - (qK u e σ).2)
      - ((qO u e σ).1 - (qK u e σ).1) * ((qR u e σ).2 - (qK u e σ).2)
      = -(ca u e ^ 2 * (ca u e * cb u e)) := by
    simp only [qR, qK, qO, ca, cb]; field_simp; ring
  rw [hE]
  exact neg_ne_zero.mpr (mul_pos (pow_pos (hapos hu he) 2) (mul_pos (hapos hu he) (hbpos hu he))).ne'

theorem det4 : ((qBp u e σ).1 - (qJ u e σ).1) * ((qE u e σ).2 - (qJ u e σ).2)
    - ((qE u e σ).1 - (qJ u e σ).1) * ((qBp u e σ).2 - (qJ u e σ).2) ≠ 0 := by
  have hE : ((qBp u e σ).1 - (qJ u e σ).1) * ((qE u e σ).2 - (qJ u e σ).2)
      - ((qE u e σ).1 - (qJ u e σ).1) * ((qBp u e σ).2 - (qJ u e σ).2)
      = (u * e) ^ 2 * (ca u e * cb u e) := by
    simp only [qBp, qJ, qE, ca, cb]; ring
  rw [hE]
  exact (mul_pos (by positivity) (mul_pos (hapos hu he) (hbpos hu he))).ne'

theorem det5 : ((qX u e σ).1 - (qO u e σ).1) * ((qJ u e σ).2 - (qO u e σ).2)
    - ((qJ u e σ).1 - (qO u e σ).1) * ((qX u e σ).2 - (qO u e σ).2) ≠ 0 := by
  have h2 : u + e ≠ 0 := (hvpos hu he).ne'
  have hE : ((qX u e σ).1 - (qO u e σ).1) * ((qJ u e σ).2 - (qO u e σ).2)
      - ((qJ u e σ).1 - (qO u e σ).1) * ((qX u e σ).2 - (qO u e σ).2)
      = -((u * e) ^ 2 * (ca u e * cb u e)) := by
    simp only [qX, qO, qJ, ca, cb]; field_simp; ring
  rw [hE]
  exact neg_ne_zero.mpr (mul_pos (by positivity) (mul_pos (hapos hu he) (hbpos hu he))).ne'

theorem det8 : ((qR u e σ).1 - (qY u e σ).1) * ((qE u e σ).2 - (qY u e σ).2)
    - ((qE u e σ).1 - (qY u e σ).1) * ((qR u e σ).2 - (qY u e σ).2) ≠ 0 := by
  have h2 : u + e ≠ 0 := (hvpos hu he).ne'
  have hE : ((qR u e σ).1 - (qY u e σ).1) * ((qE u e σ).2 - (qY u e σ).2)
      - ((qE u e σ).1 - (qY u e σ).1) * ((qR u e σ).2 - (qY u e σ).2)
      = (u * e) ^ 2 * (ca u e * cb u e) := by
    simp only [qR, qY, qE, ca, cb]; field_simp; ring
  rw [hE]
  exact (mul_pos (by positivity) (mul_pos (hapos hu he) (hbpos hu he))).ne'

/-- `Z3 = K R O`, the tile at scale `a = uv` -/
noncomputable def RT3 (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = ca u e) :
    RTiling (Phi (gF u e) '' Z3 u e σ) (Mod hu he) (k * k) :=
  scaledRT (gF u e) (hfr hu he) (qK u e σ) (qR u e σ) (qO u e σ) k hk0 (det3 hu he hσ) _
    (baseTri_cong _ _ (ca u e) (cb u e) (((u + e) ^ 2) ^ 2) (hapos hu he) (hbpos hu he) (hab_id hu he) _ _ _
      k hk0 _
      (by have h1 : u ≠ 0 := hu.ne'
          have h2 : u + e ≠ 0 := (hvpos hu he).ne'
          rw [hk]; simp only [qK, qR, qO, ca, cb, gF]; field_simp; ring)
      (by have h1 : u ≠ 0 := hu.ne'
          have h2 : u + e ≠ 0 := (hvpos hu he).ne'
          rw [hk]; simp only [qK, qR, qO, ca, cb, gF]; field_simp; ring)
      (by have h1 : u ≠ 0 := hu.ne'
          have h2 : u + e ≠ 0 := (hvpos hu he).ne'
          rw [hk]; simp only [qK, qR, qO, ca, cb, gF]; field_simp; ring))

/-- `Z4 = J B' E`, the tile at scale `h = u (v − u)` -/
noncomputable def RT4 (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = u * e) :
    RTiling (Phi (gF u e) '' Z4 u e σ) (Mod hu he) (k * k) :=
  scaledRT (gF u e) (hfr hu he) (qJ u e σ) (qBp u e σ) (qE u e σ) k hk0 (det4 hu he hσ) _
    (baseTri_cong _ _ (ca u e) (cb u e) (((u + e) ^ 2) ^ 2) (hapos hu he) (hbpos hu he) (hab_id hu he) _ _ _
      k hk0 _
      (by have h1 : u ≠ 0 := hu.ne'
          have h2 : u + e ≠ 0 := (hvpos hu he).ne'
          rw [hk]; simp only [qJ, qBp, qE, ca, cb, gF]; field_simp; ring)
      (by have h1 : u ≠ 0 := hu.ne'
          have h2 : u + e ≠ 0 := (hvpos hu he).ne'
          rw [hk]; simp only [qJ, qBp, qE, ca, cb, gF]; field_simp; ring)
      (by have h1 : u ≠ 0 := hu.ne'
          have h2 : u + e ≠ 0 := (hvpos hu he).ne'
          rw [hk]; simp only [qJ, qBp, qE, ca, cb, gF]; field_simp; ring))

/-- `Z5 = O X J`, the tile at scale `h` -/
noncomputable def RT5 (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = u * e) :
    RTiling (Phi (gF u e) '' Z5 u e σ) (Mod hu he) (k * k) :=
  scaledRT (gF u e) (hfr hu he) (qO u e σ) (qX u e σ) (qJ u e σ) k hk0 (det5 hu he hσ) _
    (baseTri_cong _ _ (ca u e) (cb u e) (((u + e) ^ 2) ^ 2) (hapos hu he) (hbpos hu he) (hab_id hu he) _ _ _
      k hk0 _
      (by have h1 : u ≠ 0 := hu.ne'
          have h2 : u + e ≠ 0 := (hvpos hu he).ne'
          rw [hk]; simp only [qO, qX, qJ, ca, cb, gF]; field_simp; ring)
      (by have h1 : u ≠ 0 := hu.ne'
          have h2 : u + e ≠ 0 := (hvpos hu he).ne'
          rw [hk]; simp only [qO, qX, qJ, ca, cb, gF]; field_simp; ring)
      (by have h1 : u ≠ 0 := hu.ne'
          have h2 : u + e ≠ 0 := (hvpos hu he).ne'
          rw [hk]; simp only [qO, qX, qJ, ca, cb, gF]; field_simp; ring))

/-- `Z8 = Y R E`, the tile at scale `h` -/
noncomputable def RT8 (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = u * e) :
    RTiling (Phi (gF u e) '' Z8 u e σ) (Mod hu he) (k * k) :=
  scaledRT (gF u e) (hfr hu he) (qY u e σ) (qR u e σ) (qE u e σ) k hk0 (det8 hu he hσ) _
    (baseTri_cong _ _ (ca u e) (cb u e) (((u + e) ^ 2) ^ 2) (hapos hu he) (hbpos hu he) (hab_id hu he) _ _ _
      k hk0 _
      (by have h1 : u ≠ 0 := hu.ne'
          have h2 : u + e ≠ 0 := (hvpos hu he).ne'
          rw [hk]; simp only [qY, qR, qE, ca, cb, gF]; field_simp; ring)
      (by have h1 : u ≠ 0 := hu.ne'
          have h2 : u + e ≠ 0 := (hvpos hu he).ne'
          rw [hk]; simp only [qY, qR, qE, ca, cb, gF]; field_simp; ring)
      (by have h1 : u ≠ 0 := hu.ne'
          have h2 : u + e ≠ 0 := (hvpos hu he).ne'
          rw [hk]; simp only [qY, qR, qE, ca, cb, gF]; field_simp; ring))

/-- `Z6`: the parallelogram `X R E J`, `(v − u) v × u (v − u)` cells of the lattice `(r, s)` -/
theorem RT6 (k l : ℕ) (hk : (k : ℝ) + 1 = e * (u + e)) (hl : (l : ℝ) + 1 = u * e) :
    ∃ S : Set Plane, Nonempty (RTiling S (Mod hu he) (2 * (k + 1) * (l + 1))) ∧ S ⊆ Phi (gF u e) '' Z6 u e σ := by
  have h1 : u ≠ 0 := hu.ne'
  have h2 : u + e ≠ 0 := (hvpos hu he).ne'
  have h := mapped_grid (hfr hu he) (hfr hu he) (hapos hu he) (hbpos hu he) (cellB hu he) k l (qX u e σ)
    (vr u e) (vs u e)
    (by have hE : (vr u e).1 * (vs u e).2 - (vs u e).1 * (vr u e).2 = -(ca u e * cb u e) := by
          simp only [vr, vs, ca, cb]; field_simp; ring
        rw [hE]; exact neg_ne_zero.mpr (mul_pos (hapos hu he) (hbpos hu he)).ne')
    (by simp only [vr, ca, gF]; field_simp; ring) (by simp only [vs, cb, gF]; field_simp; ring)
    (by simp only [vr, vs, ca, cb, gF]; field_simp; ring)
  rw [hk, hl] at h
  exact h

/-- `Z7`: the parallelogram `K C Y R`, `u (v − u) × u²` cells of the lattice `(p, w)` -/
theorem RT7 (k l : ℕ) (hk : (k : ℝ) + 1 = u * e) (hl : (l : ℝ) + 1 = u ^ 2) :
    ∃ S : Set Plane, Nonempty (RTiling S (Mod hu he) (2 * (k + 1) * (l + 1))) ∧ S ⊆ Phi (gF u e) '' Z7 u e σ := by
  have h1 : u ≠ 0 := hu.ne'
  have h2 : u + e ≠ 0 := (hvpos hu he).ne'
  have h3 : 3 * (u + e) ^ 2 - u ^ 2 ≠ 0 := (hPpos hu he).ne'
  have h := mapped_grid (hφβ hu he) (hfr hu he) (hapos hu he) (pow_pos (hvpos hu he) 2) (cellC hu he) k l
    (qK u e σ) (vp u e) (vw u e)
    (by have hE : (vp u e).1 * (vw u e).2 - (vw u e).1 * (vp u e).2 = -(ca u e * cb u e) := by
          simp only [vp, vw, ca, cb]; ring
        rw [hE]; exact neg_ne_zero.mpr (mul_pos (hapos hu he) (hbpos hu he)).ne')
    (by simp only [vp, ca, gF]; field_simp; ring) (by simp only [vw, gF]; field_simp; ring)
    (by simp only [vp, vw, ca, gF, φβ]; field_simp; ring)
  rw [hk, hl] at h
  exact h

end pieces

/-! ## Assembly: the nine regions fill `W_{t+u}` -/

/-- the regions in the plane; the two parallelograms are given as sets -/
noncomputable def regionOf (u e σ : ℝ) (S6 S7 : Set Plane) : Fin 9 → Set Plane := fun i => match i with
  | ⟨0, _⟩ => Phi (gF u e) '' Z0 u e σ
  | ⟨1, _⟩ => Phi (gF u e) '' Z1 u e σ
  | ⟨2, _⟩ => Phi (gF u e) '' Z2 u e σ
  | ⟨3, _⟩ => Phi (gF u e) '' Z3 u e σ
  | ⟨4, _⟩ => Phi (gF u e) '' Z4 u e σ
  | ⟨5, _⟩ => Phi (gF u e) '' Z5 u e σ
  | ⟨6, _⟩ => S6
  | ⟨7, _⟩ => S7
  | ⟨8, _⟩ => Phi (gF u e) '' Z8 u e σ
  | ⟨k + 9, h⟩ => absurd h (by omega)

section assemble
variable {u e σ : ℝ} (hu : 0 < u) (he : 0 < e) (hσ : 0 < σ)
include hu he hσ

theorem tA_pos : 0 < cA u e * (ct e σ + u) :=
  mul_pos (cA_pos hu he hσ) (by have := ct_pos hu he hσ; linarith)
theorem tB_pos : 0 < cB u e * (ct e σ + u) :=
  mul_pos (cB_pos hu he hσ) (by have := ct_pos hu he hσ; linarith)

/-- the target `W_{t+u}` -/
noncomputable def tgt : Erdos634.Geometry.Tri :=
  WTriR (gF u e) (hF1 hu he) (cA u e * (ct e σ + u)) (cB u e * (ct e σ + u)) (tA_pos hu he hσ) (tB_pos hu he hσ)

theorem carrier_tgt : (tgt hu he hσ).carrier = Phi (gF u e) '' ZT u e σ :=
  carrier_WTriR _ _ _ _ _ _

open MeasureTheory in
theorem vol_tgt : volume (tgt hu he hσ).carrier
    = ENNReal.ofReal (|sD (gF u e) / (2 * gF u e)|
        * (cA u e * (ct e σ + u) * (cB u e * (ct e σ + u))))
      * volume Erdos634.AreaDet.stdCarrier := by
  have hu0 := tA_pos hu he hσ
  have hv0 := tB_pos hu he hσ
  have hdet : (((cA u e * (ct e σ + u), cB u e * (ct e σ + u)) : ℝ × ℝ).1
          - ((cA u e * (ct e σ + u), (0 : ℝ)) : ℝ × ℝ).1)
        * ((((0 : ℝ), cB u e * (ct e σ + u)) : ℝ × ℝ).2 - ((cA u e * (ct e σ + u), (0 : ℝ)) : ℝ × ℝ).2)
      - ((((0 : ℝ), cB u e * (ct e σ + u)) : ℝ × ℝ).1 - ((cA u e * (ct e σ + u), (0 : ℝ)) : ℝ × ℝ).1)
        * (((cA u e * (ct e σ + u), cB u e * (ct e σ + u)) : ℝ × ℝ).2
          - ((cA u e * (ct e σ + u), (0 : ℝ)) : ℝ × ℝ).2)
      = cA u e * (ct e σ + u) * (cB u e * (ct e σ + u)) := by ring
  have hne : (((cA u e * (ct e σ + u), cB u e * (ct e σ + u)) : ℝ × ℝ).1
          - ((cA u e * (ct e σ + u), (0 : ℝ)) : ℝ × ℝ).1)
        * ((((0 : ℝ), cB u e * (ct e σ + u)) : ℝ × ℝ).2 - ((cA u e * (ct e σ + u), (0 : ℝ)) : ℝ × ℝ).2)
      - ((((0 : ℝ), cB u e * (ct e σ + u)) : ℝ × ℝ).1 - ((cA u e * (ct e σ + u), (0 : ℝ)) : ℝ × ℝ).1)
        * (((cA u e * (ct e σ + u), cB u e * (ct e σ + u)) : ℝ × ℝ).2
          - ((cA u e * (ct e σ + u), (0 : ℝ)) : ℝ × ℝ).2)
      ≠ 0 := by rw [hdet]; exact (mul_pos hu0 hv0).ne'
  have hc : (tgt hu he hσ).carrier
      = (triC (gF u e) (hfr hu he) (cA u e * (ct e σ + u), 0)
          (cA u e * (ct e σ + u), cB u e * (ct e σ + u)) (0, cB u e * (ct e σ + u)) hne).carrier := by
    rw [carrier_tgt, carrier_triC]
    show Phi (gF u e) '' WS _ _ = _
    rw [← hull_WS _ _ hu0 hv0]
  rw [hc, vol_triC]
  congr 2
  rw [abs_mul]
  congr 1
  rw [hdet, abs_of_pos (mul_pos hu0 hv0)]

/-- **The collar step, real parameters.**  A tiling of `W_t` by `n₀` tiles gives a dissection of `W_{t+u}`. -/
theorem collar_real (n0 k1 l1 k2 l2 k3 k4 k6 l6 k7 l7 : ℕ)
    (hn0 : (n0 : ℝ) = cQ u e * ct e σ ^ 2)
    (hk1 : (k1 : ℝ) + 1 = ca u e) (hl1 : (l1 : ℝ) + 1 = (u + e) * ct e σ)
    (hk2 : (k2 : ℝ) + 1 = cb u e) (hl2 : (l2 : ℝ) + 1 = u * σ)
    (hk30 : 0 < k3) (hk3 : (k3 : ℝ) = ca u e) (hk40 : 0 < k4) (hk4 : (k4 : ℝ) = u * e)
    (hk6 : (k6 : ℝ) + 1 = e * (u + e)) (hl6 : (l6 : ℝ) + 1 = u * e)
    (hk7 : (k7 : ℝ) + 1 = u * e) (hl7 : (l7 : ℝ) + 1 = u ^ 2)
    (R0 : RTiling (Phi (gF u e) '' Wt (cA u e) (cB u e) (ct e σ)) (Mod hu he) n0) :
    ∃ (N : ℕ) (D : CongruentDissection N), (N : ℝ) = cQ u e * (ct e σ + u) ^ 2 ∧ D.model = Mod hu he ∧
      D.target = tgt hu he hσ := by
  obtain ⟨S6, ⟨R6⟩, h6⟩ := RT6 hu he hσ k6 l6 hk6 hl6
  obtain ⟨S7, ⟨R7⟩, h7⟩ := RT7 hu he hσ k7 l7 hk7 hl7
  have R0s : RTiling (Phi (gF u e) '' Z0 u e σ) (Mod hu he) n0 := shiftR R0 (0, cB u e * u)
  have Rall : ∀ a : Fin 9, RTiling (regionOf u e σ S6 S7 a) (Mod hu he)
      (cnt n0 (2 * (k1 + 1) * (l1 + 1)) (2 * (k2 + 1) * (l2 + 1)) (k3 * k3) (k4 * k4) (k4 * k4)
        (2 * (k6 + 1) * (l6 + 1)) (2 * (k7 + 1) * (l7 + 1)) (k4 * k4) a) := fun a => match a with
    | ⟨0, _⟩ => R0s
    | ⟨1, _⟩ => RT1 hu he k1 l1 hk1 hl1
    | ⟨2, _⟩ => RT2 hu he k2 l2 hk2 hl2
    | ⟨3, _⟩ => RT3 hu he hσ k3 hk30 hk3
    | ⟨4, _⟩ => RT4 hu he hσ k4 hk40 hk4
    | ⟨5, _⟩ => RT5 hu he hσ k4 hk40 hk4
    | ⟨6, _⟩ => R6
    | ⟨7, _⟩ => R7
    | ⟨8, _⟩ => RT8 hu he hσ k4 hk40 hk4
    | ⟨k + 9, h⟩ => absurd h (by omega)
  have sub_all : ∀ a : Fin 9, regionOf u e σ S6 S7 a ⊆ Phi (gF u e) '' Zf u e σ a := fun a => match a with
    | ⟨0, _⟩ => subset_rfl
    | ⟨1, _⟩ => subset_rfl
    | ⟨2, _⟩ => subset_rfl
    | ⟨3, _⟩ => subset_rfl
    | ⟨4, _⟩ => subset_rfl
    | ⟨5, _⟩ => subset_rfl
    | ⟨6, _⟩ => h6
    | ⟨7, _⟩ => h7
    | ⟨8, _⟩ => subset_rfl
    | ⟨k + 9, h⟩ => absurd h (by omega)
  have hS_all : ∀ a b : Fin 9, a ≠ b →
      Disjoint (interior (regionOf u e σ S6 S7 a)) (interior (regionOf u e σ S6 S7 b)) := fun a b hab =>
    (disjoint_image' (hfr hu he) (dZ_all hu he hσ a b hab)).mono (interior_mono (sub_all a))
      (interior_mono (sub_all b))
  have hsub_all : ∀ a : Fin 9, regionOf u e σ S6 S7 a ⊆ (tgt hu he hσ).carrier := fun a => by
    rw [carrier_tgt]
    exact (sub_all a).trans (Set.image_mono (Zf_sub hu he hσ a))
  have hsumR : ((∑ a, cnt n0 (2 * (k1 + 1) * (l1 + 1)) (2 * (k2 + 1) * (l2 + 1)) (k3 * k3) (k4 * k4) (k4 * k4)
      (2 * (k6 + 1) * (l6 + 1)) (2 * (k7 + 1) * (l7 + 1)) (k4 * k4) a : ℕ) : ℝ)
      = cQ u e * (ct e σ + u) ^ 2 := by
    rw [sum_cnt]
    push_cast
    rw [hn0, hk1, hl1, hk2, hl2, hk3, hk4, hk6, hl6, hk7, hl7]
    simp only [cQ, ca, cb, ct]; ring
  have hvol : ((∑ a, cnt n0 (2 * (k1 + 1) * (l1 + 1)) (2 * (k2 + 1) * (l2 + 1)) (k3 * k3) (k4 * k4) (k4 * k4)
      (2 * (k6 + 1) * (l6 + 1)) (2 * (k7 + 1) * (l7 + 1)) (k4 * k4) a : ℕ) : ENNReal)
        * MeasureTheory.volume (Mod hu he).carrier
      = MeasureTheory.volume (tgt hu he hσ).carrier := by
    have hNR : (0 : ℝ) ≤ ((∑ a, cnt n0 (2 * (k1 + 1) * (l1 + 1)) (2 * (k2 + 1) * (l2 + 1)) (k3 * k3) (k4 * k4)
        (k4 * k4) (2 * (k6 + 1) * (l6 + 1)) (2 * (k7 + 1) * (l7 + 1)) (k4 * k4) a : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [volMod hu he, vol_tgt hu he hσ, ← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hNR, hsumR]
    congr 2
    simp only [cQ, cA, cB, ca, cb]; ring
  obtain ⟨D, hM, hT⟩ := Erdos634.Draft.S2L.pack_exists (M := Mod hu he) (T := tgt hu he hσ)
    (regionOf u e σ S6 S7) _ Rall hS_all hsub_all hvol
  exact ⟨_, D, hsumR, hM, hT⟩

end assemble

/-! ## The frame and dissections given by side lengths -/

/-- the three corners of the lift triangle: `X = (A T, B T)`, `P = (0, B T)`, `Q = (A T, C T)` -/
def bX (u e T : ℝ) : ℝ × ℝ := (cA u e * T, cB u e * T)
def bP (u e T : ℝ) : ℝ × ℝ := (0, cB u e * T)
def bQ (u e T : ℝ) : ℝ × ℝ := (cA u e * T, cC u e * T)

theorem DTriR_sq (F : ℝ) (hF : 1 < F) (x y w : ℝ) (hx : 0 < x) (hw : 0 < w) :
    dist ((DTriR F hF x y w hx hw).pts 0) ((DTriR F hF x y w hx hw).pts 1) ^ 2 = w ^ 2 ∧
    dist ((DTriR F hF x y w hx hw).pts 1) ((DTriR F hF x y w hx hw).pts 2) ^ 2
      = x ^ 2 + (w - y) ^ 2 + x * (w - y) / F ∧
    dist ((DTriR F hF x y w hx hw).pts 0) ((DTriR F hF x y w hx hw).pts 2) ^ 2 = x ^ 2 + y ^ 2 - x * y / F := by
  simp only [DTriR, Erdos634.Draft.WBrickF.triC_pts, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  refine ⟨?_, ?_, ?_⟩
  · rw [sq_Phi hF]; simp only; ring
  · rw [sq_Phi hF]; simp only; ring
  · rw [sq_Phi hF]; simp only; ring

section convert
variable {u e : ℝ} (hu : 0 < u) (he : 0 < e)
include hu he

/-- the triangle `W_T` of the frame -/
noncomputable def WT (T : ℝ) (hT : 0 < T) : Erdos634.Geometry.Tri :=
  WTriR (gF u e) (hF1 hu he) (cA u e * T) (cB u e * T) (mul_pos (cApos hu he) hT) (mul_pos (cBpos hu he) hT)

theorem carrier_WT (T : ℝ) (hT : 0 < T) :
    (WT hu he T hT).carrier = Phi (gF u e) '' Wt (cA u e) (cB u e) T :=
  (carrier_WTriR _ _ _ _ _ _).trans (congrArg _ (WS_eq _ _ _ hT))

theorem WT_sides (T : ℝ) (hT : 0 < T) :
    dist ((WT hu he T hT).pts 0) ((WT hu he T hT).pts 1) = cB u e * T ∧
    dist ((WT hu he T hT).pts 1) ((WT hu he T hT).pts 2) = cA u e * T ∧
    dist ((WT hu he T hT).pts 0) ((WT hu he T hT).pts 2) = T * (u + e) ^ 3 := by
  have h1 : u ≠ 0 := hu.ne'
  have h2 : u + e ≠ 0 := (hvpos hu he).ne'
  have hA := mul_pos (cApos hu he) hT
  have hB := mul_pos (cBpos hu he) hT
  have hv := hvpos hu he
  obtain ⟨q01, q12, q02⟩ := WTriR_sq (gF u e) (hF1 hu he) _ _ hA hB
  refine ⟨(sq_eq_sq₀ dist_nonneg hB.le).mp q01, (sq_eq_sq₀ dist_nonneg hA.le).mp q12, ?_⟩
  refine (sq_eq_sq₀ dist_nonneg (by positivity)).mp ?_
  show dist ((WTriR (gF u e) _ _ _ _ _).pts 0) ((WTriR (gF u e) _ _ _ _ _).pts 2) ^ 2 = _
  rw [q02]; simp only [cA, cB, gF]; field_simp; ring

/-- `W_T` has the sides `(A T, T v³, B T)` on the edges `12, 20, 01` -/
theorem WT_hasSides (T : ℝ) (hT : 0 < T) :
    HasSides (WT hu he T hT) (cA u e * T) (T * (u + e) ^ 3) (cB u e * T) := by
  obtain ⟨d01, d12, d02⟩ := WT_sides hu he T hT
  exact ⟨Equiv.refl _, by simp only [Equiv.refl_apply]; exact d12,
    by simp only [Equiv.refl_apply]; rw [dist_comm]; exact d02, by simp only [Equiv.refl_apply]; exact d01⟩

/-- **A dissection with the sides of `W_T` and of the tile is a tiling of the frame region.** -/
theorem frame_of_dissection {T : ℝ} (hT : 0 < T) {N : ℕ} (D : CongruentDissection N)
    (hTs : HasSides D.target (cA u e * T) (T * (u + e) ^ 3) (cB u e * T))
    (hMs : HasSides D.model (cb u e) ((u + e) ^ 2) (ca u e)) :
    Nonempty (RTiling (Phi (gF u e) '' Wt (cA u e) (cB u e) T) (Mod hu he) N) := by
  obtain ⟨d01, d12, d02⟩ := WT_sides hu he T hT
  have hTU := congruent_of_hasSides' hTs d01 d12 d02
  obtain ⟨g, D', hD'T, hD'M, -⟩ := Erdos634.NormalPosition.exists_normal_position_congruent D hTU
  obtain ⟨m1, m2, m3⟩ := Mod_sides hu he
  have hMF : D.model.Congruent (Mod hu he) := congruent_of_hasSides' hMs m1 m2 m3
  exact ⟨{ tile := D'.tile
           covers := by rw [D'.covers, hD'T, carrier_WT]
           disj := D'.interiors_disjoint
           cong := fun i => (D'.tiles_congruent i).trans (by rw [hD'M]; exact hMF) }⟩

/-- the converse -/
theorem dissection_of_frame {T : ℝ} (hT : 0 < T) {N : ℕ}
    (R : RTiling (Phi (gF u e) '' Wt (cA u e) (cB u e) T) (Mod hu he) N) :
    ∃ D : CongruentDissection N, HasSides D.target (cA u e * T) (T * (u + e) ^ 3) (cB u e * T) ∧
      HasSides D.model (cb u e) ((u + e) ^ 2) (ca u e) :=
  ⟨toCD (T := WT hu he T hT) (RTiling.cast (carrier_WT hu he T hT).symm R), WT_hasSides hu he T hT,
    Mod_hasSides hu he⟩

theorem detQ {T : ℝ} (hT : 0 < T) : ((bX u e T).1 - (bQ u e T).1) * ((bP u e T).2 - (bQ u e T).2)
    - ((bP u e T).1 - (bQ u e T).1) * ((bX u e T).2 - (bQ u e T).2) ≠ 0 := by
  have hE : ((bX u e T).1 - (bQ u e T).1) * ((bP u e T).2 - (bQ u e T).2)
      - ((bP u e T).1 - (bQ u e T).1) * ((bX u e T).2 - (bQ u e T).2)
      = -(cA u e * T * (u * (u + e) ^ 2 * T)) := by
    simp only [bX, bP, bQ, cB, cC]; ring
  rw [hE]
  exact neg_ne_zero.mpr (mul_pos (mul_pos (cApos hu he) hT) (by positivity)).ne'

/-- **The beta lift, real parameters.**  A tiling of `W_T` and the tile at scale `T v` fill the base-β target at
scale `T`: the triangle with legs `T v³` and base `T u (3v² − u²)`. -/
theorem beta_lift_real {T : ℝ} (hT : 0 < T) {N k : ℕ} (hk0 : 0 < k) (hk : (k : ℝ) = T * (u + e))
    (R : RTiling (Phi (gF u e) '' Wt (cA u e) (cB u e) T) (Mod hu he) N) :
    ∃ D : CongruentDissection (N + k * k),
      HasSides D.target (T * (u + e) ^ 3) (T * (u + e) ^ 3) (cC u e * T) ∧
      HasSides D.model (ca u e) (cb u e) ((u + e) ^ 2) := by
  have hF := hF1 hu he
  have hf := hfr hu he
  have h1 : u ≠ 0 := hu.ne'
  have h2 : u + e ≠ 0 := (hvpos hu he).ne'
  have hv := hvpos hu he
  have hA : 0 < cA u e * T := mul_pos (cApos hu he) hT
  have hB : 0 < cB u e * T := mul_pos (cBpos hu he) hT
  have hgap : 0 < u * (u + e) ^ 2 * T := by positivity
  have hBC : cB u e * T < cC u e * T := by
    have hE : cC u e * T - cB u e * T = u * (u + e) ^ 2 * T := by simp only [cC, cB]; ring
    linarith
  have hC : 0 < cC u e * T := lt_trans hB hBC
  -- the lift triangle `Q X P`: the tile at scale `k = T v`
  have RQ0 : RTiling (Phi (gF u e) '' convexHull ℝ {bQ u e T, bX u e T, bP u e T}) (Mod hu he) (k * k) :=
    scaledRT (gF u e) hf (bQ u e T) (bX u e T) (bP u e T) k hk0 (detQ hu he hT) _
      (baseTri_cong _ _ (ca u e) (cb u e) (((u + e) ^ 2) ^ 2) (hapos hu he) (hbpos hu he) (hab_id hu he) _ _ _
        k hk0 _
        (by rw [hk]; simp only [bQ, bX, bP, ca, cb, cA, cB, cC, gF]; field_simp; ring)
        (by rw [hk]; simp only [bQ, bX, bP, ca, cb, cA, cB, cC, gF]; field_simp; ring)
        (by rw [hk]; simp only [bQ, bX, bP, ca, cb, cA, cB, cC, gF]; field_simp; ring))
  have hset : ({bQ u e T, bX u e T, bP u e T} : Set (ℝ × ℝ))
      = {((0 : ℝ), cB u e * T), (cA u e * T, cB u e * T), (cA u e * T, cC u e * T)} := by
    ext x
    simp only [bQ, bX, bP, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have RQ : RTiling (Phi (gF u e) '' QS (cA u e * T) (cB u e * T) (cC u e * T)) (Mod hu he) (k * k) :=
    RTiling.cast (by rw [hset, hull_QS _ _ _ hA hB hBC]) RQ0
  have RW : RTiling (Phi (gF u e) '' WS (cA u e * T) (cB u e * T)) (Mod hu he) N :=
    RTiling.cast (by rw [WS_eq _ _ _ hT]) R
  have hd : Disjoint (interior (Phi (gF u e) '' WS (cA u e * T) (cB u e * T)))
      (interior (Phi (gF u e) '' QS (cA u e * T) (cB u e * T) (cC u e * T))) :=
    disjoint_image' hf (interior_disj_snd (cB u e * T) (by rintro q ⟨_, b, _⟩; exact b)
      (by rintro q ⟨_, b, _⟩; exact b))
  have hcar : Phi (gF u e) '' WS (cA u e * T) (cB u e * T) ∪ Phi (gF u e) '' QS (cA u e * T) (cB u e * T) (cC u e * T)
      = (DTriR (gF u e) hF (cA u e * T) (cB u e * T) (cC u e * T) hA hC).carrier := by
    rw [← Set.image_union, ← DS_eq _ _ _ hA hB hBC]
    exact (carrier_DTriR _ hF _ _ _ hA hB hBC).symm
  obtain ⟨q01, q12, q02⟩ := DTriR_sq (gF u e) hF (cA u e * T) (cB u e * T) (cC u e * T) hA hC
  have hleg : 0 ≤ T * (u + e) ^ 3 := by positivity
  refine ⟨toCD (T := DTriR (gF u e) hF (cA u e * T) (cB u e * T) (cC u e * T) hA hC)
    (RTiling.cast hcar (union RW RQ hd)), ⟨Equiv.refl _, ?_, ?_, ?_⟩,
    hasSides_rot (hasSides_rot (Mod_hasSides hu he))⟩
  · simp only [Equiv.refl_apply]
    refine (sq_eq_sq₀ dist_nonneg hleg).mp ?_
    show dist ((DTriR (gF u e) hF _ _ _ hA hC).pts 1) ((DTriR (gF u e) hF _ _ _ hA hC).pts 2) ^ 2 = _
    rw [q12]; simp only [cA, cB, cC, gF]; field_simp; ring
  · simp only [Equiv.refl_apply]
    rw [dist_comm]
    refine (sq_eq_sq₀ dist_nonneg hleg).mp ?_
    show dist ((DTriR (gF u e) hF _ _ _ hA hC).pts 0) ((DTriR (gF u e) hF _ _ _ hA hC).pts 2) ^ 2 = _
    rw [q02]; simp only [cA, cB, cC, gF]; field_simp; ring
  · simp only [Equiv.refl_apply]
    exact (sq_eq_sq₀ dist_nonneg hC.le).mp q01

end convert

/-! ## Naturals -/

/-- **`W_T` of the member `(u, v)` has a tiling**: the triangle with sides `T v (v² − u²)`, `T u (2v² − u²)`, `T v³`
(angles `β, 2α, α + β`) is cut into `(2v² − u²) T²` congruent triangles with sides `(uv, v² − u², v²)`. -/
def WTilable (u v T : ℕ) : Prop :=
  ∃ D : CongruentDissection ((2 * v ^ 2 - u ^ 2) * T ^ 2),
    HasSides D.target ((T : ℝ) * ((v : ℝ) * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2)))
      ((T : ℝ) * ((u : ℝ) * (2 * (v : ℝ) ^ 2 - (u : ℝ) ^ 2))) ((T : ℝ) * (v : ℝ) ^ 3) ∧
    HasSides D.model ((u : ℝ) * v) ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) ((v : ℝ) ^ 2)

theorem pred_cast (n : ℕ) (hn : 0 < n) : ∃ k : ℕ, (k : ℝ) + 1 = (n : ℝ) :=
  ⟨n - 1, by have h := Nat.sub_add_cancel hn; exact_mod_cast h⟩

/-- the dissection form and the frame form are the same statement -/
theorem wTilable_iff_frame (u g T : ℕ) (hu : 0 < u) (hg : 0 < g) (hT : 0 < T) :
    WTilable u (u + g) T ↔
      Nonempty (RTiling (Phi (gF (u : ℝ) (g : ℝ)) '' Wt (cA (u : ℝ) (g : ℝ)) (cB (u : ℝ) (g : ℝ)) (T : ℝ))
        (Mod (u := (u : ℝ)) (e := (g : ℝ)) (Nat.cast_pos.mpr hu) (Nat.cast_pos.mpr hg))
        ((2 * (u + g) ^ 2 - u ^ 2) * T ^ 2)) := by
  have hu' : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hg' : (0 : ℝ) < g := Nat.cast_pos.mpr hg
  have hT' : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  constructor
  · rintro ⟨D, hTs, hMs⟩
    refine frame_of_dissection hu' hg' hT' D ?_ ?_
    · exact hasSides_congr (hasSides_rot (hasSides_swap hTs)) (by simp only [cA]; pc_ring) (by pc_ring)
        (by simp only [cB]; pc_ring)
    · exact hasSides_congr (hasSides_rot hMs) (by simp only [cb]; pc_ring) (by pc_ring) (by simp only [ca]; pc_ring)
  · rintro ⟨R⟩
    obtain ⟨D, hTs, hMs⟩ := dissection_of_frame hu' hg' hT' R
    exact ⟨D, hasSides_congr (hasSides_rot (hasSides_swap hTs)) (by simp only [cA]; pc_ring)
        (by simp only [cB]; pc_ring) (by pc_ring),
      hasSides_congr (hasSides_rot (hasSides_rot hMs)) (by simp only [ca]; pc_ring) (by simp only [cb]; pc_ring)
        (by pc_ring)⟩

/-- **The collar step**: `W_T → W_{T+u}` for the member `(u, u + g)` and every `T = g + s`, `s ≥ 1`. -/
theorem collar_nat (u g s : ℕ) (hu : 0 < u) (hg : 0 < g) (hs : 0 < s) (h : WTilable u (u + g) (g + s)) :
    WTilable u (u + g) (g + s + u) := by
  have hu' : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hg' : (0 : ℝ) < g := Nat.cast_pos.mpr hg
  have hs' : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  obtain ⟨R⟩ := (wTilable_iff_frame u g (g + s) hu hg (by omega)).mp h
  have hct : ((g + s : ℕ) : ℝ) = ct (g : ℝ) (s : ℝ) := Nat.cast_add g s
  have hTT : ((g + s + u : ℕ) : ℝ) = ct (g : ℝ) (s : ℝ) + (u : ℝ) := by rw [Nat.cast_add, hct]
  have R0 : RTiling (Phi (gF (u : ℝ) (g : ℝ)) '' Wt (cA (u : ℝ) (g : ℝ)) (cB (u : ℝ) (g : ℝ)) (ct (g : ℝ) (s : ℝ)))
      (Mod hu' hg') ((2 * (u + g) ^ 2 - u ^ 2) * (g + s) ^ 2) := RTiling.cast (by rw [hct]) R
  have h1 : u ^ 2 ≤ 2 * (u + g) ^ 2 := by nlinarith [Nat.zero_le g, Nat.zero_le u]
  have hn0 : (((2 * (u + g) ^ 2 - u ^ 2) * (g + s) ^ 2 : ℕ) : ℝ) = cQ (u : ℝ) (g : ℝ) * ct (g : ℝ) (s : ℝ) ^ 2 := by
    rw [Nat.cast_mul, Nat.cast_sub h1]; simp only [cQ, ct]; pc_ring
  obtain ⟨k1, hk1⟩ := pred_cast (u * (u + g)) (Nat.mul_pos hu (by omega))
  obtain ⟨l1, hl1⟩ := pred_cast ((u + g) * (g + s)) (Nat.mul_pos (by omega) (by omega))
  obtain ⟨k2, hk2⟩ := pred_cast (g * (2 * u + g)) (Nat.mul_pos hg (by omega))
  obtain ⟨l2, hl2⟩ := pred_cast (u * s) (Nat.mul_pos hu hs)
  obtain ⟨k6, hk6⟩ := pred_cast (g * (u + g)) (Nat.mul_pos hg (by omega))
  obtain ⟨l6, hl6⟩ := pred_cast (u * g) (Nat.mul_pos hu hg)
  obtain ⟨l7, hl7⟩ := pred_cast (u ^ 2) (pow_pos hu 2)
  obtain ⟨N, D, hN, hM, hT⟩ := collar_real hu' hg' hs' _ k1 l1 k2 l2 (u * (u + g)) (u * g) k6 l6 l6 l7 hn0
    (hk1.trans (by simp only [ca]; pc_ring)) (hl1.trans (by simp only [ct]; pc_ring))
    (hk2.trans (by simp only [cb]; pc_ring)) (hl2.trans (by pc_ring))
    (Nat.mul_pos hu (by omega)) (by simp only [ca]; pc_ring) (Nat.mul_pos hu hg) (by pc_ring)
    (hk6.trans (by pc_ring)) (hl6.trans (by pc_ring)) (hl6.trans (by pc_ring)) (hl7.trans (by pc_ring)) R0
  have hNn : N = (2 * (u + g) ^ 2 - u ^ 2) * (g + s + u) ^ 2 := by
    have : (N : ℝ) = (((2 * (u + g) ^ 2 - u ^ 2) * (g + s + u) ^ 2 : ℕ) : ℝ) := by
      rw [hN, Nat.cast_mul, Nat.cast_sub h1]; simp only [cQ, ct]; pc_ring
    exact_mod_cast this
  subst hNn
  have hpos : (0 : ℝ) < ct (g : ℝ) (s : ℝ) + (u : ℝ) := by have := ct_pos hu' hg' hs'; linarith
  have hc : D.target.carrier
      = Phi (gF (u : ℝ) (g : ℝ)) '' Wt (cA (u : ℝ) (g : ℝ)) (cB (u : ℝ) (g : ℝ)) ((g + s + u : ℕ) : ℝ) := by
    rw [hT, carrier_tgt, hTT]
    show Phi (gF (u : ℝ) (g : ℝ)) '' WS (cA (u : ℝ) (g : ℝ) * (ct (g : ℝ) (s : ℝ) + (u : ℝ)))
      (cB (u : ℝ) (g : ℝ) * (ct (g : ℝ) (s : ℝ) + (u : ℝ))) = _
    rw [WS_eq _ _ _ hpos]
  exact (wTilable_iff_frame u g (g + s + u) hu hg (by omega)).mpr
    ⟨RegionTiling.remodel (RTiling.cast hc (ofCD D)) (by rw [hM]; exact Erdos634.Geometry.Tri.Congruent.refl _)⟩

/-- **The seed**: `W_v` of every member (the seed credited to M. Beeson; `WSeedG.w_seed`). -/
theorem wTilable_seed (u v : ℕ) (hu : 1 ≤ u) (huv : u < v) : WTilable u v v := by
  have hN : v ^ 2 * (2 * v ^ 2 - u ^ 2) = (2 * v ^ 2 - u ^ 2) * v ^ 2 := Nat.mul_comm _ _
  have key := Erdos634.Draft.WSeedG.w_seed u v hu huv
  rw [hN] at key
  obtain ⟨D, hT, hM⟩ := key
  exact ⟨D, hasSides_congr hT (by ring) (by ring) (by ring), hM⟩

/-- **Multiples**: a tiling of `W_T` gives one of `W_{kT}` (`Ladder.ladder`). -/
theorem wTilable_mul {u v T : ℕ} (h : WTilable u v T) {k : ℕ} (hk : 0 < k) : WTilable u v (k * T) := by
  obtain ⟨D, ⟨τ, t0, t1, t2⟩, hM⟩ := h
  obtain ⟨hind, heta⟩ := Erdos634.Draft.RWEast.tri_eta D.target
  obtain ⟨E, hEt, hEm⟩ := Erdos634.Ladder.ladder (D.target.pts 0) (D.target.pts 1) (D.target.pts 2) hind D heta k hk
  have hd := Erdos634.Draft.RWEast.dist_bigTri (D.target.pts 0) (D.target.pts 1) (D.target.pts 2) hind k hk
  have hvec : ∀ i : Fin 3, (![D.target.pts 0, D.target.pts 1, D.target.pts 2] : Fin 3 → Plane) i = D.target.pts i := by
    intro i; fin_cases i <;> rfl
  have hd' : ∀ i j : Fin 3,
      dist (E.target.pts i) (E.target.pts j) = (k : ℝ) * dist (D.target.pts i) (D.target.pts j) := by
    intro i j
    rw [hEt, hd i j, hvec i, hvec j]
  have key : ∃ E : CongruentDissection (k * k * ((2 * v ^ 2 - u ^ 2) * T ^ 2)),
      HasSides E.target (((k * T : ℕ) : ℝ) * ((v : ℝ) * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2)))
        (((k * T : ℕ) : ℝ) * ((u : ℝ) * (2 * (v : ℝ) ^ 2 - (u : ℝ) ^ 2))) (((k * T : ℕ) : ℝ) * (v : ℝ) ^ 3) ∧
      HasSides E.model ((u : ℝ) * v) ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) ((v : ℝ) ^ 2) := by
    refine ⟨E, ⟨τ, ?_, ?_, ?_⟩, by rw [hEm]; exact hM⟩
    · rw [hd', t0]; pc_ring
    · rw [hd', t1]; pc_ring
    · rw [hd', t2]; pc_ring
  have hN : k * k * ((2 * v ^ 2 - u ^ 2) * T ^ 2) = (2 * v ^ 2 - u ^ 2) * (k * T) ^ 2 := by ring
  rw [hN] at key
  exact key

/-- **`W` of every member at every scale `j v + i u`, `j ≥ 1`.** -/
theorem wTilable_lin (u v : ℕ) (hu : 1 ≤ u) (huv : u < v) (j : ℕ) (hj : 1 ≤ j) (i : ℕ) :
    WTilable u v (j * v + i * u) := by
  obtain ⟨g, rfl⟩ : ∃ g, v = u + g := ⟨v - u, by omega⟩
  have hg : 0 < g := by omega
  induction i with
  | zero =>
    have e0 : j * (u + g) + 0 * u = j * (u + g) := by rw [Nat.zero_mul, Nat.add_zero]
    rw [e0]
    exact wTilable_mul (wTilable_seed u (u + g) hu huv) hj
  | succ i ih =>
    have hP : u + g ≤ j * (u + g) := Nat.le_mul_of_pos_left _ hj
    obtain ⟨s, hs⟩ : ∃ s, j * (u + g) + i * u = g + s := ⟨j * (u + g) + i * u - g, by omega⟩
    have hs0 : 0 < s := by omega
    rw [hs] at ih
    have h := collar_nat u g s hu hg hs0 ih
    have e2 : g + s + u = j * (u + g) + (i + 1) * u := by rw [← hs]; ring
    rwa [e2] at h

/-- **The beta lift**: a tiling of `W_T` gives the base-β target at scale `T`. -/
theorem betaTilable_of_wTilable (u g T : ℕ) (hu : 0 < u) (hg : 0 < g) (hT : 0 < T) (h : WTilable u (u + g) T) :
    BetaTilable u (u + g) T := by
  have hu' : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hg' : (0 : ℝ) < g := Nat.cast_pos.mpr hg
  have hT' : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  obtain ⟨R⟩ := (wTilable_iff_frame u g T hu hg hT).mp h
  obtain ⟨D, hTs, hMs⟩ := beta_lift_real hu' hg' hT' (k := T * (u + g)) (Nat.mul_pos hT (by omega))
    (by pc_ring) R
  exact ⟨_, D, hasSides_congr hTs (by pc_ring) (by pc_ring) (by simp only [cC]; pc_ring),
    hasSides_congr hMs (by simp only [ca]; pc_ring) (by simp only [cb]; pc_ring) (by pc_ring)⟩

/-- **The base-β target of every member `(u, v)` has a tiling at every scale `j v + i u`, `j ≥ 1`**: the isosceles
triangle with legs `M v³` and base `M u (3v² − u²)` is cut into congruent triangles with sides `(uv, v² − u², v²)`. -/
theorem betaTilable_lin (u v : ℕ) (hu : 1 ≤ u) (huv : u < v) (j : ℕ) (hj : 1 ≤ j) (i : ℕ) :
    BetaTilable u v (j * v + i * u) := by
  have hw := wTilable_lin u v hu huv j hj i
  obtain ⟨g, rfl⟩ : ∃ g, v = u + g := ⟨v - u, by omega⟩
  have hP : u + g ≤ j * (u + g) := Nat.le_mul_of_pos_left _ hj
  exact betaTilable_of_wTilable u g _ hu (by omega) (by omega) hw

/-- **Every large scale.**  For coprime `u < v` the base-β target has a tiling at every scale
`M ≥ (u − 1)(v − 1) + v` (the scales `v + a u + b v`; Sylvester's bound for the semigroup `⟨u, v⟩`). -/
theorem betaTilable_large (u v : ℕ) (hu : 1 ≤ u) (huv : u < v) (hco : Nat.Coprime u v) (M : ℕ)
    (hM : (u - 1) * (v - 1) + v ≤ M) : BetaTilable u v M := by
  obtain ⟨a, b, hab⟩ := Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le u v (M - v)
    (by rw [Nat.Coprime.gcd_eq_one hco]; exact one_dvd _) (by simp only [Nat.pred_eq_sub_one]; omega)
  have hMe : M = (b + 1) * v + a * u := by
    have h2 : a * u + b * v + v = M := by omega
    rw [← h2]; ring
  rw [hMe]
  exact betaTilable_lin u v hu huv (b + 1) (by omega) a

/-- the same for `W` -/
theorem wTilable_large (u v : ℕ) (hu : 1 ≤ u) (huv : u < v) (hco : Nat.Coprime u v) (M : ℕ)
    (hM : (u - 1) * (v - 1) + v ≤ M) : WTilable u v M := by
  obtain ⟨a, b, hab⟩ := Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le u v (M - v)
    (by rw [Nat.Coprime.gcd_eq_one hco]; exact one_dvd _) (by simp only [Nat.pred_eq_sub_one]; omega)
  have hMe : M = (b + 1) * v + a * u := by
    have h2 : a * u + b * v + v = M := by omega
    rw [← h2]; ring
  rw [hMe]
  exact wTilable_lin u v hu huv (b + 1) (by omega) a

/-- the threshold statement at every scale `M ≥ (u − 1)(v − 1) + v` -/
theorem thresholdAt_large (u v : ℕ) (hu : 1 ≤ u) (huv : u < v) (hco : Nat.Coprime u v) (M : ℕ)
    (hM : (u - 1) * (v - 1) + v ≤ M) : ThresholdAt u v M :=
  ⟨fun _ => by omega, fun _ => betaTilable_large u v hu huv hco M hM⟩

/-- the threshold statement at every scale `j v + i u`, `j ≥ 1` -/
theorem thresholdAt_lin (u v : ℕ) (hu : 1 ≤ u) (huv : u < v) (j : ℕ) (hj : 1 ≤ j) (i : ℕ) :
    ThresholdAt u v (j * v + i * u) :=
  ⟨fun _ => by have hP : v ≤ j * v := Nat.le_mul_of_pos_left _ hj
               omega, fun _ => betaTilable_lin u v hu huv j hj i⟩

/-- **The member `(2, 3)`**: a tiling at every scale `M ≥ 3` except possibly `M = 4`. -/
theorem betaTilable_2_3 (M : ℕ) (hM : 3 ≤ M) (h4 : M ≠ 4) : BetaTilable 2 3 M := by
  by_cases h5 : 5 ≤ M
  · exact betaTilable_large 2 3 (by norm_num) (by norm_num) (by decide) M (by omega)
  · have h3 : M = 3 := by omega
    subst h3
    exact betaTilable_lin 2 3 (by norm_num) (by norm_num) 1 le_rfl 0

end Erdos634.Draft.CollarG

#print axioms Erdos634.Draft.CollarG.collar_real
#print axioms Erdos634.Draft.CollarG.collar_nat
#print axioms Erdos634.Draft.CollarG.wTilable_lin
#print axioms Erdos634.Draft.CollarG.betaTilable_lin
#print axioms Erdos634.Draft.CollarG.betaTilable_large
#print axioms Erdos634.Draft.CollarG.betaTilable_2_3
