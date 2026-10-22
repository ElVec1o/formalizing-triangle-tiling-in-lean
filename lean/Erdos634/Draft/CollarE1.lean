/-
Draft/CollarE1.lean -- the +1 collar of the members `(1, f)`, and with it EVERY scale `M ≥ f`.

    theorem collar_step (g τn : ℕ) : WClosed (g + 2) _ (g + 2 + τn) → WClosed (g + 2) _ (g + 2 + τn + 1)
    theorem wClosed_ge (f : ℕ) (hf : 2 ≤ f) : ∀ M, f ≤ M → WClosed f hf M
    theorem betaTilable_e1 (f : ℕ) (hf : 2 ≤ f) : ∀ M, f ≤ M → BetaTilable 1 f M

So for every `f ≥ 2` and every `M ≥ f` the triangle `W_M` (sides `M f (f² − 1)`, `M (2f² − 1)`, `M f³`) and the
base-β target `T_M(1, f)` (legs `M f³`, base `M (3f² − 1)`) are cut into copies of the tile `(f, f² − 1, f²)`: the half
"`M ≥ f` gives a tiling" of the threshold statement, for the whole family `e = 1`.

THE CONSTRUCTION IS NOT OURS.  The collar (a strip of parallelograms and a cap of six pieces) is D. Paliy's, "A
six-block cap for every primitive W and beta tile" (3 October 2026, unrefereed), which states the existence of these
tilings; the seed at scale `f` is the one his notes credit to M. Beeson.  What is added here is a formal proof.
Layout and all linear bounds: `Draft.CollarE1Geom` (generated).  Here: the tilings of the nine regions (four scaled
triangles, two brick rectangles, two lattice parallelograms carried by isometries, and the given tiling of `W_T`),
the packing lemma with the area identity, and the induction.
Constructive side of the composite problem; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.CollarE1Geom
import Erdos634.Draft.WClosedBase
import Erdos634.SssCongruent

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Rect RTiling.cast RTiling.castN)

namespace Erdos634.Draft.CollarE1
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling
open Erdos634.Draft.S2G (triC triC_pts carrier_triC brickL brickU brick_rt cong_U_cell grid scaledRT baseTri
  baseTri_cong vol_triC sq_Phi' dPhi' disjoint_image' f_ne)
open Erdos634.Draft.BrickGridF (shift_rect)
open Erdos634.SssCongruent (sssIso sssIso_apply ev evMap evMap_basis)
open Erdos634.Draft.WAddF (Wt WClosed)
open Erdos634.Draft.WtoDeltaF (WS)
open Erdos634.Draft.FDBBaseBetaE1 (HasSides hasSides_rot hasSides_swap congruent_of_hasSides')
open Erdos634.Draft.UniformThreshold (BetaTilable hasSides_congr)

/-! ## Tools -/

/-- the SSS isometry in barycentric form -/
theorem sssIso_bary {T U : Erdos634.Geometry.Tri}
    (hd : ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts i) (U.pts j)) (s u : ℝ) :
    sssIso hd (T.pts 0 + s • (T.pts 1 - T.pts 0) + u • (T.pts 2 - T.pts 0))
      = U.pts 0 + s • (U.pts 1 - U.pts 0) + u • (U.pts 2 - U.pts 0) := by
  rw [sssIso_apply]
  have e : T.pts 0 + s • (T.pts 1 - T.pts 0) + u • (T.pts 2 - T.pts 0) + -T.pts 0
      = s • ev T 0 + u • ev T 1 := by
    simp only [ev, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    abel
  rw [e, map_add, map_smul, map_smul, evMap_basis, evMap_basis]
  simp only [ev, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  abel

/-- `Φ` is linear: affine combinations -/
theorem Phi_comb (f : ℝ) (A B C : ℝ × ℝ) (s u : ℝ) :
    Phi f A + s • (Phi f B - Phi f A) + u • (Phi f C - Phi f A)
      = Phi f (A + s • (B - A) + u • (C - A)) := by
  ext i
  fin_cases i <;> simp [Phi_apply0, Phi_apply1] <;> ring

theorem dPhi2 {f g : ℝ} (a b c d : ℝ × ℝ)
    (h : dist (Phi f a) (Phi f b) ^ 2 = dist (Phi g c) (Phi g d) ^ 2) :
    dist (Phi f a) (Phi f b) = dist (Phi g c) (Phi g d) :=
  Erdos634.Draft.SumTwoSquares.eqsq dist_nonneg dist_nonneg h

theorem mem_Pg (P0 E1 E2 : ℝ × ℝ) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    P0 + s • E1 + t • E2 ∈ Pg P0 E1 E2 := by
  show P0 + s • E1 + t • E2 ∈ convexHull ℝ ({P0, P0 + E1, P0 + E1 + E2, P0 + E2} : Set (ℝ × ℝ))
  have hc := convex_convexHull ℝ ({P0, P0 + E1, P0 + E1 + E2, P0 + E2} : Set (ℝ × ℝ))
  have m0 : P0 ∈ convexHull ℝ ({P0, P0 + E1, P0 + E1 + E2, P0 + E2} : Set (ℝ × ℝ)) :=
    subset_convexHull ℝ _ (by simp)
  have m1 : P0 + E1 ∈ convexHull ℝ ({P0, P0 + E1, P0 + E1 + E2, P0 + E2} : Set (ℝ × ℝ)) :=
    subset_convexHull ℝ _ (by simp)
  have m2 : P0 + E1 + E2 ∈ convexHull ℝ ({P0, P0 + E1, P0 + E1 + E2, P0 + E2} : Set (ℝ × ℝ)) :=
    subset_convexHull ℝ _ (by simp)
  have m3 : P0 + E2 ∈ convexHull ℝ ({P0, P0 + E1, P0 + E1 + E2, P0 + E2} : Set (ℝ × ℝ)) :=
    subset_convexHull ℝ _ (by simp)
  have u := hc m0 m1 (by linarith : (0 : ℝ) ≤ 1 - s) hs0 (by ring)
  have v := hc m3 m2 (by linarith : (0 : ℝ) ≤ 1 - s) hs0 (by ring)
  have z := hc u v (by linarith : (0 : ℝ) ≤ 1 - t) ht0 (by ring)
  have e : (1 - t) • ((1 - s) • P0 + s • (P0 + E1)) + t • ((1 - s) • (P0 + E2) + s • (P0 + E1 + E2))
      = P0 + s • E1 + t • E2 := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring
  rw [e] at z
  exact z

/-- the lower cell halves of the `(A, B)` and of the `(B, A)` brick are congruent -/
theorem cong_swap {f : ℝ} (hf : 1 < 4 * f ^ 2) (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    (brickL f hf A B hA hB).Congruent (brickL f hf B A hB hA) := by
  have h0 : f ≠ 0 := f_ne hf
  refine ((brickL f hf A B hA hB).congruent_relabel (Equiv.swap (0 : Fin 3) 2)).trans ?_
  refine Erdos634.SssCongruent.congruent_of_dist_three ?_ ?_ ?_ <;>
    simp only [Erdos634.Geometry.Tri.relabel, brickL, triC_pts] <;>
    (refine dPhi' _ _ _ _ ?_; rw [sq_Phi' hf, sq_Phi' hf]; field_simp; ring)

/-- **A grid of one frame, carried by an isometry into another frame.**  The cell `[0, α₁] × [0, α₂]` of the frame `φ`
and the triangle `P₀, P₀ + e₁, P₀ + e₂` of the frame `F` have the same three side lengths. -/
theorem mapped_grid {φ F : ℝ} (hφ : 1 < 4 * φ ^ 2) (hF : 1 < 4 * F ^ 2) {α1 α2 : ℝ} (h1 : 0 < α1)
    (h2 : 0 < α2) {M : Erdos634.Geometry.Tri} {n : ℕ} (Rb : RTiling (Phi φ '' Rect 0 α1 0 α2) M n) (k l : ℕ)
    (P0 e1 e2 : ℝ × ℝ) (hdet : e1.1 * e2.2 - e2.1 * e1.2 ≠ 0)
    (H1 : e1.1 ^ 2 + e1.2 ^ 2 + e1.1 * e1.2 / F = α1 ^ 2)
    (H2 : e2.1 ^ 2 + e2.2 ^ 2 + e2.1 * e2.2 / F = α2 ^ 2)
    (H12 : (e2.1 - e1.1) ^ 2 + (e2.2 - e1.2) ^ 2 + (e2.1 - e1.1) * (e2.2 - e1.2) / F
      = α1 ^ 2 + α2 ^ 2 - α1 * α2 / φ) :
    ∃ S : Set Plane, Nonempty (RTiling S M (n * (k + 1) * (l + 1))) ∧
      S ⊆ Phi F '' Pg P0 (((k : ℝ) + 1) • e1) (((l : ℝ) + 1) • e2) := by
  have hφ0 : φ ≠ 0 := f_ne hφ
  have hF0 : F ≠ 0 := f_ne hF
  have dT : (((α1, (0 : ℝ)) : ℝ × ℝ).1 - ((0 : ℝ), (0 : ℝ)).1) * (((0 : ℝ), α2).2 - ((0 : ℝ), (0 : ℝ)).2)
      - ((((0 : ℝ), α2) : ℝ × ℝ).1 - ((0 : ℝ), (0 : ℝ)).1) * ((α1, (0 : ℝ)).2 - ((0 : ℝ), (0 : ℝ)).2) ≠ 0 := by
    have e : (((α1, (0 : ℝ)) : ℝ × ℝ).1 - ((0 : ℝ), (0 : ℝ)).1) * (((0 : ℝ), α2).2 - ((0 : ℝ), (0 : ℝ)).2)
      - ((((0 : ℝ), α2) : ℝ × ℝ).1 - ((0 : ℝ), (0 : ℝ)).1) * ((α1, (0 : ℝ)).2 - ((0 : ℝ), (0 : ℝ)).2)
        = α1 * α2 := by ring
    rw [e]; exact (mul_pos h1 h2).ne'
  have dU : ((P0 + e1).1 - P0.1) * ((P0 + e2).2 - P0.2) - ((P0 + e2).1 - P0.1) * ((P0 + e1).2 - P0.2) ≠ 0 := by
    have e : ((P0 + e1).1 - P0.1) * ((P0 + e2).2 - P0.2) - ((P0 + e2).1 - P0.1) * ((P0 + e1).2 - P0.2)
        = e1.1 * e2.2 - e2.1 * e1.2 := by
      simp only [Prod.fst_add, Prod.snd_add]; ring
    rw [e]; exact hdet
  let T : Erdos634.Geometry.Tri := triC φ hφ (0, 0) (α1, 0) (0, α2) dT
  let U : Erdos634.Geometry.Tri := triC F hF P0 (P0 + e1) (P0 + e2) dU
  have hT0 : T.pts 0 = Phi φ (0, 0) := by show (triC φ hφ _ _ _ dT).pts 0 = _; rw [triC_pts]; rfl
  have hT1 : T.pts 1 = Phi φ (α1, 0) := by show (triC φ hφ _ _ _ dT).pts 1 = _; rw [triC_pts]; rfl
  have hT2 : T.pts 2 = Phi φ (0, α2) := by show (triC φ hφ _ _ _ dT).pts 2 = _; rw [triC_pts]; rfl
  have hU0 : U.pts 0 = Phi F P0 := by show (triC F hF _ _ _ dU).pts 0 = _; rw [triC_pts]; rfl
  have hU1 : U.pts 1 = Phi F (P0 + e1) := by show (triC F hF _ _ _ dU).pts 1 = _; rw [triC_pts]; rfl
  have hU2 : U.pts 2 = Phi F (P0 + e2) := by show (triC F hF _ _ _ dU).pts 2 = _; rw [triC_pts]; rfl
  have d01 : dist (T.pts 0) (T.pts 1) = dist (U.pts 0) (U.pts 1) := by
    rw [hT0, hT1, hU0, hU1]
    refine dPhi2 _ _ _ _ ?_
    rw [sq_Phi' hφ, sq_Phi' hF]
    simp only [Prod.fst_add, Prod.snd_add]
    linear_combination (-1 : ℝ) * H1
  have d02 : dist (T.pts 0) (T.pts 2) = dist (U.pts 0) (U.pts 2) := by
    rw [hT0, hT2, hU0, hU2]
    refine dPhi2 _ _ _ _ ?_
    rw [sq_Phi' hφ, sq_Phi' hF]
    simp only [Prod.fst_add, Prod.snd_add]
    linear_combination (-1 : ℝ) * H2
  have d12 : dist (T.pts 1) (T.pts 2) = dist (U.pts 1) (U.pts 2) := by
    rw [hT1, hT2, hU1, hU2]
    refine dPhi2 _ _ _ _ ?_
    rw [sq_Phi' hφ, sq_Phi' hF]
    simp only [Prod.fst_add, Prod.snd_add]
    linear_combination (-1 : ℝ) * H12
  have htri : ∀ y : Fin 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide
  have hdist : ∀ i j : Fin 3, dist (T.pts i) (T.pts j) = dist (U.pts i) (U.pts j) := by
    intro i j
    rcases htri i with rfl | rfl | rfl <;> rcases htri j with rfl | rfl | rfl <;>
      first
        | (simp only [dist_self])
        | exact d01
        | exact d02
        | exact d12
        | (rw [dist_comm (T.pts 1) (T.pts 0), dist_comm (U.pts 1) (U.pts 0)]; exact d01)
        | (rw [dist_comm (T.pts 2) (T.pts 0), dist_comm (U.pts 2) (U.pts 0)]; exact d02)
        | (rw [dist_comm (T.pts 2) (T.pts 1), dist_comm (U.pts 2) (U.pts 1)]; exact d12)
  let g : Plane ≃ᵢ Plane := sssIso hdist
  have R := grid hφ h1 h2 Rb k l
  refine ⟨g '' (Phi φ '' Rect 0 (α1 * ((k : ℝ) + 1)) 0 (α2 * ((l : ℝ) + 1))), ⟨RegionTiling.map R g⟩, ?_⟩
  rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
  obtain ⟨hq1, hq2, hq3, hq4⟩ := hq
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hl : (0 : ℝ) < (l : ℝ) + 1 := by positivity
  have eq : ((0 : ℝ), (0 : ℝ)) + (q.1 / α1) • ((α1, (0 : ℝ)) - ((0 : ℝ), (0 : ℝ)))
      + (q.2 / α2) • (((0 : ℝ), α2) - ((0 : ℝ), (0 : ℝ))) = q := by
    ext
    · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]; field_simp; ring
    · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]; field_simp; ring
  have e1' : Phi φ q = T.pts 0 + (q.1 / α1) • (T.pts 1 - T.pts 0) + (q.2 / α2) • (T.pts 2 - T.pts 0) := by
    rw [hT0, hT1, hT2, Phi_comb, eq]
  have e2' : g (Phi φ q) = Phi F (P0 + (q.1 / α1) • e1 + (q.2 / α2) • e2) := by
    show sssIso hdist (Phi φ q) = _
    rw [e1', sssIso_bary hdist, hU0, hU1, hU2, Phi_comb]
    congr 1
    ext
    · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]; ring
    · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]; ring
  refine ⟨P0 + (q.1 / α1 / ((k : ℝ) + 1)) • (((k : ℝ) + 1) • e1) + (q.2 / α2 / ((l : ℝ) + 1)) • (((l : ℝ) + 1) • e2),
    mem_Pg _ _ _ (div_nonneg (div_nonneg hq1 h1.le) hk.le) ?_ (div_nonneg (div_nonneg hq3 h2.le) hl.le) ?_, ?_⟩
  · rw [div_le_one hk, div_le_iff₀ h1]; linarith [mul_comm α1 ((k : ℝ) + 1)]
  · rw [div_le_one hl, div_le_iff₀ h2]; linarith [mul_comm α2 ((l : ℝ) + 1)]
  · show Phi F _ = g (Phi φ q)
    rw [e2']
    have ea : q.1 / α1 / ((k : ℝ) + 1) * ((k : ℝ) + 1) = q.1 / α1 := by field_simp
    have eb : q.2 / α2 / ((l : ℝ) + 1) * ((l : ℝ) + 1) = q.2 / α2 := by field_simp
    rw [smul_smul, smul_smul, ea, eb]

/-! ## The frame `F = d + 2`, the model, the cells -/

/-- the frame in which the cell `F × F²` has a diagonal of length `F² − 1` -/
noncomputable def φβ (d : ℝ) : ℝ := -(d + 2) ^ 3 / (3 * (d + 2) ^ 2 - 1)

section frame
variable {d : ℝ} (hd : 0 ≤ d)
include hd

theorem hfr : 1 < 4 * (d + 2) ^ 2 := by nlinarith [sq_nonneg d]
theorem hFpos : (0 : ℝ) < d + 2 := by linarith
theorem hbpos : (0 : ℝ) < (d + 2) ^ 2 - 1 := by nlinarith [sq_nonneg d]

/-- the model tile: edges `01, 12, 20` of lengths `F, F² − 1, F²` -/
noncomputable def Mod : Erdos634.Geometry.Tri :=
  brickL (d + 2) (hfr hd) (d + 2) ((d + 2) ^ 2 - 1) (hFpos hd) (hbpos hd)

theorem hab_id : (d + 2) ^ 2 + ((d + 2) ^ 2 - 1) ^ 2 + (d + 2) * ((d + 2) ^ 2 - 1) / (d + 2)
    = ((d + 2) ^ 2) ^ 2 := by
  have h : d + 2 ≠ 0 := (hFpos hd).ne'
  field_simp; ring

/-- the cell `F × (F² − 1)` -/
noncomputable def cellB : RTiling (Phi (d + 2) '' Rect 0 (d + 2) 0 ((d + 2) ^ 2 - 1)) (Mod hd) 2 :=
  brick_rt (d + 2) (hfr hd) (d + 2) ((d + 2) ^ 2 - 1) (hFpos hd) (hbpos hd) _
    (Erdos634.Geometry.Tri.Congruent.refl _) (cong_U_cell (hfr hd) _ _ _ _)

/-- the cell `(F² − 1) × F` -/
noncomputable def cellA : RTiling (Phi (d + 2) '' Rect 0 ((d + 2) ^ 2 - 1) 0 (d + 2)) (Mod hd) 2 :=
  brick_rt (d + 2) (hfr hd) ((d + 2) ^ 2 - 1) (d + 2) (hbpos hd) (hFpos hd) _
    (cong_swap (hfr hd) _ _ _ _) ((cong_U_cell (hfr hd) _ _ _ _).trans (cong_swap (hfr hd) _ _ _ _))

theorem h3pos : (0 : ℝ) < 3 * (d + 2) ^ 2 - 1 := by nlinarith [sq_nonneg d]

theorem hφβ : 1 < 4 * φβ d ^ 2 := by
  have h3 := h3pos hd
  have e : φβ d ^ 2 = ((d + 2) ^ 3) ^ 2 / (3 * (d + 2) ^ 2 - 1) ^ 2 := by
    simp only [φβ]; rw [neg_div, neg_sq, div_pow]
  rw [e, ← mul_div_assoc, lt_div_iff₀ (pow_pos h3 2)]
  have k : 4 * ((d + 2) ^ 3) ^ 2 - 1 * (3 * (d + 2) ^ 2 - 1) ^ 2
      = 4 * d ^ 6 + 48 * d ^ 5 + 231 * d ^ 4 + 568 * d ^ 3 + 750 * d ^ 2 + 504 * d + 135 := by ring
  have p : (0 : ℝ) < 4 * d ^ 6 + 48 * d ^ 5 + 231 * d ^ 4 + 568 * d ^ 3 + 750 * d ^ 2 + 504 * d + 135 := by
    positivity
  linarith

theorem cong_β : (brickL (φβ d) (hφβ hd) (d + 2) ((d + 2) ^ 2) (hFpos hd) (pow_pos (hFpos hd) 2)).Congruent
    (Mod hd) := by
  have h0 : d + 2 ≠ 0 := (hFpos hd).ne'
  have h3 : 3 * (d + 2) ^ 2 - 1 ≠ 0 := (h3pos hd).ne'
  refine ((brickL _ _ _ _ _ _).congruent_relabel (Equiv.swap (0 : Fin 3) 1)).trans ?_
  refine Erdos634.SssCongruent.congruent_of_dist_three ?_ ?_ ?_ <;>
    simp only [Erdos634.Geometry.Tri.relabel, Mod, brickL, triC_pts] <;>
    (refine dPhi2 _ _ _ _ ?_; rw [sq_Phi' (hφβ hd), sq_Phi' (hfr hd)]; simp only [φβ]; field_simp; ring)

/-- the cell `F × F²` of the frame `φβ` -/
noncomputable def cellC : RTiling (Phi (φβ d) '' Rect 0 (d + 2) 0 ((d + 2) ^ 2)) (Mod hd) 2 :=
  brick_rt (φβ d) (hφβ hd) (d + 2) ((d + 2) ^ 2) (hFpos hd) (pow_pos (hFpos hd) 2) _
    (cong_β hd) ((cong_U_cell (hφβ hd) _ _ _ _).trans (cong_β hd))

end frame

/-! ## The tilings of the regions -/
section pieces
variable {d τ : ℝ} (hd : 0 ≤ d) (hτ : 0 ≤ τ)
include hd hτ

/-- `Z1`: `F` columns of width `F² − 1`, `F t` rows of height `F` -/
noncomputable def RT1 (k l : ℕ) (hk : (k : ℝ) + 1 = d + 2) (hl : (l : ℝ) + 1 = (d + 2) * ct d τ) :
    RTiling (Phi (d + 2) '' Z1 d τ) (Mod hd) (2 * (k + 1) * (l + 1)) :=
  shift_rect (grid (hfr hd) (hbpos hd) (hFpos hd) (cellA hd) k l) (cA d * ct d τ) (cB d + cL d)
    (cA d * ct d τ + cA d) (cB d + cL d + (d + 2) ^ 2 * ct d τ)
    (by rw [hk]; simp only [cA]; ring) (by rw [hl]; ring)

/-- `Z2`: `F² − 1` columns of width `F`, `τ + 1` rows of height `F² − 1` -/
noncomputable def RT2 (k l : ℕ) (hk : (k : ℝ) + 1 = (d + 2) ^ 2 - 1) (hl : (l : ℝ) + 1 = τ + 1) :
    RTiling (Phi (d + 2) '' Z2 d τ) (Mod hd) (2 * (k + 1) * (l + 1)) :=
  shift_rect (grid (hfr hd) (hFpos hd) (hbpos hd) (cellB hd) k l) (cA d * ct d τ)
    (cB d + cL d + (d + 2) ^ 2 * ct d τ) (cA d * ct d τ + cA d) (cB d * (ct d τ + 1))
    (by rw [hk]; simp only [cA]; ring) (by rw [hl]; simp only [cB, cL, ct]; ring)

theorem det3 : ((qR d τ).1 - (qK d τ).1) * ((qO d τ).2 - (qK d τ).2)
    - ((qO d τ).1 - (qK d τ).1) * ((qR d τ).2 - (qK d τ).2) ≠ 0 := by
  have h2 : d + 2 ≠ 0 := (hFpos hd).ne'
  have e : ((qR d τ).1 - (qK d τ).1) * ((qO d τ).2 - (qK d τ).2)
      - ((qO d τ).1 - (qK d τ).1) * ((qR d τ).2 - (qK d τ).2)
      = -(d ^ 5 + 10 * d ^ 4 + 39 * d ^ 3 + 74 * d ^ 2 + 68 * d + 24) := by
    simp only [qR, qK, qO]; field_simp; ring
  rw [e]; exact neg_ne_zero.mpr (by positivity)

theorem det4 : ((qBp d τ).1 - (qJ d τ).1) * ((qE d τ).2 - (qJ d τ).2)
    - ((qE d τ).1 - (qJ d τ).1) * ((qBp d τ).2 - (qJ d τ).2) ≠ 0 := by
  have e : ((qBp d τ).1 - (qJ d τ).1) * ((qE d τ).2 - (qJ d τ).2)
      - ((qE d τ).1 - (qJ d τ).1) * ((qBp d τ).2 - (qJ d τ).2)
      = d ^ 5 + 8 * d ^ 4 + 24 * d ^ 3 + 34 * d ^ 2 + 23 * d + 6 := by
    simp only [qBp, qJ, qE]; ring
  rw [e]; positivity

theorem det5 : ((qX d τ).1 - (qO d τ).1) * ((qJ d τ).2 - (qO d τ).2)
    - ((qJ d τ).1 - (qO d τ).1) * ((qX d τ).2 - (qO d τ).2) ≠ 0 := by
  have h2 : d + 2 ≠ 0 := (hFpos hd).ne'
  have e : ((qX d τ).1 - (qO d τ).1) * ((qJ d τ).2 - (qO d τ).2)
      - ((qJ d τ).1 - (qO d τ).1) * ((qX d τ).2 - (qO d τ).2)
      = -(d ^ 5 + 8 * d ^ 4 + 24 * d ^ 3 + 34 * d ^ 2 + 23 * d + 6) := by
    simp only [qX, qO, qJ]; field_simp; ring
  rw [e]; exact neg_ne_zero.mpr (by positivity)

theorem det8 : ((qR d τ).1 - (qY d τ).1) * ((qE d τ).2 - (qY d τ).2)
    - ((qE d τ).1 - (qY d τ).1) * ((qR d τ).2 - (qY d τ).2) ≠ 0 := by
  have h2 : d + 2 ≠ 0 := (hFpos hd).ne'
  have e : ((qR d τ).1 - (qY d τ).1) * ((qE d τ).2 - (qY d τ).2)
      - ((qE d τ).1 - (qY d τ).1) * ((qR d τ).2 - (qY d τ).2)
      = d ^ 5 + 8 * d ^ 4 + 24 * d ^ 3 + 34 * d ^ 2 + 23 * d + 6 := by
    simp only [qR, qY, qE]; field_simp; ring
  rw [e]; positivity

/-- `Z3 = K R O`, the tile at scale `F` -/
noncomputable def RT3 (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = d + 2) :
    RTiling (Phi (d + 2) '' Z3 d τ) (Mod hd) (k * k) :=
  scaledRT (d + 2) (hfr hd) (qK d τ) (qR d τ) (qO d τ) k hk0 (det3 hd hτ) _
    (baseTri_cong _ _ (d + 2) ((d + 2) ^ 2 - 1) (((d + 2) ^ 2) ^ 2) (hFpos hd) (hbpos hd) (hab_id hd) _ _ _ k hk0 _
      (by have h2 : d + 2 ≠ 0 := (hFpos hd).ne'
          rw [hk]; simp only [qK, qR, qO]; field_simp; ring)
      (by have h2 : d + 2 ≠ 0 := (hFpos hd).ne'
          rw [hk]; simp only [qK, qR, qO]; field_simp; ring)
      (by have h2 : d + 2 ≠ 0 := (hFpos hd).ne'
          rw [hk]; simp only [qK, qR, qO]; field_simp; ring))

/-- `Z4 = J B' E`, the tile at scale `F − 1` -/
noncomputable def RT4 (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = d + 1) :
    RTiling (Phi (d + 2) '' Z4 d τ) (Mod hd) (k * k) :=
  scaledRT (d + 2) (hfr hd) (qJ d τ) (qBp d τ) (qE d τ) k hk0 (det4 hd hτ) _
    (baseTri_cong _ _ (d + 2) ((d + 2) ^ 2 - 1) (((d + 2) ^ 2) ^ 2) (hFpos hd) (hbpos hd) (hab_id hd) _ _ _ k hk0 _
      (by have h2 : d + 2 ≠ 0 := (hFpos hd).ne'
          rw [hk]; simp only [qJ, qBp, qE]; field_simp; ring)
      (by have h2 : d + 2 ≠ 0 := (hFpos hd).ne'
          rw [hk]; simp only [qJ, qBp, qE]; field_simp; ring)
      (by have h2 : d + 2 ≠ 0 := (hFpos hd).ne'
          rw [hk]; simp only [qJ, qBp, qE]; field_simp; ring))

/-- `Z5 = O X J`, the tile at scale `F − 1` -/
noncomputable def RT5 (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = d + 1) :
    RTiling (Phi (d + 2) '' Z5 d τ) (Mod hd) (k * k) :=
  scaledRT (d + 2) (hfr hd) (qO d τ) (qX d τ) (qJ d τ) k hk0 (det5 hd hτ) _
    (baseTri_cong _ _ (d + 2) ((d + 2) ^ 2 - 1) (((d + 2) ^ 2) ^ 2) (hFpos hd) (hbpos hd) (hab_id hd) _ _ _ k hk0 _
      (by have h2 : d + 2 ≠ 0 := (hFpos hd).ne'
          rw [hk]; simp only [qO, qX, qJ]; field_simp; ring)
      (by have h2 : d + 2 ≠ 0 := (hFpos hd).ne'
          rw [hk]; simp only [qO, qX, qJ]; field_simp; ring)
      (by have h2 : d + 2 ≠ 0 := (hFpos hd).ne'
          rw [hk]; simp only [qO, qX, qJ]; field_simp; ring))

/-- `Z8 = Y R E`, the tile at scale `F − 1` -/
noncomputable def RT8 (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = d + 1) :
    RTiling (Phi (d + 2) '' Z8 d τ) (Mod hd) (k * k) :=
  scaledRT (d + 2) (hfr hd) (qY d τ) (qR d τ) (qE d τ) k hk0 (det8 hd hτ) _
    (baseTri_cong _ _ (d + 2) ((d + 2) ^ 2 - 1) (((d + 2) ^ 2) ^ 2) (hFpos hd) (hbpos hd) (hab_id hd) _ _ _ k hk0 _
      (by have h2 : d + 2 ≠ 0 := (hFpos hd).ne'
          rw [hk]; simp only [qY, qR, qE]; field_simp; ring)
      (by have h2 : d + 2 ≠ 0 := (hFpos hd).ne'
          rw [hk]; simp only [qY, qR, qE]; field_simp; ring)
      (by have h2 : d + 2 ≠ 0 := (hFpos hd).ne'
          rw [hk]; simp only [qY, qR, qE]; field_simp; ring))

/-- `Z6`: the parallelogram `X R E J`, `(F² − F) × (F − 1)` cells of the lattice `(r, s)` -/
theorem RT6 (k l : ℕ) (hk : (k : ℝ) + 1 = (d + 2) * (d + 1)) (hl : (l : ℝ) + 1 = d + 1) :
    ∃ S : Set Plane, Nonempty (RTiling S (Mod hd) (2 * (k + 1) * (l + 1))) ∧ S ⊆ Phi (d + 2) '' Z6 d τ := by
  have h2 : d + 2 ≠ 0 := (hFpos hd).ne'
  have h := mapped_grid (hfr hd) (hfr hd) (hFpos hd) (hbpos hd) (cellB hd) k l (qX d τ) (vr d) (vs d)
    (by have e : (vr d).1 * (vs d).2 - (vs d).1 * (vr d).2 = -(d ^ 3 + 6 * d ^ 2 + 11 * d + 6) := by
          simp only [vr, vs]; field_simp; ring
        rw [e]; exact neg_ne_zero.mpr (by positivity))
    (by simp only [vr]; field_simp; ring) (by simp only [vs]; field_simp; ring)
    (by simp only [vr, vs]; field_simp; ring)
  rw [hk, hl] at h
  exact h

/-- `Z7`: the parallelogram `K C Y R`, `(F − 1) × 1` cells of the lattice `(p, w)` -/
theorem RT7 (k : ℕ) (hk : (k : ℝ) + 1 = d + 1) :
    ∃ S : Set Plane, Nonempty (RTiling S (Mod hd) (2 * (k + 1) * (0 + 1))) ∧ S ⊆ Phi (d + 2) '' Z7 d τ := by
  have h2 : d + 2 ≠ 0 := (hFpos hd).ne'
  have h3 : 3 * (d + 2) ^ 2 - 1 ≠ 0 := (h3pos hd).ne'
  have h := mapped_grid (hφβ hd) (hfr hd) (hFpos hd) (pow_pos (hFpos hd) 2) (cellC hd) k 0 (qK d τ) (vp d) (vw d)
    (by have e : (vp d).1 * (vw d).2 - (vw d).1 * (vp d).2 = -(d ^ 3 + 6 * d ^ 2 + 11 * d + 6) := by
          simp only [vp, vw]; ring
        rw [e]; exact neg_ne_zero.mpr (by positivity))
    (by simp only [vp]; field_simp; ring) (by simp only [vw]; field_simp; ring)
    (by simp only [vp, vw, φβ]; field_simp; ring)
  rw [hk] at h
  have e0 : ((0 : ℕ) : ℝ) + 1 = 1 := by norm_num
  rw [e0] at h
  exact h

end pieces

/-! ## Assembly: the nine regions fill `W_{t+1}` -/

/-- the regions in the plane; the two parallelograms are given as sets -/
noncomputable def regionOf (d τ : ℝ) (S6 S7 : Set Plane) : Fin 9 → Set Plane := fun i => match i with
  | ⟨0, _⟩ => Phi (d + 2) '' Z0 d τ
  | ⟨1, _⟩ => Phi (d + 2) '' Z1 d τ
  | ⟨2, _⟩ => Phi (d + 2) '' Z2 d τ
  | ⟨3, _⟩ => Phi (d + 2) '' Z3 d τ
  | ⟨4, _⟩ => Phi (d + 2) '' Z4 d τ
  | ⟨5, _⟩ => Phi (d + 2) '' Z5 d τ
  | ⟨6, _⟩ => S6
  | ⟨7, _⟩ => S7
  | ⟨8, _⟩ => Phi (d + 2) '' Z8 d τ
  | ⟨k + 9, h⟩ => absurd h (by omega)

def cnt (n0 n1 n2 n3 n4 n5 n6 n7 n8 : ℕ) : Fin 9 → ℕ := fun i => match i with
  | ⟨0, _⟩ => n0
  | ⟨1, _⟩ => n1
  | ⟨2, _⟩ => n2
  | ⟨3, _⟩ => n3
  | ⟨4, _⟩ => n4
  | ⟨5, _⟩ => n5
  | ⟨6, _⟩ => n6
  | ⟨7, _⟩ => n7
  | ⟨8, _⟩ => n8
  | ⟨k + 9, h⟩ => absurd h (by omega)

theorem sum_cnt (n0 n1 n2 n3 n4 n5 n6 n7 n8 : ℕ) :
    ∑ a, cnt n0 n1 n2 n3 n4 n5 n6 n7 n8 a = n0 + (n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_eight]
  rfl

section assemble
variable {d τ : ℝ} (hd : 0 ≤ d) (hτ : 0 ≤ τ)
include hd hτ

theorem hF1 : (1 : ℝ) < d + 2 := by linarith
theorem hu : 0 < cA d * (ct d τ + 1) := mul_pos (cA_pos hd hτ) (by have := ct_pos hd hτ; linarith)
theorem hv : 0 < cB d * (ct d τ + 1) := mul_pos (cB_pos hd hτ) (by have := ct_pos hd hτ; linarith)

/-- the target `W_{t+1}` -/
noncomputable def tgt : Erdos634.Geometry.Tri :=
  Erdos634.Draft.WClosedBase.WTriR (d + 2) (hF1 hd hτ) (cA d * (ct d τ + 1)) (cB d * (ct d τ + 1)) (hu hd hτ)
    (hv hd hτ)

theorem carrier_tgt : (tgt hd hτ).carrier = Phi (d + 2) '' ZT d τ :=
  Erdos634.Draft.WClosedBase.carrier_WTriR _ _ _ _ _ _

theorem Mod_sides : dist ((Mod hd).pts 0) ((Mod hd).pts 1) = d + 2 ∧
    dist ((Mod hd).pts 1) ((Mod hd).pts 2) = (d + 2) ^ 2 - 1 ∧
    dist ((Mod hd).pts 0) ((Mod hd).pts 2) = (d + 2) ^ 2 := by
  have hf := hfr hd
  have h2 : d + 2 ≠ 0 := (hFpos hd).ne'
  simp only [Mod, brickL, triC_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  refine ⟨?_, ?_, ?_⟩
  · refine (sq_eq_sq₀ dist_nonneg (hFpos hd).le).mp ?_
    rw [sq_Phi' hf]; ring
  · refine (sq_eq_sq₀ dist_nonneg (hbpos hd).le).mp ?_
    rw [sq_Phi' hf]; ring
  · refine (sq_eq_sq₀ dist_nonneg (by positivity)).mp ?_
    rw [sq_Phi' hf]; field_simp; ring

open MeasureTheory in
theorem volMod : volume (Mod hd).carrier
    = ENNReal.ofReal (|sD (d + 2) / (2 * (d + 2))| * ((d + 2) * ((d + 2) ^ 2 - 1)))
      * volume Erdos634.AreaDet.stdCarrier := by
  unfold Mod Erdos634.Draft.S2G.brickL
  rw [vol_triC]
  congr 2
  rw [abs_mul]
  congr 1
  have e : ((d + 2, (0 : ℝ)).1 - ((0 : ℝ), (0 : ℝ)).1) * ((d + 2, (d + 2) ^ 2 - 1).2 - ((0 : ℝ), (0 : ℝ)).2)
      - ((d + 2, (d + 2) ^ 2 - 1).1 - ((0 : ℝ), (0 : ℝ)).1) * ((d + 2, (0 : ℝ)).2 - ((0 : ℝ), (0 : ℝ)).2)
      = (d + 2) * ((d + 2) ^ 2 - 1) := by ring
  rw [e, abs_of_pos (mul_pos (hFpos hd) (hbpos hd))]

open MeasureTheory in
theorem vol_tgt : volume (tgt hd hτ).carrier
    = ENNReal.ofReal (|sD (d + 2) / (2 * (d + 2))| * (cA d * (ct d τ + 1) * (cB d * (ct d τ + 1))))
      * volume Erdos634.AreaDet.stdCarrier := by
  have hu' := hu hd hτ
  have hv' := hv hd hτ
  have hdet : (((cA d * (ct d τ + 1), cB d * (ct d τ + 1)) : ℝ × ℝ).1 - ((cA d * (ct d τ + 1), (0 : ℝ)) : ℝ × ℝ).1)
        * ((((0 : ℝ), cB d * (ct d τ + 1)) : ℝ × ℝ).2 - ((cA d * (ct d τ + 1), (0 : ℝ)) : ℝ × ℝ).2)
      - ((((0 : ℝ), cB d * (ct d τ + 1)) : ℝ × ℝ).1 - ((cA d * (ct d τ + 1), (0 : ℝ)) : ℝ × ℝ).1)
        * (((cA d * (ct d τ + 1), cB d * (ct d τ + 1)) : ℝ × ℝ).2 - ((cA d * (ct d τ + 1), (0 : ℝ)) : ℝ × ℝ).2)
      = cA d * (ct d τ + 1) * (cB d * (ct d τ + 1)) := by ring
  have hne : (((cA d * (ct d τ + 1), cB d * (ct d τ + 1)) : ℝ × ℝ).1 - ((cA d * (ct d τ + 1), (0 : ℝ)) : ℝ × ℝ).1)
        * ((((0 : ℝ), cB d * (ct d τ + 1)) : ℝ × ℝ).2 - ((cA d * (ct d τ + 1), (0 : ℝ)) : ℝ × ℝ).2)
      - ((((0 : ℝ), cB d * (ct d τ + 1)) : ℝ × ℝ).1 - ((cA d * (ct d τ + 1), (0 : ℝ)) : ℝ × ℝ).1)
        * (((cA d * (ct d τ + 1), cB d * (ct d τ + 1)) : ℝ × ℝ).2 - ((cA d * (ct d τ + 1), (0 : ℝ)) : ℝ × ℝ).2)
      ≠ 0 := by rw [hdet]; exact (mul_pos hu' hv').ne'
  have hc : (tgt hd hτ).carrier
      = (triC (d + 2) (hfr hd) (cA d * (ct d τ + 1), 0) (cA d * (ct d τ + 1), cB d * (ct d τ + 1))
          (0, cB d * (ct d τ + 1)) hne).carrier := by
    rw [carrier_tgt, carrier_triC]
    show Phi (d + 2) '' WS _ _ = _
    rw [← Erdos634.Draft.WClosedBase.hull_WS _ _ hu' hv']
  rw [hc, vol_triC]
  congr 2
  rw [abs_mul]
  congr 1
  rw [hdet, abs_of_pos (mul_pos hu' hv')]

theorem tgt_sides :
    dist ((tgt hd hτ).pts 0) ((tgt hd hτ).pts 1) = cB d * (ct d τ + 1) ∧
    dist ((tgt hd hτ).pts 1) ((tgt hd hτ).pts 2) = cA d * (ct d τ + 1) ∧
    dist ((tgt hd hτ).pts 0) ((tgt hd hτ).pts 2) = (ct d τ + 1) * (d + 2) ^ 3 := by
  have h2 : d + 2 ≠ 0 := (hFpos hd).ne'
  have ht := ct_pos hd hτ
  obtain ⟨q01, q12, q02⟩ := Erdos634.Draft.WClosedBase.WTriR_sq (d + 2) (hF1 hd hτ) _ _ (hu hd hτ) (hv hd hτ)
  refine ⟨(sq_eq_sq₀ dist_nonneg (hv hd hτ).le).mp q01, (sq_eq_sq₀ dist_nonneg (hu hd hτ).le).mp q12, ?_⟩
  refine (sq_eq_sq₀ dist_nonneg (by positivity)).mp ?_
  show dist ((Erdos634.Draft.WClosedBase.WTriR (d + 2) _ _ _ _ _).pts 0)
    ((Erdos634.Draft.WClosedBase.WTriR (d + 2) _ _ _ _ _).pts 2) ^ 2 = _
  rw [q02]; simp only [cA, cB]; field_simp; ring

/-- **The collar step, real parameters.**  A tiling of `W_t` by `n₀` tiles gives a dissection of `W_{t+1}`. -/
theorem collar_real (n0 k1 l1 k2 l2 k3 k4 k6 l6 k7 : ℕ)
    (hn0 : (n0 : ℝ) = cB d * ct d τ ^ 2)
    (hk1 : (k1 : ℝ) + 1 = d + 2) (hl1 : (l1 : ℝ) + 1 = (d + 2) * ct d τ)
    (hk2 : (k2 : ℝ) + 1 = (d + 2) ^ 2 - 1) (hl2 : (l2 : ℝ) + 1 = τ + 1)
    (hk30 : 0 < k3) (hk3 : (k3 : ℝ) = d + 2) (hk40 : 0 < k4) (hk4 : (k4 : ℝ) = d + 1)
    (hk6 : (k6 : ℝ) + 1 = (d + 2) * (d + 1)) (hl6 : (l6 : ℝ) + 1 = d + 1) (hk7 : (k7 : ℝ) + 1 = d + 1)
    (R0 : RTiling (Phi (d + 2) '' Wt (cA d) (cB d) (ct d τ)) (Mod hd) n0) :
    ∃ (N : ℕ) (D : CongruentDissection N), (N : ℝ) = cB d * (ct d τ + 1) ^ 2 ∧ D.model = Mod hd ∧
      D.target = tgt hd hτ := by
  obtain ⟨S6, ⟨R6⟩, h6⟩ := RT6 hd hτ k6 l6 hk6 hl6
  obtain ⟨S7, ⟨R7⟩, h7⟩ := RT7 hd hτ k7 hk7
  have R0s : RTiling (Phi (d + 2) '' Z0 d τ) (Mod hd) n0 := shiftR R0 (0, cB d)
  have Rall : ∀ a : Fin 9, RTiling (regionOf d τ S6 S7 a) (Mod hd)
      (cnt n0 (2 * (k1 + 1) * (l1 + 1)) (2 * (k2 + 1) * (l2 + 1)) (k3 * k3) (k4 * k4) (k4 * k4)
        (2 * (k6 + 1) * (l6 + 1)) (2 * (k7 + 1) * (0 + 1)) (k4 * k4) a) := fun a => match a with
    | ⟨0, _⟩ => R0s
    | ⟨1, _⟩ => RT1 hd k1 l1 hk1 hl1
    | ⟨2, _⟩ => RT2 hd k2 l2 hk2 hl2
    | ⟨3, _⟩ => RT3 hd hτ k3 hk30 hk3
    | ⟨4, _⟩ => RT4 hd hτ k4 hk40 hk4
    | ⟨5, _⟩ => RT5 hd hτ k4 hk40 hk4
    | ⟨6, _⟩ => R6
    | ⟨7, _⟩ => R7
    | ⟨8, _⟩ => RT8 hd hτ k4 hk40 hk4
    | ⟨k + 9, h⟩ => absurd h (by omega)
  have sub_all : ∀ a : Fin 9, regionOf d τ S6 S7 a ⊆ Phi (d + 2) '' Zf d τ a := fun a => match a with
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
      Disjoint (interior (regionOf d τ S6 S7 a)) (interior (regionOf d τ S6 S7 b)) := fun a b hab =>
    (disjoint_image' (hfr hd) (dZ_all hd hτ a b hab)).mono (interior_mono (sub_all a)) (interior_mono (sub_all b))
  have hsub_all : ∀ a : Fin 9, regionOf d τ S6 S7 a ⊆ (tgt hd hτ).carrier := fun a => by
    rw [carrier_tgt]
    exact (sub_all a).trans (Set.image_mono (Zf_sub hd hτ a))
  have hsumR : ((∑ a, cnt n0 (2 * (k1 + 1) * (l1 + 1)) (2 * (k2 + 1) * (l2 + 1)) (k3 * k3) (k4 * k4) (k4 * k4)
      (2 * (k6 + 1) * (l6 + 1)) (2 * (k7 + 1) * (0 + 1)) (k4 * k4) a : ℕ) : ℝ) = cB d * (ct d τ + 1) ^ 2 := by
    rw [sum_cnt]
    push_cast
    rw [hn0, hk1, hl1, hk2, hl2, hk3, hk4, hk6, hl6, hk7]
    simp only [cB, ct]; ring
  have hvol : ((∑ a, cnt n0 (2 * (k1 + 1) * (l1 + 1)) (2 * (k2 + 1) * (l2 + 1)) (k3 * k3) (k4 * k4) (k4 * k4)
      (2 * (k6 + 1) * (l6 + 1)) (2 * (k7 + 1) * (0 + 1)) (k4 * k4) a : ℕ) : ENNReal) * MeasureTheory.volume (Mod hd).carrier
      = MeasureTheory.volume (tgt hd hτ).carrier := by
    have hNR : (0 : ℝ) ≤ ((∑ a, cnt n0 (2 * (k1 + 1) * (l1 + 1)) (2 * (k2 + 1) * (l2 + 1)) (k3 * k3) (k4 * k4)
        (k4 * k4) (2 * (k6 + 1) * (l6 + 1)) (2 * (k7 + 1) * (0 + 1)) (k4 * k4) a : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [volMod hd hτ, vol_tgt hd hτ, ← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hNR, hsumR]
    congr 2
    simp only [cA, cB]; ring
  obtain ⟨D, hM, hT⟩ := Erdos634.Draft.S2L.pack_exists (M := Mod hd) (T := tgt hd hτ) (regionOf d τ S6 S7) _
    Rall hS_all hsub_all hvol
  exact ⟨_, D, hsumR, hM, hT⟩

end assemble

/-! ## The step for naturals, and every scale `M ≥ f` -/

/-- **The collar step**: `W_T → W_{T+1}` for the member `(1, f)`, `f = g + 2`, `T = f + τ`. -/
theorem collar_step (g τn : ℕ) (hW : WClosed (g + 2) (by omega) (g + 2 + τn)) :
    WClosed (g + 2) (by omega) (g + 2 + τn + 1) := by
  obtain ⟨R⟩ := hW
  have hd : (0 : ℝ) ≤ (g : ℝ) := Nat.cast_nonneg _
  have hτ : (0 : ℝ) ≤ (τn : ℝ) := Nat.cast_nonneg _
  have hf : 2 ≤ g + 2 := by omega
  have hFr := Erdos634.Draft.WPgramF.hF (g + 2) hf
  have eF : ((g + 2 : ℕ) : ℝ) = (g : ℝ) + 2 := by push_cast; ring
  -- the given tiling, in the notation of this file
  have hS : Phi ((g + 2 : ℕ) : ℝ) '' Wt (((g + 2 : ℕ) : ℝ) * (((g + 2 : ℕ) : ℝ) ^ 2 - 1))
      (2 * ((g + 2 : ℕ) : ℝ) ^ 2 - 1) ((g + 2 + τn : ℕ) : ℝ)
      = Phi ((g : ℝ) + 2) '' Wt (cA (g : ℝ)) (cB (g : ℝ)) (ct (g : ℝ) (τn : ℝ)) := by
    simp only [cA, cB, ct]; push_cast; rfl
  obtain ⟨m1, m2, m3⟩ := Erdos634.Draft.WPgramWrap.MF_sides hFr
  obtain ⟨s1, s2, s3⟩ := Mod_sides hd hτ
  have hMF0 : HasSides (Erdos634.Draft.WBrickF.MF ((g + 2 : ℕ) : ℝ) hFr) ((g + 2 : ℕ) : ℝ)
      (((g + 2 : ℕ) : ℝ) ^ 2) (((g + 2 : ℕ) : ℝ) ^ 2 - 1) :=
    ⟨Equiv.refl _, by simp only [Equiv.refl_apply]; exact m2,
      by simp only [Equiv.refl_apply]; rw [dist_comm]; exact m3, by simp only [Equiv.refl_apply]; exact m1⟩
  have hMF : (Erdos634.Draft.WBrickF.MF ((g + 2 : ℕ) : ℝ) hFr).Congruent (Mod hd) :=
    congruent_of_hasSides' (hasSides_rot (hasSides_rot (hasSides_swap hMF0)))
      (by rw [s1, eF]) (by rw [s2, eF]) (by rw [s3, eF])
  have R0 : RTiling (Phi ((g : ℝ) + 2) '' Wt (cA (g : ℝ)) (cB (g : ℝ)) (ct (g : ℝ) (τn : ℝ))) (Mod hd)
      ((2 * (g + 2) ^ 2 - 1) * (g + 2 + τn) ^ 2) := RegionTiling.remodel (RTiling.cast hS R) hMF
  have h1 : 1 ≤ 2 * (g + 2) ^ 2 := by nlinarith
  have hn0 : (((2 * (g + 2) ^ 2 - 1) * (g + 2 + τn) ^ 2 : ℕ) : ℝ) = cB (g : ℝ) * ct (g : ℝ) (τn : ℝ) ^ 2 := by
    rw [Nat.cast_mul, Nat.cast_sub h1]; simp only [cB, ct]; push_cast; ring
  obtain ⟨l1, hl1n⟩ : ∃ l1, l1 + 1 = (g + 2) * (g + 2 + τn) :=
    ⟨(g + 2) * (g + 2 + τn) - 1, Nat.sub_add_cancel (Nat.mul_pos (by omega) (by omega))⟩
  obtain ⟨k2, hk2n⟩ : ∃ k2, k2 + 1 = (g + 2) ^ 2 - 1 :=
    ⟨(g + 2) ^ 2 - 1 - 1, Nat.sub_add_cancel (Nat.le_sub_of_add_le (by nlinarith))⟩
  obtain ⟨k6, hk6n⟩ : ∃ k6, k6 + 1 = (g + 2) * (g + 1) :=
    ⟨(g + 2) * (g + 1) - 1, Nat.sub_add_cancel (Nat.mul_pos (by omega) (by omega))⟩
  have hl1 : (l1 : ℝ) + 1 = ((g : ℝ) + 2) * ct (g : ℝ) (τn : ℝ) := by
    have h := congrArg (Nat.cast : ℕ → ℝ) hl1n
    push_cast at h; simp only [ct]; linarith
  have hk2 : (k2 : ℝ) + 1 = ((g : ℝ) + 2) ^ 2 - 1 := by
    have h4 : 1 ≤ (g + 2) ^ 2 := by nlinarith
    have h := congrArg (Nat.cast : ℕ → ℝ) hk2n
    rw [Nat.cast_sub h4] at h
    push_cast at h; linarith
  have hk6 : (k6 : ℝ) + 1 = ((g : ℝ) + 2) * ((g : ℝ) + 1) := by
    have h := congrArg (Nat.cast : ℕ → ℝ) hk6n
    push_cast at h; linarith
  obtain ⟨N, D, hN, hM, hT⟩ := collar_real hd hτ _ (g + 1) l1 k2 τn (g + 2) (g + 1) k6 g g hn0
    (by push_cast; ring) hl1 hk2 rfl (by omega) (by push_cast; ring) (by omega) (by push_cast; ring) hk6 rfl rfl R0
  -- the number of tiles
  have h1' : 1 ≤ 2 * (g + 2) ^ 2 := h1
  have hNn : N = (2 * (g + 2) ^ 2 - 1) * (g + 2 + τn + 1) ^ 2 := by
    have : (N : ℝ) = (((2 * (g + 2) ^ 2 - 1) * (g + 2 + τn + 1) ^ 2 : ℕ) : ℝ) := by
      rw [hN, Nat.cast_mul, Nat.cast_sub h1']; simp only [cB, ct]; push_cast; ring
    exact_mod_cast this
  subst hNn
  obtain ⟨t01, t12, t02⟩ := tgt_sides hd hτ
  refine Erdos634.Draft.WClosedBase.WClosed_of_dissection (g + 2) hf (g + 2 + τn + 1) (by omega) D ?_ ?_
  · have hTs : HasSides D.target (cA (g : ℝ) * (ct (g : ℝ) (τn : ℝ) + 1))
        ((ct (g : ℝ) (τn : ℝ) + 1) * ((g : ℝ) + 2) ^ 3) (cB (g : ℝ) * (ct (g : ℝ) (τn : ℝ) + 1)) :=
      ⟨Equiv.refl _, by simp only [Equiv.refl_apply]; rw [hT]; exact t12,
        by simp only [Equiv.refl_apply]; rw [hT, dist_comm]; exact t02,
        by simp only [Equiv.refl_apply]; rw [hT]; exact t01⟩
    exact hasSides_congr hTs (by simp only [cA, ct]; push_cast; ring) (by simp only [ct]; push_cast; ring)
      (by simp only [cB, ct]; push_cast; ring)
  · have hMs : HasSides D.model (((g : ℝ) + 2) ^ 2 - 1) (((g : ℝ) + 2) ^ 2) ((g : ℝ) + 2) :=
      ⟨Equiv.refl _, by simp only [Equiv.refl_apply]; rw [hM]; exact s2,
        by simp only [Equiv.refl_apply]; rw [hM, dist_comm]; exact s3,
        by simp only [Equiv.refl_apply]; rw [hM]; exact s1⟩
    exact hasSides_congr (hasSides_rot (hasSides_rot (hasSides_swap hMs))) (by push_cast; ring)
      (by push_cast; ring) (by push_cast; ring)

/-- **`W` of the member `(1, f)` at every scale `M ≥ f`.** -/
theorem wClosed_ge (f : ℕ) (hf : 2 ≤ f) : ∀ M, f ≤ M → WClosed f hf M := by
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by omega⟩
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => exact Erdos634.Draft.WClosedBase.WClosed_seed (g + 2) hf
  | succ n hn ih =>
    obtain ⟨τn, rfl⟩ : ∃ τn, n = g + 2 + τn := ⟨n - (g + 2), by omega⟩
    exact collar_step g τn ih

/-- **The base-β target of the member `(1, f)` has a tiling at every scale `M ≥ f`**: the isosceles triangle with
legs `M f³` and base `M (3f² − 1)` is cut into congruent triangles with sides `(f, f² − 1, f²)`. -/
theorem betaTilable_e1 (f : ℕ) (hf : 2 ≤ f) : ∀ M, f ≤ M → BetaTilable 1 f M :=
  fun M hM => Erdos634.Draft.WClosedBase.betaTilable_of_WClosed f hf M (by omega) (wClosed_ge f hf M hM)

/-- the same for `W`: the triangle with sides `M f (f² − 1)`, `M (2f² − 1)`, `M f³` -/
theorem wTilable_e1 (f : ℕ) (hf : 2 ≤ f) (M : ℕ) (hM : f ≤ M) :
    ∃ D : CongruentDissection ((2 * f ^ 2 - 1) * M ^ 2),
      D.model = Erdos634.Draft.WBrickF.MF (f : ℝ) (Erdos634.Draft.WPgramF.hF f hf) := by
  obtain ⟨R⟩ := wClosed_ge f hf M hM
  have hF1 := Erdos634.Draft.WPgramF.hF f hf
  have hm0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hu := mul_pos (Erdos634.Draft.WGridF.A_pos f hf) hm0
  have hv := mul_pos (Erdos634.Draft.WGridF.B_pos f hf) hm0
  have hc : (Erdos634.Draft.WClosedBase.WTriR (f : ℝ) hF1 _ _ hu hv).carrier = _ :=
    (Erdos634.Draft.WClosedBase.carrier_WTriR _ hF1 _ _ hu hv).trans
      (congrArg _ (Erdos634.Draft.WtoDeltaF.WS_eq _ _ _ hm0))
  exact ⟨RegionTiling.toCD (T := Erdos634.Draft.WClosedBase.WTriR (f : ℝ) hF1 _ _ hu hv)
    (RTiling.cast hc.symm R), rfl⟩

open Erdos634.Draft.UniformThreshold (ThresholdAt threshold_one) in
/-- the threshold statement of the member `(1, f)` at every scale `M ≥ f` -/
theorem thresholdAt_e1_of_ge (f : ℕ) (hf : 2 ≤ f) {M : ℕ} (hM : f ≤ M) : ThresholdAt 1 f M :=
  ⟨fun _ => hM, fun _ => betaTilable_e1 f hf M hM⟩

open Erdos634.Draft.UniformThreshold (ThresholdAt threshold_one) in
/-- **The family `e = 1`.**  The threshold statement (a tiling of the base-β target at scale `M` if and only if
`M ≥ f`) holds for all members `(1, f)` and all scales if and only if no member has a tiling at a scale
`2 ≤ M < f`. -/
theorem threshold_e1_iff :
    (∀ f M : ℕ, 2 ≤ f → 1 ≤ M → ThresholdAt 1 f M) ↔ (∀ f M : ℕ, 2 ≤ M → M < f → ¬ BetaTilable 1 f M) := by
  constructor
  · intro h f M h2 hMf hB
    have := (h f M (by omega) (by omega)).mp hB
    omega
  · intro h f M hf hM
    by_cases h1 : f ≤ M
    · exact thresholdAt_e1_of_ge f hf h1
    · by_cases h2 : M = 1
      · subst h2; exact threshold_one (Nat.coprime_one_left f) le_rfl (by omega)
      · exact ⟨fun hB => absurd hB (h f M (by omega) (by omega)), fun hfM => absurd hfM h1⟩

end Erdos634.Draft.CollarE1

#print axioms Erdos634.Draft.CollarE1.mapped_grid
#print axioms Erdos634.Draft.CollarE1.collar_step
#print axioms Erdos634.Draft.CollarE1.wClosed_ge
#print axioms Erdos634.Draft.CollarE1.betaTilable_e1
#print axioms Erdos634.Draft.CollarE1.threshold_e1_iff
