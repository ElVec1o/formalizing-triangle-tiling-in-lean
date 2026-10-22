/-
Draft/WSeedG.lean -- the base-β target of EVERY member `(e, f)` has a tiling at scale `f`: frame and layout.

For reals `u, d > 0` put `v = u + d`, `a = u v`, `b = d (2u + d) = v² − u²`, `c = v²`, `P = 3v² − u²`,
`Q = 2v² − u²`.  The tile is `(a, b, c)`.  In the skew frame `Φ_f` with `1/(2f) = −u P / (2 v³)` (the two axes
make the angle `π − β`), the cell `[0, a] × [0, c]` is cut by its diagonal into two copies of the tile, and with

    O = (0, 0),  D = (ab, 0),  E = (0, −a²),  B = (ab, −a²),  A = (ab, bc),  C = (−ac, −a²),  Z = (−2ac, −a²)

the triangle `A Z B` (sides `c², aP, c²`: the base-β target at scale `v`) is the union of five pieces:

    G1 = O C A   (tile at scale b)        G2 = O D A   (tile at scale b)        G3 = O E C   (tile at scale a)
    G4 = [0, ab] × [−a², 0]   (b × u² cells)                                    G5 = C Z A   (tile at scale c).

`G1 ∪ G2 ∪ G3 ∪ G4` is the triangle `A C B` (the target `W` at scale `v`), and `G5` is the "beta lift".
Count: `2 b² + a² + 2 b u² + c² = v² P`.

THE CONSTRUCTION IS NOT OURS: the four pieces of `A C B` are the seed that D. Paliy's note of 3 October 2026
(`research/w-beta-caps/PROOF.md`, Section 6) credits to M. Beeson (Triangle tiling: the case `3α + 2β = π`,
Theorem 11), and `G5` is the beta lift of the same note (Section 5).  What this file adds is a formal proof, in the
framework of `Draft.S2GFrame` (region tilings, packing lemma with the area identity).

This file: the frame, the model, the five region tilings (real parameters).  `Draft.WSeedGAssemble`: disjointness,
containment, areas, and the theorem for natural `1 ≤ e < f`.

Composite-N / constructive side; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.S2GLayout

open scoped Classical
set_option linter.unusedSectionVars false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Rect RTiling.cast RTiling.castN interior_disj_fst interior_disj_snd)

namespace Erdos634.Draft.WSeedG
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF
open Erdos634.Draft.S2G (triC triC_pts carrier_triC brickL brickU brick_rt cong_U_cell grid scaledRT baseTri
  baseTri_cong vol_triC sq_Phi' dPhi' disjoint_image' rect_le rect_ge f_ne)
open Erdos634.Draft.BrickGridF (shift_rect)

/-- the frame parameter `f = −v³ / (u P)` (negative) -/
noncomputable def fw (u d : ℝ) : ℝ := -(u + d) ^ 3 / (u * (2 * u ^ 2 + 6 * u * d + 3 * d ^ 2))

def pO : ℝ × ℝ := (0, 0)
def pD (u d : ℝ) : ℝ × ℝ := (u * (u + d) * (d * (2 * u + d)), 0)
def pE (u d : ℝ) : ℝ × ℝ := (0, -(u * (u + d)) ^ 2)
def pB (u d : ℝ) : ℝ × ℝ := (u * (u + d) * (d * (2 * u + d)), -(u * (u + d)) ^ 2)
def pA (u d : ℝ) : ℝ × ℝ := (u * (u + d) * (d * (2 * u + d)), d * (2 * u + d) * (u + d) ^ 2)
def pC (u d : ℝ) : ℝ × ℝ := (-(u * (u + d) * (u + d) ^ 2), -(u * (u + d)) ^ 2)
def pZ (u d : ℝ) : ℝ × ℝ := (-(2 * (u * (u + d) * (u + d) ^ 2)), -(u * (u + d)) ^ 2)

def G1 (u d : ℝ) : Set (ℝ × ℝ) := convexHull ℝ {pO, pC u d, pA u d}
def G2 (u d : ℝ) : Set (ℝ × ℝ) := convexHull ℝ {pO, pD u d, pA u d}
def G3 (u d : ℝ) : Set (ℝ × ℝ) := convexHull ℝ {pO, pE u d, pC u d}
def G4 (u d : ℝ) : Set (ℝ × ℝ) := Rect 0 (u * (u + d) * (d * (2 * u + d))) (-(u * (u + d)) ^ 2) 0
def G5 (u d : ℝ) : Set (ℝ × ℝ) := convexHull ℝ {pC u d, pZ u d, pA u d}
/-- the target: the triangle `A Z B` -/
def GT (u d : ℝ) : Set (ℝ × ℝ) := convexHull ℝ {pA u d, pZ u d, pB u d}

section real
variable {u d : ℝ} (hu : 0 < u) (hd : 0 < d)
include hu hd

theorem hfr : 1 < 4 * (fw u d) ^ 2 := by
  have hD : 0 < u * (2 * u ^ 2 + 6 * u * d + 3 * d ^ 2) := by positivity
  have e : fw u d ^ 2 = ((u + d) ^ 3) ^ 2 / (u * (2 * u ^ 2 + 6 * u * d + 3 * d ^ 2)) ^ 2 := by
    simp only [fw]; rw [neg_div, neg_sq, div_pow]
  rw [e, ← mul_div_assoc, lt_div_iff₀ (by positivity)]
  ppos_lt

theorem Fq (x y : ℝ) : x ^ 2 + y ^ 2 + x * y / fw u d
    = x ^ 2 + y ^ 2 - u * (2 * u ^ 2 + 6 * u * d + 3 * d ^ 2) * x * y / (u + d) ^ 3 := by
  have h1 : (u + d) ≠ 0 := by positivity
  have h2 : u * (2 * u ^ 2 + 6 * u * d + 3 * d ^ 2) ≠ 0 := by positivity
  simp only [fw]; field_simp; ring

theorem hapos : 0 < u * (u + d) := by positivity
theorem hcpos : 0 < (u + d) ^ 2 := by positivity
theorem hbpos : 0 < d * (2 * u + d) := by positivity

/-- the model tile: the lower half of the cell `[0, a] × [0, c]`; its edges `01, 12, 20` have lengths `a, c, b` -/
noncomputable def Mod : Tri := brickL (fw u d) (hfr hu hd) (u * (u + d)) ((u + d) ^ 2) (hapos hu hd) (hcpos hu hd)

theorem hab_id : (u * (u + d)) ^ 2 + ((u + d) ^ 2) ^ 2 + (u * (u + d)) * ((u + d) ^ 2) / fw u d
    = (d * (2 * u + d)) ^ 2 := by
  have h1 : (u + d) ≠ 0 := by positivity
  rw [Fq hu hd]; field_simp; ring

noncomputable def cellRT : RTiling (Phi (fw u d) '' Rect 0 (u * (u + d)) 0 ((u + d) ^ 2)) (Mod hu hd) 2 :=
  brick_rt (fw u d) (hfr hu hd) (u * (u + d)) ((u + d) ^ 2) (hapos hu hd) (hcpos hu hd) _
    (Tri.Congruent.refl _) (cong_U_cell (hfr hu hd) _ _ _ _)

/-! ### nondegeneracy -/
theorem det1 : ((pC u d).1 - (pO).1) * ((pA u d).2 - (pO).2) - ((pA u d).1 - (pO).1) * ((pC u d).2 - (pO).2) ≠ 0 := by
  have e : ((pC u d).1 - (pO).1) * ((pA u d).2 - (pO).2) - ((pA u d).1 - (pO).1) * ((pC u d).2 - (pO).2)
      = -(d ^ 2 * u * (u + d) ^ 3 * (2 * u + d) ^ 2) := by simp only [pO, pC, pA]; ring
  rw [e]; exact neg_ne_zero.mpr (by positivity)
theorem det2 : ((pD u d).1 - (pO).1) * ((pA u d).2 - (pO).2) - ((pA u d).1 - (pO).1) * ((pD u d).2 - (pO).2) ≠ 0 := by
  have e : ((pD u d).1 - (pO).1) * ((pA u d).2 - (pO).2) - ((pA u d).1 - (pO).1) * ((pD u d).2 - (pO).2)
      = d ^ 2 * u * (u + d) ^ 3 * (2 * u + d) ^ 2 := by simp only [pO, pD, pA]; ring
  rw [e]; positivity
theorem det3 : ((pE u d).1 - (pO).1) * ((pC u d).2 - (pO).2) - ((pC u d).1 - (pO).1) * ((pE u d).2 - (pO).2) ≠ 0 := by
  have e : ((pE u d).1 - (pO).1) * ((pC u d).2 - (pO).2) - ((pC u d).1 - (pO).1) * ((pE u d).2 - (pO).2)
      = -(u ^ 3 * (u + d) ^ 5) := by simp only [pO, pE, pC]; ring
  rw [e]; exact neg_ne_zero.mpr (by positivity)
theorem det5 : ((pZ u d).1 - (pC u d).1) * ((pA u d).2 - (pC u d).2) - ((pA u d).1 - (pC u d).1) * ((pZ u d).2 - (pC u d).2) ≠ 0 := by
  have e : ((pZ u d).1 - (pC u d).1) * ((pA u d).2 - (pC u d).2) - ((pA u d).1 - (pC u d).1) * ((pZ u d).2 - (pC u d).2)
      = -(u * (u + d) ^ 7) := by simp only [pC, pZ, pA]; ring
  rw [e]; exact neg_ne_zero.mpr (by positivity)
theorem detT : ((pZ u d).1 - (pA u d).1) * ((pB u d).2 - (pA u d).2) - ((pB u d).1 - (pA u d).1) * ((pZ u d).2 - (pA u d).2) ≠ 0 := by
  have e : ((pZ u d).1 - (pA u d).1) * ((pB u d).2 - (pA u d).2) - ((pB u d).1 - (pA u d).1) * ((pZ u d).2 - (pA u d).2)
      = u * (u + d) ^ 5 * (2 * u ^ 2 + 6 * u * d + 3 * d ^ 2) := by simp only [pA, pZ, pB]; ring
  rw [e]; positivity

/-! ### the four triangular pieces -/

/-- `G1 = O C A`, the tile at scale `k = b` -/
noncomputable def R1 (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = d * (2 * u + d)) :
    RTiling (Phi (fw u d) '' G1 u d) (Mod hu hd) (k * k) :=
  scaledRT (fw u d) (hfr hu hd) pO (pC u d) (pA u d) k hk0 (det1 hu hd) _
    (baseTri_cong _ _ (u * (u + d)) ((u + d) ^ 2) ((d * (2 * u + d)) ^ 2) (hapos hu hd) (hcpos hu hd)
      (hab_id hu hd) _ _ _ k hk0 _
      (by rw [hk]; rw [Fq hu hd]; simp only [pO, pC, pA]; field_simp; ring)
      (by rw [hk]; rw [Fq hu hd]; simp only [pO, pC, pA]; field_simp; ring)
      (by rw [hk]; rw [Fq hu hd]; simp only [pO, pC, pA]; field_simp; ring))

/-- `G2 = O D A`, the tile at scale `k = b` -/
noncomputable def R2 (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = d * (2 * u + d)) :
    RTiling (Phi (fw u d) '' G2 u d) (Mod hu hd) (k * k) :=
  scaledRT (fw u d) (hfr hu hd) pO (pD u d) (pA u d) k hk0 (det2 hu hd) _
    (baseTri_cong _ _ (u * (u + d)) ((u + d) ^ 2) ((d * (2 * u + d)) ^ 2) (hapos hu hd) (hcpos hu hd)
      (hab_id hu hd) _ _ _ k hk0 _
      (by rw [hk]; rw [Fq hu hd]; simp only [pO, pD, pA]; field_simp; ring)
      (by rw [hk]; rw [Fq hu hd]; simp only [pO, pD, pA]; field_simp; ring)
      (by rw [hk]; rw [Fq hu hd]; simp only [pO, pD, pA]; field_simp; ring))

/-- `G3 = O E C`, the tile at scale `k = a` -/
noncomputable def R3 (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = u * (u + d)) :
    RTiling (Phi (fw u d) '' G3 u d) (Mod hu hd) (k * k) :=
  scaledRT (fw u d) (hfr hu hd) pO (pE u d) (pC u d) k hk0 (det3 hu hd) _
    (baseTri_cong _ _ (u * (u + d)) ((u + d) ^ 2) ((d * (2 * u + d)) ^ 2) (hapos hu hd) (hcpos hu hd)
      (hab_id hu hd) _ _ _ k hk0 _
      (by rw [hk]; rw [Fq hu hd]; simp only [pO, pE, pC]; field_simp; ring)
      (by rw [hk]; rw [Fq hu hd]; simp only [pO, pE, pC]; field_simp; ring)
      (by rw [hk]; rw [Fq hu hd]; simp only [pO, pE, pC]; field_simp; ring))

/-- `G5 = C Z A`, the tile at scale `k = c` -/
noncomputable def R5 (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = (u + d) ^ 2) :
    RTiling (Phi (fw u d) '' G5 u d) (Mod hu hd) (k * k) :=
  scaledRT (fw u d) (hfr hu hd) (pC u d) (pZ u d) (pA u d) k hk0 (det5 hu hd) _
    (baseTri_cong _ _ (u * (u + d)) ((u + d) ^ 2) ((d * (2 * u + d)) ^ 2) (hapos hu hd) (hcpos hu hd)
      (hab_id hu hd) _ _ _ k hk0 _
      (by rw [hk]; rw [Fq hu hd]; simp only [pC, pZ, pA]; field_simp; ring)
      (by rw [hk]; rw [Fq hu hd]; simp only [pC, pZ, pA]; field_simp; ring)
      (by rw [hk]; rw [Fq hu hd]; simp only [pC, pZ, pA]; field_simp; ring))

/-- `G4`: the grid of `(kb + 1) × (ku + 1)` cells, shifted down by `a²` -/
noncomputable def R4 (kb ku : ℕ) (hkb : ((kb : ℝ) + 1) = d * (2 * u + d)) (hku : ((ku : ℝ) + 1) = u ^ 2) :
    RTiling (Phi (fw u d) '' G4 u d) (Mod hu hd) (2 * (kb + 1) * (ku + 1)) :=
  shift_rect (grid (hfr hu hd) (hapos hu hd) (hcpos hu hd) (cellRT hu hd) kb ku) 0 (-(u * (u + d)) ^ 2)
    (u * (u + d) * (d * (2 * u + d))) 0 (by rw [hkb]; ring) (by rw [hku]; ring)

end real

end Erdos634.Draft.WSeedG
