/-
Draft/WSeedGW.lean -- the target `W = (2α, β, α + β)` of EVERY member `(e, f)` has a tiling at scale `f`.

    theorem w_seed (u v : ℕ) (hu : 1 ≤ u) (huv : u < v) :
        ∃ D : CongruentDissection (v ^ 2 * (2 * v ^ 2 - u ^ 2)),
          HasSides D.target (v² (v² − u²)) (u v (2v² − u²)) (v ^ 4) ∧ HasSides D.model (u v) (v² − u²) (v²)

The triangle `A C B` of `Draft.WSeedG` (sides `|AC| = bc`, `|CB| = aQ`, `|BA| = c²`) is the union of the four
pieces `G1, G2, G3, G4`: two copies of the tile at scale `b`, one at scale `a`, and `b × u²` cells.  Count
`2 b² + a² + 2 b u² = v² (2v² − u²)`.

THE CONSTRUCTION IS NOT OURS: it is the seed that D. Paliy's note of 3 October 2026 credits to M. Beeson (Triangle
tiling: the case `3α + 2β = π`, Theorem 11).  What is added is the formal proof for all `1 ≤ e < f`.
Composite-N / constructive side; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.WSeedGAssemble
import Erdos634.Draft.TileCountFamilies

open scoped Classical
set_option linter.unusedSectionVars false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Rect RTiling.cast RTiling.castN interior_disj_fst interior_disj_snd)

namespace Erdos634.Draft.WSeedG
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF
open Erdos634.Draft.S2G (triC vol_triC sq_Phi')
open Erdos634.Draft.S2L (pack_exists mem_hull3' rect_subset)
open Erdos634.Draft.FDBBaseBetaE1 (HasSides hasSides_rot hasSides_swap)

/-- the target `W`: the triangle `A C B` -/
def GW (u d : ℝ) : Set (ℝ × ℝ) := convexHull ℝ {pA u d, pC u d, pB u d}

section facts
variable {u d : ℝ} (hu : 0 < u) (hd : 0 < d)
include hu hd

theorem mem_GW (p : ℝ × ℝ) (h1 : -(u * (u + d)) ^ 2 ≤ p.2) (h2 : p.1 ≤ u * (u + d) * (d * (2 * u + d)))
    (h3 : u * (u + d) * (u ^ 2 + 4 * u * d + 2 * d ^ 2) * (p.2 + (u * (u + d)) ^ 2)
      ≤ ((u + d) ^ 2) ^ 2 * (p.1 + u * (u + d) * (u + d) ^ 2)) : p ∈ GW u d := by
  have hD : 0 < u * (u + d) * (u ^ 2 + 4 * u * d + 2 * d ^ 2) * ((u + d) ^ 2) ^ 2 := by positivity
  refine mem_hull3' (A := pA u d) (B := pC u d) (C := pB u d)
    (u * (u + d) * (u ^ 2 + 4 * u * d + 2 * d ^ 2) * ((u + d) ^ 2) ^ 2)
    (u * (u + d) * (u ^ 2 + 4 * u * d + 2 * d ^ 2) * (p.2 + (u * (u + d)) ^ 2))
    (((u + d) ^ 2) ^ 2 * (u * (u + d) * (d * (2 * u + d)) - p.1))
    (((u + d) ^ 2) ^ 2 * (p.1 + u * (u + d) * (u + d) ^ 2)
      - u * (u + d) * (u ^ 2 + 4 * u * d + 2 * d ^ 2) * (p.2 + (u * (u + d)) ^ 2))
    hD (mul_nonneg (by positivity) (by linarith)) (mul_nonneg (by positivity) (by linarith)) (by linarith)
    (by ring) p ?_ ?_
  · simp only [pA, pC, pB]; ring
  · simp only [pA, pC, pB]; ring

theorem pO_memW : pO ∈ GW u d := mem_GW hu hd _ (by simp only [pO]; ppos) (by simp only [pO]; ppos)
  (by simp only [pO]; ppos)
theorem pD_memW : pD u d ∈ GW u d := mem_GW hu hd _ (by simp only [pD]; ppos) (by simp only [pD]; ppos)
  (by simp only [pD]; ppos)
theorem pE_memW : pE u d ∈ GW u d := mem_GW hu hd _ (by simp only [pE]; ppos) (by simp only [pE]; ppos)
  (by simp only [pE]; ppos)
omit hu hd in
theorem pA_memW : pA u d ∈ GW u d := subset_convexHull ℝ _ (by simp)
omit hu hd in
theorem pC_memW : pC u d ∈ GW u d := subset_convexHull ℝ _ (by simp)
omit hu hd in
theorem pB_memW : pB u d ∈ GW u d := subset_convexHull ℝ _ (by simp)

omit hu hd in
theorem sub_triW {a b c : ℝ × ℝ} (ha : a ∈ GW u d) (hb : b ∈ GW u d) (hc : c ∈ GW u d) :
    convexHull ℝ {a, b, c} ⊆ GW u d := by
  refine convexHull_min ?_ (convex_convexHull ℝ _)
  intro w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl <;> assumption

theorem sub1W : G1 u d ⊆ GW u d := sub_triW (pO_memW hu hd) pC_memW pA_memW
theorem sub2W : G2 u d ⊆ GW u d := sub_triW (pO_memW hu hd) (pD_memW hu hd) pA_memW
theorem sub3W : G3 u d ⊆ GW u d := sub_triW (pO_memW hu hd) (pE_memW hu hd) pC_memW
theorem sub4W : G4 u d ⊆ GW u d := by
  refine rect_subset (convex_convexHull ℝ _) (by ppos_lt) (by ppos_lt) ?_ ?_ ?_ ?_
  · exact pE_memW hu hd
  · exact pB_memW
  · exact pO_memW hu hd
  · exact pD_memW hu hd

theorem detW : ((pC u d).1 - (pA u d).1) * ((pB u d).2 - (pA u d).2) - ((pB u d).1 - (pA u d).1) * ((pC u d).2 - (pA u d).2) ≠ 0 := by
  have e : ((pC u d).1 - (pA u d).1) * ((pB u d).2 - (pA u d).2) - ((pB u d).1 - (pA u d).1) * ((pC u d).2 - (pA u d).2)
      = u * (u + d) ^ 5 * (u ^ 2 + 4 * u * d + 2 * d ^ 2) := by simp only [pA, pC, pB]; ring
  rw [e]; positivity

/-- the target triangle `A C B` -/
noncomputable def tgtWR : Erdos634.Geometry.Tri :=
  triC (fw u d) (hfr hu hd) (pA u d) (pC u d) (pB u d) (detW hu hd)

open MeasureTheory in
theorem volTW : volume (tgtWR hu hd).carrier
    = ENNReal.ofReal (|sD (fw u d) / (2 * fw u d)| *
        (u * (u + d) ^ 5 * (u ^ 2 + 4 * u * d + 2 * d ^ 2)))
      * volume Erdos634.AreaDet.stdCarrier := by
  unfold tgtWR
  rw [vol_triC]
  congr 2
  rw [abs_mul]
  congr 1
  have e : ((pC u d).1 - (pA u d).1) * ((pB u d).2 - (pA u d).2) - ((pB u d).1 - (pA u d).1) * ((pC u d).2 - (pA u d).2)
      = u * (u + d) ^ 5 * (u ^ 2 + 4 * u * d + 2 * d ^ 2) := by
    simp only [pA, pC, pB]; ring
  rw [e, abs_of_pos (by positivity)]

end facts

noncomputable def regionOfW (u v : ℕ) : Fin 4 → Set Plane := fun i => match i with
  | ⟨0, _⟩ => Phi (fw (u : ℝ) ((v - u : ℕ) : ℝ)) '' G1 (u : ℝ) ((v - u : ℕ) : ℝ)
  | ⟨1, _⟩ => Phi (fw (u : ℝ) ((v - u : ℕ) : ℝ)) '' G2 (u : ℝ) ((v - u : ℕ) : ℝ)
  | ⟨2, _⟩ => Phi (fw (u : ℝ) ((v - u : ℕ) : ℝ)) '' G3 (u : ℝ) ((v - u : ℕ) : ℝ)
  | ⟨3, _⟩ => Phi (fw (u : ℝ) ((v - u : ℕ) : ℝ)) '' G4 (u : ℝ) ((v - u : ℕ) : ℝ)
  | ⟨k + 4, h⟩ => absurd h (by omega)

def cntW (u v : ℕ) : Fin 4 → ℕ := fun i => match i with
  | ⟨0, _⟩ => (v ^ 2 - u ^ 2) * (v ^ 2 - u ^ 2)
  | ⟨1, _⟩ => (v ^ 2 - u ^ 2) * (v ^ 2 - u ^ 2)
  | ⟨2, _⟩ => (u * v) * (u * v)
  | ⟨3, _⟩ => 2 * (v ^ 2 - u ^ 2) * u ^ 2
  | ⟨k + 4, h⟩ => absurd h (by omega)

section nat
variable {u v : ℕ} (hu : 1 ≤ u) (huv : u < v)
include hu huv

noncomputable def RallW : ∀ a : Fin 4, RTiling (regionOfW u v a)
    (Mod (hUp hu huv) (hDp hu huv)) (cntW u v a) := fun a => match a with
  | ⟨0, _⟩ => Rall hu huv ⟨0, by norm_num⟩
  | ⟨1, _⟩ => Rall hu huv ⟨1, by norm_num⟩
  | ⟨2, _⟩ => Rall hu huv ⟨2, by norm_num⟩
  | ⟨3, _⟩ => Rall hu huv ⟨3, by norm_num⟩
  | ⟨k + 4, h⟩ => absurd h (by omega)

theorem hS_allW : ∀ a b : Fin 4, a ≠ b →
    Disjoint (interior (regionOfW u v a)) (interior (regionOfW u v b)) := by
  have hU := hUp hu huv
  have hD := hDp hu huv
  intro a b hab
  exact match a, b with
  | ⟨0, _⟩, ⟨0, _⟩ => absurd rfl hab
  | ⟨0, _⟩, ⟨1, _⟩ => d12 hU hD
  | ⟨0, _⟩, ⟨2, _⟩ => d13 hU hD
  | ⟨0, _⟩, ⟨3, _⟩ => d14 hU hD
  | ⟨1, _⟩, ⟨0, _⟩ => (d12 hU hD).symm
  | ⟨1, _⟩, ⟨1, _⟩ => absurd rfl hab
  | ⟨1, _⟩, ⟨2, _⟩ => d23 hU hD
  | ⟨1, _⟩, ⟨3, _⟩ => d24 hU hD
  | ⟨2, _⟩, ⟨0, _⟩ => (d13 hU hD).symm
  | ⟨2, _⟩, ⟨1, _⟩ => (d23 hU hD).symm
  | ⟨2, _⟩, ⟨2, _⟩ => absurd rfl hab
  | ⟨2, _⟩, ⟨3, _⟩ => d34 hU hD
  | ⟨3, _⟩, ⟨0, _⟩ => (d14 hU hD).symm
  | ⟨3, _⟩, ⟨1, _⟩ => (d24 hU hD).symm
  | ⟨3, _⟩, ⟨2, _⟩ => (d34 hU hD).symm
  | ⟨3, _⟩, ⟨3, _⟩ => absurd rfl hab
  | ⟨k + 4, h⟩, _ => absurd h (by omega)
  | _, ⟨k + 4, h⟩ => absurd h (by omega)

/-- the target triangle -/
noncomputable def tgtW : Erdos634.Geometry.Tri := tgtWR (hUp hu huv) (hDp hu huv)

theorem hsub_allW : ∀ a : Fin 4, regionOfW u v a ⊆ (tgtW hu huv).carrier := by
  have hU := hUp hu huv
  have hD := hDp hu huv
  have hc : (tgtW hu huv).carrier = Phi (fw (u : ℝ) ((v - u : ℕ) : ℝ)) '' GW (u : ℝ) ((v - u : ℕ) : ℝ) :=
    Erdos634.Draft.S2G.carrier_triC (fw (u : ℝ) ((v - u : ℕ) : ℝ)) (hfr hU hD) (pA _ _) (pC _ _) (pB _ _)
      (detW hU hD)
  intro a
  rw [hc]
  exact match a with
  | ⟨0, _⟩ => Set.image_mono (sub1W hU hD)
  | ⟨1, _⟩ => Set.image_mono (sub2W hU hD)
  | ⟨2, _⟩ => Set.image_mono (sub3W hU hD)
  | ⟨3, _⟩ => Set.image_mono (sub4W hU hD)
  | ⟨k + 4, h⟩ => absurd h (by omega)

theorem sum_cntW : ∑ a, cntW u v a = v ^ 2 * (2 * v ^ 2 - u ^ 2) := by
  rw [Fin.sum_univ_four]
  show (v ^ 2 - u ^ 2) * (v ^ 2 - u ^ 2) + (v ^ 2 - u ^ 2) * (v ^ 2 - u ^ 2) + (u * v) * (u * v)
    + 2 * (v ^ 2 - u ^ 2) * u ^ 2 = _
  have h1 : u ^ 2 ≤ v ^ 2 := (hsq hu huv).le
  have h2 : u ^ 2 ≤ 2 * v ^ 2 := by omega
  zify [h1, h2]
  ring

theorem sum_cntW_real : ((∑ a, cntW u v a : ℕ) : ℝ) = (v : ℝ) ^ 2 * (2 * (v : ℝ) ^ 2 - (u : ℝ) ^ 2) := by
  have h2 : u ^ 2 ≤ 2 * v ^ 2 := by have := hsq hu huv; omega
  rw [sum_cntW hu huv, Nat.cast_mul, Nat.cast_sub h2]
  push_cast; ring

open MeasureTheory in
theorem hvol_allW :
    ((∑ a, cntW u v a : ℕ) : ENNReal) * volume (Mod (hUp hu huv) (hDp hu huv)).carrier
      = volume (tgtW hu huv).carrier := by
  have hU := hUp hu huv
  have hD := hDp hu huv
  show _ = volume (tgtWR hU hD).carrier
  rw [volM hU hD, volTW hU hD, ← mul_assoc, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _), sum_cntW_real hu huv]
  congr 2
  have hv : (v : ℝ) = (u : ℝ) + ((v - u : ℕ) : ℝ) := by rw [hDv hu huv]; ring
  rw [hv]
  ring

/-- **The W seed, model and target named.** -/
theorem w_seed_model :
    ∃ D : CongruentDissection (v ^ 2 * (2 * v ^ 2 - u ^ 2)),
      D.model = Mod (hUp hu huv) (hDp hu huv) ∧ D.target = tgtW hu huv := by
  have := pack_exists (M := Mod (hUp hu huv) (hDp hu huv)) (T := tgtW hu huv)
    (regionOfW u v) (cntW u v) (RallW hu huv) (hS_allW hu huv) (hsub_allW hu huv) (hvol_allW hu huv)
  rw [sum_cntW hu huv] at this
  exact this

/-- side lengths of the target: `|AC| = v² (v² − u²)`, `|CB| = u v (2v² − u²)`, `|BA| = v⁴` -/
theorem tgtW_sides :
    dist ((tgtW hu huv).pts 0) ((tgtW hu huv).pts 1) = (v : ℝ) ^ 2 * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) ∧
    dist ((tgtW hu huv).pts 1) ((tgtW hu huv).pts 2) = (u : ℝ) * v * (2 * (v : ℝ) ^ 2 - (u : ℝ) ^ 2) ∧
    dist ((tgtW hu huv).pts 2) ((tgtW hu huv).pts 0) = (v : ℝ) ^ 4 := by
  have hU := hUp hu huv
  have hD := hDp hu huv
  have hf := hfr hU hD
  have hv : (v : ℝ) = (u : ℝ) + ((v - u : ℕ) : ℝ) := by rw [hDv hu huv]; ring
  have hne : ((u : ℝ) + ((v - u : ℕ) : ℝ)) ≠ 0 := by positivity
  have hb : (0 : ℝ) ≤ (v : ℝ) ^ 2 * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) := by
    rw [hv]
    have e : ((u : ℝ) + ((v - u : ℕ) : ℝ)) ^ 2 * (((u : ℝ) + ((v - u : ℕ) : ℝ)) ^ 2 - (u : ℝ) ^ 2)
        = ((u : ℝ) + ((v - u : ℕ) : ℝ)) ^ 2 * (((v - u : ℕ) : ℝ) * (2 * (u : ℝ) + ((v - u : ℕ) : ℝ))) := by ring
    rw [e]; positivity
  have hq : (0 : ℝ) ≤ (u : ℝ) * v * (2 * (v : ℝ) ^ 2 - (u : ℝ) ^ 2) := by
    rw [hv]
    have e : (u : ℝ) * ((u : ℝ) + ((v - u : ℕ) : ℝ)) * (2 * ((u : ℝ) + ((v - u : ℕ) : ℝ)) ^ 2 - (u : ℝ) ^ 2)
        = (u : ℝ) * ((u : ℝ) + ((v - u : ℕ) : ℝ))
          * ((u : ℝ) ^ 2 + 4 * (u : ℝ) * ((v - u : ℕ) : ℝ) + 2 * ((v - u : ℕ) : ℝ) ^ 2) := by ring
    rw [e]; positivity
  simp only [tgtW, tgtWR, Erdos634.Draft.S2G.triC_pts, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  refine ⟨?_, ?_, ?_⟩
  · refine (sq_eq_sq₀ dist_nonneg hb).mp ?_
    rw [sq_Phi' hf, Fq hU hD, hv]; simp only [pA, pC]; field_simp; ring
  · refine (sq_eq_sq₀ dist_nonneg hq).mp ?_
    rw [sq_Phi' hf, hv]; simp only [pC, pB]; ring
  · refine (sq_eq_sq₀ dist_nonneg (by positivity)).mp ?_
    rw [sq_Phi' hf, hv]; simp only [pB, pA]; ring

end nat

/-- **The target `W` of every member at scale `f`** (`e = u`, `f = v`): the triangle with sides `v² (v² − u²)`,
`u v (2v² − u²)`, `v⁴` is cut into `v² (2v² − u²)` congruent copies of the tile `(uv, v² − u², v²)`. -/
theorem w_seed (u v : ℕ) (hu : 1 ≤ u) (huv : u < v) :
    ∃ D : CongruentDissection (v ^ 2 * (2 * v ^ 2 - u ^ 2)),
      HasSides D.target ((v : ℝ) ^ 2 * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2)) ((u : ℝ) * v * (2 * (v : ℝ) ^ 2 - (u : ℝ) ^ 2))
        ((v : ℝ) ^ 4) ∧
      HasSides D.model ((u : ℝ) * v) ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) ((v : ℝ) ^ 2) := by
  obtain ⟨D, hM, hT⟩ := w_seed_model hu huv
  obtain ⟨t01, t12, t20⟩ := tgtW_sides hu huv
  obtain ⟨m01, m12, m20⟩ := model_sides hu huv
  -- `HasSides T a b c` with the identity labelling reads `dist 1 2 = a`, `dist 2 0 = b`, `dist 0 1 = c`
  have hTs : HasSides D.target ((u : ℝ) * v * (2 * (v : ℝ) ^ 2 - (u : ℝ) ^ 2)) ((v : ℝ) ^ 4)
      ((v : ℝ) ^ 2 * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2)) :=
    ⟨Equiv.refl _, by simp only [Equiv.refl_apply]; rw [hT]; exact t12,
      by simp only [Equiv.refl_apply]; rw [hT]; exact t20, by simp only [Equiv.refl_apply]; rw [hT]; exact t01⟩
  have hMs : HasSides D.model ((v : ℝ) ^ 2) ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) ((u : ℝ) * v) :=
    ⟨Equiv.refl _, by simp only [Equiv.refl_apply]; rw [hM]; exact m12,
      by simp only [Equiv.refl_apply]; rw [hM]; exact m20, by simp only [Equiv.refl_apply]; rw [hM]; exact m01⟩
  exact ⟨D, hasSides_rot (hasSides_rot hTs), hasSides_swap (hasSides_rot hMs)⟩

/-- `f² (2f² − e²)` is a tile count for all `1 ≤ e < f`. -/
theorem tileCount_w_seed (u v : ℕ) (hu : 1 ≤ u) (huv : u < v) :
    Erdos634.Draft.TileCountFamilies.TileCount (v ^ 2 * (2 * v ^ 2 - u ^ 2)) := by
  obtain ⟨D, -, -⟩ := w_seed_model hu huv
  exact ⟨D⟩

end Erdos634.Draft.WSeedG

#print axioms Erdos634.Draft.WSeedG.w_seed
#print axioms Erdos634.Draft.WSeedG.tileCount_w_seed
