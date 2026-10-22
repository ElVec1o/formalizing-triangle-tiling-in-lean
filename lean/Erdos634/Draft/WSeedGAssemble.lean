/-
Draft/WSeedGAssemble.lean -- the base-β target of every member `(e, f)` has a tiling at scale `f` (assembly).

    theorem beta_seed (u v : ℕ) (hu : 1 ≤ u) (huv : u < v) :
        ∃ D : CongruentDissection (v ^ 2 * (3 * v ^ 2 - u ^ 2)),
          HasSides D.target (v ^ 4) (v ^ 4) (u v (3 v² − u²)) ∧ HasSides D.model (u v) (v² − u²) (v²)

The five pieces of `Draft.WSeedG` have pairwise disjoint interiors (six separating lines), lie in the target, and
their areas add up to the area of the target; `S2L.pack_exists` assembles them.  No coprimality is needed.

THE CONSTRUCTION IS NOT OURS (seed credited to M. Beeson, beta lift as written by D. Paliy; see `Draft.WSeedG`).
What is added is the formal proof.  Composite-N / constructive side; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.WSeedG
import Erdos634.Draft.HasSidesPerm

open scoped Classical
set_option linter.unusedSectionVars false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Rect RTiling.cast RTiling.castN interior_disj_fst interior_disj_snd)

namespace Erdos634.Draft.WSeedG
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF
open Erdos634.Draft.S2G (triC triC_pts carrier_triC brickL vol_triC sq_Phi' disjoint_image' rect_le rect_ge)
open Erdos634.Draft.S2L (pack_exists mem_hull3' tri_le tri_ge tri_fst_le tri_fst_ge tri_snd_le tri_snd_ge rect_subset)
open Erdos634.Draft.FDBBaseBetaE1 (HasSides hasSides_rot hasSides_swap)

section facts
variable {u d : ℝ} (hu : 0 < u) (hd : 0 < d)
include hu hd

/-! ### membership in the target -/
theorem mem_GT (p : ℝ × ℝ) (h1 : -(u * (u + d)) ^ 2 ≤ p.2) (h2 : p.1 ≤ u * (u + d) * (d * (2 * u + d)))
    (h3 : u * (u + d) * (2 * u ^ 2 + 6 * u * d + 3 * d ^ 2) * (p.2 + (u * (u + d)) ^ 2)
      ≤ ((u + d) ^ 2) ^ 2 * (p.1 + 2 * (u * (u + d) * (u + d) ^ 2))) : p ∈ GT u d := by
  have hD : 0 < u * (u + d) * (2 * u ^ 2 + 6 * u * d + 3 * d ^ 2) * ((u + d) ^ 2) ^ 2 := by positivity
  refine mem_hull3' (A := pA u d) (B := pZ u d) (C := pB u d)
    (u * (u + d) * (2 * u ^ 2 + 6 * u * d + 3 * d ^ 2) * ((u + d) ^ 2) ^ 2)
    (u * (u + d) * (2 * u ^ 2 + 6 * u * d + 3 * d ^ 2) * (p.2 + (u * (u + d)) ^ 2))
    (((u + d) ^ 2) ^ 2 * (u * (u + d) * (d * (2 * u + d)) - p.1))
    (((u + d) ^ 2) ^ 2 * (p.1 + 2 * (u * (u + d) * (u + d) ^ 2))
      - u * (u + d) * (2 * u ^ 2 + 6 * u * d + 3 * d ^ 2) * (p.2 + (u * (u + d)) ^ 2))
    hD (mul_nonneg (by positivity) (by linarith)) (mul_nonneg (by positivity) (by linarith)) (by linarith)
    (by ring) p ?_ ?_
  · simp only [pA, pZ, pB]; ring
  · simp only [pA, pZ, pB]; ring

theorem pO_mem : pO ∈ GT u d := mem_GT hu hd _ (by simp only [pO]; ppos) (by simp only [pO]; ppos)
  (by simp only [pO]; ppos)
theorem pD_mem : pD u d ∈ GT u d := mem_GT hu hd _ (by simp only [pD]; ppos) (by simp only [pD]; ppos)
  (by simp only [pD]; ppos)
theorem pE_mem : pE u d ∈ GT u d := mem_GT hu hd _ (by simp only [pE]; ppos) (by simp only [pE]; ppos)
  (by simp only [pE]; ppos)
theorem pC_mem : pC u d ∈ GT u d := mem_GT hu hd _ (by simp only [pC]; ppos) (by simp only [pC]; ppos)
  (by simp only [pC]; ppos)
omit hu hd in
theorem pA_mem : pA u d ∈ GT u d := subset_convexHull ℝ _ (by simp)
omit hu hd in
theorem pZ_mem : pZ u d ∈ GT u d := subset_convexHull ℝ _ (by simp)
omit hu hd in
theorem pB_mem : pB u d ∈ GT u d := subset_convexHull ℝ _ (by simp)

omit hu hd in
theorem sub_tri {a b c : ℝ × ℝ} (ha : a ∈ GT u d) (hb : b ∈ GT u d) (hc : c ∈ GT u d) :
    convexHull ℝ {a, b, c} ⊆ GT u d := by
  refine convexHull_min ?_ (convex_convexHull ℝ _)
  intro w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl <;> assumption

theorem sub1 : G1 u d ⊆ GT u d := sub_tri (pO_mem hu hd) (pC_mem hu hd) pA_mem
theorem sub2 : G2 u d ⊆ GT u d := sub_tri (pO_mem hu hd) (pD_mem hu hd) pA_mem
theorem sub3 : G3 u d ⊆ GT u d := sub_tri (pO_mem hu hd) (pE_mem hu hd) (pC_mem hu hd)
theorem sub5 : G5 u d ⊆ GT u d := sub_tri (pC_mem hu hd) pZ_mem pA_mem
theorem sub4 : G4 u d ⊆ GT u d := by
  refine rect_subset (convex_convexHull ℝ _) (by ppos_lt) (by ppos_lt) ?_ ?_ ?_ ?_
  · exact pE_mem hu hd
  · exact pB_mem
  · exact pO_mem hu hd
  · exact pD_mem hu hd

/-! ### separating functionals -/
-- the line `O A`:  c s − a t   (G1: ≤ 0;  G2, G4: ≥ 0)
theorem G1_la : ∀ p ∈ G1 u d, (u + d) ^ 2 * p.1 + (-(u * (u + d))) * p.2 ≤ 0 :=
  tri_le (A := pO) (B := pC u d) (C := pA u d) _ _ _ (by simp only [pO]; ppos) (by simp only [pC]; ppos)
    (by simp only [pA]; ppos)
theorem G2_la : ∀ p ∈ G2 u d, 0 ≤ (u + d) ^ 2 * p.1 + (-(u * (u + d))) * p.2 :=
  tri_ge (A := pO) (B := pD u d) (C := pA u d) _ _ _ (by simp only [pO]; ppos) (by simp only [pD]; ppos)
    (by simp only [pA]; ppos)
theorem G4_la : ∀ p ∈ G4 u d, 0 ≤ (u + d) ^ 2 * p.1 + (-(u * (u + d))) * p.2 :=
  rect_ge (by ppos_lt) (by ppos_lt) _ _ _ (by ppos) (by ppos) (by ppos) (by ppos)

-- the line `O C`:  a s − c t   (G1: ≤ 0;  G3: ≥ 0)
theorem G1_lc : ∀ p ∈ G1 u d, u * (u + d) * p.1 + (-((u + d) ^ 2)) * p.2 ≤ 0 :=
  tri_le (A := pO) (B := pC u d) (C := pA u d) _ _ _ (by simp only [pO]; ppos) (by simp only [pC]; ppos)
    (by simp only [pA]; ppos)
theorem G3_lc : ∀ p ∈ G3 u d, 0 ≤ u * (u + d) * p.1 + (-((u + d) ^ 2)) * p.2 :=
  tri_ge (A := pO) (B := pE u d) (C := pC u d) _ _ _ (by simp only [pO]; ppos) (by simp only [pE]; ppos)
    (by simp only [pC]; ppos)

-- the vertical line s = 0   (G3: ≤ 0;  G2, G4: ≥ 0)
theorem G3_x : ∀ p ∈ G3 u d, p.1 ≤ 0 :=
  tri_fst_le (A := pO) (B := pE u d) (C := pC u d) _ (by simp only [pO]; ppos) (by simp only [pE]; ppos)
    (by simp only [pC]; ppos)
theorem G2_x : ∀ p ∈ G2 u d, 0 ≤ p.1 :=
  tri_fst_ge (A := pO) (B := pD u d) (C := pA u d) _ (by simp only [pO]; ppos) (by simp only [pD]; ppos)
    (by simp only [pA]; ppos)
omit hu hd in
theorem G4_x : ∀ p ∈ G4 u d, 0 ≤ p.1 := by
  rintro p ⟨a1, a2, a3, a4⟩; exact a1

-- the horizontal line t = 0   (G4: ≤ 0;  G2: ≥ 0)
theorem G2_y : ∀ p ∈ G2 u d, 0 ≤ p.2 :=
  tri_snd_ge (A := pO) (B := pD u d) (C := pA u d) _ (by simp only [pO]; ppos) (by simp only [pD]; ppos)
    (by simp only [pA]; ppos)
omit hu hd in
theorem G4_y : ∀ p ∈ G4 u d, p.2 ≤ 0 := by
  rintro p ⟨a1, a2, a3, a4⟩; exact a4

-- the line `C A`:  c² s − a Q t  against  K = −a b² c   (G5: ≤ K;  G1, G2, G3, G4: ≥ K)
theorem G5_lt : ∀ p ∈ G5 u d, ((u + d) ^ 2) ^ 2 * p.1 + (-(u * (u + d) * (u ^ 2 + 4 * u * d + 2 * d ^ 2))) * p.2
    ≤ -(u * (u + d) * (d * (2 * u + d)) ^ 2 * (u + d) ^ 2) :=
  tri_le (A := pC u d) (B := pZ u d) (C := pA u d) _ _ _ (by simp only [pC]; ppos) (by simp only [pZ]; ppos)
    (by simp only [pA]; ppos)
theorem G1_lt : ∀ p ∈ G1 u d, -(u * (u + d) * (d * (2 * u + d)) ^ 2 * (u + d) ^ 2)
    ≤ ((u + d) ^ 2) ^ 2 * p.1 + (-(u * (u + d) * (u ^ 2 + 4 * u * d + 2 * d ^ 2))) * p.2 :=
  tri_ge (A := pO) (B := pC u d) (C := pA u d) _ _ _ (by simp only [pO]; ppos) (by simp only [pC]; ppos)
    (by simp only [pA]; ppos)
theorem G2_lt : ∀ p ∈ G2 u d, -(u * (u + d) * (d * (2 * u + d)) ^ 2 * (u + d) ^ 2)
    ≤ ((u + d) ^ 2) ^ 2 * p.1 + (-(u * (u + d) * (u ^ 2 + 4 * u * d + 2 * d ^ 2))) * p.2 :=
  tri_ge (A := pO) (B := pD u d) (C := pA u d) _ _ _ (by simp only [pO]; ppos) (by simp only [pD]; ppos)
    (by simp only [pA]; ppos)
theorem G3_lt : ∀ p ∈ G3 u d, -(u * (u + d) * (d * (2 * u + d)) ^ 2 * (u + d) ^ 2)
    ≤ ((u + d) ^ 2) ^ 2 * p.1 + (-(u * (u + d) * (u ^ 2 + 4 * u * d + 2 * d ^ 2))) * p.2 :=
  tri_ge (A := pO) (B := pE u d) (C := pC u d) _ _ _ (by simp only [pO]; ppos) (by simp only [pE]; ppos)
    (by simp only [pC]; ppos)
theorem G4_lt : ∀ p ∈ G4 u d, -(u * (u + d) * (d * (2 * u + d)) ^ 2 * (u + d) ^ 2)
    ≤ ((u + d) ^ 2) ^ 2 * p.1 + (-(u * (u + d) * (u ^ 2 + 4 * u * d + 2 * d ^ 2))) * p.2 :=
  rect_ge (by ppos_lt) (by ppos_lt) _ _ _ (by ppos) (by ppos) (by ppos) (by ppos)

/-! ### the ten pairs -/
theorem la_ne : (u + d) ^ 2 ≠ 0 := by positivity
theorem lc_ne : u * (u + d) ≠ 0 := by positivity
theorem lt_ne : ((u + d) ^ 2) ^ 2 ≠ 0 := by positivity

theorem d12 : Disjoint (interior (Phi (fw u d) '' G1 u d)) (interior (Phi (fw u d) '' G2 u d)) :=
  disjoint_image' (hfr hu hd) (interior_disj_lin _ _ 0 (la_ne hu hd) (G1_la hu hd) (G2_la hu hd))
theorem d13 : Disjoint (interior (Phi (fw u d) '' G1 u d)) (interior (Phi (fw u d) '' G3 u d)) :=
  disjoint_image' (hfr hu hd) (interior_disj_lin _ _ 0 (lc_ne hu hd) (G1_lc hu hd) (G3_lc hu hd))
theorem d14 : Disjoint (interior (Phi (fw u d) '' G1 u d)) (interior (Phi (fw u d) '' G4 u d)) :=
  disjoint_image' (hfr hu hd) (interior_disj_lin _ _ 0 (la_ne hu hd) (G1_la hu hd) (G4_la hu hd))
theorem d15 : Disjoint (interior (Phi (fw u d) '' G1 u d)) (interior (Phi (fw u d) '' G5 u d)) :=
  (disjoint_image' (hfr hu hd) (interior_disj_lin _ _ _ (lt_ne hu hd) (G5_lt hu hd) (G1_lt hu hd))).symm
theorem d23 : Disjoint (interior (Phi (fw u d) '' G2 u d)) (interior (Phi (fw u d) '' G3 u d)) :=
  (disjoint_image' (hfr hu hd) (interior_disj_fst 0 (G3_x hu hd) (G2_x hu hd))).symm
theorem d24 : Disjoint (interior (Phi (fw u d) '' G2 u d)) (interior (Phi (fw u d) '' G4 u d)) :=
  (disjoint_image' (hfr hu hd) (interior_disj_snd 0 G4_y (G2_y hu hd))).symm
theorem d25 : Disjoint (interior (Phi (fw u d) '' G2 u d)) (interior (Phi (fw u d) '' G5 u d)) :=
  (disjoint_image' (hfr hu hd) (interior_disj_lin _ _ _ (lt_ne hu hd) (G5_lt hu hd) (G2_lt hu hd))).symm
theorem d34 : Disjoint (interior (Phi (fw u d) '' G3 u d)) (interior (Phi (fw u d) '' G4 u d)) :=
  disjoint_image' (hfr hu hd) (interior_disj_fst 0 (G3_x hu hd) G4_x)
theorem d35 : Disjoint (interior (Phi (fw u d) '' G3 u d)) (interior (Phi (fw u d) '' G5 u d)) :=
  (disjoint_image' (hfr hu hd) (interior_disj_lin _ _ _ (lt_ne hu hd) (G5_lt hu hd) (G3_lt hu hd))).symm
theorem d45 : Disjoint (interior (Phi (fw u d) '' G4 u d)) (interior (Phi (fw u d) '' G5 u d)) :=
  (disjoint_image' (hfr hu hd) (interior_disj_lin _ _ _ (lt_ne hu hd) (G5_lt hu hd) (G4_lt hu hd))).symm

/-! ### areas -/
/-- the target triangle `A Z B` -/
noncomputable def tgtR : Erdos634.Geometry.Tri :=
  triC (fw u d) (hfr hu hd) (pA u d) (pZ u d) (pB u d) (detT hu hd)

open MeasureTheory in
theorem volM : volume (Mod hu hd).carrier
    = ENNReal.ofReal (|sD (fw u d) / (2 * fw u d)| * (u * (u + d) * (u + d) ^ 2))
      * volume Erdos634.AreaDet.stdCarrier := by
  unfold Mod Erdos634.Draft.S2G.brickL
  rw [vol_triC]
  congr 2
  rw [abs_mul]
  congr 1
  have e : ((u * (u + d), (0 : ℝ)).1 - ((0 : ℝ), (0 : ℝ)).1) * ((u * (u + d), (u + d) ^ 2).2 - ((0 : ℝ), (0 : ℝ)).2)
      - ((u * (u + d), (u + d) ^ 2).1 - ((0 : ℝ), (0 : ℝ)).1) * ((u * (u + d), (0 : ℝ)).2 - ((0 : ℝ), (0 : ℝ)).2)
      = u * (u + d) * (u + d) ^ 2 := by ring
  rw [e, abs_of_pos (by positivity)]

open MeasureTheory in
theorem volT : volume (tgtR hu hd).carrier
    = ENNReal.ofReal (|sD (fw u d) / (2 * fw u d)| *
        (u * (u + d) ^ 5 * (2 * u ^ 2 + 6 * u * d + 3 * d ^ 2)))
      * volume Erdos634.AreaDet.stdCarrier := by
  unfold tgtR
  rw [vol_triC]
  congr 2
  rw [abs_mul]
  congr 1
  have e : ((pZ u d).1 - (pA u d).1) * ((pB u d).2 - (pA u d).2) - ((pB u d).1 - (pA u d).1) * ((pZ u d).2 - (pA u d).2)
      = u * (u + d) ^ 5 * (2 * u ^ 2 + 6 * u * d + 3 * d ^ 2) := by
    simp only [pA, pZ, pB]; ring
  rw [e, abs_of_pos (by positivity)]

end facts

/-! ## Natural parameters `1 ≤ u < v`, with `d = v − u` -/

noncomputable def regionOf (u v : ℕ) : Fin 5 → Set Plane := fun i => match i with
  | ⟨0, _⟩ => Phi (fw (u : ℝ) ((v - u : ℕ) : ℝ)) '' G1 (u : ℝ) ((v - u : ℕ) : ℝ)
  | ⟨1, _⟩ => Phi (fw (u : ℝ) ((v - u : ℕ) : ℝ)) '' G2 (u : ℝ) ((v - u : ℕ) : ℝ)
  | ⟨2, _⟩ => Phi (fw (u : ℝ) ((v - u : ℕ) : ℝ)) '' G3 (u : ℝ) ((v - u : ℕ) : ℝ)
  | ⟨3, _⟩ => Phi (fw (u : ℝ) ((v - u : ℕ) : ℝ)) '' G4 (u : ℝ) ((v - u : ℕ) : ℝ)
  | ⟨4, _⟩ => Phi (fw (u : ℝ) ((v - u : ℕ) : ℝ)) '' G5 (u : ℝ) ((v - u : ℕ) : ℝ)
  | ⟨k + 5, h⟩ => absurd h (by omega)

def cnt (u v : ℕ) : Fin 5 → ℕ := fun i => match i with
  | ⟨0, _⟩ => (v ^ 2 - u ^ 2) * (v ^ 2 - u ^ 2)
  | ⟨1, _⟩ => (v ^ 2 - u ^ 2) * (v ^ 2 - u ^ 2)
  | ⟨2, _⟩ => (u * v) * (u * v)
  | ⟨3, _⟩ => 2 * (v ^ 2 - u ^ 2) * u ^ 2
  | ⟨4, _⟩ => v ^ 2 * v ^ 2
  | ⟨k + 5, h⟩ => absurd h (by omega)

section nat
variable {u v : ℕ} (hu : 1 ≤ u) (huv : u < v)
include hu huv

theorem hUp : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu
theorem hDp : (0 : ℝ) < ((v - u : ℕ) : ℝ) := by
  have : 0 < v - u := by omega
  exact_mod_cast this
theorem hDv : ((v - u : ℕ) : ℝ) = (v : ℝ) - u := by
  rw [Nat.cast_sub huv.le]
theorem hsq : u ^ 2 < v ^ 2 := Nat.pow_lt_pow_left huv (by norm_num)

theorem hkb : ((v ^ 2 - u ^ 2 : ℕ) : ℝ) = ((v - u : ℕ) : ℝ) * (2 * (u : ℝ) + ((v - u : ℕ) : ℝ)) := by
  rw [Nat.cast_sub (hsq hu huv).le, hDv hu huv]; push_cast; ring
theorem hka : ((u * v : ℕ) : ℝ) = (u : ℝ) * ((u : ℝ) + ((v - u : ℕ) : ℝ)) := by
  rw [hDv hu huv]; push_cast; ring
theorem hkc : ((v ^ 2 : ℕ) : ℝ) = ((u : ℝ) + ((v - u : ℕ) : ℝ)) ^ 2 := by
  rw [hDv hu huv]; push_cast; ring

theorem cast_pred {n : ℕ} (h : 1 ≤ n) : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
  rw [Nat.cast_sub h]; push_cast; ring

noncomputable def Rall : ∀ a : Fin 5, RTiling (regionOf u v a)
    (Mod (hUp hu huv) (hDp hu huv)) (cnt u v a) := fun a => match a with
  | ⟨0, _⟩ => R1 (hUp hu huv) (hDp hu huv) (v ^ 2 - u ^ 2) (by have := hsq hu huv; omega) (hkb hu huv)
  | ⟨1, _⟩ => R2 (hUp hu huv) (hDp hu huv) (v ^ 2 - u ^ 2) (by have := hsq hu huv; omega) (hkb hu huv)
  | ⟨2, _⟩ => R3 (hUp hu huv) (hDp hu huv) (u * v) (Nat.mul_pos hu (by omega)) (hka hu huv)
  | ⟨3, _⟩ => by
      have h1 : 1 ≤ v ^ 2 - u ^ 2 := by have := hsq hu huv; omega
      have h2 : 1 ≤ u ^ 2 := Nat.one_le_pow _ _ hu
      have S := R4 (hUp hu huv) (hDp hu huv) (v ^ 2 - u ^ 2 - 1) (u ^ 2 - 1)
        (by rw [cast_pred hu huv h1]; exact hkb hu huv) (by rw [cast_pred hu huv h2]; push_cast; ring)
      refine RTiling.castN ?_ S
      show 2 * (v ^ 2 - u ^ 2 - 1 + 1) * (u ^ 2 - 1 + 1) = 2 * (v ^ 2 - u ^ 2) * u ^ 2
      rw [Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
  | ⟨4, _⟩ => R5 (hUp hu huv) (hDp hu huv) (v ^ 2) (pow_pos (by omega) 2) (hkc hu huv)
  | ⟨k + 5, h⟩ => absurd h (by omega)

theorem hS_all : ∀ a b : Fin 5, a ≠ b →
    Disjoint (interior (regionOf u v a)) (interior (regionOf u v b)) := by
  have hU := hUp hu huv
  have hD := hDp hu huv
  intro a b hab
  exact match a, b with
  | ⟨0, _⟩, ⟨0, _⟩ => absurd rfl hab
  | ⟨0, _⟩, ⟨1, _⟩ => d12 hU hD
  | ⟨0, _⟩, ⟨2, _⟩ => d13 hU hD
  | ⟨0, _⟩, ⟨3, _⟩ => d14 hU hD
  | ⟨0, _⟩, ⟨4, _⟩ => d15 hU hD
  | ⟨1, _⟩, ⟨0, _⟩ => (d12 hU hD).symm
  | ⟨1, _⟩, ⟨1, _⟩ => absurd rfl hab
  | ⟨1, _⟩, ⟨2, _⟩ => d23 hU hD
  | ⟨1, _⟩, ⟨3, _⟩ => d24 hU hD
  | ⟨1, _⟩, ⟨4, _⟩ => d25 hU hD
  | ⟨2, _⟩, ⟨0, _⟩ => (d13 hU hD).symm
  | ⟨2, _⟩, ⟨1, _⟩ => (d23 hU hD).symm
  | ⟨2, _⟩, ⟨2, _⟩ => absurd rfl hab
  | ⟨2, _⟩, ⟨3, _⟩ => d34 hU hD
  | ⟨2, _⟩, ⟨4, _⟩ => d35 hU hD
  | ⟨3, _⟩, ⟨0, _⟩ => (d14 hU hD).symm
  | ⟨3, _⟩, ⟨1, _⟩ => (d24 hU hD).symm
  | ⟨3, _⟩, ⟨2, _⟩ => (d34 hU hD).symm
  | ⟨3, _⟩, ⟨3, _⟩ => absurd rfl hab
  | ⟨3, _⟩, ⟨4, _⟩ => d45 hU hD
  | ⟨4, _⟩, ⟨0, _⟩ => (d15 hU hD).symm
  | ⟨4, _⟩, ⟨1, _⟩ => (d25 hU hD).symm
  | ⟨4, _⟩, ⟨2, _⟩ => (d35 hU hD).symm
  | ⟨4, _⟩, ⟨3, _⟩ => (d45 hU hD).symm
  | ⟨4, _⟩, ⟨4, _⟩ => absurd rfl hab
  | ⟨k + 5, h⟩, _ => absurd h (by omega)
  | _, ⟨k + 5, h⟩ => absurd h (by omega)

/-- the target triangle -/
noncomputable def tgt : Erdos634.Geometry.Tri := tgtR (hUp hu huv) (hDp hu huv)

theorem hsub_all : ∀ a : Fin 5, regionOf u v a ⊆ (tgt hu huv).carrier := by
  have hU := hUp hu huv
  have hD := hDp hu huv
  have hc : (tgt hu huv).carrier = Phi (fw (u : ℝ) ((v - u : ℕ) : ℝ)) '' GT (u : ℝ) ((v - u : ℕ) : ℝ) :=
    Erdos634.Draft.S2G.carrier_triC (fw (u : ℝ) ((v - u : ℕ) : ℝ)) (hfr hU hD) (pA _ _) (pZ _ _) (pB _ _)
      (detT hU hD)
  intro a
  rw [hc]
  exact match a with
  | ⟨0, _⟩ => Set.image_mono (sub1 hU hD)
  | ⟨1, _⟩ => Set.image_mono (sub2 hU hD)
  | ⟨2, _⟩ => Set.image_mono (sub3 hU hD)
  | ⟨3, _⟩ => Set.image_mono (sub4 hU hD)
  | ⟨4, _⟩ => Set.image_mono (sub5 hU hD)
  | ⟨k + 5, h⟩ => absurd h (by omega)

theorem sum_cnt : ∑ a, cnt u v a = v ^ 2 * (3 * v ^ 2 - u ^ 2) := by
  rw [Fin.sum_univ_five]
  show (v ^ 2 - u ^ 2) * (v ^ 2 - u ^ 2) + (v ^ 2 - u ^ 2) * (v ^ 2 - u ^ 2) + (u * v) * (u * v)
    + 2 * (v ^ 2 - u ^ 2) * u ^ 2 + v ^ 2 * v ^ 2 = _
  have h1 : u ^ 2 ≤ v ^ 2 := (hsq hu huv).le
  have h2 : u ^ 2 ≤ 3 * v ^ 2 := by omega
  zify [h1, h2]
  ring

theorem sum_cnt_real : ((∑ a, cnt u v a : ℕ) : ℝ) = (v : ℝ) ^ 2 * (3 * (v : ℝ) ^ 2 - (u : ℝ) ^ 2) := by
  have h2 : u ^ 2 ≤ 3 * v ^ 2 := by have := hsq hu huv; omega
  rw [sum_cnt hu huv, Nat.cast_mul, Nat.cast_sub h2]
  push_cast; ring

open MeasureTheory in
theorem hvol_all :
    ((∑ a, cnt u v a : ℕ) : ENNReal) * volume (Mod (hUp hu huv) (hDp hu huv)).carrier
      = volume (tgt hu huv).carrier := by
  have hU := hUp hu huv
  have hD := hDp hu huv
  show _ = volume (tgtR hU hD).carrier
  rw [volM hU hD, volT hU hD, ← mul_assoc, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _), sum_cnt_real hu huv]
  congr 2
  have hv : (v : ℝ) = (u : ℝ) + ((v - u : ℕ) : ℝ) := by rw [hDv hu huv]; ring
  rw [hv]
  ring

/-- **The beta seed, model and target named.** -/
theorem beta_seed_model :
    ∃ D : CongruentDissection (v ^ 2 * (3 * v ^ 2 - u ^ 2)),
      D.model = Mod (hUp hu huv) (hDp hu huv) ∧ D.target = tgt hu huv := by
  have := pack_exists (M := Mod (hUp hu huv) (hDp hu huv)) (T := tgt hu huv)
    (regionOf u v) (cnt u v) (Rall hu huv) (hS_all hu huv) (hsub_all hu huv) (hvol_all hu huv)
  rw [sum_cnt hu huv] at this
  exact this

/-- side lengths of the model: `a, c, b` on the edges `01, 12, 20` -/
theorem model_sides :
    dist ((Mod (hUp hu huv) (hDp hu huv)).pts 0) ((Mod (hUp hu huv) (hDp hu huv)).pts 1) = (u : ℝ) * v ∧
    dist ((Mod (hUp hu huv) (hDp hu huv)).pts 1) ((Mod (hUp hu huv) (hDp hu huv)).pts 2) = (v : ℝ) ^ 2 ∧
    dist ((Mod (hUp hu huv) (hDp hu huv)).pts 2) ((Mod (hUp hu huv) (hDp hu huv)).pts 0)
      = (v : ℝ) ^ 2 - (u : ℝ) ^ 2 := by
  have hU := hUp hu huv
  have hD := hDp hu huv
  have hf := hfr hU hD
  have hv : (v : ℝ) = (u : ℝ) + ((v - u : ℕ) : ℝ) := by rw [hDv hu huv]; ring
  have hvp : (0 : ℝ) < v := by rw [hv]; positivity
  have hb : (0 : ℝ) ≤ (v : ℝ) ^ 2 - (u : ℝ) ^ 2 := by rw [hv]; nlinarith [mul_pos hU hD, hD.le]
  simp only [Mod, Erdos634.Draft.S2G.brickL, Erdos634.Draft.S2G.triC_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  refine ⟨?_, ?_, ?_⟩
  · refine (sq_eq_sq₀ dist_nonneg (by positivity)).mp ?_
    rw [sq_Phi' hf, hv]; ring
  · refine (sq_eq_sq₀ dist_nonneg (by positivity)).mp ?_
    rw [sq_Phi' hf, hv]; ring
  · refine (sq_eq_sq₀ dist_nonneg hb).mp ?_
    rw [sq_Phi' hf]
    have h1 := hab_id hU hD
    have e : ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) ^ 2
        = (((v - u : ℕ) : ℝ) * (2 * (u : ℝ) + ((v - u : ℕ) : ℝ))) ^ 2 := by rw [hv]; ring
    rw [e, ← h1]; ring

/-- side lengths of the target: `|AZ| = v⁴`, `|ZB| = u v (3v² − u²)`, `|BA| = v⁴` -/
theorem tgt_sides :
    dist ((tgt hu huv).pts 0) ((tgt hu huv).pts 1) = (v : ℝ) ^ 4 ∧
    dist ((tgt hu huv).pts 1) ((tgt hu huv).pts 2) = (u : ℝ) * v * (3 * (v : ℝ) ^ 2 - (u : ℝ) ^ 2) ∧
    dist ((tgt hu huv).pts 2) ((tgt hu huv).pts 0) = (v : ℝ) ^ 4 := by
  have hU := hUp hu huv
  have hD := hDp hu huv
  have hf := hfr hU hD
  have hv : (v : ℝ) = (u : ℝ) + ((v - u : ℕ) : ℝ) := by rw [hDv hu huv]; ring
  have hvp : (0 : ℝ) < v := by rw [hv]; positivity
  have hne : ((u : ℝ) + ((v - u : ℕ) : ℝ)) ≠ 0 := by positivity
  have hP : (0 : ℝ) ≤ (u : ℝ) * v * (3 * (v : ℝ) ^ 2 - (u : ℝ) ^ 2) := by
    rw [hv]; nlinarith [mul_pos hU hD, mul_pos hU hU, mul_pos hD hD, mul_pos (mul_pos hU hU) hU,
      mul_pos (mul_pos hU hU) hD, mul_pos (mul_pos hU hD) hD, mul_pos (mul_pos hD hD) hD,
      mul_pos (mul_pos hU hU) (mul_pos hU hU), mul_pos (mul_pos hU hU) (mul_pos hU hD),
      mul_pos (mul_pos hU hU) (mul_pos hD hD), mul_pos (mul_pos hU hD) (mul_pos hD hD)]
  simp only [tgt, tgtR, Erdos634.Draft.S2G.triC_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  refine ⟨?_, ?_, ?_⟩
  · refine (sq_eq_sq₀ dist_nonneg (by positivity)).mp ?_
    rw [sq_Phi' hf, Fq hU hD, hv]; simp only [pA, pZ]; field_simp; ring
  · refine (sq_eq_sq₀ dist_nonneg hP).mp ?_
    rw [sq_Phi' hf, hv]; simp only [pZ, pB]; ring
  · refine (sq_eq_sq₀ dist_nonneg (by positivity)).mp ?_
    rw [sq_Phi' hf, hv]; simp only [pB, pA]; ring

end nat

/-- **The base-β target of every member at scale `f`** (`e = u`, `f = v`): the isosceles triangle with legs `v⁴`
and base `u v (3v² − u²)` is cut into `v² (3v² − u²)` congruent copies of the tile `(uv, v² − u², v²)`. -/
theorem beta_seed (u v : ℕ) (hu : 1 ≤ u) (huv : u < v) :
    ∃ D : CongruentDissection (v ^ 2 * (3 * v ^ 2 - u ^ 2)),
      HasSides D.target ((v : ℝ) ^ 4) ((v : ℝ) ^ 4) ((u : ℝ) * v * (3 * (v : ℝ) ^ 2 - (u : ℝ) ^ 2)) ∧
      HasSides D.model ((u : ℝ) * v) ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) ((v : ℝ) ^ 2) := by
  obtain ⟨D, hM, hT⟩ := beta_seed_model hu huv
  obtain ⟨t01, t12, t20⟩ := tgt_sides hu huv
  obtain ⟨m01, m12, m20⟩ := model_sides hu huv
  -- `HasSides T a b c` with the identity labelling reads `dist 1 2 = a`, `dist 2 0 = b`, `dist 0 1 = c`
  have hTs : HasSides D.target ((u : ℝ) * v * (3 * (v : ℝ) ^ 2 - (u : ℝ) ^ 2)) ((v : ℝ) ^ 4) ((v : ℝ) ^ 4) :=
    ⟨Equiv.refl _, by simp only [Equiv.refl_apply]; rw [hT]; exact t12,
      by simp only [Equiv.refl_apply]; rw [hT]; exact t20, by simp only [Equiv.refl_apply]; rw [hT]; exact t01⟩
  have hMs : HasSides D.model ((v : ℝ) ^ 2) ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) ((u : ℝ) * v) :=
    ⟨Equiv.refl _, by simp only [Equiv.refl_apply]; rw [hM]; exact m12,
      by simp only [Equiv.refl_apply]; rw [hM]; exact m20, by simp only [Equiv.refl_apply]; rw [hM]; exact m01⟩
  exact ⟨D, hasSides_rot hTs, hasSides_swap (hasSides_rot hMs)⟩

end Erdos634.Draft.WSeedG

#print axioms Erdos634.Draft.WSeedG.beta_seed_model
#print axioms Erdos634.Draft.WSeedG.beta_seed
