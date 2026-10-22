/-
Draft/F4All.lean — **the F4 family (angle `2π/3`, `a < b`) for ALL Eisenstein triples**: for naturals `0 < a < b`, `c` with
`c² = a² + a b + b²`, the triangle with sides `(a c, b (2a + b), (a + b) c)` is tiled by `(2a + b)(a + b)` copies of the
tile `(a, b, c)`, hence `(2a+b)(a+b)` is a tile count (and `(2a+b)(a+b) k²` for every `k`).

The construction is due to **D. Paliy** (`github.com/DenisUkranian/erdos-634-tilings`, "Unit multiplier in one orientation of
the 120-degree F4 family", 2 Oct 2026; a generalisation of J. P. Harries's concrete 88-tiling of `(3,5,7)`); decoded in
(private working notes, not included), (private working notes, not included) (`F4_small`).  What is added here is the symbolic proof
(all `a, b, c`) in Lean.

Paliy's trapezoid `AECB` (the `b`-triangle `FAE` minus its `(b-a)`-corner `FBC`) is cut, here, along the line through `C`
parallel to `FA` into the parallelogram `B A G C` (`(b-a) × a` cells of two tiles each) and the `a`-triangle `C E G`.
Layout (skew frame `Φ_1`, i.e. Eisenstein coordinates `x + yρ`, all coordinates multiplied by `c` and translated so that `B`
is the origin; `b = a + t`, `S = a² + ab + b² = c²`):
  `T1 = O A B` : scale `c` (`c²` tiles);  `T2 = A E D`, `T3 = C E D`, `T4 = C E G` : scale `a` (`a²` tiles each);
  `PG = B A G C = Lam u w [0,t]×[0,a]`, `u = a (b, a)`, `w = (0, -S)` : `2 a (b-a)` tiles;  target `D C O`.
Count `c² + 3a² + 2a(b-a) = (2a+b)(a+b)`.  Tile: `brickL 1 (b c) (a c)` (legs along the axes, hypotenuse `c²`).

UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.S2AllTheta
import Erdos634.Draft.TileCountFamilies

open scoped Classical
set_option linter.unusedSectionVars false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Rect RTiling.cast RTiling.castN interior_disj_fst interior_disj_snd Sh_Rect)

namespace Erdos634.Draft.F4All
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.S2G Erdos634.Draft.S2AllTheta
open Erdos634.Draft.S2L (rect_subset tri_le tri_ge tri_fst_le tri_fst_ge tri_snd_le tri_snd_ge mem_hull3' pack_exists)
open Erdos634.Draft.WBrickF (interior_disj_lin)

macro "ppos_nn" : tactic => `(tactic| first
  | (rw [← sub_nonneg]; ring_nf; positivity)
  | (rw [← sub_nonneg]; ring_nf)
  | (rw [← sub_nonneg]; ring_nf; exact le_refl _))

theorem f4_eq_of_sq {d r : ℝ} (hd : 0 ≤ d) (hr : 0 ≤ r) (h : d ^ 2 = r ^ 2) : d = r :=
  Erdos634.Draft.SumTwoSquares.eqsq hd hr h

theorem hf1 : (1 : ℝ) < 4 * (1 : ℝ) ^ 2 := by norm_num

/-! ### the layout -/
/-- `S = c² = a² + a b + b²`, `b = a + t`. -/
def sS (a t : ℝ) : ℝ := a ^ 2 + a * (a + t) + (a + t) ^ 2
def vO (a t : ℝ) : ℝ × ℝ := (-((a + t) * sS a t), -(a * sS a t))
def vA (a t : ℝ) : ℝ × ℝ := (0, -(a * sS a t))
def vB (_a _t : ℝ) : ℝ × ℝ := (0, 0)
def vD (a t : ℝ) : ℝ × ℝ := (a * sS a t, -(a * sS a t))
def vC (a t : ℝ) : ℝ × ℝ := (a * (a + t) * t, a ^ 2 * t)
def vE (a t : ℝ) : ℝ × ℝ := (a * (a + t) ^ 2, -(a * (a ^ 2 + (a + t) ^ 2)))
def vG (a t : ℝ) : ℝ × ℝ := (a * (a + t) * t, -(a * (2 * a ^ 2 + (a + t) ^ 2)))
/-- lattice vectors of the parallelogram cell. -/
def uu (a t : ℝ) : ℝ × ℝ := (a * (a + t), a ^ 2)
def ww (a t : ℝ) : ℝ × ℝ := (0, -(sS a t))

def H1 (a t : ℝ) : Set (ℝ × ℝ) := convexHull ℝ {vO a t, vA a t, vB a t}
def H2 (a t : ℝ) : Set (ℝ × ℝ) := convexHull ℝ {vA a t, vE a t, vD a t}
def H3 (a t : ℝ) : Set (ℝ × ℝ) := convexHull ℝ {vC a t, vE a t, vD a t}
def H4 (a t : ℝ) : Set (ℝ × ℝ) := convexHull ℝ {vC a t, vE a t, vG a t}
def H5 (a t : ℝ) : Set (ℝ × ℝ) := Lam (uu a t) (ww a t) '' Rect 0 t 0 a
def HT (a t : ℝ) : Set (ℝ × ℝ) := convexHull ℝ {vD a t, vC a t, vO a t}

section geom
variable {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
include ha ht

/-! ### non-degeneracy -/
theorem det1 : ((vA a t).1 - (vO a t).1) * ((vB a t).2 - (vO a t).2) - ((vB a t).1 - (vO a t).1) * ((vA a t).2 - (vO a t).2) ≠ 0 := by
  have e : ((vA a t).1 - (vO a t).1) * ((vB a t).2 - (vO a t).2) - ((vB a t).1 - (vO a t).1) * ((vA a t).2 - (vO a t).2)
      = a * (a + t) * (3 * a ^ 2 + 3 * a * t + t ^ 2) ^ 2 := by simp only [vO, vA, vB, sS]; ring
  rw [e]; positivity
theorem det2 : ((vE a t).1 - (vA a t).1) * ((vD a t).2 - (vA a t).2) - ((vD a t).1 - (vA a t).1) * ((vE a t).2 - (vA a t).2) ≠ 0 := by
  have e : ((vE a t).1 - (vA a t).1) * ((vD a t).2 - (vA a t).2) - ((vD a t).1 - (vA a t).1) * ((vE a t).2 - (vA a t).2)
      = -(a ^ 3 * (a + t) * (3 * a ^ 2 + 3 * a * t + t ^ 2)) := by simp only [vE, vA, vD, sS]; ring
  rw [e]; exact neg_ne_zero.mpr (by positivity)
theorem det3 : ((vE a t).1 - (vC a t).1) * ((vD a t).2 - (vC a t).2) - ((vD a t).1 - (vC a t).1) * ((vE a t).2 - (vC a t).2) ≠ 0 := by
  have e : ((vE a t).1 - (vC a t).1) * ((vD a t).2 - (vC a t).2) - ((vD a t).1 - (vC a t).1) * ((vE a t).2 - (vC a t).2)
      = a ^ 3 * (a + t) * (3 * a ^ 2 + 3 * a * t + t ^ 2) := by simp only [vE, vC, vD, sS]; ring
  rw [e]; positivity
theorem det4 : ((vE a t).1 - (vC a t).1) * ((vG a t).2 - (vC a t).2) - ((vG a t).1 - (vC a t).1) * ((vE a t).2 - (vC a t).2) ≠ 0 := by
  have e : ((vE a t).1 - (vC a t).1) * ((vG a t).2 - (vC a t).2) - ((vG a t).1 - (vC a t).1) * ((vE a t).2 - (vC a t).2)
      = -(a ^ 3 * (a + t) * (3 * a ^ 2 + 3 * a * t + t ^ 2)) := by simp only [vE, vC, vG, sS]; ring
  rw [e]; exact neg_ne_zero.mpr (by positivity)
theorem detT : ((vC a t).1 - (vD a t).1) * ((vO a t).2 - (vD a t).2) - ((vO a t).1 - (vD a t).1) * ((vC a t).2 - (vD a t).2) ≠ 0 := by
  have e : ((vC a t).1 - (vD a t).1) * ((vO a t).2 - (vD a t).2) - ((vO a t).1 - (vD a t).1) * ((vC a t).2 - (vD a t).2)
      = a * (a + t) * (2 * a + t) * (3 * a + t) * (3 * a ^ 2 + 3 * a * t + t ^ 2) := by simp only [vD, vC, vO, sS]; ring
  rw [e]; positivity
theorem detL : (uu a t).1 * (ww a t).2 - (uu a t).2 * (ww a t).1 ≠ 0 := by
  have e : (uu a t).1 * (ww a t).2 - (uu a t).2 * (ww a t).1 = -(a * (a + t) * (3 * a ^ 2 + 3 * a * t + t ^ 2)) := by
    simp only [uu, ww, sS]; ring
  rw [e]; exact neg_ne_zero.mpr (by positivity)

/-! ### separating functionals and containment -/
macro "vchk" : tactic => `(tactic| (simp only [vO, vA, vB, vD, vC, vE, vG, sS] <;> ppos_nn))

theorem H1_x : ∀ x ∈ H1 a t, x.1 ≤ 0 :=
  tri_fst_le (A := vO a t) (B := vA a t) (C := vB a t) _ (by vchk) (by vchk) (by vchk)
theorem H2_x : ∀ x ∈ H2 a t, 0 ≤ x.1 :=
  tri_fst_ge (A := vA a t) (B := vE a t) (C := vD a t) _ (by vchk) (by vchk) (by vchk)
theorem H3_x : ∀ x ∈ H3 a t, 0 ≤ x.1 :=
  tri_fst_ge (A := vC a t) (B := vE a t) (C := vD a t) _ (by vchk) (by vchk) (by vchk)
theorem H4_x : ∀ x ∈ H4 a t, 0 ≤ x.1 :=
  tri_fst_ge (A := vC a t) (B := vE a t) (C := vG a t) _ (by vchk) (by vchk) (by vchk)
theorem H3_xc : ∀ x ∈ H3 a t, a * (a + t) * t ≤ x.1 :=
  tri_fst_ge (A := vC a t) (B := vE a t) (C := vD a t) _ (by vchk) (by vchk) (by vchk)
theorem H4_xc : ∀ x ∈ H4 a t, a * (a + t) * t ≤ x.1 :=
  tri_fst_ge (A := vC a t) (B := vE a t) (C := vG a t) _ (by vchk) (by vchk) (by vchk)
theorem H2_l23 : ∀ x ∈ H2 a t, (a + t) * x.1 + (2 * a + t) * x.2 ≤ -(a ^ 2 * (3 * a ^ 2 + 3 * a * t + t ^ 2)) :=
  tri_le (A := vA a t) (B := vE a t) (C := vD a t) _ _ _ (by vchk) (by vchk) (by vchk)
theorem H3_l23 : ∀ x ∈ H3 a t, -(a ^ 2 * (3 * a ^ 2 + 3 * a * t + t ^ 2)) ≤ (a + t) * x.1 + (2 * a + t) * x.2 :=
  tri_ge (A := vC a t) (B := vE a t) (C := vD a t) _ _ _ (by vchk) (by vchk) (by vchk)
theorem H2_lAE : ∀ x ∈ H2 a t, a * (a + t) * (3 * a ^ 2 + 3 * a * t + t ^ 2) ≤ a * x.1 + (-(a + t)) * x.2 :=
  tri_ge (A := vA a t) (B := vE a t) (C := vD a t) _ _ _ (by vchk) (by vchk) (by vchk)
theorem H4_lAE : ∀ x ∈ H4 a t, a * x.1 + (-(a + t)) * x.2 ≤ a * (a + t) * (3 * a ^ 2 + 3 * a * t + t ^ 2) :=
  tri_le (A := vC a t) (B := vE a t) (C := vG a t) _ _ _ (by vchk) (by vchk) (by vchk)
theorem H3_lCE : ∀ x ∈ H3 a t, a * t * (3 * a ^ 2 + 3 * a * t + t ^ 2) ≤ (2 * a + t) * x.1 + a * x.2 :=
  tri_ge (A := vC a t) (B := vE a t) (C := vD a t) _ _ _ (by vchk) (by vchk) (by vchk)
theorem H4_lCE : ∀ x ∈ H4 a t, (2 * a + t) * x.1 + a * x.2 ≤ a * t * (3 * a ^ 2 + 3 * a * t + t ^ 2) :=
  tri_le (A := vC a t) (B := vE a t) (C := vG a t) _ _ _ (by vchk) (by vchk) (by vchk)

theorem H5_x : ∀ x ∈ H5 a t, 0 ≤ x.1 := by
  rintro _ ⟨z, ⟨h1, h2, h3, h4⟩, rfl⟩
  have hc : 0 ≤ a * (a + t) := by positivity
  simp only [Lam, uu, ww, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  nlinarith [mul_nonneg hc h1]
theorem H5_xc : ∀ x ∈ H5 a t, x.1 ≤ a * (a + t) * t := by
  rintro _ ⟨z, ⟨h1, h2, h3, h4⟩, rfl⟩
  have hc : 0 ≤ a * (a + t) := by positivity
  simp only [Lam, uu, ww, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  nlinarith [mul_nonneg hc (sub_nonneg.mpr h2)]
theorem H5_lAE : ∀ x ∈ H5 a t, a * x.1 + (-(a + t)) * x.2 ≤ a * (a + t) * (3 * a ^ 2 + 3 * a * t + t ^ 2) := by
  rintro _ ⟨z, ⟨h1, h2, h3, h4⟩, rfl⟩
  have hc : 0 ≤ (a + t) * (3 * a ^ 2 + 3 * a * t + t ^ 2) := by positivity
  simp only [Lam, uu, ww, sS, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  nlinarith [mul_nonneg hc (sub_nonneg.mpr h4)]

variable {f : ℝ} (hf : 1 < 4 * f ^ 2)
include hf

theorem d12 : Disjoint (interior (Phi f '' H1 a t)) (interior (Phi f '' H2 a t)) :=
  disjoint_image' hf (interior_disj_fst 0 (H1_x ha ht) (H2_x ha ht))
theorem d13 : Disjoint (interior (Phi f '' H1 a t)) (interior (Phi f '' H3 a t)) :=
  disjoint_image' hf (interior_disj_fst 0 (H1_x ha ht) (H3_x ha ht))
theorem d14 : Disjoint (interior (Phi f '' H1 a t)) (interior (Phi f '' H4 a t)) :=
  disjoint_image' hf (interior_disj_fst 0 (H1_x ha ht) (H4_x ha ht))
theorem d15 : Disjoint (interior (Phi f '' H1 a t)) (interior (Phi f '' H5 a t)) :=
  disjoint_image' hf (interior_disj_fst 0 (H1_x ha ht) (H5_x ha ht))
theorem d23 : Disjoint (interior (Phi f '' H2 a t)) (interior (Phi f '' H3 a t)) :=
  disjoint_image' hf (interior_disj_lin (a + t) (2 * a + t) _ (by positivity) (H2_l23 ha ht) (H3_l23 ha ht))
theorem d24 : Disjoint (interior (Phi f '' H2 a t)) (interior (Phi f '' H4 a t)) :=
  disjoint_image' hf (interior_disj_lin a (-(a + t)) _ ha.ne' (H4_lAE ha ht) (H2_lAE ha ht)).symm
theorem d25 : Disjoint (interior (Phi f '' H2 a t)) (interior (Phi f '' H5 a t)) :=
  disjoint_image' hf (interior_disj_lin a (-(a + t)) _ ha.ne' (H5_lAE ha ht) (H2_lAE ha ht)).symm
theorem d34 : Disjoint (interior (Phi f '' H3 a t)) (interior (Phi f '' H4 a t)) :=
  disjoint_image' hf (interior_disj_lin (2 * a + t) a _ (by positivity) (H4_lCE ha ht) (H3_lCE ha ht)).symm
theorem d35 : Disjoint (interior (Phi f '' H3 a t)) (interior (Phi f '' H5 a t)) :=
  disjoint_image' hf (interior_disj_fst _ (H5_xc ha ht) (H3_xc ha ht)).symm
theorem d45 : Disjoint (interior (Phi f '' H4 a t)) (interior (Phi f '' H5 a t)) :=
  disjoint_image' hf (interior_disj_fst _ (H5_xc ha ht) (H4_xc ha ht)).symm

omit hf

/-! ### containment in the target `D C O` -/
theorem mem_A : vA a t ∈ HT a t :=
  mem_hull3' (A := vD a t) (B := vC a t) (C := vO a t) (2 * a + t) (a + t) 0 a
    (by positivity) (by positivity) (le_refl _) ha.le (by ring) _
    (by simp only [vA, vD, vC, vO, sS]; ring) (by simp only [vA, vD, vC, vO, sS]; ring)

theorem mem_B : vB a t ∈ HT a t :=
  mem_hull3' (A := vD a t) (B := vC a t) (C := vO a t) ((a + t) * (3 * a + t)) 0 (3 * a ^ 2 + 3 * a * t + t ^ 2) (a * t)
    (by positivity) (le_refl _) (by positivity) (by positivity) (by ring) _
    (by simp only [vB, vD, vC, vO, sS]; ring) (by simp only [vB, vD, vC, vO, sS]; ring)

theorem mem_E : vE a t ∈ HT a t :=
  mem_hull3' (A := vD a t) (B := vC a t) (C := vO a t) ((2 * a + t) * (3 * a + t))
    ((a + t) * (3 * a + t)) (a * (2 * a + t)) (a ^ 2)
    (by positivity) (by positivity) (by positivity) (by positivity) (by ring) _
    (by simp only [vE, vD, vC, vO, sS]; ring) (by simp only [vE, vD, vC, vO, sS]; ring)

theorem mem_G : vG a t ∈ HT a t :=
  mem_hull3' (A := vD a t) (B := vC a t) (C := vO a t) ((a + t) * (2 * a + t) * (3 * a + t))
    ((a + t) ^ 2 * (3 * a + t)) (a * t * (2 * a + t)) (a ^ 2 * (3 * a + 2 * t))
    (by positivity) (by positivity) (by positivity) (by positivity) (by ring) _
    (by simp only [vG, vD, vC, vO, sS]; ring) (by simp only [vG, vD, vC, vO, sS]; ring)

omit ha ht in
theorem mem_D : vD a t ∈ HT a t := subset_convexHull ℝ _ (by simp)
omit ha ht in
theorem mem_C : vC a t ∈ HT a t := subset_convexHull ℝ _ (by simp)
omit ha ht in
theorem mem_O : vO a t ∈ HT a t := subset_convexHull ℝ _ (by simp)

theorem sub_tri {x y z : ℝ × ℝ} (hx : x ∈ HT a t) (hy : y ∈ HT a t) (hz : z ∈ HT a t) :
    convexHull ℝ {x, y, z} ⊆ HT a t := by
  refine convexHull_min ?_ (convex_convexHull ℝ _)
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl | rfl <;> assumption

theorem sub1 : H1 a t ⊆ HT a t := sub_tri ha ht mem_O (mem_A ha ht) (mem_B ha ht)
theorem sub2 : H2 a t ⊆ HT a t := sub_tri ha ht (mem_A ha ht) (mem_E ha ht) mem_D
theorem sub3 : H3 a t ⊆ HT a t := sub_tri ha ht mem_C (mem_E ha ht) mem_D
theorem sub4 : H4 a t ⊆ HT a t := sub_tri ha ht mem_C (mem_E ha ht) (mem_G ha ht)
theorem sub5 : H5 a t ⊆ HT a t := by
  have hK : Convex ℝ {z : ℝ × ℝ | Lam (uu a t) (ww a t) z ∈ HT a t} :=
    (convex_convexHull ℝ ({vD a t, vC a t, vO a t} : Set (ℝ × ℝ))).linear_preimage (LamL (uu a t) (ww a t))
  have key := rect_subset hK ht ha
    (c00 := by
      show Lam (uu a t) (ww a t) (0, 0) ∈ HT a t
      have e : Lam (uu a t) (ww a t) (0, 0) = vB a t := by
        ext <;> simp only [Lam, uu, ww, vB, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring
      rw [e]; exact mem_B ha ht)
    (c10 := by
      show Lam (uu a t) (ww a t) (t, 0) ∈ HT a t
      have e : Lam (uu a t) (ww a t) (t, 0) = vC a t := by
        ext <;> simp only [Lam, uu, ww, vC, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring
      rw [e]; exact mem_C)
    (c01 := by
      show Lam (uu a t) (ww a t) (0, a) ∈ HT a t
      have e : Lam (uu a t) (ww a t) (0, a) = vA a t := by
        ext <;> simp only [Lam, uu, ww, vA, sS, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring
      rw [e]; exact mem_A ha ht)
    (c11 := by
      show Lam (uu a t) (ww a t) (t, a) ∈ HT a t
      have e : Lam (uu a t) (ww a t) (t, a) = vG a t := by
        ext <;> simp only [Lam, uu, ww, vG, sS, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring
      rw [e]; exact mem_G ha ht)
  rintro _ ⟨z, hz, rfl⟩
  exact key hz
end geom

/-! ### the tile and the pieces -/
section pieces
variable {a t c : ℝ} (ha : 0 < a) (ht : 0 < t) (hc0 : 0 < c)

/-- the model tile (scaled by `c`): legs `b c`, `a c` along the axes, hypotenuse `c²`. -/
noncomputable def Mod : Tri :=
  brickL 1 hf1 ((a + t) * c) (a * c) (by positivity) (by positivity)

include ha ht hc0 in
theorem hab_id (hc : c ^ 2 = 3 * a ^ 2 + 3 * a * t + t ^ 2) :
    ((a + t) * c) ^ 2 + (a * c) ^ 2 + ((a + t) * c) * (a * c) / 1 = (c ^ 2) ^ 2 := by
  linear_combination (-c ^ 2) * hc

include ha ht hc0 in
noncomputable def R1 (hc : c ^ 2 = 3 * a ^ 2 + 3 * a * t + t ^ 2) (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = c) :
    RTiling (Phi 1 '' H1 a t) (Mod ha ht hc0) (k * k) :=
  scaledRT 1 hf1 (vO a t) (vA a t) (vB a t) k hk0 (det1 ha ht) _
    (baseTri_cong _ _ _ _ ((c ^ 2) ^ 2) (by positivity) (by positivity) (hab_id ha ht hc0 hc) _ _ _ k hk0 _
      (by rw [hk]; simp only [vO, vA, vB, sS]
          linear_combination (-(a + t) ^ 2 * (3 * a ^ 2 + 3 * a * t + c ^ 2 + t ^ 2)) * hc)
      (by rw [hk]; simp only [vO, vA, vB, sS]
          linear_combination (-a ^ 2 * (3 * a ^ 2 + 3 * a * t + c ^ 2 + t ^ 2)) * hc)
      (by rw [hk]; simp only [vO, vA, vB, sS]
          linear_combination (-9 * a ^ 4 - 18 * a ^ 3 * t - 3 * a ^ 2 * c ^ 2 - 15 * a ^ 2 * t ^ 2 - 3 * a * c ^ 2 * t
            - 6 * a * t ^ 3 - c ^ 4 - c ^ 2 * t ^ 2 - t ^ 4) * hc))

include ha ht hc0 in
noncomputable def R2 (hc : c ^ 2 = 3 * a ^ 2 + 3 * a * t + t ^ 2) (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = a) :
    RTiling (Phi 1 '' H2 a t) (Mod ha ht hc0) (k * k) :=
  scaledRT 1 hf1 (vA a t) (vE a t) (vD a t) k hk0 (det2 ha ht) _
    (baseTri_cong _ _ _ _ ((c ^ 2) ^ 2) (by positivity) (by positivity) (hab_id ha ht hc0 hc) _ _ _ k hk0 _
      (by rw [hk]; simp only [vA, vE, vD, sS]
          linear_combination (-a ^ 2 * (a + t) ^ 2) * hc)
      (by rw [hk]; simp only [vA, vE, vD, sS]
          linear_combination (-a ^ 4) * hc)
      (by rw [hk]; simp only [vA, vE, vD, sS]
          linear_combination (-a ^ 2 * (3 * a ^ 2 + 3 * a * t + c ^ 2 + t ^ 2)) * hc))

include ha ht hc0 in
noncomputable def R3 (hc : c ^ 2 = 3 * a ^ 2 + 3 * a * t + t ^ 2) (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = a) :
    RTiling (Phi 1 '' H3 a t) (Mod ha ht hc0) (k * k) :=
  scaledRT 1 hf1 (vC a t) (vE a t) (vD a t) k hk0 (det3 ha ht) _
    (baseTri_cong _ _ _ _ ((c ^ 2) ^ 2) (by positivity) (by positivity) (hab_id ha ht hc0 hc) _ _ _ k hk0 _
      (by rw [hk]; simp only [vC, vE, vD, sS]
          linear_combination (-a ^ 2 * (a + t) ^ 2) * hc)
      (by rw [hk]; simp only [vC, vE, vD, sS]
          linear_combination (-a ^ 4) * hc)
      (by rw [hk]; simp only [vC, vE, vD, sS]
          linear_combination (-a ^ 2 * (3 * a ^ 2 + 3 * a * t + c ^ 2 + t ^ 2)) * hc))

include ha ht hc0 in
noncomputable def R4 (hc : c ^ 2 = 3 * a ^ 2 + 3 * a * t + t ^ 2) (k : ℕ) (hk0 : 0 < k) (hk : (k : ℝ) = a) :
    RTiling (Phi 1 '' H4 a t) (Mod ha ht hc0) (k * k) :=
  scaledRT 1 hf1 (vC a t) (vE a t) (vG a t) k hk0 (det4 ha ht) _
    (baseTri_cong _ _ _ _ ((c ^ 2) ^ 2) (by positivity) (by positivity) (hab_id ha ht hc0 hc) _ _ _ k hk0 _
      (by rw [hk]; simp only [vC, vE, vG, sS]
          linear_combination (-a ^ 2 * (a + t) ^ 2) * hc)
      (by rw [hk]; simp only [vC, vE, vG, sS]
          linear_combination (-a ^ 4) * hc)
      (by rw [hk]; simp only [vC, vE, vG, sS]
          linear_combination (-a ^ 2 * (3 * a ^ 2 + 3 * a * t + c ^ 2 + t ^ 2)) * hc))

/-! ### the parallelogram -/
include ha ht hc0 in
theorem cong_TL (hc : c ^ 2 = 3 * a ^ 2 + 3 * a * t + t ^ 2) :
    (TL hf1 (uu a t) (ww a t) (detL ha ht)).Congruent (Mod ha ht hc0) := by
  unfold TL Mod brickL
  refine triC_cong hf1 _ _ _ _ _ _ _ _ ?_ ?_ ?_ <;>
    simp only [uu, ww, sS, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero]
  · linear_combination (-(a + t) ^ 2) * hc
  · linear_combination (-a ^ 2) * hc
  · linear_combination (-(3 * a ^ 2 + 3 * a * t + t ^ 2)) * hc

include ha ht hc0 in
theorem cong_TU (hc : c ^ 2 = 3 * a ^ 2 + 3 * a * t + t ^ 2) :
    (TU hf1 (uu a t) (ww a t) (detL ha ht)).Congruent (Mod ha ht hc0) := by
  unfold TU Mod brickL
  refine triC_cong hf1 _ _ _ _ _ _ _ _ ?_ ?_ ?_ <;>
    simp only [uu, ww, sS, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero]
  · linear_combination (-(a + t) ^ 2) * hc
  · linear_combination (-a ^ 2) * hc
  · linear_combination (-(3 * a ^ 2 + 3 * a * t + t ^ 2)) * hc

include ha ht hc0 in
/-- the `(k+1) × (l+1)` parallelogram of cells, `2 (k+1)(l+1)` tiles. -/
noncomputable def R5 (hc : c ^ 2 = 3 * a ^ 2 + 3 * a * t + t ^ 2) (k l : ℕ) (hk : (k : ℝ) + 1 = t) (hl : (l : ℝ) + 1 = a) :
    RTiling (Phi 1 '' H5 a t) (Mod ha ht hc0) (2 * (k + 1) * (l + 1)) := by
  have G := gridT (ThH hf1 (uu a t) (ww a t) (detL ha ht))
    (ThH_add hf1 (uu a t) (ww a t) (detL ha ht)) (A := 1) (B := 1) one_pos one_pos
    (cellRT hf1 (uu a t) (ww a t) (detL ha ht) (Mod ha ht hc0) (cong_TL ha ht hc0 hc) (cong_TU ha ht hc0 hc)) k l
  rw [ThH_image] at G
  rw [hk, hl, one_mul, one_mul] at G
  exact G

end pieces

/-! ### assembly -/
noncomputable def regionOf (a t : ℝ) : Fin 5 → Set Plane := fun i => match i with
  | ⟨0, _⟩ => Phi 1 '' H1 a t
  | ⟨1, _⟩ => Phi 1 '' H2 a t
  | ⟨2, _⟩ => Phi 1 '' H3 a t
  | ⟨3, _⟩ => Phi 1 '' H4 a t
  | ⟨4, _⟩ => Phi 1 '' H5 a t
  | ⟨k + 5, h⟩ => absurd h (by omega)

def cnt (kc ka nt : ℕ) : Fin 5 → ℕ := fun i => match i with
  | ⟨0, _⟩ => kc * kc
  | ⟨1, _⟩ => ka * ka
  | ⟨2, _⟩ => ka * ka
  | ⟨3, _⟩ => ka * ka
  | ⟨4, _⟩ => 2 * nt * ka
  | ⟨k + 5, h⟩ => absurd h (by omega)

section asm
variable {a t c : ℝ} (ha : 0 < a) (ht : 0 < t) (hc0 : 0 < c)
include ha ht

/-- the target triangle `D C O`. -/
noncomputable def tgt (a t : ℝ) (ha : 0 < a) (ht : 0 < t) : Tri :=
  triC 1 hf1 (vD a t) (vC a t) (vO a t) (detT ha ht)

theorem hS_all : ∀ i j : Fin 5, i ≠ j →
    Disjoint (interior (regionOf a t i)) (interior (regionOf a t j)) := by
  intro i j hij
  exact match i, j with
  | ⟨0, _⟩, ⟨0, _⟩ => absurd rfl hij
  | ⟨0, _⟩, ⟨1, _⟩ => d12 ha ht hf1
  | ⟨0, _⟩, ⟨2, _⟩ => d13 ha ht hf1
  | ⟨0, _⟩, ⟨3, _⟩ => d14 ha ht hf1
  | ⟨0, _⟩, ⟨4, _⟩ => d15 ha ht hf1
  | ⟨1, _⟩, ⟨0, _⟩ => (d12 ha ht hf1).symm
  | ⟨1, _⟩, ⟨1, _⟩ => absurd rfl hij
  | ⟨1, _⟩, ⟨2, _⟩ => d23 ha ht hf1
  | ⟨1, _⟩, ⟨3, _⟩ => d24 ha ht hf1
  | ⟨1, _⟩, ⟨4, _⟩ => d25 ha ht hf1
  | ⟨2, _⟩, ⟨0, _⟩ => (d13 ha ht hf1).symm
  | ⟨2, _⟩, ⟨1, _⟩ => (d23 ha ht hf1).symm
  | ⟨2, _⟩, ⟨2, _⟩ => absurd rfl hij
  | ⟨2, _⟩, ⟨3, _⟩ => d34 ha ht hf1
  | ⟨2, _⟩, ⟨4, _⟩ => d35 ha ht hf1
  | ⟨3, _⟩, ⟨0, _⟩ => (d14 ha ht hf1).symm
  | ⟨3, _⟩, ⟨1, _⟩ => (d24 ha ht hf1).symm
  | ⟨3, _⟩, ⟨2, _⟩ => (d34 ha ht hf1).symm
  | ⟨3, _⟩, ⟨3, _⟩ => absurd rfl hij
  | ⟨3, _⟩, ⟨4, _⟩ => d45 ha ht hf1
  | ⟨4, _⟩, ⟨0, _⟩ => (d15 ha ht hf1).symm
  | ⟨4, _⟩, ⟨1, _⟩ => (d25 ha ht hf1).symm
  | ⟨4, _⟩, ⟨2, _⟩ => (d35 ha ht hf1).symm
  | ⟨4, _⟩, ⟨3, _⟩ => (d45 ha ht hf1).symm
  | ⟨4, _⟩, ⟨4, _⟩ => absurd rfl hij
  | ⟨k + 5, h⟩, _ => absurd h (by omega)
  | _, ⟨k + 5, h⟩ => absurd h (by omega)

theorem hsub_all : ∀ i : Fin 5, regionOf a t i ⊆ (tgt a t ha ht).carrier := by
  have hc : (tgt a t ha ht).carrier = Phi 1 '' HT a t := carrier_triC _ _ _ _ _ _
  intro i
  rw [hc]
  exact match i with
  | ⟨0, _⟩ => Set.image_mono (sub1 ha ht)
  | ⟨1, _⟩ => Set.image_mono (sub2 ha ht)
  | ⟨2, _⟩ => Set.image_mono (sub3 ha ht)
  | ⟨3, _⟩ => Set.image_mono (sub4 ha ht)
  | ⟨4, _⟩ => Set.image_mono (sub5 ha ht)
  | ⟨k + 5, h⟩ => absurd h (by omega)

include hc0 in
open MeasureTheory in
theorem volMod (hc : c ^ 2 = 3 * a ^ 2 + 3 * a * t + t ^ 2) : volume (Mod ha ht hc0).carrier
    = ENNReal.ofReal (|sD 1 / (2 * 1)| * (a * (a + t) * (3 * a ^ 2 + 3 * a * t + t ^ 2)))
      * volume Erdos634.AreaDet.stdCarrier := by
  unfold Mod brickL
  rw [vol_triC]
  congr 2
  rw [abs_mul]
  congr 1
  have hX : 0 < a * (a + t) * (3 * a ^ 2 + 3 * a * t + t ^ 2) := by positivity
  rw [← abs_of_pos hX]
  congr 1
  dsimp only
  linear_combination (a * (a + t)) * hc

open MeasureTheory in
theorem volTgt : volume (tgt a t ha ht).carrier
    = ENNReal.ofReal (|sD 1 / (2 * 1)| * (a * (a + t) * (2 * a + t) * (3 * a + t) * (3 * a ^ 2 + 3 * a * t + t ^ 2)))
      * volume Erdos634.AreaDet.stdCarrier := by
  unfold tgt
  rw [vol_triC]
  congr 2
  rw [abs_mul]
  congr 1
  have hX : 0 < a * (a + t) * (2 * a + t) * (3 * a + t) * (3 * a ^ 2 + 3 * a * t + t ^ 2) := by positivity
  rw [← abs_of_pos hX]
  congr 1
  simp only [vD, vC, vO, sS]
  ring

include hc0 in
open MeasureTheory in
theorem hvol_all (hc : c ^ 2 = 3 * a ^ 2 + 3 * a * t + t ^ 2) (N : ℕ) (hN : (N : ℝ) = (3 * a + t) * (2 * a + t)) :
    (N : ENNReal) * volume (Mod ha ht hc0).carrier = volume (tgt a t ha ht).carrier := by
  rw [volMod ha ht hc0 hc, volTgt ha ht, ← mul_assoc, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 2
  rw [hN]; ring

/-- **The F4 layout, real parameters.** -/
theorem f4_real (hc : c ^ 2 = 3 * a ^ 2 + 3 * a * t + t ^ 2) (kc ka nt N : ℕ) (hNsum : ∑ i, cnt kc ka nt i = N) (hkc0 : 0 < kc)
    (hka0 : 0 < ka) (hnt0 : 0 < nt) (hkc : (kc : ℝ) = c) (hka : (ka : ℝ) = a) (hnt : (nt : ℝ) = t) :
    ∃ D : CongruentDissection N, D.model = Mod ha ht hc0 ∧ D.target = tgt a t ha ht := by
  subst hNsum
  have R : ∀ i : Fin 5, RTiling (regionOf a t i) (Mod ha ht hc0) (cnt kc ka nt i) := fun i => match i with
    | ⟨0, _⟩ => R1 ha ht hc0 hc kc hkc0 hkc
    | ⟨1, _⟩ => R2 ha ht hc0 hc ka hka0 hka
    | ⟨2, _⟩ => R3 ha ht hc0 hc ka hka0 hka
    | ⟨3, _⟩ => R4 ha ht hc0 hc ka hka0 hka
    | ⟨4, _⟩ => RTiling.castN (by
          show 2 * (nt - 1 + 1) * (ka - 1 + 1) = 2 * nt * ka
          rw [Nat.sub_add_cancel hnt0, Nat.sub_add_cancel hka0])
        (R5 ha ht hc0 hc (nt - 1) (ka - 1)
          (by have := Nat.sub_add_cancel hnt0; rw [← hnt]; exact_mod_cast this)
          (by have := Nat.sub_add_cancel hka0; rw [← hka]; exact_mod_cast this))
    | ⟨k + 5, h⟩ => absurd h (by omega)
  refine pack_exists (M := Mod ha ht hc0) (T := tgt a t ha ht) (regionOf a t) (cnt kc ka nt) R
    (hS_all ha ht) (hsub_all ha ht) (hvol_all ha ht hc0 hc _ ?_)
  rw [Fin.sum_univ_five]
  show (((kc * kc + ka * ka + ka * ka + ka * ka + 2 * nt * ka : ℕ)) : ℝ) = _
  push_cast
  rw [hkc, hka, hnt]
  linear_combination hc

/-! ### side lengths of the layout (frame scale `c`) -/
include hc0 in
/-- Sides of the target `D C O` and of the model: `c·(a c, b (2a+b), (a+b) c)` and `c·(b, a, c)`. -/
theorem sides_real (hc : c ^ 2 = 3 * a ^ 2 + 3 * a * t + t ^ 2) :
    dist ((tgt a t ha ht).pts 0) ((tgt a t ha ht).pts 1) = c * (a * c) ∧
    dist ((tgt a t ha ht).pts 1) ((tgt a t ha ht).pts 2) = c * ((a + t) * (3 * a + t)) ∧
    dist ((tgt a t ha ht).pts 2) ((tgt a t ha ht).pts 0) = c * ((2 * a + t) * c) ∧
    dist ((Mod ha ht hc0).pts 0) ((Mod ha ht hc0).pts 1) = c * (a + t) ∧
    dist ((Mod ha ht hc0).pts 1) ((Mod ha ht hc0).pts 2) = c * a ∧
    dist ((Mod ha ht hc0).pts 2) ((Mod ha ht hc0).pts 0) = c * c := by
  have hx : ∀ x y : ℝ × ℝ, ∀ r : ℝ, 0 ≤ r → ((x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2 + (x.1 - y.1) * (x.2 - y.2) / 1 = r ^ 2) →
      dist (Phi 1 x) (Phi 1 y) = r := fun x y r hr h => by
    refine f4_eq_of_sq dist_nonneg hr ?_
    rw [sq_Phi' hf1]; exact h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [tgt, triC_pts]
    exact hx _ _ _ (by positivity) (by simp only [vD, vC, sS]; linear_combination (-a ^ 2 * (3 * a ^ 2 + 3 * a * t + c ^ 2 + t ^ 2)) * hc)
  · simp only [tgt, triC_pts]
    exact hx _ _ _ (by positivity) (by simp only [vC, vO, sS]; linear_combination (-(a + t) ^ 2 * (3 * a + t) ^ 2) * hc)
  · simp only [tgt, triC_pts]
    exact hx _ _ _ (by positivity) (by simp only [vO, vD, sS]; linear_combination (-(2 * a + t) ^ 2 * (3 * a ^ 2 + 3 * a * t + c ^ 2 + t ^ 2)) * hc)
  · simp only [Mod, brickL, triC_pts]
    exact hx _ _ _ (by positivity) (by simp only []; ring)
  · simp only [Mod, brickL, triC_pts]
    exact hx _ _ _ (by positivity) (by simp only []; ring)
  · simp only [Mod, brickL, triC_pts]
    exact hx _ _ _ (by positivity) (by simp only []; linear_combination (-c ^ 2) * hc)

end asm

/-! ### the theorems for naturals `0 < a < b`, `c² = a² + ab + b²` -/
theorem f4_family_dissection (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    Nonempty (CongruentDissection ((2 * a + b) * (a + b))) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hab.le
  have hs : 0 < s := by omega
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · subst h
      have : 0 < a ^ 2 := by positivity
      nlinarith
    · exact h
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have ht' : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hc0' : (0 : ℝ) < c := by exact_mod_cast hc0
  have hcR : (c : ℝ) ^ 2 = 3 * (a : ℝ) ^ 2 + 3 * a * s + s ^ 2 := by
    have : (c : ℝ) ^ 2 = (a : ℝ) ^ 2 + a * (a + s) + (a + s) ^ 2 := by exact_mod_cast hc
    rw [this]; ring
  have hsum : ∑ i, cnt c a s i = (2 * a + (a + s)) * (a + (a + s)) := by
    rw [Fin.sum_univ_five]
    show c * c + a * a + a * a + a * a + 2 * s * a = _
    nlinarith [hc]
  obtain ⟨D, -, -⟩ := f4_real (a := (a : ℝ)) (t := (s : ℝ)) (c := (c : ℝ)) ha' ht' hc0' hcR c a s _ hsum
    hc0 ha hs rfl rfl rfl
  exact ⟨D⟩

/-- **F4 for all Eisenstein triples with `a < b`** (construction of D. Paliy): `(2a+b)(a+b)` is a tile count. -/
theorem f4_family (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    Erdos634.Draft.TileCountFamilies.TileCount ((2 * a + b) * (a + b)) :=
  f4_family_dissection a b c ha hab hc

/-- with the side lengths: the target has sides `c·(a c, b (2a+b), (a+b) c)` and the tile `c·(b, a, c)`. -/
theorem f4_family_sides (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ∃ D : CongruentDissection ((2 * a + b) * (a + b)),
      dist (D.target.pts 0) (D.target.pts 1) = (c : ℝ) * ((a : ℝ) * c) ∧
      dist (D.target.pts 1) (D.target.pts 2) = (c : ℝ) * ((b : ℝ) * (2 * a + b)) ∧
      dist (D.target.pts 2) (D.target.pts 0) = (c : ℝ) * (((a : ℝ) + b) * c) ∧
      dist (D.model.pts 0) (D.model.pts 1) = (c : ℝ) * b ∧
      dist (D.model.pts 1) (D.model.pts 2) = (c : ℝ) * a ∧
      dist (D.model.pts 2) (D.model.pts 0) = (c : ℝ) * c := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hab.le
  have hs : 0 < s := by omega
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · subst h
      have : 0 < a ^ 2 := by positivity
      nlinarith
    · exact h
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have ht' : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hc0' : (0 : ℝ) < c := by exact_mod_cast hc0
  have hcR : (c : ℝ) ^ 2 = 3 * (a : ℝ) ^ 2 + 3 * a * s + s ^ 2 := by
    have : (c : ℝ) ^ 2 = (a : ℝ) ^ 2 + a * (a + s) + (a + s) ^ 2 := by exact_mod_cast hc
    rw [this]; ring
  have hsum : ∑ i, cnt c a s i = (2 * a + (a + s)) * (a + (a + s)) := by
    rw [Fin.sum_univ_five]
    show c * c + a * a + a * a + a * a + 2 * s * a = _
    nlinarith [hc]
  obtain ⟨D, hM, hT⟩ := f4_real (a := (a : ℝ)) (t := (s : ℝ)) (c := (c : ℝ)) ha' ht' hc0' hcR c a s _ hsum
    hc0 ha hs rfl rfl rfl
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := sides_real ha' ht' hc0' hcR
  refine ⟨D, ?_⟩
  rw [hT, hM]
  push_cast
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [s1]
  · rw [s2]; try ring
  · rw [s3]; try ring
  · rw [s4]; try ring
  · rw [s5]
  · rw [s6]

end Erdos634.Draft.F4All

/-- witness: `(a, b, c) = (7, 8, 13)` gives `330` (compare `Draft.N330.tileCount_330`, the same shape: there the target is
`338·(91, 176, 195)` and the tile `338·(13, 8, 7)`; here target `13·(91, 176, 195)`, tile `13·(8, 7, 13)`; ratio `26`). -/
theorem Erdos634.Draft.F4All.tileCount_330_from_family :
    Erdos634.Draft.TileCountFamilies.TileCount 330 := by
  have := f4_family 7 8 13 (by norm_num) (by norm_num) (by norm_num)
  norm_num at this
  exact this

/-- the `(7, 8, 13)` instance has the sides of `Draft.N330`'s tiling divided by `26`: target `13·(91, 176, 195)` against
`338·(91, 176, 195)`, tile `13·(13, 8, 7)` against `338·(13, 8, 7)`. -/
theorem Erdos634.Draft.F4All.sides_7_8_13 :
    ∃ D : CongruentDissection 330,
      dist (D.target.pts 0) (D.target.pts 1) = 1183 ∧ dist (D.target.pts 1) (D.target.pts 2) = 2288 ∧
      dist (D.target.pts 2) (D.target.pts 0) = 2535 ∧
      dist (D.model.pts 0) (D.model.pts 1) = 104 ∧ dist (D.model.pts 1) (D.model.pts 2) = 91 ∧
      dist (D.model.pts 2) (D.model.pts 0) = 169 := by
  have h := f4_family_sides 7 8 13 (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- agreement with `Draft.N330`: the sides above times `26` are exactly `30758, 59488, 65910` (target) and
`4394 = 26·169, 2704 = 26·104, 2366 = 26·91` (tile) of `N330.dissection_330_sides`. -/
theorem Erdos634.Draft.F4All.sides_agree_N330 :
    (26 : ℝ) * 1183 = 30758 ∧ (26 : ℝ) * 2288 = 59488 ∧ (26 : ℝ) * 2535 = 65910 ∧
    (26 : ℝ) * 169 = 4394 ∧ (26 : ℝ) * 104 = 2704 ∧ (26 : ℝ) * 91 = 2366 := by
  norm_num

#print axioms Erdos634.Draft.F4All.f4_family
#print axioms Erdos634.Draft.F4All.f4_family_sides
#print axioms Erdos634.Draft.F4All.tileCount_330_from_family
#print axioms Erdos634.Draft.F4All.sides_7_8_13
