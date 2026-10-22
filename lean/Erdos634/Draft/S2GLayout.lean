-- Draft/S2GLayout.lean — S2G: the layout L(p,q) (general p), as exact skew coordinates in the frame Φ_f, f = -c/A,
-- all polynomial in (P, g) = (p², q²-2p²) with b = P+g, c = 2P+g, A = 3P+2g, B = 5P+3g.  UNAUDITED.  Not imported into All.lean.
-- PROVED HERE for REAL P > 0, g > 0: all vertices lie in the target hull; the six regions lie in the target hull;
-- the 15 pairs of regions have disjoint interiors (6 separating lines); non-degeneracy of every piece.
-- Pieces:  T1 = (C,O,Q)  T2 = (P,O,Q)  T3 = (C,R,Q)  (scale c)   Y = (Q,P,V) (scale pq)   M = (V,P',P) (scale b)
--          S = Rect (c²+b²) (bB) 0 (bc)  (g × c cells [0,c]×[0,b]).
-- Exact numerical data: (private working notes, not included) (tables); blueprint (private working notes, not included) §2,§5,§8.
import Erdos634.Draft.S2GFrame

open scoped Classical
set_option linter.unusedSectionVars false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Rect RTiling.cast RTiling.castN interior_disj_fst interior_disj_snd)

namespace Erdos634.Draft.S2G
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF
open Erdos634.Draft.S2L (hull_le hull_ge mem_hull3' rect_subset tri_le tri_ge tri_fst_le tri_fst_ge tri_snd_le tri_snd_ge)

/-- close `a < b` likewise. -/
macro "ppos_lt" : tactic => `(tactic| first
  | (rw [← sub_pos]; ring_nf; positivity))

/-- close `a ≤ b` when `b - a` is a polynomial with nonnegative coefficients in the positive atoms. -/
macro "ppos" : tactic => `(tactic| first
  | (rw [← sub_nonneg]; ring_nf; positivity)
  | (rw [← sub_nonneg]; ring_nf)
  | (rw [← sub_nonneg]; ring_nf; exact le_refl _))

def pO : ℝ × ℝ := (0, 0)
def pB (P g : ℝ) : ℝ × ℝ := ((P + g) * (5 * P + 3 * g), 0)
def pC (P g : ℝ) : ℝ × ℝ := ((P + g) * (5 * P + 3 * g), (3 * P + 2 * g) * (2 * P + g))
def pQ (P g : ℝ) : ℝ × ℝ := ((3 * P + 2 * g) * (P + g), (2 * P + g) * (P + g))
def pP (P g : ℝ) : ℝ × ℝ := ((2 * P + g) ^ 2, 0)
def pR (P g : ℝ) : ℝ × ℝ := ((P + g) * (5 * P + 3 * g), (P + g) * (2 * P + g))
def pV (P g : ℝ) : ℝ × ℝ := ((2 * P + g) ^ 2 + (P + g) ^ 2, (P + g) * (2 * P + g))
def pW (P g : ℝ) : ℝ × ℝ := ((2 * P + g) ^ 2 + (P + g) ^ 2, 0)   -- P'

def H1 (P g : ℝ) : Set (ℝ × ℝ) := convexHull ℝ {pC P g, pO, pQ P g}
def H2 (P g : ℝ) : Set (ℝ × ℝ) := convexHull ℝ {pP P g, pO, pQ P g}
def H3 (P g : ℝ) : Set (ℝ × ℝ) := convexHull ℝ {pC P g, pR P g, pQ P g}
def H4 (P g : ℝ) : Set (ℝ × ℝ) := convexHull ℝ {pQ P g, pP P g, pV P g}
def H5 (P g : ℝ) : Set (ℝ × ℝ) := convexHull ℝ {pV P g, pW P g, pP P g}
def H6 (P g : ℝ) : Set (ℝ × ℝ) := Rect ((2 * P + g) ^ 2 + (P + g) ^ 2) ((P + g) * (5 * P + 3 * g)) 0 ((P + g) * (2 * P + g))
def HT (P g : ℝ) : Set (ℝ × ℝ) := convexHull ℝ {pO, pB P g, pC P g}

theorem rect_le {x0 x1 y0 y1 : ℝ} (h0 : x0 < x1) (h1 : y0 < y1) (a b c : ℝ)
    (c00 : a * x0 + b * y0 ≤ c) (c10 : a * x1 + b * y0 ≤ c) (c01 : a * x0 + b * y1 ≤ c)
    (c11 : a * x1 + b * y1 ≤ c) : ∀ p ∈ Rect x0 x1 y0 y1, a * p.1 + b * p.2 ≤ c := by
  have hK : Convex ℝ {p : ℝ × ℝ | a * p.1 + b * p.2 ≤ c} := by
    intro x hx y hy s t hs ht hst
    simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at *
    have hc' : s * c + t * c = c := by rw [← add_mul, hst, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left hx hs, mul_le_mul_of_nonneg_left hy ht]
  exact fun p hp => rect_subset hK h0 h1 c00 c10 c01 c11 hp

theorem rect_ge {x0 x1 y0 y1 : ℝ} (h0 : x0 < x1) (h1 : y0 < y1) (a b c : ℝ)
    (c00 : c ≤ a * x0 + b * y0) (c10 : c ≤ a * x1 + b * y0) (c01 : c ≤ a * x0 + b * y1)
    (c11 : c ≤ a * x1 + b * y1) : ∀ p ∈ Rect x0 x1 y0 y1, c ≤ a * p.1 + b * p.2 := by
  intro p hp
  have := rect_le h0 h1 (-a) (-b) (-c) (by linarith) (by linarith) (by linarith) (by linarith) p hp
  linarith

section facts
variable {P g : ℝ} (hP : 0 < P) (hg : 0 < g)
include hP hg

/-! ### membership in the target hull (via a generic half-plane characterisation) -/
theorem mem_HT (p : ℝ × ℝ) (h1 : 0 ≤ p.2) (h2 : p.1 ≤ (P + g) * (5 * P + 3 * g))
    (h3 : (P + g) * (5 * P + 3 * g) * p.2 ≤ (3 * P + 2 * g) * (2 * P + g) * p.1) : p ∈ HT P g := by
  have hD : 0 < (3 * P + 2 * g) * (2 * P + g) * ((P + g) * (5 * P + 3 * g)) := by positivity
  refine mem_hull3' (A := pO) (B := pB P g) (C := pC P g)
    ((3 * P + 2 * g) * (2 * P + g) * ((P + g) * (5 * P + 3 * g)))
    ((3 * P + 2 * g) * (2 * P + g) * ((P + g) * (5 * P + 3 * g) - p.1))
    ((3 * P + 2 * g) * (2 * P + g) * p.1 - (P + g) * (5 * P + 3 * g) * p.2)
    ((P + g) * (5 * P + 3 * g) * p.2) hD
    (mul_nonneg (by positivity) (by linarith)) (by linarith) (mul_nonneg (by positivity) h1)
    (by ring) p ?_ ?_
  · simp only [pO, pB, pC]; ring
  · simp only [pO, pB, pC]; ring

theorem pQ_mem : pQ P g ∈ HT P g := mem_HT hP hg _ (by simp only [pQ]; positivity)
  (by simp only [pQ]; ppos) (by simp only [pQ]; ppos)
theorem pP_mem : pP P g ∈ HT P g := mem_HT hP hg _ (by simp only [pP]; positivity)
  (by simp only [pP]; ppos) (by simp only [pP]; ppos)
theorem pR_mem : pR P g ∈ HT P g := mem_HT hP hg _ (by simp only [pR]; positivity)
  (by simp only [pR]; ppos) (by simp only [pR]; ppos)
theorem pV_mem : pV P g ∈ HT P g := mem_HT hP hg _ (by simp only [pV]; positivity)
  (by simp only [pV]; ppos) (by simp only [pV]; ppos)
theorem pW_mem : pW P g ∈ HT P g := mem_HT hP hg _ (by simp only [pW]; positivity)
  (by simp only [pW]; ppos) (by simp only [pW]; ppos)
omit hP hg in
theorem pO_mem : pO ∈ HT P g := subset_convexHull ℝ _ (by simp)
omit hP hg in
theorem pB_mem : pB P g ∈ HT P g := subset_convexHull ℝ _ (by simp)
omit hP hg in
theorem pC_mem : pC P g ∈ HT P g := subset_convexHull ℝ _ (by simp)

theorem sub_tri {a b c : ℝ × ℝ} (ha : a ∈ HT P g) (hb : b ∈ HT P g) (hc : c ∈ HT P g) :
    convexHull ℝ {a, b, c} ⊆ HT P g := by
  refine convexHull_min ?_ (convex_convexHull ℝ _)
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl | rfl <;> assumption

theorem sub1 : H1 P g ⊆ HT P g := sub_tri hP hg pC_mem pO_mem (pQ_mem hP hg)
theorem sub2 : H2 P g ⊆ HT P g := sub_tri hP hg (pP_mem hP hg) pO_mem (pQ_mem hP hg)
theorem sub3 : H3 P g ⊆ HT P g := sub_tri hP hg pC_mem (pR_mem hP hg) (pQ_mem hP hg)
theorem sub4 : H4 P g ⊆ HT P g := sub_tri hP hg (pQ_mem hP hg) (pP_mem hP hg) (pV_mem hP hg)
theorem sub5 : H5 P g ⊆ HT P g := sub_tri hP hg (pV_mem hP hg) (pW_mem hP hg) (pP_mem hP hg)
theorem sub6 : H6 P g ⊆ HT P g := by
  refine rect_subset (convex_convexHull ℝ _) (by ppos_lt) (by ppos_lt) ?_ ?_ ?_ ?_
  · exact pW_mem hP hg
  · exact pB_mem
  · exact pV_mem hP hg
  · exact pR_mem hP hg

/-! ### separating functionals.  c = 2P+g, b = P+g, A = 3P+2g.  -/
-- L_OQ = -c x + A y   (T1: ≥ 0;  T2, Y, M, S: ≤ 0)
theorem T1_lo : ∀ p ∈ H1 P g, 0 ≤ (-(2 * P + g)) * p.1 + (3 * P + 2 * g) * p.2 :=
  tri_ge (A := pC P g) (B := pO) (C := pQ P g) _ _ _ (by simp only [pC]; ppos) (by simp only [pO]; ppos)
    (by simp only [pQ]; ppos)
theorem T2_lo : ∀ p ∈ H2 P g, (-(2 * P + g)) * p.1 + (3 * P + 2 * g) * p.2 ≤ 0 :=
  tri_le (A := pP P g) (B := pO) (C := pQ P g) _ _ _ (by simp only [pP]; ppos) (by simp only [pO]; ppos)
    (by simp only [pQ]; ppos)
theorem Y_lo : ∀ p ∈ H4 P g, (-(2 * P + g)) * p.1 + (3 * P + 2 * g) * p.2 ≤ 0 :=
  tri_le (A := pQ P g) (B := pP P g) (C := pV P g) _ _ _ (by simp only [pQ]; ppos) (by simp only [pP]; ppos)
    (by simp only [pV]; ppos)
theorem M_lo : ∀ p ∈ H5 P g, (-(2 * P + g)) * p.1 + (3 * P + 2 * g) * p.2 ≤ 0 :=
  tri_le (A := pV P g) (B := pW P g) (C := pP P g) _ _ _ (by simp only [pV]; ppos) (by simp only [pW]; ppos)
    (by simp only [pP]; ppos)
theorem S_lo : ∀ p ∈ H6 P g, (-(2 * P + g)) * p.1 + (3 * P + 2 * g) * p.2 ≤ 0 :=
  rect_le (by ppos_lt) (by ppos_lt) _ _ _ (by ppos) (by ppos) (by ppos) (by ppos)

-- L_CQ = c x - b y   vs  b c²   (T1: ≤ ; T3: ≥)
theorem T1_lc : ∀ p ∈ H1 P g, (2 * P + g) * p.1 + (-(P + g)) * p.2 ≤ (P + g) * (2 * P + g) ^ 2 :=
  tri_le (A := pC P g) (B := pO) (C := pQ P g) _ _ _ (by simp only [pC]; ppos) (by simp only [pO]; ppos)
    (by simp only [pQ]; ppos)
theorem T3_lc : ∀ p ∈ H3 P g, (P + g) * (2 * P + g) ^ 2 ≤ (2 * P + g) * p.1 + (-(P + g)) * p.2 :=
  tri_ge (A := pC P g) (B := pR P g) (C := pQ P g) _ _ _ (by simp only [pC]; ppos) (by simp only [pR]; ppos)
    (by simp only [pQ]; ppos)

-- L_QP = c b x + (c² - A b) y  vs  b c³   (T2: ≤ ; T3, Y, M, S: ≥)
theorem T2_lq : ∀ p ∈ H2 P g, (2 * P + g) * (P + g) * p.1 + ((2 * P + g) ^ 2 - (3 * P + 2 * g) * (P + g)) * p.2
    ≤ (P + g) * (2 * P + g) ^ 3 :=
  tri_le (A := pP P g) (B := pO) (C := pQ P g) _ _ _ (by simp only [pP]; ppos) (by simp only [pO]; ppos)
    (by simp only [pQ]; ppos)
theorem T3_lq : ∀ p ∈ H3 P g, (P + g) * (2 * P + g) ^ 3 ≤ (2 * P + g) * (P + g) * p.1 + ((2 * P + g) ^ 2 - (3 * P + 2 * g) * (P + g)) * p.2 :=
  tri_ge (A := pC P g) (B := pR P g) (C := pQ P g) _ _ _ (by simp only [pC]; ppos) (by simp only [pR]; ppos)
    (by simp only [pQ]; ppos)
theorem Y_lq : ∀ p ∈ H4 P g, (P + g) * (2 * P + g) ^ 3 ≤ (2 * P + g) * (P + g) * p.1 + ((2 * P + g) ^ 2 - (3 * P + 2 * g) * (P + g)) * p.2 :=
  tri_ge (A := pQ P g) (B := pP P g) (C := pV P g) _ _ _ (by simp only [pQ]; ppos) (by simp only [pP]; ppos)
    (by simp only [pV]; ppos)
theorem M_lq : ∀ p ∈ H5 P g, (P + g) * (2 * P + g) ^ 3 ≤ (2 * P + g) * (P + g) * p.1 + ((2 * P + g) ^ 2 - (3 * P + 2 * g) * (P + g)) * p.2 :=
  tri_ge (A := pV P g) (B := pW P g) (C := pP P g) _ _ _ (by simp only [pV]; ppos) (by simp only [pW]; ppos)
    (by simp only [pP]; ppos)
theorem S_lq : ∀ p ∈ H6 P g, (P + g) * (2 * P + g) ^ 3 ≤ (2 * P + g) * (P + g) * p.1 + ((2 * P + g) ^ 2 - (3 * P + 2 * g) * (P + g)) * p.2 :=
  rect_ge (by ppos_lt) (by ppos_lt) _ _ _ (by ppos) (by ppos) (by ppos) (by ppos)

-- horizontal y = b c   (T3: ≥ ; Y, M, S: ≤)
theorem T3_y : ∀ p ∈ H3 P g, (P + g) * (2 * P + g) ≤ p.2 :=
  tri_snd_ge (A := pC P g) (B := pR P g) (C := pQ P g) _ (by simp only [pC]; ppos) (by simp only [pR]; ppos)
    (by simp only [pQ]; ppos)
theorem Y_y : ∀ p ∈ H4 P g, p.2 ≤ (P + g) * (2 * P + g) :=
  tri_snd_le (A := pQ P g) (B := pP P g) (C := pV P g) _ (by simp only [pQ]; ppos) (by simp only [pP]; ppos)
    (by simp only [pV]; ppos)
theorem M_y : ∀ p ∈ H5 P g, p.2 ≤ (P + g) * (2 * P + g) :=
  tri_snd_le (A := pV P g) (B := pW P g) (C := pP P g) _ (by simp only [pV]; ppos) (by simp only [pW]; ppos)
    (by simp only [pP]; ppos)
theorem S_y : ∀ p ∈ H6 P g, p.2 ≤ (P + g) * (2 * P + g) := by
  rintro p ⟨a1, a2, a3, a4⟩; exact a4

-- L_PV = c x - b y  vs  c³   (Y: ≤ ; M, S: ≥)
theorem Y_lv : ∀ p ∈ H4 P g, (2 * P + g) * p.1 + (-(P + g)) * p.2 ≤ (2 * P + g) ^ 3 :=
  tri_le (A := pQ P g) (B := pP P g) (C := pV P g) _ _ _ (by simp only [pQ]; ppos) (by simp only [pP]; ppos)
    (by simp only [pV]; ppos)
theorem M_lv : ∀ p ∈ H5 P g, (2 * P + g) ^ 3 ≤ (2 * P + g) * p.1 + (-(P + g)) * p.2 :=
  tri_ge (A := pV P g) (B := pW P g) (C := pP P g) _ _ _ (by simp only [pV]; ppos) (by simp only [pW]; ppos)
    (by simp only [pP]; ppos)
theorem S_lv : ∀ p ∈ H6 P g, (2 * P + g) ^ 3 ≤ (2 * P + g) * p.1 + (-(P + g)) * p.2 :=
  rect_ge (by ppos_lt) (by ppos_lt) _ _ _ (by ppos) (by ppos) (by ppos) (by ppos)

-- vertical x = c² + b²  (M: ≤ ; S: ≥)
theorem M_x : ∀ p ∈ H5 P g, p.1 ≤ (2 * P + g) ^ 2 + (P + g) ^ 2 :=
  tri_fst_le (A := pV P g) (B := pW P g) (C := pP P g) _ (by simp only [pV]; ppos) (by simp only [pW]; ppos)
    (by simp only [pP]; ppos)
theorem S_x : ∀ p ∈ H6 P g, (2 * P + g) ^ 2 + (P + g) ^ 2 ≤ p.1 := by
  rintro p ⟨a1, a2, a3, a4⟩; exact a1

/-! ### the 15 pairs -/
theorem hc_ne : (2 * P + g) ≠ 0 := by positivity
theorem lo_ne : (-(2 * P + g)) ≠ 0 := neg_ne_zero.mpr (hc_ne hP hg)
theorem lq_ne : (2 * P + g) * (P + g) ≠ 0 := by positivity

variable {f : ℝ} (hf : 1 < 4 * f ^ 2)
include hf

theorem d12 : Disjoint (interior (Phi f '' H1 P g)) (interior (Phi f '' H2 P g)) :=
  disjoint_image' hf (interior_disj_lin (-(2 * P + g)) (3 * P + 2 * g) 0 (lo_ne hP hg) (fun p hp => by
    have := T2_lo hP hg p hp; exact this) (T1_lo hP hg)).symm
theorem d14 : Disjoint (interior (Phi f '' H1 P g)) (interior (Phi f '' H4 P g)) :=
  disjoint_image' hf (interior_disj_lin (-(2 * P + g)) (3 * P + 2 * g) 0 (lo_ne hP hg) (Y_lo hP hg) (T1_lo hP hg)).symm
theorem d15 : Disjoint (interior (Phi f '' H1 P g)) (interior (Phi f '' H5 P g)) :=
  disjoint_image' hf (interior_disj_lin (-(2 * P + g)) (3 * P + 2 * g) 0 (lo_ne hP hg) (M_lo hP hg) (T1_lo hP hg)).symm
theorem d16 : Disjoint (interior (Phi f '' H1 P g)) (interior (Phi f '' H6 P g)) :=
  disjoint_image' hf (interior_disj_lin (-(2 * P + g)) (3 * P + 2 * g) 0 (lo_ne hP hg) (S_lo hP hg) (T1_lo hP hg)).symm
theorem d13 : Disjoint (interior (Phi f '' H1 P g)) (interior (Phi f '' H3 P g)) :=
  disjoint_image' hf (interior_disj_lin (2 * P + g) (-(P + g)) _ (hc_ne hP hg) (T1_lc hP hg) (T3_lc hP hg))
theorem d23 : Disjoint (interior (Phi f '' H2 P g)) (interior (Phi f '' H3 P g)) :=
  disjoint_image' hf (interior_disj_lin ((2 * P + g) * (P + g)) ((2 * P + g) ^ 2 - (3 * P + 2 * g) * (P + g)) _
    (lq_ne hP hg) (T2_lq hP hg) (T3_lq hP hg))
theorem d24 : Disjoint (interior (Phi f '' H2 P g)) (interior (Phi f '' H4 P g)) :=
  disjoint_image' hf (interior_disj_lin ((2 * P + g) * (P + g)) ((2 * P + g) ^ 2 - (3 * P + 2 * g) * (P + g)) _
    (lq_ne hP hg) (T2_lq hP hg) (Y_lq hP hg))
theorem d25 : Disjoint (interior (Phi f '' H2 P g)) (interior (Phi f '' H5 P g)) :=
  disjoint_image' hf (interior_disj_lin ((2 * P + g) * (P + g)) ((2 * P + g) ^ 2 - (3 * P + 2 * g) * (P + g)) _
    (lq_ne hP hg) (T2_lq hP hg) (M_lq hP hg))
theorem d26 : Disjoint (interior (Phi f '' H2 P g)) (interior (Phi f '' H6 P g)) :=
  disjoint_image' hf (interior_disj_lin ((2 * P + g) * (P + g)) ((2 * P + g) ^ 2 - (3 * P + 2 * g) * (P + g)) _
    (lq_ne hP hg) (T2_lq hP hg) (S_lq hP hg))
theorem d34 : Disjoint (interior (Phi f '' H3 P g)) (interior (Phi f '' H4 P g)) :=
  disjoint_image' hf (interior_disj_snd _ (Y_y hP hg) (T3_y hP hg)).symm
theorem d35 : Disjoint (interior (Phi f '' H3 P g)) (interior (Phi f '' H5 P g)) :=
  disjoint_image' hf (interior_disj_snd _ (M_y hP hg) (T3_y hP hg)).symm
theorem d36 : Disjoint (interior (Phi f '' H3 P g)) (interior (Phi f '' H6 P g)) :=
  disjoint_image' hf (interior_disj_snd _ (S_y hP hg) (T3_y hP hg)).symm
theorem d45 : Disjoint (interior (Phi f '' H4 P g)) (interior (Phi f '' H5 P g)) :=
  disjoint_image' hf (interior_disj_lin (2 * P + g) (-(P + g)) _ (hc_ne hP hg) (Y_lv hP hg) (M_lv hP hg))
theorem d46 : Disjoint (interior (Phi f '' H4 P g)) (interior (Phi f '' H6 P g)) :=
  disjoint_image' hf (interior_disj_lin (2 * P + g) (-(P + g)) _ (hc_ne hP hg) (Y_lv hP hg) (S_lv hP hg))
theorem d56 : Disjoint (interior (Phi f '' H5 P g)) (interior (Phi f '' H6 P g)) :=
  disjoint_image' hf (interior_disj_fst _ (M_x hP hg) (S_x hP hg))

end facts
end Erdos634.Draft.S2G
