-- Draft/LaczFormalIVcRatB7c.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch), BLUEPRINT Part B, item B7, stage c: IDENTIFYING THE RHOMBUS.
--   A rhombus piece R = Par(x; s, w) (cells (x+s, x+w, x) and (x+w, x+s, x+s+w)) one of whose cells has the vertices {U, U+p, U+q} (the frame (U; p, q) with |p| = |q|, p.q = |p|^2/2),
--   and which lies in the half plane {beta >= 0} and misses the open box O = U + (-1,0) p + (0,1) q, equals Par(U; p, q).
--   The six placements of the three cell vertices on the labels (0,0), (1,0), (0,1) and the two cells give 12 cases: 4 give Par(U; p, q) (reparametrization), 4 have the vertex U + p - q
--   (beta = -1), 4 contain the midpoint U + (q - p)/2 of the box.
--   `rhomb_identify0` (cell 0 of the rhombus), `rhomb_identify1` (cell 1).  The frame labels are real numbers (a_k, b_k) in {(0,0), (1,0), (0,1)}, pairwise distinct; no determinant hypothesis is needed here.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatB7b

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

theorem mem_Par {g0 g1 u0 u1 w0 w1 : ℝ} {y : Plane} :
    y ∈ Par g0 g1 u0 u1 w0 w1 ↔ ∃ l m : ℝ, 0 ≤ l ∧ l ≤ 1 ∧ 0 ≤ m ∧ m ≤ 1 ∧ y 0 = g0 + l * u0 + m * w0 ∧ y 1 = g1 + l * u1 + m * w1 := Iff.rfl

/-- "No point of the set has a negative `q`-coordinate in the frame `(U; p, q)`." -/
def NoBelow (S : Set Plane) (U0 U1 p0 p1 q0 q1 : ℝ) : Prop :=
  ∀ xx z : ℝ, z < 0 → mkPt (U0 + xx * p0 + z * q0) (U1 + xx * p1 + z * q1) ∉ S

/-- "The set misses the open box `(-1,0) x (0,1)` of the frame." -/
def MissBox (S : Set Plane) (U0 U1 p0 p1 q0 q1 : ℝ) : Prop :=
  ∀ xx z : ℝ, -1 < xx → xx < 0 → 0 < z → z < 1 → mkPt (U0 + xx * p0 + z * q0) (U1 + xx * p1 + z * q1) ∉ S

theorem noBelow_use {g0 g1 u0 u1 w0 w1 U0 U1 p0 p1 q0 q1 : ℝ} (hB : NoBelow (Par g0 g1 u0 u1 w0 w1) U0 U1 p0 p1 q0 q1)
    (xx z l m : ℝ) (hz : z < 0) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (e0 : U0 + xx * p0 + z * q0 = g0 + l * u0 + m * w0) (e1 : U1 + xx * p1 + z * q1 = g1 + l * u1 + m * w1) : False :=
  hB xx z hz (mem_Par.mpr ⟨l, m, hl0, hl1, hm0, hm1, by simp [mkPt_zero, e0], by simp [mkPt_one, e1]⟩)

theorem missBox_use {g0 g1 u0 u1 w0 w1 U0 U1 p0 p1 q0 q1 : ℝ} (hB : MissBox (Par g0 g1 u0 u1 w0 w1) U0 U1 p0 p1 q0 q1)
    (xx z l m : ℝ) (hx0 : -1 < xx) (hx1 : xx < 0) (hz0 : 0 < z) (hz1 : z < 1) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (e0 : U0 + xx * p0 + z * q0 = g0 + l * u0 + m * w0) (e1 : U1 + xx * p1 + z * q1 = g1 + l * u1 + m * w1) : False :=
  hB xx z hx0 hx1 hz0 hz1 (mem_Par.mpr ⟨l, m, hl0, hl1, hm0, hm1, by simp [mkPt_zero, e0], by simp [mkPt_one, e1]⟩)

/-- The twelve frame placements: `Par` of the placement is `Par U p q`, or one of the two obstructions occurs. -/
theorem rhomb_identify_core {U0 U1 p0 p1 q0 q1 xa xb sa sb wa wb : ℝ}
    (hcase : (xa = 0 ∧ xb = 0 ∧ sa = 1 ∧ sb = 0 ∧ wa = 0 ∧ wb = 1) ∨ (xa = 0 ∧ xb = 0 ∧ sa = 0 ∧ sb = 1 ∧ wa = 1 ∧ wb = 0) ∨
      (xa = 1 ∧ xb = 1 ∧ sa = -1 ∧ sb = 0 ∧ wa = 0 ∧ wb = -1) ∨ (xa = 1 ∧ xb = 1 ∧ sa = 0 ∧ sb = -1 ∧ wa = -1 ∧ wb = 0) ∨
      (xa = 1 ∧ xb = 0 ∧ sa = -1 ∧ sb = 0 ∧ wa = -1 ∧ wb = 1) ∨ (xa = 1 ∧ xb = 0 ∧ sa = -1 ∧ sb = 1 ∧ wa = -1 ∧ wb = 0) ∨
      (xa = 0 ∧ xb = 1 ∧ sa = 0 ∧ sb = -1 ∧ wa = 1 ∧ wb = -1) ∨ (xa = 0 ∧ xb = 1 ∧ sa = 1 ∧ sb = -1 ∧ wa = 0 ∧ wb = -1) ∨
      (xa = -1 ∧ xb = 1 ∧ sa = 1 ∧ sb = 0 ∧ wa = 1 ∧ wb = -1) ∨ (xa = -1 ∧ xb = 1 ∧ sa = 1 ∧ sb = -1 ∧ wa = 1 ∧ wb = 0) ∨
      (xa = 1 ∧ xb = -1 ∧ sa = 0 ∧ sb = 1 ∧ wa = -1 ∧ wb = 1) ∨ (xa = 1 ∧ xb = -1 ∧ sa = -1 ∧ sb = 1 ∧ wa = 0 ∧ wb = 1))
    {x0 x1 s0 s1 w0 w1 : ℝ}
    (hx0 : x0 = U0 + xa * p0 + xb * q0) (hx1 : x1 = U1 + xa * p1 + xb * q1)
    (hs0 : s0 = sa * p0 + sb * q0) (hs1 : s1 = sa * p1 + sb * q1)
    (hw0 : w0 = wa * p0 + wb * q0) (hw1 : w1 = wa * p1 + wb * q1)
    (hB : NoBelow (Par x0 x1 s0 s1 w0 w1) U0 U1 p0 p1 q0 q1) (hO : MissBox (Par x0 x1 s0 s1 w0 w1) U0 U1 p0 p1 q0 q1) :
    Par x0 x1 s0 s1 w0 w1 = Par U0 U1 p0 p1 q0 q1 := by
  subst hx0 hx1 hs0 hs1 hw0 hw1
  rcases hcase with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · ext y; simp only [mem_Par]
    constructor <;> rintro ⟨l, m, h1, h2, h3, h4, e0, e1⟩ <;> exact ⟨l, m, h1, h2, h3, h4, by linear_combination e0, by linear_combination e1⟩
  · ext y; simp only [mem_Par]
    constructor <;> rintro ⟨l, m, h1, h2, h3, h4, e0, e1⟩ <;> exact ⟨m, l, h3, h4, h1, h2, by linear_combination e0, by linear_combination e1⟩
  · ext y; simp only [mem_Par]
    constructor <;> rintro ⟨l, m, h1, h2, h3, h4, e0, e1⟩ <;> exact ⟨1 - l, 1 - m, by linarith, by linarith, by linarith, by linarith, by linear_combination e0, by linear_combination e1⟩
  · ext y; simp only [mem_Par]
    constructor <;> rintro ⟨l, m, h1, h2, h3, h4, e0, e1⟩ <;> exact ⟨1 - m, 1 - l, by linarith, by linarith, by linarith, by linarith, by linear_combination e0, by linear_combination e1⟩
  · exact (missBox_use hO (-1 / 2) (1 / 2) 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by ring) (by ring)).elim
  · exact (missBox_use hO (-1 / 2) (1 / 2) (1 / 2) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by ring) (by ring)).elim
  · exact (noBelow_use hB 1 (-1) 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by ring)).elim
  · exact (noBelow_use hB 1 (-1) 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by ring)).elim
  · exact (missBox_use hO (-1 / 2) (1 / 2) 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by ring) (by ring)).elim
  · exact (missBox_use hO (-1 / 2) (1 / 2) (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by ring) (by ring)).elim
  · exact (noBelow_use hB 1 (-1) 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by ring)).elim
  · exact (noBelow_use hB 1 (-1) 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by ring)).elim

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.rhomb_identify_core
