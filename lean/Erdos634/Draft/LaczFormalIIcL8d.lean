-- Draft/LaczFormalIIcL8d.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, index split (G10), step 4: the strictly convex polygon `ConvPoly M` against `path_cross`.
--  `carrier_segment`   : the carrier is convex;   `chord_in_segment` : the line through two distinct vertices meets the polygon only in the chord between them;
--  `vertex_tri_eq`     : a vertex of the polygon lying in a triangle (A, E, C) of polygon points (A, C other vertices, E a point of the polygon) with B on the E side of AC equals E.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcL8c
import Erdos634.Draft.LaczFormalThm21Loc

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.Draft.LaczFormal.Thm21

namespace Erdos634.Draft.LaczFormal.RG

variable {M : ℕ} [NeZero M]

theorem vtx_inj' (P : ConvPoly M) : Function.Injective P.v := by
  intro i j hij
  by_contra hne
  by_cases h : j = i + 1
  · subst h
    apply P.e_ne_zero P.three_le i
    unfold ConvPoly.e
    rw [hij]; simp
  · have h1 := P.c_vertex_pos (j := i) (m := j) (fun e => hne e.symm) h
    rw [← hij, P.c_self] at h1
    exact lt_irrefl _ h1

theorem carrier_segment (P : ConvPoly M) {x y : Plane} (hx : x ∈ P.carrier) (hy : y ∈ P.carrier) : segment ℝ x y ⊆ P.carrier := by
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  intro j
  have e : a = 1 - b := by linarith
  subst e
  show 0 ≤ P.c j _
  rw [P.c_comb]
  have h1 := hx j; have h2 := hy j
  have h1' : 0 ≤ P.c j x := h1
  have h2' : 0 ≤ P.c j y := h2
  nlinarith

theorem vertex_not_both (P : ConvPoly M) {j m : Fin M} (hm : m ≠ j) (h : P.c j (P.v m) = 0) : 0 < P.c (j - 1) (P.v m) := by
  have hM := P.three_le
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := ConvPoly.fin_facts hM j
  have hm1 : m = j + 1 := by
    by_contra hne
    have := P.c_vertex_pos hm hne
    linarith
  subst hm1
  have := P.c_vertex_pos (j := j - 1) (m := j + 1) f4 (by rw [f5]; exact f1)
  exact this

theorem chord_nonneg (P : ConvPoly M) {i l : Fin M} (hil : i ≠ l) {X : Plane} (hX : X ∈ P.carrier) {t : ℝ}
    (hXt : X = (1 - t) • P.v i + t • P.v l) : 0 ≤ t := by
  by_contra hneg
  push_neg at hneg
  have c0 : 0 ≤ P.c i (P.v l) := by
    by_cases h1 : l = i + 1
    · subst h1; exact (P.c_next i).ge
    · exact (P.c_vertex_pos hil.symm h1).le
  have c1 : 0 ≤ P.c (i - 1) (P.v l) := by
    have hM := P.three_le
    by_cases h1 : l = i - 1
    · subst h1; exact (P.c_self _).ge
    · by_cases h2 : l = i - 1 + 1
      · subst h2; exact (P.c_next _).ge
      · exact (P.c_vertex_pos h1 h2).le
  have hx0 := hX i
  have hx1 := hX (i - 1)
  have hM := P.three_le
  have z0 : P.c i X = t * P.c i (P.v l) := by
    rw [hXt, P.c_comb, P.c_self]; ring
  have z1 : P.c (i - 1) X = t * P.c (i - 1) (P.v l) := by
    rw [hXt, P.c_comb, P.c_prev_next hM]; ring
  have a0 : P.c i (P.v l) = 0 := by
    have : 0 ≤ t * P.c i (P.v l) := by rw [← z0]; exact hx0
    nlinarith
  have := vertex_not_both P hil.symm a0
  have a1 : P.c (i - 1) (P.v l) = 0 := by
    have : 0 ≤ t * P.c (i - 1) (P.v l) := by rw [← z1]; exact hx1
    nlinarith
  linarith

theorem par_param (x0 x1 a0 a1 c0 c1 : ℝ) (h : (c0 - a0) * (x1 - a1) - (c1 - a1) * (x0 - a0) = 0) (hn : 0 < (c0 - a0) ^ 2 + (c1 - a1) ^ 2) :
    x0 = (1 - ((x0 - a0) * (c0 - a0) + (x1 - a1) * (c1 - a1)) / ((c0 - a0) ^ 2 + (c1 - a1) ^ 2)) * a0 +
      ((x0 - a0) * (c0 - a0) + (x1 - a1) * (c1 - a1)) / ((c0 - a0) ^ 2 + (c1 - a1) ^ 2) * c0 ∧
    x1 = (1 - ((x0 - a0) * (c0 - a0) + (x1 - a1) * (c1 - a1)) / ((c0 - a0) ^ 2 + (c1 - a1) ^ 2)) * a1 +
      ((x0 - a0) * (c0 - a0) + (x1 - a1) * (c1 - a1)) / ((c0 - a0) ^ 2 + (c1 - a1) ^ 2) * c1 := by
  constructor
  · field_simp; linear_combination (-(c1 - a1)) * h
  · field_simp; linear_combination (c0 - a0) * h

/-- the line through two distinct vertices meets the polygon only in the chord. -/
theorem chord_in_segment (P : ConvPoly M) {i l : Fin M} (hil : i ≠ l) {X : Plane} (hX : X ∈ P.carrier)
    (h0 : gl (P.v i) (P.v l) X = 0) : X ∈ segment ℝ (P.v i) (P.v l) := by
  have hne : P.v l ≠ P.v i := fun h => hil (vtx_inj' P h).symm
  have hn : 0 < (P.v l 0 - P.v i 0) ^ 2 + (P.v l 1 - P.v i 1) ^ 2 := by
    have : P.v l 0 ≠ P.v i 0 ∨ P.v l 1 ≠ P.v i 1 := by
      by_contra hc; push_neg at hc; exact hne (pl_ext hc.1 hc.2)
    rcases this with h | h
    · have := sub_ne_zero.mpr h; positivity
    · have := sub_ne_zero.mpr h; positivity
  have hcr : (P.v l 0 - P.v i 0) * (X 1 - P.v i 1) - (P.v l 1 - P.v i 1) * (X 0 - P.v i 0) = 0 := by
    unfold gl cross2 at h0; simpa using h0
  obtain ⟨e0, e1⟩ := par_param (X 0) (X 1) (P.v i 0) (P.v i 1) (P.v l 0) (P.v l 1) hcr hn
  set t : ℝ := ((X 0 - P.v i 0) * (P.v l 0 - P.v i 0) + (X 1 - P.v i 1) * (P.v l 1 - P.v i 1)) /
    ((P.v l 0 - P.v i 0) ^ 2 + (P.v l 1 - P.v i 1) ^ 2) with ht
  have hXt : X = (1 - t) • P.v i + t • P.v l := by
    apply pl_ext
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; exact e0
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; exact e1
  have t0 := chord_nonneg P hil hX hXt
  have t1 : 0 ≤ 1 - t := chord_nonneg P hil.symm hX (by rw [hXt, sub_sub_cancel, add_comm])
  exact ⟨1 - t, t, t1, t0, by ring, hXt.symm⟩

end Erdos634.Draft.LaczFormal.RG
