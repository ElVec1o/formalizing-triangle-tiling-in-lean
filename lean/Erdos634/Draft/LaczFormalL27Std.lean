import Erdos634.Draft.LaczFormalL27Fan

/-!
# Laczkovich Theorem 2.4, triples 2 and 5 of (1): the standard chart

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.4, Fig. 5), Beeson, Beeson-Zhang, Zhang.

Standard chart of `LaczFormalL26*`: `L = (0,0)`, `R = (sR,0)`, `P = (sP,tP)`, `T = LRP` the fourth-triple triangle (`fourth_chart`).
The fifth triple `(β, 2α, α+β)` is the tile `P X L` (with `X = (xL,0)`, scale `k = K/b²`) plus `T`; the second triple
`(β, β, 3α)` adds the mirror tile `P R Y` (`Y = (xY,0)`).  All piece sizes are determined by the picture (Fig. 5, middle
and top right); validity range is that of the fourth triple, `N(a₀) > 0`.
-/

namespace Erdos634.LaczL27

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL24 Erdos634.LaczL26

theorem range_mk3 (A B C : Plane) : Set.range ![A, B, C] = {A, B, C} := by
  ext z; simp [Fin.exists_fin_succ]; tauto

theorem carrier_eq_of_range {T T' : Tri} (h : Set.range T.pts = Set.range T'.pts) : T.carrier = T'.carrier := by
  simp only [Tri.carrier, h]

theorem kap_h (p q : ℝ) : kap p q 0 0 1 0 = q := by unfold kap; ring

theorem kap_h_ne {p q : ℝ} (hq : 0 < q) : kap p q 0 0 1 0 ≠ 0 := by rw [kap_h]; exact hq.ne'

/-- horizontal fan over `t = 0` with apex `(p,q)`. -/
noncomputable def hfan (p q : ℝ) (hq : 0 < q) {x y : ℝ} (hxy : x ≠ y) : Tri :=
  fanTri p q 0 0 1 0 (kap_h_ne hq) hxy

theorem hfan_range (p q : ℝ) (hq : 0 < q) {x y : ℝ} (hxy : x ≠ y) :
    Set.range (hfan p q hq hxy).pts = {mkPt p q, mkPt x 0, mkPt y 0} := by
  unfold hfan fanTri
  rw [mkTri_pts, range_mk3]
  have e1 : mkPt (0 + x * 1) (0 + x * 0) = mkPt x 0 := by congr 1 <;> ring
  have e2 : mkPt (0 + y * 1) (0 + y * 0) = mkPt y 0 := by congr 1 <;> ring
  rw [e1, e2]

theorem hfan_swap (p q : ℝ) (hq : 0 < q) {x y : ℝ} (hxy : x ≠ y) :
    (hfan p q hq hxy).carrier = (hfan p q hq hxy.symm).carrier := by
  refine carrier_eq_of_range ?_
  rw [hfan_range, hfan_range]
  ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

variable {a : ℝ}

theorem T4_eq (h : Hyp a) :
    (triT h).carrier = (hfan (sP a) (tP a) h.hK (show (0 : ℝ) ≠ sR a from (by
      have := h.ha; have := h.hK; unfold sR; positivity : 0 < sR a).ne)).carrier := by
  refine carrier_eq_of_range ?_
  rw [hfan_range]
  unfold triT
  rw [mkTri_pts, range_mk3]
  ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

/-! ### the weaker hypothesis `Hyp0` and the abstract fourth-triple input `T4RSD` -/

/-- Only positivity of `a`, `1 - a²`, `K`: all the fan constructions of Fig. 5 need (the range condition `N(a₀) > 0`
enters only through the dissection of the fourth-triple triangle `T4RSD`). -/
structure Hyp0 (a : ℝ) : Prop where
  ha : 0 < a
  hb : 0 < gb a
  hK : 0 < gK a

theorem hyp0_of_q (a0 : ℚ) (ha0 : 0 < a0) (ha1 : a0 < 1) : Hyp0 (a0 : ℝ) := by
  have ha0r : (0 : ℝ) < a0 := by exact_mod_cast ha0
  have hb0q : (0 : ℚ) < 1 - a0 ^ 2 := by nlinarith
  have hb0r : (0 : ℝ) < 1 - (a0 : ℝ) ^ 2 := by exact_mod_cast hb0q
  exact ⟨ha0r, hb0r, by unfold gK; positivity⟩

theorem sR_pos0 (h : Hyp0 a) : 0 < sR a := by
  have h1 := h.ha; have h3 := h.hK
  unfold sR; positivity

theorem detne_T0 (h : Hyp0 a) : det3 0 0 (sR a) 0 (sP a) (tP a) ≠ 0 := by
  have e : det3 0 0 (sR a) 0 (sP a) (tP a) = sR a * tP a := by unfold det3; ring
  rw [e]
  have h1 := sR_pos0 h
  have h2 : 0 < tP a := by unfold tP; exact h.hK
  positivity

/-- the fourth-triple triangle `L R P` of the chart, from `Hyp0` only. -/
noncomputable def triT0 (h : Hyp0 a) : Tri := mkTri 0 0 (sR a) 0 (sP a) (tP a) (detne_T0 h)

/-- **Input `T4RSD`**: in every chart with the standard Gram data the fourth-triple triangle `T = L R P` is a rational
similar dissection.  For `N(a₀) > 0` it is `fourth_chart` (`T4RSD_of_N`); for `N(a₀) < 0` it comes from Beeson's
Theorem 24 (`LaczFormalL28T4`). -/
def T4RSD (R : RTri) (a0 : ℚ) (ha0 : 0 < a0) (ha1 : a0 < 1) : Prop :=
  ∀ (w d : Plane) (hdet : w 0 * d 1 - w 1 * d 0 ≠ 0),
    inner ℝ w w = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2 →
    inner ℝ d d = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2 →
    inner ℝ w d = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2 * (2 - (a0 : ℝ) ^ 2) / 2 →
    ChartRSD R 0 w d hdet (hfan (sP (a0 : ℝ)) (tP (a0 : ℝ)) (hyp0_of_q a0 ha0 ha1).hK
      (show (0 : ℝ) ≠ sR (a0 : ℝ) from (sR_pos0 (hyp0_of_q a0 ha0 ha1)).ne)).carrier

/-! ### the tiles -/

def Qf (a x y : ℝ) : ℝ := x ^ 2 + (2 - a ^ 2) * (x * y) + y ^ 2

noncomputable def xL (a : ℝ) : ℝ := -(a ^ 2 * gK a / gb a)
noncomputable def xY (a : ℝ) : ℝ := a ^ 2 * gK a + a ^ 2 * gK a / gb a
noncomputable def kk (a : ℝ) : ℝ := gK a / gb a ^ 2

theorem id_L01 (hb : gb a ≠ 0) :
    Qf a (sP a - (0 + xL a * 1)) (tP a - (0 + xL a * 0)) = kk a ^ 2 * a ^ 2 * (1 - a ^ 2) ^ 2 := by
  unfold Qf sP tP xL kk gb gK at *; field_simp; ring
theorem id_L12 (hb : gb a ≠ 0) :
    Qf a ((0 + xL a * 1) - (0 + 0 * 1)) ((0 + xL a * 0) - (0 + 0 * 0)) = kk a ^ 2 * a ^ 4 * (1 - a ^ 2) ^ 2 := by
  unfold Qf xL kk gb gK at *; field_simp; ring
theorem id_L20 (hb : gb a ≠ 0) :
    Qf a ((0 + 0 * 1) - sP a) ((0 + 0 * 0) - tP a) = kk a ^ 2 * a ^ 2 * (1 - a ^ 2) ^ 4 := by
  unfold Qf sP tP kk gb gK at *; field_simp; ring
theorem id_R01 (hb : gb a ≠ 0) :
    Qf a (sP a - (0 + xY a * 1)) (tP a - (0 + xY a * 0)) = kk a ^ 2 * a ^ 2 * (1 - a ^ 2) ^ 2 := by
  unfold Qf sP tP xY kk gb gK at *; field_simp; ring
theorem id_R12 (hb : gb a ≠ 0) :
    Qf a ((0 + xY a * 1) - (0 + sR a * 1)) ((0 + xY a * 0) - (0 + sR a * 0)) = kk a ^ 2 * a ^ 4 * (1 - a ^ 2) ^ 2 := by
  unfold Qf xY sR kk gb gK at *; field_simp; ring
theorem id_R20 (hb : gb a ≠ 0) :
    Qf a ((0 + sR a * 1) - sP a) ((0 + sR a * 0) - tP a) = kk a ^ 2 * a ^ 2 * (1 - a ^ 2) ^ 4 := by
  unfold Qf sP tP sR kk gb gK at *; field_simp; ring

end Erdos634.LaczL27
