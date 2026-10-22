import Erdos634.Draft.LaczFormal9x
import Erdos634.Draft.LaczFormalRGCaseVWit
import Erdos634.Draft.LaczFormalRG4Wit
import Erdos634.Draft.LaczFormalRG4Comm

/-!
# Laczkovich DCG 48 (2012), Theorem 2.1, existence of conclusions (ii), (iii), (viii)

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Comput. Geom. 48 (2012), Thm 2.1), Beeson, Beeson-Zhang.  Formalization debt, not /goal progress.

Existence statement used: `∃ T : PolyTiling N 4, RegularPQ T.C ∧ ConclK T.C T.P` (a regular tiling attaining conclusion K).
* (ii) and (iii): the 3-4-5 rectangle `[0,3]×[0,4]` cut along a diagonal (two tiles): the M-2 = 2 angles `γ = π/2`, the other two are `1·(α+β)`
  (`α+β = π/2`); sides 3,4,3,4; the sines 4/5, 3/5, 1 are pairwise commensurable.  The same tiling satisfies (i), (ii) and (iii).
* (viii): the rhombus with angles `2π/3, π/3` and side 1 cut into two copies of the tile `(π/6, π/6, 2π/3)`.
-/

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Thm21 Erdos634.Draft.LaczFormal.RG Erdos634.Draft.LaczFormal.Graph
  Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Laczkovich9y

theorem dist_mk (a b c d r : ℝ) (hr : 0 ≤ r) (h : (a - c) ^ 2 + (b - d) ^ 2 = r ^ 2) : dist (mkPt a b) (mkPt c d) = r := by
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt]
  rw [← Real.sqrt_sq hr, ← h]
  congr 1
  rw [Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]

/-- Angle at `(c,d)` between `(a,b)` and `(e,f)`, from the lengths `n1, n2` of the two arms and the inner product. -/
theorem angle_mk (a b c d e f n1 n2 θ : ℝ) (h1 : 0 < n1) (h2 : 0 < n2) (h0 : 0 ≤ θ) (hπ : θ ≤ Real.pi)
    (hn1 : (a - c) ^ 2 + (b - d) ^ 2 = n1 ^ 2) (hn2 : (e - c) ^ 2 + (f - d) ^ 2 = n2 ^ 2)
    (hin : (a - c) * (e - c) + (b - d) * (f - d) = n1 * n2 * Real.cos θ) :
    EuclideanGeometry.angle (mkPt a b) (mkPt c d) (mkPt e f) = θ := by
  unfold EuclideanGeometry.angle InnerProductGeometry.angle
  simp only [vsub_eq_sub]
  have e1 : ‖mkPt a b - mkPt c d‖ = n1 := by
    rw [← dist_eq_norm]; exact dist_mk a b c d n1 h1.le hn1
  have e2 : ‖mkPt e f - mkPt c d‖ = n2 := by
    rw [← dist_eq_norm]; exact dist_mk e f c d n2 h2.le hn2
  have e3 : inner ℝ (mkPt a b - mkPt c d) (mkPt e f - mkPt c d) = n1 * n2 * Real.cos θ := by
    rw [← hin]; simp [PiLp.inner_apply, Fin.sum_univ_two, mkPt]; ring
  rw [e1, e2, e3]
  have : n1 * n2 * Real.cos θ / (n1 * n2) = Real.cos θ := by field_simp
  rw [this, Real.arccos_cos h0 hπ]

theorem comm_nat (a b : ℕ) (ha : 0 < a) (hb : 0 < b) : Comm (a : ℝ) (b : ℝ) :=
  ⟨b, a, hb, ha, by ring⟩

/-! ### The 3-4-5 rectangle -/

noncomputable def rect34 : PolyTiling 2 4 := rTiling 3 4 (by norm_num) (by norm_num)

theorem rect34_side (i : Fin 4) : rect34.P.side i = 3 ∨ rect34.P.side i = 4 := by
  unfold ConvPoly.side
  fin_cases i
  · left; show dist (mkPt 0 0) (mkPt 3 0) = 3
    exact dist_mk _ _ _ _ _ (by norm_num) (by norm_num)
  · right; show dist (mkPt 3 0) (mkPt 3 4) = 4
    exact dist_mk _ _ _ _ _ (by norm_num) (by norm_num)
  · left; show dist (mkPt 3 4) (mkPt 0 4) = 3
    exact dist_mk _ _ _ _ _ (by norm_num) (by norm_num)
  · right; show dist (mkPt 0 4) (mkPt 0 0) = 4
    exact dist_mk _ _ _ _ _ (by norm_num) (by norm_num)

theorem rect34_rational : RationalPoly rect34.P := by
  intro i j
  rcases rect34_side i with hi | hi <;> rcases rect34_side j with hj | hj <;> rw [hi, hj]
  · exact comm_nat 3 3 (by norm_num) (by norm_num)
  · exact comm_nat 3 4 (by norm_num) (by norm_num)
  · exact comm_nat 4 3 (by norm_num) (by norm_num)
  · exact comm_nat 4 4 (by norm_num) (by norm_num)

theorem rect34_angle (i : Fin 4) : rect34.P.angle i = Real.pi / 2 := by
  have hc : Real.cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
  have hp := Real.pi_pos
  unfold ConvPoly.angle cornerAngle
  fin_cases i
  · show EuclideanGeometry.angle (mkPt 0 4) (mkPt 0 0) (mkPt 3 0) = _
    exact angle_mk _ _ _ _ _ _ 4 3 _ (by norm_num) (by norm_num) (by positivity) (by linarith) (by norm_num) (by norm_num)
      (by rw [hc]; norm_num)
  · show EuclideanGeometry.angle (mkPt 0 0) (mkPt 3 0) (mkPt 3 4) = _
    exact angle_mk _ _ _ _ _ _ 3 4 _ (by norm_num) (by norm_num) (by positivity) (by linarith) (by norm_num) (by norm_num)
      (by rw [hc]; norm_num)
  · show EuclideanGeometry.angle (mkPt 3 0) (mkPt 3 4) (mkPt 0 4) = _
    exact angle_mk _ _ _ _ _ _ 4 3 _ (by norm_num) (by norm_num) (by positivity) (by linarith) (by norm_num) (by norm_num)
      (by rw [hc]; norm_num)
  · show EuclideanGeometry.angle (mkPt 3 4) (mkPt 0 4) (mkPt 0 0) = _
    exact angle_mk _ _ _ _ _ _ 3 4 _ (by norm_num) (by norm_num) (by positivity) (by linarith) (by norm_num) (by norm_num)
      (by rw [hc]; norm_num)

theorem rect34_gamma : angleAt rect34.C.model 2 = Real.pi / 2 := rDiss_gamma (by norm_num) (by norm_num)

theorem rect34_sinComm : SinComm rect34.C := by
  have h0 : slen rect34.C 0 = 4 := rDiss_slen0 (by norm_num) (by norm_num)
  have h1 : slen rect34.C 1 = 3 := rDiss_slen1 (by norm_num) (by norm_num)
  have h2 : slen rect34.C 2 = 5 := by
    have := rDiss_slen2 (p := 3) (q := 4) (by norm_num) (by norm_num)
    have e : (3 : ℝ) ^ 2 + 4 ^ 2 = 5 ^ 2 := by norm_num
    rw [e, Real.sqrt_sq (by norm_num)] at this
    exact this
  have hab : Comm (slen rect34.C 0) (slen rect34.C 1) := by
    rw [h0, h1]; exact_mod_cast comm_nat 4 3 (by norm_num) (by norm_num)
  have hac : Comm (slen rect34.C 0) (slen rect34.C 2) := by
    rw [h0, h2]; exact_mod_cast comm_nat 4 5 (by norm_num) (by norm_num)
  exact sinComm_of_comm rect34.C hab hac

theorem rect34_ab : angleAt rect34.C.model 0 + angleAt rect34.C.model 1 = Real.pi / 2 := by
  have hs : angleAt rect34.C.model 0 + angleAt rect34.C.model 1 + angleAt rect34.C.model 2 = Real.pi :=
    Erdos634.Draft.LaczFormal.angleAt_sum rect34.C.model
  have := rect34_gamma
  linarith

theorem rect34_regular : RegularPQ rect34.C := rDiss_regular (by norm_num) (by norm_num)

theorem rect34_concl2 : Concl2 rect34.C rect34.P := by
  refine ⟨rect34_rational, ⟨0, 1, by decide, ?_, 1, 1, ?_, ?_⟩, rect34_sinComm⟩
  · intro k _ _; rw [rect34_angle, rect34_gamma]
  · rw [rect34_angle, rect34_ab]; ring
  · rw [rect34_angle, rect34_ab]; ring

theorem rect34_concl3 : Concl3 rect34.C rect34.P := by
  refine ⟨rect34_rational, ⟨0, 1, by decide, ?_, 1, 1, ?_, ?_⟩, rect34_sinComm⟩
  · intro k _ _; rw [rect34_angle, rect34_ab]
  · rw [rect34_angle, rect34_gamma]; ring
  · rw [rect34_angle, rect34_gamma]; ring

/-- Existence of a regular tiling attaining conclusion (ii) of Theorem 2.1. -/
theorem exists_concl2 : ∃ T : PolyTiling 2 4, RegularPQ T.C ∧ Concl2 T.C T.P := ⟨rect34, rect34_regular, rect34_concl2⟩
/-- Existence of a regular tiling attaining conclusion (iii) of Theorem 2.1. -/
theorem exists_concl3 : ∃ T : PolyTiling 2 4, RegularPQ T.C ∧ Concl3 T.C T.P := ⟨rect34, rect34_regular, rect34_concl3⟩

/-! ### The 120/60 rhombus: conclusion (viii) -/

noncomputable def rhomb : PolyTiling 2 4 :=
  pTiling 1 (-(1 / 2)) (Real.sqrt 3 / 2) one_pos (by positivity)

theorem rhomb_angle (i : Fin 4) : rhomb.P.angle i = Real.pi / 3 ∨ rhomb.P.angle i = 2 * Real.pi / 3 := by
  have h3 := Erdos634.Draft.LaczFormal.RG.sqrt3_sq
  have hp := Real.pi_pos
  have c3 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
  have c23 : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, c3]
  unfold ConvPoly.angle cornerAngle
  fin_cases i
  · right
    show EuclideanGeometry.angle (mkPt (-(1 / 2)) (Real.sqrt 3 / 2)) (mkPt 0 0) (mkPt 1 0) = _
    exact angle_mk _ _ _ _ _ _ 1 1 _ one_pos one_pos (by positivity) (by linarith) (by nlinarith) (by norm_num)
      (by rw [c23]; norm_num)
  · left
    show EuclideanGeometry.angle (mkPt 0 0) (mkPt 1 0) (mkPt (1 + -(1 / 2)) (Real.sqrt 3 / 2)) = _
    exact angle_mk _ _ _ _ _ _ 1 1 _ one_pos one_pos (by positivity) (by linarith) (by norm_num) (by nlinarith)
      (by rw [c3]; norm_num)
  · right
    show EuclideanGeometry.angle (mkPt 1 0) (mkPt (1 + -(1 / 2)) (Real.sqrt 3 / 2)) (mkPt (-(1 / 2)) (Real.sqrt 3 / 2)) = _
    exact angle_mk _ _ _ _ _ _ 1 1 _ one_pos one_pos (by positivity) (by linarith) (by nlinarith) (by norm_num)
      (by rw [c23]; nlinarith)
  · left
    show EuclideanGeometry.angle (mkPt (1 + -(1 / 2)) (Real.sqrt 3 / 2)) (mkPt (-(1 / 2)) (Real.sqrt 3 / 2)) (mkPt 0 0) = _
    exact angle_mk _ _ _ _ _ _ 1 1 _ one_pos one_pos (by positivity) (by linarith) (by norm_num) (by nlinarith)
      (by rw [c3]; nlinarith)

theorem rhomb_rational : RationalPoly rhomb.P := by
  have h3 := Erdos634.Draft.LaczFormal.RG.sqrt3_sq
  have hs : ∀ i : Fin 4, rhomb.P.side i = 1 := by
    intro i
    unfold ConvPoly.side
    fin_cases i
    · show dist (mkPt 0 0) (mkPt 1 0) = 1
      exact dist_mk _ _ _ _ _ (by norm_num) (by norm_num)
    · show dist (mkPt 1 0) (mkPt (1 + -(1 / 2)) (Real.sqrt 3 / 2)) = 1
      exact dist_mk _ _ _ _ _ (by norm_num) (by nlinarith)
    · show dist (mkPt (1 + -(1 / 2)) (Real.sqrt 3 / 2)) (mkPt (-(1 / 2)) (Real.sqrt 3 / 2)) = 1
      exact dist_mk _ _ _ _ _ (by norm_num) (by nlinarith)
    · show dist (mkPt (-(1 / 2)) (Real.sqrt 3 / 2)) (mkPt 0 0) = 1
      exact dist_mk _ _ _ _ _ (by norm_num) (by nlinarith)
  intro i j
  rw [hs i, hs j]
  exact ⟨1, 1, one_pos, one_pos, by ring⟩

theorem rhomb_angles : angleAt rhomb.C.model 0 = Real.pi / 6 ∧ angleAt rhomb.C.model 1 = Real.pi / 6 ∧
    angleAt rhomb.C.model 2 = 2 * Real.pi / 3 := by
  have h3 := Erdos634.Draft.LaczFormal.RG.sqrt3_sq
  have hs3 : 0 < Real.sqrt 3 := by positivity
  have hp := Real.pi_pos
  have c6 : Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := Real.cos_pi_div_six
  have c23 : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
  refine ⟨?_, ?_, ?_⟩
  · show EuclideanGeometry.angle (mkPt (-(1 / 2)) (Real.sqrt 3 / 2)) (mkPt 1 0) (mkPt 0 0) = _
    exact angle_mk _ _ _ _ _ _ (Real.sqrt 3) 1 _ hs3 one_pos (by positivity) (by linarith) (by nlinarith) (by norm_num)
      (by rw [c6]; nlinarith)
  · show EuclideanGeometry.angle (mkPt 0 0) (mkPt (-(1 / 2)) (Real.sqrt 3 / 2)) (mkPt 1 0) = _
    exact angle_mk _ _ _ _ _ _ 1 (Real.sqrt 3) _ one_pos hs3 (by positivity) (by linarith) (by nlinarith) (by nlinarith)
      (by rw [c6]; nlinarith)
  · show EuclideanGeometry.angle (mkPt 1 0) (mkPt 0 0) (mkPt (-(1 / 2)) (Real.sqrt 3 / 2)) = _
    exact angle_mk _ _ _ _ _ _ 1 1 _ one_pos one_pos (by positivity) (by linarith) (by norm_num) (by nlinarith)
      (by rw [c23]; nlinarith)

theorem rhomb_regular : RegularPQ rhomb.C := pDiss_regular one_pos (by positivity)

theorem rhomb_concl8 : Concl8 rhomb.C rhomb.P := by
  obtain ⟨h0, h1, h2⟩ := rhomb_angles
  exact ⟨rhomb_rational, by norm_num, rhomb_angle, h0, h1, h2⟩

/-- Existence of a regular tiling attaining conclusion (viii) of Theorem 2.1. -/
theorem exists_concl8 : ∃ T : PolyTiling 2 4, RegularPQ T.C ∧ Concl8 T.C T.P := ⟨rhomb, rhomb_regular, rhomb_concl8⟩

end Erdos634.Laczkovich9y

#print axioms Erdos634.Laczkovich9y.exists_concl2
#print axioms Erdos634.Laczkovich9y.exists_concl3
#print axioms Erdos634.Laczkovich9y.exists_concl8
