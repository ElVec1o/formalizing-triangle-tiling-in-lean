-- Draft/LaczFormalBZL7a.lean -- Beeson-Zhang (arXiv 2604.01314) "L7" for POLYGON targets, gamma = 2 pi/3, via the repaired Case III (caseIIIa/b_repaired) assembled in `thm21_partial4`.
-- BZ print L7 (Thm 1.1/1.2, Table 5) only for triangle targets; Laczkovich Thm 2.1 (iv) at 2pi/3 is the equilateral row (BZ Thm 5.2).  Here:
--   `bz_L7_polygon`       : regular PolyTiling, gamma = 2pi/3, alpha not in Q pi  ==>  Concl1 (parallelogram) \/ SinComm \/ Concl6 (rational centrally symmetric hexagon, sin a/sin b rational).
--   `bz_L7_polygon_sides` : the same with SinComm replaced by Comm a b /\ Comm a c (sides of the tile commensurable).
--   `bz_L7_triangle`      : M = 3 (equilateral target): sides of the tile pairwise commensurable (BZ Thm 5.2 via thm21_partial4).
-- UNCONDITIONAL: gamma = 2pi/3 is never in the class IIc (needs gamma < pi/2), so neither IIcNoKites nor IIcClaim is used.
-- NOT claimed: commensurable sides for M = 4 (Concl1) and M = 6 (Concl6); those branches are not excluded.  NOTE, UNAUDITED.
-- Credit: Beeson-Zhang (arXiv 2604.01314, 2604.03609), Laczkovich (DCG 48 (2012), Thm 2.1, Sect. 7), Beeson.
import Erdos634.Draft.LaczFormalThm21Assembly
import Erdos634.Draft.LaczFormalRG4Comm
import Erdos634.Draft.LaczFormalIIIcGlue
import Erdos634.Draft.TheoremPConditional

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem bz_L7_polygon (T : PolyTiling N M) (hreg : RegularPQ T.C) (hγ : angleAt T.C.model 2 = 2 * Real.pi / 3)
    (hα : ¬ ∃ r : ℚ, angleAt T.C.model 0 = (r : ℝ) * Real.pi) :
    Concl1 T.C T.P ∨ SinComm T.C ∨ Concl6 T.C T.P := by
  have hpi := Real.pi_pos
  have hex : ¬ Thm21Excluded4 T := by
    intro h; have := h.1; rw [hγ] at this; linarith
  have h := thm21_partial4 T hreg hex
  have hsum : T.C.model.angleAt 0 + T.C.model.angleAt 1 + T.C.model.angleAt 2 = Real.pi := Erdos634.Draft.LaczFormal.angleAt_sum T.C.model
  have hγ' : T.C.model.angleAt 2 = 2 * Real.pi / 3 := hγ
  rcases h with h | h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h.2.2)
  · exact Or.inr (Or.inl h.2.2)
  · exact Or.inr (Or.inl h.2.2.2)
  · exfalso
    obtain ⟨k, hMk, hk4, -, hang, -⟩ := h
    have hαβ : angleAt T.C.model 0 + angleAt T.C.model 1 = Real.pi / 3 := by
      have : T.C.model.angleAt 0 + T.C.model.angleAt 1 = Real.pi / 3 := by linarith
      exact this
    have hs := poly_angle_sum T.P
    have h2 : ∑ i : Fin M, T.P.angle i = (M : ℝ) * (Real.pi / 3) := by
      rw [Finset.sum_congr rfl (fun i _ => by rw [hang i, hαβ])]
      simp
    have hc : ((M - 2 : ℕ) : ℝ) = (M : ℝ) - 2 := by rw [Nat.cast_sub (by omega)]; norm_num
    have hM8' : (8 : ℝ) ≤ M := by exact_mod_cast (show 8 ≤ M by omega)
    rw [h2, hc] at hs
    nlinarith
  · exact Or.inr (Or.inr h)
  · exfalso
    obtain ⟨-, -, hab, ha0, hg⟩ := h
    have hM : (M : ℝ) ≠ 0 := by have : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M); positivity
    have hM3 : (M : ℝ) = 3 := by
      rw [hγ] at hg
      field_simp at hg
      nlinarith
    apply hα
    refine ⟨1 / 6, ?_⟩
    rw [ha0, hM3]; push_cast; ring
  · exfalso
    obtain ⟨-, -, -, ha0, -, -⟩ := h
    exact hα ⟨1 / 6, by rw [ha0]; push_cast; ring⟩
  · exfalso
    have := h.2.2.2.1
    rw [hγ] at this; linarith

/-- SinComm gives commensurable sides (law of sines). -/
theorem comm_sides_of_sinComm (D : CongruentRegionDissection N) (h : SinComm D) : Comm (slen D 0) (slen D 1) ∧ Comm (slen D 0) (slen D 2) := by
  obtain ⟨⟨p, q, hp, hq, e1⟩, -, ⟨p', q', hp', hq', e2⟩⟩ := h
  obtain ⟨r1, r2⟩ := slen_sin_rel' D
  have h1 : Real.sin (angleAt D.model 1) * slen D 0 = Real.sin (angleAt D.model 0) * slen D 1 := r1
  have h2 : Real.sin (angleAt D.model 0) * slen D 2 = Real.sin (angleAt D.model 2) * slen D 0 := r2
  have hsum : D.model.angleAt 0 + D.model.angleAt 1 + D.model.angleAt 2 = Real.pi := Erdos634.Draft.LaczFormal.angleAt_sum D.model
  have p0 : 0 < D.model.angleAt 0 := model_angle_pos' D 0
  have p1 : 0 < D.model.angleAt 1 := model_angle_pos' D 1
  have p2 : 0 < D.model.angleAt 2 := model_angle_pos' D 2
  have s1 : 0 < Real.sin (angleAt D.model 1) := Real.sin_pos_of_pos_of_lt_pi (model_angle_pos' D 1)
    (show D.model.angleAt 1 < Real.pi by linarith)
  have s2 : 0 < Real.sin (angleAt D.model 2) := Real.sin_pos_of_pos_of_lt_pi (model_angle_pos' D 2)
    (show D.model.angleAt 2 < Real.pi by linarith)
  refine ⟨⟨p, q, hp, hq, ?_⟩, ⟨p', q', hp', hq', ?_⟩⟩
  · -- p sin0 = q sin1 ; sin1 a = sin0 b  => p a = q b
    have : ((p : ℝ) * slen D 0) * Real.sin (angleAt D.model 1) = ((q : ℝ) * slen D 1) * Real.sin (angleAt D.model 1) := by
      calc ((p : ℝ) * slen D 0) * Real.sin (angleAt D.model 1) = p * (Real.sin (angleAt D.model 1) * slen D 0) := by ring
        _ = p * (Real.sin (angleAt D.model 0) * slen D 1) := by rw [h1]
        _ = (p * Real.sin (angleAt D.model 0)) * slen D 1 := by ring
        _ = (q * Real.sin (angleAt D.model 1)) * slen D 1 := by rw [e1]
        _ = ((q : ℝ) * slen D 1) * Real.sin (angleAt D.model 1) := by ring
    exact mul_right_cancel₀ s1.ne' this
  · -- p' sin0 = q' sin2 ; sin0 c = sin2 a => p' a = q' c
    have : ((p' : ℝ) * slen D 0) * Real.sin (angleAt D.model 2) = ((q' : ℝ) * slen D 2) * Real.sin (angleAt D.model 2) := by
      calc ((p' : ℝ) * slen D 0) * Real.sin (angleAt D.model 2) = p' * (Real.sin (angleAt D.model 2) * slen D 0) := by ring
        _ = p' * (Real.sin (angleAt D.model 0) * slen D 2) := by rw [h2]
        _ = (p' * Real.sin (angleAt D.model 0)) * slen D 2 := by ring
        _ = (q' * Real.sin (angleAt D.model 2)) * slen D 2 := by rw [e2]
        _ = ((q' : ℝ) * slen D 2) * Real.sin (angleAt D.model 2) := by ring
    exact mul_right_cancel₀ s2.ne' this

theorem bz_L7_polygon_sides (T : PolyTiling N M) (hreg : RegularPQ T.C) (hγ : angleAt T.C.model 2 = 2 * Real.pi / 3)
    (hα : ¬ ∃ r : ℚ, angleAt T.C.model 0 = (r : ℝ) * Real.pi) :
    Concl1 T.C T.P ∨ (Comm (slen T.C 0) (slen T.C 1) ∧ Comm (slen T.C 0) (slen T.C 2)) ∨ Concl6 T.C T.P := by
  rcases bz_L7_polygon T hreg hγ hα with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (comm_sides_of_sinComm _ h))
  · exact Or.inr (Or.inr h)

/-- **Triangle (equilateral) target**: Concl1 needs `M = 4` and Concl6 `M = 6`, so for `M = 3` the sides of the tile are commensurable (Beeson-Zhang Thm 5.2 row via `thm21_partial4`). -/
theorem bz_L7_triangle (T : PolyTiling N 3) (hreg : RegularPQ T.C) (hγ : angleAt T.C.model 2 = 2 * Real.pi / 3)
    (hα : ¬ ∃ r : ℚ, angleAt T.C.model 0 = (r : ℝ) * Real.pi) :
    Comm (slen T.C 0) (slen T.C 1) ∧ Comm (slen T.C 0) (slen T.C 2) := by
  rcases bz_L7_polygon_sides T hreg hγ hα with h | h | h
  · exact absurd h.1.1 (by omega)
  · exact h
  · exact absurd h.1 (by omega)

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.bz_L7_polygon
#print axioms Erdos634.Draft.LaczFormal.RG.bz_L7_polygon_sides
#print axioms Erdos634.Draft.LaczFormal.RG.bz_L7_triangle
