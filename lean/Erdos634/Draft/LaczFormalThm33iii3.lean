-- Draft/LaczFormalThm33iii3.lean -- Laczkovich DCG 48 (2012) Thm 3.3 ("only if" direction, including clause (iii) "sin a, sin b, sin c pairwise commensurable"), module 3 of 3.
--   `sincomm_of_concl_tri`   : Thm21Concl on a TRIANGLE with irrational model angle alpha  =>  SinComm (only (ii), (iii), (iv) survive; (i),(v),(vi),(ix) need M = 4, >= 8, 6, 6;
--                              (vii), (viii) force alpha = pi/6);
--   `sincomm_irr_family`     : equilateral target, tile (alpha, beta, gamma), alpha not in Q pi, gamma in {pi/3, 2pi/3}  =>  sines pairwise commensurable.
--                              Route: PolyTiling (`polyTilingOf`), RegularPQ (`regular_of_irr` for 2pi/3, `regular_of_irr_pi3` for pi/3), then `thm21_partial4`.
--                              gamma = pi/3 or 2pi/3 is NEVER in the class IIc (`Thm21Excluded4` needs gamma < pi/2 and gamma != pi/3), so this is UNCONDITIONAL:
--                              it does NOT depend on IIcNoKites / IIcClaim.
--   `thm33_only_if`          : Equilateral D  =>  a permutation (x,y,z) of the tile angles satisfies (i), (ii) or (iii) of the printed Thm 3.3.
-- NOTE, UNAUDITED.  Existence ("if") direction of Thm 3.3 is NOT in this file.  Credit: Laczkovich (DCG 48 (2012), Thm 2.1, 3.3; Discrete Math 140 (1995)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalThm33iii2
import Erdos634.Draft.LaczFormalL56Final

open scoped Classical Fin.NatCast
open Erdos634.Draft.TheoremPConditional
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

theorem sincomm_of_concl_tri (C : CongruentRegionDissection N) (P : ConvPoly 3)
    (hα : ¬ ∃ r : ℚ, angleAt C.model 0 = (r : ℝ) * Real.pi) (h : Thm21Concl C P) : SinComm C := by
  have h6 : angleAt C.model 0 = Real.pi / 6 → False := fun e => hα ⟨1 / 6, by rw [e]; push_cast; ring⟩
  rcases h with h | h | h | h | h | h | h | h | h
  · exact absurd h.1.1 (by norm_num)
  · exact h.2.2
  · exact h.2.2
  · exact h.2.2.2
  · obtain ⟨k, hk, -⟩ := h; omega
  · exact absurd h.1 (by norm_num)
  · exfalso; apply h6
    have := h.2.2.2.1
    rw [this]; push_cast; ring
  · exact absurd h.2.2.2.1 (fun e => h6 e)
  · exact absurd h.1 (by norm_num)

/-- **Thm 3.3 (iii), irrational family, UNCONDITIONAL.** -/
theorem sincomm_irr_family (D : CongruentDissection N) (hEq : Equilateral D) {α β γ : ℝ}
    (hα : IrrPi α) (hγ : γ = Real.pi / 3 ∨ γ = 2 * Real.pi / 3) (h : TileAngles D α β γ) :
    Comm (Real.sin α) (Real.sin β) ∧ Comm (Real.sin β) (Real.sin γ) ∧ Comm (Real.sin α) (Real.sin γ) := by
  obtain ⟨σ, h0, h1, h2⟩ := h
  have heq := equil_sides D.target hEq
  set T := polyTilingOf D σ heq with hT
  obtain ⟨hang, hP⟩ := polyTilingOf_angles D σ heq
  have a0 : angleAt T.C.model 0 = α := by rw [hang]; exact h0
  have a1 : angleAt T.C.model 1 = β := by rw [hang]; exact h1
  have a2 : angleAt T.C.model 2 = γ := by rw [hang]; exact h2
  have hα' : ¬ ∃ r : ℚ, angleAt T.C.model 0 = (r : ℝ) * Real.pi := by rw [a0]; exact hα
  have hreg : RegularPQ T.C := by
    rcases hγ with e | e
    · exact regular_of_irr_pi3 T (a2.trans e) hα' hP
    · exact regular_of_irr T (a2.trans e) hα' hP
  have hnex : ¬ Thm21Excluded4 T := by
    rintro ⟨h1', h2', -⟩
    rw [a2] at h1' h2'
    rcases hγ with e | e
    · exact h2' e
    · rw [e] at h1'; linarith [Real.pi_pos]
  have hc := thm21_partial4 T hreg hnex
  have hs := sincomm_of_concl_tri T.C T.P hα' hc
  unfold SinComm at hs
  rw [a0, a1, a2] at hs
  exact hs

/-- The printed "only if" of Thm 3.3 (the angle triple is a permutation of the tile's angles). -/
def Thm33Only {N : ℕ} (D : CongruentDissection N) : Prop :=
  ∃ x y z : ℝ, TileAngles D x y z ∧
    ((x = Real.pi / 6 ∧ y = Real.pi / 6 ∧ z = 2 * Real.pi / 3) ∨
     (x = Real.pi / 6 ∧ y = Real.pi / 2 ∧ z = Real.pi / 3) ∨
     ((z = Real.pi / 3 ∨ z = 2 * Real.pi / 3) ∧ Comm (Real.sin x) (Real.sin y) ∧ Comm (Real.sin y) (Real.sin z) ∧
        Comm (Real.sin x) (Real.sin z)))

theorem thm33_only_if (D : CongruentDissection N) (hEq : Equilateral D) : Thm33Only D := by
  rcases equilateral_classification D hEq with ⟨α, hα, h⟩ | ⟨α, hα, h⟩ | h | h | h
  · have := sincomm_irr_family D hEq hα (Or.inl rfl) h
    exact ⟨α, 2 * Real.pi / 3 - α, Real.pi / 3, h, Or.inr (Or.inr ⟨Or.inl rfl, this⟩)⟩
  · have := sincomm_irr_family D hEq hα (Or.inr rfl) h
    exact ⟨α, Real.pi / 3 - α, 2 * Real.pi / 3, h, Or.inr (Or.inr ⟨Or.inr rfl, this⟩)⟩
  · refine ⟨_, _, _, h, Or.inr (Or.inr ⟨Or.inl rfl, ?_, ?_, ?_⟩)⟩ <;> exact ⟨1, 1, one_pos, one_pos, by simp⟩
  · exact ⟨_, _, _, h, Or.inl ⟨rfl, rfl, rfl⟩⟩
  · exact ⟨_, _, _, h.swap23, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.sincomm_of_concl_tri
#print axioms Erdos634.Draft.LaczFormal.RG.sincomm_irr_family
#print axioms Erdos634.Draft.LaczFormal.RG.thm33_only_if
