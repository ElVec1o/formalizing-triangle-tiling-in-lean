-- Draft/LaczFormalIIcG11h.lean -- Laczkovich (DCG 48 (2012)), Thm 2.1, Case IIc: the non-`AngGen` sub-cases that are VACUOUS inside IIc.
-- In the class IIc (gamma < pi/2, gamma != pi/3, a ~ b commensurable, a !~ c, and M gamma = 2 pi from the corner count):
--   alpha = gamma  or  beta = gamma   force  a ~ c  (equal sides opposite equal angles)                 -- contradicts `hac`;
--   alpha = pi/2   or  beta = pi/2    force  cos gamma rational, gamma = 2 pi / M, hence (Niven) gamma in {pi/3, pi/2, 2pi/3,..}  -- excluded by gamma < pi/2, gamma != pi/3;
--   gamma = pi/2 is excluded by `h1`.
-- So `AngGen` minus `ne01` (`AngGen'`) is DERIVABLE inside IIc; ONLY alpha = beta remains (`IIcIsoClaim`, a NAMED blocker; see G11i).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6), Beeson, Beeson-Zhang; Niven's theorem from Mathlib.
import Erdos634.Draft.LaczFormalRG4Comm
import Erdos634.Draft.LaczFormalRG12Fan222
import Mathlib.NumberTheory.Niven

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

/-- `AngGen` without the hypothesis `alpha != beta`. -/
structure AngGen' (ω : Fin 3 → ℝ) : Prop where
  pos : ∀ l, 0 < ω l
  sum : ω 0 + ω 1 + ω 2 = Real.pi
  ne02 : ω 0 ≠ ω 2
  ne12 : ω 1 ≠ ω 2
  r0 : ω 0 ≠ Real.pi / 2
  r1 : ω 1 ≠ Real.pi / 2
  r2 : ω 2 ≠ Real.pi / 2

theorem AngGen'.toAngGen {ω : Fin 3 → ℝ} (h : AngGen' ω) (h01 : ω 0 ≠ ω 1) : AngGen ω :=
  ⟨h.pos, h.sum, h01, h.ne02, h.ne12, h.r0, h.r1, h.r2⟩

theorem AngGen.toPrime {ω : Fin 3 → ℝ} (h : AngGen ω) : AngGen' ω :=
  ⟨h.pos, h.sum, h.ne02, h.ne12, h.r0, h.r1, h.r2⟩

/-- A rational cosine at `gamma = 2 pi / M` with `0 < gamma < pi/2`, `gamma != pi/3` is impossible (Niven). -/
theorem cos_rat_vacuous {γ : ℝ} {M : ℕ} (hγ : 0 < γ) (hγ1 : γ < Real.pi / 2) (hγ3 : γ ≠ Real.pi / 3) (hM : (M : ℝ) * γ = 2 * Real.pi)
    (hq : ∃ q : ℚ, Real.cos γ = q) : False := by
  have hpi := Real.pi_pos
  have hM0 : (M : ℝ) ≠ 0 := by
    intro h; rw [h] at hM; linarith
  have hθ : ∃ r : ℚ, γ = r * Real.pi := by
    refine ⟨(2 : ℚ) / M, ?_⟩
    push_cast
    field_simp
    linarith
  have := niven_angle_eq hθ hq ⟨hγ.le, by linarith⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
  rcases this with h | h | h | h | h
  · linarith
  · exact hγ3 h
  · linarith
  · linarith
  · linarith

theorem iic_angles_vacuous {α β γ s0 s1 s2 : ℝ} {M : ℕ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hsum : α + β + γ = Real.pi)
    (hs0 : 0 < s0) (hs1 : 0 < s1) (hs2 : 0 < s2) (r1 : Real.sin β * s0 = Real.sin α * s1) (r2 : Real.sin α * s2 = Real.sin γ * s0)
    (hγ1 : γ < Real.pi / 2) (hγ3 : γ ≠ Real.pi / 3) (hM : (M : ℝ) * γ = 2 * Real.pi) (hab : Comm s0 s1) (hac : ¬ Comm s0 s2) :
    α ≠ γ ∧ β ≠ γ ∧ α ≠ Real.pi / 2 ∧ β ≠ Real.pi / 2 := by
  have hpi := Real.pi_pos
  have hsα : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα (by linarith)
  have hsβ : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi hβ (by linarith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    apply hac
    rw [← h] at r2
    have : s2 = s0 := mul_left_cancel₀ hsα.ne' r2
    rw [this]; exact comm_refl' s0
  · intro h
    apply hac
    rw [← h] at r2
    have h12 : s2 = s1 := by
      apply mul_left_cancel₀ hsα.ne'
      rw [r2]; exact r1
    rw [h12]; exact hab
  · intro h
    have hβ' : β = Real.pi / 2 - γ := by linarith
    have hsin : Real.sin β = Real.cos γ := by rw [hβ', Real.sin_pi_div_two_sub]
    rw [h, Real.sin_pi_div_two, hsin] at r1
    obtain ⟨p, q, hp, hq, e⟩ := hab
    refine cos_rat_vacuous hγ hγ1 hγ3 hM ⟨(p : ℚ) / q, ?_⟩
    have hq0 : (q : ℝ) ≠ 0 := by positivity
    push_cast
    rw [eq_div_iff hq0]
    apply mul_right_cancel₀ hs0.ne'
    calc Real.cos γ * q * s0 = q * (Real.cos γ * s0) := by ring
      _ = q * (1 * s1) := by rw [r1]
      _ = p * s0 := by linarith [e]
  · intro h
    have hα' : α = Real.pi / 2 - γ := by linarith
    have hsin : Real.sin α = Real.cos γ := by rw [hα', Real.sin_pi_div_two_sub]
    rw [h, Real.sin_pi_div_two, hsin] at r1
    obtain ⟨p, q, hp, hq, e⟩ := hab
    refine cos_rat_vacuous hγ hγ1 hγ3 hM ⟨(q : ℚ) / p, ?_⟩
    have hp0 : (p : ℝ) ≠ 0 := by positivity
    push_cast
    rw [eq_div_iff hp0]
    apply mul_right_cancel₀ hs1.ne'
    calc Real.cos γ * p * s1 = p * (Real.cos γ * s1) := by ring
      _ = p * (1 * s0) := by rw [← r1]
      _ = q * s1 := by linarith [e]

variable {N : ℕ}

/-- **`AngGen'` is derivable inside Case IIc** (all of `AngGen` except `alpha != beta`). -/
theorem angGen'_of_IIc {M : ℕ} (D : CongruentRegionDissection N) (hMγ : (M : ℝ) * D.model.angleAt 2 = 2 * Real.pi)
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3)
    (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2)) : AngGen' (fun l => D.model.angleAt l) := by
  have hp0 := model_angle_pos' D 0
  have hp1 := model_angle_pos' D 1
  have hp2 := model_angle_pos' D 2
  have hsum := angleAt_sum D.model
  obtain ⟨r1, r2⟩ := slen_sin_rel' D
  obtain ⟨n1, n2, n3, n4⟩ := iic_angles_vacuous (M := M) hp0 hp1 hp2 hsum (slen_pos D 0) (slen_pos D 1) (slen_pos D 2) r1 r2 h1 h3 hMγ hab hac
  refine ⟨fun l => model_angle_pos' D l, hsum, n1, n2, n3, n4, ?_⟩
  exact ne_of_lt h1

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.angGen'_of_IIc
