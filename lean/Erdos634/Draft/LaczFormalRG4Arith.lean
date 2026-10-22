-- Draft/LaczFormalRG4Arith.lean -- Theorem 2.1, Case IV (gamma = pi/3): the angle arithmetic.  With `gamma = pi/3` we have `alpha + beta = 2 pi/3`; a block of corner angles that sums to
-- `pi` has equally many `alpha` and `beta` corners unless `alpha in {pi/6, pi/3, pi/2}`, and those three values make `a` a rational multiple of `b` (excluded by `NotComb a b c`).
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8, proof of Lemma 8.1), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRGCaseV3

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

theorem model_angle_pos' (D : CongruentRegionDissection N) (l : Fin 3) : 0 < D.model.angleAt l :=
  Erdos634.MarchFlank.cornerAngle_pos D.model l

/-- Law of sines in the model: `a sin β = b sin α`, `a sin γ = c sin α`. -/
theorem slen_sin_rel' (D : CongruentRegionDissection N) :
    Real.sin (D.model.angleAt 1) * slen D 0 = Real.sin (D.model.angleAt 0) * slen D 1 ∧
    Real.sin (D.model.angleAt 0) * slen D 2 = Real.sin (D.model.angleAt 2) * slen D 0 := by
  have h0 := Erdos634.TriLawSin.sin_angleAt_mul_sideOpp D.model 0
  have h2 := Erdos634.TriLawSin.sin_angleAt_mul_sideOpp D.model 2
  exact ⟨h0, h2⟩

/-- Standing hypotheses of Case IV (`γ = π/3`, `a` not a nonnegative rational combination of `b, c`, regular corner counts). -/
structure CaseIV (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) : Prop where
  hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k'))
  hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v
  hnc : NotComb (slen D 0) (slen D 1) (slen D 2)
  hγ : D.model.angleAt 2 = Real.pi / 3
  hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1

theorem CaseIV.hab {D : CongruentRegionDissection N} {idx : Fin N → Equiv.Perm (Fin 3)} (h : CaseIV D idx) : slen D 0 ≠ slen D 1 := by
  intro e
  have := h.hnc 1 1 0 one_pos
  apply this; rw [e]; simp

theorem CaseIV.hac {D : CongruentRegionDissection N} {idx : Fin N → Equiv.Perm (Fin 3)} (h : CaseIV D idx) : slen D 0 ≠ slen D 2 := by
  intro e
  have := h.hnc 1 0 1 one_pos
  apply this; rw [e]; simp

theorem CaseIV.hαβ {D : CongruentRegionDissection N} {idx : Fin N → Equiv.Perm (Fin 3)} (h : CaseIV D idx) :
    D.model.angleAt 0 + D.model.angleAt 1 = 2 * Real.pi / 3 := by
  have := Erdos634.Draft.LaczFormal.angleAt_sum D.model
  have hγ := h.hγ
  linarith

/-- `α ∈ {π/6, π/3, π/2}` makes `a` a rational multiple of `b` (law of sines), contradicting `NotComb`. -/
theorem no_rat_alpha (D : CongruentRegionDissection N) (hnc : NotComb (slen D 0) (slen D 1) (slen D 2))
    (hαβ : D.model.angleAt 0 + D.model.angleAt 1 = 2 * Real.pi / 3)
    (h : D.model.angleAt 0 = Real.pi / 6 ∨ D.model.angleAt 0 = Real.pi / 3 ∨ D.model.angleAt 0 = Real.pi / 2) : False := by
  obtain ⟨h1, -⟩ := slen_sin_rel' D
  rcases h with h | h | h
  · -- α = π/6, β = π/2:  a * 1 = (1/2) * b
    have hb : D.model.angleAt 1 = Real.pi / 2 := by linarith
    rw [hb, h, Real.sin_pi_div_two, Real.sin_pi_div_six] at h1
    exact hnc 2 1 0 (by norm_num) (by push_cast; linarith)
  · have hb : D.model.angleAt 1 = Real.pi / 3 := by linarith
    rw [hb, h] at h1
    have hs : Real.sin (Real.pi / 3) ≠ 0 := by rw [Real.sin_pi_div_three]; positivity
    have h1' := mul_left_cancel₀ hs h1
    exact hnc 1 1 0 one_pos (by push_cast; linarith)
  · have hb : D.model.angleAt 1 = Real.pi / 6 := by linarith
    rw [hb, h, Real.sin_pi_div_two, Real.sin_pi_div_six] at h1
    exact hnc 1 2 0 one_pos (by push_cast; linarith)

/-- **Block arithmetic.**  A block of corners with `n₀` alphas, `n₁` betas, `n₂` gammas of total angle `π`, within the sizes of the fans occurring in Case IV
(`(3,3,0)` or `(2,2,2)`), has `n₀ = n₁`. -/
theorem block_eq (D : CongruentRegionDissection N) (hnc : NotComb (slen D 0) (slen D 1) (slen D 2))
    (hγ : D.model.angleAt 2 = Real.pi / 3) (hαβ : D.model.angleAt 0 + D.model.angleAt 1 = 2 * Real.pi / 3)
    (n0 n1 n2 : ℕ) (hb : (n2 = 0 ∧ n0 ≤ 3 ∧ n1 ≤ 3) ∨ (n0 ≤ 2 ∧ n1 ≤ 2 ∧ n2 ≤ 2))
    (h : (n0 : ℝ) * D.model.angleAt 0 + n1 * D.model.angleAt 1 + n2 * D.model.angleAt 2 = Real.pi) : n0 = n1 := by
  by_contra hne
  have hA0 := model_angle_pos' D 0
  have hA1 := model_angle_pos' D 1
  have hp := Real.pi_pos
  have hb1 : D.model.angleAt 1 = 2 * Real.pi / 3 - D.model.angleAt 0 := by linarith
  rw [hγ, hb1] at h
  have hlt : D.model.angleAt 0 < 2 * Real.pi / 3 := by linarith
  have nr := no_rat_alpha D hnc hαβ
  rcases hb with ⟨rfl, h0, h1⟩ | ⟨h0, h1, h2⟩
  · interval_cases n0 <;> interval_cases n1 <;>
      first
      | exact absurd rfl hne
      | (norm_num at h; first
          | (exfalso; linarith)
          | exact nr (Or.inl (by linarith))
          | exact nr (Or.inr (Or.inl (by linarith)))
          | exact nr (Or.inr (Or.inr (by linarith))))
  · interval_cases n0 <;> interval_cases n1 <;> interval_cases n2 <;>
      first
      | exact absurd rfl hne
      | (norm_num at h; first
          | (exfalso; linarith)
          | exact nr (Or.inl (by linarith))
          | exact nr (Or.inr (Or.inl (by linarith)))
          | exact nr (Or.inr (Or.inr (by linarith))))

end Erdos634.Draft.LaczFormal.RG
