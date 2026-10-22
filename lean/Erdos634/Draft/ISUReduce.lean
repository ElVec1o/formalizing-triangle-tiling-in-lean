-- Draft/ISUReduce.lean (task ISU, 2026-10-03).  NEW file.  Standard axioms; no sorry/native_decide.
-- Reduction "target isosceles and not equilateral  ==>  IsoTP" for a 2pi/3 tile with alpha not in Q*pi,
-- with NO hypothesis on N, via `LemmaCFinal.lemmaC_general` (which is N-free) and irrationality case checks.
import Erdos634.Draft.ISUCore
import Erdos634.Draft.LemmaCFinal
import Erdos634.Draft.FluxCRow12
import Erdos634.Draft.FluxTurn

open scoped Classical

namespace Erdos634.Draft.ISUReduce

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.LemmaCFinal

-- Closes a goal `False` from linear facts when they force `hα` (resp. `hα'`) to a rational
-- multiple of `pi`, or are plainly inconsistent.  Candidate rationals were computed by solving every
-- case (script (private working notes, not included)).
set_option hygiene false in
macro "irr_close" : tactic => `(tactic| first
  | exact hα ⟨(0:ℚ), by push_cast; linarith⟩
  | exact hα ⟨(1/3:ℚ), by push_cast; linarith⟩
  | exact hα ⟨(1/6:ℚ), by push_cast; linarith⟩
  | exact hα ⟨(1/9:ℚ), by push_cast; linarith⟩
  | exact hα ⟨(2/9:ℚ), by push_cast; linarith⟩
  | exact hα ⟨(4/9:ℚ), by push_cast; linarith⟩
  | exact hα ⟨(-1/9:ℚ), by push_cast; linarith⟩
  | exact hα ⟨(1/12:ℚ), by push_cast; linarith⟩
  | exact hα ⟨(2/15:ℚ), by push_cast; linarith⟩
  | exact hα ⟨(1/5:ℚ), by push_cast; linarith⟩
  | exact hα ⟨(1/4:ℚ), by push_cast; linarith⟩
  | exact hα ⟨(1/2:ℚ), by push_cast; linarith⟩
  | exact hα ⟨(-1/6:ℚ), by push_cast; linarith⟩
  | exact hα ⟨(-1/3:ℚ), by push_cast; linarith⟩
  | exact hα ⟨(2/3:ℚ), by push_cast; linarith⟩
  | exact hα ⟨(-1:ℚ), by push_cast; linarith⟩
  | exact hα ⟨(-1/2:ℚ), by push_cast; linarith⟩
  | exact hα ⟨(5/6:ℚ), by push_cast; linarith⟩
  | exact hα ⟨(4/3:ℚ), by push_cast; linarith⟩
  | exact hα' ⟨(0:ℚ), by push_cast; linarith⟩
  | exact hα' ⟨(1/3:ℚ), by push_cast; linarith⟩
  | exact hα' ⟨(1/6:ℚ), by push_cast; linarith⟩
  | exact hα' ⟨(1/9:ℚ), by push_cast; linarith⟩
  | exact hα' ⟨(2/9:ℚ), by push_cast; linarith⟩
  | exact hα' ⟨(4/9:ℚ), by push_cast; linarith⟩
  | exact hα' ⟨(-1/9:ℚ), by push_cast; linarith⟩
  | exact hα' ⟨(1/12:ℚ), by push_cast; linarith⟩
  | exact hα' ⟨(2/15:ℚ), by push_cast; linarith⟩
  | exact hα' ⟨(1/5:ℚ), by push_cast; linarith⟩
  | exact hα' ⟨(1/4:ℚ), by push_cast; linarith⟩
  | exact hα' ⟨(1/2:ℚ), by push_cast; linarith⟩
  | exact hα' ⟨(-1/6:ℚ), by push_cast; linarith⟩
  | exact hα' ⟨(-1/3:ℚ), by push_cast; linarith⟩
  | exact hα' ⟨(2/3:ℚ), by push_cast; linarith⟩
  | exact hα' ⟨(-1:ℚ), by push_cast; linarith⟩
  | exact hα' ⟨(-1/2:ℚ), by push_cast; linarith⟩
  | exact hα' ⟨(5/6:ℚ), by push_cast; linarith⟩
  | exact hα' ⟨(4/3:ℚ), by push_cast; linarith⟩
  | linarith [Real.pi_pos])

theorem fin3_cases : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide

variable {N : ℕ}

/-- Every angle of the model of a `2pi/3` tile is `alpha`, `pi/3-alpha` or `2pi/3`. -/
theorem model_angle_mem (D : CongruentDissection N) {α a b c : ℝ}
    (hm : D.model.TwoPiThreeData α a b c) (k : Fin 3) :
    D.model.angleAt k = α ∨ D.model.angleAt k = Real.pi / 3 - α ∨
      D.model.angleAt k = 2 * Real.pi / 3 := by
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := hm
  obtain ⟨j, rfl⟩ := σ.surjective k
  rcases fin3_cases j with rfl | rfl | rfl
  · exact Or.inl h0
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h2)

/-- Distinct vertices of the model have distinct angles (irrational `alpha`). -/
theorem model_angle_ne (D : CongruentDissection N) {α a b c : ℝ} (hα : IrrPi α)
    (hm : D.model.TwoPiThreeData α a b c) :
    ∀ p q : Fin 3, p ≠ q → D.model.angleAt p ≠ D.model.angleAt q := by
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := hm
  intro p q hpq e
  obtain ⟨p', rfl⟩ := σ.surjective p
  obtain ⟨q', rfl⟩ := σ.surjective q
  have hp : p' ≠ q' := fun h => hpq (by rw [h])
  rcases fin3_cases p' with rfl | rfl | rfl <;> rcases fin3_cases q' with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hp
    | (simp only [h0, h1, h2] at e; irr_close)

theorem not_similar (D : CongruentDissection N) {α a b c : ℝ} (hα : IrrPi α)
    (hm : D.model.TwoPiThreeData α a b c)
    (hiso : ∃ i j : Fin 3, i ≠ j ∧ D.target.angleAt i = D.target.angleAt j) :
    ¬ SimilarTM D := by
  rintro ⟨μ, τ, hτ⟩
  obtain ⟨i, j, hij, e⟩ := hiso
  rw [(hτ i).1, (hτ j).1] at e
  exact model_angle_ne D hα hm (τ i) (τ j) (fun h => hij (τ.injective h)) e

theorem not_right (D : CongruentDissection N) {α a b c : ℝ} (hα : IrrPi α)
    (hm : D.model.TwoPiThreeData α a b c) : ¬ RightCase D := by
  rintro ⟨α', -, -, -, ⟨p, q, -, -, hq⟩, -⟩
  rcases model_angle_mem D hm q with h | h | h <;> rw [hq] at h
  · exact hα ⟨1 / 2, by push_cast; linarith⟩
  · exact hα ⟨-1 / 6, by push_cast; linarith⟩
  · linarith [Real.pi_pos]

theorem not_twoAlpha (D : CongruentDissection N) {α a b c : ℝ} (hα : IrrPi α)
    (hm : D.model.TwoPiThreeData α a b c) : ¬ TwoAlphaCase D := by
  rintro ⟨α', a', b', c', hα', ⟨τ, h0, -, h1, -, h2, -⟩, -⟩
  have m0 := model_angle_mem D hm (τ 0)
  have m1 := model_angle_mem D hm (τ 1)
  have m2 := model_angle_mem D hm (τ 2)
  rw [h0] at m0; rw [h1] at m1; rw [h2] at m2
  rcases m0 with m0 | m0 | m0 <;> rcases m1 with m1 | m1 | m1 <;>
    rcases m2 with m2 | m2 | m2 <;> irr_close

theorem not_sixty (D : CongruentDissection N) {α a b c : ℝ} (hα : IrrPi α)
    (hm : D.model.TwoPiThreeData α a b c) : ¬ SixtyTile D := by
  rintro ⟨α', a', b', c', hα', ⟨τ, h0, -, h1, -, h2, -⟩⟩
  have m0 := model_angle_mem D hm (τ 0)
  have m1 := model_angle_mem D hm (τ 1)
  have m2 := model_angle_mem D hm (τ 2)
  rw [h0] at m0; rw [h1] at m1; rw [h2] at m2
  rcases m0 with m0 | m0 | m0 <;> rcases m1 with m1 | m1 | m1 <;>
    rcases m2 with m2 | m2 | m2 <;> irr_close

theorem not_threeTwo (D : CongruentDissection N) {α a b c : ℝ} (hα : IrrPi α)
    (hm : D.model.TwoPiThreeData α a b c) : ¬ ThreeTwoCase D := by
  rintro ⟨α', β', a', b', c', hα', hrel, ⟨τ, h0, -, h1, -, h2, -⟩, -⟩
  have m0 := model_angle_mem D hm (τ 0)
  have m1 := model_angle_mem D hm (τ 1)
  have m2 := model_angle_mem D hm (τ 2)
  rw [h0] at m0; rw [h1] at m1; rw [h2] at m2
  rcases m0 with m0 | m0 | m0 <;> rcases m1 with m1 | m1 | m1 <;>
    rcases m2 with m2 | m2 | m2 <;> irr_close

/-- A target with three pairwise distinct prescribed angles has no two equal corner angles. -/
theorem tgt_ne (D : CongruentDissection N) {x y z : ℝ} (h : TgtAngles D x y z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∀ i j : Fin 3, i ≠ j → D.target.angleAt i ≠ D.target.angleAt j := by
  obtain ⟨σ, h0, h1, h2⟩ := h
  intro i j hij e
  obtain ⟨i', rfl⟩ := σ.surjective i
  obtain ⟨j', rfl⟩ := σ.surjective j
  have hp : i' ≠ j' := fun h => hij (by rw [h])
  rcases fin3_cases i' with rfl | rfl | rfl <;> rcases fin3_cases j' with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hp
    | (simp only [h0, h1, h2] at e; first | exact hxy e | exact hxy e.symm | exact hxz e | exact hxz e.symm | exact hyz e | exact hyz e.symm)

theorem not_F1 (D : CongruentDissection N) {α : ℝ} (hα : IrrPi α)
    (hiso : ∃ i j : Fin 3, i ≠ j ∧ D.target.angleAt i = D.target.angleAt j) :
    ¬ F1Shape D α := by
  obtain ⟨i, j, hij, e⟩ := hiso
  rintro (h | h) <;>
    exact tgt_ne D h (by intro hh; irr_close) (by intro hh; irr_close) (by intro hh; irr_close)
      i j hij e

theorem not_F2to4 (D : CongruentDissection N) {α : ℝ} (hα : IrrPi α)
    (hiso : ∃ i j : Fin 3, i ≠ j ∧ D.target.angleAt i = D.target.angleAt j) :
    ¬ F2to4Shape D α := by
  obtain ⟨i, j, hij, e⟩ := hiso
  rintro (h | h | h | h | h) <;>
    exact tgt_ne D h (by intro hh; irr_close) (by intro hh; irr_close) (by intro hh; irr_close)
      i j hij e

/-- **Reduction.**  A `2pi/3` tile with `alpha` irrational (any `N`) whose target has two equal
corner angles and is not equilateral forces the target to be one of the two `IsoTP` shapes, for
some irrational-angle `2pi/3` description of the model. -/
theorem iso_to_isoTP (D : CongruentDissection N) {α a b c : ℝ} (hα : IrrPi α)
    (hm : D.model.TwoPiThreeData α a b c)
    (hiso : ∃ i j : Fin 3, i ≠ j ∧ D.target.angleAt i = D.target.angleAt j)
    (hne : ¬ Equilateral D) :
    ∃ α' a' b' c' : ℝ, IrrPi α' ∧ D.model.TwoPiThreeData α' a' b' c' ∧ IsoTP D α' := by
  have hirr : ∃ k, IrrPi (D.model.angleAt k) := by
    obtain ⟨σ, h0, -⟩ := hm
    exact ⟨σ 0, by rw [h0]; exact hα⟩
  have hns := not_similar D hα hm hiso
  rcases lemmaC_general D hirr hns with h | h | h | h | h
  · exact absurd h (not_right D hα hm)
  · exact absurd h (not_twoAlpha D hα hm)
  · exact absurd h (not_sixty D hα hm)
  · obtain ⟨α', a', b', c', hα', hm', hc⟩ := h
    refine ⟨α', a', b', c', hα', hm', ?_⟩
    rcases hc with h | h | h | h
    · exact absurd h hne
    · exact h
    · exact absurd h (not_F1 D hα' hiso)
    · exact absurd h (not_F2to4 D hα' hiso)
  · exact absurd h (not_threeTwo D hα hm)

end Erdos634.Draft.ISUReduce
