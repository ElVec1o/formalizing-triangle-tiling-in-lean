-- Draft/BeesonIso2a.lean -- Beeson, "Tilings of an isosceles triangle" (arXiv 1206.1974v7), Sect. 12.1: Theorem 12.5 and the relation form of Lemmas 12.3, 12.4.
--   `beeson_t12_5`  : D a CongruentDissection (any N, reflections, not edge-to-edge) of an isosceles triangle with base angles alpha (target corners 0 and 1) by the tile (alpha, pi/3 - alpha, 2 pi/3),
--                     alpha not in Q pi  ==>  Comm a b /\ Comm a c  (the tile is rational).  Route: Beeson-Zhang Thm 1.1 (`bz_thm11`, for every triangle not similar to the tile); the printed route
--                     (links Gamma_a, Gamma_c, Lemmas 12.2-12.4) is NOT followed.
--   `beeson_l12_3`, `beeson_l12_4` : the relations j c = p a + q b (j > 0) and j a = p b + q c (j > 0, p > 0), derived FROM beeson_t12_5 (so these are consequences here, not steps; Beeson uses them to prove 12.5).
-- WITNESS STATUS: no isosceles (non-equilateral) tiling by the 2pi/3 tile is known, so the geometric hypotheses (CongruentDissection of such a target) are NOT witnessed.  `notSim_isosceles` has its arithmetic
-- witnessed on cos alpha = 13/14 (`wit_notSim_arith`).  NOTE, UNAUDITED.
-- Credit: Beeson (arXiv 1206.1974v7, Thm 12.5, Lemmas 12.3, 12.4), Beeson-Zhang (arXiv 2604.01314, Thm 1.1), Laczkovich (DCG 48 (2012)), Herdt, Zhang.
import Erdos634.Draft.LaczFormalBZL7d7
import Erdos634.Draft.FluxPaperWitness

open scoped Classical
open Erdos634.Geometry Erdos634.Draft.LaczFormal.Thm21 Erdos634.Draft.LaczFormal.RG Erdos634.Draft.LaczFormal.BZL7Wit Erdos634.Draft.FluxPaperWitness

namespace Erdos634.Draft.BeesonIso2a

variable {N : ℕ}

/-- Arithmetic: the apex angle `pi - 2 alpha` is none of `alpha`, `pi/3 - alpha`, `2 pi/3` when `alpha` is irrational. -/
theorem apex_ne {α : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) :
    Real.pi - 2 * α ≠ α ∧ Real.pi - 2 * α ≠ Real.pi / 3 - α ∧ Real.pi - 2 * α ≠ 2 * Real.pi / 3 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; exact hα ⟨1 / 3, by push_cast; linarith⟩
  · intro h; exact hα ⟨2 / 3, by push_cast; linarith⟩
  · intro h; exact hα ⟨1 / 6, by push_cast; linarith⟩

theorem notSim_isosceles (D : CongruentDissection N) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoPiThreeData α a b c) (hA : D.target.angleAt 0 = α) (hB : D.target.angleAt 1 = α) : NotSim D := by
  have hC : D.target.angleAt 2 = Real.pi - 2 * α := by
    have hs := D.target.angleAt_sum; rw [hA, hB] at hs; linarith
  obtain ⟨h1, h2, h3⟩ := apex_ne hα
  exact notSim_of_no_match D h 2 (by rw [hC]; exact h1) (by rw [hC]; exact h2) (by rw [hC]; exact h3)

/-- **Beeson Theorem 12.5.**  -/
theorem beeson_t12_5 (D : CongruentDissection N) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoPiThreeData α a b c) (hA : D.target.angleAt 0 = α) (hB : D.target.angleAt 1 = α) :
    Comm a b ∧ Comm a c :=
  bz_thm11 D hα h (notSim_isosceles D hα h hA hB)

/-- **Beeson Lemma 12.3** (relation form, derived from Theorem 12.5): `j c = p a + q b`, `j > 0`. -/
theorem beeson_l12_3 (D : CongruentDissection N) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoPiThreeData α a b c) (hA : D.target.angleAt 0 = α) (hB : D.target.angleAt 1 = α) :
    ∃ j p q : ℕ, 0 < j ∧ (j : ℝ) * c = p * a + q * b := by
  obtain ⟨-, p, q, hp, hq, hpq⟩ := beeson_t12_5 D hα h hA hB
  exact ⟨q, p, 0, hq, by push_cast; linarith⟩

/-- **Beeson Lemma 12.4** (relation form, derived): `j a = p b + q c`, `j > 0`, `p > 0`. -/
theorem beeson_l12_4 (D : CongruentDissection N) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoPiThreeData α a b c) (hA : D.target.angleAt 0 = α) (hB : D.target.angleAt 1 = α) :
    ∃ j p q : ℕ, 0 < j ∧ 0 < p ∧ (j : ℝ) * a = p * b + q * c := by
  obtain ⟨⟨j, p, hj, hp, hjp⟩, -⟩ := beeson_t12_5 D hα h hA hB
  exact ⟨j, p, 0, hj, hp, by push_cast; linarith⟩

/-- Witness for the arithmetic of `apex_ne` on the (3,5,7) tile (`cos alpha = 13/14`, `alpha357_irr`). -/
theorem wit_notSim_arith : (¬ ∃ r : ℚ, α357 = (r : ℝ) * Real.pi) ∧ Real.cos α357 = 13 / 14 ∧
    Real.pi - 2 * α357 ≠ α357 ∧ Real.pi - 2 * α357 ≠ Real.pi / 3 - α357 ∧ Real.pi - 2 * α357 ≠ 2 * Real.pi / 3 :=
  ⟨α357_irr, cos_α357, (apex_ne α357_irr).1, (apex_ne α357_irr).2.1, (apex_ne α357_irr).2.2⟩

end Erdos634.Draft.BeesonIso2a

#print axioms Erdos634.Draft.BeesonIso2a.beeson_t12_5
#print axioms Erdos634.Draft.BeesonIso2a.beeson_l12_3
#print axioms Erdos634.Draft.BeesonIso2a.beeson_l12_4
#print axioms Erdos634.Draft.BeesonIso2a.wit_notSim_arith
