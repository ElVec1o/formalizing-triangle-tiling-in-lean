-- Draft/LaczFormalBZ6.lean -- Beeson-Zhang (arXiv 2604.01314v1) Theorem 5.2 (= Theorem 1.1 for an equilateral triangle) and the corollary for polygon targets of Theorem 2.1:
--   `bz_ab_comm`  : `a, b` commensurable (Lemma 3.5 for `a` and for `b`, Lemma 3.6);
--   `bz_thm52`    : `a, b, c` pairwise commensurable;
--   `bz_concl4`   : an equilateral target tiled by the `2 pi/3` tile with alpha not in Q pi satisfies conclusion (iv) of Laczkovich's Theorem 2.1 (sines pairwise commensurable).
-- UNAUDITED.  Credit: Beeson-Zhang (arXiv 2604.01314v1, Thm 5.2), Laczkovich (DCG 48 (2012), Thm 2.1 (iv), Sect. 4, 7).
import Erdos634.Draft.LaczFormalBZ5

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

/-- **Beeson-Zhang Lemma 3.6 with Lemmas 3.5**: `a` and `b` are commensurable. -/
theorem bz_ab_comm (D : CongruentDissection N) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoPiThreeData α a b c)
    (heq : ∀ j : Fin 3, dist (D.target.pts j) (D.target.pts (j + 1)) = dist (D.target.pts 0) (D.target.pts 1)) :
    Comm a b := by
  have h1 := bz_lemma35_tri D hα h heq
  have hα' : ¬ ∃ r : ℚ, Real.pi / 3 - α = (r : ℝ) * Real.pi := by
    rintro ⟨r, hr⟩
    apply hα
    refine ⟨1 / 3 - r, ?_⟩
    push_cast
    linarith
  have h2 := bz_lemma35_tri D hα' (tpt_swap h) heq
  unfold NotComb at h1 h2
  push Not at h1 h2
  obtain ⟨r, p, q, hr, e1⟩ := h1
  obtain ⟨r', p', q', hr', e2⟩ := h2
  have ha : 0 < a := by
    obtain ⟨σ, -, o0, -⟩ := h
    rw [← o0]; exact D.model.oppLen_pos' _
  have hb : 0 < b := by
    obtain ⟨σ, -, -, -, o1, -⟩ := h
    rw [← o1]; exact D.model.oppLen_pos' _
  exact comm_of_two_combs ha hb hr e1 hr' e2

/-- **Beeson-Zhang Theorem 5.2.**  A congruent dissection of an equilateral triangle (any `N`, reflections allowed, not edge-to-edge) by the tile with angles `(α, π/3-α, 2π/3)`, `α ∉ ℚπ`
(sides `a, b, c` opposite `α, β, γ`) has pairwise commensurable `a, b, c`. -/
theorem bz_thm52 (D : CongruentDissection N) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoPiThreeData α a b c)
    (heq : ∀ j : Fin 3, dist (D.target.pts j) (D.target.pts (j + 1)) = dist (D.target.pts 0) (D.target.pts 1)) :
    Comm a b ∧ Comm a c := by
  have hab := bz_ab_comm D hα h heq
  refine ⟨hab, ?_⟩
  obtain ⟨r, hr⟩ := bz_c_rational D hα h hab heq
  have ha : 0 < a := by
    obtain ⟨σ, -, o0, -⟩ := h
    rw [← o0]; exact D.model.oppLen_pos' _
  have hc : 0 < c := by
    obtain ⟨σ, -, -, -, -, -, o2⟩ := h
    rw [← o2]; exact D.model.oppLen_pos' _
  have hrpos : (0 : ℚ) < r := by
    by_contra hneg
    push Not at hneg
    have : (r : ℝ) ≤ 0 := by exact_mod_cast hneg
    nlinarith
  have hnum : 0 < r.num := Rat.num_pos.mpr hrpos
  refine ⟨r.num.toNat, r.den, ?_, r.den_pos, ?_⟩
  · omega
  · have h1 : ((r.num.toNat : ℕ) : ℝ) = (r.num : ℝ) := by
      have : ((r.num.toNat : ℕ) : ℤ) = r.num := Int.toNat_of_nonneg hnum.le
      exact_mod_cast this
    have h2 : (r : ℝ) * (r.den : ℝ) = (r.num : ℝ) := by
      have := Rat.mul_den_eq_num r
      exact_mod_cast this
    rw [h1, hr, ← h2]
    ring

/-- **Conclusion (iv) of Laczkovich's Theorem 2.1 for an equilateral target and the `2π/3` tile** (the case that Beeson-Zhang repair): the sines of the tile angles are pairwise commensurable,
by the law of sines. -/
theorem bz_sines_comm (D : CongruentDissection N) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoPiThreeData α a b c)
    (heq : ∀ j : Fin 3, dist (D.target.pts j) (D.target.pts (j + 1)) = dist (D.target.pts 0) (D.target.pts 1)) :
    Comm (Real.sin α) (Real.sin (Real.pi / 3 - α)) ∧ Comm (Real.sin α) (Real.sin (2 * Real.pi / 3)) := by
  obtain ⟨hab, hac⟩ := bz_thm52 D hα h heq
  have hr := h.alpha_range
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  -- law of sines: a / sin α = b / sin β = c / sin γ
  have hls : ∀ x y : Fin 3, x ≠ y → Real.sin (D.model.angleAt y) * D.model.oppLen x = Real.sin (D.model.angleAt x) * D.model.oppLen y := by
    intro x y hxy
    have key : ∀ k : Fin 3, Real.sin (D.model.angleAt (k + 1)) * D.model.oppLen k = Real.sin (D.model.angleAt k) * D.model.oppLen (k + 1) :=
      Erdos634.TriLawSin.sin_angleAt_mul_sideOpp D.model
    have k0 := key 0
    have k1 := key 1
    have k2 := key 2
    simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (1 : Fin 3) + 1 = 2 from rfl, show (2 : Fin 3) + 1 = 0 from rfl] at k0 k1 k2
    have hcases : (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 0) ∨ (x = 1 ∧ y = 0) ∨ (x = 2 ∧ y = 1) ∨ (x = 0 ∧ y = 2) := by
      fin_cases x <;> fin_cases y <;> simp at hxy ⊢
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact k0
    · exact k1
    · exact k2
    · exact k0.symm
    · exact k1.symm
    · exact k2.symm
  have s01 : Real.sin (Real.pi / 3 - α) * a = Real.sin α * b := by
    have := hls (σ 0) (σ 1) (fun e => absurd (σ.injective e) (by decide))
    rw [h0, h1, o0, o1] at this
    exact this
  have s02 : Real.sin (2 * Real.pi / 3) * a = Real.sin α * c := by
    have := hls (σ 0) (σ 2) (fun e => absurd (σ.injective e) (by decide))
    rw [h0, h2, o0, o2] at this
    exact this
  have hb : 0 < b := by rw [← o1]; exact D.model.oppLen_pos' _
  have hc : 0 < c := by rw [← o2]; exact D.model.oppLen_pos' _
  obtain ⟨p, q, hp, hq, hpq⟩ := hab
  obtain ⟨p', q', hp', hq', hpq'⟩ := hac
  refine ⟨⟨p, q, hp, hq, ?_⟩, ⟨p', q', hp', hq', ?_⟩⟩
  · apply mul_right_cancel₀ hb.ne'
    linear_combination (-(p : ℝ)) * s01 + Real.sin (Real.pi / 3 - α) * hpq
  · apply mul_right_cancel₀ hc.ne'
    linear_combination (-(p' : ℝ)) * s02 + Real.sin (2 * Real.pi / 3) * hpq'

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.bz_ab_comm
#print axioms Erdos634.Draft.LaczFormal.RG.bz_thm52
#print axioms Erdos634.Draft.LaczFormal.RG.bz_sines_comm
