-- Draft/LaczFormalIIcWN6.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2/6.3, Route B: NON-VACUITY witness for `wind_pm_one` (B4).
-- The triangle 0, 1, I is a `SimplePoly`, height 1/2 is generic and crossed, so the hypotheses of `wind_pm_one` are satisfiable.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2/6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN5

open scoped Classical Fin.NatCast
open Complex

namespace Erdos634.Draft.LaczFormal.WN

noncomputable def tri : Fin 3 → ℂ := ![0, 1, I]

theorem tri_simple : SimplePoly tri := by
  intro i j hij z hz
  obtain ⟨h1, h2⟩ := hz
  rw [segment_eq_image'] at h1 h2
  obtain ⟨u, ⟨hu0, hu1⟩, hz1⟩ := h1
  obtain ⟨v, ⟨hv0, hv1⟩, hz2⟩ := h2
  simp only [Complex.real_smul] at hz1 hz2
  fin_cases i <;> fin_cases j <;> simp [tri] at hij hz1 hz2 ⊢
  · -- 0,1
    subst hz1
    have a := congrArg Complex.re hz2; have b := congrArg Complex.im hz2
    simp at a b
    have hv : v = 0 := by linarith
    subst hv
    have hu : u = 1 := by simpa using a.symm
    subst hu; simp
  · -- 0,2
    subst hz1
    have a := congrArg Complex.re hz2; have b := congrArg Complex.im hz2
    simp at a b
    have hu : u = 0 := by linarith
    subst hu; simp
  · -- 1,0
    subst hz2
    have a := congrArg Complex.re hz1; have b := congrArg Complex.im hz1
    simp at a b
    have hu : u = 0 := by linarith
    subst hu
    have hv : v = 1 := by linarith
    subst hv; simp
  · -- 1,2
    subst hz1
    have a := congrArg Complex.re hz2; have b := congrArg Complex.im hz2
    simp at a b
    have hu : u = 1 := by linarith
    subst hu; simp
  · -- 2,0
    subst hz2
    have a := congrArg Complex.re hz1; have b := congrArg Complex.im hz1
    simp at a b
    have hu : u = 1 := by linarith
    subst hu
    have hv : v = 0 := by linarith
    subst hv; simp
  · -- 2,1
    subst hz1
    have a := congrArg Complex.re hz2; have b := congrArg Complex.im hz2
    simp at a b
    have hu : v = 1 := by linarith
    subst hu
    have hu' : u = 0 := by linarith
    subst hu'; simp

/-- Non-vacuity of `wind_pm_one`: the triangle `0, 1, I` at generic height `1/2`. -/
theorem tri_hyp : SimplePoly tri ∧ (∀ i, (tri i).im ≠ 1 / 2) ∧ ∃ z ∈ edgeSet tri, z.im = 1 / 2 := by
  refine ⟨tri_simple, ?_, ⟨(I / 2 : ℂ), ?_, by simp⟩⟩
  · intro i; fin_cases i <;> simp [tri]
  · refine Set.mem_iUnion.2 ⟨2, ?_⟩
    rw [segment_eq_image']
    refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    simp [tri]; ring

end Erdos634.Draft.LaczFormal.WN
