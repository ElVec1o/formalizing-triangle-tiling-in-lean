-- Draft/LaczFormalIIcWN12.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2/6.3, Route B: NON-VACUITY witness for `simple_wind_dichotomy` (B5) and axiom check.
-- The triangle 0, 1, I satisfies all hypotheses (SimplePoly, injective, 3 <= n); by `wind_pm_one` (B4) the sign sigma is attained, so the dichotomy is not trivially "0 or 0".
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2/6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN6
import Erdos634.Draft.LaczFormalIIcWN11

open scoped Classical Fin.NatCast
open Complex

namespace Erdos634.Draft.LaczFormal.WN

theorem tri_injective : Function.Injective tri := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [tri, Complex.ext_iff] at h ⊢

theorem tri_dichotomy_witness :
    SimplePoly tri ∧ Function.Injective tri ∧ 3 ≤ 3 ∧
    (∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ z : ℂ, z ∉ edgeSet tri → wind tri z = 0 ∨ wind tri z = σ) ∧
    (∃ z, z ∉ edgeSet tri ∧ (wind tri z = 1 ∨ wind tri z = -1)) :=
  ⟨tri_simple, tri_injective, le_rfl, simple_wind_dichotomy tri_simple tri_injective le_rfl,
    wind_pm_one tri_simple (1 / 2) (by
      intro i; fin_cases i <;> simp [tri])
      ⟨(1 : ℂ) / 2 + (1 : ℂ) / 2 * I, by
        refine Set.mem_iUnion.2 ⟨1, ?_⟩
        rw [segment_eq_image']
        refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
        simp [tri, Complex.real_smul]; ring_nf, by simp⟩⟩

#print axioms simple_wind_dichotomy
#print axioms tri_dichotomy_witness

end Erdos634.Draft.LaczFormal.WN
