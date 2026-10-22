-- Draft/LaczFormalIIcWN56.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2 (`IIcNoKites`), step (h): NON-VACUITY witness for `no_concave`.
-- The triangle 0, 1, I carries an orientation `OrientOK tri sigma`, and the chord family hypothesis holds for it (vacuously: a triangle has no concave vertex, as its three
-- interior angles are positive with sum pi).  (The theorem says no polygon with a concave vertex satisfies the chord hypotheses; a witness of the hypotheses can only be convex.)
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN55
import Erdos634.Draft.LaczFormalIIcWN25

open scoped Classical Fin.NatCast
open Complex

namespace Erdos634.Draft.LaczFormal.WN

theorem no_concave_witness :
    ∃ σ : ℝ, OrientOK tri σ ∧ (∀ J : Fin 3 → Fin 3, ChordFam tri σ J) ∧ (∀ k : Fin 3, ¬ σ * extAng tri k < 0) := by
  obtain ⟨σ, hO⟩ := orient_exists tri_simple tri_injective (le_refl 3)
  have hno : ∀ k : Fin 3, ¬ σ * extAng tri k < 0 := by
    intro k hk
    have hb := hO.2.1
    have hsum := hO.2.2.1
    have h0 := (hb k).1
    have hpos : ∀ j : Fin 3, 0 < Real.pi - σ * extAng tri j := fun j => (hb j).1
    have : Real.pi < Real.pi - σ * extAng tri k := by linarith
    have hs3 : ∑ j : Fin 3, (Real.pi - σ * extAng tri j) = Real.pi := by rw [hsum]; norm_num
    rw [Fin.sum_univ_three] at hs3
    fin_cases k <;> simp at this <;> nlinarith [hpos 0, hpos 1, hpos 2]
  refine ⟨σ, hO, fun J => ⟨fun k hk => absurd hk (hno k), fun k k' hk => absurd hk (hno k)⟩, hno⟩

#print axioms no_concave_witness

end Erdos634.Draft.LaczFormal.WN
