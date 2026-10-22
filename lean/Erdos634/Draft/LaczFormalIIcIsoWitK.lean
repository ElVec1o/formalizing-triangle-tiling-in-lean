-- Draft/LaczFormalIIcIsoWitK.lean -- NON-VACUITY witness for `IIcIsoCore`, step K: `GExc octDiss idx (V j) O` at EVERY vertex of the regular octagon (the maximal segment is the diameter through `V j`; both gamma-runs end at the centre).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcIsoWitJ
import Erdos634.Draft.LaczFormalRG12GExc

open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Thm21 Erdos634.Draft.LaczFormal.RG Erdos634.Draft.LaczFormal.Graph

namespace Erdos634.Draft.LaczFormal.IsoWit

theorem gammaHead_apex (i : Fin 8) : GammaHead octDiss idx (i, oct.v 0, mkPt 0 0) := by
  refine ⟨2, tp2 i, ?_⟩
  simp [idx]

theorem not_gammaHead (i j : Fin 8) : ¬ GammaHead octDiss idx (i, mkPt 0 0, oct.v j) := by
  rintro ⟨k, hk, hk2⟩
  have : k = 2 := by simpa [idx] using hk2
  subst this
  exact pts2_ne i j hk

theorem gexc_at (j : Fin 8) : GExc octDiss idx (oct.v j) (mkPt 0 0) := by
  refine ⟨dvec j, oct.v (j + 4),
    [(j - 1, oct.v j, mkPt 0 0), (j + 4, mkPt 0 0, oct.v (j + 4))],
    [(j, oct.v j, mkPt 0 0), (j + 3, mkPt 0 0, oct.v (j + 4))], mkPt 0 0, mkPt 0 0,
    dvec_ne j, noBack j, ?_, ?_, by simp, by simp, noStepFwd j, noStepBwd j, ?_, ?_, Or.inl ⟨rfl, le_rfl⟩⟩
  · exact WalkT.cons (stepA j) (WalkT.cons (stepB j) (WalkT.nil _))
  · exact WalkR.cons (stepC j) (WalkR.cons (stepD j) (WalkR.nil _))
  · refine ⟨[(j - 1, oct.v j, mkPt 0 0)], [(j + 4, mkPt 0 0, oct.v (j + 4))], rfl, by simp, ?_, ?_, ⟨_, rfl, rfl⟩⟩
    · intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      exact ⟨2, tp2 _, by simp [idx]⟩
    · intro e he
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at he
      subst he
      exact not_gammaHead _ _
  · refine ⟨[(j, oct.v j, mkPt 0 0)], [(j + 3, mkPt 0 0, oct.v (j + 4))], rfl, by simp, ?_, ?_, ⟨_, rfl, rfl⟩⟩
    · intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      exact ⟨2, tp2 _, by simp [idx]⟩
    · intro e he
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at he
      subst he
      exact not_gammaHead _ _

end Erdos634.Draft.LaczFormal.IsoWit
