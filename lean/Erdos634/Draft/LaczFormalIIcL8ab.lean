-- Draft/LaczFormalIIcL8ab.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3: `lemma63` (arbitrary M) and the remaining Case IIc statement modulo Lemma 6.2 (NoKites) and the printed inequality G11.
--  `lemma63`   : under the Case IIc block with `kiteB = empty`:  Concl7  or  (Concl5Rest and a geometric side sequence), conclusion (v) without its printed inequality.
--  `iic_ang_modulo_62` : for every regular polygon tiling of class IIc whose model angles are generic (`AngGen`) and whose `kiteB` is empty: Thm21Concl or (Concl5Rest and Concl5Seq).
--  The inputs NOT proved: (1) `IIcNoKites` -- Lemma 6.2 for generic angles (`kiteB = empty`); (2) the printed inequality of (v) (G11); (3) the subclass of IIc where `AngGen` fails (alpha = beta, or alpha or beta a right angle).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.1-6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcL8aa
import Erdos634.Draft.LaczFormalThm21Assembly

open scoped Classical Fin.NatCast
open EuclideanGeometry Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

/-- **Lemma 6.3** (conditional on `kiteB = empty`; conclusion (v) without its printed inequality). -/
theorem lemma63 [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0)
    (hNK : kiteB D idx = ∅) (W : Fin M → Plane) (hW : ∀ j, GExc D idx (P.v j) (W j)) :
    Concl7 D P ∨ ∃ k, Concl5Rest D P k ∧ ∃ (s : Fin M) (rev : Bool) (a : ℕ → ℝ), Concl5Seq D P k s rev a := by
  by_cases hdiff : ∃ j, W j ≠ W 0
  · obtain ⟨k, rfl⟩ := M_even_of_two D P hreg idx hC hab hac h1 h3 G hcor hNK W hW hdiff
    exact Or.inr ⟨k, lemma63_two D P hreg idx hC hab hac h1 h3 G hcor hNK W hW hdiff⟩
  · push Not at hdiff
    exact Or.inl (lemma63_one D P hreg idx hC hab hac h1 h3 G hcor W hW (fun j => hdiff j))

/-- Lemma 6.2 for generic angles: no type-(B) kite vertex (NOT proved). -/
def IIcNoKites : Prop :=
  ∀ (N M : ℕ) [NeZero M] (T : PolyTiling N M) (idx : Fin N → Equiv.Perm (Fin 3)), CaseC T.C idx →
    angleAt T.C.model 2 < Real.pi / 2 → angleAt T.C.model 2 ≠ Real.pi / 3 → Comm (slen T.C 0) (slen T.C 1) → ¬ Comm (slen T.C 0) (slen T.C 2) →
    AngGen (fun l => T.C.model.angleAt l) →
    (∀ j : Fin M, cnt T.C idx (T.P.v j) 0 = 1 ∧ cnt T.C idx (T.P.v j) 1 = 1 ∧ cnt T.C idx (T.P.v j) 2 = 0) → kiteB T.C idx = ∅

theorem corners_of_cntP0 [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (hP : cntP0 D idx P = M) :
    ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0 := by
  have hall : ∀ k : Fin M, cnt D idx (P.v (k + 1)) 0 = 1 ∧ cnt D idx (P.v (k + 1)) 2 = 0 := by
    intro k
    rcases caseII_polyvertex D P hreg idx hC.hidxA hC.hregc h1 k with ⟨h0, h2, -⟩ | ⟨h0, -, -⟩
    · exact ⟨h0, h2⟩
    · exfalso
      have hle : ∀ i : Fin M, cnt D idx (P.v (i + 1)) 0 ≤ 1 := by
        intro i
        rcases caseII_polyvertex D P hreg idx hC.hidxA hC.hregc h1 i with ⟨h0', -, -⟩ | ⟨h0', -, -⟩ <;> omega
      have : ∑ i : Fin M, cnt D idx (P.v (i + 1)) 0 < ∑ i : Fin M, 1 :=
        Finset.sum_lt_sum (fun i _ => by have := hle i; omega) ⟨k, Finset.mem_univ _, by omega⟩
      unfold cntP0 at hP
      simp at this
      omega
  intro j
  have := hall (j - 1)
  rw [sub_add_cancel] at this
  exact ⟨this.1, by rw [← hC.hregc]; exact this.1, this.2⟩

set_option maxHeartbeats 12800000 in
/-- **Case IIc, generic angles, modulo Lemma 6.2 (NoKites)**: either Theorem 2.1's conclusion holds, or conclusion (v) holds without its printed inequality. -/
theorem iic_ang_modulo_62 (hNK : IIcNoKites) {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) (hex : Thm21Excluded4 T)
    (hAng : AngGen (fun l => T.C.model.angleAt l)) :
    Thm21Concl T.C T.P ∨ ∃ k, Concl5Rest T.C T.P k ∧ ∃ (s : Fin M) (rev : Bool) (a : ℕ → ℝ), Concl5Seq T.C T.P k s rev a := by
  classical
  obtain ⟨h1, h3, hab, hac⟩ := hex
  rcases lemma61 T hreg h1 h3 hab hac with hc1 | hangs
  · exact Or.inl (Or.inl hc1)
  · obtain ⟨idx, hA, hcnt⟩ := hreg
    haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
    have hC : CaseC T.C idx := ⟨idx_dist_of_angle T.C idx hA, hA, fun X => hcnt X, notComb_c_of_comm (slen_pos T.C 2) hab hac⟩
    rcases lemma61_core T.C T.P T.region_eq idx hC h1 h3 with hP | ⟨-, a, ha1, -, -⟩
    · have hcor := corners_of_cntP0 T.C T.P T.region_eq idx hC h1 hP
      have hW : ∀ j : Fin M, ∃ W, GExc T.C idx (T.P.v j) W := fun j => gexc_start_of_corner T.C T.P T.region_eq idx hC h1 h3 hcor j
      choose W hW using hW
      have hNK' := hNK N M T idx hC h1 h3 hab hac hAng hcor
      rcases lemma63 T.C T.P T.region_eq idx hC hab hac h1 h3 hAng hcor hNK' W hW with h7 | h5
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h7)))))))
      · exact Or.inr h5
    · exfalso
      have := hangs (a + 1)
      have ha1' : T.P.angle (a + 1) = angleAt T.C.model 2 := ha1
      rw [ha1'] at this
      linarith

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.lemma63
#print axioms Erdos634.Draft.LaczFormal.RG.iic_ang_modulo_62
