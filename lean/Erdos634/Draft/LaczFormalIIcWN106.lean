-- Draft/LaczFormalIIcWN106.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3, p. 359-360), Lemma 6.2, R3 ASSEMBLED: the chords `V_i W_i` from the corners of `A` to the corner polygon `q` of the outermost cycle are
-- exterior to `q` (`chord_outside`, WN102) and pairwise disjoint (`spokes_disjoint_C`, WN105): `ChordsExt A q w sigma`, with `w i` the index in `q` of the end of the Gamma_except edge from `P.v i`.
-- Hypotheses: `ExcInside` (NAMED RESIDUE E), R1 (`hOut`), the strictly convex corner polygon `q` (all turns `sigma * gamma`, `SC q sigma`) and `IsCornerOfS` (WN103).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN105
import Erdos634.Draft.LaczFormalIIcWN103
import Erdos634.Draft.LaczFormalIIcWN79

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG
open Erdos634.Draft.LaczFormal.WN (edgeSet wind extAng OrientOK sideFn SC IsCornerOfS ChordsExt)

local notation "tc" => Erdos634.Draft.LaczFormal.WN.toC

variable {N M : ℕ}

set_option maxHeartbeats 6400000 in
theorem r3_chordsExt [NeZero N] [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0)
    {m : ℕ} [NeZero m] (C : Fin m → Plane) (hCy : ∀ k : Fin m, GKite D idx (C k) (C (k + 1)))
    (hExc : ∀ E ∈ excVerts2 D idx P, tc E ∉ edgeSet (cyc C) ∧ wind (cyc C) (tc E) ≠ 0)
    (hOut : ∀ v Y, GKite D idx v Y → v ∈ Set.range C ∨ (tc v ∉ edgeSet (cyc C) ∧ wind (cyc C) (tc v) ≠ 0))
    (hin : ∀ (j : Fin M) (k : Fin m), 0 < sideFn (tc (P.v j)) (tc (P.v (j + 1)) - tc (P.v j)) (tc (C k)))
    (q : Fin M → ℂ) (hq : IsCornerOfS (cyc C) q) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hSC : SC q σ) :
    ∃ w : Fin M → Fin M, (∀ i, GExc D idx (P.v i) (Erdos634.Draft.LaczFormal.WN.toC.symm (q (w i)))) ∧
      ChordsExt (fun j => tc (P.v j)) q w σ := by
  classical
  obtain ⟨⟨h3M, hqs, hqi, hqne, hqe, hqv⟩, hqsurj⟩ := hq
  have key := fun i => r3_chord_core D P hreg idx hC hab hac h1 h3 G hcor C hCy hExc hOut hin i
  choose W k hW hWk hstr hchord using key
  have hsurj : ∀ i, ∃ j, q j = cyc C (k i) := by
    intro i
    apply hqsurj
    intro h0
    exact hstr i ((gkite_cycle_straight_iff D P hreg idx hC h1 h3 G C hCy (k i)).2 h0)
  choose w hw using hsurj
  have hqw : ∀ i, q (w i) = tc (W i) := by
    intro i; rw [hw i]; unfold cyc; rw [hWk i]
  have hWi : ∀ i, GExc D idx (P.v i) (C (k i)) := fun i => by rw [← hWk i]; exact hW i
  refine ⟨w, fun i => ?_, ?_, ?_⟩
  · rw [hqw i]; simpa using hW i
  · -- exterior
    intro i s hs0 hs1
    have he : tc (P.v (i + 1)) - tc (P.v i) ≠ 0 := by
      intro e
      exact Erdos634.Draft.LaczFormal.WN.convPoly_e_ne P i (Erdos634.Draft.LaczFormal.WN.toC.injective (sub_eq_zero.1 e))
    have hpq : ∀ a : Fin M, 0 < sideFn (tc (P.v i)) (tc (P.v (i + 1)) - tc (P.v i)) (q a) := by
      intro a
      obtain ⟨k', hk', -⟩ := hqv a
      rw [hk']; exact hin i k'
    have hx0 : wind q (tc (P.v i)) = 0 :=
      Erdos634.Draft.LaczFormal.WN.wind_zero_of_halfplane q _ _ he hpq _ (by rw [Erdos634.Draft.LaczFormal.WN.sideFn_base])
    have hx : tc (P.v i) ∉ edgeSet q := by
      intro hmem
      have := Erdos634.Draft.LaczFormal.WN.edgeSet_sideFn_pos q _ _ hpq _ hmem
      rw [Erdos634.Draft.LaczFormal.WN.sideFn_base] at this
      exact lt_irrefl _ this
    have hmiss : ∀ s' : ℝ, 0 < s' → s' < 1 → tc (P.v i) + (s' : ℂ) * (q (w i) - tc (P.v i)) ∉ edgeSet q := by
      intro s' hs0' hs1'
      rw [hqe, hqw i, ← tc_chord_pt]
      exact (hchord i s' hs0' hs1').1
    exact Erdos634.Draft.LaczFormal.WN.chord_outside hqi h3M hSC hσ _ _ hx hx0 hmiss s hs0 hs1
  · -- disjointness
    intro i j hij
    rw [Set.disjoint_left]
    intro z hz1 hz2
    obtain ⟨V, hV⟩ : ∃ V : Plane, tc V = z := ⟨Erdos634.Draft.LaczFormal.WN.toC.symm z, by simp⟩
    subst hV
    rw [hqw i] at hz1
    rw [hqw j] at hz2
    have e1 := (Erdos634.Draft.LaczFormal.WN.mem_segment_toC _ _ _).2 hz1
    have e2 := (Erdos634.Draft.LaczFormal.WN.mem_segment_toC _ _ _).2 hz2
    rw [hWk i] at e1
    rw [hWk j] at e2
    refine spokes_disjoint_C D P hreg idx hC hab hac h1 h3 G C hCy hExc hij (hWi i) (hWi j) ?_ V e1 e2
    intro s hs0 hs1
    have := (hchord i s hs0 hs1).2
    rwa [hWk i] at this

#print axioms r3_chordsExt

end Erdos634.Draft.LaczFormal.RG
