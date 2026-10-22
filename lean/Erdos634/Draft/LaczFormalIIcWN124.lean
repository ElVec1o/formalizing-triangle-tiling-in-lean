-- Draft/LaczFormalIIcWN124.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3, p. 358), Lemma 6.2: the BASE CASE of `ExcInsideAll`: a closed Gamma_kite chain with no Gamma_kite vertex strictly inside contains ALL exceptional points.
-- Printed: "we may assume that C-degree does not contain any vertex of Gamma_kite ... u(alpha+beta) + v(alpha+beta+2 gamma) = (u+v-2) pi ... u = v + N ... there are at least N convex vertices of C such that the corresponding edge arrives at an exceptional point belonging to C-degree".
-- Route: (c) `gkite_cycle_turn_sigma` + `OrientOK` (sum of turns `2 pi`) give `#convex = #concave + M`; (b) `r2c_chord_core`, `r2c_chord_end` (WN122): the chord of a convex vertex runs inside and ends at a concave vertex (injectively, `gexc_arrive_kite_unique`) or at an exceptional point;
-- (d) `exc_all_inside_gen` (WN120) with the capacities `cnt gamma - cnt alpha` (`gexc_exc_interior_exact`, sum `M` by `exc_census`); an exceptional point is not on the polygon (`exc_not_on_kite_edge`, WN123) and its winding number is `sigma` (`wind_end_eq`).
-- NOTE, UNAUDITED.  Hypotheses: the Case IIc block + AngGen.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN123
import Erdos634.Draft.LaczFormalIIcWN122
import Erdos634.Draft.LaczFormalIIcWN120
import Erdos634.Draft.LaczFormalIIcWN70
import Erdos634.Draft.LaczFormalIIcWN46

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG
open Erdos634.Draft.LaczFormal.WN (edgeSet wind extAng OrientOK)

local notation "tc" => Erdos634.Draft.LaczFormal.WN.toC

variable {N M : ℕ}

/-- `#convex = #concave + M` for a closed injective Gamma_kite chain (printed `u = v + N`), in the orientation `sigma`. -/
theorem convex_count [NeZero N] [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0)
    {m : ℕ} [NeZero m] (C : Fin m → Plane) (hCy : ∀ k : Fin m, GKite D idx (C k) (C (k + 1))) (hinj : Function.Injective C) {σ : ℝ} (hO : OrientOK (cyc C) σ) :
    (Finset.univ.filter (fun k : Fin m => 0 < σ * extAng (cyc C) k)).card =
      (Finset.univ.filter (fun k : Fin m => σ * extAng (cyc C) k < 0)).card + M := by
  have hσ : σ = 1 ∨ σ = -1 := hO.1.1
  have hγ := G.pos 2
  have hMγ := (corner_angles_gamma D P hreg idx hC h1 h3 hcor).2
  have hsum := hO.2.2.1
  have hs2 : ∑ k : Fin m, σ * extAng (cyc C) k = 2 * Real.pi := by
    rw [Finset.sum_sub_distrib] at hsum
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    linarith
  have hturn := gkite_cycle_turn_sigma D P hreg idx hC h1 h3 G C hCy hinj hσ
  set γ := D.model.angleAt 2 with hγdef
  have hpt : ∀ k : Fin m, σ * extAng (cyc C) k = (if 0 < σ * extAng (cyc C) k then γ else 0) - (if σ * extAng (cyc C) k < 0 then γ else 0) := by
    intro k
    rcases hturn k with h | h | h
    · rw [h, if_pos hγ, if_neg (not_lt.2 (by linarith))]; ring
    · rw [h, if_neg (not_lt.2 (by linarith)), if_pos (by linarith)]; ring
    · rw [h]; simp
  have e1 : ∑ k : Fin m, (if 0 < σ * extAng (cyc C) k then γ else 0) =
      ((Finset.univ.filter (fun k : Fin m => 0 < σ * extAng (cyc C) k)).card : ℝ) * γ := by
    rw [← Finset.sum_filter]; simp
  have e2 : ∑ k : Fin m, (if σ * extAng (cyc C) k < 0 then γ else 0) =
      ((Finset.univ.filter (fun k : Fin m => σ * extAng (cyc C) k < 0)).card : ℝ) * γ := by
    rw [← Finset.sum_filter]; simp
  rw [Finset.sum_congr rfl (fun k _ => hpt k), Finset.sum_sub_distrib, e1, e2] at hs2
  have : (((Finset.univ.filter (fun k : Fin m => 0 < σ * extAng (cyc C) k)).card : ℝ)) =
      ((Finset.univ.filter (fun k : Fin m => σ * extAng (cyc C) k < 0)).card : ℝ) + M := by
    have hh : (((Finset.univ.filter (fun k : Fin m => 0 < σ * extAng (cyc C) k)).card : ℝ) -
        ((Finset.univ.filter (fun k : Fin m => σ * extAng (cyc C) k < 0)).card : ℝ) - M) * γ = 0 := by nlinarith
    rcases mul_eq_zero.1 hh with h | h
    · linarith
    · exact absurd h hγ.ne'
  exact_mod_cast this

#print axioms convex_count

end Erdos634.Draft.LaczFormal.RG
