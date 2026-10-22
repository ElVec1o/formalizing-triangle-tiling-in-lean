-- Draft/LaczFormalIIcWN76.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2: `IIcNoKites` from the SMALLER supply `IIcInnerCycleSupply`.
-- All data of the full cycle are now DERIVED at tile level: the cycle is a closed injective chain of Gamma_kite edges (`GKite`), its polygon `toC o C` is simple (`gkite_cycle_simple`, WN18) with >= 3 vertices,
-- every vertex turns by gamma, 0 or -gamma (`gkite_cycle_turn`, WN70), `gamma = 2 pi / M` and `3 <= M` (`corner_angles_gamma`, `ConvPoly.three_le`), `alpha != beta` and the angle sum (`AngGen`);
-- the straight-vertex gap of the printed proof is repaired (`exists_corner`, WN73).  The ONLY named supply left is `InnerCornerSupply`, stated for the OUTERMOST (the cycle C1 of the printed nesting C_{i+1} in C_i-interior) cycle: for every corner polygon `q` of it
-- and every orientation sign `sigma`, a chord family (Gamma_except edges of concave vertices; direction/non-crossing/disjointness), the ring `RingSetup` of the Gamma_except edges of the vertices of A and the Fig. 8
-- shapes (`CornerRing`).  The existence of the outermost (C1 of the printed nesting C_{i+1} in C_i-interior) cycle (printed p. 359: "we may list the cycles of Gamma_kite as C_1, ..., C_s, where C_{i+1} in C_i-interior"; the convexity step is for C_1 since A minus C_1-interior contains no vertex of Gamma_kite) is inside the supply as well (it needs nesting, WN31, plus a Jordan-type inside relation).
-- NOTE, UNAUDITED.  No witness of the supply by design (it is the inconsistent hypothesis set of the printed proof).  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN74
import Erdos634.Draft.LaczFormalIIcWN75
import Erdos634.Draft.LaczFormalIIcWN70
import Erdos634.Draft.LaczFormalIIcSym

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

/-- The tile-level content for the outermost (C1 of the printed nesting C_{i+1} in C_i-interior) cycle `C` (as a complex polygon). -/
def InnerCornerSupply (M : ℕ) [NeZero M] (α β γ : ℝ) {m : ℕ} [NeZero m] (C : Fin m → ℂ) : Prop :=
  ∀ (m' : ℕ) [NeZero m'] (q : Fin m' → ℂ), Erdos634.Draft.LaczFormal.WN.IsCornerOf C q → ∀ σ, Erdos634.Draft.LaczFormal.WN.OrientOK q σ →
    Erdos634.Draft.LaczFormal.WN.CornerRing M α β γ q σ

/-- The (single) named supply: an outermost (C1 of the printed nesting C_{i+1} in C_i-interior) closed Gamma_kite chain carrying the corner/chord/ring data. -/
def IIcInnerCycleSupply : Prop :=
  ∀ (N M : ℕ) [NeZero M] (T : PolyTiling N M) (idx : Fin N → Equiv.Perm (Fin 3)), CaseC T.C idx →
    angleAt T.C.model 2 < Real.pi / 2 → angleAt T.C.model 2 ≠ Real.pi / 3 → Comm (slen T.C 0) (slen T.C 1) → ¬ Comm (slen T.C 0) (slen T.C 2) →
    AngGen (fun l => T.C.model.angleAt l) →
    (∀ j : Fin M, cnt T.C idx (T.P.v j) 0 = 1 ∧ cnt T.C idx (T.P.v j) 1 = 1 ∧ cnt T.C idx (T.P.v j) 2 = 0) →
    kiteB T.C idx ≠ ∅ →
    ∃ (m : ℕ) (_ : NeZero m) (C : Fin m → Plane), (∀ k : Fin m, GKite T.C idx (C k) (C (k + 1))) ∧ Function.Injective C ∧
      InnerCornerSupply M (T.C.model.angleAt 0) (T.C.model.angleAt 1) (T.C.model.angleAt 2) (fun k => Erdos634.Draft.LaczFormal.WN.toC (C k))

theorem iicNoKites_of_supply3 (H : IIcInnerCycleSupply) : IIcNoKites := by
  intro N M _ T idx hC h1 h3 hab hac hAng hcor
  by_contra hne
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  obtain ⟨m, hm, C, hCy, hinj, hS⟩ := H N M T idx hC h1 h3 hab hac hAng hcor hne
  haveI : NeZero N := ⟨by obtain ⟨i, -⟩ := hCy 0; exact (Fin.pos i).ne'⟩
  obtain ⟨hm3, hs⟩ := gkite_cycle_simple T.C idx C hCy hinj
  have hsC := (Erdos634.Draft.LaczFormal.WN.simplePolyP_iff C).1 hs
  have hinjC : Function.Injective (fun k => Erdos634.Draft.LaczFormal.WN.toC (C k)) :=
    fun a b h => hinj (Erdos634.Draft.LaczFormal.WN.toC.injective h)
  have hcg := (corner_angles_gamma T.C T.P T.region_eq idx hC h1 h3 hcor).2
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hγM : T.C.model.angleAt 2 = 2 * Real.pi / M := by
    field_simp
    linarith
  exact Erdos634.Draft.LaczFormal.WN.kiteLayer2_false
    { α := T.C.model.angleAt 0
      β := T.C.model.angleAt 1
      γ := T.C.model.angleAt 2
      hsum := hAng.sum
      hα := hAng.pos 0
      hβ := hAng.pos 1
      hγ := hAng.pos 2
      hγM := hγM
      hne := hAng.ne01
      hM := T.P.three_le
      m := m
      hmne := hm
      C := fun k => Erdos634.Draft.LaczFormal.WN.toC (C k)
      hm := hm3
      hCs := hsC
      hCi := hinjC
      turn := gkite_cycle_turn T.C T.P T.region_eq idx hC h1 h3 hAng C hCy hinj
      corner := hS }

#print axioms iicNoKites_of_supply3

end Erdos634.Draft.LaczFormal.RG
