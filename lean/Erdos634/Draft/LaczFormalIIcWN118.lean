-- Draft/LaczFormalIIcWN118.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2: `iicNoKites_of_supply7`, the conditional with the supply shrunk to ONE hypothesis after R1, R2, R3, R4.
-- PROVED: R1 (outermost cycle), R2 (chord family of the concave vertices), R3 (chords from the corners of `A`: exterior to the corner polygon, pairwise disjoint), R4 (Fig. 8 shapes of the ring quadrilaterals), the fan lemma, the printed-gap repair (corner polygon).
-- NAMED RESIDUE (`IIcSupply7`): (E) `ExcInsideAll` ONLY -- every exceptional point lies strictly inside every closed Gamma_kite chain (printed "C1deg contains all exceptional points", p. 359).
-- NOTE, UNAUDITED.  No witness of the supply by design.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN117
import Erdos634.Draft.LaczFormalIIcWN116
import Erdos634.Draft.LaczFormalIIcWN106
import Erdos634.Draft.LaczFormalIIcWN100

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG
open Erdos634.Draft.LaczFormal.WN (edgeSet wind extAng OrientOK sideFn SC IsCornerOfS ChordsExt)

local notation "tc" => Erdos634.Draft.LaczFormal.WN.toC

variable {N M : ℕ}

def IIcSupply7 : Prop :=
  ∀ (N M : ℕ) [NeZero M] (T : PolyTiling N M) (idx : Fin N → Equiv.Perm (Fin 3)), CaseC T.C idx →
    angleAt T.C.model 2 < Real.pi / 2 → angleAt T.C.model 2 ≠ Real.pi / 3 → Comm (slen T.C 0) (slen T.C 1) → ¬ Comm (slen T.C 0) (slen T.C 2) →
    AngGen (fun l => T.C.model.angleAt l) →
    (∀ j : Fin M, cnt T.C idx (T.P.v j) 0 = 1 ∧ cnt T.C idx (T.P.v j) 1 = 1 ∧ cnt T.C idx (T.P.v j) 2 = 0) →
    kiteB T.C idx ≠ ∅ →
    ExcInsideAll T.C idx T.P

set_option maxHeartbeats 6400000 in
theorem iicNoKites_of_supply7 (H : IIcSupply7) : IIcNoKites := by
  intro N M _ T idx hC h1 h3 hab hac hAng hcor
  by_contra hne
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hExcAll := H N M T idx hC h1 h3 hab hac hAng hcor hne
  obtain ⟨Y0, hY0⟩ := Finset.nonempty_iff_ne_empty.2 hne
  simp only [kiteB, Finset.mem_filter] at hY0
  obtain ⟨-, ⟨Z0, hYZ0⟩, -⟩ := hY0
  obtain ⟨E, hE⟩ := excVerts2_nonempty T.C T.P T.region_eq idx hC h1 h3 hcor
  have hz : ∃ z : ℂ, ∀ (m : ℕ) [NeZero m] (C : Fin m → Plane), (∀ k : Fin m, GKite T.C idx (C k) (C (k + 1))) → Function.Injective C →
      z ∉ Erdos634.Draft.LaczFormal.WN.edgeSet (fun k => tc (C k)) ∧ Erdos634.Draft.LaczFormal.WN.wind (fun k => tc (C k)) z ≠ 0 :=
    ⟨tc E, fun m _ C hCy hinj => hExcAll m C hCy hinj E hE⟩
  obtain ⟨m, hm, C, hCy, hinj, hOut⟩ := r1_outermost_cycle T.C T.P T.region_eq idx hC hab hac h1 h3 hz hYZ0
  haveI : NeZero N := ⟨by obtain ⟨i, -⟩ := hCy 0; exact (Fin.pos i).ne'⟩
  obtain ⟨hm3, hs⟩ := gkite_cycle_simple T.C idx C hCy hinj
  have hsC := (Erdos634.Draft.LaczFormal.WN.simplePolyP_iff C).1 hs
  have hinjC : Function.Injective (fun k => tc (C k)) :=
    fun a b h => hinj (Erdos634.Draft.LaczFormal.WN.toC.injective h)
  have hcg := (corner_angles_gamma T.C T.P T.region_eq idx hC h1 h3 hcor).2
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hγM : T.C.model.angleAt 2 = 2 * Real.pi / M := by
    field_simp
    linarith
  have hint : ∀ k : Fin m, C k ∈ interior T.P.carrier := by
    intro k
    have hXY : GKite T.C idx (C (k - 1)) (C k) := by simpa using hCy (k - 1)
    have := (gkite_vertex_type T.C T.P T.region_eq idx hC.hidxA hC.hregc h1 h3 hXY).1.1
    rw [T.region_eq] at this
    exact this
  have hin : ∀ (j : Fin M) (k : Fin m), 0 < sideFn (tc (T.P.v j)) (tc (T.P.v (j + 1)) - tc (T.P.v j)) (tc (C k)) := by
    intro j k
    have := Erdos634.Draft.LaczFormal.WN.convPoly_inside T.P (hint k) j
    simpa using this
  exact Erdos634.Draft.LaczFormal.WN.kiteLayer6_false
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
      C := fun k => tc (C k)
      hm := hm3
      hCs := hsC
      hCi := hinjC
      turn := gkite_cycle_turn T.C T.P T.region_eq idx hC h1 h3 hAng C hCy hinj
      A := fun j => tc (T.P.v j)
      hAinj := Erdos634.Draft.LaczFormal.WN.convPoly_inj T.P
      hAsc := Erdos634.Draft.LaczFormal.WN.convPoly_SC T.P
      hinside := fun j k => Erdos634.Draft.LaczFormal.WN.convPoly_inside T.P (hint k) j
      fam := fun σ hO => r2_chordfam T.C T.P T.region_eq idx hC hab hac h1 h3 hAng hcor C hCy hinj hO (hExcAll m C hCy hinj) hOut
      ring := by
        intro m' _ q hqS σ hO hturn h
        subst h
        have hσ := hO.1.1
        have hSC : SC q σ := Erdos634.Draft.LaczFormal.WN.equiangular_SC hqS.1.1.2.2.1 hqS.1.1.1 hσ hγM hturn
        obtain ⟨w, hGE, hCE⟩ := r3_chordsExt T.C T.P T.region_eq idx hC hab hac h1 h3 hAng hcor C hCy (hExcAll m C hCy hinj) hOut hin q hqS.1 hσ hSC
        exact ⟨w, hCE, fun hmono => r4_fig8 T.C T.P T.region_eq idx hC hab hac h1 h3 hAng hcor C hCy hinj q hqS hσ hturn w hGE hmono⟩ }

#print axioms iicNoKites_of_supply7

end Erdos634.Draft.LaczFormal.RG
