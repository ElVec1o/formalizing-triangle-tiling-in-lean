-- Draft/LaczFormalIIcWN108.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2: `iicNoKites_of_supply6`, the conditional with the supply shrunk after R1, R2, R3.
-- PROVED: R1 (outermost cycle), R2 (chord family of the concave vertices), R3 (chords from the corners of `A`: exterior to the corner polygon, pairwise disjoint), the fan lemma, the printed-gap repair (corner polygon).
-- NAMED RESIDUE (`IIcSupply6`): (E) `ExcInsideAll` -- every exceptional point lies strictly inside every closed Gamma_kite chain (printed "C1deg contains all exceptional points", p. 359);
-- (R4) `Fig8Residue` -- for the chords of R3 in cyclic (monotone) order, the ring quadrilaterals `V_{i-1} V_i W_i W_{i-1}` have the shapes of Fig. 8 (`RingQuadA/B` closure equations).
-- NOTE, UNAUDITED.  No witness of the supply by design.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN107
import Erdos634.Draft.LaczFormalIIcWN106
import Erdos634.Draft.LaczFormalIIcWN100

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG
open Erdos634.Draft.LaczFormal.WN (edgeSet wind extAng OrientOK sideFn SC IsCornerOfS ChordsExt)

local notation "tc" => Erdos634.Draft.LaczFormal.WN.toC

variable {N M : ℕ}

/-- (R4) The Fig. 8 shapes of the ring quadrilaterals, for the chords of R3 in cyclic order. -/
def Fig8Residue [NeZero M] (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (P : ConvPoly M) (α β γ : ℝ) : Prop :=
  ∀ (m : ℕ) [NeZero m] (C : Fin m → Plane), (∀ k : Fin m, GKite D idx (C k) (C (k + 1))) → Function.Injective C → OutermostChain D idx C →
    ∀ (q : Fin M → ℂ), IsCornerOfS (cyc C) q → ∀ σ, OrientOK q σ → (∀ k, σ * extAng q k = γ) →
      ∀ w : Fin M → Fin M, (∀ i, GExc D idx (P.v i) (Erdos634.Draft.LaczFormal.WN.toC.symm (q (w i)))) →
        ChordsExt (fun j => tc (P.v j)) q w σ →
        (((∀ i, w (i + 1) = w i + 1) ∨ (∀ i, w (i + 1) = w i - 1)) →
          ∃ d L mm : ZMod M → ℝ, ∀ i, RG.RingQuadA α β γ (L i) (d i) (mm i) (d (i - 1)) ∨ RG.RingQuadB α β γ (L i) (d i) (mm i) (d (i - 1)))

def IIcSupply6 : Prop :=
  ∀ (N M : ℕ) [NeZero M] (T : PolyTiling N M) (idx : Fin N → Equiv.Perm (Fin 3)), CaseC T.C idx →
    angleAt T.C.model 2 < Real.pi / 2 → angleAt T.C.model 2 ≠ Real.pi / 3 → Comm (slen T.C 0) (slen T.C 1) → ¬ Comm (slen T.C 0) (slen T.C 2) →
    AngGen (fun l => T.C.model.angleAt l) →
    (∀ j : Fin M, cnt T.C idx (T.P.v j) 0 = 1 ∧ cnt T.C idx (T.P.v j) 1 = 1 ∧ cnt T.C idx (T.P.v j) 2 = 0) →
    kiteB T.C idx ≠ ∅ →
    ExcInsideAll T.C idx T.P ∧ Fig8Residue T.C idx T.P (T.C.model.angleAt 0) (T.C.model.angleAt 1) (T.C.model.angleAt 2)

set_option maxHeartbeats 6400000 in
theorem iicNoKites_of_supply6 (H : IIcSupply6) : IIcNoKites := by
  intro N M _ T idx hC h1 h3 hab hac hAng hcor
  by_contra hne
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  obtain ⟨hExcAll, hFig8⟩ := H N M T idx hC h1 h3 hab hac hAng hcor hne
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
  exact Erdos634.Draft.LaczFormal.WN.kiteLayer5_false
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
        have hSC : SC q σ := Erdos634.Draft.LaczFormal.WN.equiangular_SC hqS.1.2.2.1 hqS.1.1 hσ hγM hturn
        obtain ⟨w, hGE, hCE⟩ := r3_chordsExt T.C T.P T.region_eq idx hC hab hac h1 h3 hAng hcor C hCy (hExcAll m C hCy hinj) hOut hin q hqS hσ hSC
        exact ⟨w, hCE, hFig8 m C hCy hinj hOut q hqS σ hO hturn w hGE hCE⟩ }

#print axioms iicNoKites_of_supply6

end Erdos634.Draft.LaczFormal.RG
