-- Draft/LaczFormalIIcWN100.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2: `iicNoKites_of_supply5`, the conditional with the SHRUNK supply after R1 and R2.
-- Proved here: R1 (outermost cycle, WN82-84) and R2 (chord family of the concave vertices, WN88-98), the fan lemma (WN85-87), the printed-gap repair (corner polygon, WN71-73), the abstract ring (WN57-65, WN99).
-- NAMED RESIDUE (`IIcSupply5`): (E) `ExcInsideAll`: every exceptional point lies strictly inside every closed Gamma_kite chain (printed "C1deg contains all exceptional points", p. 359; counting (d4), WN69, needs the
-- interior direction and non-crossing of the chords of CONVEX vertices); (R3, R4) `RingResidue`: for the outermost cycle `C` and each of its corner polygons `q` with all turns `sigma * gamma`, the chords from the vertices of `A`
-- (exterior, pairwise disjoint) and the shapes of the ring quadrilaterals (Fig. 8).
-- NOTE, UNAUDITED.  No witness of the supply by design (hypothesis set of a proof by contradiction).  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN99
import Erdos634.Draft.LaczFormalIIcWN98
import Erdos634.Draft.LaczFormalIIcWN80

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG
open Erdos634.Draft.LaczFormal.WN (edgeSet wind extAng OrientOK ChordFam ExtChord)

local notation "tc" => Erdos634.Draft.LaczFormal.WN.toC

variable {N M : ℕ}

/-- (E) Every exceptional point lies off every closed Gamma_kite chain and has nonzero winding number about it. -/
def ExcInsideAll [NeZero M] (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (P : ConvPoly M) : Prop :=
  ∀ (m : ℕ) [NeZero m] (C : Fin m → Plane), (∀ k : Fin m, GKite D idx (C k) (C (k + 1))) → Function.Injective C →
    ∀ E ∈ excVerts2 D idx P, tc E ∉ edgeSet (cyc C) ∧ wind (cyc C) (tc E) ≠ 0

/-- The outermost property of a chain (output of R1). -/
def OutermostChain (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {m : ℕ} [NeZero m] (C : Fin m → Plane) : Prop :=
  ∀ v Y, GKite D idx v Y → v ∈ Set.range C ∨ (tc v ∉ edgeSet (cyc C) ∧ wind (cyc C) (tc v) ≠ 0)

/-- (R3, R4) The ring residue for the corner polygons of an outermost chain. -/
def RingResidue [NeZero M] (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (P : ConvPoly M) (α β γ : ℝ) : Prop :=
  ∀ (m : ℕ) [NeZero m] (C : Fin m → Plane), (∀ k : Fin m, GKite D idx (C k) (C (k + 1))) → Function.Injective C → OutermostChain D idx C →
    ∀ (m' : ℕ) [NeZero m'] (q : Fin m' → ℂ), Erdos634.Draft.LaczFormal.WN.IsCornerOf (cyc C) q → ∀ σ, OrientOK q σ → (∀ k, σ * extAng q k = γ) → ∀ h : m' = M,
      ∃ w : Fin M → Fin M, Erdos634.Draft.LaczFormal.WN.ChordsExt (fun j => tc (P.v j)) (fun j : Fin M => q (Fin.cast h.symm j)) w σ ∧
        (((∀ i, w (i + 1) = w i + 1) ∨ (∀ i, w (i + 1) = w i - 1)) →
          ∃ d L mm : ZMod M → ℝ, ∀ i, RG.RingQuadA α β γ (L i) (d i) (mm i) (d (i - 1)) ∨ RG.RingQuadB α β γ (L i) (d i) (mm i) (d (i - 1)))

def IIcSupply5 : Prop :=
  ∀ (N M : ℕ) [NeZero M] (T : PolyTiling N M) (idx : Fin N → Equiv.Perm (Fin 3)), CaseC T.C idx →
    angleAt T.C.model 2 < Real.pi / 2 → angleAt T.C.model 2 ≠ Real.pi / 3 → Comm (slen T.C 0) (slen T.C 1) → ¬ Comm (slen T.C 0) (slen T.C 2) →
    AngGen (fun l => T.C.model.angleAt l) →
    (∀ j : Fin M, cnt T.C idx (T.P.v j) 0 = 1 ∧ cnt T.C idx (T.P.v j) 1 = 1 ∧ cnt T.C idx (T.P.v j) 2 = 0) →
    kiteB T.C idx ≠ ∅ →
    ExcInsideAll T.C idx T.P ∧ RingResidue T.C idx T.P (T.C.model.angleAt 0) (T.C.model.angleAt 1) (T.C.model.angleAt 2)

theorem excVerts2_nonempty [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3)
    (hcor : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0) : (excVerts2 D idx P).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have := exc_census D P hreg idx hC h1 h3 hcor
  rw [h, Finset.sum_empty] at this
  exact NeZero.ne M this.symm

set_option maxHeartbeats 6400000 in
theorem iicNoKites_of_supply5 (H : IIcSupply5) : IIcNoKites := by
  intro N M _ T idx hC h1 h3 hab hac hAng hcor
  by_contra hne
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  obtain ⟨hExcAll, hRing⟩ := H N M T idx hC h1 h3 hab hac hAng hcor hne
  -- a kite edge
  obtain ⟨Y0, hY0⟩ := Finset.nonempty_iff_ne_empty.2 hne
  simp only [kiteB, Finset.mem_filter] at hY0
  obtain ⟨-, ⟨Z0, hYZ0⟩, -⟩ := hY0
  -- an exceptional point gives a common interior point
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
  exact Erdos634.Draft.LaczFormal.WN.kiteLayer4_false
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
      ring := fun m' _ q hq σ hO hturn h => hRing m C hCy hinj hOut m' q hq σ hO hturn h }

#print axioms iicNoKites_of_supply5

end Erdos634.Draft.LaczFormal.RG
