-- Draft/LaczFormalIIcWN80.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2: `IIcNoKites` from the supply `IIcInnerCycleSupply4`.
-- Everything except the corner residue is derived at tile level: the cycle is a closed injective chain of GKite edges (WN75 gives one through every kiteB vertex), its polygon is simple, with >= 3
-- vertices, turns in {gamma, 0, -gamma} (WN70), `gamma = 2 pi / M`, `3 <= M`, `alpha != beta`, the outer polygon `A i = toC (P.v i)` is strictly convex (WN78), and every vertex of the cycle is an INTERIOR vertex of
-- the tiling (`gkite_vertex_type`), hence strictly inside every edge half-plane of A (WN78 `convPoly_inside`).  Printed gap (straight vertices) repaired by `exists_corner` (WN73).
-- THE NAMED RESIDUE (`InnerCycleSupply4`): an OUTERMOST (the cycle C1 of the printed nesting C_{i+1} in C_i-interior) closed Gamma_kite chain `C` whose every corner polygon `q` (every orientation sign `sigma`) carries `CornerRing3`: (fam) a chord family for the concave
-- corners, (chords) the Gamma_except edges from the vertices of A to the corner polygon, exterior and pairwise disjoint, (fig8) the shapes of the ring quadrilaterals.
-- NOTE, UNAUDITED.  No witness of the supply by design (inconsistent hypothesis set of the printed proof).  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN79
import Erdos634.Draft.LaczFormalIIcWN76

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

/-- The corner residue for the outermost (C1 of the printed nesting C_{i+1} in C_i-interior) cycle `C` (as a complex polygon) against the outer polygon `A`. -/
def InnerCycleSupply4 (M : ℕ) [NeZero M] (α β γ : ℝ) (A : Fin M → ℂ) {m : ℕ} [NeZero m] (C : Fin m → ℂ) : Prop :=
  ∀ (m' : ℕ) [NeZero m'] (q : Fin m' → ℂ), Erdos634.Draft.LaczFormal.WN.IsCornerOf C q → ∀ σ, Erdos634.Draft.LaczFormal.WN.OrientOK q σ →
    Erdos634.Draft.LaczFormal.WN.CornerRing3 M α β γ A q σ

def IIcInnerCycleSupply4 : Prop :=
  ∀ (N M : ℕ) [NeZero M] (T : PolyTiling N M) (idx : Fin N → Equiv.Perm (Fin 3)), CaseC T.C idx →
    angleAt T.C.model 2 < Real.pi / 2 → angleAt T.C.model 2 ≠ Real.pi / 3 → Comm (slen T.C 0) (slen T.C 1) → ¬ Comm (slen T.C 0) (slen T.C 2) →
    AngGen (fun l => T.C.model.angleAt l) →
    (∀ j : Fin M, cnt T.C idx (T.P.v j) 0 = 1 ∧ cnt T.C idx (T.P.v j) 1 = 1 ∧ cnt T.C idx (T.P.v j) 2 = 0) →
    kiteB T.C idx ≠ ∅ →
    ∃ (m : ℕ) (_ : NeZero m) (C : Fin m → Plane), (∀ k : Fin m, GKite T.C idx (C k) (C (k + 1))) ∧ Function.Injective C ∧
      InnerCycleSupply4 M (T.C.model.angleAt 0) (T.C.model.angleAt 1) (T.C.model.angleAt 2)
        (fun j => Erdos634.Draft.LaczFormal.WN.toC (T.P.v j)) (fun k => Erdos634.Draft.LaczFormal.WN.toC (C k))

theorem iicNoKites_of_supply4 (H : IIcInnerCycleSupply4) : IIcNoKites := by
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
  have hint : ∀ k : Fin m, C k ∈ interior T.P.carrier := by
    intro k
    have hXY : GKite T.C idx (C (k - 1)) (C k) := by simpa using hCy (k - 1)
    have := (gkite_vertex_type T.C T.P T.region_eq idx hC.hidxA hC.hregc h1 h3 hXY).1.1
    rw [T.region_eq] at this
    exact this
  exact Erdos634.Draft.LaczFormal.WN.kiteLayer3_false
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
      A := fun j => Erdos634.Draft.LaczFormal.WN.toC (T.P.v j)
      hAinj := Erdos634.Draft.LaczFormal.WN.convPoly_inj T.P
      hAsc := Erdos634.Draft.LaczFormal.WN.convPoly_SC T.P
      hinside := fun j k => Erdos634.Draft.LaczFormal.WN.convPoly_inside T.P (hint k) j
      corner := hS }

#print axioms iicNoKites_of_supply4

end Erdos634.Draft.LaczFormal.RG
