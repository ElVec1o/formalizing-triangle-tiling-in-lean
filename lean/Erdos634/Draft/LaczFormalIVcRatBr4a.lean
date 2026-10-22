-- Draft/LaczFormalIVcRatBr4a.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch): BRIDGE stage Br4a (B-c bookkeeping, part 1).
--   The partner function `pOf` (an involution without fixed points, from `Pr_exists` and `Pr.unique`), the piece sets `pieceSet i = tile i u tile (pOf i)`, their interiors are pairwise disjoint
--   (`pieces_disj`, via `interior_union_disj`), the kite and rhombus index types (`KIdx`: i < pOf i and the pair is a kite; `RIdx`: i < pOf i and it is a parallelogram) and the chosen pieces.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatBr3d

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M] {D : CongruentRegionDissection N} {P : ConvPoly M} {idx : Fin N → Equiv.Perm (Fin 3)} {s : ℝ} {ρ π : Fin 3}
variable [HasFansC D.toRegionDissection] (h : BrHyp D P idx s ρ π)

include h in
theorem exists_partner (i : Fin N) : ∃ j, j ≠ i ∧ Pr D i j := Pr_exists h i

/-- The chosen partner tile. -/
noncomputable def pOf (i : Fin N) : Fin N := Classical.choose (Pr_exists h i)
theorem pOf_ne (i : Fin N) : pOf h i ≠ i := (Classical.choose_spec (Pr_exists h i)).1
theorem Pr_pOf (i : Fin N) : Pr D i (pOf h i) := (Classical.choose_spec (Pr_exists h i)).2
theorem pOf_pOf (i : Fin N) : pOf h (pOf h i) = i :=
  (Pr.unique D idx h.hC.hidx h.h0 h.h1 (Pr_pOf h i).symm (Pr_pOf h (pOf h i))).symm
theorem pOf_eq_of_Pr {i j : Fin N} (hij : Pr D i j) : j = pOf h i :=
  Pr.unique D idx h.hC.hidx h.h0 h.h1 hij (Pr_pOf h i)

/-- The pair `(i, pOf i)` is a kite. -/
def IsK (i : Fin N) : Prop := KitePair D idx s ρ π i (pOf h i)

theorem pair_shape (i : Fin N) : IsK h i ∨ ParPair D idx s i (pOf h i) := by
  obtain ⟨d, U, V, hS, hc, hS'⟩ := Pr_pOf h i
  exact pair_tile_shape D idx h.hC.hidx h.hs h.hρπ h.hρ h.hπ h.hlρ h.hlπ h.hl2 hS hS' hc

/-- The union of the two tiles of the pair of `i`. -/
def pieceSet (i : Fin N) : Set Plane := (D.tile i).carrier ∪ (D.tile (pOf h i)).carrier

theorem pieces_disj {i i' : Fin N} (hi : i < pOf h i) (hi' : i' < pOf h i') (hne : i ≠ i') :
    Disjoint (interior (pieceSet h i)) (interior (pieceSet h i')) := by
  have e1 : i ≠ pOf h i' := by
    intro e
    have e' : pOf h i = i' := by rw [e, pOf_pOf]
    rw [e'] at hi; rw [← e] at hi'; exact lt_asymm hi hi'
  have e2 : pOf h i ≠ i' := by
    intro e
    have e' : pOf h i' = i := by rw [← e, pOf_pOf]
    rw [e] at hi; rw [e'] at hi'; exact lt_asymm hi hi'
  have e3 : pOf h i ≠ pOf h i' := by
    intro e
    apply hne
    rw [← pOf_pOf h i, e, pOf_pOf]
  have d1 : Disjoint (interior (D.tile i).carrier) (interior (pieceSet h i')) :=
    (interior_union_disj (tri_closure_interior _) (tri_closure_interior _) (D.interiors_disjoint hne.symm) (D.interiors_disjoint e1.symm)).symm
  have d2 : Disjoint (interior (D.tile (pOf h i)).carrier) (interior (pieceSet h i')) :=
    (interior_union_disj (tri_closure_interior _) (tri_closure_interior _) (D.interiors_disjoint e2.symm) (D.interiors_disjoint e3.symm)).symm
  exact interior_union_disj (tri_closure_interior _) (tri_closure_interior _) d1 d2

/-- Index of the kite pieces: one representative `i < pOf i` per kite pair. -/
def KIdx : Type := {i : Fin N // IsK h i ∧ i < pOf h i}
/-- Index of the parallelogram pairs (each gives two rhombi). -/
def RIdx : Type := {i : Fin N // ¬ IsK h i ∧ i < pOf h i}

noncomputable def kd (k : KIdx h) : KiteData s := Classical.choose k.2.1
theorem kd_spec (k : KIdx h) :
    (∃ a, (D.tile k.1).pts a = (kd h k).V ∧ idx k.1 a = π) ∧ (∃ a, (D.tile (pOf h k.1)).pts a = (kd h k).V ∧ idx (pOf h k.1) a = π) ∧
    (∃ a, (D.tile k.1).pts a = (kd h k).W ∧ idx k.1 a = ρ) ∧ (∃ a, (D.tile (pOf h k.1)).pts a = (kd h k).W ∧ idx (pOf h k.1) a = ρ) ∧
    (kd h k).set = pieceSet h k.1 ∧ True := by
  obtain ⟨a, b, c, d, e, -⟩ := Classical.choose_spec k.2.1
  exact ⟨a, b, c, d, e, trivial⟩

theorem parPair_of (r : RIdx h) : ParPair D idx s r.1 (pOf h r.1) := (pair_shape h r.1).resolve_left r.2.1

noncomputable def rd1 (r : RIdx h) : RhombData s := Classical.choose (parPair_of h r).1
noncomputable def rd2 (r : RIdx h) : RhombData s := Classical.choose (Classical.choose_spec (parPair_of h r).1)
theorem rd_spec (r : RIdx h) : Disjoint (interior (rd1 h r).set) (interior (rd2 h r).set) ∧ (rd1 h r).set ∪ (rd2 h r).set = pieceSet h r.1 :=
  Classical.choose_spec (Classical.choose_spec (parPair_of h r).1)

/-- The rhombus pieces: two per parallelogram pair. -/
noncomputable def rdd (r : RIdx h × Fin 2) : RhombData s := if r.2 = 0 then rd1 h r.1 else rd2 h r.1

theorem rdd_sub (r : RIdx h × Fin 2) : (rdd h r).set ⊆ pieceSet h r.1.1 := by
  unfold rdd
  split_ifs
  · exact (Set.subset_union_left).trans (rd_spec h r.1).2.subset
  · exact (Set.subset_union_right).trans (rd_spec h r.1).2.subset

#print axioms Erdos634.Draft.LaczFormal.RG.pieces_disj
#print axioms Erdos634.Draft.LaczFormal.RG.kd_spec
#print axioms Erdos634.Draft.LaczFormal.RG.rdd_sub

end Erdos634.Draft.LaczFormal.RG
