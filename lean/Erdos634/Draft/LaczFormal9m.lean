import Erdos634.Draft.LaczFormal9e
import Erdos634.Draft.LaczFormal9l
import Erdos634.Draft.LaczFormalIIcIsoWitM

/-!
# Laczkovich DCG 48 (2012) Theorem 2.4 with genuine central symmetry

NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012) Thm 2.1, Thm 2.4), Beeson, Beeson-Zhang.  Formalization debt, not /goal progress.

`thm24_2012_csym`: as `thm24_2012` (LaczFormal9e) but the third alternative is "`A` is rational and centrally symmetric" in the literal
sense `CentSym` (`exists c, forall x in A, 2c - x in A`), using `csym_of_equiangular` (LaczFormal9l) on the outputs (v), (vi) of Thm 2.1.
`csym_octagon` is the real witness of `csym_of_equiangular`: the regular octagon `IsoWit.oct` is centrally symmetric.
-/

open scoped Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.RegionDissection Erdos634.Draft.TheoremPConditional
  Erdos634.Draft.LaczFormal Erdos634.Draft.LaczFormal.Thm21 Erdos634.Draft.LaczFormal.RG

namespace Erdos634.Laczkovich9

theorem thm24_of_sigma_csym {N M : ℕ} [NeZero M] (T : PolyTiling N M) (σ : Equiv.Perm (Fin 3))
    (h : ∃ idx : Fin N → Equiv.Perm (Fin 3), (∀ i v, angleAt T.C.model (idx i v) = angleAt (T.C.tile i) v) ∧
      ∀ X, cntR T.C idx X (σ 0) = cntR T.C idx X (σ 1)) :
    M ≤ 6 ∨ ((∀ i, T.P.side i = T.P.side 0) ∧ ∀ i, T.P.angle i = T.P.angle 0) ∨ (RationalPoly T.P ∧ CentSym T.P) ∨
      (Comm (sideOpp T.C.model 0) (sideOpp T.C.model 1) ∧ Comm (sideOpp T.C.model 1) (sideOpp T.C.model 2) ∧
        Comm (sideOpp T.C.model 0) (sideOpp T.C.model 2)) := by
  have hreg := regular_relabel T.C σ h
  let T' : PolyTiling N M := ⟨relabel T.C σ, T.P, T.region_eq⟩
  have hc : Thm21Concl T'.C T'.P := theorem21_unconditional N M T' hreg
  have hsc : SinComm (relabel T.C σ) → _ := sides_of_sinComm T.C σ
  rcases hc with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact Or.inl (by rcases h1 with ⟨⟨h4, -⟩, -⟩; omega)
  · exact Or.inr (Or.inr (Or.inr (hsc h2.2.2)))
  · exact Or.inr (Or.inr (Or.inr (hsc h3.2.2)))
  · exact Or.inl (by have := h4.1; omega)
  · right; right; left
    obtain ⟨k, hM, -, hrat, hang, hside, -⟩ := h5
    exact ⟨hrat, csym_of_equiangular T.P k hM (fun i => by rw [hang i, hang 0]) hside⟩
  · right; right; left
    obtain ⟨hM, hrat, hside, hang, -⟩ := h6
    exact ⟨hrat, csym_of_equiangular T.P 3 (by omega) (fun i => by rw [hang i, hang 0]) (fun i => hside i)⟩
  · right; left
    exact ⟨h7.1, h7.2.1⟩
  · exact Or.inl h8.2.1
  · exact Or.inl (by have := h9.1; omega)

/-- **Laczkovich DCG 48 (2012), Theorem 2.4** (central symmetry in the literal sense `CentSym`). -/
theorem thm24_2012_csym {N M : ℕ} [NeZero M] (T : PolyTiling N M)
    (h : ∃ idx : Fin N → Equiv.Perm (Fin 3), (∀ i v, angleAt T.C.model (idx i v) = angleAt (T.C.tile i) v) ∧
      ((∀ X, cntR T.C idx X 0 = cntR T.C idx X 1) ∨ (∀ X, cntR T.C idx X 0 = cntR T.C idx X 2) ∨
        (∀ X, cntR T.C idx X 1 = cntR T.C idx X 2))) :
    M ≤ 6 ∨ ((∀ i, T.P.side i = T.P.side 0) ∧ ∀ i, T.P.angle i = T.P.angle 0) ∨ (RationalPoly T.P ∧ CentSym T.P) ∨
      (Comm (sideOpp T.C.model 0) (sideOpp T.C.model 1) ∧ Comm (sideOpp T.C.model 1) (sideOpp T.C.model 2) ∧
        Comm (sideOpp T.C.model 0) (sideOpp T.C.model 2)) := by
  obtain ⟨idx, hA, h01 | h02 | h12⟩ := h
  · exact thm24_of_sigma_csym T 1 ⟨idx, hA, fun X => h01 X⟩
  · exact thm24_of_sigma_csym T (Equiv.swap 1 2) ⟨idx, hA, fun X => by simpa using h02 X⟩
  · exact thm24_of_sigma_csym T (Equiv.swap 0 2) ⟨idx, hA, fun X => by simpa using (h12 X).symm⟩

/-- Witness: the regular octagon is centrally symmetric (hypotheses of `csym_of_equiangular` on a real polygon). -/
theorem csym_octagon : CentSym Erdos634.Draft.LaczFormal.IsoWit.oct := by
  have hc7 := Erdos634.Draft.LaczFormal.IsoWit.lemma63_one_iso_octagon
  exact csym_of_equiangular _ 4 (by norm_num) hc7.2.1 (fun i => by rw [hc7.1 i, hc7.1 (i + Fin.ofNat 8 4)])

end Erdos634.Laczkovich9

#print axioms Erdos634.Laczkovich9.thm24_2012_csym
#print axioms Erdos634.Laczkovich9.csym_octagon
