import Erdos634.Draft.BeesonIso3i
import Erdos634.Draft.BeesonIsoL11Geo
import Erdos634.Draft.LaczFormalBZL7h17

/-!
# Beeson, "Tilings of an isosceles triangle" (arXiv 1206.1974 v7), Lemma 11.8 (isosceles triangle, tile `(alpha, beta, 2 alpha)`)

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.1974 v7, Lemma 11.8, Thm 10.7; arXiv 1206.2229), Laczkovich (DCG 48 (2012), Sect. 4), Beeson-Zhang, Herdt, Zhang.
Formalization debt, not progress on the /goal outcomes.

`beeson_l11_8`: isosceles `ABC` with base angles `alpha` (target corners `0`, `1`; apex `B` = corner `2`) `N`-tiled (`CongruentDissection`) by a tile with angles `(alpha, beta, 2 alpha)`,
`alpha` not a rational multiple of `pi` (H1).  Then no tile has a vertex in the relative interior of `AB` and a vertex in the relative interior of `BC`.
PRINTED GAPS: see `chord_no_tile` (the literal statement fails at `B`; "E on AC" is a typo; the angle step and the case `l = b` are repaired).
Witness status: every hypothesis except the existence of a tile with the two vertices holds for the certified 1125-tiling (`witness_1125_thm107` of BZL7h17: angles, H1, a
corner of each kind, rationality), so the lemma applies to it and says that the 1125-tiling has no tile with a vertex in the relative interior of each of `AB`, `BC`
(non-existence conclusion; the hypotheses are NOT vacuous).
-/

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem chord_no_tile_open (C : CongruentRegionDissection N) [HasFansC C.toRegionDissection] (P : ConvPoly M) (hreg : C.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((C.tile i).pts k) ((C.tile i).pts k') = dist (C.model.pts (idx i k)) (C.model.pts (idx i k')))
    (hidxA : ∀ i v, C.model.angleAt (idx i v) = (C.tile i).angleAt v)
    (hβ : C.model.angleAt 1 = Real.pi - 3 * C.model.angleAt 0) (hγ : C.model.angleAt 2 = 2 * C.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, C.model.angleAt 0 = (r : ℝ) * Real.pi)
    (i : Fin M) {E F : Plane} (hE : E ∈ openSegment ℝ (P.v i) (P.v (i + 1))) (hF : F ∈ openSegment ℝ (P.v (i + 1)) (P.v (i + 1 + 1)))
    (hB : P.angle (i + 1) = Real.pi - 2 * C.model.angleAt 0)
    {i0 : Fin N} {kE kF : Fin 3} (hkE : (C.tile i0).pts kE = E) (hkF : (C.tile i0).pts kF = F)
    (hrat : ∃ r s : ℚ, slen C 0 = (r : ℝ) * slen C 1 ∧ slen C 2 = (s : ℝ) * slen C 0)
    (hrel : slen C 2 ^ 2 = slen C 0 ^ 2 + slen C 0 * slen C 1) (htri : slen C 1 < slen C 0 + slen C 2) : False := by
  obtain ⟨a, b, ha, hb, hab, hEe⟩ := hE
  obtain ⟨a', b', ha', hb', hab', hFe⟩ := hF
  have hE' : E = (1 - b) • P.v i + b • P.v (i + 1) := by rw [← hEe]; congr 2; linarith
  have hF' : F = (1 - b') • P.v (i + 1) + b' • P.v (i + 1 + 1) := by rw [← hFe]; congr 2; linarith
  exact chord_no_tile C P hreg idx hidx hidxA hβ hγ hα i hb (by linarith) hb' (by linarith) hE' hF' hB hkE hkF hrat hrel htri

theorem fin3_add_two_one : ∀ j : Fin 3, j + 2 + 1 = j := by decide

theorem fin3_cases3 : ∀ u w j : Fin 3, u ≠ j → w ≠ j → u ≠ w → (u = j + 1 ∧ w = j + 2) ∨ (u = j + 2 ∧ w = j + 1) := by decide

theorem beeson_l11_8 (D : CongruentDissection N) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoAlphaData α a b c) (hA : D.target.angleAt 0 = α) (hB : D.target.angleAt 1 = α)
    {i0 : Fin N} {kE kF : Fin 3} {E F : Plane} (hkE : (D.tile i0).pts kE = E) (hkF : (D.tile i0).pts kF = F)
    (hE : E ∈ openSegment ℝ (D.target.pts 0) (D.target.pts 2)) (hF : F ∈ openSegment ℝ (D.target.pts 1) (D.target.pts 2)) : False := by
  have hrel0 := (Erdos634.Draft.BeesonIsoL11Geo.l11_1_4 D hα h hA hB).1
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  set C := relabel D.toRegion σ with hC
  have hAC : C.model.angleAt 0 = α := (relabel_angleAt D.toRegion σ 0).trans h0
  have hβ : C.model.angleAt 1 = Real.pi - 3 * C.model.angleAt 0 := by
    rw [hAC]; exact (relabel_angleAt D.toRegion σ 1).trans h1
  have hγ : C.model.angleAt 2 = 2 * C.model.angleAt 0 := by
    rw [hAC]; exact (relabel_angleAt D.toRegion σ 2).trans h2
  have hirr : ¬ ∃ r : ℚ, C.model.angleAt 0 = (r : ℝ) * Real.pi := by rw [hAC]; exact hα
  obtain ⟨P, hPc, τ, hPa, hPv⟩ := exists_convpoly_of_tri' D.target
  have hreg : C.region = P.carrier := hPc.symm
  haveI : HasFansC C.toRegionDissection := hasFansC_poly _ P hreg
  obtain ⟨idx, hidx, hidxA⟩ := exists_idx_both C
  have hsum := Erdos634.Draft.LaczFormal.angleAt_sum D.target
  have t2 : D.target.angleAt 2 = Real.pi - 2 * α := by linarith
  have hang : ∀ j : Fin 3, D.target.angleAt j = α ∨ D.target.angleAt j = Real.pi - 2 * α := by
    intro j; fin_cases j
    · exact Or.inl hA
    · exact Or.inl hB
    · exact Or.inr t2
  obtain ⟨k0, hk0⟩ := τ.surjective 2
  obtain ⟨kA, hkA⟩ := τ.surjective 0
  obtain ⟨r, s, hr, hs⟩ := beeson_thm107_proved C P hreg hβ hγ hirr
    (fun k => by rw [hPa, hAC]; exact hang _) (k0 - 1) (by simp only [sub_add_cancel]; rw [hPa, hk0, hAC]; exact t2)
    (kA - 1) (by simp only [sub_add_cancel]; rw [hPa, hkA, hAC]; exact hA)
  have ea : slen C 0 = a := (relabel_slen D.toRegion σ 0).trans o0
  have eb : slen C 1 = b := (relabel_slen D.toRegion σ 1).trans o1
  have ec : slen C 2 = c := (relabel_slen D.toRegion σ 2).trans o2
  have hrel : slen C 2 ^ 2 = slen C 0 ^ 2 + slen C 0 * slen C 1 := by rw [ea, eb, ec]; exact hrel0
  have htri : slen C 1 < slen C 0 + slen C 2 := by
    have := Tri.oppLen_lt_sum C.model 1
    have e0 : C.model.oppLen 0 = slen C 0 := rfl
    have e1 : C.model.oppLen 1 = slen C 1 := rfl
    have e2 : C.model.oppLen 2 = slen C 2 := rfl
    simp only [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl] at this
    rw [e0, e1, e2] at this
    linarith
  -- the position of B in the polygon
  set j : Fin 3 := τ.symm 2 with hj
  have hPj : P.v j = D.target.pts 2 := by rw [hPv, hj]; simp
  have hAj : P.angle j = Real.pi - 2 * α := by rw [hPa, hj]; simp; exact t2
  have hu : τ.symm 0 ≠ j := fun e => by have := τ.symm.injective e; simp at this
  have hw : τ.symm 1 ≠ j := fun e => by have := τ.symm.injective e; simp at this
  have huw : τ.symm 0 ≠ τ.symm 1 := fun e => by have := τ.symm.injective e; simp at this
  have hP0 : P.v (τ.symm 0) = D.target.pts 0 := by rw [hPv]; simp
  have hP1 : P.v (τ.symm 1) = D.target.pts 1 := by rw [hPv]; simp
  have hrat : ∃ r s : ℚ, slen C 0 = (r : ℝ) * slen C 1 ∧ slen C 2 = (s : ℝ) * slen C 0 := ⟨r, s, hr, hs⟩
  have hBang : ∀ i : Fin 3, i + 1 = j → P.angle (i + 1) = Real.pi - 2 * C.model.angleAt 0 := by
    intro i hi; rw [hi, hAC]; exact hAj
  rcases fin3_cases3 _ _ j hu hw huw with ⟨e0, e1⟩ | ⟨e0, e1⟩
  · -- pts 0 = v (j+1), pts 1 = v (j+2): the chord is E' = F on side j+2, F' = E on side j
    have s1 : j + 2 + 1 = j := fin3_add_two_one j
    have hF2 : F ∈ openSegment ℝ (P.v (j + 2)) (P.v (j + 2 + 1)) := by
      rw [s1, hPj, ← e1, hP1]; exact hF
    have hE2 : E ∈ openSegment ℝ (P.v (j + 2 + 1)) (P.v (j + 2 + 1 + 1)) := by
      rw [s1, ← e0, hP0, hPj]; rw [openSegment_symm]; exact hE
    exact chord_no_tile_open C P hreg idx hidx hidxA hβ hγ hirr (j + 2) hF2 hE2 (hBang _ s1) hkF hkE hrat hrel htri
  · have s1 : j + 2 + 1 = j := fin3_add_two_one j
    have hE2 : E ∈ openSegment ℝ (P.v (j + 2)) (P.v (j + 2 + 1)) := by
      rw [s1, hPj, ← e0, hP0]; exact hE
    have hF2 : F ∈ openSegment ℝ (P.v (j + 2 + 1)) (P.v (j + 2 + 1 + 1)) := by
      rw [s1, ← e1, hP1, hPj]; rw [openSegment_symm]; exact hF
    exact chord_no_tile_open C P hreg idx hidx hidxA hβ hγ hirr (j + 2) hE2 hF2 (hBang _ s1) hkE hkF hrat hrel htri

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.chord_no_tile_open
#print axioms Erdos634.Draft.LaczFormal.RG.beeson_l11_8
