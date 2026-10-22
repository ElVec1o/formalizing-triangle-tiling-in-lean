import Erdos634.Draft.LaczFormal9e
import Erdos634.Draft.LaczFormal9d
import Erdos634.Draft.LaczFormalThm21AssemblyWit
import Erdos634.Draft.LaczFormalIIcIsoWitM
import Erdos634.Draft.LaczFormal9g
import Erdos634.Draft.LaczFormal9h

/-!
# Witnesses for the 2026-10-22 additions (Laczkovich DM 140 Thm 3.3, 3.4, 5.4; DCG 48 Thm 2.4)

NOTE, UNAUDITED.  Credit: Laczkovich, Beeson, Beeson-Zhang.  Each hypothesis block of `dm140_thm33`, `dm140_thm34`,
`thm54_congruent`, `thm24_2012` is exhibited on a real object and the theorem is applied to it.
-/

open scoped Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional Erdos634.Draft.LaczFormal Erdos634.Draft.LaczFormal.Thm21
  Erdos634.Draft.LaczFormal.RG

namespace Erdos634.Laczkovich9

/-- Thm 5.4 (congruent form) applied to the real equilateral dissection `D_i` (the 4-tile ladder). -/
theorem thm54_witness : ∃ k : Fin 3, D_i.model.angleAt k = Real.pi / 3 ∨ D_i.model.angleAt k = 2 * Real.pi / 3 :=
  thm54_congruent D_i D_i_equilateral

/-- Thm 3.3 at `(x, y) = (1, 1)` (tile `(3, 3, 3)`; `n = 9 k^2`). -/
theorem thm33_witness_11 : ∃ (k N : ℕ), 0 < k ∧ N = (1 * 1 * (1 + 2 * 1) * (1 + 2 * 1) : ℤ).natAbs * k ^ 2 ∧
    ∃ D : CongruentDissection N, Equilateral D := by
  obtain ⟨k, N, hk, hN, D, hE, -⟩ := dm140_thm33 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨k, N, hk, hN, D, hE⟩

/-- Thm 3.3 at `(x, y) = (-1, 4)` (the printed example: tile `(7, 8, 13)`, `gamma = 2 pi / 3`). -/
theorem thm33_witness_m14 : ∃ (k N : ℕ), 0 < k ∧ N = ((-1) * 4 * ((-1) + 2 * 4) * (4 + 2 * (-1)) : ℤ).natAbs * k ^ 2 ∧
    ∃ D : CongruentDissection N, Equilateral D := by
  obtain ⟨k, N, hk, hN, D, hE, -⟩ := dm140_thm33 (-1) 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨k, N, hk, hN, D, hE⟩

/-- Thm 3.4 for `P = {2, 3}`. -/
theorem thm34_witness : ∃ (N : ℕ) (D : CongruentDissection N), Equilateral D ∧
    Odd (padicValNat 2 N) ∧ Odd (padicValNat 3 N) := by
  obtain ⟨N, D, hE, h⟩ := dm140_thm34 {2, 3} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> norm_num)
  exact ⟨N, D, hE, h 2 (by simp), h 3 (by simp)⟩

/-- Thm 2.4 on the real regular tiling `rTilingSqrt3` (30-60-90 rectangle, `PolyTiling 2 4`): the hypothesis block holds and the
theorem applies (the disjunction it returns holds with `M = 4 <= 6`). -/
theorem thm24_witness : (4 : ℕ) ≤ 6 := by
  have _h := thm24_2012 rTilingSqrt3 (by
    obtain ⟨idx, hA, hc⟩ := rDiss_regular (p := 1) (q := Real.sqrt 3) one_pos (Real.sqrt_pos.mpr (by norm_num))
    exact ⟨idx, hA, Or.inl hc⟩)
  norm_num

/-- Thm 3.4 (ii) on the real regular octagon `octTiling` (`PolyTiling 8 8`, regular tiling by 8 isosceles triangles from the centre):
all hypotheses hold (`M = 8` is not 3, 4, 6; sides and angles equal by `Concl7`; `RegularPQ`), and the angles are
`(pi/2 - pi/8, pi/2 - pi/8, 2 pi / 8)` in some order. -/
theorem thm34ii_witness : ∃ σ : Equiv.Perm (Fin 3),
    angleAt Erdos634.Draft.LaczFormal.IsoWit.octTiling.C.model (σ 0) = Real.pi / 2 - Real.pi / (8 : ℕ) ∧
    angleAt Erdos634.Draft.LaczFormal.IsoWit.octTiling.C.model (σ 1) = Real.pi / 2 - Real.pi / (8 : ℕ) ∧
    angleAt Erdos634.Draft.LaczFormal.IsoWit.octTiling.C.model (σ 2) = 2 * Real.pi / (8 : ℕ) := by
  have hc7 := Erdos634.Draft.LaczFormal.IsoWit.lemma63_one_iso_octagon
  exact thm34ii_2012 Erdos634.Draft.LaczFormal.IsoWit.octTiling ⟨by norm_num, by norm_num, by norm_num⟩ hc7.1 hc7.2.1
    (by
      obtain ⟨idx, hA, hc⟩ := Erdos634.Draft.LaczFormal.IsoWit.octTiling_regular
      exact ⟨idx, hA, Or.inl hc⟩)

end Erdos634.Laczkovich9

#print axioms Erdos634.Laczkovich9.thm54_witness
#print axioms Erdos634.Laczkovich9.thm33_witness_11
#print axioms Erdos634.Laczkovich9.thm33_witness_m14
#print axioms Erdos634.Laczkovich9.thm34_witness
#print axioms Erdos634.Laczkovich9.thm24_witness
#print axioms Erdos634.Laczkovich9.thm34ii_witness
