-- Draft/LaczFormalL5.lean -- atom L5 (incommensurable half): Table 3 of Beeson-Rosu (arXiv 2607.23453),
-- = Beeson "Iso" Thm 3.1 (B-R Thm 7), assembled by Beeson from Laczkovich 1995 (Thms 4.1, 5.1, 5.3).
-- A congruent dissection of an ISOSCELES NON-EQUILATERAL triangle by a tile with an irrational angle:
-- the tile/target pair is one of lines 1-7 of Table 3.
--  line 1 similar;  line 2 gamma = pi/2, T = (beta,beta,2alpha);  line 3 gamma = 2alpha, T = (alpha,alpha,pi-2alpha);
--  line 4 gamma = 2pi/3, T = (alpha,alpha,pi-2alpha);  lines 5-7: 3alpha+2beta = pi,
--  T = (alpha,alpha,alpha+2beta), (beta,beta,3alpha), (alpha+beta,alpha+beta,alpha).
-- Proof: OUR `LemmaCFinal.lemmaC_general` (any N) + `LemmaPProof.lemmaP_general` (pi/3 tile, any N) +
-- `noniso` (the non-isosceles shapes F1-F4', (2a,b,a+b), (2a,a,2b) are never isosceles when alpha is
-- irrational).  The COMMENSURABLE half of Table 3 (lines 1-2 only) is NOT here: it needs Laczkovich 1995
-- Thm 5.3 (atom L9, blocked).  UNAUDITED beyond TABLE.md.
import Erdos634.Draft.LaczFormalBase
import Erdos634.Draft.LemmaPProof

open scoped Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
  Erdos634.Draft.LemmaCFinal

namespace Erdos634.Draft.LaczFormal

theorem table3_irr {N : ℕ} (D : CongruentDissection N)
    (hiso : ∃ i j : Fin 3, i ≠ j ∧ D.target.angleAt i = D.target.angleAt j)
    (hne : ¬ Equilateral D) (hirr : ∃ k, IrrPi (D.model.angleAt k)) :
    SimilarTM D ∨
    (∃ α β : ℝ, IrrPi α ∧ TileAngles D α β (Real.pi / 2) ∧ TgtAngles D β β (2 * α)) ∨
    (∃ α β : ℝ, IrrPi α ∧ TileAngles D α β (2 * α) ∧ TgtAngles D α α (Real.pi - 2 * α)) ∨
    (∃ α β : ℝ, IrrPi α ∧ TileAngles D α β (2 * Real.pi / 3) ∧
      TgtAngles D α α (Real.pi - 2 * α)) ∨
    (∃ α β : ℝ, IrrPi α ∧ 3 * α + 2 * β = Real.pi ∧ TileAngles D α β (2 * α + β) ∧
      TgtAngles D α α (α + 2 * β)) ∨
    (∃ α β : ℝ, IrrPi α ∧ 3 * α + 2 * β = Real.pi ∧ TileAngles D α β (2 * α + β) ∧
      TgtAngles D β β (3 * α)) ∨
    (∃ α β : ℝ, IrrPi α ∧ 3 * α + 2 * β = Real.pi ∧ TileAngles D α β (2 * α + β) ∧
      TgtAngles D (α + β) (α + β) α) := by
  by_cases hs : SimilarTM D
  · exact Or.inl hs
  right
  rcases lemmaC_general D hirr hs with h | h | h | h | h
  · -- right tile
    obtain ⟨α, -, -, hα0, ⟨p, q, hpq, hp, hq⟩, γ, hγ, i, j, hij, hi, hj⟩ := h
    have hα := irrPi_of_irrational hα0
    have hT : TileAngles D α (Real.pi / 2 - α) (Real.pi / 2) :=
      ((tile_of_two D p q hpq α (Real.pi / 2) hp hq).swap23).cast rfl (by ring) rfl
    rcases hγ with hg | hg
    · have hα' : IrrPi (Real.pi / 2 - α) :=
        irr_transfer α (Real.pi / 2 - α) (-1) (1 / 2) (by push_cast; ring) hα
      left
      exact ⟨Real.pi / 2 - α, α, hα', hT.swap,
        tgt_congr3 (tgt_of_two D i j hij α (hi.trans hg) (hj.trans hg)) (by ring)⟩
    · left
      exact ⟨α, Real.pi / 2 - α, hα, hT,
        tgt_congr3 (tgt_of_two D i j hij (Real.pi / 2 - α) (hi.trans hg) (hj.trans hg)) (by ring)⟩
  · obtain ⟨α, a, b, c, hα, ⟨σ, h0, -, h1, -, h2, -⟩, i, j, hij, hi, hj⟩ := h
    right; left
    exact ⟨α, Real.pi - 3 * α, hα, ⟨σ, h0, h1, h2⟩, tgt_of_two D i j hij α hi hj⟩
  · obtain ⟨α, a, b, c, hα, hd⟩ := h
    exact absurd (Erdos634.Draft.LemmaPProof.lemmaP_general D α a b c hα hd hs) hne
  · obtain ⟨α, a, b, c, hα, hd, hsh⟩ := h
    obtain ⟨σ, h0, -, h1, -, h2, -⟩ := hd
    have hT : TileAngles D α (Real.pi / 3 - α) (2 * Real.pi / 3) := ⟨σ, h0, h1, h2⟩
    rcases hsh with hE | hI | hF1 | hF2
    · exact absurd hE hne
    · rcases hI with h | h
      · right; right; left
        exact ⟨α, Real.pi / 3 - α, hα, hT, tgt_congr3 h (by ring)⟩
      · right; right; left
        have hβ : IrrPi (Real.pi / 3 - α) :=
          irr_transfer α (Real.pi / 3 - α) (-1) (1 / 3) (by push_cast; ring) hα
        exact ⟨Real.pi / 3 - α, α, hβ, hT.swap, tgt_congr3 h (by ring)⟩
    · exfalso
      rcases hF1 with h | h
      · exact noniso hiso hα h (1) (0) (0) (1/3) (-1) (2/3) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring) (by norm_num) (by norm_num) (by norm_num)
      · exact noniso hiso hα h (-1) (1/3) (0) (1/3) (1) (1/3) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring) (by norm_num) (by norm_num) (by norm_num)
    · exfalso
      rcases hF2 with h | h | h | h | h
      · exact noniso hiso hα h (2) (0) (-2) (2/3) (0) (1/3) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring) (by norm_num) (by norm_num) (by norm_num)
      · exact noniso hiso hα h (1) (0) (2) (0) (-3) (1) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring) (by norm_num) (by norm_num) (by norm_num)
      · exact noniso hiso hα h (-1) (1/3) (-2) (2/3) (3) (0) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring) (by norm_num) (by norm_num) (by norm_num)
      · exact noniso hiso hα h (1) (0) (-2) (2/3) (1) (1/3) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring) (by norm_num) (by norm_num) (by norm_num)
      · exact noniso hiso hα h (-1) (1/3) (2) (0) (-1) (2/3) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring) (by norm_num) (by norm_num) (by norm_num)
  · obtain ⟨α, β, a, b, c, hα, hrel, hd, hsh⟩ := h
    obtain ⟨σ, h0, -, h1, -, h2, -⟩ := hd
    have hT : TileAngles D α β (2 * α + β) := ⟨σ, h0, h1, h2⟩
    rcases hsh with h | h | h | h | h
    · right; right; right; right; left
      exact ⟨α, β, hα, hrel, hT, h⟩
    · right; right; right; right; right
      exact ⟨α, β, hα, hrel, hT, h⟩
    · exfalso
      have hb : β = (-3 / 2 : ℚ) * α + (1 / 2 : ℚ) * Real.pi := by push_cast; linarith
      subst hb
      exact noniso hiso hα h 2 0 (-3 / 2) (1 / 2) (-1 / 2) (1 / 2) (by push_cast; ring)
        (by push_cast; ring) (by push_cast; ring) (by norm_num) (by norm_num) (by norm_num)
    · exfalso
      have hb : β = (-3 / 2 : ℚ) * α + (1 / 2 : ℚ) * Real.pi := by push_cast; linarith
      subst hb
      exact noniso hiso hα h 2 0 1 0 (-3) 1 (by push_cast; ring)
        (by push_cast; ring) (by push_cast; ring) (by norm_num) (by norm_num) (by norm_num)
    · right; right; right; left
      exact ⟨α, β, hα, hrel, hT, h⟩

/-- Non-vacuity: the three hypotheses of `table3_irr` hold jointly on the certified 44-tiling
(`TheoremPConditional.D44`: isosceles target `(β,β,3α)`, `cos α = 7/8`, `α ∉ ℚπ`), so the theorem is
not about an empty class; its conclusion there is line 6 of Table 3. -/
theorem table3_irr_witness :
    ∃ (N : ℕ) (D : CongruentDissection N),
      (∃ i j : Fin 3, i ≠ j ∧ D.target.angleAt i = D.target.angleAt j) ∧ ¬ Equilateral D ∧
      ∃ k, IrrPi (D.model.angleAt k) := by
  have t0 : D44.target.angleAt 0 =
      Erdos634.Draft.FluxGridWitness.β44 := Erdos634.Draft.FluxGridWitness.t_angle0
  have t1 : D44.target.angleAt 1 =
      Erdos634.Draft.FluxGridWitness.β44 := Erdos634.Draft.FluxGridWitness.t_angle1
  refine ⟨_, D44, ⟨0, 1, by decide, t0.trans t1.symm⟩, ?_,
    lemmaC_conclusion_real_44.2⟩
  intro hE
  have h0 := hE 0
  rw [t0] at h0
  have hrel := Erdos634.Draft.FluxGridWitness.three_α_two_β
  exact Erdos634.Draft.FluxGridWitness.α44_irr ⟨1 / 9, by push_cast; linarith⟩

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.table3_irr
#print axioms Erdos634.Draft.LaczFormal.table3_irr_witness
