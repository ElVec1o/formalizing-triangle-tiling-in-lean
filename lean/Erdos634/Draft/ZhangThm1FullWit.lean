import Erdos634.Draft.ZhangThm1Full
import Erdos634.Draft.LaczFormalBZL7d7

/-! Witness for `ZhangThm1Full.zhang_thm1`: the certified N = 1215 dissection (equilateral target of side 135, tile `1890 (3,5,7)`, `2pi/3` tile) satisfies
every hypothesis (irrational angle, not similar, no right angle).  NOTE, UNAUDITED.  Credit Zhang, Beeson-Zhang, Laczkovich. -/

open scoped Classical
open Erdos634.Geometry Erdos634.Draft.LaczFormal.Thm21 Erdos634.Draft.LaczFormal.RG Erdos634.Draft.LaczFormal.BZL7Wit Erdos634.Draft.G3CAng Erdos634.Draft.TheoremPConditional

namespace Erdos634.Draft.ZhangThm1Full

theorem zhang_thm1_wit : ∃ (N : ℕ) (D : CongruentDissection N), (∃ k, IrrPi (D.model.angleAt k)) ∧ ¬ SimilarTM D ∧
    (∀ k, D.model.angleAt k ≠ Real.pi / 2) ∧
    Comm (D.model.oppLen 0) (D.model.oppLen 1) ∧ Comm (D.model.oppLen 0) (D.model.oppLen 2) := by
  open Erdos634.Draft.G3CEqui135Control in
  have hpi := Real.pi_pos
  open Erdos634.Draft.G3CEqui135Control in
  obtain ⟨hr0, hr1⟩ := data.alpha_range
  open Erdos634.Draft.G3CEqui135Control in
  have hNS : NotSim D := notSim_of_no_match D data 0 (by rw [t_angle]; intro e; exact α_irr ⟨1 / 3, by push_cast; linarith⟩)
    (by rw [t_angle]; intro e; linarith) (by rw [t_angle]; intro e; linarith)
  open Erdos634.Draft.G3CEqui135Control in
  have hns : ¬ SimilarTM D := by rintro ⟨μ, τ, h⟩; exact hNS ⟨τ, fun j => (h j).1⟩
  open Erdos634.Draft.G3CEqui135Control in
  have hirr : ∃ k, IrrPi (D.model.angleAt k) := by
    obtain ⟨σ, e0, -⟩ := data
    exact ⟨σ 0, by rw [e0]; exact α_irr⟩
  open Erdos634.Draft.G3CEqui135Control in
  have hnr : ∀ k, D.model.angleAt k ≠ Real.pi / 2 := by
    obtain ⟨σ, e0, -, e1, -, e2, -⟩ := data
    intro k
    obtain ⟨j, rfl⟩ := σ.surjective k
    fin_cases j
    · show D.model.angleAt (σ 0) ≠ _
      rw [e0]; intro e; exact α_irr ⟨1 / 2, by push_cast; linarith⟩
    · show D.model.angleAt (σ 1) ≠ _
      rw [e1]; intro e; exact α_irr ⟨-1 / 6, by push_cast; linarith⟩
    · show D.model.angleAt (σ 2) ≠ _
      rw [e2]; intro e; linarith
  open Erdos634.Draft.G3CEqui135Control in
  exact ⟨_, D, hirr, hns, hnr, zhang_thm1 D hirr hns hnr⟩

end Erdos634.Draft.ZhangThm1Full
#print axioms Erdos634.Draft.ZhangThm1Full.zhang_thm1_wit
