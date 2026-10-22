-- Draft/LemmaCSimilar.lean — `cfig = (1,1,1)` forces `SimilarTM` (the `c ≠ (1,1,1)` input of
-- LemmaCAssemble.lemmaC_geometric).  Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.Draft.LemmaCAssemble
import Erdos634.Draft.FluxCRow12
import Erdos634.Draft.FluxGRow3RP
import Erdos634.Draft.A1FieldClause
import Erdos634.Draft.TheoremPConditional

open scoped Classical
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.LemmaCAssemble

namespace Erdos634.Draft.LemmaCSimilar

/-- AAA ⇒ proportional sides (law of sines). -/
theorem sides_of_angles (T M : Tri) (τ : Equiv.Perm (Fin 3))
    (h : ∀ k, T.angleAt k = M.angleAt (τ k)) :
    ∃ μ : ℝ, ∀ k, T.oppLen k = μ * M.oppLen (τ k) := by
  have hs : 0 < Real.sin (T.angleAt 0) := Erdos634.Geometry.A1Field.sin_angle_pos T 0
  have hm : 0 < M.oppLen (τ 0) := Erdos634.Geometry.Row3.RP.oppLen_pos M _
  refine ⟨T.oppLen 0 / M.oppLen (τ 0), fun k => ?_⟩
  have h1 := T.lawSin 0 k
  have h2 := M.lawSin (τ 0) (τ k)
  rw [← h 0, ← h k] at h2
  field_simp
  have : Real.sin (T.angleAt 0) * (T.oppLen k * M.oppLen (τ 0))
      = Real.sin (T.angleAt 0) * (T.oppLen 0 * M.oppLen (τ k)) := by
    linear_combination M.oppLen (τ 0) * h1 - T.oppLen 0 * h2
  exact mul_left_cancel₀ hs.ne' this

/-- Abstract counting: one tile corner of each label across the three target corners, each
target corner carrying at least one, forces a matching of target angles to model angles. -/
theorem perm_of_figures (T M : Tri) (α β γ : ℝ)
    (hM0 : M.angleAt 0 = α) (hM1 : M.angleAt 1 = β) (hM2 : M.angleAt 2 = γ)
    (a b c : Fin 3 → ℕ)
    (hF : ∀ k, (a k : ℝ) * α + (b k : ℝ) * β + (c k : ℝ) * γ = T.angleAt k)
    (hpos : ∀ k, 1 ≤ a k + b k + c k)
    (h0 : a 0 + a 1 + a 2 = 1) (h1 : b 0 + b 1 + b 2 = 1) (h2 : c 0 + c 1 + c 2 = 1) :
    ∃ τ : Equiv.Perm (Fin 3), ∀ k, T.angleAt k = M.angleAt (τ k) := by
  have p0 := hpos 0; have p1 := hpos 1; have p2 := hpos 2
  have fin3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  let J : Fin 3 → Fin 3 := fun k => if a k = 1 then 0 else if b k = 1 then 1 else 2
  have hc : ∀ k : Fin 3, (a k = 1 ∧ b k = 0 ∧ c k = 0) ∨ (a k = 0 ∧ b k = 1 ∧ c k = 0)
      ∨ (a k = 0 ∧ b k = 0 ∧ c k = 1) := by
    have : ∀ k : Fin 3, 1 ≤ a k + b k + c k := hpos
    intro k
    rcases fin3 k with rfl | rfl | rfl <;> omega
  have hJinj : Function.Injective J := by
    intro k l hkl
    by_contra hne
    have hk := hc k; have hl := hc l
    have hkl' : k ≠ l := hne
    rcases fin3 k with rfl | rfl | rfl <;> rcases fin3 l with rfl | rfl | rfl <;>
      first | exact absurd rfl hkl' | (simp only [J] at hkl; split_ifs at hkl <;> simp_all <;> omega)
  have hθ : ∀ k, T.angleAt k = M.angleAt (J k) := by
    intro k
    have hk := hF k
    rcases hc k with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩
    · simp only [J, e0, if_true]; rw [← hk, e0, e1, e2, hM0]; simp
    · simp only [J, e0, e1]; simp; rw [← hk, e0, e1, e2, hM1]; simp
    · simp only [J, e0, e1]; simp; rw [← hk, e0, e1, e2, hM2]; simp
  exact ⟨Equiv.ofBijective J (Finite.injective_iff_bijective.mp hJinj), hθ⟩


theorem cfig_ne_of_notSimilar {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (hα0 : 0 < α) (hβ0 : 0 < β) (hγ0 : 0 < γ)
    (hαπ : α < Real.pi) (hβπ : β < Real.pi) (hγπ : γ < Real.pi)
    (hns : ¬ SimilarTM D) :
    ¬ (cfig D ![α, β, γ] 0 = 1 ∧ cfig D ![α, β, γ] 1 = 1 ∧ cfig D ![α, β, γ] 2 = 1) := by
  rintro ⟨h0, h1, h2⟩
  apply hns
  have hcorner := fun kk => Erdos634.Draft.LemmaCFigures.corner_figure D α β γ hmα hmβ hmγ hαβ hαγ
    hβγ hα0 hβ0 hγ0 hαπ hβπ hγπ kk
  obtain ⟨τ, hτ⟩ := perm_of_figures D.target D.model α β γ hmα hmβ hmγ
    (fun k => cnt D α (D.target.pts k)) (fun k => cnt D β (D.target.pts k))
    (fun k => cnt D γ (D.target.pts k))
    (fun k => (hcorner k).2.1) (fun k => (hcorner k).2.2)
    (by simpa [cfig, Fin.sum_univ_three] using h0)
    (by simpa [cfig, Fin.sum_univ_three] using h1)
    (by simpa [cfig, Fin.sum_univ_three] using h2)
  obtain ⟨μ, hμ⟩ := sides_of_angles D.target D.model τ hτ
  exact ⟨μ, τ, fun k => ⟨hτ k, hμ k⟩⟩

end Erdos634.Draft.LemmaCSimilar

#print axioms Erdos634.Draft.LemmaCSimilar.cfig_ne_of_notSimilar
