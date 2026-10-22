import Erdos634.Draft.ZhangRat8Eq
import Erdos634.Draft.ZhangRat8Tri
import Erdos634.Draft.ZhangBeeson1
import Erdos634.Draft.LemmaCFinal
import Erdos634.Draft.LemmaPProof
import Erdos634.Draft.LaczFormalBase

/-!
# Zhang (arXiv 2512.22696v4) THEOREM 1 (= Beeson-Zhang [5, Thm 1.2]), assembled

Statement: a triangle dissected into congruent tiles `R` (any `N`), `R` not similar to the target, no right angle, not all angles commensurable with `pi`
(i.e. some angle is irrational over `pi`) => the sides of `R` are commensurable (`Comm`).  Proof: Lemma C (`lemmaC_general`: right / `gamma = 2 alpha` /
`pi/3` / `2pi/3` / `3a+2b=pi` classification), then one theorem per class: `2pi/3` rows `bz_thm11`; `pi/3` = Lemma P (`lemmaP_general`, equilateral) +
`zhang_thm1_equilateral_pi3` (Laczkovich Thm 3.3); `gamma = 2 alpha` = `beeson_thm107_tri`; `3a+2b = pi` = `zhang_thm1_beeson3` (Beeson III rows 11-15).
NOTE, UNAUDITED.  Credit: Zhang (arXiv 2512.22696v4, Thm 1), Beeson-Zhang, Beeson (1206.1974, 1206.2229), Laczkovich (DCG 48 (2012); Discrete Math 140 (1995)).
-/

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional

namespace Erdos634.Draft.ZhangThm1Full
open Erdos634.Draft.LaczFormal.RG Erdos634.Geometry.Row14AnyLabel

variable {N : ℕ}

/-- Commensurability of the sides from commensurability of the sides at `sigma 0, sigma 1, sigma 2`. -/
theorem sides_of_perm (D : CongruentDissection N) (σ : Equiv.Perm (Fin 3))
    (h1 : Comm (D.model.oppLen (σ 0)) (D.model.oppLen (σ 1))) (h2 : Comm (D.model.oppLen (σ 0)) (D.model.oppLen (σ 2))) :
    Comm (D.model.oppLen 0) (D.model.oppLen 1) ∧ Comm (D.model.oppLen 0) (D.model.oppLen 2) := by
  have h12 := comm_trans' (comm_symm' h1) h2
  have key : ∀ x y : Fin 3, Comm (D.model.oppLen (σ x)) (D.model.oppLen (σ y)) := by
    intro x y
    have s1 := comm_symm' h1
    have s2 := comm_symm' h2
    have s12 := comm_symm' h12
    fin_cases x <;> fin_cases y <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    all_goals first | assumption | exact comm_refl' _
  have k := fun i j : Fin 3 => by simpa using key (σ.symm i) (σ.symm j)
  exact ⟨k 0 1, k 0 2⟩

theorem notSim_of_not_similar (D : CongruentDissection N) (hns : ¬ SimilarTM D) : NotSim D := by
  rintro ⟨ρ, hρ⟩
  apply hns
  have hcm := (A1Field.circD_pos D.model).ne'
  refine ⟨A1Field.circD D.target / A1Field.circD D.model, ρ, fun j => ⟨hρ j, ?_⟩⟩
  rw [A1Field.oppLen_eq D.target j, A1Field.oppLen_eq D.model (ρ j), hρ j]
  field_simp

theorem twoAlpha_comm (D : CongruentDissection N) (h : TwoAlphaCase D) :
    Comm (D.model.oppLen 0) (D.model.oppLen 1) ∧ Comm (D.model.oppLen 0) (D.model.oppLen 2) := by
  obtain ⟨α, a, b, c, hα, ⟨σ, h0, o0, h1, o1, h2, o2⟩, i, j, hij, ti, tj⟩ := h
  have ha : 0 < a := o0 ▸ D.model.oppLen_pos (σ 0)
  have hb : 0 < b := o1 ▸ D.model.oppLen_pos (σ 1)
  have hc : 0 < c := o2 ▸ D.model.oppLen_pos (σ 2)
  set D' := D.relabelModel σ with hD'
  have hM : ∀ k, D'.model.pts k = D.model.pts (σ k) := fun k => rfl
  have a0 : D'.model.angleAt 0 = α := by rw [angleAt_of_pts σ hM]; exact h0
  have a1 : D'.model.angleAt 1 = Real.pi - 3 * α := by rw [angleAt_of_pts σ hM]; exact h1
  have a2 : D'.model.angleAt 2 = 2 * α := by rw [angleAt_of_pts σ hM]; exact h2
  have hα' : ¬ ∃ r : ℚ, D'.model.angleAt 0 = (r : ℝ) * Real.pi := by rw [a0]; exact hα
  obtain ⟨τ, hτ0, hτ1⟩ := exists_perm i j hij
  have hsum := Erdos634.Draft.LaczFormal.angleAt_sum D.target
  have hsum' : D.target.angleAt (τ 0) + D.target.angleAt (τ 1) + D.target.angleAt (τ 2) = Real.pi := by
    have := Equiv.sum_comp τ (fun k => D.target.angleAt k)
    rw [Fin.sum_univ_three, Fin.sum_univ_three] at this
    rw [this]; exact hsum
  have hT : TgtAngles D' (D'.model.angleAt 0) (D'.model.angleAt 0) (Real.pi - 2 * D'.model.angleAt 0) := by
    refine ⟨τ, ?_, ?_, ?_⟩
    · show D.target.angleAt (τ 0) = _
      rw [hτ0, ti, a0]
    · show D.target.angleAt (τ 1) = _
      rw [hτ1, tj, a0]
    · show D.target.angleAt (τ 2) = _
      rw [hτ0, hτ1, ti, tj] at hsum'
      rw [a0]; linarith
  obtain ⟨r, s, e1, e2⟩ := ZhangRat8Tri.beeson_thm107_tri D' (by rw [a1, a0]) (by rw [a2, a0]) hα' hT
  have q0 : slen D'.toRegion 0 = a := (oppLen_of_pts σ hM 0).trans o0
  have q1 : slen D'.toRegion 1 = b := (oppLen_of_pts σ hM 1).trans o1
  have q2 : slen D'.toRegion 2 = c := (oppLen_of_pts σ hM 2).trans o2
  rw [q0, q1] at e1
  rw [q2, q0] at e2
  have c1 : Comm b a := comm_of_ratmul hb ha r e1
  have c2 : Comm a c := comm_of_ratmul ha hc s e2
  exact sides_of_perm D σ (by rw [o0, o1]; exact comm_symm' c1) (by rw [o0, o2]; exact c2)

/-- **Zhang Theorem 1.** -/
theorem zhang_thm1 (D : CongruentDissection N) (hirr : ∃ k, IrrPi (D.model.angleAt k)) (hns : ¬ SimilarTM D)
    (hnr : ∀ k, D.model.angleAt k ≠ Real.pi / 2) :
    Comm (D.model.oppLen 0) (D.model.oppLen 1) ∧ Comm (D.model.oppLen 0) (D.model.oppLen 2) := by
  rcases Erdos634.Draft.LemmaCFinal.lemmaC_general D hirr hns with
    ⟨α, -, -, -, ⟨p, q, -, -, hq⟩, -⟩ | h | ⟨α, a, b, c, hα, hd⟩ | ⟨α, a, b, c, hα, hd, -⟩ | ⟨α, β, a, b, c, hα, hrel, hd, hT⟩
  · exact absurd hq (hnr q)
  · exact twoAlpha_comm D h
  · have hE := Erdos634.Draft.LemmaPProof.lemmaP_general D α a b c hα hd hns
    have := ZhangRat8Eq.zhang_thm1_equilateral_pi3 D hE hα hd
    obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := hd
    exact sides_of_perm D σ (by rw [o0, o1]; exact this.1) (by rw [o0, o2]; exact this.2)
  · have := bz_thm11 D hα hd (notSim_of_not_similar D hns)
    obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := hd
    exact sides_of_perm D σ (by rw [o0, o1]; exact this.1) (by rw [o0, o2]; exact this.2)
  · have := ZhangBeeson1.zhang_thm1_beeson3 D hα hrel hd (by
      rcases hT with t | t | t | t | t
      · exact Or.inr (Or.inr (Or.inr (Or.inl t)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr t)))
      · exact Or.inl t
      · exact Or.inr (Or.inl t)
      · exact Or.inr (Or.inr (Or.inl t)))
    obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := hd
    exact sides_of_perm D σ (by rw [o0, o1]; exact this.1) (by rw [o0, o2]; exact this.2)

end Erdos634.Draft.ZhangThm1Full
#print axioms Erdos634.Draft.ZhangThm1Full.zhang_thm1
