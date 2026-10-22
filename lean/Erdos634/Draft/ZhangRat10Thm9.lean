import Erdos634.Draft.ZhangThm1Full
import Erdos634.Draft.LaczFormal51Lemma1
import Erdos634.Draft.BeesonShapesL5L6L11

/-!
# Beeson (arXiv 1206.2229v4) THEOREM 9, in its printed (hypothesis-free) form

Printed: "Let ABC be a triangle, not similar to T, tiled by copies of a triangle T with 3 alpha + 2 beta = pi.  Then T is rational."
(Proof printed: Lemma 11 gives five shapes; Thms 5, 6, 8 give rationality.)  Zhang (arXiv 2512.22696v4) cites it as "Theorem 3 of [2]".
There is NO hypothesis that alpha is irrational over pi; Beeson's Lemma 1 derives it from Laczkovich Thms 5.1, 5.3.  Here:
* `BeesonH1.lemma1_unconditional` (Lacz51Gen2.lacz51_all + lacz53_thm) gives `alpha not in Q pi` from "target not similar";
* `BeesonColoring.lemma11` gives the five shapes; `ZhangBeeson1.zhang_thm1_beeson3` (Rows 11-15 rationality) gives the sides.
`beeson_thm9` : AAA reading of "not similar" (the form `lemma1_unconditional` uses); `beeson_thm9_printed` : literal statement
(tile angles `alpha, beta` with `3 alpha + 2 beta = pi` at some vertices; `not SimilarTM`; conclusion all side ratios rational).
NOTE, UNAUDITED.  Credit: Beeson (arXiv 1206.2229v4, Thm 9, Lemmas 1, 11), Laczkovich (Discrete Math 140 (1995) Thms 5.1, 5.3),
Zhang (arXiv 2512.22696v4), Beeson-Zhang.
-/

open scoped Classical
open Erdos634.Geometry Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
  Erdos634.BeesonColoring

namespace Erdos634.Draft.ZhangRat10Thm9
open Erdos634.Draft.LaczFormal.RG

/-- `Triple3` is "the triple is a permutation of the other", as an `Equiv.Perm`. -/
theorem triple3_perm (f : Fin 3 → ℝ) {p q r : ℝ} (h : Triple3 (f 0) (f 1) (f 2) p q r) :
    ∃ σ : Equiv.Perm (Fin 3), f (σ 0) = p ∧ f (σ 1) = q ∧ f (σ 2) = r := by
  rcases h with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · exact ⟨1, h0, h1, h2⟩
  · exact ⟨Equiv.swap 1 2, by simpa using h0, by simpa using h2, by simpa using h1⟩
  · exact ⟨Equiv.swap 0 1, by simpa using h1, by simpa using h0, by simpa using h2⟩
  · exact ⟨⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩, h2, h0, h1⟩
  · exact ⟨⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩, h1, h2, h0⟩
  · exact ⟨Equiv.swap 0 2, by simpa using h2, by simpa using h1, by simpa using h0⟩

theorem tgt_swap {N : ℕ} {D : CongruentDissection N} {p q r : ℝ} (h : TgtAngles D p q r) : TgtAngles D p r q := by
  obtain ⟨σ, h0, h1, h2⟩ := h
  exact ⟨σ * Equiv.swap 1 2, by simpa using h0, by simpa using h2, by simpa using h1⟩

theorem fiveShapes_tgt {N : ℕ} {D : CongruentDissection N} {α β : ℝ}
    (h : FiveShapes (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β) :
    TgtAngles D (2 * α) β (α + β) ∨ TgtAngles D (2 * α) α (2 * β) ∨ TgtAngles D α α (α + 2 * β) ∨
      TgtAngles D β β (3 * α) ∨ TgtAngles D (α + β) (α + β) α := by
  have key := fun {p q r : ℝ} (t : Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) p q r) =>
    (triple3_perm D.target.angleAt t : ∃ σ : Equiv.Perm (Fin 3), D.target.angleAt (σ 0) = p ∧
      D.target.angleAt (σ 1) = q ∧ D.target.angleAt (σ 2) = r)
  rcases h with t | t | t | t | t
  · exact Or.inr (Or.inr (Or.inl (tgt_swap (key t))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (tgt_swap (key t)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (tgt_swap (key t)))))
  · exact Or.inl (key t)
  · exact Or.inr (Or.inl (key t))

/-- **Beeson Theorem 9** (AAA reading of "not similar"; `T` rational = all side ratios rational). -/
theorem beeson_thm9 {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi) (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) :
    Comm a b ∧ Comm a c := by
  have hα := Erdos634.BeesonH1.lemma1_unconditional D hrel h hns
  obtain ⟨h5, -⟩ := lemma11 D hα hrel h hns
  exact ZhangBeeson1.zhang_thm1_beeson3 D hα hrel h (by
    rcases fiveShapes_tgt h5 with t | t | t | t | t
    · exact Or.inl t
    · exact Or.inr (Or.inl t)
    · exact Or.inr (Or.inr (Or.inl t))
    · exact Or.inr (Or.inr (Or.inr (Or.inl t)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr t))))

/-- ABC not similar to T in the sense of `SimilarTM` implies the AAA non-similarity used by Lemma 1. -/
theorem notTriple3_of_not_similar {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (h : D.model.ThreeAlphaData α β a b c) (hγ : 2 * α + β = Real.pi - α - β)
    (hns : ¬ SimilarTM D) :
    ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β) := by
  intro t
  obtain ⟨τ, t0, t1, t2⟩ := triple3_perm D.target.angleAt t
  obtain ⟨σ, m0, -, m1, -, m2, -⟩ := h
  apply Erdos634.Draft.ZhangThm1Full.notSim_of_not_similar D hns
  refine ⟨τ.symm.trans σ, fun j => ?_⟩
  obtain ⟨k, rfl⟩ := τ.surjective j
  fin_cases k
  · simp [t0, m0]
  · simp [t1, m1]
  · simp [t2, m2]

/-- **Beeson Theorem 9, printed form.**  `D`: a dissection of a triangle by copies of a tile having angles `alpha, beta` (at some vertices) with
`3 alpha + 2 beta = pi`; the target is not similar to the tile (`SimilarTM`).  Then every ratio of tile sides is rational. -/
theorem beeson_thm9_printed {N : ℕ} (D : CongruentDissection N) (α β : ℝ)
    (hrel : 3 * α + 2 * β = Real.pi)
    (hang : ∃ σ : Equiv.Perm (Fin 3), D.model.angleAt (σ 0) = α ∧ D.model.angleAt (σ 1) = β)
    (hns : ¬ SimilarTM D) :
    ∀ i j, Comm (D.model.oppLen i) (D.model.oppLen j) := by
  obtain ⟨σ, m0, m1⟩ := hang
  have hsum := Erdos634.Draft.LaczFormal.angleAt_sum D.model
  have hsum' : D.model.angleAt (σ 0) + D.model.angleAt (σ 1) + D.model.angleAt (σ 2) = Real.pi := by
    have := Equiv.sum_comp σ (fun k => D.model.angleAt k)
    rw [Fin.sum_univ_three, Fin.sum_univ_three] at this
    rw [this]; exact hsum
  have m2 : D.model.angleAt (σ 2) = 2 * α + β := by rw [m0, m1] at hsum'; linarith
  have h : D.model.ThreeAlphaData α β (D.model.oppLen (σ 0)) (D.model.oppLen (σ 1)) (D.model.oppLen (σ 2)) :=
    ⟨σ, m0, rfl, m1, rfl, m2, rfl⟩
  have hns' := notTriple3_of_not_similar D h (by linarith) hns
  obtain ⟨c1, c2⟩ := beeson_thm9 D hrel h hns'
  have hpos : ∀ k, 0 < D.model.oppLen k := fun k => D.model.oppLen_pos k
  have key : ∀ x y : Fin 3, Comm (D.model.oppLen (σ x)) (D.model.oppLen (σ y)) := by
    have s1 := comm_symm' c1
    have s2 := comm_symm' c2
    have s12 := comm_trans' s1 c2
    have s21 := comm_symm' s12
    intro x y
    fin_cases x <;> fin_cases y <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    all_goals first | assumption | exact comm_refl' _
  intro i j
  obtain ⟨x, rfl⟩ := σ.surjective i
  obtain ⟨y, rfl⟩ := σ.surjective j
  exact key x y

/-- Zhang Thm 1, Beeson-III rows, WITHOUT the irrationality assumption `alpha not in Q pi`: replaced by the printed hypothesis "target not similar to the tile"
(the five target shapes are then a conclusion, not an input; this is `beeson_thm9`).  The shape hypothesis `hT` is kept only to match `zhang_thm1_beeson3`'s statement and is unused. -/
theorem zhang_thm1_beeson3_unc {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi) (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β))
    (_hT : TgtAngles D (2 * α) β (α + β) ∨ TgtAngles D (2 * α) α (2 * β) ∨ TgtAngles D α α (α + 2 * β) ∨
      TgtAngles D β β (3 * α) ∨ TgtAngles D (α + β) (α + β) α) :
    Comm a b ∧ Comm a c := beeson_thm9 D hrel h hns

end Erdos634.Draft.ZhangRat10Thm9
#print axioms Erdos634.Draft.ZhangRat10Thm9.beeson_thm9
#print axioms Erdos634.Draft.ZhangRat10Thm9.beeson_thm9_printed
#print axioms Erdos634.Draft.ZhangRat10Thm9.zhang_thm1_beeson3_unc
