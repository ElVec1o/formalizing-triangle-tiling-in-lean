-- Draft/LemmaCFinal.lean — Lemma C / Corollary C′ assembly: `LemmaCStatement`.
-- Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.Draft.LemmaCShapes
import Erdos634.Draft.LemmaCIso
import Erdos634.Draft.LemmaCArith
import Erdos634.Draft.LemmaCFigures

open scoped Classical
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.LemmaCAssemble
  Erdos634.Draft.LemmaCShapes

namespace Erdos634.Draft.LemmaCFinal

theorem key3 : ∀ p q r k : Fin 3, p ≠ q → p ≠ r → q ≠ r → k = p ∨ k = q ∨ k = r := by decide

theorem sum3 {M : Type*} [AddCommMonoid M] (f : Fin 3 → M) (i j l : Fin 3)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) : f i + f j + f l = f 0 + f 1 + f 2 := by
  have huniv : (Finset.univ : Finset (Fin 3)) = {i, j, l} := by
    ext k; simp [key3 i j l k hij hil hjl]
  have h := Fin.sum_univ_three f
  rw [huniv, Finset.sum_insert (by simp [hij, hil]), Finset.sum_insert (by simp [hjl]),
    Finset.sum_singleton] at h
  rw [← h, add_assoc]

theorem irr_transfer (y w : ℝ) (a b : ℚ) (h : y = a * w + b * Real.pi) (hy : IrrPi y) :
    IrrPi w := by
  rintro ⟨q, hq⟩
  exact hy ⟨a * q + b, by rw [h, hq]; push_cast; ring⟩

/-- Permutation with prescribed values. -/
noncomputable def permOf (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Equiv.Perm (Fin 3) :=
  Equiv.ofBijective ![a, b, c]
    ((by decide : ∀ i j l : Fin 3, i ≠ j → i ≠ l → j ≠ l → Function.Bijective ![i, j, l])
      a b c hab hac hbc)

theorem permOf_0 (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    permOf a b c hab hac hbc 0 = a := rfl
theorem permOf_1 (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    permOf a b c hab hac hbc 1 = b := rfl
theorem permOf_2 (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    permOf a b c hab hac hbc 2 = c := rfl

theorem sim_of_TA {N : ℕ} (D : CongruentDissection N) (a b c : Fin 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h : TA (fun k => D.target.angleAt k) (D.model.angleAt a) (D.model.angleAt b)
      (D.model.angleAt c)) : SimilarTM D := by
  obtain ⟨σ, h0, h1, h2⟩ := h
  let τ : Equiv.Perm (Fin 3) := σ.symm.trans (permOf a b c hab hac hbc)
  have hτ : ∀ k, D.target.angleAt k = D.model.angleAt (τ k) := by
    intro k
    obtain ⟨m, rfl⟩ := σ.surjective k
    have fin3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
    rcases fin3 m with rfl | rfl | rfl
    · simp only [τ, Equiv.trans_apply, Equiv.symm_apply_apply, permOf_0]; exact h0
    · simp only [τ, Equiv.trans_apply, Equiv.symm_apply_apply, permOf_1]; exact h1
    · simp only [τ, Equiv.trans_apply, Equiv.symm_apply_apply, permOf_2]; exact h2
  obtain ⟨μ, hμ⟩ := Erdos634.Draft.LemmaCSimilar.sides_of_angles D.target D.model τ hτ
  exact ⟨μ, τ, fun k => ⟨hτ k, hμ k⟩⟩

/-- Type `x_l = π/3`: `d = (-1,-1,2)`. -/
theorem caseSixty {N : ℕ} (D : CongruentDissection N) (i j l : Fin 3)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hirr : ∃ m, IrrPi (D.model.angleAt m))
    (hsum : D.model.angleAt i + D.model.angleAt j + D.model.angleAt l = Real.pi)
    (hrel : -D.model.angleAt i - D.model.angleAt j + 2 * D.model.angleAt l = 0) : SixtyTile D := by
  have hl : D.model.angleAt l = Real.pi / 3 := by linarith
  have hj : D.model.angleAt j = 2 * Real.pi / 3 - D.model.angleAt i := by linarith
  have hIrr : IrrPi (D.model.angleAt i) := by
    obtain ⟨m, hm⟩ := hirr
    rcases key3 i j l m hij hil hjl with rfl | rfl | rfl
    · exact hm
    · exact irr_transfer _ _ (-1) (2 / 3) (by rw [hj]; push_cast; ring) hm
    · exact irr_transfer _ _ 0 (1 / 3) (by rw [hl]; push_cast; ring) hm
  refine ⟨D.model.angleAt i, D.model.oppLen i, D.model.oppLen j, D.model.oppLen l, hIrr,
    permOf i j l hij hil hjl, ?_, rfl, ?_, rfl, ?_, rfl⟩
  · rw [permOf_0]
  · rw [permOf_1, hj]
  · rw [permOf_2, hl]


/-- Type `3α+2β = π`: `d = (-1,1,2)`. -/
theorem caseThreeTwo {N : ℕ} (D : CongruentDissection N) (i j l : Fin 3)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hirr : ∃ m, IrrPi (D.model.angleAt m)) (hns : ¬ SimilarTM D)
    (hsum : D.model.angleAt i + D.model.angleAt j + D.model.angleAt l = Real.pi)
    (hrel : -D.model.angleAt i + D.model.angleAt j + 2 * D.model.angleAt l = 0)
    (P Q R : Fin 3 → ℕ)
    (hθ : ∀ k, D.target.angleAt k = (P k : ℝ) * D.model.angleAt i + (Q k : ℝ) * D.model.angleAt j
      + (R k : ℝ) * D.model.angleAt l)
    (hP : P 0 + P 1 + P 2 = 0) (hQ : Q 0 + Q 1 + Q 2 = 2) (hR : R 0 + R 1 + R 2 = 3)
    (hpos : ∀ k, 1 ≤ P k + Q k + R k) : ThreeTwoCase D := by
  have hu : D.model.angleAt i = 2 * D.model.angleAt l + D.model.angleAt j := by linarith
  have hr2 : 3 * D.model.angleAt l + 2 * D.model.angleAt j = Real.pi := by linarith
  have hj : D.model.angleAt j = Real.pi / 2 - 3 / 2 * D.model.angleAt l := by linarith
  have hIrr : IrrPi (D.model.angleAt l) := by
    obtain ⟨m, hm⟩ := hirr
    rcases key3 i j l m hij hil hjl with rfl | rfl | rfl
    · exact irr_transfer _ _ (1 / 2) (1 / 2) (by rw [hu, hj]; push_cast; ring) hm
    · exact irr_transfer _ _ (-3 / 2) (1 / 2) (by rw [hj]; push_cast; ring) hm
    · exact hm
  have hdata : D.model.ThreeAlphaData (D.model.angleAt l) (D.model.angleAt j)
      (D.model.oppLen l) (D.model.oppLen j) (D.model.oppLen i) :=
    ⟨permOf l j i hjl.symm hil.symm hij.symm, by rw [permOf_0], rfl, by rw [permOf_1], rfl,
      by rw [permOf_2, hu], rfl⟩
  refine ⟨_, _, _, _, _, hIrr, hr2, hdata, ?_⟩
  rcases shapes_threeTwo (fun k => D.target.angleAt k) _ _ _ P Q R hu hr2 hθ hP hQ hR hpos with
    h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · exact absurd (sim_of_TA D l j i hjl.symm hil.symm hij.symm h) hns


/-- Type `γ = 2α`: `d = (-1,0,2)`. -/
theorem caseTwoAlpha {N : ℕ} (D : CongruentDissection N) (i j l : Fin 3)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hirr : ∃ m, IrrPi (D.model.angleAt m)) (hns : ¬ SimilarTM D)
    (hsum : D.model.angleAt i + D.model.angleAt j + D.model.angleAt l = Real.pi)
    (hrel : -D.model.angleAt i + 0 * D.model.angleAt j + 2 * D.model.angleAt l = 0)
    (P Q R : Fin 3 → ℕ)
    (hθ : ∀ k, D.target.angleAt k = (P k : ℝ) * D.model.angleAt i + (Q k : ℝ) * D.model.angleAt j
      + (R k : ℝ) * D.model.angleAt l)
    (hP : P 0 + P 1 + P 2 = 0) (hQ : Q 0 + Q 1 + Q 2 = 1) (hR : R 0 + R 1 + R 2 = 3)
    (hpos : ∀ k, 1 ≤ P k + Q k + R k) : TwoAlphaCase D := by
  have hu : D.model.angleAt i = 2 * D.model.angleAt l := by linarith
  have hv : D.model.angleAt j = Real.pi - 3 * D.model.angleAt l := by linarith
  have hIrr : IrrPi (D.model.angleAt l) := by
    obtain ⟨m, hm⟩ := hirr
    rcases key3 i j l m hij hil hjl with rfl | rfl | rfl
    · exact irr_transfer _ _ 2 0 (by rw [hu]; push_cast; ring) hm
    · exact irr_transfer _ _ (-3) 1 (by rw [hv]; push_cast; ring) hm
    · exact hm
  have hdata : D.model.TwoAlphaData (D.model.angleAt l) (D.model.oppLen l) (D.model.oppLen j)
      (D.model.oppLen i) :=
    ⟨permOf l j i hjl.symm hil.symm hij.symm, by rw [permOf_0], rfl, by rw [permOf_1, hv], rfl,
      by rw [permOf_2, hu], rfl⟩
  refine ⟨_, _, _, _, hIrr, hdata, ?_⟩
  rcases shapes_twoAlpha (fun k => D.target.angleAt k) _ _ _ P Q R hu hv hθ hP hQ hR hpos with h | h
  · obtain ⟨σ, h0, h1, -⟩ := h
    exact ⟨σ 0, σ 1, fun e => absurd (σ.injective e) (by decide), h0, h1⟩
  · exact absurd (sim_of_TA D l j i hjl.symm hil.symm hij.symm h) hns

/-- Type right angle: `d = (-1,1,1)`. -/
theorem caseRight {N : ℕ} (D : CongruentDissection N) (i j l : Fin 3)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hirr : ∃ m, IrrPi (D.model.angleAt m)) (hns : ¬ SimilarTM D)
    (hsum : D.model.angleAt i + D.model.angleAt j + D.model.angleAt l = Real.pi)
    (hrel : -D.model.angleAt i + D.model.angleAt j + D.model.angleAt l = 0)
    (P Q R : Fin 3 → ℕ)
    (hθ : ∀ k, D.target.angleAt k = (P k : ℝ) * D.model.angleAt i + (Q k : ℝ) * D.model.angleAt j
      + (R k : ℝ) * D.model.angleAt l)
    (hP : P 0 + P 1 + P 2 = 0) (hQ : Q 0 + Q 1 + Q 2 = 2) (hR : R 0 + R 1 + R 2 = 2)
    (hpos : ∀ k, 1 ≤ P k + Q k + R k) : RightCase D := by
  have hu : D.model.angleAt i = Real.pi / 2 := by linarith
  have hw : D.model.angleAt l = Real.pi / 2 - D.model.angleAt j := by linarith
  have hlpos : 0 < D.model.angleAt l := Erdos634.MarchFlank.cornerAngle_pos D.model l
  have hjpos : 0 < D.model.angleAt j := Erdos634.MarchFlank.cornerAngle_pos D.model j
  have hIrr : IrrPi (D.model.angleAt j) := by
    obtain ⟨m, hm⟩ := hirr
    rcases key3 i j l m hij hil hjl with rfl | rfl | rfl
    · exact absurd ⟨1 / 2, by rw [hu]; push_cast; ring⟩ hm
    · exact hm
    · exact irr_transfer _ _ (-1) (1 / 2) (by rw [hw]; push_cast; ring) hm
  have hirrat : Irrational (D.model.angleAt j / Real.pi) := by
    rintro ⟨q, hq⟩
    apply hIrr
    refine ⟨q, ?_⟩
    have := Real.pi_pos.ne'
    field_simp at hq ⊢
    linarith
  refine ⟨D.model.angleAt j, hjpos, by linarith, hirrat, ⟨j, i, hij.symm, rfl, hu⟩, ?_⟩
  rcases shapes_right (fun k => D.target.angleAt k) _ _ _ P Q R hu hw hθ hP hQ hR hpos with
    h | h | h
  · obtain ⟨σ, h0, h1, -⟩ := h
    exact ⟨D.model.angleAt j, Or.inl rfl, σ 0, σ 1,
      fun e => absurd (σ.injective e) (by decide), h0, h1⟩
  · obtain ⟨σ, -, h1, h2⟩ := h
    exact ⟨D.model.angleAt l, Or.inr hw, σ 1, σ 2,
      fun e => absurd (σ.injective e) (by decide), h1, h2⟩
  · exact absurd (sim_of_TA D i j l hij hil hjl h) hns

/-- Type `2π/3`: `d = (-1,2,2)`. -/
theorem caseTwoPiThree {N : ℕ} (D : CongruentDissection N) (i j l : Fin 3)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hirr : ∃ m, IrrPi (D.model.angleAt m)) (hns : ¬ SimilarTM D)
    (hsum : D.model.angleAt i + D.model.angleAt j + D.model.angleAt l = Real.pi)
    (hrel : -D.model.angleAt i + 2 * D.model.angleAt j + 2 * D.model.angleAt l = 0)
    (P Q R : Fin 3 → ℕ)
    (hθ : ∀ k, D.target.angleAt k = (P k : ℝ) * D.model.angleAt i + (Q k : ℝ) * D.model.angleAt j
      + (R k : ℝ) * D.model.angleAt l)
    (hP : P 0 + P 1 + P 2 = 0) (hQ : Q 0 + Q 1 + Q 2 = 3) (hR : R 0 + R 1 + R 2 = 3)
    (hpos : ∀ k, 1 ≤ P k + Q k + R k) : TwoPiThreeCase D := by
  have hu : D.model.angleAt i = 2 * Real.pi / 3 := by linarith
  have hv : D.model.angleAt j = Real.pi / 3 - D.model.angleAt l := by linarith
  have hIrr : IrrPi (D.model.angleAt l) := by
    obtain ⟨m, hm⟩ := hirr
    rcases key3 i j l m hij hil hjl with rfl | rfl | rfl
    · exact absurd ⟨2 / 3, by rw [hu]; push_cast; ring⟩ hm
    · exact irr_transfer _ _ (-1) (1 / 3) (by rw [hv]; push_cast; ring) hm
    · exact hm
  have hdata : D.model.TwoPiThreeData (D.model.angleAt l) (D.model.oppLen l) (D.model.oppLen j)
      (D.model.oppLen i) :=
    ⟨permOf l j i hjl.symm hil.symm hij.symm, by rw [permOf_0], rfl, by rw [permOf_1, hv], rfl,
      by rw [permOf_2, hu], rfl⟩
  have hθ' : ∀ k, D.target.angleAt k = (P k : ℝ) * D.model.angleAt i
      + (Q k : ℝ) * (Real.pi / 3 - D.model.angleAt l) + (R k : ℝ) * D.model.angleAt l := by
    intro k; rw [hθ k, hv]
  refine ⟨_, _, _, _, hIrr, hdata, ?_⟩
  rcases shapes_twoPiThree (fun k => D.target.angleAt k) _ _ _ P Q R hu rfl hθ' hP hQ hR hpos with
    h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (Or.inl h))
  · exact Or.inr (Or.inl (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inl (Or.inr h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
  · have h' : TA (fun k => D.target.angleAt k) (D.model.angleAt l) (D.model.angleAt j)
        (D.model.angleAt i) := by rw [hv]; exact h
    exact absurd (sim_of_TA D l j i hjl.symm hil.symm hij.symm h') hns


/-- Lemma C + Corollary C′ in full generality: no primality or congruence hypothesis on `N`. -/
theorem lemmaC_general {N : ℕ} (D : CongruentDissection N)
    (hirr : ∃ k, IrrPi (D.model.angleAt k)) (hns : ¬ SimilarTM D) :
    RightCase D ∨ TwoAlphaCase D ∨ SixtyTile D ∨ TwoPiThreeCase D ∨ ThreeTwoCase D := by
  have fin3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  by_cases iso : ∃ p q : Fin 3, p ≠ q ∧ D.model.angleAt p = D.model.angleAt q
  · obtain ⟨p, q, hpq, he⟩ := iso
    have h3 : ∀ p q : Fin 3, p ≠ q → ∃ r, p ≠ r ∧ q ≠ r := by decide
    obtain ⟨r, hpr, hqr⟩ := h3 p q hpq
    exact absurd (Erdos634.Draft.LemmaCIso.iso_similar D p q r hpq hpr hqr he hirr) hns
  push Not at iso
  set α := D.model.angleAt 0 with hα
  set β := D.model.angleAt 1 with hβ
  set γ := D.model.angleAt 2 with hγ
  have hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α := rfl
  have hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β := rfl
  have hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ := rfl
  have hαβ : α ≠ β := iso 0 1 (by decide)
  have hαγ : α ≠ γ := iso 0 2 (by decide)
  have hβγ : β ≠ γ := iso 1 2 (by decide)
  have hpos : ∀ m, 0 < D.model.angleAt m := fun m => Erdos634.MarchFlank.cornerAngle_pos D.model m
  have hlt : ∀ m, D.model.angleAt m < Real.pi := fun m =>
    Erdos634.RouteOneVertexKill.cornerAngle_lt_pi D.model m
  have hxm : ∀ m, (![α, β, γ] : Fin 3 → ℝ) m = D.model.angleAt m := by
    intro m; rcases fin3 m with rfl | rfl | rfl <;> rfl
  have hirr' : ∃ i, ¬ ∃ r : ℚ, (![α, β, γ] : Fin 3 → ℝ) i = (r : ℝ) * Real.pi := by
    obtain ⟨k, hk⟩ := hirr
    exact ⟨k, by rw [hxm]; exact hk⟩
  have hne := Erdos634.Draft.LemmaCSimilar.cfig_ne_of_notSimilar D α β γ hmα hmβ hmγ hαβ hαγ hβγ
    (hpos 0) (hpos 1) (hpos 2) (hlt 0) (hlt 1) (hlt 2) hns
  obtain ⟨d, hd1, hd2, hd3, hd4, hd5, hd6⟩ := lemmaC_geometric D α β γ hmα hmβ hmγ hαβ hαγ hβγ
    (hpos 0) (hpos 1) (hpos 2) (hlt 0) (hlt 1) (hlt 2) hirr' hne
  have hm : d 0 = -1 ∨ d 1 = -1 ∨ d 2 = -1 := by
    obtain ⟨j, hj⟩ := hd3; rcases fin3 j with rfl | rfl | rfl <;> simp_all
  have hp : 0 < d 0 ∨ 0 < d 1 ∨ 0 < d 2 := by
    obtain ⟨j, hj⟩ := hd4; rcases fin3 j with rfl | rfl | rfl <;> simp_all
  obtain ⟨i, j, l, hij, hjl, hil, hmem⟩ := Erdos634.Draft.LemmaCArith.enum_six (d 0) (d 1) (d 2)
    (hd2 0) (hd2 1) (hd2 2) hm hp hd5
  have hdi : ∀ m, (![d 0, d 1, d 2] : Fin 3 → ℤ) m = d m := by
    intro m; rcases fin3 m with rfl | rfl | rfl <;> rfl
  simp only [hdi, Erdos634.Draft.LemmaCArith.sixVectors, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq] at hmem
  -- reindexed relations
  have hsumπ : D.model.angleAt i + D.model.angleAt j + D.model.angleAt l = Real.pi := by
    rw [sum3 (fun m => D.model.angleAt m) i j l hij hil hjl]
    exact Erdos634.Geometry.cornerAngle_sum D.model
  have hrel : (d i : ℝ) * D.model.angleAt i + (d j : ℝ) * D.model.angleAt j
      + (d l : ℝ) * D.model.angleAt l = 0 := by
    rw [sum3 (fun m => (d m : ℝ) * D.model.angleAt m) i j l hij hil hjl]
    exact hd6
  -- corner data reindexed
  have hcorner := fun kk => Erdos634.Draft.LemmaCFigures.corner_figure D α β γ hmα hmβ hmγ hαβ hαγ
    hβγ (hpos 0) (hpos 1) (hpos 2) (hlt 0) (hlt 1) (hlt 2) kk
  set P : Fin 3 → ℕ := fun k => cnt D (D.model.angleAt i) (D.target.pts k) with hP
  set Q : Fin 3 → ℕ := fun k => cnt D (D.model.angleAt j) (D.target.pts k) with hQ
  set R : Fin 3 → ℕ := fun k => cnt D (D.model.angleAt l) (D.target.pts k) with hR
  have hθ : ∀ k, D.target.angleAt k = (P k : ℝ) * D.model.angleAt i + (Q k : ℝ) * D.model.angleAt j
      + (R k : ℝ) * D.model.angleAt l := by
    intro k
    have h := (hcorner k).2.1
    have h2 := sum3 (fun m => ((cnt D (D.model.angleAt m) (D.target.pts k) : ℕ) : ℝ) *
      D.model.angleAt m) i j l hij hil hjl
    simp only [Fin.sum_univ_three] at h2
    have hk : D.target.angleAt k = cornerAngle (D.target.pts (k + 1)) (D.target.pts k)
      (D.target.pts (k + 2)) := rfl
    rw [hk, ← h]
    simp only [hP, hQ, hR]
    simp only [cnt] at h2 ⊢
    linarith [h2]
  have hposk : ∀ k, 1 ≤ P k + Q k + R k := by
    intro k
    have h : 1 ≤ cnt D (D.model.angleAt 0) (D.target.pts k)
        + cnt D (D.model.angleAt 1) (D.target.pts k) + cnt D (D.model.angleAt 2) (D.target.pts k) :=
      (hcorner k).2.2
    have h2 := sum3 (fun m => cnt D (D.model.angleAt m) (D.target.pts k)) i j l hij hil hjl
    simp only [hP, hQ, hR] at h2 ⊢
    omega
  have htot : ∀ m, cnt D (D.model.angleAt m) (D.target.pts 0) + cnt D (D.model.angleAt m) (D.target.pts 1)
      + cnt D (D.model.angleAt m) (D.target.pts 2) = cfig D ![α, β, γ] m := by
    intro m
    simp only [cfig, Fin.sum_univ_three, hxm]
  have hPt : ∀ e : ℤ, d i = e → P 0 + P 1 + P 2 = (1 + e).toNat := by
    intro e he; have := hd1 i; have := htot i; simp only [hP]; omega
  have hQt : ∀ e : ℤ, d j = e → Q 0 + Q 1 + Q 2 = (1 + e).toNat := by
    intro e he; have := hd1 j; have := htot j; simp only [hQ]; omega
  have hRt : ∀ e : ℤ, d l = e → R 0 + R 1 + R 2 = (1 + e).toNat := by
    intro e he; have := hd1 l; have := htot l; simp only [hR]; omega
  have hc : ∀ (a b c : ℤ), d i = a → d j = b → d l = c →
      (a : ℝ) * D.model.angleAt i + (b : ℝ) * D.model.angleAt j + (c : ℝ) * D.model.angleAt l = 0 := by
    intro a b c ha hb hc'
    have := hrel; rw [ha, hb, hc'] at this; exact this
  rcases hmem with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
  · exfalso
    have := hc _ _ _ e1 e2 e3
    push_cast at this
    exact iso i j hij (by linarith)
  · refine Or.inr (Or.inl (caseTwoAlpha D i j l hij hil hjl hirr hns hsumπ ?_ P Q R hθ ?_ ?_ ?_ hposk))
    · have := hc _ _ _ e1 e2 e3; push_cast at this; linarith
    · rw [hPt _ e1]; rfl
    · rw [hQt _ e2]; rfl
    · rw [hRt _ e3]; rfl
  · refine Or.inl (caseRight D i j l hij hil hjl hirr hns hsumπ ?_ P Q R hθ ?_ ?_ ?_ hposk)
    · have := hc _ _ _ e1 e2 e3; push_cast at this; linarith
    · rw [hPt _ e1]; rfl
    · rw [hQt _ e2]; rfl
    · rw [hRt _ e3]; rfl
  · refine Or.inr (Or.inr (Or.inr (Or.inr (caseThreeTwo D i j l hij hil hjl hirr hns hsumπ ?_ P Q R hθ ?_ ?_ ?_ hposk))))
    · have := hc _ _ _ e1 e2 e3; push_cast at this; linarith
    · rw [hPt _ e1]; rfl
    · rw [hQt _ e2]; rfl
    · rw [hRt _ e3]; rfl
  · refine Or.inr (Or.inr (Or.inr (Or.inl (caseTwoPiThree D i j l hij hil hjl hirr hns hsumπ ?_ P Q R hθ ?_ ?_ ?_ hposk))))
    · have := hc _ _ _ e1 e2 e3; push_cast at this; linarith
    · rw [hPt _ e1]; rfl
    · rw [hQt _ e2]; rfl
    · rw [hRt _ e3]; rfl
  · refine Or.inr (Or.inr (Or.inl (caseSixty D i j l hij hil hjl hirr hsumπ ?_)))
    have := hc _ _ _ e1 e2 e3; push_cast at this; linarith

theorem lemmaCStatement : LemmaCStatement :=
  fun _ D _ _ _ hirr hns => lemmaC_general D hirr hns

/-- Non-vacuity: the hypotheses of `lemmaC_general` (an irrational model angle, target not
similar to the tile) hold jointly on the certified 44-tiling, whose conclusion is the
`ThreeTwoCase` of `lemmaC_conclusion_real_44`. -/
theorem lemmaC_hyps_witness_44 :
    (∃ k, IrrPi (D44.model.angleAt k)) ∧ ¬ SimilarTM D44 := by
  refine ⟨lemmaC_conclusion_real_44.2, ?_⟩
  rintro ⟨μ, τ, h⟩
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := Erdos634.Draft.FluxRow11Witness.data44
  have g0 : D44.model.angleAt (σ 0) = Erdos634.Draft.FluxGridWitness.α44 := h0
  have g1 : D44.model.angleAt (σ 1) = Erdos634.Draft.FluxGridWitness.β44 := h1
  have g2 : D44.model.angleAt (σ 2) = 2 * Erdos634.Draft.FluxGridWitness.α44
      + Erdos634.Draft.FluxGridWitness.β44 := h2
  have t0 : D44.target.angleAt 0 = Erdos634.Draft.FluxGridWitness.β44 :=
    Erdos634.Draft.FluxGridWitness.t_angle0
  have t1 : D44.target.angleAt 1 = Erdos634.Draft.FluxGridWitness.β44 :=
    Erdos634.Draft.FluxGridWitness.t_angle1
  have hτ : τ 0 ≠ τ 1 := τ.injective.ne (by decide)
  have e0 : Erdos634.Draft.FluxGridWitness.β44 = D44.model.angleAt (τ 0) := by
    rw [← t0]; exact (h 0).1
  have e1 : Erdos634.Draft.FluxGridWitness.β44 = D44.model.angleAt (τ 1) := by
    rw [← t1]; exact (h 1).1
  obtain ⟨m0, hm0⟩ := σ.surjective (τ 0)
  obtain ⟨m1, hm1⟩ := σ.surjective (τ 1)
  rw [← hm0] at e0; rw [← hm1] at e1
  have hne : m0 ≠ m1 := fun e => hτ (by rw [← hm0, ← hm1, e])
  have hα : 0 < Erdos634.Draft.FluxGridWitness.α44 := by
    have := Erdos634.MarchFlank.cornerAngle_pos D44.model (σ 0)
    change 0 < D44.model.angleAt (σ 0) at this
    rwa [g0] at this
  have hrel := Erdos634.Draft.FluxGridWitness.three_α_two_β
  have hα44 := Erdos634.Draft.FluxGridWitness.α44_irr
  have fin3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  have bad : ∀ m : Fin 3, m ≠ 1 → Erdos634.Draft.FluxGridWitness.β44 = D44.model.angleAt (σ m)
      → False := by
    intro m hm e
    rcases fin3 m with rfl | rfl | rfl
    · rw [g0] at e
      exact hα44 ⟨1 / 5, by push_cast; linarith⟩
    · exact hm rfl
    · rw [g2] at e; linarith
  by_cases hm : m0 = 1
  · exact bad m1 (fun e => hne (hm.trans e.symm)) e1
  · exact bad m0 hm e0

end Erdos634.Draft.LemmaCFinal

#print axioms Erdos634.Draft.LemmaCFinal.lemmaC_general
#print axioms Erdos634.Draft.LemmaCFinal.lemmaCStatement
