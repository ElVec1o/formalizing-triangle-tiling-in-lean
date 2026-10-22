import Erdos634.Draft.BeesonL28c2

/-!
# Beeson (arXiv 1206.2229v4) Lemma 28 and Definition 8, with `M1, M2` the PRINTED sums of tile signs

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Lemma 23, Thm 3, Thm 4, Def. 8, Lemma 28), Laczkovich
(DCG 48 (2012)), Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.

Replaces the weak `BeesonL28b.lemma28_printed` (existential `M1, M2`, triquadratic clause `exists M1 M2, M1 = M2`).
Here, for the printed vertex order (angles of `ABC` at `A, B, C` = target vertices `0, 1, 2`):
* `M1 := sum_i eps1_i`, `M2 := sum_i eps2_i`, where `eps1_i` (`eps2_i`) is the sign of the `Phi_1` (`Phi_2`) flux of tile `i`
  against the model's value `a+b+c` (`a-b-c`), the characters being anchored at `AB` (Lemma 23 normalisation `Phi_i = +1`
  on `AB`).  Nothing is existentially quantified: `M1, M2` are universally quantified integers equal to these sums.
* the triquadratic clause is `M1 = M2` together with `M1 = Lambda s`, so `M1 != 0` and `M2 - M1 = 0` (Def. 8 does not apply);
* `kappa := (M1 + M2)/(M2 - M1)` is `-s`, `s`, and `s/(2-s^2)` with `0 < kappa < 1`, `s = kappa(2-s^2)`, quartic.
* `exists_signs1`, `exists_signs2`: the sign vectors exist (so the hypotheses are satisfiable); `eps1` is a proper 2-colouring,
  so `M1` is blacks minus whites (Remark after Thm 3, Lemma 12).
(H1): `delta = alpha + beta` irrational, as in the printed section (Lemma 27 divides by `sin delta`), equivalent to
`alpha notin Q pi` (`delta_irr_iff`).  LABEL: PARTIAL only in that `eps2` is the flux sign `(-1)^{n+eps}` by definition of
`Phi_2` (Lemma 22), not re-derived from a tile-orientation parity `n`.
-/

open scoped Classical

namespace Erdos634.BeesonColoring

open Erdos634.Geometry Erdos634.Geometry.A1Field

variable {N : ℕ}

theorem model_hext_anc (T : Tri) {α β a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.ThreeAlphaData α β a b c) (hrel : 3 * α + 2 * β = Real.pi) (anc : Real.Angle) :
    ∀ k, (chiAt α hα 1 anc).chi ((Real.pi - T.angleAt k : ℝ) : Real.Angle) = 1 := by
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := h
  intro k
  obtain ⟨m, rfl⟩ := σ.surjective k
  have hk : m = 0 ∨ m = 1 ∨ m = 2 := by fin_cases m <;> simp
  rcases hk with rfl | rfl | rfl
  · rw [h0, show Real.pi - α = ((2 : ℤ) : ℝ) * Real.pi + ((-2 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) by
      push_cast; ring, chiAt_chi, if_pos (by decide)]
  · rw [h1, show Real.pi - β = ((-1 : ℤ) : ℝ) * Real.pi + ((3 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) by
      push_cast; linarith, chiAt_chi, if_pos (by decide)]
  · rw [h2, show Real.pi - (2 * α + β) = ((1 : ℤ) : ℝ) * Real.pi + ((-1 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) by
      push_cast; linarith, chiAt_chi, if_pos (by decide)]

/-- The `Phi_1` signs exist and form a proper 2-colouring (blacks/whites). -/
theorem exists_signs1 (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) :
    ∃ ε1 : Fin N → ℤ, SignsFor D (Phi1 D α hα) ε1 ∧ D.toDissection.ProperColouring ε1 := by
  obtain ⟨ε, hε, hfl, -⟩ := D.flux_colouring (Phi1 D α hα) (chiAt_sq _ _ _ _)
    (D.model.threeAlpha_angles_mem hα hrel h 1) (model_hext_anc D.model hα h hrel _)
  exact ⟨ε, hfl, hε⟩

/-- The `Phi_2` signs exist (each tile has flux `+-` the model value). -/
theorem exists_signs2 (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) :
    ∃ ε2 : Fin N → ℤ, SignsFor D (Phi2 D α hα) ε2 ∧ ∀ i, ε2 i = 1 ∨ ε2 i = -1 := by
  set G := Phi2 D α hα with hG
  have hsq := chiAt_sq α hα 0 (D.target.leftUnit 0).angle
  have hmodel : ∀ k, ((D.model.angleAt k : ℝ) : Real.Angle) ∈ G.L :=
    D.model.threeAlpha_angles_mem hα hrel h 0
  set K := G.tileValue D.model with hKdef
  have htile : ∀ i, (D.tile i).flux G.weight = K ∨ (D.tile i).flux G.weight = -K := by
    intro i
    obtain ⟨σ, hσ⟩ := (D.tiles_congruent i).exists_perm
    have hi : ∀ k, (((D.tile i).angleAt k : ℝ) : Real.Angle) ∈ G.L := fun k => by
      rw [(hσ k).1]; exact hmodel _
    rw [hKdef, ← G.tileValue_congr (D.tiles_congruent i)]
    exact (D.tile i).flux_grid_pm G hsq hi
  refine ⟨fun i => if (D.tile i).flux G.weight = K then 1 else -1, ?_, ?_⟩
  · intro i
    by_cases hi : (D.tile i).flux G.weight = K
    · simp only [if_pos hi]; push_cast; rw [one_mul, hi]
    · simp only [if_neg hi]; push_cast
      rcases htile i with h1 | h1
      · exact absurd h1 hi
      · rw [h1, neg_one_mul]
  · intro i
    by_cases hi : (D.tile i).flux G.weight = K
    · left; exact if_pos hi
    · right; exact if_neg hi

/-- **Beeson Lemma 28 and Def. 8 as printed** (UNAUDITED; PARTIAL only as described in the header).  Shapes are listed at
`A, B, C` (target vertices `0, 1, 2`); `M1 = sum eps1`, `M2 = sum eps2` (sums of the `Phi_1`, `Phi_2` tile signs anchored at
`AB`), `s = a/c`, `Lambda = circD target / circD model`; `kappa = (M1 + M2)/(M2 - M1)`. -/
theorem lemma28_printed2 (D : CongruentDissection N) {α β a b c : ℝ}
    (hδ : ¬ ∃ r : ℚ, α + β = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) (ε1 ε2 : Fin N → ℤ)
    (hε1 : SignsFor D (Phi1 D α ((delta_irr_iff hrel).mpr hδ)) ε1)
    (hε2 : SignsFor D (Phi2 D α ((delta_irr_iff hrel).mpr hδ)) ε2)
    (M1 M2 : ℤ) (hM1 : M1 = ∑ i, ε1 i) (hM2 : M2 = ∑ i, ε2 i) :
    -- triquadratic (2α, β, α+β): M1 = M2 (= Λ s), so κ is undefined
    ((D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = α + β) →
      M1 = M2 ∧ (M1 : ℝ) = (circD D.target / circD D.model) * (a / c)) ∧
    -- (β, 3α, β): κ = -s
    ((D.target.angleAt 0 = β ∧ D.target.angleAt 1 = 3 * α ∧ D.target.angleAt 2 = β) →
      (M2 : ℝ) - M1 ≠ 0 ∧ ((M1 : ℝ) + M2) / ((M2 : ℝ) - M1) = -(a / c)) ∧
    -- (α+β, α, α+β): κ = s
    ((D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + β) →
      (M2 : ℝ) - M1 ≠ 0 ∧ ((M1 : ℝ) + M2) / ((M2 : ℝ) - M1) = a / c) ∧
    -- (α, α+2β, α) and (2α, α, 2β): κ = s/(2-s²), 0 < κ < 1, s = κ(2-s²), quartic
    ((D.target.angleAt 0 = α ∧ D.target.angleAt 1 = α + 2 * β ∧ D.target.angleAt 2 = α) ∨
        (D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = 2 * β) →
      (M2 : ℝ) - M1 ≠ 0 ∧ ∀ κ : ℝ, κ = ((M1 : ℝ) + M2) / ((M2 : ℝ) - M1) →
        κ = (a / c) / (2 - (a / c) ^ 2) ∧ 0 < κ ∧ κ < 1 ∧ a / c = κ * (2 - (a / c) ^ 2) ∧
          κ ^ 2 * (a / c) ^ 4 - (4 * κ ^ 2 + 1) * (a / c) ^ 2 + 4 * κ ^ 2 = 0) := by
  have hα := (delta_irr_iff hrel).mpr hδ
  obtain ⟨hΛ, hs0, hs1⟩ := t4_aux D hrel h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ⟨e0, e1, e2⟩
    obtain ⟨v1, v2⟩ := val_tri D hα hrel h ε1 ε2 hε1 hε2 e0 e1 e2
    rw [← hM1] at v1; rw [← hM2] at v2
    exact ⟨by exact_mod_cast v1.trans v2.symm, v1⟩
  · intro ⟨e0, e1, e2⟩
    obtain ⟨v1, v2⟩ := val_beta3 D hα hrel h ε1 ε2 hε1 hε2 e0 e1 e2
    rw [← hM1] at v1; rw [← hM2] at v2
    exact kap_shape2 _ _ _ _ hΛ hs0 hs1 v1 v2
  · intro ⟨e0, e1, e2⟩
    obtain ⟨v1, v2⟩ := val_apb D hα hrel h ε1 ε2 hε1 hε2 e0 e1 e2
    rw [← hM1] at v1; rw [← hM2] at v2
    exact kap_shape3 _ _ _ _ hΛ hs0 hs1 v1 v2
  · intro e
    have key : (M2 : ℝ) - M1 ≠ 0 ∧ ((M1 : ℝ) + M2) / ((M2 : ℝ) - M1) = (a / c) / (2 - (a / c) ^ 2) := by
      rcases e with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩
      · obtain ⟨v1, v2⟩ := val_a2b D hα hrel h ε1 ε2 hε1 hε2 e0 e1 e2
        rw [← hM1] at v1; rw [← hM2] at v2
        exact kap_shape1 _ _ _ _ hΛ hs0 hs1 v1 v2
      · obtain ⟨v1, v2⟩ := val_2a2b D hα hrel h ε1 ε2 hε1 hε2 e0 e1 e2
        rw [← hM1] at v1; rw [← hM2] at v2
        exact kap_shape4 _ _ _ _ hΛ hs0 hs1 v1 v2
    refine ⟨key.1, fun κ hκ => ?_⟩
    have hk : κ = (a / c) / (2 - (a / c) ^ 2) := hκ.trans key.2
    obtain ⟨q0, q1, q2, q3⟩ := kappa_props _ _ hs0 hs1 hk
    exact ⟨hk, q0, q1, q2, q3⟩

/-- `M1` is blacks minus whites of the proper colouring `eps1`. -/
theorem M1_black_white (D : CongruentDissection N) (ε1 : Fin N → ℤ)
    (hc : D.toDissection.ProperColouring ε1) :
    ∑ i, ε1 i = ((Finset.univ.filter fun i => ε1 i = 1).card : ℤ)
      - ((Finset.univ.filter fun i => ε1 i = -1).card : ℤ) :=
  sum_eq_black_sub_white ε1 hc.1

end Erdos634.BeesonColoring

#print axioms Erdos634.BeesonColoring.exists_signs1
#print axioms Erdos634.BeesonColoring.exists_signs2
#print axioms Erdos634.BeesonColoring.lemma28_printed2
#print axioms Erdos634.BeesonColoring.M1_black_white
