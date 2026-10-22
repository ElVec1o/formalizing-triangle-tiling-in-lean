import Erdos634.Draft.BeesonL28d1

/-!
# Beeson (arXiv 1206.2229v4) Lemma 28, step 3b: the PRINTED `M1 = sum (-1)^eps`, `M2 = sum (-1)^{n+eps}`

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Def. 6, Lemmas 19-23, Thm 3, Thm 4, Lemma 28), Laczkovich
(DCG 48 (2012)), Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.

Closes the PARTIAL gap of `BeesonL28c3` (flux sign vs printed `(-1)^{n+eps}`), under the single named hypothesis
`AnchorCoset` (Beeson Lemma 19) for the existence of `(n_i, eps_i)`; the sign identities themselves hold for ANY
`(k_i, n_i, eps_i)` describing the `alpha`-opposite edge of tile `i` as `anchor + n delta + eps pi`
(`eps2_printed`, `eps1_printed`), with no hypothesis beyond `3 alpha + 2 beta = pi`, `alpha notin Q pi`.
-/

open scoped Classical

namespace Erdos634.BeesonColoring

open Erdos634.Geometry Erdos634.Geometry.A1Field

variable {N : ℕ}

theorem zsign' (j : ℤ) : (if (j : ZMod 2) = 0 then (1 : ℝ) else -1) = (-1 : ℝ) ^ j := by
  have := zsign j
  simpa using this

theorem angle_rep {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (n e : ℤ) :
    (n : ℝ) * (α + β) + (e : ℝ) * Real.pi
      = ((n + e : ℤ) : ℝ) * Real.pi + ((-n : ℤ) : ℝ) * (α / 2 + Real.pi / 2) := by
  have hβ : β = (Real.pi - 3 * α) / 2 := by linarith
  rw [hβ]; push_cast; ring

theorem exists_ne {α β : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (anc x : Real.Angle) (hx : x ∈ (chiAt α hα 0 anc).L) :
    ∃ n e : ℤ, x = (((n : ℝ) * (α + β) + (e : ℝ) * Real.pi : ℝ) : Real.Angle) := by
  obtain ⟨⟨j, k⟩, hjk⟩ := AddMonoidHom.mem_range.mp hx
  refine ⟨-k, j + k, ?_⟩
  rw [angle_rep hrel, ← hjk, rank2Map_apply]
  congr 1
  push_cast; ring_nf

section signs

variable {α β a b c : ℝ}

theorem tv_plus_ne (D : CongruentDissection N) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hrel : 3 * α + 2 * β = Real.pi) (h : D.model.ThreeAlphaData α β a b c) (anc : Real.Angle) :
    (chiAt α hα 0 anc).tileValue D.model ≠ 0 := by
  rw [chiAt_tileValue]
  have := threeAlpha_tileValue_plus D.model hα hrel h
  unfold chiPlus at this
  rw [this]
  obtain ⟨s, hs0, hs1, hc, ha, hb, -⟩ := ctx D hrel h
  rw [ha, hb]
  nlinarith [mul_pos hc hs0, mul_pos hc (sub_pos.mpr hs1), mul_pos (mul_pos hc hs0) (sub_pos.mpr hs1)]

theorem tv_minus_ne (D : CongruentDissection N) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hrel : 3 * α + 2 * β = Real.pi) (h : D.model.ThreeAlphaData α β a b c) (anc : Real.Angle) :
    (chiAt α hα 1 anc).tileValue D.model ≠ 0 := by
  rw [chiAt_tileValue]
  have := threeAlpha_tileValue_minus D.model hα hrel h
  unfold chiMinus at this
  rw [this]
  obtain ⟨ha, hb, hc, -, -⟩ := model_abc_pos h
  positivity

/-- **`eps2_i = (-1)^{n+eps}`**, for every tile (reflected or not): `n, eps` the printed coordinates of the edge
opposite a vertex of angle `alpha`. -/
theorem eps2_printed (D : CongruentDissection N) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hrel : 3 * α + 2 * β = Real.pi) (h : D.model.ThreeAlphaData α β a b c)
    (ε2 : Fin N → ℤ) (hε2 : SignsFor D (Phi2 D α hα) ε2) (i : Fin N) (k : Fin 3)
    (hk : (D.tile i).angleAt (k + 2) = α) (n e : ℤ)
    (hdir : ((D.tile i).leftUnit k).angle
      = (D.target.leftUnit 0).angle + (((n : ℝ) * (α + β) + (e : ℝ) * Real.pi : ℝ) : Real.Angle)) :
    (ε2 i : ℝ) = (-1 : ℝ) ^ (n + e) := by
  have h1 := eps_eq_edgeWeight D hα hrel h 0 (D.target.leftUnit 0).angle
    (tv_plus_ne D hα hrel h _) ε2 hε2 i k hk
  rw [h1]
  have hmem : ((D.tile i).leftUnit k).angle - (chiAt α hα 0 (D.target.leftUnit 0).angle).anchor
      ∈ (chiAt α hα 0 (D.target.leftUnit 0).angle).L := by
    rw [chiAt_anchor, hdir, add_sub_cancel_left, angle_rep hrel]; exact chiAt_mem _ _ _ _ _ _
  rw [weight_of_coset _ _ hmem, chiAt_anchor, hdir, add_sub_cancel_left, angle_rep hrel, chiAt_chi,
    zero_mul, add_zero, zsign']

/-- **`eps1_i = (-1)^{eps}`** (the colouring). -/
theorem eps1_printed (D : CongruentDissection N) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hrel : 3 * α + 2 * β = Real.pi) (h : D.model.ThreeAlphaData α β a b c)
    (ε1 : Fin N → ℤ) (hε1 : SignsFor D (Phi1 D α hα) ε1) (i : Fin N) (k : Fin 3)
    (hk : (D.tile i).angleAt (k + 2) = α) (n e : ℤ)
    (hdir : ((D.tile i).leftUnit k).angle
      = (D.target.leftUnit 0).angle + (((n : ℝ) * (α + β) + (e : ℝ) * Real.pi : ℝ) : Real.Angle)) :
    (ε1 i : ℝ) = (-1 : ℝ) ^ e := by
  have h1 := eps_eq_edgeWeight D hα hrel h 1 (D.target.leftUnit 0).angle
    (tv_minus_ne D hα hrel h _) ε1 hε1 i k hk
  rw [h1]
  have hmem : ((D.tile i).leftUnit k).angle - (chiAt α hα 1 (D.target.leftUnit 0).angle).anchor
      ∈ (chiAt α hα 1 (D.target.leftUnit 0).angle).L := by
    rw [chiAt_anchor, hdir, add_sub_cancel_left, angle_rep hrel]; exact chiAt_mem _ _ _ _ _ _
  rw [weight_of_coset _ _ hmem, chiAt_anchor, hdir, add_sub_cancel_left, angle_rep hrel, chiAt_chi,
    show ((n + e : ℤ) : ZMod 2) + 1 * ((-n : ℤ) : ZMod 2) = (e : ZMod 2) by push_cast; ring, zsign']

/-- Every tile has a vertex with angle `alpha`: an edge `k` with `angleAt (k+2) = alpha`. -/
theorem exists_aedge (D : CongruentDissection N) (h : D.model.ThreeAlphaData α β a b c) (i : Fin N) :
    ∃ k : Fin 3, (D.tile i).angleAt (k + 2) = α := by
  obtain ⟨σ, hσ⟩ := (D.tiles_congruent i).exists_perm
  obtain ⟨τ, h0, -⟩ := h
  refine ⟨σ.symm (τ 0) + 1, ?_⟩
  have : ∀ v : Fin 3, v + 1 + 2 = v := by decide
  rw [this, (hσ _).1, Equiv.apply_symm_apply, h0]

/-- Under `AnchorCoset` (Beeson Lemma 19) the printed data `(k_i, n_i, eps_i)` exist for every tile. -/
theorem exists_printed (D : CongruentDissection N) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hrel : 3 * α + 2 * β = Real.pi) (h : D.model.ThreeAlphaData α β a b c)
    (hc : AnchorCoset D α hα) :
    ∀ i : Fin N, ∃ (k : Fin 3) (n e : ℤ), (D.tile i).angleAt (k + 2) = α ∧
      ((D.tile i).leftUnit k).angle
        = (D.target.leftUnit 0).angle + (((n : ℝ) * (α + β) + (e : ℝ) * Real.pi : ℝ) : Real.Angle) := by
  intro i
  obtain ⟨k, hk⟩ := exists_aedge D h i
  obtain ⟨n, e, hne⟩ := exists_ne hα hrel _ _ (hc i k)
  exact ⟨k, n, e, hk, by rw [← hne]; abel⟩

/-- **The printed sums.**  For printed data `(k_i, n_i, eps_i)`: `sum eps1 = sum (-1)^{eps_i}`,
`sum eps2 = sum (-1)^{n_i+eps_i}`. -/
theorem printed_sums (D : CongruentDissection N) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hrel : 3 * α + 2 * β = Real.pi) (h : D.model.ThreeAlphaData α β a b c)
    (ε1 ε2 : Fin N → ℤ) (hε1 : SignsFor D (Phi1 D α hα) ε1) (hε2 : SignsFor D (Phi2 D α hα) ε2)
    (k : Fin N → Fin 3) (n e : Fin N → ℤ)
    (hk : ∀ i, (D.tile i).angleAt (k i + 2) = α)
    (hdir : ∀ i, ((D.tile i).leftUnit (k i)).angle
      = (D.target.leftUnit 0).angle + (((n i : ℝ) * (α + β) + (e i : ℝ) * Real.pi : ℝ) : Real.Angle)) :
    (((∑ i, ε1 i : ℤ)) : ℝ) = ∑ i, (-1 : ℝ) ^ (e i) ∧
      (((∑ i, ε2 i : ℤ)) : ℝ) = ∑ i, (-1 : ℝ) ^ (n i + e i) := by
  constructor
  · push_cast
    exact Finset.sum_congr rfl fun i _ =>
      eps1_printed D hα hrel h ε1 hε1 i (k i) (hk i) (n i) (e i) (hdir i)
  · push_cast
    exact Finset.sum_congr rfl fun i _ =>
      eps2_printed D hα hrel h ε2 hε2 i (k i) (hk i) (n i) (e i) (hdir i)

end signs

/-- **Lemma 28 with the PRINTED `M1 = sum (-1)^{eps_j}`, `M2 = sum (-1)^{n_j+eps_j}`** (Thm 3), for printed data
`(k_j, n_j, eps_j)` of the tiles (these exist under `AnchorCoset`, `exists_printed`).  Same conclusion as
`lemma28_printed2`. -/
theorem lemma28_printed3 (D : CongruentDissection N) {α β a b c : ℝ}
    (hδ : ¬ ∃ r : ℚ, α + β = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (k : Fin N → Fin 3) (n e : Fin N → ℤ)
    (hk : ∀ i, (D.tile i).angleAt (k i + 2) = α)
    (hdir : ∀ i, ((D.tile i).leftUnit (k i)).angle
      = (D.target.leftUnit 0).angle + (((n i : ℝ) * (α + β) + (e i : ℝ) * Real.pi : ℝ) : Real.Angle))
    (M1 M2 : ℤ) (hM1 : (M1 : ℝ) = ∑ i, (-1 : ℝ) ^ (e i))
    (hM2 : (M2 : ℝ) = ∑ i, (-1 : ℝ) ^ (n i + e i)) :
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
  obtain ⟨ε1, hε1, -⟩ := exists_signs1 D hα hrel h
  obtain ⟨ε2, hε2, -⟩ := exists_signs2 D hα hrel h
  obtain ⟨s1, s2⟩ := printed_sums D hα hrel h ε1 ε2 hε1 hε2 k n e hk hdir
  exact lemma28_printed2 D hδ hrel h ε1 ε2 hε1 hε2 M1 M2
    (by exact_mod_cast hM1.trans s1.symm) (by exact_mod_cast hM2.trans s2.symm)



end Erdos634.BeesonColoring

#print axioms Erdos634.BeesonColoring.eps2_printed
#print axioms Erdos634.BeesonColoring.eps1_printed
#print axioms Erdos634.BeesonColoring.exists_printed
#print axioms Erdos634.BeesonColoring.lemma28_printed3
