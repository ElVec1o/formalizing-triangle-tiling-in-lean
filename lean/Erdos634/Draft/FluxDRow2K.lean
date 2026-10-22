-- Draft/FluxDRow2K.lean — ROW 2, LEMMA K ((private working notes, not included) §5 "Lemma K (the tile
-- lives in Q(√p))"): from equation (1) `D v = μ v` (`D ∈ M₃(ℤ≥0)`, `μ ∉ ℚ`, `μ² = p ∈ ℤ`), the ratios
-- `a/c, b/c` and the cosines of the three angles lie in `ℚ(μ)`, and not all of `a/c, b/c` are rational
-- (so `dim_ℚ (ℚa + ℚb + ℚc) = 2`).  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- ROUTE (differs from the file's; named): the file argues "μV ⊆ V and μ² ∈ ℚ make V a `ℚ(√p)`-space,
-- so `dim_ℚ V` is even".  Here, elementarily: `v` is orthogonal to the rows of `M = D − μI`; some
-- principal `2 × 2` minor of `M` is nonzero (their sum is `3μ² − 2Tμ + S = 2p − 2Tμ`, using `S = −p`
-- from `det M = 0`, and `μ ∉ ℚ`); so the cross product `c` of the corresponding two rows is nonzero, `v`
-- is parallel to `c`, and `c` has entries in `ℤ + ℤμ` — hence `v_a/v_c = c_a/c_c ∈ ℚ(μ)`.  The
-- conclusion is the file's (its "in particular" clause and `dim V = 2`).
--
-- * `Row2.QMu μ z` : `z ∈ ℚ + ℚμ`, closed under `+ − ·` and `⁻¹` (`μ ∉ ℚ`, `μ² ∈ ℤ`).
-- * `Row2.lemmaK` (pure algebra), `Row2.lemmaK_cos` (the three cosine expressions),
-- * `Row2.lemmaK_tiling`: on a real tile-similar tiling with `N` not a square and a scalene model
--   (through S1 `Row2.sideCount_eigen` and S3 `Row2.mu_irrational`, Draft/FluxDRow2S1), the model's
--   `a/c`, `b/c` and `cos` of its three angles lie in `ℚ(√N)`.
-- Witness (Draft/FluxDRow2KWitness.lean): `lemmaK` on the `(1, 2, √7)` survivor (`a/c = √7/7`).
-- Lemmas Q, E, R are not started (Q needs algebraic-integer conjugates; R the ordered side word).
--
-- Formalization debt; not progress on the three /goal outcomes.
import Erdos634.Draft.FluxDRow2S1
import Erdos634.Draft.FluxCRow5

open scoped Classical

namespace Erdos634.Geometry

variable {N : ℕ}

/-! ## `ℚ(μ)` as a predicate -/

/-- `z ∈ ℚ + ℚ·μ`. -/
def Row2.QMu (μ z : ℝ) : Prop := ∃ q₁ q₂ : ℚ, z = q₁ + q₂ * μ

theorem Row2.QMu.rat (μ : ℝ) (q : ℚ) : Row2.QMu μ q := ⟨q, 0, by simp⟩

theorem Row2.QMu.nat (μ : ℝ) (n : ℕ) : Row2.QMu μ n := ⟨n, 0, by simp⟩

theorem Row2.QMu.mu (μ : ℝ) : Row2.QMu μ μ := ⟨0, 1, by simp⟩

theorem Row2.QMu.add {μ z w : ℝ} (hz : Row2.QMu μ z) (hw : Row2.QMu μ w) : Row2.QMu μ (z + w) := by
  obtain ⟨a, b, rfl⟩ := hz
  obtain ⟨c, d, rfl⟩ := hw
  exact ⟨a + c, b + d, by push_cast; ring⟩

theorem Row2.QMu.sub {μ z w : ℝ} (hz : Row2.QMu μ z) (hw : Row2.QMu μ w) : Row2.QMu μ (z - w) := by
  obtain ⟨a, b, rfl⟩ := hz
  obtain ⟨c, d, rfl⟩ := hw
  exact ⟨a - c, b - d, by push_cast; ring⟩

theorem Row2.QMu.mul {μ z w : ℝ} {p : ℤ} (hp : μ ^ 2 = p) (hz : Row2.QMu μ z)
    (hw : Row2.QMu μ w) : Row2.QMu μ (z * w) := by
  obtain ⟨a, b, rfl⟩ := hz
  obtain ⟨c, d, rfl⟩ := hw
  exact ⟨a * c + b * d * p, a * d + b * c, by push_cast; linear_combination ((b : ℝ) * d) * hp⟩

theorem Row2.QMu.inv {μ z : ℝ} {p : ℤ} (hμ : ¬ ∃ r : ℚ, μ = r) (hp : μ ^ 2 = p)
    (hz : Row2.QMu μ z) : Row2.QMu μ z⁻¹ := by
  obtain ⟨a, b, rfl⟩ := hz
  by_cases h0 : (a : ℝ) + b * μ = 0
  · rw [h0, inv_zero]; exact ⟨0, 0, by simp⟩
  have hn : (a : ℝ) ^ 2 - p * b ^ 2 ≠ 0 := by
    intro hn
    have e : ((a : ℝ) + b * μ) * ((a : ℝ) - b * μ) = 0 := by linear_combination hn - (b : ℝ) ^ 2 * hp
    have e2 := (mul_eq_zero.mp e).resolve_left h0
    by_cases hb : b = 0
    · subst hb; apply h0; simp at e2 ⊢; exact_mod_cast e2
    · apply hμ
      refine ⟨a / b, ?_⟩
      have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
      push_cast
      rw [eq_div_iff hb']
      linarith
  have hnq : ((a ^ 2 - p * b ^ 2 : ℚ) : ℝ) ≠ 0 := by push_cast; exact hn
  have hnq0 : (a ^ 2 - p * b ^ 2 : ℚ) ≠ 0 := fun h => hnq (by rw [h, Rat.cast_zero])
  have hprod : ((a : ℝ) + b * μ) * ((a : ℝ) - b * μ) = ((a ^ 2 - p * b ^ 2 : ℚ) : ℝ) := by
    push_cast; linear_combination (-(b : ℝ) ^ 2) * hp
  have hinv : ((a : ℝ) + b * μ)⁻¹ = ((a : ℝ) - b * μ) * (((1 / (a ^ 2 - p * b ^ 2)) : ℚ) : ℝ) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc, hprod, ← Rat.cast_mul, mul_one_div_cancel hnq0, Rat.cast_one]
  rw [hinv]
  exact ((Row2.QMu.rat μ a).sub ((Row2.QMu.rat μ b).mul hp (Row2.QMu.mu μ))).mul hp
    (Row2.QMu.rat μ _)

theorem Row2.QMu.div {μ z w : ℝ} {p : ℤ} (hμ : ¬ ∃ r : ℚ, μ = r) (hp : μ ^ 2 = p)
    (hz : Row2.QMu μ z) (hw : Row2.QMu μ w) : Row2.QMu μ (z / w) := by
  rw [div_eq_mul_inv]; exact hz.mul hp (hw.inv hμ hp)

/-! ## Parallel to a cross product -/

/-- `v ⊥ r`, `v ⊥ s` make `v` parallel to `r × s` (componentwise `v_a c_b = v_b c_a`). -/
theorem Row2.par_cross {r₀ r₁ r₂ s₀ s₁ s₂ v₀ v₁ v₂ : ℝ}
    (hr : r₀ * v₀ + r₁ * v₁ + r₂ * v₂ = 0) (hs : s₀ * v₀ + s₁ * v₁ + s₂ * v₂ = 0) :
    v₀ * (r₂ * s₀ - r₀ * s₂) = v₁ * (r₁ * s₂ - r₂ * s₁) ∧
    v₀ * (r₀ * s₁ - r₁ * s₀) = v₂ * (r₁ * s₂ - r₂ * s₁) ∧
    v₁ * (r₀ * s₁ - r₁ * s₀) = v₂ * (r₂ * s₀ - r₀ * s₂) :=
  ⟨by linear_combination r₂ * hs - s₂ * hr, by linear_combination s₁ * hr - r₁ * hs,
    by linear_combination r₀ * hs - s₀ * hr⟩

/-- From `v ∥ c` with `v > 0` and `c ≠ 0`: `c₂ ≠ 0`, `v₀ = (c₀/c₂) v₂`, `v₁ = (c₁/c₂) v₂`. -/
theorem Row2.ratio_of_par {c₀ c₁ c₂ v₀ v₁ v₂ : ℝ} (hv₂ : 0 < v₂)
    (h01 : v₀ * c₁ = v₁ * c₀) (h02 : v₀ * c₂ = v₂ * c₀) (h12 : v₁ * c₂ = v₂ * c₁)
    (hc : c₀ ≠ 0 ∨ c₁ ≠ 0 ∨ c₂ ≠ 0) : c₂ ≠ 0 ∧ v₀ / v₂ = c₀ / c₂ ∧ v₁ / v₂ = c₁ / c₂ := by
  have hc₂ : c₂ ≠ 0 := by
    intro h
    rw [h, mul_zero] at h02 h12
    have e0 : c₀ = 0 := (mul_eq_zero.mp h02.symm).resolve_left hv₂.ne'
    have e1 : c₁ = 0 := (mul_eq_zero.mp h12.symm).resolve_left hv₂.ne'
    rcases hc with h' | h' | h'
    · exact h' e0
    · exact h' e1
    · exact h' h
  refine ⟨hc₂, ?_, ?_⟩
  · rw [div_eq_div_iff hv₂.ne' hc₂]; linarith
  · rw [div_eq_div_iff hv₂.ne' hc₂]; linarith

/-! ## Lemma K -/

/-- **LEMMA K (row 2), pure algebra.**  `D ∈ M₃(ℤ≥0)`, `D v = μ v`, `v > 0`, `μ ∉ ℚ`, `μ² = p ∈ ℤ`:
`v₀/v₂, v₁/v₂ ∈ ℚ(μ)`, and they are not both rational. -/
theorem Row2.lemmaK (D : Fin 3 → Fin 3 → ℕ) (v : Fin 3 → ℝ) (hv : ∀ i, 0 < v i) {μ : ℝ}
    (hμ : ¬ ∃ r : ℚ, μ = r) {p : ℤ} (hp : μ ^ 2 = p)
    (hDv : ∀ i, ∑ j, (D i j : ℝ) * v j = μ * v i) :
    Row2.QMu μ (v 0 / v 2) ∧ Row2.QMu μ (v 1 / v 2) ∧
      ¬ ((∃ r : ℚ, v 0 = r * v 2) ∧ (∃ r : ℚ, v 1 = r * v 2)) := by
  have E0 := hDv 0
  have E1 := hDv 1
  have E2 := hDv 2
  rw [Fin.sum_univ_three] at E0 E1 E2
  -- rows of `M = D − μI`, as `r·v = 0`
  have R0 : ((D 0 0 : ℝ) - μ) * v 0 + (D 0 1 : ℝ) * v 1 + (D 0 2 : ℝ) * v 2 = 0 := by
    linear_combination E0
  have R1 : (D 1 0 : ℝ) * v 0 + ((D 1 1 : ℝ) - μ) * v 1 + (D 1 2 : ℝ) * v 2 = 0 := by
    linear_combination E1
  have R2 : (D 2 0 : ℝ) * v 0 + (D 2 1 : ℝ) * v 1 + ((D 2 2 : ℝ) - μ) * v 2 = 0 := by
    linear_combination E2
  -- entries of `M` lie in `ℚ(μ)`
  have q := fun (i j : Fin 3) => Row2.QMu.nat μ (D i j)
  have qd := fun (i : Fin 3) => (Row2.QMu.nat μ (D i i)).sub (Row2.QMu.mu μ)
  -- `det M = 0`, hence `S = −p`
  have hdet : (((D 0 0 : ℝ) - μ) * (((D 1 1 : ℝ) - μ) * ((D 2 2 : ℝ) - μ) - (D 1 2 : ℝ) * D 2 1)
      - (D 0 1 : ℝ) * ((D 1 0 : ℝ) * ((D 2 2 : ℝ) - μ) - (D 1 2 : ℝ) * D 2 0)
      + (D 0 2 : ℝ) * ((D 1 0 : ℝ) * D 2 1 - ((D 1 1 : ℝ) - μ) * D 2 0)) * v 2 = 0 := by
    linear_combination ((D 1 0 : ℝ) * D 2 1 - ((D 1 1 : ℝ) - μ) * D 2 0) * R0
      - (((D 0 0 : ℝ) - μ) * D 2 1 - (D 0 1 : ℝ) * D 2 0) * R1
      + (((D 0 0 : ℝ) - μ) * ((D 1 1 : ℝ) - μ) - (D 0 1 : ℝ) * D 1 0) * R2
  have hdet' := (mul_eq_zero.mp hdet).resolve_right (hv 2).ne'
  have e : (((-p - ((D 0 0 : ℤ) * D 1 1 + (D 0 0 : ℤ) * D 2 2 + (D 1 1 : ℤ) * D 2 2
        - (D 1 2 : ℤ) * D 2 1 - (D 0 1 : ℤ) * D 1 0 - (D 0 2 : ℤ) * D 2 0)) : ℤ) : ℝ) * μ
      + ((((D 0 0 : ℤ) + D 1 1 + D 2 2) * p
        + ((D 0 0 : ℤ) * D 1 1 * D 2 2 - (D 0 0 : ℤ) * D 1 2 * D 2 1 - (D 0 1 : ℤ) * D 1 0 * D 2 2
          + (D 0 1 : ℤ) * D 1 2 * D 2 0 + (D 0 2 : ℤ) * D 1 0 * D 2 1
          - (D 0 2 : ℤ) * D 1 1 * D 2 0) : ℤ) : ℝ) = 0 := by
    push_cast
    linear_combination hdet' + (μ - ((D 0 0 : ℝ) + D 1 1 + D 2 2)) * hp
  obtain ⟨hS, -⟩ := irr_coord_eq_zero hμ e
  have hS' := congrArg (fun z : ℤ => (z : ℝ)) hS
  push_cast at hS'
  -- some principal minor of `M` is nonzero
  have hminor : ((D 1 1 : ℝ) - μ) * ((D 2 2 : ℝ) - μ) - (D 1 2 : ℝ) * D 2 1 ≠ 0 ∨
      (D 0 2 : ℝ) * D 2 0 - ((D 0 0 : ℝ) - μ) * ((D 2 2 : ℝ) - μ) ≠ 0 ∨
      ((D 0 0 : ℝ) - μ) * ((D 1 1 : ℝ) - μ) - (D 0 1 : ℝ) * D 1 0 ≠ 0 := by
    by_contra hall
    push Not at hall
    obtain ⟨h12, h02, h01⟩ := hall
    have e2 : (((-2 * ((D 0 0 : ℤ) + D 1 1 + D 2 2)) : ℤ) : ℝ) * μ + (((2 * p) : ℤ) : ℝ) = 0 := by
      push_cast
      linear_combination h12 - h02 + h01 - 3 * hp + hS'
    obtain ⟨hT, hp0⟩ := irr_coord_eq_zero hμ e2
    have hp00 : p = 0 := by omega
    rw [hp00, Int.cast_zero] at hp
    have hμ0 : μ = 0 := (pow_eq_zero_iff two_ne_zero).mp hp
    exact hμ ⟨0, by rw [hμ0]; simp⟩
  -- the cross products; `v` is parallel to a nonzero one with entries in `ℤ + ℤμ`
  rcases hminor with hm | hm | hm
  · -- rows 1, 2: `c = r₁ × r₂`, `c₀ = P₁₂ ≠ 0`
    obtain ⟨h01, h02, h12⟩ := Row2.par_cross R1 R2
    obtain ⟨-, k0, k1⟩ := Row2.ratio_of_par (hv 2) h01 h02 h12 (Or.inl hm)
    refine ⟨?_, ?_, ?_⟩
    · rw [k0]
      exact (((qd 1).mul hp (qd 2)).sub ((q 1 2).mul hp (q 2 1))).div hμ hp
        (((q 1 0).mul hp (q 2 1)).sub ((qd 1).mul hp (q 2 0)))
    · rw [k1]
      exact (((q 1 2).mul hp (q 2 0)).sub ((q 1 0).mul hp (qd 2))).div hμ hp
        (((q 1 0).mul hp (q 2 1)).sub ((qd 1).mul hp (q 2 0)))
    · rintro ⟨⟨r₀, hr₀⟩, ⟨r₁, hr₁⟩⟩
      apply hμ
      refine ⟨(D 2 0 : ℚ) * r₀ + (D 2 1 : ℚ) * r₁ + (D 2 2 : ℚ), ?_⟩
      have : v 2 * ((D 2 0 : ℝ) * r₀ + (D 2 1 : ℝ) * r₁ + (D 2 2 : ℝ) - μ) = 0 := by
        rw [hr₀, hr₁] at R2; linear_combination R2
      have := (mul_eq_zero.mp this).resolve_left (hv 2).ne'
      push_cast; linarith
  · -- rows 0, 2: `c = r₀ × r₂`, `c₁ = −P₀₂ ≠ 0`
    obtain ⟨h01, h02, h12⟩ := Row2.par_cross R0 R2
    obtain ⟨-, k0, k1⟩ := Row2.ratio_of_par (hv 2) h01 h02 h12 (Or.inr (Or.inl hm))
    refine ⟨?_, ?_, ?_⟩
    · rw [k0]
      exact (((q 0 1).mul hp (qd 2)).sub ((q 0 2).mul hp (q 2 1))).div hμ hp
        (((qd 0).mul hp (q 2 1)).sub ((q 0 1).mul hp (q 2 0)))
    · rw [k1]
      exact (((q 0 2).mul hp (q 2 0)).sub ((qd 0).mul hp (qd 2))).div hμ hp
        (((qd 0).mul hp (q 2 1)).sub ((q 0 1).mul hp (q 2 0)))
    · rintro ⟨⟨r₀, hr₀⟩, ⟨r₁, hr₁⟩⟩
      apply hμ
      refine ⟨(D 2 0 : ℚ) * r₀ + (D 2 1 : ℚ) * r₁ + (D 2 2 : ℚ), ?_⟩
      have : v 2 * ((D 2 0 : ℝ) * r₀ + (D 2 1 : ℝ) * r₁ + (D 2 2 : ℝ) - μ) = 0 := by
        rw [hr₀, hr₁] at R2; linear_combination R2
      have := (mul_eq_zero.mp this).resolve_left (hv 2).ne'
      push_cast; linarith
  · -- rows 0, 1: `c = r₀ × r₁`, `c₂ = P₀₁ ≠ 0`
    obtain ⟨h01, h02, h12⟩ := Row2.par_cross R0 R1
    obtain ⟨-, k0, k1⟩ := Row2.ratio_of_par (hv 2) h01 h02 h12 (Or.inr (Or.inr hm))
    refine ⟨?_, ?_, ?_⟩
    · rw [k0]
      exact (((q 0 1).mul hp (q 1 2)).sub ((q 0 2).mul hp (qd 1))).div hμ hp
        (((qd 0).mul hp (qd 1)).sub ((q 0 1).mul hp (q 1 0)))
    · rw [k1]
      exact (((q 0 2).mul hp (q 1 0)).sub ((qd 0).mul hp (q 1 2))).div hμ hp
        (((qd 0).mul hp (qd 1)).sub ((q 0 1).mul hp (q 1 0)))
    · rintro ⟨⟨r₀, hr₀⟩, ⟨r₁, hr₁⟩⟩
      apply hμ
      refine ⟨(D 2 0 : ℚ) * r₀ + (D 2 1 : ℚ) * r₁ + (D 2 2 : ℚ), ?_⟩
      have : v 2 * ((D 2 0 : ℝ) * r₀ + (D 2 1 : ℝ) * r₁ + (D 2 2 : ℝ) - μ) = 0 := by
        rw [hr₀, hr₁] at R2; linear_combination R2
      have := (mul_eq_zero.mp this).resolve_left (hv 2).ne'
      push_cast; linarith

/-- **Lemma K, the cosines**: `(b² + c² − a²)/(2bc)`, `(c² + a² − b²)/(2ca)`, `(a² + b² − c²)/(2ab)`
lie in `ℚ(μ)` (`(a, b, c) = (v₀, v₁, v₂)`). -/
theorem Row2.lemmaK_cos (D : Fin 3 → Fin 3 → ℕ) (v : Fin 3 → ℝ) (hv : ∀ i, 0 < v i) {μ : ℝ}
    (hμ : ¬ ∃ r : ℚ, μ = r) {p : ℤ} (hp : μ ^ 2 = p)
    (hDv : ∀ i, ∑ j, (D i j : ℝ) * v j = μ * v i) :
    Row2.QMu μ ((v 1 ^ 2 + v 2 ^ 2 - v 0 ^ 2) / (2 * v 1 * v 2)) ∧
    Row2.QMu μ ((v 2 ^ 2 + v 0 ^ 2 - v 1 ^ 2) / (2 * v 2 * v 0)) ∧
    Row2.QMu μ ((v 0 ^ 2 + v 1 ^ 2 - v 2 ^ 2) / (2 * v 0 * v 1)) := by
  obtain ⟨h0, h1, -⟩ := Row2.lemmaK D v hv hμ hp hDv
  set t₀ := v 0 / v 2 with ht₀
  set t₁ := v 1 / v 2 with ht₁
  have hv2 := (hv 2).ne'
  have e₀ : v 0 = t₀ * v 2 := by rw [ht₀, div_mul_cancel₀ _ hv2]
  have e₁ : v 1 = t₁ * v 2 := by rw [ht₁, div_mul_cancel₀ _ hv2]
  have one : Row2.QMu μ 1 := by simpa using Row2.QMu.nat μ 1
  have two : Row2.QMu μ 2 := by simpa using Row2.QMu.nat μ 2
  have ht0 : t₀ ≠ 0 := div_ne_zero (hv 0).ne' hv2
  have ht1 : t₁ ≠ 0 := div_ne_zero (hv 1).ne' hv2
  refine ⟨?_, ?_, ?_⟩
  · have : (v 1 ^ 2 + v 2 ^ 2 - v 0 ^ 2) / (2 * v 1 * v 2) = (t₁ * t₁ + 1 - t₀ * t₀) / (2 * t₁) := by
      rw [e₀, e₁]; field_simp
    rw [this]
    exact (((h1.mul hp h1).add one).sub (h0.mul hp h0)).div hμ hp (two.mul hp h1)
  · have : (v 2 ^ 2 + v 0 ^ 2 - v 1 ^ 2) / (2 * v 2 * v 0) = (1 + t₀ * t₀ - t₁ * t₁) / (2 * t₀) := by
      rw [e₀, e₁]; field_simp
    rw [this]
    exact ((one.add (h0.mul hp h0)).sub (h1.mul hp h1)).div hμ hp (two.mul hp h0)
  · have : (v 0 ^ 2 + v 1 ^ 2 - v 2 ^ 2) / (2 * v 0 * v 1)
        = (t₀ * t₀ + t₁ * t₁ - 1) / (2 * t₀ * t₁) := by
      rw [e₀, e₁]; field_simp
    rw [this]
    exact (((h0.mul hp h0).add (h1.mul hp h1)).sub one).div hμ hp ((two.mul hp h0).mul hp h1)

/-- **Lemma K on a real tiling**: an `N`-tiling (`N` not a square) of a target similar to a scalene
model with ratio `μ` has `a/c`, `b/c` and the cosines of the model's three angles in `ℚ(μ)`,
`μ = √N`; and `a/c`, `b/c` are not both rational. -/
theorem Row2.lemmaK_tiling (D : CongruentDissection N) (μ : ℝ)
    (hside : ∀ k, D.target.oppLen k = μ * D.model.oppLen k)
    (hscal : ∀ k k', k ≠ k' → D.model.oppLen k ≠ D.model.oppLen k') (hN : ¬ IsSquare N) :
    μ ^ 2 = N ∧ Row2.QMu μ (D.model.oppLen 0 / D.model.oppLen 2) ∧
      Row2.QMu μ (D.model.oppLen 1 / D.model.oppLen 2) ∧
      ¬ ((∃ r : ℚ, D.model.oppLen 0 = r * D.model.oppLen 2) ∧
        (∃ r : ℚ, D.model.oppLen 1 = r * D.model.oppLen 2)) ∧
      ∀ k, Row2.QMu μ (Real.cos (D.model.angleAt k)) := by
  obtain ⟨hμ, hp⟩ := Row2.mu_irrational D μ hside hN
  have hDv := Row2.sideCount_eigen D μ hside hscal
  obtain ⟨k0, k1, knot⟩ := Row2.lemmaK D.sideCount D.model.oppLen D.model.oppLen_pos hμ hp hDv
  obtain ⟨c0, c1, c2⟩ := Row2.lemmaK_cos D.sideCount D.model.oppLen D.model.oppLen_pos hμ hp hDv
  refine ⟨by exact_mod_cast hp, k0, k1, knot, fun k => ?_⟩
  have hpos := D.model.oppLen_pos
  have hcos : ∀ k, Real.cos (D.model.angleAt k)
      = (D.model.oppLen (k + 1) ^ 2 + D.model.oppLen (k + 2) ^ 2 - D.model.oppLen k ^ 2)
        / (2 * D.model.oppLen (k + 1) * D.model.oppLen (k + 2)) := by
    intro k
    have hl := D.model.lawCos k
    have hne : 2 * D.model.oppLen (k + 1) * D.model.oppLen (k + 2) ≠ 0 :=
      (mul_pos (mul_pos two_pos (hpos _)) (hpos _)).ne'
    rw [eq_div_iff hne]
    linarith
  rw [hcos k]
  fin_cases k
  · exact c0
  · exact c1
  · exact c2

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row2.QMu.inv
#print axioms Erdos634.Geometry.Row2.par_cross
#print axioms Erdos634.Geometry.Row2.ratio_of_par
#print axioms Erdos634.Geometry.Row2.lemmaK
#print axioms Erdos634.Geometry.Row2.lemmaK_cos
#print axioms Erdos634.Geometry.Row2.lemmaK_tiling
