-- Draft/FluxDRow12a.lean — ROW 12(a) COMPLETE (rationality/rationality_proofs.md §4 (a) and (a′); P0
-- table: "12(a) | (β, β, 3α) | N ≥ M² | §4 (a), (a′) | no Thm 2"): on the base-β target, if Theorem 1's
-- colouring number satisfies `M² ≤ N`, the tile is rational.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- * `M² < N` (`q > 1`): `Row12.case_a` (Draft/FluxDRow12b) — the base's s-coordinate is negative.
-- * `M² = N` (`q = 1`, (a′)): the tiling quadratic becomes `s² + s − 1 = 0`; with `s = 2 sin(α/2)`
--   (law of sines) this is `4u² + 2u − 1 = 0`, `u = sin(α/2)`, which `sin(π/10)` also solves
--   (`golden_sin`, from Mathlib's `Real.cos_pi_div_five`); both positive, so `α/2 = π/10`,
--   `α = π/5 ∈ ℚπ` — contradicting (B).
-- Witnesses: `case_a` is applied on the real 44- and 99-tilings (Draft/FluxDRow12bWitness); `golden_sin`
-- and `golden_alpha` are exercised at `α = π/5` itself (`golden_alpha_witness`), where the hypothesis
-- holds — so the (a′) branch is not vacuous as algebra.  No real tiling with `N = M²` is known.
--
-- Formalization debt; not progress on the three /goal outcomes.
import Erdos634.Draft.FluxDRow12b

open scoped Classical

namespace Erdos634.Geometry

variable {N : ℕ}

/-- `w = sin(π/10)` solves `4w² + 2w − 1 = 0`. -/
theorem golden_sin : 4 * Real.sin (Real.pi / 10) ^ 2 + 2 * Real.sin (Real.pi / 10) - 1 = 0 := by
  have hw : Real.sin (Real.pi / 10) = 2 * Real.cos (Real.pi / 5) ^ 2 - 1 := by
    rw [← Real.cos_pi_div_two_sub, show Real.pi / 2 - Real.pi / 10 = 2 * (Real.pi / 5) by ring,
      Real.cos_two_mul]
  have h5 : √(5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  rw [hw, Real.cos_pi_div_five]
  linear_combination ((√(5 : ℝ)) ^ 2 + 4 * √(5 : ℝ) - 1) / 16 * h5

/-- **(a′)'s trigonometry**: if `u = sin(α/2)` with `0 < α < π` solves `4u² + 2u − 1 = 0`, then
`α = π/5`. -/
theorem golden_alpha {α : ℝ} (h0 : 0 < α) (h1 : α < Real.pi)
    (hq : 4 * Real.sin (α / 2) ^ 2 + 2 * Real.sin (α / 2) - 1 = 0) : α = Real.pi / 5 := by
  have hπ := Real.pi_pos
  have hu : 0 < Real.sin (α / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hw : 0 < Real.sin (Real.pi / 10) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  have hg := golden_sin
  have e : (Real.sin (α / 2) - Real.sin (Real.pi / 10))
      * (4 * (Real.sin (α / 2) + Real.sin (Real.pi / 10)) + 2) = 0 := by
    linear_combination hq - hg
  have heq : Real.sin (α / 2) = Real.sin (Real.pi / 10) :=
    sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_right (by linarith))
  have h2 : α / 2 = Real.pi / 10 :=
    Real.injOn_sin ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ heq
  linarith

/-- The (a′) branch is not vacuous as algebra: at `α = π/5` the hypothesis of `golden_alpha` holds. -/
theorem golden_alpha_witness :
    4 * Real.sin (Real.pi / 5 / 2) ^ 2 + 2 * Real.sin (Real.pi / 5 / 2) - 1 = 0 := by
  rw [show Real.pi / 5 / 2 = Real.pi / 10 by ring]; exact golden_sin

/-- **ROW 12(a), complete** (§4 (a) + (a′)): Theorem 1's colouring number `M` exists, and if
`M² ≤ N` the tile is rational. -/
theorem Row12.case_a_full (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hP0 : D.target.angleAt 0 = β) (hP1 : D.target.angleAt 1 = β) :
    ∃ M : ℤ, 0 < M ∧ (M : ℝ) * (a + b + c) = D.target.oppLen 2 + 2 * D.target.oppLen 0 ∧
      (M ^ 2 ≤ N → ∃ r : ℚ, a = (r : ℝ) * c) := by
  obtain ⟨s, M, hs0, hs1, hc, ha, hb, -, -, hM0, hMid, hleg, hY, hq⟩ :=
    Row12.setup D hα hrel h hP0 hP1
  refine ⟨M, hM0, hMid, fun hle => ?_⟩
  by_contra hrat
  have hirr : ¬ ∃ r : ℚ, s = r := fun ⟨r, hr⟩ => hrat ⟨r, by rw [ha, hr]⟩
  rcases lt_or_eq_of_le hle with hlt | heq
  · -- (a): `q > 1`, the base's s-coordinate is negative
    obtain ⟨-, ma, mb, mc, hw2⟩ := Row12.words D h hc ha hb hleg hY
    have hB := Row12.base_coeff hirr hs0 hq hw2
    have h1 : 0 ≤ M * (N + M ^ 2) * ma :=
      mul_nonneg (mul_nonneg hM0.le (by positivity)) (Nat.cast_nonneg ma)
    have h2 : 0 ≤ 2 * M * N * mb :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM0.le) (Nat.cast_nonneg N)) (Nat.cast_nonneg mb)
    have h3 : (N : ℤ) * (M ^ 2 - N) < 0 := by
      have hN0 : (0 : ℤ) < N := lt_of_le_of_lt (sq_nonneg M) hlt
      exact mul_neg_of_pos_of_neg hN0 (by linarith)
    linarith
  · -- (a′): `q = 1`, `s² + s − 1 = 0`, so `α = π/5`
    have hNM : (N : ℝ) = (M : ℝ) ^ 2 := by exact_mod_cast heq.symm
    have hM0' : (0 : ℝ) < M := by exact_mod_cast hM0
    have hgold : s ^ 2 + s - 1 = 0 := by
      have e : 2 * (M : ℝ) ^ 2 * (s ^ 2 + s - 1) = 0 := by
        rw [hNM] at hq; linear_combination hq
      exact (mul_eq_zero.mp e).resolve_left (mul_pos two_pos (pow_pos hM0' 2)).ne'
    -- `s = 2 sin(α/2)` (law of sines, as in `Row12.sides`)
    obtain ⟨σ, h0, o0, h1', -, h2, o2⟩ := h
    obtain ⟨tγ, tα, -, -⟩ := threeAlpha_sin_table hrel
    have ls1 := D.model.lawSin (σ 0) (σ 2)
    rw [h0, o2, h2, o0, tα, tγ] at ls1
    have hαpos : 0 < α := h0 ▸ D.model.angleAt_pos' (σ 0)
    have hβpos : 0 < β := h1' ▸ D.model.angleAt_pos' (σ 1)
    have hπ := Real.pi_pos
    have hco : 0 < Real.cos (α / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    have ha2 : a = 2 * Real.sin (α / 2) * c :=
      mul_left_cancel₀ hco.ne' (by linear_combination (-1 : ℝ) * ls1)
    have hs2 : s = 2 * Real.sin (α / 2) := by
      have : c * (s - 2 * Real.sin (α / 2)) = 0 := by rw [ha] at ha2; linear_combination ha2
      linarith [(mul_eq_zero.mp this).resolve_left hc.ne']
    rw [hs2] at hgold
    have hπ5 := golden_alpha hαpos (by linarith) (by linear_combination hgold)
    exact hα ⟨1 / 5, by rw [hπ5]; push_cast; ring⟩

end Erdos634.Geometry

#print axioms Erdos634.Geometry.golden_sin
#print axioms Erdos634.Geometry.golden_alpha
#print axioms Erdos634.Geometry.golden_alpha_witness
#print axioms Erdos634.Geometry.Row12.case_a_full
