-- Draft/G3HRows.lean — G3H (UNAUDITED). No sorry/native_decide. Formalization debt, not /goal progress.
-- LITERAL instantiations of
--   * `Rows11_13AnyLabel.Row11.rational_any_label`   (D3 / row 11, any N)
--   * `Rows11_13AnyLabel.Row11.prime_excluded_any_label` (D5 / row 11 at prime N): every hypothesis except `N.Prime` is
--     discharged on the REAL 84-tiling (`R84TilingBridge.dissection`), and `¬ Nat.Prime 84`; the prime-free variant
--     of the literal statement is REFUTED (`¬ (∀ N D ..., False)`),
--   * `Rows11_13AnyLabel.Row13.rational_any_label`   (row 13) on the REAL 48-tiling of the atom A_4 (G3CAtomTilingBridge),
-- with the conclusions evaluated to the concrete rational r = 1/2.
import Erdos634.Draft.G3CS3Control
import Erdos634.Draft.G3CAtomControl
import Erdos634.Draft.Rows11_13AnyLabel

open scoped Classical

namespace Erdos634.Draft.G3HRows

open Erdos634.Geometry Erdos634.Z15Real Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.FluxGridWitness (α44 β44 α44_irr three_α_two_β)

/-! ## Row 11 (D3), literal, on the real N = 84 tiling -/

/-- `Row11.rational_any_label`, applied verbatim to the real 84-tiling (base angles alpha at target vertices 0 and 1). -/
theorem row11_rational_84 :
    ∃ r : ℚ, (16 : ℝ) = (r : ℝ) * 32 ∧ (24 : ℝ) = (1 - (r : ℝ) ^ 2) * 32 :=
  Row11.rational_any_label G3CS3Control.D α44_irr three_α_two_β G3CS3Control.data
    (show (0 : Fin 3) ≠ 1 by decide) G3CS3Control.target_angle0 G3CS3Control.target_angle1

/-- The rational is forced to be 1/2: the conclusion is non-trivially instantiated (a = c/2, b = 3c/4). -/
theorem row11_rational_84_half : ((1 / 2 : ℚ) : ℝ) * 32 = 16 ∧ (1 - ((1 / 2 : ℚ) : ℝ) ^ 2) * 32 = 24 := by
  constructor <;> norm_num

theorem row11_r_eq_half :
    ∀ r : ℚ, (16 : ℝ) = (r : ℝ) * 32 → r = 1 / 2 := by
  intro r h
  have : (r : ℝ) = ((1 / 2 : ℚ) : ℝ) := by push_cast; linarith
  exact_mod_cast this

theorem not_prime_84 : ¬ Nat.Prime R84Tiling.tiles.length := by
  rw [G3CS3Control.len84]; decide

/-- The literal statement of `Row11.prime_excluded_any_label`, as a predicate on `N`. -/
def D5Stmt (N : ℕ) : Prop :=
  ∀ (D : CongruentDissection N) {α β a b c : ℝ},
    (¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) → 3 * α + 2 * β = Real.pi →
    D.model.ThreeAlphaData α β a b c → ∀ {t₀ t₁ : Fin 3}, t₀ ≠ t₁ →
    D.target.angleAt t₀ = α → D.target.angleAt t₁ = α → N.Prime → False

/-- The same statement with the primality hypothesis deleted. -/
def D5StmtPrimeFree (N : ℕ) : Prop :=
  ∀ (D : CongruentDissection N) {α β a b c : ℝ},
    (¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) → 3 * α + 2 * β = Real.pi →
    D.model.ThreeAlphaData α β a b c → ∀ {t₀ t₁ : Fin 3}, t₀ ≠ t₁ →
    D.target.angleAt t₀ = α → D.target.angleAt t₁ = α → False

/-- Sanity: the headline is literally `D5Stmt N` for every `N`. -/
theorem d5Stmt_all (N : ℕ) : D5Stmt N := by
  intro D α β a b c hα hrel h t₀ t₁ ht hP0 hP1 hN
  exact Row11.prime_excluded_any_label D hα hrel h ht hP0 hP1 hN

/-- **All structural premises of D5 hold jointly on a real dissection; only primality fails.** -/
theorem d5_premises_84 :
    ∃ (D : CongruentDissection R84Tiling.tiles.length) (α β a b c : ℝ) (t₀ t₁ : Fin 3),
      (¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) ∧ 3 * α + 2 * β = Real.pi ∧
      D.model.ThreeAlphaData α β a b c ∧ t₀ ≠ t₁ ∧
      D.target.angleAt t₀ = α ∧ D.target.angleAt t₁ = α ∧ ¬ Nat.Prime R84Tiling.tiles.length :=
  ⟨G3CS3Control.D, α44, β44, _, _, _, 0, 1, α44_irr, three_α_two_β, G3CS3Control.data, by decide,
    G3CS3Control.target_angle0, G3CS3Control.target_angle1, not_prime_84⟩

/-- **Literal ¬Leaf control**: the prime-free variant of D5 is FALSE at the real tiling's N = 84. -/
theorem not_d5PrimeFree_84 : ¬ D5StmtPrimeFree R84Tiling.tiles.length := fun h =>
  h G3CS3Control.D α44_irr three_α_two_β G3CS3Control.data (t₀ := 0) (t₁ := 1) (by decide)
    G3CS3Control.target_angle0 G3CS3Control.target_angle1

/-- and hence the all-N prime-free variant is false. -/
theorem not_d5PrimeFree_all : ¬ ∀ N, D5StmtPrimeFree N := fun h => not_d5PrimeFree_84 (h _)

/-! ## Row 13 (base angles alpha+beta), literal, on the real N = 48 atom tiling -/

theorem len48 : G3CAtomTiling.tiles.length = 48 := by decide

/-- `Row13.rational_any_label`, applied verbatim to the real 48-tiling of the atom A_4:
target angles `(alpha+beta, alpha+beta, alpha)`; base angles at vertices 0 and 1. -/
theorem row13_rational_48 :
    ∃ r : ℚ, (16 : ℝ) = (r : ℝ) * 32 ∧ (24 : ℝ) = (1 - (r : ℝ) ^ 2) * 32 :=
  Row13.rational_any_label G3CAtomControl.D α44_irr three_α_two_β G3CAtomControl.threeAlpha
    (show (0 : Fin 3) ≠ 1 by decide) G3CAtomControl.t_angle0 G3CAtomControl.t_angle1

theorem row13_r_eq_half :
    ∃ r : ℚ, r = 1 / 2 ∧ (16 : ℝ) = (r : ℝ) * 32 ∧ (24 : ℝ) = (1 - (r : ℝ) ^ 2) * 32 := by
  obtain ⟨r, h1, h2⟩ := row13_rational_48
  exact ⟨r, row11_r_eq_half r h1, h1, h2⟩

/-- Row 13 with the other vertex pair (1, 2 is NOT a base pair: angles alpha+beta and alpha): the premise
`t₀ ≠ t₁` with both angles `alpha+beta` is only met by `{0,1}`; here is the control that the pair `(0,2)` fails
(`alpha + beta ≠ alpha`), so the instantiation above is not label-trivial. -/
theorem row13_pair_02_fails : G3CAtomControl.D.target.angleAt 0 ≠ G3CAtomControl.D.target.angleAt 2 := by
  intro h
  rw [G3CAtomControl.t_angle0, G3CAtomControl.t_angle2] at h
  have : 0 < β44 := by
    have := G3CAtomControl.D.model.angleAt_pos' 1
    rw [G3CAtomControl.model_angle1] at this; exact this
  linarith

end Erdos634.Draft.G3HRows

#print axioms Erdos634.Draft.G3HRows.row11_rational_84
#print axioms Erdos634.Draft.G3HRows.d5Stmt_all
#print axioms Erdos634.Draft.G3HRows.d5_premises_84
#print axioms Erdos634.Draft.G3HRows.not_d5PrimeFree_84
#print axioms Erdos634.Draft.G3HRows.not_d5PrimeFree_all
#print axioms Erdos634.Draft.G3HRows.row13_rational_48
#print axioms Erdos634.Draft.G3HRows.row13_r_eq_half
#print axioms Erdos634.Draft.G3HRows.row13_pair_02_fails
