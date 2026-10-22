-- Draft/FluxGRow3Step6Alg.lean — row 3 (AUDIT_ROWS), Proposition RP, Step 6 for GENERAL N:
-- the coefficient algebra, with no geometry. Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- Formalization debt on an already paper-level-PROVED result (row3 PROOF.md, Prop RP). Not /goal
-- progress.
--
-- Input (`hsum`): for every grid degree X, the Step-3 identity Σ_tiles C_X(t) = Φ_X(∂ABC), with
-- each tile's value in exactly the shape `Tri.flux_gauss_direct/_reflected` produce on the c = 1
-- convention (a = sin α, b = cos α), a tile off the grid contributing 0 (row3 PROOF.md Step 3,
-- last bullet), and the target's value in the shape `targetIso_flux_gauss` produces with BC at grid
-- degree (0, 0).
-- Output (`step6_quadratic`): λ² + sλ + t = 0 with s, t Gaussian integers — step7_even's exact
-- hypothesis shape. `step6_even` then fires step7_even.
--
-- Route: the paper divides a Laurent identity by c·z⁻¹(z − e^{iα}). Here the division is done
-- coefficientwise: with R_X := P_X − u·Q_{X−1} (u = e^{−iα}, v = e^{iα}) the identity reads
-- R_X − v·R_{X+1} = Φ_X; R vanishes far below (finitely many tiles), and Φ_X = 0 for X ≤ −2,
-- so upward induction gives R_{−1} = 0, then R_0 = λu, R_1 = −λ — the z⁰, z¹ coefficients of (★).
import Erdos634.Draft.FluxGRow3Weight

open scoped Classical

namespace Erdos634.Geometry.Row3.Step6

open _root_.Complex

/-! ## Gaussian integers inside ℂ -/

/-- `z ∈ ℤ[i]`. -/
def IsGI (z : ℂ) : Prop := ∃ a b : ℤ, z = (a : ℂ) + (b : ℂ) * I

theorem isGI_zero : IsGI 0 := ⟨0, 0, by simp⟩

theorem isGI_add {z w : ℂ} (hz : IsGI z) (hw : IsGI w) : IsGI (z + w) := by
  obtain ⟨a, b, rfl⟩ := hz; obtain ⟨c, d, rfl⟩ := hw
  exact ⟨a + c, b + d, by push_cast; ring⟩

theorem isGI_neg {z : ℂ} (hz : IsGI z) : IsGI (-z) := by
  obtain ⟨a, b, rfl⟩ := hz
  exact ⟨-a, -b, by push_cast; ring⟩

theorem isGI_sub {z w : ℂ} (hz : IsGI z) (hw : IsGI w) : IsGI (z - w) := by
  rw [sub_eq_add_neg]; exact isGI_add hz (isGI_neg hw)

theorem isGI_mul {z w : ℂ} (hz : IsGI z) (hw : IsGI w) : IsGI (z * w) := by
  obtain ⟨a, b, rfl⟩ := hz; obtain ⟨c, d, rfl⟩ := hw
  refine ⟨a * c - b * d, a * d + b * c, ?_⟩
  push_cast
  linear_combination ((b : ℂ) * (d : ℂ)) * I_mul_I

theorem isGI_I_zpow (n : ℤ) : IsGI (I ^ n) := by
  have h4 : (4 : ℤ) ∣ (n - n % 4) := ⟨n / 4, by omega⟩
  rw [Erdos634.Geometry.Row3.Complex.I_zpow_eq_of_mod4 h4]
  have hr : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hr with h | h | h | h <;> rw [h]
  · exact ⟨1, 0, by simp⟩
  · exact ⟨0, 1, by simp⟩
  · refine ⟨-1, 0, ?_⟩
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, I_sq]; simp
  · refine ⟨0, -1, ?_⟩
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, pow_succ, I_sq]; simp

theorem isGI_ite (p : Prop) [Decidable p] {z : ℂ} (hz : IsGI z) : IsGI (if p then z else 0) := by
  split
  · exact hz
  · exact isGI_zero

theorem isGI_sum {N : ℕ} (f : Fin N → ℂ) (hf : ∀ i, IsGI (f i)) : IsGI (∑ i, f i) :=
  Finset.sum_induction f IsGI (fun _ _ ha hb => isGI_add ha hb) isGI_zero (fun i _ => hf i)

/-! ## The data -/

/-- `v = e^{iα} = cos α + i sin α` (so `b + ia = c·v` at `c = 1`). -/
noncomputable def vv (α : ℝ) : ℂ := (Real.cos α : ℂ) + (Real.sin α : ℂ) * I

/-- `u = e^{−iα} = cos α − i sin α` (so `b − ia = c·u` at `c = 1`). -/
noncomputable def uu (α : ℝ) : ℂ := (Real.cos α : ℂ) - (Real.sin α : ℂ) * I

theorem vv_mul_uu (α : ℝ) : vv α * uu α = 1 := by
  unfold vv uu
  have h := Real.sin_sq_add_cos_sq α
  have h' : ((Real.sin α : ℂ)) ^ 2 + ((Real.cos α : ℂ)) ^ 2 = 1 := by exact_mod_cast h
  linear_combination h' - ((Real.sin α : ℂ) ^ 2) * I_mul_I

theorem vv_ne_zero (α : ℝ) : vv α ≠ 0 := by
  intro h; have := vv_mul_uu α; rw [h, zero_mul] at this; exact zero_ne_one this

/-- **One tile's value at grid degree `X`** (row3 PROOF.md Step 4, `c = 1`): `g` = "the hypotenuse is
on the grid", `r` = "reflected copy", `(k, j)` = the hypotenuse's grid degree. Direct:
`i^j([k=X] − (b − ia)[k+1=X])`; reflected: `i^j([k=X] − (b + ia)[k−1=X])`; off grid: `0`. -/
noncomputable def tileVal (α : ℝ) (g r : Prop) (k j X : ℤ) : ℂ :=
  if g then
    (if r then I ^ j * ((if k = X then 1 else 0) - (if k - 1 = X then vv α else 0))
     else I ^ j * ((if k = X then 1 else 0) - (if k + 1 = X then uu α else 0)))
  else 0

/-- **The target's value at grid degree `X`** (Step 5, BC at degree `(0,0)`, `c = 1`):
`2λ cos α [0 = X] − λ[−1 = X] − λ[1 = X]`. -/
noncomputable def bdryVal (α lam : ℝ) (X : ℤ) : ℂ :=
  (if (0 : ℤ) = X then (2 * lam * Real.cos α : ℂ) else 0)
    - (if (-1 : ℤ) = X then (lam : ℂ) else 0) - (if (1 : ℤ) = X then (lam : ℂ) else 0)

variable {N : ℕ}

/-- `P_X` = Σ `i^j` over reflected on-grid tiles of hypotenuse degree `X`. -/
noncomputable def PP (g r : Fin N → Prop) (k j : Fin N → ℤ) (X : ℤ) : ℂ :=
  ∑ i, if g i ∧ r i ∧ k i = X then I ^ j i else 0

/-- `Q_X` = Σ `i^j` over direct on-grid tiles of hypotenuse degree `X`. -/
noncomputable def QQ (g r : Fin N → Prop) (k j : Fin N → ℤ) (X : ℤ) : ℂ :=
  ∑ i, if g i ∧ ¬ r i ∧ k i = X then I ^ j i else 0

theorem tileVal_split (α : ℝ) (g r : Prop) (k j X : ℤ) :
    tileVal α g r k j X
      = (if g ∧ r ∧ k = X then I ^ j else 0) + (if g ∧ ¬ r ∧ k = X then I ^ j else 0)
        - vv α * (if g ∧ r ∧ k = X + 1 then I ^ j else 0)
        - uu α * (if g ∧ ¬ r ∧ k = X - 1 then I ^ j else 0) := by
  unfold tileVal
  by_cases hg : g
  · by_cases hr : r
    · simp only [hg, hr, true_and, not_true_eq_false, false_and, if_true, if_false]
      by_cases h1 : k = X
      · have h2 : ¬ k - 1 = X := by omega
        have h3 : ¬ k = X + 1 := by omega
        simp only [if_pos h1, if_neg h2, if_neg h3]; ring
      · by_cases h2 : k - 1 = X
        · have h3 : k = X + 1 := by omega
          simp only [if_neg h1, if_pos h2, if_pos h3]; ring
        · have h3 : ¬ k = X + 1 := by omega
          simp only [if_neg h1, if_neg h2, if_neg h3]; ring
    · simp only [hg, hr, true_and, not_false_eq_true, false_and, if_true, if_false]
      by_cases h1 : k = X
      · have h2 : ¬ k + 1 = X := by omega
        have h3 : ¬ k = X - 1 := by omega
        simp only [if_pos h1, if_neg h2, if_neg h3]; ring
      · by_cases h2 : k + 1 = X
        · have h3 : k = X - 1 := by omega
          simp only [if_neg h1, if_pos h2, if_pos h3]; ring
        · have h3 : ¬ k = X - 1 := by omega
          simp only [if_neg h1, if_neg h2, if_neg h3]; ring
  · simp only [hg, false_and, if_false]; ring

theorem sum_tileVal (α : ℝ) (g r : Fin N → Prop) (k j : Fin N → ℤ) (X : ℤ) :
    ∑ i, tileVal α (g i) (r i) (k i) (j i) X
      = PP g r k j X + QQ g r k j X - vv α * PP g r k j (X + 1) - uu α * QQ g r k j (X - 1) := by
  simp only [tileVal_split, PP, QQ, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.mul_sum]

/-- `R_X = P_X − u Q_{X−1}`: the coefficients of `P(z) − u z Q(z)`. -/
noncomputable def RR (α : ℝ) (g r : Fin N → Prop) (k j : Fin N → ℤ) (X : ℤ) : ℂ :=
  PP g r k j X - uu α * QQ g r k j (X - 1)

/-- **The divided identity, coefficientwise**: `R_X − v R_{X+1} = Φ_X`. -/
theorem RR_rec (α lam : ℝ) (g r : Fin N → Prop) (k j : Fin N → ℤ)
    (hsum : ∀ X, ∑ i, tileVal α (g i) (r i) (k i) (j i) X = bdryVal α lam X) (X : ℤ) :
    RR α g r k j X - vv α * RR α g r k j (X + 1) = bdryVal α lam X := by
  rw [← hsum X, sum_tileVal]
  unfold RR
  rw [show X + 1 - 1 = X by ring]
  linear_combination (QQ g r k j X) * vv_mul_uu α

theorem PP_eq_zero (g r : Fin N → Prop) (k j : Fin N → ℤ) (X : ℤ) (h : ∀ i, k i ≠ X) :
    PP g r k j X = 0 :=
  Finset.sum_eq_zero (fun i _ => by rw [if_neg (fun hc => h i hc.2.2)])

theorem QQ_eq_zero (g r : Fin N → Prop) (k j : Fin N → ℤ) (X : ℤ) (h : ∀ i, k i ≠ X) :
    QQ g r k j X = 0 :=
  Finset.sum_eq_zero (fun i _ => by rw [if_neg (fun hc => h i hc.2.2)])

theorem bdryVal_low (α lam : ℝ) (X : ℤ) (hX : X ≤ -2) : bdryVal α lam X = 0 := by
  unfold bdryVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; ring

/-- **Finite support from below ⇒ `R_{−1} = 0`.** -/
theorem RR_neg_one (α lam : ℝ) (g r : Fin N → Prop) (k j : Fin N → ℤ)
    (hsum : ∀ X, ∑ i, tileVal α (g i) (r i) (k i) (j i) X = bdryVal α lam X) :
    RR α g r k j (-1) = 0 := by
  set M : ℤ := ∑ i, |k i| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hkM : ∀ i, -M ≤ k i := by
    intro i
    have h1 : |k i| ≤ M := Finset.single_le_sum (f := fun i => |k i|)
      (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 := neg_abs_le (k i)
    linarith
  have hlow : ∀ X, X < -M → RR α g r k j X = 0 := by
    intro X hX
    unfold RR
    rw [PP_eq_zero g r k j X (fun i h => by have := hkM i; omega),
      QQ_eq_zero g r k j (X - 1) (fun i h => by have := hkM i; omega)]
    ring
  have key : ∀ n : ℕ, (n : ℤ) ≤ M + 1 → RR α g r k j (-M - 2 + n) = 0 := by
    intro n
    induction n with
    | zero => intro _; exact hlow _ (by push_cast; omega)
    | succ n ih =>
      intro hn
      have hprev := ih (by push_cast at hn ⊢; omega)
      have hrec := RR_rec α lam g r k j hsum (-M - 2 + n)
      rw [hprev, bdryVal_low α lam _ (by push_cast at hn; omega), zero_sub, neg_eq_zero] at hrec
      have := (mul_eq_zero.mp hrec).resolve_left (vv_ne_zero α)
      rw [show -M - 2 + ((n + 1 : ℕ) : ℤ) = -M - 2 + n + 1 by push_cast; ring]
      exact this
  have h := key (M + 1).toNat (by omega)
  rwa [show -M - 2 + ((M + 1).toNat : ℤ) = -1 by omega] at h

theorem RR_zero (α lam : ℝ) (g r : Fin N → Prop) (k j : Fin N → ℤ)
    (hsum : ∀ X, ∑ i, tileVal α (g i) (r i) (k i) (j i) X = bdryVal α lam X) :
    RR α g r k j 0 = uu α * lam := by
  have h := RR_rec α lam g r k j hsum (-1)
  rw [RR_neg_one α lam g r k j hsum, show (-1 : ℤ) + 1 = 0 by norm_num] at h
  have hb : bdryVal α lam (-1) = -(lam : ℂ) := by
    unfold bdryVal; rw [if_neg (by omega), if_pos rfl, if_neg (by omega)]; ring
  rw [hb] at h
  linear_combination (-(uu α)) * h - (RR α g r k j 0) * vv_mul_uu α

theorem RR_one (α lam : ℝ) (g r : Fin N → Prop) (k j : Fin N → ℤ)
    (hsum : ∀ X, ∑ i, tileVal α (g i) (r i) (k i) (j i) X = bdryVal α lam X) :
    RR α g r k j 1 = -(lam : ℂ) := by
  have h := RR_rec α lam g r k j hsum 0
  rw [RR_zero α lam g r k j hsum, show (0 : ℤ) + 1 = 1 by norm_num] at h
  have hb : bdryVal α lam 0 = (2 * lam * Real.cos α : ℂ) := by
    unfold bdryVal; rw [if_pos rfl, if_neg (by omega), if_neg (by omega)]; ring
  rw [hb] at h
  have hvu := vv_mul_uu α
  -- `u² − 2 cos α · u = −1`
  have hu : uu α * uu α - 2 * (Real.cos α : ℂ) * uu α = -1 := by
    unfold uu
    have h' : ((Real.sin α : ℂ)) ^ 2 + ((Real.cos α : ℂ)) ^ 2 = 1 := by
      exact_mod_cast Real.sin_sq_add_cos_sq α
    linear_combination (-1 : ℂ) * h' + ((Real.sin α : ℂ) ^ 2) * I_mul_I
  -- from `h`: `u·λ − v·R₁ = 2λ cos α`; multiply by `u`
  linear_combination (-(uu α)) * h - (RR α g r k j 1) * hvu + (lam : ℂ) * hu

/-- **Step 6 → Step 7's hypothesis.** From the per-degree identity, `λ² + sλ + t = 0` with
`s = P₁ + Q₋₁`, `t = P₁Q₋₁ − P₀Q₀` Gaussian integers, delivered in `step7_even`'s literal shape. -/
theorem step6_quadratic (α lam : ℝ) (g r : Fin N → Prop) (k j : Fin N → ℤ)
    (hsum : ∀ X, ∑ i, tileVal α (g i) (r i) (k i) (j i) X = bdryVal α lam X) :
    ∃ a b c d : ℤ, (lam : ℂ) ^ 2 + ((a : ℂ) + (b : ℂ) * I) * (lam : ℂ)
      + ((c : ℂ) + (d : ℂ) * I) = 0 := by
  have e1 := RR_one α lam g r k j hsum
  have e0 := RR_zero α lam g r k j hsum
  unfold RR at e1 e0
  rw [show (1 : ℤ) - 1 = 0 by norm_num] at e1
  rw [show (0 : ℤ) - 1 = -1 by norm_num] at e0
  set P1 := PP g r k j 1
  set P0 := PP g r k j 0
  set Q0 := QQ g r k j 0
  set Qm := QQ g r k j (-1)
  have hGI : ∀ X, IsGI (PP g r k j X) ∧ IsGI (QQ g r k j X) := fun X =>
    ⟨isGI_sum _ (fun i => isGI_ite _ (isGI_I_zpow _)),
     isGI_sum _ (fun i => isGI_ite _ (isGI_I_zpow _))⟩
  obtain ⟨a, b, hab⟩ : IsGI (P1 + Qm) := isGI_add (hGI 1).1 (hGI (-1)).2
  obtain ⟨c, d, hcd⟩ : IsGI (P1 * Qm - P0 * Q0) :=
    isGI_sub (isGI_mul (hGI 1).1 (hGI (-1)).2) (isGI_mul (hGI 0).1 (hGI 0).2)
  refine ⟨a, b, c, d, ?_⟩
  rw [← hab, ← hcd]
  linear_combination ((lam : ℂ) + Qm) * e1 - Q0 * e0

/-- **Step 6 + Step 7**: with `N = 2λ²` (Step 1), `N` is even. -/
theorem step6_even (N' : ℕ) (α lam : ℝ) (g r : Fin N → Prop) (k j : Fin N → ℤ)
    (hN : (N' : ℝ) = 2 * lam ^ 2)
    (hsum : ∀ X, ∑ i, tileVal α (g i) (r i) (k i) (j i) X = bdryVal α lam X) : Even N' := by
  obtain ⟨a, b, c, d, h⟩ := step6_quadratic α lam g r k j hsum
  exact Row3.step7_even N' a b c d lam hN h

end Erdos634.Geometry.Row3.Step6

#print axioms Erdos634.Geometry.Row3.Step6.RR_neg_one
#print axioms Erdos634.Geometry.Row3.Step6.step6_quadratic
#print axioms Erdos634.Geometry.Row3.Step6.step6_even
