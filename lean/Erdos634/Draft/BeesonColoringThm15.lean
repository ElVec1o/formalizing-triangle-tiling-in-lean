import Erdos634.Draft.BeesonColoringThm13

/-!
# Beeson (arXiv 1206.2229v4) Theorem 15, only-if part, thin wrapper

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Thm 15), Laczkovich (DCG 48 (2012)), Beeson-Zhang.
Follows from `BeesonColoring.thm13`; same project hypotheses (H1) `alpha not in Q * pi` (Beeson's Lemma 1 /
Laczkovich 5.1, 5.3 are not in Lean) and (H2) `M` is the flux integer (not shown equal to the Lemma 12
black-minus-white count); see the header of `BeesonColoringThm13.lean`.  Formalization debt.
-/

open scoped Classical

namespace Erdos634.BeesonColoring

open Erdos634.Geometry

variable {N : ℕ}

/-- **Beeson Theorem 15, only if** (UNAUDITED; (H1), (H2)).  `3 alpha + 2 beta = pi`; some triangle with angles
`(2 alpha, alpha, 2 beta)` is `N`-tiled by the tile `k (a, b, c)` with integers `a, b, c` and a scale `k > 0`
(Beeson: "scale the tile so that `(a, b, c)` are integers"; the coprimality of `(a, b, c)` is not needed and is not
assumed).  Then `s = 2 sin(alpha/2) = a/c` is rational, `b c = c^2 - a^2`, `c` divides `a^2`, and there is an
integer `M > 0` with `N (b + c - a)^2 = (b + c)(b + 2c) M^2`, i.e. `N = (b+c)(b+2c) (M/(b+c-a))^2`. -/
theorem thm15_only_if (D : CongruentDissection N) {α β k : ℝ} (a b c : ℤ) (hk : 0 < k)
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β (k * a) (k * b) (k * c))
    (hP0 : D.target.angleAt 0 = 2 * α) (hP1 : D.target.angleAt 1 = α)
    (hP2 : D.target.angleAt 2 = 2 * β) :
    0 < c ∧ (2 * Real.sin (α / 2) : ℝ) = (a : ℝ) / c ∧ b * c = c ^ 2 - a ^ 2 ∧ c ∣ a ^ 2 ∧
      ∃ M : ℤ, 0 < M ∧ (N : ℤ) * (b + c - a) ^ 2 = (b + c) * (b + 2 * c) * M ^ 2 := by
  obtain ⟨M, s, hM, hsac, hs2, hb, -, -, heq, -⟩ := thm13 D hα hrel h hP0 hP1 hP2
  obtain ⟨hcpos, -⟩ := model_a_eq hrel h
  have hc0 : (0 : ℝ) < c := by
    have : 0 < k * (c : ℝ) := hcpos
    exact pos_of_mul_pos_right this hk.le |>.trans_le' le_rfl
  have hcz : 0 < c := by exact_mod_cast hc0
  have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast hcz.ne'
  have hsq : s = (a : ℚ) / c := by
    have : (s : ℝ) = (a : ℝ) / c := by
      rw [hsac]; field_simp
    have h2 : ((s : ℚ) : ℝ) = (((a : ℚ) / c : ℚ) : ℝ) := by rw [this]; push_cast; rfl
    exact_mod_cast h2
  have hbc : b * c = c ^ 2 - a ^ 2 := by
    have e : (b : ℝ) * c = (c : ℝ) ^ 2 - (a : ℝ) ^ 2 := by
      have hb' : (b : ℝ) = (1 - (s : ℝ) ^ 2) * c := by
        exact mul_left_cancel₀ hk.ne' (by linear_combination hb)
      have hsr : (s : ℝ) * c = a := by rw [hsac]; field_simp
      rw [hb']
      linear_combination (-(s : ℝ) * c - a) * hsr
    exact_mod_cast e
  -- cleared equation in ℚ then ℤ
  have hL : (N : ℚ) * ((c - a) ^ 2 * (2 * c + a) ^ 2)
      = (c : ℚ) ^ 4 * ((N : ℚ) * ((1 - s) ^ 2 * (2 + s) ^ 2)) := by
    rw [hsq]; field_simp
  have hR : (M : ℚ) ^ 2 * ((2 * c ^ 2 - a ^ 2) * (3 * c ^ 2 - a ^ 2))
      = (c : ℚ) ^ 4 * ((M : ℚ) ^ 2 * ((2 - s ^ 2) * (3 - s ^ 2))) := by
    rw [hsq]; field_simp
  have E1q : (N : ℚ) * ((c - a) ^ 2 * (2 * c + a) ^ 2)
      = (M : ℚ) ^ 2 * ((2 * c ^ 2 - a ^ 2) * (3 * c ^ 2 - a ^ 2)) := by
    rw [hL, hR, heq]
  have E1 : (N : ℤ) * ((c - a) ^ 2 * (2 * c + a) ^ 2)
      = M ^ 2 * ((2 * c ^ 2 - a ^ 2) * (3 * c ^ 2 - a ^ 2)) := by exact_mod_cast E1q
  have key : ((N : ℤ) * (b + c - a) ^ 2 - (b + c) * (b + 2 * c) * M ^ 2) * c ^ 2 = 0 := by
    linear_combination E1 + ((N : ℤ) * (b * c + (c ^ 2 - a ^ 2) + 2 * c ^ 2 - 2 * a * c)
      - M ^ 2 * (b * c + (c ^ 2 - a ^ 2) + 3 * c ^ 2)) * hbc
  have hfin := (mul_eq_zero.mp key).resolve_right (pow_ne_zero 2 hcz.ne')
  refine ⟨hcz, ?_, hbc, ⟨c - b, by linear_combination hbc⟩, M, hM, sub_eq_zero.mp hfin⟩
  rw [← hs2, hsac]; field_simp

end Erdos634.BeesonColoring

#print axioms Erdos634.BeesonColoring.thm15_only_if
