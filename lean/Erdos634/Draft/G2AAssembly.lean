/-
Draft/G2AAssembly.lean — `γ = 2α` base-α target, SQUAREFREE `N`: no tiling (Beeson [Iso Thm 11.7], squarefree case).
Atoms: A1 `FluxDRow4SqfreeArith.leg_words_gen` (exists); A2 `Row4.sqfree_legs` (this file: `P5` ⇒ `N = M M'`, `gcd(M,M') = 1`,
`k = (M'−M)/2`, `m = (M'+M)/2`, `k c = m a`, `k² b = N a`, every leg word has `q ∈ {0, k}`); A3 `Row4.L8_nob` (G2AGeo3, no `b` on either leg);
the `b^k` leg is `Row4.bk_leg`.  A4 here: `Row4.not_squarefree` and the any-label `caseG_of_squarefree`.
UNAUDITED.  CONDITIONAL AT THE GEOMETRIC LEVEL exactly as `Row4.not_prime` (no Lean witness tiling of this target).
No sorry, no native_decide.
-/
import Erdos634.Draft.G2AGeo3
import Erdos634.Draft.FluxDRow4SqfreeArith
import Erdos634.Draft.FluxDRow4M1AnyLabel
import Erdos634.Draft.CompositeFinal9

open scoped Classical

namespace Erdos634.Geometry

variable {N : ℕ}

/-- **A2.**  For squarefree `N`: every leg word `X = p a + q b + r c` has `q = k, p = r = 0` or `q = 0`, with `k ≥ 2`. -/
theorem Row4.sqfree_legs (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    (hA : D.target.angleAt 0 = α) (hC : D.target.angleAt 1 = α) (hsq : Squarefree N) :
    ∃ k : ℕ, 2 ≤ k ∧ ∀ p q r : ℕ, D.target.oppLen 0 = p * a + q * b + r * c →
      (q = k ∧ p = 0 ∧ r = 0) ∨ q = 0 := by
  obtain ⟨κ, -, -, ha, -, -, -, -, hX1⟩ := Row4.sides D h hA hC
  obtain ⟨M, M', hM0, hM'0, hM, hM', hNM, hM2, hM'2, hlt, -, -, hab⟩ := Row4.P5 D hα h hA hC
  lift M to ℕ using hM0.le
  lift M' to ℕ using hM'0.le
  have hNn : N = M * M' := by exact_mod_cast hNM
  push_cast at hM hM'
  have hcop : Nat.Coprime M M' := (Nat.squarefree_mul_iff.mp (hNn ▸ hsq)).1
  have hMpos : 0 < M := by exact_mod_cast hM0
  have hlt' : 3 * M < M' := by exact_mod_cast hlt
  obtain ⟨k, hk⟩ : ∃ k, M' = M + 2 * k := ⟨(M' - M) / 2, by
    have h1 : (2 : ℤ) ∣ (M : ℤ) - N := hM2
    have h2 : (2 : ℤ) ∣ (M' : ℤ) - N := hM'2
    omega⟩
  have hk2 : 2 ≤ k := by omega
  refine ⟨k, hk2, fun p q r hw => ?_⟩
  set X := D.target.oppLen 0 with hXdef
  have hkR : (M' : ℝ) = M + 2 * k := by exact_mod_cast hk
  have hNR : (N : ℝ) = M * M' := by exact_mod_cast hNn
  -- `k c = (M + k) a`
  have hkc : (k : ℝ) * c = (M + k) * a := by
    have : 2 * ((k : ℝ) * c - (M + k) * a) = 0 := by
      linear_combination hM' - hM - (c - a) * hkR
    linarith
  -- `k² b = N a`
  have hkb : (k : ℝ) ^ 2 * b = N * a := by
    have e : a * ((k : ℝ) ^ 2 * b - N * a) = 0 := by
      rw [hNR, hkR]
      linear_combination (k : ℝ) ^ 2 * hab + ((k : ℝ) * c + (M + k) * a) * hkc
    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left ha.ne')
  -- `k X = N a`
  have hkX : (k : ℝ) * X = N * a := by
    rw [hNR, hkR]
    linear_combination (k : ℝ) * (-hM) + (M : ℝ) * hkc
  -- the word equation over `ℕ`
  have hword : (M * M') * k = p * k ^ 2 + q * (M * M') + r * k * (M + k) := by
    have e : a * (((N : ℝ)) * k - (p * (k : ℝ) ^ 2 + q * N + r * k * (M + k))) = 0 := by
      linear_combination (-(k : ℝ)) * hkX + (k : ℝ) ^ 2 * hw + (q : ℝ) * hkb + (r : ℝ) * k * hkc
    have e2 := sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left ha.ne')
    rw [hNR] at e2
    exact_mod_cast e2
  have := Erdos634.Draft.FluxDRow4SqfreeArith.leg_words_gen M M' k (M + k) hMpos hcop hlt'
    (by omega) (by omega) p q r hword
  rcases this with h1 | ⟨h1, -⟩
  · exact Or.inl h1
  · exact Or.inr h1

end Erdos634.Geometry
