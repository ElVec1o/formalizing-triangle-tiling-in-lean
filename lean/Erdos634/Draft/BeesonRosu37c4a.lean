import Mathlib
import Erdos634.Draft.BeesonRosu37c3

/-!
# Beeson-Rosu Theorem 37, gap (1), part 2: reusable lemmas for the corner tile

NOTE, UNAUDITED.  Credit: Michael Beeson and Rosu (arXiv 2607.23453 v2, Theorem 37), Beeson, Laczkovich.  Formalization debt.

* `counts_sums`: `SetupG`'s chain counts with the SUMS `sum cA`, `sum cB`, `sum cC` explicit (the proof of `BeesonRosu37b1.counts_gen`, not its existential).
* `no_A_of_sum_zero`: `sum cA = 0` => no letter `A1`, `A2` in the chain.
* `seg_inter`: two sides of a triangle through a common vertex `j` (the segments `[i, j]` and `[l, j]`) meet only at `j`.
-/

open scoped Classical
set_option linter.unusedVariables false

namespace Erdos634.BeesonRosu37c4a

open Erdos634.Geometry Erdos634.Draft.FDBBaseBetaE1 Erdos634.Draft.SideRunG Erdos634.Draft.SideRunGA
  Erdos634.Draft.SideRun Erdos634.Draft.W2E1 Erdos634.BaseBetaTargetCoord Erdos634.TilePlacement Erdos634.Geometry.Dissection

variable {N : ℕ}

/-- `counts_gen` with the sums explicit -/
theorem counts_sums {e f : ℕ} {α β γ L ax ay : ℝ} {D : CongruentDissection N} {c : ℕ} {X : ℕ → ℝ} {tile : ℕ → Fin N}
    {τ : ℕ → Ty} (S : SetupG D e f α β γ L ax ay) (Ch : ChainG D e f L c X tile τ) :
    ((∑ k ∈ Finset.range c, (τ k).cA : ℕ) : ℝ) * ((e : ℝ) * f) + ((∑ k ∈ Finset.range c, (τ k).cB : ℕ) : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)
      + ((∑ k ∈ Finset.range c, (τ k).cC : ℕ) : ℝ) * (f : ℝ) ^ 2 = L ∧
      ((∃ i, i + f ≤ c ∧ ((∀ j, j < f → τ (i + j) = Ty.C1) ∨ (∀ j, j < f → τ (i + j) = Ty.C2))) →
        f ≤ ∑ k ∈ Finset.range c, (τ k).cC) := by
  have hsub : (((f ^ 2 - e ^ 2 : ℕ)) : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rw [Nat.cast_sub (Nat.pow_le_pow_left S.hef.le 2)]; push_cast; ring
  have hN : ∑ k ∈ Finset.range c, lenN e f (τ k)
      = (∑ k ∈ Finset.range c, (τ k).cA) * (e * f) + (∑ k ∈ Finset.range c, (τ k).cB) * (f ^ 2 - e ^ 2)
        + (∑ k ∈ Finset.range c, (τ k).cC) * f ^ 2 := by
    simp only [lenN, Finset.sum_add_distrib, Finset.sum_mul]
  have h1 : ∀ k ∈ Finset.range c, (τ k).lenG (e : ℝ) (f : ℝ) = X (k + 1) - X k := by
    intro k hk
    rw [Ch.hstep k (Finset.mem_range.mp hk)]; ring
  have h2 : L = ∑ k ∈ Finset.range c, (τ k).lenG (e : ℝ) (f : ℝ) := by
    rw [Finset.sum_congr rfl h1, Finset.sum_range_sub, Ch.hXm, Ch.hX0, sub_zero]
  have h3 : ∑ k ∈ Finset.range c, (τ k).lenG (e : ℝ) (f : ℝ)
      = ((∑ k ∈ Finset.range c, lenN e f (τ k) : ℕ) : ℝ) := by
    rw [Nat.cast_sum]; exact Finset.sum_congr rfl (fun k _ => lenG_cast S.hef (τ k))
  refine ⟨?_, ?_⟩
  · rw [h2, h3, hN]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, hsub]
  · rintro ⟨i, him, hrun⟩
    exact Erdos634.Draft.SideRun.cC_run τ i f c him hrun

/-- no letter `A1`, `A2` when `sum cA = 0` -/
theorem no_A_of_sum_zero {c : ℕ} {τ : ℕ → Ty} (h : ∑ k ∈ Finset.range c, (τ k).cA = 0) {k : ℕ} (hk : k < c) :
    (τ k).cA = 0 := (Finset.sum_eq_zero_iff.mp h) k (Finset.mem_range.mpr hk)

/-- **two sides of a triangle through a vertex meet only there**: the points `lineMap (pts i) (pts j) s` and `lineMap (pts l) (pts j) s'`
coincide only for `s = s' = 1` (both are the vertex `pts j`), `i, l, j` distinct -/
theorem seg_inter (T : Erdos634.Geometry.Tri) {i l j : Fin 3} (hij : i ≠ j) (hlj : l ≠ j) (hil : i ≠ l) {s s' : ℝ}
    (h : AffineMap.lineMap (T.pts i) (T.pts j) s = AffineMap.lineMap (T.pts l) (T.pts j) s') : s = 1 := by
  have key := congrArg (fun p => T.basis.coord i p) h
  simp only [AffineMap.apply_lineMap] at key
  have e1 : T.basis.coord i (T.pts i) = 1 := T.basis.coord_apply_eq i
  have e2 : T.basis.coord i (T.pts j) = 0 := T.basis.coord_apply_ne hij
  have e3 : T.basis.coord i (T.pts l) = 0 := T.basis.coord_apply_ne hil
  rw [e1, e2, e3] at key
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul] at key
  linarith

end Erdos634.BeesonRosu37c4a
