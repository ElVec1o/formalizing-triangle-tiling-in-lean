-- Draft/LaczFormalIIcWN57.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2 (`IIcNoKites`), step (i) ("the W_i are adjacent on C1"), part 1:
-- strictly convex polygons given by half-plane data (`SC c tau`), affine behaviour of `sideFn`, vertex and midpoint facts.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN56

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {N : ℕ} [NeZero N]

theorem sideFn_lin (x0 d z1 z2 : ℂ) (s : ℝ) :
    sideFn x0 d (z1 + (s : ℂ) * (z2 - z1)) = (1 - s) * sideFn x0 d z1 + s * sideFn x0 d z2 := by
  unfold sideFn
  have : (z1 + (s : ℂ) * (z2 - z1) - x0) / d = ((1 - s : ℝ) : ℂ) * ((z1 - x0) / d) + (s : ℂ) * ((z2 - x0) / d) := by
    push_cast; ring
  rw [this, Complex.add_im, Complex.im_ofReal_mul, Complex.im_ofReal_mul]

theorem sideFn_base (x0 d : ℂ) : sideFn x0 d x0 = 0 := by simp [sideFn]

theorem sideFn_tip {x0 d : ℂ} (hd : d ≠ 0) : sideFn x0 d (x0 + d) = 0 := by
  unfold sideFn
  rw [add_sub_cancel_left, div_self hd]; simp

/-- Strict convexity of the polygon `c` with sign `τ`: every vertex off an edge lies strictly on the positive side of its line. -/
def SC (c : Fin N → ℂ) (τ : ℝ) : Prop :=
  ∀ j m : Fin N, m ≠ j → m ≠ j + 1 → 0 < τ * sideFn (c j) (c (j + 1) - c j) (c m)

theorem SC.vert_nonneg {c : Fin N → ℂ} {τ : ℝ} (hinj : Function.Injective c) (hn : 3 ≤ N) (h : SC c τ) (j m : Fin N) :
    0 ≤ τ * sideFn (c j) (c (j + 1) - c j) (c m) := by
  by_cases h1 : m = j
  · rw [h1, sideFn_base]; simp
  · by_cases h2 : m = j + 1
    · rw [h2]
      have hd : c (j + 1) - c j ≠ 0 := sub_ne_zero.2 (nd hinj hn j)
      have := sideFn_tip (x0 := c j) hd
      rw [show c j + (c (j + 1) - c j) = c (j + 1) by ring] at this
      rw [this]; simp
    · exact (h j m h1 h2).le

/-- Points weakly inside `c` (all half-plane values `>= 0`) form a convex set; combination lemma. -/
theorem comb_nonneg {x0 d z1 z2 : ℂ} {τ : ℝ} {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (h1 : 0 ≤ τ * sideFn x0 d z1)
    (h2 : 0 ≤ τ * sideFn x0 d z2) : 0 ≤ τ * sideFn x0 d (z1 + (s : ℂ) * (z2 - z1)) := by
  rw [sideFn_lin]
  have : τ * ((1 - s) * sideFn x0 d z1 + s * sideFn x0 d z2) = (1 - s) * (τ * sideFn x0 d z1) + s * (τ * sideFn x0 d z2) := by ring
  rw [this]
  have : 0 ≤ 1 - s := by linarith
  positivity

theorem comb_pos {x0 d z1 z2 : ℂ} {τ : ℝ} {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (h1 : 0 < τ * sideFn x0 d z1)
    (h2 : 0 < τ * sideFn x0 d z2) : 0 < τ * sideFn x0 d (z1 + (s : ℂ) * (z2 - z1)) := by
  rw [sideFn_lin]
  have : τ * ((1 - s) * sideFn x0 d z1 + s * sideFn x0 d z2) = (1 - s) * (τ * sideFn x0 d z1) + s * (τ * sideFn x0 d z2) := by ring
  rw [this]
  rcases hs0.lt_or_eq with h | h
  · have : 0 ≤ 1 - s := by linarith
    have := mul_nonneg this h1.le
    nlinarith [mul_pos h h2]
  · rw [← h]; simpa using h1

theorem comb_pos_left {x0 d z1 z2 : ℂ} {τ : ℝ} {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (h1 : 0 < τ * sideFn x0 d z1)
    (h2 : 0 ≤ τ * sideFn x0 d z2) : 0 < τ * sideFn x0 d (z1 + (s : ℂ) * (z2 - z1)) := by
  rw [sideFn_lin]
  have : τ * ((1 - s) * sideFn x0 d z1 + s * sideFn x0 d z2) = (1 - s) * (τ * sideFn x0 d z1) + s * (τ * sideFn x0 d z2) := by ring
  rw [this]
  have h3 : 0 < 1 - s := by linarith
  nlinarith [mul_pos h3 h1, mul_nonneg hs0 h2]

end Erdos634.Draft.LaczFormal.WN
