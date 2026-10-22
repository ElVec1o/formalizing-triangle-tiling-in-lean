-- Draft/LaczFormalIIcWN21.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2/6.3, Lemma 6.2 (`IIcNoKites`), step (c) `u = v + N`:
-- discrete Hopf (Umlaufsatz) for simple polygons, part 2: row sums, row recursion, `hopf_core` on a N-indexed vertex sequence.
-- Hypotheses: non-adjacent edges disjoint, consecutive edge directions not antiparallel, vertex 0 lexicographically minimal.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2/6.3), Beeson, Beeson-Zhang; discrete form of Hopf's proof of the Umlaufsatz.
import Erdos634.Draft.LaczFormalIIcWN20

open Complex

namespace Erdos634.Draft.LaczFormal.WN

/-- The half plane `H = {re > 0} ∪ {re = 0, im > 0}` (points lexicographically after `0`). -/
def InH (z : ℂ) : Prop := 0 < z.re ∨ (z.re = 0 ∧ 0 < z.im)

theorem InH.ne {z : ℂ} (h : InH z) : z ≠ 0 := by
  rintro rfl; simp [InH] at h

theorem InH.arg_bounds {z : ℂ} (h : InH z) : -(Real.pi / 2) < Complex.arg z ∧ Complex.arg z ≤ Real.pi / 2 := by
  rcases h with h | ⟨h0, h1⟩
  · have := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl h)
    rw [abs_lt] at this; exact ⟨this.1, this.2.le⟩
  · have : Complex.arg z = Real.pi / 2 := Complex.arg_eq_pi_div_two_iff.2 ⟨h0, h1⟩
    rw [this]; constructor <;> linarith [Real.pi_pos]

theorem arg_div_sub_of_InH {z w : ℂ} (hz : InH z) (hw : InH w) :
    Complex.arg (w / z) = Complex.arg w - Complex.arg z := by
  have hz0 := hz.ne
  have hw0 := hw.ne
  have hnpi : Complex.arg z ≠ Real.pi := by
    have := hz.arg_bounds; intro h; linarith [this.2, Real.pi_pos]
  have hai : Complex.arg z⁻¹ = - Complex.arg z := by rw [Complex.arg_inv]; simp [hnpi]
  rw [div_eq_mul_inv]
  have := Complex.arg_mul hw0 (inv_ne_zero hz0) (by
    rw [hai]
    constructor <;> linarith [hz.arg_bounds.1, hz.arg_bounds.2, hw.arg_bounds.1, hw.arg_bounds.2, Real.pi_pos])
  rw [this, hai]; ring

theorem tele (f : ℕ → ℝ) {a b : ℕ} (h : a ≤ b) : ∑ j ∈ Finset.Ico a b, (f j - f (j + 1)) = f a - f b := by
  induction b, h using Nat.le_induction with
  | base => simp
  | succ b hab ih => rw [Finset.sum_Ico_succ_top hab, ih]; ring

/-- Chord vector `q j - q i`. -/
def cc (q : ℕ → ℂ) (i j : ℕ) : ℂ := q j - q i
/-- Edge vector. -/
def dd (q : ℕ → ℂ) (k : ℕ) : ℂ := q (k + 1) - q k
/-- Sweep of the chord from `q i` as the other endpoint moves from `q j` to `q (j+1)`. -/
noncomputable def gg (q : ℕ → ℂ) (i j : ℕ) : ℝ := ang (cc q i j) (cc q i (j + 1))
/-- Sweep of the chord to `q j` as the base moves from `q i` to `q (i+1)`. -/
noncomputable def VV (q : ℕ → ℂ) (i j : ℕ) : ℝ := ang (cc q i j) (cc q (i + 1) j)
/-- Row sum. -/
noncomputable def Rr (q : ℕ → ℂ) (n i : ℕ) : ℝ := ∑ j ∈ Finset.Ico (i + 1) n, gg q i j

theorem cell_cc (q : ℕ → ℂ) {i j : ℕ} (h : Disjoint (segment ℝ (q i) (q (i + 1))) (segment ℝ (q j) (q (j + 1)))) :
    gg q i j - gg q (i + 1) j = VV q i j - VV q i (j + 1) := by
  obtain ⟨u, h1, h2, h3, h4⟩ := cell_halfplane (q i) (q (i + 1)) (q j) (q (j + 1)) h
  have hu : u ≠ 0 := by rintro rfl; simp at h1
  unfold gg VV cc
  rw [ang_eq_of_hp hu h1 h2, ang_eq_of_hp hu h4 h3, ang_eq_of_hp hu h1 h4, ang_eq_of_hp hu h2 h3]
  ring

theorem diag_term (q : ℕ → ℂ) (i : ℕ) (h0 : dd q i ≠ 0) (h1 : dd q (i + 1) ≠ 0)
    (hr : ¬ ((dd q (i + 1) / dd q i).im = 0 ∧ (dd q (i + 1) / dd q i).re ≤ 0)) :
    gg q i (i + 1) + VV q i (i + 2) = ang (dd q i) (dd q (i + 1)) := by
  have hb := ang_bisect h0 h1 hr
  have e1 : cc q i (i + 1) = dd q i := rfl
  have e2 : cc q i (i + 1 + 1) = dd q i + dd q (i + 1) := by simp [cc, dd]
  have e3 : cc q (i + 1) (i + 2) = dd q (i + 1) := rfl
  unfold gg VV
  rw [e1, e2, e3]
  exact hb

/-- Row recursion for rows `i >= 1` (all cells `(i, j)` with `j >= i+2`, `j+1 <= n` nondegenerate). -/
theorem rowstep (q : ℕ → ℂ) (n i : ℕ) (hn : i + 2 ≤ n)
    (hcell : ∀ j, i + 2 ≤ j → j + 1 ≤ n → Disjoint (segment ℝ (q i) (q (i + 1))) (segment ℝ (q j) (q (j + 1))))
    (h0 : dd q i ≠ 0) (h1 : dd q (i + 1) ≠ 0)
    (hr : ¬ ((dd q (i + 1) / dd q i).im = 0 ∧ (dd q (i + 1) / dd q i).re ≤ 0)) :
    Rr q n i - Rr q n (i + 1) = ang (dd q i) (dd q (i + 1)) - VV q i n := by
  have hlt : i + 1 < n := by omega
  unfold Rr
  rw [Finset.sum_eq_sum_Ico_succ_bot hlt]
  have e : Finset.Ico (i + 1 + 1) n = Finset.Ico (i + 2) n := rfl
  rw [e]
  have hsum : ∑ j ∈ Finset.Ico (i + 2) n, (gg q i j - gg q (i + 1) j) = VV q i (i + 2) - VV q i n := by
    rw [← tele (fun j => VV q i j) (by omega : i + 2 ≤ n)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_Ico] at hj
    exact cell_cc q (hcell j hj.1 (by omega))
  have := diag_term q i h0 h1 hr
  rw [Finset.sum_sub_distrib] at hsum
  linarith

end Erdos634.Draft.LaczFormal.WN
