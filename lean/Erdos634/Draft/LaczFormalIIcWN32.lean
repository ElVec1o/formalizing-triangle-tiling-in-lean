-- Draft/LaczFormalIIcWN32.lean -- NON-VACUITY witness for `nesting_dichotomy` (WN31): two concentric axis-parallel squares (radii 1 and 1/2), disjoint, both of winding number 1 about 0.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN31

open scoped Classical Fin.NatCast
open Complex

namespace Erdos634.Draft.LaczFormal.WN

/-- Square of radius `r` about 0, counterclockwise. -/
noncomputable def sqr (r : ℝ) : Fin 4 → ℂ := fun k => (r : ℂ) * ![(-1 : ℂ) - I, 1 - I, 1 + I, -1 + I] k

theorem sqr_ne (r : ℝ) (hr : 0 < r) (k : Fin 4) : sqr r k ≠ 0 := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  fin_cases k <;> simp [sqr, hr', Complex.ext_iff]

theorem sqr_succ (r : ℝ) (k : Fin 4) : sqr r (k + 1) = I * sqr r k := by
  fin_cases k <;> (simp [sqr]; apply Complex.ext <;> simp <;> ring)

theorem sqr_ratio (r : ℝ) (hr : 0 < r) (k : Fin 4) : sqr r (k + 1) / sqr r k = I := by
  rw [sqr_succ, mul_div_assoc, div_self (sqr_ne r hr k), mul_one]

theorem sqr_wind (r : ℝ) (hr : 0 < r) : wind (sqr r) 0 = 1 := by
  unfold wind turnSum angStep
  have : ∀ k : Fin 4, Complex.arg ((sqr r (k + 1) - 0) / (sqr r k - 0)) = Real.pi / 2 := by
    intro k; rw [sub_zero, sub_zero, sqr_ratio r hr k]; exact Complex.arg_I
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have := Real.pi_pos
  field_simp
  norm_num

/-- Every point of the boundary of the square of radius `r` has sup-norm `r`. -/
theorem sqr_edge_norm (r : ℝ) (hr : 0 < r) (k : Fin 4) : ∀ w ∈ segment ℝ (sqr r k) (sqr r (k + 1)), max |w.re| |w.im| = r := by
  intro w hw
  rw [segment_eq_image'] at hw
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hw
  fin_cases k <;> simp [sqr, abs_of_pos hr, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.real_smul]
  all_goals (rw [abs_le]; constructor <;> nlinarith)

theorem sqr_zero_not_mem (r : ℝ) (hr : 0 < r) : (0 : ℂ) ∉ edgeSet (sqr r) := by
  intro h
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 h
  have := sqr_edge_norm r hr k 0 hk
  simp at this
  linarith

theorem sqr_disjoint : Disjoint (edgeSet (sqr 1)) (edgeSet (sqr (1 / 2))) := by
  rw [Set.disjoint_left]
  intro w h1 h2
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 h1
  obtain ⟨k', hk'⟩ := Set.mem_iUnion.1 h2
  have a := sqr_edge_norm 1 one_pos k w hk
  have b := sqr_edge_norm (1 / 2) (by norm_num) k' w hk'
  rw [a] at b
  norm_num at b

theorem nesting_witness :
    wind (sqr 1) 0 ≠ 0 ∧ wind (sqr (1 / 2)) 0 ≠ 0 ∧ (0 : ℂ) ∉ edgeSet (sqr 1) ∧ (0 : ℂ) ∉ edgeSet (sqr (1 / 2)) ∧
      Disjoint (edgeSet (sqr 1)) (edgeSet (sqr (1 / 2))) ∧
      ((∀ x ∈ edgeSet (sqr (1 / 2)), wind (sqr 1) x ≠ 0) ∨ (∀ x ∈ edgeSet (sqr 1), wind (sqr (1 / 2)) x ≠ 0)) := by
  have h1 : wind (sqr 1) 0 ≠ 0 := by rw [sqr_wind 1 one_pos]; norm_num
  have h2 : wind (sqr (1 / 2)) 0 ≠ 0 := by rw [sqr_wind (1 / 2) (by norm_num)]; norm_num
  have n1 := sqr_zero_not_mem 1 one_pos
  have n2 := sqr_zero_not_mem (1 / 2) (by norm_num)
  exact ⟨h1, h2, n1, n2, sqr_disjoint, nesting_dichotomy _ _ sqr_disjoint n1 n2 h1 h2⟩

#print axioms nesting_witness

end Erdos634.Draft.LaczFormal.WN
