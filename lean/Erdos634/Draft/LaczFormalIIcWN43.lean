-- Draft/LaczFormalIIcWN43.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, Lemma 6.2 (`IIcNoKites`), step (h), part 4:
-- `wind_split`: winding numbers add when a closed polygon is cut along a chord:  wind p z = wind (arcPoly p a d) z + wind (arcPoly p (a+d) (n-d)) z
-- for z off p and off the chord.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN42

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

theorem angStep_arc_lt (p : Fin n → ℂ) (a : Fin n) {d : ℕ} (z : ℂ) (i : ℕ) (hi : i < d) :
    angStep (arcPoly p a d) z ⟨i, by omega⟩ = angStep p z (phi a i) := by
  unfold angStep
  rw [arcPoly_succ p a i hi, phi_succ]
  rfl

theorem turnSum_arc (p : Fin n → ℂ) (a : Fin n) (d : ℕ) (z : ℂ) :
    turnSum (arcPoly p a d) z = ∑ i ∈ Finset.range d, angStep p z (phi a i) +
      Complex.arg ((p a - z) / (p (phi a d) - z)) := by
  unfold turnSum
  rw [Fin.sum_univ_castSucc]
  congr 1
  · rw [← Fin.sum_univ_eq_sum_range (fun i => angStep p z (phi a i)) d]
    apply Finset.sum_congr rfl
    intro i _
    have := angStep_arc_lt p a z i.val i.isLt
    simpa using this
  · unfold angStep
    rw [arcPoly_last, arcPoly_last_succ]

theorem turnSum_rot (p : Fin n → ℂ) (a : Fin n) (z : ℂ) :
    turnSum p z = ∑ i ∈ Finset.range n, angStep p z (phi a i) := by
  unfold turnSum
  have hre : ∑ k : Fin n, angStep p z k = ∑ k : Fin n, angStep p z (a + k) :=
    (Equiv.sum_comp (Equiv.addLeft a) (angStep p z)).symm
  rw [hre, ← Fin.sum_univ_eq_sum_range (fun j => angStep p z (phi a j)) n]
  apply Finset.sum_congr rfl
  intro i _
  simp [phi]

theorem wind_split (p : Fin n → ℂ) (a : Fin n) {d : ℕ} (hdn : d ≤ n) {z : ℂ} (hz : z ∉ edgeSet p)
    (hzc : z ∉ segment ℝ (p (phi a d)) (p a)) :
    wind p z = wind (arcPoly p a d) z + wind (arcPoly p (phi a d) (n - d)) z := by
  unfold wind
  rw [← add_div]
  congr 1
  rw [turnSum_arc, turnSum_arc, turnSum_rot p a z]
  have hsum : ∑ i ∈ Finset.range n, angStep p z (phi a i) =
      ∑ i ∈ Finset.range d, angStep p z (phi a i) + ∑ i ∈ Finset.range (n - d), angStep p z (phi (phi a d) i) := by
    have e : Finset.range n = Finset.range (d + (n - d)) := by rw [Nat.add_sub_cancel' hdn]
    rw [e, Finset.sum_range_add]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    unfold phi
    rw [Nat.cast_add, add_assoc]
  have hlast : phi (phi a d) (n - d) = a := by
    unfold phi
    rw [add_assoc, ← Nat.cast_add, Nat.add_sub_cancel' hdn]; simp
  rw [hsum, hlast]
  have hsl := ratio_mem_slitPlane (a := p (phi a d)) (b := p a) (z := z) hzc
  have hne : Complex.arg ((p a - z) / (p (phi a d) - z)) ≠ Real.pi := by
    intro h
    exact (Complex.mem_slitPlane_iff_arg.1 hsl).1 h
  have hinv : (p (phi a d) - z) / (p a - z) = ((p a - z) / (p (phi a d) - z))⁻¹ := by rw [inv_div]
  rw [hinv, Complex.arg_inv]
  rw [if_neg hne]
  ring

end Erdos634.Draft.LaczFormal.WN
