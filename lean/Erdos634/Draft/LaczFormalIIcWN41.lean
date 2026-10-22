-- Draft/LaczFormalIIcWN41.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, Lemma 6.2 (`IIcNoKites`), step (h), part 2:
-- `arc_simple` (SimplePoly of `arcPoly`), `arc_inj` (injectivity).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN40

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

theorem phi_inj_nat (a : Fin n) {i j : ℕ} (hi : i < n) (hj : j < n) (h : phi a i = phi a j) : i = j := by
  unfold phi at h
  have h2 : ((i : ℕ) : Fin n) = ((j : ℕ) : Fin n) := add_left_cancel h
  have h3 := congrArg Fin.val h2
  simp only [Fin.val_natCast] at h3
  rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h3

theorem arc_inj {p : Fin n → ℂ} (hinj : Function.Injective p) (a : Fin n) {d : ℕ} (hd : d + 1 ≤ n) :
    Function.Injective (arcPoly p a d) := by
  intro i j h
  have h1 := hinj h
  have := phi_inj_nat a (by have := i.isLt; omega) (by have := j.isLt; omega) h1
  exact Fin.ext this

theorem cast_pred (hn : 1 ≤ n) : ((n - 1 : ℕ) : Fin n) = -1 := by
  have h : ((n - 1 : ℕ) : Fin n) + 1 = 0 := by
    rw [← Nat.cast_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hn]; simp
  exact eq_neg_of_add_eq_zero_left h

/-- Key step: a chord point lying on an original arc edge is an endpoint of both. -/
theorem chord_edge {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (a : Fin n) {d : ℕ} (hd2 : 2 ≤ d) (hdn : d + 2 ≤ n)
    (hchord : ∀ z ∈ segment ℝ (p (phi a d)) (p a), z ∈ edgeSet p → z = p a ∨ z = p (phi a d))
    {j : ℕ} (hj : j < d) {z : ℂ} (hz1 : z ∈ segment ℝ (p (phi a d)) (p a)) (hz2 : z ∈ segment ℝ (p (phi a j)) (p (phi a (j + 1)))) :
    (z = p (phi a d) ∨ z = p a) ∧ (z = p (phi a j) ∨ z = p (phi a (j + 1))) := by
  have hz2e : z ∈ segment ℝ (p (phi a j)) (p (phi a j + 1)) := by rw [← phi_succ]; exact hz2
  have hE : z ∈ edgeSet p := Set.mem_iUnion.2 ⟨phi a j, hz2e⟩
  rcases hchord z hz1 hE with h | h
  · refine ⟨Or.inr h, ?_⟩
    subst h
    by_cases hj0 : j = 0
    · subst hj0; left; simp [phi]
    · exfalso
      have hv := vertex_not_other hs hinj (a - 1) (phi a j) (by
        intro h'
        have : phi a j = phi a (n - 1) := by
          rw [h']; unfold phi; rw [cast_pred (by omega), sub_eq_add_neg]
        have := phi_inj_nat a (by omega) (by omega) this
        omega) (by
        intro h'
        rw [sub_add_cancel] at h'
        have h0 : phi a j = phi a 0 := by rw [h']; unfold phi; simp
        have := phi_inj_nat a (by omega) (by omega) h0
        omega)
      rw [sub_add_cancel] at hv
      exact hv hz2e
  · refine ⟨Or.inl h, ?_⟩
    subst h
    by_cases hjd : j = d - 1
    · right; rw [hjd]; congr 2; omega
    · exfalso
      have e : phi a (d - 1) + 1 = phi a d := by rw [← phi_succ]; congr 1; omega
      have hv := vertex_not_other hs hinj (phi a (d - 1)) (phi a j) (by
        intro h'
        have := phi_inj_nat a (by omega) (by omega) h'
        omega) (by
        intro h'
        rw [e] at h'
        have := phi_inj_nat a (by omega) (by omega) h'
        omega)
      rw [e] at hv
      exact hv hz2e

end Erdos634.Draft.LaczFormal.WN
