-- Draft/LaczFormalIIcWN24.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2/6.3, Lemma 6.2 (`IIcNoKites`), step (c) `u = v + N`:
-- discrete Hopf, part 5: ASSEMBLY.  For a simple polygon `p : Fin n -> C` (SimplePoly, injective, 3 <= n) the exterior angles
-- `arg ((p (k+1) - p k) / (p k - p (k-1)))` sum to `2 pi rho`, `rho = +-1`; hence the interior angles `pi - rho * ext_k`
-- lie in `(0, 2 pi)` and sum to `(n-2) pi`.  No Jordan theorem, no ear removal.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2/6.3), Beeson, Beeson-Zhang; discrete form of Hopf's proof of the Umlaufsatz.
import Erdos634.Draft.LaczFormalIIcWN23

open scoped Classical Fin.NatCast
open Complex

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

/-- Exterior (turning) angle of `p` at the vertex `k`. -/
noncomputable def extAng (p : Fin n → ℂ) (k : Fin n) : ℝ := Complex.arg ((p (k + 1) - p k) / (p k - p (k - 1)))

/-- The rotated sequence `k |-> p (m0 + k)`. -/
def qq (p : Fin n → ℂ) (m0 : Fin n) : ℕ → ℂ := fun k => p (phi m0 k)

theorem dd_qq (p : Fin n → ℂ) (m0 : Fin n) (k : ℕ) : dd (qq p m0) k = p (phi m0 k + 1) - p (phi m0 k) := by
  simp [dd, qq, phi_succ]

theorem hdata {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n) (m0 : Fin n)
    (hm0 : ∀ k : Fin n, k ≠ m0 → InH (p k - p m0)) {m : ℕ} (hm : m + 1 = n) : HData m (qq p m0) := by
  have hφm : phi m0 m + 1 = m0 := by rw [← phi_succ, hm, phi_n]
  have hq1 : ∀ k, p (phi m0 k + 1) = p (phi m0 (k + 1)) := by intro k; rw [phi_succ]
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [qq]; rw [hm, phi_n, phi_zero]
  · intro k _
    rw [dd_qq]; exact sub_ne_zero.2 (nd hinj hn _)
  · intro k _
    rw [dd_qq, dd_qq]; simp only [phi_succ]
    exact turn_ok hs hinj hn (phi m0 k)
  · rw [dd_qq, dd_qq, phi_zero, hφm]
    have := turn_ok hs hinj hn (phi m0 m)
    rwa [hφm] at this
  · intro i j h1 h2 h3
    rw [Set.disjoint_left]
    intro z hz1 hz2
    have hne : phi m0 i ≠ phi m0 j := by
      intro h
      have := phi_inj_small hinj m0 (a := i) (b := j) (by omega) (by omega) (by rw [h])
      omega
    have hz1' : z ∈ segment ℝ (p (phi m0 i)) (p (phi m0 i + 1)) := by
      rw [hq1]; exact hz1
    have hz2' : z ∈ segment ℝ (p (phi m0 j)) (p (phi m0 j + 1)) := by
      rw [hq1]; exact hz2
    obtain ⟨hA, hB⟩ := hs _ _ hne z ⟨hz1', hz2'⟩
    rw [hq1] at hA hB
    rcases hA with hA | hA <;> rcases hB with hB | hB
    · have := phi_inj_small hinj m0 (a := i) (b := j) (by omega) (by omega) (hA.symm.trans hB)
      omega
    · have := phi_inj_small hinj m0 (a := i) (b := j + 1) (by omega) (by omega) (hA.symm.trans hB)
      omega
    · have := phi_inj_small hinj m0 (a := i + 1) (b := j) (by omega) (by omega) (hA.symm.trans hB)
      omega
    · have := phi_inj_small hinj m0 (a := i + 1) (b := j + 1) (by omega) (by omega) (hA.symm.trans hB)
      omega
  · intro k hk1 hkm
    have hne : phi m0 k ≠ m0 := by
      intro h
      have h' : p (phi m0 k) = p (phi m0 0) := by rw [h, phi_zero]
      have := phi_inj_small hinj m0 (a := k) (b := 0) (by omega) (by omega) h'
      omega
    have := hm0 _ hne
    simpa [qq, phi_zero] using this

/-- **Exterior angle sum of a simple polygon (discrete Umlaufsatz).** -/
theorem exterior_angle_sum {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n) :
    ∃ ρ : ℝ, (ρ = 1 ∨ ρ = -1) ∧ ∑ k : Fin n, extAng p k = 2 * Real.pi * ρ := by
  obtain ⟨m0, hm0⟩ := exists_lexmin hinj
  obtain ⟨m, hm⟩ : ∃ m, m + 1 = n := ⟨n - 1, by omega⟩
  have H := hdata hs hinj hn m0 hm0 hm
  have hc := hopf_core H
  have hφm : phi m0 m + 1 = m0 := by rw [← phi_succ, hm, phi_n]
  -- reindex the sum
  have hre : ∑ k : Fin n, extAng p k = ∑ k : Fin n, extAng p (m0 + k) :=
    (Equiv.sum_comp (Equiv.addLeft m0) (extAng p)).symm
  have hg : ∑ k : Fin n, extAng p (m0 + k) = ∑ j ∈ Finset.range n, extAng p (phi m0 j) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => extAng p (phi m0 j)) n]
    apply Finset.sum_congr rfl
    intro i _
    simp [phi]
  have hrange : ∑ j ∈ Finset.range n, extAng p (phi m0 j) =
      ∑ i ∈ Finset.range m, ang (dd (qq p m0) i) (dd (qq p m0) (i + 1)) + ang (dd (qq p m0) m) (dd (qq p m0) 0) := by
    have e : Finset.range n = Finset.range (m + 1) := by rw [hm]
    rw [e, Finset.sum_range_succ']
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      unfold extAng ang
      rw [dd_qq, dd_qq, phi_succ]
      simp
    · unfold extAng ang
      rw [dd_qq, dd_qq, phi_zero]
      have : m0 - 1 = phi m0 m := (eq_sub_of_add_eq hφm).symm
      rw [this, hφm]
  rw [hre, hg, hrange, hc]
  split_ifs
  · exact ⟨1, Or.inl rfl, by ring⟩
  · exact ⟨-1, Or.inr rfl, by ring⟩

/-- Every exterior angle lies strictly between `-pi` and `pi` (no antiparallel consecutive edges). -/
theorem extAng_bounds {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n) (k : Fin n) :
    -Real.pi < extAng p k ∧ extAng p k < Real.pi := by
  refine ⟨Complex.neg_pi_lt_arg _, ?_⟩
  have := turn_ok hs hinj hn (k - 1)
  rw [sub_add_cancel] at this
  unfold extAng
  rw [Complex.arg_lt_pi_iff]
  by_cases h : 0 ≤ ((p (k + 1) - p k) / (p k - p (k - 1))).re
  · exact Or.inl h
  · right
    intro him
    apply this
    refine ⟨him, ?_⟩
    exact (not_le.1 h).le

/-- **Interior angle sum (Laczkovich, `u = v + N`).**  With `ρ = ±1` the orientation, the interior angles
`pi - ρ * ext_k` lie in `(0, 2 pi)` and sum to `(n-2) pi`. -/
theorem interior_angle_sum {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n) :
    ∃ ρ : ℝ, (ρ = 1 ∨ ρ = -1) ∧ (∀ k : Fin n, 0 < Real.pi - ρ * extAng p k ∧ Real.pi - ρ * extAng p k < 2 * Real.pi) ∧
      ∑ k : Fin n, (Real.pi - ρ * extAng p k) = ((n : ℝ) - 2) * Real.pi := by
  obtain ⟨ρ, hρ, hsum⟩ := exterior_angle_sum hs hinj hn
  refine ⟨ρ, hρ, ?_, ?_⟩
  · intro k
    have hb := extAng_bounds hs hinj hn k
    rcases hρ with rfl | rfl
    · constructor <;> linarith [hb.1, hb.2]
    · constructor <;> linarith [hb.1, hb.2]
  · rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum]
    simp
    rcases hρ with rfl | rfl <;> ring

end Erdos634.Draft.LaczFormal.WN
