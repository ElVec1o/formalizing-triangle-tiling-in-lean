-- Draft/LaczFormalIIcWN36.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2/6.3, Lemma 6.2 (`IIcNoKites`), step (d1), part 4:
-- `exterior_angle_sum_lex`: the exterior angle sum `2 pi rho` of a simple polygon, together with a lexicographically minimal vertex `m0`
-- at which the exterior angle has the sign of `rho` (the proof of WN24 `exterior_angle_sum` with the sign of `rho` exposed).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2/6.3), Beeson, Beeson-Zhang; discrete Hopf.
import Erdos634.Draft.LaczFormalIIcWN35

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

theorem exterior_angle_sum_lex {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n) :
    ∃ ρ : ℝ, (ρ = 1 ∨ ρ = -1) ∧ ∑ k : Fin n, extAng p k = 2 * Real.pi * ρ ∧
      ∃ m0 : Fin n, (∀ k : Fin n, k ≠ m0 → InH (p k - p m0)) ∧ ((ρ = 1 ∧ 0 < extAng p m0) ∨ (ρ = -1 ∧ extAng p m0 < 0)) := by
  obtain ⟨m0, hm0⟩ := exists_lexmin hinj
  obtain ⟨m, hm⟩ : ∃ m, m + 1 = n := ⟨n - 1, by omega⟩
  have H := hdata hs hinj hn m0 hm0 hm
  have hc := hopf_core H
  have hφm : phi m0 m + 1 = m0 := by rw [← phi_succ, hm, phi_n]
  have hre : ∑ k : Fin n, extAng p k = ∑ k : Fin n, extAng p (m0 + k) :=
    (Equiv.sum_comp (Equiv.addLeft m0) (extAng p)).symm
  have hg : ∑ k : Fin n, extAng p (m0 + k) = ∑ j ∈ Finset.range n, extAng p (phi m0 j) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => extAng p (phi m0 j)) n]
    apply Finset.sum_congr rfl
    intro i _
    simp [phi]
  have hlast : ang (dd (qq p m0) m) (dd (qq p m0) 0) = extAng p m0 := by
    unfold extAng ang
    rw [dd_qq, dd_qq, phi_zero]
    have : m0 - 1 = phi m0 m := (eq_sub_of_add_eq hφm).symm
    rw [this, hφm]
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
    · rw [hlast]
      unfold extAng
      rw [phi_zero]
  rw [hre, hg, hrange, hc]
  have hext0 : (dd (qq p m0) 0 / dd (qq p m0) m) = (p (m0 + 1) - p m0) / (p m0 - p (m0 - 1)) := by
    rw [dd_qq, dd_qq, phi_zero]
    have : m0 - 1 = phi m0 m := (eq_sub_of_add_eq hφm).symm
    rw [this, hφm]
  have hlast' : extAng p m0 = Complex.arg (dd (qq p m0) 0 / dd (qq p m0) m) := by
    rw [hext0]; rfl
  refine ⟨if 0 < (dd (qq p m0) 0 / dd (qq p m0) m).im then 1 else -1, ?_, ?_, m0, hm0, ?_⟩
  · split_ifs <;> simp
  · split_ifs <;> ring
  · split_ifs with hpos
    · left
      refine ⟨rfl, ?_⟩
      rw [hlast']
      rcases (Complex.arg_nonneg_iff.2 hpos.le).lt_or_eq with h | h
      · exact h
      · exfalso
        have := Complex.arg_eq_zero_iff.1 h.symm
        linarith [this.2]
    · right
      refine ⟨rfl, ?_⟩
      rw [hlast']
      have him : (dd (qq p m0) 0 / dd (qq p m0) m).im ≠ 0 := by
        intro h0
        have hmm := H.wrap
        have h1 : ¬ (0 < (dd (qq p m0) 0 / dd (qq p m0) m).re) := by
          intro hre'
          -- im = 0 and re > 0 contradicts lex-minimality (as in hopf_core)
          have h1' : InH (dd (qq p m0) 0) := by
            have := H.lex 1 le_rfl (by omega); simpa [dd] using this
          have h2 : InH (-dd (qq p m0) m) := by
            have := H.lex m (by omega) le_rfl
            have e : (qq p m0) m - (qq p m0) 0 = -dd (qq p m0) m := by simp [dd, H.per]
            rwa [e] at this
          have h3 : InH ((dd (qq p m0) 0 / dd (qq p m0) m) * (-dd (qq p m0) m)) := InH_mul_pos h0 hre' h2
          have e3 : (dd (qq p m0) 0 / dd (qq p m0) m) * (-dd (qq p m0) m) = -dd (qq p m0) 0 := by
            have := H.nz m le_rfl
            field_simp
          rw [e3] at h3
          exact InH_neg h1' h3
        exact hmm ⟨h0, not_lt.1 h1⟩
      exact Complex.arg_neg_iff.2 (lt_of_le_of_ne (not_lt.1 hpos) him)

end Erdos634.Draft.LaczFormal.WN
