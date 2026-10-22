import Erdos634.Draft.LaczFormalBZL7j3
import Erdos634.Draft.LaczFormal51Gen2

-- Draft/LaczFormalBZL7k1.lean -- THE RATIONAL-ANGLE CASE alpha in Q pi of the gamma = 2pi/3 tile (alpha, pi/3 - alpha, 2pi/3), EVERY DENOMINATOR n (no `Covered3` hypothesis).
-- Method: the argument of `LaczFormal51Gen1/2` (Laczkovich, Discrete Math. 140 (1995), proof of Thm 5.1: Lemma K -> `KStar`, corner counts P_l, Lemma 5.2) re-run for the family relation
-- 3 a_0 + 3 a_1 = n, a_2 = 2 a_0 + 2 a_1 (units pi/n, gcd 1).  Corner counts: P_gamma <= 1 (2 a_gamma = 4n/3 > n), P_alpha, P_beta <= 2 or Lemma 5.2 gives n | 3*{3,4,6,10} (Covered);
-- sum_l P_l a_l = n with these bounds forces P = (1,1,1) (target angles = tile angles, i.e. similar) or {P_alpha,P_beta} = {2,0}, a_0 = a_1 = 1, n = 6 (Covered).
--   `n_small3`        : Lemma 5.2's output + the relation  ==>  Covered n.
--   `uncov_core3`     : n not Covered  ==>  the target numerators are a permutation of the tile numerators.
--   `bz_rational_all` : the tile (alpha, pi/3 - alpha, 2pi/3), alpha in Q pi, tiling a NON-SIMILAR triangle  ==>  alpha = pi/6 and the target is equilateral.   (BZ Thm 1.1 hypothesis alpha not in Q pi is
--                       necessary: BZL7j4.)  NOTE, UNAUDITED.
-- Credit: Laczkovich (Discrete Math. 140 (1995) Thm 5.1, Lemma 5.2; Combinatorica 10 (1990)), Beeson-Zhang (arXiv 2604.01314), Beeson.

open scoped BigOperators Classical

namespace Erdos634.Lacz51Gen3

open Erdos634 Erdos634.Geometry Erdos634.BeesonColoring Erdos634.BeesonH1 Erdos634.Draft.LaczFormal
  Erdos634.Draft.TheoremPConditional Erdos634.Lacz51Cov Erdos634.Lacz51Gen Erdos634.Lacz51Gen2 Erdos634.Geometry.CaseA.LemmaV
  Erdos634.LemmaKStar Erdos634.Draft.LaczFormal.RG

theorem n_small3 {n b0 b1 b2 : ℕ} (hb0 : 0 < b0) (hb1 : 0 < b1) (hrel : 3 * b0 + 3 * b1 = n) (h2 : b2 = 2 * b0 + 2 * b1)
    (hd : ∀ d, d ∣ b0 → d ∣ b1 → d ∣ b2 → d = 1) {t : ℕ} (ht : t = b0 ∨ t = b1)
    (h52 : n / Nat.gcd t n = 3 ∨ n / Nat.gcd t n = 4 ∨ n / Nat.gcd t n = 6 ∨ n / Nat.gcd t n = 10) : Covered n := by
  have hcop : Nat.Coprime b0 b1 := by
    apply hd
    · exact Nat.gcd_dvd_left _ _
    · exact Nat.gcd_dvd_right _ _
    · rw [h2]; exact dvd_add (Dvd.dvd.mul_left (Nat.gcd_dvd_left _ _) 2) (Dvd.dvd.mul_left (Nat.gcd_dvd_right _ _) 2)
  set g := Nat.gcd t n with hg
  have hgn : g ∣ n := Nat.gcd_dvd_right _ _
  have hgt : g ∣ t := Nat.gcd_dvd_left _ _
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right _ (by omega)
  have hn : n = g * (n / g) := (Nat.mul_div_cancel' hgn).symm
  have hg13 : g = 1 ∨ g = 3 := by
    have h3 : g ∣ 3 := by
      rcases ht with rfl | rfl
      · have h1 : g ∣ 3 * t + 3 * b1 := hrel ▸ hgn
        have h3 : g ∣ 3 * t := Dvd.dvd.mul_left hgt 3
        have h4 : g ∣ 3 * b1 := (Nat.dvd_add_right h3).mp h1
        have hc : Nat.Coprime g b1 := Nat.Coprime.coprime_dvd_left hgt hcop
        exact hc.dvd_of_dvd_mul_right h4
      · have h1 : g ∣ 3 * b0 + 3 * t := hrel ▸ hgn
        have h3 : g ∣ 3 * t := Dvd.dvd.mul_left hgt 3
        have h4 : g ∣ 3 * b0 := (Nat.dvd_add_left h3).mp h1
        have hc : Nat.Coprime g b0 := Nat.Coprime.coprime_dvd_left hgt hcop.symm
        exact hc.dvd_of_dvd_mul_right h4
    exact (Nat.dvd_prime Nat.prime_three).mp h3
  apply covered_small
  rcases hg13 with h | h <;> rcases h52 with h' | h' | h' | h' <;> (rw [h] at hn h'; omega)

set_option maxHeartbeats 4000000 in
theorem uncov_core3 {n : ℕ} {a : Fin 3 → ℕ} {f : Fin 3 → Fin 3 → ℕ} (ha : ∀ i, 1 ≤ a i) (hsum : ∑ i, a i = n)
    (hd : ∀ d, (∀ i, d ∣ a i) → d = 1)
    (σ : Equiv.Perm (Fin 3)) (hr1 : 3 * a (σ 0) + 3 * a (σ 1) = n) (hr2 : a (σ 2) = 2 * a (σ 0) + 2 * a (σ 1))
    (hf : ∀ j, f j ≠ 0) (hu : ∑ j, uu a f j = n) (hK : KStar n a f) (hnc : ¬ Covered n) :
    ((uu a f 0 = a 0 ∧ uu a f 1 = a 1 ∧ uu a f 2 = a 2) ∨ (uu a f 0 = a 0 ∧ uu a f 1 = a 2 ∧ uu a f 2 = a 1) ∨
      (uu a f 0 = a 1 ∧ uu a f 1 = a 0 ∧ uu a f 2 = a 2) ∨ (uu a f 0 = a 1 ∧ uu a f 1 = a 2 ∧ uu a f 2 = a 0) ∨
      (uu a f 0 = a 2 ∧ uu a f 1 = a 0 ∧ uu a f 2 = a 1) ∨ (uu a f 0 = a 2 ∧ uu a f 1 = a 1 ∧ uu a f 2 = a 0)) := by
  have hPs0 := hPsum_eq hu
  have hPs : FF f (σ 0) * a (σ 0) + FF f (σ 1) * a (σ 1) + FF f (σ 2) * a (σ 2) = n := by
    rw [← hPs0, ← Equiv.sum_comp σ (fun l => FF f l * a l), Fin.sum_univ_three]
  have hdd : ∀ d, d ∣ a (σ 0) → d ∣ a (σ 1) → d ∣ a (σ 2) → d = 1 := by
    intro d h0 h1 h2
    apply hd
    intro i
    obtain ⟨m', rfl⟩ := σ.surjective i
    fin_cases m' <;> assumption
  have hcop : Nat.Coprime (a (σ 0)) (a (σ 1)) := by
    apply hdd
    · exact Nat.gcd_dvd_left _ _
    · exact Nat.gcd_dvd_right _ _
    · rw [hr2]; exact dvd_add (Dvd.dvd.mul_left (Nat.gcd_dvd_left _ _) 2) (Dvd.dvd.mul_left (Nat.gcd_dvd_right _ _) 2)
  have hsum' := hsum
  rw [Fin.sum_univ_three] at hsum'
  have hle2 : FF f (σ 2) * a (σ 2) ≤ n := by omega
  have hlt : ∀ m, a (σ m) < n := fun m => LemmaKStar.a_lt (n := n) (a := a) (by rw [Fin.sum_univ_three]; exact hsum') ha (σ m)
  have l0 : FF f (σ 0) ≤ 2 := by
    by_contra h3
    apply hnc
    have h52 := Erdos634.Lacz51.lemma52 (a (σ 0)) n (ha _) (hlt 0)
      (fun k hk => kstar_frac (by rw [Fin.sum_univ_three]; exact hsum') ha hK (σ 0) (by omega) k hk)
    exact n_small3 (ha _) (ha _) hr1 hr2 hdd (Or.inl rfl) h52
  have l1 : FF f (σ 1) ≤ 2 := by
    by_contra h3
    apply hnc
    have h52 := Erdos634.Lacz51.lemma52 (a (σ 1)) n (ha _) (hlt 1)
      (fun k hk => kstar_frac (by rw [Fin.sum_univ_three]; exact hsum') ha hK (σ 1) (by omega) k hk)
    exact n_small3 (ha _) (ha _) hr1 hr2 hdd (Or.inr rfl) h52
  have l2 : FF f (σ 2) ≤ 1 := by
    have h2 := hle2
    by_contra hc
    have : 2 * a (σ 2) ≤ FF f (σ 2) * a (σ 2) := Nat.mul_le_mul_right _ (by omega)
    have := ha (σ 0); have := ha (σ 1)
    omega
  have hcov6 : a (σ 0) = a (σ 1) → Covered n := by
    intro heq
    rw [heq] at hcop
    have h1 : a (σ 1) = 1 := (Nat.coprime_self _).mp hcop
    apply covered_small
    right; right; left
    omega
  have hrow : ∀ j, 1 ≤ ∑ i, f j i := by
    intro j
    by_contra hcon
    apply hf j
    funext i
    have : ∑ i, f j i = 0 := by omega
    exact Finset.sum_eq_zero_iff.mp this i (Finset.mem_univ _)
  have hSS : ∑ j, ∑ i, f j i = ∑ l, FF f l := by
    unfold FF; rw [Finset.sum_comm]
  have hFsum : FF f 0 + FF f 1 + FF f 2 = FF f (σ 0) + FF f (σ 1) + FF f (σ 2) := by
    have := Equiv.sum_comp σ (fun l => FF f l)
    rw [Fin.sum_univ_three, Fin.sum_univ_three] at this
    omega
  have e0 : FF f 0 = f 0 0 + f 1 0 + f 2 0 := by unfold FF; rw [Fin.sum_univ_three]
  have e1 : FF f 1 = f 0 1 + f 1 1 + f 2 1 := by unfold FF; rw [Fin.sum_univ_three]
  have e2 : FF f 2 = f 0 2 + f 1 2 + f 2 2 := by unfold FF; rw [Fin.sum_univ_three]
  have h3 : FF f (σ 0) = 1 ∧ FF f (σ 1) = 1 ∧ FF f (σ 2) = 1 := by
    have d0 : FF f (σ 0) = 0 ∨ FF f (σ 0) = 1 ∨ FF f (σ 0) = 2 := by omega
    have d1 : FF f (σ 1) = 0 ∨ FF f (σ 1) = 1 ∨ FF f (σ 1) = 2 := by omega
    have d2 : FF f (σ 2) = 0 ∨ FF f (σ 2) = 1 := by omega
    have a0 := ha (σ 0); have a1 := ha (σ 1)
    rcases d0 with h0 | h0 | h0 <;> rcases d1 with h1 | h1 | h1 <;> rcases d2 with h2 | h2 <;>
      rw [h0, h1, h2] at hPs <;>
      first
      | omega
      | (exfalso; have := hcov6 (by omega); exact hnc this)
  have hall1 : ∀ l, FF f l = 1 := by
    intro l
    obtain ⟨m, rfl⟩ := σ.surjective l
    have f3 : m = 0 ∨ m = 1 ∨ m = 2 := by revert m; decide
    rcases f3 with rfl | rfl | rfl
    · exact h3.1
    · exact h3.2.1
    · exact h3.2.2
  have a0' := hall1 0; have a1' := hall1 1; have a2' := hall1 2
  have hr0 := hrow 0; have hr1' := hrow 1; have hr2' := hrow 2
  have hu' := hu
  simp only [Fin.sum_univ_three] at hr0 hr1' hr2' hSS hu'
  have row0 : (f 0 0 = 1 ∧ f 0 1 = 0 ∧ f 0 2 = 0) ∨ (f 0 0 = 0 ∧ f 0 1 = 1 ∧ f 0 2 = 0) ∨ (f 0 0 = 0 ∧ f 0 1 = 0 ∧ f 0 2 = 1) := by omega
  have row1 : (f 1 0 = 1 ∧ f 1 1 = 0 ∧ f 1 2 = 0) ∨ (f 1 0 = 0 ∧ f 1 1 = 1 ∧ f 1 2 = 0) ∨ (f 1 0 = 0 ∧ f 1 1 = 0 ∧ f 1 2 = 1) := by omega
  have row2 : (f 2 0 = 1 ∧ f 2 1 = 0 ∧ f 2 2 = 0) ∨ (f 2 0 = 0 ∧ f 2 1 = 1 ∧ f 2 2 = 0) ∨ (f 2 0 = 0 ∧ f 2 1 = 0 ∧ f 2 2 = 1) := by omega
  simp only [uu, Fin.sum_univ_three] at hu' ⊢
  rcases row0 with ⟨p0, p1, p2⟩ | ⟨p0, p1, p2⟩ | ⟨p0, p1, p2⟩ <;>
  rcases row1 with ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ | ⟨q0, q1, q2⟩ <;>
  rcases row2 with ⟨r0, r1, r2⟩ | ⟨r0, r1, r2⟩ | ⟨r0, r1, r2⟩ <;>
  simp only [p0, p1, p2, q0, q1, q2, r0, r1, r2] at hu' ⊢ <;>
  first
  | omega
  | (exfalso; omega)

open Erdos634.TilePlacement in
/-- **The rational-angle case, EVERY denominator.**  The tile `(alpha, pi/3 - alpha, 2pi/3)` with `alpha in Q pi` tiling a triangle not similar to it: `alpha = pi/6` and the target is equilateral. -/
theorem bz_rational_all {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ} (h : D.model.TwoPiThreeData α a b c) (hNS : NotSim D)
    (hrat : ∃ r : ℚ, α = (r : ℝ) * Real.pi) :
    α = Real.pi / 6 ∧ ∀ j, D.target.angleAt j = Real.pi / 3 := by
  have hpi := Real.pi_pos
  obtain ⟨n, a', hn, ha, hg⟩ := bz_rational_exists D h hrat
  by_cases hcov : Covered3 n
  · exact bz_rational_classify D h hNS hn a' ha hg hcov
  exfalso
  have hnc : ¬ Covered n := fun hc => hcov (Or.inl hc)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have ha1 : ∀ k, 1 ≤ a' k := fun k => (nat_bounds hn (ha k) (angle_pos _ k) (angle_lt_pi _ k)).1
  have hsum' : ∑ k, a' k = n := sum_of_angles hn D.model a' ha
  have hd : ∀ d, (∀ i, d ∣ a' i) → d = 1 := by
    intro d hdd
    have := Nat.dvd_gcd (hdd 0) (Nat.dvd_gcd (hdd 1) (hdd 2))
    rw [hg] at this; exact Nat.dvd_one.mp this
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := id h
  have e1 : (a' (σ 0) : ℝ) * Real.pi / n + (a' (σ 1) : ℝ) * Real.pi / n = Real.pi / 3 := by
    rw [← ha, ← ha, h0, h1]; ring
  have e2 : (a' (σ 2) : ℝ) * Real.pi / n = 2 * Real.pi / 3 := by rw [← ha, h2]
  field_simp at e1 e2
  have hr1 : 3 * a' (σ 0) + 3 * a' (σ 1) = n := by
    have : ((3 * a' (σ 0) + 3 * a' (σ 1) : ℕ) : ℝ) = n := by
      push_cast; linarith [e1]
    exact_mod_cast this
  have h32 : 3 * a' (σ 2) = 2 * n := by
    have : ((3 * a' (σ 2) : ℕ) : ℝ) = ((2 * n : ℕ) : ℝ) := by
      push_cast; linarith [e2]
    exact_mod_cast this
  have hr2 : a' (σ 2) = 2 * a' (σ 0) + 2 * a' (σ 1) := by omega
  obtain ⟨idx, hidx⟩ := KConj.exists_idx D a' ha
  obtain ⟨htarget, hK0⟩ := KConj.lemmaK D hn a' ha idx hidx
  set f := KConj.fig D idx with hf
  have hupos : ∀ j, 0 < LemmaKStar.uu a' f j := fun j =>
    (nat_bounds hn (htarget j) (angle_pos _ j) (angle_lt_pi _ j)).1
  have hfne : ∀ j, f j ≠ 0 := by
    intro j h0'
    have := hupos j
    simp [LemmaKStar.uu, h0'] at this
  have hu : ∑ j, LemmaKStar.uu a' f j = n := sum_of_angles hn D.target _ htarget
  have hn3 : 3 ≤ n := by rw [← hsum', Fin.sum_univ_three]; have := ha1 0; have := ha1 1; have := ha1 2; omega
  have hK := (LemmaKStar.lemmaKStar hn3 ha1 hsum' hfne hu).1.mp hK0
  have h6 := uncov_core3 ha1 hsum' hd σ hr1 hr2 hfne hu hK hnc
  obtain ⟨τ, hτ⟩ := six_perm (fun j => LemmaKStar.uu a' f j) a' h6
  apply hNS
  refine ⟨τ, fun k => ?_⟩
  rw [htarget k, hτ k, ha]

end Erdos634.Lacz51Gen3

#print axioms Erdos634.Lacz51Gen3.n_small3
#print axioms Erdos634.Lacz51Gen3.uncov_core3
#print axioms Erdos634.Lacz51Gen3.bz_rational_all
