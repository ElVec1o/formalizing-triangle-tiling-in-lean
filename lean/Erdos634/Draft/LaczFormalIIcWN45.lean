-- Draft/LaczFormalIIcWN45.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, Lemma 6.2 (`IIcNoKites`), step (h), part 6:
-- `chord_signs`: cutting a simple polygon q along a chord whose open part misses q and along which `wind q = c`: the two pieces have orientations
-- sigma1 = - sigma2 if c = 0 (exterior chord) and sigma1 = sigma2 = c if c <> 0 (interior chord).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN44

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

theorem arcEdge_sub (q : Fin n → ℂ) (a : Fin n) {d : ℕ} (j : Fin (d + 1)) (hj : j ≠ Fin.last d) :
    segment ℝ (arcPoly q a d j) (arcPoly q a d (j + 1)) ⊆ edgeSet q := by
  have hjlt : j.val < d := by
    have := j.isLt
    have : j.val ≠ d := fun h' => hj (Fin.ext (by simpa using h'))
    omega
  obtain ⟨e1, e2⟩ := edge_lt q a j hjlt
  rw [e1, e2]
  intro z hz
  refine Set.mem_iUnion.2 ⟨phi a j.val, ?_⟩
  rw [phi_succ] at hz
  exact hz

theorem sidePt_swap (A B : ℂ) (t : ℝ) : sidePt B A (1 / 2) t = sidePt A B (1 / 2) (-t) := by
  simp only [sidePt]; push_cast; ring

theorem sidePt_swap' (A B : ℂ) (t : ℝ) : sidePt B A (1 / 2) (-t) = sidePt A B (1 / 2) t := by
  simp only [sidePt]; push_cast; ring

theorem chord_signs {q : Fin n → ℂ} (hinj : Function.Injective q) (a : Fin n) {d : ℕ} (hd2 : 2 ≤ d) (hdn : d + 2 ≤ n)
    (hopen : ∀ s : ℝ, 0 < s → s < 1 → q (phi a d) + (s : ℂ) * (q a - q (phi a d)) ∉ edgeSet q)
    {σ1 σ2 c : ℝ} (O1 : Dich (arcPoly q a d) σ1) (O2 : Dich (arcPoly q (phi a d) (n - d)) σ2)
    (hc : wind q (q (phi a d) + ((1 / 2 : ℝ) : ℂ) * (q a - q (phi a d))) = c) :
    (c = 0 → σ1 = -σ2) ∧ (c ≠ 0 → σ1 = c ∧ σ2 = c) := by
  set A := q (phi a d) with hA
  set B := q a with hB
  have hd : B - A ≠ 0 := by
    intro h
    have h2 : phi a d = phi a 0 := hinj (by rw [phi_zero]; exact (sub_eq_zero.1 h).symm)
    have := phi_inj_nat a (by omega) (by omega) h2
    omega
  have hx : A + ((1 / 2 : ℝ) : ℂ) * (B - A) ∉ edgeSet q := hopen (1 / 2) (by norm_num) (by norm_num)
  -- jump for the piece 1
  have hd1 : arcPoly q a d (Fin.last d + 1) - arcPoly q a d (Fin.last d) ≠ 0 := by
    rw [arcPoly_last_succ, arcPoly_last]; exact hd
  have hoth1 : ∀ j, j ≠ Fin.last d → sidePt (arcPoly q a d (Fin.last d)) (arcPoly q a d (Fin.last d + 1)) (1 / 2) 0 ∉
      segment ℝ (arcPoly q a d j) (arcPoly q a d (j + 1)) := by
    intro j hj hm
    apply hx
    have := arcEdge_sub q a j hj hm
    rw [arcPoly_last_succ, arcPoly_last] at this
    simpa [sidePt] using this
  have j1 := wind_jump (arcPoly q a d) (Fin.last d) hd1 (s := 1 / 2) (by norm_num) (by norm_num) hoth1
  rw [arcPoly_last_succ, arcPoly_last] at j1
  -- jump for the piece 2
  have hlast2 : arcPoly q (phi a d) (n - d) (Fin.last (n - d)) = B := by
    rw [arcPoly_last, phi_phi_last a (by omega)]
  have hlast2' : arcPoly q (phi a d) (n - d) (Fin.last (n - d) + 1) = A := by
    rw [arcPoly_last_succ]
  have hd2' : arcPoly q (phi a d) (n - d) (Fin.last (n - d) + 1) - arcPoly q (phi a d) (n - d) (Fin.last (n - d)) ≠ 0 := by
    rw [hlast2, hlast2']
    intro h; apply hd; linear_combination -h
  have hoth2 : ∀ j, j ≠ Fin.last (n - d) → sidePt (arcPoly q (phi a d) (n - d) (Fin.last (n - d)))
      (arcPoly q (phi a d) (n - d) (Fin.last (n - d) + 1)) (1 / 2) 0 ∉
      segment ℝ (arcPoly q (phi a d) (n - d) j) (arcPoly q (phi a d) (n - d) (j + 1)) := by
    intro j hj hm
    apply hx
    have := arcEdge_sub q (phi a d) j hj hm
    rw [hlast2, hlast2'] at this
    have e : sidePt B A (1 / 2) 0 = A + ((1 / 2 : ℝ) : ℂ) * (B - A) := by simp [sidePt]; ring
    rw [e] at this
    exact this
  have j2 := wind_jump (arcPoly q (phi a d) (n - d)) (Fin.last (n - d)) hd2' (s := 1 / 2) (by norm_num) (by norm_num) hoth2
  rw [hlast2, hlast2'] at j2
  have j2' : ∀ᶠ t in 𝓝[>] (0 : ℝ), (sidePt A B (1 / 2) (-t) ∉ edgeSet (arcPoly q (phi a d) (n - d)) ∧
      sidePt A B (1 / 2) t ∉ edgeSet (arcPoly q (phi a d) (n - d)) ∧
      wind (arcPoly q (phi a d) (n - d)) (sidePt A B (1 / 2) (-t)) = wind (arcPoly q (phi a d) (n - d)) (sidePt A B (1 / 2) t) + 1) :=
    j2.mono (fun t h => by rw [sidePt_swap A B t, sidePt_swap' A B t] at h; exact h)
  -- local constancy of wind q at x
  obtain ⟨ε, hε, hlc⟩ := wind_locallyConstant q (A + ((1 / 2 : ℝ) : ℂ) * (B - A)) hx
  have hBA : 0 < ‖B - A‖ := norm_pos_iff.2 hd
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < ε / ‖B - A‖ := by
    have := Ioo_mem_nhdsGT (show (0 : ℝ) < ε / ‖B - A‖ by positivity)
    filter_upwards [this] with t ht using ht.2
  obtain ⟨t, ⟨hL1, hR1, hjump1⟩, ⟨hR2, hL2, hjump2⟩, ht, htpos⟩ := (j1.and (j2'.and (hsmall.and eventually_mem_nhdsWithin))).exists
  have hdist : ∀ τ : ℝ, |τ| < ε / ‖B - A‖ → dist (sidePt A B (1 / 2) τ) (A + ((1 / 2 : ℝ) : ℂ) * (B - A)) < ε := by
    intro τ hτ
    rw [dist_eq_norm]
    have e : sidePt A B (1 / 2) τ - (A + ((1 / 2 : ℝ) : ℂ) * (B - A)) = (τ : ℂ) * I * (B - A) := by
      simp [sidePt]
    rw [e, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    rwa [lt_div_iff₀ hBA] at hτ
  have ht0 : 0 < t := htpos
  have hLq := hlc (sidePt A B (1 / 2) t) (hdist t (by rw [abs_of_pos ht0]; exact ht))
  have hRq := hlc (sidePt A B (1 / 2) (-t)) (hdist (-t) (by rw [abs_neg, abs_of_pos ht0]; exact ht))
  have hsL := wind_split q a (by omega : d ≤ n) hLq.1 (sidePt_not_mem_segment (a := A) (b := B) hd (1 / 2) ht0.ne')
  have hsR := wind_split q a (by omega : d ≤ n) hRq.1 (sidePt_not_mem_segment (a := A) (b := B) hd (1 / 2) (neg_ne_zero.2 ht0.ne'))
  have hcL : wind q (sidePt A B (1 / 2) t) = c := by rw [hLq.2, hc]
  have hA1 := O1.2 _ hL1
  have hA1' := O1.2 _ hR1
  have hB1 := O2.2 _ hL2
  have hB1' := O2.2 _ hR2
  refine sign_arith (A := wind (arcPoly q a d) (sidePt A B (1 / 2) t)) (B := wind (arcPoly q (phi a d) (n - d)) (sidePt A B (1 / 2) t))
    O1.1 O2.1 hA1 ?_ hB1 ?_ (by rw [← hsL, hcL])
  · rcases hA1' with h | h
    · left; linarith
    · right; linarith
  · rcases hB1' with h | h
    · left; linarith
    · right; linarith

end Erdos634.Draft.LaczFormal.WN
