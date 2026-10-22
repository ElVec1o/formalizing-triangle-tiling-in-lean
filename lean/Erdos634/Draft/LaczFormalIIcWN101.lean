-- Draft/LaczFormalIIcWN101.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3, p. 359-360), Lemma 6.2, R3 (pure convex geometry): "the segment XW is in the exterior of C1".
-- (1) `wind_zero_of_ray`, `wind_zero_of_halfplane`: a point on the far side of a line that has the whole polygon strictly on its other side has winding number 0 (used for a vertex of A against the corner polygon q inside A);
-- (2) `wind_ne_of_inside`: a point strictly inside every edge half-plane of a polygon has nonzero winding number;
-- (3) `edge_of_zero`: a point weakly inside every half-plane of a strictly convex polygon and ON the line of an edge lies on that edge;
-- (4) `chord_outside`: a segment from a point `x` of winding number 0 (off the polygon) whose open part misses a strictly convex polygon `q` stays strictly outside some half-plane of `q` on `[0, 1)` (the `out` field of `RingSetup`).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN82
import Erdos634.Draft.LaczFormalIIcWN57

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

theorem wind_zero_of_ray (p : Fin n → ℂ) (z nvec : ℂ) (hn : nvec ≠ 0) (h : ∀ t : ℝ, 0 ≤ t → z + (t : ℂ) * nvec ∉ edgeSet p) : wind p z = 0 := by
  obtain ⟨K, hK, hKs⟩ := Filter.mem_cocompact.1 (wind_eventually_zero p)
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  have hnn : 0 < ‖nvec‖ := norm_pos_iff.2 hn
  set T : ℝ := (max R 0 + ‖z‖ + 1) / ‖nvec‖ with hT
  have hT0 : 0 ≤ T := by
    have := le_max_right R 0
    have := norm_nonneg z
    rw [hT]; positivity
  have hfar : wind p (z + (T : ℂ) * nvec) = 0 := by
    apply hKs
    intro hmem
    have h1 := hR hmem
    rw [mem_closedBall_zero_iff] at h1
    have h0 : ‖(T : ℂ) * nvec‖ = T * ‖nvec‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hT0]
    have h2 : ‖(T : ℂ) * nvec‖ ≤ ‖z + (T : ℂ) * nvec‖ + ‖z‖ := by
      calc ‖(T : ℂ) * nvec‖ = ‖(z + (T : ℂ) * nvec) - z‖ := by ring_nf
        _ ≤ ‖z + (T : ℂ) * nvec‖ + ‖z‖ := norm_sub_le _ _
    have h3 : T * ‖nvec‖ = max R 0 + ‖z‖ + 1 := by rw [hT]; field_simp
    have := le_max_left R 0
    linarith
  rw [← hfar]
  apply wind_const_segment
  intro w hw
  rw [segment_eq_image'] at hw
  obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hw
  beta_reduce
  have : z + s • (z + (T : ℂ) * nvec - z) = z + ((s * T : ℝ) : ℂ) * nvec := by rw [Complex.real_smul]; push_cast; ring
  rw [this]
  exact h (s * T) (mul_nonneg hs0 hT0)

theorem wind_zero_of_halfplane (p : Fin n → ℂ) (a e : ℂ) (he : e ≠ 0) (hp : ∀ i, 0 < sideFn a e (p i)) (z : ℂ) (hz : sideFn a e z ≤ 0) :
    wind p z = 0 := by
  apply wind_zero_of_ray p z (-(Complex.I * e)) (by simp [he])
  intro t ht hmem
  have hs : sideFn a e (z + (t : ℂ) * (-(Complex.I * e))) = sideFn a e z - t := by
    unfold sideFn
    have : (z + (t : ℂ) * (-(Complex.I * e)) - a) / e = (z - a) / e + ((-t : ℝ) : ℂ) * Complex.I := by
      push_cast; field_simp; ring
    rw [this, Complex.add_im]
    simp
    ring
  unfold edgeSet at hmem
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hmem
  rw [segment_eq_image'] at hi
  obtain ⟨s, ⟨hs0, hs1⟩, hsx⟩ := hi
  have hpos : 0 < sideFn a e (z + (t : ℂ) * (-(Complex.I * e))) := by
    rw [← hsx]
    beta_reduce
    rw [Complex.real_smul, sideFn_lin]
    have hA := hp i
    have hB := hp (i + 1)
    rcases hs0.eq_or_lt with h0 | h0
    · rw [← h0]; simpa using hA
    · nlinarith [mul_pos h0 hB, mul_nonneg (sub_nonneg.2 hs1) hA.le]
  linarith

theorem wind_ne_of_inside (q : Fin n → ℂ) (τ : ℝ) (hτ : τ = 1 ∨ τ = -1) (z : ℂ)
    (h : ∀ j : Fin n, 0 < τ * sideFn (q j) (q (j + 1) - q j) z) : wind q z ≠ 0 := by
  have key : ∀ j : Fin n, 0 < τ * angStep q z j := by
    intro j
    have hs := h j
    set d := q (j + 1) - q j with hd
    have hd0 : d ≠ 0 := by
      intro h0; rw [h0] at hs; simp [sideFn] at hs
    set w := (z - q j) / d with hw
    have hw0 : w ≠ 0 := by
      intro h0
      have : sideFn (q j) d z = 0 := by unfold sideFn; rw [← hw, h0]; simp
      rw [this] at hs; simp at hs
    have ha : q j - z = -(d * w) := by rw [hw]; field_simp; ring
    have hb : q (j + 1) - z = d * (1 - w) := by rw [hd] at *; rw [show q (j + 1) - z = (q (j + 1) - q j) + (q j - z) from by ring, ha]; ring
    have hratio : (q (j + 1) - z) / (q j - z) = 1 - w⁻¹ := by
      rw [hb, ha]
      have hdw : d * w ≠ 0 := mul_ne_zero hd0 hw0
      field_simp
      ring
    have him : ((q (j + 1) - z) / (q j - z)).im = w.im / Complex.normSq w := by
      rw [hratio, Complex.sub_im, Complex.inv_im]; simp; ring
    have hwim : τ * w.im > 0 := by unfold sideFn at hs; rw [← hw] at hs; exact hs
    have hnsq : 0 < Complex.normSq w := Complex.normSq_pos.2 hw0
    unfold angStep
    rcases hτ with rfl | rfl
    · have him' : 0 < ((q (j + 1) - z) / (q j - z)).im := by rw [him]; exact div_pos (by linarith) hnsq
      have h1 : 0 ≤ Complex.arg ((q (j + 1) - z) / (q j - z)) := Complex.arg_nonneg_iff.2 him'.le
      have h2 : Complex.arg ((q (j + 1) - z) / (q j - z)) ≠ 0 := by
        intro h0; rw [Complex.arg_eq_zero_iff] at h0; linarith [h0.2]
      have := lt_of_le_of_ne h1 (Ne.symm h2)
      linarith
    · have him' : ((q (j + 1) - z) / (q j - z)).im < 0 := by
        rw [him]; exact div_neg_of_neg_of_pos (by linarith) hnsq
      have h1 : Complex.arg ((q (j + 1) - z) / (q j - z)) < 0 := Complex.arg_neg_iff.2 him'
      linarith
  have hsum : 0 < τ * turnSum q z := by
    unfold turnSum
    rw [Finset.mul_sum]
    exact Finset.sum_pos (fun j _ => key j) Finset.univ_nonempty
  intro hw0
  unfold wind at hw0
  have : turnSum q z = 0 := by
    have hpi := Real.pi_pos
    field_simp at hw0; simpa using hw0
  rw [this] at hsum; simp at hsum

end Erdos634.Draft.LaczFormal.WN
