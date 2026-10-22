-- Draft/LaczFormalIIcWN82.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3, p. 359), Lemma 6.2, R1: SELECTION OF THE OUTERMOST CYCLE (pure winding-number geometry).
-- Printed: "the cycles are nested, C_{i+1} in C_i-interior"; C_1 is the one that contains all the others.  Here: finitely many pairwise disjoint closed polygons with a common point z of nonzero winding
-- number have an OUTERMOST member `a`: every other polygon lies in the degree-region `{wind (p a) <> 0}` of `p a`.
-- Route: a point `e` of maximal real part on the union lies on some `p a`; if `p a` lay in the degree region of `p b` (b <> a), then `wind (p b) e <> 0` is locally constant near `e` but vanishes to the right of `p b`.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN31

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

/-- The winding number vanishes at a point strictly to the right of the whole polygon. -/
theorem wind_zero_of_right (p : Fin n → ℂ) (x : ℂ) (h : ∀ z ∈ edgeSet p, z.re < x.re) : wind p x = 0 := by
  obtain ⟨K, hK, hKs⟩ := Filter.mem_cocompact.1 (wind_eventually_zero p)
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  set t : ℝ := max R 0 + |x.re| + |x.im| + 1 with ht
  have htpos : 0 < t := by
    have := le_max_right R 0
    have := abs_nonneg x.re
    have := abs_nonneg x.im
    rw [ht]; linarith
  set y : ℂ := x + (t : ℂ) with hy
  have hyre : y.re = x.re + t := by simp [hy]
  have hyim : y.im = x.im := by simp [hy]
  have hy0 : wind p y = 0 := by
    apply hKs
    intro hmem
    have h1 := hR hmem
    rw [mem_closedBall_zero_iff] at h1
    have h2 := Complex.abs_re_le_norm y
    have h4 := neg_abs_le x.re
    have h5 := le_max_left R 0
    have h6 := abs_nonneg x.im
    have h7 := le_abs_self (x.re + t)
    rw [hyre] at h2
    have h8 : t = max R 0 + |x.re| + |x.im| + 1 := ht
    linarith
  rw [← hy0]
  apply wind_const_segment
  intro z hz hzE
  have hz' : z ∈ segment ℝ x y := hz
  rw [segment_eq_image'] at hz'
  obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hz'
  have := h _ hzE
  have hre : (x + s • (y - x)).re = x.re + s * t := by simp [hy]
  rw [hre] at this
  nlinarith

variable {n' : ℕ} [NeZero n']

/-- Core of R1: if `p` contains a point `e` of maximal real part of `p` and `q` together, and the disjoint polygons `p`, `q` share a point of nonzero winding number, then `q` lies in the degree region of `p`. -/
theorem outer_of_maxre (p : Fin n → ℂ) (q : Fin n' → ℂ) (hd : Disjoint (edgeSet p) (edgeSet q)) {e : ℂ} (he : e ∈ edgeSet p)
    (hmax : ∀ w ∈ edgeSet q, w.re ≤ e.re) {z : ℂ} (hzp : z ∉ edgeSet p) (hzq : z ∉ edgeSet q) (h1 : wind p z ≠ 0) (h2 : wind q z ≠ 0) :
    ∀ x ∈ edgeSet q, wind p x ≠ 0 := by
  rcases nesting_dichotomy p q hd hzp hzq h1 h2 with h | h
  · exact h
  · exfalso
    have hWe : wind q e ≠ 0 := h e he
    have heq : e ∉ edgeSet q := fun hh => Set.disjoint_left.1 hd he hh
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (wind_eventually_nhds q heq)
    have hy := hball (y := e + ((δ / 2 : ℝ) : ℂ)) (by
      rw [dist_eq_norm]; simp [Complex.norm_real, abs_of_pos hδ]; linarith)
    have hy0 : wind q (e + ((δ / 2 : ℝ) : ℂ)) = 0 := by
      apply wind_zero_of_right
      intro w hw
      have := hmax w hw
      simp
      linarith
    exact hWe (by rw [← hy, hy0])

/-- **R1 (abstract).**  Finitely many pairwise disjoint closed polygons with a common point `z` of nonzero winding number have an outermost member:
every other polygon lies in the degree region `{wind <> 0}` of it. -/
theorem outermost_cycle {ι : Type*} [Fintype ι] [Nonempty ι] {nn : ι → ℕ} [∀ a, NeZero (nn a)] (p : ∀ a, Fin (nn a) → ℂ)
    (hdisj : ∀ a b, a ≠ b → Disjoint (edgeSet (p a)) (edgeSet (p b)))
    {z : ℂ} (hz : ∀ a, z ∉ edgeSet (p a) ∧ wind (p a) z ≠ 0) :
    ∃ a, ∀ b, b ≠ a → ∀ x ∈ edgeSet (p b), wind (p a) x ≠ 0 := by
  set U : Set ℂ := ⋃ a, edgeSet (p a) with hU
  have hUc : IsCompact U := isCompact_iUnion fun a => isCompact_edgeSet (p a)
  have hUne : U.Nonempty := by
    obtain ⟨a⟩ := ‹Nonempty ι›
    exact ⟨p a 0, Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨0, left_mem_segment ℝ _ _⟩⟩⟩
  obtain ⟨e, he, hmax⟩ := hUc.exists_isMaxOn hUne Complex.continuous_re.continuousOn
  obtain ⟨a0, ha0⟩ := Set.mem_iUnion.1 he
  refine ⟨a0, fun b hb => ?_⟩
  exact outer_of_maxre (p a0) (p b) (hdisj a0 b (Ne.symm hb)) ha0
    (fun w hw => hmax (Set.mem_iUnion.2 ⟨b, hw⟩)) (hz a0).1 (hz b).1 (hz a0).2 (hz b).2

#print axioms wind_zero_of_right
#print axioms outermost_cycle

end Erdos634.Draft.LaczFormal.WN
