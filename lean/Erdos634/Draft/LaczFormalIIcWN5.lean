-- Draft/LaczFormalIIcWN5.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2/6.3, Route B, item B4 (main): `wind_pm_one`.
-- A simple closed polygon has a point off the polygon with winding number +1 or -1 (generic-height crossing sweep).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2/6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN4
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.Convex

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

/-- Side function of the line through `x0` with direction `d`. -/
noncomputable def sideFn (x0 d z : ℂ) : ℝ := ((z - x0) / d).im

theorem convex_side_pos (x0 d : ℂ) : Convex ℝ {z : ℂ | 0 < sideFn x0 d z} := by
  have hl : IsLinearMap ℝ (fun z : ℂ => (z / d).im) :=
    ⟨fun x y => by simp [add_div], fun c x => by rw [Complex.real_smul, mul_div_assoc]; simp⟩
  have := convex_halfSpace_gt hl (((x0) / d).im)
  convert this using 1
  ext z
  simp [sideFn, sub_div]

theorem convex_side_neg (x0 d : ℂ) : Convex ℝ {z : ℂ | sideFn x0 d z < 0} := by
  have hl : IsLinearMap ℝ (fun z : ℂ => (z / d).im) :=
    ⟨fun x y => by simp [add_div], fun c x => by rw [Complex.real_smul, mul_div_assoc]; simp⟩
  have := convex_halfSpace_lt hl (((x0) / d).im)
  convert this using 1
  ext z
  simp [sideFn, sub_div]

/-- Points of the edge line itself have side value `0`. -/
theorem sideFn_edge {a b : ℂ} {s : ℝ} (u : ℝ) : sideFn (a + s * (b - a)) (b - a) (a + u * (b - a)) = 0 := by
  unfold sideFn
  by_cases hd : b - a = 0
  · simp [hd]
  · have : (a + u * (b - a) - (a + s * (b - a))) / (b - a) = ((u - s : ℝ) : ℂ) := by
      push_cast; field_simp; ring
    rw [this]; simp

theorem sideFn_sidePt {a b : ℂ} (hd : b - a ≠ 0) (s t : ℝ) : sideFn (a + s * (b - a)) (b - a) (sidePt a b s t) = t := by
  unfold sideFn sidePt
  have : (a + s * (b - a) + t * I * (b - a) - (a + s * (b - a))) / (b - a) = t * I := by
    field_simp; ring
  rw [this]; simp

/-- **B4.**  A simple closed polygon has a point off it with winding number `+1` or `-1`.
`c` is a generic height (no vertex on the line `Im = c`) that the polygon crosses. -/
theorem wind_pm_one {p : Fin n → ℂ} (hs : SimplePoly p) (c : ℝ) (hc : ∀ i, (p i).im ≠ c)
    (hX : ∃ z ∈ edgeSet p, z.im = c) : ∃ z, z ∉ edgeSet p ∧ (wind p z = 1 ∨ wind p z = -1) := by
  -- leftmost crossing point
  have hXc : IsCompact (edgeSet p ∩ {z : ℂ | z.im = c}) :=
    (isCompact_edgeSet p).inter_right (isClosed_eq Complex.continuous_im continuous_const)
  obtain ⟨z1, hz1, hz1c⟩ := hX
  obtain ⟨x0, ⟨hx0E, hx0c⟩, hmin⟩ := hXc.exists_isMinOn ⟨z1, hz1, hz1c⟩ Complex.continuous_re.continuousOn
  have hmin' : ∀ z ∈ edgeSet p, z.im = c → x0.re ≤ z.re := fun z hz hzc => hmin ⟨hz, hzc⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx0E
  set a := p i with ha
  set b := p (i + 1) with hb
  rw [segment_eq_image'] at hi
  obtain ⟨s, ⟨hs0, hs1⟩, hxs⟩ := hi
  simp only [Complex.real_smul] at hxs
  have hai : a.im ≠ c := hc i
  have hbi : b.im ≠ c := hc (i + 1)
  have hs0' : 0 < s := by
    rcases hs0.lt_or_eq with h | h
    · exact h
    · exfalso; apply hai; rw [← hx0c, ← hxs, ← h]; simp
  have hs1' : s < 1 := by
    rcases hs1.lt_or_eq with h | h
    · exact h
    · exfalso; apply hbi; rw [← hx0c, ← hxs, h]; simp
  have himd : (b - a).im ≠ 0 := by
    intro h
    apply hai
    have h2 := congrArg Complex.im hxs
    simp at h2
    rw [Complex.sub_im] at h
    have : b.im = a.im := by linarith
    have hx : x0.im = c := hx0c
    rw [this] at h2
    have h3 : (s : ℝ) * (a.im - a.im) = 0 := by ring
    linarith
  have hd : b - a ≠ 0 := fun h => himd (by rw [h]; simp)
  -- x0 is on no other edge
  have hother : ∀ j, j ≠ i → sidePt a b s 0 ∉ segment ℝ (p j) (p (j + 1)) := by
    intro j hj hmem
    have hx : sidePt a b s 0 = x0 := by unfold sidePt; rw [← hxs]; simp
    rw [hx] at hmem
    have := (hs i j hj.symm x0 ⟨by rw [segment_eq_image']; exact ⟨s, ⟨hs0, hs1⟩, by simp only [Complex.real_smul]; exact hxs⟩, hmem⟩).1
    rcases this with h | h
    · exact hai (by rw [← hx0c, h])
    · exact hbi (by rw [← hx0c, h])
  have hx0 : sidePt a b s 0 = x0 := by unfold sidePt; rw [← hxs]; simp
  -- ball around x0 free of the other edges
  set E' : Set ℂ := ⋃ (j : Fin n) (_ : j ≠ i), segment ℝ (p j) (p (j + 1)) with hE'
  have hE'c : IsClosed E' := isClosed_iUnion_of_finite fun j => isClosed_iUnion_of_finite fun _ => isClosed_segment' _ _
  have hxE' : x0 ∉ E' := by
    simp only [hE', Set.mem_iUnion, not_exists]
    intro j hj; rw [← hx0]; exact hother j hj
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hE'c.isOpen_compl x0 hxE'
  -- the leftward point y and its winding number
  set ε : ℝ := r / 2 with hε
  have hεpos : 0 < ε := by positivity
  set y : ℂ := x0 - ε with hy
  have hy_im : y.im = c := by
    have : x0.im = c := hx0c
    simp [hy, this]
  have hy_re : y.re = x0.re - ε := by simp [hy]
  obtain ⟨w0, hw0im, hw0re, hw0⟩ := exists_far_left p c y.re
  have hwy : wind p y = 0 := by
    rw [← hw0]
    symm
    apply wind_const_segment
    intro z hz hzE
    rw [segment_eq_image'] at hz
    obtain ⟨θ, ⟨h0, h1⟩, hzθ⟩ := hz
    have hzim : z.im = c := by
      rw [← hzθ]; simp [hw0im, hy_im]
    have hzre : z.re ≤ y.re := by
      rw [← hzθ]; simp
      nlinarith
    have := hmin' z hzE hzim
    linarith
  -- y is within r of x0
  have hyball : y ∈ Metric.ball x0 r := by
    rw [Metric.mem_ball, hy]; simp [abs_of_pos hεpos]; linarith
  have hnoE : ∀ z ∈ Metric.ball x0 r, z ∉ E' := fun z hz => hball hz
  have hside_edge : ∀ u : ℝ, sideFn x0 (b - a) (a + u * (b - a)) = 0 := by
    intro u; rw [← hxs]; exact sideFn_edge u
  have hside_pt : ∀ t : ℝ, sideFn x0 (b - a) (sidePt a b s t) = t := by
    intro t; rw [← hxs]; exact sideFn_sidePt hd s t
  have hsy : sideFn x0 (b - a) y = ε * ((b - a).im / Complex.normSq (b - a)) := by
    unfold sideFn
    have : (y - x0) / (b - a) = ((-ε : ℝ) : ℂ) / (b - a) := by simp [hy]
    rw [this, Complex.div_im]
    simp [Complex.normSq_apply]
    field_simp
  have hnsq : 0 < Complex.normSq (b - a) := Complex.normSq_pos.2 hd
  -- a segment inside the ball and strictly on one side avoids the polygon
  have hseg : ∀ u v : ℂ, u ∈ Metric.ball x0 r → v ∈ Metric.ball x0 r →
      ((0 < sideFn x0 (b - a) u ∧ 0 < sideFn x0 (b - a) v) ∨ (sideFn x0 (b - a) u < 0 ∧ sideFn x0 (b - a) v < 0)) →
      ∀ z ∈ segment ℝ u v, z ∉ edgeSet p := by
    intro u v hu hv hside z hz hzE
    have hzb : z ∈ Metric.ball x0 r := (convex_ball x0 r).segment_subset hu hv hz
    have hzside : 0 < sideFn x0 (b - a) z ∨ sideFn x0 (b - a) z < 0 := by
      rcases hside with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ((convex_side_pos x0 (b - a)).segment_subset h1 h2 hz)
      · exact Or.inr ((convex_side_neg x0 (b - a)).segment_subset h1 h2 hz)
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hzE
    by_cases hji : j = i
    · subst hji
      rw [segment_eq_image'] at hj
      obtain ⟨u', -, hu'⟩ := hj
      simp only [Complex.real_smul] at hu'
      have := hside_edge u'
      rw [hu'] at this
      rcases hzside with h | h <;> linarith
    · exact hnoE z hzb (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hji, hj⟩⟩)
  have hjump := wind_jump p i hd hs0' hs1' hother
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < r / (‖b - a‖ + 1) :=
    (eventually_lt_nhds (by positivity : (0 : ℝ) < r / (‖b - a‖ + 1))).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ⟨hL, hR, hLR⟩, htδ, htpos⟩ := (hjump.and (hsmall.and self_mem_nhdsWithin)).exists
  have ht : (0 : ℝ) < t := htpos
  have hdist : ∀ t' : ℝ, |t'| < r / (‖b - a‖ + 1) → sidePt a b s t' ∈ Metric.ball x0 r := by
    intro t' h
    rw [Metric.mem_ball, dist_eq_norm]
    have : sidePt a b s t' - x0 = (t' : ℂ) * I * (b - a) := by
      unfold sidePt; rw [← hxs]; ring
    rw [this, norm_mul, norm_mul]
    simp only [Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    have h1 : |t'| * (‖b - a‖ + 1) < r := by
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < ‖b - a‖ + 1)).1 h
      linarith
    nlinarith [abs_nonneg t', norm_nonneg (b - a)]
  have hLb := hdist t (by rw [abs_of_pos ht]; exact htδ)
  have hRb := hdist (-t) (by rw [abs_neg, abs_of_pos ht]; exact htδ)
  rcases lt_or_gt_of_ne himd with hneg | hpos
  · -- Im d < 0: y is on the right side
    have hsy' : sideFn x0 (b - a) y < 0 := by
      rw [hsy]; exact mul_neg_of_pos_of_neg hεpos (div_neg_of_neg_of_pos hneg hnsq)
    have hRs : sideFn x0 (b - a) (sidePt a b s (-t)) < 0 := by rw [hside_pt]; linarith
    have hw : wind p (sidePt a b s (-t)) = wind p y :=
      wind_const_segment p (hseg _ _ hRb hyball (Or.inr ⟨hRs, hsy'⟩))
    refine ⟨sidePt a b s t, hL, Or.inl ?_⟩
    rw [hLR, hw, hwy]; ring
  · have hsy' : 0 < sideFn x0 (b - a) y := by
      rw [hsy]; exact mul_pos hεpos (div_pos hpos hnsq)
    have hLs : 0 < sideFn x0 (b - a) (sidePt a b s t) := by rw [hside_pt]; exact ht
    have hw : wind p (sidePt a b s t) = wind p y :=
      wind_const_segment p (hseg _ _ hLb hyball (Or.inl ⟨hLs, hsy'⟩))
    refine ⟨sidePt a b s (-t), hR, Or.inr ?_⟩
    have : wind p (sidePt a b s (-t)) = wind p (sidePt a b s t) - 1 := by linarith
    rw [this, hw, hwy]; ring

end Erdos634.Draft.LaczFormal.WN
