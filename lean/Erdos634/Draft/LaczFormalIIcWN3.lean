-- Draft/LaczFormalIIcWN3.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2/6.3, Route B (winding-number interior), item B2:
-- the winding number jumps by exactly +1 when one crosses an edge of a closed polygon from its right to its left (at a point lying on no other edge).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN1

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

/-- The point at parameter `s` on the directed edge `a -> b`, displaced by `t` times the left normal `I (b - a)` (`t > 0` is the left side). -/
noncomputable def sidePt (a b : ℂ) (s t : ℝ) : ℂ := a + s * (b - a) + t * I * (b - a)

/-- The model ratio `(b - z)/(a - z)` at `z = sidePt a b s t`, with the edge vector cancelled. -/
noncomputable def rr (s t : ℝ) : ℂ := (((1 - s : ℝ) : ℂ) - t * I) / (((-s : ℝ) : ℂ) - t * I)

theorem ratio_sidePt {a b : ℂ} (hd : b - a ≠ 0) (s t : ℝ) :
    (b - sidePt a b s t) / (a - sidePt a b s t) = rr s t := by
  unfold sidePt rr
  have h1 : b - (a + s * (b - a) + t * I * (b - a)) = (b - a) * (((1 - s : ℝ) : ℂ) - t * I) := by push_cast; ring
  have h2 : a - (a + s * (b - a) + t * I * (b - a)) = (b - a) * (((-s : ℝ) : ℂ) - t * I) := by push_cast; ring
  rw [h1, h2, mul_div_mul_left _ _ hd]

theorem rr_im (s t : ℝ) : (rr s t).im = t / (s ^ 2 + t ^ 2) := by
  by_cases h : s ^ 2 + t ^ 2 = 0
  · have hs : s = 0 := by nlinarith [sq_nonneg s, sq_nonneg t]
    have ht : t = 0 := by nlinarith [sq_nonneg s, sq_nonneg t]
    subst hs; subst ht; simp [rr]
  · simp [rr, Complex.div_im, Complex.normSq_apply]
    field_simp
    ring

theorem rr_zero {s : ℝ} (hs : 0 < s) : rr s 0 = (((1 - s) / (-s) : ℝ) : ℂ) := by
  simp [rr, Complex.ofReal_div]

theorem rr_continuousAt {s : ℝ} (hs : 0 < s) : ContinuousAt (rr s) 0 := by
  unfold rr
  refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
  simp
  exact hs.ne'

theorem rr_arg_pos {s : ℝ} (hs : 0 < s) (hs1 : s < 1) : Tendsto (fun t => Complex.arg (rr s t)) (𝓝[>] 0) (𝓝 Real.pi) := by
  have hre : ((((1 - s) / (-s) : ℝ)) : ℂ).re < 0 := by
    rw [Complex.ofReal_re]; exact div_neg_of_pos_of_neg (sub_pos.2 hs1) (neg_neg_of_pos hs)
  have hlim : Tendsto (rr s) (𝓝[>] 0) (𝓝[{z : ℂ | 0 ≤ z.im}] (((1 - s) / (-s) : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := (rr_continuousAt hs).tendsto
      rw [rr_zero hs] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_setOf_eq, rr_im]
      have : (0 : ℝ) < t := ht
      positivity
  exact (Complex.tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero hre (Complex.ofReal_im _)).comp hlim

theorem rr_arg_neg {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    Tendsto (fun t => Complex.arg (rr s (-t))) (𝓝[>] 0) (𝓝 (-Real.pi)) := by
  have hre : ((((1 - s) / (-s) : ℝ)) : ℂ).re < 0 := by
    rw [Complex.ofReal_re]; exact div_neg_of_pos_of_neg (sub_pos.2 hs1) (neg_neg_of_pos hs)
  have hlim : Tendsto (fun t => rr s (-t)) (𝓝[>] 0) (𝓝[{z : ℂ | z.im < 0}] (((1 - s) / (-s) : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h1 : ContinuousAt (fun t : ℝ => rr s (-t)) 0 := by
        have := rr_continuousAt hs
        simp only [neg_zero] at this
        exact ContinuousAt.comp_of_eq (g := rr s) (f := fun t : ℝ => -t) this continuous_neg.continuousAt (by simp)
      have := h1.tendsto
      simp only [neg_zero, rr_zero hs] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_setOf_eq, rr_im]
      have : (0 : ℝ) < t := ht
      have : 0 < s ^ 2 + (-t) ^ 2 := by positivity
      exact div_neg_of_neg_of_pos (by linarith) this
  exact (Complex.tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero hre (Complex.ofReal_im _)).comp hlim

theorem angStep_continuousAt (p : Fin n → ℂ) (z : ℂ) (j : Fin n) (hz : z ∉ segment ℝ (p j) (p (j + 1))) :
    ContinuousAt (fun w => angStep p w j) z := by
  have ha : p j - z ≠ 0 := fun h => hz (by rw [← sub_eq_zero.1 h]; exact left_mem_segment ℝ _ _)
  have hcont : ContinuousAt (fun w : ℂ => (p (j + 1) - w) / (p j - w)) z :=
    (continuousAt_const.sub continuousAt_id).div (continuousAt_const.sub continuousAt_id) ha
  exact ContinuousAt.comp (f := fun w : ℂ => (p (j + 1) - w) / (p j - w)) (Complex.continuousAt_arg (ratio_mem_slitPlane hz)) hcont

theorem sidePt_not_mem_segment {a b : ℂ} (hd : b - a ≠ 0) (s : ℝ) {t : ℝ} (ht : t ≠ 0) :
    sidePt a b s t ∉ segment ℝ a b := by
  rw [segment_eq_image']
  rintro ⟨u, -, hu⟩
  simp only [sidePt, Complex.real_smul] at hu
  have h1 : ((u : ℂ) - s - t * I) * (b - a) = 0 := by linear_combination hu
  have h2 := (mul_eq_zero.1 h1).resolve_right hd
  have := congrArg Complex.im h2
  simp at this
  exact ht this

/-- **B2.**  Let `x = p i + s (p (i+1) - p i)`, `0 < s < 1`, lie on no other edge.  Then for small `t > 0` the points `x ± t I (p(i+1) - p i)`
are off the polygon and the winding number is exactly one larger on the left side. -/
theorem wind_jump (p : Fin n → ℂ) (i : Fin n) (hd : p (i + 1) - p i ≠ 0) {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hother : ∀ j, j ≠ i → sidePt (p i) (p (i + 1)) s 0 ∉ segment ℝ (p j) (p (j + 1))) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), sidePt (p i) (p (i + 1)) s t ∉ edgeSet p ∧ sidePt (p i) (p (i + 1)) s (-t) ∉ edgeSet p ∧
      wind p (sidePt (p i) (p (i + 1)) s t) = wind p (sidePt (p i) (p (i + 1)) s (-t)) + 1 := by
  set a := p i with ha
  set b := p (i + 1) with hb
  have hsp : Continuous (fun t : ℝ => sidePt a b s t) := by unfold sidePt; fun_prop
  -- off the polygon
  set E' : Set ℂ := ⋃ (j : Fin n) (_ : j ≠ i), segment ℝ (p j) (p (j + 1)) with hE'
  have hE'c : IsClosed E' := isClosed_iUnion_of_finite fun j => isClosed_iUnion_of_finite fun _ => isClosed_segment' _ _
  have hxE' : sidePt a b s 0 ∉ E' := by
    simp only [hE', Set.mem_iUnion, not_exists]
    exact fun j hj => hother j hj
  have hev1 : ∀ᶠ t in 𝓝 (0 : ℝ), sidePt a b s t ∉ E' := hsp.continuousAt.eventually_mem (hE'c.isOpen_compl.mem_nhds hxE')
  have hev2 : ∀ᶠ t in 𝓝 (0 : ℝ), sidePt a b s (-t) ∉ E' :=
    (hsp.comp continuous_neg).continuousAt.eventually_mem (hE'c.isOpen_compl.mem_nhds (by simpa using hxE'))
  have hoff : ∀ t : ℝ, t ≠ 0 → sidePt a b s t ∉ E' → sidePt a b s t ∉ edgeSet p := by
    intro t ht hE hmem
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hmem
    by_cases hji : j = i
    · subst hji; exact sidePt_not_mem_segment hd s ht hj
    · exact hE (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hji, hj⟩⟩)
  -- limit of the difference
  set S : ℝ → ℝ := fun t => ∑ j ∈ Finset.univ.erase i, angStep p (sidePt a b s t) j with hS
  have hSc : ContinuousAt S 0 := by
    refine tendsto_finsetSum _ fun j hj => ?_
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    exact ContinuousAt.comp_of_eq (f := fun t : ℝ => sidePt a b s t) (angStep_continuousAt p _ j (hother j hji)) hsp.continuousAt rfl
  have hS1 : Tendsto S (𝓝[>] 0) (𝓝 (S 0)) := hSc.tendsto.mono_left nhdsWithin_le_nhds
  have hS2 : Tendsto (fun t => S (-t)) (𝓝[>] 0) (𝓝 (S 0)) := by
    have : ContinuousAt (fun t : ℝ => S (-t)) 0 := ContinuousAt.comp_of_eq (f := fun t : ℝ => -t) hSc continuous_neg.continuousAt (by simp)
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  have hwind : ∀ t : ℝ, wind p (sidePt a b s t) = (Complex.arg (rr s t) + S t) / (2 * Real.pi) := by
    intro t
    unfold wind turnSum
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    congr 2
    unfold angStep
    rw [ratio_sidePt hd]
  have hlim : Tendsto (fun t => wind p (sidePt a b s t) - wind p (sidePt a b s (-t))) (𝓝[>] 0) (𝓝 1) := by
    have h := (((rr_arg_pos hs hs1).add hS1).sub ((rr_arg_neg hs hs1).add hS2)).div_const (2 * Real.pi)
    have e : (Real.pi + S 0 - (-Real.pi + S 0)) / (2 * Real.pi) = 1 := by
      have := Real.pi_pos; field_simp; ring
    rw [e] at h
    refine h.congr fun t => ?_
    simp only [hwind, sub_div]
  have hnear : ∀ᶠ t in 𝓝[>] (0 : ℝ), |wind p (sidePt a b s t) - wind p (sidePt a b s (-t)) - 1| < 1 / 2 := by
    have := hlim.eventually (Metric.ball_mem_nhds (1 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [this] with t ht
    rw [Real.dist_eq] at ht
    rcases abs_lt.1 ht with ⟨l, u⟩
    exact abs_lt.2 ⟨by linarith, by linarith⟩
  filter_upwards [hnear, hev1.filter_mono nhdsWithin_le_nhds, hev2.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t h1 h2 h3 h4
  have ht : (0 : ℝ) < t := h4
  have o1 := hoff t ht.ne' h2
  have o2 := hoff (-t) (neg_ne_zero.2 ht.ne') h3
  refine ⟨o1, o2, ?_⟩
  obtain ⟨k1, hk1⟩ := wind_int p _ o1
  obtain ⟨k2, hk2⟩ := wind_int p _ o2
  rw [hk1, hk2] at h1 ⊢
  have hh : |((k1 - k2 - 1 : ℤ) : ℝ)| < 1 := by
    push_cast; linarith [h1]
  have : |k1 - k2 - 1| < 1 := by exact_mod_cast hh
  have h0 : k1 - k2 - 1 = 0 := Int.abs_lt_one_iff.1 this
  have : k1 = k2 + 1 := by omega
  rw [this]; push_cast; ring

end Erdos634.Draft.LaczFormal.WN
