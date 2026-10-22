-- Draft/LaczFormalIIcWN2.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2/6.3, Route B (winding-number interior), item B3:
-- the winding number of a closed polygon is 0 outside a large ball (so "C-degree" regions are bounded).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN1

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

theorem ratio_tendsto_one (a b : ℂ) : Tendsto (fun z : ℂ => (b - z) / (a - z)) (cocompact ℂ) (𝓝 1) := by
  have h1 : Tendsto (fun z : ℂ => (b - z) / (a - z)) (cocompact ℂ) (𝓝 1) := by
    have hinf : Tendsto (fun z : ℂ => ‖z‖) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop
    have key : ∀ᶠ z : ℂ in cocompact ℂ, (b - z) / (a - z) = 1 + (b - a) / (a - z) := by
      filter_upwards [hinf.eventually_gt_atTop (‖a‖)] with z hz
      have : a - z ≠ 0 := by
        intro h; have : a = z := sub_eq_zero.1 h; rw [this] at hz; exact lt_irrefl _ hz
      field_simp; ring
    refine Tendsto.congr' (key.mono fun z hz => hz.symm) ?_
    have : Tendsto (fun z : ℂ => (b - a) / (a - z)) (cocompact ℂ) (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hb : Tendsto (fun z : ℂ => ‖b - a‖ / (‖z‖ - ‖a‖)) (cocompact ℂ) (𝓝 0) :=
        tendsto_const_nhds.div_atTop ((tendsto_atTop_add_const_right _ (-‖a‖) hinf).congr fun z => by ring)
      refine squeeze_zero_norm' ?_ hb
      filter_upwards [hinf.eventually_gt_atTop (‖a‖)] with z hz
      rw [norm_norm, norm_div]
      have h1 : ‖z‖ - ‖a‖ ≤ ‖a - z‖ := by
        have := norm_sub_norm_le z a
        rwa [norm_sub_rev] at this
      have h2 : 0 < ‖z‖ - ‖a‖ := sub_pos.2 hz
      exact div_le_div_of_nonneg_left (norm_nonneg _) h2 h1
    simpa using tendsto_const_nhds.add this
  exact h1

/-- **B3.**  Far from the polygon the winding number is `0`. -/
theorem wind_eventually_zero (p : Fin n → ℂ) : ∀ᶠ z : ℂ in cocompact ℂ, wind p z = 0 := by
  have hT : Tendsto (wind p) (cocompact ℂ) (𝓝 0) := by
    have : Tendsto (fun z : ℂ => ∑ i : Fin n, angStep p z i) (cocompact ℂ) (𝓝 0) := by
      have h0 : ∀ i : Fin n, Tendsto (fun z : ℂ => angStep p z i) (cocompact ℂ) (𝓝 0) := fun i => by
        have := (Complex.continuousAt_arg (by simp : (1 : ℂ) ∈ Complex.slitPlane)).tendsto.comp (ratio_tendsto_one (p i) (p (i + 1)))
        simpa [angStep] using this
      simpa using tendsto_finsetSum _ fun i _ => h0 i
    simpa [wind, turnSum] using this.div_const (2 * Real.pi)
  have hnear : ∀ᶠ z : ℂ in cocompact ℂ, |wind p z| < 1 := by
    have := hT.eventually (Metric.ball_mem_nhds (0 : ℝ) one_pos)
    filter_upwards [this] with z hz
    simpa [Real.dist_eq] using hz
  have hfar : ∀ᶠ z : ℂ in cocompact ℂ, z ∉ edgeSet p := by
    have hc : IsCompact (edgeSet p) := by
      refine isCompact_iUnion fun i => ?_
      rw [segment_eq_image]; exact isCompact_Icc.image (by fun_prop)
    exact (hc.compl_mem_cocompact)
  filter_upwards [hnear, hfar] with z h1 h2
  obtain ⟨k, hk⟩ := wind_int p z h2
  rw [hk] at h1 ⊢
  have : |k| < 1 := by exact_mod_cast h1
  have : k = 0 := Int.abs_lt_one_iff.1 this
  simp [this]

end Erdos634.Draft.LaczFormal.WN
