-- Draft/LaczFormalIIcWN119.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3, p. 358-359), Lemma 6.2, `ExcInsideAll` step (i): NESTING OF DISJOINT POLYGONS (pure winding-number geometry, no Jordan theorem).
-- Printed: "we take a cycle C1 of Gamma_kite belonging to C-degree and having minimal area ... if C1-degree contains all exceptional points then so does C-degree".
-- Here: `no_mutual_nest` (two disjoint polygons cannot each lie in the degree region of the other: a point of maximal real part), `ray_first_hit` (first hit of a ray with a polygon where the winding number is nonzero),
-- `nest_contain`: if the disjoint polygons `p`, `q` satisfy `wind p <> 0` at one point of `q`, then every point of nonzero `q`-winding is off `p` and has nonzero `p`-winding (the degree region of `q` lies in that of `p`).
-- Route: the ray from `z` to its first hit `y` with `q`; if `z` were off the degree region of `p`, the segment `[z, y)` would meet `p` at a point of nonzero `q`-winding, so `p` would lie in the `q`-degree region (`wind_const_on_edgeSet`), contradicting `no_mutual_nest`.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN82

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {n n' : ℕ} [NeZero n] [NeZero n']

/-- At a point off `q` whose real part is at least that of every point of `q`, the winding number about `q` is `0`. -/
theorem wind_zero_at_maxre (q : Fin n' → ℂ) {e : ℂ} (heq : e ∉ edgeSet q) (hmax : ∀ w ∈ edgeSet q, w.re ≤ e.re) : wind q e = 0 := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (wind_eventually_nhds q heq)
  have hy := hball (y := e + ((δ / 2 : ℝ) : ℂ)) (by
    rw [dist_eq_norm]; simp [Complex.norm_real, abs_of_pos hδ]; linarith)
  have hy0 : wind q (e + ((δ / 2 : ℝ) : ℂ)) = 0 := by
    apply wind_zero_of_right
    intro w hw
    have := hmax w hw
    simp
    linarith
  rw [← hy, hy0]

/-- Two disjoint closed polygons cannot lie each in the degree region of the other. -/
theorem no_mutual_nest (p : Fin n → ℂ) (q : Fin n' → ℂ) (hd : Disjoint (edgeSet p) (edgeSet q))
    (hp : ∀ x ∈ edgeSet p, wind q x ≠ 0) (hq : ∀ y ∈ edgeSet q, wind p y ≠ 0) : False := by
  set U : Set ℂ := edgeSet p ∪ edgeSet q with hU
  have hUc : IsCompact U := (isCompact_edgeSet p).union (isCompact_edgeSet q)
  have hUne : U.Nonempty := ⟨p 0, Or.inl (vertex_mem_edgeSet p 0)⟩
  obtain ⟨e, he, hmax⟩ := hUc.exists_isMaxOn hUne Complex.continuous_re.continuousOn
  have hm : ∀ w ∈ U, w.re ≤ e.re := fun w hw => isMaxOn_iff.1 hmax w hw
  rcases he with he | he
  · have heq : e ∉ edgeSet q := Set.disjoint_left.1 hd he
    exact hp e he (wind_zero_at_maxre q heq (fun w hw => hm w (Or.inr hw)))
  · have heq : e ∉ edgeSet p := Set.disjoint_right.1 hd he
    exact hq e he (wind_zero_at_maxre p heq (fun w hw => hm w (Or.inl hw)))

/-- A point far to the right of `z` on the real ray has winding number `0`. -/
theorem exists_far_ray (q : Fin n' → ℂ) (z : ℂ) : ∃ T : ℝ, 0 < T ∧ wind q (z + (T : ℂ)) = 0 := by
  obtain ⟨K, hK, hKs⟩ := Filter.mem_cocompact.1 (wind_eventually_zero q)
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  refine ⟨max R 0 + ‖z‖ + 1, by positivity, ?_⟩
  apply hKs
  intro hmem
  have := hR hmem
  rw [mem_closedBall_zero_iff] at this
  have h1 : ‖((max R 0 + ‖z‖ + 1 : ℝ) : ℂ)‖ = max R 0 + ‖z‖ + 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h2 := norm_sub_norm_le (((max R 0 + ‖z‖ + 1 : ℝ) : ℂ)) (-z)
  have h3 : ‖z + ((max R 0 + ‖z‖ + 1 : ℝ) : ℂ)‖ ≥ ‖((max R 0 + ‖z‖ + 1 : ℝ) : ℂ)‖ - ‖z‖ := by
    have := norm_sub_le_norm_add (((max R 0 + ‖z‖ + 1 : ℝ) : ℂ)) z
    have e : ((max R 0 + ‖z‖ + 1 : ℝ) : ℂ) + z = z + ((max R 0 + ‖z‖ + 1 : ℝ) : ℂ) := by ring
    have h4 := norm_sub_norm_le (((max R 0 + ‖z‖ + 1 : ℝ) : ℂ)) (-z)
    rw [norm_neg, sub_neg_eq_add, e] at h4
    exact h4
  have := le_max_left R 0
  linarith

/-- First hit of the real ray from `z` with the polygon `q`, when `z` has nonzero winding number about `q`. -/
theorem ray_first_hit (q : Fin n' → ℂ) {z : ℂ} (hz : z ∉ edgeSet q) (hw : wind q z ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ z + (t : ℂ) ∈ edgeSet q ∧ ∀ s : ℝ, 0 ≤ s → s < t → z + (s : ℂ) ∉ edgeSet q := by
  set S : Set ℝ := {t | 0 ≤ t ∧ z + (t : ℂ) ∈ edgeSet q} with hS
  have hSne : S.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    obtain ⟨T, hT, hT0⟩ := exists_far_ray q z
    apply hw
    rw [← hT0]
    apply wind_const_segment
    intro x hx
    rw [segment_eq_image'] at hx
    obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hx
    intro hmem
    have : θ * T ∈ S := ⟨by nlinarith, by
      have e : z + θ • (z + (T : ℂ) - z) = z + ((θ * T : ℝ) : ℂ) := by
        rw [Complex.real_smul]; push_cast; ring
      rw [← e]; exact hmem⟩
    rw [hne] at this; exact this
  have hSclosed : IsClosed S := by
    have : S = Set.Ici (0 : ℝ) ∩ (fun t : ℝ => z + (t : ℂ)) ⁻¹' edgeSet q := by
      ext t; simp [hS]
    rw [this]
    exact isClosed_Ici.inter ((isClosed_edgeSet q).preimage (by fun_prop))
  have hSbdd : BddBelow S := ⟨0, fun t ht => ht.1⟩
  have hmem := hSclosed.csInf_mem hSne hSbdd
  refine ⟨sInf S, ?_, hmem.2, ?_⟩
  · rcases hmem.1.lt_or_eq with h | h
    · exact h
    · exfalso; apply hz; have := hmem.2; rw [← h] at this; simpa using this
  · intro s hs0 hst hin
    have : sInf S ≤ s := csInf_le hSbdd ⟨hs0, hin⟩
    linarith

/-- **Nesting (i).**  If `q` has a point of nonzero `p`-winding and the polygons are disjoint, the degree region of `q` lies in that of `p`. -/
theorem nest_contain (p : Fin n → ℂ) (q : Fin n' → ℂ) (hd : Disjoint (edgeSet p) (edgeSet q))
    (hq : ∃ y ∈ edgeSet q, wind p y ≠ 0) {z : ℂ} (hz : z ∉ edgeSet q) (hwz : wind q z ≠ 0) :
    z ∉ edgeSet p ∧ wind p z ≠ 0 := by
  obtain ⟨y0, hy0, hy0w⟩ := hq
  have hqall : ∀ y ∈ edgeSet q, wind p y ≠ 0 := fun y hy => by
    rw [wind_const_on_edgeSet p q hd y hy y0 hy0]; exact hy0w
  obtain ⟨t, ht0, hty, hbefore⟩ := ray_first_hit q hz hwz
  set y : ℂ := z + (t : ℂ) with hy
  have hyp : y ∉ edgeSet p := Set.disjoint_right.1 hd hty
  by_contra hcon
  have hex : ∃ x ∈ segment ℝ z y, x ∈ edgeSet p := by
    by_contra hnone
    push_neg at hnone
    apply hcon
    refine ⟨hnone z (left_mem_segment ℝ _ _), ?_⟩
    rw [wind_const_segment p (fun x hx => hnone x hx)]
    exact hqall y hty
  obtain ⟨x, hxseg, hxp⟩ := hex
  rw [segment_eq_image'] at hxseg
  obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hxseg
  beta_reduce at hxp
  have hxe : z + θ • (y - z) = z + ((θ * t : ℝ) : ℂ) := by
    rw [Complex.real_smul, hy]; push_cast; ring
  rw [hxe] at hxp
  have hlt : θ * t < t := by
    rcases h1.lt_or_eq with h | h
    · nlinarith
    · exfalso; apply hyp; subst h; simpa [hy] using hxp
  have hnn : 0 ≤ θ * t := by positivity
  have hxq : wind q z = wind q (z + ((θ * t : ℝ) : ℂ)) := by
    apply wind_const_segment
    intro w hw
    rw [segment_eq_image'] at hw
    obtain ⟨θ', ⟨h0', h1'⟩, rfl⟩ := hw
    beta_reduce
    have e : z + θ' • (z + ((θ * t : ℝ) : ℂ) - z) = z + ((θ' * (θ * t) : ℝ) : ℂ) := by
      rw [Complex.real_smul]; push_cast; ring
    rw [e]
    apply hbefore _ (by positivity)
    nlinarith
  have hxw : wind q (z + ((θ * t : ℝ) : ℂ)) ≠ 0 := by rw [← hxq]; exact hwz
  have hpall : ∀ x' ∈ edgeSet p, wind q x' ≠ 0 := fun x' hx' => by
    rw [wind_const_on_edgeSet q p hd.symm x' hx' _ hxp]; exact hxw
  exact no_mutual_nest p q hd hpall hqall

#print axioms nest_contain

end Erdos634.Draft.LaczFormal.WN
