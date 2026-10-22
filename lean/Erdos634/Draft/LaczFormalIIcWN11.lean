-- Draft/LaczFormalIIcWN11.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2/6.3, Route B, item B5 (Jordan-type dichotomy), assembly:
-- for a simple closed polygon with distinct vertices (n >= 3) the winding number off the polygon takes the values {0, sigma}, sigma = +-1.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2/6.3), Beeson, Beeson-Zhang.
-- Route: local sector constancy (WN7/WN8), right value constant along an edge (WN9), vertex gluing (WN10), then a clopen argument; no Umlaufsatz, no diagonal induction.
-- INJECTIVITY of the vertices is required: SimplePoly alone permits a figure-8 touching at a vertex, where the dichotomy is false.
import Erdos634.Draft.LaczFormalIIcWN10
import Mathlib.Analysis.Normed.Module.Convex

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

/-- The common right value of edge `i` (the winding number just to its right). -/
noncomputable def edgeVal {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n) (i : Fin n) : ℤ :=
  Classical.choose (good_exists hs hinj hn i (s := 1 / 2) (by norm_num) (by norm_num))

theorem edgeVal_spec {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n) (i : Fin n) :
    Good p i (1 / 2) (edgeVal hs hinj hn i) :=
  Classical.choose_spec (good_exists hs hinj hn i (s := 1 / 2) (by norm_num) (by norm_num))

theorem good_eq_edgeVal {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n) (i : Fin n)
    {s R : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hg : Good p i s R) : R = edgeVal hs hinj hn i :=
  good_edge_const hs hinj hn i hs0 hs1 (by norm_num) (by norm_num) hg (edgeVal_spec hs hinj hn i)

theorem edgeVal_succ {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n) (i : Fin n) :
    edgeVal hs hinj hn (i + 1) = edgeVal hs hinj hn i := by
  obtain ⟨k, ⟨s, hs0, hs1, hg⟩, ⟨s', hs0', hs1', hg'⟩, -⟩ := vertex_good hs hinj hn i
  have a := good_eq_edgeVal hs hinj hn i hs0 hs1 hg
  have b := good_eq_edgeVal hs hinj hn (i + 1) hs0' hs1' hg'
  exact_mod_cast b.symm.trans a

theorem edgeVal_const {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n) (i : Fin n) :
    edgeVal hs hinj hn i = edgeVal hs hinj hn 0 := by
  have h : ∀ m : ℕ, edgeVal hs hinj hn (m : Fin n) = edgeVal hs hinj hn 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.cast_succ, edgeVal_succ hs hinj hn, ih]
  have := h i.val
  rwa [Fin.cast_val_eq_self] at this

/-- Near every point of the polygon the winding number takes only the values `k0`, `k0 + 1`. -/
theorem near_polygon {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n)
    {y : ℂ} (hy : y ∈ edgeSet p) :
    ∃ r > 0, ∀ z : ℂ, dist z y < r → z ∉ edgeSet p →
      wind p z = (edgeVal hs hinj hn 0 : ℝ) ∨ wind p z = (edgeVal hs hinj hn 0 : ℝ) + 1 := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
  rw [segment_eq_image'] at hi
  obtain ⟨u, ⟨hu0, hu1⟩, rfl⟩ := hi
  rcases hu0.lt_or_eq with hu0' | hu0'
  · rcases hu1.lt_or_eq with hu1' | hu1'
    · -- open edge point
      obtain ⟨k, hk⟩ := good_exists hs hinj hn i hu0' hu1'
      have hkv := good_eq_edgeVal hs hinj hn i hu0' hu1' hk
      obtain ⟨r, hr, hb⟩ := good_ball hs hinj hn i hu0' hu1' hk
      refine ⟨r, hr, fun z hz hzE => ?_⟩
      have e : p i + u • (p (i + 1) - p i) = p i + (u : ℂ) * (p (i + 1) - p i) := by simp [Complex.real_smul]
      have hz2 : dist z (p i + u • (p (i + 1) - p i)) < r := hz
      rw [e] at hz2
      rw [edgeVal_const hs hinj hn i] at hkv
      rw [← hkv]
      exact hb z hz2 hzE
    · -- u = 1: the vertex p (i+1)
      obtain ⟨k, ⟨s, hs0, hs1, hg⟩, -, r, hr, hb⟩ := vertex_good hs hinj hn i
      have hkv := good_eq_edgeVal hs hinj hn i hs0 hs1 hg
      rw [edgeVal_const hs hinj hn i] at hkv
      refine ⟨r, hr, fun z hz hzE => ?_⟩
      have e : p i + u • (p (i + 1) - p i) = p (i + 1) := by rw [hu1']; simp
      have hz2 : dist z (p i + u • (p (i + 1) - p i)) < r := hz
      rw [e] at hz2
      rw [← hkv]
      exact hb z hz2 hzE
  · -- u = 0: the vertex p i = p ((i-1)+1)
    obtain ⟨k, ⟨s, hs0, hs1, hg⟩, -, r, hr, hb⟩ := vertex_good hs hinj hn (i - 1)
    have hkv := good_eq_edgeVal hs hinj hn (i - 1) hs0 hs1 hg
    rw [edgeVal_const hs hinj hn (i - 1)] at hkv
    refine ⟨r, hr, fun z hz hzE => ?_⟩
    have e : p i + u • (p (i + 1) - p i) = p (i - 1 + 1) := by rw [← hu0', sub_add_cancel]; simp
    have hz2 : dist z (p i + u • (p (i + 1) - p i)) < r := hz
    rw [e] at hz2
    rw [← hkv]
    exact hb z hz2 hzE

/-- **B5.  Jordan-type dichotomy for a simple polygon.** -/
theorem simple_wind_dichotomy {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ z : ℂ, z ∉ edgeSet p → wind p z = 0 ∨ wind p z = σ := by
  set k0 : ℝ := (edgeVal hs hinj hn 0 : ℝ) with hk0
  set A : Set ℂ := {z | z ∉ edgeSet p ∧ wind p z ≠ k0 ∧ wind p z ≠ k0 + 1} with hA
  have hAopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨ε, hε, hlc⟩ := wind_locallyConstant p z hz.1
    refine Metric.mem_nhds_iff.2 ⟨ε, hε, fun z' hz' => ?_⟩
    obtain ⟨h1, h2⟩ := hlc z' (Metric.mem_ball.1 hz')
    exact ⟨h1, by rw [h2]; exact hz.2.1, by rw [h2]; exact hz.2.2⟩
  have hAclosed : IsClosed A := by
    rw [← closure_subset_iff_isClosed]
    intro y hy
    by_cases hyE : y ∈ edgeSet p
    · exfalso
      obtain ⟨r, hr, hb⟩ := near_polygon hs hinj hn hyE
      obtain ⟨b, hbA, hbd⟩ := Metric.mem_closure_iff.1 hy r hr
      rcases hb b (by rw [dist_comm]; exact hbd) hbA.1 with h | h
      · exact hbA.2.1 h
      · exact hbA.2.2 h
    · obtain ⟨ε, hε, hlc⟩ := wind_locallyConstant p y hyE
      obtain ⟨b, hbA, hbd⟩ := Metric.mem_closure_iff.1 hy ε hε
      obtain ⟨h1, h2⟩ := hlc b (by rw [dist_comm]; exact hbd)
      exact ⟨hyE, by rw [← h2]; exact hbA.2.1, by rw [← h2]; exact hbA.2.2⟩
  have hAempty : A = ∅ := by
    rcases isClopen_iff.1 ⟨hAclosed, hAopen⟩ with h | h
    · exact h
    · exfalso
      have : p 0 ∈ A := by rw [h]; trivial
      exact this.1 (vertex_mem_edgeSet p 0)
  have hdich : ∀ z : ℂ, z ∉ edgeSet p → wind p z = k0 ∨ wind p z = k0 + 1 := by
    intro z hz
    by_contra hcon
    push Not at hcon
    have : z ∈ A := ⟨hz, hcon.1, hcon.2⟩
    rw [hAempty] at this
    exact this
  -- a far point
  obtain ⟨K, hK, hKs⟩ := Filter.mem_cocompact.1 (wind_eventually_zero p)
  have hfar : ∃ z : ℂ, z ∉ edgeSet p ∧ wind p z = 0 := by
    obtain ⟨R, hR⟩ := (hK.isBounded.union (isCompact_edgeSet p).isBounded).subset_closedBall (0 : ℂ)
    refine ⟨((max R 0 + 1 : ℝ) : ℂ), ?_, ?_⟩
    all_goals
      have hnot : ((max R 0 + 1 : ℝ) : ℂ) ∉ K ∪ edgeSet p := by
        intro hmem
        have := hR hmem
        rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by have := le_max_right R 0; positivity)] at this
        have := le_max_left R 0
        linarith
    · exact fun h => hnot (Or.inr h)
    · exact hKs (fun h => hnot (Or.inl h))
  obtain ⟨zf, hzf, hwf⟩ := hfar
  rcases hdich zf hzf with h | h
  · refine ⟨1, Or.inl rfl, fun z hz => ?_⟩
    rcases hdich z hz with h' | h'
    · left; rw [h']; rw [hwf] at h; exact h.symm
    · right; rw [h']; rw [hwf] at h; linarith
  · refine ⟨-1, Or.inr rfl, fun z hz => ?_⟩
    rcases hdich z hz with h' | h'
    · right; rw [h']; rw [hwf] at h; linarith
    · left; rw [h']; rw [hwf] at h; linarith

end Erdos634.Draft.LaczFormal.WN
