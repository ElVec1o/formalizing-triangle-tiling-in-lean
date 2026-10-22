-- Draft/LaczFormalIIcWN31.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2, step (g) core: NESTING of two disjoint closed polygonal curves with a common point of nonzero winding number.
-- Statement (pure winding-number lemma, no simplicity, no Jordan theorem): if `edgeSet p` and `edgeSet q` are disjoint and some point `z` has `wind p z != 0` and `wind q z != 0`
-- then either `wind p != 0` on all of `edgeSet q` (q lies in the p-degree) or `wind q != 0` on all of `edgeSet p` (p lies in the q-degree).
-- Route: `wind p` is constant on the connected curve `edgeSet q` (chain of segments); if both constants were 0, the first point where the segment from `z` to a far point meets `edgeSet p u edgeSet q`
-- would have a nonzero limit value of one winding number and a zero value of it, contradiction.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2, "Let C1 and C2 be disjoint cycles ... C2 in C1deg or C1 in C2deg"), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN4
import Mathlib.Analysis.Convex.Basic

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {n n' : ℕ} [NeZero n] [NeZero n']

/-- `wind p` is constant on a closed polygonal curve disjoint from `edgeSet p`. -/
theorem wind_const_on_edgeSet (p : Fin n → ℂ) (q : Fin n' → ℂ) (hd : Disjoint (edgeSet p) (edgeSet q)) :
    ∀ x ∈ edgeSet q, ∀ y ∈ edgeSet q, wind p x = wind p y := by
  have hseg : ∀ i : Fin n', ∀ w ∈ segment ℝ (q i) (q (i + 1)), w ∉ edgeSet p := fun i w hw hp =>
    Set.disjoint_left.1 hd hp (Set.mem_iUnion.2 ⟨i, hw⟩)
  have hstep : ∀ i : Fin n', wind p (q i) = wind p (q (i + 1)) := fun i => wind_const_segment p (hseg i)
  have hall : ∀ k : ℕ, wind p (q (k : Fin n')) = wind p (q 0) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.cast_succ, ← hstep]; exact ih
  have hv : ∀ i : Fin n', wind p (q i) = wind p (q 0) := fun i => by simpa using hall i.val
  have hpt : ∀ x ∈ edgeSet q, wind p x = wind p (q 0) := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    have : wind p x = wind p (q i) := by
      apply wind_const_segment
      intro w hw
      apply hseg i
      exact (convex_segment (q i) (q (i + 1))).segment_subset hi (left_mem_segment ℝ _ _) hw
    rw [this, hv]
  intro x hx y hy
  rw [hpt x hx, hpt y hy]

theorem wind_eventually_nhds (p : Fin n → ℂ) {x : ℂ} (hx : x ∉ edgeSet p) : ∀ᶠ y in 𝓝 x, wind p y = wind p x := by
  obtain ⟨ε, hε, h⟩ := wind_locallyConstant p x hx
  exact Metric.eventually_nhds_iff.2 ⟨ε, hε, fun y hy => (h y hy).2⟩

/-- **Nesting dichotomy** (printed: "C1° and C2° contain the exceptional points, hence C2 ⊂ C1° or C1 ⊂ C2°"). -/
theorem nesting_dichotomy (p : Fin n → ℂ) (q : Fin n' → ℂ) (hd : Disjoint (edgeSet p) (edgeSet q))
    {z : ℂ} (hzp : z ∉ edgeSet p) (hzq : z ∉ edgeSet q) (h1 : wind p z ≠ 0) (h2 : wind q z ≠ 0) :
    (∀ x ∈ edgeSet q, wind p x ≠ 0) ∨ (∀ x ∈ edgeSet p, wind q x ≠ 0) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨⟨x0, hx0, hw0⟩, ⟨y0, hy0, hv0⟩⟩ := hcon
  have hP : ∀ x ∈ edgeSet q, wind p x = 0 := fun x hx => (wind_const_on_edgeSet p q hd x hx x0 hx0).trans hw0
  have hQ : ∀ y ∈ edgeSet p, wind q y = 0 := fun y hy =>
    (wind_const_on_edgeSet q p hd.symm y hy y0 hy0).trans hv0
  -- a far point
  obtain ⟨f, hfp, hfq⟩ : ∃ f : ℂ, wind p f = 0 ∧ wind q f = 0 := by
    obtain ⟨f, hf⟩ := ((wind_eventually_zero p).and (wind_eventually_zero q)).exists
    exact ⟨f, hf.1, hf.2⟩
  set E : Set ℂ := edgeSet p ∪ edgeSet q with hE
  have hEc : IsClosed E := (isClosed_edgeSet p).union (isClosed_edgeSet q)
  set γ : ℝ → ℂ := fun t => z + t • (f - z) with hγ
  have hγc : Continuous γ := by fun_prop
  have hγ0 : γ 0 = z := by simp [hγ]
  have hzE : z ∉ E := by
    intro h; rcases h with h | h
    · exact hzp h
    · exact hzq h
  have hseg_mem : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ w ∈ segment ℝ z (γ s), ∃ r, 0 ≤ r ∧ r ≤ s ∧ w = γ r := by
    intro s hs0 hs1 w hw
    rw [segment_eq_image'] at hw
    obtain ⟨r, ⟨hr0, hr1⟩, rfl⟩ := hw
    refine ⟨r * s, by positivity, by nlinarith, ?_⟩
    simp only [hγ]
    rw [add_sub_cancel_left, smul_smul]
  -- the set of parameters meeting E
  set S : Set ℝ := {t | t ∈ Set.Icc (0 : ℝ) 1 ∧ γ t ∈ E} with hS
  have hSeq : S = Set.Icc (0 : ℝ) 1 ∩ γ ⁻¹' E := by ext t; simp [hS]
  have hSc : IsCompact S := by
    rw [hSeq]; exact isCompact_Icc.inter_right (hEc.preimage hγc)
  have hSne : S.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hav : ∀ w ∈ segment ℝ z f, w ∉ edgeSet p := by
      intro w hw hwp
      rw [segment_eq_image'] at hw
      obtain ⟨r, ⟨hr0, hr1⟩, rfl⟩ := hw
      have : r ∈ S := ⟨⟨hr0, hr1⟩, Or.inl hwp⟩
      rw [hne] at this; exact this
    have := wind_const_segment p hav
    rw [this, hfp] at h1
    exact h1 rfl
  obtain ⟨t, ⟨⟨ht0, ht1⟩, htE⟩, htmin⟩ := hSc.exists_isLeast hSne
  have htpos : 0 < t := by
    rcases ht0.lt_or_eq with h | h
    · exact h
    · exfalso; apply hzE
      have : γ t = z := by rw [← h]; exact hγ0
      rw [← this]; exact htE
  have hbefore : ∀ r, 0 ≤ r → r < t → γ r ∉ E := by
    intro r hr0 hrt hrE
    have : r ∈ S := ⟨⟨hr0, by linarith⟩, hrE⟩
    have := htmin this
    linarith
  -- common step: a point s < t close to t with the same winding value
  have hconst : ∀ {m : ℕ} [NeZero m] (r : Fin m → ℂ) (hsub : edgeSet r ⊆ E) (hx : γ t ∉ edgeSet r),
      wind r (γ t) = wind r z := by
    intro m _ r hsub hx
    have hev : ∀ᶠ s in 𝓝 t, wind r (γ s) = wind r (γ t) := hγc.continuousAt.eventually (wind_eventually_nhds r hx)
    obtain ⟨s, hs1, hs2⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsLT htpos : ∀ᶠ s in 𝓝[<] t, s ∈ Set.Ioo 0 t)).exists
    rw [← hs1]
    apply (wind_const_segment r _).symm
    intro w hw hwr
    obtain ⟨r', hr0, hrs, rfl⟩ := hseg_mem s hs2.1.le (by linarith [hs2.2]) w hw
    exact hbefore r' hr0 (by linarith [hs2.2]) (hsub hwr)
  rcases htE with hp | hq
  · -- γ t on p: wind q is continuous there
    have hnq : γ t ∉ edgeSet q := fun h => Set.disjoint_left.1 hd hp h
    have := hconst q (fun w hw => Or.inr hw) hnq
    rw [hQ _ hp] at this
    exact h2 this.symm
  · have hnp : γ t ∉ edgeSet p := fun h => Set.disjoint_left.1 hd h hq
    have := hconst p (fun w hw => Or.inl hw) hnp
    rw [hP _ hq] at this
    exact h1 this.symm

#print axioms nesting_dichotomy

end Erdos634.Draft.LaczFormal.WN
