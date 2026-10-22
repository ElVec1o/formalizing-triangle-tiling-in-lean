-- Draft/LaczFormalIIcWN96.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3, p. 359), Lemma 6.2: "These segments VW are pairwise disjoint", plane-geometry lemma for PARALLEL chords.
-- `seg_overlap_eq`: two open segments `(a,b)`, `(a',b')` of parallel directions with a common point, such that no endpoint of one lies in the open part of the other, have the same endpoints:
-- `(a = a' and b = b')` or `(a = b' and b = a')`.  (Real-interval argument along the common line.)
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcL8s
import Erdos634.Draft.LaczFormalIIcWN87

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

theorem real_overlap {s1 r σ τ : ℝ} (hr : r ≠ 0) (hσ0 : 0 < σ) (hσ1 : σ < 1) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hσ : σ = s1 + τ * r)
    (h1 : ¬ ((s1 < 0 ∧ 0 < s1 + r) ∨ (s1 + r < 0 ∧ 0 < s1)))
    (h2 : ¬ ((s1 < 1 ∧ 1 < s1 + r) ∨ (s1 + r < 1 ∧ 1 < s1)))
    (h3 : ¬ (0 < s1 ∧ s1 < 1)) (h4 : ¬ (0 < s1 + r ∧ s1 + r < 1)) :
    (s1 = 0 ∧ r = 1) ∨ (s1 = 1 ∧ r = -1) := by
  rcases lt_or_gt_of_ne hr with hneg | hpos
  · right
    have e1 : s1 + r < σ := by nlinarith
    have e2 : σ < s1 := by nlinarith
    have a1 : 0 ≤ s1 + r := by
      by_contra h; apply h1; right; exact ⟨by linarith, by linarith⟩
    have a2 : s1 ≤ 1 := by
      by_contra h; apply h2; right; exact ⟨by linarith, by linarith⟩
    have a3 : 1 ≤ s1 := by
      by_contra h; apply h3; exact ⟨by linarith, by linarith⟩
    have a4 : s1 + r ≤ 0 := by
      by_contra h; apply h4; exact ⟨by linarith, by linarith⟩
    constructor <;> linarith
  · left
    have e1 : s1 < σ := by nlinarith
    have e2 : σ < s1 + r := by nlinarith
    have a1 : 0 ≤ s1 := by
      by_contra h; apply h1; left; exact ⟨by linarith, by linarith⟩
    have a2 : s1 + r ≤ 1 := by
      by_contra h; apply h2; left; exact ⟨by linarith, by linarith⟩
    have a3 : s1 ≤ 0 := by
      by_contra h; apply h3; exact ⟨by linarith, by linarith⟩
    have a4 : 1 ≤ s1 + r := by
      by_contra h; apply h4; exact ⟨by linarith, by linarith⟩
    constructor <;> linarith

/-- Parallel nonzero vectors in the plane are real multiples of each other. -/
theorem par_exists_smul {u u' : Plane} (hu : u ≠ 0) (h : crs (toV2 u) (toV2 u') = 0) : ∃ r : ℝ, u' = r • u := by
  have hn : 0 < (u 0) ^ 2 + (u 1) ^ 2 := by
    by_contra hh
    apply hu
    have h0 : u 0 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
    have h1 : u 1 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
    ext i; fin_cases i
    · exact h0
    · exact h1
  refine ⟨((u 0) * (u' 0) + (u 1) * (u' 1)) / ((u 0) ^ 2 + (u 1) ^ 2), ?_⟩
  unfold crs toV2 at h
  simp only at h
  ext i; fin_cases i
  · simp only [PiLp.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.isValue]
    field_simp
    linear_combination (-(u 1)) * h
  · simp only [PiLp.smul_apply, smul_eq_mul, Fin.mk_one, Fin.isValue]
    field_simp
    linear_combination (u 0) * h

theorem seg_overlap_eq {a b a' b' X : Plane}
    (hX1 : X ∈ openSegment ℝ a b) (hX2 : X ∈ openSegment ℝ a' b')
    (hpar : crs (toV2 (b - a)) (toV2 (b' - a')) = 0)
    (h1 : a ∉ openSegment ℝ a' b') (h2 : b ∉ openSegment ℝ a' b') (h3 : a' ∉ openSegment ℝ a b) (h4 : b' ∉ openSegment ℝ a b) :
    (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
  obtain ⟨σ, hσ0, hσ1, hXσ⟩ := openSegment_param hX1
  obtain ⟨τ, hτ0, hτ1, hXτ⟩ := openSegment_param hX2
  have hab : a ≠ b := by
    intro e; subst e
    apply h1
    have : X = a := by rw [hXσ]; simp
    rw [← this]; exact hX2
  have hab' : a' ≠ b' := by
    intro e; subst e
    apply h3
    have : X = a' := by rw [hXτ]; simp
    rw [← this]; exact hX1
  have hu : b - a ≠ 0 := sub_ne_zero.2 hab.symm
  obtain ⟨r, hr⟩ := par_exists_smul hu hpar
  have hr0 : r ≠ 0 := by
    intro e; rw [e, zero_smul] at hr
    exact hab' (sub_eq_zero.1 hr).symm
  set u := b - a with hu_def
  have ha' : a' = a + (σ - τ * r) • u := by
    have e : a + σ • u = a' + τ • (r • u) := by rw [← hr, ← hXσ, hXτ]
    calc a' = a + σ • u - τ • (r • u) := by rw [e]; abel
      _ = a + (σ - τ * r) • u := by module
  have hb' : b' = a + ((σ - τ * r) + r) • u := by
    have : b' = a' + (b' - a') := by abel
    rw [this, hr, ha']; module
  have hb : b = a + (1 : ℝ) • u := by rw [hu_def]; module
  -- the membership tests in the parameter along u
  have mem_iff : ∀ (t : ℝ), 0 < t → t < 1 → ∀ (s : ℝ), a + s • u = a' + t • (b' - a') → s = (σ - τ * r) + t * r := by
    intro t ht0 ht1 s hs
    rw [hr, ha'] at hs
    have : (s - ((σ - τ * r) + t * r)) • u = 0 := by
      have : a + s • u - (a + (σ - τ * r) • u + t • (r • u)) = 0 := by rw [hs]; abel
      calc (s - ((σ - τ * r) + t * r)) • u = a + s • u - (a + (σ - τ * r) • u + t • (r • u)) := by module
        _ = 0 := this
    rcases smul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hu
  have openseg_of_param : ∀ (Y W : Plane) (t : ℝ), 0 < t → t < 1 → Y + t • (W - Y) ∈ openSegment ℝ Y W :=
    fun Y W t h0 h1 => ⟨1 - t, t, by linarith, h0, by ring, by module⟩
  set s1 : ℝ := σ - τ * r with hs1
  -- a point `a + c u` strictly between the parameters of a' and b' lies in the open segment (a', b')
  have between : ∀ c : ℝ, ((s1 < c ∧ c < s1 + r) ∨ (s1 + r < c ∧ c < s1)) → a + c • u ∈ openSegment ℝ a' b' := by
    intro c hc
    have ht : 0 < (c - s1) / r ∧ (c - s1) / r < 1 := by
      rcases lt_or_gt_of_ne hr0 with hneg | hpos
      · rcases hc with ⟨h, h'⟩ | ⟨h, h'⟩
        · exfalso; linarith [h.trans h']
        · constructor
          · exact div_pos_of_neg_of_neg (by linarith) hneg
          · rw [div_lt_one_of_neg hneg]; linarith
      · rcases hc with ⟨h, h'⟩ | ⟨h, h'⟩
        · constructor
          · exact div_pos (by linarith) hpos
          · rw [div_lt_one hpos]; linarith
        · exfalso; linarith [h.trans h']
    have := openseg_of_param a' b' ((c - s1) / r) ht.1 ht.2
    convert this using 1
    rw [hr, ha']
    have : ((c - s1) / r) * r = c - s1 := by field_simp
    calc a + c • u = a + s1 • u + (((c - s1) / r) * r) • u := by rw [this]; module
      _ = a + s1 • u + ((c - s1) / r) • (r • u) := by rw [mul_smul]
  have h1' : ¬ ((s1 < 0 ∧ 0 < s1 + r) ∨ (s1 + r < 0 ∧ 0 < s1)) := by
    intro h
    apply h1
    have := between 0 h
    simpa using this
  have h2' : ¬ ((s1 < 1 ∧ 1 < s1 + r) ∨ (s1 + r < 1 ∧ 1 < s1)) := by
    intro h
    apply h2
    have := between 1 h
    rw [hb]; exact this
  have h3' : ¬ (0 < s1 ∧ s1 < 1) := by
    rintro ⟨hp, hq⟩
    apply h3
    rw [ha']
    have := openseg_of_param a b s1 hp hq
    rwa [← hu_def] at this
  have h4' : ¬ (0 < s1 + r ∧ s1 + r < 1) := by
    rintro ⟨hp, hq⟩
    apply h4
    rw [hb']
    have := openseg_of_param a b (s1 + r) hp hq
    rwa [← hu_def] at this
  rcases real_overlap hr0 hσ0 hσ1 hτ0 hτ1 (by rw [hs1]; ring) h1' h2' h3' h4' with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · left
    constructor
    · rw [ha', e1]; simp
    · rw [hb', e1, e2]; rw [hu_def]; module
  · right
    constructor
    · rw [hb', e1, e2]; simp
    · rw [ha', e1, hu_def]; module

#print axioms seg_overlap_eq

end Erdos634.Draft.LaczFormal.RG
