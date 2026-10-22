import Erdos634.Refl.SoundStage5

/-! Stage 6: `okPos`/`okNeg` (the `hfree` bounds) and `hfree_sound`. -/

set_option linter.unusedSimpArgs false
open Erdos634.CertNode Erdos634.PlacementCompleteness
open Erdos634.Geometry (Plane)

namespace Refl

theorem poly_min_bound (c s tn : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ tn) : min c 0 * tn ≤ c * s := by
  rcases le_total c 0 with h | h
  · rw [min_eq_left h]; nlinarith
  · rw [min_eq_right h]; nlinarith

theorem poly_max_bound (c s tn : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ tn) : c * s ≤ max c 0 * tn := by
  rcases le_total c 0 with h | h
  · rw [max_eq_right h]; nlinarith
  · rw [max_eq_left h]; nlinarith

theorem okPos_real (c0 c1 c2 tn td t : ℝ) (htn : 0 < tn) (htd : 0 < td) (ht0 : 0 < t)
    (ht : t * td ≤ tn)
    (H : (0 < c0 ∧ 0 < c0 * td * td + min c1 0 * tn * td + min c2 0 * tn * tn) ∨
         (c0 = 0 ∧ 0 < c1 ∧ 0 < c1 * td + min c2 0 * tn) ∨ (c0 = 0 ∧ c1 = 0 ∧ 0 ≤ c2)) :
    0 ≤ c0 + c1 * t + c2 * t ^ 2 := by
  have hs0 : 0 ≤ t * td := by positivity
  rcases H with ⟨h0, h⟩ | ⟨h0, h1, h⟩ | ⟨h0, h1, h⟩
  · have b1 := poly_min_bound c1 (t * td) tn hs0 ht
    have hss : (t * td) * (t * td) ≤ tn * tn := by nlinarith
    have b2 : min c2 0 * (tn * tn) ≤ c2 * ((t * td) * (t * td)) := by
      rcases le_total c2 0 with h' | h'
      · rw [min_eq_left h']; nlinarith
      · rw [min_eq_right h']; nlinarith [mul_nonneg h' (mul_self_nonneg (t * td))]
    have key : td ^ 2 * (c0 + c1 * t + c2 * t ^ 2)
        = c0 * td * td + (c1 * (t * td)) * td + c2 * ((t * td) * (t * td)) := by ring
    have : 0 ≤ td ^ 2 * (c0 + c1 * t + c2 * t ^ 2) := by
      rw [key]; nlinarith [mul_le_mul_of_nonneg_right b1 htd.le]
    exact nonneg_of_mul_nonneg_right this (by positivity) |> fun h => by
      by_contra hn; push_neg at hn; nlinarith [mul_pos (pow_pos htd 2) (neg_pos.mpr hn)]
  · subst h0
    have b2 := poly_min_bound c2 (t * td) tn hs0 ht
    have : 0 < t * (c1 * td + c2 * (t * td)) := by
      apply mul_pos ht0; nlinarith
    nlinarith
  · subst h0; subst h1; simp; positivity

theorem okNeg_real (c0 c1 c2 tn td t : ℝ) (htn : 0 < tn) (htd : 0 < td) (ht0 : 0 < t)
    (ht : t * td ≤ tn)
    (H : (c0 < 0 ∧ c0 * td * td + max c1 0 * tn * td + max c2 0 * tn * tn < 0) ∨
         (c0 = 0 ∧ c1 < 0 ∧ c1 * td + max c2 0 * tn < 0) ∨ (c0 = 0 ∧ c1 = 0 ∧ c2 < 0)) :
    c0 + c1 * t + c2 * t ^ 2 < 0 := by
  have hs0 : 0 ≤ t * td := by positivity
  rcases H with ⟨h0, h⟩ | ⟨h0, h1, h⟩ | ⟨h0, h1, h⟩
  · have b1 := poly_max_bound c1 (t * td) tn hs0 ht
    have hss : (t * td) * (t * td) ≤ tn * tn := by nlinarith
    have b2 : c2 * ((t * td) * (t * td)) ≤ max c2 0 * (tn * tn) := by
      rcases le_total c2 0 with h' | h'
      · rw [max_eq_right h']; nlinarith [mul_nonneg (neg_nonneg.mpr h') (mul_self_nonneg (t * td))]
      · rw [max_eq_left h']; nlinarith
    have key : td ^ 2 * (c0 + c1 * t + c2 * t ^ 2)
        = c0 * td * td + (c1 * (t * td)) * td + c2 * ((t * td) * (t * td)) := by ring
    have : td ^ 2 * (c0 + c1 * t + c2 * t ^ 2) < 0 := by
      rw [key]; nlinarith [mul_le_mul_of_nonneg_right b1 htd.le]
    by_contra hn; push_neg at hn
    nlinarith [mul_nonneg (pow_pos htd 2).le hn]
  · subst h0
    have b2 := poly_max_bound c2 (t * td) tn hs0 ht
    have : t * (c1 * td + c2 * (t * td)) < 0 := by
      apply mul_neg_of_pos_of_neg ht0; nlinarith
    nlinarith
  · subst h0; subst h1; simp; nlinarith [sq_nonneg t, pow_pos ht0 2]


theorem okPos_cast (c0 c1 c2 tn td : Int) (h : okPos (c0, c1, c2) tn td = true) :
    (0 < (c0:ℝ) ∧ 0 < (c0:ℝ) * td * td + min (c1:ℝ) 0 * tn * td + min (c2:ℝ) 0 * tn * tn) ∨
    ((c0:ℝ) = 0 ∧ 0 < (c1:ℝ) ∧ 0 < (c1:ℝ) * td + min (c2:ℝ) 0 * tn) ∨
    ((c0:ℝ) = 0 ∧ (c1:ℝ) = 0 ∧ 0 ≤ (c2:ℝ)) := by
  unfold okPos at h
  simp only at h
  split_ifs at h with h1 h2 h3 h4
  · left
    simp only [decide_eq_true_eq] at h
    refine ⟨by exact_mod_cast h1, ?_⟩
    have : (0:ℝ) < ((c0 * td * td + min c1 0 * tn * td + min c2 0 * tn * tn : Int) : ℝ) := by exact_mod_cast h
    push_cast at this; exact this
  · right; left
    simp only [decide_eq_true_eq] at h
    have hc0 : c0 = 0 := by simpa using h2
    refine ⟨by exact_mod_cast hc0, by exact_mod_cast h3, ?_⟩
    have : (0:ℝ) < ((c1 * td + min c2 0 * tn : Int) : ℝ) := by exact_mod_cast h
    push_cast at this; exact this
  · right; right
    simp only [decide_eq_true_eq] at h
    have hc0 : c0 = 0 := by simpa using h2
    have hc1 : c1 = 0 := by simpa using h4
    exact ⟨by exact_mod_cast hc0, by exact_mod_cast hc1, by exact_mod_cast h⟩

theorem okNeg_cast (c0 c1 c2 tn td : Int) (h : okNeg (c0, c1, c2) tn td = true) :
    ((c0:ℝ) < 0 ∧ (c0:ℝ) * td * td + max (c1:ℝ) 0 * tn * td + max (c2:ℝ) 0 * tn * tn < 0) ∨
    ((c0:ℝ) = 0 ∧ (c1:ℝ) < 0 ∧ (c1:ℝ) * td + max (c2:ℝ) 0 * tn < 0) ∨
    ((c0:ℝ) = 0 ∧ (c1:ℝ) = 0 ∧ (c2:ℝ) < 0) := by
  unfold okNeg at h
  simp only at h
  split_ifs at h with h1 h2 h3 h4
  · left
    simp only [decide_eq_true_eq] at h
    refine ⟨by exact_mod_cast h1, ?_⟩
    have : ((c0 * td * td + max c1 0 * tn * td + max c2 0 * tn * tn : Int) : ℝ) < 0 := by exact_mod_cast h
    push_cast at this; exact this
  · right; left
    simp only [decide_eq_true_eq] at h
    have hc0 : c0 = 0 := by simpa using h2
    refine ⟨by exact_mod_cast hc0, by exact_mod_cast h3, ?_⟩
    have : ((c1 * td + max c2 0 * tn : Int) : ℝ) < 0 := by exact_mod_cast h
    push_cast at this; exact this
  · right; right
    simp only [decide_eq_true_eq] at h
    have hc0 : c0 = 0 := by simpa using h2
    have hc1 : c1 = 0 := by simpa using h4
    exact ⟨by exact_mod_cast hc0, by exact_mod_cast hc1, by exact_mod_cast h⟩

/-- the edge form along the curve `t ↦ v + t (d + t √Dn d⊥)` in rescaled coordinates -/
theorem evalL_curve (I : Inst) (Dn : ℝ) (hDn : (I.Dn : ℝ) = Dn) (v d : Pt) (hv : 0 < v.w) (hd : 0 < d.w)
    (l : Lin) (t : ℝ) :
    evalL l (v.X + d.X * t - Dn * d.Y * t ^ 2) (v.Y + d.Y * t + d.X * t ^ 2)
      = (((quad I v d l).1 : ℝ) + ((quad I v d l).2.1 : ℝ) * t + ((quad I v d l).2.2 : ℝ) * t ^ 2)
          / ((v.w : ℝ) * d.w) := by
  have h1 := Pt.w_ne v hv
  have h2 := Pt.w_ne d hd
  unfold evalL quad Pt.X Pt.Y
  push_cast
  rw [hDn]
  field_simp
  ring

theorem okPos_sound (I : Inst) (Dn : ℝ) (hDn : (I.Dn : ℝ) = Dn) (v d : Pt) (hv : 0 < v.w) (hd : 0 < d.w)
    (l : Lin) (tn td : Int) (htn : 0 < tn) (htd : 0 < td)
    (h : okPos (quad I v d l) tn td = true) (t : ℝ) (ht0 : 0 < t) (ht : t ≤ (tn : ℝ) / td) :
    0 ≤ evalL l (v.X + d.X * t - Dn * d.Y * t ^ 2) (v.Y + d.Y * t + d.X * t ^ 2) := by
  rw [evalL_curve I Dn hDn v d hv hd]
  generalize quad I v d l = q at h ⊢
  obtain ⟨c0, c1, c2⟩ := q
  have htn' : (0:ℝ) < tn := by exact_mod_cast htn
  have htd' : (0:ℝ) < td := by exact_mod_cast htd
  have ht' : t * td ≤ tn := by rwa [le_div_iff₀ htd'] at ht
  have := okPos_real _ _ _ _ _ t htn' htd' ht0 ht' (okPos_cast _ _ _ _ _ h)
  have hw : (0:ℝ) < (v.w:ℝ) * d.w := mul_pos (Pt.w_pos _ hv) (Pt.w_pos _ hd)
  exact div_nonneg this hw.le

theorem okNeg_sound (I : Inst) (Dn : ℝ) (hDn : (I.Dn : ℝ) = Dn) (v d : Pt) (hv : 0 < v.w) (hd : 0 < d.w)
    (l : Lin) (tn td : Int) (htn : 0 < tn) (htd : 0 < td)
    (h : okNeg (quad I v d l) tn td = true) (t : ℝ) (ht0 : 0 < t) (ht : t ≤ (tn : ℝ) / td) :
    evalL l (v.X + d.X * t - Dn * d.Y * t ^ 2) (v.Y + d.Y * t + d.X * t ^ 2) < 0 := by
  rw [evalL_curve I Dn hDn v d hv hd]
  generalize quad I v d l = q at h ⊢
  obtain ⟨c0, c1, c2⟩ := q
  have htn' : (0:ℝ) < tn := by exact_mod_cast htn
  have htd' : (0:ℝ) < td := by exact_mod_cast htd
  have ht' : t * td ≤ tn := by rwa [le_div_iff₀ htd'] at ht
  have := okNeg_real _ _ _ _ _ t htn' htd' ht0 ht' (okNeg_cast _ _ _ _ _ h)
  have hw : (0:ℝ) < (v.w:ℝ) * d.w := mul_pos (Pt.w_pos _ hv) (Pt.w_pos _ hd)
  exact div_neg_of_neg_of_pos this hw

#print axioms Refl.okPos_sound
#print axioms Refl.okNeg_sound
end Refl
