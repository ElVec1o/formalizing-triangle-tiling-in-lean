-- Draft/LaczFormalIIcWN72.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2, item (3), step 2: DELETING ONE STRAIGHT VERTEX of a simple polygon.
-- `p : Fin (n+3) -> C` simple and injective with `extAng p (last) = 0` (the vertex `p last` lies strictly between its neighbours: Fig. 5(A) of Laczkovich).  Then `q j = p (castSucc j)` is simple,
-- injective, has the same `edgeSet` and `extAng q j = extAng p (castSucc j)` (the merged side is a positive multiple of both old sides).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN71

open scoped Classical Fin.NatCast
open Complex

namespace Erdos634.Draft.LaczFormal.WN

section geom

theorem dl_seg_split {a b c : ℂ} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hb : b = a + (t : ℂ) * (c - a)) :
    segment ℝ a c ⊆ segment ℝ a b ∪ segment ℝ b c := by
  intro z hz
  rw [segment_eq_image'] at hz
  obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hz
  simp only [Complex.real_smul]
  by_cases hst : s ≤ t
  · left
    rw [segment_eq_image']
    refine ⟨s / t, ⟨by positivity, by rw [div_le_one ht0]; exact hst⟩, ?_⟩
    simp only [Complex.real_smul]
    rw [hb]
    have : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    push_cast
    field_simp
    ring
  · right
    have hst' : t < s := not_le.1 hst
    rw [segment_eq_image']
    refine ⟨(s - t) / (1 - t), ⟨div_nonneg (by linarith) (by linarith), by rw [div_le_one (by linarith)]; linarith⟩, ?_⟩
    simp only [Complex.real_smul]
    rw [hb]
    have : (1 - (t : ℂ)) ≠ 0 := by
      have : (1 : ℝ) - t ≠ 0 := by linarith
      exact_mod_cast this
    push_cast
    field_simp
    ring

theorem dl_seg_mem {a b c : ℂ} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hb : b = a + (t : ℂ) * (c - a)) :
    segment ℝ a b ⊆ segment ℝ a c ∧ segment ℝ b c ⊆ segment ℝ a c := by
  have hbm : b ∈ segment ℝ a c := by
    rw [segment_eq_image']
    exact ⟨t, ⟨ht0.le, ht1.le⟩, by simp only [Complex.real_smul]; rw [hb]⟩
  exact ⟨(convex_segment a c).segment_subset (left_mem_segment ℝ a c) hbm, (convex_segment a c).segment_subset hbm (right_mem_segment ℝ a c)⟩

theorem dl_straight_param {a b c : ℂ} {lam : ℝ} (hl : 0 < lam) (h : c - b = (lam : ℂ) * (b - a)) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ b = a + (t : ℂ) * (c - a) := by
  refine ⟨1 / (1 + lam), by positivity, by rw [div_lt_one (by positivity)]; linarith, ?_⟩
  have h1 : (1 + (lam : ℂ)) ≠ 0 := by
    have : (1 + lam : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  have hc : c - a = (1 + (lam : ℂ)) * (b - a) := by linear_combination h
  rw [hc]
  push_cast
  field_simp
  ring

theorem dl_pos_of_arg_zero {r : ℂ} (h0 : r ≠ 0) (h : Complex.arg r = 0) : ∃ lam : ℝ, 0 < lam ∧ r = (lam : ℂ) := by
  rw [Complex.arg_eq_zero_iff] at h
  obtain ⟨hre, him⟩ := h
  refine ⟨r.re, ?_, ?_⟩
  · rcases hre.lt_or_eq with h' | h'
    · exact h'
    · exfalso; apply h0; apply Complex.ext <;> simp [← h', him]
  · apply Complex.ext <;> simp [him]

theorem dl_arg_div_scale_den (x y : ℂ) {μ : ℝ} (hμ : 0 < μ) : Complex.arg (x / ((μ : ℂ) * y)) = Complex.arg (x / y) := by
  have : x / ((μ : ℂ) * y) = ((1 / μ : ℝ) : ℂ) * (x / y) := by
    have : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
    push_cast
    field_simp
  rw [this]
  exact Complex.arg_real_mul _ (by positivity)

theorem dl_arg_div_scale_num (x y : ℂ) {μ : ℝ} (hμ : 0 < μ) : Complex.arg (((μ : ℂ) * x) / y) = Complex.arg (x / y) := by
  have : ((μ : ℂ) * x) / y = (μ : ℂ) * (x / y) := by ring
  rw [this]
  exact Complex.arg_real_mul _ hμ

end geom

section finfacts
variable (n : ℕ)

theorem del_f1 (j : Fin (n+2)) (h : j ≠ Fin.last (n+1)) : (Fin.castSucc j : Fin (n+3)) + 1 = Fin.castSucc (j+1) := by
  apply Fin.ext
  have hj : j.val < n + 1 := by
    have := j.isLt
    have h2 : j.val ≠ n + 1 := fun e => h (Fin.ext e)
    omega
  simp [Fin.val_add]
  exact (Nat.mod_eq_of_lt (by omega)).symm

theorem del_f2 : (Fin.castSucc (Fin.last (n+1)) : Fin (n+3)) + 1 = Fin.last (n+2) := by
  apply Fin.ext
  simp

theorem del_f3 : (Fin.last (n+2) : Fin (n+3)) + 1 = 0 := by
  apply Fin.ext
  simp

theorem del_f4 : (Fin.last (n+1) : Fin (n+2)) + 1 = 0 := by
  apply Fin.ext
  simp

theorem del_f5 : (Fin.castSucc (0 : Fin (n+2)) : Fin (n+3)) = 0 := rfl

theorem del_f6 : (0 : Fin (n+3)) - 1 = Fin.last (n+2) := sub_eq_iff_eq_add.2 (del_f3 n).symm

theorem del_f6' : (0 : Fin (n+2)) - 1 = Fin.last (n+1) := sub_eq_iff_eq_add.2 (del_f4 n).symm

theorem del_f7 : (Fin.last (n+2) : Fin (n+3)) - 1 = Fin.castSucc (Fin.last (n+1)) := sub_eq_iff_eq_add.2 (del_f2 n).symm

theorem del_f8 (j : Fin (n+2)) (h : j ≠ 0) : (Fin.castSucc j : Fin (n+3)) - 1 = Fin.castSucc (j - 1) := by
  have hne : j - 1 ≠ Fin.last (n+1) := by
    intro e
    apply h
    have : j = Fin.last (n+1) + 1 := sub_eq_iff_eq_add.1 e
    rw [this, del_f4]
  apply sub_eq_iff_eq_add.2
  rw [del_f1 n _ hne]
  simp

theorem del_last_ne (m : Fin (n+2)) : (Fin.last (n+2) : Fin (n+3)) ≠ Fin.castSucc m := (Fin.castSucc_lt_last m).ne'

theorem del_last_ne0 : (Fin.last (n+1) : Fin (n+2)) ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp at this

end finfacts

/-- Delete the last vertex. -/
def delLast {n : ℕ} (p : Fin (n+3) → ℂ) : Fin (n+2) → ℂ := fun j => p (Fin.castSucc j)

theorem delLast_inj {n : ℕ} {p : Fin (n+3) → ℂ} (h : Function.Injective p) : Function.Injective (delLast p) :=
  fun a b hab => Fin.castSucc_injective _ (h hab)

/-- Data of a straight last vertex. -/
theorem straight_data {n : ℕ} {p : Fin (n+3) → ℂ} (hinj : Function.Injective p) (hst : extAng p (Fin.last (n+2)) = 0) :
    ∃ lam : ℝ, 0 < lam ∧ p 0 - p (Fin.last (n+2)) = (lam : ℂ) * (p (Fin.last (n+2)) - p (Fin.castSucc (Fin.last (n+1)))) := by
  unfold extAng at hst
  rw [del_f3, del_f7] at hst
  have h1 : p 0 - p (Fin.last (n+2)) ≠ 0 := sub_ne_zero.2 (fun e => by
    have := hinj e
    exact absurd this.symm (by simp [Fin.ext_iff]))
  have h2 : p (Fin.last (n+2)) - p (Fin.castSucc (Fin.last (n+1))) ≠ 0 := sub_ne_zero.2 (fun e => by
    have := hinj e
    exact del_last_ne (n) _ this)
  obtain ⟨lam, hl, hr⟩ := dl_pos_of_arg_zero (div_ne_zero h1 h2) hst
  refine ⟨lam, hl, ?_⟩
  rw [div_eq_iff h2] at hr
  exact hr

theorem delLast_edgeSet {n : ℕ} {p : Fin (n+3) → ℂ} (hinj : Function.Injective p) (hst : extAng p (Fin.last (n+2)) = 0) :
    edgeSet (delLast p) = edgeSet p := by
  obtain ⟨lam, hl, hc⟩ := straight_data hinj hst
  obtain ⟨t, ht0, ht1, hb⟩ := dl_straight_param hl hc
  have hsp := dl_seg_split ht0 ht1 hb
  have hsm := dl_seg_mem ht0 ht1 hb
  have hq0 : delLast p (Fin.last (n+1)) = p (Fin.castSucc (Fin.last (n+1))) := rfl
  have hq1 : delLast p (Fin.last (n+1) + 1) = p 0 := by rw [del_f4]; rfl
  ext z
  simp only [edgeSet, Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    by_cases hil : i = Fin.last (n+1)
    · subst hil
      rw [hq0, hq1] at hi
      rcases hsp hi with h | h
      · exact ⟨Fin.castSucc (Fin.last (n+1)), by rw [del_f2]; exact h⟩
      · exact ⟨Fin.last (n+2), by rw [del_f3]; exact h⟩
    · refine ⟨Fin.castSucc i, ?_⟩
      have : delLast p (i + 1) = p (Fin.castSucc i + 1) := by rw [del_f1 n i hil]; rfl
      rw [this] at hi
      exact hi
  · rintro ⟨k, hk⟩
    induction k using Fin.lastCases with
    | last =>
      rw [del_f3] at hk
      exact ⟨Fin.last (n+1), by rw [hq0, hq1]; exact hsm.2 hk⟩
    | cast i =>
      by_cases hil : i = Fin.last (n+1)
      · subst hil
        rw [del_f2] at hk
        exact ⟨Fin.last (n+1), by rw [hq0, hq1]; exact hsm.1 hk⟩
      · refine ⟨i, ?_⟩
        have : delLast p (i + 1) = p (Fin.castSucc i + 1) := by rw [del_f1 n i hil]; rfl
        rw [this]
        exact hk

theorem delLast_simple {n : ℕ} {p : Fin (n+3) → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hst : extAng p (Fin.last (n+2)) = 0) :
    SimplePoly (delLast p) := by
  obtain ⟨lam, hl, hc⟩ := straight_data hinj hst
  obtain ⟨t, ht0, ht1, hb⟩ := dl_straight_param hl hc
  have hsp := dl_seg_split ht0 ht1 hb
  have hq0 : delLast p (Fin.last (n+1)) = p (Fin.castSucc (Fin.last (n+1))) := rfl
  have hq1 : delLast p (Fin.last (n+1) + 1) = p 0 := by rw [del_f4]; rfl
  have hqn : ∀ i : Fin (n+2), i ≠ Fin.last (n+1) → delLast p (i + 1) = p (Fin.castSucc i + 1) := by
    intro i hi; rw [del_f1 n i hi]; rfl
  have key : ∀ j : Fin (n+2), j ≠ Fin.last (n+1) → ∀ z : ℂ, z ∈ segment ℝ (delLast p (Fin.last (n+1))) (delLast p (Fin.last (n+1) + 1)) →
      z ∈ segment ℝ (delLast p j) (delLast p (j + 1)) →
      (z = delLast p (Fin.last (n+1)) ∨ z = delLast p (Fin.last (n+1) + 1)) ∧ (z = delLast p j ∨ z = delLast p (j + 1)) := by
    intro j hj z hz1 hz2
    rw [hq0, hq1] at hz1
    rw [hqn j hj] at hz2 ⊢
    have hjn : ∀ m : Fin (n+2), p (Fin.last (n+2)) ≠ p (Fin.castSucc m) := fun m h => del_last_ne n m (hinj h)
    have hj' : ∀ k : Fin (n+3), k ≠ Fin.castSucc j → z ∈ segment ℝ (p k) (p (k + 1)) →
        (z = p k ∨ z = p (k + 1)) ∧ (z = p (Fin.castSucc j) ∨ z = p (Fin.castSucc j + 1)) :=
      fun k hk hz => hs k (Fin.castSucc j) hk z ⟨hz, hz2⟩
    have hcj : p (Fin.last (n+2)) ≠ p (Fin.castSucc j + 1) := by
      rw [del_f1 n j hj]; exact hjn _
    rcases hsp hz1 with h | h
    · have hne : Fin.castSucc (Fin.last (n+1)) ≠ Fin.castSucc j := fun e => hj (Fin.castSucc_injective _ e).symm
      have := hj' _ hne (by rw [del_f2]; exact h)
      rw [del_f2] at this
      refine ⟨?_, this.2.imp id id |>.imp id id⟩
      · rcases this.1 with e | e
        · left; exact e
        · exfalso
          rcases this.2 with e2 | e2
          · exact hjn _ (e.symm.trans e2)
          · exact hcj (e.symm.trans e2)
    · have hne : Fin.last (n+2) ≠ Fin.castSucc j := del_last_ne n j
      have := hj' _ hne (by rw [del_f3]; exact h)
      rw [del_f3] at this
      refine ⟨?_, this.2⟩
      rcases this.1 with e | e
      · exfalso
        rcases this.2 with e2 | e2
        · exact hjn _ (e.symm.trans e2)
        · exact hcj (e.symm.trans e2)
      · right; rw [hq1]; exact e
  intro i j hij z hz
  by_cases hi : i = Fin.last (n+1)
  · subst hi
    have hj : j ≠ Fin.last (n+1) := fun e => hij (e.symm)
    exact key j hj z hz.1 hz.2
  · by_cases hj : j = Fin.last (n+1)
    · subst hj
      have := key i hi z hz.2 hz.1
      exact ⟨this.2, this.1⟩
    · have hne : Fin.castSucc i ≠ Fin.castSucc j := fun e => hij (Fin.castSucc_injective _ e)
      have hz1 : z ∈ segment ℝ (p (Fin.castSucc i)) (p (Fin.castSucc i + 1)) := by rw [← hqn i hi]; exact hz.1
      have hz2 : z ∈ segment ℝ (p (Fin.castSucc j)) (p (Fin.castSucc j + 1)) := by rw [← hqn j hj]; exact hz.2
      have := hs _ _ hne z ⟨hz1, hz2⟩
      rw [← hqn i hi, ← hqn j hj] at this
      exact this

theorem delLast_extAng {n : ℕ} {p : Fin (n+3) → ℂ} (hinj : Function.Injective p) (hst : extAng p (Fin.last (n+2)) = 0) (j : Fin (n+2)) :
    extAng (delLast p) j = extAng p (Fin.castSucc j) := by
  obtain ⟨lam, hl, hc⟩ := straight_data hinj hst
  have hq1 : delLast p (Fin.last (n+1) + 1) = p 0 := by rw [del_f4]; rfl
  have hqn : ∀ i : Fin (n+2), i ≠ Fin.last (n+1) → delLast p (i + 1) = p (Fin.castSucc i + 1) := by
    intro i hi; rw [del_f1 n i hi]; rfl
  by_cases hj0 : j = 0
  · subst hj0
    have e1 : delLast p (0 + 1) = p (Fin.castSucc 0 + 1) := hqn 0 (Fin.last_pos.ne)
    unfold extAng
    rw [e1, del_f6' n, del_f5, del_f6 n]
    have h0 : delLast p 0 = p 0 := rfl
    have ha : delLast p (Fin.last (n+1)) = p (Fin.castSucc (Fin.last (n+1))) := rfl
    rw [h0, ha]
    set a := p (Fin.castSucc (Fin.last (n+1)))
    set b := p (Fin.last (n+2))
    set c := p 0
    have hb : b - a = (1 / lam : ℝ) * (c - b) := by
      have : (lam : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
      rw [hc]; push_cast; field_simp
    have : c - a = (((1 + lam) / lam : ℝ) : ℂ) * (c - b) := by
      have h2 : c - a = (c - b) + (b - a) := by ring
      rw [h2, hb]
      have : (lam : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
      push_cast
      field_simp
      ring
    rw [this]
    exact dl_arg_div_scale_den _ _ (by positivity)
  · by_cases hjl : j = Fin.last (n+1)
    · subst hjl
      unfold extAng
      rw [hq1, del_f2, del_f8 n _ (del_last_ne0 n)]
      have ha : delLast p (Fin.last (n+1)) = p (Fin.castSucc (Fin.last (n+1))) := rfl
      have hpr : delLast p (Fin.last (n+1) - 1) = p (Fin.castSucc (Fin.last (n+1) - 1)) := rfl
      rw [ha, hpr]
      set a := p (Fin.castSucc (Fin.last (n+1)))
      set b := p (Fin.last (n+2))
      set c := p 0
      have : c - a = (((1 + lam : ℝ)) : ℂ) * (b - a) := by
        push_cast
        linear_combination hc
      rw [this]
      exact dl_arg_div_scale_num _ _ (by positivity)
    · unfold extAng
      rw [hqn j hjl, del_f8 n j hj0]
      rfl

#print axioms delLast_simple
#print axioms delLast_extAng
#print axioms delLast_edgeSet

end Erdos634.Draft.LaczFormal.WN
