-- Draft/LaczFormalIIcWN8.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2/6.3, Route B, item B5, part 2:
-- the `TwoRays` data of a simple polygon at an open-edge point and at a vertex.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2/6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN7

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

/-- Unit vector from `b` towards `a`. -/
noncomputable def edir (a b : ℂ) : ℂ := (a - b) / (‖a - b‖ : ℂ)

theorem edir_norm {a b : ℂ} (h : a ≠ b) : ‖edir a b‖ = 1 := by
  unfold edir
  have : ‖a - b‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 h)
  rw [norm_div]; simp [this]

theorem edir_mul {a b : ℂ} (h : a ≠ b) : (‖a - b‖ : ℂ) * edir a b = a - b := by
  unfold edir
  have : (‖a - b‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 (sub_ne_zero.2 h)
  field_simp

/-- Membership in a segment from `v` to `a`, as a bounded ray. -/
theorem seg_ray {v a y : ℂ} (hav : a ≠ v) :
    y ∈ segment ℝ v a ↔ ∃ τ : ℝ, 0 ≤ τ ∧ τ ≤ ‖a - v‖ ∧ y = v + (τ : ℂ) * edir a v := by
  have hL : 0 < ‖a - v‖ := norm_pos_iff.2 (sub_ne_zero.2 hav)
  rw [segment_eq_image']
  constructor
  · rintro ⟨u, ⟨hu0, hu1⟩, rfl⟩
    refine ⟨u * ‖a - v‖, by positivity, by nlinarith, ?_⟩
    have := edir_mul hav
    simp only [Complex.real_smul]
    push_cast
    linear_combination (-(u : ℂ)) * this
  · rintro ⟨τ, h0, h1, rfl⟩
    refine ⟨τ / ‖a - v‖, ⟨by positivity, by rw [div_le_one hL]; exact h1⟩, ?_⟩
    have := edir_mul hav
    simp only [Complex.real_smul]
    have hLc : (‖a - v‖ : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    push_cast
    field_simp
    linear_combination (-(τ : ℂ)) * this

/-- A ball around `x` avoiding finitely many segments, none of which contains `x`. -/
theorem exists_ball_avoid (p : Fin n → ℂ) (J : Set (Fin n)) (x : ℂ)
    (hx : ∀ j ∈ J, x ∉ segment ℝ (p j) (p (j + 1))) :
    ∃ r > 0, ∀ y, dist y x < r → ∀ j ∈ J, y ∉ segment ℝ (p j) (p (j + 1)) := by
  set E' : Set ℂ := ⋃ j ∈ J, segment ℝ (p j) (p (j + 1)) with hE'
  have hc : IsClosed E' := isClosed_iUnion_of_finite fun j => isClosed_iUnion_of_finite fun _ => isClosed_segment' _ _
  have hxE : x ∉ E' := by
    simp only [hE', Set.mem_iUnion, not_exists]
    exact fun j hj => hx j hj
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hc.isOpen_compl x hxE
  refine ⟨r, hr, fun y hy j hj hyj => ?_⟩
  exact hball (Metric.mem_ball.2 hy) (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hj, hyj⟩⟩)

/-- Generic `TwoRays` from a description of the polygon near `v` as two segments. -/
theorem tworays_gen {p : Fin n → ℂ} {v a c : ℂ} {r Δ : ℝ} (hav : a ≠ v) (hcv : c ≠ v)
    (hra : r ≤ ‖a - v‖) (hrc : r ≤ ‖c - v‖) (hΔ : edir a v * Complex.exp (Δ * I) = edir c v)
    (hE : ∀ y, dist y v < r → (y ∈ edgeSet p ↔ y ∈ segment ℝ v a ∨ y ∈ segment ℝ v c)) :
    TwoRays p v (edir a v) Δ r := by
  intro y hy
  rw [hE y hy, seg_ray hav, seg_ray hcv, ← hΔ]
  have hn1 : ‖edir a v‖ = 1 := edir_norm hav
  have hn2 : ‖edir a v * Complex.exp (Δ * I)‖ = 1 := by rw [hΔ]; exact edir_norm hcv
  have hd : ∀ τ : ℝ, 0 ≤ τ → ∀ e : ℂ, ‖e‖ = 1 → y = v + (τ : ℂ) * e → τ < r := by
    intro τ hτ e he hye
    have : dist y v = τ := by rw [hye, dist_eq_norm]; simp [he, abs_of_nonneg hτ]
    linarith
  constructor
  · rintro (⟨τ, h0, h1, he⟩ | ⟨τ, h0, h1, he⟩)
    · exact Or.inl ⟨τ, h0, he⟩
    · exact Or.inr ⟨τ, h0, he⟩
  · rintro (⟨τ, h0, he⟩ | ⟨τ, h0, he⟩)
    · exact Or.inl ⟨τ, h0, by have := hd τ h0 _ hn1 he; linarith, he⟩
    · refine Or.inr ⟨τ, h0, ?_, he⟩
      have := hd τ h0 _ hn2 he
      linarith


theorem fin_one_ne (hn : 3 ≤ n) : (1 : Fin n) ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

theorem fin_one_add_one_ne (hn : 3 ≤ n) : (1 : Fin n) + 1 ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  rw [Fin.val_add] at this
  simp at this
  rw [Nat.mod_eq_of_lt (by omega : 2 < n)] at this
  omega

theorem nd {p : Fin n → ℂ} (hinj : Function.Injective p) (hn : 3 ≤ n) (i : Fin n) : p (i + 1) ≠ p i := by
  intro h
  have := hinj h
  exact fin_one_ne hn (by simpa using this)

theorem nd2 {p : Fin n → ℂ} (hinj : Function.Injective p) (hn : 3 ≤ n) (i : Fin n) : p (i + 1 + 1) ≠ p i := by
  intro h
  have := hinj h
  apply fin_one_add_one_ne hn
  have h2 : i + (1 + 1) = i + 0 := by rw [← add_assoc]; simpa using this
  exact add_left_cancel h2

theorem vertex_not_other {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (i : Fin n) :
    ∀ j, j ≠ i → j ≠ i + 1 → p (i + 1) ∉ segment ℝ (p j) (p (j + 1)) := by
  intro j h1 h2 hm
  have := (hs i j (Ne.symm h1) (p (i + 1)) ⟨right_mem_segment ℝ _ _, hm⟩).2
  rcases this with h | h
  · exact h2 (hinj h).symm
  · exact h1 (add_right_cancel (hinj h)).symm

theorem interior_not_other {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n)
    (i : Fin n) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∀ j, j ≠ i → p i + (s : ℂ) * (p (i + 1) - p i) ∉ segment ℝ (p j) (p (j + 1)) := by
  intro j hj hm
  have hmem : p i + (s : ℂ) * (p (i + 1) - p i) ∈ segment ℝ (p i) (p (i + 1)) := by
    rw [segment_eq_image']
    exact ⟨s, ⟨hs0.le, hs1.le⟩, by simp [Complex.real_smul]⟩
  have := (hs i j (Ne.symm hj) _ ⟨hmem, hm⟩).1
  have hd := sub_ne_zero.2 (nd hinj hn i)
  rcases this with h | h
  · have : (s : ℂ) * (p (i + 1) - p i) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h0 | h0
    · exact hs0.ne' (by exact_mod_cast h0)
    · exact hd h0
  · have : ((s : ℂ) - 1) * (p (i + 1) - p i) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h0 | h0
    · have h3 : (s : ℂ) = 1 := by linear_combination h0
      exact hs1.ne (by exact_mod_cast h3)
    · exact hd h0

theorem edir_edge1 {a b : ℂ} (hab : a ≠ b) {s : ℝ} (hs0 : 0 < s) :
    edir a (a + (s : ℂ) * (b - a)) = edir a b := by
  unfold edir
  have e1 : a - (a + (s : ℂ) * (b - a)) = (s : ℂ) * (a - b) := by ring
  rw [e1, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
  have : ‖a - b‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hab)
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hnc : (‖a - b‖ : ℂ) ≠ 0 := by exact_mod_cast this
  push_cast
  field_simp

theorem edir_edge2 {a b : ℂ} (hab : a ≠ b) {s : ℝ} (hs1 : s < 1) :
    edir b (a + (s : ℂ) * (b - a)) = -edir a b := by
  unfold edir
  have e1 : b - (a + (s : ℂ) * (b - a)) = ((1 - s : ℝ) : ℂ) * (b - a) := by push_cast; ring
  rw [e1, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s)]
  have hba : ‖b - a‖ = ‖a - b‖ := norm_sub_rev b a
  have : ‖a - b‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hab)
  have hs1c : ((1 - s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sub_pos.2 hs1).ne'
  have hnc : (‖a - b‖ : ℂ) ≠ 0 := by exact_mod_cast this
  rw [hba]
  have e2 : b - a = -(a - b) := by ring
  rw [e2]
  push_cast
  push_cast at hs1c
  field_simp

theorem seg_split {a b x : ℂ} {s : ℝ} (hx : x = a + (s : ℂ) * (b - a)) (hs0 : 0 < s) (hs1 : s < 1) (y : ℂ) :
    y ∈ segment ℝ a b ↔ y ∈ segment ℝ x a ∨ y ∈ segment ℝ x b := by
  rw [segment_eq_image', segment_eq_image', segment_eq_image']
  have hs0' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hs1' : (1 : ℂ) - s ≠ 0 := by
    intro h; apply hs1.ne; have : (s : ℂ) = 1 := by linear_combination -h
    exact_mod_cast this
  constructor
  · rintro ⟨u, ⟨hu0, hu1⟩, rfl⟩
    rcases le_total u s with h | h
    · left
      refine ⟨(s - u) / s, ⟨div_nonneg (by linarith) hs0.le, by rw [div_le_one hs0]; linarith⟩, ?_⟩
      subst hx
      simp only [Complex.real_smul]; push_cast; field_simp; ring
    · right
      refine ⟨(u - s) / (1 - s), ⟨div_nonneg (by linarith) (by linarith), by rw [div_le_one (by linarith)]; linarith⟩, ?_⟩
      subst hx
      simp only [Complex.real_smul]; push_cast; field_simp; ring
  · rintro (⟨θ, ⟨h0, h1⟩, rfl⟩ | ⟨θ, ⟨h0, h1⟩, rfl⟩)
    · refine ⟨s * (1 - θ), ⟨by nlinarith, by nlinarith⟩, ?_⟩
      subst hx
      simp only [Complex.real_smul]; push_cast; ring
    · refine ⟨s + θ * (1 - s), ⟨by nlinarith, by nlinarith⟩, ?_⟩
      subst hx
      simp only [Complex.real_smul]; push_cast; ring


theorem norm_a_x {a b : ℂ} {s : ℝ} (hs0 : 0 < s) : ‖a - (a + (s : ℂ) * (b - a))‖ = s * ‖a - b‖ := by
  have e1 : a - (a + (s : ℂ) * (b - a)) = (s : ℂ) * (a - b) := by ring
  rw [e1, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]

theorem norm_b_x {a b : ℂ} {s : ℝ} (hs1 : s < 1) : ‖b - (a + (s : ℂ) * (b - a))‖ = (1 - s) * ‖a - b‖ := by
  have e1 : b - (a + (s : ℂ) * (b - a)) = ((1 - s : ℝ) : ℂ) * (b - a) := by push_cast; ring
  rw [e1, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s), norm_sub_rev b a]

/-- **TwoRays at an open-edge point.** -/
theorem tworays_edge {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n)
    (i : Fin n) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ r > 0, r ≤ s * ‖p i - p (i + 1)‖ ∧ r ≤ (1 - s) * ‖p i - p (i + 1)‖ ∧
      TwoRays p (p i + (s : ℂ) * (p (i + 1) - p i)) (edir (p i) (p (i + 1))) Real.pi r := by
  have hab : p i ≠ p (i + 1) := (nd hinj hn i).symm
  have hL : 0 < ‖p i - p (i + 1)‖ := norm_pos_iff.2 (sub_ne_zero.2 hab)
  obtain ⟨r1, hr1, hav⟩ := exists_ball_avoid p {j | j ≠ i} (p i + (s : ℂ) * (p (i + 1) - p i))
    (fun j hj => interior_not_other hs hinj hn i hs0 hs1 j hj)
  set L := ‖p i - p (i + 1)‖ with hLdef
  have hsL : 0 < s * L := by positivity
  have h1sL : 0 < (1 - s) * L := mul_pos (by linarith) hL
  refine ⟨min r1 (min (s * L) ((1 - s) * L)), lt_min hr1 (lt_min hsL h1sL),
    (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  have hax : p i ≠ p i + (s : ℂ) * (p (i + 1) - p i) := by
    refine sub_ne_zero.1 (norm_pos_iff.1 ?_)
    rw [norm_a_x hs0]; positivity
  have hbx : p (i + 1) ≠ p i + (s : ℂ) * (p (i + 1) - p i) := by
    refine sub_ne_zero.1 (norm_pos_iff.1 ?_)
    rw [norm_b_x hs1]; positivity
  have hra : min r1 (min (s * L) ((1 - s) * L)) ≤ ‖p i - (p i + (s : ℂ) * (p (i + 1) - p i))‖ := by
    rw [norm_a_x hs0]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hrc : min r1 (min (s * L) ((1 - s) * L)) ≤ ‖p (i + 1) - (p i + (s : ℂ) * (p (i + 1) - p i))‖ := by
    rw [norm_b_x hs1]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hΔ : edir (p i) (p i + (s : ℂ) * (p (i + 1) - p i)) * Complex.exp (Real.pi * I) =
      edir (p (i + 1)) (p i + (s : ℂ) * (p (i + 1) - p i)) := by
    rw [edir_edge1 hab hs0, edir_edge2 hab hs1, Complex.exp_pi_mul_I]; ring
  have key := tworays_gen (p := p) hax hbx hra hrc hΔ (by
    intro y hy
    constructor
    · intro hmem
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hmem
      by_cases hji : j = i
      · subst hji
        exact (seg_split rfl hs0 hs1 y).1 hj
      · exact absurd hj (hav y (lt_of_lt_of_le hy (min_le_left _ _)) j hji)
    · intro h
      exact Set.mem_iUnion.2 ⟨i, (seg_split rfl hs0 hs1 y).2 h⟩)
  rwa [edir_edge1 hab hs0] at key

/-- Two distinct unit complex numbers differ by `exp(Δ I)` with `0 < Δ < 2 pi`. -/
theorem exists_angle {d1 d2 : ℂ} (h1 : ‖d1‖ = 1) (h2 : ‖d2‖ = 1) (hne : d1 ≠ d2) :
    ∃ Δ : ℝ, 0 < Δ ∧ Δ < 2 * Real.pi ∧ d1 * Complex.exp (Δ * I) = d2 := by
  have hd0 : d1 ≠ 0 := by intro h; rw [h] at h1; simp at h1
  set u := d2 / d1 with hu
  have hun : ‖u‖ = 1 := by rw [hu, norm_div, h1, h2]; simp
  have hu1 : u ≠ 1 := by
    intro h; apply hne; rw [hu, div_eq_one_iff_eq hd0] at h; exact h.symm
  have hexp : Complex.exp (Complex.arg u * I) = u := by
    have := Complex.norm_mul_exp_arg_mul_I u
    rw [hun] at this; simpa using this
  have hne0 : Complex.arg u ≠ 0 := by
    intro h
    rw [Complex.arg_eq_zero_iff] at h
    apply hu1
    apply Complex.ext
    · have : u.re = 1 := by
        have hu' : u = (u.re : ℂ) := Complex.ext (by simp) (by simpa using h.2)
        have hh := hun
        rw [hu', Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h.1] at hh
        simpa using hh
      simpa using this
    · simpa using h.2
  have hpi := Real.pi_pos
  have ha1 := Complex.neg_pi_lt_arg u
  have ha2 := Complex.arg_le_pi u
  by_cases hpos : 0 < Complex.arg u
  · refine ⟨Complex.arg u, hpos, by linarith, ?_⟩
    rw [hexp, hu]; field_simp
  · refine ⟨Complex.arg u + 2 * Real.pi, by
        have : Complex.arg u < 0 := lt_of_le_of_ne (not_lt.1 hpos) hne0
        linarith, by
        have : Complex.arg u < 0 := lt_of_le_of_ne (not_lt.1 hpos) hne0
        linarith, ?_⟩
    have : Complex.exp (((Complex.arg u + 2 * Real.pi : ℝ) : ℂ) * I) = u := by
      rw [show ((Complex.arg u + 2 * Real.pi : ℝ) : ℂ) * I = (Complex.arg u : ℂ) * I + 2 * Real.pi * I by push_cast; ring,
        Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one, hexp]
    rw [this, hu]; field_simp


theorem rays_distinct {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n) (i : Fin n) :
    edir (p i) (p (i + 1)) ≠ edir (p (i + 1 + 1)) (p (i + 1)) := by
  intro heq
  have hav : p i ≠ p (i + 1) := (nd hinj hn i).symm
  have hcv : p (i + 1 + 1) ≠ p (i + 1) := nd hinj hn (i + 1)
  have hij : i ≠ i + 1 := by
    intro h
    apply fin_one_ne hn
    exact (add_left_cancel (a := i) (show i + 0 = i + 1 by simpa using h)).symm
  have hA := edir_mul hav
  have hC := edir_mul hcv
  rcases le_total ‖p i - p (i + 1)‖ ‖p (i + 1 + 1) - p (i + 1)‖ with hle | hle
  · have ha1 : p i ∈ segment ℝ (p i) (p (i + 1)) := left_mem_segment ℝ _ _
    have ha2 : p i ∈ segment ℝ (p (i + 1)) (p (i + 1 + 1)) := by
      rw [seg_ray hcv]
      refine ⟨‖p i - p (i + 1)‖, norm_nonneg _, hle, ?_⟩
      rw [← heq]; linear_combination (-1 : ℂ) * hA
    rcases (hs i (i + 1) hij _ ⟨ha1, ha2⟩).2 with h | h
    · exact hav h
    · exact nd2 hinj hn i h.symm
  · have hc2 : p (i + 1 + 1) ∈ segment ℝ (p (i + 1)) (p (i + 1 + 1)) := right_mem_segment ℝ _ _
    have hc1 : p (i + 1 + 1) ∈ segment ℝ (p i) (p (i + 1)) := by
      rw [segment_symm, seg_ray hav]
      refine ⟨‖p (i + 1 + 1) - p (i + 1)‖, norm_nonneg _, hle, ?_⟩
      rw [heq]; linear_combination (-1 : ℂ) * hC
    rcases (hs i (i + 1) hij _ ⟨hc1, hc2⟩).1 with h | h
    · exact nd2 hinj hn i h
    · exact hcv h

/-- **TwoRays at a vertex** `p (i+1)`: the incoming edge `i` and the outgoing edge `i+1`. -/
theorem tworays_vertex {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n) (i : Fin n) :
    ∃ r > 0, ∃ Δ : ℝ, 0 < Δ ∧ Δ < 2 * Real.pi ∧
      edir (p i) (p (i + 1)) * Complex.exp (Δ * I) = edir (p (i + 1 + 1)) (p (i + 1)) ∧
      TwoRays p (p (i + 1)) (edir (p i) (p (i + 1))) Δ r := by
  have hav : p i ≠ p (i + 1) := (nd hinj hn i).symm
  have hcv : p (i + 1 + 1) ≠ p (i + 1) := nd hinj hn (i + 1)
  obtain ⟨Δ, hΔ0, hΔ1, hΔ⟩ := exists_angle (edir_norm hav) (edir_norm hcv) (rays_distinct hs hinj hn i)
  obtain ⟨r1, hr1, hav'⟩ := exists_ball_avoid p {j | j ≠ i ∧ j ≠ i + 1} (p (i + 1))
    (fun j hj => vertex_not_other hs hinj i j hj.1 hj.2)
  have hLa : 0 < ‖p i - p (i + 1)‖ := norm_pos_iff.2 (sub_ne_zero.2 hav)
  have hLc : 0 < ‖p (i + 1 + 1) - p (i + 1)‖ := norm_pos_iff.2 (sub_ne_zero.2 hcv)
  refine ⟨min r1 (min ‖p i - p (i + 1)‖ ‖p (i + 1 + 1) - p (i + 1)‖), lt_min hr1 (lt_min hLa hLc), Δ, hΔ0, hΔ1, hΔ, ?_⟩
  refine tworays_gen hav hcv ((min_le_right _ _).trans (min_le_left _ _)) ((min_le_right _ _).trans (min_le_right _ _)) hΔ ?_
  intro y hy
  constructor
  · intro hmem
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hmem
    by_cases h1 : j = i
    · subst h1; left; rwa [segment_symm]
    · by_cases h2 : j = i + 1
      · subst h2; right; exact hj
      · exact absurd hj (hav' y (lt_of_lt_of_le hy (min_le_left _ _)) j ⟨h1, h2⟩)
  · rintro (h | h)
    · exact Set.mem_iUnion.2 ⟨i, by rwa [segment_symm]⟩
    · exact Set.mem_iUnion.2 ⟨i + 1, h⟩

end Erdos634.Draft.LaczFormal.WN
