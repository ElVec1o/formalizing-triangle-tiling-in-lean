-- Draft/LaczFormalIIcWN9.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2/6.3, Route B, item B5, part 3:
-- the "right value" of an edge is constant along the edge, and the winding number near an open-edge point takes only the values R, R+1.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2/6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN8

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

theorem exp_half_pi : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * I) = I := by
  rw [Complex.exp_mul_I]; push_cast
  rw [Complex.cos_pi_div_two, Complex.sin_pi_div_two]; ring

theorem exp_three_half_pi : Complex.exp (((3 * Real.pi / 2 : ℝ) : ℂ) * I) = -I := by
  have : ((3 * Real.pi / 2 : ℝ) : ℂ) * I = ((Real.pi / 2 : ℝ) : ℂ) * I + (Real.pi : ℂ) * I := by push_cast; ring
  rw [this, Complex.exp_add, exp_half_pi, Complex.exp_pi_mul_I]; ring

/-- `Good p i s R`: just to the right of the edge point `s` the winding number is `R` and just to the left `R + 1`. -/
def Good (p : Fin n → ℂ) (i : Fin n) (s R : ℝ) : Prop :=
  ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε →
    sidePt (p i) (p (i + 1)) s t ∉ edgeSet p ∧ sidePt (p i) (p (i + 1)) s (-t) ∉ edgeSet p ∧
    wind p (sidePt (p i) (p (i + 1)) s (-t)) = R ∧ wind p (sidePt (p i) (p (i + 1)) s t) = R + 1

theorem good_exists {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n)
    (i : Fin n) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) : ∃ k : ℤ, Good p i s k := by
  have hd : p (i + 1) - p i ≠ 0 := sub_ne_zero.2 (nd hinj hn i)
  have hj := wind_jump p i hd hs0 hs1 (fun j hj => by
    have := interior_not_other hs hinj hn i hs0 hs1 j hj
    simpa [sidePt] using this)
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hj
  have hu0 : (0 : ℝ) < u := hu
  set t0 := u / 2 with ht0
  have ht0m : t0 ∈ Set.Ioo 0 u := ⟨by positivity, by linarith⟩
  obtain ⟨k, hk⟩ := wind_int p _ (hsub ht0m).2.1
  refine ⟨k, u, hu0, fun t ht0' htu => ?_⟩
  have hm : t ∈ Set.Ioo 0 u := ⟨ht0', htu⟩
  have h1 := hsub hm
  have hconst : wind p (sidePt (p i) (p (i + 1)) s (-t)) = wind p (sidePt (p i) (p (i + 1)) s (-t0)) := by
    apply wind_const_segment
    intro z hz
    rw [segment_eq_image'] at hz
    obtain ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩ := hz
    have hτ : (1 - θ) * t + θ * t0 ∈ Set.Ioo 0 u := by
      constructor <;> nlinarith [ht0m.1, ht0m.2, hm.1, hm.2]
    have e : sidePt (p i) (p (i + 1)) s (-t) + θ • (sidePt (p i) (p (i + 1)) s (-t0) - sidePt (p i) (p (i + 1)) s (-t)) =
        sidePt (p i) (p (i + 1)) s (-((1 - θ) * t + θ * t0)) := by
      simp only [sidePt, Complex.real_smul]; push_cast; ring
    beta_reduce
    rw [e]
    exact (hsub hτ).2.1
  refine ⟨h1.1, h1.2.1, ?_, ?_⟩
  · rw [hconst, hk]
  · rw [h1.2.2, hconst, hk]

theorem good_unique_s {p : Fin n → ℂ} {i : Fin n} {s R R' : ℝ} (h : Good p i s R) (h' : Good p i s R') : R = R' := by
  obtain ⟨ε, hε, h1⟩ := h
  obtain ⟨ε', hε', h2⟩ := h'
  have ht : 0 < min ε ε' / 2 := by have := lt_min hε hε'; positivity
  have a := (h1 (min ε ε' / 2) ht (by have := min_le_left ε ε'; linarith [lt_min hε hε'])).2.2.1
  have b := (h2 (min ε ε' / 2) ht (by have := min_le_right ε ε'; linarith [lt_min hε hε'])).2.2.1
  rw [← a, ← b]


theorem sidePt_right {a b : ℂ} (hab : a ≠ b) (s t : ℝ) :
    sidePt a b s (-t) = pt (a + (s : ℂ) * (b - a)) (edir a b) (t * ‖a - b‖) (Real.pi / 2) := by
  have h := edir_mul hab
  unfold sidePt pt
  rw [exp_half_pi]
  push_cast
  linear_combination (-(t : ℂ) * I) * h

theorem sidePt_left {a b : ℂ} (hab : a ≠ b) (s t : ℝ) :
    sidePt a b s t = pt (a + (s : ℂ) * (b - a)) (edir a b) (t * ‖a - b‖) (3 * Real.pi / 2) := by
  have h := edir_mul hab
  unfold sidePt pt
  rw [exp_three_half_pi]
  push_cast
  linear_combination ((t : ℂ) * I) * h


theorem arg_pos_pi {w : ℂ} (h : 0 < w.im) : 0 < Complex.arg w ∧ Complex.arg w < Real.pi := by
  refine ⟨lt_of_le_of_ne (Complex.arg_nonneg_iff.2 h.le) (Ne.symm ?_), lt_of_le_of_ne (Complex.arg_le_pi w) ?_⟩
  · intro h0; rw [Complex.arg_eq_zero_iff] at h0; linarith [h0.2]
  · intro h0; rw [Complex.arg_eq_pi_iff] at h0; linarith [h0.2]

theorem pt_eq_mul {v d1 w : ℂ} (L : ℝ) :
    v + d1 * (L : ℂ) * w = pt v d1 (L * ‖w‖) (Complex.arg w) := by
  unfold pt
  have := Complex.norm_mul_exp_arg_mul_I w
  push_cast
  linear_combination (-(d1 * (L : ℂ))) * this

/-- Sector data at an open-edge point: right sector has winding `R`, left sector `R + 1`. -/
theorem edge_sectors {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n)
    (i : Fin n) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {R : ℝ} (hg : Good p i s R) :
    ∃ r > 0, TwoRays p (p i + (s : ℂ) * (p (i + 1) - p i)) (edir (p i) (p (i + 1))) Real.pi r ∧
      (∀ ρ θ : ℝ, 0 < ρ → ρ < r → 0 < θ → θ < Real.pi →
        wind p (pt (p i + (s : ℂ) * (p (i + 1) - p i)) (edir (p i) (p (i + 1))) ρ θ) = R) ∧
      (∀ ρ θ : ℝ, 0 < ρ → ρ < r → Real.pi < θ → θ < 2 * Real.pi →
        wind p (pt (p i + (s : ℂ) * (p (i + 1) - p i)) (edir (p i) (p (i + 1))) ρ θ) = R + 1) := by
  obtain ⟨r, hr, -, -, hR⟩ := tworays_edge hs hinj hn i hs0 hs1
  obtain ⟨ε, hε, hgε⟩ := hg
  have hab : p i ≠ p (i + 1) := (nd hinj hn i).symm
  have hd1 := edir_norm hab
  have hL : 0 < ‖p i - p (i + 1)‖ := norm_pos_iff.2 (sub_ne_zero.2 hab)
  set L := ‖p i - p (i + 1)‖ with hLdef
  set t0 := min (ε / 2) (r / (2 * L)) with ht0def
  have ht0 : 0 < t0 := lt_min (by positivity) (by positivity)
  have ht0ε : t0 < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have ht0r : t0 * L < r := by
    have h1 : t0 ≤ r / (2 * L) := min_le_right _ _
    have h2 : t0 * L ≤ r / (2 * L) * L := mul_le_mul_of_nonneg_right h1 hL.le
    have h3 : r / (2 * L) * L = r / 2 := by field_simp
    linarith
  have hpi := Real.pi_pos
  obtain ⟨-, -, hwr, hwl⟩ := hgε t0 ht0 ht0ε
  rw [sidePt_right hab] at hwr
  rw [sidePt_left hab] at hwl
  refine ⟨r, hr, hR, ?_, ?_⟩
  · intro ρ θ hρ hρr hθ0 hθ1
    rw [← hwr]
    refine sector_const hR hd1 hpi (by linarith) hρ hρr (by positivity) ht0r ?_
    intro φ hφ
    rcases le_total θ (Real.pi / 2) with h | h
    · rw [Set.uIcc_of_le h] at hφ; obtain ⟨a1, a2⟩ := hφ
      exact ⟨by linarith, by linarith, by linarith⟩
    · rw [Set.uIcc_of_ge h] at hφ; obtain ⟨a1, a2⟩ := hφ
      exact ⟨by linarith, by linarith, by linarith⟩
  · intro ρ θ hρ hρr hθ0 hθ1
    rw [← hwl]
    refine sector_const hR hd1 hpi (by linarith) hρ hρr (by positivity) ht0r ?_
    intro φ hφ
    rcases le_total θ (3 * Real.pi / 2) with h | h
    · rw [Set.uIcc_of_le h] at hφ; obtain ⟨a1, a2⟩ := hφ
      exact ⟨by linarith, by linarith, by linarith⟩
    · rw [Set.uIcc_of_ge h] at hφ; obtain ⟨a1, a2⟩ := hφ
      exact ⟨by linarith, by linarith, by linarith⟩

/-- Near an open-edge point the winding number takes only the values `R`, `R+1`. -/
theorem good_ball {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n)
    (i : Fin n) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {R : ℝ} (hg : Good p i s R) :
    ∃ r > 0, ∀ z : ℂ, dist z (p i + (s : ℂ) * (p (i + 1) - p i)) < r → z ∉ edgeSet p →
      wind p z = R ∨ wind p z = R + 1 := by
  obtain ⟨r, hr, hR, h1, h2⟩ := edge_sectors hs hinj hn i hs0 hs1 hg
  have hd1 := edir_norm (nd hinj hn i).symm
  refine ⟨r, hr, fun z hz hzE => ?_⟩
  obtain ⟨ρ, θ, hρ, hρr, hθ0, hθ1, hθΔ, rfl⟩ := pt_cover hR hd1 hr hz hzE
  rcases lt_or_gt_of_ne hθΔ with h | h
  · exact Or.inl (h1 ρ θ hρ hρr hθ0 h)
  · exact Or.inr (h2 ρ θ hρ hρr h hθ1)

/-- The right value is locally constant along an edge. -/
theorem good_local {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n)
    (i : Fin n) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {R : ℝ} (hg : Good p i s R) :
    ∃ δ > 0, ∀ s' R' : ℝ, |s' - s| < δ → Good p i s' R' → R' = R := by
  obtain ⟨r, hr, hR, h1, h2⟩ := edge_sectors hs hinj hn i hs0 hs1 hg
  have hab : p i ≠ p (i + 1) := (nd hinj hn i).symm
  have hd1 := edir_norm hab
  have hL : 0 < ‖p i - p (i + 1)‖ := norm_pos_iff.2 (sub_ne_zero.2 hab)
  set L := ‖p i - p (i + 1)‖ with hLdef
  refine ⟨r / (2 * L), by positivity, fun s' R' hss' hg' => ?_⟩
  obtain ⟨ε', hε', hgε'⟩ := hg'
  set t' := min (ε' / 2) (r / (2 * L)) with ht'def
  have ht' : 0 < t' := lt_min (by positivity) (by positivity)
  have ht'ε : t' < ε' := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨-, -, hwr, -⟩ := hgε' t' ht' ht'ε
  set w : ℂ := ((s - s' : ℝ) : ℂ) + (t' : ℂ) * I with hw
  have hwim : w.im = t' := by simp [hw]
  have hwre : w.re = s - s' := by simp [hw]
  obtain ⟨a1, a2⟩ := arg_pos_pi (w := w) (by rw [hwim]; exact ht')
  have hw0 : w ≠ 0 := by intro h; rw [h] at hwim; simp at hwim; linarith
  have hnw : ‖w‖ ≤ |s - s'| + t' := by
    have := Complex.norm_le_abs_re_add_abs_im w
    rw [hwre, hwim, abs_of_pos ht'] at this; exact this
  have hz : sidePt (p i) (p (i + 1)) s' (-t') =
      pt (p i + (s : ℂ) * (p (i + 1) - p i)) (edir (p i) (p (i + 1))) (L * ‖w‖) (Complex.arg w) := by
    rw [← pt_eq_mul]
    have h := edir_mul hab
    unfold sidePt
    rw [hw]; push_cast
    linear_combination (-(((s : ℂ) - s') + (t' : ℂ) * I)) * h
  have hρ : 0 < L * ‖w‖ := mul_pos hL (norm_pos_iff.2 hw0)
  have hρr : L * ‖w‖ < r := by
    have e1 : |s - s'| < r / (2 * L) := by rw [abs_sub_comm]; exact hss'
    have e2 : t' ≤ r / (2 * L) := min_le_right _ _
    have e3 : L * ‖w‖ ≤ L * (|s - s'| + t') := mul_le_mul_of_nonneg_left hnw hL.le
    have e4 : L * (|s - s'| + t') < L * (r / (2 * L) + r / (2 * L)) :=
      mul_lt_mul_of_pos_left (by linarith) hL
    have e5 : L * (r / (2 * L) + r / (2 * L)) = r := by field_simp; ring
    linarith
  rw [hz] at hwr
  rw [← hwr]
  exact h1 _ _ hρ hρr a1 a2


/-- **The right value is constant along an edge.** -/
theorem good_edge_const {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n)
    (i : Fin n) {s s' R R' : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hs0' : 0 < s') (hs1' : s' < 1)
    (hg : Good p i s R) (hg' : Good p i s' R') : R = R' := by
  let g : ℝ → ℤ := fun u => if h : 0 < u ∧ u < 1 then Classical.choose (good_exists hs hinj hn i h.1 h.2) else 0
  have hgood : ∀ u ∈ Set.Ioo (0 : ℝ) 1, Good p i u (g u) := by
    intro u hu
    have h : 0 < u ∧ u < 1 := hu
    simp only [g, dif_pos h]
    exact Classical.choose_spec (good_exists hs hinj hn i h.1 h.2)
  have hloc : ∀ u ∈ Set.Ioo (0 : ℝ) 1, ∀ᶠ v in 𝓝 u, g v = g u := by
    intro u hu
    obtain ⟨δ, hδ, hl⟩ := good_local hs hinj hn i hu.1 hu.2 (hgood u hu)
    filter_upwards [Ioo_mem_nhds hu.1 hu.2, Metric.ball_mem_nhds u hδ] with v hv hvb
    have := hl v (g v) (by rw [← Real.dist_eq]; exact hvb) (hgood v hv)
    exact_mod_cast this
  have hcont : ContinuousOn g (Set.Ioo 0 1) := by
    intro u hu
    have h2 : g =ᶠ[𝓝 u] fun _ => g u := hloc u hu
    exact ((continuousAt_const (y := g u)).congr h2.symm).continuousWithinAt
  have e := isPreconnected_Ioo.constant hcont (x := s) (y := s') ⟨hs0, hs1⟩ ⟨hs0', hs1'⟩
  have a := good_unique_s hg (hgood s ⟨hs0, hs1⟩)
  have b := good_unique_s hg' (hgood s' ⟨hs0', hs1'⟩)
  rw [a, b, e]

end Erdos634.Draft.LaczFormal.WN
