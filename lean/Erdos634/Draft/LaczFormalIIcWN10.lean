-- Draft/LaczFormalIIcWN10.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2/6.3, Route B, item B5, part 4:
-- vertex gluing: the right values of consecutive edges agree, and near a vertex the winding number takes only the values k, k+1.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2/6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN9

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

theorem arg_small (c σ : ℝ) (hc : 0 < c) :
    Tendsto (fun t : ℝ => Complex.arg ((c : ℂ) + ((σ * t : ℝ) : ℂ) * I)) (𝓝 0) (𝓝 0) := by
  have hf : Continuous (fun t : ℝ => (c : ℂ) + ((σ * t : ℝ) : ℂ) * I) := by fun_prop
  have h0 : (c : ℂ) + ((σ * 0 : ℝ) : ℂ) * I ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left; simpa using hc
  have := (Complex.continuousAt_arg h0).tendsto.comp (hf.tendsto 0)
  simpa [Complex.arg_ofReal_of_nonneg hc.le] using this

theorem pt_add_two_pi (v d1 : ℂ) (ρ θ : ℝ) : pt v d1 ρ (θ + 2 * Real.pi) = pt v d1 ρ θ := by
  unfold pt
  rw [show ((θ + 2 * Real.pi : ℝ) : ℂ) * I = (θ : ℂ) * I + 2 * Real.pi * I by push_cast; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem pt_add_angle (v d1 : ℂ) (ρ Δ θ : ℝ) :
    pt v d1 ρ (Δ + θ) = v + (ρ : ℂ) * (d1 * Complex.exp (Δ * I)) * Complex.exp (θ * I) := by
  unfold pt
  rw [show ((Δ + θ : ℝ) : ℂ) * I = (Δ : ℂ) * I + (θ : ℂ) * I by push_cast; ring, Complex.exp_add]
  ring


theorem pt_eq_mul_rot {v d1 w : ℂ} (L Δ : ℝ) :
    v + (d1 * Complex.exp (Δ * I)) * (L : ℂ) * w = pt v d1 (L * ‖w‖) (Δ + Complex.arg w) := by
  rw [pt_add_angle]
  have := Complex.norm_mul_exp_arg_mul_I w
  push_cast
  linear_combination (-(d1 * Complex.exp (Δ * I) * (L : ℂ))) * this

/-- Abstract vertex gluing (no polygon indices): `a -> v -> c`, rays at `v` given by `TwoRays`. -/
theorem vertex_abstract {p : Fin n → ℂ} {a v c d1 : ℂ} {Δ r : ℝ} (hav : a ≠ v) (hcv : c ≠ v) (hr : 0 < r)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 2 * Real.pi) (hd1def : d1 = edir a v)
    (hΔ : d1 * Complex.exp (Δ * I) = edir c v) (hR : TwoRays p v d1 Δ r)
    {s s' : ℝ} (hs1 : s < 1) (hs1a : ‖a - v‖ * (1 - s) ≤ r / 4) (hs0' : 0 < s') (hs0c : ‖c - v‖ * s' ≤ r / 4)
    {k k' : ℝ}
    (hk : ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε → sidePt a v s t ∉ edgeSet p ∧ sidePt a v s (-t) ∉ edgeSet p ∧
      wind p (sidePt a v s (-t)) = k ∧ wind p (sidePt a v s t) = k + 1)
    (hk' : ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε → sidePt v c s' t ∉ edgeSet p ∧ sidePt v c s' (-t) ∉ edgeSet p ∧
      wind p (sidePt v c s' (-t)) = k' ∧ wind p (sidePt v c s' t) = k' + 1) :
    k' = k ∧ ∀ z : ℂ, dist z v < r → z ∉ edgeSet p → wind p z = k ∨ wind p z = k + 1 := by
  have hd1 : ‖d1‖ = 1 := by rw [hd1def]; exact edir_norm hav
  have hA := edir_mul hav
  have hC := edir_mul hcv
  rw [← hd1def] at hA
  rw [← hΔ] at hC
  have hLa : 0 < ‖a - v‖ := norm_pos_iff.2 (sub_ne_zero.2 hav)
  have hLc : 0 < ‖c - v‖ := norm_pos_iff.2 (sub_ne_zero.2 hcv)
  set La := ‖a - v‖ with hLadef
  set Lc := ‖c - v‖ with hLcdef
  obtain ⟨ε, hε, hkε⟩ := hk
  obtain ⟨ε', hε', hk'ε⟩ := hk'
  have hpi := Real.pi_pos
  set T0 := min (min ε ε') (min (r / (2 * La)) (r / (2 * Lc))) with hT0def
  have hT0 : 0 < T0 := lt_min (lt_min hε hε') (lt_min (by positivity) (by positivity))
  have hδa : 0 < 1 - s := by linarith
  set m := min Δ (2 * Real.pi - Δ) with hmdef
  have hm : 0 < m := lt_min hΔ0 (by linarith)
  have hmΔ : m ≤ Δ := min_le_left _ _
  have hm2 : m ≤ 2 * Real.pi - Δ := min_le_right _ _
  have ev1 := (arg_small (1 - s) 1 hδa).eventually (Metric.ball_mem_nhds (0 : ℝ) hm)
  have ev2 := (arg_small s' (-1) hs0').eventually (Metric.ball_mem_nhds (0 : ℝ) hm)
  have ev3 := (arg_small (1 - s) (-1) hδa).eventually (Metric.ball_mem_nhds (0 : ℝ) hm)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Set.Ioo 0 T0 ∧
      Complex.arg (((1 - s : ℝ) : ℂ) + ((1 * t : ℝ) : ℂ) * I) ∈ Metric.ball (0 : ℝ) m ∧
      Complex.arg ((s' : ℂ) + ((-1 * t : ℝ) : ℂ) * I) ∈ Metric.ball (0 : ℝ) m ∧
      Complex.arg (((1 - s : ℝ) : ℂ) + ((-1 * t : ℝ) : ℂ) * I) ∈ Metric.ball (0 : ℝ) m := by
    have h0 : Set.Ioo 0 T0 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hT0
    have h1 := (ev1.and (ev2.and ev3)).filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    filter_upwards [h0, h1] with t ht ⟨h1, h2, h3⟩
    exact ⟨ht, h1, h2, h3⟩
  obtain ⟨t, ht, a1, a2, a3⟩ := hev.exists
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at a1 a2 a3
  obtain ⟨ht0, htT⟩ := ht
  have htε : t < ε := lt_of_lt_of_le htT ((min_le_left _ _).trans (min_le_left _ _))
  have htε' : t < ε' := lt_of_lt_of_le htT ((min_le_left _ _).trans (min_le_right _ _))
  have htLa : t < r / (2 * La) := lt_of_lt_of_le htT ((min_le_right _ _).trans (min_le_left _ _))
  have htLc : t < r / (2 * Lc) := lt_of_lt_of_le htT ((min_le_right _ _).trans (min_le_right _ _))
  have htLa' : La * t < r / 2 := by
    have := mul_lt_mul_of_pos_left htLa hLa
    have e : La * (r / (2 * La)) = r / 2 := by field_simp
    linarith
  have htLc' : Lc * t < r / 2 := by
    have := mul_lt_mul_of_pos_left htLc hLc
    have e : Lc * (r / (2 * Lc)) = r / 2 := by field_simp
    linarith
  obtain ⟨-, -, hw1, hw3⟩ := hkε t ht0 htε
  obtain ⟨-, -, hw2, -⟩ := hk'ε t ht0 htε'
  -- reference sector values
  have sec1 : ∀ ρ θ : ℝ, 0 < ρ → ρ < r → 0 < θ → θ < Δ →
      wind p (pt v d1 ρ θ) = wind p (pt v d1 (r / 2) (Δ / 2)) := by
    intro ρ θ hρ hρr hθ0 hθ1
    refine sector_const hR hd1 hΔ0 hΔ1 hρ hρr (by positivity) (by linarith) ?_
    intro φ hφ
    rcases le_total θ (Δ / 2) with h | h
    · rw [Set.uIcc_of_le h] at hφ; obtain ⟨b1, b2⟩ := hφ
      exact ⟨by linarith, by linarith, by linarith⟩
    · rw [Set.uIcc_of_ge h] at hφ; obtain ⟨b1, b2⟩ := hφ
      exact ⟨by linarith, by linarith, by linarith⟩
  have sec2 : ∀ ρ θ : ℝ, 0 < ρ → ρ < r → Δ < θ → θ < 2 * Real.pi →
      wind p (pt v d1 ρ θ) = wind p (pt v d1 (r / 2) ((Δ + 2 * Real.pi) / 2)) := by
    intro ρ θ hρ hρr hθ0 hθ1
    refine sector_const hR hd1 hΔ0 hΔ1 hρ hρr (by positivity) (by linarith) ?_
    intro φ hφ
    rcases le_total θ ((Δ + 2 * Real.pi) / 2) with h | h
    · rw [Set.uIcc_of_le h] at hφ; obtain ⟨b1, b2⟩ := hφ
      exact ⟨by linarith, by linarith, by linarith⟩
    · rw [Set.uIcc_of_ge h] at hφ; obtain ⟨b1, b2⟩ := hφ
      exact ⟨by linarith, by linarith, by linarith⟩
  -- the three points
  set w1 : ℂ := ((1 - s : ℝ) : ℂ) + ((1 * t : ℝ) : ℂ) * I with hw1def
  set w2 : ℂ := (s' : ℂ) + ((-1 * t : ℝ) : ℂ) * I with hw2def
  set w3 : ℂ := ((1 - s : ℝ) : ℂ) + ((-1 * t : ℝ) : ℂ) * I with hw3def
  have w1im : w1.im = t := by simp [hw1def]
  have w2im : w2.im = -t := by simp [hw2def]
  have w3im : w3.im = -t := by simp [hw3def]
  have w1re : w1.re = 1 - s := by simp [hw1def]
  have w2re : w2.re = s' := by simp [hw2def]
  have w3re : w3.re = 1 - s := by simp [hw3def]
  have nw1 : ‖w1‖ ≤ (1 - s) + t := by
    have := Complex.norm_le_abs_re_add_abs_im w1
    rw [w1re, w1im, abs_of_pos hδa, abs_of_pos ht0] at this; exact this
  have nw2 : ‖w2‖ ≤ s' + t := by
    have := Complex.norm_le_abs_re_add_abs_im w2
    rw [w2re, w2im, abs_of_pos hs0', abs_neg, abs_of_pos ht0] at this; exact this
  have nw3 : ‖w3‖ ≤ (1 - s) + t := by
    have := Complex.norm_le_abs_re_add_abs_im w3
    rw [w3re, w3im, abs_of_pos hδa, abs_neg, abs_of_pos ht0] at this; exact this
  have w1ne : w1 ≠ 0 := by intro h; rw [h] at w1im; simp at w1im; linarith
  have w2ne : w2 ≠ 0 := by intro h; rw [h] at w2im; simp at w2im; linarith
  have w3ne : w3 ≠ 0 := by intro h; rw [h] at w3im; simp at w3im; linarith
  have z1eq : sidePt a v s (-t) = pt v d1 (La * ‖w1‖) (Complex.arg w1) := by
    rw [← pt_eq_mul]
    unfold sidePt
    simp only [hw1def, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_neg]
    linear_combination (-((1 - (s : ℂ)) + (t : ℂ) * I)) * hA
  have z2eq : sidePt v c s' (-t) = pt v d1 (Lc * ‖w2‖) (Δ + Complex.arg w2) := by
    rw [← pt_eq_mul_rot]
    unfold sidePt
    simp only [hw2def, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_neg]
    linear_combination (-((s' : ℂ) - (t : ℂ) * I)) * hC
  have z3eq : sidePt a v s t = pt v d1 (La * ‖w3‖) (Complex.arg w3 + 2 * Real.pi) := by
    rw [pt_add_two_pi, ← pt_eq_mul]
    unfold sidePt
    simp only [hw3def, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_neg]
    linear_combination (-((1 - (s : ℂ)) - (t : ℂ) * I)) * hA
  have ρ1 : 0 < La * ‖w1‖ ∧ La * ‖w1‖ < r := by
    refine ⟨mul_pos hLa (norm_pos_iff.2 w1ne), ?_⟩
    have := mul_le_mul_of_nonneg_left nw1 hLa.le
    have e : La * ((1 - s) + t) = La * (1 - s) + La * t := by ring
    linarith
  have ρ2 : 0 < Lc * ‖w2‖ ∧ Lc * ‖w2‖ < r := by
    refine ⟨mul_pos hLc (norm_pos_iff.2 w2ne), ?_⟩
    have := mul_le_mul_of_nonneg_left nw2 hLc.le
    have e : Lc * (s' + t) = Lc * s' + Lc * t := by ring
    linarith
  have ρ3 : 0 < La * ‖w3‖ ∧ La * ‖w3‖ < r := by
    refine ⟨mul_pos hLa (norm_pos_iff.2 w3ne), ?_⟩
    have := mul_le_mul_of_nonneg_left nw3 hLa.le
    have e : La * ((1 - s) + t) = La * (1 - s) + La * t := by ring
    linarith
  have ang1 := arg_pos_pi (w := w1) (by rw [w1im]; exact ht0)
  have ang2 : Complex.arg w2 < 0 := Complex.arg_neg_iff.2 (by rw [w2im]; linarith)
  have ang3 : Complex.arg w3 < 0 := Complex.arg_neg_iff.2 (by rw [w3im]; linarith)
  rw [abs_lt] at a1 a2 a3
  have v1 : wind p (sidePt a v s (-t)) = wind p (pt v d1 (r / 2) (Δ / 2)) := by
    rw [z1eq]; exact sec1 _ _ ρ1.1 ρ1.2 ang1.1 (by linarith)
  have v2 : wind p (sidePt v c s' (-t)) = wind p (pt v d1 (r / 2) (Δ / 2)) := by
    rw [z2eq]; exact sec1 _ _ ρ2.1 ρ2.2 (by linarith) (by linarith)
  have v3 : wind p (sidePt a v s t) = wind p (pt v d1 (r / 2) ((Δ + 2 * Real.pi) / 2)) := by
    rw [z3eq]; exact sec2 _ _ ρ3.1 ρ3.2 (by linarith) (by linarith)
  have hkk : k' = k := by rw [← hw2, v2, ← v1, hw1]
  refine ⟨hkk, fun z hz hzE => ?_⟩
  obtain ⟨ρ, θ, hρ, hρr, hθ0, hθ1, hθΔ, rfl⟩ := pt_cover hR hd1 hr hz hzE
  rcases lt_or_gt_of_ne hθΔ with h | h
  · left; rw [sec1 ρ θ hρ hρr hθ0 h, ← v1, hw1]
  · right; rw [sec2 ρ θ hρ hρr h hθ1, ← v3, hw3]

/-- **Vertex gluing.** -/
theorem vertex_good {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n) (i : Fin n) :
    ∃ k : ℤ, (∃ s : ℝ, 0 < s ∧ s < 1 ∧ Good p i s k) ∧ (∃ s' : ℝ, 0 < s' ∧ s' < 1 ∧ Good p (i + 1) s' k) ∧
      ∃ r > 0, ∀ z : ℂ, dist z (p (i + 1)) < r → z ∉ edgeSet p → wind p z = k ∨ wind p z = k + 1 := by
  obtain ⟨r, hr, Δ, hΔ0, hΔ1, hΔ, hR⟩ := tworays_vertex hs hinj hn i
  have hav : p i ≠ p (i + 1) := (nd hinj hn i).symm
  have hcv : p (i + 1 + 1) ≠ p (i + 1) := nd hinj hn (i + 1)
  have hLa : 0 < ‖p i - p (i + 1)‖ := norm_pos_iff.2 (sub_ne_zero.2 hav)
  have hLc : 0 < ‖p (i + 1 + 1) - p (i + 1)‖ := norm_pos_iff.2 (sub_ne_zero.2 hcv)
  set La := ‖p i - p (i + 1)‖ with hLadef
  set Lc := ‖p (i + 1 + 1) - p (i + 1)‖ with hLcdef
  set δa := min (1 / 2 : ℝ) (r / (4 * La)) with hδa
  set δc := min (1 / 2 : ℝ) (r / (4 * Lc)) with hδc
  have hδa0 : 0 < δa := lt_min (by norm_num) (by positivity)
  have hδc0 : 0 < δc := lt_min (by norm_num) (by positivity)
  have hδa1 : δa ≤ 1 / 2 := min_le_left _ _
  have hδc1 : δc ≤ 1 / 2 := min_le_left _ _
  have hδaL : La * δa ≤ r / 4 := by
    have h1 : δa ≤ r / (4 * La) := min_le_right _ _
    have := mul_le_mul_of_nonneg_left h1 hLa.le
    have e : La * (r / (4 * La)) = r / 4 := by field_simp
    linarith
  have hδcL : Lc * δc ≤ r / 4 := by
    have h1 : δc ≤ r / (4 * Lc) := min_le_right _ _
    have := mul_le_mul_of_nonneg_left h1 hLc.le
    have e : Lc * (r / (4 * Lc)) = r / 4 := by field_simp
    linarith
  obtain ⟨k, hk⟩ := good_exists hs hinj hn i (s := 1 - δa) (by linarith) (by linarith)
  obtain ⟨k', hk'⟩ := good_exists hs hinj hn (i + 1) (s := δc) hδc0 (by linarith)
  have key := vertex_abstract (p := p) (a := p i) (v := p (i + 1)) (c := p (i + 1 + 1)) (d1 := edir (p i) (p (i + 1)))
    hav hcv hr hΔ0 hΔ1 rfl hΔ hR (s := 1 - δa) (s' := δc) (by linarith) (by simpa using hδaL) hδc0 hδcL hk hk'
  obtain ⟨hkk, hball⟩ := key
  have hkk' : k' = k := by exact_mod_cast hkk
  subst hkk'
  exact ⟨k', ⟨1 - δa, by linarith, by linarith, hk⟩, ⟨δc, hδc0, by linarith, hk'⟩, r, hr, hball⟩

end Erdos634.Draft.LaczFormal.WN
