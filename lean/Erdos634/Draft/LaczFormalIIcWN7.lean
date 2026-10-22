-- Draft/LaczFormalIIcWN7.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2/6.3, Route B, item B5 (local-to-global Jordan dichotomy), part 1:
-- (a) the winding number is constant along a continuous path that avoids the polygon;
-- (b) LOCAL SECTOR LEMMA: at a point `v` where the polygon, inside `ball v r`, is exactly two rays from `v`
--     (directions `d1` and `d1 e^{i Delta}`), the winding number is constant on each of the two open sectors.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2/6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN4

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

/-- An integer-valued continuous function on `[0,1]` is constant. -/
theorem int_const_Icc (g : ℝ → ℝ) (hcont : ContinuousOn g (Set.Icc 0 1))
    (hint : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∃ k : ℤ, g τ = k) : g 0 = g 1 := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨k0, hk0⟩ := hint 0 h0
  obtain ⟨k1, hk1⟩ := hint 1 h1
  by_contra hne
  have hivt : Set.uIcc (g 0) (g 1) ⊆ g '' Set.uIcc 0 1 := by
    apply intermediate_value_uIcc
    rwa [Set.uIcc_of_le zero_le_one]
  rw [hk0, hk1] at hne hivt
  have hne' : k0 ≠ k1 := fun h => hne (by rw [h])
  rcases lt_or_gt_of_ne hne' with hlt | hgt
  · have hm : ((k0 : ℝ) + 1 / 2) ∈ Set.uIcc (k0 : ℝ) (k1 : ℝ) := by
      rw [Set.uIcc_of_le (by exact_mod_cast hlt.le)]
      have : (k0 : ℝ) + 1 ≤ k1 := by exact_mod_cast hlt
      constructor <;> linarith
    obtain ⟨τ, hτ, hgτ⟩ := hivt hm
    rw [Set.uIcc_of_le zero_le_one] at hτ
    obtain ⟨k, hk⟩ := hint τ hτ
    rw [hk] at hgτ
    have : ((k - k0 : ℤ) : ℝ) = 1 / 2 := by push_cast; linarith
    have h2 : (2 : ℝ) * ((k - k0 : ℤ) : ℝ) = 1 := by linarith
    have : (2 * (k - k0) : ℤ) = 1 := by exact_mod_cast h2
    omega
  · have hm : ((k1 : ℝ) + 1 / 2) ∈ Set.uIcc (k0 : ℝ) (k1 : ℝ) := by
      rw [Set.uIcc_of_ge (by exact_mod_cast hgt.le)]
      have : (k1 : ℝ) + 1 ≤ k0 := by exact_mod_cast hgt
      constructor <;> linarith
    obtain ⟨τ, hτ, hgτ⟩ := hivt hm
    rw [Set.uIcc_of_le zero_le_one] at hτ
    obtain ⟨k, hk⟩ := hint τ hτ
    rw [hk] at hgτ
    have : ((k - k1 : ℤ) : ℝ) = 1 / 2 := by push_cast; linarith
    have h2 : (2 : ℝ) * ((k - k1 : ℤ) : ℝ) = 1 := by linarith
    have : (2 * (k - k1) : ℤ) = 1 := by exact_mod_cast h2
    omega

/-- The winding number is constant along a continuous path `γ : [0,1] -> C` that avoids the polygon. -/
theorem wind_const_path (p : Fin n → ℂ) (γ : ℝ → ℂ) (hγ : Continuous γ)
    (h : ∀ τ ∈ Set.Icc (0 : ℝ) 1, γ τ ∉ edgeSet p) : wind p (γ 0) = wind p (γ 1) := by
  apply int_const_Icc (fun τ => wind p (γ τ))
  · intro τ hτ
    exact ((wind_continuousAt p _ (h τ hτ)).comp (hγ.continuousAt)).continuousWithinAt
  · intro τ hτ
    exact wind_int p _ (h τ hτ)

/-- `exp(φ I)` times a positive real equal to a nonnegative real forces `φ = 0` when `|φ| < 2 pi`. -/
theorem exp_real_pos {ρ τ φ : ℝ} (hρ : 0 < ρ) (hτ : 0 ≤ τ) (h1 : -(2 * Real.pi) < φ) (h2 : φ < 2 * Real.pi)
    (h : (ρ : ℂ) * Complex.exp (φ * I) = τ) : φ = 0 := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im] at hre
  rw [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im] at him
  simp at hre him
  have hs : Real.sin φ = 0 := by
    rcases him with h | h
    · exact absurd h hρ.ne'
    · exact h
  have hc : 0 ≤ Real.cos φ := by
    by_contra hneg
    push_neg at hneg
    nlinarith
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.1 hs
  have hpi := Real.pi_pos
  have hk1 : (k : ℝ) < 2 := by
    by_contra hh; push_neg at hh; rw [← hk] at h2; nlinarith
  have hk2 : (-2 : ℝ) < k := by
    by_contra hh; push_neg at hh; rw [← hk] at h1; nlinarith
  have hk1' : k < 2 := by exact_mod_cast hk1
  have hk2' : -2 < k := by exact_mod_cast hk2
  have : k = -1 ∨ k = 0 ∨ k = 1 := by omega
  rcases this with rfl | rfl | rfl
  · exfalso
    have hcos : Real.cos φ = -1 := by rw [← hk]; push_cast; simp
    linarith
  · rw [← hk]; simp
  · exfalso
    have hcos : Real.cos φ = -1 := by rw [← hk]; push_cast; simp
    linarith

/-- Point at polar coordinates `(ρ, θ)` around `v`, measured from the direction `d1`. -/
noncomputable def pt (v d1 : ℂ) (ρ θ : ℝ) : ℂ := v + (ρ : ℂ) * d1 * Complex.exp (θ * I)

theorem pt_dist {v d1 : ℂ} (hd : ‖d1‖ = 1) {ρ : ℝ} (hρ : 0 ≤ ρ) (θ : ℝ) : dist (pt v d1 ρ θ) v = ρ := by
  rw [dist_eq_norm]
  simp [pt, Complex.norm_exp_ofReal_mul_I, hd, abs_of_nonneg hρ]

/-- Sector hypothesis: inside `ball v r` the polygon is exactly the two rays `v + τ d1`, `v + τ d1 e^{i Δ}`, `τ ≥ 0`. -/
def TwoRays (p : Fin n → ℂ) (v d1 : ℂ) (Δ r : ℝ) : Prop :=
  ∀ y : ℂ, dist y v < r → (y ∈ edgeSet p ↔
    ((∃ τ : ℝ, 0 ≤ τ ∧ y = v + (τ : ℂ) * d1) ∨ (∃ τ : ℝ, 0 ≤ τ ∧ y = v + (τ : ℂ) * (d1 * Complex.exp (Δ * I)))))

theorem pt_off {p : Fin n → ℂ} {v d1 : ℂ} {Δ r : ℝ} (hR : TwoRays p v d1 Δ r) (hd : ‖d1‖ = 1)
    {ρ θ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hθ0 : 0 < θ) (hθ1 : θ < 2 * Real.pi) (hθΔ : θ ≠ Δ)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 2 * Real.pi) : pt v d1 ρ θ ∉ edgeSet p := by
  have hd0 : d1 ≠ 0 := by intro h; rw [h] at hd; simp at hd
  intro hmem
  have hdist : dist (pt v d1 ρ θ) v < r := by rw [pt_dist hd hρ.le]; exact hρr
  rcases (hR _ hdist).1 hmem with ⟨τ, hτ, he⟩ | ⟨τ, hτ, he⟩
  · have h1 : (ρ : ℂ) * Complex.exp (θ * I) = τ := by
      have : (ρ : ℂ) * d1 * Complex.exp (θ * I) = (τ : ℂ) * d1 := by
        unfold pt at he; linear_combination he
      have h2 : ((ρ : ℂ) * Complex.exp (θ * I)) * d1 = (τ : ℂ) * d1 := by linear_combination this
      exact mul_right_cancel₀ hd0 h2
    have := exp_real_pos hρ hτ (by linarith [Real.pi_pos]) hθ1 h1
    linarith
  · have h1 : (ρ : ℂ) * Complex.exp ((θ - Δ : ℝ) * I) = τ := by
      have : (ρ : ℂ) * d1 * Complex.exp (θ * I) = (τ : ℂ) * (d1 * Complex.exp (Δ * I)) := by
        unfold pt at he; linear_combination he
      have h3 : Complex.exp ((θ - Δ : ℝ) * I) * Complex.exp (Δ * I) = Complex.exp (θ * I) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      have hne : d1 * Complex.exp (Δ * I) ≠ 0 := mul_ne_zero hd0 (Complex.exp_ne_zero _)
      have h2 : ((ρ : ℂ) * Complex.exp ((θ - Δ : ℝ) * I)) * (d1 * Complex.exp (Δ * I)) = (τ : ℂ) * (d1 * Complex.exp (Δ * I)) := by
        rw [← this]; rw [← h3]; ring
      exact mul_right_cancel₀ hne h2
    have := exp_real_pos hρ hτ (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) h1
    exact hθΔ (by linarith)

/-- Every point of the ball off the polygon has polar coordinates in one of the two open sectors. -/
theorem pt_cover {p : Fin n → ℂ} {v d1 : ℂ} {Δ r : ℝ} (hR : TwoRays p v d1 Δ r) (hd : ‖d1‖ = 1) (hr : 0 < r)
    {z : ℂ} (hz : dist z v < r) (hzE : z ∉ edgeSet p) :
    ∃ ρ θ : ℝ, 0 < ρ ∧ ρ < r ∧ 0 < θ ∧ θ < 2 * Real.pi ∧ θ ≠ Δ ∧ z = pt v d1 ρ θ := by
  have hd0 : d1 ≠ 0 := by intro h; rw [h] at hd; simp at hd
  have hvE : v ∈ edgeSet p := by
    refine (hR v (by simpa using hr)).2 (Or.inl ⟨0, le_rfl, by simp⟩)
  have hzv : z ≠ v := fun h => hzE (h ▸ hvE)
  set w : ℂ := (z - v) / d1 with hw
  have hw0 : w ≠ 0 := div_ne_zero (sub_ne_zero.2 hzv) hd0
  have hwn : ‖w‖ = dist z v := by rw [hw, norm_div, hd, div_one, dist_eq_norm]
  set ρ : ℝ := ‖w‖ with hρ
  have hρ0 : 0 < ρ := norm_pos_iff.2 hw0
  set θ0 : ℝ := Complex.arg w with hθ0
  set θ : ℝ := if 0 ≤ θ0 then θ0 else θ0 + 2 * Real.pi with hθ
  have hwθ : w = (ρ : ℂ) * Complex.exp (θ * I) := by
    have h1 : w = (ρ : ℂ) * Complex.exp (θ0 * I) := by
      rw [hρ, hθ0]; exact (Complex.norm_mul_exp_arg_mul_I w).symm
    rw [h1]; unfold θ; split_ifs
    · rfl
    · congr 1
      rw [show ((θ0 + 2 * Real.pi : ℝ) : ℂ) * I = θ0 * I + 2 * Real.pi * I by push_cast; ring, Complex.exp_add,
        Complex.exp_two_pi_mul_I, mul_one]
  have hzpt : z = pt v d1 ρ θ := by
    unfold pt
    have : z = v + w * d1 := by rw [hw]; field_simp; ring_nf
    rw [this, hwθ]; ring
  have hpi := Real.pi_pos
  have hθ0le := Complex.neg_pi_lt_arg w
  have hθ1le := Complex.arg_le_pi w
  have hθ2 : θ < 2 * Real.pi := by
    unfold θ; split_ifs <;> linarith
  have hθne0 : θ ≠ 0 := by
    intro h0
    apply hzE
    refine (hR z hz).2 (Or.inl ⟨ρ, hρ0.le, ?_⟩)
    rw [hzpt]; unfold pt; rw [h0]; simp
  have hθΔ : θ ≠ Δ := by
    intro h0
    apply hzE
    refine (hR z hz).2 (Or.inr ⟨ρ, hρ0.le, ?_⟩)
    rw [hzpt]; unfold pt; rw [h0]; ring
  have hθpos : 0 < θ := by
    unfold θ at hθne0 ⊢; split_ifs at hθne0 ⊢ with h
    · exact lt_of_le_of_ne h (Ne.symm hθne0)
    · push_neg at h; linarith
  exact ⟨ρ, θ, hρ0, by rw [hwn]; exact hz, hθpos, hθ2, hθΔ, hzpt⟩

/-- **Sector constancy.**  Two points of the ball with polar coordinates joined by the stated path (radial move, then arc) have equal winding number. -/
theorem sector_const {p : Fin n → ℂ} {v d1 : ℂ} {Δ r : ℝ} (hR : TwoRays p v d1 Δ r) (hd : ‖d1‖ = 1)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 2 * Real.pi)
    {ρ ρ' θ θ' : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hρ' : 0 < ρ') (hρ'r : ρ' < r)
    (hθ : ∀ φ ∈ Set.uIcc θ θ', 0 < φ ∧ φ < 2 * Real.pi ∧ φ ≠ Δ) :
    wind p (pt v d1 ρ θ) = wind p (pt v d1 ρ' θ') := by
  have hθm : θ ∈ Set.uIcc θ θ' := Set.left_mem_uIcc
  have hθm' : θ' ∈ Set.uIcc θ θ' := Set.right_mem_uIcc
  -- radial move
  have step1 : wind p (pt v d1 ρ θ) = wind p (pt v d1 ρ' θ) := by
    have := wind_const_path p (fun τ => pt v d1 (ρ + τ * (ρ' - ρ)) θ) (by unfold pt; fun_prop) (by
      intro τ hτ
      obtain ⟨h0, h1⟩ := hτ
      have hm : 0 < ρ + τ * (ρ' - ρ) ∧ ρ + τ * (ρ' - ρ) < r := by
        have e : ρ + τ * (ρ' - ρ) = (1 - τ) * ρ + τ * ρ' := by ring
        have a1 := mul_le_mul_of_nonneg_left (min_le_left ρ ρ') (sub_nonneg.2 h1)
        have a2 := mul_le_mul_of_nonneg_left (min_le_right ρ ρ') h0
        have b1 := mul_le_mul_of_nonneg_left (le_max_left ρ ρ') (sub_nonneg.2 h1)
        have b2 := mul_le_mul_of_nonneg_left (le_max_right ρ ρ') h0
        have m0 : 0 < min ρ ρ' := lt_min hρ hρ'
        have m1 : max ρ ρ' < r := max_lt hρr hρ'r
        constructor <;> nlinarith
      exact pt_off hR hd hm.1 hm.2 (hθ θ hθm).1 (hθ θ hθm).2.1 (hθ θ hθm).2.2 hΔ0 hΔ1)
    simpa using this
  have step2 : wind p (pt v d1 ρ' θ) = wind p (pt v d1 ρ' θ') := by
    have := wind_const_path p (fun τ => pt v d1 ρ' (θ + τ * (θ' - θ))) (by unfold pt; fun_prop) (by
      intro τ hτ
      obtain ⟨h0, h1⟩ := hτ
      have hmem : θ + τ * (θ' - θ) ∈ Set.uIcc θ θ' := by
        rcases le_total θ θ' with h | h
        · rw [Set.uIcc_of_le h]; constructor <;> nlinarith
        · rw [Set.uIcc_of_ge h]; constructor <;> nlinarith
      have := hθ _ hmem
      exact pt_off hR hd hρ' hρ'r this.1 this.2.1 this.2.2 hΔ0 hΔ1)
    simpa using this
  rw [step1, step2]

end Erdos634.Draft.LaczFormal.WN
