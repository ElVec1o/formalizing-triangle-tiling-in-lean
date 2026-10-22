-- Draft/LaczFormalRG12RunRot.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2 (arrangement of the six tiles around a Gamma_kite vertex), pure plane geometry, S0c piece (ii), part 1:
-- PARTIAL cyclic angle sums.  For a chain of sectors `(u_j, v_j)` with `u_{j+1} ~ v_j` (positive multiple) the ray `u_m` is the ray `u_0` ROTATED by `S_m = sum_{j<m} wd(u_j, v_j)`
-- (`run_rotation`), so two rays of the fan are opposite exactly when the widths between them add up to `pi` mod `2 pi` (`par_rot_neg_iff`).  (`cycle_angle_sum` is the closed case.)
-- Tiling-free.  NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 4, 6.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalGraphFan

namespace Erdos634.Draft.LaczFormal.Graph

/-- Rotation of a plane vector by the angle `θ`. -/
noncomputable def rot (θ : ℝ) (z : V2) : V2 := (Real.cos θ * z.1 - Real.sin θ * z.2, Real.sin θ * z.1 + Real.cos θ * z.2)

theorem rot_ne_zero (θ : ℝ) {z : V2} (hz : z ≠ 0) : rot θ z ≠ 0 := by
  intro h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [rot, Prod.fst_zero, Prod.snd_zero] at h1 h2
  apply hz
  have hc := Real.cos_sq_add_sin_sq θ
  have e1 : z.1 = Real.cos θ * (Real.cos θ * z.1 - Real.sin θ * z.2) + Real.sin θ * (Real.sin θ * z.1 + Real.cos θ * z.2) := by linear_combination (-z.1) * hc
  have e2 : z.2 = - Real.sin θ * (Real.cos θ * z.1 - Real.sin θ * z.2) + Real.cos θ * (Real.sin θ * z.1 + Real.cos θ * z.2) := by linear_combination (-z.2) * hc
  exact Prod.ext (by show z.1 = 0; rw [e1, h1, h2]; ring) (by show z.2 = 0; rw [e2, h1, h2]; ring)

/-- **Rotation along a run.**  If `u_{j+1} ~ v_j` for all `j`, then `u_m ~ rot (sum_{j<m} wd(u_j,v_j)) u_0` (positive multiple). -/
theorem run_rotation (u v : ℕ → V2) (hu : ∀ j, u j ≠ 0) (hpar : ∀ j, Par (u (j + 1)) (v j)) (m : ℕ) :
    Par (u m) (rot (∑ j ∈ Finset.range m, wd (u j) (v j)) (u 0)) := by
  classical
  set U : ℕ → ℂ := fun j => ⟨(u j).1, (u j).2⟩ with hU
  set W : ℕ → ℂ := fun j => ⟨dt (u j) (v j), crs (u j) (v j)⟩ with hW
  choose c hc hcu using fun j => (hpar j).smul
  have hUne : ∀ j, U j ≠ 0 := by
    intro j h
    apply hu j
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp [hU] at h1 h2
    exact Prod.ext h1 h2
  have hWne : ∀ j, W j ≠ 0 := by
    intro j h0
    have h1 := congrArg Complex.re h0
    have h2 := congrArg Complex.im h0
    simp [hW] at h1 h2
    exact hu j (eq_zero_of_crs_dt (hpar j).ne_right h2 h1)
  have hstep : ∀ j, (starRingEnd ℂ) (U j) * U (j + 1) = (c j : ℂ) * W j := by
    intro j
    have h1 := congrArg Prod.fst (hcu j)
    have h2 := congrArg Prod.snd (hcu j)
    apply Complex.ext
    · simp [hU, hW, dt]
      rw [h1, h2]; ring
    · simp [hU, hW, crs]
      rw [h1, h2]; ring
  have hnn : ∀ j, (starRingEnd ℂ) (U j) * U j = ((‖U j‖ ^ 2 : ℝ) : ℂ) := by
    intro j; rw [Complex.conj_mul']; push_cast; rfl
  have hnpos : ∀ j, 0 < ‖U j‖ ^ 2 := fun j => by have := norm_pos_iff.mpr (hUne j); positivity
  have hW' : ∀ j, ((‖W j‖ : ℝ) : ℂ) * Complex.exp ((Complex.arg (W j) : ℂ) * Complex.I) = W j := fun j =>
    Complex.norm_mul_exp_arg_mul_I (W j)
  -- U (j+1) = (c j * ‖W j‖ / ‖U j‖^2) * U j * exp (i wd_j)
  have hnext : ∀ j, U (j + 1) = (((c j * ‖W j‖ / ‖U j‖ ^ 2 : ℝ)) : ℂ) * (U j * Complex.exp ((wd (u j) (v j) : ℂ) * Complex.I)) := by
    intro j
    have h1 := hstep j
    have h2 : U j * ((starRingEnd ℂ) (U j) * U (j + 1)) = U j * ((c j : ℂ) * W j) := by rw [h1]
    have h3 : (‖U j‖ ^ 2 : ℂ) * U (j + 1) = U j * ((c j : ℂ) * W j) := by
      have : U j * ((starRingEnd ℂ) (U j) * U (j + 1)) = ((starRingEnd ℂ) (U j) * U j) * U (j + 1) := by ring
      rw [this, hnn] at h2
      push_cast at h2
      exact h2
    have hne : (‖U j‖ ^ 2 : ℂ) ≠ 0 := by exact_mod_cast (hnpos j).ne'
    have hW2 : W j = ((‖W j‖ : ℝ) : ℂ) * Complex.exp ((wd (u j) (v j) : ℂ) * Complex.I) := (hW' j).symm
    calc U (j + 1) = ((‖U j‖ : ℂ) ^ 2)⁻¹ * ((‖U j‖ : ℂ) ^ 2 * U (j + 1)) := (inv_mul_cancel_left₀ hne _).symm
      _ = _ := by
        conv_lhs => rw [h3, hW2]
        push_cast; ring
  have key : ∀ m : ℕ, ∃ r : ℝ, 0 < r ∧ U m = (r : ℂ) * (U 0 * Complex.exp ((∑ j ∈ Finset.range m, wd (u j) (v j) : ℝ) * Complex.I)) := by
    intro m
    induction m with
    | zero => exact ⟨1, one_pos, by simp⟩
    | succ m ih =>
      obtain ⟨r, hr, hrU⟩ := ih
      refine ⟨(c m * ‖W m‖ / ‖U m‖ ^ 2) * r, ?_, ?_⟩
      · have := norm_pos_iff.mpr (hWne m)
        have := hc m
        have := hnpos m
        positivity
      · rw [hnext m, hrU, Finset.sum_range_succ]
        push_cast
        rw [add_mul, Complex.exp_add]
        ring
  obtain ⟨r, hr, hrU⟩ := key m
  set S : ℝ := ∑ j ∈ Finset.range m, wd (u j) (v j) with hS
  have hEre : (Complex.exp ((S : ℂ) * Complex.I)).re = Real.cos S := Complex.exp_ofReal_mul_I_re S
  have hEim : (Complex.exp ((S : ℂ) * Complex.I)).im = Real.sin S := Complex.exp_ofReal_mul_I_im S
  have h1 := congrArg Complex.re hrU
  have h2 := congrArg Complex.im hrU
  simp only [hU, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hEre, hEim] at h1 h2
  refine smul_par hr (rot_ne_zero _ (hu 0)) (Prod.ext ?_ ?_)
  · show (u m).1 = r * (Real.cos S * (u 0).1 - Real.sin S * (u 0).2)
    rw [h1]; ring
  · show (u m).2 = r * (Real.sin S * (u 0).1 + Real.cos S * (u 0).2)
    rw [h2]; ring

/-- Two rays `rot S y` and `y` point in OPPOSITE directions exactly when `S ≡ pi (mod 2 pi)`. -/
theorem par_rot_neg_iff (S : ℝ) {y : V2} (hy : y ≠ 0) :
    Par (rot S y) (-y.1, -y.2) ↔ ∃ z : ℤ, S = Real.pi + 2 * Real.pi * z := by
  have hn := nsq_pos hy
  have hcrs : crs (rot S y) (-y.1, -y.2) = Real.sin S * nsq y := by unfold crs rot nsq; ring
  have hdt : dt (rot S y) (-y.1, -y.2) = - (Real.cos S * nsq y) := by unfold dt rot nsq; ring
  unfold Par
  rw [hcrs, hdt]
  constructor
  · rintro ⟨h1, h2⟩
    have hs : Real.sin S = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h hn.ne'
    have hc : Real.cos S < 0 := by nlinarith
    have hc1 : Real.cos S = -1 := by
      have := Real.sin_sq_add_cos_sq S
      rw [hs] at this
      nlinarith
    have : Real.cos (S - Real.pi) = 1 := by rw [Real.cos_sub_pi, hc1]; norm_num
    obtain ⟨n, hn'⟩ := (Real.cos_eq_one_iff _).mp this
    exact ⟨n, by linarith⟩
  · rintro ⟨z, hz⟩
    have e : S = Real.pi + (z : ℝ) * (2 * Real.pi) := by rw [hz]; ring
    rw [e, Real.sin_add_int_mul_two_pi, Real.cos_add_int_mul_two_pi]
    simp
    exact hn

/-- NON-VACUITY: hypotheses of `run_rotation` hold for the constant chain `u = v = (1,0)` (so `S = 0`), and a genuine half-turn instance of `par_rot_neg_iff`. -/
theorem run_rotation_witness (m : ℕ) :
    Par (((1 : ℝ), (0 : ℝ)) : V2) (rot (∑ j ∈ Finset.range m, wd (((1 : ℝ), (0 : ℝ)) : V2) ((1, 0) : V2)) ((1, 0) : V2)) := by
  have h : Par (((1 : ℝ), (0 : ℝ)) : V2) ((1, 0) : V2) := ⟨by unfold crs; simp, by unfold dt; simp⟩
  exact run_rotation (fun _ => ((1 : ℝ), (0 : ℝ))) (fun _ => ((1 : ℝ), (0 : ℝ))) (fun _ => by simp) (fun _ => h) m

theorem par_rot_neg_witness : Par (rot Real.pi ((1, 0) : V2)) (-(1 : ℝ), -(0 : ℝ)) :=
  (par_rot_neg_iff Real.pi (y := ((1 : ℝ), (0 : ℝ))) (by simp)).2 ⟨0, by simp⟩

end Erdos634.Draft.LaczFormal.Graph

#print axioms Erdos634.Draft.LaczFormal.Graph.run_rotation
#print axioms Erdos634.Draft.LaczFormal.Graph.par_rot_neg_iff
#print axioms Erdos634.Draft.LaczFormal.Graph.run_rotation_witness
#print axioms Erdos634.Draft.LaczFormal.Graph.par_rot_neg_witness
