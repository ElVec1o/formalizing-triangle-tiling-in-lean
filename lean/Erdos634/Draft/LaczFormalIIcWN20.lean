-- Draft/LaczFormalIIcWN20.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2/6.3, Lemma 6.2 (`IIcNoKites`), step (c) `u = v + N`:
-- discrete Hopf (Umlaufsatz) for simple polygons, part 1: angle increments `ang`, half-plane telescoping, bisector lemma, cell lemma.
-- No Jordan theorem, no ear removal: only the disjointness of non-adjacent edges is used (Hahn-Banach separation of two disjoint segments).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2/6.3), Beeson, Beeson-Zhang; the argument is the discrete form of Hopf's proof of the Umlaufsatz.
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Convex.Segment

open Complex

namespace Erdos634.Draft.LaczFormal.WN

/-- Signed angle from the vector `u` to the vector `v` (principal value of `arg (v / u)`). -/
noncomputable def ang (u v : ℂ) : ℝ := Complex.arg (v / u)

theorem arg_inv_of_re_pos {z : ℂ} (hz : 0 < z.re) : Complex.arg z⁻¹ = - Complex.arg z := by
  rw [Complex.arg_inv]
  have : Complex.arg z ≠ Real.pi := by
    rw [Ne, Complex.arg_eq_pi_iff]; intro h; linarith [h.1]
  simp [this]

theorem arg_div_sub_of_re_pos {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    Complex.arg (w / z) = Complex.arg w - Complex.arg z := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have hzi : z⁻¹ ≠ 0 := inv_ne_zero hz0
  have h1 : |Complex.arg z| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hz)
  have h2 : |Complex.arg w| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hw)
  rw [abs_lt] at h1 h2
  rw [div_eq_mul_inv]
  have := Complex.arg_mul hw0 hzi (by
    rw [arg_inv_of_re_pos hz]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, Real.pi_pos])
  rw [this, arg_inv_of_re_pos hz]; ring

/-- If both `x*u` and `y*u` have positive real part then the angle from `x` to `y` is a difference of two arguments. -/
theorem ang_eq_of_hp {u x y : ℂ} (hu : u ≠ 0) (hx : 0 < (x * u).re) (hy : 0 < (y * u).re) :
    ang x y = Complex.arg (y * u) - Complex.arg (x * u) := by
  unfold ang
  have : y / x = (y * u) / (x * u) := (mul_div_mul_right y x hu).symm
  rw [this]
  exact arg_div_sub_of_re_pos hx hy

/-- Bisector lemma: for `u, x` nonzero with `x / u` not a nonpositive real, `ang u (u+x) + ang (u+x) x = ang u x`. -/
theorem ang_bisect {u x : ℂ} (hu : u ≠ 0) (hx : x ≠ 0) (hr : ¬ ((x / u).im = 0 ∧ (x / u).re ≤ 0)) :
    ang u (u + x) + ang (u + x) x = ang u x := by
  set r : ℂ := x / u with hrdef
  have hr0 : r ≠ 0 := div_ne_zero hx hu
  have hxr : x = r * u := by rw [hrdef]; field_simp
  have h1r : 1 + r ≠ 0 := by
    intro h
    apply hr
    have : r = -1 := by linear_combination h
    rw [this]; simp
  have hux : u + x = (1 + r) * u := by rw [hxr]; ring
  have hux0 : u + x ≠ 0 := by rw [hux]; exact mul_ne_zero h1r hu
  have e1 : (u + x) / u = 1 + r := by rw [hux]; field_simp
  have e2 : x / (u + x) = r / (1 + r) := by rw [hux, hxr]; field_simp
  unfold ang
  rw [e1, e2]
  have him : (1 + r).im = r.im := by simp
  -- sign analysis
  have key : Complex.arg (r / (1 + r)) = Complex.arg r - Complex.arg (1 + r) := by
    have hinv : (1 + r)⁻¹ ≠ 0 := inv_ne_zero h1r
    have hnpi : Complex.arg (1 + r) ≠ Real.pi := by
      rw [Ne, Complex.arg_eq_pi_iff]
      intro h
      apply hr
      refine ⟨?_, ?_⟩
      · have := h.2; simpa using this
      · have := h.1; simp at this; show r.re ≤ 0; linarith
    rw [div_eq_mul_inv]
    have hai : Complex.arg (1 + r)⁻¹ = - Complex.arg (1 + r) := by
      rw [Complex.arg_inv]; simp [hnpi]
    have hcond : Complex.arg r + Complex.arg (1 + r)⁻¹ ∈ Set.Ioc (-Real.pi) Real.pi := by
      rw [hai]
      have a1 := Complex.neg_pi_lt_arg r
      have a2 := Complex.arg_le_pi r
      have b1 := Complex.neg_pi_lt_arg (1 + r)
      have b2 := Complex.arg_le_pi (1 + r)
      rcases lt_trichotomy r.im 0 with hlt | heq | hgt
      · have c1 : Complex.arg r < 0 := Complex.arg_neg_iff.2 hlt
        have c2 : Complex.arg (1 + r) < 0 := Complex.arg_neg_iff.2 (by rw [him]; exact hlt)
        constructor <;> linarith
      · have hre : 0 < r.re := by
          by_contra hh
          exact hr ⟨heq, not_lt.1 hh⟩
        have c1 : Complex.arg r = 0 := Complex.arg_eq_zero_iff.2 ⟨hre.le, heq⟩
        have c2 : Complex.arg (1 + r) = 0 := Complex.arg_eq_zero_iff.2 ⟨by simp; linarith, by rw [him]; exact heq⟩
        rw [c1, c2]; constructor <;> linarith [Real.pi_pos]
      · have c1 : 0 ≤ Complex.arg r := Complex.arg_nonneg_iff.2 hgt.le
        have c2 : 0 ≤ Complex.arg (1 + r) := Complex.arg_nonneg_iff.2 (by rw [him]; exact hgt.le)
        have c3 : Complex.arg r < Real.pi := Complex.arg_lt_pi_iff.2 (Or.inr hgt.ne')
        have c4 : Complex.arg (1 + r) < Real.pi := Complex.arg_lt_pi_iff.2 (Or.inr (by rw [him]; exact hgt.ne'))
        constructor <;> linarith
    rw [Complex.arg_mul hr0 hinv hcond, hai]; ring
  have e3 : Complex.arg (1 + r) + Complex.arg (r / (1 + r)) = Complex.arg r := by rw [key]; ring
  exact e3

/-- Cell lemma: for two disjoint segments `[a,a']`, `[b,b']` the four corner vectors lie in a common open half plane
(Hahn-Banach separation), i.e. there is `u` with positive real part of every corner times `u`. -/
theorem cell_halfplane (a a' b b' : ℂ) (h : Disjoint (segment ℝ a a') (segment ℝ b b')) :
    ∃ u : ℂ, 0 < ((b - a) * u).re ∧ 0 < ((b' - a) * u).re ∧ 0 < ((b' - a') * u).re ∧ 0 < ((b - a') * u).re := by
  have hc : ∀ x y : ℂ, IsCompact (segment ℝ x y) := by
    intro x y
    rw [segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  haveI : LocallyConvexSpace ℝ ℂ := NormedSpace.toLocallyConvexSpace' ℝ
  obtain ⟨f, s, t, hs, hst, ht⟩ := geometric_hahn_banach_compact_closed (convex_segment a a') (hc a a')
    (convex_segment b b') (hc b b').isClosed h
  have hdec : ∀ z : ℂ, f z = z.re * f 1 + z.im * f I := by
    intro z
    have : z = z.re • (1 : ℂ) + z.im • I := by apply Complex.ext <;> simp
    have h2 : f z = f (z.re • (1 : ℂ) + z.im • I) := congrArg f this
    rw [h2, map_add, map_smul, map_smul]; simp
  refine ⟨((f 1 : ℝ) : ℂ) - ((f I : ℝ) : ℂ) * I, ?_⟩
  have hre : ∀ z : ℂ, (z * (((f 1 : ℝ) : ℂ) - ((f I : ℝ) : ℂ) * I)).re = f z := by
    intro z; rw [hdec z]; simp
  have ha : f a < s := hs a (left_mem_segment ℝ a a')
  have ha' : f a' < s := hs a' (right_mem_segment ℝ a a')
  have hb : t < f b := ht b (left_mem_segment ℝ b b')
  have hb' : t < f b' := ht b' (right_mem_segment ℝ b b')
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hre, map_sub] <;> linarith

end Erdos634.Draft.LaczFormal.WN
