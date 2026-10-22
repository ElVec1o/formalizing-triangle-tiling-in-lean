import Erdos634.Draft.LaczFormalL22Trap

/-!
# Laczkovich Lemma 2.2 (ii), first case (chart form): `trap_case1`

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Lemma 2.2 (ii), Fig. 1), Beeson,
Beeson-Zhang, Zhang.  See `LaczFormalL22Trap` for the setting.
-/

namespace Erdos634.LaczL22

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL21 Erdos634.Realizable

/-- **Lemma 2.2 (ii), first case.**  If `D c < W a` (`DC/BC > sin β / sin α`), the chart trapezoid
`trapSet τ`, `τ = 1 + D (b² - c²)/(W a c)`, is a union of finitely many rational triangles similar to `Δ`. -/
theorem trap_case1 (R : RTri) (A w d : Plane) (h : w 0 * d 1 - w 1 * d 0 ≠ 0) (W Dd : ℚ)
    (hW : 0 < W) (hD : 0 < Dd) (hw : inner ℝ w w = (W : ℝ) ^ 2) (hd : inner ℝ d d = (Dd : ℝ) ^ 2)
    (hwd : inner ℝ w d = (W : ℝ) * Dd * (R.cos1 : ℝ)) (hcase : Dd * R.c < W * R.a) :
    ChartRSD R A w d h (trapSet ((tTau R.a R.b R.c W Dd : ℚ) : ℝ)) := by
  obtain ⟨hτ, i2, i3, i4, i5, i6, i7⟩ := trap_alg1 R.a R.b R.c W Dd R.pa R.pb R.pc hW hD
  have ha := R.pa
  have hb := R.pb
  have hc := R.pc
  set f : ℚ := tF R.a R.c W Dd with hfdef
  set e : ℚ := tE R.a R.b R.c W Dd with hedef
  set τ : ℚ := tTau R.a R.b R.c W Dd with hτdef
  set k1 : ℚ := tK1 R.a Dd with hk1def
  set k2 : ℚ := tK2 R.a R.b R.c Dd with hk2def
  set g : ℚ := tG R.a R.b R.c W Dd with hgdef
  have hf1 : f < 1 := by
    have : 0 < Dd * R.c / (R.a * W) := by positivity
    rw [hfdef, tF]; linarith
  have hf0 : 0 < f := by
    have : Dd * R.c / (R.a * W) < 1 := (div_lt_one (by positivity)).mpr (by nlinarith)
    rw [hfdef, tF]; linarith
  have he : 0 < e := by rw [hedef, tE]; positivity
  have hk1 : 0 < k1 := by rw [hk1def, tK1]; positivity
  have hk2 : 0 < k2 := by rw [hk2def, tK2]; positivity
  have hgR : (g : ℝ) = (W : ℝ) * Dd * (R.cos1 : ℝ) := by
    rw [hgdef, tG, RTri.cos1]; push_cast; ring
  have hwd' : inner ℝ w d = (g : ℝ) := by rw [hgR]; exact hwd
  have hF1 : (f : ℝ) < 1 := by exact_mod_cast hf1
  have hF0 : (0 : ℝ) < f := by exact_mod_cast hf0
  have hE : (0 : ℝ) < e := by exact_mod_cast he
  have hτR : ((τ : ℚ) : ℝ) = (f : ℝ) + (e : ℝ) := by exact_mod_cast hτ
  rw [hτR, trap_cover (f : ℝ) (e : ℝ) hF0 hF1 hE]
  obtain ⟨d1, d2⟩ := trap_disj (f : ℝ) (e : ℝ) hF0 hF1 hE
  have cast_eq : ∀ {x y : ℚ}, x = y → (x : ℝ) = (y : ℝ) := fun h => by rw [h]
  refine chart_union (chart_union ?_ ?_ d1) ?_ d2
  · -- the parallelogram AFED, angle β at the corner: rotate the labels of Δ
    have hr := chart_rect (R := R.rot) A w d h W Dd hW hD hw hd
      (by rw [R.rot_cos0]; exact hwd) 0 0 f 1 hf0 one_pos
    simp only [Rat.cast_zero, zero_add, Rat.cast_one] at hr
    exact RatSimDiss.relabel (Δ := R.Δ) (finRotate 3) hr
  · -- triangle FBE
    refine chart_single _ ?_
    unfold triFBE
    have s0 : (Equiv.swap (0 : Fin 3) 1) 0 = 1 := by decide
    have s1 : (Equiv.swap (0 : Fin 3) 1) 1 = 0 := by decide
    have s2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
    refine chart_tile R A w d h W Dd hw hd g hwd' (f : ℝ) 0 1 0 (f : ℝ) 1 _ (Equiv.swap 0 1) k1 hk1 ?_ ?_ ?_
    · rw [s0, s1, dist_comm (R.Δ.pts 1) (R.Δ.pts 0), R.hc]
      have := congrArg (Rat.cast : ℚ → ℝ) i2; push_cast at this; linear_combination this
    · rw [s1, s2, dist_comm (R.Δ.pts 0) (R.Δ.pts 2), R.hb]
      have := congrArg (Rat.cast : ℚ → ℝ) i3; push_cast at this; linear_combination this
    · rw [s2, s0, dist_comm (R.Δ.pts 2) (R.Δ.pts 1), R.ha]
      have := congrArg (Rat.cast : ℚ → ℝ) i4; push_cast at this; linear_combination this
  · -- triangle EBC
    refine chart_single _ ?_
    unfold triEBC
    rw [hτ] at i6 i7
    refine chart_tile R A w d h W Dd hw hd g hwd' (f : ℝ) 1 1 0 ((f : ℝ) + e) 1 _ (Equiv.refl _) k2 hk2 ?_ ?_ ?_
    · simp only [Equiv.refl_apply, R.hc]
      have := congrArg (Rat.cast : ℚ → ℝ) i5; push_cast at this; linear_combination this
    · simp only [Equiv.refl_apply, R.ha]
      have := congrArg (Rat.cast : ℚ → ℝ) i6; push_cast at this; linear_combination this
    · simp only [Equiv.refl_apply, R.hb]
      have := congrArg (Rat.cast : ℚ → ℝ) i7; push_cast at this; linear_combination this

end Erdos634.LaczL22
