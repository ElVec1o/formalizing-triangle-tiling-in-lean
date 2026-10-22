import Erdos634.Draft.LaczFormalL26Thm
import Erdos634.Draft.LaczFormalL24Wit

/-!
# Beeson's Theorem 23 in its valid range, and witnesses for the fourth triple of Laczkovich's Theorem 2.4

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94), Beeson (arXiv 1206.2229v4, Sect. 13.3,
Theorem 23, Lemma 52), Beeson-Zhang, Zhang.

Beeson, Theorem 23 (as printed): *Suppose `3α + 2β = π`, and let `ABC` be an isosceles triangle with base angles `α + β`.
Suppose also that `b/c < 0.5698`, or equivalently `s > 0.656`.  Then for some `N` there is an `N`-tiling of a triangle
similar to `ABC` by the tile `(α, β, γ)`, `γ = 2α + β`.*  Beeson's proof is the Laczkovich construction (his Fig. 24, the
first picture of Laczkovich's Fig. 5), valid exactly when `b/c < x₀`, the real root `x₀ ≈ 0.56984` of `x³ = (1-x)²`
(Beeson, Lemma 52).

Relation with the project's parameter `t = sin(α/2)`, `a₀ = a/c = 2t`, `b/c = 1 - a₀²`: with `N(a₀) = a₀⁴ - (1-a₀²)³
= a₀⁶ - 2a₀⁴ + 3a₀² - 1 = 64t⁶ - 32t⁴ + 12t² - 1` the condition `N > 0` is *the same condition* as `x³ < (1-x)²`,
`x = b/c` (`beeson_N_eq`), i.e. `b/c < x₀` (`t > 0.32793...`).  Beeson's printed `0.5698` is a truncation of `x₀` slightly
BELOW `x₀`, so `b/c < 0.5698` is a (strictly stronger) sufficient hypothesis (`beeson_N_pos`); likewise `s > 0.656` where
`s = a₀`: `0.656² = 0.430336` gives `b/c < 0.569664`.  The theorem below is therefore the part of Theorem 23 covered by the
construction, as printed; the complementary range is Beeson's own 2018 method (not formalized here).
-/

namespace Erdos634.LaczL26

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL21 Erdos634.LaczL24 Erdos634.Realizable

theorem beeson_N_eq (a0 t : ℝ) (ht : a0 = 2 * t) :
    a0 ^ 4 - (1 - a0 ^ 2) ^ 3 = a0 ^ 6 - 2 * a0 ^ 4 + 3 * a0 ^ 2 - 1 ∧
    a0 ^ 4 - (1 - a0 ^ 2) ^ 3 = 64 * t ^ 6 - 32 * t ^ 4 + 12 * t ^ 2 - 1 ∧
    a0 ^ 4 - (1 - a0 ^ 2) ^ 3 = (1 - (1 - a0 ^ 2)) ^ 2 - (1 - a0 ^ 2) ^ 3 := by
  subst ht
  refine ⟨by ring, by ring, by ring⟩

/-- `x < 0.5698` (`x = b/c`) implies `x³ < (1-x)²`. -/
theorem beeson_N_pos (x : ℚ) (h0 : 0 < x) (h1 : x < 5698 / 10000) : 0 < (1 - x) ^ 2 - x ^ 3 := by
  have hc : (0 : ℚ) < 5698 / 10000 - x := by linarith
  have h2 : 0 < 2 - (1 - 5698 / 10000) * (x + 5698 / 10000) := by nlinarith
  have hg : (0 : ℚ) < 1 - 2 * (5698 / 10000) + (1 - 5698 / 10000) * (5698 / 10000) ^ 2 := by norm_num
  nlinarith [mul_pos hc h2, mul_pos (mul_pos h0 h0) hc]

/-- **Beeson's Theorem 23 (as printed), the part covered by the Laczkovich construction.**  `R` is a rational tile
`(a, b, c)` (sides opposite `α, β, γ`) with `3α + 2β = π` in the form of Beeson's Lemma 52 (`b = c - a²/c`), and
`b/c < 0.5698`.  Then a triangle similar to the isosceles triangle with base angles `α + β` (apex `α`) is the union of
finitely many congruent triangles similar to the tile (an `M`-tiling of it by tiles `scaleTri (1/q) Δ`). -/
theorem beeson_thm23_valid (R : RTri) (hrel : R.b * R.c = R.c ^ 2 - R.a ^ 2)
    (hx : R.b / R.c < 5698 / 10000) :
    ∃ (T : Tri) (q : ℕ) (hq : 0 < q) (M : ℕ)
      (C : Erdos634.RegionDissection.CongruentRegionDissection M),
      C.region = T.carrier ∧
      C.model = scaleTri (1 / (q : ℝ)) (one_div_pos.mpr (Nat.cast_pos.mpr hq)).ne' R.Δ ∧
      dist (T.pts 2) (T.pts 0) = dist (T.pts 2) (T.pts 1) ∧
      cornerAngle (T.pts 0) (T.pts 2) (T.pts 1)
        = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) := by
  have ha := R.pa
  have hb := R.pb
  have hc := R.pc
  have hA : R.a = (R.a / R.c) * R.c := by field_simp
  have hB : R.b = (1 - (R.a / R.c) ^ 2) * R.c := by
    field_simp
    nlinarith [hrel]
  have ha0 : 0 < R.a / R.c := by positivity
  have hxe : R.b / R.c = 1 - (R.a / R.c) ^ 2 := by
    rw [hB]; field_simp
  have ha1 : R.a / R.c < 1 := by
    have : (R.a / R.c) ^ 2 < 1 := by
      have : 0 < R.b / R.c := by positivity
      linarith
    nlinarith
  have hN : 0 < (R.a / R.c) ^ 4 - (1 - (R.a / R.c) ^ 2) ^ 3 := by
    have h := beeson_N_pos (R.b / R.c) (by positivity) hx
    rw [hxe] at h
    nlinarith [h]
  exact thm24_fourth R (R.a / R.c) ha0 ha1 hA hB hN

/-- The same with Beeson's other printed form of the hypothesis, `s > 0.656` (`s = a/c`). -/
theorem beeson_thm23_valid_s (R : RTri) (hrel : R.b * R.c = R.c ^ 2 - R.a ^ 2)
    (hs : 656 / 1000 < R.a / R.c) :
    ∃ (T : Tri) (q : ℕ) (hq : 0 < q) (M : ℕ)
      (C : Erdos634.RegionDissection.CongruentRegionDissection M),
      C.region = T.carrier ∧
      C.model = scaleTri (1 / (q : ℝ)) (one_div_pos.mpr (Nat.cast_pos.mpr hq)).ne' R.Δ ∧
      dist (T.pts 2) (T.pts 0) = dist (T.pts 2) (T.pts 1) ∧
      cornerAngle (T.pts 0) (T.pts 2) (T.pts 1)
        = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) := by
  have ha := R.pa
  have hb := R.pb
  have hc := R.pc
  refine beeson_thm23_valid R hrel ?_
  have hxe : R.b / R.c = 1 - (R.a / R.c) ^ 2 := by
    have : R.b = (1 - (R.a / R.c) ^ 2) * R.c := by field_simp; nlinarith [hrel]
    rw [this]; field_simp
  rw [hxe]
  nlinarith [hs]

/-! ### Witnesses -/

/-- `(12, 7, 16)` (`a₀ = 3/4`, `b/c = 7/16 = 0.4375 < 0.5698`) satisfies every hypothesis of `thm24_fourth`. -/
theorem wit_thm24_fourth_12716 :
    ∃ (T : Tri) (q : ℕ) (hq : 0 < q) (M : ℕ)
      (C : Erdos634.RegionDissection.CongruentRegionDissection M),
      C.region = T.carrier ∧
      C.model = scaleTri (1 / (q : ℝ)) (one_div_pos.mpr (Nat.cast_pos.mpr hq)).ne' R12716.Δ ∧
      dist (T.pts 2) (T.pts 0) = dist (T.pts 2) (T.pts 1) ∧
      cornerAngle (T.pts 0) (T.pts 2) (T.pts 1)
        = cornerAngle (R12716.Δ.pts 1) (R12716.Δ.pts 0) (R12716.Δ.pts 2) :=
  thm24_fourth R12716 (3 / 4) (by norm_num) (by norm_num) (by simp [R12716]; norm_num)
    (by simp [R12716]; norm_num) (by norm_num)

/-- The same through Beeson's Theorem 23 form (`b/c = 7/16 < 0.5698`). -/
theorem wit_beeson_thm23_12716 :
    ∃ (T : Tri) (q : ℕ) (hq : 0 < q) (M : ℕ)
      (C : Erdos634.RegionDissection.CongruentRegionDissection M),
      C.region = T.carrier ∧
      C.model = scaleTri (1 / (q : ℝ)) (one_div_pos.mpr (Nat.cast_pos.mpr hq)).ne' R12716.Δ ∧
      dist (T.pts 2) (T.pts 0) = dist (T.pts 2) (T.pts 1) ∧
      cornerAngle (T.pts 0) (T.pts 2) (T.pts 1)
        = cornerAngle (R12716.Δ.pts 1) (R12716.Δ.pts 0) (R12716.Δ.pts 2) :=
  beeson_thm23_valid R12716 (by simp [R12716]; norm_num) (by simp [R12716]; norm_num)

/-- Negative control: the project's tile `(2, 3, 4)` (`a₀ = 1/2`, `b/c = 3/4 > 0.5698`) is OUTSIDE the range: `N < 0`,
so `thm24_fourth` does not apply (the pictured pieces leave the triangle). -/
theorem control_234_out_of_range : ¬ (0 < (1 / 2 : ℚ) ^ 4 - (1 - (1 / 2 : ℚ) ^ 2) ^ 3) := by norm_num

#print axioms thm24_fourth
#print axioms beeson_thm23_valid
#print axioms beeson_thm23_valid_s
#print axioms wit_thm24_fourth_12716
#print axioms wit_beeson_thm23_12716

end Erdos634.LaczL26
