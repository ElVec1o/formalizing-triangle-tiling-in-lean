import Erdos634.Draft.LaczFormalL26Ident

/-!
# Laczkovich Theorem 2.4, fourth triple `(α, α+β, α+β)`, Fig. 5 (first picture): the chart dissection

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.4, Fig. 5), Beeson (arXiv 1206.2229,
Sect. 13.3, Theorem 23), Beeson-Zhang, Zhang.

`fourth_chart`: for a rational tile `Δ = (a, b, c)` with `a = a₀ c`, `b = (1 - a₀²) c` and `N(a₀) = a₀⁶ - 2a₀⁴ + 3a₀² - 1 > 0`
(equivalently `(b/c)³ < (1 - b/c)²`), the target triangle `T = L R P` of `LaczFormalL26Geo` is, in the chart
`(0; w₁, d₁)` (`|w₁| = |d₁| = c/(a₀ b₀)`, angle `α`), a union of rational triangles similar to `Δ`: five tiles and the
trapezoid `L R Q S` (Lemma 2.2 (ii), `trap_ii` for the swapped triangle).
-/

namespace Erdos634.LaczL26

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL21 Erdos634.LaczL24

theorem gram_smul (w d : Plane) (r s : ℝ) :
    inner ℝ (r • w) (s • d) = r * s * inner ℝ w d := by
  rw [real_inner_smul_left, real_inner_smul_right]; ring

theorem gram_smul_self (w : Plane) (r : ℝ) : inner ℝ (r • w) (r • w) = r ^ 2 * inner ℝ w w := by
  rw [real_inner_smul_left, real_inner_smul_right]; ring

theorem hyp_of_q (a0 : ℚ) (ha0 : 0 < a0) (ha1 : a0 < 1) (hN : 0 < a0 ^ 4 - (1 - a0 ^ 2) ^ 3) :
    Hyp (a0 : ℝ) := by
  have ha0r : (0 : ℝ) < a0 := by exact_mod_cast ha0
  have hb0q : (0 : ℚ) < 1 - a0 ^ 2 := by nlinarith
  have hb0r : (0 : ℝ) < 1 - (a0 : ℝ) ^ 2 := by exact_mod_cast hb0q
  have hNr : (0 : ℝ) < (a0 : ℝ) ^ 4 - (1 - (a0 : ℝ) ^ 2) ^ 3 := by exact_mod_cast hN
  exact Hyp.of_lt ha0r hb0r hNr

section tiles

variable (R : RTri) (a0 : ℚ) (ha0 : 0 < a0) (ha1 : a0 < 1)
  (hA : R.a = a0 * R.c) (hB : R.b = (1 - a0 ^ 2) * R.c)
  (hN : 0 < a0 ^ 4 - (1 - a0 ^ 2) ^ 3) (w1 d1 : Plane) (hdet : w1 0 * d1 1 - w1 1 * d1 0 ≠ 0)
  (hw : inner ℝ w1 w1 = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2)
  (hd : inner ℝ d1 d1 = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2)
  (hwd : inner ℝ w1 d1 = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2 * (2 - (a0 : ℝ) ^ 2) / 2)

include ha0 ha1 hA hB hN hdet hw hd hwd

theorem chart_A :
    ChartRSD R 0 w1 d1 hdet (triA (hyp_of_q a0 ha0 ha1 hN)).carrier := by
  have hb0q : (0 : ℚ) < 1 - a0 ^ 2 := by nlinarith
  have hane : (a0 : ℝ) ≠ 0 := by exact_mod_cast ha0.ne'
  have hbne : (1 - (a0 : ℝ) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < 1 - (a0 : ℝ) ^ 2 := by exact_mod_cast hb0q
    exact this.ne'
  exact chart_single (R := R) (A := 0) (w := w1) (d := d1) (h := hdet) (triA (hyp_of_q a0 ha0 ha1 hN))
    (tile_ok R a0 ha0 ha1 hA hB w1 d1 hdet hw hd hwd (sP (a0 : ℝ)) (tP (a0 : ℝ)) (sV (a0 : ℝ)) (tV (a0 : ℝ)) (sX (a0 : ℝ)) (tX (a0 : ℝ))
      (detne_A (hyp_of_q a0 ha0 ha1 hN)) 1 (by positivity) 1 (by push_cast; ring)
      (idA01 _ hane hbne) (idA12 _ hane hbne) (idA20 _ hane hbne))

theorem chart_B :
    ChartRSD R 0 w1 d1 hdet (triB (hyp_of_q a0 ha0 ha1 hN)).carrier := by
  have hb0q : (0 : ℚ) < 1 - a0 ^ 2 := by nlinarith
  have hane : (a0 : ℝ) ≠ 0 := by exact_mod_cast ha0.ne'
  have hbne : (1 - (a0 : ℝ) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < 1 - (a0 : ℝ) ^ 2 := by exact_mod_cast hb0q
    exact this.ne'
  exact chart_single (R := R) (A := 0) (w := w1) (d := d1) (h := hdet) (triB (hyp_of_q a0 ha0 ha1 hN))
    (tile_ok R a0 ha0 ha1 hA hB w1 d1 hdet hw hd hwd (sV (a0 : ℝ)) (tV (a0 : ℝ)) (sX (a0 : ℝ)) (tX (a0 : ℝ)) 0 (tZ (a0 : ℝ))
      (detne_B (hyp_of_q a0 ha0 ha1 hN)) (a0 : ℚ) (by positivity) (a0 : ℝ) (by push_cast; ring)
      (idB01 _ hane hbne) (idB12 _ hane hbne) (idB20 _ hane hbne))

theorem chart_C :
    ChartRSD R 0 w1 d1 hdet (triC (hyp_of_q a0 ha0 ha1 hN)).carrier := by
  have hb0q : (0 : ℚ) < 1 - a0 ^ 2 := by nlinarith
  have hane : (a0 : ℝ) ≠ 0 := by exact_mod_cast ha0.ne'
  have hbne : (1 - (a0 : ℝ) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < 1 - (a0 : ℝ) ^ 2 := by exact_mod_cast hb0q
    exact this.ne'
  exact chart_single (R := R) (A := 0) (w := w1) (d := d1) (h := hdet) (triC (hyp_of_q a0 ha0 ha1 hN))
    (tile_ok R a0 ha0 ha1 hA hB w1 d1 hdet hw hd hwd (sX (a0 : ℝ)) (tX (a0 : ℝ)) 0 0 0 (tZ (a0 : ℝ))
      (detne_C (hyp_of_q a0 ha0 ha1 hN)) (a0 ^ 2 / (1 - a0 ^ 2)) (by positivity) ((a0 : ℝ) ^ 2 / (1 - (a0 : ℝ) ^ 2)) (by push_cast; ring)
      (idC01 _ hane hbne) (idC12 _ hane hbne) (idC20 _ hane hbne))

theorem chart_D :
    ChartRSD R 0 w1 d1 hdet (triD (hyp_of_q a0 ha0 ha1 hN)).carrier := by
  have hb0q : (0 : ℚ) < 1 - a0 ^ 2 := by nlinarith
  have hane : (a0 : ℝ) ≠ 0 := by exact_mod_cast ha0.ne'
  have hbne : (1 - (a0 : ℝ) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < 1 - (a0 : ℝ) ^ 2 := by exact_mod_cast hb0q
    exact this.ne'
  exact chart_single (R := R) (A := 0) (w := w1) (d := d1) (h := hdet) (triD (hyp_of_q a0 ha0 ha1 hN))
    (tile_ok R a0 ha0 ha1 hA hB w1 d1 hdet hw hd hwd (sQ (a0 : ℝ)) (tQ (a0 : ℝ)) 0 (tZ (a0 : ℝ)) (sV (a0 : ℝ)) (tV (a0 : ℝ))
      (detne_D (hyp_of_q a0 ha0 ha1 hN)) (1 - a0 ^ 2) (by positivity) (1 - (a0 : ℝ) ^ 2) (by push_cast; ring)
      (idD01 _ hane hbne) (idD12 _ hane hbne) (idD20 _ hane hbne))

theorem chart_E :
    ChartRSD R 0 w1 d1 hdet (triE (hyp_of_q a0 ha0 ha1 hN)).carrier := by
  have hb0q : (0 : ℚ) < 1 - a0 ^ 2 := by nlinarith
  have hane : (a0 : ℝ) ≠ 0 := by exact_mod_cast ha0.ne'
  have hbne : (1 - (a0 : ℝ) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < 1 - (a0 : ℝ) ^ 2 := by exact_mod_cast hb0q
    exact this.ne'
  exact chart_single (R := R) (A := 0) (w := w1) (d := d1) (h := hdet) (triE (hyp_of_q a0 ha0 ha1 hN))
    (tile_ok R a0 ha0 ha1 hA hB w1 d1 hdet hw hd hwd 0 (tS (a0 : ℝ)) (sQ (a0 : ℝ)) (tQ (a0 : ℝ)) 0 (tZ (a0 : ℝ))
      (detne_E (hyp_of_q a0 ha0 ha1 hN)) ((1 - a0 ^ 2) / a0) (by positivity) ((1 - (a0 : ℝ) ^ 2) / (a0 : ℝ)) (by push_cast; ring)
      (idE01 _ hane hbne) (idE12 _ hane hbne) (idE20 _ hane hbne))

end tiles

end Erdos634.LaczL26
