import Erdos634.Draft.BeesonThm11

/-!
# Beeson, "Triangle tiling III" (arXiv 1206.2229v4), Theorem 20, in the printed parametrisation

> Tile `(a,b,c)` with no common factor, `c ∣ a²` (so `3α + 2β = π`), `a < c`, `b = c − a²/c`;
> the isosceles triangle `ABC` with base angles `β` and area `N` times the tile area, where
> `N = M²(3 − s²)/(1 + s)²`, `s = a/c`; suppose `a + c ∣ M`.  Then `ABC` has an `N`-tiling.

**ALREADY DONE in the `(e,f)` form:** `Draft.WSeedG.beta_seed` (scale `f`, every member) and
`Draft.UniformThreshold.betaTilable_mul_self` (every multiple).  This file adds the printed form:
`M = (a+c) j` gives `N = j²(3c² − a²)`, and with `a = e f`, `c = f²`, `b = f² − e²` (forced by
`c ∣ a²`, `a < c` and primitivity: `a = e f g`, `c = f² g`, `g ∣ gcd(a,b,c) = 1`) the triangle is
`j` times the `beta_seed` triangle: legs `j c²`, base `j a (3c² − a²)/c`; count `j² f²(3f²−e²)`
(`WSeedG.beta_seed` then `Realizable.cut_scale` with ratio `j`).
Hypotheses witnessed: tile `(6,5,9)`, `j = 1`: `N = 207`, target `(81, 81, 138)` (the kernel-checked
207-tiling), `j = 2`: `N = 828`.  Credit Beeson (arXiv 1206.2229), Paliy (beta lift), Beeson-Rosu.
UNAUDITED.
-/

namespace Erdos634.BeesonThm20

open Erdos634.Geometry Erdos634.Draft.FDBBaseBetaE1 Erdos634.Realizable Erdos634.BeesonThm11

theorem param_of_dvd_sq (M K : ℕ) (hM : 0 < M) (hMK : M < K) (hKM : K ∣ M ^ 2) :
    ∃ e f g : ℕ, 1 ≤ e ∧ e < f ∧ 0 < g ∧ M = e * (f * g) ∧ K = f * (f * g) := by
  have hKpos : 0 < K := by omega
  obtain ⟨hh, e, f, hhpos, hcop, hMe, hKf⟩ := Nat.exists_coprime' (Nat.gcd_pos_of_pos_right M hKpos)
  subst hMe hKf
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at hKpos)
  have hfdiv : f ∣ e ^ 2 * hh := by
    have h2 : f * hh ∣ (e ^ 2 * hh) * hh := by
      have : (e * hh) ^ 2 = (e ^ 2 * hh) * hh := by ring
      rw [← this]; exact hKM
    exact Nat.dvd_of_mul_dvd_mul_right hhpos h2
  have hfh : f ∣ hh := (Nat.Coprime.pow_right 2 hcop.symm).dvd_of_dvd_mul_left hfdiv
  obtain ⟨g, rfl⟩ := hfh
  have hg : 0 < g := Nat.pos_of_ne_zero (by rintro rfl; simp at hhpos)
  have he : 1 ≤ e := Nat.pos_of_ne_zero (by rintro rfl; simp at hM)
  have hef : e < f := Nat.lt_of_mul_lt_mul_right (a := g) (by
    have : e * (f * g) < f * (f * g) := hMK
    nlinarith)
  exact ⟨e, f, g, he, hef, hg, rfl, rfl⟩

theorem thm20_efj (e f j n : ℕ) (he : 1 ≤ e) (hef : e < f) (hj : 0 < j)
    (hn : n = j * j * (f ^ 2 * (3 * f ^ 2 - e ^ 2))) :
    ∃ D : CongruentDissection n,
      HasSides D.target ((j : ℝ) * (f : ℝ) ^ 4) ((j : ℝ) * (f : ℝ) ^ 4)
        ((j : ℝ) * ((e : ℝ) * f * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) ∧
      HasSides D.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2) := by
  subst hn
  obtain ⟨D, hT, hM⟩ := Erdos634.Draft.WSeedG.beta_seed e f he hef
  obtain ⟨E, hEt, hEm⟩ := cut_scale (T := D.target) (t := D.model) ⟨D, rfl, rfl⟩ j hj
  refine ⟨E, ?_, ?_⟩
  · rw [hEt]; exact hasSides_scaleN' hT j hj
  · rw [hEm]; exact hM

/-- **Beeson, Theorem 20 (printed parametrisation), UNAUDITED.**  `M = (a+c) j`, `N = j²(3c²−a²)`. -/
theorem beeson_thm20 (a b c j : ℕ) (ha : 0 < a) (hac : a < c)
    (hcop : Nat.gcd a (Nat.gcd b c) = 1) (hdiv : c ∣ a ^ 2) (hb : b + a ^ 2 / c = c)
    (hj : 0 < j) :
    ∃ D : CongruentDissection (j ^ 2 * (3 * c ^ 2 - a ^ 2)),
      HasSides D.target ((j : ℝ) * (c : ℝ) ^ 2) ((j : ℝ) * (c : ℝ) ^ 2)
        ((j : ℝ) * a * (3 * (c : ℝ) ^ 2 - (a : ℝ) ^ 2) / c) ∧
      HasSides D.model (a : ℝ) (b : ℝ) (c : ℝ) := by
  obtain ⟨e, f, g, he, hef, hg, rfl, rfl⟩ := param_of_dvd_sq a c ha hac hdiv
  have hq : (e * (f * g)) ^ 2 / (f * (f * g)) = e ^ 2 * g := by
    rw [show (e * (f * g)) ^ 2 = (f * (f * g)) * (e ^ 2 * g) by ring]
    exact Nat.mul_div_cancel_left _ (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) hg))
  rw [hq] at hb
  have hgb : g ∣ b := by
    have h1 : g ∣ b + e ^ 2 * g := by rw [hb]; exact Dvd.intro_left (f * f) (by ring)
    exact (Nat.dvd_add_left (Dvd.intro_left _ rfl)).mp h1
  have hg1 : g = 1 := by
    have := Nat.dvd_gcd (Dvd.intro_left _ (by ring : e * f * g = e * (f * g)))
      (Nat.dvd_gcd hgb (Dvd.intro_left _ (by ring : f * f * g = f * (f * g))))
    rw [hcop] at this
    exact Nat.dvd_one.mp this
  subst hg1
  have hbr : (b : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have : (b : ℝ) + (e : ℝ) ^ 2 = (f : ℝ) ^ 2 := by exact_mod_cast (by nlinarith : b + e ^ 2 = f ^ 2)
    linarith
  have hle : e ^ 2 ≤ 3 * f ^ 2 := by nlinarith
  have hN : j ^ 2 * (3 * (f * (f * 1)) ^ 2 - (e * (f * 1)) ^ 2)
      = j * j * (f ^ 2 * (3 * f ^ 2 - e ^ 2)) := by
    rw [show 3 * (f * (f * 1)) ^ 2 = f ^ 2 * (3 * f ^ 2) by ring,
      show (e * (f * 1)) ^ 2 = f ^ 2 * e ^ 2 by ring, ← Nat.mul_sub]
    ring
  obtain ⟨D, hDt, hDm⟩ := thm20_efj e f j _ he hef hj hN
  refine ⟨D, ?_, ?_⟩
  · have hf0 : (f : ℝ) ≠ 0 := by exact_mod_cast (by omega : f ≠ 0)
    refine hs_congr hDt ?_ ?_ ?_
    · push_cast; ring
    · push_cast; ring
    · push_cast
      first | (field_simp; done) | (field_simp; ring)
  · refine hs_congr hDm ?_ ?_ ?_
    · push_cast; ring
    · rw [hbr]
    · push_cast; ring

/-- Witness: tile `(6,5,9)` (`e=2,f=3`), `j = 1`: `N = 207` tiles, target `(81,81,138)`. -/
theorem beeson_thm20_6_5_9 :
    ∃ D : CongruentDissection 207, HasSides D.target 81 81 138 ∧ HasSides D.model 6 5 9 := by
  obtain ⟨D, h1, h2⟩ := beeson_thm20 6 5 9 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨D, hs_congr h1 (by norm_num) (by norm_num) (by norm_num),
    hs_congr h2 (by norm_num) (by norm_num) (by norm_num)⟩

/-- Witness, `j = 2`: `828 = 4 · 207` tiles, target `(162,162,276)` (area ratio `4`). -/
theorem beeson_thm20_6_5_9_j2 :
    ∃ D : CongruentDissection 828, HasSides D.target 162 162 276 ∧ HasSides D.model 6 5 9 := by
  obtain ⟨D, h1, h2⟩ := beeson_thm20 6 5 9 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨D, hs_congr h1 (by norm_num) (by norm_num) (by norm_num),
    hs_congr h2 (by norm_num) (by norm_num) (by norm_num)⟩

end Erdos634.BeesonThm20
