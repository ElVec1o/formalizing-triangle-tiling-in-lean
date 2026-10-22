import Erdos634.Draft.BeesonT24Gen
import Erdos634.Draft.BeesonT14General

/-!
# Beeson Theorem 24 (arXiv 1206.2229v4): the construction in general parameters, integer statement

`beeson_thm24`: for a tile `(a,b,c)` with `a^2 + c b = c^2` and naturals `lam, rho, X, Y` with
`r = mu - c^2 rho > 0`, `h = rho c (a^2+b^2) - lam a^3 (a+c) > 0`, `h = X a + Y b`, `X >= 1`
(`mu = lam a b (a+c)`), the isosceles triangle with base `mu a` and legs `mu c` (base angles `alpha + beta`)
is tiled by `p^2 + q^2 + u^2 + t^2 + v^2 + 2 t r + 2 w h` copies of a triangle with sides `c, b, a`
(`p = a c rho, q = b c rho, t = a^2 rho, w = lam a (a+c) - c rho, u = c w, v = a w`).
Credit Beeson (arXiv 1206.2229), Beeson-Zhang, Zhang (arXiv 2512.22696), Laczkovich.  UNAUDITED.
-/

namespace Erdos634.BeesonT24General

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.ZhangPara Erdos634.ZhangSporadic Erdos634.BeesonT14Chart Erdos634.BeesonT14Abs
  Erdos634.BeesonT14Piece Erdos634.BeesonT14Gen Erdos634.BeesonT14General Erdos634.BeesonT24Gen

set_option maxHeartbeats 16000000 in
theorem beeson_thm24 (a b c lam rho X Y : ℕ) (ha : 0 < a) (hb : 0 < b) (hl : 0 < lam) (hρ : 0 < rho)
    (hX : 1 ≤ X) (h : a * a + c * b = c * c)
    (hr : c * c * rho < lam * a * b * (a + c))
    (hh : lam * a ^ 3 * (a + c) < rho * c * (a * a + b * b))
    (hxy : X * a + Y * b + lam * a ^ 3 * (a + c) = rho * c * (a * a + b * b)) :
    ∃ (T : Tri) (x0 y0 x1 y1 x2 y2 : ℝ) (_ : 0 < det3 x0 y0 x1 y1 x2 y2),
      dist (T.pts 0) (T.pts 1) ^ 2 = (c : ℝ) ^ 2 ∧ dist (T.pts 0) (T.pts 2) ^ 2 = (b : ℝ) ^ 2 ∧
      dist (T.pts 1) (T.pts 2) ^ 2 = (a : ℝ) ^ 2 ∧
      (x1 - x0) ^ 2 + (y1 - y0) ^ 2 = ((lam * a * b * (a + c) * a : ℕ) : ℝ) ^ 2 ∧
      (x2 - x0) ^ 2 + (y2 - y0) ^ 2 = ((lam * a * b * (a + c) * c : ℕ) : ℝ) ^ 2 ∧
      (x2 - x1) ^ 2 + (y2 - y1) ^ 2 = ((lam * a * b * (a + c) * c : ℕ) : ℝ) ^ 2 ∧
      Dis T (TriSet x0 y0 x1 y1 x2 y2)
        ((a * c * rho) ^ 2 + (b * c * rho) ^ 2 + (c * (lam * a * (a + c) - c * rho)) ^ 2 +
          (a * a * rho) ^ 2 + (a * (lam * a * (a + c) - c * rho)) ^ 2 +
          2 * (a * a * rho) * (lam * a * b * (a + c) - c * c * rho) +
          2 * (lam * a * (a + c) - c * rho) * (X * a + Y * b)) := by
  obtain ⟨g, s, t, hg, ht, hts, hc, hat, hb'⟩ := split_ca a b c ha hb h
  have hs : 0 < s := by omega
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have htsR : (t : ℝ) < s := by exact_mod_cast hts
  have hlamR : (0 : ℝ) < lam := by exact_mod_cast hl
  have hrhoR : (0 : ℝ) < rho := by exact_mod_cast hρ
  have hcR : (c : ℝ) = g * s ^ 2 := by exact_mod_cast hc
  have haR : (a : ℝ) = g * s * t := by exact_mod_cast hat
  have hbR : (b : ℝ) = g * (s ^ 2 - t ^ 2) := by
    have : (b : ℝ) + g * t ^ 2 = g * s ^ 2 := by exact_mod_cast hb'
    linarith
  have hspos : 0 < s ^ 2 - 2 * t ^ 2 → True := fun _ => trivial
  -- positivity of F3 (r > 0) and F4 (h > 0)
  have hrR : (c : ℝ) * c * rho < lam * a * b * (a + c) := by exact_mod_cast hr
  have hhR : (lam : ℝ) * a ^ 3 * (a + c) < rho * c * (a * a + b * b) := by exact_mod_cast hh
  rw [hcR, haR, hbR] at hrR hhR
  have hF3 : (0:ℝ) < g * lam * s ^ 3 * t + g * lam * s ^ 2 * t ^ 2 - g * lam * s * t ^ 3 - g * lam * t ^ 4 - rho * s ^ 2 := by
    have e : (lam : ℝ) * (g * s * t) * (g * (s ^ 2 - t ^ 2)) * (g * s * t + g * s ^ 2) - g * s ^ 2 * (g * s ^ 2) * rho =
        g ^ 2 * s ^ 2 * (g * lam * s ^ 3 * t + g * lam * s ^ 2 * t ^ 2 - g * lam * s * t ^ 3 - g * lam * t ^ 4 - rho * s ^ 2) := by ring
    have : (0:ℝ) < g ^ 2 * s ^ 2 * (g * lam * s ^ 3 * t + g * lam * s ^ 2 * t ^ 2 - g * lam * s * t ^ 3 - g * lam * t ^ 4 - rho * s ^ 2) := by
      rw [← e]; linarith
    exact (mul_pos_iff_of_pos_left (by positivity)).mp this
  have hF4 : (0:ℝ) < -g * lam * s ^ 3 * t ^ 3 - g * lam * s ^ 2 * t ^ 4 + rho * s ^ 4 - rho * s ^ 2 * t ^ 2 + rho * t ^ 4 := by
    have e : (rho : ℝ) * (g * s ^ 2) * ((g * s * t) * (g * s * t) + g * (s ^ 2 - t ^ 2) * (g * (s ^ 2 - t ^ 2))) -
        lam * (g * s * t) ^ 3 * (g * s * t + g * s ^ 2) =
        g ^ 3 * s ^ 2 * (-g * lam * s ^ 3 * t ^ 3 - g * lam * s ^ 2 * t ^ 4 + rho * s ^ 4 - rho * s ^ 2 * t ^ 2 + rho * t ^ 4) := by ring
    have : (0:ℝ) < g ^ 3 * s ^ 2 * (-g * lam * s ^ 3 * t ^ 3 - g * lam * s ^ 2 * t ^ 4 + rho * s ^ 4 - rho * s ^ 2 * t ^ 2 + rho * t ^ 4) := by
      rw [← e]; linarith
    exact (mul_pos_iff_of_pos_left (by positivity)).mp this
  have hpos4 : (0 : ℝ) < 4 * (s : ℝ) ^ 2 - (t : ℝ) ^ 2 := by nlinarith
  set rt0 : ℝ := Real.sqrt (4 * (s : ℝ) ^ 2 - (t : ℝ) ^ 2) with hrt0
  have hrt : 0 < rt0 := Real.sqrt_pos.mpr hpos4
  have hD : rt0 * rt0 = 4 * (s : ℝ) ^ 2 - (t : ℝ) ^ 2 := Real.mul_self_sqrt hpos4.le
  have P : Par24 (g : ℝ) (s : ℝ) (t : ℝ) (lam : ℝ) (rho : ℝ) rt0 :=
    ⟨hgR, hsR, htR, hlamR, hrhoR, htsR, hrt, hD, hF3, hF4⟩
  obtain ⟨hF1, hF2, _, _, hF6, hq2, hH0⟩ := atoms24 P
  have hF1' : 0 < (g : ℝ) * lam * t * (s + t) - rho := by nlinarith [hF1]
  have hbc : b < c := by
    have : (g : ℝ) * t ^ 2 > 0 := by positivity
    have h1 : (b : ℝ) < c := by rw [hcR, hbR]; nlinarith
    exact_mod_cast h1
  -- w and r as naturals
  obtain ⟨w, hw⟩ : ∃ w, w + c * rho = lam * a * (a + c) := by
    refine ⟨lam * a * (a + c) - c * rho, Nat.sub_add_cancel ?_⟩
    have hc0 : 0 < c := by omega
    have h1 : c * (c * rho) < c * (lam * a * (a + c)) := by
      have : lam * a * b * (a + c) ≤ lam * a * c * (a + c) := by
        apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_left; exact hbc.le
      nlinarith
    exact (Nat.lt_of_mul_lt_mul_left h1).le
  obtain ⟨r, hrr⟩ : ∃ r, r + c * c * rho = lam * a * b * (a + c) :=
    ⟨lam * a * b * (a + c) - c * c * rho, Nat.sub_add_cancel hr.le⟩
  have hwR : (w : ℝ) = g * s ^ 2 * (g * lam * t * (s + t) - rho) := by
    have : (w : ℝ) + c * rho = lam * a * (a + c) := by exact_mod_cast hw
    rw [hcR, haR] at this
    linarith
  have hrR' : (r : ℝ) = g ^ 2 * s ^ 2 * (g * lam * t * (s ^ 2 - t ^ 2) * (s + t) - s ^ 2 * rho) := by
    have : (r : ℝ) + c * c * rho = lam * a * b * (a + c) := by exact_mod_cast hrr
    rw [hcR, haR, hbR] at this
    linarith
  have hw0 : 0 < w := by
    have : (0 : ℝ) < w := by rw [hwR]; positivity
    exact_mod_cast this
  have hr0 : 0 < r := by
    have : (0 : ℝ) < r := by
      rw [hrR']
      have : (0:ℝ) < g * lam * t * (s ^ 2 - t ^ 2) * (s + t) - s ^ 2 * rho := by linarith [hF3]
      positivity
    exact_mod_cast this
  obtain ⟨m, hm⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  obtain ⟨n, hn⟩ : ∃ n, a * a * rho = n + 1 := ⟨a * a * rho - 1, by have := Nat.mul_pos (Nat.mul_pos ha ha) hρ; omega⟩
  obtain ⟨m1, hm1⟩ : ∃ m1, a * w = m1 + 1 := ⟨a * w - 1, by have := Nat.mul_pos ha hw0; omega⟩
  obtain ⟨x, hx⟩ : ∃ x, X = x + 1 := ⟨X - 1, by omega⟩
  have hpR : ((a * c * rho : ℕ) : ℝ) = g ^ 2 * s ^ 3 * t * rho := by push_cast; rw [haR, hcR]; ring
  have hqR : ((b * c * rho : ℕ) : ℝ) = g ^ 2 * s ^ 2 * (s ^ 2 - t ^ 2) * rho := by push_cast; rw [hbR, hcR]; ring
  have huR : ((c * w : ℕ) : ℝ) = g ^ 2 * s ^ 4 * (g * lam * t * (s + t) - rho) := by push_cast; rw [hcR, hwR]; ring
  have httR : ((n + 1 : ℕ) : ℝ) = g ^ 2 * s ^ 2 * t ^ 2 * rho := by
    rw [← hn]; push_cast; rw [haR]; ring
  have hvR : ((m1 + 1 : ℕ) : ℝ) = g ^ 2 * s ^ 3 * t * (g * lam * t * (s + t) - rho) := by
    rw [← hm1]; push_cast; rw [haR, hwR]; ring
  have hmR : ((m + 1 : ℕ) : ℝ) = g ^ 2 * s ^ 2 * (g * lam * t * (s ^ 2 - t ^ 2) * (s + t) - s ^ 2 * rho) := by
    rw [← hm]; exact hrR'
  have hxyR : (X : ℝ) * a + Y * b + lam * a ^ 3 * (a + c) = rho * c * (a * a + b * b) := by exact_mod_cast hxy
  have hxyR' : (X : ℝ) * (g * s * t) + Y * (g * (s ^ 2 - t ^ 2)) = g ^ 3 * s ^ 2 *
      (-g * lam * s ^ 3 * t ^ 3 - g * lam * s ^ 2 * t ^ 4 + rho * s ^ 4 - rho * s ^ 2 * t ^ 2 + rho * t ^ 4) := by
    rw [haR, hbR, hcR] at hxyR
    linear_combination hxyR
  -- the parallelogram GRLV and the core
  have hcore : ∃ n7 : ℕ, n7 = 2 * (a * w) * X + 2 * (b * w) * Y ∧
      Dis (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts (toPar P)).1)
        (CS (1 / (2 * (s : ℝ))) (rt0 / (2 * (s : ℝ)))
          (TriR 0 0 (TYx g s t lam rho) 0 (TBx g s t lam rho) (TBw g s t lam rho)))
        ((a * c * rho) * (a * c * rho) + (b * c * rho) * (b * c * rho) + (c * w) * (c * w) +
          (n + 1) * (n + 1) + (m1 + 1) * (m1 + 1) + 2 * (m + 1) * (n + 1) + n7) := by
    rcases Nat.eq_zero_or_pos Y with hY0 | hY0
    · subst hY0
      refine ⟨2 * (m1 + 1) * (x + 1), by rw [hm1, hx]; ring, ?_⟩
      have hxA : ((x + 1 : ℕ) : ℝ) * (g * s * t) = g ^ 3 * s ^ 2 *
          (-g * lam * s ^ 3 * t ^ 3 - g * lam * s ^ 2 * t ^ 4 + rho * s ^ 4 - rho * s ^ 2 * t ^ 2 + rho * t ^ 4) := by
        rw [hx] at hxyR'
        push_cast at hxyR' ⊢
        linarith
      exact core24 P (a * c * rho) (b * c * rho) (c * w) (m1 + 1) m n hpR hqR huR httR hvR hmR
        (grlv24_one P m1 x hvR hxA)
    · obtain ⟨y, hy⟩ : ∃ y, Y = y + 1 := ⟨Y - 1, by omega⟩
      obtain ⟨m2, hm2⟩ : ∃ m2, b * w = m2 + 1 := ⟨b * w - 1, by have := Nat.mul_pos hb hw0; omega⟩
      refine ⟨2 * (m1 + 1) * (x + 1) + 2 * (m2 + 1) * (y + 1), by rw [hm1, hm2, hx, hy], ?_⟩
      have hm2R : ((m2 + 1 : ℕ) : ℝ) = g ^ 2 * s ^ 2 * (s ^ 2 - t ^ 2) * (g * lam * t * (s + t) - rho) := by
        rw [← hm2]; push_cast; rw [hbR, hwR]; ring
      have hxyA : ((x + 1 : ℕ) : ℝ) * (g * s * t) + ((y + 1 : ℕ) : ℝ) * (g * (s ^ 2 - t ^ 2)) = g ^ 3 * s ^ 2 *
          (-g * lam * s ^ 3 * t ^ 3 - g * lam * s ^ 2 * t ^ 4 + rho * s ^ 4 - rho * s ^ 2 * t ^ 2 + rho * t ^ 4) := by
        rw [hx, hy] at hxyR'
        push_cast at hxyR' ⊢
        linarith
      exact core24 P (a * c * rho) (b * c * rho) (c * w) (m1 + 1) m n hpR hqR huR httR hvR hmR
        (grlv24_two P m1 m2 x y hvR hm2R hxyA)
  obtain ⟨n7, hn7, hDis⟩ := hcore
  have hlam2 : (2 * (s : ℝ)) ≠ 0 := by positivity
  have hα : 0 < 1 / (2 * (s : ℝ)) := by positivity
  have hβ : 0 < rt0 / (2 * (s : ℝ)) := by positivity
  have hdet : 0 < det3 (1 / (2 * (s : ℝ)) * 0) (rt0 / (2 * (s : ℝ)) * 0)
      (1 / (2 * (s : ℝ)) * TYx g s t lam rho) (rt0 / (2 * (s : ℝ)) * 0)
      (1 / (2 * (s : ℝ)) * TBx g s t lam rho) (rt0 / (2 * (s : ℝ)) * TBw g s t lam rho) := by
    have e : det3 (1 / (2 * (s : ℝ)) * 0) (rt0 / (2 * (s : ℝ)) * 0)
      (1 / (2 * (s : ℝ)) * TYx g s t lam rho) (rt0 / (2 * (s : ℝ)) * 0)
      (1 / (2 * (s : ℝ)) * TBx g s t lam rho) (rt0 / (2 * (s : ℝ)) * TBw g s t lam rho)
        = (1 / (2 * (s : ℝ))) * (rt0 / (2 * (s : ℝ))) *
          detR 0 0 (TYx g s t lam rho) 0 (TBx g s t lam rho) (TBw g s t lam rho) := by
      simp only [det3, detR]; ring
    rw [e]
    have := fact24_dBig P
    positivity
  refine ⟨tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts (toPar P)).1, _, _, _, _, _, _, hdet,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e0 : (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts (toPar P)).1).pts 0 = mkPt 0 0 := rfl
    have e1 : (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts (toPar P)).1).pts 1 =
      mkPt (g * s ^ 2) 0 := rfl
    rw [e0, e1, dist_sq_mkPt, hcR]; ring
  · have e0 : (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts (toPar P)).1).pts 0 = mkPt 0 0 := rfl
    have e2 : (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts (toPar P)).1).pts 2 =
      mkPt (xb g s t) (yb g s t rt0) := rfl
    have := (tile_facts (toPar P)).2.1
    unfold bbc at this
    rw [e0, e2, dist_sq_mkPt, hbR]; nlinarith
  · have e1 : (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts (toPar P)).1).pts 1 =
      mkPt (g * s ^ 2) 0 := rfl
    have e2 : (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts (toPar P)).1).pts 2 =
      mkPt (xb g s t) (yb g s t rt0) := rfl
    have := (tile_facts (toPar P)).2.2
    unfold aac at this
    rw [e1, e2, dist_sq_mkPt, haR]; nlinarith
  · rw [chart_dist _ _ _ hlam2 hD, div_eq_iff (by positivity)]
    push_cast
    rw [hcR, haR, hbR]; simp only [TYx]; ring
  · rw [chart_dist _ _ _ hlam2 hD, div_eq_iff (by positivity)]
    push_cast
    rw [hcR, haR, hbR]; simp only [TBx, TBw]; ring
  · rw [chart_dist _ _ _ hlam2 hD, div_eq_iff (by positivity)]
    push_cast
    rw [hcR, haR, hbR]; simp only [TBx, TBw, TYx]; ring
  · rw [TriSet_CS hα hβ]
    refine hDis.congr rfl ?_
    have e1 : lam * a * (a + c) - c * rho = w := by omega
    have e2 : lam * a * b * (a + c) - c * c * rho = r := by omega
    rw [e1, e2, hn7, ← hn, ← hm1, ← hm]
    ring

/-! ### Instances: tile `(2,3,4)`, `lam = 1`, `rho = 2` (`h = 56 = 28*2 + 0*3 = 25*2 + 2*3`) -/

theorem t24_2_3_4_y0 : ∃ (T : Tri) (x0 y0 x1 y1 x2 y2 : ℝ) (_ : 0 < det3 x0 y0 x1 y1 x2 y2),
    Dis T (TriSet x0 y0 x1 y1 x2 y2) 1728 := by
  obtain ⟨T, x0, y0, x1, y1, x2, y2, hd, _, _, _, _, _, _, hD⟩ :=
    beeson_thm24 2 3 4 1 2 28 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨T, x0, y0, x1, y1, x2, y2, hd, hD.congr rfl (by norm_num)⟩

theorem t24_2_3_4_y2 : ∃ (T : Tri) (x0 y0 x1 y1 x2 y2 : ℝ) (_ : 0 < det3 x0 y0 x1 y1 x2 y2),
    Dis T (TriSet x0 y0 x1 y1 x2 y2) 1728 := by
  obtain ⟨T, x0, y0, x1, y1, x2, y2, hd, _, _, _, _, _, _, hD⟩ :=
    beeson_thm24 2 3 4 1 2 25 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨T, x0, y0, x1, y1, x2, y2, hd, hD.congr rfl (by norm_num)⟩

end Erdos634.BeesonT24General

