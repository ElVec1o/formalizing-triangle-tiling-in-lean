import Erdos634.Draft.BeesonT14Gen

/-!
# Beeson Theorem 14 (arXiv 1206.2229v4, Fig. 17): general statement in integers

`split_ca`: every integer tile with `a^2 + c b = c^2` is `(g s t, g (s^2 - t^2), g s^2)`.
`beeson_thm14`: the triangle with sides `j c^2`, `j b (b + 2 c)`, `j c (b + c)` is tiled by
`3 (j c)^2 + (j b)^2 + (j a)^2 + 2 r (j a)` copies of the tile `(a,b,c)` whenever `(j a + r) a = j c b`, `r > 0`.
Credit Beeson (arXiv 1206.2229), Beeson-Zhang, Zhang (arXiv 2512.22696), Laczkovich.  UNAUDITED.
-/

namespace Erdos634.BeesonT14General

theorem split_ca (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (h : a * a + c * b = c * c) :
    ∃ g s t : ℕ, 0 < g ∧ 0 < t ∧ t < s ∧ c = g * s ^ 2 ∧ a = g * s * t ∧ b + g * t ^ 2 = g * s ^ 2 := by
  have hc : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0; simp at h; omega
    · exact h0
  have hbc : b < c := by
    by_contra hcb
    push_neg at hcb
    nlinarith [Nat.mul_le_mul_left c hcb, Nat.mul_pos ha ha]
  obtain ⟨d, rfl⟩ : ∃ d, c = b + d := ⟨c - b, by omega⟩
  have hd : 0 < d := by omega
  have had : a * a = (b + d) * d := by nlinarith
  obtain ⟨c', d', hcop, hc', hd'⟩ := Nat.exists_coprime (b + d) d
  set G := Nat.gcd (b + d) d with hG
  have hGpos : 0 < G := Nat.gcd_pos_of_pos_right _ hd
  have hGG : G * G ∣ a * a := by
    refine ⟨c' * d', ?_⟩
    rw [had]; rw [hc', hd']; ring
  have hGa : G ∣ a := by
    have : G ^ 2 ∣ a ^ 2 := by simpa [pow_two] using hGG
    exact (Nat.pow_dvd_pow_iff (by norm_num)).mp this
  obtain ⟨a', ha'⟩ := hGa
  have hcd : a' * a' = c' * d' := by
    have : G * G * (a' * a') = G * G * (c' * d') := by
      calc G * G * (a' * a') = a * a := by rw [ha']; ring
        _ = (b + d) * d := had
        _ = G * G * (c' * d') := by rw [hc', hd']; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  -- c' = s^2, d' = t^2
  have hc'pos : 0 < c' := by
    rcases Nat.eq_zero_or_pos c' with h0 | h0
    · rw [h0] at hc'; omega
    · exact h0
  have hd'pos : 0 < d' := by
    rcases Nat.eq_zero_or_pos d' with h0 | h0
    · rw [h0] at hd'; omega
    · exact h0
  have hcopZ : Int.gcd (c' : ℤ) (d' : ℤ) = 1 := by
    simpa [Int.gcd_natCast_natCast] using hcop
  have hcdsq : c' * d' = a' ^ 2 := by rw [pow_two]; exact hcd.symm
  have hdcsq : d' * c' = a' ^ 2 := by rw [mul_comm]; exact hcdsq
  obtain ⟨s0, hs0⟩ := Int.sq_of_gcd_eq_one hcopZ (c := (a' : ℤ)) (by exact_mod_cast hcdsq)
  obtain ⟨t0, ht0⟩ := Int.sq_of_gcd_eq_one (by rw [Int.gcd_comm]; exact hcopZ) (c := (a' : ℤ))
    (by exact_mod_cast hdcsq)
  have hs : c' = s0.natAbs ^ 2 := by
    rcases hs0 with h1 | h1
    · have : (c' : ℤ) = (s0.natAbs : ℤ) ^ 2 := by rw [h1]; simp
      exact_mod_cast this
    · exfalso
      have : (0 : ℤ) < c' := by exact_mod_cast hc'pos
      nlinarith [sq_nonneg s0]
  have ht : d' = t0.natAbs ^ 2 := by
    rcases ht0 with h1 | h1
    · have : (d' : ℤ) = (t0.natAbs : ℤ) ^ 2 := by rw [h1]; simp
      exact_mod_cast this
    · exfalso
      have : (0 : ℤ) < d' := by exact_mod_cast hd'pos
      nlinarith [sq_nonneg t0]
  set s := s0.natAbs
  set t := t0.natAbs
  have hat : a' = s * t := by
    have : a' * a' = (s * t) * (s * t) := by rw [hcd, hs, ht]; ring
    exact Nat.mul_self_inj.mp this
  have hspos : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · rw [h0] at hs; simp at hs; omega
    · exact h0
  have htpos : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · rw [h0] at ht; simp at ht; omega
    · exact h0
  have hcnat : b + d = G * s ^ 2 := by rw [hc', hs]; ring
  have hdnat : d = G * t ^ 2 := by rw [hd', ht]; ring
  refine ⟨G, s, t, hGpos, htpos, ?_, hcnat, ?_, ?_⟩
  · -- t < s from b > 0
    by_contra hst
    push_neg at hst
    have : G * s ^ 2 ≤ G * t ^ 2 := Nat.mul_le_mul_left G (Nat.pow_le_pow_left hst 2)
    omega
  · rw [ha', hat]; ring
  · omega

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.ZhangPara Erdos634.ZhangSporadic Erdos634.BeesonT14Chart Erdos634.BeesonT14Abs
  Erdos634.BeesonT14Piece Erdos634.BeesonT14Gen

theorem chart_dist (lam rt0 D0 : ℝ) (hlam : lam ≠ 0) (hD : rt0 * rt0 = D0) (X0 W0 X1 W1 : ℝ) :
    (1 / lam * X1 - 1 / lam * X0) ^ 2 + (rt0 / lam * W1 - rt0 / lam * W0) ^ 2 =
      ((X1 - X0) ^ 2 + D0 * (W1 - W0) ^ 2) / lam ^ 2 := by
  rw [← hD]; field_simp

set_option maxHeartbeats 4000000 in
/-- **Beeson Theorem 14, general (UNAUDITED).**  If `a^2 + c b = c^2` (the tile `(a,b,c)` has `3 alpha + 2 beta = pi`),
`(j a + r) a = j c b` and `r > 0`, then the triangle with sides `j c^2`, `j b (b + 2 c)`, `j c (b + c)`
(angles `2 alpha, alpha, 2 beta`) is tiled by `3 (j c)^2 + (j b)^2 + (j a)^2 + 2 r (j a) = j^2 (b+c)(b+2c)`
copies of a triangle with sides `c, b, a`. -/
theorem beeson_thm14 (a b c j r : ℕ) (ha : 0 < a) (hb : 0 < b) (hj : 0 < j) (hr0 : 0 < r)
    (h : a * a + c * b = c * c) (hr : (j * a + r) * a = j * c * b) :
    ∃ (T : Tri) (x0 y0 x1 y1 x2 y2 : ℝ) (_ : 0 < det3 x0 y0 x1 y1 x2 y2),
      dist (T.pts 0) (T.pts 1) ^ 2 = (c : ℝ) ^ 2 ∧ dist (T.pts 0) (T.pts 2) ^ 2 = (b : ℝ) ^ 2 ∧
      dist (T.pts 1) (T.pts 2) ^ 2 = (a : ℝ) ^ 2 ∧
      (x1 - x0) ^ 2 + (y1 - y0) ^ 2 = ((j * c ^ 2 : ℕ) : ℝ) ^ 2 ∧
      (x2 - x0) ^ 2 + (y2 - y0) ^ 2 = ((j * b * (b + 2 * c) : ℕ) : ℝ) ^ 2 ∧
      (x2 - x1) ^ 2 + (y2 - y1) ^ 2 = ((j * c * (b + c) : ℕ) : ℝ) ^ 2 ∧
      Dis T (TriSet x0 y0 x1 y1 x2 y2) (3 * (j * c) ^ 2 + (j * b) ^ 2 + (j * a) ^ 2 + 2 * r * (j * a)) := by
  obtain ⟨g, s, t, hg, ht, hts, hc, hat, hb'⟩ := split_ca a b c ha hb h
  have hs : 0 < s := by omega
  -- c < 2 b
  have hq : 2 * t ^ 2 < s ^ 2 := by
    have h1 : j * (a * a) < j * (c * b) := by
      have : (j * a) * a < (j * a + r) * a := by nlinarith
      nlinarith
    have h2 : a * a < c * b := Nat.lt_of_mul_lt_mul_left h1
    have h3 : c < 2 * b := by
      have : c * c < c * (2 * b) := by nlinarith
      exact Nat.lt_of_mul_lt_mul_left this
    have h4 : g * (2 * t ^ 2) < g * s ^ 2 := by nlinarith
    exact Nat.lt_of_mul_lt_mul_left h4
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have htsR : (t : ℝ) < s := by exact_mod_cast hts
  have hqR : 2 * (t : ℝ) ^ 2 < (s : ℝ) ^ 2 := by exact_mod_cast hq
  have hpos4 : (0 : ℝ) < 4 * (s : ℝ) ^ 2 - (t : ℝ) ^ 2 := by nlinarith
  set rt0 : ℝ := Real.sqrt (4 * (s : ℝ) ^ 2 - (t : ℝ) ^ 2) with hrt0
  have hrt : 0 < rt0 := Real.sqrt_pos.mpr hpos4
  have hD : rt0 * rt0 = 4 * (s : ℝ) ^ 2 - (t : ℝ) ^ 2 := Real.mul_self_sqrt hpos4.le
  have P : Par (g : ℝ) (s : ℝ) (t : ℝ) (j : ℝ) rt0 := ⟨hgR, hjR, hsR, htR, htsR, hqR, hrt, hD⟩
  have hcR : (c : ℝ) = g * s ^ 2 := by exact_mod_cast hc
  have haR : (a : ℝ) = g * s * t := by exact_mod_cast hat
  have hbR : (b : ℝ) = g * (s ^ 2 - t ^ 2) := by
    have : (b : ℝ) + g * t ^ 2 = g * s ^ 2 := by exact_mod_cast hb'
    linarith
  obtain ⟨m, hm⟩ : ∃ m, j * a = m + 1 := ⟨j * a - 1, by have := Nat.mul_pos hj ha; omega⟩
  obtain ⟨n, hn⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  have hJA : ((m + 1 : ℕ) : ℝ) = j * g * s * t := by
    rw [← hm]; push_cast; rw [haR]; ring
  have hrR : ((n + 1 : ℕ) : ℝ) * t = j * g * s * (s ^ 2 - 2 * t ^ 2) := by
    have hr' : ((j : ℝ) * a + r) * a = j * c * b := by exact_mod_cast hr
    rw [← hn] at *
    rw [haR, hcR, hbR] at hr'
    have h0 : (g : ℝ) * s * t ≠ 0 := by positivity
    have : (g * s * t) * ((r : ℝ) * t - j * g * s * (s ^ 2 - 2 * t ^ 2)) = 0 := by
      linear_combination t * hr'
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h h0
    · have := h
      linarith
  have hL : ((j * c : ℕ) : ℝ) = j * g * s ^ 2 := by push_cast; rw [hcR]; ring
  have hJB : ((j * b : ℕ) : ℝ) = j * g * (s ^ 2 - t ^ 2) := by push_cast; rw [hbR]; ring
  have hL0 : 0 < j * c := Nat.mul_pos hj (by omega)
  have hJB0 : 0 < j * b := Nat.mul_pos hj hb
  have fin := core P (j * c) (j * b) m n hL0 hJB0 hL hJA hJB hrR
  have hlam : (2 * (s : ℝ) ^ 4) ≠ 0 := by positivity
  have hdet : 0 < det3 (1 / (2 * (s : ℝ) ^ 4) * 0) (rt0 / (2 * (s : ℝ) ^ 4) * 0)
      (1 / (2 * (s : ℝ) ^ 4) * Kc g s t j) (rt0 / (2 * (s : ℝ) ^ 4) * 0)
      (1 / (2 * (s : ℝ) ^ 4) * Bx g s t j) (rt0 / (2 * (s : ℝ) ^ 4) * Bw g s t j) := by
    have e : det3 (1 / (2 * (s : ℝ) ^ 4) * 0) (rt0 / (2 * (s : ℝ) ^ 4) * 0)
      (1 / (2 * (s : ℝ) ^ 4) * Kc g s t j) (rt0 / (2 * (s : ℝ) ^ 4) * 0)
      (1 / (2 * (s : ℝ) ^ 4) * Bx g s t j) (rt0 / (2 * (s : ℝ) ^ 4) * Bw g s t j)
        = (1 / (2 * (s : ℝ) ^ 4)) * (rt0 / (2 * (s : ℝ) ^ 4)) * detR 0 0 (Kc g s t j) 0 (Bx g s t j) (Bw g s t j) := by
      simp only [det3, detR]; ring
    rw [e]
    have := fact_dBig P
    positivity
  have hα : 0 < 1 / (2 * (s : ℝ) ^ 4) := by positivity
  have hβ : 0 < rt0 / (2 * (s : ℝ) ^ 4) := by positivity
  refine ⟨tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts P).1, _, _, _, _, _, _, hdet,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e0 : (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts P).1).pts 0 = mkPt 0 0 := rfl
    have e1 : (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts P).1).pts 1 = mkPt (g * s ^ 2) 0 := rfl
    rw [e0, e1, dist_sq_mkPt, hcR]; ring
  · have e0 : (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts P).1).pts 0 = mkPt 0 0 := rfl
    have e2 : (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts P).1).pts 2 =
      mkPt (xb g s t) (yb g s t rt0) := rfl
    have := (tile_facts P).2.1
    unfold bbc at this
    rw [e0, e2, dist_sq_mkPt, hbR]; nlinarith
  · have e1 : (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts P).1).pts 1 = mkPt (g * s ^ 2) 0 := rfl
    have e2 : (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts P).1).pts 2 =
      mkPt (xb g s t) (yb g s t rt0) := rfl
    have := (tile_facts P).2.2
    unfold aac at this
    rw [e1, e2, dist_sq_mkPt, haR]; nlinarith
  · rw [chart_dist _ _ _ hlam hD, div_eq_iff (by positivity)]
    push_cast
    rw [hcR]; simp only [Kc]; ring
  · rw [chart_dist _ _ _ hlam hD, div_eq_iff (by positivity)]
    push_cast
    rw [hcR, hbR]; simp only [Bx, Bw]; ring
  · rw [chart_dist _ _ _ hlam hD, div_eq_iff (by positivity)]
    push_cast
    rw [hcR, hbR]; simp only [Bx, Bw, Kc]; ring
  · rw [TriSet_CS hα hβ]
    refine fin.congr rfl ?_
    rw [hn, hm]; ring

/-! ### The five earlier instances as specializations -/

theorem t14_2_3_4 : ∃ (T : Tri) (x0 y0 x1 y1 x2 y2 : ℝ) (_ : 0 < det3 x0 y0 x1 y1 x2 y2),
    Dis T (TriSet x0 y0 x1 y1 x2 y2) 77 := by
  obtain ⟨T, x0, y0, x1, y1, x2, y2, hd, _, _, _, _, _, _, hD⟩ :=
    beeson_thm14 2 3 4 1 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨T, x0, y0, x1, y1, x2, y2, hd, hD.congr rfl (by norm_num)⟩

theorem t14_6_5_9 : ∃ (T : Tri) (x0 y0 x1 y1 x2 y2 : ℝ) (_ : 0 < det3 x0 y0 x1 y1 x2 y2),
    Dis T (TriSet x0 y0 x1 y1 x2 y2) 1288 := by
  obtain ⟨T, x0, y0, x1, y1, x2, y2, hd, _, _, _, _, _, _, hD⟩ :=
    beeson_thm14 6 5 9 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨T, x0, y0, x1, y1, x2, y2, hd, hD.congr rfl (by norm_num)⟩

theorem t14_3_8_9 : ∃ (T : Tri) (x0 y0 x1 y1 x2 y2 : ℝ) (_ : 0 < det3 x0 y0 x1 y1 x2 y2),
    Dis T (TriSet x0 y0 x1 y1 x2 y2) 442 := by
  obtain ⟨T, x0, y0, x1, y1, x2, y2, hd, _, _, _, _, _, _, hD⟩ :=
    beeson_thm14 3 8 9 1 21 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨T, x0, y0, x1, y1, x2, y2, hd, hD.congr rfl (by norm_num)⟩

theorem t14_4_15_16 : ∃ (T : Tri) (x0 y0 x1 y1 x2 y2 : ℝ) (_ : 0 < det3 x0 y0 x1 y1 x2 y2),
    Dis T (TriSet x0 y0 x1 y1 x2 y2) 1457 := by
  obtain ⟨T, x0, y0, x1, y1, x2, y2, hd, _, _, _, _, _, _, hD⟩ :=
    beeson_thm14 4 15 16 1 56 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨T, x0, y0, x1, y1, x2, y2, hd, hD.congr rfl (by norm_num)⟩

theorem t14_15_16_25 : ∃ (T : Tri) (x0 y0 x1 y1 x2 y2 : ℝ) (_ : 0 < det3 x0 y0 x1 y1 x2 y2),
    Dis T (TriSet x0 y0 x1 y1 x2 y2) 24354 := by
  obtain ⟨T, x0, y0, x1, y1, x2, y2, hd, _, _, _, _, _, _, hD⟩ :=
    beeson_thm14 15 16 25 3 35 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨T, x0, y0, x1, y1, x2, y2, hd, hD.congr rfl (by norm_num)⟩

end Erdos634.BeesonT14General
