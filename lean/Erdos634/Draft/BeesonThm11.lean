import Erdos634.Draft.WSeedGW
import Erdos634.Realizable

/-!
# Beeson, "Triangle tiling III: the case 3α+2β = π" (arXiv 1206.2229v4), Theorem 11

> Let `M² + N = 2K²` with `M² < N` and `K ∣ N`.  The triangle with sides `BC = M N / K`,
> `AC = N − K²`, `AB = K²` has an `N`-tiling by the tile `(a,b,c) = (M, N/K − K, K)`.

**ALREADY DONE for the `(e,f)`-parametrised family:** `Draft.WSeedG.w_seed` (`WSeedGW.lean`), the
triangle with sides `f²(f²−e²), ef(2f²−e²), f⁴` cut into `f²(2f²−e²)` tiles `(ef, f²−e², f²)`.
What this file adds is the reduction of Beeson's general `(M, N, K)` to that family and the final
statement `beeson_thm11`: from `K ∣ M²`, `M = e f g`, `K = f² g` (`h = gcd(M,K) = f g`,
`e/f = M/K` in lowest terms), the tile is `g (ef, f²−e², f²)` and the triangle is `g²` times the
`w_seed` triangle; the dissection is `Realizable.scaleDissection` with real ratio `g`, then
`Realizable.cut_scale` with natural ratio `g` (count `g² f²(2f²−e²) = 2K² − M² = N`).
Hypotheses witnessed: `(M,N,K) = (6,126,9)` (tile `(6,5,9)`, triangle `(45,84,81)`; area check
`126² · 200 = 3175200 = 16 · Area²(45,84,81)`-Heron radicand) and `(2,28,4)` (tile `(2,3,4)`, triangle `(12,14,16)`).
Credit Beeson (arXiv 1206.2229), Paliy (beta seed note), Beeson-Rosu.  UNAUDITED.
-/

namespace Erdos634.BeesonThm11

open Erdos634.Geometry Erdos634.Draft.FDBBaseBetaE1 Erdos634.Realizable

theorem hs_congr {T : Erdos634.Geometry.Tri} {a b c a' b' c' : ℝ} (h : HasSides T a b c)
    (ha : a = a') (hb : b = b') (hc : c = c') : HasSides T a' b' c' := by
  subst ha hb hc; exact h

theorem hasSides_target_scaleDiss {N : ℕ} (D : CongruentDissection N) (p : Plane) (r : ℝ)
    (hr : r ≠ 0) {a b c : ℝ} (h : HasSides D.target a b c) :
    HasSides (scaleDissection p r hr D).target (|r| * a) (|r| * b) (|r| * c) := by
  obtain ⟨τ, h1, h2, h3⟩ := h
  refine ⟨τ, ?_, ?_, ?_⟩
  · rw [scaleDissection_target_pts, scaleDissection_target_pts, homothetyEquiv_dist, h1]
  · rw [scaleDissection_target_pts, scaleDissection_target_pts, homothetyEquiv_dist, h2]
  · rw [scaleDissection_target_pts, scaleDissection_target_pts, homothetyEquiv_dist, h3]

theorem hasSides_model_scaleDiss {N : ℕ} (D : CongruentDissection N) (p : Plane) (r : ℝ)
    (hr : r ≠ 0) {a b c : ℝ} (h : HasSides D.model a b c) :
    HasSides (scaleDissection p r hr D).model (|r| * a) (|r| * b) (|r| * c) := by
  obtain ⟨τ, h1, h2, h3⟩ := h
  refine ⟨τ, ?_, ?_, ?_⟩
  · rw [scaleDissection_model_pts, scaleDissection_model_pts, homothetyEquiv_dist, h1]
  · rw [scaleDissection_model_pts, scaleDissection_model_pts, homothetyEquiv_dist, h2]
  · rw [scaleDissection_model_pts, scaleDissection_model_pts, homothetyEquiv_dist, h3]

theorem hasSides_scaleN' {T : Erdos634.Geometry.Tri} {a b c : ℝ} (h : HasSides T a b c) (k : ℕ) (hk : 0 < k) :
    HasSides (scaleN k hk T) (k * a) (k * b) (k * c) := by
  obtain ⟨τ, h1, h2, h3⟩ := h
  have hk0 : |(k : ℝ)| = k := abs_of_nonneg (Nat.cast_nonneg k)
  refine ⟨τ, ?_, ?_, ?_⟩
  · show dist (AffineMap.homothety (T.pts 0) (k : ℝ) (T.pts (τ 1)))
      (AffineMap.homothety (T.pts 0) (k : ℝ) (T.pts (τ 2))) = _
    rw [dist_homothety, h1, hk0]
  · show dist (AffineMap.homothety (T.pts 0) (k : ℝ) (T.pts (τ 2)))
      (AffineMap.homothety (T.pts 0) (k : ℝ) (T.pts (τ 0))) = _
    rw [dist_homothety, h2, hk0]
  · show dist (AffineMap.homothety (T.pts 0) (k : ℝ) (T.pts (τ 0)))
      (AffineMap.homothety (T.pts 0) (k : ℝ) (T.pts (τ 1))) = _
    rw [dist_homothety, h3, hk0]

/-- The `(e,f,g)`-parametrised form: the triangle `g² · W(e,f)` is cut into `g² f²(2f²−e²)` tiles
`g (ef, f²−e², f²)`. -/
theorem thm11_efg (e f g n : ℕ) (he : 1 ≤ e) (hef : e < f) (hg : 0 < g)
    (hn : n = g * g * (f ^ 2 * (2 * f ^ 2 - e ^ 2))) :
    ∃ D : CongruentDissection n,
      HasSides D.target ((g : ℝ) * ((g : ℝ) * ((f : ℝ) ^ 2 * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))))
        ((g : ℝ) * ((g : ℝ) * ((e : ℝ) * f * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))))
        ((g : ℝ) * ((g : ℝ) * (f : ℝ) ^ 4)) ∧
      HasSides D.model ((g : ℝ) * ((e : ℝ) * f)) ((g : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
        ((g : ℝ) * (f : ℝ) ^ 2) := by
  subst hn
  obtain ⟨D0, h0t, h0m⟩ := Erdos634.Draft.WSeedG.w_seed e f he hef
  have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have habs : |(g : ℝ)| = g := abs_of_nonneg (Nat.cast_nonneg g)
  set D1 := scaleDissection (D0.target.pts 0) (g : ℝ) hg0 D0 with hD1
  have h1t := hasSides_target_scaleDiss D0 (D0.target.pts 0) (g : ℝ) hg0 h0t
  have h1m := hasSides_model_scaleDiss D0 (D0.target.pts 0) (g : ℝ) hg0 h0m
  rw [habs] at h1t h1m
  obtain ⟨E, hEt, hEm⟩ := cut_scale (T := D1.target) (t := D1.model) ⟨D1, rfl, rfl⟩ g hg
  refine ⟨E, ?_, ?_⟩
  · rw [hEt]; exact hasSides_scaleN' h1t g hg
  · rw [hEm]; exact h1m

/-- **Beeson, Theorem 11 (arXiv 1206.2229v4), UNAUDITED.** -/
theorem beeson_thm11 (M N K : ℕ) (hM : 0 < M) (h : M ^ 2 + N = 2 * K ^ 2) (hlt : M ^ 2 < N)
    (hdiv : K ∣ N) :
    ∃ D : CongruentDissection N,
      HasSides D.target ((N : ℝ) - (K : ℝ) ^ 2) ((M : ℝ) * N / K) ((K : ℝ) ^ 2) ∧
      HasSides D.model (M : ℝ) ((N : ℝ) / K - K) (K : ℝ) := by
  have hMK : M ^ 2 < K ^ 2 := by nlinarith
  have hKpos : 0 < K := Nat.pos_of_ne_zero (by rintro rfl; simp at hMK)
  have hKM : K ∣ M ^ 2 := by
    have : K ∣ M ^ 2 + N := by rw [h]; exact Dvd.intro (2 * K) (by ring)
    exact (Nat.dvd_add_left hdiv).mp this
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
  have hef : e < f := by
    have : e * (f * g) < f * (f * g) := by
      have h1 : (e * (f * g)) ^ 2 < (f * (f * g)) ^ 2 := hMK
      exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) h1
    exact Nat.lt_of_mul_lt_mul_right this
  have hle : e ^ 2 ≤ 2 * f ^ 2 := by nlinarith
  have h' : N + g ^ 2 * f ^ 2 * e ^ 2 = 2 * g ^ 2 * f ^ 4 := by
    have := h; ring_nf at this ⊢; linarith
  have hNnat : N = g * g * (f ^ 2 * (2 * f ^ 2 - e ^ 2)) := by
    have h'z : (N : ℤ) + g ^ 2 * f ^ 2 * e ^ 2 = 2 * g ^ 2 * f ^ 4 := by exact_mod_cast h'
    zify [hle]
    linear_combination h'z
  have hNr : (N : ℝ) = (g : ℝ) * ((g : ℝ) * ((f : ℝ) ^ 2 * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) := by
    have h'r : (N : ℝ) + (g : ℝ) ^ 2 * (f : ℝ) ^ 2 * (e : ℝ) ^ 2 = 2 * (g : ℝ) ^ 2 * (f : ℝ) ^ 4 := by
      exact_mod_cast h'
    linear_combination h'r
  obtain ⟨D, hDt, hDm⟩ := thm11_efg e f g N he hef hg hNnat
  refine ⟨D, ?_, ?_⟩
  · refine hs_congr hDt ?_ ?_ ?_
    · rw [hNr]; push_cast; ring
    · rw [hNr]; push_cast
      have : (f : ℝ) ≠ 0 := by exact_mod_cast hf.ne'
      have : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
      first | (field_simp; done) | (field_simp; ring)
    · push_cast; ring
  · refine hs_congr hDm ?_ ?_ ?_
    · push_cast; ring
    · rw [hNr]; push_cast
      have : (f : ℝ) ≠ 0 := by exact_mod_cast hf.ne'
      have : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
      first | (field_simp; done) | (field_simp; ring)
    · push_cast; ring

/-- Witness `(M,N,K) = (6,126,9)`: tile `(6,5,9)`, triangle `(AC,BC,AB) = (45,84,81)`. -/
theorem beeson_thm11_6_126_9 :
    ∃ D : CongruentDissection 126, HasSides D.target 45 84 81 ∧ HasSides D.model 6 5 9 := by
  obtain ⟨D, h1, h2⟩ := beeson_thm11 6 126 9 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  exact ⟨D, hs_congr h1 (by norm_num) (by norm_num) (by norm_num),
    hs_congr h2 (by norm_num) (by norm_num) (by norm_num)⟩

/-- Witness `(M,N,K) = (2,28,4)`: tile `(2,3,4)`, triangle `(AC,BC,AB) = (12,14,16)`
(Heron radicand check: `28² · (15·1·... )`: area ratio `28 = (Area(12,14,16)/Area(2,3,4))`). -/
theorem beeson_thm11_2_28_4 :
    ∃ D : CongruentDissection 28, HasSides D.target 12 14 16 ∧ HasSides D.model 2 3 4 := by
  obtain ⟨D, h1, h2⟩ := beeson_thm11 2 28 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  exact ⟨D, hs_congr h1 (by norm_num) (by norm_num) (by norm_num),
    hs_congr h2 (by norm_num) (by norm_num) (by norm_num)⟩

end Erdos634.BeesonThm11
