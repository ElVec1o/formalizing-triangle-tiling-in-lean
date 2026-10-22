import Erdos634.Draft.BeesonT14General
import Erdos634.Draft.LadderWrap

/-!
# Beeson (arXiv 1206.2229v4) Theorem 15, converse: `c < 2b` gives tilings with `N = t^2 j^2 (b+c)(b+2c)`

NOTE, UNAUDITED.  Credit: Beeson (arXiv 1206.2229), Beeson-Zhang, Zhang, Laczkovich.

Printed: *if `c < 2b`, then for every positive integer `t` there is a tiling with `M = t j (b+c-a)` and
`N = t^2 j^2 (b+c)(b+2c)`, `j = lcm(a,c)/c`.* Proof printed: take the tiling of Thm 14 and replace each tile by a
quadratic tiling of scale `t`.  Here: the count `N` and the triangle (side lengths); `M` is the colouring parameter
(Beeson Thm 1), not proved here.  Hypotheses of `beeson_thm14` are discharged from `c < 2b` with the explicit
`r = (c/g)(2b - c)`, `g = gcd(a,c)`, `j = a/g = lcm(a,c)/c`.
-/

namespace Erdos634.BeesonT15Conv

open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.BeesonT14General Erdos634.ZhangSporadic

theorem dist_P10 (A B C : Plane) (k : ℕ) :
    dist A (Erdos634.Subdivision.P A B C k 0) = k * dist A B := by
  unfold Erdos634.Subdivision.P
  rw [dist_eq_norm, show A - (A + (k : ℝ) • (B - A) + ((0 : ℕ) : ℝ) • (C - A)) = (k : ℝ) • (A - B) by
    simp; module, norm_smul, ← dist_eq_norm]
  simp

theorem dist_P01 (A B C : Plane) (k : ℕ) :
    dist A (Erdos634.Subdivision.P A B C 0 k) = k * dist A C := by
  unfold Erdos634.Subdivision.P
  rw [dist_eq_norm, show A - (A + ((0 : ℕ) : ℝ) • (B - A) + (k : ℝ) • (C - A)) = (k : ℝ) • (A - C) by
    simp; module, norm_smul, ← dist_eq_norm]
  simp

theorem dist_P12 (A B C : Plane) (k : ℕ) :
    dist (Erdos634.Subdivision.P A B C k 0) (Erdos634.Subdivision.P A B C 0 k) = k * dist B C := by
  unfold Erdos634.Subdivision.P
  rw [dist_eq_norm, show (A + (k : ℝ) • (B - A) + ((0 : ℕ) : ℝ) • (C - A))
      - (A + ((0 : ℕ) : ℝ) • (B - A) + (k : ℝ) • (C - A)) = (k : ℝ) • (B - C) by simp; module,
    norm_smul, ← dist_eq_norm]
  simp

/-- the integers of Thm 15's converse: `j = lcm(a,c)/c` and the Thm 14 parameter `r` with `(j a + r) a = j c b`. -/
theorem params (a b c : ℕ) (ha : 0 < a) (h : a * a + c * b = c * c) (hcb : c < 2 * b) :
    ∃ r : ℕ, 0 < r ∧ (Nat.lcm a c / c * a + r) * a = Nat.lcm a c / c * c * b := by
  have hc : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0; simp at h; omega
    · exact h0
  obtain ⟨a', ha'⟩ := Nat.gcd_dvd_left a c
  obtain ⟨c', hc'⟩ := Nat.gcd_dvd_right a c
  set g := Nat.gcd a c with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ ha
  have hc'pos : 0 < c' := by
    rcases Nat.eq_zero_or_pos c' with h0 | h0
    · rw [h0] at hc'; omega
    · exact h0
  have hj : Nat.lcm a c / c = a' := by
    have h1 : g * Nat.lcm a c = g * (g * a' * c') := by
      rw [Nat.gcd_mul_lcm]
      conv_lhs => rw [ha', hc']
      ring
    have h2 : Nat.lcm a c = g * a' * c' := Nat.eq_of_mul_eq_mul_left hgpos h1
    rw [h2]
    conv_lhs => rw [show c = g * c' from hc']
    rw [show g * a' * c' = (g * c') * a' by ring]
    exact Nat.mul_div_cancel_left _ (by positivity)
  obtain ⟨d, hd⟩ : ∃ d, 2 * b = c + d := ⟨2 * b - c, by omega⟩
  have hdpos : 0 < d := by omega
  have h1 : g * (a' * a') + c' * b = g * (c' * c') := by
    have : g * (g * (a' * a') + c' * b) = g * (g * (c' * c')) := by
      rw [ha', hc'] at h; nlinarith [h]
    exact Nat.eq_of_mul_eq_mul_left hgpos this
  refine ⟨c' * d, Nat.mul_pos hc'pos hdpos, ?_⟩
  rw [hj]
  have e : c' * (2 * b) = c' * (c + d) := by rw [hd]
  have key : a' * a + c' * d = c' * b := by
    rw [ha', hc'] at *; nlinarith [e, h1]
  rw [key, ha', hc']
  ring

/-- **Beeson Thm 15, converse (count and triangle).**  `a^2 + c b = c^2`, `c < 2 b`, `t >= 1`, `j = lcm(a,c)/c`:
a triangle with sides `t j c^2`, `t j b (b+2c)`, `t j c (b+c)` is dissected into `t^2 j^2 (b+c)(b+2c)` copies of the
tile `(a,b,c)`. -/
theorem thm15_converse (a b c t : ℕ) (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) (h : a * a + c * b = c * c)
    (hcb : c < 2 * b) :
    ∃ (T : Tri) (E : CongruentDissection (t * t * ((Nat.lcm a c / c) * (Nat.lcm a c / c) * ((b + c) * (b + 2 * c))))),
      E.model = T ∧ dist (T.pts 0) (T.pts 1) ^ 2 = (c : ℝ) ^ 2 ∧ dist (T.pts 0) (T.pts 2) ^ 2 = (b : ℝ) ^ 2 ∧
      dist (T.pts 1) (T.pts 2) ^ 2 = (a : ℝ) ^ 2 ∧
      dist (E.target.pts 0) (E.target.pts 1) ^ 2 = ((t * (Nat.lcm a c / c) * c ^ 2 : ℕ) : ℝ) ^ 2 ∧
      dist (E.target.pts 0) (E.target.pts 2) ^ 2 = ((t * (Nat.lcm a c / c) * b * (b + 2 * c) : ℕ) : ℝ) ^ 2 ∧
      dist (E.target.pts 1) (E.target.pts 2) ^ 2 = ((t * (Nat.lcm a c / c) * c * (b + c) : ℕ) : ℝ) ^ 2 := by
  obtain ⟨r, hr, hrel⟩ := params a b c ha h hcb
  set j := Nat.lcm a c / c with hjdef
  have hjpos : 0 < j := by
    rw [hjdef]; apply Nat.div_pos
    · exact Nat.le_of_dvd (Nat.lcm_pos ha (by rcases Nat.eq_zero_or_pos c with h0 | h0 <;>
        [(subst h0; simp at h; omega); exact h0])) (Nat.dvd_lcm_right a c)
    · rcases Nat.eq_zero_or_pos c with h0 | h0 <;> [(subst h0; simp at h; omega); exact h0]
  obtain ⟨T, x0, y0, x1, y1, x2, y2, hd, e1, e2, e3, s1, s2, s3, hD⟩ := beeson_thm14 a b c j r ha hb hjpos hr h hrel
  obtain ⟨C, hreg, hm⟩ := hD
  set T' := mkTri x0 y0 x1 y1 x2 y2 hd.ne' with hT'
  set D := C.toCongruentDissection T' (hreg.trans (TriSet_eq_carrier hd)) with hDdef
  have hDt : D.target = T' := rfl
  obtain ⟨E, hE1, hE2⟩ := Erdos634.Draft.LadderWrap.ladder_dissection (T'.pts 0) (T'.pts 1) (T'.pts 2) T'.indep
    (N := 3 * (j * c) ^ 2 + (j * b) ^ 2 + (j * a) ^ 2 + 2 * r * (j * a)) D hDt t ht
  have hN : t * t * (3 * (j * c) ^ 2 + (j * b) ^ 2 + (j * a) ^ 2 + 2 * r * (j * a))
      = t * t * (j * j * ((b + c) * (b + 2 * c))) := by
    congr 1
    apply Nat.cast_injective (R := ℤ)
    push_cast
    have hrel' : ((j : ℤ) * a + r) * a = j * c * b := by exact_mod_cast hrel
    have h' : (a : ℤ) * a + c * b = c * c := by exact_mod_cast h
    linear_combination (2 * (j : ℤ)) * hrel' - (j : ℤ) ^ 2 * h'
  obtain ⟨E', hE'1, hE'2⟩ : ∃ E' : CongruentDissection (t * t * (j * j * ((b + c) * (b + 2 * c)))),
      E'.target = E.target ∧ E'.model = E.model := by
    rw [← hN]; exact ⟨E, rfl, rfl⟩
  have d01 : dist (T'.pts 0) (T'.pts 1) ^ 2 = ((j * c ^ 2 : ℕ) : ℝ) ^ 2 := by
    show dist (mkPt x0 y0) (mkPt x1 y1) ^ 2 = _
    rw [dist_sq_mkPt, ← s1]; ring
  have d02 : dist (T'.pts 0) (T'.pts 2) ^ 2 = ((j * b * (b + 2 * c) : ℕ) : ℝ) ^ 2 := by
    show dist (mkPt x0 y0) (mkPt x2 y2) ^ 2 = _
    rw [dist_sq_mkPt, ← s2]; ring
  have d12 : dist (T'.pts 1) (T'.pts 2) ^ 2 = ((j * c * (b + c) : ℕ) : ℝ) ^ 2 := by
    show dist (mkPt x1 y1) (mkPt x2 y2) ^ 2 = _
    rw [dist_sq_mkPt, ← s3]; ring
  refine ⟨T, E', ?_, e1, e2, e3, ?_, ?_, ?_⟩
  · rw [hE'2, hE2]; exact hm
  · rw [hE'1, hE1, Erdos634.Subdivision.bigTri_pts0, Erdos634.Subdivision.bigTri_pts1, dist_P10, mul_pow, d01]
    push_cast; ring
  · rw [hE'1, hE1, Erdos634.Subdivision.bigTri_pts0, Erdos634.Subdivision.bigTri_pts2, dist_P01, mul_pow, d02]
    push_cast; ring
  · rw [hE'1, hE1, Erdos634.Subdivision.bigTri_pts1, Erdos634.Subdivision.bigTri_pts2, dist_P12, mul_pow, d12]
    push_cast; ring

/-- Non-vacuity: `(a,b,c) = (2,3,4)`, `t = 1` (`j = 1`, `N = 77 = 7 * 11`), and `t = 2` (`N = 308`); `(3,8,9)`,
`t = 1`: `j = 1`, `N = 17 * 26 = 442`. -/
theorem thm15_wit_234 : ∃ N : ℕ, N = 77 ∧ ∃ (_ : CongruentDissection N), True := by
  obtain ⟨T, E, _⟩ := thm15_converse 2 3 4 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨_, by norm_num [Nat.lcm], E, trivial⟩

theorem thm15_wit_389 : ∃ N : ℕ, N = 442 ∧ ∃ (_ : CongruentDissection N), True := by
  obtain ⟨T, E, _⟩ := thm15_converse 3 8 9 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨_, by norm_num [Nat.lcm], E, trivial⟩

/-- `t = 3` on `(2,3,4)`: `N = 9 * 77 = 693`. -/
theorem thm15_wit_234_t3 : ∃ N : ℕ, N = 693 ∧ ∃ (_ : CongruentDissection N), True := by
  obtain ⟨T, E, _⟩ := thm15_converse 2 3 4 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨_, by norm_num [Nat.lcm], E, trivial⟩

#print axioms thm15_converse
#print axioms thm15_wit_234
end Erdos634.BeesonT15Conv
