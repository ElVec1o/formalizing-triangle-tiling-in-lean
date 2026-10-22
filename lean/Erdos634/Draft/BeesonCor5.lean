import Erdos634.Draft.BeesonT24Exists
import Erdos634.Draft.BeesonLemma52
import Erdos634.Draft.LaczFormalTransportCor
import Erdos634.Draft.LaczFormalL24Wit
import Erdos634.Draft.LaczFormalL26Beeson

/-!
# Beeson (arXiv 1206.2229v4) Corollary 5: every rational tile with `3 alpha + 2 beta = pi` has an isosceles
triangle with base angles `alpha + beta` that is tiled (up to similarity) by it

NOTE, UNAUDITED.  Credit: Beeson (arXiv 1206.2229), Laczkovich (Discrete Math. 140 (1995)), Beeson-Zhang, Zhang.

Printed: *Let `3 alpha + 2 beta = pi` and the tile be rational.  Then for some `N`, some isosceles triangle with base
angles `alpha + beta` can be `N`-tiled by the tile.*  Proof printed: by Lemma 52 either Laczkovich's construction
(Thm 23) or Thm 24 applies.

Form here: tile `(a,b,c)` of naturals with `a^2 + c b = c^2` (i.e. `3 alpha + 2 beta = pi`, `c | a^2`) and no common
factor (`gcd(gcd a b) c = 1`, Beeson's hypothesis; `gcd(a,b) = 1` is derived, Beeson Lemma 4), `R : RTri` the real
tile with sides `a,b,c`.  Conclusion: a `CongruentDissection` of an isosceles triangle (apex `pts 2`, apex angle
`alpha`, hence base angles `(pi - alpha)/2 = alpha + beta`) whose tiles are congruent to `scaleTri s R.Delta`, `s > 0`
(`s = 1` in the Thm 24 branch, `s = 1/q` in the Thm 23 branch: "tiled by the tile" means similar copies, as in Beeson).
GAP CHECK (honest): the split is NOT at the truncated 0.5698.  Thm 23 as printed needs `b/c < 0.5698`, which covers
`s > 0.656`; but `thm24_fourth` (Laczkovich 2.4, fourth triple) is proved for the exact condition `b^3 < c (c-b)^2`
(root `x ~ 0.56984`), and Thm 24 for `a^2 c < b (a^2+b^2)` (the complementary one, `b^3 > c(c-b)^2`).  Lemma 52 plus
the rational root test shows equality never holds, so there is no gap.  `cor5_rational` removes the integer
assumption: any `R : RTri` (rational sides) with `b c = c^2 - a^2` is rescaled to coprime naturals (`rat_scale`) and
the conclusion transported by `scaleTri`.
-/

namespace Erdos634.BeesonCor5

open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.ZhangPara Erdos634.ZhangSporadic
  Erdos634.LaczL22 Erdos634.BeesonT24Exists Erdos634.Realizable Erdos634.LaczL24

theorem gcd_ab_of_three (a b c : ℕ) (h : a * a + c * b = c * c) (hg : Nat.gcd (Nat.gcd a b) c = 1) :
    Nat.gcd a b = 1 := by
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have hpa : p ∣ a := hpd.trans (Nat.gcd_dvd_left _ _)
  have hpb : p ∣ b := hpd.trans (Nat.gcd_dvd_right _ _)
  have hcc : p ∣ c * c := by
    rw [← h]; exact dvd_add (dvd_mul_of_dvd_left hpa _) (dvd_mul_of_dvd_right hpb _)
  have hpc : p ∣ c := by
    rcases hp.dvd_mul.mp hcc with h1 | h1 <;> exact h1
  have : p ∣ Nat.gcd (Nat.gcd a b) c := Nat.dvd_gcd hpd hpc
  rw [hg] at this
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

/-- apex angle of the isosceles triangle of Thm 24 equals `alpha` (law of cosines on both). -/
theorem apex_angle (T' : Tri) (R : RTri) (a b c : ℕ) (mu : ℝ) (hmu : 0 < mu) (ha : 0 < a) (hb : 0 < b)
    (h : a * a + c * b = c * c) (hRa : R.a = (a : ℚ)) (hRb : R.b = (b : ℚ)) (hRc : R.c = (c : ℚ))
    (h01 : dist (T'.pts 0) (T'.pts 1) ^ 2 = (mu * a) ^ 2) (h02 : dist (T'.pts 0) (T'.pts 2) ^ 2 = (mu * c) ^ 2)
    (h12 : dist (T'.pts 1) (T'.pts 2) ^ 2 = (mu * c) ^ 2) :
    cornerAngle (T'.pts 0) (T'.pts 2) (T'.pts 1) = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) := by
  have hcpos : 0 < c := by rcases Nat.eq_zero_or_pos c with h0 | h0 <;> [(subst h0; simp at h; omega); exact h0]
  have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have hbR : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have hcR : (0 : ℝ) < c := Nat.cast_pos.mpr hcpos
  have hR1 : dist (R.Δ.pts 1) (R.Δ.pts 0) = c := by
    rw [dist_comm, R.hc, hRc]; simp
  have hR2 : dist (R.Δ.pts 2) (R.Δ.pts 0) = b := by rw [R.hb, hRb]; simp
  have hR3 : dist (R.Δ.pts 1) (R.Δ.pts 2) = a := by rw [R.ha, hRa]; simp
  have hd02 : dist (T'.pts 0) (T'.pts 2) = mu * c :=
    eq_of_sq_eq' dist_nonneg (by positivity) h02
  have hd12 : dist (T'.pts 1) (T'.pts 2) = mu * c :=
    eq_of_sq_eq' dist_nonneg (by positivity) h12
  have hd01 : dist (T'.pts 0) (T'.pts 1) ^ 2 = (mu * a) ^ 2 := h01
  have hhR : ((a : ℝ)) * a + c * b = c * c := by exact_mod_cast h
  have c1 := Erdos634.AngleThreshold.cos_of_sides (T'.pts 0) (T'.pts 2) (T'.pts 1)
    (by rw [hd02]; positivity) (by rw [hd12]; positivity)
  have c2 := Erdos634.AngleThreshold.cos_of_sides (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2)
    (by rw [hR1]; positivity) (by rw [hR2]; positivity)
  have hcos : Real.cos (cornerAngle (T'.pts 0) (T'.pts 2) (T'.pts 1))
      = Real.cos (cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2)) := by
    rw [c1, c2, hd02, hd12, hd01, hR1, hR2, hR3]
    field_simp
    nlinarith [hhR]
  exact Real.injOn_cos ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩ hcos

/-- **Cor 5, branch Thm 24** (`a^2 c < b(a^2+b^2)`). -/
theorem cor5_thm24 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (h : a * a + c * b = c * c)
    (hg : Nat.gcd (Nat.gcd a b) c = 1) (hlt : a * a * c < b * (a * a + b * b)) (R : RTri)
    (hRa : R.a = (a : ℚ)) (hRb : R.b = (b : ℚ)) (hRc : R.c = (c : ℚ)) :
    ∃ (s : ℝ) (hs : 0 < s) (N : ℕ) (D : CongruentDissection N),
      dist (D.target.pts 2) (D.target.pts 0) = dist (D.target.pts 2) (D.target.pts 1) ∧
      cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1)
        = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) ∧
      D.model.Congruent (scaleTri s hs.ne' R.Δ) := by
  have hg2 := gcd_ab_of_three a b c h hg
  obtain ⟨lam, n, T, x0, y0, x1, y1, x2, y2, hd, hl, t1, t2, t3, s1, s2, s3, hD⟩ :=
    beeson_thm24_exists a b c ha hb h hg2 hlt
  obtain ⟨C, hr, hm⟩ := hD
  have hcpos : 0 < c := by rcases Nat.eq_zero_or_pos c with h0 | h0 <;> [(subst h0; simp at h; omega); exact h0]
  set mu : ℝ := ((lam * a * b * (a + c) : ℕ) : ℝ) with hmu
  have hmupos : 0 < mu := by rw [hmu]; exact_mod_cast Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hl ha) hb) (by omega)
  set T' := mkTri x0 y0 x1 y1 x2 y2 hd.ne' with hT'
  have e01 : dist (T'.pts 0) (T'.pts 1) ^ 2 = (mu * a) ^ 2 := by
    show dist (mkPt x0 y0) (mkPt x1 y1) ^ 2 = _
    rw [dist_sq_mkPt]
    calc _ = (x1 - x0) ^ 2 + (y1 - y0) ^ 2 := by ring
      _ = _ := by rw [s1]; simp only [hmu]; push_cast; ring
  have e02 : dist (T'.pts 0) (T'.pts 2) ^ 2 = (mu * c) ^ 2 := by
    show dist (mkPt x0 y0) (mkPt x2 y2) ^ 2 = _
    rw [dist_sq_mkPt]
    calc _ = (x2 - x0) ^ 2 + (y2 - y0) ^ 2 := by ring
      _ = _ := by rw [s2]; simp only [hmu]; push_cast; ring
  have e12 : dist (T'.pts 1) (T'.pts 2) ^ 2 = (mu * c) ^ 2 := by
    show dist (mkPt x1 y1) (mkPt x2 y2) ^ 2 = _
    rw [dist_sq_mkPt]
    calc _ = (x2 - x1) ^ 2 + (y2 - y1) ^ 2 := by ring
      _ = _ := by rw [s3]; simp only [hmu]; push_cast; ring
  have hcR : (0 : ℝ) < c := Nat.cast_pos.mpr hcpos
  refine ⟨1, one_pos, n, C.toCongruentDissection T' (hr.trans (TriSet_eq_carrier hd)), ?_, ?_, ?_⟩
  · show dist (T'.pts 2) (T'.pts 0) = dist (T'.pts 2) (T'.pts 1)
    rw [dist_comm (T'.pts 2) (T'.pts 0), dist_comm (T'.pts 2) (T'.pts 1)]
    exact (eq_of_sq_eq' dist_nonneg (by positivity) e02).trans
      (eq_of_sq_eq' dist_nonneg (by positivity) e12).symm
  · exact apex_angle T' R a b c mu hmupos ha hb h hRa hRb hRc e01 e02 e12
  · show C.model.Congruent _
    rw [hm]
    refine congr_of_sq3 T R.Δ 1 1 one_pos ?_ ?_ ?_
    · have : dist (R.Δ.pts ((1 : Equiv.Perm (Fin 3)) 0)) (R.Δ.pts ((1 : Equiv.Perm (Fin 3)) 1)) = c := by
        simp [R.hc, hRc]
      rw [this, t1]; ring
    · have : dist (R.Δ.pts ((1 : Equiv.Perm (Fin 3)) 1)) (R.Δ.pts ((1 : Equiv.Perm (Fin 3)) 2)) = a := by
        simp [R.ha, hRa]
      rw [this, t3]; ring
    · have : dist (R.Δ.pts ((1 : Equiv.Perm (Fin 3)) 2)) (R.Δ.pts ((1 : Equiv.Perm (Fin 3)) 0)) = b := by
        simp [R.hb, hRb]
      rw [this, dist_comm, t2]; ring

/-- **Cor 5, branch Thm 23 / Laczkovich 2.4 fourth** (`b^3 < c (c-b)^2`, i.e. `b/c < 0.56984`, which contains Beeson's
printed range `b/c < 0.5698`). -/
theorem cor5_fourth (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hbc : b < c) (h : a * a + c * b = c * c)
    (hlt : (b : ℝ) ^ 3 < c * (c - b) ^ 2) (R : RTri)
    (hRa : R.a = (a : ℚ)) (hRb : R.b = (b : ℚ)) (hRc : R.c = (c : ℚ)) :
    ∃ (s : ℝ) (hs : 0 < s) (N : ℕ) (D : CongruentDissection N),
      dist (D.target.pts 2) (D.target.pts 0) = dist (D.target.pts 2) (D.target.pts 1) ∧
      cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1)
        = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) ∧
      D.model.Congruent (scaleTri s hs.ne' R.Δ) := by
  have hcR : (0 : ℚ) < c := by exact_mod_cast (by omega : 0 < c)
  have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
  have haQ : (0 : ℚ) < a := by exact_mod_cast ha
  have hbcQ : (b : ℚ) < c := by exact_mod_cast hbc
  have hhQ : (a : ℚ) * a + c * b = c * c := by exact_mod_cast h
  have hltQ : (b : ℚ) ^ 3 < c * (c - b) ^ 2 := by exact_mod_cast hlt
  obtain ⟨T, q, hq, M, C, hC1, hC2, hiso, hang⟩ :=
    Erdos634.LaczL26.thm24_fourth R ((a : ℚ) / c) (by positivity) (by rw [div_lt_one hcR]; nlinarith)
      (by rw [hRa, hRc]; field_simp)
      (by rw [hRb, hRc]; field_simp; nlinarith [hhQ])
      (by
        have hcb : (c : ℚ) - b ≠ 0 := by linarith
        have hu : ((a : ℚ) / c) ^ 2 = (c - b) / c := by
          field_simp; nlinarith [hhQ]
        have h4 : ((a : ℚ) / c) ^ 4 = ((c - b) / c) ^ 2 := by rw [← hu]; ring
        have h1 : (1 : ℚ) - (c - b) / c = b / c := by field_simp; ring
        rw [h4, hu, h1]
        have e : ((c - b : ℚ) / c) ^ 2 - (b / c) ^ 3 = (c * (c - b) ^ 2 - b ^ 3) / c ^ 3 := by
          field_simp
        rw [e]
        exact div_pos (by linarith) (by positivity))
  exact ⟨1 / (q : ℝ), one_div_pos.mpr (Nat.cast_pos.mpr hq), M, C.toCongruentDissection T hC1, hiso, hang,
    by show C.model.Congruent _; rw [hC2]; exact Tri.Congruent.refl _⟩

/-- **Beeson Corollary 5** (natural-number tile form; see the header for what is and is not covered). -/
theorem cor5 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (h : a * a + c * b = c * c)
    (hg : Nat.gcd (Nat.gcd a b) c = 1) (R : RTri)
    (hRa : R.a = (a : ℚ)) (hRb : R.b = (b : ℚ)) (hRc : R.c = (c : ℚ)) :
    ∃ (s : ℝ) (hs : 0 < s) (N : ℕ) (D : CongruentDissection N),
      dist (D.target.pts 2) (D.target.pts 0) = dist (D.target.pts 2) (D.target.pts 1) ∧
      cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1)
        = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) ∧
      D.model.Congruent (scaleTri s hs.ne' R.Δ) := by
  have hcpos : 0 < c := by rcases Nat.eq_zero_or_pos c with h0 | h0 <;> [(subst h0; simp at h; omega); exact h0]
  have hbc : b < c := by
    by_contra hcon
    push_neg at hcon
    have : c * c ≤ c * b := Nat.mul_le_mul_left c hcon
    nlinarith
  have hsub : a * a = c * (c - b) := by
    obtain ⟨d, hd⟩ : ∃ d, c = b + d := ⟨c - b, by omega⟩
    subst hd; rw [Nat.add_sub_cancel_left]; nlinarith
  rcases Erdos634.BeesonLemma52.lemma52 a b c hb hbc hsub with ⟨h1, _⟩ | ⟨h2, _⟩
  · -- (i): `b^3 < c (c-b)^2`
    have hhR : (a : ℝ) ^ 2 = c * (c - b) := by
      have : ((a * a : ℕ) : ℝ) = ((c * (c - b) : ℕ) : ℝ) := by rw [hsub]
      push_cast [Nat.cast_sub hbc.le] at this; nlinarith [this]
    have hcR : (0 : ℝ) < c := Nat.cast_pos.mpr hcpos
    have hbR : (0 : ℝ) < b := Nat.cast_pos.mpr hb
    refine cor5_fourth a b c ha hb hbc h ?_ R hRa hRb hRc
    rw [hhR] at h1
    rw [← sub_pos] at h1
    have e : (c * (c - b) / b + b - (c + b ^ 2 / c) : ℝ) = (c * (c - b) ^ 2 - b ^ 3) / (b * c) := by
      field_simp; ring
    rw [e] at h1
    have := (div_pos_iff_of_pos_right (by positivity)).mp h1
    linarith
  · have hlt : a * a * c < b * (a * a + b * b) := by exact_mod_cast (by nlinarith [h2] : (a : ℝ) * a * c < b * (a * a + b * b))
    exact cor5_thm24 a b c ha hb h hg hlt R hRa hRb hRc

/-! ### Rational tiles: rescale to coprime naturals (`Cor 5` for every `RTri` with `3 alpha + 2 beta = pi`) -/

theorem angle_scale (T : Tri) (r : ℝ) (hr : 0 < r) (i j k : Fin 3) (hij : i ≠ j) (hkj : k ≠ j) :
    cornerAngle ((scaleTri r hr.ne' T).pts i) ((scaleTri r hr.ne' T).pts j) ((scaleTri r hr.ne' T).pts k)
      = cornerAngle (T.pts i) (T.pts j) (T.pts k) := by
  have hd : ∀ x y : Fin 3, dist ((scaleTri r hr.ne' T).pts x) ((scaleTri r hr.ne' T).pts y)
      = r * dist (T.pts x) (T.pts y) := by
    intro x y
    simp only [scaleTri_pts]
    rw [Erdos634.Realizable.dist_homothety, abs_of_pos hr]
  have hne : ∀ x y : Fin 3, x ≠ y → dist (T.pts x) (T.pts y) ≠ 0 := fun x y hxy =>
    dist_ne_zero.mpr (fun he => hxy (T.indep.injective he))
  have c1 := Erdos634.AngleThreshold.cos_of_sides ((scaleTri r hr.ne' T).pts i) ((scaleTri r hr.ne' T).pts j)
    ((scaleTri r hr.ne' T).pts k) (by rw [hd]; exact mul_ne_zero hr.ne' (hne _ _ hij))
    (by rw [hd]; exact mul_ne_zero hr.ne' (hne _ _ hkj))
  have c2 := Erdos634.AngleThreshold.cos_of_sides (T.pts i) (T.pts j) (T.pts k) (hne _ _ hij) (hne _ _ hkj)
  have hik : dist (T.pts i) (T.pts k) = dist (T.pts i) (T.pts k) := rfl
  have hcos : Real.cos (cornerAngle ((scaleTri r hr.ne' T).pts i) ((scaleTri r hr.ne' T).pts j)
      ((scaleTri r hr.ne' T).pts k)) = Real.cos (cornerAngle (T.pts i) (T.pts j) (T.pts k)) := by
    rw [c1, c2, hd, hd, hd]
    have h1 := hne _ _ hij
    have h2 := hne _ _ hkj
    field_simp
  exact Real.injOn_cos ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩ hcos

theorem rat_scale (a b c : ℚ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∃ (A B C : ℕ) (k : ℚ), 0 < k ∧ 0 < A ∧ 0 < B ∧ 0 < C ∧ a = k * A ∧ b = k * B ∧ c = k * C ∧
      Nat.gcd (Nat.gcd A B) C = 1 := by
  have key : ∀ x : ℚ, 0 < x → ∃ n : ℕ, (x.num : ℚ) = n ∧ 0 < n := by
    intro x hx
    have : 0 < x.num := Rat.num_pos.mpr hx
    exact ⟨x.num.toNat, by exact_mod_cast (Int.toNat_of_nonneg this.le).symm, by omega⟩
  obtain ⟨na, hna, hna0⟩ := key a ha
  obtain ⟨nb, hnb, hnb0⟩ := key b hb
  obtain ⟨nc, hnc, hnc0⟩ := key c hc
  set d : ℕ := a.den * b.den * c.den with hd
  have hdpos : 0 < d := Nat.mul_pos (Nat.mul_pos a.den_pos b.den_pos) c.den_pos
  set A0 : ℕ := na * (b.den * c.den) with hA0
  set B0 : ℕ := nb * (a.den * c.den) with hB0
  set C0 : ℕ := nc * (a.den * b.den) with hC0
  have eA : a = (A0 : ℚ) / d := by
    have := Rat.num_div_den a
    rw [← this]; simp only [hA0, hd, hna]; push_cast
    have := a.den_pos; have := b.den_pos; have := c.den_pos
    field_simp
  have eB : b = (B0 : ℚ) / d := by
    have := Rat.num_div_den b
    rw [← this]; simp only [hB0, hd, hnb]; push_cast
    have := a.den_pos; have := b.den_pos; have := c.den_pos
    field_simp
  have eC : c = (C0 : ℚ) / d := by
    have := Rat.num_div_den c
    rw [← this]; simp only [hC0, hd, hnc]; push_cast
    have := a.den_pos; have := b.den_pos; have := c.den_pos
    field_simp
  have hA0p : 0 < A0 := Nat.mul_pos hna0 (Nat.mul_pos b.den_pos c.den_pos)
  have hB0p : 0 < B0 := Nat.mul_pos hnb0 (Nat.mul_pos a.den_pos c.den_pos)
  have hC0p : 0 < C0 := Nat.mul_pos hnc0 (Nat.mul_pos a.den_pos b.den_pos)
  set g : ℕ := Nat.gcd (Nat.gcd A0 B0) C0 with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (Nat.gcd_pos_of_pos_left _ hA0p)
  have gA : g ∣ A0 := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  have gB : g ∣ B0 := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  have gC : g ∣ C0 := Nat.gcd_dvd_right _ _
  refine ⟨A0 / g, B0 / g, C0 / g, (g : ℚ) / d, by positivity, Nat.div_pos (Nat.le_of_dvd hA0p gA) hgpos,
    Nat.div_pos (Nat.le_of_dvd hB0p gB) hgpos, Nat.div_pos (Nat.le_of_dvd hC0p gC) hgpos, ?_, ?_, ?_, ?_⟩
  · rw [eA]; have := Nat.div_mul_cancel gA; field_simp
    have h2 : ((A0 / g : ℕ) : ℚ) * g = A0 := by exact_mod_cast this
    linarith
  · rw [eB]; have := Nat.div_mul_cancel gB; field_simp
    have h2 : ((B0 / g : ℕ) : ℚ) * g = B0 := by exact_mod_cast this
    linarith
  · rw [eC]; have := Nat.div_mul_cancel gC; field_simp
    have h2 : ((C0 / g : ℕ) : ℚ) * g = C0 := by exact_mod_cast this
    linarith
  · rw [Nat.gcd_div gA gB, Nat.gcd_div (Nat.dvd_gcd gA gB) gC]
    exact Nat.div_self hgpos

/-- **Cor 5 for every rational tile.**  `R : RTri` has rational sides; `3 alpha + 2 beta = pi` is `b c = c^2 - a^2`. -/
theorem cor5_rational (R : RTri) (hrel : R.b * R.c = R.c ^ 2 - R.a ^ 2) :
    ∃ (s : ℝ) (hs : 0 < s) (N : ℕ) (D : CongruentDissection N),
      dist (D.target.pts 2) (D.target.pts 0) = dist (D.target.pts 2) (D.target.pts 1) ∧
      cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1)
        = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) ∧
      D.model.Congruent (scaleTri s hs.ne' R.Δ) := by
  obtain ⟨A, B, C, k, hk, hA, hB, hC, ea, eb, ec, hg⟩ := rat_scale R.a R.b R.c R.pa R.pb R.pc
  have hkR : (0 : ℝ) < ((1 / k : ℚ) : ℝ) := by exact_mod_cast (by positivity : (0 : ℚ) < 1 / k)
  have hk1 : (0 : ℝ) < 1 / (k : ℝ) := by exact_mod_cast (by positivity : (0 : ℚ) < 1 / k)
  have hkne : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hh : A * A + C * B = C * C := by
    have : (A : ℚ) * A + C * B = C * C := by
      have h1 : k ^ 2 * (B * C) = k ^ 2 * (C ^ 2 - A ^ 2) := by
        have := hrel; rw [ea, eb, ec] at this; nlinarith [this]
      have hk2 : k ^ 2 ≠ 0 := by positivity
      have := mul_left_cancel₀ hk2 h1
      nlinarith [this]
    exact_mod_cast this
  let R1 : RTri :=
    { Δ := scaleTri (1 / (k : ℝ)) hk1.ne' R.Δ
      a := A
      b := B
      c := C
      ha := by
        simp only [scaleTri_pts]
        rw [Erdos634.Realizable.dist_homothety, abs_of_pos hk1, R.ha, ea]
        push_cast; field_simp
      hb := by
        simp only [scaleTri_pts]
        rw [Erdos634.Realizable.dist_homothety, abs_of_pos hk1, R.hb, eb]
        push_cast; field_simp
      hc := by
        simp only [scaleTri_pts]
        rw [Erdos634.Realizable.dist_homothety, abs_of_pos hk1, R.hc, ec]
        push_cast; field_simp
      pa := by exact_mod_cast hA
      pb := by exact_mod_cast hB
      pc := by exact_mod_cast hC }
  obtain ⟨s, hs, N, D, h1, h2, h3⟩ := cor5 A B C hA hB hh hg R1 rfl rfl rfl
  refine ⟨s * (1 / (k : ℝ)), mul_pos hs hk1, N, D, h1, ?_, ?_⟩
  · rw [h2]
    exact angle_scale R.Δ _ hk1 1 0 2 (by decide) (by decide)
  · rw [← scaleTri_scaleTri s _ hs.ne' hk1.ne' (mul_pos hs hk1).ne']
    exact h3

/-! ### Witnesses: every hypothesis holds; `RTri`s with sides `(2,3,4)`, `(3,8,9)` come from `beeson_thm24_exists`. -/

theorem exists_RTri (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (h : a * a + c * b = c * c)
    (hg : Nat.gcd a b = 1) (hlt : a * a * c < b * (a * a + b * b)) :
    ∃ R : RTri, R.a = (a : ℚ) ∧ R.b = (b : ℚ) ∧ R.c = (c : ℚ) := by
  obtain ⟨lam, n, T, x0, y0, x1, y1, x2, y2, hd, hl, t1, t2, t3, -⟩ := beeson_thm24_exists a b c ha hb h hg hlt
  have hcpos : 0 < c := by rcases Nat.eq_zero_or_pos c with h0 | h0 <;> [(subst h0; simp at h; omega); exact h0]
  have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have hbR : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have hcR : (0 : ℝ) < c := Nat.cast_pos.mpr hcpos
  refine ⟨⟨T, a, b, c, ?_, ?_, ?_, by exact_mod_cast ha, by exact_mod_cast hb, by exact_mod_cast hcpos⟩, rfl, rfl, rfl⟩
  · simpa using eq_of_sq_eq' dist_nonneg haR.le t3
  · rw [dist_comm]; simpa using eq_of_sq_eq' dist_nonneg hbR.le t2
  · simpa using eq_of_sq_eq' dist_nonneg hcR.le t1

theorem cor5_wit_234 : ∃ R : RTri, R.a = 2 ∧ R.b = 3 ∧ R.c = 4 ∧
    ∃ (s : ℝ) (hs : 0 < s) (N : ℕ) (D : CongruentDissection N),
      dist (D.target.pts 2) (D.target.pts 0) = dist (D.target.pts 2) (D.target.pts 1) ∧
      cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1)
        = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) ∧
      D.model.Congruent (scaleTri s hs.ne' R.Δ) := by
  obtain ⟨R, h1, h2, h3⟩ := exists_RTri 2 3 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨R, by simpa using h1, by simpa using h2, by simpa using h3,
    cor5 2 3 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) R h1 h2 h3⟩

theorem cor5_wit_389 : ∃ R : RTri, R.a = 3 ∧ R.b = 8 ∧ R.c = 9 ∧
    ∃ (s : ℝ) (hs : 0 < s) (N : ℕ) (D : CongruentDissection N),
      dist (D.target.pts 2) (D.target.pts 0) = dist (D.target.pts 2) (D.target.pts 1) ∧
      cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1)
        = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) ∧
      D.model.Congruent (scaleTri s hs.ne' R.Δ) := by
  obtain ⟨R, h1, h2, h3⟩ := exists_RTri 3 8 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨R, by simpa using h1, by simpa using h2, by simpa using h3,
    cor5 3 8 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) R h1 h2 h3⟩

/-- `(12, 7, 16)`: outside Thm 24 (`2304 > 1351`), inside the fourth-triple branch (`343 < 16 * 81`). -/
theorem cor5_wit_12716 :
    ∃ (s : ℝ) (hs : 0 < s) (N : ℕ) (D : CongruentDissection N),
      dist (D.target.pts 2) (D.target.pts 0) = dist (D.target.pts 2) (D.target.pts 1) ∧
      cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1)
        = cornerAngle (R12716.Δ.pts 1) (R12716.Δ.pts 0) (R12716.Δ.pts 2) ∧
      D.model.Congruent (scaleTri s hs.ne' R12716.Δ) :=
  cor5 12 7 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) R12716 (by simp [R12716]) (by simp [R12716])
    (by simp [R12716])

theorem not_thm24_12716 : ¬ (12 * 12 * 16 < 7 * (12 * 12 + 7 * 7)) := by norm_num

#print axioms cor5
#print axioms cor5_wit_234
#print axioms cor5_wit_389
#print axioms cor5_wit_12716
#print axioms cor5_rational

end Erdos634.BeesonCor5
