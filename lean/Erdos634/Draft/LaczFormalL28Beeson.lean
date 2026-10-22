import Erdos634.Draft.BeesonCor5
import Erdos634.Draft.LaczFormalTransport

/-!
# Beeson Theorem 24 as a rational similar dissection of every isosceles triangle with rational legs

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.4, Fig. 5), Beeson (arXiv 1206.2229,
Theorem 24, Lemma 52), Beeson-Zhang, Zhang.

`BeesonCor5.cor5_thm24` hides the size `mu = lam a b (a+c)` of Beeson's triangle.  Here it is exposed
(`thm24_ratio`), made rational for every rational tile (`thm24_rational`), and the tiling is moved to ANY triangle
`T'` isosceles at `T'₂` with apex angle `α` and RATIONAL legs (`ratsim_iso_beeson`): the result is a `RatSimDiss`
(Laczkovich's vocabulary of `LaczFormalL22Base`), exactly what the fan constructions of Fig. 5 need for the
complementary range `N(a₀) < 0` of the fourth-triple triangle.  Range: `R.a^4 < R.b^3 R.c` (equivalently
`a² c < b (a² + b²)`, Beeson's hypothesis of Theorem 24).
-/

namespace Erdos634.LaczL28

open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.ZhangPara Erdos634.ZhangSporadic
  Erdos634.LaczL22 Erdos634.BeesonT24Exists Erdos634.Realizable Erdos634.LaczL24 Erdos634.BeesonCor5
  Erdos634.DissectionMap Erdos634.TranslateDissection Erdos634.Ladder Erdos634.SssCongruent
  Erdos634.LaczTransport EuclideanGeometry

/-- `transport_similar` with the similarity ratio exposed. -/
theorem transport_similar_ratio {N : ℕ} (D : CongruentDissection N) (T' : Tri) (a b c : Fin 3)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h1 : ∠ (D.target.pts a) (D.target.pts b) (D.target.pts c) = ∠ (T'.pts a) (T'.pts b) (T'.pts c))
    (h2 : ∠ (D.target.pts b) (D.target.pts c) (D.target.pts a) = ∠ (T'.pts b) (T'.pts c) (T'.pts a)) :
    ∃ (r : ℝ) (hr : 0 < r) (D' : CongruentDissection N),
      D'.target.carrier = T'.carrier ∧ D'.model.Congruent (scaleTri r hr.ne' D.model) ∧
      ∀ x y, dist (T'.pts x) (T'.pts y) = r * dist (D.target.pts x) (D.target.pts y) := by
  obtain ⟨r, hr, hdist⟩ := sim_of_angles D.target T' a b c hab hbc hac h1 h2
  set p : Plane := D.target.pts 0 with hp
  set hom := homothetyEquiv p r hr.ne' with hhom
  have hU : (mapTri hom D.target).Congruent T' := by
    refine congruent_of_dist (fun i j => ?_)
    show dist (hom (D.target.pts i)) (hom (D.target.pts j)) = _
    rw [hhom, homothetyEquiv_dist, abs_of_pos hr, hdist]
  obtain ⟨f, σ, hf⟩ := hU
  let D₁ := scaleDissection p r hr.ne' D
  let g : Plane ≃ᵃⁱ[ℝ] Plane := f.toRealAffineIsometryEquiv
  refine ⟨r, hr, isoCongruentDissection g D₁, ?_, ?_, hdist⟩
  · rw [iso_target, mapTri_carrier]
    show g.toAffineEquiv '' (mapTri hom D.target).carrier = T'.carrier
    rw [← mapTri_carrier]
    simp only [Tri.carrier, mapTri]
    have hpts : (g.toAffineEquiv ∘ (hom ∘ D.target.pts)) = T'.pts ∘ σ := by
      funext k
      exact hf k
    rw [hpts, Function.Surjective.range_comp σ.surjective]
  · rw [iso_model]
    refine congruent_of_dist (fun i j => ?_)
    show dist (hom (D.model.pts i)) (hom (D.model.pts j)) = dist ((scaleTri r hr.ne' D.model).pts i)
      ((scaleTri r hr.ne' D.model).pts j)
    rw [hhom, homothetyEquiv_dist, scaleTri_pts, scaleTri_pts, dist_homothety]

theorem congr_scale {X Y : Tri} (h : X.Congruent Y) (r : ℝ) (hr : 0 < r) :
    (scaleTri r hr.ne' X).Congruent (scaleTri r hr.ne' Y) := by
  obtain ⟨σ, hσ⟩ := h.dist_eq
  refine congruent_of_dist_perm σ (fun i j => ?_)
  simp only [scaleTri_pts]
  rw [Erdos634.Realizable.dist_homothety, Erdos634.Realizable.dist_homothety, abs_of_pos hr, hσ i j]

theorem scaleTri_congr (T : Tri) {r s : ℝ} (h : r = s) (hr : r ≠ 0) (hs : s ≠ 0) :
    scaleTri r hr T = scaleTri s hs T := by
  subst h; rfl

/-- Beeson Thm 24 for a natural-number tile, with the size `m c` of the legs exposed. -/
theorem thm24_ratio (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (h : a * a + c * b = c * c)
    (hg : Nat.gcd a b = 1) (hlt : a * a * c < b * (a * a + b * b)) (R : RTri)
    (hRa : R.a = (a : ℚ)) (hRb : R.b = (b : ℚ)) (hRc : R.c = (c : ℚ)) :
    ∃ (m : ℕ) (N : ℕ) (D : CongruentDissection N), 0 < m ∧
      dist (D.target.pts 2) (D.target.pts 0) = (m : ℝ) * c ∧
      dist (D.target.pts 2) (D.target.pts 1) = (m : ℝ) * c ∧
      cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1)
        = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) ∧
      D.model.Congruent (scaleTri 1 one_ne_zero R.Δ) := by
  obtain ⟨lam, n, T, x0, y0, x1, y1, x2, y2, hd, hl, t1, t2, t3, s1, s2, s3, hD⟩ :=
    beeson_thm24_exists a b c ha hb h hg hlt
  obtain ⟨C, hr, hm⟩ := hD
  have hcpos : 0 < c := by rcases Nat.eq_zero_or_pos c with h0 | h0 <;> [(subst h0; simp at h; omega); exact h0]
  set mu : ℝ := ((lam * a * b * (a + c) : ℕ) : ℝ) with hmu
  have hmpos : 0 < lam * a * b * (a + c) := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hl ha) hb) (by omega)
  have hmupos : 0 < mu := by rw [hmu]; exact_mod_cast hmpos
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
  have l02 : dist (T'.pts 0) (T'.pts 2) = mu * c := eq_of_sq_eq' dist_nonneg (by positivity) e02
  have l12 : dist (T'.pts 1) (T'.pts 2) = mu * c := eq_of_sq_eq' dist_nonneg (by positivity) e12
  refine ⟨lam * a * b * (a + c), n, C.toCongruentDissection T' (hr.trans (TriSet_eq_carrier hd)), hmpos, ?_, ?_, ?_, ?_⟩
  · show dist (T'.pts 2) (T'.pts 0) = _
    rw [dist_comm]; exact l02
  · show dist (T'.pts 2) (T'.pts 1) = _
    rw [dist_comm]; exact l12
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

/-- Beeson Thm 24 for every rational tile with `3α + 2β = π` and `a^4 < b^3 c` (the complementary range of the
fourth triple): an isosceles triangle with rational legs `ℓ0`, apex angle `α`, tiled by copies of `scaleTri κ Δ`, `κ`
rational. -/
theorem thm24_rational (R : RTri) (hrel : R.b * R.c = R.c ^ 2 - R.a ^ 2) (hlt : R.a ^ 4 < R.b ^ 3 * R.c) :
    ∃ (κ ℓ0 : ℚ) (hκ : 0 < κ) (_ : 0 < ℓ0) (N : ℕ) (D : CongruentDissection N),
      dist (D.target.pts 2) (D.target.pts 0) = (ℓ0 : ℝ) ∧
      dist (D.target.pts 2) (D.target.pts 1) = (ℓ0 : ℝ) ∧
      cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1)
        = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) ∧
      D.model.Congruent (scaleTri (κ : ℝ) (by exact_mod_cast hκ.ne') R.Δ) := by
  obtain ⟨A, B, C, k, hk, hA, hB, hC, ea, eb, ec, hg⟩ := rat_scale R.a R.b R.c R.pa R.pb R.pc
  have hk1 : (0 : ℝ) < 1 / (k : ℝ) := by exact_mod_cast (by positivity : (0 : ℚ) < 1 / k)
  have hhQ : (A : ℚ) * A + C * B = C * C := by
    have h1 : k ^ 2 * (B * C) = k ^ 2 * (C ^ 2 - A ^ 2) := by
      have := hrel; rw [ea, eb, ec] at this; nlinarith [this]
    have hk2 : k ^ 2 ≠ 0 := by positivity
    have := mul_left_cancel₀ hk2 h1
    nlinarith [this]
  have hh : A * A + C * B = C * C := by exact_mod_cast hhQ
  have hg2 := gcd_ab_of_three A B C hh hg
  -- Beeson's inequality
  have hq4 : (A : ℚ) ^ 4 < (B : ℚ) ^ 3 * C := by
    have e1 : (k * A) ^ 4 = k ^ 4 * (A : ℚ) ^ 4 := by ring
    have e2 : (k * B) ^ 3 * (k * C) = k ^ 4 * ((B : ℚ) ^ 3 * C) := by ring
    rw [ea, eb, ec, e1, e2] at hlt
    exact lt_of_mul_lt_mul_left hlt (by positivity)
  have hCQ : (0 : ℚ) < C := by exact_mod_cast hC
  have hkey : (C : ℚ) * ((B : ℚ) * (A * A + B * B) - A * A * C) = (B : ℚ) ^ 3 * C - (A : ℚ) ^ 4 := by
    linear_combination ((A : ℚ) * A) * hhQ
  have hltQ : (A : ℚ) * A * C < B * (A * A + B * B) := by
    have : 0 < (C : ℚ) * ((B : ℚ) * (A * A + B * B) - A * A * C) := by rw [hkey]; linarith
    have := (mul_pos_iff_of_pos_left hCQ).mp this
    linarith
  have hlt' : A * A * C < B * (A * A + B * B) := by exact_mod_cast hltQ
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
  obtain ⟨m, N, D, hm, d1, d2, hap, hmod⟩ := thm24_ratio A B C hA hB hh hg2 hlt' R1 rfl rfl rfl
  have hκ : (0 : ℚ) < 1 / k := by positivity
  have hℓ : (0 : ℚ) < (m : ℚ) * C := by positivity
  refine ⟨1 / k, (m : ℚ) * C, hκ, hℓ, N, D, ?_, ?_, ?_, ?_⟩
  · rw [d1]; push_cast; ring
  · rw [d2]; push_cast; ring
  · rw [hap]
    exact angle_scale R.Δ _ hk1 1 0 2 (by decide) (by decide)
  · have e : scaleTri (1 : ℝ) one_ne_zero R1.Δ = scaleTri (((1 / k : ℚ)) : ℝ) (by exact_mod_cast hκ.ne') R.Δ := by
      show scaleTri 1 one_ne_zero (scaleTri (1 / (k : ℝ)) hk1.ne' R.Δ) = _
      rw [scaleTri_scaleTri 1 _ one_ne_zero hk1.ne' (by simpa using hk1.ne')]
      exact scaleTri_congr R.Δ (by push_cast; ring) _ _
    rw [← e]; exact hmod

/-- **Beeson Theorem 24 as a rational similar dissection of an arbitrary isosceles triangle with rational legs.**
`R` rational tile, `3α + 2β = π` (`b c = c² - a²`), `a⁴ < b³ c`; `T'` isosceles at `T'₂` with apex angle `α` and legs of
rational length `ℓ`.  Then `T'` is the union of finitely many rational triangles similar to `Δ`. -/
theorem ratsim_iso_beeson (R : RTri) (hrel : R.b * R.c = R.c ^ 2 - R.a ^ 2) (hlt : R.a ^ 4 < R.b ^ 3 * R.c)
    (T' : Tri) (hiso : dist (T'.pts 2) (T'.pts 0) = dist (T'.pts 2) (T'.pts 1))
    (hang : cornerAngle (T'.pts 0) (T'.pts 2) (T'.pts 1)
      = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2))
    (ℓ : ℚ) (hℓ : 0 < ℓ) (hdist : dist (T'.pts 2) (T'.pts 0) = (ℓ : ℝ)) :
    RatSimDiss R.Δ T'.carrier := by
  obtain ⟨κ, ℓ0, hκ, hℓ0, N, D, d1, d2, hap, hmod⟩ := thm24_rational R hrel hlt
  have hiso0 : dist (D.target.pts 2) (D.target.pts 0) = dist (D.target.pts 2) (D.target.pts 1) := d1.trans d2.symm
  have hT := Erdos634.LaczTransport.base_angle D.target hiso0
  have hT' := Erdos634.LaczTransport.base_angle T' hiso
  obtain ⟨r, hr, D', e1, e2, e3⟩ := transport_similar_ratio D T' 0 2 1 (by decide) (by decide) (by decide)
    (hap.trans hang.symm)
    (by
      have h1 : cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1)
          = cornerAngle (T'.pts 0) (T'.pts 2) (T'.pts 1) := hap.trans hang.symm
      unfold cornerAngle at h1
      linarith)
  have hrℓ : (ℓ : ℝ) = r * (ℓ0 : ℝ) := by
    have := e3 2 0
    rw [hdist, d1] at this
    exact this
  have hℓ0r : (0 : ℝ) < (ℓ0 : ℝ) := by exact_mod_cast hℓ0
  have hrq : r = ((ℓ / ℓ0 : ℚ) : ℝ) := by
    push_cast
    field_simp
    linarith
  set k : ℚ := ℓ / ℓ0 * κ with hkdef
  have hk : 0 < k := by positivity
  have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hmodel : D'.model.Congruent (scaleTri (k : ℝ) hkr.ne' R.Δ) := by
    have h1 := (congr_scale hmod r hr)
    have e : scaleTri r hr.ne' (scaleTri (κ : ℝ) (by exact_mod_cast hκ.ne') R.Δ) = scaleTri (k : ℝ) hkr.ne' R.Δ := by
      rw [scaleTri_scaleTri r _ hr.ne' (by exact_mod_cast hκ.ne') (mul_pos hr (by exact_mod_cast hκ)).ne']
      exact scaleTri_congr R.Δ (by rw [hrq, hkdef]; push_cast; ring) _ _
    exact e2.trans (e ▸ h1)
  refine ⟨Fin N, inferInstance, D'.tile, D'.covers.trans e1, fun i j hij => D'.interiors_disjoint hij, fun i => ?_⟩
  exact ratSimTile_of_cong R.rational k hk ((D'.tiles_congruent i).trans hmodel)

#print axioms ratsim_iso_beeson

end Erdos634.LaczL28
