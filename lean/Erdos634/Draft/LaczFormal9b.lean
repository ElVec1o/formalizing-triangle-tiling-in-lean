import Erdos634.Draft.LaczFormal9a
import Erdos634.Draft.LaczFormalL6Wit1
import Erdos634.Draft.ZhangRegionDilate
import Erdos634.Draft.FluxCRow5
import Erdos634.Draft.FluxCRow2
import Erdos634.TriLawSin

/-!
# Laczkovich, Discrete Math. 140 (1995), Theorem 3.3 (the count `|x y (x+2y)(y+2x)| k^2`)

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) Thm 3.1, Lemma 2.1, Lemma 3.2, Thm 3.3), Beeson, Beeson-Zhang, Zhang
(the natural dilation `ZhangRegionDilate.dilate_region`).  Formalization debt, not progress on the /goal outcomes.

Printed Theorem 3.3: `x, y` non-zero integers with `x + 2y != 0 != y + 2x`.  Then there is a positive integer `k` such that the
equilateral triangle can be dissected into `n = |x y (x+2y)(y+2x)| k^2` congruent triangles.  (The tile is the triangle `Delta`
of sides `a = |x(x+2y)|, b = |y(y+2x)|, c = x^2+xy+y^2` of Lemma 3.2; the proof applies Theorem 3.1, then dilates by `a b`.)

* `equi_count`: area/Heron identity of an equilateral `CongruentDissection` whose model has the Heron value `3 (p q)^2`:
  `L^2 = N p q` (L = target side).
* `equi_n_formula`: with model sides `(u, v, w)/q`, naturals, the side `L = n/q` is a natural combination (side walk) and
  `M * (A B) = n^2`.
* `dilate_equi`: an equilateral `CongruentDissection` dilates by a natural `k` to an equilateral one with `k*k*M` tiles, same model.
* `dm140_thm33`: the printed statement (any N and tile positions; `D.model` has sides `s (a, b, c)` in some order).
-/

open scoped Classical
open EuclideanGeometry Erdos634.Geometry Erdos634.RegionDissection Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
  Erdos634.Draft.LaczFormal Erdos634.LaczL35 Erdos634.LaczL22 Erdos634.CertCoord Erdos634.LaczThm33If
  Erdos634.Realizable Erdos634.DissectionMap

namespace Erdos634.Laczkovich9

theorem scaleTri_oppLen (r : ℝ) (hr : r ≠ 0) (T : Tri) (j : Fin 3) :
    (scaleTri r hr T).oppLen j = |r| * T.oppLen j := by
  unfold Tri.oppLen
  simp only [scaleTri_pts]
  rw [Erdos634.Realizable.dist_homothety]

theorem mapHom_oppLen (p : Plane) (r : ℝ) (hr : r ≠ 0) (T : Tri) (j : Fin 3) :
    (mapTri (homothetyEquiv p r hr) T).oppLen j = |r| * T.oppLen j := by
  unfold Tri.oppLen
  show dist (homothetyEquiv p r hr (T.pts (j + 1))) (homothetyEquiv p r hr (T.pts (j + 2))) = _
  rw [homothetyEquiv_dist]

/-- A triangle with all angles `pi/3` has three equal sides. -/
theorem equi_oppLen (T : Tri) (h : ∀ k, T.angleAt k = Real.pi / 3) (j : Fin 3) : T.oppLen j = T.oppLen 0 := by
  have s0 := Erdos634.TriLawSin.sin_angleAt_mul_sideOpp T 0
  have s1 := Erdos634.TriLawSin.sin_angleAt_mul_sideOpp T 1
  have hs : 0 < Real.sin (Real.pi / 3) := by rw [Real.sin_pi_div_three]; positivity
  have e01 : (0 : Fin 3) + 1 = 1 := rfl
  have e12 : (1 : Fin 3) + 1 = 2 := rfl
  have h' : ∀ k, angleAt T k = Real.pi / 3 := h
  rw [e01, h' 1, h' 0] at s0
  rw [e12, h' 2, h' 1] at s1
  have a01 : T.oppLen 0 = T.oppLen 1 := (mul_left_cancel₀ hs.ne' s0)
  have a12 : T.oppLen 1 = T.oppLen 2 := (mul_left_cancel₀ hs.ne' s1)
  fin_cases j
  · rfl
  · exact a01.symm
  · exact a12.symm.trans a01.symm

/-- **Area identity.**  An equilateral target, a model whose Heron value is `3 (p q)^2`: `L^2 = N p q`. -/
theorem equi_count {N : ℕ} (D : CongruentDissection N) (hEq : ∀ k, D.target.angleAt k = Real.pi / 3)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hH : (∑ k, D.model.oppLen k ^ 2) ^ 2 - 2 * ∑ k, D.model.oppLen k ^ 4 = 3 * (p * q) ^ 2) :
    D.target.oppLen 0 ^ 2 = N * (p * q) := by
  set L := D.target.oppLen 0 with hLdef
  have hL : ∀ j, D.target.oppLen j = L := fun j => equi_oppLen D.target hEq j
  have hLpos : 0 < L := D.target.oppLen_pos 0
  have ht := D.target.four_detTri_sq_sym
  have hm := D.model.four_detTri_sq_sym
  have hdet := D.abs_detTri_target
  have hd2 : Erdos634.AreaDet.detTri D.target ^ 2 = (N : ℝ) ^ 2 * Erdos634.AreaDet.detTri D.model ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hdet
    simp only [mul_pow, sq_abs] at h
    exact h
  simp only [Fin.sum_univ_three, hL] at ht
  have e1 : 4 * Erdos634.AreaDet.detTri D.target ^ 2 = 3 * L ^ 4 := by rw [ht]; ring
  have e2 : 4 * Erdos634.AreaDet.detTri D.model ^ 2 = 3 * (p * q) ^ 2 := by rw [hm]; exact hH
  have h3 : 3 * L ^ 4 = 3 * ((N : ℝ) * (p * q)) ^ 2 := by
    rw [← e1, hd2]
    linear_combination (N : ℝ) ^ 2 * e2
  have h4 : (L ^ 2) ^ 2 = ((N : ℝ) * (p * q)) ^ 2 := by nlinarith [h3]
  have hpq : 0 ≤ (N : ℝ) * (p * q) := by positivity
  exact (pow_left_inj₀ (by positivity) hpq two_ne_zero).mp h4

/-- From a rational similar dissection of an equilateral `T`: an equilateral `CongruentDissection` whose model sides are
`(1/q)` times the sides of `R`. -/
theorem equi_model (R : RTri) (T : Tri) (h : RatSimDiss R.Δ T.carrier)
    (a0 : cornerAngle (T.pts 1) (T.pts 0) (T.pts 2) = Real.pi / 3)
    (a1 : cornerAngle (T.pts 2) (T.pts 1) (T.pts 0) = Real.pi / 3)
    (a2 : cornerAngle (T.pts 0) (T.pts 2) (T.pts 1) = Real.pi / 3) :
    ∃ (q : ℕ) (_ : 0 < q) (M : ℕ) (D : CongruentDissection M), Equilateral D ∧
      ∀ j, D.model.oppLen j = (1 / (q : ℝ)) * R.Δ.oppLen j := by
  obtain ⟨q, hq, M, C, hC1, hC2⟩ := RatSimDiss.toCongruent R.rational h
  refine ⟨q, hq, M, C.toCongruentDissection T hC1, ?_, ?_⟩
  · intro k
    have htri : ∀ y : Fin 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide
    rcases htri k with rfl | rfl | rfl
    · exact a0
    · exact a1
    · exact a2
  · intro j
    show C.model.oppLen j = _
    rw [hC2, scaleTri_oppLen, abs_of_pos (one_div_pos.mpr (Nat.cast_pos.mpr hq))]

/-- The side count: model sides `(u, v, w)/q` (naturals), Heron value `3 (A B)^2`, equilateral target:
`M * (A * B) = n^2` with `n` a positive natural. -/
theorem equi_n_formula {M : ℕ} (D : CongruentDissection M) (hEq : Equilateral D) (q : ℕ) (hq : 0 < q)
    (u v w A B : ℕ) (hA : 0 < A) (hB : 0 < B)
    (h0 : D.model.oppLen 0 = (u : ℝ) / q) (h1 : D.model.oppLen 1 = (v : ℝ) / q)
    (h2 : D.model.oppLen 2 = (w : ℝ) / q)
    (hH : ((u : ℝ) ^ 2 + v ^ 2 + w ^ 2) ^ 2 - 2 * ((u : ℝ) ^ 4 + v ^ 4 + w ^ 4) = 3 * ((A : ℝ) * B) ^ 2) :
    ∃ n : ℕ, 0 < n ∧ M * (A * B) = n ^ 2 := by
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hAR : (0 : ℝ) < A := Nat.cast_pos.mpr hA
  have hBR : (0 : ℝ) < B := Nat.cast_pos.mpr hB
  have hcount := equi_count D hEq ((A : ℝ) / q) ((B : ℝ) / q) (by positivity) (by positivity) (by
    simp only [Fin.sum_univ_three, h0, h1, h2]
    field_simp
    linear_combination (q : ℝ) ^ 4 * hH * 0 + hH)
  -- the side walk along the side from vertex 0 to vertex 1
  obtain ⟨P, Q, S, hPQS, -⟩ := Erdos634.EdgeWordConversion.side_walk_congruent D 0
  have s0 : Erdos634.EdgeWordConversion.sideLen D 0 = D.model.oppLen 2 := rfl
  have s1 : Erdos634.EdgeWordConversion.sideLen D 1 = D.model.oppLen 0 := rfl
  have s2 : Erdos634.EdgeWordConversion.sideLen D 2 = D.model.oppLen 1 := rfl
  have t2 : dist (D.target.pts 0) (D.target.pts (0 + 1)) = D.target.oppLen 2 := rfl
  rw [s0, s1, s2, t2, h0, h1, h2] at hPQS
  have hLeq : D.target.oppLen 2 = D.target.oppLen 0 := equi_oppLen D.target hEq 2
  set n : ℕ := P * w + Q * u + S * v with hn
  have hnR : (n : ℝ) = (q : ℝ) * D.target.oppLen 0 := by
    rw [← hLeq, ← hPQS, hn]; push_cast; field_simp
  refine ⟨n, ?_, ?_⟩
  · have hLpos : 0 < D.target.oppLen 0 := D.target.oppLen_pos 0
    have : (0 : ℝ) < n := by rw [hnR]; positivity
    exact_mod_cast this
  · have : ((n : ℝ)) ^ 2 = (M : ℝ) * (A * B) := by
      rw [hnR, mul_pow, hcount]
      field_simp
    exact_mod_cast this.symm

/-- Natural dilation of an equilateral dissection (same model). -/
theorem dilate_equi {M : ℕ} (D : CongruentDissection M) (hEq : Equilateral D) (k : ℕ) (hk : 0 < k) :
    ∃ D' : CongruentDissection (k * k * M), Equilateral D' ∧ D'.model = D.model := by
  have hkne : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  obtain ⟨C', hC1, hC2⟩ := Erdos634.ZhangRegionDilate.dilate_region D.toRegion (D.target.pts 0) k hk
  have hreg : C'.region = (mapTri (homothetyEquiv (D.target.pts 0) (k : ℝ) hkne) D.target).carrier := by
    rw [hC1, mapTri_carrier]; rfl
  refine ⟨C'.toCongruentDissection _ hreg, ?_, hC2⟩
  intro j
  have hang := angleAt_of_scaled D.target (mapTri (homothetyEquiv (D.target.pts 0) (k : ℝ) hkne) D.target) (k : ℝ)
    (by exact_mod_cast hk) (fun i => by rw [mapHom_oppLen, abs_of_pos (by exact_mod_cast hk)]) j
  show (mapTri (homothetyEquiv (D.target.pts 0) (k : ℝ) hkne) D.target).angleAt j = _
  rw [hang]; exact hEq j

end Erdos634.Laczkovich9

#print axioms Erdos634.Laczkovich9.equi_count
#print axioms Erdos634.Laczkovich9.equi_model
#print axioms Erdos634.Laczkovich9.equi_n_formula
#print axioms Erdos634.Laczkovich9.dilate_equi
