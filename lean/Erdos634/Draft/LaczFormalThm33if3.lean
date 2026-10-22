import Erdos634.Draft.LaczFormalThm33if2

/-!
# Laczkovich DCG 48 (2012) Thm 3.3, "if" direction, module 3 of 4: clause (iii) complete

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Thm 3.1, Lemma 2.1, 2.2 (iii); DCG 48 (2012) 330-372,
Thm 3.3), Beeson, Beeson-Zhang, Zhang.

* `equi_pi3`            : a rational tile with `vang 1 = π/3` dissects the equilateral triangle `e '' Qtri` (angles `π/3`).
* `thm33_if_rtri_pi3`   : `Thm33If (vang R.Δ 0) (vang R.Δ 1) (vang R.Δ 2)` for such `R`.
* `thm33_if_iii`        : **clause (iii) of the printed Theorem 3.3**: angles `x, y, z > 0`, `x + y + z = π`, `z ∈ {π/3, 2π/3}`,
                          `sin x, sin y, sin z` pairwise commensurable  =>  `Thm33If x y z`.
-/

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
  Erdos634.Draft.LaczFormal Erdos634.Draft.LaczFormal.Thm21 Erdos634.LaczL35 Erdos634.LaczL22 Erdos634.CertCoord
  Erdos634.LaczL37 Erdos634.DissectionMap Erdos634.CertGeom
open Erdos634.LaczL33 (equi_angle)

namespace Erdos634.LaczThm33If

theorem carrier_T0 (h : det3 0 0 3 0 0 3 ≠ 0) : (mkTri 0 0 3 0 0 3 h).carrier = Qtri := by
  ext x
  constructor
  · intro hx
    have f1 := le_of_forall_pts_le (t := mkTri 0 0 3 0 0 3 h) (lineFun 0 0 0 1) (c := 0)
      (by intro k; fin_cases k <;> simp [lineFun_apply]) x hx
    have f2 := le_of_forall_pts_le (t := mkTri 0 0 3 0 0 3 h) (lineFun 1 0 0 0) (c := 0)
      (by intro k; fin_cases k <;> simp [lineFun_apply]) x hx
    have f3 := le_of_forall_pts_le (t := mkTri 0 0 3 0 0 3 h) (lineFun 0 3 3 0) (c := 0)
      (by intro k; fin_cases k <;> simp [lineFun_apply] <;> norm_num) x hx
    simp only [lineFun_apply] at f1 f2 f3
    refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h0, h1, h2⟩
    have hD : 0 < det3 0 0 3 0 0 3 := by simp [det3]
    have := mem_carrier_of_dets (x₀ := 0) (y₀ := 0) (x₁ := 3) (y₁ := 0) (x₂ := 0) (y₂ := 3) (a := x 0) (b := x 1) hD
      (by simp [det3]; linarith) (by simp [det3]; linarith) (by simp [det3]; linarith)
    rwa [mkPt_eta] at this

theorem equi_pi3 (R : RTri) (hβ : vang R.Δ 1 = Real.pi / 3) :
    ∃ T : Tri, RatSimDiss R.Δ T.carrier ∧
      cornerAngle (T.pts 1) (T.pts 0) (T.pts 2) = Real.pi / 3 ∧
      cornerAngle (T.pts 2) (T.pts 1) (T.pts 0) = Real.pi / 3 ∧
      cornerAngle (T.pts 0) (T.pts 2) (T.pts 1) = Real.pi / 3 := by
  obtain ⟨u, v, hu', hv', huv', hdet⟩ := Erdos634.LaczL24.exists_gram_chart 1 1 (1 / 2) one_pos one_pos (by norm_num)
  have hu : inner ℝ u u = 1 := by simpa using hu'
  have hv : inner ℝ v v = 1 := by simpa using hv'
  have huv : inner ℝ u v = 1 / 2 := by simpa using huv'
  have hd0 : det3 0 0 3 0 0 3 ≠ 0 := by simp [det3]
  set e := chartEquiv 0 u v hdet with he
  have hsq : ∀ p q : Plane, dist (e p) (e q) ^ 2
      = (p 0 - q 0) ^ 2 + (p 0 - q 0) * (p 1 - q 1) + (p 1 - q 1) ^ 2 := by
    intro p q
    rw [he, dist_chart_sq, hu, hv, huv]; ring
  have d3 : ∀ p q : Plane, (p 0 - q 0) ^ 2 + (p 0 - q 0) * (p 1 - q 1) + (p 1 - q 1) ^ 2 = 3 ^ 2 →
      dist (e p) (e q) = 3 := by
    intro p q h
    exact eq_of_sq_eq' dist_nonneg (by norm_num) (by rw [hsq, h])
  refine ⟨mapTri e (mkTri 0 0 3 0 0 3 hd0), ?_, ?_, ?_, ?_⟩
  · rw [mapTri_carrier, carrier_T0]
    exact qtri_ratsim R hβ u v hu hv huv hdet
  all_goals
    have D01 : dist (e (mkPt 0 0)) (e (mkPt 3 0)) = 3 := d3 _ _ (by first | (simp; done) | (simp; norm_num))
    have D02 : dist (e (mkPt 0 0)) (e (mkPt 0 3)) = 3 := d3 _ _ (by first | (simp; done) | (simp; norm_num))
    have D12 : dist (e (mkPt 3 0)) (e (mkPt 0 3)) = 3 := d3 _ _ (by first | (simp; done) | (simp; norm_num))
  · show cornerAngle (e (mkPt 3 0)) (e (mkPt 0 0)) (e (mkPt 0 3)) = _
    exact equi_angle _ _ _ 3 (by norm_num) (by rw [dist_comm]; exact D01) (by rw [dist_comm]; exact D02) D12
  · show cornerAngle (e (mkPt 0 3)) (e (mkPt 3 0)) (e (mkPt 0 0)) = _
    exact equi_angle _ _ _ 3 (by norm_num) (by rw [dist_comm]; exact D12) D01 (by rw [dist_comm]; exact D02)
  · show cornerAngle (e (mkPt 0 0)) (e (mkPt 0 3)) (e (mkPt 3 0)) = _
    exact equi_angle _ _ _ 3 (by norm_num) D02 D12 D01

theorem thm33_if_rtri_pi3 (R : RTri) (hβ : vang R.Δ 1 = Real.pi / 3) :
    Thm33If (vang R.Δ 0) (vang R.Δ 1) (vang R.Δ 2) := by
  obtain ⟨T, h, a0, a1, a2⟩ := equi_pi3 R hβ
  exact thm33_if_of_equi R T h a0 a1 a2

theorem Thm33If.swap {x y z : ℝ} (h : Thm33If x y z) : Thm33If y x z := by
  obtain ⟨N, D, e, t⟩ := h; exact ⟨N, D, e, t.swap⟩

theorem Thm33If.swap23 {x y z : ℝ} (h : Thm33If x y z) : Thm33If x z y := by
  obtain ⟨N, D, e, t⟩ := h; exact ⟨N, D, e, t.swap23⟩

theorem comm_ratio {a b : ℝ} (hb : 0 < b) (h : Comm a b) : ∃ r : ℚ, 0 < r ∧ a = r * b := by
  obtain ⟨p, q, hp, hq, e⟩ := h
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  refine ⟨(q : ℚ) / p, ?_, ?_⟩
  · positivity
  · push_cast; field_simp; linarith

/-- **Clause (iii) of Laczkovich's Theorem 3.3 ("if").** -/
theorem thm33_if_iii (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hsum : x + y + z = Real.pi)
    (hz3 : z = Real.pi / 3 ∨ z = 2 * Real.pi / 3)
    (hxy : Comm (Real.sin x) (Real.sin y)) (hyz : Comm (Real.sin y) (Real.sin z))
    (hxz : Comm (Real.sin x) (Real.sin z)) : Thm33If x y z := by
  have sz := Real.sin_pos_of_pos_of_lt_pi hz (by linarith)
  have sy := Real.sin_pos_of_pos_of_lt_pi hy (by linarith)
  obtain ⟨p, hp, hpe⟩ := comm_ratio sz hxz
  obtain ⟨q, hq, hqe⟩ := comm_ratio sz hyz
  rcases hz3 with h | h
  · -- put the angle `z = π/3` at vertex 1: tile angles `(x, z, y)`
    have hq' : 0 < p / q := by positivity
    have hq'' : 0 < 1 / q := by positivity
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    obtain ⟨R, r0, r1, r2⟩ := rtri_of_sines x z y hx hz hy (by linarith) (p / q) (1 / q) hq' hq''
      (by push_cast; rw [hpe, hqe]; field_simp) (by push_cast; rw [hqe]; field_simp)
    have := thm33_if_rtri_pi3 R (by rw [r1, h])
    rw [r0, r1, r2] at this
    exact this.swap23
  · exact thm33_if_2pi3 x y z hx hy hz hsum h p q hp hq hpe hqe

#print axioms Erdos634.LaczThm33If.thm33_if_iii

end Erdos634.LaczThm33If
