import Erdos634.Draft.LaczFormalL30All
import Erdos634.Draft.LaczFormalL27Ang
import Erdos634.Draft.LaczFormalL27Std

/-!
# Laczkovich Theorem 2.5: gluing one tile to a rational triangle with an angle `π/3`

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.5, Fig. 7), Beeson, Beeson-Zhang, Zhang.

PRINT GAP: "Similar constructions apply for the other triples listed in (2); see Fig. 7."  In Fig. 7 three of the pictures
(first, third, fourth: triples `(α, α, π-2α)`, `(α, 2β, 2α+β)`, `(α, 2α, π-3α)`) are one tile glued to a triangle with an
angle `π/3 = α + β` at `S` (the triangle of Fig. 6, resp. the triangle `Θ` of the second picture): the tile `(X, U, S)`
has angle `γ = 2π/3` at `S`, angle `β` at `U`, angle `α` at `X`, and `X` lies on the line `V S` beyond `S`.
Its size is determined: `U S = a s` forces the scale `s = |US|/a` and `S X = b s`.

`attach`: `T = (U, V, S)` a rational triangle (rational sides), a rational similar dissection, with `∠ U S V = π/3`.  Then
`T' = (X, V, U)` is again a rational similar dissection with rational sides, with `∠ V X U = α` and `∠ U V X = ∠ U V S`.
-/

namespace Erdos634.LaczL31

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL21 Erdos634.LaczL24 Erdos634.Realizable
  Erdos634.DissectionMap EuclideanGeometry
open Erdos634.LaczL27 (hfan hfan_range carrier_eq_of_range range_mk3 fan_cover2 fan_disj kap_h kap_h_ne angle_ray
  angle_eq_of_prop)

theorem lagrange2 (w d : Plane) :
    (w 0 * d 1 - w 1 * d 0) ^ 2 = inner ℝ w w * inner ℝ d d - (inner ℝ w d) ^ 2 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]
  ring

theorem inner_of_angle (x y : Plane) (c : ℝ) (h : InnerProductGeometry.angle x y = c) :
    inner ℝ x y = Real.cos c * (‖x‖ * ‖y‖) := by
  rw [← h]; exact (InnerProductGeometry.cos_angle_mul_norm_mul_norm x y).symm

private theorem htri3 : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide

set_option maxHeartbeats 8000000 in
theorem attach_core (R : RTri) (hγ : R.a ^ 2 + R.a * R.b + R.b ^ 2 = R.c ^ 2) (U V S : Plane) (p q : ℚ)
    (hp : 0 < p) (hq : 0 < q) (hUS : dist U S = p) (hVS : dist V S = q) (hang : ∠ U S V = Real.pi / 3)
    (hT : RatSimDiss R.Δ (convexHull ℝ (Set.range ![U, V, S]))) :
    ∃ (X : Plane) (T' : Tri), T'.pts = ![X, V, U] ∧ RatSimDiss R.Δ T'.carrier ∧
      (∃ r : ℚ, dist X V = r) ∧ (∃ r : ℚ, dist X U = r) ∧
      ∠ V X U = ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) ∧ ∠ U V X = ∠ U V S := by
  have ha := R.pa
  have hb := R.pb
  have hc := R.pc
  have hγR : (R.a : ℝ) ^ 2 + R.a * R.b + R.b ^ 2 = (R.c : ℝ) ^ 2 := by exact_mod_cast hγ
  -- the chart with `w = V - S`, `d = U - S`
  obtain ⟨w, hwdef⟩ : ∃ w : Plane, w = V - S := ⟨_, rfl⟩
  obtain ⟨d, hddef⟩ : ∃ d : Plane, d = U - S := ⟨_, rfl⟩
  have hnw : ‖w‖ = (q : ℝ) := by rw [hwdef, ← dist_eq_norm]; exact hVS
  have hnd : ‖d‖ = (p : ℝ) := by rw [hddef, ← dist_eq_norm]; exact hUS
  have hww : inner ℝ w w = (q : ℝ) ^ 2 := by rw [real_inner_self_eq_norm_sq, hnw]
  have hdd : inner ℝ d d = (p : ℝ) ^ 2 := by rw [real_inner_self_eq_norm_sq, hnd]
  have hwd : inner ℝ w d = (q : ℝ) * p * (1 / 2) := by
    have h1 : InnerProductGeometry.angle d w = Real.pi / 3 := by
      rw [← hang]; unfold EuclideanGeometry.angle; simp only [vsub_eq_sub]; rw [hddef, hwdef]
    have := inner_of_angle d w _ h1
    rw [real_inner_comm, this, Real.cos_pi_div_three, hnd, hnw]; ring
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hdet : w 0 * d 1 - w 1 * d 0 ≠ 0 := by
    intro h0
    have := lagrange2 w d
    rw [h0, hww, hdd, hwd] at this
    nlinarith [mul_pos hqR hpR, sq_pos_of_pos (mul_pos hqR hpR)]
  have hV : V = S + w := by rw [hwdef]; abel
  have hU : U = S + d := by rw [hddef]; abel
  -- rational parameters: the tile scale `s = p / a` and `μ = b s / q`
  obtain ⟨s, hsdef⟩ : ∃ s : ℚ, s = p / R.a := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hsdef]; positivity
  have hsa : (R.a : ℚ) * s = p := by rw [hsdef]; field_simp
  obtain ⟨μ, hμdef⟩ : ∃ μ : ℚ, μ = R.b * s / q := ⟨_, rfl⟩
  have hμ0 : 0 < μ := by rw [hμdef]; positivity
  have hμq : μ * q = R.b * s := by rw [hμdef]; field_simp
  have hsaR : (R.a : ℝ) * s = p := by exact_mod_cast hsa
  have hμqR : (μ : ℝ) * q = R.b * s := by exact_mod_cast hμq
  have hμ0R : (0 : ℝ) < μ := by exact_mod_cast hμ0
  have hs0R : (0 : ℝ) < s := by exact_mod_cast hs0
  have haR : (0 : ℝ) < R.a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < R.b := by exact_mod_cast hb
  have hcR : (0 : ℝ) < R.c := by exact_mod_cast hc
  -- the chart
  have pt : ∀ x y : ℝ, chartEquiv S w d hdet (mkPt x y) = S + x • w + y • d := by
    intro x y; rw [chartEquiv_apply]; simp only [mkPt_zero, mkPt_one]
  have hdet0 : det3 0 1 1 0 0 0 ≠ 0 := by simp only [det3]; norm_num
  have hbase : chartEquiv S w d hdet '' (mkTri 0 1 1 0 0 0 hdet0).carrier = convexHull ℝ (Set.range ![U, V, S]) := by
    rw [← mapTri_carrier]
    simp only [Tri.carrier, mapTri]
    congr 2
    funext i; fin_cases i
    · show chartEquiv S w d hdet (mkPt 0 1) = U
      rw [pt, hU]; module
    · show chartEquiv S w d hdet (mkPt 1 0) = V
      rw [pt, hV]; module
    · show chartEquiv S w d hdet (mkPt 0 0) = S
      rw [pt]; module
  have cT0 : ChartRSD R S w d hdet (mkTri 0 1 1 0 0 0 hdet0).carrier := by
    unfold ChartRSD; rw [hbase]; exact hT
  -- the tile `X U S`
  have hdetT : det3 (-(μ : ℝ)) 0 0 1 0 0 ≠ 0 := by
    simp only [det3]; intro h; nlinarith
  have key01 : (μ : ℝ) ^ 2 * (q : ℝ) ^ 2 + μ * q * p + (p : ℝ) ^ 2 = (s : ℝ) ^ 2 * (R.c : ℝ) ^ 2 := by
    have e : (μ : ℝ) ^ 2 * (q : ℝ) ^ 2 + μ * q * p + (p : ℝ) ^ 2 = ((μ : ℝ) * q) ^ 2 + (μ * q) * p + (p : ℝ) ^ 2 := by ring
    rw [e, hμqR, ← hsaR, ← hγR]; ring
  have cTile : ChartRSD R S w d hdet (mkTri (-(μ : ℝ)) 0 0 1 0 0 hdetT).carrier := by
    refine chart_single (R := R) (A := S) (w := w) (d := d) (h := hdet) _
      (chart_tile R S w d hdet q p hww hdd ((q : ℝ) * p * (1 / 2)) hwd (-(μ : ℝ)) 0 0 1 0 0 hdetT 1 s hs0 ?_ ?_ ?_)
    · simp only [Equiv.Perm.coe_one, id_eq]; rw [R.hc]; linear_combination key01
    · simp only [Equiv.Perm.coe_one, id_eq]; rw [R.ha, ← hsaR]; ring
    · simp only [Equiv.Perm.coe_one, id_eq]; rw [R.hb]; linear_combination ((μ : ℝ) * q + R.b * s) * hμqR
  -- union by fans over the `x`-axis with apex `(0,1)`
  have hq1 : (0 : ℝ) < 1 := one_pos
  have hκ : 0 < Erdos634.LaczL27.kap 0 1 0 0 1 0 := by rw [kap_h]; norm_num
  have hne : Erdos634.LaczL27.kap 0 1 0 0 1 0 ≠ 0 := hκ.ne'
  have h1 : (-(μ : ℝ)) < 0 := by linarith
  have h2 : (0 : ℝ) < 1 := one_pos
  have cT0' : ChartRSD R S w d hdet (hfan 0 1 hq1 (x := 0) (y := 1) h2.ne).carrier := by
    have e : (hfan 0 1 hq1 (x := 0) (y := 1) h2.ne).carrier = (mkTri 0 1 1 0 0 0 hdet0).carrier := by
      refine carrier_eq_of_range ?_
      rw [hfan_range, mkTri_pts, range_mk3]
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [e]; exact cT0
  have cTile' : ChartRSD R S w d hdet (hfan 0 1 hq1 (x := -(μ : ℝ)) (y := 0) h1.ne).carrier := by
    have e : (hfan 0 1 hq1 (x := -(μ : ℝ)) (y := 0) h1.ne).carrier = (mkTri (-(μ : ℝ)) 0 0 1 0 0 hdetT).carrier := by
      refine carrier_eq_of_range ?_
      rw [hfan_range, mkTri_pts, range_mk3]
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [e]; exact cTile
  have hdetB : det3 (-(μ : ℝ)) 0 1 0 0 1 ≠ 0 := by simp only [det3]; intro h; nlinarith
  have cBig : ChartRSD R S w d hdet (mkTri (-(μ : ℝ)) 0 1 0 0 1 hdetB).carrier := by
    have hcov := fan_cover2 (u0 := -(μ : ℝ)) (u1 := 0) (u2 := 1) hκ hne h1 h2
    have e : (mkTri (-(μ : ℝ)) 0 1 0 0 1 hdetB).carrier
        = (hfan 0 1 hq1 (x := -(μ : ℝ)) (y := 0) h1.ne).carrier ∪ (hfan 0 1 hq1 (x := 0) (y := 1) h2.ne).carrier := by
      refine Eq.trans ?_ hcov.symm
      refine carrier_eq_of_range ?_
      rw [mkTri_pts]
      show _ = Set.range (hfan 0 1 hq1 (x := -(μ : ℝ)) (y := 1) _).pts
      rw [hfan_range, range_mk3]
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [e]
    exact chart_union cTile' cT0'
      (fan_disj hκ hne (m := 0) h1.ne h2.ne h1.le (le_refl _) (le_refl _) h2.le)
  refine ⟨chartEquiv S w d hdet (mkPt (-(μ : ℝ)) 0),
    Erdos634.DissectionMap.mapTri (chartEquiv S w d hdet) (mkTri (-(μ : ℝ)) 0 1 0 0 1 hdetB), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext i; fin_cases i
    · rfl
    · show chartEquiv S w d hdet (mkPt 1 0) = V
      rw [pt, hV]; module
    · show chartEquiv S w d hdet (mkPt 0 1) = U
      rw [pt, hU]; module
  · unfold ChartRSD at cBig
    rw [Erdos634.DissectionMap.mapTri_carrier]; exact cBig
  · -- dist X V = (1 + μ) q
    refine ⟨(1 + μ) * q, ?_⟩
    have e : chartEquiv S w d hdet (mkPt (-(μ : ℝ)) 0) - V = (-(1 + (μ : ℝ))) • w := by
      rw [pt, hV]; module
    rw [dist_eq_norm, e, norm_smul, hnw, Real.norm_eq_abs, abs_neg, abs_of_pos (by linarith)]
    push_cast; ring
  · -- dist X U = c s
    refine ⟨R.c * s, ?_⟩
    have e : chartEquiv S w d hdet (mkPt (-(μ : ℝ)) 0) - U = (-(μ : ℝ)) • w + (-1 : ℝ) • d := by
      rw [pt, hU]; module
    rw [dist_eq_norm, e]
    push_cast
    refine Erdos634.LaczL26.norm_comb w d _ _ _ (by positivity) ?_
    rw [Erdos634.LaczL26.gram2, hww, hdd, hwd]
    linear_combination key01
  · -- the angle at `X` is `α`
    have hX := pt (-(μ : ℝ)) 0
    have hXS : S - chartEquiv S w d hdet (mkPt (-(μ : ℝ)) 0) = (μ : ℝ) • w := by rw [hX]; module
    have hXV : V - chartEquiv S w d hdet (mkPt (-(μ : ℝ)) 0) = (1 + (μ : ℝ)) • w := by rw [hX, hV]; module
    have hXU : U - chartEquiv S w d hdet (mkPt (-(μ : ℝ)) 0) = (μ : ℝ) • w + (1 : ℝ) • d := by rw [hX, hU]; module
    have dSX : dist S (chartEquiv S w d hdet (mkPt (-(μ : ℝ)) 0)) = s * R.b := by
      rw [dist_eq_norm, hXS, norm_smul, hnw, Real.norm_eq_abs, abs_of_pos hμ0R, hμqR]; ring
    have dUX : dist U (chartEquiv S w d hdet (mkPt (-(μ : ℝ)) 0)) = s * R.c := by
      rw [dist_eq_norm, hXU]
      refine Eq.trans (Erdos634.LaczL26.norm_comb w d _ _ (s * R.c) (by positivity) ?_) rfl
      rw [Erdos634.LaczL26.gram2, hww, hdd, hwd]
      linear_combination key01
    have dUS : dist U S = s * R.a := by rw [hUS, ← hsaR]; ring
    have dΔ1 : dist (R.Δ.pts 1) (R.Δ.pts 0) = R.c := by rw [dist_comm]; exact R.hc
    have dΔ2 : dist (R.Δ.pts 2) (R.Δ.pts 0) = R.b := R.hb
    have dΔ3 : dist (R.Δ.pts 1) (R.Δ.pts 2) = R.a := R.ha
    rw [EuclideanGeometry.angle_comm V (chartEquiv S w d hdet (mkPt (-(μ : ℝ)) 0)) U]
    have hray := angle_ray (p := U) (x := chartEquiv S w d hdet (mkPt (-(μ : ℝ)) 0)) (r := V) (l := S)
      (c := (1 + (μ : ℝ)) / μ) (by positivity) (by
        rw [hXV, hXS, smul_smul]; congr 1; field_simp)
    rw [hray]
    exact angle_eq_of_prop hs0R (by rw [dUX, dΔ1]) (by rw [dSX, dΔ2]) (by rw [dUS, dΔ3])
      (Erdos634.LaczL27.delta_ne R (show (1 : Fin 3) ≠ 0 by decide))
      (Erdos634.LaczL27.delta_ne R (show (2 : Fin 3) ≠ 0 by decide))
  · -- the angle at `V` is unchanged
    have hX := pt (-(μ : ℝ)) 0
    exact angle_ray (p := U) (x := V) (r := chartEquiv S w d hdet (mkPt (-(μ : ℝ)) 0)) (l := S)
      (c := 1 + (μ : ℝ)) (by positivity) (by rw [hX, hV]; module)

#print axioms attach_core

/-- **Gluing a tile to a rational triangle with an angle `π/3` at `T₂`.**  `T = (U, V, S)` has rational sides, is a rational
similar dissection and `∠ U S V = π/3`.  Then `T' = (X, V, U)` (`X` on the line `V S` beyond `S`, `S X = b s`,
`s = |US|/a`) is a rational similar dissection with rational sides, `∠ V X U = α` and `∠ U V X = ∠ U V S`. -/
theorem attach (R : RTri) (hγ : R.a ^ 2 + R.a * R.b + R.b ^ 2 = R.c ^ 2) (T : Tri)
    (hT : RatSimDiss R.Δ T.carrier) (hRat : IsRationalTri T)
    (hS : cornerAngle (T.pts 0) (T.pts 2) (T.pts 1) = Real.pi / 3) :
    ∃ T' : Tri, RatSimDiss R.Δ T'.carrier ∧ IsRationalTri T' ∧
      cornerAngle (T'.pts 1) (T'.pts 0) (T'.pts 2) = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) ∧
      cornerAngle (T'.pts 2) (T'.pts 1) (T'.pts 0) = cornerAngle (T.pts 0) (T.pts 1) (T.pts 2) := by
  have hne : ∀ i j : Fin 3, i ≠ j → dist (T.pts i) (T.pts j) ≠ 0 := fun i j hij =>
    dist_ne_zero.mpr (fun h => hij (T.indep.injective h))
  obtain ⟨p, hp⟩ := hRat 0 2
  obtain ⟨q, hq⟩ := hRat 1 2
  have hp0 : 0 < p := by
    have h := hne 0 2 (by decide)
    have : (0 : ℝ) < p := by rw [← hp]; exact dist_pos.mpr (fun he => h (by rw [he, dist_self]))
    exact_mod_cast this
  have hq0 : 0 < q := by
    have h := hne 1 2 (by decide)
    have : (0 : ℝ) < q := by rw [← hq]; exact dist_pos.mpr (fun he => h (by rw [he, dist_self]))
    exact_mod_cast this
  have hpts : T.pts = ![T.pts 0, T.pts 1, T.pts 2] := by funext i; fin_cases i <;> rfl
  have hT' : RatSimDiss R.Δ (convexHull ℝ (Set.range ![T.pts 0, T.pts 1, T.pts 2])) := by
    have e : T.carrier = convexHull ℝ (Set.range ![T.pts 0, T.pts 1, T.pts 2]) := by
      show convexHull ℝ (Set.range T.pts) = _
      rw [← hpts]
    rw [← e]; exact hT
  obtain ⟨X, T', hT'pts, hRSD, ⟨r1, hr1⟩, ⟨r2, hr2⟩, hA, hB⟩ :=
    attach_core R hγ (T.pts 0) (T.pts 1) (T.pts 2) p q hp0 hq0 hp hq hS hT'
  have e0 : T'.pts 0 = X := by rw [hT'pts]; rfl
  have e1 : T'.pts 1 = T.pts 1 := by rw [hT'pts]; rfl
  have e2 : T'.pts 2 = T.pts 0 := by rw [hT'pts]; rfl
  refine ⟨T', hRSD, ?_, ?_, ?_⟩
  · intro j k
    obtain ⟨r3, hr3⟩ := hRat 1 0
    rcases (by decide : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2) j with rfl | rfl | rfl <;>
      rcases (by decide : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2) k with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨r1, by rw [e0, e1]; exact hr1⟩
    · exact ⟨r2, by rw [e0, e2]; exact hr2⟩
    · exact ⟨r1, by rw [e0, e1, dist_comm]; exact hr1⟩
    · exact ⟨0, by simp⟩
    · exact ⟨r3, by rw [e1, e2]; exact hr3⟩
    · exact ⟨r2, by rw [e0, e2, dist_comm]; exact hr2⟩
    · exact ⟨r3, by rw [e1, e2, dist_comm]; exact hr3⟩
    · exact ⟨0, by simp⟩
  · show ∠ (T'.pts 1) (T'.pts 0) (T'.pts 2) = _
    rw [e0, e1, e2]; exact hA
  · show ∠ (T'.pts 2) (T'.pts 1) (T'.pts 0) = ∠ (T.pts 0) (T.pts 1) (T.pts 2)
    rw [e0, e1, e2]; exact hB

#print axioms attach

end Erdos634.LaczL31
