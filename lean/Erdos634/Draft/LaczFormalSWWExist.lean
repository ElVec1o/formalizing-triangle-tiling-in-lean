-- Draft/LaczFormalSWWExist.lean -- Snover-Waiveris-Williams (Discrete Math 91 (1991) 193-200): EXISTENCE of the reptile
-- outcomes.  (i) N = a^2 + b^2 (a, b >= 1): a real `CongruentDissection` whose target is similar to the tile and whose tile is
-- the right triangle with legs a : b (`sww_sumsq_exists`; construction = `SumTwoSquares.sum_two_squares_tiling`, strengthened to
-- keep target/model); (ii) N = 3 m^2 (m >= 1): the scale-m ladder of the 30-60-90 three-piece dissection `HBCFalse3.D3`
-- (`sww_three_exists`).  NOTE, UNAUDITED.  Credit: Snover-Waiveris-Williams, Golomb, Beeson, Beeson-Rosu, Zhang, Laczkovich.
import Erdos634.Draft.SumTwoSquares
import Erdos634.Draft.LaczFormalSWWWit

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.RWGlue Erdos634.Draft.RWEast
  Erdos634.Draft.RAAssemble Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
  Erdos634.Draft.SumTwoSquares Erdos634.Draft.G3CAng
open Erdos634.RouteOneCrossing (selfDissection)

namespace Erdos634.Draft.LaczFormal

/-- Equal angles from proportional opposite sides (any vertex correspondence). -/
theorem angle_of_opp (T U : Tri) (μ : ℝ) (hμ : 0 < μ) (τ : Equiv.Perm (Fin 3))
    (h : ∀ k, T.oppLen k = μ * U.oppLen (τ k)) (k : Fin 3) : T.angleAt k = U.angleAt (τ k) := by
  have pT := Tri.oppLen_pos T
  have pU := Tri.oppLen_pos U
  fin_cases k
  · show T.angleAt 0 = U.angleAt (τ 0)
    refine angle_eq_of_cos 0 (τ 0) ?_
    rw [cos_angleAt_opp T 0 (pT _) (pT _), cos_s0 U τ (pU _) (pU _)]
    simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl, h 0, h 1, h 2]
    have := pU (τ 1); have := pU (τ 2)
    field_simp
    try ring
  · show T.angleAt 1 = U.angleAt (τ 1)
    refine angle_eq_of_cos 1 (τ 1) ?_
    rw [cos_angleAt_opp T 1 (pT _) (pT _), cos_s1 U τ (pU _) (pU _)]
    simp only [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl, h 0, h 1, h 2]
    have := pU (τ 0); have := pU (τ 2)
    field_simp
    try ring
  · show T.angleAt 2 = U.angleAt (τ 2)
    refine angle_eq_of_cos 2 (τ 2) ?_
    rw [cos_angleAt_opp T 2 (pT _) (pT _), cos_s2 U τ (pU _) (pU _)]
    simp only [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl, h 0, h 1, h 2]
    have := pU (τ 0); have := pU (τ 1)
    field_simp
    try ring

theorem sww_sumsq_exists (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ∃ D : CongruentDissection (a * a + b * b), SimilarTM D ∧ RightLegs D a b := by
  have hA : (0 : ℝ) < a := by exact_mod_cast ha
  have hB : (0 : ℝ) < b := by exact_mod_cast hb
  set A : ℝ := (a : ℝ) with hAdef
  set B : ℝ := (b : ℝ) with hBdef
  set NN : ℝ := A ^ 2 + B ^ 2 with hNN
  have hNpos : 0 < NN := by positivity
  set c : ℝ := Real.sqrt NN with hc
  have hcpos : 0 < c := Real.sqrt_pos.mpr hNpos
  have hcsq : c ^ 2 = NN := Real.sq_sqrt hNpos.le
  have hAB := mul_pos hA hB
  have dT : det3 (A ^ 2) (A * B) 0 0 NN 0 ≠ 0 := by
    unfold det3; nlinarith [mul_pos (mul_pos hA hA) hAB, mul_pos hAB (mul_pos hB hB)]
  have dT1 : det3 (A ^ 2) (A * B) 0 0 (A ^ 2) 0 ≠ 0 := by
    unfold det3; nlinarith [mul_pos (mul_pos hA hA) hAB]
  have dT2 : det3 (A ^ 2) (A * B) (A ^ 2) 0 NN 0 ≠ 0 := by
    unfold det3; nlinarith [mul_pos hAB (mul_pos hB hB)]
  have dM1 : det3 0 B A 0 0 0 ≠ 0 := by unfold det3; nlinarith
  have dM2 : det3 A 0 0 0 0 B ≠ 0 := by unfold det3; nlinarith
  set T : Tri := mkTri (A ^ 2) (A * B) 0 0 NN 0 dT
  set T1 : Tri := mkTri (A ^ 2) (A * B) 0 0 (A ^ 2) 0 dT1
  set T2 : Tri := mkTri (A ^ 2) (A * B) (A ^ 2) 0 NN 0 dT2
  set M1 : Tri := mkTri 0 B A 0 0 0 dM1
  set M2 : Tri := mkTri A 0 0 0 0 B dM2
  have hM21 : M2.Congruent M1 := by
    refine (M2.congruent_relabel (finRotate 3).symm).trans ?_
    refine SssCongruent.congruent_of_dist_three ?_ ?_ ?_ <;> rfl
  have ac : dist (mkPt (0 : ℝ) B) (mkPt A 0) = c := dsq _ _ _ _ _ hcpos.le (by rw [hcsq]; ring)
  -- piece 1: (R, P, F) = a · M1
  obtain ⟨E1, hE1, hE1m⟩ := ladder_piece M1 M1 T1 a ha (Tri.Congruent.refl M1)
    (by
      show dist (mkPt (A ^ 2) (A * B)) (mkPt 0 0) = (a : ℝ) * dist (mkPt (0 : ℝ) B) (mkPt A 0)
      rw [ac]; exact dsq _ _ _ _ _ (by positivity) (by rw [mul_pow, hcsq]; ring))
    (by
      show dist (mkPt (0 : ℝ) 0) (mkPt (A ^ 2) 0) = (a : ℝ) * dist (mkPt A 0) (mkPt (0 : ℝ) 0)
      rw [dsq A 0 0 0 A hA.le (by ring)]
      exact dsq _ _ _ _ _ (by positivity) (by ring))
    (by
      show dist (mkPt (A ^ 2) 0) (mkPt (A ^ 2) (A * B)) = (a : ℝ) * dist (mkPt (0 : ℝ) 0) (mkPt 0 B)
      rw [dsq 0 0 0 B B hB.le (by ring)]
      exact dsq _ _ _ _ _ (by positivity) (by ring))
  -- piece 2: (R, F, Q) = b · M2 (M2 ≅ M1)
  obtain ⟨E2, hE2, hE2m⟩ := ladder_piece M2 M1 T2 b hb hM21
    (by
      show dist (mkPt (A ^ 2) (A * B)) (mkPt (A ^ 2) 0) = (b : ℝ) * dist (mkPt A (0 : ℝ)) (mkPt 0 0)
      rw [dsq A 0 0 0 A hA.le (by ring)]
      exact dsq _ _ _ _ _ (by positivity) (by ring))
    (by
      show dist (mkPt (A ^ 2) (0 : ℝ)) (mkPt NN 0) = (b : ℝ) * dist (mkPt (0 : ℝ) 0) (mkPt 0 B)
      rw [dsq 0 0 0 B B hB.le (by ring)]
      exact dsq _ _ _ _ _ (by positivity) (by rw [hNN]; ring))
    (by
      show dist (mkPt NN (0 : ℝ)) (mkPt (A ^ 2) (A * B)) = (b : ℝ) * dist (mkPt (0 : ℝ) B) (mkPt A 0)
      rw [ac]
      exact dsq _ _ _ _ _ (by positivity) (by rw [mul_pow, hcsq, hNN]; ring))
  have hlm : AffineMap.lineMap (mkPt (0 : ℝ) 0) (mkPt NN 0) (A ^ 2 / NN) = mkPt (A ^ 2) 0 := by
    rw [lm]; congr 1; field_simp; ring
  have ht0 : 0 < A ^ 2 / NN := by positivity
  have ht1 : A ^ 2 / NN < 1 := by
    rw [div_lt_one hNpos, hNN]; nlinarith [pow_pos hB 2]
  obtain ⟨D, hDt, hDm⟩ := glue_two T T1 T2 (A ^ 2 / NN) ht0 ht1
    (by show mkPt (A ^ 2) (A * B) = mkPt (A ^ 2) (A * B); rfl)
    (by show mkPt (0 : ℝ) 0 = mkPt 0 0; rfl)
    (by show mkPt (A ^ 2) (0 : ℝ) = AffineMap.lineMap (mkPt (0 : ℝ) 0) (mkPt NN 0) (A ^ 2 / NN); rw [hlm])
    (by show mkPt (A ^ 2) (A * B) = mkPt (A ^ 2) (A * B); rfl)
    (by show mkPt (A ^ 2) (0 : ℝ) = AffineMap.lineMap (mkPt (0 : ℝ) 0) (mkPt NN 0) (A ^ 2 / NN); rw [hlm])
    (by show mkPt NN (0 : ℝ) = mkPt NN 0; rfl)
    E1 E2 (by rw [hE2m, hE1m]; exact Tri.Congruent.refl _) hE1 hE2
  have hn : a * a * 1 + b * b * 1 = a * a + b * b := by ring
  have hmod : D.model = M1 := hDm.trans hE1m
  have oM0 : M1.oppLen 0 = A := by
    show dist (mkPt A (0 : ℝ)) (mkPt 0 0) = A
    exact dsq _ _ _ _ _ hA.le (by ring)
  have oM1 : M1.oppLen 1 = B := by
    show dist (mkPt (0 : ℝ) 0) (mkPt 0 B) = B
    exact dsq _ _ _ _ _ hB.le (by ring)
  have oM2 : M1.oppLen 2 = c := by
    show dist (mkPt (0 : ℝ) B) (mkPt A 0) = c
    exact ac
  have oT0 : T.oppLen 0 = c * c := by
    show dist (mkPt (0 : ℝ) 0) (mkPt NN 0) = c * c
    exact dsq _ _ _ _ _ (by positivity) (by rw [mul_pow, hcsq, hNN]; ring)
  have oT1 : T.oppLen 1 = c * B := by
    show dist (mkPt NN (0 : ℝ)) (mkPt (A ^ 2) (A * B)) = c * B
    exact dsq _ _ _ _ _ (by positivity) (by rw [mul_pow, hcsq, hNN]; ring)
  have oT2 : T.oppLen 2 = c * A := by
    show dist (mkPt (A ^ 2) (A * B)) (mkPt 0 0) = c * A
    exact dsq _ _ _ _ _ (by positivity) (by rw [mul_pow, hcsq, hNN]; ring)
  have hsim : SimilarTM D := by
    refine ⟨c, Equiv.swap 0 2, fun k => ?_⟩
    rw [hDt, hmod]
    have hh : ∀ k, T.oppLen k = c * M1.oppLen (Equiv.swap (0 : Fin 3) 2 k) := by
      intro k; fin_cases k
      · show T.oppLen 0 = c * M1.oppLen (Equiv.swap (0 : Fin 3) 2 0)
        rw [show Equiv.swap (0 : Fin 3) 2 0 = 2 by decide, oT0, oM2]
      · show T.oppLen 1 = c * M1.oppLen (Equiv.swap (0 : Fin 3) 2 1)
        rw [show Equiv.swap (0 : Fin 3) 2 1 = 1 by decide, oT1, oM1]
      · show T.oppLen 2 = c * M1.oppLen (Equiv.swap (0 : Fin 3) 2 2)
        rw [show Equiv.swap (0 : Fin 3) 2 2 = 0 by decide, oT2, oM0]
    exact ⟨angle_of_opp T M1 c hcpos _ hh k, hh k⟩
  have hc0 : Real.cos (M1.angleAt 2) = 0 := by
    rw [cos_angleAt_opp M1 2 (by rw [show (2 : Fin 3) + 1 = 0 from rfl, oM0]; exact hA)
      (by rw [show (2 : Fin 3) + 2 = 1 from rfl, oM1]; exact hB)]
    rw [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl, oM0, oM1, oM2, hcsq, hNN]
    ring
  have hright : M1.angleAt 2 = Real.pi / 2 :=
    Real.injOn_cos (Erdos634.Draft.FluxPaperWitness.cornerAngle_mem' _ _ _)
      ⟨by positivity, by linarith [Real.pi_pos]⟩ (hc0.trans Real.cos_pi_div_two.symm)
  have key : ∃ D : CongruentDissection (a * a * 1 + b * b * 1), SimilarTM D ∧ RightLegs D a b := by
    refine ⟨D, hsim, 0, 1, 2, by decide, by decide, by decide, by rw [hmod]; exact hright, ?_⟩
    rw [hmod, oM0, oM1]
    simp only [hAdef, hBdef]; ring
  rw [hn] at key
  exact key

/-- Witnesses of the `A^2 + B^2` family with `A ≠ B`: `N = 5 = 1 + 4` (legs 1 : 2), `N = 13` (legs 2 : 3), `N = 10` (1 : 3). -/
theorem sww_sumsq_N5 : ∃ D : CongruentDissection 5, SimilarTM D ∧ RightLegs D 1 2 := sww_sumsq_exists 1 2 (by norm_num) (by norm_num)
theorem sww_sumsq_N13 : ∃ D : CongruentDissection 13, SimilarTM D ∧ RightLegs D 2 3 := sww_sumsq_exists 2 3 (by norm_num) (by norm_num)
theorem sww_sumsq_N10 : ∃ D : CongruentDissection 10, SimilarTM D ∧ RightLegs D 1 3 := sww_sumsq_exists 1 3 (by norm_num) (by norm_num)

/-- The tile of `HBCFalse3.D3` is the 30-60-90 triangle. -/
theorem D3_tileAngles : TileAngles Erdos634.Draft.HBCFalse3.D3 (Real.pi / 6) (Real.pi / 3) (Real.pi / 2) := by
  have hs : SimilarTM Erdos634.Draft.HBCFalse3.D3 := ⟨Erdos634.Draft.HBCFalse3.s, 1, Erdos634.Draft.HBCFalse3.D3_sim⟩
  rcases reptile_SWW _ hs with h | ⟨A, B, hAB, -⟩ | h
  · exact absurd h not_square_three
  · exact absurd ⟨A, B, hAB⟩ Erdos634.Draft.HBCFalse3.three_not_sumsq
  · exact h.2

/-- Scale-`m` ladder of a dissection: the target's opposite sides are `m` times the old ones, same model. -/
theorem ladder_opp {N : ℕ} (D : CongruentDissection N) (m : ℕ) (hm : 0 < m) :
    ∃ E : CongruentDissection (m * m * N), E.model = D.model ∧ ∀ k, E.target.oppLen k = m * D.target.oppLen k := by
  obtain ⟨hind, heta⟩ := tri_eta D.target
  obtain ⟨E, hEt, hEm⟩ := Erdos634.Ladder.ladder (D.target.pts 0) (D.target.pts 1) (D.target.pts 2) hind D heta m hm
  refine ⟨E, hEm, fun k => ?_⟩
  have hd := dist_bigTri (D.target.pts 0) (D.target.pts 1) (D.target.pts 2) hind m hm
  rw [hEt]
  fin_cases k
  · show dist _ _ = _ * dist (D.target.pts 1) (D.target.pts 2)
    exact hd 1 2
  · show dist _ _ = _ * dist (D.target.pts 2) (D.target.pts 0)
    exact hd 2 0
  · show dist _ _ = _ * dist (D.target.pts 0) (D.target.pts 1)
    exact hd 0 1

/-- **`N = 3 m^2`, every `m >= 1`:** a real `CongruentDissection` into `3 m^2` copies of the 30-60-90 triangle whose target is
similar to the tile. -/
theorem sww_three_exists (m : ℕ) (hm : 0 < m) :
    ∃ D : CongruentDissection (m * m * 3), SimilarTM D ∧ TileAngles D (Real.pi / 6) (Real.pi / 3) (Real.pi / 2) := by
  obtain ⟨E, hEm, hEo⟩ := ladder_opp Erdos634.Draft.HBCFalse3.D3 m hm
  have hμ : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨E, ⟨m * Erdos634.Draft.HBCFalse3.s, 1, fun k => ?_⟩, ?_⟩
  · have hang := angle_of_opp E.target Erdos634.Draft.HBCFalse3.D3.target m hμ 1 (fun k => by simpa using hEo k) k
    obtain ⟨h1, h2⟩ := Erdos634.Draft.HBCFalse3.D3_sim k
    refine ⟨?_, ?_⟩
    · rw [hang, hEm]; simpa using h1
    · rw [hEo, hEm, h2]; simp; ring
  · obtain ⟨σ, h0, h1, h2⟩ := D3_tileAngles
    exact ⟨σ, by rw [hEm]; exact h0, by rw [hEm]; exact h1, by rw [hEm]; exact h2⟩

theorem sww_three_N12 : ∃ D : CongruentDissection 12, SimilarTM D ∧ TileAngles D (Real.pi / 6) (Real.pi / 3) (Real.pi / 2) :=
  sww_three_exists 2 (by norm_num)
theorem sww_three_N27 : ∃ D : CongruentDissection 27, SimilarTM D ∧ TileAngles D (Real.pi / 6) (Real.pi / 3) (Real.pi / 2) :=
  sww_three_exists 3 (by norm_num)

/-- Area check (automatic for every `CongruentDissection`): the `N = 5` instance has `|target| = 5 |tile|`. -/
theorem sww_N5_area : ∃ D : CongruentDissection 5, SimilarTM D ∧ MeasureTheory.volume D.target.carrier = 5 * MeasureTheory.volume D.model.carrier := by
  obtain ⟨D, h, -⟩ := sww_sumsq_N5
  exact ⟨D, h, by simpa using Erdos634.CongruentArea.congruentDissection_volume_target D⟩

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.sww_sumsq_exists
#print axioms Erdos634.Draft.LaczFormal.sww_sumsq_N5
#print axioms Erdos634.Draft.LaczFormal.sww_sumsq_N13
#print axioms Erdos634.Draft.LaczFormal.sww_three_exists
#print axioms Erdos634.Draft.LaczFormal.sww_three_N12
#print axioms Erdos634.Draft.LaczFormal.sww_three_N27
#print axioms Erdos634.Draft.LaczFormal.sww_N5_area
