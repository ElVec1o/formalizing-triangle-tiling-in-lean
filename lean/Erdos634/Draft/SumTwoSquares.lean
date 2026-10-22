-- Draft/SumTwoSquares.lean — existence half of the prime problem: for all `a,b ≥ 1`, the right
-- triangle with hypotenuse `[0,N]` (N = a²+b²) and apex `(a², ab)` is dissected into `a²+b²` congruent
-- right triangles with legs `(a,b)`: altitude cut + thm:ladder on the two similar pieces.
-- Imported via AllNew8→All.lean (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.Draft.PrimeWitness2

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.RWGlue Erdos634.Draft.RWEast
  Erdos634.Draft.RAAssemble
open Erdos634.RouteOneCrossing (selfDissection)

namespace Erdos634.Draft.SumTwoSquares

theorem eqsq {d v : ℝ} (hd : 0 ≤ d) (hv : 0 ≤ v) (h : d ^ 2 = v ^ 2) : d = v := by
  nlinarith [sq_nonneg (d - v), sq_nonneg (d + v)]

/-- Ladder piece: a tile `M` scaled by `k` covers any triangle `U` with the scaled side lengths. -/
theorem ladder_piece (M Mod U : Tri) (k : ℕ) (hk : 0 < k) (hMod : M.Congruent Mod)
    (h01 : dist (U.pts 0) (U.pts 1) = k * dist (M.pts 0) (M.pts 1))
    (h12 : dist (U.pts 1) (U.pts 2) = k * dist (M.pts 1) (M.pts 2))
    (h20 : dist (U.pts 2) (U.pts 0) = k * dist (M.pts 2) (M.pts 0)) :
    ∃ E : CongruentDissection (k * k * 1), E.target.Congruent U ∧ E.model = Mod := by
  obtain ⟨hind, heta⟩ := tri_eta M
  set D0 : CongruentDissection 1 :=
    { toDissection := selfDissection M, model := Mod, tiles_congruent := fun _ => hMod }
  obtain ⟨E, hEt, hEm⟩ := Erdos634.Ladder.ladder (M.pts 0) (M.pts 1) (M.pts 2) hind D0 heta k hk
  refine ⟨E, ?_, hEm⟩
  rw [hEt]
  have hd := dist_bigTri (M.pts 0) (M.pts 1) (M.pts 2) hind k hk
  refine SssCongruent.congruent_of_dist_three ?_ ?_ ?_
  · rw [hd 0 1]; exact h01.symm
  · rw [hd 1 2]; exact h12.symm
  · rw [hd 2 0]; exact h20.symm

theorem dsq (x1 y1 x2 y2 : ℝ) (v : ℝ) (hv : 0 ≤ v) (h : (x1 - x2) ^ 2 + (y1 - y2) ^ 2 = v ^ 2) :
    dist (mkPt x1 y1) (mkPt x2 y2) = v :=
  eqsq dist_nonneg hv (by rw [dist_sq_mkPt]; exact h)

theorem sum_two_squares_tiling (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Nonempty (CongruentDissection (a * a + b * b)) := by
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
  obtain ⟨D, -, -⟩ := glue_two T T1 T2 (A ^ 2 / NN) ht0 ht1
    (by show mkPt (A ^ 2) (A * B) = mkPt (A ^ 2) (A * B); rfl)
    (by show mkPt (0 : ℝ) 0 = mkPt 0 0; rfl)
    (by show mkPt (A ^ 2) (0 : ℝ) = AffineMap.lineMap (mkPt (0 : ℝ) 0) (mkPt NN 0) (A ^ 2 / NN); rw [hlm])
    (by show mkPt (A ^ 2) (A * B) = mkPt (A ^ 2) (A * B); rfl)
    (by show mkPt (A ^ 2) (0 : ℝ) = AffineMap.lineMap (mkPt (0 : ℝ) 0) (mkPt NN 0) (A ^ 2 / NN); rw [hlm])
    (by show mkPt NN (0 : ℝ) = mkPt NN 0; rfl)
    E1 E2 (by rw [hE2m, hE1m]; exact Tri.Congruent.refl _) hE1 hE2
  have hn : a * a * 1 + b * b * 1 = a * a + b * b := by ring
  exact ⟨hn ▸ D⟩

end Erdos634.Draft.SumTwoSquares

#print axioms Erdos634.Draft.SumTwoSquares.sum_two_squares_tiling
