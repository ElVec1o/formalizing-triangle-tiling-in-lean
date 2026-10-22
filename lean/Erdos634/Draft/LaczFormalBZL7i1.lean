import Erdos634.Draft.LaczFormalBZL7d6
import Erdos634.Draft.LaczFormalBZL7d7
import Erdos634.Draft.ZhangRat3Prop11
import Erdos634.Draft.G3CAng

-- Draft/LaczFormalBZL7i1.lean -- GENERIC WITNESS MACHINERY for rows 3-6 of Beeson-Zhang Thm 1.1 (gamma = 2pi/3, target not similar to the tile).
--   `region_to_D`    : a congruent REGION dissection of a coordinate triangle by a copy of the rational tile (3/2,5/2,7/2) gives a genuine `CongruentDissection`
--                      with target `mkTri ..`, and a vertex permutation `tau` with `model.oppLen (tau j)` = the three sides.
--   `tile_angles`    : alpha = model.angleAt (tau 0) has cos 13/14 (irrational multiple of pi), beta = angleAt (tau 1) has cos 11/14 and alpha + beta = pi/3.
--   `bz_apply`       : `bz_thm11` for any target angle of the form not in {alpha, pi/3 - alpha, 2 pi/3}.
-- Zhang's constructions (arXiv 2512.22696v4 Props 8-11) supply the region dissections in BZL7i2 (rows 3, 6), i3 (row 5), i4 (row 4).  NOTE, UNAUDITED.
-- Credit: Zhang (arXiv 2512.22696v4), Beeson-Zhang (arXiv 2604.01314), Laczkovich (DCG 48 (2012)), Beeson.

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Thm21 Erdos634.Draft.LaczFormal.RG
  Erdos634.Draft.LaczFormal.BZL7Wit Erdos634.Draft.G3CAng Erdos634.Draft.TheoremPConditional Erdos634.LaczL22 Erdos634.ZhangSporadic

namespace Erdos634.Draft.LaczFormal.BZL7i

theorem perm_side (σ : Equiv.Perm (Fin 3)) (j : Fin 3) :
    (σ (σ.symm j + 1) = j + 1 ∧ σ (σ.symm j + 2) = j + 2) ∨ (σ (σ.symm j + 1) = j + 2 ∧ σ (σ.symm j + 2) = j + 1) := by
  revert σ j; decide

theorem dist_mk_of_sq {x1 y1 x2 y2 r : ℝ} (hr : 0 ≤ r) (h : (x1 - x2) ^ 2 + (y1 - y2) ^ 2 = r ^ 2) :
    dist (mkPt x1 y1) (mkPt x2 y2) = r := by
  have h1 := dist_sq_mkPt x1 y1 x2 y2
  rw [h] at h1
  exact (pow_left_inj₀ dist_nonneg hr two_ne_zero).mp h1

theorem region_to_D {n : ℕ} (C : CongruentRegionDissection n) (R : RTri) (ha : R.a = 3 / 2) (hb : R.b = 5 / 2) (hc : R.c = 7 / 2)
    (hmod : C.model.Congruent R.Δ) (x0 y0 x1 y1 x2 y2 : ℝ) (hdet : 0 < det3 x0 y0 x1 y1 x2 y2)
    (hreg : C.region = TriSet x0 y0 x1 y1 x2 y2) :
    ∃ D : CongruentDissection n, D.target = mkTri x0 y0 x1 y1 x2 y2 hdet.ne' ∧ ∃ τ : Equiv.Perm (Fin 3),
      D.model.oppLen (τ 0) = 3 / 2 ∧ D.model.oppLen (τ 1) = 5 / 2 ∧ D.model.oppLen (τ 2) = 7 / 2 := by
  have hr : C.region = (mkTri x0 y0 x1 y1 x2 y2 hdet.ne').carrier := hreg.trans (TriSet_eq_carrier hdet)
  refine ⟨C.toCongruentDissection _ hr, rfl, ?_⟩
  obtain ⟨σ, hσ⟩ := hmod.dist_eq
  have key : ∀ j : Fin 3, C.model.oppLen (σ.symm j) = dist (R.Δ.pts (j + 1)) (R.Δ.pts (j + 2)) := by
    intro j
    show dist (C.model.pts (σ.symm j + 1)) (C.model.pts (σ.symm j + 2)) = _
    rw [hσ]
    rcases perm_side σ j with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]
    · rw [e1, e2, dist_comm]
  refine ⟨σ.symm, ?_, ?_, ?_⟩
  · show C.model.oppLen (σ.symm 0) = _
    rw [key 0]
    have := R.ha
    simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl]
    rw [this, ha]; norm_num
  · show C.model.oppLen (σ.symm 1) = _
    rw [key 1]
    have := R.hb
    simp only [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl]
    rw [this, hb]; norm_num
  · show C.model.oppLen (σ.symm 2) = _
    rw [key 2]
    have := R.hc
    simp only [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl]
    rw [this, hc]; norm_num

/-- the tile `(3/2,5/2,7/2)` seen from a model with the vertex permutation `tau`: `alpha`, `beta`, their cosines and `alpha + beta = pi/3`. -/
theorem tile_angles (T : Tri) (τ : Equiv.Perm (Fin 3)) (o0 : T.oppLen (τ 0) = 3 / 2) (o1 : T.oppLen (τ 1) = 5 / 2)
    (o2 : T.oppLen (τ 2) = 7 / 2) :
    T.TwoPiThreeData (T.angleAt (τ 0)) (1 / 2 * 3) (1 / 2 * 5) (1 / 2 * 7) ∧ Real.cos (T.angleAt (τ 0)) = 13 / 14 ∧
      Real.cos (T.angleAt (τ 1)) = 11 / 14 ∧ T.angleAt (τ 0) + T.angleAt (τ 1) = Real.pi / 3 ∧
      ¬ ∃ r : ℚ, T.angleAt (τ 0) = (r : ℝ) * Real.pi := by
  have o0' : T.oppLen (τ 0) = 1 / 2 * 3 := by rw [o0]; norm_num
  have o1' : T.oppLen (τ 1) = 1 / 2 * 5 := by rw [o1]; norm_num
  have o2' : T.oppLen (τ 2) = 1 / 2 * 7 := by rw [o2]; norm_num
  have data := tp_data T τ (1 / 2) 3 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) o0' o1' o2'
  have c0 : Real.cos (T.angleAt (τ 0)) = 13 / 14 := by
    rw [cos_s0 T τ (by rw [o1]; norm_num) (by rw [o2]; norm_num), o0, o1, o2]; norm_num
  have c1 : Real.cos (T.angleAt (τ 1)) = 11 / 14 := by
    rw [cos_s1 T τ (by rw [o0]; norm_num) (by rw [o2]; norm_num), o0, o1, o2]; norm_num
  have hirr : IrrPi (T.angleAt (τ 0)) :=
    irrPi_of_cos _ (13 / 14) (by rw [c0]; norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨-, hb⟩ := tp_angles T τ (1 / 2) 3 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) o0' o1' o2'
  exact ⟨data, c0, c1, by linarith, hirr⟩

/-- `bz_thm11` applied to a dissection whose target has an angle outside `{alpha, pi/3 - alpha, 2 pi/3}`. -/
theorem bz_apply {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoPiThreeData α a b c) (j : Fin 3) (h0 : D.target.angleAt j ≠ α) (h1 : D.target.angleAt j ≠ Real.pi / 3 - α)
    (h2 : D.target.angleAt j ≠ 2 * Real.pi / 3) : NotSim D ∧ Comm a b ∧ Comm a c := by
  have hNS := notSim_of_no_match D h j h0 h1 h2
  exact ⟨hNS, bz_thm11 D hα h hNS⟩

theorem mk_oppLen (x0 y0 x1 y1 x2 y2 : ℝ) (hdet : det3 x0 y0 x1 y1 x2 y2 ≠ 0) (s0 s1 s2 : ℝ) (p0 : 0 ≤ s0) (p1 : 0 ≤ s1) (p2 : 0 ≤ s2)
    (h0 : (x1 - x2) ^ 2 + (y1 - y2) ^ 2 = s0 ^ 2) (h1 : (x2 - x0) ^ 2 + (y2 - y0) ^ 2 = s1 ^ 2)
    (h2 : (x0 - x1) ^ 2 + (y0 - y1) ^ 2 = s2 ^ 2) :
    (mkTri x0 y0 x1 y1 x2 y2 hdet).oppLen 0 = s0 ∧ (mkTri x0 y0 x1 y1 x2 y2 hdet).oppLen 1 = s1 ∧
      (mkTri x0 y0 x1 y1 x2 y2 hdet).oppLen 2 = s2 := by
  refine ⟨dist_mk_of_sq p0 h0, dist_mk_of_sq p1 h1, dist_mk_of_sq p2 h2⟩

/-- cosines of the three angles of a triangle from its three side lengths. -/
theorem tri_cos (T : Tri) (u0 u1 u2 : ℝ) (p0 : 0 < u0) (p1 : 0 < u1) (p2 : 0 < u2) (o0 : T.oppLen 0 = u0) (o1 : T.oppLen 1 = u1)
    (o2 : T.oppLen 2 = u2) :
    Real.cos (T.angleAt 0) = (u1 ^ 2 + u2 ^ 2 - u0 ^ 2) / (2 * u1 * u2) ∧
      Real.cos (T.angleAt 1) = (u0 ^ 2 + u2 ^ 2 - u1 ^ 2) / (2 * u0 * u2) ∧
      Real.cos (T.angleAt 2) = (u0 ^ 2 + u1 ^ 2 - u2 ^ 2) / (2 * u0 * u1) := by
  have a := cos_s0 T 1 (by simpa [o1] using p1) (by simpa [o2] using p2)
  have b := cos_s1 T 1 (by simpa [o0] using p0) (by simpa [o2] using p2)
  have c := cos_s2 T 1 (by simpa [o0] using p0) (by simpa [o1] using p1)
  simp only [Equiv.Perm.coe_one, id_eq] at a b c
  rw [o0, o1, o2] at a b c
  exact ⟨a, b, c⟩

end Erdos634.Draft.LaczFormal.BZL7i

#print axioms Erdos634.Draft.LaczFormal.BZL7i.region_to_D
#print axioms Erdos634.Draft.LaczFormal.BZL7i.tile_angles
#print axioms Erdos634.Draft.LaczFormal.BZL7i.bz_apply
#print axioms Erdos634.Draft.LaczFormal.BZL7i.mk_oppLen
#print axioms Erdos634.Draft.LaczFormal.BZL7i.tri_cos
