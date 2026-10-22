import Erdos634.Draft.BeesonIso3b
import Erdos634.Draft.LaczFormalBZL7h10

/-!
# Beeson, "Tilings of an isosceles triangle" (arXiv 1206.1974 v7), Sect. 11: the CHORD LAYER, part 2 (geometry of a chord between two adjacent sides)

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.1974 v7, Lemma 11.8; arXiv 1206.2229), Laczkovich (DCG 48 (2012), Sect. 4), Beeson-Zhang, Herdt, Zhang.
Formalization debt, not progress on the /goal outcomes.

Polygon `P` (convex, counterclockwise), `E` in the relative interior of the side `v_i v_{i+1}`, `F` in the relative interior of the NEXT side `v_{i+1} v_{i+2}`
(so `B = v_{i+1}`).  The chord `d = F - E` satisfies `crs (e_i) d > 0`, `crs d (e_{i+1}) > 0`, `crs (e_{i+1}) (-e_i) > 0`: the triangle `B E F` has `B` on the RIGHT of `E -> F`.
* `chord_geo`: these three crosses.
* `wd_triangle`: `wd u v + wd v w + wd w (-u) = pi` whenever the three consecutive crosses are positive (angle sum of the triangle `BEF` for the sector widths).
* `exit_F`: no tile has a left step from `F` along `d` or a right step arriving at `F` from further along `d` (beyond `F` lies outside the polygon).
-/

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem toV2_lin (a b : ℝ) (u w : Plane) :
    toV2 (a • u + b • w) = (a * (toV2 u).1 + b * (toV2 w).1, a * (toV2 u).2 + b * (toV2 w).2) := by
  unfold toV2; simp

/-- The chord `F - E` between interior points of two adjacent sides. -/
theorem chord_vec (P : ConvPoly M) (i : Fin M) {t t' : ℝ} {E F : Plane}
    (hE : E = (1 - t) • P.v i + t • P.v (i + 1)) (hF : F = (1 - t') • P.v (i + 1) + t' • P.v (i + 1 + 1)) :
    toV2 (F - E) = ((1 - t) * (toV2 (P.e i)).1 + t' * (toV2 (P.e (i + 1))).1,
      (1 - t) * (toV2 (P.e i)).2 + t' * (toV2 (P.e (i + 1))).2) := by
  rw [← toV2_lin]
  congr 1
  rw [hE, hF]
  unfold ConvPoly.e
  ext j; simp; ring

theorem chord_geo (P : ConvPoly M) (i : Fin M) {t t' : ℝ} (ht1 : t < 1) (ht0' : 0 < t') {E F : Plane}
    (hE : E = (1 - t) • P.v i + t • P.v (i + 1)) (hF : F = (1 - t') • P.v (i + 1) + t' • P.v (i + 1 + 1)) :
    0 < crs (toV2 (P.e i)) (toV2 (F - E)) ∧ 0 < crs (toV2 (F - E)) (toV2 (P.e (i + 1))) ∧
      0 < crs (toV2 (P.e (i + 1))) (-(toV2 (P.e i)).1, -(toV2 (P.e i)).2) := by
  have hc := crs_consecutive_pos P i
  rw [chord_vec P i hE hF]
  refine ⟨?_, ?_, ?_⟩
  · have : crs (toV2 (P.e i)) ((1 - t) * (toV2 (P.e i)).1 + t' * (toV2 (P.e (i + 1))).1,
        (1 - t) * (toV2 (P.e i)).2 + t' * (toV2 (P.e (i + 1))).2) = t' * crs (toV2 (P.e i)) (toV2 (P.e (i + 1))) := by
      unfold crs; simp only; ring
    rw [this]; exact mul_pos ht0' hc
  · have : crs ((1 - t) * (toV2 (P.e i)).1 + t' * (toV2 (P.e (i + 1))).1,
        (1 - t) * (toV2 (P.e i)).2 + t' * (toV2 (P.e (i + 1))).2) (toV2 (P.e (i + 1))) = (1 - t) * crs (toV2 (P.e i)) (toV2 (P.e (i + 1))) := by
      unfold crs; simp only; ring
    rw [this]; exact mul_pos (by linarith) hc
  · have : crs (toV2 (P.e (i + 1))) (-(toV2 (P.e i)).1, -(toV2 (P.e i)).2) = crs (toV2 (P.e i)) (toV2 (P.e (i + 1))) := by
      unfold crs; simp only; ring
    rw [this]; exact hc

/-- The angle sum of the triangle `B E F` in terms of sector widths. -/
theorem wd_triangle {u v w : V2} (h1 : 0 < crs u v) (h2 : 0 < crs v w) (h3 : 0 < crs w (-u.1, -u.2)) :
    wd u v + wd v w + wd w (-u.1, -u.2) = Real.pi := by
  have hu : u ≠ 0 := by rintro rfl; unfold crs at h1; simp at h1
  have hv : v ≠ 0 := by rintro rfl; unfold crs at h1; simp at h1
  have hw : w ≠ 0 := by rintro rfl; unfold crs at h2; simp at h2
  have hu' : (-u.1, -u.2) ≠ (0 : V2) := by
    intro h; apply hu; have a := congrArg Prod.fst h; have b := congrArg Prod.snd h
    exact Prod.ext (by simpa using a) (by simpa using b)
  have z1 := hz_ne hu hv h1.le
  have z2 := hz_ne hv hw h2.le
  have z3 := hz_ne hw hu' h3.le
  have e12 : hz u v * hz v w = ((nsq v : ℝ) : ℂ) * hz u w := hz_mul u v w
  have hnv : 0 < nsq v := nsq_pos hv
  have hnw : 0 < nsq w := nsq_pos hw
  have hz12 : hz u w ≠ 0 := by
    intro h; apply mul_ne_zero z1 z2; rw [e12, h]; simp
  have e123 : (hz u v * hz v w) * hz w (-u.1, -u.2) = ((nsq v * nsq w : ℝ) : ℂ) * hz u (-u.1, -u.2) := by
    rw [e12, mul_assoc, hz_mul u w (-u.1, -u.2)]; push_cast; ring
  have hneg : hz u (-u.1, -u.2) = ((-(nsq u) : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [hz, Complex.ofReal_re]; unfold dt nsq; ring
    · simp only [hz, Complex.ofReal_im]; unfold crs; ring
  have hnu : 0 < nsq u := nsq_pos hu
  have harg : Complex.arg ((hz u v * hz v w) * hz w (-u.1, -u.2)) = Real.pi := by
    rw [e123, hneg, ← Complex.ofReal_mul, Complex.arg_ofReal_of_neg]
    nlinarith [mul_pos hnv hnw]
  have a1 : 0 < wd u v := wd_pos (Or.inl h1)
  have a2 : 0 < wd v w := wd_pos (Or.inl h2)
  have a3 : 0 < wd w (-u.1, -u.2) := wd_pos (Or.inl h3)
  have b1 : wd u v < Real.pi := wd_lt_pi_of_crs_pos h1
  have b2 : wd v w < Real.pi := wd_lt_pi_of_crs_pos h2
  have b3 : wd w (-u.1, -u.2) < Real.pi := wd_lt_pi_of_crs_pos h3
  have hang : ((wd u v + wd v w + wd w (-u.1, -u.2) : ℝ) : Real.Angle) = ((Real.pi : ℝ) : Real.Angle) := by
    have := Complex.arg_mul_coe_angle (mul_ne_zero z1 z2) z3
    rw [Complex.arg_mul_coe_angle z1 z2, harg] at this
    rw [wd_eq_arg_hz, wd_eq_arg_hz, wd_eq_arg_hz]
    push_cast
    exact this.symm
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hang
  have hpi := Real.pi_pos
  have hk1 : (k : ℝ) < 1 := by
    by_contra hh; push Not at hh
    nlinarith
  have hk2 : (-1 : ℝ) < k := by
    by_contra hh; push Not at hh
    nlinarith
  have hk1' : k < 1 := by exact_mod_cast hk1
  have hk2' : -1 < k := by exact_mod_cast hk2
  have hk0 : k = 0 := by omega
  rw [hk0] at hk
  simp at hk
  linarith

end Erdos634.Draft.LaczFormal.RG
