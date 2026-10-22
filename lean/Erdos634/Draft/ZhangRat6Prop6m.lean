import Erdos634.Draft.ZhangRat
import Erdos634.Draft.ZhangRegionDilate

/-!
# Zhang Proposition 6 for every integer `m >= 1` (arXiv 2512.22696v4, Fig. 7)

Printed: "For any integer `m >= 1` the following two tilings are possible: (1) the triangle with sides
`((a+2b) m a c, (b+2a) m b c, c^3 m)` into `(b+2a)(a+2b) m^2 c^2` copies of `(a,b,c)`; (2) `((a+2b) m a b,
(b+2a) m b^2, b c^2 m)` into `(b+2a)(a+2b) m^2 b^2` copies."  Printed proof: "it suffices to prove `m = 1`".
`ZhangProp6.zhang_prop6_1` / `ZhangProp6b.zhang_prop6_2` are the `m = 1` cases (with `b = a + d > a`, the
convention of Fig. 7 bottom).  Here the `m`-fold dilate about the origin (`ZhangRegionDilate.dilate_region`,
exact count `m * m * N`).  The region is stated as the `m`-dilate `dil m (LT ...)` of the `m = 1` triangle, which is the
triangle with the printed `m`-scaled sides.  UNAUDITED.
Credit Zhang (arXiv 2512.22696v4), Beeson, Beeson-Zhang, Laczkovich.
-/

namespace Erdos634.ZhangRat6

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.ZhangRat Erdos634.ZhangProp6 Erdos634.ZhangProp6b Erdos634.ZhangLat Erdos634.ZhangL1
  Erdos634.ZhangPara

theorem zhang_prop6_1_m (a d c m : ℕ) (ha : 0 < a) (hd : 0 < d)
    (hcab : c * c = a * a + (a + d) * (a + d) + a * (a + d)) (hcop : Nat.Coprime a (a + d))
    (hm : 0 < m) :
    ∃ C : CongruentRegionDissection (m * m * (((a + d) + 2 * a) * (a + 2 * (a + d)) * (c * c))),
      C.region = dil (m : ℝ)
        (LT 0 (pAv (a : ℝ) d) (pCu (a : ℝ) d) 0 (pBu (a : ℝ) d) (pBv (a : ℝ) d)) ∧
      C.model = Rmodel (Nat.cast_pos.mpr ha : (0:ℝ) < a)
        (Nat.cast_pos.mpr (by omega) : (0:ℝ) < ((a + d : ℕ) : ℝ)) := by
  obtain ⟨C0, hr, hmod⟩ := zhang_prop6_1 a d c ha hd hcab hcop
  obtain ⟨C1, h1, h2⟩ := Erdos634.ZhangRegionDilate.dilate_region C0 0 m hm
  refine ⟨C1, ?_, by rw [h2, hmod]⟩
  rw [h1, hr]
  exact hom_image_eq (m : ℝ) (by exact_mod_cast hm) _

theorem zhang_prop6_2_m (a d c m : ℕ) (ha : 0 < a) (hd : 0 < d)
    (hcab : c * c = a * a + (a + d) * (a + d) + a * (a + d)) (hcop : Nat.Coprime a (a + d))
    (hm : 0 < m) :
    ∃ C : CongruentRegionDissection (m * m * (((a + d) + 2 * a) * (a + 2 * (a + d)) * ((a + d) * (a + d)))),
      C.region = dil (m : ℝ)
        (LT (qAu (a : ℝ) d) 0 (pFu (a : ℝ) d) 0 (qBu (a : ℝ) d) (qBv (a : ℝ) d)) ∧
      C.model = Rmodel (Nat.cast_pos.mpr ha : (0:ℝ) < a)
        (Nat.cast_pos.mpr (by omega) : (0:ℝ) < ((a + d : ℕ) : ℝ)) := by
  obtain ⟨C0, hr, hmod⟩ := zhang_prop6_2 a d c ha hd hcab hcop
  obtain ⟨C1, h1, h2⟩ := Erdos634.ZhangRegionDilate.dilate_region C0 0 m hm
  refine ⟨C1, ?_, by rw [h2, hmod]⟩
  rw [h1, hr]
  exact hom_image_eq (m : ℝ) (by exact_mod_cast hm) _

/-- witness `(3,5,7)`, `m = 2`: `4 * 7007` and `4 * 3575` tiles. -/
theorem prop6_m_wit : (∃ C : CongruentRegionDissection (2 * 2 * 7007), True) ∧
    ∃ C : CongruentRegionDissection (2 * 2 * 3575), True := by
  obtain ⟨C1, -⟩ := zhang_prop6_1_m 3 2 7 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C2, -⟩ := zhang_prop6_2_m 3 2 7 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨⟨C1, trivial⟩, ⟨C2, trivial⟩⟩

end Erdos634.ZhangRat6

#print axioms Erdos634.ZhangRat6.zhang_prop6_1_m
#print axioms Erdos634.ZhangRat6.zhang_prop6_2_m
#print axioms Erdos634.ZhangRat6.prop6_m_wit
