import Erdos634.Draft.ZhangProp11

/-!
# Zhang Proposition 11 (2) (arXiv 2512.22696v4, Fig. 12): triangles `(beta, 2 beta, 3 alpha)`

Part (2) is the exchange `a <-> b` of Part (1) (`ZhangProp11.zhang_prop11_core`).  Here the tile is
still `(a,b,c)`, `c^2 = a^2+ab+b^2`; the triangle `A D B` (counterclockwise) has `AD = (b+2a) m b`,
`BD = (a+2b) m a`, `AB = c^2 m`; if it carries `n0` tiles then `A C B`, `C = D + ((b+2a)/(a+2b))(D-B)`,
`BC = 3(a+b) m a`, carries `n0 + ((b+2a) m)^2` tiles; with `n0 = (b+2a)(a+2b) m^2`
this is `3 m^2 (2a+b)(a+b)`.  Proof: `zhang_prop11_core b a m` together with `Dis_swap`
(`(a,b,c)` and `(b,a,c)` are congruent).  The witness needs the triangle of Prop 6(2) in the
opposite orientation, so a plane reflection transports a `Dis` (`Dis_mirror`, via
`mapCongruentRegionDissection`).  Credit Zhang (arXiv 2512.22696), Beeson, Beeson-Rosu, Laczkovich.
UNAUDITED.
-/

set_option maxHeartbeats 1600000

namespace Erdos634.ZhangProp11b

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.GlueCut Erdos634.SssCongruent Erdos634.ZhangL1 Erdos634.ZhangPara
  Erdos634.ZhangProp3 Erdos634.ZhangThm4 Erdos634.ZhangSporadic

/-- **Zhang Prop. 11 (2), metric form.** -/
theorem zhang_prop11_2_core (a b m : ℕ) (ha : 0 < a) (hb : 0 < b) (hm : 0 < m) {n0 : ℕ}
    (Ax Ay Bx By Dx Dy : ℝ) (hD : 0 < det3 Ax Ay Dx Dy Bx By)
    (hAD : (Ax - Dx) ^ 2 + (Ay - Dy) ^ 2 = (((b : ℝ) + 2 * a) * m * b) ^ 2)
    (hBD : (Bx - Dx) ^ 2 + (By - Dy) ^ 2 = (((a : ℝ) + 2 * b) * a * m) ^ 2)
    (hAB : (Ax - Bx) ^ 2 + (Ay - By) ^ 2 = (((a : ℝ) ^ 2 + a * b + b ^ 2) * m) ^ 2)
    (hT : Dis (RM a b ha hb) (TriSet Ax Ay Dx Dy Bx By) n0) :
    Dis (RM a b ha hb)
      (TriSet Ax Ay (Dx + ((b + 2 * a : ℝ) / (a + 2 * b)) * (Dx - Bx))
        (Dy + ((b + 2 * a : ℝ) / (a + 2 * b)) * (Dy - By)) Bx By)
      (n0 + ((b + 2 * a) * m) * ((b + 2 * a) * m)) := by
  have h := ZhangProp11.zhang_prop11_core b a m hb ha hm Ax Ay Bx By Dx Dy hD hAD
    (by rw [hBD]) (by rw [hAB]; ring) (n0 := n0) (Dis_swap _ _ hT)
  exact Dis_swap _ _ h

/-! ### Plane reflection transports a dissection -/

/-- Reflection `(x,y) -> (x,-y)`. -/
noncomputable def mir (p : Plane) : Plane := WithLp.toLp 2 ![p 0, - p 1]

@[simp] theorem mir_zero (p : Plane) : mir p 0 = p 0 := rfl
@[simp] theorem mir_one (p : Plane) : mir p 1 = - p 1 := rfl

theorem mir_inv (p : Plane) : mir (mir p) = p := by
  ext i; fin_cases i <;> simp

noncomputable def mirL : Plane ≃ₗᵢ[ℝ] Plane where
  toFun := mir
  invFun := mir
  map_add' := by intro x y; ext i; fin_cases i <;> simp; ring
  map_smul' := by intro c x; ext i; fin_cases i <;> simp
  left_inv := mir_inv
  right_inv := mir_inv
  norm_map' := by
    intro x
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]

theorem Dis_mirror {R : Tri} {S : Set Plane} {n : ℕ} (h : Dis R S n) :
    Dis R (mir '' S) n := by
  obtain ⟨C, hr, hm⟩ := h
  refine ⟨mapCongruentRegionDissection mirL.toAffineIsometryEquiv C, ?_, hm⟩
  show mirL.toAffineIsometryEquiv.toAffineEquiv '' C.region = _
  rw [hr]; rfl

theorem mir_image_TriSet (x0 y0 x1 y1 x2 y2 : ℝ) :
    mir '' TriSet x0 y0 x1 y1 x2 y2 = TriSet x0 (-y0) x2 (-y2) x1 (-y1) := by
  ext p
  simp only [Set.mem_image, TriSet, Set.mem_setOf_eq, det3]
  constructor
  · rintro ⟨q, ⟨h1, h2, h3⟩, rfl⟩
    simp only [mir_zero, mir_one]
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨h1, h2, h3⟩
    refine ⟨mir p, ?_, mir_inv p⟩
    simp only [mir_zero, mir_one]
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith

/-! ### Witness `(a,b,c) = (3,5,7)`, `m = 5` -/

/-- Prop 11 (2) witness.  `A* = B0'`, `D* = D0'`, `B* = A0'` are the mirror images of the vertices of
the `3575`-tile triangle of Prop 6(2) (`A0 = (-18,0)`, `D0 = (177,0)`, `B0 = (-98,275)` lattice
coordinates), so `A*D* = 275 = (b+2a) m b`, `B*D* = 195 = (a+2b) m a`, `A*B* = 245 = c^2 m`;
the triangle `A* C B*` carries `3575 + 55^2 = 6600 = 3*25*11*8` tiles.  Area check: `A*D*B*` has
`3575` tiles of area `T`, `D* C B*` is the tile scaled by `55` (`3025 T`), total `6600 T`. -/
theorem zhang_prop11_2_357 :
    Dis (RM 3 5 (by norm_num) (by norm_num))
      (TriSet (shx 0 (-98) 275) (-(shy 0 275))
        (shx 0 177 0 + ((5 + 2 * 3 : ℝ) / (3 + 2 * 5)) * (shx 0 177 0 - shx 0 (-18) 0))
        (-(shy 0 0) + ((5 + 2 * 3 : ℝ) / (3 + 2 * 5)) * (-(shy 0 0) - -(shy 0 0)))
        (shx 0 (-18) 0) (-(shy 0 0))) 6600 := by
  have h := ZhangProp6b.zhang_prop6_2 3 2 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hz := zs_sq
  have hzp := zs_pos
  have h0 : Dis (RM 3 5 (by norm_num) (by norm_num))
      (TriSet (shx 0 (-18) 0) (shy 0 0) (shx 0 177 0) (shy 0 0) (shx 0 (-98) 275) (shy 0 275)) 3575 :=
    h.congr (by
      simp only [ZhangProp6b.qAu, ZhangProp6.pFu, ZhangProp6.pX, ZhangProp6.pY, ZhangProp6.pW,
        ZhangProp6b.qBu, ZhangProp6b.qBv, ZhangLat.LT]
      norm_num <;> rfl) (by norm_num)
  have hm := Dis_mirror h0
  rw [mir_image_TriSet] at hm
  -- hm : TriSet A0' B0' D0'  ; rotate to (B0', D0', A0')
  have hr := Dis_rot _ _ _ _ _ _ hm
  have := zhang_prop11_2_core 3 5 5 (by norm_num) (by norm_num) (by norm_num)
    (shx 0 (-98) 275) (-(shy 0 275)) (shx 0 (-18) 0) (-(shy 0 0)) (shx 0 177 0) (-(shy 0 0))
    (by simp only [det3, shx, shy]; nlinarith)
    (by simp only [shx, shy]; norm_num <;> nlinarith)
    (by simp only [shx, shy]; norm_num <;> nlinarith)
    (by simp only [shx, shy]; norm_num <;> nlinarith)
    (n0 := 3575) (by simpa using hr)
  exact this.congr (by simp) (by norm_num)

end Erdos634.ZhangProp11b
