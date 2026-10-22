import Erdos634.Draft.ZhangRat2Transport

/-!
# Zhang Prop 11: the tiling hypothesis derived from Prop 6(2)

`ZhangProp11.zhang_prop11_core` (and `ZhangRat.zhang_prop11_*_rational`) take as hypothesis that the
integer-length triangle `A D B` (sides `(a+2b) m a`, `(b+2a) b m`, `c^2 m`) is tiled by `n0` model
tiles.  Here that hypothesis is DERIVED from Zhang's Prop 6(2) (`zhang_prop6_2`, triangle with sides
`(a+2b)ab`, `(b+2a)b^2`, `b c^2`) when `a < b`, `gcd(a,b) = 1` and `b ∣ m`: the placed triangle is
congruent to the `t`-fold dilate (`m = b t`) of the Prop 6(2) triangle (`Dis_scale_congr`), so it carries
`(a+2b)(b+2a) m^2` tiles.  For part (2) (`a <-> b` exchange) the same Prop 6(2) triangle is used with
the vertex order reversed (a reflection).  LIMIT: `b ∣ m` (not every `m`) and `a < b`
(`a > b` would need Prop 6(2) for the swapped tile, whose hypothesis `a<b` fails).  UNAUDITED.
Credit Zhang (arXiv 2512.22696), Beeson, Beeson-Zhang, Laczkovich.
-/

set_option maxHeartbeats 3200000

namespace Erdos634.ZhangRat2

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.SssCongruent Erdos634.ZhangPara Erdos634.ZhangL1 Erdos634.ZhangLat Erdos634.ZhangProp6
  Erdos634.ZhangProp6b Erdos634.ZhangSporadic

theorem dsq_lat (u v u' v' : ℝ) :
    (shx 0 u v - shx 0 u' v') ^ 2 + (shy 0 v - shy 0 v') ^ 2
      = (u - u') ^ 2 + (u - u') * (v - v') + (v - v') ^ 2 := by
  have := zs_sq
  simp only [shx, shy]
  linear_combination ((v - v') ^ 2 / 4) * this

theorem det62 (a d t : ℝ) (ha : 0 < a) (hd : 0 < d) (ht : 0 < t) :
    0 < det3 (t * qAu a d) 0 (t * pFu a d) 0 (t * qBu a d) (t * qBv a d) := by
  have : det3 (t * qAu a d) 0 (t * pFu a d) 0 (t * qBu a d) (t * qBv a d)
      = t ^ 2 * (a * (a + d) * (a + 2 * (a + d))) * ((a + d) ^ 2 * (3 * a + d)) := by
    simp only [det3, pFu, pX, pY, pW, qAu, qBu, qBv]; ring
  rw [this]; positivity

/-- the Prop 6(2) triangle, dilated by `t`, in lattice coordinates. -/
noncomputable def T62 (a d t : ℝ) (ha : 0 < a) (hd : 0 < d) (ht : 0 < t) : Tri :=
  triUV 0 0 (t * qAu a d) 0 (t * pFu a d) 0 (t * qBu a d) (t * qBv a d) (det62 a d t ha hd ht)

theorem T62_one_carrier (a d : ℝ) (ha : 0 < a) (hd : 0 < d) :
    (T62 a d 1 ha hd one_pos).carrier = ZhangLat.LT (qAu a d) 0 (pFu a d) 0 (qBu a d) (qBv a d) := by
  have h0 : 0 < det3 (qAu a d) 0 (pFu a d) 0 (qBu a d) (qBv a d) := by
    have := det62 a d 1 ha hd one_pos
    simpa using this
  have e := TriSet_eq_carrier (det_raw_pos 0 0 _ _ _ _ _ _ h0)
  unfold ZhangLat.LT
  rw [e]
  have : T62 a d 1 ha hd one_pos = triUV 0 0 (qAu a d) 0 (pFu a d) 0 (qBu a d) (qBv a d) h0 := by
    unfold T62; simp only [one_mul]
  rw [this]; rfl

theorem T62_pts (a d t : ℝ) (ha : 0 < a) (hd : 0 < d) (ht : 0 < t) (i : Fin 3) :
    (T62 a d t ha hd ht).pts i = t • (T62 a d 1 ha hd one_pos).pts i := by
  unfold T62 triUV
  fin_cases i <;> simp only [mkTri_pts] <;> simp [mkPt_smul, shx, shy] <;> (try (congr 1 <;> ring))


theorem Dis_T62_base (a d c : ℕ) (ha : 0 < a) (hd : 0 < d)
    (hcab : c * c = a * a + (a + d) * (a + d) + a * (a + d)) (hcop : Nat.Coprime a (a + d)) :
    Dis (RM a (a + d) ha (by omega))
      (T62 (a : ℝ) (d : ℝ) 1 (Nat.cast_pos.mpr ha) (Nat.cast_pos.mpr hd) one_pos).carrier
      (((a + d) + 2 * a) * (a + 2 * (a + d)) * ((a + d) * (a + d))) := by
  have h := ZhangProp6b.zhang_prop6_2 a d c ha hd hcab hcop
  rw [T62_one_carrier]
  exact h

section tiled
variable (a d c t : ℕ) (ha : 0 < a) (hd : 0 < d)
  (hcab : c * c = a * a + (a + d) * (a + d) + a * (a + d)) (hcop : Nat.Coprime a (a + d)) (ht : 0 < t)
include ha hd hcab hcop ht

/-- **Prop 11 (1) tiling hypothesis, derived** (`m = (a+d) t`, `a < b = a+d`): the integer-length
triangle `A D B` is tiled by `t^2 (b+2a)(a+2b) b^2 = (a+2b)(b+2a) m^2` model tiles. -/
theorem prop11_1_tiled (Ax Ay Bx By Dx Dy : ℝ) (hD : 0 < det3 Ax Ay Dx Dy Bx By)
    (hAD : (Ax - Dx) ^ 2 + (Ay - Dy) ^ 2
      = ((((a : ℝ) + 2 * ((a + d : ℕ) : ℝ)) * (((a + d) * t : ℕ) : ℝ)) * a) ^ 2)
    (hBD : (Bx - Dx) ^ 2 + (By - Dy) ^ 2
      = (((((a + d : ℕ) : ℝ) + 2 * a) * ((a + d : ℕ) : ℝ)) * (((a + d) * t : ℕ) : ℝ)) ^ 2)
    (hAB : (Ax - Bx) ^ 2 + (Ay - By) ^ 2
      = ((((a : ℝ) ^ 2 + a * ((a + d : ℕ) : ℝ) + ((a + d : ℕ) : ℝ) ^ 2)) * (((a + d) * t : ℕ) : ℝ)) ^ 2) :
    Dis (RM a (a + d) ha (by omega)) (TriSet Ax Ay Dx Dy Bx By)
      (((a + d) + 2 * a) * (a + 2 * (a + d)) * (((a + d) * t) * ((a + d) * t))) := by
  have ha' : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have ht' : (0 : ℝ) < t := Nat.cast_pos.mpr ht
  have h6 := Dis_T62_base a d c ha hd hcab hcop
  let T1 := T62 (a : ℝ) (d : ℝ) (t : ℝ) ha' hd' ht'
  let U := mkTri Ax Ay Dx Dy Bx By hD.ne'
  have p0 : T1.pts 0 = mkPt (shx 0 (t * qAu (a : ℝ) d) 0) (shy 0 0) := rfl
  have p1 : T1.pts 1 = mkPt (shx 0 (t * pFu (a : ℝ) d) 0) (shy 0 0) := rfl
  have p2 : T1.pts 2 = mkPt (shx 0 (t * qBu (a : ℝ) d) (t * qBv (a : ℝ) d)) (shy 0 (t * qBv (a : ℝ) d)) := rfl
  have u0 : U.pts 0 = mkPt Ax Ay := rfl
  have u1 : U.pts 1 = mkPt Dx Dy := rfl
  have u2 : U.pts 2 = mkPt Bx By := rfl
  have hcong : T1.Congruent U := by
    apply congruent_of_dist_three
    · apply dist_of_sq
      rw [p0, p1, u0, u1, dist_sq_mkPt, dist_sq_mkPt, dsq_lat, hAD]
      simp only [qAu, pFu, pX, pY, pW]; push_cast; ring
    · apply dist_of_sq
      rw [p1, p2, u1, u2, dist_sq_mkPt, dist_sq_mkPt, dsq_lat]
      have : (Dx - Bx) ^ 2 + (Dy - By) ^ 2 = (Bx - Dx) ^ 2 + (By - Dy) ^ 2 := by ring
      rw [this, hBD]
      simp only [qBu, qBv, pFu, pX, pY, pW]; push_cast; ring
    · apply dist_of_sq
      rw [p2, p0, u2, u0, dist_sq_mkPt, dist_sq_mkPt, dsq_lat]
      have : (Bx - Ax) ^ 2 + (By - Ay) ^ 2 = (Ax - Bx) ^ 2 + (Ay - By) ^ 2 := by ring
      rw [this, hAB]
      simp only [qAu, qBu, qBv]; push_cast; ring
  have := Dis_scale_congr ht h6 (T62_pts (a : ℝ) (d : ℝ) (t : ℝ) ha' hd' ht') hcong
  rw [TriSet_eq_carrier hD]
  refine this.congr rfl ?_
  ring

/-- **Prop 11 (2) tiling hypothesis, derived**: same Prop 6(2) triangle, vertices `(B,D,A)` (a reflection). -/
theorem prop11_2_tiled (Ax Ay Bx By Dx Dy : ℝ) (hD : 0 < det3 Ax Ay Dx Dy Bx By)
    (hAD : (Ax - Dx) ^ 2 + (Ay - Dy) ^ 2
      = (((((a + d : ℕ) : ℝ) + 2 * a) * (((a + d) * t : ℕ) : ℝ)) * ((a + d : ℕ) : ℝ)) ^ 2)
    (hBD : (Bx - Dx) ^ 2 + (By - Dy) ^ 2
      = ((((a : ℝ) + 2 * ((a + d : ℕ) : ℝ)) * a) * (((a + d) * t : ℕ) : ℝ)) ^ 2)
    (hAB : (Ax - Bx) ^ 2 + (Ay - By) ^ 2
      = ((((a : ℝ) ^ 2 + a * ((a + d : ℕ) : ℝ) + ((a + d : ℕ) : ℝ) ^ 2)) * (((a + d) * t : ℕ) : ℝ)) ^ 2) :
    Dis (RM a (a + d) ha (by omega)) (TriSet Ax Ay Dx Dy Bx By)
      (((a + d) + 2 * a) * (a + 2 * (a + d)) * (((a + d) * t) * ((a + d) * t))) := by
  have ha' : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have ht' : (0 : ℝ) < t := Nat.cast_pos.mpr ht
  have h6 := Dis_T62_base a d c ha hd hcab hcop
  let T1 := T62 (a : ℝ) (d : ℝ) (t : ℝ) ha' hd' ht'
  let U := mkTri Ax Ay Dx Dy Bx By hD.ne'
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 2
  have p0 : T1.pts 0 = mkPt (shx 0 (t * qAu (a : ℝ) d) 0) (shy 0 0) := rfl
  have p1 : T1.pts 1 = mkPt (shx 0 (t * pFu (a : ℝ) d) 0) (shy 0 0) := rfl
  have p2 : T1.pts 2 = mkPt (shx 0 (t * qBu (a : ℝ) d) (t * qBv (a : ℝ) d)) (shy 0 (t * qBv (a : ℝ) d)) := rfl
  have u0 : (permTri U σ).pts 0 = mkPt Bx By := by simp [permTri, σ, U]
  have s1 : σ 1 = 1 := Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  have u1 : (permTri U σ).pts 1 = mkPt Dx Dy := by simp [permTri, s1, U]
  have u2 : (permTri U σ).pts 2 = mkPt Ax Ay := by simp [permTri, σ, U]
  have hcong : T1.Congruent U := by
    refine (congruent_of_dist_three (U := permTri U σ) ?_ ?_ ?_).trans (congruent_permTri U σ)
    · apply dist_of_sq
      rw [p0, p1, u0, u1, dist_sq_mkPt, dist_sq_mkPt, dsq_lat, hBD]
      simp only [qAu, pFu, pX, pY, pW]; push_cast; ring
    · apply dist_of_sq
      rw [p1, p2, u1, u2, dist_sq_mkPt, dist_sq_mkPt, dsq_lat]
      have : (Dx - Ax) ^ 2 + (Dy - Ay) ^ 2 = (Ax - Dx) ^ 2 + (Ay - Dy) ^ 2 := by ring
      rw [this, hAD]
      simp only [qBu, qBv, pFu, pX, pY, pW]; push_cast; ring
    · apply dist_of_sq
      rw [p2, p0, u2, u0, dist_sq_mkPt, dist_sq_mkPt, dsq_lat]
      have : (Ax - Bx) ^ 2 + (Ay - By) ^ 2 = (Ax - Bx) ^ 2 + (Ay - By) ^ 2 := rfl
      rw [hAB]
      simp only [qAu, qBu, qBv]; push_cast; ring
  have := Dis_scale_congr ht h6 (T62_pts (a : ℝ) (d : ℝ) (t : ℝ) ha' hd' ht') hcong
  rw [TriSet_eq_carrier hD]
  refine this.congr rfl ?_
  ring

end tiled

/-- **Witness of the hypotheses of `prop11_1_tiled` / `prop11_2_tiled`** for `(a,d,t) = (3,2,1)` (tile
`(3,5,7)`, `m = 5`): the Prop 6(2) triangle itself in Cartesian coordinates; so the geometric
hypotheses (orientation and the three squared side lengths) are satisfiable. -/
theorem prop11_wit : ∃ Ax Ay Bx By Dx Dy : ℝ, 0 < det3 Ax Ay Dx Dy Bx By ∧
    (Ax - Dx) ^ 2 + (Ay - Dy) ^ 2
      = ((((3 : ℕ) : ℝ) + 2 * (((3 + 2 : ℕ)) : ℝ)) * (((3 + 2) * 1 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)) ^ 2 ∧
    (Bx - Dx) ^ 2 + (By - Dy) ^ 2
      = ((((((3 + 2 : ℕ)) : ℝ) + 2 * ((3 : ℕ) : ℝ)) * (((3 + 2 : ℕ)) : ℝ)) * (((3 + 2) * 1 : ℕ) : ℝ)) ^ 2 ∧
    (Ax - Bx) ^ 2 + (Ay - By) ^ 2
      = (((((3 : ℕ) : ℝ) ^ 2 + ((3 : ℕ) : ℝ) * (((3 + 2 : ℕ)) : ℝ) + (((3 + 2 : ℕ)) : ℝ) ^ 2))
          * (((3 + 2) * 1 : ℕ) : ℝ)) ^ 2 := by
  have h0 : 0 < det3 (qAu (3 : ℝ) (2 : ℕ)) 0 (pFu (3 : ℝ) (2 : ℕ)) 0 (qBu (3 : ℝ) (2 : ℕ)) (qBv (3 : ℝ) (2 : ℕ)) := by
    have := det62 3 2 1 (by norm_num) (by norm_num) one_pos
    simp only [one_mul] at this
    simpa using this
  refine ⟨shx 0 (qAu (3 : ℝ) (2 : ℕ)) 0, shy 0 0, shx 0 (qBu (3 : ℝ) (2 : ℕ)) (qBv (3 : ℝ) (2 : ℕ)),
    shy 0 (qBv (3 : ℝ) (2 : ℕ)), shx 0 (pFu (3 : ℝ) (2 : ℕ)) 0, shy 0 0,
    det_raw_pos 0 0 _ _ _ _ _ _ h0, ?_, ?_, ?_⟩
  · rw [dsq_lat]; simp only [qAu, pFu, pX, pY, pW]; norm_num
  · rw [dsq_lat]; simp only [qBu, qBv, pFu, pX, pY, pW]; norm_num
  · rw [dsq_lat]; simp only [qAu, qBu, qBv]; norm_num

end Erdos634.ZhangRat2
