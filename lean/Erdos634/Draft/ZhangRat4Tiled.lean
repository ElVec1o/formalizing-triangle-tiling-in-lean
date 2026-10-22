import Erdos634.Draft.ZhangRat3Prop11

/-!
# Zhang Prop 11: the tiling hypothesis derived for EVERY admissible `m`

Zhang's Prop 11 (arXiv 2512.22696v4) assumes that the `((a+2b)am, (b+2a)bm, c^2 m)` triangle tiles into
`(a,b,c)`.  Its sides are exactly those of the lattice triangle of Zhang's Theorem 7
(`ZhangThm7.zhang_thm7`: `a(a+2b)m`, `b(b+2a)m`, `c^2 m`), which carries `(b+2a)(a+2b)m^2` tiles for all
`m > bc - b - c`.  Prop 6(2) (`ZhangRat2Prop11`) covers `b ∣ m`.  So the hypothesis is DERIVED for
`a < b` and every natural `m` with `b ∣ m` or `bc < m + b + c` ("admissible").  The admissibility
predicate is the exact range covered by Zhang's own earlier results (the printed Prop 11 does not
restrict `m`; "the assumptions" are exactly the tileability, which for the other `m` is not known to
follow from the earlier results).  `a > b` is covered by the part (2) statements only through the
exchange `a <-> b` (the hypothesis then needs Prop 6(2)/Thm 7 for the tile `(b,a,c)`, not available
since those need `a < b`).  UNAUDITED.  Credit Zhang (arXiv 2512.22696v4), Beeson, Beeson-Zhang, Laczkovich.
-/

set_option maxHeartbeats 3200000

namespace Erdos634.ZhangRat4

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.SssCongruent Erdos634.ZhangPara Erdos634.ZhangL1 Erdos634.ZhangLat Erdos634.ZhangProp6
  Erdos634.ZhangProp6b Erdos634.ZhangSporadic Erdos634.ZhangRat2

/-- Admissible `m` for the tile with sides `a < b = a+d`, `c`: Prop 6(2) (`b ∣ m`) or Thm 7. -/
def Adm (a d c m : ℕ) : Prop := (a + d) ∣ m ∨ (a + d) * c < m + (a + d) + c

/-- the Theorem-7 triangle of parameter `m`, as a `Tri`. -/
noncomputable def T7 (a d m : ℕ) (ha : 0 < a) (hd : 0 < d) (hm : 0 < m) : Tri :=
  triUV 0 0 0 0 ((a : ℝ) * (a + 2 * ((a : ℝ) + d)) * m) 0
    (((a : ℝ) * (a + 2 * ((a : ℝ) + d)) - ((a : ℝ) + d) * (2 * a + ((a : ℝ) + d))) * m)
    ((((a : ℝ) + d)) * (2 * a + ((a : ℝ) + d)) * m)
    (by
      have ha' : (0 : ℝ) < a := Nat.cast_pos.mpr ha
      have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
      have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
      have : det3 0 0 ((a : ℝ) * (a + 2 * ((a : ℝ) + d)) * m) 0
          (((a : ℝ) * (a + 2 * ((a : ℝ) + d)) - ((a : ℝ) + d) * (2 * a + ((a : ℝ) + d))) * m)
          ((((a : ℝ) + d)) * (2 * a + ((a : ℝ) + d)) * m)
          = ((a : ℝ) * (a + 2 * ((a : ℝ) + d)) * m) * ((((a : ℝ) + d)) * (2 * a + ((a : ℝ) + d)) * m) := by
        simp only [det3]; ring
      rw [this]; positivity)

theorem T7_carrier (a d m : ℕ) (ha : 0 < a) (hd : 0 < d) (hm : 0 < m) :
    (T7 a d m ha hd hm).carrier = LT 0 0 ((a : ℝ) * (a + 2 * ((a : ℝ) + d)) * m) 0
      (((a : ℝ) * (a + 2 * ((a : ℝ) + d)) - ((a : ℝ) + d) * (2 * a + ((a : ℝ) + d))) * m)
      ((((a : ℝ) + d)) * (2 * a + ((a : ℝ) + d)) * m) := by
  have ha' : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have h0 : 0 < det3 0 0 ((a : ℝ) * (a + 2 * ((a : ℝ) + d)) * m) 0
          (((a : ℝ) * (a + 2 * ((a : ℝ) + d)) - ((a : ℝ) + d) * (2 * a + ((a : ℝ) + d))) * m)
          ((((a : ℝ) + d)) * (2 * a + ((a : ℝ) + d)) * m) := by
    have : det3 0 0 ((a : ℝ) * (a + 2 * ((a : ℝ) + d)) * m) 0
          (((a : ℝ) * (a + 2 * ((a : ℝ) + d)) - ((a : ℝ) + d) * (2 * a + ((a : ℝ) + d))) * m)
          ((((a : ℝ) + d)) * (2 * a + ((a : ℝ) + d)) * m)
          = ((a : ℝ) * (a + 2 * ((a : ℝ) + d)) * m) * ((((a : ℝ) + d)) * (2 * a + ((a : ℝ) + d)) * m) := by
      simp only [det3]; ring
    rw [this]; positivity
  have e := TriSet_eq_carrier (det_raw_pos 0 0 _ _ _ _ _ _ h0)
  unfold ZhangLat.LT
  rw [e]
  rfl

theorem T7_pts_self (a d m : ℕ) (ha : 0 < a) (hd : 0 < d) (hm : 0 < m) (i : Fin 3) :
    (T7 a d m ha hd hm).pts i = ((1 : ℕ) : ℝ) • (T7 a d m ha hd hm).pts i := by simp

section tiled
variable (a d c m : ℕ) (ha : 0 < a) (hd : 0 < d)
  (hcab : c * c = a * a + (a + d) * (a + d) + a * (a + d)) (hcop : Nat.Coprime a (a + d)) (hm : 0 < m)

include ha hd hcab hcop hm

/-- **Prop 11 (1) tiling hypothesis for every admissible `m`.** -/
theorem prop11_1_tiled_all (hadm : Adm a d c m) (Ax Ay Bx By Dx Dy : ℝ)
    (hD : 0 < det3 Ax Ay Dx Dy Bx By)
    (hAD : (Ax - Dx) ^ 2 + (Ay - Dy) ^ 2
      = ((((a : ℝ) + 2 * ((a + d : ℕ) : ℝ)) * (m : ℝ)) * a) ^ 2)
    (hBD : (Bx - Dx) ^ 2 + (By - Dy) ^ 2
      = (((((a + d : ℕ) : ℝ) + 2 * a) * ((a + d : ℕ) : ℝ)) * (m : ℝ)) ^ 2)
    (hAB : (Ax - Bx) ^ 2 + (Ay - By) ^ 2
      = ((((a : ℝ) ^ 2 + a * ((a + d : ℕ) : ℝ) + ((a + d : ℕ) : ℝ) ^ 2)) * (m : ℝ)) ^ 2) :
    Dis (RM a (a + d) ha (by omega)) (TriSet Ax Ay Dx Dy Bx By)
      (((a + d) + 2 * a) * (a + 2 * (a + d)) * (m * m)) := by
  rcases hadm with ⟨t, rfl⟩ | hlt
  · have ht : 0 < t := Nat.pos_of_mul_pos_left hm |> fun h => by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · subst h0; simp at hm
      · exact h0
    have := ZhangRat2.prop11_1_tiled a d c t ha hd hcab hcop ht Ax Ay Bx By Dx Dy hD
      (by rw [hAD]; all_goals (push_cast; try ring)) (by rw [hBD]; all_goals (push_cast; try ring)) (by rw [hAB]; all_goals (push_cast; try ring))
    exact this
  · have ha' : (0 : ℝ) < a := Nat.cast_pos.mpr ha
    have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
    have h7 := ZhangThm7.zhang_thm7 a d c m ha hd hcab hcop hlt
    let T1 := T7 a d m ha hd hm
    let U := mkTri Ax Ay Dx Dy Bx By hD.ne'
    have p0 : T1.pts 0 = mkPt (shx 0 0 0) (shy 0 0) := rfl
    have p1 : T1.pts 1 = mkPt (shx 0 ((a : ℝ) * (a + 2 * ((a : ℝ) + d)) * m) 0) (shy 0 0) := rfl
    have p2 : T1.pts 2 = mkPt
        (shx 0 (((a : ℝ) * (a + 2 * ((a : ℝ) + d)) - ((a : ℝ) + d) * (2 * a + ((a : ℝ) + d))) * m)
          ((((a : ℝ) + d)) * (2 * a + ((a : ℝ) + d)) * m))
        (shy 0 ((((a : ℝ) + d)) * (2 * a + ((a : ℝ) + d)) * m)) := rfl
    have u0 : U.pts 0 = mkPt Ax Ay := rfl
    have u1 : U.pts 1 = mkPt Dx Dy := rfl
    have u2 : U.pts 2 = mkPt Bx By := rfl
    have hcong : T1.Congruent U := by
      apply congruent_of_dist_three
      · apply dist_of_sq
        rw [p0, p1, u0, u1, dist_sq_mkPt, dist_sq_mkPt, dsq_lat, hAD]
        push_cast; ring
      · apply dist_of_sq
        rw [p1, p2, u1, u2, dist_sq_mkPt, dist_sq_mkPt, dsq_lat]
        have : (Dx - Bx) ^ 2 + (Dy - By) ^ 2 = (Bx - Dx) ^ 2 + (By - Dy) ^ 2 := by ring
        rw [this, hBD]
        push_cast; ring
      · apply dist_of_sq
        rw [p2, p0, u2, u0, dist_sq_mkPt, dist_sq_mkPt, dsq_lat]
        have : (Bx - Ax) ^ 2 + (By - Ay) ^ 2 = (Ax - Bx) ^ 2 + (Ay - By) ^ 2 := by ring
        rw [this, hAB]
        push_cast; ring
    have h7' : Dis (RM a (a + d) ha (by omega)) T1.carrier
        (((a + d) + 2 * a) * (a + 2 * (a + d)) * (m * m)) := by
      rw [T7_carrier]; exact h7
    have := Dis_scale_congr (t := 1) one_pos h7' (T7_pts_self a d m ha hd hm) hcong
    rw [TriSet_eq_carrier hD]
    refine this.congr rfl ?_
    ring

/-- **Prop 11 (2) tiling hypothesis for every admissible `m`** (vertex order `(B,D,A)`: a reflection). -/
theorem prop11_2_tiled_all (hadm : Adm a d c m) (Ax Ay Bx By Dx Dy : ℝ)
    (hD : 0 < det3 Ax Ay Dx Dy Bx By)
    (hAD : (Ax - Dx) ^ 2 + (Ay - Dy) ^ 2
      = (((((a + d : ℕ) : ℝ) + 2 * a) * (m : ℝ)) * ((a + d : ℕ) : ℝ)) ^ 2)
    (hBD : (Bx - Dx) ^ 2 + (By - Dy) ^ 2
      = ((((a : ℝ) + 2 * ((a + d : ℕ) : ℝ)) * a) * (m : ℝ)) ^ 2)
    (hAB : (Ax - Bx) ^ 2 + (Ay - By) ^ 2
      = ((((a : ℝ) ^ 2 + a * ((a + d : ℕ) : ℝ) + ((a + d : ℕ) : ℝ) ^ 2)) * (m : ℝ)) ^ 2) :
    Dis (RM a (a + d) ha (by omega)) (TriSet Ax Ay Dx Dy Bx By)
      (((a + d) + 2 * a) * (a + 2 * (a + d)) * (m * m)) := by
  rcases hadm with ⟨t, rfl⟩ | hlt
  · have ht : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · subst h0; simp at hm
      · exact h0
    exact ZhangRat2.prop11_2_tiled a d c t ha hd hcab hcop ht Ax Ay Bx By Dx Dy hD
      (by rw [hAD]; all_goals (push_cast; try ring)) (by rw [hBD]; all_goals (push_cast; try ring)) (by rw [hAB]; all_goals (push_cast; try ring))
  · have h7 := ZhangThm7.zhang_thm7 a d c m ha hd hcab hcop hlt
    let T1 := T7 a d m ha hd hm
    let U := mkTri Ax Ay Dx Dy Bx By hD.ne'
    let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 2
    have p0 : T1.pts 0 = mkPt (shx 0 0 0) (shy 0 0) := rfl
    have p1 : T1.pts 1 = mkPt (shx 0 ((a : ℝ) * (a + 2 * ((a : ℝ) + d)) * m) 0) (shy 0 0) := rfl
    have p2 : T1.pts 2 = mkPt
        (shx 0 (((a : ℝ) * (a + 2 * ((a : ℝ) + d)) - ((a : ℝ) + d) * (2 * a + ((a : ℝ) + d))) * m)
          ((((a : ℝ) + d)) * (2 * a + ((a : ℝ) + d)) * m))
        (shy 0 ((((a : ℝ) + d)) * (2 * a + ((a : ℝ) + d)) * m)) := rfl
    have u0 : (permTri U σ).pts 0 = mkPt Bx By := by simp [permTri, σ, U]
    have s1 : σ 1 = 1 := Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
    have u1 : (permTri U σ).pts 1 = mkPt Dx Dy := by simp [permTri, s1, U]
    have u2 : (permTri U σ).pts 2 = mkPt Ax Ay := by simp [permTri, σ, U]
    have hcong : T1.Congruent U := by
      refine (congruent_of_dist_three (U := permTri U σ) ?_ ?_ ?_).trans (congruent_permTri U σ)
      · apply dist_of_sq
        rw [p0, p1, u0, u1, dist_sq_mkPt, dist_sq_mkPt, dsq_lat, hBD]
        push_cast; ring
      · apply dist_of_sq
        rw [p1, p2, u1, u2, dist_sq_mkPt, dist_sq_mkPt, dsq_lat]
        have : (Dx - Ax) ^ 2 + (Dy - Ay) ^ 2 = (Ax - Dx) ^ 2 + (Ay - Dy) ^ 2 := by ring
        rw [this, hAD]
        push_cast; ring
      · apply dist_of_sq
        rw [p2, p0, u2, u0, dist_sq_mkPt, dist_sq_mkPt, dsq_lat]
        rw [hAB]
        push_cast; ring
    have h7' : Dis (RM a (a + d) ha (by omega)) T1.carrier
        (((a + d) + 2 * a) * (a + 2 * (a + d)) * (m * m)) := by
      rw [T7_carrier]; exact h7
    have := Dis_scale_congr (t := 1) one_pos h7' (T7_pts_self a d m ha hd hm) hcong
    rw [TriSet_eq_carrier hD]
    refine this.congr rfl ?_
    ring

end tiled

/-- non-vacuity of `Adm`: for every tile all `m > bc - b - c` are admissible. -/
theorem adm_large (a d c m : ℕ) (h : (a + d) * c < m + (a + d) + c) : Adm a d c m := Or.inr h

end Erdos634.ZhangRat4

#print axioms Erdos634.ZhangRat4.prop11_1_tiled_all
#print axioms Erdos634.ZhangRat4.prop11_2_tiled_all
