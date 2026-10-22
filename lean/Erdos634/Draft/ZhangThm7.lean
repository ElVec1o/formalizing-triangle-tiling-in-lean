import Erdos634.Draft.ZhangProp11
import Erdos634.Draft.CVCCevianCut

/-!
# Triangle dilation lemma and Zhang Theorem 7 (arXiv 2512.22696v4, Fig. 8)

* `Dis_dilate`: if a triangle `x0 x1 x2` (counterclockwise) carries `n` tiles congruent to `R`, its
  homothetic image of integer ratio `k` about `x0` carries `k*k*n` (via `Erdos634.Ladder.ladder`).
  This is the TRIANGLE case of "region dilation"; a dilation of an arbitrary region dissection
  is not proved here.
Credit Zhang (arXiv 2512.22696), Beeson, Beeson-Rosu, Laczkovich.  UNAUDITED.
-/

namespace Erdos634.ZhangThm7

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.GlueCut Erdos634.SssCongruent Erdos634.ZhangL1 Erdos634.ZhangPara
  Erdos634.ZhangProp3 Erdos634.ZhangThm4 Erdos634.ZhangSporadic Erdos634.Subdivision

theorem Dis_dilate {R : Tri} {n : ℕ} (x0 y0 x1 y1 x2 y2 : ℝ) (hU : 0 < det3 x0 y0 x1 y1 x2 y2)
    (h : Dis R (TriSet x0 y0 x1 y1 x2 y2) n) (k : ℕ) (hk : 0 < k)
    (X1 Y1 X2 Y2 : ℝ) (hX1 : X1 = x0 + k * (x1 - x0)) (hY1 : Y1 = y0 + k * (y1 - y0))
    (hX2 : X2 = x0 + k * (x2 - x0)) (hY2 : Y2 = y0 + k * (y2 - y0)) :
    Dis R (TriSet x0 y0 X1 Y1 X2 Y2) (k * k * n) := by
  classical
  have hT : 0 < det3 x0 y0 X1 Y1 X2 Y2 := by
    have : det3 x0 y0 X1 Y1 X2 Y2 = (k : ℝ) ^ 2 * det3 x0 y0 x1 y1 x2 y2 := by
      subst hX1 hY1 hX2 hY2; simp only [det3]; ring
    rw [this]
    have : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    positivity
  obtain ⟨C, hr, hm⟩ := h
  set U : Tri := mkTri x0 y0 x1 y1 x2 y2 hU.ne' with hUdef
  have hr' : C.region = U.carrier := by rw [hr]; exact TriSet_eq_carrier hU
  have hfun : (![U.pts 0, U.pts 1, U.pts 2] : Fin 3 → Plane) = U.pts := by
    funext x; fin_cases x <;> rfl
  have hind : AffineIndependent ℝ (![U.pts 0, U.pts 1, U.pts 2] : Fin 3 → Plane) := by
    rw [hfun]; exact U.indep
  set U' : Tri := ⟨![U.pts 0, U.pts 1, U.pts 2], hind⟩ with hU'
  have hU'U : U' = U := tri_ext_pts hfun
  have hrU' : C.region = U'.carrier := by rw [hU'U]; exact hr'
  obtain ⟨E, hEt, hEm⟩ := Erdos634.Ladder.ladder (U.pts 0) (U.pts 1) (U.pts 2) hind
    (C.toCongruentDissection U' hrU') rfl k hk
  subst hX1 hY1 hX2 hY2
  set T : Tri := mkTri x0 y0 (x0 + k * (x1 - x0)) (y0 + k * (y1 - y0)) (x0 + k * (x2 - x0))
      (y0 + k * (y2 - y0)) hT.ne' with hTdef
  have hTeq : bigTri (U.pts 0) (U.pts 1) (U.pts 2) hind k hk = T := by
    apply tri_ext_pts
    funext x
    fin_cases x
    · show U.pts 0 = T.pts 0
      simp [hTdef, hUdef, mkTri]
    · show Erdos634.Subdivision.P (U.pts 0) (U.pts 1) (U.pts 2) k 0 = T.pts 1
      simp only [Erdos634.Subdivision.P]
      simp [hTdef, hUdef, mkTri, mkPt_sub, mkPt_smul, mkPt_add]
    · show Erdos634.Subdivision.P (U.pts 0) (U.pts 1) (U.pts 2) 0 k = T.pts 2
      simp only [Erdos634.Subdivision.P]
      simp [hTdef, hUdef, mkTri, mkPt_sub, mkPt_smul, mkPt_add]
  refine ⟨E.toRegion, ?_, hEm.trans hm⟩
  show E.target.carrier = _
  rw [hEt, hTeq, hTdef, ← TriSet_eq_carrier hT]


open Erdos634.ZhangLat

/-- Lattice form of `Dis_dilate`: ratio `k` about the vertex `0`. -/
theorem Dis_dilate_LT {R : Tri} {n : ℕ} (u0 v0 u1 v1 u2 v2 : ℝ) (hU : 0 < ld u0 v0 u1 v1 u2 v2)
    (h : Dis R (LT u0 v0 u1 v1 u2 v2) n) (k : ℕ) (hk : 0 < k)
    (U1 V1 U2 V2 : ℝ) (hU1 : U1 = u0 + k * (u1 - u0)) (hV1 : V1 = v0 + k * (v1 - v0))
    (hU2 : U2 = u0 + k * (u2 - u0)) (hV2 : V2 = v0 + k * (v2 - v0)) :
    Dis R (LT u0 v0 U1 V1 U2 V2) (k * k * n) := by
  have hz := zs_pos
  have hD : 0 < det3 (shx 0 u0 v0) (shy 0 v0) (shx 0 u1 v1) (shy 0 v1) (shx 0 u2 v2) (shy 0 v2) := by
    rw [det3_lat]; positivity
  exact Dis_dilate _ _ _ _ _ _ hD h k hk (shx 0 U1 V1) (shy 0 V1) (shx 0 U2 V2) (shy 0 V2)
    (by simp only [shx]; rw [hU1, hV1]; ring) (by simp only [shy]; rw [hV1]; ring)
    (by simp only [shx]; rw [hU2, hV2]; ring) (by simp only [shy]; rw [hV2]; ring)

/-- Lattice norm. -/
def nm (s t : ℝ) : ℝ := s ^ 2 + s * t + t ^ 2

theorem dlat (u v u' v' : ℝ) :
    (shx 0 u v - shx 0 u' v') ^ 2 + (shy 0 v - shy 0 v') ^ 2 = nm (u - u') (v - v') := by
  have hs := zs_sq
  simp only [shx, shy, nm]
  linear_combination ((v - v') ^ 2 / 4) * hs

/-- **Moving a lattice triangle tile-dissection**: a lattice triangle with the same three lattice
side norms (labelled) is congruent, so carries the same number of tiles (`transport`). -/
theorem Dis_LT_move {R : Tri} {n : ℕ} (u0 v0 u1 v1 u2 v2 w0 z0 w1 z1 w2 z2 : ℝ)
    (hP : 0 < ld u0 v0 u1 v1 u2 v2) (hQ : 0 < ld w0 z0 w1 z1 w2 z2)
    (h01 : nm (u1 - u0) (v1 - v0) = nm (w1 - w0) (z1 - z0))
    (h02 : nm (u2 - u0) (v2 - v0) = nm (w2 - w0) (z2 - z0))
    (h12 : nm (u2 - u1) (v2 - v1) = nm (w2 - w1) (z2 - z1))
    (h : Dis R (LT u0 v0 u1 v1 u2 v2) n) : Dis R (LT w0 z0 w1 z1 w2 z2) n := by
  have hz := zs_pos
  have hs := zs_sq
  have hdP : 0 < det3 (shx 0 u0 v0) (shy 0 v0) (shx 0 u1 v1) (shy 0 v1) (shx 0 u2 v2) (shy 0 v2) := by
    rw [det3_lat]; positivity
  have hdQ : 0 < det3 (shx 0 w0 z0) (shy 0 z0) (shx 0 w1 z1) (shy 0 z1) (shx 0 w2 z2) (shy 0 z2) := by
    rw [det3_lat]; positivity
  obtain ⟨C, hr, hm⟩ := h
  have hr' : C.region = (mkTri _ _ _ _ _ _ hdP.ne').carrier := by
    rw [hr]; exact TriSet_eq_carrier hdP
  have hcong0 : (mkTri _ _ _ _ _ _ hdP.ne').Congruent
      (mkTri _ _ _ _ _ _ hdQ.ne') := by
    refine congruent_of_sq_dist_perm 1 ?_
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [mkTri, dist_sq_mkPt] <;> rw [dlat, dlat] <;>
      simp only [nm] at h01 h02 h12 ⊢ <;> linarith
  obtain ⟨E, hE, hEm⟩ := Erdos634.Draft.CVCCevianCut.transport (C.toCongruentDissection _ hr') _ hcong0
  refine ⟨E.toRegion, ?_, hEm.trans hm⟩
  show E.target.carrier = _
  rw [hE]
  exact (TriSet_eq_carrier hdQ).symm


/-! ### Assembly of Fig. 8: big triangle = corner triangle + parallelogram + corner triangle

Lattice frame: `A = (0,0)`, `E = (uE,0)`, `C = (uC,0)`, `F = (uE - vF, vF)`, `D = (uC - vF, vF)`,
`B = (uC - vB, vB)` with `vB * uE = uC * vF`.  Triangle `A E F` and `F D B` and the parallelogram
`E F D C = {0 <= v <= vF, uE <= u+v <= uC}` tile `A C B`. -/

theorem key_xy (uE uC vF vB u v : ℝ) (h0 : 0 < uE) (h1 : uE < uC) (h2 : 0 < vF) (h3 : vF < vB)
    (hrel : vB * uE = uC * vF) :
    (0 ≤ ld u v uC 0 (uC - vB) vB ∧ 0 ≤ ld 0 0 u v (uC - vB) vB ∧ 0 ≤ ld 0 0 uC 0 u v) ↔
      ((0 ≤ ld u v uE 0 (uE - vF) vF ∧ 0 ≤ ld 0 0 u v (uE - vF) vF ∧ 0 ≤ ld 0 0 uE 0 u v) ∨
        ((0 ≤ v ∧ v ≤ vF ∧ u + v ≤ uC ∧ uE ≤ u + v) ∨
          (0 ≤ ld u v (uC - vF) vF (uC - vB) vB ∧ 0 ≤ ld (uE - vF) vF u v (uC - vB) vB ∧
            0 ≤ ld (uE - vF) vF (uC - vF) vF u v))) := by
  have e1 : ld u v uC 0 (uC - vB) vB = vB * (uC - u - v) := by simp only [ld]; ring
  have e2 : ld 0 0 u v (uC - vB) vB = vB * (u + v) - uC * v := by simp only [ld]; ring
  have e3 : ld 0 0 uC 0 u v = uC * v := by simp only [ld]; ring
  have f1 : ld u v uE 0 (uE - vF) vF = vF * (uE - u - v) := by simp only [ld]; ring
  have f2 : ld 0 0 u v (uE - vF) vF = vF * (u + v) - uE * v := by simp only [ld]; ring
  have f3 : ld 0 0 uE 0 u v = uE * v := by simp only [ld]; ring
  have g1 : ld u v (uC - vF) vF (uC - vB) vB = (vB - vF) * (uC - u - v) := by simp only [ld]; ring
  have g2 : ld (uE - vF) vF u v (uC - vB) vB = (vB - vF) * (u + v) - (uC - uE) * v := by
    simp only [ld]; linear_combination (-1 : ℝ) * hrel
  have g3 : ld (uE - vF) vF (uC - vF) vF u v = (uC - uE) * (v - vF) := by simp only [ld]; ring
  rw [e1, e2, e3, f1, f2, f3, g1, g2, g3]
  have hvB : 0 < vB := by linarith
  have hvBF : 0 < vB - vF := by linarith
  have huCE : 0 < uC - uE := by linarith
  have huC : 0 < uC := by linarith
  -- vF * (vB y - uC x) relations
  have r1 : vB * ((vB - vF) * (u + v) - (uC - uE) * v) = (vB - vF) * (vB * (u + v) - uC * v) := by
    linear_combination v * hrel
  have r2 : vB * (vF * (u + v) - uE * v) = vF * (vB * (u + v) - uC * v) := by
    linear_combination (-v) * hrel
  constructor
  · rintro ⟨a1, a2, a3⟩
    have hx : 0 ≤ v := nn_of_mul huC a3
    have hy : u + v ≤ uC := by
      have := nn_of_mul hvB a1; linarith
    rcases le_total (u + v) uE with hle | hge
    · left
      refine ⟨mul_nonneg h2.le (by linarith), ?_, mul_nonneg h0.le hx⟩
      have : 0 ≤ vF * (vB * (u + v) - uC * v) := mul_nonneg h2.le a2
      rw [← r2] at this
      exact nn_of_mul hvB this
    · right
      rcases le_total v vF with hv | hv
      · left; exact ⟨hx, hv, hy, hge⟩
      · right
        refine ⟨mul_nonneg hvBF.le (by linarith), ?_, mul_nonneg huCE.le (by linarith)⟩
        have : 0 ≤ (vB - vF) * (vB * (u + v) - uC * v) := mul_nonneg hvBF.le a2
        rw [← r1] at this
        exact nn_of_mul hvB this
  · rintro (⟨a1, a2, a3⟩ | ⟨hx, hv, hy, hge⟩ | ⟨a1, a2, a3⟩)
    · have hy : u + v ≤ uE := by have := nn_of_mul h2 a1; linarith
      have hx : 0 ≤ v := nn_of_mul h0 a3
      refine ⟨mul_nonneg hvB.le (by linarith), ?_, mul_nonneg huC.le hx⟩
      have : 0 ≤ vB * (vF * (u + v) - uE * v) := mul_nonneg hvB.le a2
      rw [r2] at this
      exact nn_of_mul h2 this
    · refine ⟨mul_nonneg hvB.le (by linarith), ?_, mul_nonneg huC.le hx⟩
      nlinarith [mul_nonneg hvB.le (sub_nonneg.mpr hge), mul_nonneg huC.le (sub_nonneg.mpr hv)]
    · have hy : u + v ≤ uC := by have := nn_of_mul hvBF a1; linarith
      have hx : vF ≤ v := by have := nn_of_mul huCE a3; linarith
      refine ⟨mul_nonneg hvB.le (by linarith), ?_, mul_nonneg huC.le (by linarith)⟩
      have : 0 ≤ vB * ((vB - vF) * (u + v) - (uC - uE) * v) := mul_nonneg hvB.le a2
      rw [r1] at this
      exact nn_of_mul hvBF this

theorem assemble {R : Tri} {nA nP nB : ℕ} (uE uC vF vB : ℝ) (h0 : 0 < uE) (h1 : uE < uC)
    (h2 : 0 < vF) (h3 : vF < vB) (hrel : vB * uE = uC * vF)
    (hA : Dis R (LT 0 0 uE 0 (uE - vF) vF) nA)
    (hB : Dis R (LT (uE - vF) vF (uC - vF) vF (uC - vB) vB) nB)
    (hP : Dis R {q | 0 ≤ vv 0 0 q ∧ vv 0 0 q ≤ vF ∧ uu 0 0 q + vv 0 0 q ≤ uC ∧
      uE ≤ uu 0 0 q + vv 0 0 q} nP) :
    Dis R (LT 0 0 uC 0 (uC - vB) vB) (nA + (nP + nB)) := by
  have hN1 : (0 : ℝ) ^ 2 + 1 ^ 2 ≠ 0 := by norm_num
  have hN2 : (1 : ℝ) ^ 2 + 1 ^ 2 ≠ 0 := by norm_num
  have hPB := Dis.glue_lat hP hB 0 1 vF hN1
    (fun q hq => by have := hq.2.1; linarith)
    (fun q hq => by
      rw [mem_LT] at hq
      have h3' := hq.2.2
      have e : ld (uE - vF) vF (uC - vF) vF (uu 0 0 q) (vv 0 0 q)
          = (uC - uE) * (vv 0 0 q - vF) := by simp only [ld]; ring
      rw [e] at h3'
      have := nn_of_mul (by linarith : 0 < uC - uE) h3'
      linarith)
  have hAll := Dis.glue_lat hA hPB 1 1 uE hN2
    (fun q hq => by
      rw [mem_LT] at hq
      have h1' := hq.1
      have e : ld (uu 0 0 q) (vv 0 0 q) uE 0 (uE - vF) vF
          = vF * (uE - uu 0 0 q - vv 0 0 q) := by simp only [ld]; ring
      rw [e] at h1'
      have := nn_of_mul h2 h1'
      linarith)
    (fun q hq => by
      rcases hq with hq | hq
      · have := hq.2.2.2; linarith
      · rw [mem_LT] at hq
        obtain ⟨a1, a2, a3⟩ := hq
        have e2 : ld (uE - vF) vF (uu 0 0 q) (vv 0 0 q) (uC - vB) vB
            = (vB - vF) * (uu 0 0 q + vv 0 0 q) - (uC - uE) * vv 0 0 q := by
          simp only [ld]; linear_combination (-1 : ℝ) * hrel
        have e3 : ld (uE - vF) vF (uC - vF) vF (uu 0 0 q) (vv 0 0 q)
            = (uC - uE) * (vv 0 0 q - vF) := by simp only [ld]; ring
        rw [e2] at a2; rw [e3] at a3
        have hx := nn_of_mul (by linarith : 0 < uC - uE) a3
        have h4 : 0 ≤ (vB - vF) * (uu 0 0 q + vv 0 0 q - uE) := by
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ uC - uE) hx]
        have := nn_of_mul (by linarith : 0 < vB - vF) h4
        linarith)
  refine hAll.congr ?_ rfl
  ext q
  rw [Set.mem_union, Set.mem_union, mem_LT, mem_LT, mem_LT, Set.mem_setOf_eq,
    key_xy uE uC vF vB (uu 0 0 q) (vv 0 0 q) h0 h1 h2 h3 hrel |>.symm.trans (by rfl)]


/-! ### The parallelogram -/

section pg
variable {a b c : ℝ}


theorem dis_PG (ha : 0 < a) (hb : 0 < b) (hc2 : c ^ 2 = a ^ 2 + b ^ 2 + a * b)
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (uE uC vF : ℝ) (hvF : vF = p * b) (hS : uC - uE = q * a) :
    Dis (Rmodel ha hb) {q' : Plane | 0 ≤ vv 0 0 q' ∧ vv 0 0 q' ≤ vF ∧ uu 0 0 q' + vv 0 0 q' ≤ uC ∧
      uE ≤ uu 0 0 q' + vv 0 0 q'} (q * (p * 2)) := by
  have h1 : ∀ px py, Dis (Rmodel ha hb) (Qs px py b a) 2 := fun px py =>
    Dis_Qs_two ha hb hc2 b a (Or.inr ⟨rfl, rfl⟩) px py
  have h2 := Dis.rowN hb.le ha.le h1 p hp
  have h3 := Dis.colN (by positivity) ha.le h2 q hq
  have h4 := Dis.rot (shx 0 uC 0) (shy 0 0)
    (fun u v => 0 ≤ u ∧ u ≤ p * b ∧ 0 ≤ v ∧ v ≤ q * a) (h3 _ _)
  refine h4.congr ?_ rfl
  ext q'
  simp only [Set.mem_setOf_eq, uu_sh, vv_sh, sub_zero, hvF]
  constructor
  · rintro ⟨e1, e2, e3, e4⟩
    refine ⟨e1, e2, by linarith, by linarith⟩
  · rintro ⟨e1, e2, e3, e4⟩
    refine ⟨e1, e2, by linarith, by linarith⟩

end pg

/-! ### Zhang Theorem 7, main case `k, k' >= 1` -/

open Erdos634.ZhangProp6 Erdos634.ZhangProp6b

set_option maxHeartbeats 4000000 in
/-- **Zhang's Theorem 7 (Fig. 8), main case.**  `a < b = a+d`, `c^2 = a^2+ab+b^2`, `gcd(a,b)=1`,
`k, k' >= 1`, `L = bk + ck'`: the lattice triangle `A=(0,0)`, `C=(a(a+2b)L,0)`,
`B=((a^2-b^2)L, b(2a+b)L)` (sides `AC = a(a+2b)L`, `BC = b(b+2a)L`, `AB = c^2 L`, angles
`(2 beta, alpha+beta, 2 alpha)` at `A, C, B`... in the labelling of `zhang_prop6_2`) carries
`k^2 N6 + 2 (b(2a+b)k)((a+2b)ck') + k'^2 N1 = (b+2a)(a+2b) L^2` tiles. -/
theorem thm7_main (a d c k k' : ℕ) (ha : 0 < a) (hd : 0 < d)
    (hcab : c * c = a * a + (a + d) * (a + d) + a * (a + d)) (hcop : Nat.Coprime a (a + d))
    (hk : 0 < k) (hk' : 0 < k') :
    Dis (Rmodel (Nat.cast_pos.mpr ha : (0:ℝ) < a)
        (Nat.cast_pos.mpr (by omega) : (0:ℝ) < ((a + d : ℕ) : ℝ)))
      (LT 0 0 ((a : ℝ) * (a + 2 * ((a : ℝ) + d)) * (((a : ℝ) + d) * k + c * k')) 0
        (((a : ℝ) * (a + 2 * ((a : ℝ) + d)) - ((a : ℝ) + d) * (2 * a + ((a : ℝ) + d))) *
          (((a : ℝ) + d) * k + c * k'))
        ((((a : ℝ) + d)) * (2 * a + ((a : ℝ) + d)) * (((a : ℝ) + d) * k + c * k')))
      (k * k * (((a + d) + 2 * a) * (a + 2 * (a + d)) * ((a + d) * (a + d))) +
        (((k' * c * (a + 2 * (a + d))) * ((a + d) * (2 * a + (a + d)) * k)) * 2 +
          k' * k' * (((a + d) + 2 * a) * (a + 2 * (a + d)) * (c * c)))) := by
  have hc : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · subst h; nlinarith [Nat.mul_pos ha ha]
    · exact h
  have hcR : (c : ℝ) * c = (a : ℝ) * a + ((a : ℝ) + d) * ((a : ℝ) + d) + a * ((a : ℝ) + d) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) hcab
    push_cast at this; linarith
  have hcpos : (0 : ℝ) < c := Nat.cast_pos.mpr hc
  have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hkR' : (0 : ℝ) < k' := Nat.cast_pos.mpr hk'
  have T6 := zhang_prop6_2 a d c ha hd hcab hcop
  have T1 := zhang_prop6_1 a d c ha hd hcab hcop
  -- piece A : k * T6, moved to (A, E, F)
  have hld6 : 0 < ld (qAu (a : ℝ) d) 0 (pFu (a : ℝ) d) 0 (qBu (a : ℝ) d) (qBv (a : ℝ) d) := by
    have : ld (qAu (a : ℝ) d) 0 (pFu (a : ℝ) d) 0 (qBu (a : ℝ) d) (qBv (a : ℝ) d)
        = ((a : ℝ) * (a + d) * (a + 2 * (a + d))) * (((a : ℝ) + d) ^ 2 * (3 * a + d)) := by
      simp only [ld, qAu, pFu, pX, pY, pW, qBu, qBv]; ring
    rw [this]; positivity
  have hbR : (((a + d : ℕ)) : ℝ) = (a : ℝ) + d := by push_cast; ring
  -- pieces' lattice data
  obtain ⟨uE, huE⟩ : ∃ x : ℝ, x = (a : ℝ) * (a + 2 * ((a : ℝ) + d)) * (((a : ℝ) + d) * k) := ⟨_, rfl⟩
  obtain ⟨vF, hvF⟩ : ∃ x : ℝ, x = ((a : ℝ) + d) ^ 2 * (2 * a + ((a : ℝ) + d)) * k := ⟨_, rfl⟩
  obtain ⟨uC, huC⟩ : ∃ x : ℝ, x = (a : ℝ) * (a + 2 * ((a : ℝ) + d)) *
      (((a : ℝ) + d) * k + c * k') := ⟨_, rfl⟩
  obtain ⟨vB, hvB⟩ : ∃ x : ℝ, x = ((a : ℝ) + d) * (2 * a + ((a : ℝ) + d)) *
      (((a : ℝ) + d) * k + c * k') := ⟨_, rfl⟩
  have hbpos : (0 : ℝ) < (a : ℝ) + d := by positivity
  have hP1 : 0 < uE := by rw [huE]; positivity
  have hP2 : uE < uC := by rw [huE, huC]; nlinarith [mul_pos (mul_pos haR (by positivity : (0:ℝ) < a + 2 * ((a : ℝ) + d))) (mul_pos hcpos hkR')]
  have hP3 : 0 < vF := by rw [hvF]; positivity
  have hP4 : vF < vB := by
    rw [hvF, hvB]
    nlinarith [mul_pos (mul_pos hbpos (by positivity : (0:ℝ) < 2 * a + ((a : ℝ) + d))) (mul_pos hcpos hkR')]
  have hrel : vB * uE = uC * vF := by rw [hvB, huE, huC, hvF]; ring
  -- piece A
  have hA0 := Dis_dilate_LT _ _ _ _ _ _ hld6 T6 k hk
    (qAu (a : ℝ) d + k * (pFu (a : ℝ) d - qAu (a : ℝ) d)) (0 + k * (0 - 0))
    (qAu (a : ℝ) d + k * (qBu (a : ℝ) d - qAu (a : ℝ) d)) (0 + k * (qBv (a : ℝ) d - 0))
    rfl rfl rfl rfl
  have hA1 := Dis_LT_move _ _ _ _ _ _ 0 0 uE 0 (uE - vF) vF
    (by
      have : ld (qAu (a : ℝ) d) 0 (qAu (a : ℝ) d + k * (pFu (a : ℝ) d - qAu (a : ℝ) d)) (0 + k * (0 - 0))
          (qAu (a : ℝ) d + k * (qBu (a : ℝ) d - qAu (a : ℝ) d)) (0 + k * (qBv (a : ℝ) d - 0))
          = (k : ℝ) ^ 2 * ld (qAu (a : ℝ) d) 0 (pFu (a : ℝ) d) 0 (qBu (a : ℝ) d) (qBv (a : ℝ) d) := by
        simp only [ld]; ring
      rw [this]; positivity)
    (by simp only [ld]; nlinarith [mul_pos hP1 hP3])
    (by simp only [nm, qAu, pFu, pX, pY, pW, qBu, qBv, huE]; ring)
    (by
      simp only [nm, qAu, pFu, pX, pY, pW, qBu, qBv, huE, hvF]; ring)
    (by
      simp only [nm, qAu, pFu, pX, pY, pW, qBu, qBv, huE, hvF]; ring)
    hA0
  -- piece B
  have hld1 : 0 < ld 0 (pAv (a : ℝ) d) (pCu (a : ℝ) d) 0 (pBu (a : ℝ) d) (pBv (a : ℝ) d) := by
    have : ld 0 (pAv (a : ℝ) d) (pCu (a : ℝ) d) 0 (pBu (a : ℝ) d) (pBv (a : ℝ) d)
        = (a : ℝ) * (a + d) * (3 * a + d) * (3 * a + 2 * d) * (3 * a ^ 2 + 3 * a * d + d ^ 2) := by
      simp only [ld, pAv, pBu, pBv, pCu, pY, pW]; ring
    rw [this]; positivity
  have hB0 := Dis_dilate_LT _ _ _ _ _ _ hld1 T1 k'  hk'
    (0 + k' * (pCu (a : ℝ) d - 0)) (pAv (a : ℝ) d + k' * (0 - pAv (a : ℝ) d))
    (0 + k' * (pBu (a : ℝ) d - 0)) (pAv (a : ℝ) d + k' * (pBv (a : ℝ) d - pAv (a : ℝ) d))
    rfl rfl rfl rfl
  have hB1 := Dis_LT_move _ _ _ _ _ _ (uE - vF) vF (uC - vF) vF (uC - vB) vB
    (by
      have : ld 0 (pAv (a : ℝ) d) (0 + k' * (pCu (a : ℝ) d - 0)) (pAv (a : ℝ) d + k' * (0 - pAv (a : ℝ) d))
          (0 + k' * (pBu (a : ℝ) d - 0)) (pAv (a : ℝ) d + k' * (pBv (a : ℝ) d - pAv (a : ℝ) d))
          = (k' : ℝ) ^ 2 * ld 0 (pAv (a : ℝ) d) (pCu (a : ℝ) d) 0 (pBu (a : ℝ) d) (pBv (a : ℝ) d) := by
        simp only [ld]; ring
      rw [this]; positivity)
    (by simp only [ld]; nlinarith [mul_pos (sub_pos.mpr hP2) (sub_pos.mpr hP4)])
    (by
      simp only [nm, pAv, pBu, pBv, pCu, pY, pW, huE, huC, hvF, hvB]
      linear_combination ((k' : ℝ) ^ 2 * a ^ 2 * (a + 2 * ((a : ℝ) + d)) ^ 2) * (-hcR))
    (by
      simp only [nm, pAv, pBu, pBv, pCu, pY, pW, huE, huC, hvF, hvB]
      linear_combination (-((k' : ℝ) ^ 2) * ((a : ℝ) * a + ((a : ℝ) + d) * ((a : ℝ) + d) + a * ((a : ℝ) + d)) ^ 2) * hcR)
    (by
      simp only [nm, pAv, pBu, pBv, pCu, pY, pW, huE, huC, hvF, hvB]
      linear_combination (-((k' : ℝ) ^ 2) * ((a : ℝ) + d) ^ 2 * (2 * a + ((a : ℝ) + d)) ^ 2) * hcR)
    hB0
  -- parallelogram
  have hc2 : (c : ℝ) ^ 2 = (a : ℝ) ^ 2 + (((a + d : ℕ)) : ℝ) ^ 2 + a * (((a + d : ℕ)) : ℝ) := by
    rw [hbR]; nlinarith [hcR]
  have hPG := dis_PG (Nat.cast_pos.mpr ha : (0:ℝ) < a)
    (Nat.cast_pos.mpr (by omega) : (0:ℝ) < ((a + d : ℕ) : ℝ)) hc2
    ((a + d) * (2 * a + (a + d)) * k) (k' * c * (a + 2 * (a + d)))
    (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) hk)
    (Nat.mul_pos (Nat.mul_pos hk' hc) (by omega)) uE uC vF
    (by rw [hvF, hbR]; push_cast; ring) (by rw [huE, huC]; push_cast; ring)
  have hAll := assemble uE uC vF vB hP1 hP2 hP3 hP4 hrel hA1 hB1 hPG
  refine hAll.congr ?_ ?_
  · rw [huC, hvB]; congr 1 <;> ring
  · ring

/-! ### Degenerate cases `k' = 0` or `k = 0`, and all large `m` -/

set_option maxHeartbeats 4000000 in
theorem thm7_kpz (a d c k : ℕ) (ha : 0 < a) (hd : 0 < d)
    (hcab : c * c = a * a + (a + d) * (a + d) + a * (a + d)) (hcop : Nat.Coprime a (a + d))
    (hk : 0 < k) :
    Dis (Rmodel (Nat.cast_pos.mpr ha : (0:ℝ) < a)
        (Nat.cast_pos.mpr (by omega) : (0:ℝ) < ((a + d : ℕ) : ℝ)))
      (LT 0 0 ((a : ℝ) * (a + 2 * ((a : ℝ) + d)) * (((a : ℝ) + d) * k)) 0
        (((a : ℝ) * (a + 2 * ((a : ℝ) + d)) - ((a : ℝ) + d) * (2 * a + ((a : ℝ) + d))) *
          (((a : ℝ) + d) * k))
        ((((a : ℝ) + d)) * (2 * a + ((a : ℝ) + d)) * (((a : ℝ) + d) * k)))
      (k * k * (((a + d) + 2 * a) * (a + 2 * (a + d)) * ((a + d) * (a + d)))) := by
  have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have T6 := zhang_prop6_2 a d c ha hd hcab hcop
  have hld6 : 0 < ld (qAu (a : ℝ) d) 0 (pFu (a : ℝ) d) 0 (qBu (a : ℝ) d) (qBv (a : ℝ) d) := by
    have : ld (qAu (a : ℝ) d) 0 (pFu (a : ℝ) d) 0 (qBu (a : ℝ) d) (qBv (a : ℝ) d)
        = ((a : ℝ) * (a + d) * (a + 2 * (a + d))) * (((a : ℝ) + d) ^ 2 * (3 * a + d)) := by
      simp only [ld, qAu, pFu, pX, pY, pW, qBu, qBv]; ring
    rw [this]; positivity
  have hA0 := Dis_dilate_LT _ _ _ _ _ _ hld6 T6 k hk
    (qAu (a : ℝ) d + k * (pFu (a : ℝ) d - qAu (a : ℝ) d)) (0 + k * (0 - 0))
    (qAu (a : ℝ) d + k * (qBu (a : ℝ) d - qAu (a : ℝ) d)) (0 + k * (qBv (a : ℝ) d - 0))
    rfl rfl rfl rfl
  refine Dis_LT_move _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ hA0
  · have : ld (qAu (a : ℝ) d) 0 (qAu (a : ℝ) d + k * (pFu (a : ℝ) d - qAu (a : ℝ) d)) (0 + k * (0 - 0))
        (qAu (a : ℝ) d + k * (qBu (a : ℝ) d - qAu (a : ℝ) d)) (0 + k * (qBv (a : ℝ) d - 0))
        = (k : ℝ) ^ 2 * ld (qAu (a : ℝ) d) 0 (pFu (a : ℝ) d) 0 (qBu (a : ℝ) d) (qBv (a : ℝ) d) := by
      simp only [ld]; ring
    rw [this]; positivity
  · have : ld 0 0 ((a : ℝ) * (a + 2 * ((a : ℝ) + d)) * (((a : ℝ) + d) * k)) 0
        (((a : ℝ) * (a + 2 * ((a : ℝ) + d)) - ((a : ℝ) + d) * (2 * a + ((a : ℝ) + d))) *
          (((a : ℝ) + d) * k))
        ((((a : ℝ) + d)) * (2 * a + ((a : ℝ) + d)) * (((a : ℝ) + d) * k))
        = ((a : ℝ) * (a + 2 * ((a : ℝ) + d)) * (((a : ℝ) + d) * k)) *
          ((((a : ℝ) + d)) * (2 * a + ((a : ℝ) + d)) * (((a : ℝ) + d) * k)) := by
      simp only [ld]; ring
    rw [this]; have : (0:ℝ) < (a : ℝ) + d := by positivity
    positivity
  · simp only [nm, qAu, pFu, pX, pY, pW, qBu, qBv]; ring
  · simp only [nm, qAu, pFu, pX, pY, pW, qBu, qBv]; ring
  · simp only [nm, qAu, pFu, pX, pY, pW, qBu, qBv]; ring

set_option maxHeartbeats 4000000 in
theorem thm7_kz (a d c k' : ℕ) (ha : 0 < a) (hd : 0 < d)
    (hcab : c * c = a * a + (a + d) * (a + d) + a * (a + d)) (hcop : Nat.Coprime a (a + d))
    (hk' : 0 < k') :
    Dis (Rmodel (Nat.cast_pos.mpr ha : (0:ℝ) < a)
        (Nat.cast_pos.mpr (by omega) : (0:ℝ) < ((a + d : ℕ) : ℝ)))
      (LT 0 0 ((a : ℝ) * (a + 2 * ((a : ℝ) + d)) * (c * k')) 0
        (((a : ℝ) * (a + 2 * ((a : ℝ) + d)) - ((a : ℝ) + d) * (2 * a + ((a : ℝ) + d))) *
          (c * k'))
        ((((a : ℝ) + d)) * (2 * a + ((a : ℝ) + d)) * (c * k')))
      (k' * k' * (((a + d) + 2 * a) * (a + 2 * (a + d)) * (c * c))) := by
  have hc : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · subst h; nlinarith [Nat.mul_pos ha ha]
    · exact h
  have hcR : (c : ℝ) * c = (a : ℝ) * a + ((a : ℝ) + d) * ((a : ℝ) + d) + a * ((a : ℝ) + d) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) hcab
    push_cast at this; linarith
  have hcpos : (0 : ℝ) < c := Nat.cast_pos.mpr hc
  have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hkR' : (0 : ℝ) < k' := Nat.cast_pos.mpr hk'
  have T1 := zhang_prop6_1 a d c ha hd hcab hcop
  have hld1 : 0 < ld 0 (pAv (a : ℝ) d) (pCu (a : ℝ) d) 0 (pBu (a : ℝ) d) (pBv (a : ℝ) d) := by
    have : ld 0 (pAv (a : ℝ) d) (pCu (a : ℝ) d) 0 (pBu (a : ℝ) d) (pBv (a : ℝ) d)
        = (a : ℝ) * (a + d) * (3 * a + d) * (3 * a + 2 * d) * (3 * a ^ 2 + 3 * a * d + d ^ 2) := by
      simp only [ld, pAv, pBu, pBv, pCu, pY, pW]; ring
    rw [this]; positivity
  have hB0 := Dis_dilate_LT _ _ _ _ _ _ hld1 T1 k' hk'
    (0 + k' * (pCu (a : ℝ) d - 0)) (pAv (a : ℝ) d + k' * (0 - pAv (a : ℝ) d))
    (0 + k' * (pBu (a : ℝ) d - 0)) (pAv (a : ℝ) d + k' * (pBv (a : ℝ) d - pAv (a : ℝ) d))
    rfl rfl rfl rfl
  refine Dis_LT_move _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ hB0
  · have : ld 0 (pAv (a : ℝ) d) (0 + k' * (pCu (a : ℝ) d - 0)) (pAv (a : ℝ) d + k' * (0 - pAv (a : ℝ) d))
        (0 + k' * (pBu (a : ℝ) d - 0)) (pAv (a : ℝ) d + k' * (pBv (a : ℝ) d - pAv (a : ℝ) d))
        = (k' : ℝ) ^ 2 * ld 0 (pAv (a : ℝ) d) (pCu (a : ℝ) d) 0 (pBu (a : ℝ) d) (pBv (a : ℝ) d) := by
      simp only [ld]; ring
    rw [this]; positivity
  · have : ld 0 0 ((a : ℝ) * (a + 2 * ((a : ℝ) + d)) * (c * k')) 0
        (((a : ℝ) * (a + 2 * ((a : ℝ) + d)) - ((a : ℝ) + d) * (2 * a + ((a : ℝ) + d))) *
          (c * k'))
        ((((a : ℝ) + d)) * (2 * a + ((a : ℝ) + d)) * (c * k'))
        = ((a : ℝ) * (a + 2 * ((a : ℝ) + d)) * (c * k')) *
          ((((a : ℝ) + d)) * (2 * a + ((a : ℝ) + d)) * (c * k')) := by
      simp only [ld]; ring
    rw [this]; have : (0:ℝ) < (a : ℝ) + d := by positivity
    positivity
  · simp only [nm, pAv, pBu, pBv, pCu, pY, pW]
    linear_combination (-((a : ℝ) ^ 2 * (a + 2 * ((a : ℝ) + d)) ^ 2 * (k' : ℝ) ^ 2)) * hcR
  · simp only [nm, pAv, pBu, pBv, pCu, pY, pW]
    linear_combination (-((k' : ℝ) ^ 2) * ((a : ℝ) * a + ((a : ℝ) + d) * ((a : ℝ) + d) + a * ((a : ℝ) + d)) ^ 2) * hcR
  · simp only [nm, pAv, pBu, pBv, pCu, pY, pW]
    linear_combination (-((k' : ℝ) ^ 2) * ((a : ℝ) + d) ^ 2 * (2 * a + ((a : ℝ) + d)) ^ 2) * hcR

theorem coprime_b_c (a d c : ℕ) (hcab : c * c = a * a + (a + d) * (a + d) + a * (a + d))
    (hcop : Nat.Coprime a (a + d)) : Nat.Coprime (a + d) c := by
  apply Nat.coprime_of_dvd
  intro p hp hpb hpc
  have e : c * c = (a + d) * ((a + d) + a) + a * a := by rw [hcab]; ring
  have h1 : p ∣ c * c := dvd_mul_of_dvd_left hpc _
  rw [e] at h1
  have h2 : p ∣ (a + d) * ((a + d) + a) := dvd_mul_of_dvd_left hpb _
  have h3 : p ∣ a * a := (Nat.dvd_add_right h2).mp h1
  have h4 : p ∣ a := (hp.dvd_mul.mp h3).elim id id
  have h5 : p ∣ Nat.gcd a (a + d) := Nat.dvd_gcd h4 hpb
  rw [hcop] at h5
  exact hp.one_lt.ne' (Nat.dvd_one.mp h5)

/-- **Zhang's Theorem 7 (UNAUDITED).**  `a < b = a+d`, `c^2 = a^2+ab+b^2`, `gcd(a,b)=1`.  For every
`m` with `bc < m + b + c` (i.e. `m > bc - b - c`) the lattice triangle `A=(0,0)`, `C=(a(a+2b)m,0)`,
`B=((a^2-b^2)m... , b(2a+b)m)` (sides `a(a+2b)m`, `b(b+2a)m`, `c^2 m`) carries `(b+2a)(a+2b) m^2`
tiles.  Proof: `m = i b + j c` (Frobenius, `ZhangPara.frob`), then `thm7_main` (`i,j >= 1`) or the
degenerate cases `thm7_kpz`, `thm7_kz`. -/
theorem zhang_thm7 (a d c m : ℕ) (ha : 0 < a) (hd : 0 < d)
    (hcab : c * c = a * a + (a + d) * (a + d) + a * (a + d)) (hcop : Nat.Coprime a (a + d))
    (hm : (a + d) * c < m + (a + d) + c) :
    Dis (Rmodel (Nat.cast_pos.mpr ha : (0:ℝ) < a)
        (Nat.cast_pos.mpr (by omega) : (0:ℝ) < ((a + d : ℕ) : ℝ)))
      (LT 0 0 ((a : ℝ) * (a + 2 * ((a : ℝ) + d)) * m) 0
        (((a : ℝ) * (a + 2 * ((a : ℝ) + d)) - ((a : ℝ) + d) * (2 * a + ((a : ℝ) + d))) * m)
        ((((a : ℝ) + d)) * (2 * a + ((a : ℝ) + d)) * m))
      (((a + d) + 2 * a) * (a + 2 * (a + d)) * (m * m)) := by
  have hc : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · subst h; nlinarith [Nat.mul_pos ha ha]
    · exact h
  obtain ⟨i, j, hij⟩ := ZhangPara.frob (a + d) c m (coprime_b_c a d c hcab hcop) (by omega) hc hm
  have hmR : (m : ℝ) = ((a : ℝ) + d) * i + c * j := by
    have := congrArg (fun n : ℕ => (n : ℝ)) hij
    push_cast at this; linarith
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      have hb2 : 2 ≤ a + d := by omega
      have hc2 : 2 ≤ c := by nlinarith [Nat.mul_pos ha ha]
      have h0 : m = 0 := by rw [hij]; ring
      subst h0
      nlinarith [Nat.mul_le_mul hb2 hc2]
    · have := thm7_kz a d c j ha hd hcab hcop hj
      have hm' : m = c * j := by rw [hij]; ring
      subst hm'
      refine (this.congr ?_ ?_)
      · push_cast; rfl
      · ring
  · rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      have := thm7_kpz a d c i ha hd hcab hcop hi
      have hm' : m = (a + d) * i := by rw [hij]; ring
      subst hm'
      refine (this.congr ?_ ?_)
      · push_cast; rfl
      · ring
    · have := thm7_main a d c i j ha hd hcab hcop hi hj
      refine (this.congr ?_ ?_)
      · rw [hmR]
      · rw [hij]; ring

/-- Witness `(a,b,c) = (3,5,7)`, `m = 12 = 5 + 7` (main case `k = k' = 1`; below Zhang's bound
`m > 23`, but covered by the construction): `143 * 144 = 20592` tiles.  Area check
`3575 + 2*55*91 + 7007 = 3575 + 10010 + 7007 = 20592`. -/
theorem zhang_thm7_357_m12 :
    Dis (Rmodel (by norm_num : (0:ℝ) < ((3 : ℕ) : ℝ)) (by norm_num : (0:ℝ) < (((3 + 2 : ℕ)) : ℝ)))
      (LT 0 0 (((3 : ℕ) : ℝ) * (((3 : ℕ) : ℝ) + 2 * (((3 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))) *
          ((((3 : ℕ) : ℝ) + ((2 : ℕ) : ℝ)) * ((1 : ℕ) : ℝ) + ((7 : ℕ) : ℝ) * ((1 : ℕ) : ℝ))) 0
        (((((3 : ℕ) : ℝ) * (((3 : ℕ) : ℝ) + 2 * (((3 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))) -
          (((3 : ℕ) : ℝ) + ((2 : ℕ) : ℝ)) * (2 * ((3 : ℕ) : ℝ) + (((3 : ℕ) : ℝ) + ((2 : ℕ) : ℝ)))) *
          ((((3 : ℕ) : ℝ) + ((2 : ℕ) : ℝ)) * ((1 : ℕ) : ℝ) + ((7 : ℕ) : ℝ) * ((1 : ℕ) : ℝ))))
        (((((3 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))) * (2 * ((3 : ℕ) : ℝ) + (((3 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))) *
          ((((3 : ℕ) : ℝ) + ((2 : ℕ) : ℝ)) * ((1 : ℕ) : ℝ) + ((7 : ℕ) : ℝ) * ((1 : ℕ) : ℝ))))
      20592 :=
  (thm7_main 3 2 7 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).congr rfl (by norm_num)

/-- Witness via `zhang_thm7` with `m = 24 > bc - b - c = 23`: `143 * 576 = 82368` tiles. -/
theorem zhang_thm7_357_m24 : ∃ n : ℕ, n = 82368 ∧ ∃ C : CongruentRegionDissection n,
    C.region = LT 0 0 (((3 : ℕ) : ℝ) * (((3 : ℕ) : ℝ) + 2 * (((3 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))) *
          ((24 : ℕ) : ℝ)) 0
        (((((3 : ℕ) : ℝ) * (((3 : ℕ) : ℝ) + 2 * (((3 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))) -
          (((3 : ℕ) : ℝ) + ((2 : ℕ) : ℝ)) * (2 * ((3 : ℕ) : ℝ) + (((3 : ℕ) : ℝ) + ((2 : ℕ) : ℝ)))) *
          ((24 : ℕ) : ℝ)))
        (((((3 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))) * (2 * ((3 : ℕ) : ℝ) + (((3 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))) *
          ((24 : ℕ) : ℝ)) := by
  obtain ⟨C, hr, -⟩ := zhang_thm7 3 2 7 24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  exact ⟨_, by norm_num, C, hr⟩

end Erdos634.ZhangThm7