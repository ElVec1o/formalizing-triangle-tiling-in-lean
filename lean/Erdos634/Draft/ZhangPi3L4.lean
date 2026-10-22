import Erdos634.Draft.ZhangPi3A
import Erdos634.Draft.ZhangL1Aux

/-!
# Zhang Theorem 5, part B (arXiv 2512.22696v4, Lemma 4 / Fig. 6)

`zhang_lemma4`: for naturals `a,b,c > 0` with `c² + ab = a² + b²` (tile with angle `π/3` between
`a` and `b`), the trapezoid `Tz px py (c²) (a b)` (isosceles, base angles `π/3`, top `c²`, legs
`ab`, bottom `a²+b²`) carries `a² + b² + c²` tiles congruent to `R3 a b`.
Frame coordinates `(u,v)`: `A=(0,0)`, `E=(a²,0)`, `B=(a²+b²,0)`, `D=(0,ab)`, `C=(a²+b²-ab, ab)`;
pieces `ADE = a·R`, `EBC = b·R`, `EC D = c·R`.  UNAUDITED.
Credit Zhang (arXiv 2512.22696), Beeson, Beeson-Rosu, Laczkovich.
-/

namespace Erdos634.ZhangPi3

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.GlueCut Erdos634.SssCongruent Erdos634.ZhangL1 Erdos634.ZhangPara

theorem pm (κ x : ℝ) (h : 0 < κ) : 0 ≤ κ * x ↔ 0 ≤ x := mul_nonneg_iff_of_pos_left h

/-- scaled copy of a lattice triangle, in frame coordinates -/
theorem Dis_scaled_uv {R : Tri} (px py u0 v0 u1 v1 u2 v2 u1' v1' u2' v2' : ℝ) (k : ℕ)
    (hk : 0 < k) (hd : 0 < det3 u0 v0 u1 v1 u2 v2) (hd' : 0 < det3 u0 v0 u1' v1' u2' v2')
    (hU : (triUV px py u0 v0 u1 v1 u2 v2 hd).Congruent R)
    (e1 : u1' = u0 + k * (u1 - u0)) (f1 : v1' = v0 + k * (v1 - v0))
    (e2 : u2' = u0 + k * (u2 - u0)) (f2 : v2' = v0 + k * (v2 - v0)) :
    Dis R (triUV px py u0 v0 u1' v1' u2' v2' hd').carrier (k * k * 1) := by
  have h1 : (triUV px py u0 v0 u1' v1' u2' v2' hd').pts 1 =
      (triUV px py u0 v0 u1 v1 u2 v2 hd).pts 0 + (k : ℝ) •
        ((triUV px py u0 v0 u1 v1 u2 v2 hd).pts 1 - (triUV px py u0 v0 u1 v1 u2 v2 hd).pts 0) := by
    show mkPt (shx px u1' v1') (shy py v1') = mkPt (shx px u0 v0) (shy py v0) +
      (k : ℝ) • (mkPt (shx px u1 v1) (shy py v1) - mkPt (shx px u0 v0) (shy py v0))
    rw [mkPt_sub, mkPt_smul, mkPt_add]
    congr 1 <;> simp only [shx, shy] <;> (try rw [e1]) <;> (try rw [f1]) <;> ring
  have h2 : (triUV px py u0 v0 u1' v1' u2' v2' hd').pts 2 =
      (triUV px py u0 v0 u1 v1 u2 v2 hd).pts 0 + (k : ℝ) •
        ((triUV px py u0 v0 u1 v1 u2 v2 hd).pts 2 - (triUV px py u0 v0 u1 v1 u2 v2 hd).pts 0) := by
    show mkPt (shx px u2' v2') (shy py v2') = mkPt (shx px u0 v0) (shy py v0) +
      (k : ℝ) • (mkPt (shx px u2 v2) (shy py v2) - mkPt (shx px u0 v0) (shy py v0))
    rw [mkPt_sub, mkPt_smul, mkPt_add]
    congr 1 <;> simp only [shx, shy] <;> (try rw [e2]) <;> (try rw [f2]) <;> ring
  obtain ⟨C, hC, hm⟩ := scaledPiece (triUV px py u0 v0 u1 v1 u2 v2 hd) R
    (triUV px py u0 v0 u1' v1' u2' v2' hd') hU k hk rfl h1 h2
  exact ⟨C, hC, hm⟩

section geo
variable {a b : ℝ}

def Reg1 (px py a b : ℝ) : Set Plane :=
  {q | 0 ≤ a ^ 2 * b - (b * uu px py q + a * vv px py q) ∧ 0 ≤ uu px py q ∧ 0 ≤ vv px py q}
def Reg2 (px py a b : ℝ) : Set Plane :=
  {q | 0 ≤ a * (uu px py q - a ^ 2) - (b - a) * vv px py q ∧ 0 ≤ vv px py q ∧
    0 ≤ a ^ 2 + b ^ 2 - uu px py q - vv px py q}
def Reg3 (px py a b : ℝ) : Set Plane :=
  {q | 0 ≤ a * b - vv px py q ∧ 0 ≤ b * uu px py q + a * vv px py q - a ^ 2 * b ∧
    0 ≤ -(a * (uu px py q - a ^ 2) - (b - a) * vv px py q)}

theorem hc2pos (ha : 0 < a) (hb : 0 < b) : 0 < a ^ 2 + b ^ 2 - a * b := by
  nlinarith [sq_nonneg (a - b), mul_pos ha hb]

theorem d1 (ha : 0 < a) (hb : 0 < b) : 0 < det3 0 0 (a ^ 2) 0 0 (a * b) := by
  simp only [det3]; nlinarith [mul_pos ha hb, pow_pos ha 2, mul_pos (pow_pos ha 2) (mul_pos ha hb)]
theorem d2 (ha : 0 < a) (hb : 0 < b) :
    0 < det3 (a ^ 2 + b ^ 2) 0 (a ^ 2 + b ^ 2 - a * b) (a * b) (a ^ 2) 0 := by
  simp only [det3]; nlinarith [mul_pos (pow_pos hb 2) (mul_pos ha hb)]
theorem d3 (ha : 0 < a) (hb : 0 < b) :
    0 < det3 (a ^ 2) 0 (a ^ 2 + b ^ 2 - a * b) (a * b) 0 (a * b) := by
  have := mul_pos (mul_pos ha hb) (hc2pos ha hb)
  simp only [det3]; nlinarith [this]

theorem P1_eq (px py : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (triUV px py 0 0 (a ^ 2) 0 0 (a * b) (d1 ha hb)).carrier = Reg1 px py a b := by
  ext q; rw [mem_triUV]
  have e1 : det3 (uu px py q) (vv px py q) (a ^ 2) 0 0 (a * b)
      = a * (a ^ 2 * b - (b * uu px py q + a * vv px py q)) := by simp only [det3]; ring
  have e2 : det3 0 0 (uu px py q) (vv px py q) 0 (a * b) = (a * b) * uu px py q := by
    simp only [det3]; ring
  have e3 : det3 0 0 (a ^ 2) 0 (uu px py q) (vv px py q) = a ^ 2 * vv px py q := by
    simp only [det3]; ring
  rw [e1, e2, e3, pm _ _ ha, pm _ _ (mul_pos ha hb), pm _ _ (pow_pos ha 2)]
  rfl

theorem P2_eq (px py : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (triUV px py (a ^ 2 + b ^ 2) 0 (a ^ 2 + b ^ 2 - a * b) (a * b) (a ^ 2) 0
      (d2 ha hb)).carrier = Reg2 px py a b := by
  ext q; rw [mem_triUV]
  have e1 : det3 (uu px py q) (vv px py q) (a ^ 2 + b ^ 2 - a * b) (a * b) (a ^ 2) 0
      = b * (a * (uu px py q - a ^ 2) - (b - a) * vv px py q) := by simp only [det3]; ring
  have e2 : det3 (a ^ 2 + b ^ 2) 0 (uu px py q) (vv px py q) (a ^ 2) 0
      = b ^ 2 * vv px py q := by simp only [det3]; ring
  have e3 : det3 (a ^ 2 + b ^ 2) 0 (a ^ 2 + b ^ 2 - a * b) (a * b) (uu px py q) (vv px py q)
      = (a * b) * (a ^ 2 + b ^ 2 - uu px py q - vv px py q) := by simp only [det3]; ring
  rw [e1, e2, e3, pm _ _ hb, pm _ _ (pow_pos hb 2), pm _ _ (mul_pos ha hb)]
  rfl

theorem P3_eq (px py : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (triUV px py (a ^ 2) 0 (a ^ 2 + b ^ 2 - a * b) (a * b) 0 (a * b)
      (d3 ha hb)).carrier = Reg3 px py a b := by
  ext q; rw [mem_triUV]
  have e1 : det3 (uu px py q) (vv px py q) (a ^ 2 + b ^ 2 - a * b) (a * b) 0 (a * b)
      = (a ^ 2 + b ^ 2 - a * b) * (a * b - vv px py q) := by simp only [det3]; ring
  have e2 : det3 (a ^ 2) 0 (uu px py q) (vv px py q) 0 (a * b)
      = a * (b * uu px py q + a * vv px py q - a ^ 2 * b) := by simp only [det3]; ring
  have e3 : det3 (a ^ 2) 0 (a ^ 2 + b ^ 2 - a * b) (a * b) (uu px py q) (vv px py q)
      = b * (-(a * (uu px py q - a ^ 2) - (b - a) * vv px py q)) := by simp only [det3]; ring
  rw [e1, e2, e3, pm _ _ (hc2pos ha hb), pm _ _ ha, pm _ _ hb]
  rfl

end geo


section union
variable {a b : ℝ}

theorem Reg1_sub (px py : ℝ) (ha : 0 < a) (hb : 0 < b) (q : Plane) (h : q ∈ Reg1 px py a b) :
    q ∈ Tz px py (a ^ 2 + b ^ 2 - a * b) (a * b) := by
  obtain ⟨h1, hu, hv⟩ := h
  have hab := mul_pos ha hb
  refine ⟨hu, hv, ?_, ?_⟩
  · by_contra hc
    push Not at hc
    nlinarith [mul_nonneg hb.le hu]
  · rcases le_total b a with hba | hab'
    · have : b * (uu px py q + vv px py q) ≤ a ^ 2 * b := by
        nlinarith [mul_nonneg (sub_nonneg.2 hba) hv]
      have : uu px py q + vv px py q ≤ a ^ 2 := by
        by_contra hc; push Not at hc; nlinarith
      nlinarith [sq_nonneg b]
    · have : a * (uu px py q + vv px py q) ≤ a ^ 2 * b := by
        nlinarith [mul_nonneg (sub_nonneg.2 hab') hu]
      have : uu px py q + vv px py q ≤ a * b := by
        by_contra hc; push Not at hc; nlinarith
      nlinarith [sq_nonneg (a - b), sq_nonneg a]

theorem Reg3_sub (px py : ℝ) (ha : 0 < a) (hb : 0 < b) (q : Plane) (h : q ∈ Reg3 px py a b) :
    q ∈ Tz px py (a ^ 2 + b ^ 2 - a * b) (a * b) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hab := mul_pos ha hb
  have hc := hc2pos ha hb
  have hv0 : 0 ≤ (a ^ 2 + b ^ 2 - a * b) * vv px py q := by
    nlinarith [mul_nonneg ha.le h2, mul_nonneg hb.le h3]
  have hv : 0 ≤ vv px py q := by
    by_contra hn; push Not at hn; nlinarith [mul_pos hc (neg_pos.2 hn)]
  have hu0 : 0 ≤ b * uu px py q := by nlinarith [mul_nonneg ha.le h1]
  have hu : 0 ≤ uu px py q := by
    by_contra hn; push Not at hn; nlinarith [mul_pos hb (neg_pos.2 hn)]
  refine ⟨hu, hv, by linarith, ?_⟩
  have e : a * (a ^ 2 + b ^ 2 - uu px py q - vv px py q)
      = (-(a * (uu px py q - a ^ 2) - (b - a) * vv px py q)) + b * (a * b - vv px py q) := by ring
  have : 0 ≤ a * (a ^ 2 + b ^ 2 - uu px py q - vv px py q) := by
    rw [e]; nlinarith [mul_nonneg hb.le h1]
  have := (pm _ _ ha).1 this
  linarith

theorem Reg2_sub (px py : ℝ) (ha : 0 < a) (hb : 0 < b) (q : Plane) (h : q ∈ Reg2 px py a b) :
    q ∈ Tz px py (a ^ 2 + b ^ 2 - a * b) (a * b) := by
  obtain ⟨h1, hv, h3⟩ := h
  have hab := mul_pos ha hb
  have hc := hc2pos ha hb
  have e : b * (a * b - vv px py q)
      = a * (a ^ 2 + b ^ 2 - uu px py q - vv px py q)
        + (a * (uu px py q - a ^ 2) - (b - a) * vv px py q) := by ring
  have hvab : 0 ≤ a * b - vv px py q := by
    have : 0 ≤ b * (a * b - vv px py q) := by rw [e]; nlinarith [mul_nonneg ha.le h3]
    exact (pm _ _ hb).1 this
  have hu : 0 ≤ uu px py q := by
    have hacc : 0 ≤ a * (a ^ 2 + b ^ 2 - a * b) := (mul_pos ha hc).le
    have : 0 ≤ (a * b) * (a * uu px py q) := by
      nlinarith [mul_nonneg hab.le h1, mul_nonneg hv hacc, mul_nonneg hvab (pow_pos ha 3).le]
    have := (pm _ _ hab).1 this
    exact (pm _ _ ha).1 this
  exact ⟨hu, hv, by linarith, by linarith⟩

theorem Tz_eq_union (px py : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tz px py (a ^ 2 + b ^ 2 - a * b) (a * b) = (Reg1 px py a b ∪ Reg3 px py a b) ∪ Reg2 px py a b := by
  ext q
  constructor
  · rintro ⟨hu, hv, hvab, hsum⟩
    rcases le_total (b * uu px py q + a * vv px py q - a ^ 2 * b) 0 with hf | hf
    · left; left; exact ⟨by linarith, hu, hv⟩
    · rcases le_total (a * (uu px py q - a ^ 2) - (b - a) * vv px py q) 0 with hg | hg
      · left; right; exact ⟨by linarith, hf, by linarith⟩
      · right; exact ⟨hg, hv, by linarith⟩
  · rintro ((h | h) | h)
    · exact Reg1_sub px py ha hb q h
    · exact Reg3_sub px py ha hb q h
    · exact Reg2_sub px py ha hb q h

end union


/-! ### The three scaled pieces -/

section pieces
variable {a b : ℝ}

theorem U1_cong (px py : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (triUV px py 0 0 a 0 0 b (det_ab ha hb)).Congruent (R3 ha hb) := by
  refine cong_of_three ⟨![0, 1, 2], ![0, 1, 2], by decide, by decide⟩ ?_ ?_ ?_
  · show _ = dist ((R3 ha hb).pts 0) ((R3 ha hb).pts 1) ^ 2
    rw [tri_d01, R3_01]; ring
  · show _ = dist ((R3 ha hb).pts 1) ((R3 ha hb).pts 2) ^ 2
    rw [tri_d12, R3_12]; ring
  · show _ = dist ((R3 ha hb).pts 0) ((R3 ha hb).pts 2) ^ 2
    rw [tri_d02, R3_02]; ring

theorem dU2 (ha : 0 < a) (hb : 0 < b) :
    0 < det3 (a ^ 2 + b ^ 2) 0 (a ^ 2 + b ^ 2 - a) a (a ^ 2 + b ^ 2 - b) 0 := by
  simp only [det3]; nlinarith [mul_pos ha hb]

theorem U2_cong (px py : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (triUV px py (a ^ 2 + b ^ 2) 0 (a ^ 2 + b ^ 2 - a) a (a ^ 2 + b ^ 2 - b) 0
      (dU2 ha hb)).Congruent (R3 ha hb) := by
  refine cong_of_three ⟨![0, 1, 2], ![0, 1, 2], by decide, by decide⟩ ?_ ?_ ?_
  · show _ = dist ((R3 ha hb).pts 0) ((R3 ha hb).pts 1) ^ 2
    rw [tri_d01, R3_01]; ring
  · show _ = dist ((R3 ha hb).pts 1) ((R3 ha hb).pts 2) ^ 2
    rw [tri_d12, R3_12]; ring
  · show _ = dist ((R3 ha hb).pts 0) ((R3 ha hb).pts 2) ^ 2
    rw [tri_d02, R3_02]; ring

theorem dU3 {c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hc2 : c ^ 2 + a * b = a ^ 2 + b ^ 2) :
    0 < det3 (a ^ 2) 0 (a ^ 2 + (b ^ 2 - a * b) / c) (a * b / c) (a ^ 2 - a ^ 2 / c) (a * b / c) := by
  have : det3 (a ^ 2) 0 (a ^ 2 + (b ^ 2 - a * b) / c) (a * b / c) (a ^ 2 - a ^ 2 / c) (a * b / c)
      = a * b * (a ^ 2 + b ^ 2 - a * b) / c ^ 2 := by
    simp only [det3]; field_simp; ring
  rw [this]
  have := hc2pos ha hb
  positivity

theorem U3_cong {c : ℝ} (px py : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hc2 : c ^ 2 + a * b = a ^ 2 + b ^ 2) :
    (triUV px py (a ^ 2) 0 (a ^ 2 + (b ^ 2 - a * b) / c) (a * b / c) (a ^ 2 - a ^ 2 / c) (a * b / c)
      (dU3 ha hb hc hc2)).Congruent (R3 ha hb) := by
  have hc2' : c ^ 2 = a ^ 2 - a * b + b ^ 2 := by linarith
  refine cong_of_three ⟨![0, 2, 1], ![0, 2, 1], by decide, by decide⟩ ?_ ?_ ?_
  · show _ = dist ((R3 ha hb).pts 0) ((R3 ha hb).pts 2) ^ 2
    rw [tri_d01, R3_02]; field_simp; nlinarith [hc2']
  · show _ = dist ((R3 ha hb).pts 2) ((R3 ha hb).pts 1) ^ 2
    rw [tri_d12, dist_comm, R3_12]; field_simp; nlinarith [hc2']
  · show _ = dist ((R3 ha hb).pts 0) ((R3 ha hb).pts 1) ^ 2
    rw [tri_d02, R3_01]; field_simp; nlinarith [hc2']

end pieces


/-! ### Lemma 4 -/

/-- **Zhang's Lemma 4 (UNAUDITED).**  `a,b,c` naturals, `c² + ab = a² + b²` (tile `(a,b,c)` with
angle `π/3` between `a` and `b`).  The isosceles trapezoid `Tz px py (c²) (ab)` (base angles `π/3`,
top `c²`, legs `ab`, bottom `a²+b²`) carries `a²+b²+c²` tiles congruent to `R3 a b`. -/
theorem zhang_lemma4 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hcab : c * c + a * b = a * a + b * b) (px py : ℝ) :
    Dis (R3 (Nat.cast_pos.mpr ha : (0:ℝ) < a) (Nat.cast_pos.mpr hb : (0:ℝ) < b))
      (Tz px py ((c : ℝ) ^ 2) ((a : ℝ) * b)) (a * a + b * b + c * c) := by
  have ha' : (0:ℝ) < a := Nat.cast_pos.mpr ha
  have hb' : (0:ℝ) < b := Nat.cast_pos.mpr hb
  have hc' : (0:ℝ) < c := Nat.cast_pos.mpr hc
  have hc2 : (c:ℝ) ^ 2 + (a:ℝ) * b = (a:ℝ) ^ 2 + (b:ℝ) ^ 2 := by
    have h := congrArg (Nat.cast (R := ℝ)) hcab
    push_cast at h; nlinarith [h]
  have hcc : (c:ℝ) ^ 2 = (a:ℝ) ^ 2 + (b:ℝ) ^ 2 - a * b := by linarith
  have hP1 := Dis_scaled_uv (R := R3 ha' hb') px py 0 0 (a:ℝ) 0 0 (b:ℝ) ((a:ℝ) ^ 2) 0 0
    ((a:ℝ) * b) a ha (det_ab ha' hb') (d1 ha' hb') (U1_cong px py ha' hb')
    (by ring) (by ring) (by ring) (by ring)
  rw [P1_eq px py ha' hb'] at hP1
  have hP2 := Dis_scaled_uv (R := R3 ha' hb') px py ((a:ℝ) ^ 2 + (b:ℝ) ^ 2) 0
    ((a:ℝ) ^ 2 + (b:ℝ) ^ 2 - a) a ((a:ℝ) ^ 2 + (b:ℝ) ^ 2 - b) 0
    ((a:ℝ) ^ 2 + (b:ℝ) ^ 2 - a * b) ((a:ℝ) * b) ((a:ℝ) ^ 2) 0 b hb (dU2 ha' hb') (d2 ha' hb')
    (U2_cong px py ha' hb') (by ring) (by ring) (by ring) (by ring)
  rw [P2_eq px py ha' hb'] at hP2
  have hP3 := Dis_scaled_uv (R := R3 ha' hb') px py ((a:ℝ) ^ 2) 0
    ((a:ℝ) ^ 2 + ((b:ℝ) ^ 2 - a * b) / c) ((a:ℝ) * b / c) ((a:ℝ) ^ 2 - (a:ℝ) ^ 2 / c)
    ((a:ℝ) * b / c)
    ((a:ℝ) ^ 2 + (b:ℝ) ^ 2 - a * b) ((a:ℝ) * b) 0 ((a:ℝ) * b) c hc (dU3 ha' hb' hc' hc2)
    (d3 ha' hb') (U3_cong px py ha' hb' hc' hc2)
    (by field_simp <;> ring) (by field_simp <;> ring) (by field_simp <;> ring) (by field_simp <;> ring)
  rw [P3_eq px py ha' hb'] at hP3
  have hab := mul_pos ha' hb'
  have hcpos := hc2pos ha' hb'
  have g13 := Dis.glue_uv hP1 hP3 px py 0 ((a:ℝ) * b) ((a:ℝ) ^ 2) 0
    (Or.inl (by positivity)) ?_ ?_
  · have g := Dis.glue_uv g13 hP2 px py ((a:ℝ) ^ 2 + (b:ℝ) ^ 2 - a * b) ((a:ℝ) * b) ((a:ℝ) ^ 2) 0
      (Or.inr (by positivity)) ?_ ?_
    · refine g.congr ?_ ?_
      · rw [hcc, Tz_eq_union px py ha' hb']
      · ring
    · rintro q (⟨h1, hu, hv⟩ | ⟨h1, h2, h3⟩)
      · simp only [Lf]; nlinarith [mul_nonneg ha'.le h1, mul_nonneg hcpos.le hv]
      · simp only [Lf]; nlinarith [mul_nonneg hb'.le h3]
    · rintro q ⟨h1, hv, h3⟩
      simp only [Lf]; nlinarith [mul_nonneg hb'.le h1]
  · rintro q ⟨h1, hu, hv⟩
    simp only [Lf]; nlinarith [mul_nonneg ha'.le h1]
  · rintro q ⟨h1, h2, h3⟩
    simp only [Lf]; nlinarith [mul_nonneg ha'.le h2]

end Erdos634.ZhangPi3
