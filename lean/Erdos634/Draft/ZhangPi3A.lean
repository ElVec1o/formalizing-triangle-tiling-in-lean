import Erdos634.Draft.ZhangPara

/-!
# Zhang Theorem 5, part A (arXiv 2512.22696v4, §3.2, Fig. 6): the pi/3 tile

Tile `R3 a b` = the triangle with `(u,v)`-lattice vertices `(0,0), (a,0), (0,b)` in the frame of
`ZhangPara` (`e₁=(1,0)`, `e₂=(1/2,√3/2)`): sides `a`, `b` with angle `π/3` between them and third
side `c`, `c² = a² − ab + b²`.  Everything in `ZhangPara` (`Dis`, `Dis.glue_u/v`, `Dis.colN`,
`Dis.rowMix`, `frob`) is generic in the tile, so only the base pieces are new:

* `Dis_Qs_two3`: the parallelogram `Qs px py s t`, `(s,t) ∈ {(a,b),(b,a)}`, is two tiles
  (cut along the SHORT diagonal);
* `zhang_lemma2_pi3`: `Qs px py x (ab)` carries `2x` tiles for coprime `a,b`, `ab < x+a+b`;
* `zhang_lemma4`: Zhang's Lemma 4 (Fig. 6): `Tz px py (c²) (ab)` (isosceles trapezoid, base angles
  `π/3`, top `c²`, legs `ab`, bottom `a²+b²`) carries `a²+b²+c²` tiles: `ADE = a·R`, `EBC = b·R`,
  `DEC = c·R` with `E` on the bottom at distance `a²` from `A`.  Layout checked by side lengths
  (`DE = ac`, `EC = bc`, `DC = c²`; angle `π/3` at `E`).
UNAUDITED.  Credit Zhang (arXiv 2512.22696), Beeson, Beeson-Rosu, Laczkovich.
-/

namespace Erdos634.ZhangPi3

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.GlueCut Erdos634.SssCongruent Erdos634.ZhangL1 Erdos634.ZhangPara

/-! ### Generic gluing along a line through two lattice points -/

/-- Signed form of the line through `(u0,v0)` and `(u1,v1)` in the frame. -/
noncomputable def Lf (px py u0 v0 u1 v1 : ℝ) (q : Plane) : ℝ :=
  (u1 - u0) * (vv px py q - v0) - (uu px py q - u0) * (v1 - v0)

theorem lineFun_uv (px py u0 v0 u1 v1 : ℝ) (q : Plane) :
    lineFun (shx px u0 v0) (shy py v0) (shx px u1 v1) (shy py v1) q
      = zs / 2 * Lf px py u0 v0 u1 v1 q := by
  have := zs_pos.ne'
  simp only [lineFun_apply, Lf]; unfold uu vv shx shy; field_simp; ring

theorem Dis.glue_uv {R : Tri} {S1 S2 : Set Plane} {n1 n2 : ℕ} (h1 : Dis R S1 n1)
    (h2 : Dis R S2 n2) (px py u0 v0 u1 v1 : ℝ) (hne : u0 ≠ u1 ∨ v0 ≠ v1)
    (hS1 : ∀ q ∈ S1, Lf px py u0 v0 u1 v1 q ≤ 0) (hS2 : ∀ q ∈ S2, 0 ≤ Lf px py u0 v0 u1 v1 q) :
    Dis R (S1 ∪ S2) (n1 + n2) := by
  obtain ⟨C1, r1, m1⟩ := h1
  obtain ⟨C2, r2, m2⟩ := h2
  have hz := zs_pos
  have hf : (lineFun (shx px u0 v0) (shy py v0) (shx px u1 v1) (shy py v1)).linear ≠ 0 := by
    apply lineFun_linear_ne_zero
    rcases hne with h | h
    · by_cases hv : v0 = v1
      · left; unfold shx; subst hv; intro e; apply h; linarith
      · right; unfold shy; intro e; apply hv; nlinarith
    · right; unfold shy; intro e; apply h; nlinarith
  refine ⟨glueByLine C1 C2 (m1.trans m2.symm) _ hf ?_ ?_, ?_, ?_⟩
  · intro x hx
    rw [lineFun_uv]
    have := hS1 x (by rwa [← r1])
    nlinarith
  · intro x hx
    rw [lineFun_uv]
    have := hS2 x (by rwa [← r2])
    nlinarith
  · simp [r1, r2]
  · simp [m1]

/-! ### The tile -/

section tile
variable {a b : ℝ}

theorem det_ab (ha : 0 < a) (hb : 0 < b) : 0 < det3 0 0 a 0 0 b := by
  simp only [det3]; nlinarith [mul_pos ha hb]

noncomputable def R3 (ha : 0 < a) (hb : 0 < b) : Tri := triUV 0 0 0 0 a 0 0 b (det_ab ha hb)

theorem tri_d01 (px py u0 v0 u1 v1 u2 v2 : ℝ) (h : 0 < det3 u0 v0 u1 v1 u2 v2) :
    dist ((triUV px py u0 v0 u1 v1 u2 v2 h).pts 0) ((triUV px py u0 v0 u1 v1 u2 v2 h).pts 1) ^ 2
      = (u0 - u1) ^ 2 + (u0 - u1) * (v0 - v1) + (v0 - v1) ^ 2 := dist_sq_sh px py u0 v0 u1 v1

theorem tri_d12 (px py u0 v0 u1 v1 u2 v2 : ℝ) (h : 0 < det3 u0 v0 u1 v1 u2 v2) :
    dist ((triUV px py u0 v0 u1 v1 u2 v2 h).pts 1) ((triUV px py u0 v0 u1 v1 u2 v2 h).pts 2) ^ 2
      = (u1 - u2) ^ 2 + (u1 - u2) * (v1 - v2) + (v1 - v2) ^ 2 := dist_sq_sh px py u1 v1 u2 v2

theorem tri_d02 (px py u0 v0 u1 v1 u2 v2 : ℝ) (h : 0 < det3 u0 v0 u1 v1 u2 v2) :
    dist ((triUV px py u0 v0 u1 v1 u2 v2 h).pts 0) ((triUV px py u0 v0 u1 v1 u2 v2 h).pts 2) ^ 2
      = (u0 - u2) ^ 2 + (u0 - u2) * (v0 - v2) + (v0 - v2) ^ 2 := dist_sq_sh px py u0 v0 u2 v2

theorem R3_01 (ha : 0 < a) (hb : 0 < b) :
    dist ((R3 ha hb).pts 0) ((R3 ha hb).pts 1) ^ 2 = a ^ 2 := by
  have := tri_d01 0 0 0 0 a 0 0 b (det_ab ha hb); unfold R3; rw [this]; ring
theorem R3_12 (ha : 0 < a) (hb : 0 < b) :
    dist ((R3 ha hb).pts 1) ((R3 ha hb).pts 2) ^ 2 = a ^ 2 - a * b + b ^ 2 := by
  have := tri_d12 0 0 0 0 a 0 0 b (det_ab ha hb); unfold R3; rw [this]; ring
theorem R3_02 (ha : 0 < a) (hb : 0 < b) :
    dist ((R3 ha hb).pts 0) ((R3 ha hb).pts 2) ^ 2 = b ^ 2 := by
  have := tri_d02 0 0 0 0 a 0 0 b (det_ab ha hb); unfold R3; rw [this]; ring

end tile

/-! ### The parallelogram is two tiles -/

section two
variable {a b : ℝ}

theorem Dis_Qs_two3 (ha : 0 < a) (hb : 0 < b) (s t : ℝ)
    (hst : (s = a ∧ t = b) ∨ (s = b ∧ t = a)) (px py : ℝ) :
    Dis (R3 ha hb) (Qs px py s t) 2 := by
  have hs0 : 0 < s := by rcases hst with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> assumption
  have ht0 : 0 < t := by rcases hst with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> assumption
  have d1 : 0 < det3 0 0 s 0 0 t := by simp only [det3]; nlinarith
  have d2 : 0 < det3 s 0 s t 0 t := by simp only [det3]; nlinarith
  have r01 := R3_01 ha hb
  have r12 := R3_12 ha hb
  have r02 := R3_02 ha hb
  have cong1 : (triUV px py 0 0 s 0 0 t d1).Congruent (R3 ha hb) := by
    rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine cong_of_three ⟨![0, 1, 2], ![0, 1, 2], by decide, by decide⟩ ?_ ?_ ?_
      · show _ = dist ((R3 ha hb).pts 0) ((R3 ha hb).pts 1) ^ 2
        rw [tri_d01, r01]; ring
      · show _ = dist ((R3 ha hb).pts 1) ((R3 ha hb).pts 2) ^ 2
        rw [tri_d12, r12]; ring
      · show _ = dist ((R3 ha hb).pts 0) ((R3 ha hb).pts 2) ^ 2
        rw [tri_d02, r02]; ring
    · refine cong_of_three ⟨![0, 2, 1], ![0, 2, 1], by decide, by decide⟩ ?_ ?_ ?_
      · show _ = dist ((R3 ha hb).pts 0) ((R3 ha hb).pts 2) ^ 2
        rw [tri_d01, r02]; ring
      · show _ = dist ((R3 ha hb).pts 2) ((R3 ha hb).pts 1) ^ 2
        rw [tri_d12, dist_comm, r12]; ring
      · show _ = dist ((R3 ha hb).pts 0) ((R3 ha hb).pts 1) ^ 2
        rw [tri_d02, r01]; ring
  have cong2 : (triUV px py s 0 s t 0 t d2).Congruent (R3 ha hb) := by
    rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine cong_of_three ⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩ ?_ ?_ ?_
      · show _ = dist ((R3 ha hb).pts 2) ((R3 ha hb).pts 0) ^ 2
        rw [tri_d01, dist_comm, r02]; ring
      · show _ = dist ((R3 ha hb).pts 0) ((R3 ha hb).pts 1) ^ 2
        rw [tri_d12, r01]; ring
      · show _ = dist ((R3 ha hb).pts 2) ((R3 ha hb).pts 1) ^ 2
        rw [tri_d02, dist_comm, r12]; ring
    · refine cong_of_three ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩ ?_ ?_ ?_
      · show _ = dist ((R3 ha hb).pts 1) ((R3 ha hb).pts 0) ^ 2
        rw [tri_d01, dist_comm, r01]; ring
      · show _ = dist ((R3 ha hb).pts 0) ((R3 ha hb).pts 2) ^ 2
        rw [tri_d12, r02]; ring
      · show _ = dist ((R3 ha hb).pts 1) ((R3 ha hb).pts 2) ^ 2
        rw [tri_d02, r12]; ring
  obtain ⟨C1, r1, m1⟩ := Dis_tri _ _ cong1
  obtain ⟨C2, r2, m2⟩ := Dis_tri _ _ cong2
  refine (Dis.glue_uv (R := R3 ha hb) ⟨C2, r2, m2⟩ ⟨C1, r1, m1⟩ px py s 0 0 t
    (Or.inl (by intro h; linarith)) ?_ ?_).congr ?_ (by norm_num)
  · intro q hq
    rw [mem_triUV] at hq
    simp only [det3] at hq
    obtain ⟨_, h2, _⟩ := hq
    simp only [Lf]; nlinarith
  · intro q hq
    rw [mem_triUV] at hq
    simp only [det3] at hq
    obtain ⟨h1, _, _⟩ := hq
    simp only [Lf]; nlinarith
  · ext q
    simp only [Set.mem_union, mem_triUV, Qs, Set.mem_setOf_eq, det3]
    constructor
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
      · refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
      · refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
    · rintro ⟨h1, h2, h3, h4⟩
      rcases le_total (t * uu px py q + s * vv px py q) (s * t) with h | h
      · right; refine ⟨?_, ?_, ?_⟩ <;> nlinarith
      · left; refine ⟨?_, ?_, ?_⟩ <;> nlinarith

end two


/-! ### Lemma 2 for the pi/3 tile -/

theorem zhang_lemma2_pi3 (a b x : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hcop : Nat.Coprime a b) (hx0 : 0 < x) (hx : a * b < x + a + b) (px py : ℝ) :
    Dis (R3 (Nat.cast_pos.mpr ha : (0:ℝ) < a) (Nat.cast_pos.mpr hb : (0:ℝ) < b))
      (Qs px py (x : ℝ) ((a : ℝ) * b)) (2 * x) := by
  have ha' : (0:ℝ) < a := Nat.cast_pos.mpr ha
  have hb' : (0:ℝ) < b := Nat.cast_pos.mpr hb
  obtain ⟨i, j, hij⟩ := frob a b x hcop ha hb hx
  have hA : ∀ px py, Dis (R3 ha' hb') (Qs px py (a:ℝ) ((a:ℝ) * b)) (a * 2) := fun px py =>
    Dis.colN ha'.le hb'.le (fun px py => Dis_Qs_two3 ha' hb' a b (Or.inl ⟨rfl, rfl⟩) px py)
      a ha px py
  have hB : ∀ px py, Dis (R3 ha' hb') (Qs px py (b:ℝ) ((a:ℝ) * b)) (b * 2) := fun px py =>
    (Dis.colN hb'.le ha'.le (fun px py => Dis_Qs_two3 ha' hb' b a (Or.inr ⟨rfl, rfl⟩) px py)
      b hb px py).congr (by rw [mul_comm (b:ℝ) (a:ℝ)]) rfl
  have key := Dis.rowMix ha' hb' (mul_pos ha' hb').le hA hB i j (by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp at hij; omega
      · omega
    · omega) px py
  refine key.congr ?_ ?_
  · congr 1
    have : (x:ℝ) = i * a + j * b := by exact_mod_cast hij
    rw [this]
  · rw [hij]; ring

end Erdos634.ZhangPi3
