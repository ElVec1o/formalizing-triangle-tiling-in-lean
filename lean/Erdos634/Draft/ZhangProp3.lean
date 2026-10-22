import Erdos634.Draft.ZhangPara
import Erdos634.TranslateDissection

/-!
# Zhang Proposition 3 (arXiv 2512.22696v4): ideal trapezoids with `x > c² − a − b` and `ab ∣ y`

Frame as in `ZhangPara`.  `Tz px py x y` is the isosceles trapezoid with `π/3` base angles, short
side `x`, legs `y`, long base `x + y`, vertices `p, p+(x+y)e₁, p+x e₁+y e₂, p+y e₂`.

`zhang_prop3`: for naturals `a,b,c` with `c² = a²+b²+ab`, `gcd(a,b)=1` (implicit in Zhang's use of
Lemma 2), `x` with `c² < x + a + b` (i.e. `x > c²−a−b`) and `k ≥ 1`, the trapezoid
`Tz px py x (k a b)` (legs `y = k a b`) carries `k (2x + k a b)` tiles congruent to `Rmodel`.
The tile count is forced by area: `y(2x+y)/(ab)`.

Proof: the trapezoid is stacked from `k` slices of leg `ab` (`Tz_split_v`); each slice is a
parallelogram `Qs z (ab)` (Lemma 2) glued along `u = z` to the Lemma-1 trapezoid
(`Trap = Tz 0 0 (a²+b²) (ab)`, translated).  UNAUDITED.
Credit Zhang (arXiv 2512.22696), Beeson, Beeson-Rosu, Laczkovich.
-/

namespace Erdos634.ZhangProp3

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.GlueCut Erdos634.SssCongruent Erdos634.ZhangL1 Erdos634.ZhangPara
  Erdos634.TranslateDissection

/-! ### Translation of dissections of frame-defined sets -/

theorem uu_add (px py : ℝ) (r : Plane) : uu px py (mkPt px py +ᵥ r) = uu 0 0 r := by
  have := zs_pos.ne'
  simp only [uu, vadd_eq_add, PiLp.add_apply, mkPt_zero, mkPt_one]; ring_nf

theorem vv_add (px py : ℝ) (r : Plane) : vv px py (mkPt px py +ᵥ r) = vv 0 0 r := by
  have := zs_pos.ne'
  simp only [vv, vadd_eq_add, PiLp.add_apply, mkPt_zero, mkPt_one]; ring_nf

theorem image_transl (P : ℝ → ℝ → Prop) (px py : ℝ) :
    (transEquiv (mkPt px py)) '' {q | P (uu 0 0 q) (vv 0 0 q)}
      = {q | P (uu px py q) (vv px py q)} := by
  ext q
  constructor
  · rintro ⟨r, hr, rfl⟩
    show P (uu px py (mkPt px py +ᵥ r)) (vv px py (mkPt px py +ᵥ r))
    rw [uu_add, vv_add]; exact hr
  · intro hq
    refine ⟨q - mkPt px py, ?_, ?_⟩
    · show P (uu 0 0 (q - mkPt px py)) (vv 0 0 (q - mkPt px py))
      have e1 : uu 0 0 (q - mkPt px py) = uu px py q := by
        have := zs_pos.ne'
        simp only [uu, PiLp.sub_apply, mkPt_zero, mkPt_one]; ring_nf
      have e2 : vv 0 0 (q - mkPt px py) = vv px py q := by
        have := zs_pos.ne'
        simp only [vv, PiLp.sub_apply, mkPt_zero, mkPt_one]; ring_nf
      rw [e1, e2]; exact hq
    · show mkPt px py +ᵥ (q - mkPt px py) = q
      simp

theorem Dis.transl {R : Tri} {n : ℕ} (P : ℝ → ℝ → Prop)
    (h : Dis R {q | P (uu 0 0 q) (vv 0 0 q)} n) (px py : ℝ) :
    Dis R {q | P (uu px py q) (vv px py q)} n := by
  obtain ⟨C, hr, hm⟩ := h
  refine ⟨mapCongruentRegionDissection (transEquiv (mkPt px py)) C, ?_, hm⟩
  show (transEquiv (mkPt px py)).toAffineEquiv '' C.region = _
  rw [hr]
  exact image_transl P px py

/-! ### Lemma 1's trapezoid in the frame -/

variable {a b c : ℝ}

theorem Trap_eq_Tz (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hc2 : c ^ 2 = a ^ 2 + b ^ 2 + a * b) :
    Trap a b c = Tz 0 0 (a ^ 2 + b ^ 2) (a * b) := by
  have hz := zs_pos
  have hzs := zs_sq
  have hh0 := hh_pos ha hb
  have hab : 0 < a * b := mul_pos ha hb
  have hcab : 0 < c ^ 2 - a * b := by nlinarith [sq_nonneg a, sq_nonneg b]
  have hhh : hh a b = a * b * zs / 2 := rfl
  ext q
  have hq0 := q0_eq 0 0 q
  have hq1 := q1_eq 0 0 q
  simp only [Tz, Set.mem_setOf_eq]
  constructor
  · intro hq
    obtain ⟨hAB, hBC, hCD, hDA⟩ := hull_ineq ha hb hc2 q hq
    simp only [det3] at hAB hBC hCD hDA
    have h1 : 0 ≤ q 1 := by nlinarith
    have h2 : q 1 ≤ hh a b := by nlinarith
    have h3 : q 1 ≤ zs * q 0 := by
      have : 0 ≤ (a * b / 2) * (zs * q 0 - q 1) := by rw [hhh] at hDA; nlinarith
      have hp : 0 < a * b / 2 := by positivity
      nlinarith [(mul_nonneg_iff_of_pos_left hp).mp this]
    have h4 : q 1 + zs * q 0 ≤ zs * c ^ 2 := by
      have : 0 ≤ (a * b / 2) * (zs * c ^ 2 - q 1 - zs * q 0) := by rw [hhh] at hBC; nlinarith
      have hp : 0 < a * b / 2 := by positivity
      nlinarith [(mul_nonneg_iff_of_pos_left hp).mp this]
    unfold uu vv
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [sub_zero]
      rw [sub_nonneg, div_le_iff₀ hz]; linarith
    · simp only [sub_zero]; positivity
    · simp only [sub_zero]
      rw [div_le_iff₀ hz, hhh] at *; nlinarith
    · simp only [sub_zero]
      have : q 0 - q 1 / zs + 2 * q 1 / zs = q 0 + q 1 / zs := by field_simp; ring
      rw [this, show a ^ 2 + b ^ 2 + a * b = c ^ 2 by rw [hc2]]
      have : q 0 + q 1 / zs ≤ c ^ 2 := by
        rw [← sub_nonneg]
        have : c ^ 2 - (q 0 + q 1 / zs) = (zs * c ^ 2 - q 1 - zs * q 0) / zs := by field_simp; ring
        rw [this]; apply div_nonneg <;> linarith
      exact this
  · rintro ⟨hu, hv, hv', huv⟩
    have hc3 : (a ^ 2 + b ^ 2) + a * b = c ^ 2 := by rw [hc2]
    have hu' : 0 ≤ uu 0 0 q := hu
    have e0 : q 0 = uu 0 0 q + vv 0 0 q / 2 := by linarith
    have e1 : q 1 = vv 0 0 q * zs / 2 := by linarith
    have hmem : q ∈ (T2 ha hb hc2).carrier ∪ (T3 ha hb hc).carrier ∪ (T1 ha hb).carrier := by
      apply trap_sub_union_of_ineq ha hb hc hc2 q <;> simp only [det3] <;> rw [e0, e1] <;> (try rw [hhh])
      · nlinarith [mul_nonneg hv hz.le, sq_nonneg c]
      · nlinarith [mul_nonneg (mul_nonneg hab.le hz.le) (sub_nonneg.mpr (show uu 0 0 q + vv 0 0 q ≤ c ^ 2 by linarith))]
      · nlinarith [mul_nonneg (mul_nonneg hab.le hz.le) (sub_nonneg.mpr hv'), hab]
      · nlinarith [mul_nonneg (mul_nonneg hab.le hz.le) hu]
    have := tri_sub_trap ha hb hc hc2
    rcases hmem with (h | h) | h
    · exact this.2.1 h
    · exact this.2.2 h
    · exact this.1 h

/-- Lemma 1's trapezoid, translated to any frame origin, as a `Dis`. -/
theorem Dis_Tz_lemma1 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hcab : c * c = a * a + b * b + a * b) (px py : ℝ) :
    Dis (Rmodel (Nat.cast_pos.mpr ha : (0:ℝ) < a) (Nat.cast_pos.mpr hb : (0:ℝ) < b))
      (Tz px py ((a:ℝ) ^ 2 + (b:ℝ) ^ 2) ((a:ℝ) * b)) (a * a + b * b + c * c) := by
  have ha' : (0:ℝ) < a := Nat.cast_pos.mpr ha
  have hb' : (0:ℝ) < b := Nat.cast_pos.mpr hb
  have hc' : (0:ℝ) < c := Nat.cast_pos.mpr hc
  have hc2 : (c:ℝ) ^ 2 = (a:ℝ) ^ 2 + (b:ℝ) ^ 2 + a * b := by
    exact_mod_cast (by nlinarith [hcab] : c ^ 2 = a ^ 2 + b ^ 2 + a * b)
  obtain ⟨N, hN, C, hr, hm⟩ := zhang_lemma1 a b c ha hb hc hcab
  have h0 : Dis (Rmodel ha' hb') (Tz 0 0 ((a:ℝ) ^ 2 + (b:ℝ) ^ 2) ((a:ℝ) * b)) N := by
    refine ⟨C, ?_, hm⟩
    rw [hr, Trap_eq_Tz ha' hb' hc' hc2]
  subst hN
  exact Dis.transl (fun u v => 0 ≤ u ∧ 0 ≤ v ∧ v ≤ (a:ℝ) * b ∧
    u + v ≤ ((a:ℝ) ^ 2 + (b:ℝ) ^ 2) + (a:ℝ) * b) h0 px py

/-! ### Splitting trapezoids -/

theorem Tz_split_u (px py z x0 y : ℝ) (hz : 0 ≤ z) (hx0 : 0 ≤ x0) (hy : 0 ≤ y) :
    Tz px py (z + x0) y = Qs px py z y ∪ Tz (shx px z 0) (shy py 0) x0 y := by
  ext q
  simp only [Tz, Qs, Set.mem_union, Set.mem_setOf_eq, uu_sh, vv_sh, sub_zero]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    rcases le_total (uu px py q) z with h | h
    · exact Or.inl ⟨h1, h, h2, h3⟩
    · exact Or.inr ⟨by linarith, h2, h3, by linarith⟩
  · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
    · exact ⟨h1, h3, h4, by linarith⟩
    · exact ⟨by linarith, h2, h3, by linarith⟩

theorem Tz_split_v (px py x y y' : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hy' : 0 ≤ y') :
    Tz px py x (y + y') = Tz px py (x + y') y ∪ Tz (shx px 0 y) (shy py y) x y' := by
  ext q
  simp only [Tz, Set.mem_union, Set.mem_setOf_eq, uu_sh, vv_sh, sub_zero]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    rcases le_total (vv px py q) y with h | h
    · exact Or.inl ⟨h1, h2, h, by linarith⟩
    · exact Or.inr ⟨h1, by linarith, by linarith, by linarith⟩
  · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
    · exact ⟨h1, h2, by linarith, by linarith⟩
    · exact ⟨h1, by linarith, by linarith, by linarith⟩

/-- `a + b ≤ a b` for a Löschian triple in naturals (so `a, b ≥ 2` automatically). -/
theorem add_le_mul_of_cab (a b c : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hcab : c * c = a * a + b * b + a * b) : a + b ≤ a * b := by
  by_contra hcon
  replace hcon := not_le.mp hcon
  have : a = 1 ∨ b = 1 := by
    by_contra h2
    push Not at h2
    have : 2 ≤ a := by omega
    have : 2 ≤ b := by omega
    nlinarith
  rcases this with rfl | rfl
  · rcases le_or_gt c b with h | h <;> nlinarith
  · rcases le_or_gt c a with h | h <;> nlinarith

/-- One slice: the trapezoid of leg `ab` and short side `X` with `c² < X + a + b`. -/
theorem Dis_slice (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hcab : c * c = a * a + b * b + a * b) (hcop : Nat.Coprime a b) (X : ℕ)
    (hX : c * c < X + a + b) (px py : ℝ) :
    Dis (Rmodel (Nat.cast_pos.mpr ha : (0:ℝ) < a) (Nat.cast_pos.mpr hb : (0:ℝ) < b))
      (Tz px py (X : ℝ) ((a:ℝ) * b)) (2 * X + a * b) := by
  have hge := add_le_mul_of_cab a b c ha hb hcab
  have hXz : a * a + b * b < X := by omega
  obtain ⟨z, hz⟩ : ∃ z, X = z + (a * a + b * b) := ⟨X - (a * a + b * b), by omega⟩
  have hz0 : 0 < z := by omega
  have hzab : a * b < z + a + b := by omega
  have hq := zhang_lemma2 a b c z ha hb hcab hcop hz0 hzab px py
  have ht := Dis_Tz_lemma1 a b c ha hb hc hcab (shx px (z:ℝ) 0) (shy py 0)
  have hz' : (0:ℝ) ≤ z := Nat.cast_nonneg z
  have hab' : (0:ℝ) ≤ (a:ℝ) * b := by positivity
  have hx0 : (0:ℝ) ≤ (a:ℝ) ^ 2 + (b:ℝ) ^ 2 := by positivity
  refine (Dis.glue_u hq ht px py (z:ℝ) ?_ ?_).congr ?_ ?_
  · intro q hq; exact hq.2.1
  · intro q hq
    have := hq.1; rw [uu_sh] at this; linarith
  · rw [← Tz_split_u px py z _ _ hz' hx0 hab']
    congr 1
    rw [hz]; push_cast; ring
  · rw [hz]; nlinarith [hcab]

/-- Stack of `m ≥ 1` slices. -/
theorem Dis_stack (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hcab : c * c = a * a + b * b + a * b) (hcop : Nat.Coprime a b) :
    ∀ m : ℕ, 0 < m → ∀ (X : ℕ), c * c < X + a + b → ∀ px py : ℝ,
    Dis (Rmodel (Nat.cast_pos.mpr ha : (0:ℝ) < a) (Nat.cast_pos.mpr hb : (0:ℝ) < b))
      (Tz px py (X : ℝ) ((m : ℝ) * ((a:ℝ) * b))) (m * (2 * X + m * (a * b))) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro X hX px py
    exact (Dis_slice a b c ha hb hc hcab hcop X hX px py).congr (by simp) (by ring)
  | succ m hm ih =>
    intro X hX px py
    have hX' : c * c < X + m * (a * b) + a + b := by omega
    have hlow := Dis_slice a b c ha hb hc hcab hcop (X + m * (a * b)) hX' px py
    have hup := ih X hX (shx px 0 ((a:ℝ) * b)) (shy py ((a:ℝ) * b))
    have hab' : (0:ℝ) ≤ (a:ℝ) * b := by positivity
    have hm' : (0:ℝ) ≤ (m:ℝ) * ((a:ℝ) * b) := by positivity
    have hX0 : (0:ℝ) ≤ (X:ℝ) := Nat.cast_nonneg X
    refine (Dis.glue_v hlow hup px py ((a:ℝ) * b) ?_ ?_).congr ?_ ?_
    · intro q hq; exact hq.2.2.1
    · intro q hq
      have := hq.2.1; rw [vv_sh] at this; linarith
    · have e := Tz_split_v px py (X:ℝ) ((a:ℝ) * b) ((m:ℝ) * ((a:ℝ) * b)) hX0 hab' hm'
      rw [show ((m + 1 : ℕ) : ℝ) * ((a:ℝ) * b) = (a:ℝ) * b + (m:ℝ) * ((a:ℝ) * b) by push_cast; ring,
        e]
      push_cast
      try rfl
    · ring

/-- **Zhang's Proposition 3 (UNAUDITED).**  `a,b,c` naturals with `c² = a²+b²+ab`, `gcd(a,b)=1`;
`x` natural with `x > c² − a − b` (stated `c² < x + a + b`); `k ≥ 1`.  The ideal trapezoid
`Tz px py x (k a b)` (base angles `π/3`, short side `x`, legs `y = k a b`) is tiled by
`k (2x + k a b)` copies of `Rmodel`. -/
theorem zhang_prop3 (a b c x k : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hcab : c * c = a * a + b * b + a * b) (hcop : Nat.Coprime a b)
    (hx : c * c < x + a + b) (hk : 0 < k) (px py : ℝ) :
    Dis (Rmodel (Nat.cast_pos.mpr ha : (0:ℝ) < a) (Nat.cast_pos.mpr hb : (0:ℝ) < b))
      (Tz px py (x : ℝ) ((k : ℝ) * ((a : ℝ) * b))) (k * (2 * x + k * (a * b))) :=
  Dis_stack a b c ha hb hc hcab hcop k hk x hx px py

/-- Witness `(3,5,7)`: `x = 42 > 41`, `k = 1`: `2·42 + 15 = 99` tiles.
Area check: `y(2x+y)/(ab) = 15·99/15`. -/
theorem zhang_prop3_357 (px py : ℝ) : ∃ n : ℕ, n = 99 ∧ ∃ C : CongruentRegionDissection n,
    C.region = Tz px py (42 : ℕ) ((1 : ℕ) * (((3:ℕ):ℝ) * ((5:ℕ):ℝ))) := by
  obtain ⟨C, hr, -⟩ := zhang_prop3 3 5 7 42 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) px py
  exact ⟨_, by norm_num, C, by simpa using hr⟩

/-- Witness `(3,5,7)`, `x = 45`, `k = 3` (legs 45): `3(90+45) = 405` tiles. -/
theorem zhang_prop3_357_k3 (px py : ℝ) : ∃ n : ℕ, n = 405 ∧ ∃ C : CongruentRegionDissection n,
    C.region = Tz px py (45 : ℕ) ((3 : ℕ) * (((3:ℕ):ℝ) * ((5:ℕ):ℝ))) := by
  obtain ⟨C, hr, -⟩ := zhang_prop3 3 5 7 45 3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) px py
  exact ⟨_, by norm_num, C, by simpa using hr⟩

/-- Witness `(8,7,13)`, `x = 155 > 154`, `k = 2`: `2(310 + 112) = 844` tiles. -/
theorem zhang_prop3_8_7_13 (px py : ℝ) : ∃ n : ℕ, n = 844 ∧ ∃ C : CongruentRegionDissection n,
    C.region = Tz px py (155 : ℕ) ((2 : ℕ) * (((8:ℕ):ℝ) * ((7:ℕ):ℝ))) := by
  obtain ⟨C, hr, -⟩ := zhang_prop3 8 7 13 155 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) px py
  exact ⟨_, by norm_num, C, by simpa using hr⟩

end Erdos634.ZhangProp3
