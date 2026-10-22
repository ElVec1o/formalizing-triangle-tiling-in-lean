import Erdos634.Draft.ZhangPi3L4
import Erdos634.Draft.ZhangThm4

/-!
# Zhang Theorem 5 (arXiv 2512.22696v4, §3.2): equilateral triangles of side `m a b` for the `π/3` tile

Tile `(a,b,c)` with `c² + ab = a² + b²` (angle `π/3` between `a` and `b`), model `R3 a b`.
Chain, all generic frame machinery of `ZhangPara`/`ZhangProp3`/`ZhangThm4` reused:
* `Dis_slice3`: `Tz px py X (ab)` carries `2X + ab` tiles when `a²+b² < X+a+b`
  (Lemma 2' parallelogram of width `z = X − c²` glued to Lemma 4's trapezoid);
* `Dis_stack3`: `Tz px py X (m ab)` carries `m(2X + m ab)` tiles (Prop 3 analogue);
* `zhang_thm5_rst`: for `r,s,t` with `a²+b² < ·(ab)+a+b`, the equilateral triangle of side
  `(r+s+t)ab` carries `(r+s+t)²ab` tiles (pinwheel `Dis_pinwheel`);
* `zhang_thm5`: with `M₀ = ⌊(a²+b²−a−b)/(ab)⌋ + 1`, all `m ≥ 3 M₀`: side `m a b`, `m² a b` tiles.
Zhang's `M = 3⌈(a²+b²−a−b)/(ab)⌉` equals `3 M₀` unless `ab ∣ a²+b²−a−b` (strict inequality is
needed in Frobenius).  Extra hypotheses made explicit: `gcd(a,b)=1` (implicit in Zhang's Lemma 2)
and `1 < ab` (excludes the unit equilateral tile `(1,1,1)`).  UNAUDITED.
Credit Zhang (arXiv 2512.22696), Beeson, Beeson-Rosu, Laczkovich.
-/

namespace Erdos634.ZhangThm5

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.GlueCut Erdos634.SssCongruent Erdos634.ZhangL1 Erdos634.ZhangPara
  Erdos634.ZhangPi3 Erdos634.ZhangProp3 Erdos634.ZhangThm4

theorem add_le_mul_pi3 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (h1 : 1 < a * b)
    (hcab : c * c + a * b = a * a + b * b) : a + b ≤ a * b := by
  by_contra hcon
  replace hcon := not_le.mp hcon
  have : a = 1 ∨ b = 1 := by
    by_contra h2
    push Not at h2
    have : 2 ≤ a := by omega
    have : 2 ≤ b := by omega
    nlinarith
  rcases this with rfl | rfl
  · have hb2 : 2 ≤ b := by omega
    rcases le_or_gt b c with h | h
    · nlinarith
    · have : c + 1 ≤ b := h
      nlinarith
  · have ha2 : 2 ≤ a := by omega
    rcases le_or_gt a c with h | h
    · nlinarith
    · have : c + 1 ≤ a := h
      nlinarith

/-- One slice. -/
theorem Dis_slice3 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : 1 < a * b)
    (hcab : c * c + a * b = a * a + b * b) (hcop : Nat.Coprime a b) (X : ℕ)
    (hX : a * a + b * b < X + a + b) (px py : ℝ) :
    Dis (R3 (Nat.cast_pos.mpr ha : (0:ℝ) < a) (Nat.cast_pos.mpr hb : (0:ℝ) < b))
      (Tz px py (X : ℝ) ((a:ℝ) * b)) (2 * X + a * b) := by
  have hge := add_le_mul_pi3 a b c ha hb h1 hcab
  have hXz : c * c < X := by
    have : 0 < c * c := Nat.mul_pos hc hc
    omega
  obtain ⟨z, hz⟩ : ∃ z, X = z + c * c := ⟨X - c * c, by omega⟩
  have hz0 : 0 < z := by omega
  have hzab : a * b < z + a + b := by omega
  have hq := zhang_lemma2_pi3 a b z ha hb hcop hz0 hzab px py
  have ht := zhang_lemma4 a b c ha hb hc hcab (shx px (z:ℝ) 0) (shy py 0)
  have hz' : (0:ℝ) ≤ z := Nat.cast_nonneg z
  have hab' : (0:ℝ) ≤ (a:ℝ) * b := by positivity
  have hx0 : (0:ℝ) ≤ (c:ℝ) ^ 2 := by positivity
  refine (Dis.glue_u hq ht px py (z:ℝ) ?_ ?_).congr ?_ ?_
  · intro q hq; exact hq.2.1
  · intro q hq
    have := hq.1; rw [uu_sh] at this; linarith
  · rw [← Tz_split_u px py z _ _ hz' hx0 hab']
    congr 1
    rw [hz]; push_cast; ring
  · rw [hz]; nlinarith [hcab]

/-- Stack of `m ≥ 1` slices. -/
theorem Dis_stack3 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : 1 < a * b)
    (hcab : c * c + a * b = a * a + b * b) (hcop : Nat.Coprime a b) :
    ∀ m : ℕ, 0 < m → ∀ (X : ℕ), a * a + b * b < X + a + b → ∀ px py : ℝ,
    Dis (R3 (Nat.cast_pos.mpr ha : (0:ℝ) < a) (Nat.cast_pos.mpr hb : (0:ℝ) < b))
      (Tz px py (X : ℝ) ((m : ℝ) * ((a:ℝ) * b))) (m * (2 * X + m * (a * b))) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro X hX px py
    exact (Dis_slice3 a b c ha hb hc h1 hcab hcop X hX px py).congr (by simp) (by ring)
  | succ m hm ih =>
    intro X hX px py
    have hX' : a * a + b * b < X + m * (a * b) + a + b := by omega
    have hlow := Dis_slice3 a b c ha hb hc h1 hcab hcop (X + m * (a * b)) hX' px py
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

theorem prop3_cast3 (a b c x k : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : 1 < a * b)
    (hcab : c * c + a * b = a * a + b * b) (hcop : Nat.Coprime a b)
    (hx : a * a + b * b < x * (a * b) + a + b) (hk : 0 < k) (px py : ℝ) :
    Dis (R3 (Nat.cast_pos.mpr ha : (0:ℝ) < a) (Nat.cast_pos.mpr hb : (0:ℝ) < b))
      (Tz px py ((x : ℝ) * ((a : ℝ) * b)) ((k : ℝ) * ((a : ℝ) * b)))
      (k * (2 * (x * (a * b)) + k * (a * b))) := by
  refine (Dis_stack3 a b c ha hb hc h1 hcab hcop k hk (x * (a * b)) hx px py).congr ?_ rfl
  push_cast; rfl

/-- **Zhang's Theorem 5, `r,s,t` form (UNAUDITED).** -/
theorem zhang_thm5_rst (a b c r s t : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : 1 < a * b)
    (hcab : c * c + a * b = a * a + b * b) (hcop : Nat.Coprime a b)
    (hr : a * a + b * b < r * (a * b) + a + b) (hs : a * a + b * b < s * (a * b) + a + b)
    (ht : a * a + b * b < t * (a * b) + a + b) :
    Dis (R3 (Nat.cast_pos.mpr ha : (0:ℝ) < a) (Nat.cast_pos.mpr hb : (0:ℝ) < b))
      (Tri3 0 0 (((r + s + t : ℕ) : ℝ) * ((a : ℝ) * b))) ((r + s + t) * (r + s + t) * (a * b)) := by
  have ha' : (0:ℝ) < a := Nat.cast_pos.mpr ha
  have hb' : (0:ℝ) < b := Nat.cast_pos.mpr hb
  have hpos : ∀ x : ℕ, a * a + b * b < x * (a * b) + a + b → 0 < x := by
    intro x hx
    rcases Nat.eq_zero_or_pos x with rfl | h
    · exfalso
      have : a ≤ a * a := Nat.le_mul_self a
      have : b ≤ b * b := Nat.le_mul_self b
      simp at hx; omega
    · exact h
  have hr0 := hpos r hr
  have hs0 := hpos s hs
  have ht0 := hpos t ht
  have hab : (0:ℝ) < (a:ℝ) * b := mul_pos ha' hb'
  have h1' := prop3_cast3 a b c r s ha hb hc h1 hcab hcop hr hs0 0 0
  have h2 := fun px py => prop3_cast3 a b c s t ha hb hc h1 hcab hcop hs ht0 px py
  have h3 := fun px py => prop3_cast3 a b c t r ha hb hc h1 hcab hcop ht hr0 px py
  have key := Dis_pinwheel (((r:ℝ)) * ((a:ℝ) * b)) ((s:ℝ) * ((a:ℝ) * b)) ((t:ℝ) * ((a:ℝ) * b))
    (by positivity) (by positivity) (by positivity) h1' h2 h3
  refine key.congr ?_ ?_
  · congr 1; push_cast; ring
  · ring

/-- Equiconstructibility for the `π/3` tile. -/
def EquiConstr3 (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (X : ℝ) (n : ℕ) : Prop :=
  Dis (R3 (Nat.cast_pos.mpr ha : (0:ℝ) < a) (Nat.cast_pos.mpr hb : (0:ℝ) < b)) (Tri3 0 0 X) n

/-- **Zhang's Theorem 5 (UNAUDITED).**  `M₀ = ⌊(a²+b²−a−b)/(ab)⌋ + 1`; for all `m ≥ 3 M₀`, the
equilateral triangle of side `m a b` is tiled by `m² a b` copies of the tile with angle `π/3`. -/
theorem zhang_thm5 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1 : 1 < a * b)
    (hcab : c * c + a * b = a * a + b * b) (hcop : Nat.Coprime a b)
    (m : ℕ) (hm : 3 * ((a * a + b * b - a - b) / (a * b) + 1) ≤ m) :
    EquiConstr3 a b ha hb ((m : ℝ) * ((a : ℝ) * b)) (m * m * (a * b)) := by
  set M0 := (a * a + b * b - a - b) / (a * b) + 1 with hM0
  have hab : 0 < a * b := Nat.mul_pos ha hb
  have hlt : a * a + b * b - a - b < M0 * (a * b) := by
    have := Nat.lt_mul_div_succ (a * a + b * b - a - b) hab
    rw [hM0]; linarith [Nat.mul_comm (a * b) ((a * a + b * b - a - b) / (a * b) + 1)]
  have hle1 : a ≤ a * a := Nat.le_mul_self a
  have hle2 : b ≤ b * b := Nat.le_mul_self b
  have hM : a * a + b * b < M0 * (a * b) + a + b := by omega
  have hge : ∀ x, M0 ≤ x → a * a + b * b < x * (a * b) + a + b := by
    intro x hx
    have := Nat.mul_le_mul_right (a * b) hx
    omega
  have key := zhang_thm5_rst a b c M0 M0 (m - 2 * M0) ha hb hc h1 hcab hcop hM hM
    (hge _ (by omega))
  unfold EquiConstr3
  have e : M0 + M0 + (m - 2 * M0) = m := by omega
  rw [e] at key
  exact key

/-- Witness `(5,8,7)` (Zhang's example, Herdt): `49 + 40 = 25 + 64`, `gcd = 1`, `ab = 40`,
`M₀ = ⌊76/40⌋ + 1 = 2`, `m = 6`: side `240`, `36·40 = 1440` tiles; area `240²√3/4 = 1440·40√3/4`. -/
theorem zhang_thm5_587 : ∃ n : ℕ, n = 1440 ∧ ∃ C : CongruentRegionDissection n,
    C.region = Tri3 0 0 (((6:ℕ):ℝ) * (((5:ℕ):ℝ) * ((8:ℕ):ℝ))) := by
  obtain ⟨C, hr, -⟩ := zhang_thm5 5 8 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) 6 (by norm_num)
  exact ⟨_, by norm_num, C, hr⟩

/-- Second witness `(3,8,7)`: `49 + 24 = 9 + 64`, `ab = 24`, `M₀ = ⌊62/24⌋ + 1 = 3`, `m = 9`:
side `216`, `81·24 = 1944` tiles. -/
theorem zhang_thm5_387 : ∃ n : ℕ, n = 1944 ∧ ∃ C : CongruentRegionDissection n,
    C.region = Tri3 0 0 (((9:ℕ):ℝ) * (((3:ℕ):ℝ) * ((8:ℕ):ℝ))) := by
  obtain ⟨C, hr, -⟩ := zhang_thm5 3 8 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) 9 (by norm_num)
  exact ⟨_, by norm_num, C, hr⟩

/-- Lemma 2' witness `(5,8)`, `x = 40 > 27`: `2x = 80` tiles. -/
theorem zhang_lemma2_pi3_58 (px py : ℝ) : ∃ n : ℕ, n = 80 ∧ ∃ C : CongruentRegionDissection n,
    C.region = Qs px py (40 : ℕ) (((5:ℕ):ℝ) * ((8:ℕ):ℝ)) := by
  obtain ⟨C, hr, -⟩ := zhang_lemma2_pi3 5 8 40 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) px py
  exact ⟨2 * 40, by norm_num, C, hr⟩

/-- Lemma 4 witness `(5,8,7)`: `Tz` with top `49`, legs `40`: `25+64+49 = 138` tiles
(area `40·(98+40)/40 = 138`). -/
theorem zhang_lemma4_587 (px py : ℝ) : ∃ n : ℕ, n = 138 ∧ ∃ C : CongruentRegionDissection n,
    C.region = Tz px py (((7:ℕ):ℝ) ^ 2) (((5:ℕ):ℝ) * ((8:ℕ):ℝ)) := by
  obtain ⟨C, hr, -⟩ := zhang_lemma4 5 8 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) px py
  exact ⟨_, by norm_num, C, hr⟩

end Erdos634.ZhangThm5
