import Erdos634.Draft.LaczFormalL25Main

/-!
# Laczkovich Theorem 2.5, first triple `(α, α+β, α+2β)`: the theorem

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.5, Fig. 6), Beeson,
Beeson-Zhang, Zhang.  See `LaczFormalL25Main` for the construction.
-/

namespace Erdos634.LaczL25

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL21 Erdos634.LaczL24 Erdos634.Realizable

theorem norm_comb (w d : Plane) (p q x : ℝ) (hx : 0 ≤ x)
    (h : inner ℝ (p • w + q • d) (p • w + q • d) = x ^ 2) : ‖p • w + q • d‖ = x :=
  eq_of_sq_eq' (norm_nonneg _) hx (by rw [← real_inner_self_eq_norm_sq]; exact h)

theorem cos_sw01 (R : RTri) (hγ : R.a ^ 2 + R.a * R.b + R.b ^ 2 = R.c ^ 2) (W : ℚ)
    (hWdef : W = R.a + 2 * R.b) : R.sw01.cos1 = W / (2 * R.c) := by
  have ha := R.pa; have hb := R.pb; have hc := R.pc
  simp only [RTri.cos1, RTri.sw01]
  rw [hWdef, div_eq_div_iff (by positivity) (by positivity)]
  nlinarith [hγ]

theorem tau_sw01 (R : RTri) (hγ : R.a ^ 2 + R.a * R.b + R.b ^ 2 = R.c ^ 2) (W τq : ℚ)
    (hWdef : W = R.a + 2 * R.b) (hτdef : τq = R.b / W) :
    τq = tTau R.sw01.a R.sw01.b R.sw01.c W R.c := by
  have ha := R.pa; have hb := R.pb; have hc := R.pc
  simp only [tTau, RTri.sw01]
  have e : R.a ^ 2 - R.c ^ 2 = -(R.b * (R.a + R.b)) := by nlinarith [hγ]
  rw [e, hτdef, hWdef]; field_simp; ring

theorem cos_rot (R : RTri) (hγ : R.a ^ 2 + R.a * R.b + R.b ^ 2 = R.c ^ 2) : R.rot.cos1 = -1 / 2 := by
  have ha := R.pa; have hb := R.pb
  simp only [RTri.cos1, RTri.rot]
  rw [div_eq_div_iff (by positivity) (by norm_num)]
  nlinarith [hγ]

theorem tauI_rot (R : RTri) (hγ : R.a ^ 2 + R.a * R.b + R.b ^ 2 = R.c ^ 2) :
    tTauI R.rot.a R.rot.b R.rot.c R.a R.a = 2 := by
  have ha := R.pa; have hb := R.pb
  simp only [tTauI, RTri.rot]
  have e : R.b ^ 2 + R.a ^ 2 - R.c ^ 2 = -(R.a * R.b) := by nlinarith [hγ]
  rw [e]; field_simp; ring

set_option maxHeartbeats 2000000 in
/-- **The chart form of the first triple** (Fig. 6).  In a Gram chart `(D; w = F - D, d = A - D)` with `|w| = W = a + 2b`,
`|d| = c`, `⟨w, d⟩ = W²/2`, the target `T = E B D` (`ST τ`, `τ = b/W`) is a rational similar dissection. -/
theorem chart_ST (R : RTri) (hγ : R.a ^ 2 + R.a * R.b + R.b ^ 2 = R.c ^ 2) (W τq : ℚ) (hWdef : W = R.a + 2 * R.b)
    (hτdef : τq = R.b / W) (w d : Plane) (hdet : w 0 * d 1 - w 1 * d 0 ≠ 0)
    (hw : inner ℝ w w = (W : ℝ) ^ 2) (hd : inner ℝ d d = ((R.c : ℚ) : ℝ) ^ 2)
    (hwd : inner ℝ w d = (W : ℝ) ^ 2 / 2) :
    ChartRSD R 0 w d hdet (ST (τq : ℝ)) := by
  have ha := R.pa
  have hb := R.pb
  have hc := R.pc
  have hW : 0 < W := by rw [hWdef]; positivity
  have hτW : τq * W = R.b := by rw [hτdef]; field_simp
  have hτ0 : 0 < τq := by rw [hτdef]; positivity
  have hτ1 : τq < 1 / 2 := by
    rw [hτdef, div_lt_div_iff₀ hW (by norm_num), hWdef]; linarith
  have hρW : (1 - τq) * W = R.a + R.b := by rw [sub_mul, one_mul, hτW, hWdef]; ring
  have Iw : (1 - τq) ^ 2 * W ^ 2 - (1 - τq) * W ^ 2 + R.c ^ 2 = R.a ^ 2 := by
    have e : (1 - τq) ^ 2 * W ^ 2 - (1 - τq) * W ^ 2 + R.c ^ 2
        = ((1 - τq) * W) ^ 2 - ((1 - τq) * W) * W + R.c ^ 2 := by ring
    rw [e, hρW, hWdef]; nlinarith [hγ]
  have Id : τq ^ 2 * W ^ 2 - τq * W ^ 2 + R.c ^ 2 = R.a ^ 2 := by
    have e : τq ^ 2 * W ^ 2 - τq * W ^ 2 + R.c ^ 2 = (τq * W) ^ 2 - (τq * W) * W + R.c ^ 2 := by ring
    rw [e, hτW, hWdef]; nlinarith [hγ]
  have Iwd : -(τq * (1 - τq)) * W ^ 2 + W ^ 2 / 2 - R.c ^ 2 = -(R.a ^ 2 / 2) := by
    have e : -(τq * (1 - τq)) * W ^ 2 + W ^ 2 / 2 - R.c ^ 2
        = -((τq * W) * ((1 - τq) * W)) + W ^ 2 / 2 - R.c ^ 2 := by ring
    rw [e, hτW, hρW, hWdef]; nlinarith [hγ]
  have hτ0' : (0 : ℝ) < τq := by exact_mod_cast hτ0
  have hτ1' : (τq : ℝ) < 1 / 2 := by
    have h := (Rat.cast_lt (K := ℝ)).2 hτ1; push_cast at h; exact h
  -- (1) the trapezoid FDAC, Lemma 2.2 (ii)
  have hcosq : R.sw01.cos1 = W / (2 * R.c) := cos_sw01 R hγ W hWdef
  have hwd1 : inner ℝ w d = (W : ℝ) * (R.c : ℝ) * (R.sw01.cos1 : ℝ) := by
    rw [hcosq, hwd]; push_cast
    have : (R.c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
    field_simp
  have hτq : τq = tTau R.sw01.a R.sw01.b R.sw01.c W R.c := tau_sw01 R hγ W τq hWdef hτdef
  have cF : ChartRSD R 0 w d hdet (trapSet (τq : ℝ)) :=
    RatSimDiss.relabel (Δ := R.Δ) (Equiv.swap 0 1)
      (trap_ii R.sw01 0 w d hdet W R.c hW hc hw hd hwd1 τq hτq hτ0)
  -- (2) the tile ABC
  have hγR : (R.a : ℝ) ^ 2 + R.a * R.b + R.b ^ 2 = (R.c : ℝ) ^ 2 := by exact_mod_cast hγ
  have hWr : (W : ℝ) = R.a + 2 * R.b := by exact_mod_cast hWdef
  have hτWr : (τq : ℝ) * W = R.b := by exact_mod_cast hτW
  have hρWr : (1 - (τq : ℝ)) * W = R.a + R.b := by exact_mod_cast hρW
  have Iwr : (1 - (τq : ℝ)) ^ 2 * (W : ℝ) ^ 2 - (1 - (τq : ℝ)) * (W : ℝ) ^ 2 + (R.c : ℝ) ^ 2
      = (R.a : ℝ) ^ 2 := by exact_mod_cast Iw
  have Idr : (τq : ℝ) ^ 2 * (W : ℝ) ^ 2 - (τq : ℝ) * (W : ℝ) ^ 2 + (R.c : ℝ) ^ 2 = (R.a : ℝ) ^ 2 := by
    exact_mod_cast Id
  have Iwdr : -((τq : ℝ) * (1 - (τq : ℝ))) * (W : ℝ) ^ 2 + (W : ℝ) ^ 2 / 2 - (R.c : ℝ) ^ 2
      = -((R.a : ℝ) ^ 2 / 2) := by exact_mod_cast Iwd
  have cA : ChartRSD R 0 w d hdet (SA (τq : ℝ)) := by
    rw [← triAB_carrier hτ0' hτ1']
    refine chart_single (R := R) (A := 0) (w := w) (d := d) (h := hdet) _ ?_
    refine chart_tile R 0 w d hdet W R.c hw hd ((W : ℝ) ^ 2 / 2) hwd 0 1 0 2 (τq : ℝ) 1
      (by simp only [det3]; nlinarith) 1 1 one_pos ?_ ?_ ?_
    · simp only [Equiv.Perm.coe_one, id_eq, Rat.cast_one, one_pow, one_mul]
      rw [R.hc]; ring
    · simp only [Equiv.Perm.coe_one, id_eq, Rat.cast_one, one_pow, one_mul]
      rw [R.ha]; linear_combination Idr
    · simp only [Equiv.Perm.coe_one, id_eq, Rat.cast_one, one_pow, one_mul]
      rw [R.hb]; linear_combination ((τq : ℝ) * W + R.b) * hτWr
  -- (3) the isosceles trapezoid BEFC, Lemma 2.2 (iii), in a sub-chart
  have hdet' : ((1 - (τq : ℝ)) • w + (-1 : ℝ) • d) 0 * ((-(τq : ℝ)) • w + (1 : ℝ) • d) 1
      - ((1 - (τq : ℝ)) • w + (-1 : ℝ) • d) 1 * ((-(τq : ℝ)) • w + (1 : ℝ) • d) 0 ≠ 0 := by
    rw [det_comb]
    exact mul_ne_zero (by intro h; linarith) hdet
  have gw : inner ℝ ((1 - (τq : ℝ)) • w + (-1 : ℝ) • d) ((1 - (τq : ℝ)) • w + (-1 : ℝ) • d)
      = ((R.a : ℚ) : ℝ) ^ 2 := by
    rw [gram2, hw, hd, hwd]; linear_combination Iwr
  have gd : inner ℝ ((-(τq : ℝ)) • w + (1 : ℝ) • d) ((-(τq : ℝ)) • w + (1 : ℝ) • d)
      = ((R.a : ℚ) : ℝ) ^ 2 := by
    rw [gram2, hw, hd, hwd]; linear_combination Idr
  have hcosr : R.rot.cos1 = -1 / 2 := cos_rot R hγ
  have hwd' : inner ℝ ((1 - (τq : ℝ)) • w + (-1 : ℝ) • d) ((-(τq : ℝ)) • w + (1 : ℝ) • d)
      = ((R.a : ℚ) : ℝ) * ((R.a : ℚ) : ℝ) * (R.rot.cos1 : ℝ) := by
    rw [gram2, hw, hd, hwd, hcosr]; push_cast
    linear_combination Iwdr
  have htI : tTauI R.rot.a R.rot.b R.rot.c R.a R.a = 2 := tauI_rot R hγ
  have cB : ChartRSD R 0 w d hdet (SB (τq : ℝ)) := by
    have key := RatSimDiss.relabel (Δ := R.Δ) (finRotate 3)
      (trap_iii R.rot (0 + (τq : ℝ) • w + (1 : ℝ) • d) _ _ hdet' R.a R.a ha ha gw gd hwd'
        (by rw [htI]; norm_num))
    have htI' : (((tTauI R.rot.a R.rot.b R.rot.c R.a R.a : ℚ)) : ℝ) = 2 := by rw [htI]; norm_num
    rw [htI'] at key
    unfold ChartRSD
    rw [← sub_image 0 w d hdet (τq : ℝ) hτ0' hτ1' hdet']
    exact key
  -- (4) assembly
  have cT : ChartRSD R 0 w d hdet ((trapSet (τq : ℝ) ∪ SA (τq : ℝ)) ∪ SB (τq : ℝ)) :=
    chart_union (chart_union cF cA (disj_FA hτ0' hτ1')) cB
      (disjoint_interior_union (isClosed_trapSet _) (disj_FB hτ0' hτ1') (disj_AB hτ0' hτ1'))
  have key : RatSimDiss R.Δ (chartEquiv 0 w d hdet '' ST (τq : ℝ)) := by
    have := cT
    unfold ChartRSD at this
    rw [cover_eq hτ0' hτ1'] at this
    exact this
  unfold ChartRSD
  exact key

set_option maxHeartbeats 2000000 in
/-- **Laczkovich Theorem 2.5, first triple `(α, α+β, α+2β)`** (Fig. 6).  `Δ` is a rational triangle (sides `a, b, c`
opposite `α, β, γ`) with `γ = 2π/3`, i.e. `c² = a² + ab + b²` (so `α + β = π/3`; the paper's hypothesis "`√3 sin α`
and `cos α` rational" is exactly the existence of such a rational `Δ`).  Then the triangle `T = D E B` with angle `α`
at `D = T₀`, `π/3 = α + β` at `E = T₁` (and so `α + 2β` at `B`) is a union of finitely many congruent triangles,
each similar to `Δ` (a `CongruentRegionDissection` of `T` with model `scaleTri (1/q) Δ`). -/
theorem thm25_first (R : RTri) (hγ : R.a ^ 2 + R.a * R.b + R.b ^ 2 = R.c ^ 2) :
    ∃ (T : Tri) (q : ℕ) (hq : 0 < q) (M : ℕ)
      (C : Erdos634.RegionDissection.CongruentRegionDissection M),
      C.region = T.carrier ∧
      C.model = scaleTri (1 / (q : ℝ)) (one_div_pos.mpr (Nat.cast_pos.mpr hq)).ne' R.Δ ∧
      cornerAngle (T.pts 1) (T.pts 0) (T.pts 2)
        = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) ∧
      cornerAngle (T.pts 2) (T.pts 1) (T.pts 0) = Real.pi / 3 := by
  have ha := R.pa
  have hb := R.pb
  have hc := R.pc
  obtain ⟨W, hWdef⟩ : ∃ W : ℚ, W = R.a + 2 * R.b := ⟨_, rfl⟩
  have hW : 0 < W := by rw [hWdef]; positivity
  obtain ⟨τq, hτdef⟩ : ∃ τq : ℚ, τq = R.b / W := ⟨_, rfl⟩
  have hτW : τq * W = R.b := by rw [hτdef]; field_simp
  have hτ0 : 0 < τq := by rw [hτdef]; positivity
  have hτ1 : τq < 1 / 2 := by
    rw [hτdef, div_lt_div_iff₀ hW (by norm_num), hWdef]; linarith
  have hρW : (1 - τq) * W = R.a + R.b := by rw [sub_mul, one_mul, hτW, hWdef]; ring
  have Iw : (1 - τq) ^ 2 * W ^ 2 - (1 - τq) * W ^ 2 + R.c ^ 2 = R.a ^ 2 := by
    have e : (1 - τq) ^ 2 * W ^ 2 - (1 - τq) * W ^ 2 + R.c ^ 2
        = ((1 - τq) * W) ^ 2 - ((1 - τq) * W) * W + R.c ^ 2 := by ring
    rw [e, hρW, hWdef]; nlinarith [hγ]
  have Id : τq ^ 2 * W ^ 2 - τq * W ^ 2 + R.c ^ 2 = R.a ^ 2 := by
    have e : τq ^ 2 * W ^ 2 - τq * W ^ 2 + R.c ^ 2 = (τq * W) ^ 2 - (τq * W) * W + R.c ^ 2 := by ring
    rw [e, hτW, hWdef]; nlinarith [hγ]
  have Iwd : -(τq * (1 - τq)) * W ^ 2 + W ^ 2 / 2 - R.c ^ 2 = -(R.a ^ 2 / 2) := by
    have e : -(τq * (1 - τq)) * W ^ 2 + W ^ 2 / 2 - R.c ^ 2
        = -((τq * W) * ((1 - τq) * W)) + W ^ 2 / 2 - R.c ^ 2 := by ring
    rw [e, hτW, hρW, hWdef]; nlinarith [hγ]
  have hcos2 : (W / (2 * R.c)) ^ 2 < 1 := by
    rw [div_pow, div_lt_one (by positivity), hWdef]; nlinarith [hγ, sq_pos_of_pos ha]
  obtain ⟨w, d, hw, hd, hwd0, hdet⟩ := exists_gram_chart (W : ℝ) (R.c : ℝ) ((W / (2 * R.c) : ℚ) : ℝ)
    (by exact_mod_cast hW) (by exact_mod_cast hc) (by exact_mod_cast hcos2)
  have hwd : inner ℝ w d = (W : ℝ) ^ 2 / 2 := by
    rw [hwd0]; push_cast
    have : (R.c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
    field_simp
  have hτ0' : (0 : ℝ) < τq := by exact_mod_cast hτ0
  have hτ1' : (τq : ℝ) < 1 / 2 := by
    have h := (Rat.cast_lt (K := ℝ)).2 hτ1; push_cast at h; exact h
  -- (1) the trapezoid FDAC, Lemma 2.2 (ii)
  have hcosq : R.sw01.cos1 = W / (2 * R.c) := cos_sw01 R hγ W hWdef
  have hwd1 : inner ℝ w d = (W : ℝ) * (R.c : ℝ) * (R.sw01.cos1 : ℝ) := by
    rw [hcosq, hwd]; push_cast
    have : (R.c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
    field_simp
  have hτq : τq = tTau R.sw01.a R.sw01.b R.sw01.c W R.c := tau_sw01 R hγ W τq hWdef hτdef
  have cF : ChartRSD R 0 w d hdet (trapSet (τq : ℝ)) :=
    RatSimDiss.relabel (Δ := R.Δ) (Equiv.swap 0 1)
      (trap_ii R.sw01 0 w d hdet W R.c hW hc hw hd hwd1 τq hτq hτ0)
  -- (2) the tile ABC
  have hγR : (R.a : ℝ) ^ 2 + R.a * R.b + R.b ^ 2 = (R.c : ℝ) ^ 2 := by exact_mod_cast hγ
  have hWr : (W : ℝ) = R.a + 2 * R.b := by exact_mod_cast hWdef
  have hτWr : (τq : ℝ) * W = R.b := by exact_mod_cast hτW
  have hρWr : (1 - (τq : ℝ)) * W = R.a + R.b := by exact_mod_cast hρW
  have Iwr : (1 - (τq : ℝ)) ^ 2 * (W : ℝ) ^ 2 - (1 - (τq : ℝ)) * (W : ℝ) ^ 2 + (R.c : ℝ) ^ 2
      = (R.a : ℝ) ^ 2 := by exact_mod_cast Iw
  have Idr : (τq : ℝ) ^ 2 * (W : ℝ) ^ 2 - (τq : ℝ) * (W : ℝ) ^ 2 + (R.c : ℝ) ^ 2 = (R.a : ℝ) ^ 2 := by
    exact_mod_cast Id
  have Iwdr : -((τq : ℝ) * (1 - (τq : ℝ))) * (W : ℝ) ^ 2 + (W : ℝ) ^ 2 / 2 - (R.c : ℝ) ^ 2
      = -((R.a : ℝ) ^ 2 / 2) := by exact_mod_cast Iwd
  have cA : ChartRSD R 0 w d hdet (SA (τq : ℝ)) := by
    rw [← triAB_carrier hτ0' hτ1']
    refine chart_single (R := R) (A := 0) (w := w) (d := d) (h := hdet) _ ?_
    refine chart_tile R 0 w d hdet W R.c hw hd ((W : ℝ) ^ 2 / 2) hwd 0 1 0 2 (τq : ℝ) 1
      (by simp only [det3]; nlinarith) 1 1 one_pos ?_ ?_ ?_
    · simp only [Equiv.Perm.coe_one, id_eq, Rat.cast_one, one_pow, one_mul]
      rw [R.hc]; ring
    · simp only [Equiv.Perm.coe_one, id_eq, Rat.cast_one, one_pow, one_mul]
      rw [R.ha]; linear_combination Idr
    · simp only [Equiv.Perm.coe_one, id_eq, Rat.cast_one, one_pow, one_mul]
      rw [R.hb]; linear_combination ((τq : ℝ) * W + R.b) * hτWr
  -- (3) the isosceles trapezoid BEFC, Lemma 2.2 (iii), in a sub-chart
  have hdet' : ((1 - (τq : ℝ)) • w + (-1 : ℝ) • d) 0 * ((-(τq : ℝ)) • w + (1 : ℝ) • d) 1
      - ((1 - (τq : ℝ)) • w + (-1 : ℝ) • d) 1 * ((-(τq : ℝ)) • w + (1 : ℝ) • d) 0 ≠ 0 := by
    rw [det_comb]
    exact mul_ne_zero (by intro h; linarith) hdet
  have gw : inner ℝ ((1 - (τq : ℝ)) • w + (-1 : ℝ) • d) ((1 - (τq : ℝ)) • w + (-1 : ℝ) • d)
      = ((R.a : ℚ) : ℝ) ^ 2 := by
    rw [gram2, hw, hd, hwd]; linear_combination Iwr
  have gd : inner ℝ ((-(τq : ℝ)) • w + (1 : ℝ) • d) ((-(τq : ℝ)) • w + (1 : ℝ) • d)
      = ((R.a : ℚ) : ℝ) ^ 2 := by
    rw [gram2, hw, hd, hwd]; linear_combination Idr
  have hcosr : R.rot.cos1 = -1 / 2 := cos_rot R hγ
  have hwd' : inner ℝ ((1 - (τq : ℝ)) • w + (-1 : ℝ) • d) ((-(τq : ℝ)) • w + (1 : ℝ) • d)
      = ((R.a : ℚ) : ℝ) * ((R.a : ℚ) : ℝ) * (R.rot.cos1 : ℝ) := by
    rw [gram2, hw, hd, hwd, hcosr]; push_cast
    linear_combination Iwdr
  have htI : tTauI R.rot.a R.rot.b R.rot.c R.a R.a = 2 := tauI_rot R hγ
  have cB : ChartRSD R 0 w d hdet (SB (τq : ℝ)) := by
    have key := RatSimDiss.relabel (Δ := R.Δ) (finRotate 3)
      (trap_iii R.rot (0 + (τq : ℝ) • w + (1 : ℝ) • d) _ _ hdet' R.a R.a ha ha gw gd hwd'
        (by rw [htI]; norm_num))
    have htI' : (((tTauI R.rot.a R.rot.b R.rot.c R.a R.a : ℚ)) : ℝ) = 2 := by rw [htI]; norm_num
    rw [htI'] at key
    unfold ChartRSD
    rw [← sub_image 0 w d hdet (τq : ℝ) hτ0' hτ1' hdet']
    exact key
  -- (4) assembly
  have cT : ChartRSD R 0 w d hdet ((trapSet (τq : ℝ) ∪ SA (τq : ℝ)) ∪ SB (τq : ℝ)) :=
    chart_union (chart_union cF cA (disj_FA hτ0' hτ1')) cB
      (disjoint_interior_union (isClosed_trapSet _) (disj_FB hτ0' hτ1') (disj_AB hτ0' hτ1'))
  have key : RatSimDiss R.Δ (chartEquiv 0 w d hdet '' ST (τq : ℝ)) := by
    have := cT
    unfold ChartRSD at this
    rw [cover_eq hτ0' hτ1'] at this
    exact this
  obtain ⟨q, hq, M, C, hC1, hC2⟩ := RatSimDiss.toCongruent R.rational key
  have hwn : ‖w‖ = (W : ℝ) := by
    refine eq_of_sq_eq' (norm_nonneg _) (by exact_mod_cast hW.le) ?_
    rw [← real_inner_self_eq_norm_sq]; exact hw
  have hdn : ‖d‖ = (R.c : ℝ) := by
    refine eq_of_sq_eq' (norm_nonneg _) (by exact_mod_cast hc.le) ?_
    rw [← real_inner_self_eq_norm_sq]; exact hd
  have hρpos : (0 : ℝ) < 1 - (τq : ℝ) := by linarith
  refine ⟨Erdos634.DissectionMap.mapTri (chartEquiv 0 w d hdet) (triTT hτ0' hτ1'), q, hq, M, C,
    ?_, hC2, ?_, ?_⟩
  · rw [hC1, Erdos634.DissectionMap.mapTri_carrier, triTT_carrier]
  · -- the angle at D
    have e1 : chartEquiv 0 w d hdet (mkPt (2 * (1 - (τq : ℝ))) 0) - chartEquiv 0 w d hdet (mkPt 0 0)
        = (2 * (1 - (τq : ℝ))) • w := by
      rw [chartEquiv_apply, chartEquiv_apply]; simp only [mkPt_zero, mkPt_one]; module
    have e2 : chartEquiv 0 w d hdet (mkPt 0 2) - chartEquiv 0 w d hdet (mkPt 0 0) = (2 : ℝ) • d := by
      rw [chartEquiv_apply, chartEquiv_apply]; simp only [mkPt_zero, mkPt_one]; module
    have h1 : ‖R.Δ.pts 1 - R.Δ.pts 0‖ = R.c := by rw [← dist_eq_norm, dist_comm]; exact R.hc
    have h2 : ‖R.Δ.pts 2 - R.Δ.pts 0‖ = R.b := by rw [← dist_eq_norm]; exact R.hb
    show EuclideanGeometry.angle (chartEquiv 0 w d hdet (mkPt (2 * (1 - (τq : ℝ))) 0))
        (chartEquiv 0 w d hdet (mkPt 0 0)) (chartEquiv 0 w d hdet (mkPt 0 2))
      = EuclideanGeometry.angle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2)
    unfold EuclideanGeometry.angle
    simp only [vsub_eq_sub]
    rw [e1, e2, InnerProductGeometry.angle_smul_left_of_pos _ _ (by linarith),
      InnerProductGeometry.angle_smul_right_of_pos _ _ two_pos]
    unfold InnerProductGeometry.angle
    rw [R.inner_uv, h1, h2, hwd, hwn, hdn]
    congr 1
    have hW0 : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
    have hc0 : (R.c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
    have hb0 : (R.b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
    field_simp
    rw [hWr]
    nlinarith [hγR]
  · -- the angle at E
    have e1 : chartEquiv 0 w d hdet (mkPt 0 2) - chartEquiv 0 w d hdet (mkPt (2 * (1 - (τq : ℝ))) 0)
        = (-(2 * (1 - (τq : ℝ)))) • w + (2 : ℝ) • d := by
      rw [chartEquiv_apply, chartEquiv_apply]; simp only [mkPt_zero, mkPt_one]; module
    have e2 : chartEquiv 0 w d hdet (mkPt 0 0) - chartEquiv 0 w d hdet (mkPt (2 * (1 - (τq : ℝ))) 0)
        = (-(2 * (1 - (τq : ℝ)))) • w + (0 : ℝ) • d := by
      rw [chartEquiv_apply, chartEquiv_apply]; simp only [mkPt_zero, mkPt_one]; module
    show EuclideanGeometry.angle (chartEquiv 0 w d hdet (mkPt 0 2))
        (chartEquiv 0 w d hdet (mkPt (2 * (1 - (τq : ℝ))) 0)) (chartEquiv 0 w d hdet (mkPt 0 0))
      = Real.pi / 3
    unfold EuclideanGeometry.angle
    simp only [vsub_eq_sub]
    rw [e1, e2]
    have nu : ‖(-(2 * (1 - (τq : ℝ)))) • w + (2 : ℝ) • d‖ = 2 * R.a := by
      refine norm_comb w d _ _ _ (by positivity) ?_
      rw [gram2, hw, hd, hwd]; linear_combination 4 * Iwr
    have nv : ‖(-(2 * (1 - (τq : ℝ)))) • w + (0 : ℝ) • d‖ = 2 * (R.a + R.b) := by
      refine norm_comb w d _ _ _ (by positivity) ?_
      rw [gram2, hw, hd, hwd]
      have e : (-(2 * (1 - (τq : ℝ)))) * (-(2 * (1 - (τq : ℝ)))) * (W : ℝ) ^ 2
          + ((-(2 * (1 - (τq : ℝ)))) * 0 + 0 * (-(2 * (1 - (τq : ℝ))))) * ((W : ℝ) ^ 2 / 2)
          + 0 * 0 * (R.c : ℝ) ^ 2 = 4 * ((1 - (τq : ℝ)) * W) ^ 2 := by ring
      rw [e, hρWr]; ring
    have iuv : inner ℝ ((-(2 * (1 - (τq : ℝ)))) • w + (2 : ℝ) • d)
        ((-(2 * (1 - (τq : ℝ)))) • w + (0 : ℝ) • d) = 2 * R.a * (R.a + R.b) := by
      rw [gram2, hw, hd, hwd]
      have e : (-(2 * (1 - (τq : ℝ)))) * (-(2 * (1 - (τq : ℝ)))) * (W : ℝ) ^ 2
          + ((-(2 * (1 - (τq : ℝ)))) * 0 + 2 * (-(2 * (1 - (τq : ℝ))))) * ((W : ℝ) ^ 2 / 2)
          + 2 * 0 * (R.c : ℝ) ^ 2
          = 4 * ((1 - (τq : ℝ)) * W) ^ 2 - 2 * ((1 - (τq : ℝ)) * W) * W := by ring
      rw [e, hρWr, hWr]; ring
    unfold InnerProductGeometry.angle
    rw [nu, nv, iuv]
    have hfrac : 2 * (R.a : ℝ) * (R.a + R.b) / (2 * R.a * (2 * (R.a + R.b))) = 1 / 2 := by
      have : (R.a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
      have : (R.a : ℝ) + R.b ≠ 0 := by positivity
      field_simp
    rw [hfrac, ← Real.cos_pi_div_three, Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])]

end Erdos634.LaczL25
