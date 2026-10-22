import Erdos634.Draft.LaczFormalL22Strips

/-!
# Laczkovich Lemma 2.2 (iii) (chart form): the isosceles trapezoid with base angles `β`

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Lemma 2.2 (iii), Fig. 2), Beeson, Beeson-Zhang, Zhang.

Chart `(A, w, d)` with Gram data `|w| = W`, `|d| = D`, `⟨w, d⟩ = W D cos β`.  The isosceles trapezoid `ABCD`
(`|BC| = |AD| = D`, angle `β` at `A` and `B`, `AB = W`, top side `DC = τ W`) is `trapSet τ` with
`τ = 1 - D (a² + c² - b²)/(a c W) = 1 - 2 D cos β / W` (`tTauI`).  First case (`AB/BC > sin α/ sin γ`, i.e.
`D a < W c`): cut off the triangle `EBC` (angles `β, γ, α` at `B, E, C`; `E = (ε, 0)`, `ε = 1 - D a/(c W)`); the
rest `AECD` is a trapezoid with angles `β, α+β`, i.e. Lemma 2.2 (ii) (`trap_ii`).  Otherwise cut the legs into
equal parts (`trap_strips`).
-/

namespace Erdos634.LaczL22

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL21 Erdos634.Realizable

def tEps (a c W Dd : ℚ) : ℚ := 1 - Dd * a / (c * W)
def tTauI (a b c W Dd : ℚ) : ℚ := 1 - Dd * (a ^ 2 + c ^ 2 - b ^ 2) / (a * c * W)

theorem trap_alg3 (a b c W Dd : ℚ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hW : 0 < W) (hD : 0 < Dd)
    (hε : c * W - Dd * a ≠ 0) :
    (1 - tEps a c W Dd) ^ 2 * W ^ 2 = (Dd / c) ^ 2 * a ^ 2 ∧
    (1 - tTauI a b c W Dd) ^ 2 * W ^ 2 + 2 * (tTauI a b c W Dd - 1) * tG a b c W Dd + Dd ^ 2
      = (Dd / c) ^ 2 * c ^ 2 ∧
    (tTauI a b c W Dd - tEps a c W Dd) ^ 2 * W ^ 2
      + 2 * (tTauI a b c W Dd - tEps a c W Dd) * tG a b c W Dd + Dd ^ 2 = (Dd / c) ^ 2 * b ^ 2 ∧
    tTau a b c (tEps a c W Dd * W) Dd * tEps a c W Dd = tTauI a b c W Dd := by
  have ha' := ha.ne'; have hb' := hb.ne'; have hc' := hc.ne'; have hW' := hW.ne'; have hD' := hD.ne'
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [tEps]; field_simp; ring
  · simp only [tTauI, tG]; field_simp; ring
  · simp only [tTauI, tEps, tG]; field_simp; ring
  · have e : tEps a c W Dd = (c * W - Dd * a) / (c * W) := by simp only [tEps]; field_simp
    rw [e]
    simp only [tTau, tTauI]
    field_simp
    ring

theorem tTauI_scale (a b c : ℚ) (ha : 0 < a) (hc : 0 < c) (W Dd : ℚ) (hW : 0 < W) (n : ℕ) (L : ℚ)
    (hn : 0 < n) (hL : 0 < L) :
    tTauI a b c (L * W) (Dd / n) - 1 = (tTauI a b c W Dd - 1) / (n * L) := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [tTauI]
  field_simp
  ring

/-! ## Geometry -/

/-- `AECD` of the paper in the chart: `0 ≤ t ≤ 1`, `0 ≤ s ≤ ε + (τ - ε) t`. -/
def aecSet (ε τ : ℝ) : Set Plane :=
  {z | 0 ≤ z 1 ∧ z 1 ≤ 1 ∧ 0 ≤ z 0 ∧ z 0 ≤ ε + (τ - ε) * z 1}

/-- `E B C` of the paper: chart vertices `(ε,0), (1,0), (τ,1)`. -/
noncomputable def triEBC3 (ε τ : ℝ) (hε : ε < 1) : Tri :=
  mkTri ε 0 1 0 τ 1 (by simp only [det3]; nlinarith)

theorem triEBC3_pts (ε τ : ℝ) (hε : ε < 1) :
    (triEBC3 ε τ hε).pts 0 = mkPt ε 0 ∧ (triEBC3 ε τ hε).pts 1 = mkPt 1 0 ∧
      (triEBC3 ε τ hε).pts 2 = mkPt τ 1 :=
  ⟨rfl, rfl, rfl⟩

private theorem htri3' : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide

theorem iso_cover (ε τ : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hτ : 0 ≤ τ) :
    trapSet τ = aecSet ε τ ∪ (triEBC3 ε τ hε1).carrier := by
  have hF' : 0 < 1 - ε := by linarith
  ext z
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    by_cases hh : z 0 ≤ ε + (τ - ε) * z 1
    · left; exact ⟨h1, h2, h3, hh⟩
    · push Not at hh
      right
      refine Erdos634.CertGeom.mem_carrier_of_combo _ z
        ![1 - (z 0 - ε - (τ - ε) * z 1) / (1 - ε) - z 1, (z 0 - ε - (τ - ε) * z 1) / (1 - ε), z 1]
        ?_ ?_ ?_
      · show (1 - (z 0 - ε - (τ - ε) * z 1) / (1 - ε) - z 1) + (z 0 - ε - (τ - ε) * z 1) / (1 - ε)
          + z 1 = 1
        ring
      · intro k
        rcases htri3' k with rfl | rfl | rfl
        · show 0 ≤ 1 - (z 0 - ε - (τ - ε) * z 1) / (1 - ε) - z 1
          have : (z 0 - ε - (τ - ε) * z 1) / (1 - ε) ≤ 1 - z 1 := by
            rw [div_le_iff₀ hF']; nlinarith
          linarith
        · show 0 ≤ (z 0 - ε - (τ - ε) * z 1) / (1 - ε)
          exact div_nonneg (by linarith) hF'.le
        · exact h1
      · obtain ⟨p0, p1, p2⟩ := triEBC3_pts ε τ hε1
        show z = _ • (triEBC3 ε τ hε1).pts 0 + _ • (triEBC3 ε τ hε1).pts 1 + _ • (triEBC3 ε τ hε1).pts 2
        rw [p0, p1, p2]
        have hF'' : (1 - ε) ≠ 0 := hF'.ne'
        ext i
        fin_cases i <;> simp [mkPt] <;> field_simp <;> ring
  · intro hz
    rcases hz with hz | hz
    · obtain ⟨h1, h2, h3, h4⟩ := hz
      refine ⟨h1, h2, h3, ?_⟩
      nlinarith
    · refine carrier_subset_trap ?_ hz
      intro k
      obtain ⟨p0, p1, p2⟩ := triEBC3_pts ε τ hε1
      rcases htri3' k with rfl | rfl | rfl
      · rw [p0]; simp [trapSet]; first | (constructor <;> nlinarith) | nlinarith
      · rw [p1]; simp [trapSet]
      · rw [p2]; simp [trapSet]; linarith

theorem iso_disj (ε τ : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    Disjoint (interior (aecSet ε τ)) (interior (triEBC3 ε τ hε1).carrier) := by
  obtain ⟨p0, p1, p2⟩ := triEBC3_pts ε τ hε1
  refine disjoint_interior_of_sep (coordFun 1 (-(τ - ε)) (-ε))
    (coordFun_linear_ne_zero _ (Or.inl one_ne_zero)) 0 ?_ ?_
  · intro z hz
    obtain ⟨h1, h2, h3, h4⟩ := hz
    simp only [coordFun_apply]; nlinarith
  · intro z hz
    refine ge_of_forall_pts_ge (coordFun 1 (-(τ - ε)) (-ε)) ?_ z hz
    intro k
    rcases htri3' k with rfl | rfl | rfl
    · rw [p0]; simp
    · rw [p1]; simp; linarith
    · rw [p2]; simp


theorem aec_image (A w d : Plane) (h : w 0 * d 1 - w 1 * d 0 ≠ 0) (ε τ τ' : ℝ) (hε : 0 < ε)
    (hτ : τ' * ε = τ)
    (hdet : ((ε : ℝ) • w) 0 * d 1 - ((ε : ℝ) • w) 1 * d 0 ≠ 0) :
    chartEquiv A w d h '' aecSet ε τ = chartEquiv A ((ε : ℝ) • w) d hdet '' trapSet τ' := by
  have hε' : ε ≠ 0 := hε.ne'
  ext x
  constructor
  · rintro ⟨z, ⟨h1, h2, h3, h4⟩, rfl⟩
    refine ⟨mkPt (z 0 / ε) (z 1), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simpa using h1
    · simpa using h2
    · simp only [mkPt_zero]; positivity
    · simp only [mkPt_zero, mkPt_one]
      rw [div_le_iff₀ hε]
      have e : (1 + (τ' - 1) * z 1) * ε = ε + (τ - ε) * z 1 := by rw [← hτ]; ring
      rw [e]; exact h4
    · rw [chartEquiv_apply, chartEquiv_apply]
      simp only [mkPt_zero, mkPt_one]
      have e : (z 0 / ε) • ((ε : ℝ) • w) = z 0 • w := by
        rw [smul_smul, div_mul_cancel₀ _ hε']
      rw [e]
  · rintro ⟨z, ⟨h1, h2, h3, h4⟩, rfl⟩
    refine ⟨mkPt (ε * z 0) (z 1), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simpa using h1
    · simpa using h2
    · simp only [mkPt_zero]; positivity
    · simp only [mkPt_zero, mkPt_one]
      have h5 : ε * z 0 ≤ ε * (1 + (τ' - 1) * z 1) := mul_le_mul_of_nonneg_left h4 hε.le
      have e : ε * (1 + (τ' - 1) * z 1) = ε + (τ - ε) * z 1 := by rw [← hτ]; ring
      linarith
    · rw [chartEquiv_apply, chartEquiv_apply]
      simp only [mkPt_zero, mkPt_one]
      have e : (ε * z 0) • w = z 0 • ((ε : ℝ) • w) := by rw [smul_smul, mul_comm]
      rw [e]

/-- **Lemma 2.2 (iii), first case** (chart form). -/
theorem iso_case1 (R : RTri) (A w d : Plane) (h : w 0 * d 1 - w 1 * d 0 ≠ 0) (W Dd : ℚ)
    (hW : 0 < W) (hD : 0 < Dd) (hw : inner ℝ w w = (W : ℝ) ^ 2) (hd : inner ℝ d d = (Dd : ℝ) ^ 2)
    (hwd : inner ℝ w d = (W : ℝ) * Dd * (R.cos1 : ℝ)) (hcase : Dd * R.a < W * R.c)
    (hτpos : 0 < tTauI R.a R.b R.c W Dd) :
    ChartRSD R A w d h (trapSet ((tTauI R.a R.b R.c W Dd : ℚ) : ℝ)) := by
  have ha := R.pa
  have hb := R.pb
  have hc := R.pc
  have hεne : R.c * W - Dd * R.a ≠ 0 := by nlinarith
  obtain ⟨i1, i2, i3, i4⟩ := trap_alg3 R.a R.b R.c W Dd ha hb hc hW hD hεne
  set ε : ℚ := tEps R.a R.c W Dd with hεdef
  set τ : ℚ := tTauI R.a R.b R.c W Dd with hτdef
  set k : ℚ := Dd / R.c with hkdef
  set g : ℚ := tG R.a R.b R.c W Dd with hgdef
  have hε1 : ε < 1 := by
    have : 0 < Dd * R.a / (R.c * W) := by positivity
    rw [hεdef, tEps]; linarith
  have hε0 : 0 < ε := by
    have : Dd * R.a / (R.c * W) < 1 := (div_lt_one (by positivity)).mpr (by nlinarith)
    rw [hεdef, tEps]; linarith
  have hk : 0 < k := by rw [hkdef]; positivity
  have hgR : (g : ℝ) = (W : ℝ) * Dd * (R.cos1 : ℝ) := by
    rw [hgdef, tG, RTri.cos1]; push_cast; ring
  have hwd' : inner ℝ w d = (g : ℝ) := by rw [hgR]; exact hwd
  have hε1R : (ε : ℝ) < 1 := by exact_mod_cast hε1
  have hε0R : (0 : ℝ) < ε := by exact_mod_cast hε0
  have hτ0R : (0 : ℝ) ≤ τ := by exact_mod_cast hτpos.le
  rw [iso_cover (ε : ℝ) (τ : ℝ) hε0R hε1R hτ0R]
  refine chart_union ?_ ?_ (iso_disj (ε : ℝ) (τ : ℝ) hε0R hε1R)
  · -- the trapezoid AECD, angles β and α+β: Lemma 2.2 (ii)
    have hεW : 0 < ε * W := mul_pos hε0 hW
    have hdet' : ((ε : ℝ) • w) 0 * d 1 - ((ε : ℝ) • w) 1 * d 0 ≠ 0 := by
      have e : ((ε : ℝ) • w) 0 * d 1 - ((ε : ℝ) • w) 1 * d 0 = (ε : ℝ) * (w 0 * d 1 - w 1 * d 0) := by
        simp only [PiLp.smul_apply, smul_eq_mul]; ring
      rw [e]; exact mul_ne_zero hε0R.ne' h
    have hw' : inner ℝ ((ε : ℝ) • w) ((ε : ℝ) • w) = ((ε * W : ℚ) : ℝ) ^ 2 := by
      simp only [real_inner_smul_left, real_inner_smul_right, hw]; push_cast; ring
    have hwd'' : inner ℝ ((ε : ℝ) • w) d = ((ε * W : ℚ) : ℝ) * Dd * (R.cos1 : ℝ) := by
      simp only [real_inner_smul_left, real_inner_smul_right, hwd]; push_cast; ring
    set τ' : ℚ := tTau R.a R.b R.c (ε * W) Dd with hτ'def
    have hττ : τ' * ε = τ := i4
    have hτ'pos : 0 < τ' := by
      have : 0 < τ' * ε := by rw [hττ]; exact hτpos
      exact pos_of_mul_pos_left this hε0.le
    have key := trap_ii R A ((ε : ℝ) • w) d hdet' (ε * W) Dd hεW hD hw' hd hwd'' τ' hτ'def hτ'pos
    unfold ChartRSD at key ⊢
    rw [aec_image A w d h (ε : ℝ) (τ : ℝ) (τ' : ℝ) hε0R (by exact_mod_cast hττ) hdet']
    exact key
  · -- triangle EBC
    refine chart_single _ ?_
    unfold triEBC3
    have s0 : (Equiv.swap (0 : Fin 3) 2) 0 = 2 := by decide
    have s1 : (Equiv.swap (0 : Fin 3) 2) 1 = 1 := by decide
    have s2 : (Equiv.swap (0 : Fin 3) 2) 2 = 0 := by decide
    refine chart_tile R A w d h W Dd hw hd g hwd' (ε : ℝ) 0 1 0 (τ : ℝ) 1 _ (Equiv.swap 0 2) k hk ?_ ?_ ?_
    · rw [s0, s1, dist_comm (R.Δ.pts 2) (R.Δ.pts 1), R.ha]
      have := congrArg (Rat.cast : ℚ → ℝ) i1; push_cast at this; linear_combination this
    · rw [s1, s2, dist_comm (R.Δ.pts 1) (R.Δ.pts 0), R.hc]
      have := congrArg (Rat.cast : ℚ → ℝ) i2; push_cast at this; linear_combination this
    · rw [s2, s0, dist_comm (R.Δ.pts 0) (R.Δ.pts 2), R.hb]
      have := congrArg (Rat.cast : ℚ → ℝ) i3; push_cast at this; linear_combination this

/-- **Lemma 2.2 (iii)** (chart form): the isosceles trapezoid with base angles `β` (`τ = 1 - 2 D cos β / W`),
`τ > 0`, is dissected into rational triangles similar to `Δ`. -/
theorem trap_iii (R : RTri) (A w d : Plane) (h : w 0 * d 1 - w 1 * d 0 ≠ 0) (W Dd : ℚ)
    (hW : 0 < W) (hD : 0 < Dd) (hw : inner ℝ w w = (W : ℝ) ^ 2) (hd : inner ℝ d d = (Dd : ℝ) ^ 2)
    (hwd : inner ℝ w d = (W : ℝ) * Dd * (R.cos1 : ℝ)) (hτpos : 0 < tTauI R.a R.b R.c W Dd) :
    ChartRSD R A w d h (trapSet ((tTauI R.a R.b R.c W Dd : ℚ) : ℝ)) := by
  have ha := R.pa
  have hc := R.pc
  refine trap_strips R A w d h W Dd hW hD hw hd R.cos1 (R.a / R.c) (by positivity) hwd
    (tTauI R.a R.b R.c)
    (fun W Dd n L hn hL hW hD => tTauI_scale R.a R.b R.c ha hc W Dd hW n L hn hL)
    ?_ _ rfl hτpos
  intro A' w' d' h' W' Dd' hW' hD' hw' hd' hwd' hcase' hτ'
  refine iso_case1 R A' w' d' h' W' Dd' hW' hD' hw' hd' hwd' ?_ hτ'
  have h1 := hcase'
  rw [← mul_div_assoc, div_lt_iff₀ hc] at h1
  exact h1

end Erdos634.LaczL22
