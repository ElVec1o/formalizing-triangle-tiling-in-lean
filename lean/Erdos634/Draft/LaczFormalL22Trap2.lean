import Erdos634.Draft.LaczFormalL22Trap1

/-!
# Laczkovich Lemma 2.2 (ii) (chart form): every trapezoid with angles `β, α+β` is dissected

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Lemma 2.2 (ii)), Beeson, Beeson-Zhang, Zhang.

Second case of the paper (`DC/BC ≤ sin β / sin α`): cut the legs into `n` equal parts; the `n` strips are trapezoids of
the same angles whose top side is long enough for the first case (`trap_case1`).  Here the choice of `n` makes
the first case apply to every strip, so no case split is needed: `trap_ii` covers every `τ > 0`.
A strip is the chart image of a standard trapezoid in the re-chart `(A + (i/n) d, L_i w, d/n)`.
-/

namespace Erdos634.LaczL22

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL21 Erdos634.Realizable

/-- The `i`-th horizontal strip (of `n`) of the chart trapezoid. -/
def stripSet (τ : ℝ) (n i : ℕ) : Set Plane :=
  {z | (i : ℝ) / n ≤ z 1 ∧ z 1 ≤ ((i : ℝ) + 1) / n ∧ 0 ≤ z 0 ∧ z 0 ≤ 1 + (τ - 1) * z 1}

/-- The prefix trapezoid `0 ≤ t ≤ m/n`. -/
def prefSet (τ : ℝ) (n m : ℕ) : Set Plane :=
  {z | 0 ≤ z 1 ∧ z 1 ≤ (m : ℝ) / n ∧ 0 ≤ z 0 ∧ z 0 ≤ 1 + (τ - 1) * z 1}

theorem tTau_strip (a b c W Dd : ℚ) (ha : 0 < a) (hc : 0 < c) (hW : 0 < W) (n : ℕ) (hn : 0 < n)
    (L : ℚ) (hL : 0 < L) :
    tTau a b c (L * W) (Dd / n) - 1 = (tTau a b c W Dd - 1) / (n * L) := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [tTau]
  field_simp
  ring

theorem strip_image (R : RTri) (A w d : Plane) (h : w 0 * d 1 - w 1 * d 0 ≠ 0) (τq : ℚ)
    (n i : ℕ) (hn : 0 < n) (L : ℚ) (hL : 0 < L) (hLdef : L = 1 + (τq - 1) * i / n)
    (Dd W : ℚ) (hτ : τq = tTau R.a R.b R.c W Dd) (hW : 0 < W)
    (hdet : ((L : ℝ) • w) 0 * ((1 / (n : ℝ)) • d) 1 - ((L : ℝ) • w) 1 * ((1 / (n : ℝ)) • d) 0 ≠ 0) :
    chartEquiv A w d h '' stripSet (τq : ℝ) n i
      = chartEquiv (A + ((i : ℝ) / n) • d) ((L : ℝ) • w) ((1 / (n : ℝ)) • d) hdet ''
          trapSet ((tTau R.a R.b R.c (L * W) (Dd / n) : ℚ) : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hrel := tTau_strip R.a R.b R.c W Dd R.pa R.pc hW n hn L hL
  rw [← hτ] at hrel
  have hrelR : (((tTau R.a R.b R.c (L * W) (Dd / n) : ℚ) : ℝ) - 1) * ((n : ℝ) * L)
      = (τq : ℝ) - 1 := by
    have h1 : ((tTau R.a R.b R.c (L * W) (Dd / n) : ℚ) - 1) * ((n : ℚ) * L) = τq - 1 := by
      rw [hrel]; field_simp
    exact_mod_cast h1
  have hLR : (L : ℝ) = 1 + ((τq : ℝ) - 1) * i / n := by
    have : ((L : ℚ) : ℝ) = (((1 + (τq - 1) * i / n : ℚ)) : ℝ) := by rw [← hLdef]
    rw [this]; push_cast; ring
  set τi : ℝ := ((tTau R.a R.b R.c (L * W) (Dd / n) : ℚ) : ℝ) with hτi
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hvL : (τi - 1) * L = ((τq : ℝ) - 1) / n := by
    rw [eq_div_iff hn']
    nlinarith [hrelR]
  have hpt : ∀ (s t : ℝ), A + s • w + t • d
      = (A + ((i : ℝ) / n) • d) + (s / L) • ((L : ℝ) • w) + (n * t - i) • ((1 / (n : ℝ)) • d) := by
    intro s t
    have e1 : (s / L) * L = s := div_mul_cancel₀ _ hL'
    have e2 : ((n : ℝ) * t - i) * (1 / n) = t - i / n := by field_simp
    simp only [smul_smul, e1, e2]
    module
  have hpt' : ∀ (s t : ℝ), (A + ((i : ℝ) / n) • d) + s • ((L : ℝ) • w) + t • ((1 / (n : ℝ)) • d)
      = A + (L * s) • w + ((i : ℝ) / n + t / n) • d := by
    intro s t
    simp only [smul_smul]
    have e2 : t * (1 / (n : ℝ)) = t / n := by ring
    rw [e2]
    module
  ext x
  constructor
  · rintro ⟨z, ⟨h1, h2, h3, h4⟩, rfl⟩
    refine ⟨mkPt (z 0 / L) ((n : ℝ) * z 1 - i), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp only [mkPt_one]
      have := (div_le_iff₀ hnp).mp h1; linarith
    · simp only [mkPt_one]
      have := (le_div_iff₀ hnp).mp h2; linarith
    · simp only [mkPt_zero]
      positivity
    · simp only [mkPt_zero, mkPt_one]
      rw [div_le_iff₀ hLp]
      have e : (1 + (τi - 1) * ((n : ℝ) * z 1 - i)) * L = 1 + ((τq : ℝ) - 1) * z 1 := by
        have : (1 + (τi - 1) * ((n : ℝ) * z 1 - i)) * L = L + ((τi - 1) * L) * ((n : ℝ) * z 1 - i) := by ring
        rw [this, hvL, hLR]
        field_simp
        ring
      rw [e]; exact h4
    · rw [chartEquiv_apply, chartEquiv_apply, hpt (z 0) (z 1)]
      simp only [mkPt_zero, mkPt_one]
  · rintro ⟨z, ⟨h1, h2, h3, h4⟩, rfl⟩
    refine ⟨mkPt (L * z 0) ((i : ℝ) / n + z 1 / n), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp only [mkPt_one]
      have : 0 ≤ z 1 / n := by positivity
      linarith
    · simp only [mkPt_one]
      have : z 1 / n ≤ 1 / n := by gcongr
      have e : ((i : ℝ) + 1) / n = i / n + 1 / n := by ring
      rw [e]; linarith
    · simp only [mkPt_zero]
      positivity
    · simp only [mkPt_zero, mkPt_one]
      have h5 : L * z 0 ≤ L * (1 + (τi - 1) * z 1) := mul_le_mul_of_nonneg_left h4 hLp.le
      have e : L * (1 + (τi - 1) * z 1) = 1 + ((τq : ℝ) - 1) * ((i : ℝ) / n + z 1 / n) := by
        have : L * (1 + (τi - 1) * z 1) = L + ((τi - 1) * L) * z 1 := by ring
        rw [this, hvL, hLR]
        field_simp
        ring
      linarith
    · rw [chartEquiv_apply, chartEquiv_apply, hpt']
      simp only [mkPt_zero, mkPt_one]


theorem strip_chart (R : RTri) (A w d : Plane) (h : w 0 * d 1 - w 1 * d 0 ≠ 0) (W Dd : ℚ)
    (hW : 0 < W) (hD : 0 < Dd) (hw : inner ℝ w w = (W : ℝ) ^ 2) (hd : inner ℝ d d = (Dd : ℝ) ^ 2)
    (hwd : inner ℝ w d = (W : ℝ) * Dd * (R.cos1 : ℝ)) (τq : ℚ)
    (hτ : τq = tTau R.a R.b R.c W Dd) (n i : ℕ) (hn : 0 < n) (hi : i < n)
    (hcase : Dd * R.c < n * min 1 τq * W * R.a) :
    ChartRSD R A w d h (stripSet (τq : ℝ) n i) := by
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hx0 : (0 : ℚ) ≤ (i : ℚ) / n := by positivity
  have hx1 : (i : ℚ) / n ≤ 1 := by
    rw [div_le_one hn']; exact_mod_cast hi.le
  set L : ℚ := 1 + (τq - 1) * i / n with hLdef
  have hLx : L = 1 + (τq - 1) * ((i : ℚ) / n) := by rw [hLdef]; ring
  have hm1 : min 1 τq ≤ 1 := min_le_left _ _
  have hm2 : min 1 τq ≤ τq := min_le_right _ _
  have hLm : min 1 τq ≤ L := by
    rw [hLx]
    nlinarith [mul_nonneg hx0 (sub_nonneg.2 hm2), mul_nonneg (sub_nonneg.2 hx1) (sub_nonneg.2 hm1)]
  have hmpos : 0 < min 1 τq := lt_min one_pos (by
    -- τq > 0 is not assumed here; recover it from hcase
    by_contra hneg
    push_neg at hneg
    have : min 1 τq ≤ 0 := le_trans (min_le_right _ _) hneg
    have h1 : n * min 1 τq * W * R.a ≤ 0 := by
      have := R.pa
      have : n * min 1 τq ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hn'.le (by linarith)
      nlinarith [mul_pos hW R.pa]
    have : 0 < Dd * R.c := mul_pos hD R.pc
    linarith)
  have hL : 0 < L := lt_of_lt_of_le hmpos hLm
  have hdet : ((L : ℝ) • w) 0 * ((1 / (n : ℝ)) • d) 1 - ((L : ℝ) • w) 1 * ((1 / (n : ℝ)) • d) 0 ≠ 0 := by
    have e : ((L : ℝ) • w) 0 * ((1 / (n : ℝ)) • d) 1 - ((L : ℝ) • w) 1 * ((1 / (n : ℝ)) • d) 0
        = ((L : ℝ) * (1 / n)) * (w 0 * d 1 - w 1 * d 0) := by
      simp only [PiLp.smul_apply, smul_eq_mul]; ring
    rw [e]
    have : (0 : ℝ) < (L : ℝ) * (1 / n) := by
      have : (0 : ℝ) < L := by exact_mod_cast hL
      have : (0 : ℝ) < n := by exact_mod_cast hn
      positivity
    exact mul_ne_zero this.ne' h
  have hWi : 0 < L * W := mul_pos hL hW
  have hDi : 0 < Dd / n := by positivity
  have hw' : inner ℝ ((L : ℝ) • w) ((L : ℝ) • w) = ((L * W : ℚ) : ℝ) ^ 2 := by
    simp only [real_inner_smul_left, real_inner_smul_right, hw]; push_cast; ring
  have hd' : inner ℝ ((1 / (n : ℝ)) • d) ((1 / (n : ℝ)) • d) = ((Dd / n : ℚ) : ℝ) ^ 2 := by
    simp only [real_inner_smul_left, real_inner_smul_right, hd]; push_cast; ring
  have hwd' : inner ℝ ((L : ℝ) • w) ((1 / (n : ℝ)) • d)
      = ((L * W : ℚ) : ℝ) * ((Dd / n : ℚ) : ℝ) * (R.cos1 : ℝ) := by
    simp only [real_inner_smul_left, real_inner_smul_right, hwd]; push_cast; ring
  have hc1 : Dd / n * R.c < (L * W) * R.a := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hn']
    have : (n : ℚ) * min 1 τq * W * R.a ≤ n * L * W * R.a := by
      have := mul_pos hW R.pa
      have h1 : (n : ℚ) * min 1 τq ≤ n * L := mul_le_mul_of_nonneg_left hLm hn'.le
      nlinarith
    nlinarith
  have key := trap_case1 R (A + ((i : ℝ) / n) • d) ((L : ℝ) • w) ((1 / (n : ℝ)) • d) hdet (L * W) (Dd / n)
    hWi hDi hw' hd' hwd' hc1
  unfold ChartRSD
  rw [strip_image R A w d h τq n i hn L hL hLdef Dd W hτ hW hdet]
  exact key

theorem trap_ii (R : RTri) (A w d : Plane) (h : w 0 * d 1 - w 1 * d 0 ≠ 0) (W Dd : ℚ)
    (hW : 0 < W) (hD : 0 < Dd) (hw : inner ℝ w w = (W : ℝ) ^ 2) (hd : inner ℝ d d = (Dd : ℝ) ^ 2)
    (hwd : inner ℝ w d = (W : ℝ) * Dd * (R.cos1 : ℝ)) (τq : ℚ)
    (hτ : τq = tTau R.a R.b R.c W Dd) (hτpos : 0 < τq) :
    ChartRSD R A w d h (trapSet (τq : ℝ)) := by
  have hmpos : 0 < min 1 τq := lt_min one_pos hτpos
  have hden : 0 < min 1 τq * W * R.a := by have := R.pa; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (Dd * R.c / (min 1 τq * W * R.a))
  set n : ℕ := N + 1 with hndef
  have hn : 0 < n := Nat.succ_pos N
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hcase : Dd * R.c < n * min 1 τq * W * R.a := by
    have h1 : Dd * R.c / (min 1 τq * W * R.a) < n := by
      have : (N : ℚ) ≤ n := by rw [hndef]; push_cast; linarith
      linarith
    rw [div_lt_iff₀ hden] at h1
    nlinarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have step : ∀ m : ℕ, 1 ≤ m → m ≤ n → ChartRSD R A w d h (prefSet (τq : ℝ) n m) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      intro hmn
      have : prefSet (τq : ℝ) n 1 = stripSet (τq : ℝ) n 0 := by
        ext z; simp [prefSet, stripSet]
      rw [this]
      exact strip_chart R A w d h W Dd hW hD hw hd hwd τq hτ n 0 hn hn hcase
    | succ m hm ih =>
      intro hmn
      have ih' := ih (by omega)
      have hs := strip_chart R A w d h W Dd hW hD hw hd hwd τq hτ n m hn (by omega) hcase
      have hset : prefSet (τq : ℝ) n (m + 1) = prefSet (τq : ℝ) n m ∪ stripSet (τq : ℝ) n m := by
        ext z
        simp only [prefSet, stripSet, Set.mem_union, Set.mem_setOf_eq]
        push_cast
        constructor
        · rintro ⟨h1, h2, h3, h4⟩
          by_cases hz : z 1 ≤ (m : ℝ) / n
          · exact Or.inl ⟨h1, hz, h3, h4⟩
          · push_neg at hz
            exact Or.inr ⟨hz.le, h2, h3, h4⟩
        · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
          · refine ⟨h1, ?_, h3, h4⟩
            have : (m : ℝ) / n ≤ ((m : ℝ) + 1) / n := by gcongr; linarith
            linarith
          · refine ⟨?_, h2, h3, h4⟩
            have : (0 : ℝ) ≤ (m : ℝ) / n := by positivity
            linarith
      rw [hset]
      refine chart_union ih' hs ?_
      exact sepY ((m : ℝ) / n) (fun z hz => hz.2.1) (fun z hz => hz.1)
  have := step n (by omega) le_rfl
  have hfin : prefSet (τq : ℝ) n n = trapSet (τq : ℝ) := by
    ext z
    simp only [prefSet, trapSet, Set.mem_setOf_eq]
    rw [div_self hnR.ne']
  rwa [hfin] at this

end Erdos634.LaczL22
