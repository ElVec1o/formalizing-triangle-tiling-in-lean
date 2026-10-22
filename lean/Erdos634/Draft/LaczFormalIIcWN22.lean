-- Draft/LaczFormalIIcWN22.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2/6.3, Lemma 6.2 (`IIcNoKites`), step (c) `u = v + N`:
-- discrete Hopf (Umlaufsatz) for simple polygons, part 3: row 0, closing identity `hopf_core`: the exterior angles of a polygon
-- with m+1 vertices whose non-adjacent edges are disjoint and whose vertex 0 is lexicographically minimal sum to `2 pi` or `-2 pi`.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2/6.3), Beeson, Beeson-Zhang; discrete form of Hopf's proof of the Umlaufsatz.
import Erdos634.Draft.LaczFormalIIcWN21

open Complex

namespace Erdos634.Draft.LaczFormal.WN

theorem InH_neg {z : ℂ} (h : InH z) (h' : InH (-z)) : False := by
  unfold InH at h h'
  simp at h'
  rcases h with h | ⟨h0, h1⟩ <;> rcases h' with h' | ⟨h0', h1'⟩ <;> linarith

theorem InH_mul_pos {r w : ℂ} (hi : r.im = 0) (hr : 0 < r.re) (h : InH w) : InH (r * w) := by
  unfold InH at h ⊢
  have e1 : (r * w).re = r.re * w.re := by simp [Complex.mul_re, hi]
  have e2 : (r * w).im = r.re * w.im := by simp [Complex.mul_im, hi]
  rw [e1, e2]
  rcases h with h | ⟨h0, h1⟩
  · left; exact mul_pos hr h
  · right; exact ⟨by rw [h0]; ring, mul_pos hr h1⟩

/-- Row 0 against row 1. -/
theorem rowzero (q : ℕ → ℂ) (m : ℕ) (hm : 2 ≤ m) (per : q (m + 1) = q 0)
    (hcell : ∀ j, 2 ≤ j → j < m → Disjoint (segment ℝ (q 0) (q 1)) (segment ℝ (q j) (q (j + 1))))
    (h0 : dd q 0 ≠ 0) (h1 : dd q 1 ≠ 0) (hm0 : dd q m ≠ 0)
    (hr : ¬ ((dd q 1 / dd q 0).im = 0 ∧ (dd q 1 / dd q 0).re ≤ 0))
    (hw : ¬ ((dd q 0 / dd q m).im = 0 ∧ (dd q 0 / dd q m).re ≤ 0)) :
    (∑ j ∈ Finset.Ico 1 m, gg q 0 j) - Rr q (m + 1) 1 = ang (dd q 0) (dd q 1) - ang (dd q m) (dd q 0) := by
  unfold Rr
  rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : 1 < m)]
  have e : Finset.Ico (1 + 1) (m + 1) = Finset.Ico 2 (m + 1) := rfl
  rw [e, Finset.sum_Ico_succ_top (by omega : 2 ≤ m)]
  have hsum : ∑ j ∈ Finset.Ico 2 m, (gg q 0 j - gg q 1 j) = VV q 0 2 - VV q 0 m := by
    rw [← tele (fun j => VV q 0 j) (by omega : 2 ≤ m)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_Ico] at hj
    have := cell_cc q (i := 0) (j := j) (hcell j hj.1 hj.2)
    simpa using this
  rw [Finset.sum_sub_distrib] at hsum
  have hd := diag_term q 0 h0 h1 hr
  simp only [zero_add] at hd
  -- tail triangle
  have hx : cc q 1 (m + 1) = -dd q 0 := by simp [cc, dd, per]
  have hu : cc q 0 m = -dd q m := by simp [cc, dd, per]
  have hwv : cc q 1 m = cc q 0 m + cc q 1 (m + 1) := by simp [cc, per]
  have hu0 : cc q 0 m ≠ 0 := by rw [hu]; exact neg_ne_zero.2 hm0
  have hx0 : cc q 1 (m + 1) ≠ 0 := by rw [hx]; exact neg_ne_zero.2 h0
  have hq : (cc q 1 (m + 1) / cc q 0 m) = dd q 0 / dd q m := by rw [hx, hu, neg_div_neg_eq]
  have hb := ang_bisect hu0 hx0 (by rw [hq]; exact hw)
  have hb2 : VV q 0 m + gg q 1 m = ang (dd q m) (dd q 0) := by
    have e1 : VV q 0 m = ang (cc q 0 m) (cc q 0 m + cc q 1 (m + 1)) := by
      unfold VV; rw [← hwv]
    have e2 : gg q 1 m = ang (cc q 0 m + cc q 1 (m + 1)) (cc q 1 (m + 1)) := by
      unfold gg; rw [← hwv]
    rw [e1, e2, hb]
    unfold ang; rw [hq]
  linarith

theorem final_angle (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (him : (a / b).im ≠ 0) :
    Complex.arg ((-b) / a) + Complex.arg (a / b) = if 0 < (a / b).im then Real.pi else -Real.pi := by
  set r : ℂ := a / b with hr
  have hr0 : r ≠ 0 := div_ne_zero ha hb
  have e : (-b) / a = -(r⁻¹) := by rw [hr, inv_div]; ring
  have hnpi : Complex.arg r ≠ Real.pi := by
    rw [Ne, Complex.arg_eq_pi_iff]; intro h; exact him h.2
  have hai : Complex.arg r⁻¹ = - Complex.arg r := by rw [Complex.arg_inv]; simp [hnpi]
  have himinv : r⁻¹.im = - r.im / Complex.normSq r := by rw [Complex.inv_im]
  have hns : 0 < Complex.normSq r := Complex.normSq_pos.2 hr0
  rw [e]
  split_ifs with hpos
  · have : r⁻¹.im < 0 := by rw [himinv]; exact div_neg_of_neg_of_pos (by linarith) hns
    rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg this, hai]; ring
  · have hneg : r.im < 0 := lt_of_le_of_ne (not_lt.1 hpos) him
    have : 0 < r⁻¹.im := by rw [himinv]; exact div_pos (by linarith) hns
    rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos this, hai]; ring

/-- Data of a closed polygon with `m+1` vertices `q 0, ..., q m` (`q (m+1) = q 0`), vertex 0 lexicographically minimal,
non-adjacent edges disjoint, consecutive edges not antiparallel. -/
structure HData (m : ℕ) (q : ℕ → ℂ) : Prop where
  m2 : 2 ≤ m
  per : q (m + 1) = q 0
  nz : ∀ k, k ≤ m → dd q k ≠ 0
  turn : ∀ k, k + 1 ≤ m → ¬ ((dd q (k + 1) / dd q k).im = 0 ∧ (dd q (k + 1) / dd q k).re ≤ 0)
  wrap : ¬ ((dd q 0 / dd q m).im = 0 ∧ (dd q 0 / dd q m).re ≤ 0)
  disj : ∀ i j, i + 2 ≤ j → j + 1 ≤ m + 1 → (i ≠ 0 ∨ j ≠ m) →
    Disjoint (segment ℝ (q i) (q (i + 1))) (segment ℝ (q j) (q (j + 1)))
  lex : ∀ k, 1 ≤ k → k ≤ m → InH (q k - q 0)

/-- **Discrete Umlaufsatz**: the exterior angles sum to `2 pi` (counterclockwise) or `-2 pi`. -/
theorem hopf_core {m : ℕ} {q : ℕ → ℂ} (H : HData m q) :
    (∑ i ∈ Finset.range m, ang (dd q i) (dd q (i + 1))) + ang (dd q m) (dd q 0) =
      if 0 < (dd q 0 / dd q m).im then 2 * Real.pi else -(2 * Real.pi) := by
  have hm := H.m2
  -- Step A: rows 1 .. m-1
  have hA : Rr q (m + 1) 1 = ∑ i ∈ Finset.Ico 1 m, (ang (dd q i) (dd q (i + 1)) - VV q i (m + 1)) := by
    have ht := tele (fun i => Rr q (m + 1) i) (by omega : 1 ≤ m)
    have hRm : Rr q (m + 1) m = 0 := by simp [Rr]
    have hstep : ∀ i ∈ Finset.Ico 1 m, Rr q (m + 1) i - Rr q (m + 1) (i + 1) =
        ang (dd q i) (dd q (i + 1)) - VV q i (m + 1) := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      exact rowstep q (m + 1) i (by omega)
        (fun j hj1 hj2 => H.disj i j hj1 hj2 (Or.inl (by omega)))
        (H.nz i (by omega)) (H.nz (i + 1) (by omega)) (H.turn i (by omega))
    rw [Finset.sum_congr rfl hstep] at ht
    simp only at ht
    rw [hRm] at ht
    linarith
  -- Step C: the top side equals row 0
  have hC : ∑ i ∈ Finset.Ico 1 m, VV q i (m + 1) = ∑ j ∈ Finset.Ico 1 m, gg q 0 j := by
    apply Finset.sum_congr rfl
    intro i _
    unfold VV gg ang cc
    rw [H.per]
    have e1 : q 0 - q (i + 1) = -(q (i + 1) - q 0) := by ring
    have e2 : q 0 - q i = -(q i - q 0) := by ring
    rw [e1, e2, neg_div_neg_eq]
  -- Step B: row 0
  have hB := rowzero q m hm H.per
    (fun j hj1 hj2 => by simpa using H.disj 0 j (by omega) (by omega) (Or.inr (by omega)))
    (H.nz 0 (by omega)) (H.nz 1 (by omega)) (H.nz m le_rfl) (H.turn 0 (by omega)) H.wrap
  -- Step E: row 0 telescopes in the half plane
  have hE : ∑ j ∈ Finset.Ico 1 m, gg q 0 j = Complex.arg ((q m - q 0) / (q 1 - q 0)) := by
    have hf : ∀ k, 1 ≤ k → k ≤ m → InH (q k - q 0) := H.lex
    have hterm : ∀ j ∈ Finset.Ico 1 m, gg q 0 j =
        (-Complex.arg (q j - q 0)) - (-Complex.arg (q (j + 1) - q 0)) := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      unfold gg ang cc
      rw [arg_div_sub_of_InH (hf j hj.1 (by omega)) (hf (j + 1) (by omega) hj.2)]
      ring
    rw [Finset.sum_congr rfl hterm, tele (fun j => -Complex.arg (q j - q 0)) (by omega : 1 ≤ m)]
    rw [arg_div_sub_of_InH (hf 1 le_rfl (by omega)) (hf m (by omega) le_rfl)]
    ring
  have hfm : (q m - q 0) / (q 1 - q 0) = (-dd q m) / dd q 0 := by
    have : q m - q 0 = -dd q m := by simp [dd, H.per]
    rw [this]; rfl
  -- im r ≠ 0 from lexicographic minimality
  have him : (dd q 0 / dd q m).im ≠ 0 := by
    intro h0
    have hre : 0 < (dd q 0 / dd q m).re := by
      by_contra hh; exact H.wrap ⟨h0, not_lt.1 hh⟩
    have h1 : InH (dd q 0) := by
      have := H.lex 1 le_rfl (by omega); simpa [dd] using this
    have h2 : InH (-dd q m) := by
      have := H.lex m (by omega) le_rfl
      have e : q m - q 0 = -dd q m := by simp [dd, H.per]
      rwa [e] at this
    have h3 : InH ((dd q 0 / dd q m) * (-dd q m)) := InH_mul_pos h0 hre h2
    have e3 : (dd q 0 / dd q m) * (-dd q m) = -dd q 0 := by
      have := H.nz m le_rfl
      field_simp
    rw [e3] at h3
    exact InH_neg h1 h3
  have hfin := final_angle (dd q 0) (dd q m) (H.nz 0 (by omega)) (H.nz m le_rfl) him
  -- assemble
  have hrange : ∑ i ∈ Finset.range m, ang (dd q i) (dd q (i + 1)) =
      ang (dd q 0) (dd q 1) + ∑ i ∈ Finset.Ico 1 m, ang (dd q i) (dd q (i + 1)) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < m)]
  rw [Finset.sum_sub_distrib, hC] at hA
  rw [hfm] at hE
  have hsplit : ang (dd q m) (dd q 0) = Complex.arg (dd q 0 / dd q m) := rfl
  split_ifs with hpos
  · rw [if_pos hpos] at hfin
    rw [hrange, hsplit]; rw [hsplit] at hB; linarith
  · rw [if_neg hpos] at hfin
    rw [hrange, hsplit]; rw [hsplit] at hB; linarith

end Erdos634.Draft.LaczFormal.WN
