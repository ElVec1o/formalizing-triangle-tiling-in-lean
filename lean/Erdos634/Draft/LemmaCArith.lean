-- Draft/LemmaCArith.lean — arithmetic core of Lemma C (C1), Steps 0–4 of
-- (private working notes, not included) §1.
-- Pure integer/real arithmetic: no geometry.  The geometric inputs (F1)-(F3) are hypotheses here.
-- Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Mathlib

open scoped BigOperators

namespace Erdos634.Draft.LemmaCArith

/-- Step 0: two integer relations on an irrational-type angle vector are proportional. -/
lemma rat_prop (x : Fin 3 → ℝ) (hsum : x 0 + x 1 + x 2 = Real.pi)
    (hirr : ∃ i, ¬ ∃ r : ℚ, x i = (r : ℝ) * Real.pi)
    (g e : Fin 3 → ℤ)
    (hg : (g 0 : ℝ) * x 0 + g 1 * x 1 + g 2 * x 2 = 0)
    (he : (e 0 : ℝ) * x 0 + e 1 * x 1 + e 2 * x 2 = 0) (hne : e ≠ 0) :
    ∀ i j, g i * e j = g j * e i := by
  by_contra hcon
  have hw : ¬ (g 1 * e 2 - g 2 * e 1 = 0 ∧ g 2 * e 0 - g 0 * e 2 = 0 ∧
      g 0 * e 1 - g 1 * e 0 = 0) := by
    rintro ⟨h0, h1, h2⟩
    apply hcon
    intro i j
    fin_cases i <;> fin_cases j <;> simp <;> linarith
  obtain ⟨i0, hi0⟩ := hirr
  set w0 : ℤ := g 1 * e 2 - g 2 * e 1 with hw0
  set w1 : ℤ := g 2 * e 0 - g 0 * e 2 with hw1
  set w2 : ℤ := g 0 * e 1 - g 1 * e 0 with hw2
  have h01 : x 0 * (w1 : ℝ) = x 1 * w0 := by
    simp only [hw0, hw1]; push_cast
    linear_combination (g 2 : ℝ) * he - (e 2 : ℝ) * hg
  have h02 : x 0 * (w2 : ℝ) = x 2 * w0 := by
    simp only [hw0, hw2]; push_cast
    linear_combination (-(g 1 : ℝ)) * he + (e 1 : ℝ) * hg
  have h12 : x 1 * (w2 : ℝ) = x 2 * w1 := by
    simp only [hw1, hw2]; push_cast
    linear_combination (g 0 : ℝ) * he - (e 0 : ℝ) * hg
  have hS : ((w0 + w1 + w2 : ℤ) : ℝ) ≠ 0 := by
    intro hS0
    push_cast at hS0
    have a0 : (w0 : ℝ) * Real.pi = 0 := by
      have : x 0 * ((w0 : ℝ) + w1 + w2) = (w0 : ℝ) * Real.pi := by
        rw [← hsum]; linear_combination h01 + h02
      rw [← this, hS0]; ring
    have a1 : (w1 : ℝ) * Real.pi = 0 := by
      have : x 1 * ((w0 : ℝ) + w1 + w2) = (w1 : ℝ) * Real.pi := by
        rw [← hsum]; linear_combination (-1 : ℝ) * h01 + h12
      rw [← this, hS0]; ring
    have a2 : (w2 : ℝ) * Real.pi = 0 := by
      have : x 2 * ((w0 : ℝ) + w1 + w2) = (w2 : ℝ) * Real.pi := by
        rw [← hsum]; linear_combination (-1 : ℝ) * h02 - h12
      rw [← this, hS0]; ring
    have hpi := Real.pi_pos.ne'
    have b0 : (w0 : ℝ) = 0 := by
      rcases mul_eq_zero.mp a0 with h | h
      · exact h
      · exact absurd h hpi
    have b1 : (w1 : ℝ) = 0 := by
      rcases mul_eq_zero.mp a1 with h | h
      · exact h
      · exact absurd h hpi
    have b2 : (w2 : ℝ) = 0 := by
      rcases mul_eq_zero.mp a2 with h | h
      · exact h
      · exact absurd h hpi
    exact hw ⟨by exact_mod_cast b0, by exact_mod_cast b1, by exact_mod_cast b2⟩
  apply hi0
  have hSq : ((w0 + w1 + w2 : ℤ) : ℚ) ≠ 0 := by
    intro h; apply hS; have := congrArg (fun q : ℚ => (q : ℝ)) h; simpa using this
  have hx0 : x 0 * ((w0 : ℝ) + w1 + w2) = (w0 : ℝ) * Real.pi := by
    rw [← hsum]; linear_combination h01 + h02
  have hx1 : x 1 * ((w0 : ℝ) + w1 + w2) = (w1 : ℝ) * Real.pi := by
    rw [← hsum]; linear_combination (-1 : ℝ) * h01 + h12
  have hx2 : x 2 * ((w0 : ℝ) + w1 + w2) = (w2 : ℝ) * Real.pi := by
    rw [← hsum]; linear_combination (-1 : ℝ) * h02 - h12
  push_cast at hS
  fin_cases i0
  · refine ⟨(w0 : ℚ) / ((w0 : ℚ) + w1 + w2), ?_⟩
    push_cast; field_simp; linarith
  · refine ⟨(w1 : ℚ) / ((w0 : ℚ) + w1 + w2), ?_⟩
    push_cast; field_simp; linarith
  · refine ⟨(w2 : ℚ) / ((w0 : ℚ) + w1 + w2), ?_⟩
    push_cast; field_simp; linarith


/-- **Lemma C, arithmetic core (Steps 0-4).**  Hypotheses (F1)-(F3) of the paper proof are the
data `c` (sum of the three target-corner figures), `f`/`k` (the figures of the other vertices,
each with angle sum `k*π`, `k ∈ {1,2}`), and the count `Σ = N`. -/
theorem lemmaC_arith (x : Fin 3 → ℝ) (hpos : ∀ i, 0 < x i)
    (hsum : x 0 + x 1 + x 2 = Real.pi)
    (hirr : ∃ i, ¬ ∃ r : ℚ, x i = (r : ℝ) * Real.pi)
    (c : Fin 3 → ℕ) (hc3 : 3 ≤ c 0 + c 1 + c 2)
    (hc : (c 0 : ℝ) * x 0 + c 1 * x 1 + c 2 * x 2 = Real.pi)
    (hne : ¬ (c 0 = 1 ∧ c 1 = 1 ∧ c 2 = 1))
    {ι : Type*} (s : Finset ι) (f : ι → Fin 3 → ℕ) (k : ι → ℕ)
    (hk : ∀ v ∈ s, k v = 1 ∨ k v = 2)
    (hf : ∀ v ∈ s, (f v 0 : ℝ) * x 0 + f v 1 * x 1 + f v 2 * x 2 = (k v : ℝ) * Real.pi)
    (N : ℕ) (hN : ∀ j, ∑ v ∈ s, f v j + c j = N) :
    ∃ d : Fin 3 → ℤ, (∀ j, (c j : ℤ) = 1 + d j) ∧ (∀ j, -1 ≤ d j ∧ d j ≤ 2) ∧
      (∃ j, d j = -1) ∧ (∃ j, 0 < d j) ∧ 0 ≤ d 0 + d 1 + d 2 ∧
      (d 0 : ℝ) * x 0 + d 1 * x 1 + d 2 * x 2 = 0 := by
  classical
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  set e : Fin 3 → ℤ := fun j => (c j : ℤ) - 1 with he_def
  have hex : (e 0 : ℝ) * x 0 + e 1 * x 1 + e 2 * x 2 = 0 := by
    simp only [he_def]; push_cast; linarith
  have hene : e ≠ 0 := by
    intro h
    apply hne
    have h0 := congrFun h 0; have h1 := congrFun h 1; have h2 := congrFun h 2
    simp only [he_def, Pi.zero_apply] at h0 h1 h2
    omega
  set g : ι → Fin 3 → ℤ := fun v j => (f v j : ℤ) - k v with hg_def
  have hgx : ∀ v ∈ s, (g v 0 : ℝ) * x 0 + g v 1 * x 1 + g v 2 * x 2 = 0 := by
    intro v hv
    simp only [hg_def]; push_cast
    have := hf v hv
    linear_combination this - (k v : ℝ) * hsum
  have hp : ∀ v ∈ s, ∀ i j, g v i * e j = g v j * e i := fun v hv =>
    rat_prop x hsum hirr (g v) e (hgx v hv) hex hene
  -- Bezout for the gcd of e
  obtain ⟨n, hnpos, hndvd, α, hnα⟩ : ∃ n : ℤ, 0 < n ∧ (∀ j, n ∣ e j) ∧
      ∃ α : Fin 3 → ℤ, n = α 0 * e 0 + α 1 * e 1 + α 2 * e 2 := by
    set m : ℤ := (Int.gcd (e 0) (e 1) : ℤ) with hm
    have hm0 : m ∣ e 0 := Int.gcd_dvd_left ..
    have hm1 : m ∣ e 1 := Int.gcd_dvd_right ..
    have hmB : m = e 0 * Int.gcdA (e 0) (e 1) + e 1 * Int.gcdB (e 0) (e 1) :=
      Int.gcd_eq_gcd_ab _ _
    set n : ℤ := (Int.gcd m (e 2) : ℤ) with hn
    have hnm : n ∣ m := Int.gcd_dvd_left ..
    have hn2 : n ∣ e 2 := Int.gcd_dvd_right ..
    have hnB : n = m * Int.gcdA m (e 2) + e 2 * Int.gcdB m (e 2) := Int.gcd_eq_gcd_ab _ _
    have hdv : ∀ j, n ∣ e j := by
      intro j; fin_cases j
      · exact hnm.trans hm0
      · exact hnm.trans hm1
      · exact hn2
    refine ⟨n, ?_, hdv, ![Int.gcdA (e 0) (e 1) * Int.gcdA m (e 2),
      Int.gcdB (e 0) (e 1) * Int.gcdA m (e 2), Int.gcdB m (e 2)], ?_⟩
    · have hn0 : n ≠ 0 := by
        intro h0
        apply hene
        funext j
        have := hdv j
        rw [h0, zero_dvd_iff] at this
        simpa using this
      exact lt_of_le_of_ne (Int.natCast_nonneg _) (Ne.symm hn0)
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      rw [hnB, hmB]; ring
  have hn0 : n ≠ 0 := hnpos.ne'
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
  set d : Fin 3 → ℤ := fun j => e j / n with hd_def
  have hed : ∀ j, e j = n * d j := fun j => (Int.mul_ediv_cancel' (hndvd j)).symm
  have hdx : (d 0 : ℝ) * x 0 + d 1 * x 1 + d 2 * x 2 = 0 := by
    have h : (n : ℝ) * ((d 0 : ℝ) * x 0 + d 1 * x 1 + d 2 * x 2) = 0 := by
      have := hex
      rw [hed 0, hed 1, hed 2] at this
      push_cast at this; linarith
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hnR
    · exact h
  have hdne : ∃ j, d j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hene; funext j; rw [hed j, hcon j]; simp
  set t : ι → ℤ := fun v => α 0 * g v 0 + α 1 * g v 1 + α 2 * g v 2 with ht_def
  have hgt : ∀ v ∈ s, ∀ j, g v j = t v * d j := by
    intro v hv j
    have hp' := hp v hv
    have key : n * g v j = n * (t v * d j) := by
      have h1 : n * g v j = t v * e j := by
        rw [hnα]; simp only [ht_def]
        linear_combination α 0 * hp' j 0 + α 1 * hp' j 1 + α 2 * hp' j 2
      rw [h1, hed j]; ring
    exact mul_left_cancel₀ hn0 key
  have hfv : ∀ v ∈ s, ∀ j, (f v j : ℤ) = k v + t v * d j := by
    intro v hv j
    have := hgt v hv j
    simp only [hg_def] at this
    linarith
  have hcj : ∀ j, (c j : ℤ) = 1 + n * d j := by
    intro j; have := hed j; simp only [he_def] at this; linarith
  -- Step 2
  set T : ℤ := ∑ v ∈ s, t v with hT
  set K : ℤ := ∑ v ∈ s, (k v : ℤ) with hK
  have hcount : ∀ j, K + T * d j = (N : ℤ) - c j := by
    intro j
    have h1 : ∑ v ∈ s, (f v j : ℤ) = (N : ℤ) - c j := by
      have := hN j
      have h2 : ((∑ v ∈ s, f v j : ℕ) : ℤ) + c j = N := by exact_mod_cast this
      push_cast at h2; linarith
    rw [← h1, Finset.sum_congr rfl (fun v hv => hfv v hv j), Finset.sum_add_distrib, ← Finset.sum_mul]
  have hTn : ∀ j, (T + n) * d j = (N : ℤ) - 1 - K := by
    intro j; have := hcount j; have := hcj j; linarith
  have hNK : (N : ℤ) - 1 - K = 0 := by
    have h : ((N : ℝ) - 1 - K) * Real.pi = 0 := by
      have e0 := hTn 0; have e1 := hTn 1; have e2 := hTn 2
      have r0 : (((T + n) * d 0 : ℤ) : ℝ) = (((N : ℤ) - 1 - K : ℤ) : ℝ) := by rw [e0]
      have r1 : (((T + n) * d 1 : ℤ) : ℝ) = (((N : ℤ) - 1 - K : ℤ) : ℝ) := by rw [e1]
      have r2 : (((T + n) * d 2 : ℤ) : ℝ) = (((N : ℤ) - 1 - K : ℤ) : ℝ) := by rw [e2]
      push_cast at r0 r1 r2
      have : ((N : ℝ) - 1 - K) * (x 0 + x 1 + x 2)
          = ((T : ℝ) + n) * ((d 0 : ℝ) * x 0 + d 1 * x 1 + d 2 * x 2) := by
        linear_combination (-x 0) * r0 + (-x 1) * r1 + (-x 2) * r2
      rw [hsum, hdx] at this; linarith
    rcases mul_eq_zero.mp h with h | h
    · exact_mod_cast (by linarith : ((N : ℝ) - 1 - K) = 0)
    · exact absurd h hpi
  have hTn0 : T + n = 0 := by
    obtain ⟨j, hj⟩ := hdne
    have := hTn j
    rw [hNK] at this
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hj
  have hTneg : T = -n := by linarith
  obtain ⟨v0, hv0, htv0⟩ : ∃ v ∈ s, t v < 0 := by
    by_contra h
    push Not at h
    have : 0 ≤ T := Finset.sum_nonneg h
    linarith
  have hk2 : (k v0 : ℤ) ≤ 2 := by have := hk v0 hv0; omega
  have hdle : ∀ j, d j ≤ 2 := by
    intro j
    by_contra hj
    push Not at hj
    have h1 := hfv v0 hv0 j
    have h2 : (0 : ℤ) ≤ (f v0 j : ℤ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ -1 - t v0) (by linarith : (0 : ℤ) ≤ d j)]
  have hneg : ∃ j, d j < 0 := by
    by_contra h
    push Not at h
    obtain ⟨j, hj⟩ := hdne
    have hjpos : 0 < d j := lt_of_le_of_ne (h j) (Ne.symm hj)
    have t0 : 0 ≤ (d 0 : ℝ) * x 0 := mul_nonneg (by exact_mod_cast h 0) (hpos 0).le
    have t1 : 0 ≤ (d 1 : ℝ) * x 1 := mul_nonneg (by exact_mod_cast h 1) (hpos 1).le
    have t2 : 0 ≤ (d 2 : ℝ) * x 2 := mul_nonneg (by exact_mod_cast h 2) (hpos 2).le
    have hjr : 0 < (d j : ℝ) * x j := mul_pos (by exact_mod_cast hjpos) (hpos j)
    fin_cases j <;> simp at hjr <;> linarith
  have hposx : ∃ j, 0 < d j := by
    by_contra h
    push Not at h
    obtain ⟨j, hj⟩ := hdne
    have hjneg : d j < 0 := lt_of_le_of_ne (h j) hj
    have t0 : (d 0 : ℝ) * x 0 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h 0) (hpos 0).le
    have t1 : (d 1 : ℝ) * x 1 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h 1) (hpos 1).le
    have t2 : (d 2 : ℝ) * x 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h 2) (hpos 2).le
    have hjr : (d j : ℝ) * x j < 0 := mul_neg_of_neg_of_pos (by exact_mod_cast hjneg) (hpos j)
    fin_cases j <;> simp at hjr <;> linarith
  obtain ⟨j0, hj0⟩ := hneg
  have hc0 : (0 : ℤ) ≤ (c j0 : ℤ) := Nat.cast_nonneg _
  have hn1 : n = 1 := by
    have := hcj j0
    nlinarith [mul_nonneg hnpos.le (by linarith : (0 : ℤ) ≤ -1 - d j0)]
  subst hn1
  have hcj1 : ∀ j, (c j : ℤ) = 1 + d j := fun j => by have := hcj j; linarith
  have hge : ∀ j, -1 ≤ d j := fun j => by
    have := hcj1 j; have : (0 : ℤ) ≤ (c j : ℤ) := Nat.cast_nonneg _; linarith
  refine ⟨d, hcj1, fun j => ⟨hge j, hdle j⟩, ⟨j0, by have := hge j0; omega⟩, hposx, ?_, hdx⟩
  have h0 := hcj1 0; have h1 := hcj1 1; have h2 := hcj1 2
  omega


/-- The six admissible difference vectors of Lemma C. -/
def sixVectors : Finset (ℤ × ℤ × ℤ) :=
  {(-1, 1, 0), (-1, 0, 2), (-1, 1, 1), (-1, 1, 2), (-1, 2, 2), (-1, -1, 2)}

/-- **Step 4, enumeration.** Entries in `{-1,..,2}`, one `-1`, one positive entry, sum `≥ 0`:
up to reordering, `d` is one of the six vectors. -/
theorem enum_six (a b c : ℤ) (ha : -1 ≤ a ∧ a ≤ 2) (hb : -1 ≤ b ∧ b ≤ 2) (hc : -1 ≤ c ∧ c ≤ 2)
    (hm : a = -1 ∨ b = -1 ∨ c = -1) (hp : 0 < a ∨ 0 < b ∨ 0 < c) (hs : 0 ≤ a + b + c) :
    ∃ i j l : Fin 3, i ≠ j ∧ j ≠ l ∧ i ≠ l ∧
      (![a, b, c] i, ![a, b, c] j, ![a, b, c] l) ∈ sixVectors := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  interval_cases a <;> interval_cases b <;> interval_cases c <;> first
    | (exfalso; omega)
    | decide

end Erdos634.Draft.LemmaCArith

#print axioms Erdos634.Draft.LemmaCArith.lemmaC_arith
#print axioms Erdos634.Draft.LemmaCArith.enum_six
