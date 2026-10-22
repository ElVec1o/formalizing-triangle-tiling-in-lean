-- Draft/CaseALemmaF.lean — CASE A, node A7: **Lemma F** (shapes left by trivial relations),
-- (private working notes, not included) §3.6 (and proposal a, l.557–565);
-- PRIME_CASE_PROOF.md §3.1 row A7:
--   e ∈ R₀(a), F·a = n, three nonzero corner figures, T neither equilateral nor right isosceles
--   → ABC ~ T, or T is right and ABC is isosceles with base angle an acute angle of T.
--
-- Lemma F is pure arithmetic on (a, f): no dissection enters its statement.  The dissection
-- only supplies its inputs (corner figures f_j with f_j·a = the target angle, via Lemma K/K*).
--
-- Findings recorded in the statements below:
--   * `F·a = n` is NOT used by the core (`lemmaF`); it is used only to drop the right-isosceles
--     exclusion (`lemmaF_all`), where it is essential.
--   * The equilateral exclusion is never used (equilateral tiles give ABC ~ T).
--   * With `F·a = n`, the right-isosceles exclusion is unnecessary too (`lemmaF_all`).
--
-- `saw/relSpace/trivSpace` (CaseACorF) and `uu/FF/ev/K1/K2/lemmaKStar` (CaseALemmaKStar) are reused.
-- Formalization debt on a paper-level PROVED node; NOT /goal progress.  Imported into All.lean (All.lean:650).
import Erdos634.Draft.CaseALemmaKStar

open scoped BigOperators

namespace Erdos634.LemmaF

open Erdos634.LemmaS Erdos634.LemmaKStar

/-- ABC ~ T: the multiset of target corner angles (units π/n, `uu a f j = f_j·a`) equals the
multiset of tile angles `a`, stated by counts. -/
def Similar (a : Fin 3 → ℕ) (f : Fin 3 → Fin 3 → ℕ) : Prop :=
  ∀ x : ℕ, ∑ j, (if uu a f j = x then 1 else 0 : ℕ) = ∑ i, (if a i = x then 1 else 0 : ℕ)

/-- Half-isosceles: T is right (`2 a_k = n`) and two target corners equal the same acute tile
angle `a_l`, `l ≠ k` (ABC isosceles with base angle an acute angle of T). -/
def HalfIso (n : ℕ) (a : Fin 3 → ℕ) (f : Fin 3 → Fin 3 → ℕ) : Prop :=
  ∃ k l : Fin 3, 2 * a k = n ∧ l ≠ k ∧
    ∃ j₁ j₂ : Fin 3, j₁ ≠ j₂ ∧ uu a f j₁ = a l ∧ uu a f j₂ = a l

/-- T right isosceles. -/
def RightIso (n : ℕ) (a : Fin 3 → ℕ) : Prop := (∃ k, 2 * a k = n) ∧ ∃ i, 4 * a i = n

variable {n : ℕ} {a : Fin 3 → ℕ} {f : Fin 3 → Fin 3 → ℕ}

/-! ## Fin 3 bookkeeping -/

theorem cover : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → ∀ l, l = i ∨ l = j ∨ l = k := by
  decide

theorem sum3 {M : Type*} [AddCommMonoid M] (g : Fin 3 → M) {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : ∑ l, g l = g i + g j + g k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all [Fin.sum_univ_three] <;> abel

/-! ## Invariants of R₀(a) -/

/-- Every `e ∈ R₀(a)` is killed by every weight `c` constant on equal-angle classes and zero on
right angles. -/
theorem inv_of_mem {e : Fin 3 → ℚ} (he : e ∈ trivSpace n a) (c : Fin 3 → ℚ)
    (hc1 : ∀ i j, a i = a j → c i = c j) (hc2 : ∀ k, 2 * a k = n → c k = 0) :
    ∑ i, e i * c i = 0 := by
  unfold trivSpace at he
  induction he using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨i, j, _, hij, rfl⟩ | ⟨k, hk, rfl⟩
    · simp [sub_mul, Finset.sum_sub_distrib, Pi.single_apply, hc1 i j hij]
    · simp [Pi.single_apply, hc2 k hk]
  | zero => simp
  | add x y _ _ hx hy => simp [add_mul, Finset.sum_add_distrib, hx, hy]
  | smul r x _ hx => simp [mul_assoc, ← Finset.mul_sum, hx]

theorem ev_zero {e : Fin 3 → ℚ} (he : e ∈ trivSpace n a) (i : Fin 3)
    (hlone : ∀ q, q ≠ i → a q ≠ a i) (hnr : 2 * a i ≠ n) : e i = 0 := by
  have h := inv_of_mem he (fun p => if p = i then 1 else 0)
    (fun p q hpq => by
      by_cases hp : p = i <;> by_cases hq : q = i <;> simp only [hp, hq, if_true, if_false]
      · subst hp; exact absurd hpq.symm (hlone q hq)
      · subst hq; exact absurd hpq (hlone p hp))
    (fun k hk => by
      by_cases h : k = i
      · subst h; exact absurd hk hnr
      · simp [h])
  simpa using h

theorem ev_eq (l : Fin 3) :
    ev f l = (FF f l : ℚ) - 1 - ((FF f 0 : ℚ) - 1 + ((FF f 1 : ℚ) - 1) + ((FF f 2 : ℚ) - 1)) := by
  simp [ev, dv, δ, Fin.sum_univ_three]; ring

/-! ## Corner counting -/

theorem row_ne (hf : ∀ j, f j ≠ 0) (j : Fin 3) : 1 ≤ ∑ i, f j i := by
  by_contra h
  apply hf j
  funext i
  have h0 : ∑ i, f j i = 0 := by omega
  exact (Finset.sum_eq_zero_iff.mp h0) i (Finset.mem_univ _)

theorem mass_eq (f : Fin 3 → Fin 3 → ℕ) : ∑ i, FF f i = ∑ j, ∑ i, f j i := by
  simp only [FF]; exact Finset.sum_comm

theorem mass_ge (hf : ∀ j, f j ≠ 0) : 3 ≤ ∑ i, FF f i := by
  rw [mass_eq, Fin.sum_univ_three]
  have := row_ne hf 0; have := row_ne hf 1; have := row_ne hf 2
  omega

theorem row_count (r : Fin 3 → ℕ) (hr : ∑ i, r i = 1) (x : ℕ) :
    (if ∑ i, r i * a i = x then 1 else 0 : ℕ) = ∑ i, r i * (if a i = x then 1 else 0) := by
  simp only [Fin.sum_univ_three] at *
  have : (r 0 = 1 ∧ r 1 = 0 ∧ r 2 = 0) ∨ (r 0 = 0 ∧ r 1 = 1 ∧ r 2 = 0) ∨
      (r 0 = 0 ∧ r 1 = 0 ∧ r 2 = 1) := by omega
  rcases this with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;> simp [h0, h1, h2]

/-- Total corner mass 3 ⇒ every corner is a single tile corner, and target-angle counts are
F-weighted tile-angle counts. -/
theorem count_mass3 (hf : ∀ j, f j ≠ 0) (hM : ∑ i, FF f i = 3) (x : ℕ) :
    ∑ j, (if uu a f j = x then 1 else 0 : ℕ) = ∑ i, FF f i * (if a i = x then 1 else 0) := by
  rw [mass_eq, Fin.sum_univ_three] at hM
  have h0 := row_ne hf 0; have h1 := row_ne hf 1; have h2 := row_ne hf 2
  have hr : ∑ i, f 0 i = 1 ∧ ∑ i, f 1 i = 1 ∧ ∑ i, f 2 i = 1 := by omega
  have hrow : ∀ j, ∑ i, f j i = 1 := by
    intro j; fin_cases j
    exacts [hr.1, hr.2.1, hr.2.2]
  calc ∑ j, (if uu a f j = x then 1 else 0 : ℕ)
      = ∑ j, ∑ i, f j i * (if a i = x then 1 else 0) :=
        Finset.sum_congr rfl fun j _ => row_count (f j) (hrow j) x
    _ = ∑ i, FF f i * (if a i = x then 1 else 0) := by
        rw [Finset.sum_comm]; simp only [FF, Finset.sum_mul]

/-! ## Branch 1: no right angle -/

theorem nonright_branch (hf : ∀ j, f j ≠ 0) (hR : ∀ k, 2 * a k ≠ n)
    (he : ev f ∈ trivSpace n a) : Similar a f := by
  have h1 := inv_of_mem he (fun _ => 1) (fun _ _ _ => rfl) (fun k hk => absurd hk (hR k))
  simp only [Fin.sum_univ_three, ev_eq, mul_one] at h1
  have hM : (FF f 0 : ℚ) + FF f 1 + FF f 2 = 3 := by linarith
  have hM' : ∑ i, FF f i = 3 := by rw [Fin.sum_univ_three]; exact_mod_cast hM
  intro x
  rw [count_mass3 hf hM' x]
  have h2 := inv_of_mem he (fun i => if a i = x then 1 else 0)
    (fun i j hij => by simp [hij]) (fun k hk => absurd hk (hR k))
  simp only [Fin.sum_univ_three, ev_eq] at h2
  simp only [Fin.sum_univ_three]
  by_cases h0 : a 0 = x <;> by_cases h1' : a 1 = x <;> by_cases h2' : a 2 = x <;>
    simp [h0, h1', h2'] at h2 ⊢ <;> (qify; linarith)

/-! ## Branch 2: T right, not isosceles -/

/-- The combinatorial core of F = (2,2,0): three nonzero corner figures on the two acute angles
A, B (the right angle is A + B). -/
theorem right_core (x0 x1 x2 y0 y1 y2 A B : ℕ)
    (hx : x0 + x1 + x2 = 2) (hy : y0 + y1 + y2 = 2)
    (h0 : 1 ≤ x0 + y0) (h1 : 1 ≤ x1 + y1) (h2 : 1 ≤ x2 + y2) :
    (∀ z : ℕ, (if x0 * A + y0 * B = z then 1 else 0 : ℕ) + (if x1 * A + y1 * B = z then 1 else 0)
        + (if x2 * A + y2 * B = z then 1 else 0) =
        (if A = z then 1 else 0) + (if B = z then 1 else 0) + (if A + B = z then 1 else 0)) ∨
    ((x0 * A + y0 * B = B ∧ x1 * A + y1 * B = B) ∨ (x0 * A + y0 * B = B ∧ x2 * A + y2 * B = B) ∨
      (x1 * A + y1 * B = B ∧ x2 * A + y2 * B = B)) ∨
    ((x0 * A + y0 * B = A ∧ x1 * A + y1 * B = A) ∨ (x0 * A + y0 * B = A ∧ x2 * A + y2 * B = A) ∨
      (x1 * A + y1 * B = A ∧ x2 * A + y2 * B = A)) := by
  have : x0 ≤ 2 := by omega
  have : x1 ≤ 2 := by omega
  have : x2 ≤ 2 := by omega
  have : y0 ≤ 2 := by omega
  have : y1 ≤ 2 := by omega
  have : y2 ≤ 2 := by omega
  interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> try omega
  all_goals (interval_cases y0 <;> interval_cases y1 <;> interval_cases y2 <;> try omega)
  all_goals first
    | (left; intro z; (try simp only [zero_mul, one_mul, zero_add, add_zero]);
        (try (split_ifs <;> omega)); done)
    | (right; left; simp; done)
    | (right; right; simp; done)

theorem right_case {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hk : 2 * a k = n) (hrel : a i + a j = a k) (hf : ∀ j, f j ≠ 0)
    (hFk : FF f k = 0) (hFi : FF f i = 2) (hFj : FF f j = 2) : Similar a f ∨ HalfIso n a f := by
  have hz : ∀ r, f r k = 0 := fun r =>
    (Finset.sum_eq_zero_iff.mp hFk) r (Finset.mem_univ _)
  have hu : ∀ r, uu a f r = f r i * a i + f r j * a j := by
    intro r
    simp only [uu]
    rw [sum3 (fun l => f r l * a l) hij hik hjk, hz r]
    simp
  have hx : f 0 i + f 1 i + f 2 i = 2 := by
    have := hFi; simp only [FF, Fin.sum_univ_three] at this; exact this
  have hy : f 0 j + f 1 j + f 2 j = 2 := by
    have := hFj; simp only [FF, Fin.sum_univ_three] at this; exact this
  have hne : ∀ r, 1 ≤ f r i + f r j := by
    intro r
    have := row_ne hf r
    rw [sum3 (fun l => f r l) hij hik hjk, hz r] at this
    simpa using this
  rcases right_core (f 0 i) (f 1 i) (f 2 i) (f 0 j) (f 1 j) (f 2 j) (a i) (a j) hx hy
    (hne 0) (hne 1) (hne 2) with h | h | h
  · left
    intro z
    rw [Fin.sum_univ_three, hu 0, hu 1, hu 2, sum3 (fun l => if a l = z then 1 else 0) hij hik hjk,
      ← hrel]
    exact h z
  · right
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨k, j, hk, hjk, 0, 1, by decide, by rw [hu]; exact h1, by rw [hu]; exact h2⟩
    · exact ⟨k, j, hk, hjk, 0, 2, by decide, by rw [hu]; exact h1, by rw [hu]; exact h2⟩
    · exact ⟨k, j, hk, hjk, 1, 2, by decide, by rw [hu]; exact h1, by rw [hu]; exact h2⟩
  · right
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨k, i, hk, hik, 0, 1, by decide, by rw [hu]; exact h1, by rw [hu]; exact h2⟩
    · exact ⟨k, i, hk, hik, 0, 2, by decide, by rw [hu]; exact h1, by rw [hu]; exact h2⟩
    · exact ⟨k, i, hk, hik, 1, 2, by decide, by rw [hu]; exact h1, by rw [hu]; exact h2⟩

theorem right_branch {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hpos : ∀ i, 1 ≤ a i) (hsum : ∑ i, a i = n) (hf : ∀ j, f j ≠ 0)
    (hk : 2 * a k = n) (hRI : ¬ RightIso n a) (he : ev f ∈ trivSpace n a) :
    Similar a f ∨ HalfIso n a f := by
  have hs := hsum
  rw [sum3 a hij hik hjk] at hs
  have hrel : a i + a j = a k := by omega
  have hpi := hpos i; have hpj := hpos j
  have hij' : a i ≠ a j := fun h => hRI ⟨⟨k, hk⟩, ⟨i, by omega⟩⟩
  have hei : ev f i = 0 := ev_zero he i (fun q hq => by
      rcases cover i j k hij hik hjk q with rfl | rfl | rfl
      · exact absurd rfl hq
      · exact fun h => hij' h.symm
      · omega) (by omega)
  have hej : ev f j = 0 := ev_zero he j (fun q hq => by
      rcases cover i j k hij hik hjk q with rfl | rfl | rfl
      · exact hij'
      · exact absurd rfl hq
      · omega) (by omega)
  have hδ : ∀ l, ev f l = (FF f l : ℚ) - 1 - ((FF f i : ℚ) - 1 + ((FF f j : ℚ) - 1) + ((FF f k : ℚ) - 1)) := by
    intro l; simp only [ev, dv, δ]; rw [sum3 (fun l => (FF f l : ℚ) - 1) hij hik hjk]
  rw [hδ] at hei hej
  have e1 : (FF f i : ℚ) = FF f j := by linarith
  have e2 : (FF f i : ℚ) + FF f k = 2 := by linarith
  have n1 : FF f i = FF f j := by exact_mod_cast e1
  have n2 : FF f i + FF f k = 2 := by exact_mod_cast e2
  have hm := mass_ge hf
  rw [sum3 (FF f) hij hik hjk] at hm
  by_cases h2 : FF f i = 2
  · exact right_case hij hik hjk hk hrel hf (by omega) h2 (by omega)
  · -- F = (1,1,1)
    left
    have hall : ∀ l, FF f l = 1 := by
      intro l; rcases cover i j k hij hik hjk l with rfl | rfl | rfl <;> omega
    have hM : ∑ l, FF f l = 3 := by simp [hall]
    intro x
    rw [count_mass3 hf hM x]
    simp [hall]

/-! ## Lemma F -/

/-- **Lemma F** (A7), arithmetic core.  `e ∈ R₀(a)` with three nonzero corner figures and T not
right isosceles ⇒ ABC ~ T or half-isosceles.  (No `F·a = n`, no equilateral exclusion.) -/
theorem lemmaF (hpos : ∀ i, 1 ≤ a i) (hsum : ∑ i, a i = n) (hf : ∀ j, f j ≠ 0)
    (hRI : ¬ RightIso n a) (he : ev f ∈ trivSpace n a) : Similar a f ∨ HalfIso n a f := by
  by_cases hR : ∃ k, 2 * a k = n
  · obtain ⟨k, hk⟩ := hR
    fin_cases k
    · exact right_branch (i := 1) (j := 2) (k := 0) (by decide) (by decide) (by decide)
        hpos hsum hf hk hRI he
    · exact right_branch (i := 0) (j := 2) (k := 1) (by decide) (by decide) (by decide)
        hpos hsum hf hk hRI he
    · exact right_branch (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)
        hpos hsum hf hk hRI he
  · push Not at hR
    exact Or.inl (nonright_branch hf hR he)

/-- Right isosceles tiles: with `F·a = n` every target is similar (all corners are multiples of
`t = n/4`).  No relation hypothesis. -/
theorem rightIso_similar (hpos : ∀ i, 1 ≤ a i) (hsum : ∑ i, a i = n) (hf : ∀ j, f j ≠ 0)
    (hu : ∑ j, uu a f j = n) (hRI : RightIso n a) : Similar a f := by
  obtain ⟨⟨k, hk⟩, ⟨i, hi⟩⟩ := hRI
  obtain ⟨t, rfl⟩ : ∃ t, n = 4 * t := ⟨a i, hi.symm⟩
  have ht : ∀ l, a l = t ∨ a l = 2 * t := by
    rw [Fin.sum_univ_three] at hsum
    intro l
    fin_cases i <;> fin_cases k <;> fin_cases l <;> simp at hi hk ⊢ <;> omega
  have htp : 1 ≤ t := by have := hpos i; omega
  -- each corner is t * c_j with c_j ≥ 1
  have hc : ∀ r, ∃ c, uu a f r = t * c ∧ 1 ≤ c := by
    intro r
    have hdvd : t ∣ uu a f r := Finset.dvd_sum fun l _ => by
      rcases ht l with h | h <;> rw [h]
      · exact Dvd.intro_left _ rfl
      · exact Dvd.dvd.mul_left (Dvd.intro_left 2 rfl) _
    have hge : t * ∑ l, f r l ≤ uu a f r := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun l _ => by
        rcases ht l with h | h <;> rw [h] <;> nlinarith
    obtain ⟨c, hc⟩ := hdvd
    refine ⟨c, hc, ?_⟩
    have := row_ne hf r
    have h2 : t * 1 ≤ t * c := by nlinarith
    exact Nat.le_of_mul_le_mul_left h2 htp
  obtain ⟨c0, hc0, p0⟩ := hc 0
  obtain ⟨c1, hc1, p1⟩ := hc 1
  obtain ⟨c2, hc2, p2⟩ := hc 2
  rw [Fin.sum_univ_three, hc0, hc1, hc2, ← mul_add, ← mul_add] at hu
  have hcs : c0 + c1 + c2 = 4 := by
    have : t * (c0 + c1 + c2) = t * 4 := by rw [hu]; ring
    exact Nat.eq_of_mul_eq_mul_left htp this
  intro x
  rw [Fin.sum_univ_three, Fin.sum_univ_three, hc0, hc1, hc2]
  rw [Fin.sum_univ_three] at hsum
  -- tile angles are (t, t, 2t) in some order
  have hshape : (a 0 = t ∧ a 1 = t ∧ a 2 = 2 * t) ∨ (a 0 = t ∧ a 1 = 2 * t ∧ a 2 = t) ∨
      (a 0 = 2 * t ∧ a 1 = t ∧ a 2 = t) := by
    rcases ht 0 with h0 | h0 <;> rcases ht 1 with h1 | h1 <;> rcases ht 2 with h2 | h2 <;> omega
  have hcases : (c0 = 1 ∧ c1 = 1 ∧ c2 = 2) ∨ (c0 = 1 ∧ c1 = 2 ∧ c2 = 1) ∨
      (c0 = 2 ∧ c1 = 1 ∧ c2 = 1) := by omega
  rcases hshape with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ <;>
  rcases hcases with ⟨d0, d1, d2⟩ | ⟨d0, d1, d2⟩ | ⟨d0, d1, d2⟩ <;>
    (rw [e0, e1, e2, d0, d1, d2]; split_ifs <;> omega)

/-- **Lemma F, all tiles** (with `F·a = n`): no shape exclusion at all. -/
theorem lemmaF_all (hpos : ∀ i, 1 ≤ a i) (hsum : ∑ i, a i = n) (hf : ∀ j, f j ≠ 0)
    (hu : ∑ j, uu a f j = n) (he : ev f ∈ trivSpace n a) : Similar a f ∨ HalfIso n a f := by
  by_cases hRI : RightIso n a
  · exact Or.inl (rightIso_similar hpos hsum hf hu hRI)
  · exact lemmaF hpos hsum hf hRI he

/-- The paper's hypothesis form: `p ≥ 7` dividing `n` (primality not needed) and a primitive tile
exclude the right isosceles tile (it would force `n = 4`). -/
theorem not_rightIso_of_prime {p : ℕ} (hp7 : 7 ≤ p) (hpn : p ∣ n)
    (hsum : ∑ i, a i = n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) : ¬ RightIso n a := by
  rintro ⟨⟨k, hk⟩, ⟨i, hi⟩⟩
  have ht : ∀ l, a i ∣ a l := by
    rw [Fin.sum_univ_three] at hsum
    intro l
    have : a l = a i ∨ a l = 2 * a i := by
      fin_cases i <;> fin_cases k <;> fin_cases l <;> simp at hi hk ⊢ <;> omega
    rcases this with h | h
    · rw [h]
    · rw [h]; exact dvd_mul_left _ _
  have h1 : a i ∣ 1 := hgcd ▸ Nat.dvd_gcd (ht 0) (Nat.dvd_gcd (ht 1) (ht 2))
  have h4 : n = 4 := by rw [← hi, Nat.dvd_one.mp h1]
  have := Nat.le_of_dvd (by norm_num) (h4 ▸ hpn)
  omega

/-! ## Chaining K\* + (Lemma S) + F: the A8 steps 2–3 -/

/-- A8 steps 2–3, conditional on Lemma S at `(n, a)`: Lemma K's conclusion (K1 ∧ K2 for every unit)
⇒ ABC ~ T or half-isosceles. -/
theorem shapes_of_K (hn : 3 ≤ n) (hpos : ∀ i, 1 ≤ a i) (hsum : ∑ i, a i = n)
    (hf : ∀ j, f j ≠ 0) (hu : ∑ j, uu a f j = n)
    (hS : relSpace n a = trivSpace n a)
    (hK : ∀ k : ℤ, Int.gcd k n = 1 → K1 n a f k ∧ K2 n a f k) :
    Similar a f ∨ HalfIso n a f :=
  lemmaF_all hpos hsum hf hu (hS ▸ lemmaKStar_toRel hn hpos hsum hf hu hK)

/-- A8 steps 2–3 unconditionally for `n ∈ {21, 28, 42, 66}` (Lemma S from `lemmaS_finite`). -/
theorem shapes_of_K_finite (hn : n = 21 ∨ n = 28 ∨ n = 42 ∨ n = 66) (hpos : ∀ i, 1 ≤ a i)
    (hsum : ∑ i, a i = n) (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (hf : ∀ j, f j ≠ 0) (hu : ∑ j, uu a f j = n)
    (hK : ∀ k : ℤ, Int.gcd k n = 1 → K1 n a f k ∧ K2 n a f k) :
    Similar a f ∨ HalfIso n a f :=
  shapes_of_K (by omega) hpos hsum hf hu
    (lemmaS_finite hn a (fun i => hpos i) hsum hgcd) hK

/-! ## Witnesses and negative controls -/

/-- Half-isosceles witness at n = 28: right tile (1,13,14), corners (2,13,13). -/
def aH : Fin 3 → ℕ := ![1, 13, 14]
def fH : Fin 3 → Fin 3 → ℕ := ![![2, 0, 0], ![0, 1, 0], ![0, 1, 0]]

theorem witnessH_hyps :
    (∀ i, 1 ≤ aH i) ∧ ∑ i, aH i = 28 ∧ (∀ j, fH j ≠ 0) ∧ ∑ j, uu aH fH j = 28 ∧
      Nat.gcd (aH 0) (Nat.gcd (aH 1) (aH 2)) = 1 := by
  refine ⟨by decide, by decide, ?_, by decide, by decide⟩
  intro j h
  fin_cases j <;> [exact absurd (congrFun h 0) (by simp [fH]);
    exact absurd (congrFun h 1) (by simp [fH]); exact absurd (congrFun h 1) (by simp [fH])]

theorem witnessH_mem : ev fH ∈ trivSpace 28 aH := by
  have h : ev fH = (-2 : ℚ) • Pi.single 2 1 := by
    have h0 : FF fH 0 = 2 := by decide
    have h1 : FF fH 1 = 2 := by decide
    have h2 : FF fH 2 = 0 := by decide
    funext i
    fin_cases i <;> simp [ev, dv, δ, Fin.sum_univ_three, h0, h1, h2] <;> norm_num
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨2, by decide, rfl⟩))

/-- Every hypothesis of `shapes_of_K_finite` holds (K1 ∧ K2 via K\*), and the half-isosceles
branch is the one realised: ABC is not similar to T. -/
theorem witnessH :
    (∀ k : ℤ, Int.gcd k 28 = 1 → K1 28 aH fH k ∧ K2 28 aH fH k) ∧
    HalfIso 28 aH fH ∧ ¬ Similar aH fH := by
  obtain ⟨ha, hs, hf, hu, _⟩ := witnessH_hyps
  refine ⟨?_, ⟨2, 1, by decide, by decide, 1, 2, by decide, by decide, by decide⟩, ?_⟩
  · have hm : ev fH ∈ relSpaceInt 28 aH := by
      rw [relSpaceInt_eq (by norm_num)]; exact trivSpace_le _ _ witnessH_mem
    exact (lemmaKStar (by norm_num) ha hs hf hu).1.mpr
      ((lemmaKStar (by norm_num) ha hs hf hu).2.mpr hm)
  · intro h
    have := h 1
    simp [Fin.sum_univ_three, uu, aH, fH] at this

/-- **Negative control** (the R₀ hypothesis has teeth): F2 of the row-0c table, the equilateral
target cut into 3 tiles (1,1,4)π/6, corners (2,2,2).  All other hypotheses hold, the conclusion
fails, and correspondingly e ∉ R₀(a) (it lies in the exceptional R(a) at n = 6). -/
def aE : Fin 3 → ℕ := ![1, 1, 4]
def fE : Fin 3 → Fin 3 → ℕ := ![![2, 0, 0], ![2, 0, 0], ![2, 0, 0]]

theorem negative_control :
    (∀ i, 1 ≤ aE i) ∧ ∑ i, aE i = 6 ∧ (∀ j, fE j ≠ 0) ∧ ∑ j, uu aE fE j = 6 ∧
    ¬ (Similar aE fE ∨ HalfIso 6 aE fE) ∧ ev fE ∉ trivSpace 6 aE ∧ ev fE ∈ relSpace 6 aE := by
  have hev : ev fE = ![2, -4, -4] := by
    have h0 : FF fE 0 = 6 := by decide
    have h1 : FF fE 1 = 0 := by decide
    have h2 : FF fE 2 = 0 := by decide
    funext i
    fin_cases i <;> simp [ev, dv, δ, Fin.sum_univ_three, h0, h1, h2] <;> norm_num
  refine ⟨by decide, by decide, ?_, by decide, ?_, ?_, ?_⟩
  · intro j h
    fin_cases j <;> exact absurd (congrFun h 0) (by simp [fE])
  · rintro (h | ⟨k, l, hk, -⟩)
    · exact absurd (h 2) (by decide)
    · fin_cases k <;> simp [aE] at hk
  · intro hm
    have := inv_of_mem hm (fun i => if aE i = 1 then 1 else 0)
      (fun i j hij => by simp [hij]) (fun k hk => by fin_cases k <;> simp [aE] at hk ⊢)
    rw [hev] at this
    simp [Fin.sum_univ_three, aE] at this
    norm_num at this
  · rw [hev, mem_relSpace_Z (by norm_num)]
    intro k hk
    have hr : Nat.gcd (k % 6) 6 = 1 := by
      rw [← Nat.gcd_rec, Nat.gcd_comm]; exact hk
    simp only [aE, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [sawZ_mod 6 k 1, sawZ_mod 6 k 4]
    have hlt : k % 6 < 6 := Nat.mod_lt _ (by norm_num)
    generalize k % 6 = r at hr hlt
    interval_cases r <;> simp_all [sawZ] <;> norm_num

end Erdos634.LemmaF

#print axioms Erdos634.LemmaF.lemmaF
#print axioms Erdos634.LemmaF.lemmaF_all
#print axioms Erdos634.LemmaF.not_rightIso_of_prime
#print axioms Erdos634.LemmaF.shapes_of_K
#print axioms Erdos634.LemmaF.shapes_of_K_finite
#print axioms Erdos634.LemmaF.witnessH
#print axioms Erdos634.LemmaF.negative_control
