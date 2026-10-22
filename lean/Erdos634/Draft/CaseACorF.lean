-- Draft/CaseACorF.lean — CASE A, node A6: **Corollary F (finite residue)** of Lemma S
-- ((private working notes, not included) P2, l.575; Lean vocabulary l.855–880).
--
--   For n ∈ {21, 28, 42, 66} and every a with a_j ≥ 1, Σ a = n, gcd(a) = 1:  R(a) = R₀(a).
--
-- The definitions `saw`, `relSpace`, `trivSpace` are the ones written (statements only) in
-- PROOF_lemmaS.md l.855–866, verbatim.  Route (the one recorded there): R₀ ⊆ R in general
-- (`trivSpace_le`), and R ⊆ R₀ by a certificate per ordered tile: according to the tile's pattern
-- (two equal entries / one entry n/2 / generic) some 2×2 or 3×3 integer minor of the 2n-scaled
-- sawtooth matrix, over units k, is nonzero.  The certificate search is a Bool function checked by
-- `decide +kernel` (kernel GMP arithmetic; NOT `native_decide`, so no `Lean.ofReduceBool`).
-- Negative control: the same statement FAILS at n = 10, a = (1,2,7) (`negative_control_n10`),
-- matching the recorded deletion control "P7 weakened to p = 5".
--
-- Pure algebra: there is no dissection in this node's statement.  Formalization debt on a
-- paper-level PROVED node; NOT progress on the three /goal outcomes.  Imported into All.lean (All.lean:621).
import Mathlib

open scoped BigOperators

namespace Erdos634.LemmaS

/-- ((t)) -/
def saw (t : ℚ) : ℚ := if Int.fract t = 0 then 0 else Int.fract t - 1 / 2

/-- R(a) -/
def relSpace (n : ℕ) (a : Fin 3 → ℕ) : Submodule ℚ (Fin 3 → ℚ) :=
  ⨅ (k : ℕ) (_ : k.Coprime n),
    LinearMap.ker (∑ i, saw ((k * a i : ℕ) / (n : ℚ)) •
      LinearMap.proj (R := ℚ) (φ := fun _ : Fin 3 => ℚ) i)

/-- R₀(a) -/
def trivSpace (n : ℕ) (a : Fin 3 → ℕ) : Submodule ℚ (Fin 3 → ℚ) :=
  Submodule.span ℚ ({v | ∃ i j, i ≠ j ∧ a i = a j ∧ v = Pi.single i 1 - Pi.single j 1} ∪
                    {v | ∃ i, 2 * a i = n ∧ v = Pi.single i 1})

theorem mem_relSpace {n : ℕ} {a : Fin 3 → ℕ} {e : Fin 3 → ℚ} :
    e ∈ relSpace n a ↔ ∀ k : ℕ, k.Coprime n → ∑ i, saw ((k * a i : ℕ) / (n : ℚ)) * e i = 0 := by
  simp [relSpace, Submodule.mem_iInf, LinearMap.mem_ker]

/-! ## The integer sawtooth -/

/-- `2n·((m/n))` as an integer. -/
def sawZ (n m : ℕ) : ℤ := if m % n == 0 then 0 else 2 * ((m % n : ℕ) : ℤ) - n

theorem saw_eq {n : ℕ} (hn : 0 < n) (m : ℕ) :
    saw ((m : ℕ) / (n : ℚ)) = (sawZ n m : ℚ) / (2 * n) := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold saw sawZ
  rw [Int.fract_div_natCast_eq_div_natCast_mod]
  by_cases h : m % n = 0
  · simp [h]
  · have h' : ((m % n : ℕ) : ℚ) / n ≠ 0 := div_ne_zero (by exact_mod_cast h) hn'
    rw [if_neg h']
    simp only [beq_iff_eq, h, if_false]
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    field_simp

theorem sawZ_mod (n k a : ℕ) : sawZ n (k * a) = sawZ n ((k % n) * a) := by
  unfold sawZ
  rw [Nat.mul_mod k a n, Nat.mul_mod (k % n) a n, Nat.mod_mod]

theorem mem_relSpace_Z {n : ℕ} (hn : 0 < n) {a : Fin 3 → ℕ} {e : Fin 3 → ℚ} :
    e ∈ relSpace n a ↔ ∀ k : ℕ, k.Coprime n →
      (sawZ n (k * a 0) : ℚ) * e 0 + (sawZ n (k * a 1) : ℚ) * e 1 + (sawZ n (k * a 2) : ℚ) * e 2 = 0 := by
  rw [mem_relSpace]
  have h2n : (2 * n : ℚ) ≠ 0 := by positivity
  refine forall_congr' fun k => imp_congr_right fun _ => ?_
  rw [Fin.sum_univ_three, saw_eq hn, saw_eq hn, saw_eq hn]
  constructor
  · intro h
    have := congrArg (· * (2 * n : ℚ)) h
    simp only [zero_mul] at this
    rw [← this]; field_simp
  · intro h
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
      ← add_div, h, zero_div]

/-- A column of the half entry vanishes: `2a = n`, `k` prime to `n` ⇒ `sawZ n (k a) = 0`. -/
theorem sawZ_half {n a k : ℕ} (h : 2 * a = n) (hk : k.Coprime n) : sawZ n (k * a) = 0 := by
  have hodd : k % 2 = 1 := by
    by_contra hc
    have h2k : 2 ∣ k := Nat.dvd_of_mod_eq_zero (by omega)
    have : 2 ∣ Nat.gcd k n := Nat.dvd_gcd h2k ⟨a, h.symm⟩
    rw [hk] at this
    omega
  unfold sawZ
  by_cases ha : a = 0
  · subst ha; simp
  have hk' : k * a = (k / 2) * n + a := by
    rw [← h]
    have := Nat.div_add_mod k 2
    calc k * a = (2 * (k / 2) + k % 2) * a := by rw [this]
      _ = (k / 2) * (2 * a) + a := by rw [hodd]; ring
  have hmod : k * a % n = a := by
    rw [hk', Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  rw [hmod]
  simp only [beq_iff_eq, ha, if_false]
  rw [← h]; push_cast; ring

/-! ## R₀ ⊆ R -/

theorem trivSpace_le (n : ℕ) (a : Fin 3 → ℕ) : trivSpace n a ≤ relSpace n a := by
  unfold trivSpace
  rw [Submodule.span_le]
  rintro v (⟨i, j, hij, haij, rfl⟩ | ⟨i, hi, rfl⟩)
  · rw [SetLike.mem_coe, mem_relSpace]
    intro k _
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    simp [Pi.single_apply, haij]
  · rw [SetLike.mem_coe, mem_relSpace]
    intro k hk
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [saw]
    · rw [saw_eq hn, sawZ_half hi hk]; simp

/-! ## Linear algebra -/

theorem two_by_two {u0 u1 v0 v1 x y : ℚ} (h1 : u0 * x + v0 * y = 0) (h2 : u1 * x + v1 * y = 0)
    (hd : u0 * v1 - u1 * v0 ≠ 0) : x = 0 ∧ y = 0 := by
  constructor
  · have : (u0 * v1 - u1 * v0) * x = 0 := by linear_combination v1 * h1 - v0 * h2
    exact (mul_eq_zero.mp this).resolve_left hd
  · have : (u0 * v1 - u1 * v0) * y = 0 := by linear_combination u0 * h2 - u1 * h1
    exact (mul_eq_zero.mp this).resolve_left hd

/-- 3×3 determinant, rows `(p_i, q_i, r_i)`. -/
def det3 (p0 q0 r0 p1 q1 r1 p2 q2 r2 : ℤ) : ℤ :=
  p0 * (q1 * r2 - r1 * q2) - q0 * (p1 * r2 - r1 * p2) + r0 * (p1 * q2 - q1 * p2)

theorem three_by_three {p0 q0 r0 p1 q1 r1 p2 q2 r2 : ℤ} {x y z : ℚ}
    (h0 : (p0 : ℚ) * x + q0 * y + r0 * z = 0) (h1 : (p1 : ℚ) * x + q1 * y + r1 * z = 0)
    (h2 : (p2 : ℚ) * x + q2 * y + r2 * z = 0) (hd : det3 p0 q0 r0 p1 q1 r1 p2 q2 r2 ≠ 0) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  have hd' : ((det3 p0 q0 r0 p1 q1 r1 p2 q2 r2 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hd
  unfold det3 at hd'
  push_cast at hd'
  refine ⟨?_, ?_, ?_⟩
  · have : ((p0 : ℚ) * (q1 * r2 - r1 * q2) - q0 * (p1 * r2 - r1 * p2) + r0 * (p1 * q2 - q1 * p2)) * x
        = 0 := by
      linear_combination (↑q1 * ↑r2 - ↑r1 * ↑q2) * h0 - (↑q0 * ↑r2 - ↑r0 * ↑q2) * h1
        + (↑q0 * ↑r1 - ↑r0 * ↑q1) * h2
    exact (mul_eq_zero.mp this).resolve_left hd'
  · have : ((p0 : ℚ) * (q1 * r2 - r1 * q2) - q0 * (p1 * r2 - r1 * p2) + r0 * (p1 * q2 - q1 * p2)) * y
        = 0 := by
      linear_combination -(↑p1 * ↑r2 - ↑r1 * ↑p2) * h0 + (↑p0 * ↑r2 - ↑r0 * ↑p2) * h1
        - (↑p0 * ↑r1 - ↑r0 * ↑p1) * h2
    exact (mul_eq_zero.mp this).resolve_left hd'
  · have : ((p0 : ℚ) * (q1 * r2 - r1 * q2) - q0 * (p1 * r2 - r1 * p2) + r0 * (p1 * q2 - q1 * p2)) * z
        = 0 := by
      linear_combination (↑p1 * ↑q2 - ↑q1 * ↑p2) * h0 - (↑p0 * ↑q2 - ↑q0 * ↑p2) * h1
        + (↑p0 * ↑q1 - ↑q0 * ↑p1) * h2
    exact (mul_eq_zero.mp this).resolve_left hd'

/-! ## The certificate -/

/-- Units mod `n` (representatives `0 ≤ k < n`). -/
def unitsL (n : ℕ) : List ℕ := (List.range n).filter (fun k => Nat.gcd k n == 1)

theorem coprime_of_mem_unitsL {n k : ℕ} (h : k ∈ unitsL n) : k.Coprime n := by
  unfold unitsL at h
  rw [List.mem_filter] at h
  exact beq_iff_eq.mp h.2

def minor2 (n a b : ℕ) : Bool :=
  (unitsL n).any fun k => (unitsL n).any fun k' =>
    sawZ n (k * a) * sawZ n (k' * b) - sawZ n (k' * a) * sawZ n (k * b) != 0

def minor3 (n a b c : ℕ) : Bool :=
  (unitsL n).any fun k => (unitsL n).any fun k' => (unitsL n).any fun k'' =>
    det3 (sawZ n (k * a)) (sawZ n (k * b)) (sawZ n (k * c))
      (sawZ n (k' * a)) (sawZ n (k' * b)) (sawZ n (k' * c))
      (sawZ n (k'' * a)) (sawZ n (k'' * b)) (sawZ n (k'' * c)) != 0

def cert (n a0 a1 a2 : ℕ) : Bool :=
  if a0 = a1 then minor2 n a0 a2 else if a1 = a2 then minor2 n a0 a1
  else if a0 = a2 then minor2 n a0 a1 else if 2 * a0 = n then minor2 n a1 a2
  else if 2 * a1 = n then minor2 n a0 a2 else if 2 * a2 = n then minor2 n a0 a1
  else minor3 n a0 a1 a2

def allCert (n : ℕ) : Bool :=
  (List.range n).all fun a0 => (List.range n).all fun a1 =>
    if 1 ≤ a0 ∧ 1 ≤ a1 ∧ a0 + a1 < n ∧ Nat.gcd a0 (Nat.gcd a1 (n - a0 - a1)) = 1 then
      cert n a0 a1 (n - a0 - a1) else true

theorem minor2_sound {n a b : ℕ} (h : minor2 n a b = true) {x y : ℚ}
    (hrow : ∀ k : ℕ, k.Coprime n → (sawZ n (k * a) : ℚ) * x + (sawZ n (k * b) : ℚ) * y = 0) :
    x = 0 ∧ y = 0 := by
  unfold minor2 at h
  simp only [List.any_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨k, hk, k', hk', hd⟩ := h
  refine two_by_two (hrow k (coprime_of_mem_unitsL hk)) (hrow k' (coprime_of_mem_unitsL hk')) ?_
  exact_mod_cast hd

theorem minor3_sound {n a b c : ℕ} (h : minor3 n a b c = true) {x y z : ℚ}
    (hrow : ∀ k : ℕ, k.Coprime n →
      (sawZ n (k * a) : ℚ) * x + (sawZ n (k * b) : ℚ) * y + (sawZ n (k * c) : ℚ) * z = 0) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  unfold minor3 at h
  simp only [List.any_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨k, hk, k', hk', k'', hk'', hd⟩ := h
  exact three_by_three (hrow k (coprime_of_mem_unitsL hk)) (hrow k' (coprime_of_mem_unitsL hk'))
    (hrow k'' (coprime_of_mem_unitsL hk'')) hd

/-- Generators of `trivSpace`, in the shapes the certificate produces. -/
theorem pair_mem {n : ℕ} {a : Fin 3 → ℕ} {i j : Fin 3} (hij : i ≠ j) (h : a i = a j) (t : ℚ) :
    t • (Pi.single i 1 - Pi.single j 1 : Fin 3 → ℚ) ∈ trivSpace n a :=
  Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨i, j, hij, h, rfl⟩))

theorem half_mem {n : ℕ} {a : Fin 3 → ℕ} {i : Fin 3} (h : 2 * a i = n) (t : ℚ) :
    t • (Pi.single i 1 : Fin 3 → ℚ) ∈ trivSpace n a :=
  Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨i, h, rfl⟩))

/-- **Soundness of one tile's certificate.** -/
theorem cert_sound {n : ℕ} (hn : 0 < n) {a : Fin 3 → ℕ} (hc : cert n (a 0) (a 1) (a 2) = true)
    {e : Fin 3 → ℚ} (he : e ∈ relSpace n a) : e ∈ trivSpace n a := by
  rw [mem_relSpace_Z hn] at he
  unfold cert at hc
  split_ifs at hc with h01 h12 h02 h0 h1 h2
  · obtain ⟨hx, hy⟩ := minor2_sound hc (x := e 0 + e 1) (y := e 2) fun k hk => by
      have := he k hk; rw [← h01] at this; linear_combination this
    have : e = e 0 • (Pi.single 0 1 - Pi.single 1 1 : Fin 3 → ℚ) := by
      funext i; fin_cases i <;> simp <;> linarith
    rw [this]; exact pair_mem (by decide) h01 _
  · obtain ⟨hx, hy⟩ := minor2_sound hc (x := e 0) (y := e 1 + e 2) fun k hk => by
      have := he k hk; rw [← h12] at this; linear_combination this
    have : e = e 1 • (Pi.single 1 1 - Pi.single 2 1 : Fin 3 → ℚ) := by
      funext i; fin_cases i <;> simp <;> linarith
    rw [this]; exact pair_mem (by decide) h12 _
  · obtain ⟨hx, hy⟩ := minor2_sound hc (x := e 0 + e 2) (y := e 1) fun k hk => by
      have := he k hk; rw [← h02] at this; linear_combination this
    have : e = e 0 • (Pi.single 0 1 - Pi.single 2 1 : Fin 3 → ℚ) := by
      funext i; fin_cases i <;> simp <;> linarith
    rw [this]; exact pair_mem (by decide) h02 _
  · obtain ⟨hx, hy⟩ := minor2_sound hc (x := e 1) (y := e 2) fun k hk => by
      have := he k hk; rw [sawZ_half h0 hk] at this; linear_combination this
    have : e = e 0 • (Pi.single 0 1 : Fin 3 → ℚ) := by
      funext i; fin_cases i <;> simp [hx, hy]
    rw [this]; exact half_mem h0 _
  · obtain ⟨hx, hy⟩ := minor2_sound hc (x := e 0) (y := e 2) fun k hk => by
      have := he k hk; rw [sawZ_half h1 hk] at this; linear_combination this
    have : e = e 1 • (Pi.single 1 1 : Fin 3 → ℚ) := by
      funext i; fin_cases i <;> simp [hx, hy]
    rw [this]; exact half_mem h1 _
  · obtain ⟨hx, hy⟩ := minor2_sound hc (x := e 0) (y := e 1) fun k hk => by
      have := he k hk; rw [sawZ_half h2 hk] at this; linear_combination this
    have : e = e 2 • (Pi.single 2 1 : Fin 3 → ℚ) := by
      funext i; fin_cases i <;> simp [hx, hy]
    rw [this]; exact half_mem h2 _
  · obtain ⟨hx, hy, hz⟩ := minor3_sound hc (x := e 0) (y := e 1) (z := e 2) fun k hk => he k hk
    have : e = 0 := by funext i; fin_cases i <;> simp [hx, hy, hz]
    rw [this]; exact Submodule.zero_mem _

/-- The whole level from `allCert n`. -/
theorem of_allCert {n : ℕ} (hA : allCert n = true) (a : Fin 3 → ℕ) (hpos : ∀ i, 0 < a i)
    (hsum : ∑ i, a i = n) (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) :
    relSpace n a = trivSpace n a := by
  rw [Fin.sum_univ_three] at hsum
  have h0 := hpos 0; have h1 := hpos 1; have h2 := hpos 2
  have hn : 0 < n := by omega
  have ha2 : a 2 = n - a 0 - a 1 := by omega
  unfold allCert at hA
  simp only [List.all_eq_true, List.mem_range] at hA
  have hc := hA (a 0) (by omega) (a 1) (by omega)
  rw [← ha2, if_pos ⟨h0, h1, by omega, hgcd⟩] at hc
  exact le_antisymm (fun e he => cert_sound hn hc he) (trivSpace_le n a)

theorem allCert_21 : allCert 21 = true := by decide +kernel
theorem allCert_28 : allCert 28 = true := by decide +kernel
theorem allCert_42 : allCert 42 = true := by decide +kernel
theorem allCert_66 : allCert 66 = true := by decide +kernel

/-- **Corollary F (finite residue)**, PROOF_lemmaS.md l.575 / l.879, as written. -/
theorem lemmaS_finite {n : ℕ} (hn : n = 21 ∨ n = 28 ∨ n = 42 ∨ n = 66) (a : Fin 3 → ℕ)
    (hpos : ∀ i, 0 < a i) (hsum : ∑ i, a i = n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) :
    relSpace n a = trivSpace n a := by
  rcases hn with rfl | rfl | rfl | rfl
  · exact of_allCert allCert_21 a hpos hsum hgcd
  · exact of_allCert allCert_28 a hpos hsum hgcd
  · exact of_allCert allCert_42 a hpos hsum hgcd
  · exact of_allCert allCert_66 a hpos hsum hgcd

/-- Witness: every hypothesis of `lemmaS_finite` holds at `n = 21`, `a = (1, 2, 18)`. -/
theorem lemmaS_finite_witness :
    relSpace 21 ![1, 2, 18] = trivSpace 21 ![1, 2, 18] :=
  lemmaS_finite (by decide) _ (by intro i; fin_cases i <;> decide)
    (by simp [Fin.sum_univ_three]) (by decide)

/-- **Negative control** (the recorded deletion control for P7 weakened to p = 5):
at `n = 10`, `a = (1, 2, 7)` (T1–T3 hold), `R(a) ≠ R₀(a)`: `(1, −2, −1) ∈ R(a) ∖ R₀(a)`. -/
theorem negative_control_n10 : relSpace 10 ![1, 2, 7] ≠ trivSpace 10 ![1, 2, 7] := by
  intro hEq
  have hmem : (![1, -2, -1] : Fin 3 → ℚ) ∈ relSpace 10 ![1, 2, 7] := by
    rw [mem_relSpace_Z (by norm_num)]
    intro k hk
    have hr : Nat.gcd (k % 10) 10 = 1 := by
      rw [← Nat.gcd_rec, Nat.gcd_comm]; exact hk
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [sawZ_mod 10 k 1, sawZ_mod 10 k 2, sawZ_mod 10 k 7]
    have hlt : k % 10 < 10 := Nat.mod_lt _ (by norm_num)
    generalize k % 10 = r at hr hlt
    interval_cases r <;> simp_all [sawZ] <;> norm_num
  have htriv : trivSpace 10 ![1, 2, 7] = ⊥ := by
    unfold trivSpace
    rw [Submodule.span_eq_bot]
    rintro v (⟨i, j, hij, h, -⟩ | ⟨i, h, -⟩)
    · fin_cases i <;> fin_cases j <;> simp_all
    · fin_cases i <;> simp_all
  rw [hEq, htriv, Submodule.mem_bot] at hmem
  have := congrFun hmem 0
  simp at this

end Erdos634.LemmaS

#print axioms Erdos634.LemmaS.trivSpace_le
#print axioms Erdos634.LemmaS.cert_sound
#print axioms Erdos634.LemmaS.lemmaS_finite
#print axioms Erdos634.LemmaS.lemmaS_finite_witness
#print axioms Erdos634.LemmaS.negative_control_n10
