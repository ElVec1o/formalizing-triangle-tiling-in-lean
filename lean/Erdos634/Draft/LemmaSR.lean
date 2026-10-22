/-
# Lemma S, Lemma R (Lemma S ⟸ Lemma P)

Source: (private working notes, not included) P2 and §3.3:

  **Lemma R** (T1–T3; p a prime dividing n). If Lemma P's conclusion holds for every e ∈ R(a),
  then R(a) = R₀(a).

Lemma P's conclusion (P2, class form of P1.2): E_x = 0 for every I-point x, where
I = {j : p ∤ a_j} and E_x = Σ_{j∈I, x_j = x} e_j.  Since 1 ≤ a_j < n, x_j = x_k ⟺ a_j = a_k, so
E_{x_j} = Σ_{k ∈ I, a_k = a_j} e_k.

Proof as in §3.3: |I| ≥ 2 (two indices with p | a would give p | gcd(a)); the I-part of e is a
combination of differences within classes; the at most one index l ∉ I then satisfies
e_l·((k x_l)) ≡ 0, and at k = 1 this forces e_l = 0 or x_l = ½.

Formalization debt only (Lemma S is PROVED at paper level); NOT /goal progress.
-/
import Mathlib
import Erdos634.Draft.CaseACorF

open scoped BigOperators
open Finset

namespace Erdos634.LemmaSR

open Erdos634.LemmaS

/-- A class-dependent weight summed against coefficients with vanishing class sums gives 0. -/
theorem class_zero {M : Type*} [AddCommGroup M] [Module ℚ M] (I : Finset (Fin 3)) (a : Fin 3 → ℕ)
    (e : Fin 3 → ℚ) (hcl : ∀ j ∈ I, ∑ k ∈ I.filter (fun k => a k = a j), e k = 0)
    (w : Fin 3 → M) (hw : ∀ j k, a j = a k → w j = w k) :
    ∑ j ∈ I, e j • w j = 0 := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun x hx => mem_image_of_mem a hx)]
  refine sum_eq_zero (fun v hv => ?_)
  obtain ⟨j0, hj0, rfl⟩ := mem_image.1 hv
  rw [sum_congr rfl (fun j hj => by rw [hw j j0 (mem_filter.1 hj).2]), ← sum_smul, hcl j0 hj0,
    zero_smul]

theorem saw_eq_zero_imp {n m : ℕ} (hm : 0 < m) (hmn : m < n) (h : saw ((m : ℚ) / n) = 0) :
    2 * m = n := by
  unfold saw at h
  have hn : (0 : ℚ) < n := by exact_mod_cast (lt_trans hm hmn)
  have hf : Int.fract ((m : ℚ) / n) = (m : ℚ) / n := by
    rw [Int.fract_eq_self]
    exact ⟨by positivity, (div_lt_one hn).mpr (by exact_mod_cast hmn)⟩
  have hne : (m : ℚ) / n ≠ 0 := div_ne_zero (by exact_mod_cast hm.ne') hn.ne'
  rw [hf, if_neg hne] at h
  have : (2 * m : ℚ) = n := by field_simp at h; linarith
  exact_mod_cast this

/-- **Lemma R** (PROOF_lemmaS.md P2): Lemma S ⟸ Lemma P. -/
theorem lemmaR {n p : ℕ} (a : Fin 3 → ℕ) (hpos : ∀ i, 0 < a i) (hsum : ∑ i, a i = n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) (hp : p.Prime) (hpn : p ∣ n)
    (hP : ∀ e ∈ relSpace n a, ∀ j, ¬ p ∣ a j →
      ∑ k ∈ (univ.filter (fun k => ¬ p ∣ a k)).filter (fun k => a k = a j), e k = 0) :
    relSpace n a = trivSpace n a := by
  classical
  refine le_antisymm ?_ (trivSpace_le n a)
  intro e he
  set I := univ.filter (fun j : Fin 3 => ¬ p ∣ a j) with hI
  have hcl : ∀ j ∈ I, ∑ k ∈ I.filter (fun k => a k = a j), e k = 0 :=
    fun j hj => hP e he j (mem_filter.1 hj).2
  have hs3 : a 0 + a 1 + a 2 = n := by simpa [Fin.sum_univ_three] using hsum
  have hlt : ∀ i, a i < n := by
    intro i; have := hpos 0; have := hpos 1; have := hpos 2
    fin_cases i <;> simp <;> omega
  -- at most one index outside I
  have hatmost : ∀ l l', l ∉ I → l' ∉ I → l = l' := by
    intro l l' hl hl'
    by_contra hne
    have hl1 : p ∣ a l := by simpa [hI] using hl
    have hl2 : p ∣ a l' := by simpa [hI] using hl'
    have hall : ∀ i, p ∣ a i := by
      intro i
      by_cases h1 : i = l
      · rw [h1]; exact hl1
      by_cases h2 : i = l'
      · rw [h2]; exact hl2
      have huniv : ({l, l', i} : Finset (Fin 3)) = univ := by
        apply Finset.eq_univ_of_card
        rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
        all_goals first
          | rfl
          | (simp only [mem_insert, mem_singleton, not_or]
             (try constructor) <;> intro h <;> subst h <;> simp_all)
      have hsum' : a l + a l' + a i = n := by
        rw [← hsum, ← huniv, sum_insert, sum_insert, sum_singleton]
        · ring
        all_goals first
          | rfl
          | (simp only [mem_insert, mem_singleton, not_or]
             (try constructor) <;> intro h <;> subst h <;> simp_all)
      have : p ∣ a l + a l' + a i := hsum' ▸ hpn
      exact (Nat.dvd_add_right (dvd_add hl1 hl2)).1 this
    have : p ∣ Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) :=
      Nat.dvd_gcd (hall 0) (Nat.dvd_gcd (hall 1) (hall 2))
    rw [hgcd] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  -- class representatives
  let repv : ℕ → Fin 3 := fun v =>
    if h : (I.filter (fun m => a m = v)).Nonempty then (I.filter (fun m => a m = v)).min' h else 0
  have hrep : ∀ j ∈ I, repv (a j) ∈ I ∧ a (repv (a j)) = a j := by
    intro j hj
    have hne : (I.filter (fun m => a m = a j)).Nonempty := ⟨j, mem_filter.2 ⟨hj, rfl⟩⟩
    have := min'_mem _ hne
    simp only [repv, dif_pos hne]
    exact mem_filter.1 this
  -- decomposition of e
  have hdec : e = ∑ j ∈ I, e j • ((Pi.single j 1 : Fin 3 → ℚ) - Pi.single (repv (a j)) 1)
      + ∑ j ∈ I, e j • (Pi.single (repv (a j)) 1 : Fin 3 → ℚ)
      + ∑ j ∈ univ.filter (fun j => ¬ ¬ p ∣ a j), e j • (Pi.single j 1 : Fin 3 → ℚ) := by
    rw [← sum_add_distrib]
    simp only [smul_sub, sub_add_cancel]
    rw [hI, sum_filter_add_sum_filter_not]
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hmid : ∑ j ∈ I, e j • (Pi.single (repv (a j)) 1 : Fin 3 → ℚ) = 0 :=
    class_zero I a e hcl (fun j => (Pi.single (repv (a j)) 1 : Fin 3 → ℚ))
      (fun j k hjk => by simp only [hjk])
  rw [hdec, hmid, add_zero]
  refine Submodule.add_mem _ (Submodule.sum_mem _ (fun j hj => ?_)) (Submodule.sum_mem _ (fun j hj => ?_))
  · -- I-part: differences within a class
    obtain ⟨_, hra⟩ := hrep j hj
    by_cases hjr : j = repv (a j)
    · rw [← hjr, sub_self, smul_zero]; exact Submodule.zero_mem _
    · exact pair_mem hjr hra.symm (e j)
  · -- the (unique) index outside I
    have hjI : j ∉ I := by simpa [hI] using hj
    have hsing : univ.filter (fun m : Fin 3 => ¬ ¬ p ∣ a m) = {j} := by
      rw [eq_singleton_iff_unique_mem]
      exact ⟨hj, fun x hx => hatmost x j (by simpa [hI] using hx) hjI⟩
    have hk1 := (mem_relSpace.1 he) 1 (Nat.coprime_one_left n)
    simp only [one_mul] at hk1
    have hIpart : ∑ i ∈ I, e i • saw ((a i : ℕ) / (n : ℚ)) = 0 :=
      class_zero I a e hcl (fun i => saw ((a i : ℕ) / (n : ℚ))) (fun i k hik => by simp only [hik])
    have hsplit := sum_filter_add_sum_filter_not univ (fun m : Fin 3 => ¬ p ∣ a m)
      (fun i => saw ((a i : ℕ) / (n : ℚ)) * e i)
    rw [hk1, hsing, sum_singleton, ← hI] at hsplit
    have hI' : ∑ i ∈ I, saw ((a i : ℕ) / (n : ℚ)) * e i = 0 := by
      rw [← hIpart]; exact sum_congr rfl (fun i _ => by rw [smul_eq_mul, mul_comm])
    rw [hI', zero_add] at hsplit
    rcases mul_eq_zero.1 hsplit with h0 | h0
    · exact half_mem (saw_eq_zero_imp (hpos j) (hlt j) h0) (e j)
    · rw [h0, zero_smul]; exact Submodule.zero_mem _

/-! ## Witness: every hypothesis of `lemmaR` is satisfiable, at n = 21, a = (1, 6, 14), p = 7
(here one index, a₃ = 14, lies outside I; `hP` is discharged through Corollary F). -/

theorem lemmaR_witness : relSpace 21 ![1, 6, 14] = trivSpace 21 ![1, 6, 14] := by
  have hpos : ∀ i, 0 < (![1, 6, 14] : Fin 3 → ℕ) i := by intro i; fin_cases i <;> decide
  have hsum : ∑ i, (![1, 6, 14] : Fin 3 → ℕ) i = 21 := by simp [Fin.sum_univ_three]
  have hgcd : Nat.gcd ((![1, 6, 14] : Fin 3 → ℕ) 0)
      (Nat.gcd ((![1, 6, 14] : Fin 3 → ℕ) 1) ((![1, 6, 14] : Fin 3 → ℕ) 2)) = 1 := by decide
  refine lemmaR _ hpos hsum hgcd (by norm_num : Nat.Prime 7) (by norm_num) ?_
  -- hP: from Corollary F, R = R₀ = 0 here (a pairwise distinct, no 2a_i = 21)
  intro e he j _
  have hR := lemmaS_finite (Or.inl rfl) _ hpos hsum hgcd
  rw [hR] at he
  have h0 : e = 0 := by
    have hspan : trivSpace 21 ![1, 6, 14] = ⊥ := by
      unfold trivSpace
      rw [Submodule.span_eq_bot]
      rintro v (⟨i, k, hik, h, rfl⟩ | ⟨i, h, rfl⟩)
      · exfalso; fin_cases i <;> fin_cases k <;> simp_all
      · exfalso; fin_cases i <;> simp_all
    rw [hspan, Submodule.mem_bot] at he
    exact he
  simp [h0]

end Erdos634.LemmaSR

#print axioms Erdos634.LemmaSR.lemmaR
#print axioms Erdos634.LemmaSR.lemmaR_witness
