/-
# Lemma S, Lemma G2 (avoiding two values at 2 and 3)

Source: (private working notes, not included) P2 and `round2/PROOF_round2.md` §4.1:

  **Lemma G2** (p ≥ 7 prime; r ≥ 1; a, b ∈ ℂ^×). Some odd primitive ψ mod p^r has ψ(2) ≠ a and
  ψ(3) ≠ b.

Proof (round 2 §4.1): the odd ψ with ψ(2) = a lie in one coset of the characters trivial on
⟨2, −1⟩, so there are at most φ/|⟨2,−1⟩| ≤ φ/6 of them; likewise for 3; and the odd primitive
characters number more than φ/3.  Here |⟨c, −1⟩| ≥ 6 is shown by the six distinct elements
±1, ±c, ±c² (their differences have no prime factor ≥ 7), and |H|·#{χ : χ|_H = 1} = φ by
orthogonality.  The count of odd primitive ψ is bounded below by 2|O| ≥ φ(p^r) − φ(p^{r−1}).

Formalization debt only (Lemma S is PROVED at paper level); NOT /goal progress.
-/
import Mathlib
import Erdos634.Draft.LemmaSG
import Erdos634.Draft.LemmaSN

open scoped BigOperators
open Finset

namespace Erdos634.LemmaSG2Avoid

open Erdos634.LemmaSN (pred_dvd isPrimitive_iff_not_factorsThrough)

/-- `|H| · #{χ : χ = 1 on H} = φ(n)`. -/
theorem card_mul_card_triv {n : ℕ} [NeZero n] (H : Subgroup (ZMod n)ˣ) [DecidablePred (· ∈ H)] :
    Fintype.card H *
      (univ.filter (fun χ : DirichletCharacter ℂ n => ∀ h ∈ H, χ (h : ZMod n) = 1)).card
      = n.totient := by
  classical
  set K := univ.filter (fun χ : DirichletCharacter ℂ n => ∀ h ∈ H, χ (h : ZMod n) = 1) with hK
  have hsum : ∀ χ : DirichletCharacter ℂ n, ∑ h : H, χ ((h : (ZMod n)ˣ) : ZMod n)
      = if χ ∈ K then (Fintype.card H : ℂ) else 0 := by
    intro χ
    split_ifs with hχ
    · have hK' := (mem_filter.1 hχ).2
      rw [sum_congr rfl (fun h _ => hK' h.1 h.property), sum_const, card_univ, nsmul_eq_mul, mul_one]
    · simp only [hK, mem_filter, mem_univ, true_and, not_forall] at hχ
      obtain ⟨h0, hh0, hne⟩ := hχ
      set S := ∑ h : H, χ ((h : (ZMod n)ˣ) : ZMod n) with hS
      have hSS : S = χ (h0 : ZMod n) * S := by
        rw [hS]
        conv_lhs => rw [← Equiv.sum_comp (Equiv.mulLeft (⟨h0, hh0⟩ : H))]
        rw [mul_sum]
        refine sum_congr rfl (fun h _ => ?_)
        simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, Units.val_mul, map_mul]
      have : (1 - χ (h0 : ZMod n)) * S = 0 := by rw [sub_mul, one_mul, ← hSS, sub_self]
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm hne))
  have htot : ∑ χ : DirichletCharacter ℂ n, ∑ h : H, χ ((h : (ZMod n)ˣ) : ZMod n)
      = (n.totient : ℂ) := by
    rw [sum_comm]
    simp_rw [DirichletCharacter.sum_characters_eq ℂ]
    rw [sum_eq_single (1 : H)]
    · simp
    · intro h _ hne
      rw [if_neg]
      intro h1
      exact hne (Subtype.ext (Units.ext (by simpa using h1)))
    · intro h; exact absurd (mem_univ _) h
  simp_rw [hsum] at htot
  rw [← sum_filter, filter_mem_eq_inter, univ_inter, sum_const, nsmul_eq_mul] at htot
  have : ((Fintype.card H * K.card : ℕ) : ℂ) = (n.totient : ℂ) := by push_cast; rw [← htot]; ring
  exact_mod_cast this

/-- Small differences are not divisible by p^r when p ≥ 7. -/
theorem not_dvd_small {p r : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hr : 1 ≤ r) (d : ℤ) (hd0 : d ≠ 0)
    (hdb : d.natAbs ≤ 18) (h7 : ¬ (7 : ℤ) ∣ d) (h11 : ¬ (11 : ℤ) ∣ d) (h13 : ¬ (13 : ℤ) ∣ d)
    (h17 : ¬ (17 : ℤ) ∣ d) : ¬ ((p ^ r : ℕ) : ℤ) ∣ d := by
  intro h
  have hpd : (p : ℤ) ∣ d :=
    dvd_trans (by exact_mod_cast dvd_pow_self p (by omega : r ≠ 0)) h
  have hle : p ≤ d.natAbs := Nat.le_of_dvd (Int.natAbs_pos.2 hd0) (Int.natCast_dvd.1 hpd)
  have hp18 : p ≤ 18 := le_trans hle hdb
  interval_cases p <;> first | exact h7 (by exact_mod_cast hpd) | exact h11 (by exact_mod_cast hpd) | exact h13 (by exact_mod_cast hpd) | exact h17 (by exact_mod_cast hpd) | (exfalso; norm_num at hp)

/-- Six distinct elements `±1, ±c, ±c²` of ⟨c, −1⟩ give |⟨c, −1⟩| ≥ 6. -/
theorem six_le_card {p r : ℕ} [hp : Fact p.Prime] (hp7 : 7 ≤ p) (hr : 1 ≤ r) (c : ℤ)
    (hc : c = 2 ∨ c = 3) (u : (ZMod (p ^ r))ˣ) (hu : (u : ZMod (p ^ r)) = (c : ZMod (p ^ r)))
    (H : Subgroup (ZMod (p ^ r))ˣ) [DecidablePred (· ∈ H)] (huH : u ∈ H) (hmH : (-1 : (ZMod (p ^ r))ˣ) ∈ H) :
    6 ≤ Fintype.card H := by
  classical
  set L : List (ZMod (p ^ r))ˣ := [1, u, u * u, -1, -u, -(u * u)] with hL
  have hvals : L.map (fun v : (ZMod (p ^ r))ˣ => (v : ZMod (p ^ r)))
      = ([1, c, c * c, -1, -c, -(c * c)] : List ℤ).map (fun z : ℤ => (z : ZMod (p ^ r))) := by
    simp [hL, hu]
  have hinj : ∀ x ∈ ([1, c, c * c, -1, -c, -(c * c)] : List ℤ),
      ∀ y ∈ ([1, c, c * c, -1, -c, -(c * c)] : List ℤ),
      (x : ZMod (p ^ r)) = (y : ZMod (p ^ r)) → x = y := by
    intro x hx y hy hxy
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hxy
    by_contra hne
    have hd0 : y - x ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hc with rfl | rfl <;>
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact hne rfl
      | exact not_dvd_small hp.out hp7 hr _ hd0 (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) hxy
  have hndZ : ([1, c, c * c, -1, -c, -(c * c)] : List ℤ).Nodup := by
    rcases hc with rfl | rfl <;> decide
  have hnd : L.Nodup := by
    have h1 := List.Nodup.map_on hinj hndZ
    have h2 : (L.map (fun v : (ZMod (p ^ r))ˣ => (v : ZMod (p ^ r)))).Nodup := by
      rw [hvals]; exact h1
    exact List.Nodup.of_map _ h2
  have hsub : L.toFinset ⊆ univ.filter (· ∈ H) := by
    intro v hv
    rw [List.mem_toFinset] at hv
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    have hmu : -u ∈ H := by rw [← neg_one_mul]; exact H.mul_mem hmH huH
    have hmuu : -(u * u) ∈ H := by rw [← neg_one_mul]; exact H.mul_mem hmH (H.mul_mem huH huH)
    simp only [hL, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact H.one_mem
    · exact huH
    · exact H.mul_mem huH huH
    · exact hmH
    · exact hmu
    · exact hmuu
  have := card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd] at this
  rw [Fintype.card_subtype]
  simpa [hL] using this

theorem coprime_small {p r : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (c : ℕ) (hc : c = 2 ∨ c = 3) :
    c.Coprime (p ^ r) := by
  apply Nat.Coprime.pow_right
  rcases hc with rfl | rfl
  · exact (Nat.coprime_primes Nat.prime_two hp).2 (by omega)
  · exact (Nat.coprime_primes Nat.prime_three hp).2 (by omega)

/-- The characters of a fixed value at a unit `u` and parity −1, relative to one of them,
are trivial on ⟨u, −1⟩: at most φ/6 of them. -/
theorem card_fixed_le {p r : ℕ} [hp : Fact p.Prime] (hp7 : 7 ≤ p) (hr : 1 ≤ r) (c : ℕ)
    (hc : c = 2 ∨ c = 3) (S : Finset (DirichletCharacter ℂ (p ^ r))) (z : ℂ)
    (hS : ∀ ψ ∈ S, ψ (-1) = -1 ∧ ψ (c : ZMod (p ^ r)) = z) :
    6 * S.card ≤ (p ^ r).totient := by
  classical
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rcases S.eq_empty_or_nonempty with h | ⟨ψ0, hψ0⟩
  · rw [h]; simp
  set u : (ZMod (p ^ r))ˣ := ZMod.unitOfCoprime c (coprime_small hp.out hp7 c hc) with hu
  have hucoe : (u : ZMod (p ^ r)) = (c : ZMod (p ^ r)) := ZMod.coe_unitOfCoprime _ _
  set H := Subgroup.closure ({u, -1} : Set (ZMod (p ^ r))ˣ) with hH
  have huH : u ∈ H := Subgroup.subset_closure (by simp)
  have hmH : (-1 : (ZMod (p ^ r))ˣ) ∈ H := Subgroup.subset_closure (by simp)
  have h6 : 6 ≤ Fintype.card H := by
    refine six_le_card hp7 hr (c : ℤ) (by rcases hc with rfl | rfl <;> simp) u
      (by rw [hucoe]; simp) H huH hmH
  set K := univ.filter (fun χ : DirichletCharacter ℂ (p ^ r) => ∀ h ∈ H, χ (h : ZMod (p ^ r)) = 1)
  have hHK := card_mul_card_triv H
  -- S injects into K via ψ ↦ ψ · ψ0⁻¹
  have hSK : S.card ≤ K.card := by
    refine card_le_card_of_injOn (fun ψ => ψ * ψ0⁻¹) ?_ ?_
    · intro ψ hψ
      rw [Finset.mem_coe, mem_filter]
      refine ⟨mem_univ _, ?_⟩
      intro h hh
      have hle : H ≤ (ψ * ψ0⁻¹).toUnitHom.ker := by
        rw [hH, Subgroup.closure_le]
        intro v hv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
        rw [SetLike.mem_coe, MonoidHom.mem_ker]
        apply Units.ext
        rw [MulChar.coe_toUnitHom, Units.val_one]
        obtain ⟨h1, h2⟩ := hS ψ hψ
        obtain ⟨h1', h2'⟩ := hS ψ0 hψ0
        have hz : z ≠ 0 := by
          rw [← h2', ← hucoe]
          intro h0
          have := ψ0.unit_norm_eq_one u
          rw [h0, norm_zero] at this
          exact zero_ne_one this
        rcases hv with rfl | rfl
        · show ψ (u : ZMod (p ^ r)) * ψ0⁻¹ (u : ZMod (p ^ r)) = 1
          rw [MulChar.inv_apply_eq_inv', hucoe, h2, h2', mul_inv_cancel₀ hz]
        · show ψ ((-1 : (ZMod (p ^ r))ˣ) : ZMod (p ^ r)) * ψ0⁻¹ ((-1 : (ZMod (p ^ r))ˣ) : ZMod (p ^ r)) = 1
          rw [MulChar.inv_apply_eq_inv', Units.val_neg, Units.val_one, h1, h1']; norm_num
      have := hle hh
      rw [MonoidHom.mem_ker] at this
      have := congrArg Units.val this
      rwa [MulChar.coe_toUnitHom, Units.val_one] at this
    · intro x _ y _ hxy
      exact mul_right_cancel hxy
  have : 6 * K.card ≤ (p ^ r).totient := by rw [← hHK]; exact Nat.mul_le_mul_right _ h6
  omega

theorem changeLevel_neg_one' {m n : ℕ} [NeZero n] (h : m ∣ n) (ψ : DirichletCharacter ℂ m) :
    DirichletCharacter.changeLevel h ψ (-1) = ψ (-1) := by
  have h1 := DirichletCharacter.changeLevel_eq_cast_of_dvd ψ h (-1)
  simp only [Units.val_neg, Units.val_one] at h1
  rw [h1, ZMod.cast_neg h, ZMod.cast_one h]

open Classical in
/-- Lower bound for the number of odd primitive characters mod p^r:
`φ(p^r) ≤ 2·#{odd primitive} + φ(p^(r−1))`. -/
theorem card_odd_prim_lower {p r : ℕ} [hp : Fact p.Prime] (hp7 : 7 ≤ p) (hr : 1 ≤ r) :
    (p ^ r).totient ≤
      2 * ((univ.filter (fun ψ : DirichletCharacter ℂ (p ^ r) => ψ (-1) = -1)).filter
        (fun ψ => ψ.IsPrimitive)).card + (p ^ (r - 1)).totient := by
  classical
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  haveI : NeZero (p ^ (r - 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hq7 : 7 ≤ p ^ r := le_trans hp7 (Nat.le_self_pow (by omega) p)
  haveI : Fact (2 < p ^ r) := ⟨by omega⟩
  have hm1 : (-1 : ZMod (p ^ r)) ≠ 1 := ZMod.neg_one_ne_one
  have hd := pred_dvd p r
  set X := univ.filter (fun ψ : DirichletCharacter ℂ (p ^ r) => ψ (-1) = -1) with hX
  set X' := univ.filter (fun ψ : DirichletCharacter ℂ (p ^ (r - 1)) => ψ (-1) = -1) with hX'
  -- 2|X| = φ(p^r)
  have hP := Erdos634.LemmaSG.parity_sum (-1) (Or.inr rfl) (1 : ZMod (p ^ r))
  rw [DirichletCharacter.sum_characters_eq ℂ, DirichletCharacter.sum_characters_eq ℂ, if_pos rfl,
    if_neg hm1, mul_zero, add_zero, ← hX] at hP
  simp only [MulChar.map_one, mul_one, sum_const, nsmul_eq_mul] at hP
  have hXc : 2 * X.card = (p ^ r).totient := by
    have : ((2 * X.card : ℕ) : ℂ) = ((p ^ r).totient : ℂ) := by push_cast; rw [← hP]; ring
    exact_mod_cast this
  -- 2|X'| ≤ φ(p^(r−1))
  have hP' := Erdos634.LemmaSG.parity_sum (-1) (Or.inr rfl) (1 : ZMod (p ^ (r - 1)))
  rw [DirichletCharacter.sum_characters_eq ℂ, DirichletCharacter.sum_characters_eq ℂ, if_pos rfl,
    ← hX'] at hP'
  simp only [MulChar.map_one, mul_one, sum_const, nsmul_eq_mul] at hP'
  have hX'c : 2 * X'.card ≤ (p ^ (r - 1)).totient := by
    by_cases h1 : (-1 : ZMod (p ^ (r - 1))) = 1
    · rw [if_pos h1] at hP'
      have : ((2 * X'.card : ℕ) : ℂ) = 0 := by push_cast; linear_combination hP'
      have : 2 * X'.card = 0 := by exact_mod_cast this
      omega
    · rw [if_neg h1, mul_zero, add_zero] at hP'
      have : ((2 * X'.card : ℕ) : ℂ) = ((p ^ (r - 1)).totient : ℂ) := by
        push_cast; linear_combination hP'
      have : 2 * X'.card = (p ^ (r - 1)).totient := by exact_mod_cast this
      omega
  -- non-primitive odd characters come from level p^(r−1)
  have hsub : X.filter (fun ψ => ¬ ψ.IsPrimitive) ⊆ X'.image (DirichletCharacter.changeLevel hd) := by
    intro ψ hψ
    obtain ⟨hψX, hnp⟩ := mem_filter.1 hψ
    have hpar := (mem_filter.1 hψX).2
    have hf : ψ.FactorsThrough (p ^ (r - 1)) :=
      not_not.1 (fun h' => hnp ((isPrimitive_iff_not_factorsThrough hr ψ).2 h'))
    have heq := hf.eq_changeLevel
    rw [mem_image]
    refine ⟨hf.χ₀, mem_filter.2 ⟨mem_univ _, ?_⟩, heq.symm⟩
    rw [← changeLevel_neg_one' hd, ← heq]; exact hpar
  have hc1 := card_le_card hsub
  have hc2 := card_image_le (s := X') (f := DirichletCharacter.changeLevel hd)
  have hsplit := card_filter_add_card_filter_not (s := X) (fun ψ => ψ.IsPrimitive)
  omega

/-- `(p − 1)·φ(p^(r−1)) ≤ φ(p^r)`. -/
theorem totient_pred_le {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r) :
    (p - 1) * (p ^ (r - 1)).totient ≤ (p ^ r).totient := by
  rcases Nat.lt_or_ge r 2 with h | h
  · obtain rfl : r = 1 := by omega
    simp [Nat.totient_prime hp]
  · have htot : (p ^ r).totient = p * (p ^ (r - 1)).totient := by
      rw [show p ^ r = p * p ^ (r - 1) by rw [← pow_succ']; congr 1; omega]
      exact Nat.totient_mul_of_prime_of_dvd hp (dvd_pow_self p (by omega))
    rw [htot]
    exact Nat.mul_le_mul_right _ (Nat.sub_le p 1)

/-- **Lemma G2** (PROOF_lemmaS.md P2), as written: p ≥ 7 prime, r ≥ 1, a, b ∈ ℂ^×. -/
theorem lemmaG2 {p r : ℕ} [hp : Fact p.Prime] (hp7 : 7 ≤ p) (hr : 1 ≤ r) (a b : ℂ)
    (_ha : a ≠ 0) (_hb : b ≠ 0) :
    ∃ ψ : DirichletCharacter ℂ (p ^ r), ψ.IsPrimitive ∧ ψ.Odd ∧
      ψ (2 : ZMod (p ^ r)) ≠ a ∧ ψ (3 : ZMod (p ^ r)) ≠ b := by
  classical
  set O := (univ.filter (fun ψ : DirichletCharacter ℂ (p ^ r) => ψ (-1) = -1)).filter
    (fun ψ => ψ.IsPrimitive) with hO
  set B2 := O.filter (fun ψ => ψ (2 : ZMod (p ^ r)) = a) with hB2
  set B3 := O.filter (fun ψ => ψ (3 : ZMod (p ^ r)) = b) with hB3
  have hmemO : ∀ ψ ∈ O, ψ (-1) = -1 ∧ ψ.IsPrimitive := by
    intro ψ hψ
    obtain ⟨h1, h2⟩ := mem_filter.1 hψ
    exact ⟨(mem_filter.1 h1).2, h2⟩
  have h2 : 6 * B2.card ≤ (p ^ r).totient := by
    refine card_fixed_le hp7 hr 2 (Or.inl rfl) B2 a (fun ψ hψ => ?_)
    obtain ⟨hψO, hψa⟩ := mem_filter.1 hψ
    exact ⟨(hmemO ψ hψO).1, by simpa using hψa⟩
  have h3 : 6 * B3.card ≤ (p ^ r).totient := by
    refine card_fixed_le hp7 hr 3 (Or.inr rfl) B3 b (fun ψ hψ => ?_)
    obtain ⟨hψO, hψb⟩ := mem_filter.1 hψ
    exact ⟨(hmemO ψ hψO).1, by simpa using hψb⟩
  have hlow := card_odd_prim_lower (p := p) hp7 hr
  rw [← hO] at hlow
  have hpred := totient_pred_le hp.out hr
  have hφ : 0 < (p ^ r).totient := Nat.totient_pos.2 (pow_pos hp.out.pos r)
  have hlt : (B2 ∪ B3).card < O.card := by
    refine lt_of_le_of_lt (card_union_le B2 B3) ?_
    by_contra hge
    push Not at hge
    -- φ ≤ 3 φ'
    have h4 : (p ^ r).totient ≤ 3 * (p ^ (r - 1)).totient := by omega
    have h5 : (p - 1) * (p ^ r).totient ≤ 3 * (p ^ r).totient := by
      calc (p - 1) * (p ^ r).totient ≤ (p - 1) * (3 * (p ^ (r - 1)).totient) :=
            Nat.mul_le_mul_left _ h4
        _ = 3 * ((p - 1) * (p ^ (r - 1)).totient) := by ring
        _ ≤ 3 * (p ^ r).totient := Nat.mul_le_mul_left _ hpred
    have := Nat.le_of_mul_le_mul_right h5 hφ
    omega
  obtain ⟨ψ, hψO, hψn⟩ := exists_mem_notMem_of_card_lt_card hlt
  obtain ⟨hodd, hprim⟩ := hmemO ψ hψO
  refine ⟨ψ, hprim, hodd, fun h => hψn (mem_union_left _ (mem_filter.2 ⟨hψO, h⟩)),
    fun h => hψn (mem_union_right _ (mem_filter.2 ⟨hψO, h⟩))⟩

/-- Witness: G2 fires at p = 7, r = 2 with a = b = 1 (genuine data; the conclusion is a real
odd primitive character mod 49 avoiding 1 at both 2 and 3). -/
theorem lemmaG2_witness : ∃ ψ : DirichletCharacter ℂ (7 ^ 2), ψ.IsPrimitive ∧ ψ.Odd ∧
    ψ (2 : ZMod (7 ^ 2)) ≠ 1 ∧ ψ (3 : ZMod (7 ^ 2)) ≠ 1 :=
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  lemmaG2 (p := 7) (r := 2) le_rfl (by norm_num) 1 1 one_ne_zero one_ne_zero

end Erdos634.LemmaSG2Avoid

#print axioms Erdos634.LemmaSG2Avoid.card_mul_card_triv
#print axioms Erdos634.LemmaSG2Avoid.lemmaG2
#print axioms Erdos634.LemmaSG2Avoid.lemmaG2_witness
