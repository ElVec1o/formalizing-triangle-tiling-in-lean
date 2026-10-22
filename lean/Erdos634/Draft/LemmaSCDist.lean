/-
# Lemma S, Lemma C — steps 3–4: distribution relation and Möbius (inclusion–exclusion) sieve

Source: (private working notes, not included) §3.1 steps 3–4.

* Step 3 (distribution relation): for ω a Dirichlet character mod f and M = f·k,
  `Σ_{x mod M} ω(x)((x/M)) = B_{1,ω} := Σ_{y mod f} ω(y)((y/f))`   (`A_eq`).
  Primitivity is NOT needed for this step (it holds for every ω of level f).
* Step 4 (Möbius inversion over d | M, done as inclusion–exclusion over the primes of M not
  dividing f): `Σ_{(x,M)=1} ω(x)((x/M)) = B_{1,ω} · ∏_{ℓ | M, ℓ ∤ f} (1 − ω(ℓ))`  (`T_eq`),
  and the same sum written over `(ZMod M)ˣ` with the level-M character `ω.changeLevel`
  (`sum_units_changeLevel`).

Formalization debt only (Lemma S is PROVED at paper level); not /goal progress.
-/
import Mathlib
import Erdos634.Draft.CaseACorF

open scoped BigOperators
open Finset

namespace Erdos634.LemmaSC

open Erdos634.LemmaS (saw)

/-- `((x/M))` as a complex number. -/
noncomputable def sN (M x : ℕ) : ℂ := ((saw ((x : ℚ) / M) : ℚ) : ℂ)

theorem saw_add_nat (t : ℚ) (m : ℕ) : saw (t + m) = saw t := by
  unfold saw; rw [Int.fract_add_natCast]

theorem sN_mod (M x : ℕ) : sN M x = sN M (x % M) := by
  unfold sN
  congr 1
  rcases Nat.eq_zero_or_pos M with h | h
  · subst h; simp
  · have hM : (M : ℚ) ≠ 0 := by exact_mod_cast h.ne'
    have hq : (x : ℚ) = ((x % M : ℕ) : ℚ) + (M : ℚ) * ((x / M : ℕ) : ℚ) := by
      exact_mod_cast (Nat.mod_add_div x M).symm
    rw [hq, add_div, mul_div_cancel_left₀ _ hM, saw_add_nat]

theorem sN_mul {d : ℕ} (hd : 0 < d) (M y : ℕ) : sN (d * M) (d * y) = sN M y := by
  unfold sN
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  push_cast
  rw [mul_div_mul_left _ _ hd']

theorem sN_lt {M x : ℕ} (hx : x < M) :
    sN M x = if x = 0 then 0 else (x : ℂ) / M - 1 / 2 := by
  unfold sN saw
  have hM : (0 : ℚ) < M := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le x) hx)
  have hf : Int.fract ((x : ℚ) / M) = (x : ℚ) / M := by
    rw [Int.fract_eq_self]
    exact ⟨by positivity, (div_lt_one hM).mpr (by exact_mod_cast hx)⟩
  rw [hf]
  by_cases h0 : x = 0
  · subst h0; simp
  · have hne : (x : ℚ) / M ≠ 0 := div_ne_zero (by exact_mod_cast h0) hM.ne'
    rw [if_neg hne, if_neg h0]
    push_cast; ring

/-- Splitting `range (f*k)` into `k` blocks of length `f`. -/
theorem sum_range_mul_block (G : ℕ → ℂ) (f k : ℕ) :
    ∑ x ∈ range (f * k), G x = ∑ t ∈ range k, ∑ y ∈ range f, G (f * t + y) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]

theorem sum_range_cast_mul_two (m : ℕ) : (∑ t ∈ range m, (t : ℂ)) * 2 = m * ((m : ℂ) - 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, add_mul, ih]; push_cast; ring

/-- **Distribution relation** `Σ_{t<k} (((y + f t)/(f k))) = ((y/f))` for `0 ≤ y < f`. -/
theorem dist {f k y : ℕ} (hk : 0 < k) (hy : y < f) :
    ∑ t ∈ range k, sN (f * k) (f * t + y) = sN f y := by
  have hf : 0 < f := lt_of_le_of_lt (Nat.zero_le y) hy
  have hlt : ∀ t ∈ range k, f * t + y < f * k := by
    intro t ht
    have := mem_range.1 ht
    calc f * t + y < f * t + f := by omega
      _ = f * (t + 1) := by ring
      _ ≤ f * k := Nat.mul_le_mul_left f this
  have hfC : (f : ℂ) ≠ 0 := by exact_mod_cast hf.ne'
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hS := sum_range_cast_mul_two k
  by_cases hy0 : y = 0
  · subst hy0
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [sum_range_succ']
    have hterm : ∀ t ∈ range k', sN (f * (k' + 1)) (f * (t + 1) + 0)
        = (t : ℂ) * (1 / ((k' : ℂ) + 1)) + (1 / ((k' : ℂ) + 1) - 1 / 2) := by
      intro t ht
      rw [sN_lt (hlt (t + 1) (by simp at ht ⊢; omega)), if_neg (by positivity)]
      have hk1 : (k' : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k')
      push_cast; field_simp; ring
    rw [sum_congr rfl hterm, sum_add_distrib, ← sum_mul, sum_const, card_range, nsmul_eq_mul,
      show f * 0 + 0 = 0 by simp, sN_lt (show 0 < f * (k' + 1) by positivity), if_pos rfl,
      sN_lt hy, if_pos rfl, add_zero]
    have hS' := sum_range_cast_mul_two k'
    have hk1 : (k' : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k')
    have : (∑ t ∈ range k', (t : ℂ)) = k' * ((k' : ℂ) - 1) / 2 := by
      rw [eq_div_iff (two_ne_zero)]; exact hS'
    rw [this]; field_simp; ring
  · have hterm : ∀ t ∈ range k, sN (f * k) (f * t + y)
        = (t : ℂ) * (1 / k) + ((y : ℂ) / (f * k) - 1 / 2) := by
      intro t ht
      rw [sN_lt (hlt t ht), if_neg (by omega)]
      push_cast; field_simp; ring
    rw [sum_congr rfl hterm, sum_add_distrib, ← sum_mul, sum_const, card_range, nsmul_eq_mul,
      sN_lt hy, if_neg hy0]
    have : (∑ t ∈ range k, (t : ℂ)) = k * ((k : ℂ) - 1) / 2 := by
      rw [eq_div_iff (two_ne_zero)]; exact hS
    rw [this]; field_simp; ring

/-- `B_{1,ω} := Σ_{y mod f} ω(y)((y/f))` — the same expression as in `LemmaSB1Hurwitz.B1`. -/
noncomputable def B {f : ℕ} [NeZero f] (ω : DirichletCharacter ℂ f) : ℂ :=
  ∑ y : ZMod f, ω y * ((saw ((y.val : ℚ) / f) : ℚ) : ℂ)

theorem sum_zmod_eq_range {f : ℕ} [NeZero f] (G : ZMod f → ℂ) :
    ∑ y : ZMod f, G y = ∑ i ∈ range f, G (i : ZMod f) := by
  refine Finset.sum_nbij' (fun y => y.val) (fun i => (i : ZMod f)) ?_ ?_ ?_ ?_ ?_
  · intro y _; simp [ZMod.val_lt]
  · intro i _; simp
  · intro y _; simp
  · intro i hi; simp [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.1 hi)]
  · intro y _; simp

theorem B_eq_range {f : ℕ} [NeZero f] (ω : DirichletCharacter ℂ f) :
    B ω = ∑ i ∈ range f, ω (i : ZMod f) * sN f i := by
  unfold B
  rw [sum_zmod_eq_range]
  refine sum_congr rfl (fun i hi => ?_)
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.1 hi)]
  rfl

/-- `A(M) := Σ_{x mod M} ω(x mod f)((x/M))`. -/
noncomputable def A {f : ℕ} (ω : DirichletCharacter ℂ f) (M : ℕ) : ℂ :=
  ∑ x ∈ range M, ω (x : ZMod f) * sN M x

/-- **Step 3.** `A(f k) = B_{1,ω}` for `k ≥ 1`. -/
theorem A_eq {f k : ℕ} [NeZero f] (ω : DirichletCharacter ℂ f) (hk : 0 < k) :
    A ω (f * k) = B ω := by
  unfold A
  rw [sum_range_mul_block, sum_comm, B_eq_range]
  refine sum_congr rfl (fun y hy => ?_)
  have hω : ∀ t, ω (((f * t + y : ℕ)) : ZMod f) = ω (y : ZMod f) := by
    intro t; push_cast; rw [ZMod.natCast_self, zero_mul, zero_add]
  simp_rw [hω, ← mul_sum]
  rw [dist hk (mem_range.1 hy)]

/-- `∏_{ℓ∈P} (1 − c ℓ) = Σ_{D ⊆ P} (−1)^{|D|} ∏_{ℓ∈D} c ℓ`. -/
theorem prod_one_sub (P : Finset ℕ) (c : ℕ → ℂ) :
    ∏ ℓ ∈ P, (1 - c ℓ) = ∑ D ∈ P.powerset, (-1 : ℂ) ^ D.card * ∏ ℓ ∈ D, c ℓ := by
  have h := Finset.prod_add (fun ℓ => -c ℓ) (fun _ => (1 : ℂ)) P
  simp only [prod_const_one, mul_one] at h
  rw [show ∏ ℓ ∈ P, (1 - c ℓ) = ∏ ℓ ∈ P, (-c ℓ + 1) from prod_congr rfl (fun _ _ => by ring), h]
  refine sum_congr rfl (fun D _ => ?_)
  rw [show ∏ ℓ ∈ D, -c ℓ = ∏ ℓ ∈ D, ((-1) * c ℓ) from prod_congr rfl (fun _ _ => by ring),
    prod_mul_distrib, prod_const]

theorem prod_ind {D : Finset ℕ} (hD : ∀ ℓ ∈ D, ℓ.Prime) (x : ℕ) :
    ∏ ℓ ∈ D, (if ℓ ∣ x then (1 : ℂ) else 0) = if (∏ ℓ ∈ D, ℓ) ∣ x then 1 else 0 := by
  by_cases h : ∀ ℓ ∈ D, ℓ ∣ x
  · rw [prod_eq_one (fun ℓ hℓ => if_pos (h ℓ hℓ)), if_pos]
    exact Finset.prod_primes_dvd x (fun ℓ hℓ => (hD ℓ hℓ).prime) h
  · push Not at h
    obtain ⟨ℓ, hℓ, hn⟩ := h
    rw [prod_eq_zero hℓ (if_neg hn), if_neg]
    exact fun hd => hn (dvd_trans (dvd_prod_of_mem _ hℓ) hd)

/-- The sieve's inner sum: restricting to multiples of `d` (coprime to `f`) gives `ω(d)·B`. -/
theorem inner {f d M : ℕ} [NeZero f] (ω : DirichletCharacter ℂ f) (hd : 0 < d) (hdM : d ∣ M)
    (hcop : d.Coprime f) (hfM : f ∣ M) (hM : 0 < M) :
    ∑ x ∈ range M, (if d ∣ x then (1 : ℂ) else 0) * ω (x : ZMod f) * sN M x
      = ω (d : ZMod f) * B ω := by
  obtain ⟨M', rfl⟩ := hdM
  have hfM' : f ∣ M' := hcop.symm.dvd_of_dvd_mul_left hfM
  obtain ⟨k, rfl⟩ := hfM'
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hM
    · exact h
  rw [sum_range_mul_block]
  have hin : ∀ t ∈ range (f * k), ∑ r ∈ range d,
      (if d ∣ d * t + r then (1 : ℂ) else 0) * ω ((d * t + r : ℕ) : ZMod f) * sN (d * (f * k)) (d * t + r)
      = ω (d : ZMod f) * (ω (t : ZMod f) * sN (f * k) t) := by
    intro t _
    rw [Finset.sum_eq_single 0]
    · rw [add_zero, if_pos (dvd_mul_right d t), one_mul, sN_mul hd]
      push_cast; rw [map_mul]; ring
    · intro r hr hr0
      rw [if_neg, zero_mul, zero_mul]
      intro hdv
      have : d ∣ r := (Nat.dvd_add_right (dvd_mul_right d t)).mp hdv
      exact hr0 (Nat.eq_zero_of_dvd_of_lt this (mem_range.1 hr))
    · intro h; exact absurd (mem_range.2 hd) h
  rw [sum_congr rfl hin, ← mul_sum]
  change ω (d : ZMod f) * A ω (f * k) = _
  rw [A_eq ω hk]

/-- The set of primes `ℓ | M` with `ℓ ∤ f` (the Euler primes). -/
def eulerPrimes (M f : ℕ) : Finset ℕ := M.primeFactors.filter (fun ℓ => ¬ ℓ ∣ f)

/-- **Step 4 (over ℕ).** `Σ_{x<M, (x,M)=1} ω(x)((x/M)) = B_{1,ω} ∏_{ℓ|M, ℓ∤f} (1 − ω(ℓ))`. -/
theorem T_eq {f M : ℕ} [NeZero f] (ω : DirichletCharacter ℂ f) (hfM : f ∣ M) (hM : 0 < M) :
    ∑ x ∈ range M, (if x.Coprime M then ω (x : ZMod f) else 0) * sN M x
      = B ω * ∏ ℓ ∈ eulerPrimes M f, (1 - ω (ℓ : ZMod f)) := by
  set P := eulerPrimes M f with hP
  have hPmem : ∀ ℓ ∈ P, ℓ.Prime ∧ ℓ ∣ M ∧ ¬ ℓ ∣ f := by
    intro ℓ hℓ
    obtain ⟨h1, h2⟩ := mem_filter.1 hℓ
    exact ⟨Nat.prime_of_mem_primeFactors h1, Nat.dvd_of_mem_primeFactors h1, h2⟩
  have key : ∀ x, (if x.Coprime M then ω (x : ZMod f) else 0)
      = (∏ ℓ ∈ P, (1 - if ℓ ∣ x then (1 : ℂ) else 0)) * ω (x : ZMod f) := by
    intro x
    by_cases hc : x.Coprime M
    · rw [if_pos hc, prod_eq_one, one_mul]
      intro ℓ hℓ
      obtain ⟨hp, hℓM, _⟩ := hPmem ℓ hℓ
      rw [if_neg, sub_zero]
      intro hdx
      have := Nat.dvd_gcd hdx hℓM
      rw [Nat.Coprime.gcd_eq_one hc] at this
      exact hp.not_dvd_one this
    · rw [if_neg hc]
      have hg : Nat.gcd x M ≠ 1 := hc
      have hp := Nat.minFac_prime hg
      have hℓx : (Nat.gcd x M).minFac ∣ x := dvd_trans (Nat.minFac_dvd _) (Nat.gcd_dvd_left x M)
      have hℓM : (Nat.gcd x M).minFac ∣ M := dvd_trans (Nat.minFac_dvd _) (Nat.gcd_dvd_right x M)
      by_cases hℓf : (Nat.gcd x M).minFac ∣ f
      · rw [MulChar.map_nonunit ω, mul_zero]
        rw [ZMod.isUnit_iff_coprime]
        intro hcop
        have := Nat.dvd_gcd hℓx hℓf
        rw [Nat.Coprime.gcd_eq_one hcop] at this
        exact hp.not_dvd_one this
      · rw [prod_eq_zero (i := (Nat.gcd x M).minFac), zero_mul]
        · exact mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hp, hℓM, hM.ne'⟩, hℓf⟩
        · rw [if_pos hℓx, sub_self]
  have hDprops : ∀ D ∈ P.powerset, 0 < ∏ ℓ ∈ D, ℓ ∧ (∏ ℓ ∈ D, ℓ) ∣ M ∧ (∏ ℓ ∈ D, ℓ).Coprime f
      ∧ ∀ ℓ ∈ D, ℓ.Prime := by
    intro D hD
    have hsub := mem_powerset.1 hD
    have hpr : ∀ ℓ ∈ D, ℓ.Prime := fun ℓ hℓ => (hPmem ℓ (hsub hℓ)).1
    refine ⟨prod_pos (fun ℓ hℓ => (hpr ℓ hℓ).pos), ?_, ?_, hpr⟩
    · exact Finset.prod_primes_dvd M (fun ℓ hℓ => (hpr ℓ hℓ).prime)
        (fun ℓ hℓ => (hPmem ℓ (hsub hℓ)).2.1)
    · exact Nat.Coprime.prod_left (fun ℓ hℓ =>
        (Nat.Prime.coprime_iff_not_dvd (hpr ℓ hℓ)).2 (hPmem ℓ (hsub hℓ)).2.2)
  calc ∑ x ∈ range M, (if x.Coprime M then ω (x : ZMod f) else 0) * sN M x
      = ∑ x ∈ range M, ∑ D ∈ P.powerset, (-1 : ℂ) ^ D.card *
          ((if (∏ ℓ ∈ D, ℓ) ∣ x then (1 : ℂ) else 0) * ω (x : ZMod f) * sN M x) := by
        refine sum_congr rfl (fun x _ => ?_)
        rw [key, prod_one_sub, sum_mul, sum_mul]
        refine sum_congr rfl (fun D hD => ?_)
        rw [prod_ind (hDprops D hD).2.2.2]
        ring
    _ = ∑ D ∈ P.powerset, (-1 : ℂ) ^ D.card * ∑ x ∈ range M,
          (if (∏ ℓ ∈ D, ℓ) ∣ x then (1 : ℂ) else 0) * ω (x : ZMod f) * sN M x := by
        rw [sum_comm]
        refine sum_congr rfl (fun D _ => ?_)
        rw [mul_sum]
    _ = ∑ D ∈ P.powerset, (-1 : ℂ) ^ D.card * (ω ((∏ ℓ ∈ D, ℓ : ℕ) : ZMod f) * B ω) := by
        refine sum_congr rfl (fun D hD => ?_)
        obtain ⟨h1, h2, h3, _⟩ := hDprops D hD
        rw [inner ω h1 h2 h3 hfM hM]
    _ = B ω * ∏ ℓ ∈ P, (1 - ω (ℓ : ZMod f)) := by
        rw [prod_one_sub, mul_sum]
        refine sum_congr rfl (fun D _ => ?_)
        rw [Nat.cast_prod, map_prod]
        ring

/-- Sum over units = sum over all residues, for a function killed by `χ` off the units. -/
theorem sum_units_eq_sum {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (F : ZMod M → ℂ) :
    ∑ u : (ZMod M)ˣ, χ u * F u = ∑ x : ZMod M, χ x * F x := by
  symm
  rw [← Finset.sum_subset (Finset.subset_univ
    (Finset.univ.map ⟨(Units.val : (ZMod M)ˣ → ZMod M), Units.val_injective⟩))]
  · rw [Finset.sum_map]; rfl
  · intro x _ hx
    have : ¬ IsUnit x := by
      rintro ⟨u, rfl⟩
      exact hx (by simp)
    rw [MulChar.map_nonunit χ this, zero_mul]

/-- **Step 4 (units form).** For `ω` of level `f ∣ M`,
`Σ_{u ∈ (ℤ/M)^×} ω(u)((u/M)) = B_{1,ω} ∏_{ℓ|M, ℓ∤f} (1 − ω(ℓ))`. -/
theorem sum_units_changeLevel {f M : ℕ} [NeZero f] [NeZero M] (ω : DirichletCharacter ℂ f)
    (hfM : f ∣ M) :
    ∑ u : (ZMod M)ˣ, DirichletCharacter.changeLevel hfM ω (u : ZMod M) * sN M (u : ZMod M).val
      = B ω * ∏ ℓ ∈ eulerPrimes M f, (1 - ω (ℓ : ZMod f)) := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  rw [sum_units_eq_sum (DirichletCharacter.changeLevel hfM ω) (fun x => sN M x.val),
    sum_zmod_eq_range, ← T_eq ω hfM hM]
  refine sum_congr rfl (fun i hi => ?_)
  have hi' := mem_range.1 hi
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hi']
  congr 1
  by_cases hc : i.Coprime M
  · rw [if_pos hc]
    have hu : IsUnit (i : ZMod M) := (ZMod.isUnit_iff_coprime i M).2 hc
    have := DirichletCharacter.changeLevel_eq_cast_of_dvd ω hfM hu.unit
    rw [IsUnit.unit_spec] at this
    rw [this, ZMod.cast_natCast hfM]
  · rw [if_neg hc]
    exact MulChar.map_nonunit _ (fun h => hc ((ZMod.isUnit_iff_coprime i M).1 h))

/-! ## Witness: the step-4 formula at a real character (ω = trivial, f = 1, M = 6):
both sides are well-typed at genuine data; `T_eq` fires. -/
example : ∑ x ∈ range 6, (if x.Coprime 6 then (1 : DirichletCharacter ℂ 1) (x : ZMod 1) else 0) * sN 6 x
      = B (1 : DirichletCharacter ℂ 1) * ∏ ℓ ∈ eulerPrimes 6 1, (1 - (1 : DirichletCharacter ℂ 1) (ℓ : ZMod 1)) :=
  T_eq _ (one_dvd 6) (by norm_num)

end Erdos634.LemmaSC
