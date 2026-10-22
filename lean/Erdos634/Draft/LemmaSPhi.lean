/-
Lemma S, node A5: the p-primitive component formula, Φ_η (PROOF_lemmaS.md §3.3).

  Take χ = ψη (ψ primitive mod p^r, η mod m, p ∤ m, n = p^r m). Then p^r | f_χ, so C kills every
  term with j ∉ I. For j ∈ I: n_j = p^r d_j, b_j = β_j d_j + p^r γ_j, χ*(b_j) = ψ(β_j d_j)·η*(p^r)·η*(γ_j),
  the Euler primes are the ℓ | d_j with ℓ ∤ f_η, and
     Σ_j e_j[x_j]_χ = η*(p^r) · ψ(Φ_η),
     Φ_η := Σ_{j∈I, f_η | d_j} e_j w(d_j) η*(γ_j) [β_j d_j] ∏_{ℓ|d_j, ℓ∤f_η} (1 − η̄*(ℓ)[ℓ]^{−1}) ∈ ℂ[𝒢],
  with w(d) = φ(m)/φ(d), and ψ extended linearly to ℂ[𝒢].

Encoding: x_j = a_j/n; [x]_χ = `LemmaSC.bracket χ a` (Lemma C without B); I = {j : p ∤ a_j};
d_j = m / gcd(m, a_j) (the order of the m-part of x_j); b_j = a_j / gcd(n, a_j); an element of
ℂ[𝒢] is a function 𝒢 → ℂ and ψ(Φ) = Σ_u ψ(u)Φ(u) (the convention of LemmaSN.lemmaN); the product
over ℓ in ℂ[𝒢] is expanded over subsets S, [β d]·∏_{ℓ∈S}[ℓ]^{−1} being the point u with u·∏ℓ = βd.

Also: values of χ* at non-unit residues (`primChar_mul_nat`, `primChar_nat_of_isPrimitive`),
extending DirichletCRT.prod_unit.
Formalization debt, not /goal progress.
-/
import Mathlib
import Erdos634.Draft.LemmaSCCrit
import Erdos634.Draft.DirichletCRT
import Erdos634.Draft.LemmaSGpp

open scoped BigOperators
open Finset

namespace Erdos634.LemmaSPhi

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.DirichletCRT (conductor_eq primitiveCharacter_eq)

/-! ### χ* at arbitrary residues -/

theorem changeLevel_nat {d n : ℕ} (hd : d ∣ n) (ω : DirichletCharacter ℂ d) (b : ℕ)
    (hb : b.Coprime n) : changeLevel hd ω (b : ZMod n) = ω (b : ZMod d) := by
  have := changeLevel_eq_cast_of_dvd ω hd (ZMod.unitOfCoprime b hb)
  rw [ZMod.coe_unitOfCoprime, ZMod.cast_natCast hd] at this
  exact this

/-- For primitive ψ, ψ* and ψ agree at every natural residue (units and non-units). -/
theorem primChar_nat_of_isPrimitive {N : ℕ} [NeZero N] {ψ : DirichletCharacter ℂ N}
    (hψ : ψ.IsPrimitive) (b : ℕ) : ψ.primitiveCharacter (b : ZMod ψ.conductor) = ψ (b : ZMod N) := by
  have hc : ψ.conductor = N := hψ
  by_cases hb : b.Coprime N
  · conv_rhs => rw [← changeLevel_primitiveCharacter ψ]
    rw [changeLevel_nat _ _ b hb]
  · have h1 : ¬ IsUnit (b : ZMod ψ.conductor) := by rw [ZMod.isUnit_iff_coprime, hc]; exact hb
    have h2 : ¬ IsUnit (b : ZMod N) := by rw [ZMod.isUnit_iff_coprime]; exact hb
    rw [MulChar.map_nonunit _ h1, MulChar.map_nonunit _ h2]

/-- **χ* = ψ*η* at every natural residue** (extends `prod_unit` to non-units). -/
theorem primChar_mul_nat {m₁ m₂ : ℕ} [NeZero m₁] [NeZero m₂] (h : m₁.Coprime m₂)
    {χ : DirichletCharacter ℂ (m₁ * m₂)} {ψ : DirichletCharacter ℂ m₁} {η : DirichletCharacter ℂ m₂}
    (hχ : χ = changeLevel (Nat.dvd_mul_right m₁ m₂) ψ * changeLevel (Nat.dvd_mul_left m₂ m₁) η)
    (b : ℕ) :
    χ.primitiveCharacter (b : ZMod χ.conductor) =
      ψ.primitiveCharacter (b : ZMod ψ.conductor) * η.primitiveCharacter (b : ZMod η.conductor) := by
  haveI : NeZero (m₁ * m₂) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  have hc := conductor_eq h hχ
  rw [primitiveCharacter_eq h hχ, MulChar.coeToFun_mul, Pi.mul_apply]
  by_cases hb : b.Coprime χ.conductor
  · have hb' := hb; rw [hc] at hb'
    rw [changeLevel_nat _ _ b hb, changeLevel_nat _ _ b hb]
  · have h1 : ¬ IsUnit (b : ZMod χ.conductor) := by rw [ZMod.isUnit_iff_coprime]; exact hb
    rw [MulChar.map_nonunit _ h1, MulChar.map_nonunit _ h1, zero_mul]
    rw [hc, Nat.coprime_mul_iff_right, not_and_or] at hb
    rcases hb with hb | hb
    · rw [MulChar.map_nonunit ψ.primitiveCharacter (by rw [ZMod.isUnit_iff_coprime]; exact hb),
        zero_mul]
    · rw [MulChar.map_nonunit η.primitiveCharacter (by rw [ZMod.isUnit_iff_coprime]; exact hb),
        mul_zero]

/-! ### The component formula -/

section Comp
variable {p r m : ℕ} [hp : Fact p.Prime] [NeZero m] (hr : 1 ≤ r) (hpm : ¬ p ∣ m)
  {ψ : DirichletCharacter ℂ (p ^ r)} (hψ : ψ.IsPrimitive) (η : DirichletCharacter ℂ m)

instance neZero_pr : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
instance neZero_prm : NeZero (p ^ r * m) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩

theorem cop_pr (hpm : ¬ p ∣ m) : (p ^ r).Coprime m :=
  Nat.Coprime.pow_left r ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hpm)

/-- χ = ψη at level p^r m. -/
noncomputable abbrev chi (ψ : DirichletCharacter ℂ (p ^ r)) (η : DirichletCharacter ℂ m) :
    DirichletCharacter ℂ (p ^ r * m) :=
  changeLevel (Nat.dvd_mul_right (p ^ r) m) ψ * changeLevel (Nat.dvd_mul_left m (p ^ r)) η

include hpm hψ in
theorem conductor_chi : (chi ψ η).conductor = p ^ r * η.conductor := by
  rw [conductor_eq (cop_pr hpm) rfl, show ψ.conductor = p ^ r from hψ]

/-- d_j: the order of the m-part of a/n. -/
def dm (m a : ℕ) : ℕ := m / m.gcd a

include hr hpm hψ in
/-- **Terms with j ∉ I vanish**: p | a ⟹ [a/n]_χ = 0. -/
theorem bracket_p_dvd (a : ℕ) (ha : p ∣ a) : bracket (chi ψ η) a = 0 := by
  unfold bracket
  rw [if_neg]
  rw [conductor_chi hpm hψ η]
  intro hdv
  set n := p ^ r * m
  have hg : n.gcd a ∣ n := Nat.gcd_dvd_left n a
  have h1 : p ^ r ∣ n / n.gcd a := dvd_trans (Nat.dvd_mul_right _ _) hdv
  have h2 : p ^ r * n.gcd a ∣ n := by
    have := Nat.mul_dvd_mul_right h1 (n.gcd a)
    rwa [Nat.div_mul_cancel hg] at this
  have h3 : n.gcd a ∣ m := (Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.out.pos r) h2)
  have h4 : p ∣ n.gcd a := Nat.dvd_gcd (dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) m) ha
  exact hpm (dvd_trans h4 h3)

include hpm in
theorem gcd_eq (a : ℕ) (ha : ¬ p ∣ a) : (p ^ r * m).gcd a = m.gcd a :=
  Nat.Coprime.gcd_mul_left_cancel m (Nat.Coprime.pow_left r
    ((Nat.Prime.coprime_iff_not_dvd hp.out).2 ha))

include hpm in
theorem euler_eq (d f : ℕ) (hd : d ∣ m) (hd0 : d ≠ 0) (hf0 : f ≠ 0) :
    eulerPrimes (p ^ r * d) (p ^ r * f) = eulerPrimes d f := by
  ext ℓ
  simp only [eulerPrimes, mem_filter, Nat.mem_primeFactors]
  have hP0 : p ^ r ≠ 0 := NeZero.ne _
  constructor
  · rintro ⟨⟨hl, hdv, -⟩, hn⟩
    have hlp : ¬ ℓ ∣ p ^ r := fun h' => hn (dvd_mul_of_dvd_left h' _)
    refine ⟨⟨hl, (hl.dvd_mul.1 hdv).resolve_left hlp, hd0⟩, fun h' => hn (dvd_mul_of_dvd_right h' _)⟩
  · rintro ⟨⟨hl, hdv, -⟩, hn⟩
    refine ⟨⟨hl, dvd_mul_of_dvd_right hdv _, Nat.mul_ne_zero hP0 hd0⟩, fun h' => ?_⟩
    rcases hl.dvd_mul.1 h' with h' | h'
    · have := (Nat.prime_dvd_prime_iff_eq hl hp.out).1 (hl.dvd_of_dvd_pow h')
      subst this; exact hpm (dvd_trans hdv hd)
    · exact hn h'

include hpm hψ in
/-- **Component formula, one term, j ∈ I** (before splitting b_j into β_j, γ_j). -/
theorem bracket_unit (a : ℕ) (ha : ¬ p ∣ a) :
    bracket (chi ψ η) a =
      if η.conductor ∣ dm m a then
        ((m.totient : ℂ) / (dm m a).totient) * ψ ((a / m.gcd a : ℕ) : ZMod (p ^ r))
          * η.primitiveCharacter ((a / m.gcd a : ℕ) : ZMod η.conductor)
          * ∏ ℓ ∈ eulerPrimes (dm m a) η.conductor,
              (1 - ψ⁻¹ (ℓ : ZMod (p ^ r)) * η.primitiveCharacter⁻¹ (ℓ : ZMod η.conductor))
      else 0 := by
  have hcop := cop_pr (r := r) hpm
  have hg := gcd_eq (r := r) hpm a ha
  have hdm : dm m a ∣ m := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left m a)
  have hd0 : dm m a ≠ 0 := by
    intro h0
    have := Nat.div_mul_cancel (Nat.gcd_dvd_left m a)
    rw [show m / m.gcd a = 0 from h0, zero_mul] at this
    exact NeZero.ne m this.symm
  have hnd : p ^ r * m / m.gcd a = p ^ r * dm m a := Nat.mul_div_assoc _ (Nat.gcd_dvd_left m a)
  have hP : 0 < p ^ r := pow_pos hp.out.pos r
  unfold bracket
  rw [hg, hnd]
  by_cases hf : η.conductor ∣ dm m a
  · rw [if_pos (by rw [conductor_chi hpm hψ η]; exact Nat.mul_dvd_mul_left _ hf), if_pos hf]
    have hE : eulerPrimes (p ^ r * dm m a) (chi ψ η).conductor = eulerPrimes (dm m a) η.conductor := by
      rw [conductor_chi hpm hψ η]; exact euler_eq hpm _ _ hdm hd0 (conductor_ne_zero η)
    have hT : (((p ^ r * m).totient : ℕ) : ℂ) / ((p ^ r * dm m a).totient : ℕ)
        = (m.totient : ℂ) / (dm m a).totient := by
      rw [Nat.totient_mul hcop, Nat.totient_mul (hcop.coprime_dvd_right hdm)]
      push_cast
      exact mul_div_mul_left _ _ (by exact_mod_cast (Nat.totient_pos.2 hP).ne')
    rw [hE, hT, primChar_mul_nat (cop_pr hpm) rfl, primChar_nat_of_isPrimitive hψ]
    have hprod : ∀ ℓ ∈ eulerPrimes (dm m a) η.conductor,
        (1 - (chi ψ η).primitiveCharacter⁻¹ (ℓ : ZMod (chi ψ η).conductor))
          = (1 - ψ⁻¹ (ℓ : ZMod (p ^ r)) * η.primitiveCharacter⁻¹ (ℓ : ZMod η.conductor)) := by
      intro ℓ _
      simp only [MulChar.inv_apply_eq_inv']
      rw [primChar_mul_nat (cop_pr hpm) rfl, primChar_nat_of_isPrimitive hψ, mul_inv]
    rw [prod_congr rfl hprod]
    ring
  · rw [if_neg hf, if_neg]
    intro h
    rw [conductor_chi hpm hψ η] at h
    exact hf (Nat.dvd_of_mul_dvd_mul_left hP h)

include hpm hψ in
/-- **Component formula, one term, j ∈ I**, with b_j = β_j d_j + p^r γ_j (mod n_j = p^r d_j):
[x_j]_χ = η*(p^r) · [f_η | d_j] · w(d_j) η*(γ_j) ψ(β_j d_j) ∏_{ℓ|d_j, ℓ∤f_η} (1 − ψ̄(ℓ) η̄*(ℓ)). -/
theorem bracket_I (a β γ : ℕ) (ha : ¬ p ∣ a)
    (hbg : a / m.gcd a ≡ β * dm m a + p ^ r * γ [MOD p ^ r * dm m a]) :
    bracket (chi ψ η) a = η.primitiveCharacter ((p ^ r : ℕ) : ZMod η.conductor) *
      if η.conductor ∣ dm m a then
        ((m.totient : ℂ) / (dm m a).totient) * η.primitiveCharacter (γ : ZMod η.conductor)
          * ψ ((β * dm m a : ℕ) : ZMod (p ^ r))
          * ∏ ℓ ∈ eulerPrimes (dm m a) η.conductor,
              (1 - ψ⁻¹ (ℓ : ZMod (p ^ r)) * η.primitiveCharacter⁻¹ (ℓ : ZMod η.conductor))
      else 0 := by
  rw [bracket_unit hpm hψ η a ha]
  by_cases hf : η.conductor ∣ dm m a
  · rw [if_pos hf, if_pos hf]
    have h1 : ((a / m.gcd a : ℕ) : ZMod (p ^ r)) = ((β * dm m a : ℕ) : ZMod (p ^ r)) := by
      rw [ZMod.natCast_eq_natCast_iff]
      refine (hbg.of_mul_right _).trans ?_
      show (β * dm m a + p ^ r * γ) % p ^ r = (β * dm m a) % p ^ r
      exact Nat.add_mul_mod_self_left _ _ _
    have h2 : ((a / m.gcd a : ℕ) : ZMod η.conductor)
        = ((p ^ r : ℕ) : ZMod η.conductor) * (γ : ZMod η.conductor) := by
      rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 (hbg.of_dvd (dvd_mul_of_dvd_right hf _))]
      push_cast
      rw [(ZMod.natCast_eq_zero_iff _ _).2 hf, mul_zero, zero_add]
    rw [h1, h2, map_mul]
    ring
  · rw [if_neg hf, if_neg hf, mul_zero]

/-- Σ_u ψ(u)[u·L = x] = ψ(x) ψ(L)^{-1} for L a unit (x arbitrary). -/
theorem sum_indicator {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (L x : ZMod N) (hL : IsUnit L) :
    ∑ u : (ZMod N)ˣ, ψ (u : ZMod N) * (if (u : ZMod N) * L = x then 1 else 0) = ψ x * (ψ L)⁻¹ := by
  by_cases hx : IsUnit x
  · obtain ⟨Lu, rfl⟩ := hL
    obtain ⟨xu, rfl⟩ := hx
    set u0 : (ZMod N)ˣ := xu * Lu⁻¹
    have hu0 : ((u0 : (ZMod N)ˣ) : ZMod N) * (Lu : ZMod N) = xu := by
      rw [← Units.val_mul, inv_mul_cancel_right]
    rw [sum_eq_single u0]
    · rw [if_pos hu0, mul_one]
      have hψL : ψ (Lu : ZMod N) ≠ 0 := Erdos634.DirichletCRT.unit_val_ne_zero ψ _
      rw [eq_mul_inv_iff_mul_eq₀ hψL, ← map_mul, hu0]
    · intro u _ hne
      rw [if_neg, mul_zero]
      intro h
      apply hne
      have : (((u * Lu : (ZMod N)ˣ)) : ZMod N) = ((u0 * Lu : (ZMod N)ˣ) : ZMod N) := by
        rw [Units.val_mul, Units.val_mul, h, hu0]
      exact mul_right_cancel (Units.ext this)
    · intro h; exact absurd (mem_univ _) h
  · rw [MulChar.map_nonunit ψ hx, zero_mul]
    refine sum_eq_zero (fun u _ => ?_)
    rw [if_neg, mul_zero]
    intro h; exact hx (h ▸ u.isUnit.mul hL)

open scoped Classical in
/-- **Φ_η ∈ ℂ[𝒢]** exactly as §3.3, as a function 𝒢 → ℂ: the product ∏_ℓ (1 − η̄*(ℓ)[ℓ]^{−1})
expanded over subsets S of the Euler primes, the monomial [β_j d_j]·∏_{ℓ∈S}[ℓ]^{−1} being the
indicator of the u with u·∏_{ℓ∈S} ℓ = β_j d_j. -/
noncomputable def Phi {ι : Type*} [Fintype ι] (p r m : ℕ) (η : DirichletCharacter ℂ m)
    (a β γ : ι → ℕ) (e : ι → ℚ) (u : (ZMod (p ^ r))ˣ) : ℂ :=
  ∑ j, if ¬ p ∣ a j ∧ η.conductor ∣ dm m (a j) then
    (e j : ℂ) * ((m.totient : ℂ) / (dm m (a j)).totient) * η.primitiveCharacter (γ j : ZMod η.conductor)
      * ∑ S ∈ (eulerPrimes (dm m (a j)) η.conductor).powerset,
          (∏ ℓ ∈ S, (-η.primitiveCharacter⁻¹ (ℓ : ZMod η.conductor)))
            * (if (u : ZMod (p ^ r)) * ∏ ℓ ∈ S, (ℓ : ZMod (p ^ r)) = ((β j * dm m (a j) : ℕ) : ZMod (p ^ r))
                then 1 else 0)
  else 0

include hpm in
theorem euler_unit (d f ℓ : ℕ) (hd : d ∣ m) (hl : ℓ ∈ eulerPrimes d f) : IsUnit (ℓ : ZMod (p ^ r)) := by
  simp only [eulerPrimes, mem_filter, Nat.mem_primeFactors] at hl
  obtain ⟨⟨hl, hld, -⟩, -⟩ := hl
  rw [ZMod.isUnit_iff_coprime]
  refine Nat.Coprime.pow_right r ((Nat.coprime_primes hl hp.out).2 ?_)
  rintro rfl; exact hpm (dvd_trans hld hd)

include hr hpm hψ in
/-- **The Φ_η component formula** (§3.3): Σ_j e_j [x_j]_χ = η*(p^r) · ψ(Φ_η). -/
theorem phi_formula {ι : Type*} [Fintype ι] (a β γ : ι → ℕ) (e : ι → ℚ)
    (hbg : ∀ j, ¬ p ∣ a j →
      a j / m.gcd (a j) ≡ β j * dm m (a j) + p ^ r * γ j [MOD p ^ r * dm m (a j)]) :
    ∑ j, (e j : ℂ) * bracket (chi ψ η) (a j) =
      η.primitiveCharacter ((p ^ r : ℕ) : ZMod η.conductor) *
        ∑ u : (ZMod (p ^ r))ˣ, ψ (u : ZMod (p ^ r)) * Phi p r m η a β γ e u := by
  classical
  unfold Phi
  have hswap : ∀ F : (ZMod (p ^ r))ˣ → ι → ℂ,
      ∑ u : (ZMod (p ^ r))ˣ, ψ (u : ZMod (p ^ r)) * ∑ j, F u j =
        ∑ j, ∑ u : (ZMod (p ^ r))ˣ, ψ (u : ZMod (p ^ r)) * F u j := by
    intro F; simp_rw [mul_sum]; exact sum_comm
  rw [hswap, mul_sum]
  refine sum_congr rfl (fun j _ => ?_)
  by_cases hpa : p ∣ a j
  · rw [bracket_p_dvd hr hpm hψ η _ hpa, mul_zero]
    refine (mul_eq_zero_of_right _ (sum_eq_zero (fun u _ => ?_))).symm
    rw [if_neg (fun h => h.1 hpa), mul_zero]
  rw [bracket_I hpm hψ η _ _ _ hpa (hbg j hpa)]
  have hdm : dm m (a j) ∣ m := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left m (a j))
  by_cases hf : η.conductor ∣ dm m (a j)
  · rw [if_pos hf]
    simp_rw [if_pos (show ¬ p ∣ a j ∧ η.conductor ∣ dm m (a j) from ⟨hpa, hf⟩)]
    set E := eulerPrimes (dm m (a j)) η.conductor
    set x : ZMod (p ^ r) := ((β j * dm m (a j) : ℕ) : ZMod (p ^ r))
    set K : ℂ := (e j : ℂ) * ((m.totient : ℂ) / (dm m (a j)).totient) *
      η.primitiveCharacter (γ j : ZMod η.conductor)
    set c : ℕ → ℂ := fun ℓ => -η.primitiveCharacter⁻¹ (ℓ : ZMod η.conductor)
    have hLu : ∀ S ∈ E.powerset, IsUnit (∏ ℓ ∈ S, (ℓ : ZMod (p ^ r))) := by
      intro S hS
      exact prod_induction _ IsUnit (fun _ _ ha hb => ha.mul hb) isUnit_one
        (fun ℓ hℓ => euler_unit hpm _ _ ℓ hdm (mem_powerset.1 hS hℓ))
    have hin : ∀ S ∈ E.powerset,
        ∑ u : (ZMod (p ^ r))ˣ, ψ (u : ZMod (p ^ r)) *
          ((∏ ℓ ∈ S, c ℓ) *
            (if (u : ZMod (p ^ r)) * ∏ ℓ ∈ S, (ℓ : ZMod (p ^ r)) = x then 1 else 0))
        = ψ x * ∏ ℓ ∈ S, (-(ψ⁻¹ (ℓ : ZMod (p ^ r)) * η.primitiveCharacter⁻¹ (ℓ : ZMod η.conductor))) := by
      intro S hS
      have h1 := sum_indicator ψ _ x (hLu S hS)
      rw [map_prod, ← prod_inv_distrib] at h1
      calc _ = (∏ ℓ ∈ S, c ℓ) * ∑ u : (ZMod (p ^ r))ˣ, ψ (u : ZMod (p ^ r)) *
            (if (u : ZMod (p ^ r)) * ∏ ℓ ∈ S, (ℓ : ZMod (p ^ r)) = x then 1 else 0) := by
              rw [mul_sum]; exact sum_congr rfl (fun u _ => by ring)
        _ = ψ x * ∏ ℓ ∈ S, (c ℓ * (ψ (ℓ : ZMod (p ^ r)))⁻¹) := by rw [h1, prod_mul_distrib]; ring
        _ = _ := by
              congr 1; refine prod_congr rfl (fun ℓ _ => ?_)
              rw [MulChar.inv_apply_eq_inv' ψ]; simp only [c]; ring
    have hmove : ∑ u : (ZMod (p ^ r))ˣ, ψ (u : ZMod (p ^ r)) *
        (K * ∑ S ∈ E.powerset, (∏ ℓ ∈ S, c ℓ) *
          (if (u : ZMod (p ^ r)) * ∏ ℓ ∈ S, (ℓ : ZMod (p ^ r)) = x then 1 else 0))
        = K * ∑ S ∈ E.powerset, ∑ u : (ZMod (p ^ r))ˣ, ψ (u : ZMod (p ^ r)) *
          ((∏ ℓ ∈ S, c ℓ) *
            (if (u : ZMod (p ^ r)) * ∏ ℓ ∈ S, (ℓ : ZMod (p ^ r)) = x then 1 else 0)) := by
      simp_rw [mul_sum]; rw [sum_comm]
      exact sum_congr rfl (fun S _ => sum_congr rfl (fun u _ => by ring))
    rw [hmove, sum_congr rfl hin, ← mul_sum, ← prod_one_add]
    simp only [← sub_eq_add_neg]
    ring
  · rw [if_neg hf, mul_zero, mul_zero]
    refine (mul_eq_zero_of_right _ (sum_eq_zero (fun u _ => ?_))).symm
    rw [if_neg (fun h => hf h.2), mul_zero]

include hpm in
/-- The paper's decomposition b_j = β_j d_j + p^r γ_j (mod p^r d_j) always exists (CRT). -/
theorem exists_beta_gamma (a : ℕ) :
    ∃ β γ : ℕ, a / m.gcd a ≡ β * dm m a + p ^ r * γ [MOD p ^ r * dm m a] := by
  have hcop := cop_pr (r := r) hpm
  have hdm : dm m a ∣ m := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left m a)
  have hd0 : dm m a ≠ 0 := by
    intro h0
    have := Nat.div_mul_cancel (Nat.gcd_dvd_left m a)
    rw [show m / m.gcd a = 0 from h0, zero_mul] at this
    exact NeZero.ne m this.symm
  haveI : NeZero (dm m a) := ⟨hd0⟩
  have hc : (p ^ r).Coprime (dm m a) := hcop.coprime_dvd_right hdm
  set b := a / m.gcd a
  set d := dm m a
  refine ⟨((b : ZMod (p ^ r)) * (d : ZMod (p ^ r))⁻¹).val, ((b : ZMod d) * ((p ^ r : ℕ) : ZMod d)⁻¹).val, ?_⟩
  refine (Nat.modEq_and_modEq_iff_modEq_mul hc).1 ⟨?_, ?_⟩
  · rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_add, Nat.cast_mul, Nat.cast_mul,
      ZMod.natCast_zmod_val, ZMod.natCast_self, zero_mul, add_zero, mul_assoc,
      mul_comm ((d : ZMod (p ^ r))⁻¹), ZMod.coe_mul_inv_eq_one _ hc.symm, mul_one]
  · rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_add, Nat.cast_mul, Nat.cast_mul,
      ZMod.natCast_zmod_val, ZMod.natCast_self, mul_zero, zero_add, mul_left_comm,
      ZMod.coe_mul_inv_eq_one _ hc, mul_one]

include hr hpm hψ in
/-- **Φ_η formula, unconditional form**: for every index family (a, e) there are β, γ as in the
paper with Σ_j e_j [x_j]_χ = η*(p^r) · ψ(Φ_η). -/
theorem phi_formula_exists {ι : Type*} [Fintype ι] (a : ι → ℕ) (e : ι → ℚ) :
    ∃ β γ : ι → ℕ, ∑ j, (e j : ℂ) * bracket (chi ψ η) (a j) =
      η.primitiveCharacter ((p ^ r : ℕ) : ZMod η.conductor) *
        ∑ u : (ZMod (p ^ r))ˣ, ψ (u : ZMod (p ^ r)) * Phi p r m η a β γ e u := by
  choose β γ h using fun j => exists_beta_gamma (r := r) hpm (a j)
  exact ⟨β, γ, phi_formula hr hpm hψ η a β γ e (fun j _ => h j)⟩

end Comp

/-! ## Witness: p = 7, r = 1, m = 2 (n = 14), a = (2, 5, 7), η trivial; the hypotheses of
`phi_formula` are all realised (a primitive ψ mod 7 exists; β, γ exist), so it is not vacuous. -/
theorem witness_14 : ∃ ψ : DirichletCharacter ℂ (7 ^ 1), ψ.IsPrimitive ∧
    ∃ β γ : Fin 3 → ℕ, ∑ j, (((![1, 1, 0] : Fin 3 → ℚ) j : ℚ) : ℂ) *
        bracket (chi ψ (1 : DirichletCharacter ℂ 2)) (![2, 5, 7] j) =
      (1 : DirichletCharacter ℂ 2).primitiveCharacter ((7 ^ 1 : ℕ) : ZMod (1 : DirichletCharacter ℂ 2).conductor) *
        ∑ u : (ZMod (7 ^ 1))ˣ, ψ (u : ZMod (7 ^ 1)) *
          Phi 7 1 2 (1 : DirichletCharacter ℂ 2) ![2, 5, 7] β γ ![1, 1, 0] u := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨ψ, hψ⟩ := Erdos634.LemmaSGpp.exists_primitive_pp (q := 7) (v := 1) le_rfl (by norm_num)
  exact ⟨ψ, hψ, phi_formula_exists le_rfl (by norm_num) hψ _ _ _⟩

#print axioms Erdos634.LemmaSPhi.phi_formula
#print axioms Erdos634.LemmaSPhi.phi_formula_exists
#print axioms Erdos634.LemmaSPhi.primChar_mul_nat
#print axioms Erdos634.LemmaSPhi.witness_14

end Erdos634.LemmaSPhi
