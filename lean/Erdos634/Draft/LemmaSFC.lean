/-
Lemma S, node A5: **the full-conductor core (FC-odd), generic cases** (PROOF_lemmaS.md §4).

  Setup (2 ∤ m or 4 | m, i.e. m ≢ 2 mod 4; m_I = m by P1.3). Take η primitive mod m. Then no Euler
  factor survives, and Φ′ = Σ_{x ∈ F} c_x [β_x], c_x = E_x η(γ_x), c_x = 0 ⟺ E_x = 0.
  |F| = 1: 2 points < |N|, so Φ′ = 0. |F| = 2, β_k ≠ ±β_j: 4 points < |N|, N(a) forces c = 0.
  |F| = 3, β's pairwise distinct: 6 points; if p ≥ 11 or r ≥ 2 then 6 < |N| and N(a) applies.

Proved here, in class form (P1.2):
* `fc_term`       : for a full I-point x (p ∤ x, gcd(x, m) = 1) [x/n]_{ψη} = ψ(x)η(x), and for an
                    I-point that is not full it is 0 (η primitive mod m).
* `fc_component`  : Σ_j e_j [x_j]_{ψη} = Σ_{x full I-point} E_x ψ(x) η(x)  (= ψ(Φ′)).
* `fc_symm`       : Φ′ = η(−1)[−1]Φ′ for every primitive η mod m, when 2·#(distinct β's) < |N| (N(a)).
* `fc_isolated`   : if x is a full I-point, no other full I-point y with E_y ≠ 0 has y ≡ ±x (mod p^r)
                    (β_y ≠ ±β_x), and 2·#(full I-points) < |N|, then E_x = 0.
* `fc_isolated_even` : the same for r = 1 with NO count condition, when m ∉ {3, 4} (η even, N(b)).
* `card_N`        : |N| = p − 1 (r = 1), p (r ≥ 2).
* `fc_generic`    : tile datum (a : Fin 3 → ℕ): the same conclusion whenever p ≥ 11, or r ≥ 2, or
                    there are at most two full I-points, or r = 1 and m ∉ {3, 4} — §4's cases |F| = 1,
                    |F| = 2 with β_k ≠ ±β_j, and |F| = 3 with distinct β (all p ≥ 7 except n ∈ {21,28}).
NOT covered in THIS file: §4's relation cases (R1, R1′, R1F2, R3, R2b, R2a) and the p = 7, r = 1,
three-point case with m ∈ {3, 4}, i.e. n ∈ {21, 28}.  (Note 2026-10-03: these are formalized elsewhere,
in LemmaSFCPair/LemmaSR1p/LemmaSR1F2/LemmaSR3/LemmaSR2a/LemmaSR2b12/LemmaSFCOdd, and n ∈ {21, 28}
in LemmaSOddAll; all imported into All.lean.)
Formalization debt, not /goal progress.
-/
import Mathlib
import Erdos634.Draft.LemmaSElim
import Erdos634.Draft.LemmaSParity

open scoped BigOperators
open Finset

namespace Erdos634.LemmaSFC

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi (chi dm conductor_chi bracket_p_dvd bracket_unit primChar_nat_of_isPrimitive
  sum_indicator)
open Erdos634.LemmaSElim (classSum regroup)
open Erdos634.LemmaSN (pred_dvd lemmaN_a lemmaN_b)

section FC
variable {p r m : ℕ} [hp : Fact p.Prime] [NeZero m]

theorem dm_eq_iff (y : ℕ) : dm m y = m ↔ y.Coprime m := by
  rw [dm, Nat.div_eq_self]
  simp only [NeZero.ne m, false_or]
  exact ⟨fun h => Nat.coprime_comm.1 h, fun h => Nat.coprime_comm.1 h⟩

/-- One term at η primitive mod m. -/
theorem fc_term (hpm : ¬ p ∣ m) {ψ : DirichletCharacter ℂ (p ^ r)} (hψ : ψ.IsPrimitive)
    {η : DirichletCharacter ℂ m} (hη : η.IsPrimitive) (y : ℕ) (hy : ¬ p ∣ y) :
    bracket (chi ψ η) y = if y.Coprime m then ψ (y : ZMod (p ^ r)) * η (y : ZMod m) else 0 := by
  have hc : η.conductor = m := hη
  rw [bracket_unit hpm hψ η y hy]
  by_cases hcop : y.Coprime m
  · have hdm : dm m y = m := (dm_eq_iff y).2 hcop
    have hg : m.gcd y = 1 := Nat.coprime_comm.1 hcop
    rw [if_pos (by rw [hc, hdm]), if_pos hcop, hg, Nat.div_one, hdm]
    have hE : eulerPrimes m η.conductor = ∅ := by
      rw [hc]; ext ℓ
      simp only [eulerPrimes, mem_filter, Nat.mem_primeFactors, Finset.notMem_empty, iff_false]
      rintro ⟨⟨-, h, -⟩, h'⟩; exact h' h
    rw [hE, prod_empty, primChar_nat_of_isPrimitive hη,
      div_self (by exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne m))).ne')]
    ring
  · rw [if_neg hcop, if_neg]
    intro h
    rw [hc] at h
    exact hcop ((dm_eq_iff y).1 (Nat.dvd_antisymm (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left m y)) h))

/-- The full I-points. -/
def fullPts {ι : Type*} [Fintype ι] [DecidableEq ι] (p m : ℕ) (a : ι → ℕ) : Finset ℕ :=
  (univ.image a).filter (fun y => ¬ p ∣ y ∧ y.Coprime m)

/-- **Component at η primitive mod m** = ψ(Φ′). -/
theorem fc_component (hr : 1 ≤ r) (hpm : ¬ p ∣ m) {ψ : DirichletCharacter ℂ (p ^ r)}
    (hψ : ψ.IsPrimitive) {η : DirichletCharacter ℂ m} (hη : η.IsPrimitive) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ) :
    ∑ j, (e j : ℂ) * bracket (chi ψ η) (a j) =
      ∑ y ∈ fullPts p m a, ((classSum a e y : ℚ) : ℂ) * (ψ (y : ZMod (p ^ r)) * η (y : ZMod m)) := by
  rw [regroup, sum_coe_sort (univ.image a)
    (fun y => ((classSum a e y : ℚ) : ℂ) * bracket (chi ψ η) y), fullPts, sum_filter]
  refine sum_congr rfl (fun y _ => ?_)
  by_cases hpy : p ∣ y
  · rw [bracket_p_dvd hr hpm hψ η y hpy, if_neg (fun h => h.1 hpy), mul_zero]
  · rw [fc_term hpm hψ hη y hpy]
    by_cases hcop : y.Coprime m
    · rw [if_pos hcop, if_pos ⟨hpy, hcop⟩]
    · rw [if_neg hcop, if_neg (fun h => hcop h.2), mul_zero]

/-- Φ′ ∈ ℂ[𝒢]: the point (x mod p^r) carries E_x η(x). -/
noncomputable def PhiF {ι : Type*} [Fintype ι] [DecidableEq ι] (p r m : ℕ)
    (η : DirichletCharacter ℂ m) (a : ι → ℕ) (e : ι → ℚ) (u : (ZMod (p ^ r))ˣ) : ℂ :=
  ∑ y ∈ fullPts p m a, if (u : ZMod (p ^ r)) = y then ((classSum a e y : ℚ) : ℂ) * η (y : ZMod m) else 0

theorem psi_PhiF (ψ : DirichletCharacter ℂ (p ^ r)) (η : DirichletCharacter ℂ m) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ) :
    ∑ u : (ZMod (p ^ r))ˣ, ψ (u : ZMod (p ^ r)) * PhiF p r m η a e u =
      ∑ y ∈ fullPts p m a, ((classSum a e y : ℚ) : ℂ) * (ψ (y : ZMod (p ^ r)) * η (y : ZMod m)) := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  unfold PhiF
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl (fun y _ => ?_)
  have := sum_indicator ψ 1 (y : ZMod (p ^ r)) isUnit_one
  rw [map_one, inv_one, mul_one] at this
  calc _ = ((classSum a e y : ℚ) : ℂ) * η (y : ZMod m) * ∑ u : (ZMod (p ^ r))ˣ,
        ψ (u : ZMod (p ^ r)) * (if (u : ZMod (p ^ r)) * 1 = y then 1 else 0) := by
          rw [mul_sum]; refine sum_congr rfl (fun u _ => ?_)
          rw [mul_one]; split_ifs <;> ring
    _ = _ := by rw [this]; ring

/-- Units with a prescribed value: at most one. -/
theorem card_val_le_one {N : ℕ} [NeZero N] (x : ZMod N) :
    (univ.filter (fun v : (ZMod N)ˣ => (v : ZMod N) = x)).card ≤ 1 :=
  card_le_one.2 (fun v hv w hw => Units.ext ((mem_filter.1 hv).2.trans (mem_filter.1 hw).2.symm))

/-- **The N(a) symmetry at every primitive η mod m**: Φ′ = −ε[−1]Φ′ = η(−1)[−1]Φ′. -/
theorem fc_symm (hr : 1 ≤ r) (hpm : ¬ p ∣ m) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    {η : DirichletCharacter ℂ m} (hη : η.IsPrimitive)
    (hN : 2 * ((fullPts p m a).image (fun y : ℕ => (y : ZMod (p ^ r)))).card <
      (univ.filter (fun v : (ZMod (p ^ r))ˣ => ZMod.unitsMap (pred_dvd p r) v = 1)).card) :
    ∀ u, PhiF p r m η a e u = η (-1) * PhiF p r m η a e (-u) := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  set ε : ℂ := -η (-1)
  have hε : ε = 1 ∨ ε = -1 := by
    rcases η.even_or_odd with h | h
    · right; simp only [ε, show η (-1) = 1 from h]
    · left; simp only [ε, show η (-1) = -1 from h, neg_neg]
  have hη2 : η (-1) * η (-1) = 1 := by
    rcases η.even_or_odd with h | h
    · rw [show η (-1) = 1 from h]; ring
    · rw [show η (-1) = -1 from h]; ring
  set Φ := PhiF p r m η a e
  have hΦ : ∀ ψ : DirichletCharacter ℂ (p ^ r), ψ.IsPrimitive → ψ (-1) = ε →
      ∑ u : (ZMod (p ^ r))ˣ, ψ (u : ZMod (p ^ r)) * Φ u = 0 := by
    intro ψ hψ hψε
    have hodd : (chi ψ η).Odd := by
      show (chi ψ η) (-1) = -1
      rw [MulChar.coeToFun_mul, Pi.mul_apply,
        Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_right (p ^ r) m) ψ,
        Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_left m (p ^ r)) η, hψε]
      simp only [ε]; linear_combination -hη2
    have h0 := hP (chi ψ η) hodd (by rw [conductor_chi hpm hψ η]; exact Nat.dvd_mul_right _ _)
    rw [fc_component hr hpm hψ hη a e] at h0
    rw [psi_PhiF]; exact h0
  -- the count hypothesis of N(a)
  have hS : ∀ v : (ZMod (p ^ r))ˣ, Φ v ≠ 0 → ∃ y ∈ fullPts p m a, (v : ZMod (p ^ r)) = y := by
    intro v hv
    by_contra hno
    push Not at hno
    exact hv (sum_eq_zero (fun y hy => if_neg (hno y hy)))
  have hcount : ∀ u : (ZMod (p ^ r))ˣ,
      (univ.filter (fun v => ZMod.unitsMap (pred_dvd p r) v = ZMod.unitsMap (pred_dvd p r) u ∧
        (Φ v ≠ 0 ∨ Φ (-v) ≠ 0))).card
        < (univ.filter (fun v => ZMod.unitsMap (pred_dvd p r) v = 1)).card := by
    intro u
    refine lt_of_le_of_lt ?_ hN
    calc _ ≤ (((fullPts p m a).image (fun y : ℕ => (y : ZMod (p ^ r)))).biUnion (fun t =>
            univ.filter (fun v : (ZMod (p ^ r))ˣ => (v : ZMod (p ^ r)) = t) ∪
            univ.filter (fun v : (ZMod (p ^ r))ˣ => (v : ZMod (p ^ r)) = -t))).card := by
          refine card_le_card (fun v hv => ?_)
          rcases (mem_filter.1 hv).2.2 with h | h
          · obtain ⟨y, hy, hvy⟩ := hS v h
            exact mem_biUnion.2 ⟨_, mem_image_of_mem _ hy,
              mem_union_left _ (mem_filter.2 ⟨mem_univ _, hvy⟩)⟩
          · obtain ⟨y, hy, hvy⟩ := hS (-v) h
            refine mem_biUnion.2 ⟨_, mem_image_of_mem _ hy,
              mem_union_right _ (mem_filter.2 ⟨mem_univ _, ?_⟩)⟩
            rw [Units.val_neg] at hvy; rw [← hvy, neg_neg]
      _ ≤ ∑ t ∈ (fullPts p m a).image (fun y : ℕ => (y : ZMod (p ^ r))), 2 := by
          refine card_biUnion_le.trans (sum_le_sum (fun t _ => ?_))
          exact (card_union_le _ _).trans (by
            have := card_val_le_one (N := p ^ r) t
            have := card_val_le_one (N := p ^ r) (-t)
            omega)
      _ = 2 * ((fullPts p m a).image (fun y : ℕ => (y : ZMod (p ^ r)))).card := by
          rw [sum_const, smul_eq_mul, mul_comm]
  intro u
  rw [lemmaN_a hr Φ hε hΦ hcount u]
  simp only [ε, neg_neg]

/-- **FC isolation**, with the count on distinct β's (N(a) counts support points). -/
theorem fc_isolated_img (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) (hm4 : m % 4 ≠ 2) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (x : ℕ) (hx : x ∈ fullPts p m a)
    (hsep : ∀ y ∈ fullPts p m a, y ≠ x → classSum a e y ≠ 0 →
      (y : ZMod (p ^ r)) ≠ x ∧ (y : ZMod (p ^ r)) ≠ -x)
    (hN : 2 * ((fullPts p m a).image (fun y : ℕ => (y : ZMod (p ^ r)))).card <
      (univ.filter (fun v : (ZMod (p ^ r))ˣ => ZMod.unitsMap (pred_dvd p r) v = 1)).card) :
    classSum a e x = 0 := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  obtain ⟨η, hη⟩ := Erdos634.LemmaSGprime.exists_primitive (NeZero.ne m) hm4
  set Φ := PhiF p r m η a e
  have hN' : ∀ u, Φ u = η (-1) * Φ (-u) := fc_symm hr hpm a e hP hη hN
  -- evaluate at x
  have hxf := mem_filter.1 hx
  have hxP : x.Coprime (p ^ r) :=
    Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hxf.2.1).symm
  set ux : (ZMod (p ^ r))ˣ := ZMod.unitOfCoprime x hxP
  have hux : (ux : ZMod (p ^ r)) = x := ZMod.coe_unitOfCoprime x hxP
  have hxx : (x : ZMod (p ^ r)) ≠ -x := by
    intro h
    have h2 : ((2 * x : ℕ) : ZMod (p ^ r)) = 0 := by push_cast; linear_combination h
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := (Nat.Prime.dvd_mul hp.out).1 (dvd_trans (dvd_pow_self p (by omega)) h2)
    rcases this with h | h
    · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
    · exact hxf.2.1 h
  have hv1 : Φ ux = ((classSum a e x : ℚ) : ℂ) * η (x : ZMod m) := by
    simp only [Φ, PhiF]
    rw [sum_eq_single x]
    · rw [if_pos hux]
    · intro y hy hyx
      by_cases hE : classSum a e y = 0
      · split_ifs <;> simp [hE]
      · rw [if_neg]; rw [hux]; exact fun h => (hsep y hy hyx hE).1 h.symm
    · intro h; exact absurd hx h
  have hv2 : Φ (-ux) = 0 := by
    simp only [Φ, PhiF]
    refine sum_eq_zero (fun y hy => ?_)
    rw [Units.val_neg, hux]
    by_cases hyx : y = x
    · subst hyx; rw [if_neg (fun h => hxx h.symm)]
    by_cases hE : classSum a e y = 0
    · split_ifs <;> simp [hE]
    · rw [if_neg]; exact fun h => (hsep y hy hyx hE).2 h.symm
  have := hN' ux
  rw [hv1, hv2, mul_zero] at this
  have hηx : η (x : ZMod m) ≠ 0 := by
    rw [← ZMod.coe_unitOfCoprime x hxf.2.2]; exact Erdos634.DirichletCRT.unit_val_ne_zero _ _
  exact_mod_cast (mul_eq_zero.1 this).resolve_right hηx

/-- **FC isolation.** -/
theorem fc_isolated (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) (hm4 : m % 4 ≠ 2) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (x : ℕ) (hx : x ∈ fullPts p m a)
    (hsep : ∀ y ∈ fullPts p m a, y ≠ x → classSum a e y ≠ 0 →
      (y : ZMod (p ^ r)) ≠ x ∧ (y : ZMod (p ^ r)) ≠ -x)
    (hN : 2 * (fullPts p m a).card <
      (univ.filter (fun v : (ZMod (p ^ r))ˣ => ZMod.unitsMap (pred_dvd p r) v = 1)).card) :
    classSum a e x = 0 :=
  fc_isolated_img hp7 hr hpm hm4 a e hP x hx hsep
    (lt_of_le_of_lt (Nat.mul_le_mul_left 2 card_image_le) hN)

/-- **FC isolation at r = 1 with an even η** (§4: "If p = 7 and r = 1, choose η even. This is
possible iff m_I ∉ {3, 4} … Then N(b) applies."): no count condition. -/
theorem fc_isolated_even (hp7 : 7 ≤ p) (hpm : ¬ p ∣ m) (hm4 : m % 4 ≠ 2) (hm34 : m ≠ 3 ∧ m ≠ 4)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ 1 * m), χ.Odd → p ^ 1 ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (x : ℕ) (hx : x ∈ fullPts p m a)
    (hsep : ∀ y ∈ fullPts p m a, y ≠ x → classSum a e y ≠ 0 →
      (y : ZMod (p ^ 1)) ≠ x ∧ (y : ZMod (p ^ 1)) ≠ -x) :
    classSum a e x = 0 := by
  haveI : NeZero (p ^ 1) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  obtain ⟨η, hη, hev⟩ :=
    (Erdos634.LemmaSParity.exists_even_primitive_iff (NeZero.ne m) hm4).2 hm34
  set Φ := PhiF p 1 m η a e
  have hΦ : ∀ ψ : DirichletCharacter ℂ (p ^ 1), ψ.IsPrimitive → ψ (-1) = -1 →
      ∑ u : (ZMod (p ^ 1))ˣ, ψ (u : ZMod (p ^ 1)) * Φ u = 0 := by
    intro ψ hψ hψε
    have hodd : (chi ψ η).Odd := by
      show (chi ψ η) (-1) = -1
      rw [MulChar.coeToFun_mul, Pi.mul_apply,
        Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_right (p ^ 1) m) ψ,
        Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_left m (p ^ 1)) η, hψε,
        show η (-1) = 1 from hev, mul_one]
    have h0 := hP (chi ψ η) hodd (by rw [conductor_chi hpm hψ η]; exact Nat.dvd_mul_right _ _)
    rw [fc_component le_rfl hpm hψ hη a e] at h0
    rw [psi_PhiF]; exact h0
  have hN' := lemmaN_b Φ hΦ
  have hxf := mem_filter.1 hx
  have hxP : x.Coprime (p ^ 1) :=
    Nat.Coprime.pow_right 1 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hxf.2.1).symm
  set ux : (ZMod (p ^ 1))ˣ := ZMod.unitOfCoprime x hxP
  have hux : (ux : ZMod (p ^ 1)) = x := ZMod.coe_unitOfCoprime x hxP
  have hxx : (x : ZMod (p ^ 1)) ≠ -x := by
    intro h
    have h2 : ((2 * x : ℕ) : ZMod (p ^ 1)) = 0 := by push_cast; linear_combination h
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := (Nat.Prime.dvd_mul hp.out).1 (dvd_trans (dvd_pow_self p (by omega)) h2)
    rcases this with h | h
    · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
    · exact hxf.2.1 h
  have hv1 : Φ ux = ((classSum a e x : ℚ) : ℂ) * η (x : ZMod m) := by
    simp only [Φ, PhiF]
    rw [sum_eq_single x]
    · rw [if_pos hux]
    · intro y hy hyx
      by_cases hE : classSum a e y = 0
      · split_ifs <;> simp [hE]
      · rw [if_neg]; rw [hux]; exact fun h => (hsep y hy hyx hE).1 h.symm
    · intro h; exact absurd hx h
  have hv2 : Φ (-ux) = 0 := by
    simp only [Φ, PhiF]
    refine sum_eq_zero (fun y hy => ?_)
    rw [Units.val_neg, hux]
    by_cases hyx : y = x
    · subst hyx; rw [if_neg (fun h => hxx h.symm)]
    by_cases hE : classSum a e y = 0
    · split_ifs <;> simp [hE]
    · rw [if_neg]; exact fun h => (hsep y hy hyx hE).2 h.symm
  have := hN' ux
  rw [hv1, hv2] at this
  have hηx : η (x : ZMod m) ≠ 0 := by
    rw [← ZMod.coe_unitOfCoprime x hxf.2.2]; exact Erdos634.DirichletCRT.unit_val_ne_zero _ _
  exact_mod_cast (mul_eq_zero.1 this).resolve_right hηx

/-- |N| = p − 1 for r = 1 and p for r ≥ 2. -/
theorem card_N (hr : 1 ≤ r) :
    (univ.filter (fun v : (ZMod (p ^ r))ˣ => ZMod.unitsMap (pred_dvd p r) v = 1)).card =
      if r = 1 then p - 1 else p := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  haveI : NeZero (p ^ (r - 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have h := Erdos634.LemmaSC.fiber_card (pred_dvd p r)
  have hT0 : ((p ^ (r - 1)).totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.2 (pow_pos hp.out.pos _)).ne'
  rw [eq_div_iff hT0] at h
  have hnat : (univ.filter (fun v : (ZMod (p ^ r))ˣ => ZMod.unitsMap (pred_dvd p r) v = 1)).card *
      (p ^ (r - 1)).totient = (p ^ r).totient := by exact_mod_cast h
  have hT0' : 0 < (p ^ (r - 1)).totient := Nat.totient_pos.2 (pow_pos hp.out.pos _)
  split_ifs with h1
  · subst h1
    simp only [Nat.sub_self, pow_zero, Nat.totient_one, mul_one, pow_one,
      Nat.totient_prime hp.out] at hnat
    exact hnat
  · have htot : (p ^ r).totient = p * (p ^ (r - 1)).totient := by
      rw [show p ^ r = p * p ^ (r - 1) by rw [← pow_succ']; congr 1; omega]
      exact Nat.totient_mul_of_prime_of_dvd hp.out (dvd_pow_self p (by omega))
    rw [htot] at hnat
    exact Nat.eq_of_mul_eq_mul_right hT0' hnat

/-- **FC-odd, generic cases, for a tile datum.** -/
theorem fc_generic (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) (hm4 : m % 4 ≠ 2)
    (a : Fin 3 → ℕ) (e : Fin 3 → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (hcase : 11 ≤ p ∨ 2 ≤ r ∨ (fullPts p m a).card ≤ 2 ∨ (r = 1 ∧ m ≠ 3 ∧ m ≠ 4))
    (x : ℕ) (hx : x ∈ fullPts p m a)
    (hsep : ∀ y ∈ fullPts p m a, y ≠ x → classSum a e y ≠ 0 →
      (y : ZMod (p ^ r)) ≠ x ∧ (y : ZMod (p ^ r)) ≠ -x) :
    classSum a e x = 0 := by
  have h3 : (fullPts p m a).card ≤ 3 :=
    (card_filter_le _ _).trans ((card_image_le).trans (by simp))
  rcases hcase with hc | hc | hc | ⟨rfl, hm34⟩
  rotate_left 3
  · exact fc_isolated_even hp7 hpm hm4 hm34 a e hP x hx hsep
  all_goals refine fc_isolated hp7 hr hpm hm4 a e hP x hx hsep ?_
  all_goals rw [card_N hr]
  all_goals split_ifs with h1 <;> omega

end FC

/-! ## Witness: n = 7·9 = 63, a = (1, 2, 60), p = 7, r = 1, m = 9; e = 0 satisfies Lemma P's
hypothesis; the full I-points are 1 and 2 (60 is not coprime to 9), so `hcase`'s third branch
holds and every hypothesis of `fc_generic` is met at x = 1 (non-vacuity of the hypotheses; the
conclusion is then 0 = 0, a data-only check). -/
theorem witness_fc : classSum (![1, 2, 60] : Fin 3 → ℕ) (fun _ => 0) 1 = 0 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hfp : fullPts 7 9 (![1, 2, 60] : Fin 3 → ℕ) = {1, 2} := by decide
  refine fc_generic (p := 7) (r := 1) (m := 9) (by norm_num) le_rfl (by norm_num) (by norm_num)
    _ _ (fun χ _ _ => by simp) (Or.inr (Or.inr (Or.inl (by rw [hfp]; decide)))) 1
    (by rw [hfp]; decide) (fun y _ _ h => absurd (by simp [classSum]) h)

#print axioms Erdos634.LemmaSFC.fc_isolated
#print axioms Erdos634.LemmaSFC.fc_generic
#print axioms Erdos634.LemmaSFC.card_N
#print axioms Erdos634.LemmaSFC.fc_isolated_even
#print axioms Erdos634.LemmaSFC.witness_fc

end Erdos634.LemmaSFC
