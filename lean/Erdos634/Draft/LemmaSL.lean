/-
Lemma S, node A5: **Lemma L (one level down)** (PROOF_lemmaS.md §4 and P2), with the top-level
G′ relations it consumes.

  Lemma L (FC-odd setting; (a, p) ∈ R1′ ∪ R1F2c, with the pair j, k and the special prime
  q ∈ {2, 3} with g_q ≠ 1). e_j = e_k = 0.
  1. f₂ := m_I/3 (q = 3), or m_I/2 (q = 2, 8 | m_I), or m_I/4 (q = 2, 4 ∥ m_I); f₂ ≢ 2 (mod 4).
  2. Terms j, k survive with the same Euler set; the third term is absent or dies at f₂.
  3. By G some ψ ∈ X_ε has E ≠ 0 (q ∈ {2,3} ≢ ±1 mod p); dividing gives e_j η(g mod f₂) ± e_k = 0.
  4. g mod f₂ has lost its q-component, so η(g mod f₂) = (−1)^{τ(g)−1}.
  5. Against the top-level identity with (−1)^{τ(g)}, e_j = e_k = 0.

Encoding (class form, P1.2): the pair is two full I-points x ≠ y with y ≡ σx (mod p^r), σ = ±1
(σ = 1: β_k = β_j, classes R1F2/R1F3; σ = −1: β_k = −β_j, class R1′); g = x/(σy) mod m, given by any
integer z with z·σy ≡ x (mod m); m = q^v m' (q ∤ m'); f₂ = q^{v'} m' with v' = 0 (q = 3, or q = 2
with 4 ∥ m) or v' = v − 1 (q = 2, 8 | m); "the third term dies at f₂" is `hdie`.
Proved here:
* `rel_Gprime` : a relation E_x η(x) + σE_y η(σy) = 0 for all primitive η mod d (d ≢ 2 mod 4) gives
                 E_x = E_y = 0, or g ∈ Sp(d) and E_y = −σ(−1)^{τ(g)} E_x   (G′ step of §4).
* `fc_key`     : the top-level relation (N(a) at every primitive η mod m).
* `key_level2` : the level-f₂ relation (steps 2–3).
* `tau_drop`   : g ∈ Sp(m), g_q ≠ 1 ⟹ g ∈ Sp(f₂) and τ_{f₂}(g) = τ_m(g) − 1 (step 4).
* `lemmaL`     : E_x = E_y = 0.
Formalization debt, not /goal progress.
-/
import Mathlib
import Erdos634.Draft.LemmaSFCPair

open scoped BigOperators
open Finset

namespace Erdos634.LemmaSL

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi (chi dm conductor_chi bracket_p_dvd bracket_unit changeLevel_nat)
open Erdos634.LemmaSElim (classSum regroup)
open Erdos634.LemmaSFC (fullPts PhiF fc_symm dm_eq_iff)
open Erdos634.LemmaSN (pred_dvd)
open Erdos634.LemmaSGprime (Sp tau lemmaG' Sp_mul tau_mul Sp_pp tau_pp)
open Erdos634.LemmaSIso (conductor_changeLevel_of_isPrimitive two_ne_pm_one)

/-! ### The G′ step -/

/-- From the relation at every primitive η mod d to Sp(d) and the sign (§4, "By G′ …"). -/
theorem rel_Gprime {d : ℕ} [NeZero d] (hd4 : d % 4 ≠ 2) (Ex Ey : ℚ) (x y : ℕ) (hx : x.Coprime d)
    (hy : y.Coprime d) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (z : ℤ) (hz : z * (σ * y) ≡ x [ZMOD d])
    (hrel : ∀ η : DirichletCharacter ℂ d, η.IsPrimitive →
      (Ex : ℂ) * η (x : ZMod d) + (σ : ℂ) * Ey * η (((σ * y : ℤ)) : ZMod d) = 0) :
    (Ex = 0 ∧ Ey = 0) ∨ (Sp d z ∧ Ey = -σ * (-1) ^ tau d z * Ex) := by
  obtain ⟨η0, hη0⟩ := Erdos634.LemmaSGprime.exists_primitive (NeZero.ne d) hd4
  have hxu : IsUnit ((x : ℕ) : ZMod d) := (ZMod.isUnit_iff_coprime x d).2 hx
  have hyu : IsUnit ((y : ℕ) : ZMod d) := (ZMod.isUnit_iff_coprime y d).2 hy
  have hsy : IsUnit (((σ * y : ℤ)) : ZMod d) := by
    rcases hσ with rfl | rfl
    · rw [show (((1 * y : ℤ)) : ZMod d) = (y : ZMod d) by push_cast; ring]; exact hyu
    · rw [show (((-1 * y : ℤ)) : ZMod d) = -(y : ZMod d) by push_cast; ring]; exact hyu.neg
  have hσ2 : (σ : ℂ) * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσ0 : (σ : ℂ) ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  obtain ⟨uy, huy⟩ := hsy
  obtain ⟨ux, hux⟩ := hxu
  have hne : ∀ η : DirichletCharacter ℂ d, η (((σ * y : ℤ)) : ZMod d) ≠ 0 := by
    intro η; rw [← huy]; exact Erdos634.DirichletCRT.unit_val_ne_zero _ _
  by_cases hEx : Ex = 0
  · left
    refine ⟨hEx, ?_⟩
    have := hrel η0 hη0
    rw [hEx, Rat.cast_zero, zero_mul, zero_add] at this
    have h2 := (mul_eq_zero.1 this).resolve_right (hne η0)
    exact_mod_cast (mul_eq_zero.1 h2).resolve_left hσ0
  · right
    set g : (ZMod d)ˣ := ux * uy⁻¹
    have hzg : ((z : ℤ) : ZMod d) = g := by
      have h1 : ((z : ℤ) : ZMod d) * (((σ * y : ℤ)) : ZMod d) = (x : ZMod d) := by
        have := (ZMod.intCast_eq_intCast_iff (z * (σ * y)) x d).2 hz
        rw [Int.cast_mul, Int.cast_natCast] at this; exact this
      have hyy : (((σ * y : ℤ)) : ZMod d) * ((uy⁻¹ : (ZMod d)ˣ) : ZMod d) = 1 := by
        rw [← huy, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      calc ((z : ℤ) : ZMod d)
          = ((z : ℤ) : ZMod d) * (((σ * y : ℤ)) : ZMod d) * ((uy⁻¹ : (ZMod d)ˣ) : ZMod d) := by
            rw [mul_assoc, hyy, mul_one]
        _ = _ := by rw [h1, ← hux, ← Units.val_mul]
    have hEx' : ((Ex : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hEx
    have hval : ∀ η : DirichletCharacter ℂ d, η.IsPrimitive → η (g : ZMod d) = -(σ : ℂ) * Ey / Ex := by
      intro η hη
      have hk := hrel η hη
      have hinv : η ((uy⁻¹ : (ZMod d)ˣ) : ZMod d) * η (((σ * y : ℤ)) : ZMod d) = 1 := by
        rw [← huy, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
      rw [eq_div_iff hEx']
      simp only [g, Units.val_mul, map_mul, hux]
      linear_combination η ((uy⁻¹ : (ZMod d)ˣ) : ZMod d) * hk - (σ : ℂ) * Ey * hinv
    obtain ⟨G1, G2⟩ := lemmaG' (NeZero.ne d) hd4 g z hzg
    have hSp : Sp d z := G1.1 ⟨_, hval⟩
    refine ⟨hSp, ?_⟩
    have h := G2 hSp η0 hη0
    rw [hval η0 hη0, div_eq_iff hEx'] at h
    have : ((Ey : ℚ) : ℂ) = ((-σ * (-1) ^ tau d z * Ex : ℚ) : ℂ) := by
      push_cast; linear_combination (-(σ : ℂ)) * h - (Ey : ℂ) * hσ2
    exact_mod_cast this

section L
variable {p r m : ℕ} [hp : Fact p.Prime] [NeZero m]

/-- **The top-level relation** (N(a) at every primitive η mod m, both signs σ). -/
theorem fc_key (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (x y : ℕ) (hx : x ∈ fullPts p m a) (hy : y ∈ fullPts p m a) (hxy : x ≠ y)
    (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (hβ : (y : ZMod (p ^ r)) = (σ : ZMod (p ^ r)) * x)
    (hsep : ∀ w ∈ fullPts p m a, w ≠ x → w ≠ y → classSum a e w ≠ 0 →
      (w : ZMod (p ^ r)) ≠ x ∧ (w : ZMod (p ^ r)) ≠ -x)
    (hN : 2 * ((fullPts p m a).image (fun y : ℕ => (y : ZMod (p ^ r)))).card <
      (univ.filter (fun v : (ZMod (p ^ r))ˣ => ZMod.unitsMap (pred_dvd p r) v = 1)).card) :
    ∀ η : DirichletCharacter ℂ m, η.IsPrimitive →
      ((classSum a e x : ℚ) : ℂ) * η (x : ZMod m) +
        (σ : ℂ) * (classSum a e y : ℚ) * η (((σ * y : ℤ)) : ZMod m) = 0 := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  intro η hη
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
  have hs := fc_symm hr hpm a e hP hη hN ux
  have hzero : ∀ w ∈ fullPts p m a, w ≠ x → w ≠ y → ∀ t : ZMod (p ^ r), (t = x ∨ t = -x) →
      (if t = (w : ZMod (p ^ r)) then ((classSum a e w : ℚ) : ℂ) * η (w : ZMod m) else 0) = 0 := by
    intro w hw hwx hwy t ht
    by_cases hE : classSum a e w = 0
    · split_ifs <;> simp [hE]
    · rw [if_neg]
      rcases ht with rfl | rfl
      · exact fun h => (hsep w hw hwx hwy hE).1 h.symm
      · exact fun h => (hsep w hw hwx hwy hE).2 h.symm
  rcases hσ with rfl | rfl
  · -- same β
    have hβ' : (y : ZMod (p ^ r)) = x := by rw [hβ]; push_cast; ring
    have h1 : PhiF p r m η a e ux =
        ((classSum a e x : ℚ) : ℂ) * η (x : ZMod m) + ((classSum a e y : ℚ) : ℂ) * η (y : ZMod m) := by
      unfold PhiF
      rw [sum_eq_add_of_mem x y hx hy hxy]
      · rw [if_pos hux, if_pos (by rw [hux, hβ'])]
      · intro w hw ⟨hwx, hwy⟩; rw [hux]; exact hzero w hw hwx hwy _ (Or.inl rfl)
    have h2 : PhiF p r m η a e (-ux) = 0 := by
      unfold PhiF
      refine sum_eq_zero (fun w hw => ?_)
      rw [Units.val_neg, hux]
      by_cases hwx : w = x
      · subst hwx; rw [if_neg (fun h => hxx h.symm)]
      by_cases hwy : w = y
      · subst hwy; rw [if_neg (fun h => hxx (by rw [h, hβ']))]
      exact hzero w hw hwx hwy _ (Or.inr rfl)
    rw [h1, h2, mul_zero] at hs
    rw [show (((1 * y : ℤ)) : ZMod m) = (y : ZMod m) by push_cast; ring]
    push_cast; linear_combination hs
  · -- opposite β
    have hβ' : (y : ZMod (p ^ r)) = -x := by rw [hβ]; push_cast; ring
    have hyx : (y : ZMod (p ^ r)) ≠ x := fun h => hxx (h.symm.trans hβ')
    have h1 : PhiF p r m η a e ux = ((classSum a e x : ℚ) : ℂ) * η (x : ZMod m) := by
      unfold PhiF
      rw [sum_eq_single x]
      · rw [if_pos hux]
      · intro w hw hwx
        rw [hux]
        by_cases hwy : w = y
        · subst hwy; rw [if_neg (fun h => hyx h.symm)]
        exact hzero w hw hwx hwy _ (Or.inl rfl)
      · intro h; exact absurd hx h
    have h2 : PhiF p r m η a e (-ux) = ((classSum a e y : ℚ) : ℂ) * η (y : ZMod m) := by
      unfold PhiF
      rw [sum_eq_single y]
      · rw [Units.val_neg, hux, if_pos hβ'.symm]
      · intro w hw hwy
        rw [Units.val_neg, hux]
        by_cases hwx : w = x
        · subst hwx; rw [if_neg (fun h => hxx h.symm)]
        exact hzero w hw hwx hwy _ (Or.inr rfl)
      · intro h; exact absurd hy h
    rw [h1, h2] at hs
    have hm1 : η (((-1 * y : ℤ)) : ZMod m) = η (-1) * η (y : ZMod m) := by
      rw [← map_mul]; congr 1; push_cast; ring
    rw [hm1]; push_cast; linear_combination hs

/-- The value of a raised character's primitive part at a residue prime to the level. -/
theorem primChar_lift {f : ℕ} [NeZero f] (h : f ∣ m) (η₀ : DirichletCharacter ℂ f) (b : ℕ)
    (hb : b.Coprime m) :
    (changeLevel h η₀).primitiveCharacter (b : ZMod (changeLevel h η₀).conductor) = η₀ (b : ZMod f) := by
  set χ := changeLevel h η₀
  have e1 : χ (b : ZMod m) = η₀ (b : ZMod f) := changeLevel_nat h η₀ b hb
  have e2 : χ (b : ZMod m) = χ.primitiveCharacter (b : ZMod χ.conductor) := by
    conv_lhs => rw [← changeLevel_primitiveCharacter χ]
    exact changeLevel_nat _ _ b hb
  rw [← e2, e1]

theorem three_ne_pm_one {P : ℕ} (hP : 7 ≤ P) :
    ((3 : ℕ) : ZMod P) ≠ 1 ∧ ((3 : ℕ) : ZMod P) ≠ -1 := by
  constructor
  · intro h
    rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff] at h
    unfold Nat.ModEq at h
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
    omega
  · intro h
    have h4 : ((4 : ℕ) : ZMod P) = 0 := by
      rw [show (4 : ℕ) = 3 + 1 by rfl, Nat.cast_add, h, Nat.cast_one]; ring
    rw [ZMod.natCast_eq_zero_iff] at h4
    exact absurd (Nat.le_of_dvd (by norm_num) h4) (by omega)

/-- Step 3's choice: some ψ ∈ X_ε makes a single Euler factor at q ∈ {2, 3} nonzero (Lemma G). -/
theorem exists_good_psi (hp7 : 7 ≤ p) (hr : 1 ≤ r) {ε : ℂ} (hε : ε = 1 ∨ ε = -1) {q : ℕ}
    (hq : q = 2 ∨ q = 3) (E : Finset ℕ) (hE : E ⊆ {q}) (c : ℕ → ℂ) :
    ∃ ψ : DirichletCharacter ℂ (p ^ r), ψ.IsPrimitive ∧ ψ (-1) = ε ∧
      ∏ ℓ ∈ E, (1 - ψ⁻¹ (ℓ : ZMod (p ^ r)) * c ℓ) ≠ 0 := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hP7 : 7 ≤ p ^ r := le_trans hp7 (Nat.le_self_pow (by omega) p)
  by_contra H
  push Not at H
  have hcq : q.Coprime (p ^ r) := Nat.Coprime.pow_right r
    ((Nat.coprime_primes (by rcases hq with rfl | rfl <;> norm_num) hp.out).2 (by omega))
  set gq : (ZMod (p ^ r))ˣ := ZMod.unitOfCoprime q hcq
  have hgq : (gq : ZMod (p ^ r)) = ((q : ℕ) : ZMod (p ^ r)) := ZMod.coe_unitOfCoprime q hcq
  have hpm1 : ((q : ℕ) : ZMod (p ^ r)) ≠ 1 ∧ ((q : ℕ) : ZMod (p ^ r)) ≠ -1 := by
    rcases hq with rfl | rfl
    · exact two_ne_pm_one hP7
    · exact three_ne_pm_one hP7
  rcases subset_singleton_iff.1 hE with h0 | h1
  · have := Erdos634.LemmaSG2.lemmaG hp7 hr hε gq 0 (fun ψ hψ hψε => by
      have := H ψ hψ hψε; rw [h0, prod_empty] at this; exact absurd this one_ne_zero)
    rw [hgq] at this
    rcases this with h | h
    · exact hpm1.1 h
    · exact hpm1.2 h
  · have := Erdos634.LemmaSG2.lemmaG hp7 hr hε gq (c q) (fun ψ hψ hψε => by
      have h := H ψ hψ hψε
      rw [h1, prod_singleton] at h
      have hψq : ψ (gq : ZMod (p ^ r)) ≠ 0 := Erdos634.DirichletCRT.unit_val_ne_zero _ _
      rw [hgq] at hψq ⊢
      rw [MulChar.inv_apply_eq_inv'] at h
      have h' : (ψ ((q : ℕ) : ZMod (p ^ r)))⁻¹ * c q = 1 := by linear_combination -h
      calc ψ ((q : ℕ) : ZMod (p ^ r))
          = ψ ((q : ℕ) : ZMod (p ^ r)) * ((ψ ((q : ℕ) : ZMod (p ^ r)))⁻¹ * c q) := by rw [h', mul_one]
        _ = c q := by rw [← mul_assoc, mul_inv_cancel₀ hψq, one_mul])
    rw [hgq] at this
    rcases this with h | h
    · exact hpm1.1 h
    · exact hpm1.2 h

/-- **The level-f₂ relation** (Lemma L, steps 2–3). -/
theorem key_level2 (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (x y : ℕ) (hx : x ∈ fullPts p m a) (hy : y ∈ fullPts p m a) (hxy : x ≠ y)
    (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (hβ : (y : ZMod (p ^ r)) = (σ : ZMod (p ^ r)) * x)
    {f : ℕ} [NeZero f] (hfm : f ∣ m) {q : ℕ} (hq : q = 2 ∨ q = 3) (hE : eulerPrimes m f ⊆ {q})
    (hdie : ∀ w ∈ univ.image a, w ≠ x → w ≠ y → ¬ p ∣ w → classSum a e w ≠ 0 → ¬ f ∣ dm m w) :
    ∀ η₀ : DirichletCharacter ℂ f, η₀.IsPrimitive →
      ((classSum a e x : ℚ) : ℂ) * η₀ (x : ZMod f) +
        (σ : ℂ) * (classSum a e y : ℚ) * η₀ (((σ * y : ℤ)) : ZMod f) = 0 := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  intro η₀ hη₀
  set η : DirichletCharacter ℂ m := changeLevel hfm η₀
  have hηc : η.conductor = f := conductor_changeLevel_of_isPrimitive hfm hη₀
  set ε : ℂ := -η (-1)
  have hε : ε = 1 ∨ ε = -1 := by
    rcases η.even_or_odd with h | h
    · right; simp only [ε, show η (-1) = 1 from h]
    · left; simp only [ε, show η (-1) = -1 from h, neg_neg]
  have hη2 : η (-1) * η (-1) = 1 := by
    rcases η.even_or_odd with h | h
    · rw [show η (-1) = 1 from h]; ring
    · rw [show η (-1) = -1 from h]; ring
  have hE' : eulerPrimes m η.conductor ⊆ {q} := by rw [hηc]; exact hE
  obtain ⟨ψ, hψ, hψε, hEul⟩ := exists_good_psi hp7 hr hε hq (eulerPrimes m η.conductor) hE'
    (fun ℓ => η.primitiveCharacter⁻¹ (ℓ : ZMod η.conductor))
  have hodd : (chi ψ η).Odd := by
    show (chi ψ η) (-1) = -1
    rw [MulChar.coeToFun_mul, Pi.mul_apply,
      Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_right (p ^ r) m) ψ,
      Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_left m (p ^ r)) η, hψε]
    simp only [ε]; linear_combination -hη2
  have hsum := hP (chi ψ η) hodd (by rw [conductor_chi hpm hψ η]; exact Nat.dvd_mul_right _ _)
  rw [regroup, sum_coe_sort (univ.image a)
    (fun w => ((classSum a e w : ℚ) : ℂ) * bracket (chi ψ η) w)] at hsum
  have hxf := mem_filter.1 hx
  have hyf := mem_filter.1 hy
  rw [sum_eq_add_of_mem x y hxf.1 hyf.1 hxy] at hsum
  swap
  · intro w hw ⟨hwx, hwy⟩
    by_cases hpw : p ∣ w
    · rw [bracket_p_dvd hr hpm hψ η w hpw, mul_zero]
    by_cases hEw : classSum a e w = 0
    · rw [hEw]; simp
    rw [bracket_unit hpm hψ η w hpw, if_neg (by rw [hηc]; exact hdie w hw hwx hwy hpw hEw), mul_zero]
  -- the two surviving terms
  have hterm : ∀ t : ℕ, t ∈ fullPts p m a →
      bracket (chi ψ η) t = ψ (t : ZMod (p ^ r)) * η₀ (t : ZMod f) *
        ∏ ℓ ∈ eulerPrimes m η.conductor,
          (1 - ψ⁻¹ (ℓ : ZMod (p ^ r)) * η.primitiveCharacter⁻¹ (ℓ : ZMod η.conductor)) := by
    intro t ht
    have htf := mem_filter.1 ht
    have hdm : dm m t = m := (dm_eq_iff t).2 htf.2.2
    have hg : m.gcd t = 1 := Nat.coprime_comm.1 htf.2.2
    rw [bracket_unit hpm hψ η t htf.2.1, if_pos (by rw [hηc, hdm]; exact hfm), hg, Nat.div_one, hdm,
      primChar_lift hfm η₀ t htf.2.2,
      div_self (by exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne m))).ne'),
      one_mul]
  rw [hterm x hx, hterm y hy] at hsum
  set Eul := ∏ ℓ ∈ eulerPrimes m η.conductor,
    (1 - ψ⁻¹ (ℓ : ZMod (p ^ r)) * η.primitiveCharacter⁻¹ (ℓ : ZMod η.conductor))
  have hψx : ψ (x : ZMod (p ^ r)) ≠ 0 := by
    have hxP : x.Coprime (p ^ r) :=
      Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hxf.2.1).symm
    rw [← ZMod.coe_unitOfCoprime x hxP]; exact Erdos634.DirichletCRT.unit_val_ne_zero _ _
  have hψy : ψ (y : ZMod (p ^ r)) = ψ (σ : ZMod (p ^ r)) * ψ (x : ZMod (p ^ r)) := by
    rw [hβ, map_mul]
  rw [hψy] at hsum
  have hfac : ψ (x : ZMod (p ^ r)) * Eul *
      (((classSum a e x : ℚ) : ℂ) * η₀ (x : ZMod f) +
        ψ (σ : ZMod (p ^ r)) * ((classSum a e y : ℚ) : ℂ) * η₀ (y : ZMod f)) = 0 := by
    linear_combination hsum
  have hrel := (mul_eq_zero.1 hfac).resolve_left (mul_ne_zero hψx hEul)
  rcases hσ with rfl | rfl
  · rw [show (((1 * y : ℤ)) : ZMod f) = (y : ZMod f) by push_cast; ring]
    simp only [Int.cast_one, map_one] at hrel
    push_cast; linear_combination hrel
  · have hm1 : η₀ (((-1 * y : ℤ)) : ZMod f) = η₀ (-1) * η₀ (y : ZMod f) := by
      rw [← map_mul]; congr 1; push_cast; ring
    have hψm : ψ ((-1 : ℤ) : ZMod (p ^ r)) = -η₀ (-1) := by
      rw [Int.cast_neg, Int.cast_one, hψε]
      simp only [ε, η, Erdos634.LemmaSG2.changeLevel_neg_one]
    rw [hψm] at hrel
    rw [hm1]; push_cast; linear_combination hrel

/-- **Step 4**: passing from m = q^v m' to f₂ = q^{v'} m' removes exactly the q-component. -/
theorem tau_drop {q v v' m' : ℕ} (hq : q.Prime) (hv : 1 ≤ v) (hm' : m' ≠ 0) (hqm' : ¬ q ∣ m')
    {z : ℤ} (hSp : Sp (q ^ v * m') z) (hne : ¬ z ≡ 1 [ZMOD (q : ℤ) ^ v])
    (hv' : v' = 0 ∨ (q = 2 ∧ v' = v - 1 ∧ 3 ≤ v)) :
    Sp (q ^ v' * m') z ∧ tau (q ^ v' * m') z + 1 = tau (q ^ v * m') z := by
  have hc : ∀ k, (q ^ k).Coprime m' := fun k =>
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hq).2 hqm')
  have hq0 : ∀ k, q ^ k ≠ 0 := fun k => pow_ne_zero _ hq.ne_zero
  obtain ⟨hSq, hSm'⟩ := (Sp_mul (hc v) (hq0 v) hm' z).1 hSp
  rw [Sp_pp hq (by omega)] at hSq
  have htv : tau (q ^ v * m') z = 1 + tau m' z := by
    rw [tau_mul (hc v) (hq0 v) hm', tau_pp hq (by omega), if_neg hne]
  rcases hv' with rfl | ⟨rfl, rfl, hv3⟩
  · rw [pow_zero, one_mul, htv]; exact ⟨hSm', by ring⟩
  · have hz1 : z ≡ 1 [ZMOD ((2 : ℕ) : ℤ) ^ (v - 1)] := by
      rcases hSq with h | ⟨h, -⟩ | ⟨-, -, h⟩
      · exact absurd h hne
      · exact absurd h (by norm_num)
      · have hp' : (2 : ℤ) ^ v = 2 ^ (v - 1) * 2 := by rw [← pow_succ]; congr 1; omega
        have h' := h.of_dvd (show (2 : ℤ) ^ (v - 1) ∣ 2 ^ v from ⟨2, hp'⟩)
        push_cast
        refine h'.trans ?_
        rw [Int.modEq_iff_dvd]; exact ⟨-1, by ring⟩
    refine ⟨(Sp_mul (hc _) (hq0 _) hm' z).2 ⟨(Sp_pp hq (by omega) z).2 (Or.inl hz1), hSm'⟩, ?_⟩
    rw [tau_mul (hc _) (hq0 _) hm', tau_pp hq (by omega), if_pos hz1, htv]; ring

theorem euler_sub {q v v' m' : ℕ} (hq : q.Prime) {ℓ : ℕ}
    (hl : ℓ ∈ eulerPrimes (q ^ v * m') (q ^ v' * m')) : ℓ = q := by
  simp only [eulerPrimes, mem_filter, Nat.mem_primeFactors] at hl
  obtain ⟨⟨hl, hld, -⟩, hn⟩ := hl
  rcases hl.dvd_mul.1 hld with h | h
  · exact (Nat.prime_dvd_prime_iff_eq hl hq).1 (hl.dvd_of_dvd_pow h)
  · exact absurd (dvd_mul_of_dvd_right h _) hn

theorem f2_mod4 {q v v' m' : ℕ} (hq : q = 2 ∨ q = 3) (hqm' : ¬ q ∣ m')
    (hm4 : (q ^ v * m') % 4 ≠ 2) (hv' : v' = 0 ∨ (q = 2 ∧ v' = v - 1 ∧ 3 ≤ v)) :
    (q ^ v' * m') % 4 ≠ 2 := by
  rcases hv' with rfl | ⟨rfl, rfl, hv3⟩
  · rw [pow_zero, one_mul]
    rcases hq with rfl | rfl
    · omega
    · intro h
      apply hm4
      have ho : 3 ^ v % 4 = 1 ∨ 3 ^ v % 4 = 3 := by
        have : 3 ^ v % 2 = 1 := Nat.pow_mod 3 v 2 ▸ by simp
        omega
      rw [Nat.mul_mod, h]
      rcases ho with e | e <;> rw [e]
  · have : 4 ∣ 2 ^ (v - 1) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]; exact Nat.pow_dvd_pow 2 (by omega)
    have := dvd_mul_of_dvd_left this m'
    omega

/-- **Lemma L**, as written (class form). -/
theorem lemmaL (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m)
    {q v v' m' : ℕ} (hq : q = 2 ∨ q = 3) (hv : 1 ≤ v) (hqm' : ¬ q ∣ m') (hm : m = q ^ v * m')
    (hm4 : m % 4 ≠ 2) (hv' : v' = 0 ∨ (q = 2 ∧ v' = v - 1 ∧ 3 ≤ v))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (x y : ℕ) (hx : x ∈ fullPts p m a) (hy : y ∈ fullPts p m a) (hxy : x ≠ y)
    (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (hβ : (y : ZMod (p ^ r)) = (σ : ZMod (p ^ r)) * x)
    (hsep : ∀ w ∈ fullPts p m a, w ≠ x → w ≠ y → classSum a e w ≠ 0 →
      (w : ZMod (p ^ r)) ≠ x ∧ (w : ZMod (p ^ r)) ≠ -x)
    (hN : 2 * ((fullPts p m a).image (fun y : ℕ => (y : ZMod (p ^ r)))).card <
      (univ.filter (fun v : (ZMod (p ^ r))ˣ => ZMod.unitsMap (pred_dvd p r) v = 1)).card)
    (z : ℤ) (hz : z * (σ * y) ≡ x [ZMOD m]) (hne : ¬ z ≡ 1 [ZMOD (q : ℤ) ^ v])
    (hdie : ∀ w ∈ univ.image a, w ≠ x → w ≠ y → ¬ p ∣ w → classSum a e w ≠ 0 →
      ¬ (q ^ v' * m') ∣ dm m w) :
    classSum a e x = 0 ∧ classSum a e y = 0 := by
  have hqp : q.Prime := by rcases hq with rfl | rfl <;> norm_num
  have hm'0 : m' ≠ 0 := by rintro rfl; rw [mul_zero] at hm; exact NeZero.ne m hm
  haveI : NeZero m' := ⟨hm'0⟩
  set f := q ^ v' * m' with hf
  haveI : NeZero f := ⟨Nat.mul_ne_zero (pow_ne_zero _ hqp.ne_zero) hm'0⟩
  have hfm : f ∣ m := by
    rw [hm]; refine Nat.mul_dvd_mul_right (Nat.pow_dvd_pow q ?_) m'
    rcases hv' with rfl | ⟨-, rfl, -⟩ <;> omega
  have hf4 : f % 4 ≠ 2 := f2_mod4 hq hqm' (hm ▸ hm4) hv'
  have hxf := mem_filter.1 hx
  have hyf := mem_filter.1 hy
  -- top level
  have hmS := rel_Gprime hm4 _ _ x y hxf.2.2 hyf.2.2 σ hσ z hz
    (fc_key hp7 hr hpm a e hP x y hx hy hxy σ hσ hβ hsep hN)
  rcases hmS with h | ⟨hSp, hrel1⟩
  · exact h
  -- one level down
  have hE : eulerPrimes m f ⊆ {q} := fun ℓ hl => mem_singleton.2 (euler_sub hqp (hm ▸ hl))
  have hzf : z * (σ * y) ≡ x [ZMOD f] := hz.of_dvd (by exact_mod_cast hfm)
  have hfS := rel_Gprime hf4 _ _ x y (hxf.2.2.coprime_dvd_right hfm) (hyf.2.2.coprime_dvd_right hfm)
    σ hσ z hzf (key_level2 hp7 hr hpm a e hP x y hx hy hxy σ hσ hβ hfm hq hE hdie)
  obtain ⟨-, htau⟩ := tau_drop hqp hv hm'0 hqm' (hm ▸ hSp) hne hv'
  rw [← hm] at htau
  rcases hfS with h | ⟨-, hrel2⟩
  · exact h
  have hσ2 : (σ : ℚ) * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hx0 : classSum a e x = 0 := by
    have h := hrel1.symm.trans hrel2
    rw [← htau, pow_succ] at h
    have : 2 * ((-1 : ℚ) ^ tau f z * σ) * classSum a e x = 0 := by linear_combination h
    have hne0 : (-1 : ℚ) ^ tau f z * σ ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num)) (by rcases hσ with rfl | rfl <;> norm_num)
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero two_ne_zero hne0)
  exact ⟨hx0, by rw [hrel1, hx0, mul_zero]⟩

end L

/-! ## A genuine consequence (class R1′, q = 3): n = 105 = 7·15, a = (2, 68, 35), p = 7.
Full I-points 2 and 68 (35 has 7 | 35), 68 ≡ −2 (mod 7) (β_k = −β_j), g = 2/(−68) ≡ 11 (mod 15),
g₃ = −1, g₅ = 1, so g ∈ Sp(15) \ {1}: the top level alone does not decide. Lemma L at f₂ = 5 does:
for EVERY e satisfying Lemma P's hypothesis, E₂ = E₆₈ = 0. -/
theorem consequence_105 (e : Fin 3 → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (7 ^ 1 * 15), χ.Odd → 7 ^ 1 ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ ((![2, 68, 35] : Fin 3 → ℕ) j) = 0) :
    classSum ![2, 68, 35] e 2 = 0 ∧ classSum ![2, 68, 35] e 68 = 0 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hfp : fullPts 7 15 (![2, 68, 35] : Fin 3 → ℕ) = {2, 68} := by decide
  have hN : 2 * (fullPts 7 15 (![2, 68, 35] : Fin 3 → ℕ)).card <
      (univ.filter (fun v : (ZMod (7 ^ 1))ˣ => ZMod.unitsMap (pred_dvd 7 1) v = 1)).card := by
    rw [Erdos634.LemmaSFC.card_N le_rfl, hfp]; decide
  exact lemmaL (p := 7) (r := 1) (m := 15) (q := 3) (v := 1) (v' := 0) (m' := 5) (by norm_num)
    le_rfl (by norm_num) (Or.inr rfl) le_rfl (by norm_num) (by norm_num) (by norm_num) (Or.inl rfl)
    _ e hP 2 68 (by rw [hfp]; decide) (by rw [hfp]; decide) (by norm_num) (-1) (Or.inr rfl)
    (by decide) (fun w hw hw1 hw2 _ => by rw [hfp] at hw; simp at hw; omega)
    (lt_of_le_of_lt (Nat.mul_le_mul_left 2 card_image_le) hN) 11 (by decide)
    (by decide)
    (fun w hw hw1 hw2 hpw _ => by
      simp only [mem_image, mem_univ, true_and] at hw
      obtain ⟨j, rfl⟩ := hw
      fin_cases j <;> simp_all)

#print axioms Erdos634.LemmaSL.rel_Gprime
#print axioms Erdos634.LemmaSL.lemmaL
#print axioms Erdos634.LemmaSL.consequence_105

end Erdos634.LemmaSL
