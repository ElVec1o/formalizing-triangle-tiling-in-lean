/-
Lemma S, node A5, class EVEN (n ≡ 2 mod 4): **Theorem T applied at the top conductor**
(round2/PROOF_round2.md §4.2 and §4.1 N±).

For η primitive mod m′ (m = 2m′, m′ odd) the top element Φ_η (`PhiTop`, the five-point element of
`LemmaSEvenT`) satisfies Φ_η = η(−1)[−1]Φ_η (`top_sym`) in each of the cases
  * r ≥ 2 (N(a), per-index count: 3 groups < p);
  * r = 1 and η even (N(b));
  * r = 1, η odd, and the support of Φ ∪ −Φ lies in a set P with |P| < p − 1 (N(c)),
and then Theorem T (`LemmaSEvenT.theoremT`) gives (`top_T`): c_k = 0, and either c_i = c_j = 0,
or a_j ≡ a_i (mod p^r) with c_i + c_j = 0 (P1), or a_j ≡ −a_i with c_i = η(−1)c_j (P2).
In the P1/P2 configurations the support condition of N(c) holds for EVERY η (|P| = 4 < p − 1),
so the relation holds for every primitive η mod m′ (`top_rel_all`), which is what G′ consumes.
Formalization debt, not /goal progress.
-/
import Mathlib
import Erdos634.Draft.LemmaSEvenComp

open scoped BigOperators
open Finset

namespace Erdos634.LemmaSEvenTop

open DirichletCharacter
open Erdos634.LemmaSC (bracket)
open Erdos634.LemmaSN (pred_dvd lemmaN_b lemmaN_c)
open Erdos634.LemmaSEvenT (Phi5 theoremT)
open Erdos634.LemmaSEvenComp

/-- The group of points k·x, k ∈ L. -/
def G {N : ℕ} (x : ZMod N) (L : List ℤ) : Finset (ZMod N) :=
  (L.map (fun k : ℤ => (k : ZMod N) * x)).toFinset

theorem mem_G {N : ℕ} {x v : ZMod N} {L : List ℤ} (k : ℤ) (hk : k ∈ L)
    (hv : v = (k : ZMod N) * x) : v ∈ G x L := by
  unfold G; rw [List.mem_toFinset, List.mem_map]; exact ⟨k, hk, hv.symm⟩

/-- The top element. -/
noncomputable def PhiTop (p r m' : ℕ) (η : DirichletCharacter ℂ m') (a : Fin 3 → ℕ)
    (e : Fin 3 → ℚ) (i j k : Fin 3) (u : ZMod (p ^ r)) : ℂ :=
  Phi5 (cT p m' η a e i) (cT p m' η a e j) (cT p m' η a e k) (η 2)⁻¹
    ((2 : ZMod (p ^ r))⁻¹ * a i) (a j) ((2 : ZMod (p ^ r))⁻¹ * a j)
    ((a k / 2 : ℕ) : ZMod (p ^ r)) u

section
variable {p r m m' : ℕ} [hp : Fact p.Prime] [NeZero m] [NeZero m']

/-- The support of the top element, as the ten candidate points. -/
theorem PhiTop_supp (hp7 : 7 ≤ p) (η : DirichletCharacter ℂ m') (a : Fin 3 → ℕ) (e : Fin 3 → ℚ)
    (i j k : Fin 3) (u : ZMod (p ^ r)) (h : PhiTop p r m' η a e i j k u ≠ 0) :
    u = 2 * ((2 : ZMod (p ^ r))⁻¹ * a i) ∨ u = (2 : ZMod (p ^ r))⁻¹ * a i ∨
      u = 2 * ((2 : ZMod (p ^ r))⁻¹ * a j) ∨ u = (2 : ZMod (p ^ r))⁻¹ * a j ∨
      u = ((a k / 2 : ℕ) : ZMod (p ^ r)) := by
  have hh := two_mul_half (r := r) hp7
  have hy : (a j : ZMod (p ^ r)) = 2 * ((2 : ZMod (p ^ r))⁻¹ * a j) := by
    rw [← mul_assoc, hh, one_mul]
  rcases Erdos634.LemmaSEvenComp.Phi5_supp h with ⟨-, h1 | h1⟩ | ⟨-, h1 | h1⟩ | ⟨-, h1⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl (h1.trans hy)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h1)))

/-- **N± at the top conductor**: Φ_η = η(−1)[−1]Φ_η. -/
theorem top_sym (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) (hm : m = 2 * m')
    (hodd : m' % 2 = 1) (hdvd : m' ∣ m) {η : DirichletCharacter ℂ m'} (hη : η.IsPrimitive)
    (a : Fin 3 → ℕ) (e : Fin 3 → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hi : a i % 2 = 1)
    (hj : a j % 2 = 1) (hk : a k % 2 = 0)
    (hcase : 2 ≤ r ∨ (r = 1 ∧ (η.Even ∨ ∃ P : Finset (ZMod (p ^ r)),
      (∀ v : ZMod (p ^ r), IsUnit v → (PhiTop p r m' η a e i j k v ≠ 0 ∨
        PhiTop p r m' η a e i j k (-v) ≠ 0) → v ∈ P) ∧ P.card < p - 1))) :
    ∀ u : ZMod (p ^ r), IsUnit u →
      PhiTop p r m' η a e i j k u = η (-1) * PhiTop p r m' η a e i j k (-u) := by
  have hvan := top_vanish hp7 hr hpm hm hodd hdvd hη a e hP i j k hij hik hjk hi hj hk
  set Φ : (ZMod (p ^ r))ˣ → ℂ := fun v => PhiTop p r m' η a e i j k (v : ZMod (p ^ r)) with hΦ
  have hΦneg : ∀ v : (ZMod (p ^ r))ˣ, Φ (-v) = PhiTop p r m' η a e i j k (-(v : ZMod (p ^ r))) :=
    fun v => by simp only [Φ, Units.val_neg]
  have hvan' : ∀ ψ : DirichletCharacter ℂ (p ^ r), ψ.IsPrimitive → ψ (-1) = -η (-1) →
      ∑ u : (ZMod (p ^ r))ˣ, ψ (u : ZMod (p ^ r)) * Φ u = 0 := hvan
  intro u hu
  obtain ⟨U, rfl⟩ := hu
  rw [← hΦneg]
  change Φ U = η (-1) * Φ (-U)
  rcases hcase with hr2 | ⟨rfl, hc⟩
  · have hε : -η (-1) = 1 ∨ -η (-1) = -1 := by
      rcases η.even_or_odd with h | h
      · right; rw [show η (-1) = 1 from h]
      · left; rw [show η (-1) = -1 from h, neg_neg]
    have hh := two_mul_half (r := r) hp7
    set w := (2 : ZMod (p ^ r))⁻¹ * (a i : ZMod (p ^ r))
    set y' := (2 : ZMod (p ^ r))⁻¹ * (a j : ZMod (p ^ r))
    set V := ((a k / 2 : ℕ) : ZMod (p ^ r))
    let T : Fin 3 → Finset (ZMod (p ^ r)) :=
      ![G w [2, -2, 1, -1], G y' [2, -2, 1, -1], G V [1, -1]]
    have hsupp : ∀ v : (ZMod (p ^ r))ˣ, Φ v ≠ 0 ∨ Φ (-v) ≠ 0 → ∃ i, (v : ZMod (p ^ r)) ∈ T i := by
      intro v hv
      rcases hv with hv | hv
      · rcases PhiTop_supp hp7 η a e i j k _ hv with h1 | h1 | h1 | h1 | h1
        · exact ⟨0, mem_G 2 (by simp) (by rw [h1]; push_cast; ring)⟩
        · exact ⟨0, mem_G 1 (by simp) (by rw [h1]; push_cast; ring)⟩
        · exact ⟨1, mem_G 2 (by simp) (by rw [h1]; push_cast; ring)⟩
        · exact ⟨1, mem_G 1 (by simp) (by rw [h1]; push_cast; ring)⟩
        · exact ⟨2, mem_G 1 (by simp) (by rw [h1]; push_cast; ring)⟩
      · rw [hΦneg] at hv
        rcases PhiTop_supp hp7 η a e i j k _ hv with h1 | h1 | h1 | h1 | h1
        · exact ⟨0, mem_G (-2) (by simp) (by rw [← neg_neg (v : ZMod (p ^ r)), h1]; push_cast; ring)⟩
        · exact ⟨0, mem_G (-1) (by simp) (by rw [← neg_neg (v : ZMod (p ^ r)), h1]; push_cast; ring)⟩
        · exact ⟨1, mem_G (-2) (by simp) (by rw [← neg_neg (v : ZMod (p ^ r)), h1]; push_cast; ring)⟩
        · exact ⟨1, mem_G (-1) (by simp) (by rw [← neg_neg (v : ZMod (p ^ r)), h1]; push_cast; ring)⟩
        · exact ⟨2, mem_G (-1) (by simp) (by rw [← neg_neg (v : ZMod (p ^ r)), h1]; push_cast; ring)⟩
    have hinj : ∀ i, ∀ x ∈ T i, ∀ y ∈ T i, IsUnit x → IsUnit y →
        ZMod.castHom (dvd_pow_self p (by omega : r ≠ 0)) (ZMod p) x =
          ZMod.castHom (dvd_pow_self p (by omega : r ≠ 0)) (ZMod p) y → x = y := by
      intro t
      fin_cases t
      · exact inj_group hp7 (by omega) [2, -2, 1, -1] (by decide) w
      · exact inj_group hp7 (by omega) [2, -2, 1, -1] (by decide) y'
      · exact inj_group hp7 (by omega) [1, -1] (by decide) V
    have := lemmaN_groups hr2 Φ hε hvan' (k := 3) (by omega) T hsupp hinj U
    rw [this, neg_neg]
  · rcases η.even_or_odd with hev | hod
    · have := lemmaN_b Φ (fun ψ hψ h1 => hvan' ψ hψ (by rw [h1, show η (-1) = 1 from hev])) U
      rw [this, show η (-1) = 1 from hev, one_mul]
    · rcases hc with hc | ⟨P, hPs, hPc⟩
      · exfalso
        have h1 : η (-1) = 1 := hc
        have h2 : η (-1) = -1 := hod
        rw [h1] at h2; norm_num at h2
      · have hcard : (univ.filter (fun v : (ZMod (p ^ 1))ˣ => Φ v + Φ (-v) ≠ 0)).card < p - 1 := by
          refine lt_of_le_of_lt ?_ hPc
          calc _ ≤ (univ.filter (fun v : (ZMod (p ^ 1))ˣ => (v : ZMod (p ^ 1)) ∈ P)).card := by
                refine card_le_card (fun v hv => ?_)
                have hv' := (mem_filter.1 hv).2
                refine mem_filter.2 ⟨mem_univ _, hPs _ v.isUnit ?_⟩
                by_contra hno
                push Not at hno
                apply hv'
                rw [hΦneg]; simp only [Φ, hno.1, hno.2, add_zero]
            _ ≤ P.card := by
                refine card_le_card_of_injOn (fun v => (v : ZMod (p ^ 1))) ?_ ?_
                · intro v hv; exact (mem_filter.1 hv).2
                · intro v _ w _ hvw; exact Units.ext hvw
        have := lemmaN_c Φ (fun ψ hψ h1 => hvan' ψ hψ
          (by rw [h1, show η (-1) = -1 from hod, neg_neg])) hcard U
        rw [this, show η (-1) = -1 from hod]; ring

/-- **Theorem T at the top conductor.** -/
theorem top_T (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) (hm : m = 2 * m')
    (hodd : m' % 2 = 1) (hdvd : m' ∣ m) {η : DirichletCharacter ℂ m'} (hη : η.IsPrimitive)
    (a : Fin 3 → ℕ) (e : Fin 3 → ℚ) (hsum : a 0 + a 1 + a 2 = p ^ r * m)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hk : a k % 2 = 0)
    (hsym : ∀ u : ZMod (p ^ r), IsUnit u →
      PhiTop p r m' η a e i j k u = η (-1) * PhiTop p r m' η a e i j k (-u)) :
    cT p m' η a e k = 0 ∧
      ((cT p m' η a e i = 0 ∧ cT p m' η a e j = 0) ∨
        ((a j : ZMod (p ^ r)) = a i ∧ cT p m' η a e i + cT p m' η a e j = 0) ∨
        ((a j : ZMod (p ^ r)) = -(a i : ZMod (p ^ r)) ∧
          cT p m' η a e i = η (-1) * cT p m' η a e j)) := by
  have hh := two_mul_half (r := r) hp7
  have u2 : IsUnit (2 : ZMod (p ^ r)) := by
    have := isUnit_small (r := r) hp.out (k := 2) (by norm_num) (by norm_num) hp7
    rwa [Nat.cast_ofNat] at this
  have u3 : IsUnit (3 : ZMod (p ^ r)) := by
    have := isUnit_small (r := r) hp.out (k := 3) (by norm_num) (by norm_num) hp7
    rwa [Nat.cast_ofNat] at this
  have u5 : IsUnit (5 : ZMod (p ^ r)) := by
    have := isUnit_small (r := r) hp.out (k := 5) (by norm_num) (by norm_num) hp7
    rwa [Nat.cast_ofNat] at this
  have uh : IsUnit ((2 : ZMod (p ^ r))⁻¹) := IsUnit.of_mul_eq_one_right _ hh
  haveI : Fact (1 < p ^ r) := ⟨Nat.one_lt_pow (by omega) hp.out.one_lt⟩
  have hunit : ∀ t, ¬ p ∣ a t → IsUnit ((a t : ℕ) : ZMod (p ^ r)) := fun t h =>
    (ZMod.isUnit_iff_coprime _ _).2
      (Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp.out).2 h).symm)
  have hunit' : ∀ b : ℕ, ¬ p ∣ b → IsUnit ((b : ℕ) : ZMod (p ^ r)) := fun b h =>
    (ZMod.isUnit_iff_coprime _ _).2
      (Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp.out).2 h).symm)
  have hcT : ∀ t, cT p m' η a e t ≠ 0 → ¬ p ∣ a t := by
    intro t h hpa; apply h; unfold cT; rw [if_neg (fun h' => h'.1 hpa)]
  have hsum3 : ((a i : ℕ) : ZMod (p ^ r)) + a j + a k = 0 := by
    have h0 : ((a 0 + a 1 + a 2 : ℕ) : ZMod (p ^ r)) = 0 := by
      rw [hsum, Nat.cast_mul, ZMod.natCast_self, zero_mul]
    push_cast at h0
    fin_cases i <;> fin_cases j <;> fin_cases k
    all_goals first
      | exact absurd rfl hij | exact absurd rfl hik | exact absurd rfl hjk
      | (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at h0 ⊢; linear_combination h0)
  set V := ((a k / 2 : ℕ) : ZMod (p ^ r)) with hV
  have h2V : (2 : ZMod (p ^ r)) * V = a k := by
    rw [hV, show (2 : ZMod (p ^ r)) = ((2 : ℕ) : ZMod (p ^ r)) by norm_num, ← Nat.cast_mul,
      Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hk)]
  have hrel : 2 * ((2 : ZMod (p ^ r))⁻¹ * a i) + a j + 2 * V = 0 := by
    rw [← mul_assoc, hh, one_mul, h2V]; exact hsum3
  have hy' : 2 * ((2 : ZMod (p ^ r))⁻¹ * a j) = a j := by rw [← mul_assoc, hh, one_mul]
  have hz : (η 2)⁻¹ ≠ 0 := by
    have hu : IsUnit (2 : ZMod m') := by
      have := (ZMod.isUnit_iff_coprime 2 m').2 (Nat.coprime_two_left.2 (Nat.odd_iff.2 hodd))
      rwa [Nat.cast_ofNat] at this
    obtain ⟨u2', hu2'⟩ := hu
    rw [← hu2']
    exact inv_ne_zero (Erdos634.DirichletCRT.unit_val_ne_zero η u2')
  have hc1 : cT p m' η a e i ≠ 0 → IsUnit ((2 : ZMod (p ^ r))⁻¹ * a i) :=
    fun h => uh.mul (hunit i (hcT i h))
  have hc2 : cT p m' η a e j ≠ 0 → IsUnit ((2 : ZMod (p ^ r))⁻¹ * a j) :=
    fun h => uh.mul (hunit j (hcT j h))
  have hc3 : cT p m' η a e k ≠ 0 → IsUnit V := by
    intro h
    have hpk := hcT k h
    have hpk2 : ¬ p ∣ a k / 2 := fun hd => hpk (by
      rw [← Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hk)]; exact dvd_mul_of_dvd_right hd 2)
    exact hunit' _ hpk2
  obtain ⟨h3, h⟩ := theoremT u2 u3 u5 hrel hy' hz hc1 hc2 hc3 hsym
  refine ⟨h3, ?_⟩
  rcases h with h | ⟨hy, hs⟩ | ⟨hy, hs⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨by rw [hy, ← mul_assoc, hh, one_mul], hs⟩)
  · exact Or.inr (Or.inr ⟨by rw [hy, ← mul_assoc, hh, one_mul], hs⟩)

/-- The sum relation at level p^r. -/
theorem sum3_zmod (a : Fin 3 → ℕ) (hsum : a 0 + a 1 + a 2 = p ^ r * m) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ((a i : ℕ) : ZMod (p ^ r)) + a j + a k = 0 := by
  have h0 : ((a 0 + a 1 + a 2 : ℕ) : ZMod (p ^ r)) = 0 := by
    rw [hsum, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  push_cast at h0
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals first
    | exact absurd rfl hij | exact absurd rfl hik | exact absurd rfl hjk
    | (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at h0 ⊢; linear_combination h0)

/-- **The top relation for every primitive η**, in the configurations P1 (σ = 1) and P2 (σ = −1)
with both odd points full (the input of G′). -/
theorem top_rel_all (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) (hm : m = 2 * m')
    (hodd : m' % 2 = 1) (hdvd : m' ∣ m) (a : Fin 3 → ℕ) (e : Fin 3 → ℚ)
    (hsum : a 0 + a 1 + a 2 = p ^ r * m)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hi : a i % 2 = 1)
    (hj : a j % 2 = 1) (hk : a k % 2 = 0)
    (hfi : ¬ p ∣ a i ∧ (a i).Coprime m') (hfj : ¬ p ∣ a j ∧ (a j).Coprime m')
    (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (hβ : (a j : ZMod (p ^ r)) = (σ : ZMod (p ^ r)) * a i) :
    ∀ η : DirichletCharacter ℂ m', η.IsPrimitive →
      ((e i : ℚ) : ℂ) * η (a i : ZMod m') + (σ : ℂ) * (e j : ℚ) * η (((σ * a j : ℤ)) : ZMod m') = 0 := by
  intro η hη
  have hh := two_mul_half (r := r) hp7
  have hh' : (2 : ZMod (p ^ r))⁻¹ * 2 = 1 := by rw [mul_comm]; exact hh
  have u2 : IsUnit (2 : ZMod (p ^ r)) := by
    have := isUnit_small (r := r) hp.out (k := 2) (by norm_num) (by norm_num) hp7
    rwa [Nat.cast_ofNat] at this
  haveI : Fact (1 < p ^ r) := ⟨Nat.one_lt_pow (by omega) hp.out.one_lt⟩
  have hui : IsUnit ((a i : ℕ) : ZMod (p ^ r)) := (ZMod.isUnit_iff_coprime _ _).2
      (Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hfi.1).symm)
  set w := (2 : ZMod (p ^ r))⁻¹ * (a i : ZMod (p ^ r)) with hw
  have hwu : IsUnit w := (IsUnit.of_mul_eq_one_right _ hh).mul hui
  have hai : (a i : ZMod (p ^ r)) = 2 * w := by rw [hw, ← mul_assoc, hh, one_mul]
  have hy' : (2 : ZMod (p ^ r))⁻¹ * a j = (σ : ZMod (p ^ r)) * w := by
    rw [hβ, hai, hw]; linear_combination ((σ : ZMod (p ^ r)) * (2 : ZMod (p ^ r))⁻¹ * a i) * hh'
  have h3 := sum3_zmod (m := m) a hsum i j k hij hik hjk
  have hV : ((a k / 2 : ℕ) : ZMod (p ^ r)) = -(1 + (σ : ZMod (p ^ r))) * w := by
    apply u2.mul_left_cancel
    have h2V : (2 : ZMod (p ^ r)) * ((a k / 2 : ℕ) : ZMod (p ^ r)) = a k := by
      rw [show (2 : ZMod (p ^ r)) = ((2 : ℕ) : ZMod (p ^ r)) by norm_num, ← Nat.cast_mul,
        Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hk)]
    rw [h2V]
    have : (a j : ZMod (p ^ r)) = σ * (2 * w) := by rw [hβ, hai]
    linear_combination h3 - hai - this
  set P : Finset (ZMod (p ^ r)) := {2 * w, -(2 * w), w, -w} with hPdef
  have hPc : P.card < p - 1 := lt_of_le_of_lt Finset.card_le_four (by omega)
  have hPs : ∀ v : ZMod (p ^ r), IsUnit v → (PhiTop p r m' η a e i j k v ≠ 0 ∨
      PhiTop p r m' η a e i j k (-v) ≠ 0) → v ∈ P := by
    intro v hv hne
    have key : ∀ t : ZMod (p ^ r), IsUnit t → PhiTop p r m' η a e i j k t ≠ 0 →
        t = 2 * w ∨ t = w ∨ t = -(2 * w) ∨ t = -w := by
      intro t ht hne'
      rcases PhiTop_supp hp7 η a e i j k t hne' with h1 | h1 | h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · rw [hy'] at h1
        rcases hσ with rfl | rfl
        · left; rw [h1]; push_cast; ring
        · right; right; left; rw [h1]; push_cast; ring
      · rw [hy'] at h1
        rcases hσ with rfl | rfl
        · right; left; rw [h1]; push_cast; ring
        · right; right; right; rw [h1]; push_cast; ring
      · rw [hV] at h1
        rcases hσ with rfl | rfl
        · right; right; left; rw [h1]; push_cast; ring
        · exfalso; rw [h1] at ht; push_cast at ht; simp at ht
    rcases hne with h | h
    · rcases key v hv h with h1 | h1 | h1 | h1 <;> rw [h1] <;> simp [P]
    · rcases key (-v) hv.neg h with h1 | h1 | h1 | h1
      · rw [← neg_neg v, h1]; simp [P]
      · rw [← neg_neg v, h1]; simp [P]
      · rw [← neg_neg v, h1, neg_neg]; simp [P]
      · rw [← neg_neg v, h1, neg_neg]; simp [P]
  have hsym := top_sym hp7 hr hpm hm hodd hdvd hη a e hP i j k hij hik hjk hi hj hk
    (by rcases Nat.lt_or_ge r 2 with h | h
        · exact Or.inr ⟨by omega, Or.inr ⟨P, hPs, hPc⟩⟩
        · exact Or.inl h)
  obtain ⟨-, h⟩ := top_T hp7 hr hpm hm hodd hdvd hη a e hsum i j k hij hik hjk hk hsym
  have hci : cT p m' η a e i = (e i : ℂ) * η (a i : ZMod m') := by
    unfold cT; rw [if_pos hfi, if_pos hi]
  have hcj : cT p m' η a e j = (e j : ℂ) * η (a j : ZMod m') := by
    unfold cT; rw [if_pos hfj, if_pos hj]
  have hne2 : (a i : ZMod (p ^ r)) ≠ -(a i : ZMod (p ^ r)) := by
    intro h0
    have : (2 : ZMod (p ^ r)) * a i = 0 := by linear_combination h0
    exact (u2.mul hui).ne_zero this
  rw [hci, hcj] at h
  rcases hσ with rfl | rfl
  · have hβ' : (a j : ZMod (p ^ r)) = a i := by rw [hβ]; push_cast; ring
    rcases h with ⟨h1, h2⟩ | ⟨-, h2⟩ | ⟨h1, -⟩
    · push_cast; rw [one_mul, one_mul]; linear_combination h1 + h2
    · push_cast; rw [one_mul, one_mul]; linear_combination h2
    · exact absurd (hβ'.symm.trans h1) hne2
  · have hβ' : (a j : ZMod (p ^ r)) = -(a i) := by rw [hβ]; push_cast; ring
    have hneg : η ((((-1 : ℤ) * a j : ℤ)) : ZMod m') = η (-1) * η (a j : ZMod m') := by
      rw [← map_mul]; congr 1; push_cast; ring
    rw [hneg]
    rcases h with ⟨h1, h2⟩ | ⟨h1, -⟩ | ⟨-, h2⟩
    · push_cast; linear_combination h1 - η (-1) * h2
    · exact absurd (h1.symm.trans hβ') hne2
    · push_cast; linear_combination h2

end

end Erdos634.LemmaSEvenTop

#print axioms Erdos634.LemmaSEvenTop.top_sym
#print axioms Erdos634.LemmaSEvenTop.top_T
#print axioms Erdos634.LemmaSEvenTop.top_rel_all
