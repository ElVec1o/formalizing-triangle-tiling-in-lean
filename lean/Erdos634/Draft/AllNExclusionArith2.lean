/-
Draft/AllNExclusionArith2.lean — atom ALLN-1, part 2.  N-uniform decidable checks for the S2 leaf (global `A ∣ 4N` form), the
equilateral pair tables (π/3 and 2π/3) and the F1 pair list, each with the implication lemma quantified over ALL `N`:

  S2Chk        ⇒ S2Arith N      (coprime p<q, q²<4N, A=2q²−p² ∣ 4N, no integer S with N R² = S² A B;  A necessary AND sufficient)
  Pairs120Chk  ⇒ the hypothesis of `gapE120_of_pairs`  ⇒ GapE120 N
  Pairs60Chk   ⇒ the hypothesis of `gapE60_of_pairs`   ⇒ GapE60 N   (11 ≤ N)
  F1Chk        ⇒ the hypothesis of `f1MaGt1_of_list`   ⇒ GapF1 N    (6 < N)
(the square tests use `(t−s)²+16N = (s+t)²+4N` and `(t−s)²−…`, valid because `s t = 3N`.)
*** UNAUDITED.  Formalization debt, NOT /goal progress.  No sorry, no native_decide. ***
-/
import Erdos634.Draft.AllNExclusionArith

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.AllNExclusion

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeS2Arith Erdos634.Draft.CompositeE5Gen
open Erdos634.Draft.CompositeF1Gen Erdos634.Draft.F1KappaSide

/-- `v` is a perfect square (decidable form). -/
def sqChk (v : ℕ) : Prop := Nat.sqrt v * Nat.sqrt v = v

instance (v : ℕ) : Decidable (sqChk v) := by unfold sqChk; infer_instance

theorem not_isSquare_of_chk (v : ℕ) (D : ℤ) (hD : D = (v : ℤ)) (h : ¬ sqChk v) : ¬ IsSquare D := by
  rintro ⟨r, hr⟩
  apply h
  have : v = r.natAbs * r.natAbs := by
    have e := natAbs_mul_self_cast r
    have : ((v : ℕ) : ℤ) = ((r.natAbs * r.natAbs : ℕ) : ℤ) := by rw [← hD, hr, e]; ring
    exact_mod_cast this
  unfold sqChk
  rw [this, Nat.sqrt_eq]

theorem not_isSquare_of_neg (D : ℤ) (h : D < 0) : ¬ IsSquare D := by
  rintro ⟨r, hr⟩
  nlinarith [mul_self_nonneg r]

/-! ## S2 (global form) -/

def s2A (p q : ℕ) : ℕ := 2 * (q * q) - p * p
def s2B (p q : ℕ) : ℕ := 3 * (q * q) - p * p
def s2X (N p q : ℕ) : ℕ := N * ((q - p) * (2 * q + p)) ^ 2

def S2Chk (N : ℕ) : Prop :=
  ∀ q ≤ 4 * N, q * q < 4 * N → ∀ p < q, 0 < p → Nat.gcd p q = 1 → s2A p q ∣ 4 * N →
    ¬ (s2A p q * s2B p q ∣ s2X N p q ∧
       sqChk (s2X N p q / (s2A p q * s2B p q)))

instance (N : ℕ) : Decidable (S2Chk N) := by unfold S2Chk s2A s2B s2X sqChk; infer_instance

theorem s2Arith_of_chk {N : ℕ} (hN : 0 < N) (h : S2Chk N) : S2Arith N := by
  intro p q S hp hpq hcop hS heq
  have hd := Erdos634.Draft.CompositeS2Global.s2_dvd N p q S hcop heq
  have hApos : 0 < 2 * q ^ 2 - p ^ 2 := by nlinarith
  have hle : 2 * q ^ 2 - p ^ 2 ≤ 4 * (N : ℤ) := Int.le_of_dvd (by positivity) hd
  have hq : q ^ 2 < 4 * (N : ℤ) := by nlinarith
  have hBpos : 0 < 3 * q ^ 2 - p ^ 2 := by nlinarith
  lift p to ℕ using hp.le
  lift q to ℕ using (by omega)
  have hpq' : p < q := by exact_mod_cast hpq
  have hp' : 0 < p := by exact_mod_cast hp
  have hcop' : Nat.gcd p q = 1 := Nat.isCoprime_iff_coprime.mp (by exact_mod_cast hcop)
  have hqq : q * q < 4 * N := by
    have : (q : ℤ) * q < 4 * N := by nlinarith
    exact_mod_cast this
  have hpp : p * p ≤ 2 * (q * q) := by nlinarith
  have hpp3 : p * p ≤ 3 * (q * q) := by nlinarith
  have hAc : ((s2A p q : ℕ) : ℤ) = 2 * (q : ℤ) ^ 2 - (p : ℤ) ^ 2 := by
    unfold s2A; rw [Nat.cast_sub hpp]; push_cast; ring
  have hBc : ((s2B p q : ℕ) : ℤ) = 3 * (q : ℤ) ^ 2 - (p : ℤ) ^ 2 := by
    unfold s2B; rw [Nat.cast_sub hpp3]; push_cast; ring
  have hXc : ((s2X N p q : ℕ) : ℤ) = (N : ℤ) * (((q : ℤ) - p) * (2 * q + p)) ^ 2 := by
    unfold s2X; push_cast [Nat.cast_sub hpq'.le]; ring
  have hAd : s2A p q ∣ 4 * N := by
    have : ((s2A p q : ℕ) : ℤ) ∣ ((4 * N : ℕ) : ℤ) := by rw [hAc]; push_cast; exact hd
    exact_mod_cast this
  have hApos' : 0 < s2A p q * s2B p q := by
    have : (0 : ℤ) < ((s2A p q * s2B p q : ℕ) : ℤ) := by
      push_cast; rw [hAc, hBc]; exact mul_pos hApos hBpos
    exact_mod_cast this
  have key : s2X N p q = (S.natAbs * S.natAbs) * (s2A p q * s2B p q) := by
    have : ((s2X N p q : ℕ) : ℤ) = (((S.natAbs * S.natAbs) * (s2A p q * s2B p q) : ℕ) : ℤ) := by
      have e := natAbs_mul_self_cast S
      rw [hXc]; push_cast at e ⊢; rw [hAc, hBc, e]; linarith
    exact_mod_cast this
  apply h q (by nlinarith) hqq p hpq' hp' hcop' hAd
  refine ⟨⟨S.natAbs * S.natAbs, by rw [key]; ring⟩, ?_⟩
  have hdiv : s2X N p q / (s2A p q * s2B p q) = S.natAbs * S.natAbs := by
    rw [key]; exact Nat.mul_div_cancel _ hApos'
  unfold sqChk
  rw [hdiv, Nat.sqrt_eq]

/-- `S2Chk` with outer loop bounded by `√(4N)` (safe since `q*q < 4*N → q ≤ √(4N)`). -/
def S2ChkSq (N : ℕ) : Prop :=
  ∀ q ≤ Nat.sqrt (4 * N), q * q < 4 * N → ∀ p < q, 0 < p → Nat.gcd p q = 1 → s2A p q ∣ 4 * N →
    ¬ (s2A p q * s2B p q ∣ s2X N p q ∧
       sqChk (s2X N p q / (s2A p q * s2B p q)))
instance (N : ℕ) : Decidable (S2ChkSq N) := by unfold S2ChkSq s2A s2B s2X sqChk; infer_instance
theorem s2Chk_of_sq {N : ℕ} (h : S2ChkSq N) : S2Chk N :=
  fun q _ hq => h q (Nat.le_sqrt.mpr (Nat.le_of_lt hq)) hq

/-! ## 2π/3 equilateral pairs -/

def Pairs120Chk (N : ℕ) : Prop :=
  ∀ s ≤ N, 1 ≤ s → s ∣ 3 * N → 3 * N / s ≤ N →
    ¬ sqChk ((s + 3 * N / s) ^ 2 + 4 * N) ∧ ¬ (s + 3 * N / s ∣ 2 * N)

instance (N : ℕ) : Decidable (Pairs120Chk N) := by unfold Pairs120Chk sqChk; infer_instance

theorem pairs120_of_chk {N : ℕ} (h : Pairs120Chk N) :
    ∀ s t : ℤ, 1 ≤ s → s ≤ N → 1 ≤ t → t ≤ N → s * t = 3 * (N : ℤ) →
      ¬ IsSquare ((t - s) ^ 2 + 16 * (N : ℤ)) ∧ ∀ r : ℤ, 0 ≤ r → 2 * (N : ℤ) ≠ r * (s + t) := by
  intro s t h1 h2 h3 h4 hp
  lift s to ℕ using (by omega)
  lift t to ℕ using (by omega)
  have hp' : s * t = 3 * N := by exact_mod_cast hp
  have hs1 : 1 ≤ s := by exact_mod_cast h1
  have hsN : s ≤ N := by exact_mod_cast h2
  have htN : t ≤ N := by exact_mod_cast h4
  have hdvd : s ∣ 3 * N := ⟨t, hp'.symm⟩
  have hdiv : 3 * N / s = t := by rw [← hp']; exact Nat.mul_div_cancel_left _ hs1
  obtain ⟨hA, hB⟩ := h s hsN hs1 hdvd (by rw [hdiv]; exact htN)
  rw [hdiv] at hA hB
  refine ⟨not_isSquare_of_chk ((s + t) ^ 2 + 4 * N) _ ?_ hA, ?_⟩
  · push_cast; nlinarith [hp]
  · intro r hr hcon
    apply hB
    lift r to ℕ using hr
    exact ⟨r, by have : (2 * N : ℤ) = r * (s + t) := by exact_mod_cast hcon
                 have : 2 * N = r * (s + t) := by exact_mod_cast this
                 linarith⟩

theorem gapE120_of_chk {N : ℕ} (hN : 0 < N) (h : Pairs120Chk N) : GapE120 N :=
  gapE120_of_pairs N hN (pairs120_of_chk h)

/-! ## π/3 equilateral pairs -/

def Pairs60Chk (N : ℕ) : Prop :=
  ∀ m ≤ N, 1 ≤ m → m ∣ 3 * N → 3 * N / m ≤ N → 3 * N / m < m →
    (m = N ∧ 3 * N / m = 3) ∨
    (16 * N ≤ (m + 3 * N / m) ^ 2 →
      ¬ sqChk ((m + 3 * N / m) ^ 2 - 16 * N) ∧
      ∀ p ≤ 2 * N / (m + 3 * N / m),
        ¬ (p * (m + 3 * N / m) ≤ 2 * N ∧ (m - 3 * N / m) ∣ (2 * N - p * (m + 3 * N / m))))

instance (N : ℕ) : Decidable (Pairs60Chk N) := by unfold Pairs60Chk sqChk; infer_instance

theorem pairs60_of_chk {N : ℕ} (h : Pairs60Chk N) :
    ∀ m₁ m₂ : ℤ, 1 ≤ m₁ → m₁ ≤ N → 1 ≤ m₂ → m₂ ≤ N → m₁ * m₂ = 3 * (N : ℤ) → m₂ < m₁ →
      (m₁ = N ∧ m₂ = 3) ∨ (¬ IsSquare ((m₁ + m₂) ^ 2 - 16 * (N : ℤ)) ∧
        (0 ≤ (m₁ + m₂) ^ 2 - 16 * (N : ℤ) →
          ∀ p r : ℤ, 0 ≤ p → 0 ≤ r → 2 * (N : ℤ) ≠ p * (m₁ + m₂) + r * (m₁ - m₂))) := by
  intro m₁ m₂ h1 h2 h3 h4 hp hlt
  lift m₁ to ℕ using (by omega)
  lift m₂ to ℕ using (by omega)
  have hp' : m₁ * m₂ = 3 * N := by exact_mod_cast hp
  have hm1 : 1 ≤ m₁ := by exact_mod_cast h1
  have hm1N : m₁ ≤ N := by exact_mod_cast h2
  have hm2N : m₂ ≤ N := by exact_mod_cast h4
  have hlt' : m₂ < m₁ := by exact_mod_cast hlt
  have hdvd : m₁ ∣ 3 * N := ⟨m₂, hp'.symm⟩
  have hdiv : 3 * N / m₁ = m₂ := by rw [← hp']; exact Nat.mul_div_cancel_left _ hm1
  rcases h m₁ hm1N hm1 hdvd (by rw [hdiv]; exact hm2N) (by rw [hdiv]; exact hlt') with ⟨e1, e2⟩ | hR
  · rw [hdiv] at e2
    left
    exact ⟨by exact_mod_cast e1, by exact_mod_cast e2⟩
  · rw [hdiv] at hR
    right
    have hm2pos : 1 ≤ m₂ := by exact_mod_cast h3
    constructor
    · by_cases hc : 16 * N ≤ (m₁ + m₂) ^ 2
      · exact not_isSquare_of_chk ((m₁ + m₂) ^ 2 - 16 * N) _
          (by rw [Nat.cast_sub hc]; push_cast; ring) (hR hc).1
      · apply not_isSquare_of_neg
        have : (m₁ + m₂) ^ 2 < 16 * N := by omega
        have : (((m₁ + m₂) ^ 2 : ℕ) : ℤ) < ((16 * N : ℕ) : ℤ) := by exact_mod_cast this
        push_cast at this ⊢; linarith
    · intro hD p r hp0 hr0 hcon
      have hc : 16 * N ≤ (m₁ + m₂) ^ 2 := by
        by_contra hc
        have : (m₁ + m₂) ^ 2 < 16 * N := by omega
        have : (((m₁ + m₂) ^ 2 : ℕ) : ℤ) < ((16 * N : ℕ) : ℤ) := by exact_mod_cast this
        push_cast at this hD; linarith
      lift p to ℕ using hp0
      lift r to ℕ using hr0
      have hcon' : 2 * N = p * (m₁ + m₂) + r * (m₁ - m₂) := by
        have e : (2 * N : ℤ) = p * (m₁ + m₂) + r * ((m₁ : ℤ) - m₂) := by exact_mod_cast hcon
        have e2 : (2 * N : ℤ) = ((p * (m₁ + m₂) + r * (m₁ - m₂) : ℕ) : ℤ) := by
          push_cast [Nat.cast_sub hlt'.le]; linarith
        exact_mod_cast e2
      have hApos : 0 < m₁ + m₂ := by omega
      refine (hR hc).2 p ?_ ⟨by omega, ⟨r, by rw [show 2 * N - p * (m₁ + m₂) = r * (m₁ - m₂) by omega]; ring⟩⟩
      exact (Nat.le_div_iff_mul_le hApos).mpr (by omega)

theorem gapE60_of_chk {N : ℕ} (hN : 11 ≤ N) (h : Pairs60Chk N) : GapE60 N :=
  gapE60_of_pairs N hN (pairs60_of_chk h)

/-! ## F1 pair list -/

def F1Chk (N : ℕ) : Prop :=
  ∀ a ≤ N, 1 < a → a * a < N → a ∣ N →
    a + 2 ≤ N / a ∧ (N / a - a) % 2 = 0 ∧ ¬ sqChk ((a + N / a) ^ 2 + 12 * N) ∧
      a * a + (N / a) * (N / a) ≠ 4 * a * (N / a)

instance (N : ℕ) : Decidable (F1Chk N) := by unfold F1Chk sqChk; infer_instance

theorem f1list_of_chk {N : ℕ} (h : F1Chk N) :
    ∀ Ma Mb : ℕ, 1 < Ma → Ma < Mb → Ma * Mb = N →
      ∃ κ : ℕ, 0 < κ ∧ Mb = Ma + 2 * κ ∧ ¬ IsSquare (((Ma : ℤ) + Mb) ^ 2 + 12 * (N : ℤ)) ∧
        Ma ^ 2 + Mb ^ 2 ≠ 4 * Ma * Mb := by
  intro Ma Mb h1 h2 h3
  have hMa0 : 0 < Ma := by omega
  have hdvd : Ma ∣ N := ⟨Mb, h3.symm⟩
  have hdiv : N / Ma = Mb := by rw [← h3]; exact Nat.mul_div_cancel_left _ hMa0
  have hlt : Ma * Ma < N := by rw [← h3]; exact Nat.mul_lt_mul_of_pos_left h2 hMa0
  have hle : Ma ≤ N := by nlinarith
  obtain ⟨e1, e2, e3, e4⟩ := h Ma hle h1 hlt hdvd
  rw [hdiv] at e1 e2 e3 e4
  refine ⟨(Mb - Ma) / 2, by omega, by omega, ?_, ?_⟩
  · exact not_isSquare_of_chk ((Ma + Mb) ^ 2 + 12 * N) _ (by push_cast; ring) e3
  · intro hcon; apply e4; nlinarith [hcon]

theorem gapF1_of_chk {N : ℕ} (h6 : 6 < N) (h : F1Chk N) : GapF1 N :=
  gapF1_of_MaGt1 N h6 (f1MaGt1_of_list N (f1list_of_chk h))

/-- Sqrt-bounded variant of F1Chk: quantifier runs only to Nat.sqrt N, which is O(√N) not O(N). -/
def F1ChkSq (N : ℕ) : Prop :=
  ∀ a ≤ Nat.sqrt N, 1 < a → a * a < N → a ∣ N →
    a + 2 ≤ N / a ∧ (N / a - a) % 2 = 0 ∧ ¬ sqChk ((a + N / a) ^ 2 + 12 * N) ∧
      a * a + (N / a) * (N / a) ≠ 4 * a * (N / a)

instance (N : ℕ) : Decidable (F1ChkSq N) := by unfold F1ChkSq sqChk; infer_instance

/-- F1ChkSq N implies F1Chk N (the outer bound a ≤ N vs a ≤ √N makes no difference since a*a < N forces a ≤ √N). -/
theorem f1chk_of_sq {N : ℕ} (h : F1ChkSq N) : F1Chk N := by
  intro a _ha h1 halt hdvd
  exact h a (Nat.le_sqrt.mpr halt.le) h1 halt hdvd

theorem gapF1_of_chksq {N : ℕ} (h6 : 6 < N) (h : F1ChkSq N) : GapF1 N :=
  gapF1_of_chk h6 (f1chk_of_sq h)

/-- Sqrt-bounded NoF3Chk: outer loop runs to √N and inner to √(2N), not N and 2N.
    Reduces kernel proof-term count from O(N²) to O(N). -/
def NoF3ChkSq (N : ℕ) : Prop :=
  ∀ j ≤ Nat.sqrt N, 0 < j → j * j ≤ N → ∀ s ≤ Nat.sqrt (2 * N), j < s → s * s ≤ 2 * N →
    4 * N ≠ 3 * (s + j) * (s + 3 * j)

instance (N : ℕ) : Decidable (NoF3ChkSq N) := by unfold NoF3ChkSq; infer_instance

theorem noF3Chk_of_sq {N : ℕ} (h : NoF3ChkSq N) : NoF3Chk N :=
  fun j _ hj0 hjsq s _ hjs hssq heq =>
    h j (Nat.le_sqrt.mpr hjsq) hj0 hjsq s (Nat.le_sqrt.mpr hssq) hjs hssq heq

/-- Sqrt-bounded NoF4zChk: both loops run to √N, not N. Reduces O(N²) → O(N). -/
def NoF4zChkSq (N : ℕ) : Prop :=
  ∀ x ≤ Nat.sqrt N, 0 < x → x * x ≤ N → ∀ r ≤ Nat.sqrt N, 0 < r → r * r ≤ N →
    N = (x + r) * (2 * x + r) →
    Nat.sqrt (x * x + x * r + r * r) * Nat.sqrt (x * x + x * r + r * r) ≠ x * x + x * r + r * r

instance (N : ℕ) : Decidable (NoF4zChkSq N) := by unfold NoF4zChkSq; infer_instance

theorem noF4zChk_of_sq {N : ℕ} (h : NoF4zChkSq N) : NoF4zChk N :=
  fun x _ hx0 hxsq r _ hr0 hrsq heq =>
    h x (Nat.le_sqrt.mpr hxsq) hx0 hxsq r (Nat.le_sqrt.mpr hrsq) hr0 hrsq heq

/-- Sqrt-bounded NoF2Chk: both nested loops run to √N. Reduces O(N²) → O(N). -/
def NoF2ChkSq (N : ℕ) : Prop :=
  (∀ z ≤ Nat.sqrt N, 3 * (z * z) ≠ N) ∧
  (∀ x ≤ Nat.sqrt N, 0 < x → x * x ≤ N → ∀ r ≤ Nat.sqrt N, 0 < r → r * r ≤ N →
    N = (x + r) * (2 * x + r) →
    ¬ ((N + x * x) % 3 = 0 ∧
      Nat.sqrt ((N + x * x) / 3) * Nat.sqrt ((N + x * x) / 3) = (N + x * x) / 3))

instance (N : ℕ) : Decidable (NoF2ChkSq N) := by unfold NoF2ChkSq; infer_instance

theorem noF2Chk_of_sq {N : ℕ} (h : NoF2ChkSq N) : NoF2Chk N := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun z _ heq => h1 z (Nat.le_sqrt.mpr (by nlinarith)) heq, ?_⟩
  intro x _ hx0 hxsq r _ hr0 hrsq hN hcon
  exact h2 x (Nat.le_sqrt.mpr hxsq) hx0 hxsq r (Nat.le_sqrt.mpr hrsq) hr0 hrsq hN hcon

end Erdos634.Draft.AllNExclusion

#print axioms Erdos634.Draft.AllNExclusion.s2Arith_of_chk
#print axioms Erdos634.Draft.AllNExclusion.gapE120_of_chk
#print axioms Erdos634.Draft.AllNExclusion.gapE60_of_chk
#print axioms Erdos634.Draft.AllNExclusion.gapF1_of_chk
