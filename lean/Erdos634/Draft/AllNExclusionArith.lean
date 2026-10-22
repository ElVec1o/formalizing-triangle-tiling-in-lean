/-
Draft/AllNExclusionArith.lean — atom ALLN-1, part 1.  The N-UNIFORM decidable arithmetic predicates ("checks") of the composite
chain, each with a lemma "check N ⇒ the leaf of the chain at N".  Every check is a bounded `∀ … ≤ …` / `∃ … ≤ …` statement on
`ℕ` (so `decide +kernel` evaluates it at a concrete N and a Rust transcription can enumerate all N ≤ 10000), and every
implication lemma is quantified over ALL `N`.

  NSqChk       N not a sum of two squares                   ⇒ ¬∃ x y, N = x²+y²
  NHSqChk      N/2 not a sum of two squares (N even)         ⇒ ¬∃ x y, N = 2(x²+y²)
  HArithChk    the six `HArith` exclusions                   ⇒ HArith N
  EllChk       a prime ℓ ≥ 7 divides N                       ⇒ (N squarefree) odd padic valuation of ℓ
  NoF2Chk / NoF3Chk / NoF4zChk                               ⇒ R8Gen2.NoF2 / NoF3 / NoF4z  (hence GapR8 N)
  S3Chk        the reduced Row-11 equation has no solution   ⇒ IsoQRef N  (hence S3Closed N)
  IsoH9bChk    the 2π/3-isosceles arithmetic                 ⇒ IsoH9b N
*** UNAUDITED.  Formalization debt, NOT /goal progress.  No sorry, no native_decide. ***
-/
import Erdos634.Draft.CompositeFinal12
import Erdos634.Draft.H1kFinal

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.AllNExclusion

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.CompositeS1Arith Erdos634.Draft.CompositeIsoB Erdos634.Draft.CompositeFinal2
open Erdos634.Draft.CompositeFinal3 Erdos634.Draft.R8Gen2

/-! ## sums of two squares -/

/-- `N` is not `x² + y²`: for every `x` with `x² ≤ N`, `N − x²` is not a perfect square. -/
def NSqChk (N : ℕ) : Prop :=
  ∀ x ≤ N, x * x ≤ N → Nat.sqrt (N - x * x) * Nat.sqrt (N - x * x) ≠ N - x * x

instance (N : ℕ) : Decidable (NSqChk N) := by unfold NSqChk; infer_instance

theorem nsq_of_chk {N : ℕ} (h : NSqChk N) : ¬ ∃ x y : ℕ, N = x ^ 2 + y ^ 2 := by
  rintro ⟨x, y, hxy⟩
  have hx : x * x ≤ N := by nlinarith [sq_nonneg y]
  have hxN : x ≤ N := le_trans (Nat.le_mul_self x) hx
  apply h x hxN hx
  have : N - x * x = y * y := by rw [hxy]; simp [sq]
  rw [this, Nat.sqrt_eq]

/-- `N` even and `N/2` is not `x² + y²`. -/
def NHSqChk (N : ℕ) : Prop :=
  ∀ x ≤ N, 2 * (x * x) ≤ N → Nat.sqrt (N / 2 - x * x) * Nat.sqrt (N / 2 - x * x) ≠ N / 2 - x * x

instance (N : ℕ) : Decidable (NHSqChk N) := by unfold NHSqChk; infer_instance

theorem nhsq_of_chk {N : ℕ} (hev : N % 2 = 0) (h : NHSqChk N) : ¬ ∃ x y : ℕ, N = 2 * (x ^ 2 + y ^ 2) := by
  rintro ⟨x, y, hxy⟩
  have hx : 2 * (x * x) ≤ N := by nlinarith [sq_nonneg y]
  have hxN : x ≤ N := le_trans (Nat.le_mul_self x) (by omega)
  apply h x hxN hx
  have h2 : N / 2 = x * x + y * y := by rw [hxy]; simp [sq]
  have : N / 2 - x * x = y * y := by omega
  rw [this, Nat.sqrt_eq]

/-! ## HArith -/

def HArithChk (N : ℕ) : Prop :=
  0 < N ∧ (∀ r ≤ N, 2 * (r * r) ≠ N) ∧ (∀ t ≤ N, t * t ≠ N) ∧ (∀ y ≤ N, 3 * (y * y) ≠ 2 * N) ∧
    (∀ t ≤ 2 * N, t * t ≠ 2 * N) ∧ (∀ x ≤ N, 3 * (x * x) ≠ N) ∧ (∀ r ≤ N, 10 * (r * r) ≠ N)

instance (N : ℕ) : Decidable (HArithChk N) := by unfold HArithChk; infer_instance

theorem harith_of_chk {N : ℕ} (h : HArithChk N) : Erdos634.Geometry.CaseA.LemmaH.HArith N := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr; exact h1 r (by nlinarith [Nat.le_mul_self r]) (by rw [← hr]; ring)
  · intro t ht; exact h2 t (by nlinarith [Nat.le_mul_self t]) (by rw [← ht]; ring)
  · intro y hy; exact h3 y (by nlinarith [Nat.le_mul_self y]) (by rw [← hy]; ring)
  · intro t ht; exact h4 t (by nlinarith [Nat.le_mul_self t]) (by rw [← ht]; ring)
  · intro x hx; exact h5 x (by nlinarith [Nat.le_mul_self x]) (by rw [← hx]; ring)
  · intro r hr; exact h6 r (by nlinarith [Nat.le_mul_self r]) (by rw [← hr]; ring)

/-! ## the prime ℓ ≥ 7 of odd valuation -/

/-- A prime `ℓ ≥ 7` divides `N` (primality in the elementary form `2 ≤ ℓ ∧ ∀ m < ℓ, m ∣ ℓ → m = 1`). -/
def EllChk (N : ℕ) : Prop :=
  ∃ ℓ ≤ N, 7 ≤ ℓ ∧ ℓ ∣ N ∧ ∀ m < ℓ, m ∣ ℓ → m = 1

instance (N : ℕ) : Decidable (EllChk N) := by unfold EllChk; infer_instance

theorem ell_of_chk {N : ℕ} (hsq : Squarefree N) (h : EllChk N) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ 7 ≤ ℓ ∧ ¬ Even (padicValNat ℓ N) := by
  obtain ⟨ℓ, -, h7, hd, hp⟩ := h
  have hpr : ℓ.Prime := Nat.prime_def_lt.mpr ⟨by omega, hp⟩
  refine ⟨ℓ, hpr, h7, ?_⟩
  obtain ⟨k, hk⟩ := hd
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk; subst hk; exact absurd hsq (by simp)
  have hnd : ¬ ℓ ∣ k := by
    rintro ⟨k', rfl⟩
    have : IsUnit ℓ := hsq ℓ ⟨k', by rw [hk]; ring⟩
    exact hpr.one_lt.ne' (Nat.isUnit_iff.mp this)
  rw [hk]
  exact notEven_of_odd (val_one hpr hnd hk0)

/-! ## R8: NoF2, NoF3, NoF4z -/

theorem natAbs_mul_self_cast (z : ℤ) : ((z.natAbs * z.natAbs : ℕ) : ℤ) = z ^ 2 := by
  push_cast; rw [← sq]; exact sq_abs z

def NoF3Chk (N : ℕ) : Prop :=
  ∀ j ≤ N, 0 < j → j * j ≤ N → ∀ s ≤ 2 * N, j < s → s * s ≤ 2 * N →
    4 * N ≠ 3 * (s + j) * (s + 3 * j)

instance (N : ℕ) : Decidable (NoF3Chk N) := by unfold NoF3Chk; infer_instance

theorem noF3_of_chk {N : ℕ} (h : NoF3Chk N) : NoF3 N := by
  intro s j hj hjs heq
  lift j to ℕ using hj.le
  lift s to ℕ using (by omega)
  have heq' : 4 * N = 3 * (s + j) * (s + 3 * j) := by exact_mod_cast heq
  have hj0 : 0 < j := by exact_mod_cast hj
  have hjs' : j < s := by exact_mod_cast hjs
  have h1 : j * j ≤ N := by nlinarith
  have h2 : s * s ≤ 2 * N := by nlinarith
  exact h j (by nlinarith) hj0 h1 s (by nlinarith) hjs' h2 heq'

def NoF4zChk (N : ℕ) : Prop :=
  ∀ x ≤ N, 0 < x → x * x ≤ N → ∀ r ≤ N, 0 < r → r * r ≤ N → N = (x + r) * (2 * x + r) →
    Nat.sqrt (x * x + x * r + r * r) * Nat.sqrt (x * x + x * r + r * r) ≠ x * x + x * r + r * r

instance (N : ℕ) : Decidable (NoF4zChk N) := by unfold NoF4zChk; infer_instance

theorem noF4z_of_chk {N : ℕ} (h : NoF4zChk N) : NoF4z N := by
  apply noF4z_of_int
  intro x r hx hr hN z hz
  have h1 : x * x ≤ N := by nlinarith
  have h2 : r * r ≤ N := by nlinarith
  apply h x (le_trans (Nat.le_mul_self x) h1) hx h1 r (le_trans (Nat.le_mul_self r) h2) hr h2 hN
  have hz' : z.natAbs * z.natAbs = x * x + x * r + r * r := by
    have : ((z.natAbs * z.natAbs : ℕ) : ℤ) = ((x * x + x * r + r * r : ℕ) : ℤ) := by
      have e := natAbs_mul_self_cast z; push_cast at e ⊢; nlinarith [hz, e]
    exact_mod_cast this
  rw [← hz', Nat.sqrt_eq]

def NoF2Chk (N : ℕ) : Prop :=
  (∀ z ≤ N, 3 * (z * z) ≠ N) ∧
  (∀ x ≤ N, 0 < x → x * x ≤ N → ∀ r ≤ N, 0 < r → r * r ≤ N → N = (x + r) * (2 * x + r) →
    ¬ ((N + x * x) % 3 = 0 ∧
      Nat.sqrt ((N + x * x) / 3) * Nat.sqrt ((N + x * x) / 3) = (N + x * x) / 3))

instance (N : ℕ) : Decidable (NoF2Chk N) := by unfold NoF2Chk; infer_instance

theorem noF2_of_chk {N : ℕ} (h : NoF2Chk N) : NoF2 N := by
  obtain ⟨h1, h2⟩ := h
  apply noF2_of_int
  · intro z hz
    have hz' : 3 * (z.natAbs * z.natAbs) = N := by
      have : ((3 * (z.natAbs * z.natAbs) : ℕ) : ℤ) = (N : ℤ) := by
        have e := natAbs_mul_self_cast z; push_cast at e ⊢; linarith
      exact_mod_cast this
    exact h1 z.natAbs (by nlinarith [Nat.le_mul_self z.natAbs]) hz'
  · intro x r hx hr hN z hz
    have hx1 : x * x ≤ N := by nlinarith
    have hr1 : r * r ≤ N := by nlinarith
    apply h2 x (le_trans (Nat.le_mul_self x) hx1) hx hx1 r (le_trans (Nat.le_mul_self r) hr1) hr hr1 hN
    have hz' : 3 * (z.natAbs * z.natAbs) = N + x * x := by
      have : ((3 * (z.natAbs * z.natAbs) : ℕ) : ℤ) = ((N + x * x : ℕ) : ℤ) := by
        have e := natAbs_mul_self_cast z; push_cast at e ⊢; linarith
      exact_mod_cast this
    have h3 : (N + x * x) / 3 = z.natAbs * z.natAbs := by omega
    refine ⟨by omega, ?_⟩
    rw [h3, Nat.sqrt_eq]

/-- **`GapR8 N`** from the three finite checks. -/
theorem gapR8_of_chk {N : ℕ} (h2 : NoF2Chk N) (h3 : NoF3Chk N) (h4 : NoF4zChk N) : GapR8 N :=
  gapR8_of_arith2 N (noF2_of_chk h2) (noF3_of_chk h3) (noF4z_of_chk h4)

/-! ## S3 (IsoQRef) -/

def qQ (e d : ℕ) : ℕ := e * e + 4 * e * d + 2 * (d * d)
def kK (e d : ℕ) : ℕ := (2 * e + d) * qQ e d

/-- The reduced Row-11 equation `N d = m² (2e+d)(e²+4ed+2d²)` has no solution (guards: `Q ∣ N`, forced by `gcd = 1`). -/
def S3Chk (N : ℕ) : Prop :=
  ∀ e ≤ N, 1 ≤ e → e * e ≤ N → ∀ d ≤ N, 1 ≤ d → 2 * (d * d) ≤ N → qQ e d ∣ N →
    ¬ (kK e d ∣ N * d ∧ Nat.sqrt (N * d / kK e d) * Nat.sqrt (N * d / kK e d) = N * d / kK e d)

instance (N : ℕ) : Decidable (S3Chk N) := by unfold S3Chk qQ kK; infer_instance

theorem isoQRef_of_chk {N : ℕ} (hN0 : 0 < N) (h : S3Chk N) : IsoQRef N := by
  apply isoQRef_of_dvd_case
  intro e d m he hd hQ heq
  have hQ' : qQ e d ∣ N := by simpa [qQ, sq] using hQ
  have hle : qQ e d ≤ N := Nat.le_of_dvd hN0 hQ'
  have he2 : e * e ≤ N := by unfold qQ at hle; nlinarith
  have hd2 : 2 * (d * d) ≤ N := by unfold qQ at hle; nlinarith
  have hKpos : 0 < kK e d := by unfold kK qQ; positivity
  have heq' : N * d = m * m * kK e d := by unfold kK qQ; rw [heq]; ring
  apply h e (le_trans (Nat.le_mul_self e) he2) he he2 d (by nlinarith [Nat.le_mul_self d]) hd hd2 hQ'
  have hdiv : N * d / kK e d = m * m := by
    rw [heq']; exact Nat.mul_div_cancel _ hKpos
  refine ⟨⟨m * m, by rw [heq']; ring⟩, ?_⟩
  rw [hdiv, Nat.sqrt_eq]

/-! ## IsoH9b -/

/-- the "bad" data for a pair `(a, b)`: `c² = a²+ab+b²`, `k² = b(N/e)`, `b ∣ k(c−a−b)` with parity `nA ≡ N (2)`. -/
def IsoBad (N a b : ℕ) : Prop :=
  Nat.sqrt (a ^ 2 + a * b + b ^ 2) * Nat.sqrt (a ^ 2 + a * b + b ^ 2) = a ^ 2 + a * b + b ^ 2 ∧
  Nat.sqrt (b * (N / (a + 2 * b))) * Nat.sqrt (b * (N / (a + 2 * b))) = b * (N / (a + 2 * b)) ∧
  ((Nat.sqrt (b * (N / (a + 2 * b))) : ℤ) * ((Nat.sqrt (a ^ 2 + a * b + b ^ 2) : ℤ) - a - b)) % b = 0 ∧
  ((((Nat.sqrt (b * (N / (a + 2 * b))) : ℤ) * ((Nat.sqrt (a ^ 2 + a * b + b ^ 2) : ℤ) - a - b)) / b - N) % 2 = 0)

instance (N a b : ℕ) : Decidable (IsoBad N a b) := by unfold IsoBad; infer_instance

/-- Enumerated by the divisor `e = a + 2b` of `N` and `b < e/2`. -/
def IsoH9bChk (N : ℕ) : Prop :=
  ∀ e < N, 3 ≤ e → e ∣ N → ∀ b < e, 0 < b → 2 * b < e → Nat.gcd b e = 1 → ¬ IsoBad N (e - 2 * b) b

instance (N : ℕ) : Decidable (IsoH9bChk N) := by unfold IsoH9bChk; infer_instance

theorem isoH9b_of_chk {N : ℕ} (hN : 0 < N) (h : IsoH9bChk N) : IsoH9b N := by
  apply isoH9b_of_check N hN
  intro a ha b hb ha0 hb0 hlt h3 hdvd hg h1 h2 h3' h4
  have := h (a + 2 * b) hlt h3 hdvd b (by omega) hb0 (by omega) hg
  apply this
  simp only [Nat.add_sub_cancel]
  exact ⟨h1, h2, h3', h4⟩

/-! ## sqrt-bounded variants (reduce prove-term size for large N in `decide +kernel`) -/

/-- `NSqChk` with outer bound `√N` (equivalent: `x*x ≤ N ↔ x ≤ √N`). -/
def NSqChkSq (N : ℕ) : Prop :=
  ∀ x ≤ Nat.sqrt N, x * x ≤ N → Nat.sqrt (N - x * x) * Nat.sqrt (N - x * x) ≠ N - x * x
instance (N : ℕ) : Decidable (NSqChkSq N) := by unfold NSqChkSq; infer_instance
theorem nsqChk_of_sq {N : ℕ} (h : NSqChkSq N) : NSqChk N :=
  fun x _ hx => h x (Nat.le_sqrt.mpr hx) hx

/-- `NHSqChk` with outer bound `√(N/2)` (equivalent: `2*(x*x) ≤ N ↔ x ≤ √(N/2)`). -/
def NHSqChkSq (N : ℕ) : Prop :=
  ∀ x ≤ Nat.sqrt (N / 2), 2 * (x * x) ≤ N →
    Nat.sqrt (N / 2 - x * x) * Nat.sqrt (N / 2 - x * x) ≠ N / 2 - x * x
instance (N : ℕ) : Decidable (NHSqChkSq N) := by unfold NHSqChkSq; infer_instance
theorem nhsqChk_of_sq {N : ℕ} (h : NHSqChkSq N) : NHSqChk N :=
  fun x _ hx =>
    h x (Nat.le_sqrt.mpr ((Nat.le_div_iff_mul_le (by norm_num)).mpr (by linarith))) hx

/-- `HArithChk` with sub-quantifiers bounded by `√N` or `√(2N)`. -/
def HArithChkSq (N : ℕ) : Prop :=
  0 < N ∧
  (∀ r ≤ Nat.sqrt N, 2 * (r * r) ≠ N) ∧
  (∀ t ≤ Nat.sqrt N, t * t ≠ N) ∧
  (∀ y ≤ Nat.sqrt N, 3 * (y * y) ≠ 2 * N) ∧
  (∀ t ≤ Nat.sqrt (2 * N), t * t ≠ 2 * N) ∧
  (∀ x ≤ Nat.sqrt N, 3 * (x * x) ≠ N) ∧
  (∀ r ≤ Nat.sqrt N, 10 * (r * r) ≠ N)
instance (N : ℕ) : Decidable (HArithChkSq N) := by unfold HArithChkSq; infer_instance
theorem hArithChk_of_sq {N : ℕ} (h : HArithChkSq N) : HArithChk N := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r _ heq; exact h1 r (Nat.le_sqrt.mpr (by nlinarith)) heq
  · intro t _ heq; exact h2 t (Nat.le_sqrt.mpr (by linarith)) heq
  · intro y _ heq; exact h3 y (Nat.le_sqrt.mpr (by nlinarith)) heq
  · intro t _ heq; exact h4 t (Nat.le_sqrt.mpr (by linarith)) heq
  · intro x _ heq; exact h5 x (Nat.le_sqrt.mpr (by nlinarith)) heq
  · intro r _ heq; exact h6 r (Nat.le_sqrt.mpr (by nlinarith)) heq

/-- `S3Chk` with outer loop bounded by `√N` and inner loop by `√(N/2)`. -/
def S3ChkSq (N : ℕ) : Prop :=
  ∀ e ≤ Nat.sqrt N, 1 ≤ e → e * e ≤ N →
  ∀ d ≤ Nat.sqrt (N / 2), 1 ≤ d → 2 * (d * d) ≤ N → qQ e d ∣ N →
    ¬ (kK e d ∣ N * d ∧ Nat.sqrt (N * d / kK e d) * Nat.sqrt (N * d / kK e d) = N * d / kK e d)
instance (N : ℕ) : Decidable (S3ChkSq N) := by unfold S3ChkSq qQ kK; infer_instance
theorem s3Chk_of_sq {N : ℕ} (h : S3ChkSq N) : S3Chk N :=
  fun e _ he1 he2 d _ hd1 hd2 hQ =>
    h e (Nat.le_sqrt.mpr he2) he1 he2
      d (Nat.le_sqrt.mpr ((Nat.le_div_iff_mul_le (by norm_num)).mpr (by linarith)))
      hd1 hd2 hQ

end Erdos634.Draft.AllNExclusion

#print axioms Erdos634.Draft.AllNExclusion.nsq_of_chk
#print axioms Erdos634.Draft.AllNExclusion.nhsq_of_chk
#print axioms Erdos634.Draft.AllNExclusion.harith_of_chk
#print axioms Erdos634.Draft.AllNExclusion.ell_of_chk
#print axioms Erdos634.Draft.AllNExclusion.gapR8_of_chk
#print axioms Erdos634.Draft.AllNExclusion.isoQRef_of_chk
#print axioms Erdos634.Draft.AllNExclusion.isoH9b_of_chk
