/-
Lemma S, node A5, class EVEN (n ≡ 2 mod 4): **Theorem T, the top-conductor linear algebra**,
as an abstract statement over a commutative ring R in which 2, 3, 5 are units
(round2/PROOF_round2.md §4.2 "Lemma T (EVEN, top conductor)").

At the top conductor the relation becomes a five-point element of ℂ[R]:

  Φ = c₁[x] − z c₁[x/2] + c₂[y] − z c₂[y/2] + c₃[V],   x + y + 2V = 0,

(x, y the two odd points, V the half of the even point, z = η̄(2) ≠ 0), and N± gives the parity
Φ(u) = s·Φ(−u) at every unit u (s = ±1).  Here x = 2w is written through its half w.

  **Theorem T (abstract).** Then c₃ = 0, and either c₁ = c₂ = 0, or y = x and c₁ + c₂ = 0
  (pattern P1), or y = −x and c₁ = s·c₂ (pattern P2).

This replaces `pattern_check.py`'s finite linear algebra by a proof: the coincidence pattern is
decided by case analysis on y ∈ {±x, 2x, −2x, −3x} (the only values at which a coincidence can
affect the argument), and the p = 7 double coincidence (−3x = x/2 when 7 = 0) is its own branch.
No `decide` is needed: every non-coincidence is `a − b = c·w` with c ∈ ±{1,2,3,4,5,6,8,9,10,12}
a unit.  (In ZMod (p^r), p ≥ 7, the only one of these that can vanish is 7, handled separately.)
Formalization debt, not /goal progress.
-/
import Mathlib

namespace Erdos634.LemmaSEvenT

section
variable {R : Type*} [CommRing R] [Nontrivial R] [DecidableEq R]

/-- The five-point element (as a function R → ℂ): points 2w, w, y, y', V. -/
noncomputable def Phi5 (c1 c2 c3 z : ℂ) (w y y' V : R) (u : R) : ℂ :=
  (if u = 2 * w then c1 else 0) + (if u = w then -z * c1 else 0) + (if u = y then c2 else 0) +
    (if u = y' then -z * c2 else 0) + (if u = V then c3 else 0)

theorem nek {w a b c : R} (hw : IsUnit w) (hc : IsUnit c) (h : a - b = c * w) : a ≠ b := by
  intro hab; rw [hab, sub_self] at h; exact (hc.mul hw).ne_zero h.symm

theorem small_units (u2 : IsUnit (2 : R)) (u3 : IsUnit (3 : R)) (u5 : IsUnit (5 : R)) :
    IsUnit (4 : R) ∧ IsUnit (6 : R) ∧ IsUnit (8 : R) ∧ IsUnit (9 : R) ∧ IsUnit (10 : R) ∧
      IsUnit (12 : R) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := u2.mul u2; norm_num at this; exact this
  · have := u2.mul u3; norm_num at this; exact this
  · have := (u2.mul u2).mul u2; norm_num at this; exact this
  · have := u3.mul u3; norm_num at this; exact this
  · have := u2.mul u5; norm_num at this; exact this
  · have := (u2.mul u2).mul u3; norm_num at this; exact this

end

set_option hygiene false in
/-- Prove `a ≠ b` from `a − b = c·w`, c a small unit (hypotheses named `hw`, `k2` … `k12`). -/
macro "ne_tac" : tactic => `(tactic| first
  | exact nek hw isUnit_one (by ring1) | exact nek hw isUnit_one.neg (by ring1)
  | exact nek hw k2 (by ring1) | exact nek hw k2.neg (by ring1)
  | exact nek hw k3 (by ring1) | exact nek hw k3.neg (by ring1)
  | exact nek hw k4 (by ring1) | exact nek hw k4.neg (by ring1)
  | exact nek hw k5 (by ring1) | exact nek hw k5.neg (by ring1)
  | exact nek hw k6 (by ring1) | exact nek hw k6.neg (by ring1)
  | exact nek hw k8 (by ring1) | exact nek hw k8.neg (by ring1)
  | exact nek hw k9 (by ring1) | exact nek hw k9.neg (by ring1)
  | exact nek hw k10 (by ring1) | exact nek hw k10.neg (by ring1)
  | exact nek hw k12 (by ring1) | exact nek hw k12.neg (by ring1))

set_option hygiene false in
/-- Evaluate `Phi5` at explicit points. -/
macro "evalPhi" l:(ppSpace Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp (disch := first | ring1 | ne_tac | assumption) only [Phi5, if_pos, if_neg, ↓reduceIte] $[$l]?)

section
variable {R : Type*} [CommRing R] [Nontrivial R] [DecidableEq R]

set_option maxHeartbeats 4000000 in
/-- **Key step**: the coefficient c₁ of the odd point x = 2w vanishes unless y = ±x. -/
theorem key1 {w y y' V : R} {c1 c2 c3 z s : ℂ} (u2 : IsUnit (2 : R)) (u3 : IsUnit (3 : R))
    (u5 : IsUnit (5 : R)) (hrel : 2 * w + y + 2 * V = 0) (hy' : 2 * y' = y) (hw : IsUnit w)
    (hz : z ≠ 0)
    (hsym : ∀ u, IsUnit u → Phi5 c1 c2 c3 z w y y' V u = s * Phi5 c1 c2 c3 z w y y' V (-u))
    (hne1 : y ≠ 2 * w) (hne2 : y ≠ -(2 * w)) : c1 = 0 := by
  obtain ⟨k4, k6, k8, k9, k10, k12⟩ := small_units u2 u3 u5
  have k2 := u2; have k3 := u3; have k5 := u5
  by_cases hA : y = 4 * w
  · subst hA
    obtain rfl : y' = 2 * w := u2.mul_left_cancel (by rw [hy']; ring)
    obtain rfl : V = -3 * w := u2.mul_left_cancel (by linear_combination hrel)
    have E := hsym w hw
    evalPhi at E
    have h : z * c1 = 0 := by linear_combination -E
    exact (mul_eq_zero.1 h).resolve_left hz
  by_cases hC : y = -4 * w
  · subst hC
    obtain rfl : y' = -2 * w := u2.mul_left_cancel (by rw [hy']; ring)
    obtain rfl : V = 1 * w := u2.mul_left_cancel (by linear_combination hrel)
    have E1 := hsym (2 * w) (u2.mul hw)
    have E2 := hsym (-4 * w) (k4.neg.mul hw)
    evalPhi at E1 E2
    linear_combination E1 - s * z * E2
  by_cases hB : y = -6 * w
  · subst hB
    obtain rfl : y' = -3 * w := u2.mul_left_cancel (by rw [hy']; ring)
    obtain rfl : V = 2 * w := u2.mul_left_cancel (by linear_combination hrel)
    by_cases h7 : (7 : R) = 0
    · have h76 : w = -6 * w := by linear_combination w * h7
      have E1 := hsym w hw
      have E2 := hsym (-3 * w) (k3.neg.mul hw)
      simp only [Phi5, if_pos h76] at E1
      evalPhi at E1 E2
      have h2 : z * c2 = 0 := by linear_combination -E2
      have hc2 : c2 = 0 := (mul_eq_zero.1 h2).resolve_left hz
      have h1 : z * c1 = 0 := by linear_combination -E1 + hc2
      exact (mul_eq_zero.1 h1).resolve_left hz
    · have h76 : ¬ (w = -6 * w) := by
        intro h
        apply h7
        have h' : (7 : R) * w = 0 := by linear_combination h
        obtain ⟨uw, rfl⟩ := hw
        have := congrArg (· * ((uw⁻¹ : Rˣ) : R)) h'
        simpa [mul_assoc] using this
      have E1 := hsym w hw
      evalPhi at E1
      have h1 : z * c1 = 0 := by linear_combination -E1
      exact (mul_eq_zero.1 h1).resolve_left hz
  · -- no coincidence touches ±x
    have h1 : ¬ (2 * w = y) := fun h => hne1 h.symm
    have h2 : ¬ (2 * w = y') := fun h => hA (by rw [← hy', ← h]; ring)
    have h3 : ¬ (2 * w = V) := fun h => hB (by linear_combination hrel + 2 * h)
    have h4 : ¬ (-(2 * w) = y) := fun h => hne2 h.symm
    have h5 : ¬ (-(2 * w) = y') := fun h => hC (by rw [← hy', ← h]; ring)
    have h6 : ¬ (-(2 * w) = V) := fun h => hne1 (by linear_combination hrel + 2 * h)
    have E := hsym (2 * w) (u2.mul hw)
    evalPhi at E
    linear_combination E

/-- The same five-point element with the roles of the two odd points exchanged. -/
theorem Phi5_swap (c1 c2 c3 z : ℂ) (w y y' V : R) (hy' : 2 * y' = y) (u : R) :
    Phi5 c2 c1 c3 z y' (2 * w) w V u = Phi5 c1 c2 c3 z w y y' V u := by
  unfold Phi5; rw [hy']; ring

set_option maxHeartbeats 4000000 in
/-- **Theorem T (abstract).** -/
theorem theoremT {w y y' V : R} {c1 c2 c3 z s : ℂ} (u2 : IsUnit (2 : R)) (u3 : IsUnit (3 : R))
    (u5 : IsUnit (5 : R)) (hrel : 2 * w + y + 2 * V = 0) (hy' : 2 * y' = y) (hz : z ≠ 0)
    (hc1 : c1 ≠ 0 → IsUnit w) (hc2 : c2 ≠ 0 → IsUnit y') (hc3 : c3 ≠ 0 → IsUnit V)
    (hsym : ∀ u, IsUnit u → Phi5 c1 c2 c3 z w y y' V u = s * Phi5 c1 c2 c3 z w y y' V (-u)) :
    c3 = 0 ∧ ((c1 = 0 ∧ c2 = 0) ∨ (y = 2 * w ∧ c1 + c2 = 0) ∨ (y = -(2 * w) ∧ c1 = s * c2)) := by
  obtain ⟨k4, k6, k8, k9, k10, k12⟩ := small_units u2 u3 u5
  have k2 := u2; have k3 := u3; have k5 := u5
  have K1 : c1 ≠ 0 → y = 2 * w ∨ y = -(2 * w) := by
    intro h
    by_contra hc
    push Not at hc
    exact h (key1 u2 u3 u5 hrel hy' (hc1 h) hz hsym hc.1 hc.2)
  have K2 : c2 ≠ 0 → y = 2 * w ∨ y = -(2 * w) := by
    intro h
    by_contra hc
    push Not at hc
    apply h
    refine key1 (c2 := c1) (y := 2 * w) (y' := w) (V := V) (s := s) u2 u3 u5
      (by rw [← hy'] at hrel; linear_combination hrel) rfl (hc2 h) hz
      (fun u hu => by rw [Phi5_swap _ _ _ _ _ _ _ _ hy', Phi5_swap _ _ _ _ _ _ _ _ hy']; exact hsym u hu)
      (fun h' => hc.1 (by rw [← hy']; linear_combination -h'))
      (fun h' => hc.2 (by rw [← hy']; linear_combination h'))
  by_cases h12 : c1 = 0 ∧ c2 = 0
  · refine ⟨?_, Or.inl h12⟩
    by_contra h3
    have hw := hc3 h3
    have E := hsym V hw
    obtain ⟨rfl, rfl⟩ := h12
    simp only [Phi5, mul_zero, neg_zero, ite_self, zero_add] at E
    evalPhi at E
    exact h3 (by linear_combination E)
  · have hcase : y = 2 * w ∨ y = -(2 * w) := by
      by_cases h1 : c1 = 0
      · exact K2 (fun h2 => h12 ⟨h1, h2⟩)
      · exact K1 h1
    have hw : IsUnit w := by
      by_cases h1 : c1 = 0
      · have hy := hc2 (fun h2 => h12 ⟨h1, h2⟩)
        rcases hcase with h | h
        · have : y' = w := u2.mul_left_cancel (by rw [hy', h])
          rw [← this]; exact hy
        · have : y' = -w := u2.mul_left_cancel (by rw [hy', h]; ring)
          have := hy.neg; rw [‹y' = -w›, neg_neg] at this; exact this
      · exact hc1 h1
    rcases hcase with rfl | rfl
    · obtain rfl : y' = 1 * w := u2.mul_left_cancel (by rw [hy']; ring)
      obtain rfl : V = -2 * w := u2.mul_left_cancel (by linear_combination hrel)
      have E1 := hsym w hw
      have E2 := hsym (-2 * w) (k2.neg.mul hw)
      evalPhi at E1 E2
      have hsum : c1 + c2 = 0 := by
        have : z * (c1 + c2) = 0 := by linear_combination -E1
        exact (mul_eq_zero.1 this).resolve_left hz
      exact ⟨by linear_combination E2 + s * hsum, Or.inr (Or.inl ⟨rfl, hsum⟩)⟩
    · obtain rfl : y' = -w := u2.mul_left_cancel (by rw [hy']; ring)
      obtain rfl : V = 0 := u2.mul_left_cancel (by linear_combination hrel)
      have h3 : c3 = 0 := by
        by_contra h; exact not_isUnit_zero (hc3 h)
      have E := hsym (2 * w) (u2.mul hw)
      subst h3
      evalPhi at E
      exact ⟨rfl, Or.inr (Or.inr ⟨rfl, by linear_combination E⟩)⟩

end

/-! ## Witnesses: every hypothesis of `theoremT` is satisfiable, in each conclusion branch
(R = ZMod 7, w = 4 so x = 1). -/

/-- In pattern P2 with c₁ = c₂ and c₃ = 0, Φ is even. -/
theorem Phi5_P2_even {R : Type*} [CommRing R] [DecidableEq R] (c z : ℂ) (w : R) (u : R) :
    Phi5 c c 0 z w (-(2 * w)) (-w) 0 u = Phi5 c c 0 z w (-(2 * w)) (-w) 0 (-u) := by
  have e1 : (-u = 2 * w) ↔ (u = -(2 * w)) := neg_eq_iff_eq_neg
  have e2 : (-u = w) ↔ (u = -w) := neg_eq_iff_eq_neg
  have e3 : (-u = -(2 * w)) ↔ (u = 2 * w) := neg_inj
  have e4 : (-u = -w) ↔ (u = w) := neg_inj
  unfold Phi5
  simp only [e1, e2, e3, e4, mul_zero, ite_self, add_zero]
  split_ifs <;> ring

instance fact17 : Fact (1 < 7) := ⟨by norm_num⟩

/-- **Witness** (non-vacuity of `theoremT`, pattern P2 branch): R = ZMod 7, w = 4 (x = 1), y = −1,
V = 0, c₁ = c₂ = 1, z = 1, s = 1; every hypothesis holds and the conclusion lands in P2. -/
theorem witness_T_P2 : (0 : ℂ) = 0 ∧ (((1 : ℂ) = 0 ∧ (1 : ℂ) = 0) ∨
    ((-(2 * 4) : ZMod 7) = 2 * 4 ∧ (1 : ℂ) + 1 = 0) ∨ ((-(2 * 4) : ZMod 7) = -(2 * 4) ∧ (1 : ℂ) = 1 * 1)) :=
  theoremT (R := ZMod 7) (w := 4) (y := -(2 * 4)) (y' := -4) (V := 0) (by decide) (by decide) (by decide) (by decide)
    (by ring) one_ne_zero (fun _ => by decide) (fun _ => by decide) (fun h => absurd rfl h)
    (fun u _ => by rw [one_mul]; exact Phi5_P2_even 1 1 4 u)

/-- **Witness**, pattern P1 branch: y = x = 1 (w = 4), V = −1, c₁ = 1, c₂ = −1, c₃ = 0: Φ ≡ 0. -/
theorem witness_T_P1 : (0 : ℂ) = 0 ∧ (((1 : ℂ) = 0 ∧ (-1 : ℂ) = 0) ∨
    ((2 * 4 : ZMod 7) = 2 * 4 ∧ (1 : ℂ) + -1 = 0) ∨ ((2 * 4 : ZMod 7) = -(2 * 4) ∧ (1 : ℂ) = 1 * -1)) :=
  theoremT (R := ZMod 7) (w := 4) (y' := 4) (V := -(4 * 2)) (by decide) (by decide) (by decide) (by decide)
    (by ring) one_ne_zero (fun _ => by decide) (fun _ => by decide) (fun h => absurd rfl h)
    (fun u _ => by
      simp only [Phi5]
      split_ifs <;> ring)

#print axioms Erdos634.LemmaSEvenT.key1
#print axioms Erdos634.LemmaSEvenT.theoremT
#print axioms Erdos634.LemmaSEvenT.witness_T_P2
#print axioms Erdos634.LemmaSEvenT.witness_T_P1

end Erdos634.LemmaSEvenT
