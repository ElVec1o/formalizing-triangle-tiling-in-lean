-- Draft/LaczFormalRG8Arith.lean -- pure arithmetic for Laczkovich DCG 48 (2012), Lemma 4.6: if `a, b` are commensurable and `c` is not a rational multiple of `a`, two finite lists of
-- lengths in `{a, b, c}` with the same sum contain the same number of entries `c`; and the convexity inequality along a line.  UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Lemma 4.6), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalThm21Def

open scoped Classical
namespace Erdos634.Draft.LaczFormal.RG

open Erdos634.Draft.LaczFormal.Thm21

/-- A sum of lengths in `{a, b, c}`: `n_c * c + r * a` with `r` rational, `r = 0` only for all-`c` lists. -/
theorem sum_count_c {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : Comm a b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ L : List ℝ, (∀ x ∈ L, x = a ∨ x = b ∨ x = c) →
      ∃ r : ℚ, 0 ≤ r ∧ L.sum = (L.count c : ℝ) * c + (r : ℝ) * a ∧ (r = 0 → ∀ x ∈ L, x = c) := by
  obtain ⟨p, q, hp, hq, hpq⟩ := hab
  have hbq : b = ((p : ℚ) / q : ℚ) * a := by
    have : (q : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    linarith
  intro L
  induction L with
  | nil => intro _; exact ⟨0, le_rfl, by simp, fun _ x hx => absurd hx (by simp)⟩
  | cons x L ih =>
    intro hL
    obtain ⟨r, hr0, hr, hrz⟩ := ih (fun y hy => hL y (List.mem_cons_of_mem _ hy))
    rcases hL x (List.mem_cons_self ..) with rfl | rfl | rfl
    · refine ⟨r + 1, by linarith [show (0 : ℚ) ≤ 1 by norm_num], ?_, ?_⟩
      · rw [List.sum_cons, hr, List.count_cons_of_ne hac]; push_cast; ring
      · intro h; exfalso; linarith [show (0 : ℚ) < 1 by norm_num]
    · refine ⟨r + (p : ℚ) / q, by positivity, ?_, ?_⟩
      · rw [List.sum_cons, hr, List.count_cons_of_ne hbc]
        push_cast
        have : ((p : ℚ) / q : ℚ) = ((p : ℝ) / q) := by push_cast; rfl
        rw [hbq]; push_cast; ring
      · intro h; exfalso
        have : (0 : ℚ) < (p : ℚ) / q := by positivity
        linarith
    · refine ⟨r, hr0, ?_, ?_⟩
      · rw [List.sum_cons, hr, List.count_cons_self]; push_cast; ring
      · intro h y hy
        rcases List.mem_cons.mp hy with rfl | hy'
        · rfl
        · exact hrz h y hy'

theorem comm_of_rat {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (ρ : ℚ) (h : c = (ρ : ℝ) * a) : Comm a c := by
  have hρ : 0 < ρ := by
    by_contra hn
    push_neg at hn
    have : (ρ : ℝ) ≤ 0 := by exact_mod_cast hn
    nlinarith
  refine ⟨ρ.num.toNat, ρ.den, ?_, ρ.den_pos, ?_⟩
  · have := Rat.num_pos.mpr hρ
    omega
  · have hn : ((ρ.num.toNat : ℕ) : ℤ) = ρ.num := Int.toNat_of_nonneg (Rat.num_pos.mpr hρ).le
    have h1 : ((ρ.num.toNat : ℕ) : ℝ) = (ρ.num : ℝ) := by exact_mod_cast hn
    rw [h1, h]
    have : (ρ : ℝ) = (ρ.num : ℝ) / ρ.den := by exact_mod_cast (Rat.num_div_den ρ).symm
    rw [this]
    have : (ρ.den : ℝ) ≠ 0 := by exact_mod_cast ρ.den_pos.ne'
    field_simp

/-- **Count lemma**: lists of lengths in `{a, b, c}` with equal sums have the same number of entries equal to `c`. -/
theorem count_c_eq {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : Comm a b) (hac : ¬ Comm a c) (L1 L2 : List ℝ)
    (h1 : ∀ x ∈ L1, x = a ∨ x = b ∨ x = c) (h2 : ∀ x ∈ L2, x = a ∨ x = b ∨ x = c) (hs : L1.sum = L2.sum) :
    L1.count c = L2.count c := by
  have hne_a : a ≠ c := fun e => hac ⟨1, 1, one_pos, one_pos, by rw [e]⟩
  have hne_b : b ≠ c := by
    intro e
    apply hac
    obtain ⟨p, q, hp, hq, hpq⟩ := hab
    exact ⟨p, q, hp, hq, by rw [hpq, e]⟩
  obtain ⟨r1, -, e1, -⟩ := sum_count_c ha hb hab hne_a hne_b L1 h1
  obtain ⟨r2, -, e2, -⟩ := sum_count_c ha hb hab hne_a hne_b L2 h2
  by_contra hne
  have hne' : ((L1.count c : ℕ) : ℝ) - (L2.count c : ℕ) ≠ 0 := by
    intro e; apply hne; have : ((L1.count c : ℕ) : ℝ) = (L2.count c : ℕ) := by linarith
    exact_mod_cast this
  have key : c = ((r2 - r1) / ((L1.count c : ℚ) - (L2.count c : ℚ)) : ℚ) * a := by
    have hq : ((L1.count c : ℚ) - (L2.count c : ℚ)) ≠ 0 := by
      intro e; apply hne'; have : ((L1.count c : ℕ) : ℝ) - (L2.count c : ℕ) = (((L1.count c : ℚ) - (L2.count c : ℚ) : ℚ) : ℝ) := by push_cast; ring
      rw [this, e]; simp
    have : ((((L1.count c : ℚ) - (L2.count c : ℚ)) : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hq
    push_cast at this ⊢
    field_simp
    linarith
  exact hac (comm_of_rat ha hc _ key)

/-- **Convexity of `x^2 + y^2` along a line.** -/
theorem nsq_convex {X V P : ℝ × ℝ} {d : ℝ × ℝ} (hd : 0 < d.1 ^ 2 + d.2 ^ 2) {s0 s : ℝ}
    (hV : V = (X.1 + s0 * d.1, X.2 + s0 * d.2)) (hP : P = (X.1 + s * d.1, X.2 + s * d.2)) (h0 : 0 < s0) (h1 : s0 < s)
    (hXV : X.1 ^ 2 + X.2 ^ 2 ≤ V.1 ^ 2 + V.2 ^ 2) : V.1 ^ 2 + V.2 ^ 2 < P.1 ^ 2 + P.2 ^ 2 := by
  subst hV hP
  simp only at hXV ⊢
  set u := X.1 * d.1 + X.2 * d.2 with hu
  set w := d.1 ^ 2 + d.2 ^ 2 with hw
  have e1 : (X.1 + s0 * d.1) ^ 2 + (X.2 + s0 * d.2) ^ 2 = X.1 ^ 2 + X.2 ^ 2 + 2 * s0 * u + s0 ^ 2 * w := by rw [hu, hw]; ring
  have e2 : (X.1 + s * d.1) ^ 2 + (X.2 + s * d.2) ^ 2 = X.1 ^ 2 + X.2 ^ 2 + 2 * s * u + s ^ 2 * w := by rw [hu, hw]; ring
  rw [e1] at hXV ⊢
  rw [e2]
  have h3 : 0 ≤ 2 * u + s0 * w := by
    have : 0 ≤ s0 * (2 * u + s0 * w) := by nlinarith
    exact nonneg_of_mul_nonneg_right this h0 |> fun h => by nlinarith
  nlinarith [mul_pos (sub_pos.mpr h1) (show 0 < 2 * u + (s + s0) * w by nlinarith [mul_pos (show 0 < s by linarith) hd])]

end Erdos634.Draft.LaczFormal.RG
