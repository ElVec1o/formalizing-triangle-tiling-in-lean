-- Draft/FluxFRow15Conj.lean — ROW 15 (rationality_proofs.md §5, §3): the degree case split and the
-- conjugate principle, as pure algebra over ℝ with rational coefficients.
--
-- (a) `conj_transfer`: the conjugate principle.  If `s` is an irrational root of `A x² + B x + C`
--     (`A, B, C ∈ ℚ`, `A ≠ 0`) and `v = −B/A − s` is the other root, then EVERY polynomial with
--     rational coefficients vanishing at `s` vanishes at `v`.  Proof by division by the monic
--     quadratic: the remainder `r₁ x + r₀` vanishes at the irrational `s`, so `r₁ = r₀ = 0`.
--     This is exactly the paper's reason: the word equations are polynomial identities with
--     integer coefficients; an algebra hom `ℚ(s) → ℝ` is not needed.
-- (b) `row15_algebraic`: the whole §5 case analysis, from the dissection-level equations
--     (Theorem-1 flux `S = h(s)·y`, area `N h(s)² = S² g(s)`, words of the sides `X` and `Y`)
--     to `s ∈ ℚ`.  SIMPLIFICATION RELATIVE TO THE PAPER (stated plainly): the deg-4, `q = 1` and
--     deg-3 leaves are not needed.  From `S = h(s)·w_Y(s)` and the area identity, `s` is a root of
--     `T(x) = A x² + B x + C` with `B = 2S·n_a + N + S² > 0`; so `s` always has degree ≤ 2 over ℚ.
--     (Same mechanism as the paper's deg-3/deg-4 computation `n_a = −M(q+1)/2`, which is the
--     statement `B = 0`.)  Degree 2 is dispatched to the pre-existing leaves 4–10
--     (FluxFRow15Cases/Cases2/Calculus, FluxFRow15.k_s_ne_k_v), whose bridge hypotheses
--     (`hXle`, `hYle`, `k v ≥ k s`, `hEq`) are DERIVED here from the words via `conj_transfer`.
--
-- Formalization debt (paper-level PROVED); not progress on the three /goal outcomes.
import Mathlib.Tactic
import Erdos634.Draft.FluxFRow15
import Erdos634.Draft.FluxFRow15Cases
import Erdos634.Draft.FluxFRow15Cases2
import Erdos634.Draft.FluxFRow15Calculus

open scoped Classical
open Polynomial

namespace Erdos634.Row15Conj

/-- **Conjugate principle.** -/
theorem conj_transfer {s v : ℝ} {A B D : ℚ} (hA : A ≠ 0)
    (hs : (A : ℝ) * s ^ 2 + (B : ℝ) * s + (D : ℝ) = 0) (hirr : ∀ r : ℚ, s ≠ (r : ℝ))
    (hv : v = -((B : ℝ) / A) - s) (P : ℚ[X]) (hP : aeval s P = 0) : aeval v P = 0 := by
  have hAr : (A : ℝ) ≠ 0 := by exact_mod_cast hA
  have hcast : ∀ x : ℚ, algebraMap ℚ ℝ x = (x : ℝ) := fun x => eq_ratCast _ x
  set q : ℚ[X] := X ^ 2 + C (B / A) * X + C (D / A) with hqdef
  have hqm : q.Monic := by
    rw [hqdef]; monicity!
  have hqd : q.degree = 2 := by
    rw [hqdef]; compute_degree!
  have hqs : aeval s q = 0 := by
    rw [hqdef]; simp only [map_add, map_mul, map_pow, aeval_X, aeval_C, hcast]
    push_cast
    field_simp
    linear_combination hs
  have hqv : aeval v q = 0 := by
    rw [hqdef]; simp only [map_add, map_mul, map_pow, aeval_X, aeval_C, hcast]
    push_cast
    rw [hv]
    field_simp
    linear_combination (A : ℝ) * hs
  have hdiv := modByMonic_add_div P q
  set r := P %ₘ q with hrdef
  have hqnd : q.natDegree = 2 := natDegree_eq_of_degree_eq_some hqd
  have hq1 : q ≠ 1 := by
    intro h; rw [h, natDegree_one] at hqnd; exact absurd hqnd (by decide)
  have hrlt : r.natDegree < 2 := hqnd ▸ natDegree_modByMonic_lt P hqm hq1
  have hrform := eq_X_add_C_of_natDegree_le_one (show r.natDegree ≤ 1 by omega)
  have hrs : aeval s r = 0 := by
    have := congrArg (aeval s) hdiv
    rw [map_add, map_mul, hqs, zero_mul, add_zero, hP] at this
    exact this
  rw [hrform] at hrs
  simp only [map_add, map_mul, aeval_X, aeval_C, hcast] at hrs
  have h1 : r.coeff 1 = 0 := by
    by_contra h1
    apply hirr (-(r.coeff 0) / r.coeff 1)
    have h1r : ((r.coeff 1 : ℚ) : ℝ) ≠ 0 := by exact_mod_cast h1
    push_cast
    field_simp
    linear_combination hrs
  rw [h1] at hrs
  simp at hrs
  have hr0 : r = 0 := by
    rw [hrform, h1, hrs]; simp
  rw [← hdiv, hr0, zero_add, map_mul, hqv, zero_mul]

open Erdos634.Row15 (g k)
open Erdos634.Row15Cases (h Y rho)
open Erdos634.Row15Calculus (F)

/-- `S·Y(x) = w(x)` from `h(x)·w(x) = S`. -/
theorem S_mul_Y {x S w : ℝ} (hx : h x ≠ 0) (hw : h x * w = S) : S * Y x = w := by
  unfold Y; rw [← hw]; field_simp

/-- `S·X(x) = w(x)` from `h(x)·w(x) = S(2−x²)`. -/
theorem S_mul_X {x S w : ℝ} (hx : h x ≠ 0) (hw : h x * w = S * (2 - x ^ 2)) : S * Row15Cases.X x = w := by
  unfold Row15Cases.X; field_simp; linarith [hw]

/-- `F(x) = N/S²` from the area identity at `x`. -/
theorem F_eq {x S N : ℝ} (hx : h x ≠ 0) (hS : S ≠ 0) (hA : N * h x ^ 2 = S ^ 2 * g x) :
    F x = N / S ^ 2 := by
  unfold F Y; field_simp; linear_combination -hA

theorem two_sub_sq_pos {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) : 0 < 2 - s ^ 2 := by nlinarith

theorem two_sub_sq_neg {v : ℝ} (hv : v < -2) : 2 - v ^ 2 < 0 := by nlinarith

theorem sq_ge_two {v : ℝ} (hv : 3 / 2 < v) : 2 ≤ v ^ 2 := by nlinarith

theorem ge_seventeen {v : ℝ} (hv0 : 0 < v) (hv : 3 < v ^ 2) : 17 / 10 ≤ v := by nlinarith

/-- **Row 15, the algebraic half (§5 with §3's conjugate principle), from dissection-level data.**
In units of the model's `c`-side: `s = a/c ∈ (0,1)`; `y = Y/c` (side opposite `α`) with word
`n_a s + n_b(1−s²) + n_c`; `(2−s²)·y` (side opposite `2α`) with word `m_a s + m_b(1−s²) + m_c`;
Theorem 1 `S = h(s)·y`; area `N·h(s)² = S²·g(s)`.  Then `s ∈ ℚ`. -/
theorem row15_algebraic (s y : ℝ) (S : ℤ) (N na nb nc ma mb mc : ℕ)
    (hs0 : 0 < s) (hs1 : s < 1) (hy : 0 < y)
    (hflux : (S : ℝ) = (1 - s) * (2 + s) * y)
    (harea : (N : ℝ) * ((1 - s) * (2 + s)) ^ 2 = (S : ℝ) ^ 2 * ((2 - s ^ 2) * (3 - s ^ 2)))
    (hY : y = na * s + nb * (1 - s ^ 2) + nc)
    (hX : (2 - s ^ 2) * y = ma * s + mb * (1 - s ^ 2) + mc) :
    ∃ r : ℚ, s = r := by
  have hhs : 0 < (1 - s) * (2 + s) := mul_pos (by linarith) (by linarith)
  have hSpos : (0 : ℝ) < S := by rw [hflux]; exact mul_pos hhs hy
  have hSq : (0 : ℚ) < S := by exact_mod_cast hSpos
  -- the quadratic `T` that `s` always satisfies
  set A : ℚ := (N : ℚ) - (S : ℚ) ^ 2 - 2 * S * nb with hAdef
  set B : ℚ := 2 * S * na + N + (S : ℚ) ^ 2 with hBdef
  set D : ℚ := 2 * S * (nb + nc) - 2 * N + 2 * (S : ℚ) ^ 2 with hDdef
  have hBpos : 0 < B := by
    have : (0 : ℚ) ≤ 2 * S * na := by positivity
    have : (0 : ℚ) < (S : ℚ) ^ 2 := by positivity
    have : (0 : ℚ) ≤ N := by positivity
    linarith
  have hT : (A : ℝ) * s ^ 2 + (B : ℝ) * s + (D : ℝ) = 0 := by
    have e : ((1 - s) * (2 + s)) * ((A : ℝ) * s ^ 2 + (B : ℝ) * s + (D : ℝ)) = 0 := by
      rw [hY] at hflux
      simp only [hAdef, hBdef, hDdef]; push_cast
      linear_combination (-2 * (S : ℝ)) * hflux - harea
    exact (mul_eq_zero.mp e).resolve_left hhs.ne'
  by_cases hA0 : A = 0
  · refine ⟨-D / B, ?_⟩
    have hBr : (B : ℝ) ≠ 0 := by exact_mod_cast hBpos.ne'
    rw [hA0] at hT; push_cast at hT ⊢
    field_simp; linear_combination hT
  by_contra hne
  push_neg at hne
  have hirr : ∀ r : ℚ, s ≠ (r : ℝ) := fun r e => hne r e
  set v : ℝ := -((B : ℝ) / A) - s with hvdef
  have hvirr : ∀ r : ℚ, v ≠ (r : ℝ) := by
    intro r e
    apply hirr (-(B / A) - r)
    push_cast; linarith [e, hvdef]
  have hv1 : v ≠ 1 := fun e => hvirr 1 (by rw [e]; norm_num)
  have hvm2 : v ≠ -2 := fun e => hvirr (-2) (by rw [e]; norm_num)
  have hvm1 : v ≠ -1 := fun e => hvirr (-1) (by rw [e]; norm_num)
  have hvs : v ≠ s := by
    intro e
    apply hirr (-(B / A) / 2)
    push_cast; linarith [e, hvdef]
  have hhv : h v ≠ 0 := by
    unfold h; intro e
    rcases mul_eq_zero.mp e with e | e
    · exact hv1 (by linarith)
    · exact hvm2 (by linarith)
  have hhs' : h s ≠ 0 := by unfold h; exact hhs.ne'
  -- conjugate transfer of the three word/area identities
  have tr := fun (P : ℚ[X]) => conj_transfer (s := s) (v := v) hA0 hT hirr rfl P
  have hcast : ∀ x : ℚ, algebraMap ℚ ℝ x = (x : ℝ) := fun x => eq_ratCast _ x
  set hP : ℚ[X] := (1 - X) * (2 + X) with hhP
  have ehP : ∀ x : ℝ, aeval x hP = h x := by
    intro x; simp [map_ofNat, hhP, h]
  -- area
  have areaT := tr (C (N : ℚ) * hP ^ 2 - C ((S : ℚ) ^ 2) * ((2 - X ^ 2) * (3 - X ^ 2)))
    (by simp [map_ofNat, ehP, hcast, h]; push_cast; linear_combination harea)
  simp [map_ofNat, ehP, hcast] at areaT
  have hAv : (N : ℝ) * h v ^ 2 = (S : ℝ) ^ 2 * g v := by
    unfold g; linear_combination areaT
  have hAs : (N : ℝ) * h s ^ 2 = (S : ℝ) ^ 2 * g s := by
    unfold g h; linear_combination harea
  -- Y word
  have wYT := tr (hP * ((na : ℚ[X]) * X + (nb : ℚ[X]) * (1 - X ^ 2) + (nc : ℚ[X])) - C (S : ℚ))
    (by simp [map_ofNat, ehP, hcast, h]; rw [hY] at hflux; linear_combination -hflux)
  simp [map_ofNat, ehP, hcast] at wYT
  set wY : ℝ → ℝ := fun x => na * x + nb * (1 - x ^ 2) + nc with hwY
  have hYv : h v * wY v = S := by simp only [hwY]; linear_combination wYT
  have hYs : h s * wY s = S := by simp only [hwY, h]; rw [hY] at hflux; linear_combination -hflux
  -- X word
  have wXT := tr (hP * ((ma : ℚ[X]) * X + (mb : ℚ[X]) * (1 - X ^ 2) + (mc : ℚ[X]))
      - C (S : ℚ) * (2 - X ^ 2))
    (by simp [map_ofNat, ehP, hcast, h]; linear_combination (-(2 - s ^ 2)) * hflux - (1 - s) * (2 + s) * hX)
  simp [map_ofNat, ehP, hcast] at wXT
  set wX : ℝ → ℝ := fun x => ma * x + mb * (1 - x ^ 2) + mc with hwX
  have hXv : h v * wX v = S * (2 - v ^ 2) := by simp only [hwX]; linear_combination wXT
  have hXs : h s * wX s = S * (2 - s ^ 2) := by
    simp only [hwX, h]; linear_combination (-(2 - s ^ 2)) * hflux - (1 - s) * (2 + s) * hX
  -- F(s) = F(v)
  have hSne : (S : ℝ) ≠ 0 := hSpos.ne'
  have hF : F s = F v := by rw [F_eq hhs' hSne hAs, F_eq hhv hSne hAv]
  have hFs : F s = g s * Y s ^ 2 := rfl
  have hFv : F v = g v * Y v ^ 2 := rfl
  have hna : (0 : ℝ) ≤ na := Nat.cast_nonneg _
  have hnb : (0 : ℝ) ≤ nb := Nat.cast_nonneg _
  have hnc : (0 : ℝ) ≤ nc := Nat.cast_nonneg _
  have hma : (0 : ℝ) ≤ ma := Nat.cast_nonneg _
  have hmb : (0 : ℝ) ≤ mb := Nat.cast_nonneg _
  rcases le_or_gt (s + v) 0 with hP0 | hP0
  · -- P ≥ 0: every side satisfies z(s) ≥ z(v)
    have hvle : v ≤ -s := by linarith
    have hYle : Y v ≤ Y s := by
      have e1 := S_mul_Y hhs' hYs
      have e2 := S_mul_Y hhv hYv
      have : wY v ≤ wY s := by
        have hid : wY s - wY v = (s - v) * (na - nb * (s + v)) := by simp only [hwY]; ring
        have h1 : (nb : ℝ) * (s + v) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hnb hP0
        have : 0 ≤ (s - v) * (na - nb * (s + v)) := mul_nonneg (by linarith) (by linarith)
        linarith
      have : (S : ℝ) * Y v ≤ S * Y s := by rw [e1, e2]; exact this
      exact le_of_mul_le_mul_left this hSpos
    rcases lt_or_ge v (-2) with hv | hv
    · have hXle : Row15Cases.X v ≤ Row15Cases.X s := by
        have e1 := S_mul_X hhs' hXs
        have e2 := S_mul_X hhv hXv
        have : wX v ≤ wX s := by
          have hid : wX s - wX v = (s - v) * (ma - mb * (s + v)) := by simp only [hwX]; ring
          have h1 : (mb : ℝ) * (s + v) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hmb hP0
          have : 0 ≤ (s - v) * (ma - mb * (s + v)) := mul_nonneg (by linarith) (by linarith)
          linarith
        have : (S : ℝ) * Row15Cases.X v ≤ S * Row15Cases.X s := by rw [e1, e2]; exact this
        exact le_of_mul_le_mul_left this hSpos
      have hXr : ∀ x : ℝ, h x ≠ 0 → 2 - x ^ 2 ≠ 0 → Row15Cases.X x ^ 2 * rho x = F x := by
        intro x hx hx2
        unfold Row15Cases.X rho F Y g; field_simp
      have h2s : 2 - s ^ 2 ≠ 0 := (two_sub_sq_pos hs0 hs1).ne'
      have h2v : 2 - v ^ 2 ≠ 0 := (two_sub_sq_neg hv).ne
      exact Erdos634.Row15Cases.row15_Pge0_v_lt_neg2 s v hs0 hs1 hv hXle
        (by rw [hXr s hhs' h2s, hXr v hhv h2v]; exact hF)
    rcases lt_or_ge v (-1) with hv' | hv'
    · have hv2 : -2 < v := lt_of_le_of_ne hv (Ne.symm hvm2)
      exact Erdos634.Row15Cases.row15_Pge0_v_in_neg2_neg1 s v hs0 hs1 hv2 hv' hYle hF
    · have hv2 : -1 < v := lt_of_le_of_ne hv' (Ne.symm hvm1)
      exact Erdos634.Row15Cases2.row15_Pge0_v_in_neg1_negs s v hs0 hs1 hv2 hvle hYle hF
  · -- P < 0
    rcases lt_or_ge v 1 with hv | hv
    · exact Erdos634.Row15Calculus.row15_leaf7_not_in_open_unit s v hs0 hs1 (by linarith) hv
        hvs hF
    have hv' : 1 < v := lt_of_le_of_ne hv (Ne.symm hv1)
    rcases le_or_gt v (3 / 2) with hv2 | hv2
    · -- leaf 10: the c-type word condition gives k v ≥ k s
      have hkk := Erdos634.Row15.k_s_ne_k_v s v hs0 hs1 hv' hv2
      have hbr : (1 - v ^ 2) * wY s ≤ (1 - s ^ 2) * wY v := by
        have hid : (1 - s ^ 2) * wY v - (1 - v ^ 2) * wY s
            = (v - s) * (na * (1 + s * v) + nc * (s + v)) := by simp only [hwY]; ring
        have hsv : 0 < s * v := mul_pos hs0 (by linarith)
        have h1 : 0 ≤ (na : ℝ) * (1 + s * v) := mul_nonneg hna (by linarith)
        have h2 : 0 ≤ (nc : ℝ) * (s + v) := mul_nonneg hnc (by linarith)
        have : 0 ≤ (v - s) * (na * (1 + s * v) + nc * (s + v)) :=
          mul_nonneg (by linarith) (by linarith)
        linarith
      have hhvneg : h v < 0 := by
        unfold h; exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
      have hhspos : 0 < h s := hhs
      -- multiply by h s · h v < 0
      have e3 : (1 - s ^ 2) * h s * S ≤ (1 - v ^ 2) * h v * S := by
        have hm : h s * h v < 0 := mul_neg_of_pos_of_neg hhspos hhvneg
        have := mul_le_mul_of_nonpos_left hbr hm.le
        have i1 : h s * h v * ((1 - v ^ 2) * wY s) = (1 - v ^ 2) * h v * S := by
          rw [← hYs]; ring
        have i2 : h s * h v * ((1 - s ^ 2) * wY v) = (1 - s ^ 2) * h s * S := by
          rw [← hYv]; ring
        linarith
      have e4 : (1 - s ^ 2) * h s ≤ (1 - v ^ 2) * h v := le_of_mul_le_mul_right e3 hSpos
      have hk : ∀ x : ℝ, 2 + x ≠ 0 → (N : ℝ) * h x ^ 2 = (S : ℝ) ^ 2 * g x →
          (S : ℝ) ^ 2 * k x = N * ((1 - x ^ 2) * h x) := by
        intro x hx hA
        unfold k; unfold h at hA ⊢; field_simp
        linear_combination (-(1 + x)) * hA
      have hk2 : (S : ℝ) ^ 2 * k s ≤ S ^ 2 * k v := by
        rw [hk s (by linarith) hAs, hk v (by linarith) hAv]
        exact mul_le_mul_of_nonneg_left e4 (Nat.cast_nonneg N)
      have := le_of_mul_le_mul_left hk2 (by positivity)
      linarith
    rcases le_or_gt (v ^ 2) 3 with hv3 | hv3
    · exact Erdos634.Row15Calculus.row15_leaf8 s v hs0 hs1 (sq_ge_two hv2) hv3 hF
    · exact Erdos634.Row15Calculus.row15_leaf9 s v hs0 hs1 (ge_seventeen (by linarith) hv3) hF

end Erdos634.Row15Conj

#print axioms Erdos634.Row15Conj.conj_transfer
#print axioms Erdos634.Row15Conj.row15_algebraic
