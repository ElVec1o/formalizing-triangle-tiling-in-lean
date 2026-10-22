import Erdos634.Draft.LaczFormalBZL7d6
import Erdos634.Draft.LaczFormalClassifyFinal3
import Erdos634.Draft.LaczFormalBZL7i1
import Erdos634.Draft.LaczFormal51Gen2

-- Draft/LaczFormalBZL7j3.lean -- THE RATIONAL-ANGLE CASE alpha in Q pi of the gamma = 2pi/3 tile (alpha, pi/3 - alpha, 2pi/3), target NOT similar to the tile.
-- Beeson-Zhang Thm 1.1 assumes alpha not in Q pi.  For alpha in Q pi the conclusion of Thm 1.1 (commensurable sides) is FALSE (BZL7j4: 3 copies of the (30,30,120) triangle tile an equilateral triangle, sides (1,1,sqrt 3)).
-- What the project's classification of rational-angle tiles (Laczkovich 1995 Thm 5.1/5.3 route: `classify_commensurable_final3`, `Covered3 n`) gives for this family:
--   `bz_rational_classify` : n, a' with D.model.angleAt k = a'_k pi / n, gcd(a') = 1, `Covered3 n`, target not similar  ==>  alpha = pi/6 and the target is EQUILATERAL (the tile is (pi/6, pi/6, 2pi/3));
--   `bz_rational_exists`   : for alpha in Q pi the reduced common denominator n exists, hence: for every reduced denominator n with `Covered3 n` the above holds.
-- NOT covered: reduced denominators n (3 | n) with prime factors only in {2,3,5} and not in the certified lists (`Covered3`), see (private working notes, not included).  NOTE, UNAUDITED.
-- Credit: Laczkovich (Discrete Math. 140 (1995) Thm 5.1, 5.3; Combinatorica 10 (1990); DCG 48 (2012)), Beeson-Zhang (arXiv 2604.01314), Beeson, Paliy.

open scoped BigOperators Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional Erdos634.Draft.LaczFormal.RG

namespace Erdos634.Draft.LaczFormal

variable {N : ℕ}

theorem tp_no_right {T : Tri} {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) (k : Fin 3) : T.angleAt k ≠ Real.pi / 2 := by
  obtain ⟨hr0, hr1⟩ := h.alpha_range
  have hpi := Real.pi_pos
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := h
  obtain ⟨m, rfl⟩ := σ.surjective k
  have f3 : m = 0 ∨ m = 1 ∨ m = 2 := by revert m; decide
  rcases f3 with rfl | rfl | rfl
  · rw [h0]; intro e; linarith
  · rw [h1]; intro e; linarith
  · rw [h2]; intro e; linarith

theorem bz_rational_classify (D : CongruentDissection N) {α a b c : ℝ} (h : D.model.TwoPiThreeData α a b c) (hNS : NotSim D)
    {n : ℕ} (hn : 0 < n) (a' : Fin 3 → ℕ) (ha : ∀ k, D.model.angleAt k = a' k * Real.pi / n)
    (hgcd : Nat.gcd (a' 0) (Nat.gcd (a' 1) (a' 2)) = 1) (hcov : Covered3 n) :
    α = Real.pi / 6 ∧ ∀ j, D.target.angleAt j = Real.pi / 3 := by
  have hr := h.alpha_range
  have hpi := Real.pi_pos
  have hno := tp_no_right h
  have hall : ∀ k, D.model.angleAt k = α ∨ D.model.angleAt k = Real.pi / 3 - α ∨ D.model.angleAt k = 2 * Real.pi / 3 := by
    obtain ⟨σ, h0, -, h1, -, h2, -⟩ := h
    intro k
    obtain ⟨m, rfl⟩ := σ.surjective k
    have f3 : m = 0 ∨ m = 1 ∨ m = 2 := by revert m; decide
    rcases f3 with rfl | rfl | rfl
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h2)
  rcases classify_commensurable_final3 D hn a' ha hgcd hcov with hsim | ⟨k, l, -, hk, -⟩ | hexc
  · exfalso
    obtain ⟨μ, τ, hτ⟩ := hsim
    exact hNS ⟨τ, fun j => (hτ j).1⟩
  · exact absurd hk (hno k)
  · -- ExcPair3
    have key : ∀ (x y z : ℝ), TileAngles D x y z → ∀ k, D.model.angleAt k = x ∨ D.model.angleAt k = y ∨ D.model.angleAt k = z := by
      rintro x y z ⟨τ, t0, t1, t2⟩ k
      obtain ⟨m, rfl⟩ := τ.surjective k
      have f3 : m = 0 ∨ m = 1 ∨ m = 2 := by revert m; decide
      rcases f3 with rfl | rfl | rfl
      · exact Or.inl t0
      · exact Or.inr (Or.inl t1)
      · exact Or.inr (Or.inr t2)
    have hπ6 : ∀ (x y z : ℝ), TileAngles D x y z → (x = Real.pi / 2 ∨ y = Real.pi / 2 ∨ z = Real.pi / 2) → False := by
      rintro x y z ⟨τ, t0, t1, t2⟩ hx
      rcases hx with e | e | e
      · exact hno (τ 0) (by rw [t0, e])
      · exact hno (τ 1) (by rw [t1, e])
      · exact hno (τ 2) (by rw [t2, e])
    unfold ExcPair3 at hexc
    rcases hexc with ⟨hT, hG⟩ | ⟨hT, hG⟩ | ⟨hT, hG⟩
    · refine ⟨?_, ?_⟩
      · have hk := key _ _ _ hT 0
        have := hall 0
        -- alpha is one of the model angles, hence in {pi/6, 4pi/6}; alpha < pi/3
        obtain ⟨σ, h0, -⟩ := h
        have hA := key _ _ _ hT (σ 0)
        rw [h0] at hA
        rcases hA with e | e | e
        · linarith
        · linarith
        · exfalso; linarith [hr.2]
      · obtain ⟨ρ, g0, g1, g2⟩ := hG
        intro j
        obtain ⟨m, rfl⟩ := ρ.surjective j
        have f3 : m = 0 ∨ m = 1 ∨ m = 2 := by revert m; decide
        rcases f3 with rfl | rfl | rfl
        · rw [g0]; ring
        · rw [g1]; ring
        · rw [g2]; ring
    · exact (hπ6 _ _ _ hT (Or.inr (Or.inr (by ring)))).elim
    · exact (hπ6 _ _ _ hT (Or.inr (Or.inr (by ring)))).elim

/-- For `alpha` a rational multiple of `pi`, the tile angles have a reduced common denominator `n` and numerators `a'` in the model's vertex order. -/
theorem bz_rational_exists (D : CongruentDissection N) {α a b c : ℝ} (h : D.model.TwoPiThreeData α a b c)
    (hrat : ∃ r : ℚ, α = (r : ℝ) * Real.pi) :
    ∃ (n : ℕ) (a' : Fin 3 → ℕ), 0 < n ∧ (∀ k, D.model.angleAt k = a' k * Real.pi / n) ∧
      Nat.gcd (a' 0) (Nat.gcd (a' 1) (a' 2)) = 1 := by
  obtain ⟨r, hr⟩ := hrat
  have hpi := Real.pi_pos
  have hrng := h.alpha_range
  have hq : ∀ k : Fin 3, ∃ q : ℚ, 0 < q ∧ D.model.angleAt k = (q : ℝ) * Real.pi := by
    obtain ⟨σ, h0, -, h1, -, h2, -⟩ := h
    intro k
    obtain ⟨m, rfl⟩ := σ.surjective k
    have f3 : m = 0 ∨ m = 1 ∨ m = 2 := by revert m; decide
    rcases f3 with rfl | rfl | rfl
    · refine ⟨r, ?_, by rw [h0, hr]⟩
      have : (0 : ℝ) < (r : ℝ) := by
        by_contra hneg; push Not at hneg; nlinarith [hrng.1]
      exact_mod_cast this
    · refine ⟨1 / 3 - r, ?_, by rw [h1, hr]; push_cast; ring⟩
      have : (0 : ℝ) < ((1 / 3 - r : ℚ) : ℝ) := by
        push_cast
        by_contra hneg; push Not at hneg; nlinarith [hrng.2]
      exact_mod_cast this
    · exact ⟨2 / 3, by norm_num, by rw [h2]; push_cast; ring⟩
  choose q hq0 hqa using hq
  have hs : q 0 + q 1 + q 2 = 1 := by
    have hsum := D.model.angleAt_sum
    simp only [Fin.sum_univ_three] at hsum
    rw [hqa 0, hqa 1, hqa 2] at hsum
    have : ((q 0 + q 1 + q 2 : ℚ) : ℝ) = ((1 : ℚ) : ℝ) := by
      push_cast
      have := mul_right_cancel₀ hpi.ne' (show ((q 0 : ℝ) + q 1 + q 2) * Real.pi = 1 * Real.pi by linarith)
      linarith
    exact_mod_cast this
  obtain ⟨n, a0, a1, a2, hn, -, hg, e0, e1, e2⟩ := Erdos634.Lacz51Gen2.common_denom (hq0 0) (hq0 1) (hq0 2) hs
  refine ⟨n, ![a0, a1, a2], hn, ?_, hg⟩
  intro k
  have f3 : k = 0 ∨ k = 1 ∨ k = 2 := by revert k; decide
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rcases f3 with rfl | rfl | rfl
  · rw [hqa 0, e0]; push_cast; show _ = ((a0 : ℕ) : ℝ) * Real.pi / n; ring
  · rw [hqa 1, e1]; push_cast; show _ = ((a1 : ℕ) : ℝ) * Real.pi / n; ring
  · rw [hqa 2, e2]; push_cast; show _ = ((a2 : ℕ) : ℝ) * Real.pi / n; ring

/-- **Rational-angle case of the gamma = 2pi/3 tile, target not similar**: if `alpha in Q pi`, then for the reduced common denominator `n` of the tile angles: `Covered3 n` implies `alpha = pi/6` and the target is equilateral. -/
theorem bz_rational_final (D : CongruentDissection N) {α a b c : ℝ} (h : D.model.TwoPiThreeData α a b c) (hNS : NotSim D)
    (hrat : ∃ r : ℚ, α = (r : ℝ) * Real.pi) :
    ∃ (n : ℕ) (a' : Fin 3 → ℕ), 0 < n ∧ (∀ k, D.model.angleAt k = a' k * Real.pi / n) ∧
      Nat.gcd (a' 0) (Nat.gcd (a' 1) (a' 2)) = 1 ∧
      (Covered3 n → α = Real.pi / 6 ∧ ∀ j, D.target.angleAt j = Real.pi / 3) := by
  obtain ⟨n, a', hn, ha, hg⟩ := bz_rational_exists D h hrat
  exact ⟨n, a', hn, ha, hg, fun hc => bz_rational_classify D h hNS hn a' ha hg hc⟩

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.tp_no_right
#print axioms Erdos634.Draft.LaczFormal.bz_rational_classify
#print axioms Erdos634.Draft.LaczFormal.bz_rational_exists
#print axioms Erdos634.Draft.LaczFormal.bz_rational_final
