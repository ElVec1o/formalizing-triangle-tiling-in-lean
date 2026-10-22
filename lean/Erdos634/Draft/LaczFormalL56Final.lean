-- Draft/LaczFormalL56Final.lean -- the classification theorems for the TARGET atoms L5 and L6, now with no coverage hypothesis on n.
--   `classify_rational`: a congruent dissection whose tile has commensurable angles (any N, reflections allowed): SimilarTM, or right tile + isosceles target with an acute tile angle as base angle,
--     or one of the three valid n = 6 shapes.
--   `equilateral_classification` (Laczkovich DCG 48 (2012) Thm 3.3, angle part of "only if"): an EQUILATERAL target is tiled only by a tile with an irrational angle ((a, 2pi/3-a, pi/3) or (a, pi/3-a, 2pi/3)),
--     or by (pi/3,pi/3,pi/3), (pi/6,pi/6,2pi/3), (pi/6,pi/3,pi/2).
--   `table3_full` (Table 3 lines 1-7, angle statements): an isosceles NON-equilateral target.
-- Remaining for Thm 3.3 as printed: the commensurability of the sines in (iii) (side/area arithmetic) and the existence direction (constructions): not in this file.
-- UNAUDITED (NOTE).  Credit: Laczkovich (Discrete Math 140 (1995) Thm 5.1/5.3; DCG 48 (2012) Thm 3.3), Beeson-Rosu, Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalUnifC
import Erdos634.Draft.LaczFormalL6
import Erdos634.Draft.LaczFormalL5
import Erdos634.Draft.LaczFormalL2a
import Erdos634.Draft.LaczFormalL5Total

open scoped BigOperators Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
open Erdos634.Geometry.CaseA.LemmaV (nat_bounds angle_pos angle_lt_pi)

namespace Erdos634.Draft.LaczFormal

variable {N : ℕ}

/-- Rational tile angles give a primitive `(n, a)`. -/
theorem exists_primitive_na (D : CongruentDissection N) (h : CommAngles D.model) :
    ∃ (n : ℕ) (a : Fin 3 → ℕ), 0 < n ∧ (∀ k, D.model.angleAt k = a k * Real.pi / n) ∧
      Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 := by
  rw [commAngles_iff] at h
  choose q hq using h
  set n : ℕ := (q 0).den * (q 1).den * (q 2).den with hn
  have hnpos : 0 < n := Nat.mul_pos (Nat.mul_pos (q 0).den_pos (q 1).den_pos) (q 2).den_pos
  have hpos : ∀ k, 0 < D.model.angleAt k := fun k => Erdos634.MarchFlank.cornerAngle_pos D.model k
  have hqpos : ∀ k, 0 < q k := by
    intro k
    have := hpos k; rw [hq k] at this
    have h' : (0 : ℝ) < (q k : ℝ) := by
      by_contra hc; push Not at hc
      nlinarith [Real.pi_pos, mul_nonpos_of_nonpos_of_nonneg hc Real.pi_pos.le]
    exact_mod_cast h'
  have hnat : ∀ k, ∃ a : ℕ, D.model.angleAt k = a * Real.pi / n := by
    intro k
    have hd : (q k).den ∣ n := by
      fin_cases k
      · exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
      · exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
      · exact dvd_mul_left _ _
    refine ⟨(q k).num.toNat * (n / (q k).den), ?_⟩
    have hden : ((q k).den : ℝ) ≠ 0 := by exact_mod_cast (q k).den_nz
    have hnz : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
    have hcast : ((n / (q k).den : ℕ) : ℝ) = (n : ℝ) / (q k).den := Nat.cast_div hd hden
    have hnum : (((q k).num.toNat : ℕ) : ℝ) = ((q k).num : ℝ) := by
      have : (0 : ℤ) ≤ (q k).num := Rat.num_nonneg.mpr (hqpos k).le
      exact_mod_cast Int.toNat_of_nonneg this
    rw [hq k, Rat.cast_def]
    push_cast
    rw [hcast, hnum]
    field_simp
  choose a ha using hnat
  have hsum := Erdos634.CaseA.R0c.sum_of_angles hnpos ha
  have ha1 : ∀ i, 1 ≤ a i := fun i => (nat_bounds hnpos (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  set g := Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (ha1 0)
  have hga : ∀ k, g ∣ a k := by
    intro k; fin_cases k
    · exact Nat.gcd_dvd_left _ _
    · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
    · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
  have hgn : g ∣ n := by
    rw [← hsum, Fin.sum_univ_three]; exact dvd_add (dvd_add (hga 0) (hga 1)) (hga 2)
  obtain ⟨n', hn'⟩ := hgn
  have hn'pos : 0 < n' := by
    rcases Nat.eq_zero_or_pos n' with h0 | h0
    · rw [h0] at hn'; omega
    · exact h0
  choose c hc using hga
  have hdiv : ∀ k, a k / g = c k := fun k => by rw [hc k]; exact Nat.mul_div_cancel_left (c k) hgpos
  refine ⟨n', fun k => a k / g, hn'pos, ?_, ?_⟩
  · intro k
    show D.model.angleAt k = ((a k / g : ℕ) : ℝ) * Real.pi / n'
    rw [hdiv k, ha k, hc k, hn']
    have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hgpos.ne'
    push_cast
    field_simp
  · show Nat.gcd (a 0 / g) (Nat.gcd (a 1 / g) (a 2 / g)) = 1
    rw [hdiv 0, hdiv 1, hdiv 2]
    have h1 : g = g * Nat.gcd (c 0) (Nat.gcd (c 1) (c 2)) := by
      conv_lhs => rw [hg, hc 0, hc 1, hc 2]
      rw [Nat.gcd_mul_left, Nat.gcd_mul_left]
    have : g * 1 = g * Nat.gcd (c 0) (Nat.gcd (c 1) (c 2)) := by rw [mul_one]; exact h1
    exact (Nat.eq_of_mul_eq_mul_left hgpos this).symm

/-- **Total classification, rational tile.** -/
theorem classify_rational (D : CongruentDissection N) (h : CommAngles D.model) :
    SimilarTM D ∨ (∃ k l : Fin 3, l ≠ k ∧ D.model.angleAt k = Real.pi / 2 ∧
        ∃ j₁ j₂ : Fin 3, j₁ ≠ j₂ ∧ D.target.angleAt j₁ = D.model.angleAt l ∧
          D.target.angleAt j₂ = D.model.angleAt l) ∨ ExcPair3 D := by
  obtain ⟨n, a, hn, ha, hg⟩ := exists_primitive_na D h
  exact classify_total D hn a ha hg

theorem comm_of_not_irr (D : CongruentDissection N) (h : ∀ k, ¬ IrrPi (D.model.angleAt k)) : CommAngles D.model := by
  rw [commAngles_iff]
  intro k
  have := h k
  unfold IrrPi at this
  push Not at this
  exact this

/-- **Laczkovich DCG 48 (2012) Thm 3.3, angle part of "only if".** -/
theorem equilateral_classification (D : CongruentDissection N) (hEq : Equilateral D) :
    (∃ α : ℝ, IrrPi α ∧ TileAngles D α (2 * Real.pi / 3 - α) (Real.pi / 3)) ∨
    (∃ α : ℝ, IrrPi α ∧ TileAngles D α (Real.pi / 3 - α) (2 * Real.pi / 3)) ∨
    TileAngles D (Real.pi / 3) (Real.pi / 3) (Real.pi / 3) ∨
    TileAngles D (Real.pi / 6) (Real.pi / 6) (2 * Real.pi / 3) ∨
    TileAngles D (Real.pi / 6) (Real.pi / 3) (Real.pi / 2) := by
  have hpi := Real.pi_pos
  by_cases hirr : ∃ k, IrrPi (D.model.angleAt k)
  · rcases equilateral_tile_irr D hEq hirr with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · push Not at hirr
    rcases classify_rational D (comm_of_not_irr D hirr) with hs | ⟨k, l, hlk, hk, j₁, j₂, hj, h1, h2⟩ | hx
    · -- similar to the equilateral target: the tile is equilateral
      right; right; left
      obtain ⟨μ, τ, h⟩ := hs
      have hall : ∀ m, D.model.angleAt m = Real.pi / 3 := by
        intro m
        obtain ⟨j, rfl⟩ := τ.surjective m
        rw [← (h j).1, hEq j]
      exact ⟨Equiv.refl _, hall _, hall _, hall _⟩
    · right; right; right; right
      have hl : D.model.angleAt l = Real.pi / 3 := by rw [← h1, hEq]
      have := tile_of_two D k l hlk.symm (Real.pi / 2) (Real.pi / 3) hk hl
      have t1 : TileAngles D (Real.pi - Real.pi / 2 - Real.pi / 3) (Real.pi / 3) (Real.pi / 2) :=
        this.swap23.swap.swap23
      exact t1.cast (by ring) rfl rfl
    · right; right
      rcases hx with ⟨hT, hG⟩ | ⟨hT, hG⟩ | ⟨hT, hG⟩
      · right; left
        exact hT.cast (by ring) (by ring) (by ring)
      · exfalso
        have := tgt_eq_third hEq hG
        linarith [this.1]
      · right; right
        exact hT.cast (by ring) (by ring) (by ring)

/-- **Table 3 (isosceles non-equilateral target), both halves in one statement** (angle part). -/
theorem table3_full (D : CongruentDissection N)
    (hiso : ∃ i j : Fin 3, i ≠ j ∧ D.target.angleAt i = D.target.angleAt j) (hne : ¬ Equilateral D) :
    ((∃ k, IrrPi (D.model.angleAt k)) →
      (SimilarTM D ∨
      (∃ α β : ℝ, IrrPi α ∧ TileAngles D α β (Real.pi / 2) ∧ TgtAngles D β β (2 * α)) ∨
      (∃ α β : ℝ, IrrPi α ∧ TileAngles D α β (2 * α) ∧ TgtAngles D α α (Real.pi - 2 * α)) ∨
      (∃ α β : ℝ, IrrPi α ∧ TileAngles D α β (2 * Real.pi / 3) ∧
        TgtAngles D α α (Real.pi - 2 * α)) ∨
      (∃ α β : ℝ, IrrPi α ∧ 3 * α + 2 * β = Real.pi ∧ TileAngles D α β (2 * α + β) ∧
        TgtAngles D α α (α + 2 * β)) ∨
      (∃ α β : ℝ, IrrPi α ∧ 3 * α + 2 * β = Real.pi ∧ TileAngles D α β (2 * α + β) ∧
        TgtAngles D β β (3 * α)) ∨
      (∃ α β : ℝ, IrrPi α ∧ 3 * α + 2 * β = Real.pi ∧ TileAngles D α β (2 * α + β) ∧
        TgtAngles D (α + β) (α + β) α))) ∧
    ((∀ k, ¬ IrrPi (D.model.angleAt k)) →
      (SimilarTM D ∨ ∃ α β : ℝ, TileAngles D α β (Real.pi / 2) ∧ TgtAngles D β β (2 * α))) := by
  refine ⟨fun h => table3_irr D hiso hne h, fun h => ?_⟩
  obtain ⟨n, a, hn, ha, hg⟩ := exists_primitive_na D (comm_of_not_irr D h)
  exact table3_comm_total D hne hn a ha hg

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.classify_rational
#print axioms Erdos634.Draft.LaczFormal.equilateral_classification
#print axioms Erdos634.Draft.LaczFormal.table3_full
