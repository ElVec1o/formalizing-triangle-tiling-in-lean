-- Draft/LaczFormalL6Rat.lean -- atom L6, rational cases (i)-(iii): the tile counts N for an EQUILATERAL
-- target when the tile is one of Laczkovich's three commensurable shapes (Beeson-Rosu arXiv 2607.23453,
-- proof of Thm 3, list (i)-(iii), "The possible N in the first three cases are known").
--   (i)   tile (pi/3,pi/3,pi/3):     N = m^2
--   (ii)  tile (pi/6,pi/6,2pi/3):    N = m^2 or N = 3 q^2
--   (iii) tile (pi/6,pi/3,pi/2):     N = 2 n^2 or N = 6 n^2
-- NOTE (ii): Beeson-Rosu's printed text for (ii) is garbled in the extracted PDF; the formula here is derived
-- independently from the area identity (`CaseA.LemmaV.star`, sine form, any N) and irrationality of sqrt 3;
-- N = 3 (equilateral cut from its centre) is the instance q = 1.
-- It does NOT classify which tiles can occur (that is Laczkovich's theorem, atom L9).  UNAUDITED.
import Erdos634.Draft.LaczFormalBase
import Erdos634.Draft.CaseALemmaVDissection

open scoped Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional

namespace Erdos634.Draft.LaczFormal

/-- Area identity of a dissection of an equilateral triangle by a tile with angles `x,y,z`
(in the order of `σ`): `N · sin x sin y sin z · sin(π/3) = X² sin²(π/3)`, `X = Σ aᵢ sin(angleᵢ)`. -/
theorem star_equilateral {N : ℕ} (D : CongruentDissection N) (hEq : Equilateral D) {x y z : ℝ}
    (h : TileAngles D x y z) :
    ∃ a b c : ℕ, (N : ℝ) * (Real.sin x * Real.sin y * Real.sin z) * (Real.sqrt 3 / 2)
      = ((a : ℝ) * Real.sin x + b * Real.sin y + c * Real.sin z) ^ 2 *
        (Real.sqrt 3 / 2 * (Real.sqrt 3 / 2)) := by
  obtain ⟨σ, h0, h1, h2⟩ := h
  obtain ⟨c, hc⟩ := Erdos634.Geometry.CaseA.LemmaV.star D
  have s3 : ∀ k, Real.sin (D.target.angleAt k) = Real.sqrt 3 / 2 := by
    intro k; rw [hEq k, Real.sin_pi_div_three]
  rw [s3, s3, s3] at hc
  have hp : Real.sin (D.model.angleAt 0) * Real.sin (D.model.angleAt 1) *
      Real.sin (D.model.angleAt 2) = Real.sin x * Real.sin y * Real.sin z := by
    have := Equiv.prod_comp σ (fun k => Real.sin (D.model.angleAt k))
    simp only [Fin.prod_univ_three] at this
    rw [← h0, ← h1, ← h2, ← this]
  have hs : ∑ k, (c k : ℝ) * Real.sin (D.model.angleAt k) =
      (c (σ 0) : ℝ) * Real.sin x + (c (σ 1)) * Real.sin y + (c (σ 2)) * Real.sin z := by
    have := Equiv.sum_comp σ (fun k => (c k : ℝ) * Real.sin (D.model.angleAt k))
    simp only [Fin.sum_univ_three] at this
    rw [← h0, ← h1, ← h2, Fin.sum_univ_three]; exact this.symm
  refine ⟨c (σ 0), c (σ 1), c (σ 2), ?_⟩
  rw [hs] at hc
  rw [← hp]
  linear_combination hc

/-- `N = (m + q√3)²` forces `m = 0` or `q = 0`. -/
theorem sqrt3_split {M m q : ℕ} (h : (M : ℝ) = ((m : ℝ) + q * Real.sqrt 3) ^ 2) :
    (m = 0 ∧ M = 3 * q ^ 2) ∨ (q = 0 ∧ M = m ^ 2) := by
  have hirr : Irrational (Real.sqrt 3) := by
    have := Nat.prime_three.irrational_sqrt
    simpa using this
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have key : (M : ℝ) = (m : ℝ) ^ 2 + 3 * (q : ℝ) ^ 2 + 2 * m * q * Real.sqrt 3 := by
    rw [h]; linear_combination (q : ℝ) ^ 2 * h3
  by_cases hmq : (m : ℝ) * q = 0
  · rcases mul_eq_zero.mp hmq with hm | hq
    · left
      have hm' : m = 0 := by exact_mod_cast hm
      subst hm'
      refine ⟨rfl, ?_⟩
      have : (M : ℝ) = 3 * (q : ℝ) ^ 2 := by rw [key]; simp
      exact_mod_cast this
    · right
      have hq' : q = 0 := by exact_mod_cast hq
      subst hq'
      refine ⟨rfl, ?_⟩
      have : (M : ℝ) = (m : ℝ) ^ 2 := by rw [key]; simp
      exact_mod_cast this
  · exfalso
    apply hirr
    refine ⟨(M - m ^ 2 - 3 * q ^ 2) / (2 * m * q), ?_⟩
    push_cast
    have hne : (2 * (m : ℝ) * q) ≠ 0 := by
      have : (2 : ℝ) ≠ 0 := by norm_num
      rw [mul_assoc]; exact mul_ne_zero this hmq
    rw [div_eq_iff hne]
    linear_combination key

/-- **(i)** Equilateral target, equilateral tile: `N` is a square. -/
theorem equilateral_tile_i {N : ℕ} (D : CongruentDissection N) (hEq : Equilateral D)
    (h : TileAngles D (Real.pi / 3) (Real.pi / 3) (Real.pi / 3)) : ∃ m : ℕ, N = m ^ 2 := by
  obtain ⟨a, b, c, hst⟩ := star_equilateral D hEq h
  have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hsp : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [Real.sin_pi_div_three] at hst
  have e : (N : ℝ) = ((a + b + c : ℕ) : ℝ) ^ 2 := by
    have hne : Real.sqrt 3 * Real.sqrt 3 * (Real.sqrt 3 * Real.sqrt 3) / 16 ≠ 0 := by positivity
    apply mul_right_cancel₀ hne
    push_cast
    linear_combination hst
  exact ⟨a + b + c, by exact_mod_cast e⟩

/-- **(ii)** Equilateral target, tile `(π/6, π/6, 2π/3)`: `N = m²` or `N = 3q²`. -/
theorem equilateral_tile_ii {N : ℕ} (D : CongruentDissection N) (hEq : Equilateral D)
    (h : TileAngles D (Real.pi / 6) (Real.pi / 6) (2 * Real.pi / 3)) :
    (∃ m : ℕ, N = m ^ 2) ∨ (∃ q : ℕ, N = 3 * q ^ 2) := by
  obtain ⟨a, b, c, hst⟩ := star_equilateral D hEq h
  have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hsp : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h23 : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub,
      Real.sin_pi_div_three]
  rw [h23, Real.sin_pi_div_six] at hst
  have e : (N : ℝ) = (((a + b : ℕ) : ℝ) + c * Real.sqrt 3) ^ 2 := by
    have hne : Real.sqrt 3 * Real.sqrt 3 / 16 ≠ 0 := by positivity
    apply mul_right_cancel₀ hne
    push_cast
    linear_combination hst
  rcases sqrt3_split e with ⟨-, h1⟩ | ⟨-, h1⟩
  · exact Or.inr ⟨c, h1⟩
  · exact Or.inl ⟨a + b, h1⟩

/-- **(iii)** Equilateral target, tile `(π/6, π/3, π/2)`: `N = 2n²` or `N = 6n²`. -/
theorem equilateral_tile_iii {N : ℕ} (D : CongruentDissection N) (hEq : Equilateral D)
    (h : TileAngles D (Real.pi / 6) (Real.pi / 3) (Real.pi / 2)) :
    (∃ n : ℕ, N = 2 * n ^ 2) ∨ (∃ n : ℕ, N = 6 * n ^ 2) := by
  obtain ⟨a, b, c, hst⟩ := star_equilateral D hEq h
  have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hsp : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [Real.sin_pi_div_two, Real.sin_pi_div_three, Real.sin_pi_div_six] at hst
  have e : ((2 * N : ℕ) : ℝ) = (((a + 2 * c : ℕ) : ℝ) + b * Real.sqrt 3) ^ 2 := by
    have hne : Real.sqrt 3 * Real.sqrt 3 / 16 ≠ 0 := by positivity
    apply mul_right_cancel₀ hne
    push_cast
    linear_combination hst
  rcases sqrt3_split e with ⟨-, h1⟩ | ⟨-, h1⟩
  · -- 2N = 3 b², so b is even
    right
    have h2 : 2 ∣ 3 * b ^ 2 := ⟨N, h1.symm⟩
    have h2' : 2 ∣ b := by
      have : 2 ∣ b ^ 2 := by omega
      exact Nat.Prime.dvd_of_dvd_pow Nat.prime_two this
    obtain ⟨n, hn⟩ := h2'
    exact ⟨n, by rw [hn] at h1; nlinarith⟩
  · -- 2N = u², so u is even
    left
    have h2 : 2 ∣ (a + 2 * c) ^ 2 := ⟨N, h1.symm⟩
    have h2' : 2 ∣ a + 2 * c := (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2)
    obtain ⟨n, hn⟩ := h2'
    exact ⟨n, by rw [hn] at h1; nlinarith⟩

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.star_equilateral
#print axioms Erdos634.Draft.LaczFormal.sqrt3_split
#print axioms Erdos634.Draft.LaczFormal.equilateral_tile_i
#print axioms Erdos634.Draft.LaczFormal.equilateral_tile_ii
#print axioms Erdos634.Draft.LaczFormal.equilateral_tile_iii
