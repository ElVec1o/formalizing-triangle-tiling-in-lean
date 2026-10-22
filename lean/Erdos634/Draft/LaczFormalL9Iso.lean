-- Draft/LaczFormalL9Iso.lean -- L9, isosceles RIGHT target: Laczkovich 1995 Thm 5.3 (p. 93) / Beeson-Rosu Thm 4 say that a tiling of the isosceles
-- right triangle by congruent tiles with rational angles is a reptiling.  In the generic region (`LaczFormalL9Gen`) this is the small step
-- "HalfIso => similar": if the target has angles (pi/4, pi/4, pi/2) and the tile is right with the target's equal angles equal to an acute
-- tile angle, then the tile is (pi/2, pi/4, pi/4), hence similar.  UNAUDITED.  Credit: Laczkovich (1995), Beeson-Rosu.
import Erdos634.Draft.LaczFormalL9Gen
import Erdos634.Draft.LaczFormalL9Wit

open scoped Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional Erdos634.Draft.LemmaCFinal

namespace Erdos634.Draft.LaczFormal

/-- **L9, isosceles right target, generic region.** -/
theorem l9_generic_right_iso {N : ℕ} (D : CongruentDissection N) {n : ℕ} (hn : 0 < n)
    (a : Fin 3 → ℕ) (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hpn : p ∣ n)
    (hT : TgtAngles D (Real.pi / 4) (Real.pi / 4) (Real.pi / 2)) : SimilarTM D := by
  rcases l9_generic D hn a ha hgcd hp hp7 hpn with h | ⟨k, l, hlk, hk, j₁, j₂, hj, h1, h2⟩
  · exact h
  have hpi := Real.pi_pos
  obtain ⟨σ, t0, t1, t2⟩ := hT
  have fin3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  obtain ⟨a1, rfl⟩ := σ.surjective j₁
  obtain ⟨b1, rfl⟩ := σ.surjective j₂
  have hab : a1 ≠ b1 := fun e => hj (by rw [e])
  have hl : D.model.angleAt l = Real.pi / 4 := by
    rcases fin3 a1 with rfl | rfl | rfl <;> rcases fin3 b1 with rfl | rfl | rfl <;>
      first | exact absurd rfl hab | (rw [← h1]; assumption) | (rw [← h2]; assumption) |
        (exfalso; linarith)
  obtain ⟨m, hkm, hlm⟩ := (by decide : ∀ p q : Fin 3, p ≠ q → ∃ r, p ≠ r ∧ q ≠ r) k l hlk.symm
  have h3 : D.model.angleAt k + D.model.angleAt l + D.model.angleAt m
      = D.model.angleAt 0 + D.model.angleAt 1 + D.model.angleAt 2 :=
    sum3 (fun x => D.model.angleAt x) k l m hlk.symm hkm hlm
  have hs := angleAt_sum D.model
  have hm : D.model.angleAt m = Real.pi / 4 := by rw [hk, hl] at h3; linarith
  refine sim_of_TA D l m k hlm hlk hkm.symm ⟨σ, ?_, ?_, ?_⟩
  · show D.target.angleAt (σ 0) = _
    rw [t0, hl]
  · show D.target.angleAt (σ 1) = _
    rw [t1, hm]
  · show D.target.angleAt (σ 2) = _
    rw [t2, hk]

/-- **Consequence (the non-vacuous form).**  `l9_generic_right_iso` says the tile would be similar to the target, whose angles have denominator 4;
so no tile of the generic region (exact denominator divisible by a prime `>= 7`) dissects the isosceles right triangle at all. -/
theorem no_generic_tile_for_right_iso {N : ℕ} (D : CongruentDissection N) {n : ℕ} (hn : 0 < n)
    (a : Fin 3 → ℕ) (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hpn : p ∣ n)
    (hT : TgtAngles D (Real.pi / 4) (Real.pi / 4) (Real.pi / 2)) : False := by
  have hpi := Real.pi_pos
  have hsim := l9_generic_right_iso D hn a ha hgcd hp hp7 hpn hT
  obtain ⟨μ, τ, h⟩ := hsim
  obtain ⟨σ, t0, t1, t2⟩ := hT
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  -- every model angle is pi/4 or pi/2, i.e. 4 a_k = n or 2 a_k = n
  have key : ∀ k, 4 * a k = n ∨ 2 * a k = n := by
    intro k
    obtain ⟨j, rfl⟩ := τ.surjective k
    have hj := (h j).1
    obtain ⟨i, rfl⟩ := σ.surjective j
    have hv : D.target.angleAt (σ i) = Real.pi / 4 ∨ D.target.angleAt (σ i) = Real.pi / 2 := by
      have fin3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
      rcases fin3 i with rfl | rfl | rfl
      · exact Or.inl t0
      · exact Or.inl t1
      · exact Or.inr t2
    have hv' : D.model.angleAt (τ (σ i)) = Real.pi / 4 ∨ D.model.angleAt (τ (σ i)) = Real.pi / 2 := by
      rw [← hj]; exact hv
    have hk := ha (τ (σ i))
    rcases hv' with hv | hv
    · left
      rw [hv] at hk
      have : ((4 * a (τ (σ i)) : ℕ) : ℝ) = n := by push_cast; field_simp at hk; nlinarith
      exact_mod_cast this
    · right
      rw [hv] at hk
      have : ((2 * a (τ (σ i)) : ℕ) : ℝ) = n := by push_cast; field_simp at hk; nlinarith
      exact_mod_cast this
  have hd : ∀ k, n ∣ 4 * a k := by
    intro k
    rcases key k with h | h
    · rw [h]
    · exact ⟨2, by omega⟩
  have hdiv : n ∣ 4 := by
    have := Nat.dvd_gcd (hd 0) (Nat.dvd_gcd (hd 1) (hd 2))
    rwa [Nat.gcd_mul_left, Nat.gcd_mul_left, hgcd, mul_one] at this
  have := Nat.le_of_dvd (by norm_num) (hpn.trans hdiv)
  omega

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.l9_generic_right_iso
#print axioms Erdos634.Draft.LaczFormal.no_generic_tile_for_right_iso
