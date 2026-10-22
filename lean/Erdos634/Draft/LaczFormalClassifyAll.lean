-- Draft/LaczFormalClassifyAll.lean -- CLASSIFICATION THEOREM for commensurable-angle tiles (Laczkovich 1995 Thm 5.1/5.3, congruent case), for the covered denominators n:
--   `Covered n` := n has a prime factor >= 7 (`l9_generic`), or n is one of the 16 certified smooth n (`l9_smooth`), or n is one of the exceptional
--   n = 6, 8, 10, 12, 18, 24, 30, 60 (`R(a) = R0(a)` off the 27 exceptional triples by `allCertEx`; on them the table-driven `classify_*`).
--   Conclusion: the target is SIMILAR to the tile, or the tile is right-angled and the target is isosceles with an acute tile angle as base angle (`l9_generic` shape),
--   or `ExcPair D`: one of six (tile, target) shapes: three valid ones at n = 6 and three tiles at n = 12, 30 with an equilateral target NOT excluded here.
-- UNAUDITED.  Credit: Laczkovich (1995, 2012, 2020), Beeson-Rosu, Beeson.
import Erdos634.Draft.LaczFormalClassify
import Erdos634.Draft.LaczFormalR2Ex
import Erdos634.Draft.LaczFormalR2
import Erdos634.Draft.LaczFormalR2Ext

open scoped BigOperators Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional Erdos634.LemmaS Erdos634.CaseA.R0c
open Erdos634.Geometry.CaseA.LemmaV (nat_bounds angle_pos angle_lt_pi)

namespace Erdos634.Draft.LaczFormal

variable {N : ℕ}

theorem TileAngles.reorder {D : CongruentDissection N} {x y z : ℝ} (h : TileAngles D x y z)
    (p : Equiv.Perm (Fin 3)) :
    TileAngles D ((![x, y, z] : Fin 3 → ℝ) (p 0)) ((![x, y, z] : Fin 3 → ℝ) (p 1))
      ((![x, y, z] : Fin 3 → ℝ) (p 2)) := by
  obtain ⟨σ, h0, h1, h2⟩ := h
  have : ∀ k, D.model.angleAt (σ k) = (![x, y, z] : Fin 3 → ℝ) k := by
    intro k; fin_cases k <;> simp [h0, h1, h2]
  exact ⟨p.trans σ, this (p 0), this (p 1), this (p 2)⟩

/-- A target with the tile's own angle triple is similar to the tile. -/
theorem similar_of_same_angles (D : CongruentDissection N) {x y z : ℝ} (hM : TileAngles D x y z)
    (hT : TgtAngles D x y z) : SimilarTM D := by
  obtain ⟨σ, m0, m1, m2⟩ := hM
  obtain ⟨τ, t0, t1, t2⟩ := hT
  have hm : ∀ k, D.model.angleAt (σ k) = (![x, y, z] : Fin 3 → ℝ) k := by
    intro k; fin_cases k <;> simp [m0, m1, m2]
  have ht : ∀ k, D.target.angleAt (τ k) = (![x, y, z] : Fin 3 → ℝ) k := by
    intro k; fin_cases k <;> simp [t0, t1, t2]
  have hang : ∀ j, D.target.angleAt j = D.model.angleAt ((τ.symm.trans σ) j) := by
    intro j
    simp only [Equiv.trans_apply]
    rw [hm, ← ht, Equiv.apply_symm_apply]
  set μ := A1Field.circD D.target / A1Field.circD D.model
  have hcm := (A1Field.circD_pos D.model).ne'
  refine ⟨μ, τ.symm.trans σ, fun j => ⟨hang j, ?_⟩⟩
  rw [A1Field.oppLen_eq D.target j, A1Field.oppLen_eq D.model ((τ.symm.trans σ) j), hang j]
  simp only [μ]; field_simp

/-- The six exceptional (tile, target) shapes not excluded: three valid tilings at `n = 6` (equilateral target for the `(π/6,π/6,2π/3)` and `(π/6,π/3,π/2)` tiles,
the `2π/3`-isosceles target for the 30-60-90 tile) and equilateral targets for the tiles `(π/12,π/3,7π/12)`, `(π/30,π/3,19π/30)`, `(7π/30,π/3,13π/30)` (open here). -/
def ExcPair (D : CongruentDissection N) : Prop :=
  (TileAngles D (1 * Real.pi / 6) (1 * Real.pi / 6) (4 * Real.pi / 6) ∧
    TgtAngles D (2 * Real.pi / 6) (2 * Real.pi / 6) (2 * Real.pi / 6))
  ∨ (TileAngles D (1 * Real.pi / 6) (2 * Real.pi / 6) (3 * Real.pi / 6) ∧
    TgtAngles D (1 * Real.pi / 6) (1 * Real.pi / 6) (4 * Real.pi / 6))
  ∨ (TileAngles D (1 * Real.pi / 6) (2 * Real.pi / 6) (3 * Real.pi / 6) ∧
    TgtAngles D (2 * Real.pi / 6) (2 * Real.pi / 6) (2 * Real.pi / 6))
  ∨ (TileAngles D (1 * Real.pi / 12) (4 * Real.pi / 12) (7 * Real.pi / 12) ∧
    TgtAngles D (4 * Real.pi / 12) (4 * Real.pi / 12) (4 * Real.pi / 12))
  ∨ (TileAngles D (1 * Real.pi / 30) (10 * Real.pi / 30) (19 * Real.pi / 30) ∧
    TgtAngles D (10 * Real.pi / 30) (10 * Real.pi / 30) (10 * Real.pi / 30))
  ∨ (TileAngles D (7 * Real.pi / 30) (10 * Real.pi / 30) (13 * Real.pi / 30) ∧
    TgtAngles D (10 * Real.pi / 30) (10 * Real.pi / 30) (10 * Real.pi / 30))

/-- Covered denominators. -/
def Covered (n : ℕ) : Prop := (∃ p : ℕ, p.Prime ∧ 7 ≤ p ∧ p ∣ n) ∨ CertN2 n ∨ n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 8 ∨ n = 10 ∨ n = 12 ∨ n = 18 ∨ n = 24 ∨ n = 30 ∨ n = 60

theorem exc_dispatch_3 (D : CongruentDissection N) (hn : 0 < 3) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / (3 : ℕ))
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) :
    SimilarTM D ∨ (∃ k l : Fin 3, l ≠ k ∧ D.model.angleAt k = Real.pi / 2 ∧
        ∃ j₁ j₂ : Fin 3, j₁ ≠ j₂ ∧ D.target.angleAt j₁ = D.model.angleAt l ∧
          D.target.angleAt j₂ = D.model.angleAt l) ∨ ExcPair D := by
  have ha1 : ∀ i, 0 < a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  by_cases hex : excl_3.contains (a 0, a 1, a 2) = true
  · have hmem : (a 0, a 1, a 2) ∈ excl_3 := by simpa using hex
    have hM0 : TileAngles D (a 0 * Real.pi / 3) (a 1 * Real.pi / 3) (a 2 * Real.pi / 3) :=
      ⟨Equiv.refl _, by simpa using ha 0, by simpa using ha 1, by simpa using ha 2⟩
    simp only [excl_3, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
    rcases hmem with ⟨e0, e1, e2⟩
    · have hM' : TileAngles D (1 * Real.pi / 3) (1 * Real.pi / 3) (1 * Real.pi / 3) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.refl _)
      obtain ⟨u, hu, hT⟩ := classify_3_1_1_1 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
  · exfalso
    have hsum := sum_of_angles hn ha
    rw [Fin.sum_univ_three] at hsum
    have h0 := ha1 0
    have h1 := ha1 1
    have h2 := ha1 2
    simp only [excl_3, List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq, Prod.mk.injEq] at hex
    simp at hex
    omega

theorem exc_dispatch_4 (D : CongruentDissection N) (hn : 0 < 4) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / (4 : ℕ))
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) :
    SimilarTM D ∨ (∃ k l : Fin 3, l ≠ k ∧ D.model.angleAt k = Real.pi / 2 ∧
        ∃ j₁ j₂ : Fin 3, j₁ ≠ j₂ ∧ D.target.angleAt j₁ = D.model.angleAt l ∧
          D.target.angleAt j₂ = D.model.angleAt l) ∨ ExcPair D := by
  have ha1 : ∀ i, 0 < a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  by_cases hex : excl_4.contains (a 0, a 1, a 2) = true
  · have hmem : (a 0, a 1, a 2) ∈ excl_4 := by simpa using hex
    have hM0 : TileAngles D (a 0 * Real.pi / 4) (a 1 * Real.pi / 4) (a 2 * Real.pi / 4) :=
      ⟨Equiv.refl _, by simpa using ha 0, by simpa using ha 1, by simpa using ha 2⟩
    simp only [excl_4, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
    rcases hmem with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩
    · have hM' : TileAngles D (1 * Real.pi / 4) (1 * Real.pi / 4) (2 * Real.pi / 4) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.refl _)
      obtain ⟨u, hu, hT⟩ := classify_4_1_1_2 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 4) (1 * Real.pi / 4) (2 * Real.pi / 4) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 1 2)
      obtain ⟨u, hu, hT⟩ := classify_4_1_1_2 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 4) (1 * Real.pi / 4) (2 * Real.pi / 4) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 2)
      obtain ⟨u, hu, hT⟩ := classify_4_1_1_2 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
  · exfalso
    have hsum := sum_of_angles hn ha
    rw [Fin.sum_univ_three] at hsum
    have h0 := ha1 0
    have h1 := ha1 1
    have h2 := ha1 2
    simp only [excl_4, List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq, Prod.mk.injEq] at hex
    simp at hex
    omega

theorem exc_dispatch_6 (D : CongruentDissection N) (hn : 0 < 6) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / (6 : ℕ))
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) :
    SimilarTM D ∨ (∃ k l : Fin 3, l ≠ k ∧ D.model.angleAt k = Real.pi / 2 ∧
        ∃ j₁ j₂ : Fin 3, j₁ ≠ j₂ ∧ D.target.angleAt j₁ = D.model.angleAt l ∧
          D.target.angleAt j₂ = D.model.angleAt l) ∨ ExcPair D := by
  have ha1 : ∀ i, 0 < a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  by_cases hex : excl_6.contains (a 0, a 1, a 2) = true
  · have hmem : (a 0, a 1, a 2) ∈ excl_6 := by simpa using hex
    have hM0 : TileAngles D (a 0 * Real.pi / 6) (a 1 * Real.pi / 6) (a 2 * Real.pi / 6) :=
      ⟨Equiv.refl _, by simpa using ha 0, by simpa using ha 1, by simpa using ha 2⟩
    simp only [excl_6, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
    rcases hmem with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩
    · have hM' : TileAngles D (1 * Real.pi / 6) (1 * Real.pi / 6) (4 * Real.pi / 6) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.refl _)
      obtain ⟨u, hu, hT⟩ := classify_6_1_1_4 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
      · right; right
        have hT' : TgtAngles D (2 * Real.pi / 6) (2 * Real.pi / 6) (2 * Real.pi / 6) := by simpa using hT
        unfold ExcPair
        exact Or.inl ⟨hM', hT'⟩
    · have hM' : TileAngles D (1 * Real.pi / 6) (1 * Real.pi / 6) (4 * Real.pi / 6) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 1 2)
      obtain ⟨u, hu, hT⟩ := classify_6_1_1_4 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
      · right; right
        have hT' : TgtAngles D (2 * Real.pi / 6) (2 * Real.pi / 6) (2 * Real.pi / 6) := by simpa using hT
        unfold ExcPair
        exact Or.inl ⟨hM', hT'⟩
    · have hM' : TileAngles D (1 * Real.pi / 6) (1 * Real.pi / 6) (4 * Real.pi / 6) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 2)
      obtain ⟨u, hu, hT⟩ := classify_6_1_1_4 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
      · right; right
        have hT' : TgtAngles D (2 * Real.pi / 6) (2 * Real.pi / 6) (2 * Real.pi / 6) := by simpa using hT
        unfold ExcPair
        exact Or.inl ⟨hM', hT'⟩
    · have hM' : TileAngles D (1 * Real.pi / 6) (2 * Real.pi / 6) (3 * Real.pi / 6) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.refl _)
      obtain ⟨u, hu, hT⟩ := classify_6_1_2_3 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
      · right; right
        have hT' : TgtAngles D (1 * Real.pi / 6) (1 * Real.pi / 6) (4 * Real.pi / 6) := by simpa using hT
        unfold ExcPair
        exact Or.inr (Or.inl ⟨hM', hT'⟩)
      · right; right
        have hT' : TgtAngles D (2 * Real.pi / 6) (2 * Real.pi / 6) (2 * Real.pi / 6) := by simpa using hT
        unfold ExcPair
        exact Or.inr (Or.inr (Or.inl ⟨hM', hT'⟩))
    · have hM' : TileAngles D (1 * Real.pi / 6) (2 * Real.pi / 6) (3 * Real.pi / 6) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 1 2)
      obtain ⟨u, hu, hT⟩ := classify_6_1_2_3 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
      · right; right
        have hT' : TgtAngles D (1 * Real.pi / 6) (1 * Real.pi / 6) (4 * Real.pi / 6) := by simpa using hT
        unfold ExcPair
        exact Or.inr (Or.inl ⟨hM', hT'⟩)
      · right; right
        have hT' : TgtAngles D (2 * Real.pi / 6) (2 * Real.pi / 6) (2 * Real.pi / 6) := by simpa using hT
        unfold ExcPair
        exact Or.inr (Or.inr (Or.inl ⟨hM', hT'⟩))
    · have hM' : TileAngles D (1 * Real.pi / 6) (2 * Real.pi / 6) (3 * Real.pi / 6) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 1)
      obtain ⟨u, hu, hT⟩ := classify_6_1_2_3 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
      · right; right
        have hT' : TgtAngles D (1 * Real.pi / 6) (1 * Real.pi / 6) (4 * Real.pi / 6) := by simpa using hT
        unfold ExcPair
        exact Or.inr (Or.inl ⟨hM', hT'⟩)
      · right; right
        have hT' : TgtAngles D (2 * Real.pi / 6) (2 * Real.pi / 6) (2 * Real.pi / 6) := by simpa using hT
        unfold ExcPair
        exact Or.inr (Or.inr (Or.inl ⟨hM', hT'⟩))
    · have hM' : TileAngles D (1 * Real.pi / 6) (2 * Real.pi / 6) (3 * Real.pi / 6) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 0 1).trans (Equiv.swap 1 2))
      obtain ⟨u, hu, hT⟩ := classify_6_1_2_3 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
      · right; right
        have hT' : TgtAngles D (1 * Real.pi / 6) (1 * Real.pi / 6) (4 * Real.pi / 6) := by simpa using hT
        unfold ExcPair
        exact Or.inr (Or.inl ⟨hM', hT'⟩)
      · right; right
        have hT' : TgtAngles D (2 * Real.pi / 6) (2 * Real.pi / 6) (2 * Real.pi / 6) := by simpa using hT
        unfold ExcPair
        exact Or.inr (Or.inr (Or.inl ⟨hM', hT'⟩))
    · have hM' : TileAngles D (1 * Real.pi / 6) (2 * Real.pi / 6) (3 * Real.pi / 6) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 1 2).trans (Equiv.swap 0 1))
      obtain ⟨u, hu, hT⟩ := classify_6_1_2_3 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
      · right; right
        have hT' : TgtAngles D (1 * Real.pi / 6) (1 * Real.pi / 6) (4 * Real.pi / 6) := by simpa using hT
        unfold ExcPair
        exact Or.inr (Or.inl ⟨hM', hT'⟩)
      · right; right
        have hT' : TgtAngles D (2 * Real.pi / 6) (2 * Real.pi / 6) (2 * Real.pi / 6) := by simpa using hT
        unfold ExcPair
        exact Or.inr (Or.inr (Or.inl ⟨hM', hT'⟩))
    · have hM' : TileAngles D (1 * Real.pi / 6) (2 * Real.pi / 6) (3 * Real.pi / 6) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 2)
      obtain ⟨u, hu, hT⟩ := classify_6_1_2_3 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
      · right; right
        have hT' : TgtAngles D (1 * Real.pi / 6) (1 * Real.pi / 6) (4 * Real.pi / 6) := by simpa using hT
        unfold ExcPair
        exact Or.inr (Or.inl ⟨hM', hT'⟩)
      · right; right
        have hT' : TgtAngles D (2 * Real.pi / 6) (2 * Real.pi / 6) (2 * Real.pi / 6) := by simpa using hT
        unfold ExcPair
        exact Or.inr (Or.inr (Or.inl ⟨hM', hT'⟩))
  · have hS := of_allCertEx allCertEx_6 a ha1 (sum_of_angles hn ha) hgcd (by simpa using hex)
    rcases l9_of_S D hn a ha hgcd hS with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

theorem exc_dispatch_8 (D : CongruentDissection N) (hn : 0 < 8) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / (8 : ℕ))
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) :
    SimilarTM D ∨ (∃ k l : Fin 3, l ≠ k ∧ D.model.angleAt k = Real.pi / 2 ∧
        ∃ j₁ j₂ : Fin 3, j₁ ≠ j₂ ∧ D.target.angleAt j₁ = D.model.angleAt l ∧
          D.target.angleAt j₂ = D.model.angleAt l) ∨ ExcPair D := by
  have ha1 : ∀ i, 0 < a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  by_cases hex : excl_8.contains (a 0, a 1, a 2) = true
  · have hmem : (a 0, a 1, a 2) ∈ excl_8 := by simpa using hex
    have hM0 : TileAngles D (a 0 * Real.pi / 8) (a 1 * Real.pi / 8) (a 2 * Real.pi / 8) :=
      ⟨Equiv.refl _, by simpa using ha 0, by simpa using ha 1, by simpa using ha 2⟩
    simp only [excl_8, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
    rcases hmem with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩
    · have hM' : TileAngles D (1 * Real.pi / 8) (2 * Real.pi / 8) (5 * Real.pi / 8) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.refl _)
      obtain ⟨u, hu, hT⟩ := classify_8_1_2_5 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 8) (2 * Real.pi / 8) (5 * Real.pi / 8) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 1 2)
      obtain ⟨u, hu, hT⟩ := classify_8_1_2_5 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 8) (2 * Real.pi / 8) (5 * Real.pi / 8) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 1)
      obtain ⟨u, hu, hT⟩ := classify_8_1_2_5 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 8) (2 * Real.pi / 8) (5 * Real.pi / 8) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 0 1).trans (Equiv.swap 1 2))
      obtain ⟨u, hu, hT⟩ := classify_8_1_2_5 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 8) (2 * Real.pi / 8) (5 * Real.pi / 8) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 1 2).trans (Equiv.swap 0 1))
      obtain ⟨u, hu, hT⟩ := classify_8_1_2_5 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 8) (2 * Real.pi / 8) (5 * Real.pi / 8) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 2)
      obtain ⟨u, hu, hT⟩ := classify_8_1_2_5 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
  · have hS := of_allCertEx allCertEx_8 a ha1 (sum_of_angles hn ha) hgcd (by simpa using hex)
    rcases l9_of_S D hn a ha hgcd hS with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

theorem exc_dispatch_10 (D : CongruentDissection N) (hn : 0 < 10) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / (10 : ℕ))
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) :
    SimilarTM D ∨ (∃ k l : Fin 3, l ≠ k ∧ D.model.angleAt k = Real.pi / 2 ∧
        ∃ j₁ j₂ : Fin 3, j₁ ≠ j₂ ∧ D.target.angleAt j₁ = D.model.angleAt l ∧
          D.target.angleAt j₂ = D.model.angleAt l) ∨ ExcPair D := by
  have ha1 : ∀ i, 0 < a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  by_cases hex : excl_10.contains (a 0, a 1, a 2) = true
  · have hmem : (a 0, a 1, a 2) ∈ excl_10 := by simpa using hex
    have hM0 : TileAngles D (a 0 * Real.pi / 10) (a 1 * Real.pi / 10) (a 2 * Real.pi / 10) :=
      ⟨Equiv.refl _, by simpa using ha 0, by simpa using ha 1, by simpa using ha 2⟩
    simp only [excl_10, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
    rcases hmem with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩
    · have hM' : TileAngles D (1 * Real.pi / 10) (2 * Real.pi / 10) (7 * Real.pi / 10) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.refl _)
      obtain ⟨u, hu, hT⟩ := classify_10_1_2_7 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 10) (2 * Real.pi / 10) (7 * Real.pi / 10) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 1 2)
      obtain ⟨u, hu, hT⟩ := classify_10_1_2_7 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 10) (2 * Real.pi / 10) (7 * Real.pi / 10) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 1)
      obtain ⟨u, hu, hT⟩ := classify_10_1_2_7 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 10) (2 * Real.pi / 10) (7 * Real.pi / 10) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 0 1).trans (Equiv.swap 1 2))
      obtain ⟨u, hu, hT⟩ := classify_10_1_2_7 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 10) (2 * Real.pi / 10) (7 * Real.pi / 10) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 1 2).trans (Equiv.swap 0 1))
      obtain ⟨u, hu, hT⟩ := classify_10_1_2_7 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 10) (2 * Real.pi / 10) (7 * Real.pi / 10) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 2)
      obtain ⟨u, hu, hT⟩ := classify_10_1_2_7 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 10) (3 * Real.pi / 10) (6 * Real.pi / 10) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.refl _)
      obtain ⟨u, hu, hT⟩ := classify_10_1_3_6 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 10) (3 * Real.pi / 10) (6 * Real.pi / 10) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 1 2)
      obtain ⟨u, hu, hT⟩ := classify_10_1_3_6 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 10) (3 * Real.pi / 10) (6 * Real.pi / 10) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 1)
      obtain ⟨u, hu, hT⟩ := classify_10_1_3_6 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 10) (3 * Real.pi / 10) (6 * Real.pi / 10) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 0 1).trans (Equiv.swap 1 2))
      obtain ⟨u, hu, hT⟩ := classify_10_1_3_6 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 10) (3 * Real.pi / 10) (6 * Real.pi / 10) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 1 2).trans (Equiv.swap 0 1))
      obtain ⟨u, hu, hT⟩ := classify_10_1_3_6 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 10) (3 * Real.pi / 10) (6 * Real.pi / 10) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 2)
      obtain ⟨u, hu, hT⟩ := classify_10_1_3_6 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
  · have hS := of_allCertEx allCertEx_10 a ha1 (sum_of_angles hn ha) hgcd (by simpa using hex)
    rcases l9_of_S D hn a ha hgcd hS with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

theorem exc_dispatch_12 (D : CongruentDissection N) (hn : 0 < 12) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / (12 : ℕ))
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) :
    SimilarTM D ∨ (∃ k l : Fin 3, l ≠ k ∧ D.model.angleAt k = Real.pi / 2 ∧
        ∃ j₁ j₂ : Fin 3, j₁ ≠ j₂ ∧ D.target.angleAt j₁ = D.model.angleAt l ∧
          D.target.angleAt j₂ = D.model.angleAt l) ∨ ExcPair D := by
  have ha1 : ∀ i, 0 < a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  by_cases hex : excl_12.contains (a 0, a 1, a 2) = true
  · have hmem : (a 0, a 1, a 2) ∈ excl_12 := by simpa using hex
    have hM0 : TileAngles D (a 0 * Real.pi / 12) (a 1 * Real.pi / 12) (a 2 * Real.pi / 12) :=
      ⟨Equiv.refl _, by simpa using ha 0, by simpa using ha 1, by simpa using ha 2⟩
    simp only [excl_12, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
    rcases hmem with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩
    · have hM' : TileAngles D (1 * Real.pi / 12) (2 * Real.pi / 12) (9 * Real.pi / 12) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.refl _)
      obtain ⟨u, hu, hT⟩ := classify_12_1_2_9 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 12) (2 * Real.pi / 12) (9 * Real.pi / 12) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 1 2)
      obtain ⟨u, hu, hT⟩ := classify_12_1_2_9 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 12) (2 * Real.pi / 12) (9 * Real.pi / 12) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 1)
      obtain ⟨u, hu, hT⟩ := classify_12_1_2_9 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 12) (2 * Real.pi / 12) (9 * Real.pi / 12) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 0 1).trans (Equiv.swap 1 2))
      obtain ⟨u, hu, hT⟩ := classify_12_1_2_9 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 12) (2 * Real.pi / 12) (9 * Real.pi / 12) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 1 2).trans (Equiv.swap 0 1))
      obtain ⟨u, hu, hT⟩ := classify_12_1_2_9 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 12) (2 * Real.pi / 12) (9 * Real.pi / 12) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 2)
      obtain ⟨u, hu, hT⟩ := classify_12_1_2_9 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 12) (3 * Real.pi / 12) (8 * Real.pi / 12) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.refl _)
      obtain ⟨u, hu, hT⟩ := classify_12_1_3_8 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 12) (3 * Real.pi / 12) (8 * Real.pi / 12) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 1 2)
      obtain ⟨u, hu, hT⟩ := classify_12_1_3_8 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 12) (3 * Real.pi / 12) (8 * Real.pi / 12) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 1)
      obtain ⟨u, hu, hT⟩ := classify_12_1_3_8 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 12) (3 * Real.pi / 12) (8 * Real.pi / 12) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 0 1).trans (Equiv.swap 1 2))
      obtain ⟨u, hu, hT⟩ := classify_12_1_3_8 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 12) (3 * Real.pi / 12) (8 * Real.pi / 12) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 1 2).trans (Equiv.swap 0 1))
      obtain ⟨u, hu, hT⟩ := classify_12_1_3_8 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 12) (3 * Real.pi / 12) (8 * Real.pi / 12) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 2)
      obtain ⟨u, hu, hT⟩ := classify_12_1_3_8 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 12) (4 * Real.pi / 12) (7 * Real.pi / 12) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.refl _)
      obtain ⟨u, hu, hT⟩ := classify_12_1_4_7 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
      · right; right
        have hT' : TgtAngles D (4 * Real.pi / 12) (4 * Real.pi / 12) (4 * Real.pi / 12) := by simpa using hT
        unfold ExcPair
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hM', hT'⟩)))
    · have hM' : TileAngles D (1 * Real.pi / 12) (4 * Real.pi / 12) (7 * Real.pi / 12) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 1 2)
      obtain ⟨u, hu, hT⟩ := classify_12_1_4_7 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
      · right; right
        have hT' : TgtAngles D (4 * Real.pi / 12) (4 * Real.pi / 12) (4 * Real.pi / 12) := by simpa using hT
        unfold ExcPair
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hM', hT'⟩)))
    · have hM' : TileAngles D (1 * Real.pi / 12) (4 * Real.pi / 12) (7 * Real.pi / 12) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 1)
      obtain ⟨u, hu, hT⟩ := classify_12_1_4_7 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
      · right; right
        have hT' : TgtAngles D (4 * Real.pi / 12) (4 * Real.pi / 12) (4 * Real.pi / 12) := by simpa using hT
        unfold ExcPair
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hM', hT'⟩)))
    · have hM' : TileAngles D (1 * Real.pi / 12) (4 * Real.pi / 12) (7 * Real.pi / 12) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 0 1).trans (Equiv.swap 1 2))
      obtain ⟨u, hu, hT⟩ := classify_12_1_4_7 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
      · right; right
        have hT' : TgtAngles D (4 * Real.pi / 12) (4 * Real.pi / 12) (4 * Real.pi / 12) := by simpa using hT
        unfold ExcPair
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hM', hT'⟩)))
    · have hM' : TileAngles D (1 * Real.pi / 12) (4 * Real.pi / 12) (7 * Real.pi / 12) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 1 2).trans (Equiv.swap 0 1))
      obtain ⟨u, hu, hT⟩ := classify_12_1_4_7 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
      · right; right
        have hT' : TgtAngles D (4 * Real.pi / 12) (4 * Real.pi / 12) (4 * Real.pi / 12) := by simpa using hT
        unfold ExcPair
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hM', hT'⟩)))
    · have hM' : TileAngles D (1 * Real.pi / 12) (4 * Real.pi / 12) (7 * Real.pi / 12) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 2)
      obtain ⟨u, hu, hT⟩ := classify_12_1_4_7 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
      · right; right
        have hT' : TgtAngles D (4 * Real.pi / 12) (4 * Real.pi / 12) (4 * Real.pi / 12) := by simpa using hT
        unfold ExcPair
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hM', hT'⟩)))
    · have hM' : TileAngles D (2 * Real.pi / 12) (3 * Real.pi / 12) (7 * Real.pi / 12) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.refl _)
      obtain ⟨u, hu, hT⟩ := classify_12_2_3_7 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (2 * Real.pi / 12) (3 * Real.pi / 12) (7 * Real.pi / 12) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 1 2)
      obtain ⟨u, hu, hT⟩ := classify_12_2_3_7 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (2 * Real.pi / 12) (3 * Real.pi / 12) (7 * Real.pi / 12) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 1)
      obtain ⟨u, hu, hT⟩ := classify_12_2_3_7 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (2 * Real.pi / 12) (3 * Real.pi / 12) (7 * Real.pi / 12) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 0 1).trans (Equiv.swap 1 2))
      obtain ⟨u, hu, hT⟩ := classify_12_2_3_7 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (2 * Real.pi / 12) (3 * Real.pi / 12) (7 * Real.pi / 12) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 1 2).trans (Equiv.swap 0 1))
      obtain ⟨u, hu, hT⟩ := classify_12_2_3_7 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (2 * Real.pi / 12) (3 * Real.pi / 12) (7 * Real.pi / 12) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 2)
      obtain ⟨u, hu, hT⟩ := classify_12_2_3_7 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (3 * Real.pi / 12) (4 * Real.pi / 12) (5 * Real.pi / 12) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.refl _)
      obtain ⟨u, hu, hT⟩ := classify_12_3_4_5 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (3 * Real.pi / 12) (4 * Real.pi / 12) (5 * Real.pi / 12) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 1 2)
      obtain ⟨u, hu, hT⟩ := classify_12_3_4_5 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (3 * Real.pi / 12) (4 * Real.pi / 12) (5 * Real.pi / 12) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 1)
      obtain ⟨u, hu, hT⟩ := classify_12_3_4_5 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (3 * Real.pi / 12) (4 * Real.pi / 12) (5 * Real.pi / 12) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 0 1).trans (Equiv.swap 1 2))
      obtain ⟨u, hu, hT⟩ := classify_12_3_4_5 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (3 * Real.pi / 12) (4 * Real.pi / 12) (5 * Real.pi / 12) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 1 2).trans (Equiv.swap 0 1))
      obtain ⟨u, hu, hT⟩ := classify_12_3_4_5 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (3 * Real.pi / 12) (4 * Real.pi / 12) (5 * Real.pi / 12) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 2)
      obtain ⟨u, hu, hT⟩ := classify_12_3_4_5 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
  · have hS := of_allCertEx allCertEx_12 a ha1 (sum_of_angles hn ha) hgcd (by simpa using hex)
    rcases l9_of_S D hn a ha hgcd hS with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

theorem exc_dispatch_18 (D : CongruentDissection N) (hn : 0 < 18) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / (18 : ℕ))
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) :
    SimilarTM D ∨ (∃ k l : Fin 3, l ≠ k ∧ D.model.angleAt k = Real.pi / 2 ∧
        ∃ j₁ j₂ : Fin 3, j₁ ≠ j₂ ∧ D.target.angleAt j₁ = D.model.angleAt l ∧
          D.target.angleAt j₂ = D.model.angleAt l) ∨ ExcPair D := by
  have ha1 : ∀ i, 0 < a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  by_cases hex : excl_18.contains (a 0, a 1, a 2) = true
  · have hmem : (a 0, a 1, a 2) ∈ excl_18 := by simpa using hex
    have hM0 : TileAngles D (a 0 * Real.pi / 18) (a 1 * Real.pi / 18) (a 2 * Real.pi / 18) :=
      ⟨Equiv.refl _, by simpa using ha 0, by simpa using ha 1, by simpa using ha 2⟩
    simp only [excl_18, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
    rcases hmem with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩
    · have hM' : TileAngles D (1 * Real.pi / 18) (3 * Real.pi / 18) (14 * Real.pi / 18) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.refl _)
      obtain ⟨u, hu, hT⟩ := classify_18_1_3_14 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 18) (3 * Real.pi / 18) (14 * Real.pi / 18) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 1 2)
      obtain ⟨u, hu, hT⟩ := classify_18_1_3_14 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 18) (3 * Real.pi / 18) (14 * Real.pi / 18) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 1)
      obtain ⟨u, hu, hT⟩ := classify_18_1_3_14 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 18) (3 * Real.pi / 18) (14 * Real.pi / 18) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 0 1).trans (Equiv.swap 1 2))
      obtain ⟨u, hu, hT⟩ := classify_18_1_3_14 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 18) (3 * Real.pi / 18) (14 * Real.pi / 18) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 1 2).trans (Equiv.swap 0 1))
      obtain ⟨u, hu, hT⟩ := classify_18_1_3_14 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 18) (3 * Real.pi / 18) (14 * Real.pi / 18) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 2)
      obtain ⟨u, hu, hT⟩ := classify_18_1_3_14 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (2 * Real.pi / 18) (3 * Real.pi / 18) (13 * Real.pi / 18) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.refl _)
      obtain ⟨u, hu, hT⟩ := classify_18_2_3_13 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (2 * Real.pi / 18) (3 * Real.pi / 18) (13 * Real.pi / 18) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 1 2)
      obtain ⟨u, hu, hT⟩ := classify_18_2_3_13 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (2 * Real.pi / 18) (3 * Real.pi / 18) (13 * Real.pi / 18) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 1)
      obtain ⟨u, hu, hT⟩ := classify_18_2_3_13 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (2 * Real.pi / 18) (3 * Real.pi / 18) (13 * Real.pi / 18) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 0 1).trans (Equiv.swap 1 2))
      obtain ⟨u, hu, hT⟩ := classify_18_2_3_13 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (2 * Real.pi / 18) (3 * Real.pi / 18) (13 * Real.pi / 18) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 1 2).trans (Equiv.swap 0 1))
      obtain ⟨u, hu, hT⟩ := classify_18_2_3_13 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (2 * Real.pi / 18) (3 * Real.pi / 18) (13 * Real.pi / 18) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 2)
      obtain ⟨u, hu, hT⟩ := classify_18_2_3_13 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (3 * Real.pi / 18) (7 * Real.pi / 18) (8 * Real.pi / 18) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.refl _)
      obtain ⟨u, hu, hT⟩ := classify_18_3_7_8 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (3 * Real.pi / 18) (7 * Real.pi / 18) (8 * Real.pi / 18) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 1 2)
      obtain ⟨u, hu, hT⟩ := classify_18_3_7_8 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (3 * Real.pi / 18) (7 * Real.pi / 18) (8 * Real.pi / 18) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 1)
      obtain ⟨u, hu, hT⟩ := classify_18_3_7_8 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (3 * Real.pi / 18) (7 * Real.pi / 18) (8 * Real.pi / 18) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 0 1).trans (Equiv.swap 1 2))
      obtain ⟨u, hu, hT⟩ := classify_18_3_7_8 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (3 * Real.pi / 18) (7 * Real.pi / 18) (8 * Real.pi / 18) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 1 2).trans (Equiv.swap 0 1))
      obtain ⟨u, hu, hT⟩ := classify_18_3_7_8 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (3 * Real.pi / 18) (7 * Real.pi / 18) (8 * Real.pi / 18) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 2)
      obtain ⟨u, hu, hT⟩ := classify_18_3_7_8 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
  · have hS := of_allCertEx allCertEx_18 a ha1 (sum_of_angles hn ha) hgcd (by simpa using hex)
    rcases l9_of_S D hn a ha hgcd hS with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

theorem exc_dispatch_24 (D : CongruentDissection N) (hn : 0 < 24) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / (24 : ℕ))
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) :
    SimilarTM D ∨ (∃ k l : Fin 3, l ≠ k ∧ D.model.angleAt k = Real.pi / 2 ∧
        ∃ j₁ j₂ : Fin 3, j₁ ≠ j₂ ∧ D.target.angleAt j₁ = D.model.angleAt l ∧
          D.target.angleAt j₂ = D.model.angleAt l) ∨ ExcPair D := by
  have ha1 : ∀ i, 0 < a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  by_cases hex : excl_24.contains (a 0, a 1, a 2) = true
  · have hmem : (a 0, a 1, a 2) ∈ excl_24 := by simpa using hex
    have hM0 : TileAngles D (a 0 * Real.pi / 24) (a 1 * Real.pi / 24) (a 2 * Real.pi / 24) :=
      ⟨Equiv.refl _, by simpa using ha 0, by simpa using ha 1, by simpa using ha 2⟩
    simp only [excl_24, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
    rcases hmem with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩
    · have hM' : TileAngles D (1 * Real.pi / 24) (4 * Real.pi / 24) (19 * Real.pi / 24) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.refl _)
      obtain ⟨u, hu, hT⟩ := classify_24_1_4_19 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 24) (4 * Real.pi / 24) (19 * Real.pi / 24) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 1 2)
      obtain ⟨u, hu, hT⟩ := classify_24_1_4_19 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 24) (4 * Real.pi / 24) (19 * Real.pi / 24) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 1)
      obtain ⟨u, hu, hT⟩ := classify_24_1_4_19 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 24) (4 * Real.pi / 24) (19 * Real.pi / 24) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 0 1).trans (Equiv.swap 1 2))
      obtain ⟨u, hu, hT⟩ := classify_24_1_4_19 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 24) (4 * Real.pi / 24) (19 * Real.pi / 24) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 1 2).trans (Equiv.swap 0 1))
      obtain ⟨u, hu, hT⟩ := classify_24_1_4_19 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 24) (4 * Real.pi / 24) (19 * Real.pi / 24) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 2)
      obtain ⟨u, hu, hT⟩ := classify_24_1_4_19 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 24) (6 * Real.pi / 24) (17 * Real.pi / 24) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.refl _)
      obtain ⟨u, hu, hT⟩ := classify_24_1_6_17 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 24) (6 * Real.pi / 24) (17 * Real.pi / 24) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 1 2)
      obtain ⟨u, hu, hT⟩ := classify_24_1_6_17 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 24) (6 * Real.pi / 24) (17 * Real.pi / 24) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 1)
      obtain ⟨u, hu, hT⟩ := classify_24_1_6_17 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 24) (6 * Real.pi / 24) (17 * Real.pi / 24) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 0 1).trans (Equiv.swap 1 2))
      obtain ⟨u, hu, hT⟩ := classify_24_1_6_17 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 24) (6 * Real.pi / 24) (17 * Real.pi / 24) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 1 2).trans (Equiv.swap 0 1))
      obtain ⟨u, hu, hT⟩ := classify_24_1_6_17 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 24) (6 * Real.pi / 24) (17 * Real.pi / 24) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 2)
      obtain ⟨u, hu, hT⟩ := classify_24_1_6_17 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (4 * Real.pi / 24) (7 * Real.pi / 24) (13 * Real.pi / 24) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.refl _)
      obtain ⟨u, hu, hT⟩ := classify_24_4_7_13 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (4 * Real.pi / 24) (7 * Real.pi / 24) (13 * Real.pi / 24) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 1 2)
      obtain ⟨u, hu, hT⟩ := classify_24_4_7_13 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (4 * Real.pi / 24) (7 * Real.pi / 24) (13 * Real.pi / 24) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 1)
      obtain ⟨u, hu, hT⟩ := classify_24_4_7_13 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (4 * Real.pi / 24) (7 * Real.pi / 24) (13 * Real.pi / 24) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 0 1).trans (Equiv.swap 1 2))
      obtain ⟨u, hu, hT⟩ := classify_24_4_7_13 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (4 * Real.pi / 24) (7 * Real.pi / 24) (13 * Real.pi / 24) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 1 2).trans (Equiv.swap 0 1))
      obtain ⟨u, hu, hT⟩ := classify_24_4_7_13 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (4 * Real.pi / 24) (7 * Real.pi / 24) (13 * Real.pi / 24) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 2)
      obtain ⟨u, hu, hT⟩ := classify_24_4_7_13 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (5 * Real.pi / 24) (6 * Real.pi / 24) (13 * Real.pi / 24) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.refl _)
      obtain ⟨u, hu, hT⟩ := classify_24_5_6_13 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (5 * Real.pi / 24) (6 * Real.pi / 24) (13 * Real.pi / 24) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 1 2)
      obtain ⟨u, hu, hT⟩ := classify_24_5_6_13 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (5 * Real.pi / 24) (6 * Real.pi / 24) (13 * Real.pi / 24) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 1)
      obtain ⟨u, hu, hT⟩ := classify_24_5_6_13 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (5 * Real.pi / 24) (6 * Real.pi / 24) (13 * Real.pi / 24) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 0 1).trans (Equiv.swap 1 2))
      obtain ⟨u, hu, hT⟩ := classify_24_5_6_13 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (5 * Real.pi / 24) (6 * Real.pi / 24) (13 * Real.pi / 24) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 1 2).trans (Equiv.swap 0 1))
      obtain ⟨u, hu, hT⟩ := classify_24_5_6_13 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (5 * Real.pi / 24) (6 * Real.pi / 24) (13 * Real.pi / 24) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 2)
      obtain ⟨u, hu, hT⟩ := classify_24_5_6_13 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
  · have hS := of_allCertEx allCertEx_24 a ha1 (sum_of_angles hn ha) hgcd (by simpa using hex)
    rcases l9_of_S D hn a ha hgcd hS with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

theorem exc_dispatch_30 (D : CongruentDissection N) (hn : 0 < 30) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / (30 : ℕ))
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) :
    SimilarTM D ∨ (∃ k l : Fin 3, l ≠ k ∧ D.model.angleAt k = Real.pi / 2 ∧
        ∃ j₁ j₂ : Fin 3, j₁ ≠ j₂ ∧ D.target.angleAt j₁ = D.model.angleAt l ∧
          D.target.angleAt j₂ = D.model.angleAt l) ∨ ExcPair D := by
  have ha1 : ∀ i, 0 < a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  by_cases hex : excl_30.contains (a 0, a 1, a 2) = true
  · have hmem : (a 0, a 1, a 2) ∈ excl_30 := by simpa using hex
    have hM0 : TileAngles D (a 0 * Real.pi / 30) (a 1 * Real.pi / 30) (a 2 * Real.pi / 30) :=
      ⟨Equiv.refl _, by simpa using ha 0, by simpa using ha 1, by simpa using ha 2⟩
    simp only [excl_30, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
    rcases hmem with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩
    · have hM' : TileAngles D (1 * Real.pi / 30) (5 * Real.pi / 30) (24 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.refl _)
      obtain ⟨u, hu, hT⟩ := classify_30_1_5_24 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 30) (5 * Real.pi / 30) (24 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 1 2)
      obtain ⟨u, hu, hT⟩ := classify_30_1_5_24 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 30) (5 * Real.pi / 30) (24 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 1)
      obtain ⟨u, hu, hT⟩ := classify_30_1_5_24 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 30) (5 * Real.pi / 30) (24 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 0 1).trans (Equiv.swap 1 2))
      obtain ⟨u, hu, hT⟩ := classify_30_1_5_24 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 30) (5 * Real.pi / 30) (24 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 1 2).trans (Equiv.swap 0 1))
      obtain ⟨u, hu, hT⟩ := classify_30_1_5_24 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 30) (5 * Real.pi / 30) (24 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 2)
      obtain ⟨u, hu, hT⟩ := classify_30_1_5_24 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 30) (10 * Real.pi / 30) (19 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.refl _)
      obtain ⟨u, hu, hT⟩ := classify_30_1_10_19 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
      · right; right
        have hT' : TgtAngles D (10 * Real.pi / 30) (10 * Real.pi / 30) (10 * Real.pi / 30) := by simpa using hT
        unfold ExcPair
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hM', hT'⟩))))
    · have hM' : TileAngles D (1 * Real.pi / 30) (10 * Real.pi / 30) (19 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 1 2)
      obtain ⟨u, hu, hT⟩ := classify_30_1_10_19 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
      · right; right
        have hT' : TgtAngles D (10 * Real.pi / 30) (10 * Real.pi / 30) (10 * Real.pi / 30) := by simpa using hT
        unfold ExcPair
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hM', hT'⟩))))
    · have hM' : TileAngles D (1 * Real.pi / 30) (10 * Real.pi / 30) (19 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 1)
      obtain ⟨u, hu, hT⟩ := classify_30_1_10_19 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
      · right; right
        have hT' : TgtAngles D (10 * Real.pi / 30) (10 * Real.pi / 30) (10 * Real.pi / 30) := by simpa using hT
        unfold ExcPair
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hM', hT'⟩))))
    · have hM' : TileAngles D (1 * Real.pi / 30) (10 * Real.pi / 30) (19 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 0 1).trans (Equiv.swap 1 2))
      obtain ⟨u, hu, hT⟩ := classify_30_1_10_19 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
      · right; right
        have hT' : TgtAngles D (10 * Real.pi / 30) (10 * Real.pi / 30) (10 * Real.pi / 30) := by simpa using hT
        unfold ExcPair
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hM', hT'⟩))))
    · have hM' : TileAngles D (1 * Real.pi / 30) (10 * Real.pi / 30) (19 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 1 2).trans (Equiv.swap 0 1))
      obtain ⟨u, hu, hT⟩ := classify_30_1_10_19 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
      · right; right
        have hT' : TgtAngles D (10 * Real.pi / 30) (10 * Real.pi / 30) (10 * Real.pi / 30) := by simpa using hT
        unfold ExcPair
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hM', hT'⟩))))
    · have hM' : TileAngles D (1 * Real.pi / 30) (10 * Real.pi / 30) (19 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 2)
      obtain ⟨u, hu, hT⟩ := classify_30_1_10_19 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
      · right; right
        have hT' : TgtAngles D (10 * Real.pi / 30) (10 * Real.pi / 30) (10 * Real.pi / 30) := by simpa using hT
        unfold ExcPair
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hM', hT'⟩))))
    · have hM' : TileAngles D (5 * Real.pi / 30) (6 * Real.pi / 30) (19 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.refl _)
      obtain ⟨u, hu, hT⟩ := classify_30_5_6_19 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (5 * Real.pi / 30) (6 * Real.pi / 30) (19 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 1 2)
      obtain ⟨u, hu, hT⟩ := classify_30_5_6_19 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (5 * Real.pi / 30) (6 * Real.pi / 30) (19 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 1)
      obtain ⟨u, hu, hT⟩ := classify_30_5_6_19 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (5 * Real.pi / 30) (6 * Real.pi / 30) (19 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 0 1).trans (Equiv.swap 1 2))
      obtain ⟨u, hu, hT⟩ := classify_30_5_6_19 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (5 * Real.pi / 30) (6 * Real.pi / 30) (19 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 1 2).trans (Equiv.swap 0 1))
      obtain ⟨u, hu, hT⟩ := classify_30_5_6_19 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (5 * Real.pi / 30) (6 * Real.pi / 30) (19 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 2)
      obtain ⟨u, hu, hT⟩ := classify_30_5_6_19 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (5 * Real.pi / 30) (7 * Real.pi / 30) (18 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.refl _)
      obtain ⟨u, hu, hT⟩ := classify_30_5_7_18 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (5 * Real.pi / 30) (7 * Real.pi / 30) (18 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 1 2)
      obtain ⟨u, hu, hT⟩ := classify_30_5_7_18 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (5 * Real.pi / 30) (7 * Real.pi / 30) (18 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 1)
      obtain ⟨u, hu, hT⟩ := classify_30_5_7_18 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (5 * Real.pi / 30) (7 * Real.pi / 30) (18 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 0 1).trans (Equiv.swap 1 2))
      obtain ⟨u, hu, hT⟩ := classify_30_5_7_18 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (5 * Real.pi / 30) (7 * Real.pi / 30) (18 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 1 2).trans (Equiv.swap 0 1))
      obtain ⟨u, hu, hT⟩ := classify_30_5_7_18 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (5 * Real.pi / 30) (7 * Real.pi / 30) (18 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 2)
      obtain ⟨u, hu, hT⟩ := classify_30_5_7_18 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (5 * Real.pi / 30) (12 * Real.pi / 30) (13 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.refl _)
      obtain ⟨u, hu, hT⟩ := classify_30_5_12_13 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (5 * Real.pi / 30) (12 * Real.pi / 30) (13 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 1 2)
      obtain ⟨u, hu, hT⟩ := classify_30_5_12_13 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (5 * Real.pi / 30) (12 * Real.pi / 30) (13 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 1)
      obtain ⟨u, hu, hT⟩ := classify_30_5_12_13 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (5 * Real.pi / 30) (12 * Real.pi / 30) (13 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 0 1).trans (Equiv.swap 1 2))
      obtain ⟨u, hu, hT⟩ := classify_30_5_12_13 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (5 * Real.pi / 30) (12 * Real.pi / 30) (13 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 1 2).trans (Equiv.swap 0 1))
      obtain ⟨u, hu, hT⟩ := classify_30_5_12_13 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (5 * Real.pi / 30) (12 * Real.pi / 30) (13 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 2)
      obtain ⟨u, hu, hT⟩ := classify_30_5_12_13 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (7 * Real.pi / 30) (10 * Real.pi / 30) (13 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.refl _)
      obtain ⟨u, hu, hT⟩ := classify_30_7_10_13 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
      · right; right
        have hT' : TgtAngles D (10 * Real.pi / 30) (10 * Real.pi / 30) (10 * Real.pi / 30) := by simpa using hT
        unfold ExcPair
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨hM', hT'⟩)))))
    · have hM' : TileAngles D (7 * Real.pi / 30) (10 * Real.pi / 30) (13 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 1 2)
      obtain ⟨u, hu, hT⟩ := classify_30_7_10_13 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
      · right; right
        have hT' : TgtAngles D (10 * Real.pi / 30) (10 * Real.pi / 30) (10 * Real.pi / 30) := by simpa using hT
        unfold ExcPair
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨hM', hT'⟩)))))
    · have hM' : TileAngles D (7 * Real.pi / 30) (10 * Real.pi / 30) (13 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 1)
      obtain ⟨u, hu, hT⟩ := classify_30_7_10_13 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
      · right; right
        have hT' : TgtAngles D (10 * Real.pi / 30) (10 * Real.pi / 30) (10 * Real.pi / 30) := by simpa using hT
        unfold ExcPair
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨hM', hT'⟩)))))
    · have hM' : TileAngles D (7 * Real.pi / 30) (10 * Real.pi / 30) (13 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 0 1).trans (Equiv.swap 1 2))
      obtain ⟨u, hu, hT⟩ := classify_30_7_10_13 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
      · right; right
        have hT' : TgtAngles D (10 * Real.pi / 30) (10 * Real.pi / 30) (10 * Real.pi / 30) := by simpa using hT
        unfold ExcPair
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨hM', hT'⟩)))))
    · have hM' : TileAngles D (7 * Real.pi / 30) (10 * Real.pi / 30) (13 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 1 2).trans (Equiv.swap 0 1))
      obtain ⟨u, hu, hT⟩ := classify_30_7_10_13 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
      · right; right
        have hT' : TgtAngles D (10 * Real.pi / 30) (10 * Real.pi / 30) (10 * Real.pi / 30) := by simpa using hT
        unfold ExcPair
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨hM', hT'⟩)))))
    · have hM' : TileAngles D (7 * Real.pi / 30) (10 * Real.pi / 30) (13 * Real.pi / 30) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 2)
      obtain ⟨u, hu, hT⟩ := classify_30_7_10_13 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
      · right; right
        have hT' : TgtAngles D (10 * Real.pi / 30) (10 * Real.pi / 30) (10 * Real.pi / 30) := by simpa using hT
        unfold ExcPair
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨hM', hT'⟩)))))
  · have hS := of_allCertEx allCertEx_30 a ha1 (sum_of_angles hn ha) hgcd (by simpa using hex)
    rcases l9_of_S D hn a ha hgcd hS with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

theorem exc_dispatch_60 (D : CongruentDissection N) (hn : 0 < 60) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / (60 : ℕ))
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) :
    SimilarTM D ∨ (∃ k l : Fin 3, l ≠ k ∧ D.model.angleAt k = Real.pi / 2 ∧
        ∃ j₁ j₂ : Fin 3, j₁ ≠ j₂ ∧ D.target.angleAt j₁ = D.model.angleAt l ∧
          D.target.angleAt j₂ = D.model.angleAt l) ∨ ExcPair D := by
  have ha1 : ∀ i, 0 < a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  by_cases hex : excl_60.contains (a 0, a 1, a 2) = true
  · have hmem : (a 0, a 1, a 2) ∈ excl_60 := by simpa using hex
    have hM0 : TileAngles D (a 0 * Real.pi / 60) (a 1 * Real.pi / 60) (a 2 * Real.pi / 60) :=
      ⟨Equiv.refl _, by simpa using ha 0, by simpa using ha 1, by simpa using ha 2⟩
    simp only [excl_60, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
    rcases hmem with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩
    · have hM' : TileAngles D (1 * Real.pi / 60) (10 * Real.pi / 60) (49 * Real.pi / 60) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.refl _)
      obtain ⟨u, hu, hT⟩ := classify_60_1_10_49 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 60) (10 * Real.pi / 60) (49 * Real.pi / 60) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 1 2)
      obtain ⟨u, hu, hT⟩ := classify_60_1_10_49 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 60) (10 * Real.pi / 60) (49 * Real.pi / 60) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 1)
      obtain ⟨u, hu, hT⟩ := classify_60_1_10_49 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 60) (10 * Real.pi / 60) (49 * Real.pi / 60) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 0 1).trans (Equiv.swap 1 2))
      obtain ⟨u, hu, hT⟩ := classify_60_1_10_49 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 60) (10 * Real.pi / 60) (49 * Real.pi / 60) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 1 2).trans (Equiv.swap 0 1))
      obtain ⟨u, hu, hT⟩ := classify_60_1_10_49 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (1 * Real.pi / 60) (10 * Real.pi / 60) (49 * Real.pi / 60) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 2)
      obtain ⟨u, hu, hT⟩ := classify_60_1_10_49 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (7 * Real.pi / 60) (10 * Real.pi / 60) (43 * Real.pi / 60) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.refl _)
      obtain ⟨u, hu, hT⟩ := classify_60_7_10_43 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (7 * Real.pi / 60) (10 * Real.pi / 60) (43 * Real.pi / 60) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 1 2)
      obtain ⟨u, hu, hT⟩ := classify_60_7_10_43 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (7 * Real.pi / 60) (10 * Real.pi / 60) (43 * Real.pi / 60) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 1)
      obtain ⟨u, hu, hT⟩ := classify_60_7_10_43 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (7 * Real.pi / 60) (10 * Real.pi / 60) (43 * Real.pi / 60) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 0 1).trans (Equiv.swap 1 2))
      obtain ⟨u, hu, hT⟩ := classify_60_7_10_43 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (7 * Real.pi / 60) (10 * Real.pi / 60) (43 * Real.pi / 60) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 1 2).trans (Equiv.swap 0 1))
      obtain ⟨u, hu, hT⟩ := classify_60_7_10_43 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (7 * Real.pi / 60) (10 * Real.pi / 60) (43 * Real.pi / 60) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 2)
      obtain ⟨u, hu, hT⟩ := classify_60_7_10_43 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (10 * Real.pi / 60) (13 * Real.pi / 60) (37 * Real.pi / 60) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.refl _)
      obtain ⟨u, hu, hT⟩ := classify_60_10_13_37 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (10 * Real.pi / 60) (13 * Real.pi / 60) (37 * Real.pi / 60) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 1 2)
      obtain ⟨u, hu, hT⟩ := classify_60_10_13_37 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (10 * Real.pi / 60) (13 * Real.pi / 60) (37 * Real.pi / 60) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 1)
      obtain ⟨u, hu, hT⟩ := classify_60_10_13_37 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (10 * Real.pi / 60) (13 * Real.pi / 60) (37 * Real.pi / 60) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 0 1).trans (Equiv.swap 1 2))
      obtain ⟨u, hu, hT⟩ := classify_60_10_13_37 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (10 * Real.pi / 60) (13 * Real.pi / 60) (37 * Real.pi / 60) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 1 2).trans (Equiv.swap 0 1))
      obtain ⟨u, hu, hT⟩ := classify_60_10_13_37 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (10 * Real.pi / 60) (13 * Real.pi / 60) (37 * Real.pi / 60) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 2)
      obtain ⟨u, hu, hT⟩ := classify_60_10_13_37 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (10 * Real.pi / 60) (19 * Real.pi / 60) (31 * Real.pi / 60) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.refl _)
      obtain ⟨u, hu, hT⟩ := classify_60_10_19_31 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (10 * Real.pi / 60) (19 * Real.pi / 60) (31 * Real.pi / 60) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 1 2)
      obtain ⟨u, hu, hT⟩ := classify_60_10_19_31 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (10 * Real.pi / 60) (19 * Real.pi / 60) (31 * Real.pi / 60) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 1)
      obtain ⟨u, hu, hT⟩ := classify_60_10_19_31 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (10 * Real.pi / 60) (19 * Real.pi / 60) (31 * Real.pi / 60) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 0 1).trans (Equiv.swap 1 2))
      obtain ⟨u, hu, hT⟩ := classify_60_10_19_31 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (10 * Real.pi / 60) (19 * Real.pi / 60) (31 * Real.pi / 60) := by
        simpa [e0, e1, e2] using hM0.reorder ((Equiv.swap 1 2).trans (Equiv.swap 0 1))
      obtain ⟨u, hu, hT⟩ := classify_60_10_19_31 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
    · have hM' : TileAngles D (10 * Real.pi / 60) (19 * Real.pi / 60) (31 * Real.pi / 60) := by
        simpa [e0, e1, e2] using hM0.reorder (Equiv.swap 0 2)
      obtain ⟨u, hu, hT⟩ := classify_60_10_19_31 D hM'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl
      · left; exact similar_of_same_angles D hM' (by simpa using hT)
  · have hS := of_allCertEx allCertEx_60 a ha1 (sum_of_angles hn ha) hgcd (by simpa using hex)
    rcases l9_of_S D hn a ha hgcd hS with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

/-- **Classification of commensurable tiles (covered denominators).** -/
theorem classify_commensurable (D : CongruentDissection N) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) (hcov : Covered n) :
    SimilarTM D ∨ (∃ k l : Fin 3, l ≠ k ∧ D.model.angleAt k = Real.pi / 2 ∧
        ∃ j₁ j₂ : Fin 3, j₁ ≠ j₂ ∧ D.target.angleAt j₁ = D.model.angleAt l ∧
          D.target.angleAt j₂ = D.model.angleAt l) ∨ ExcPair D := by
  rcases hcov with ⟨p, hp, hp7, hpn⟩ | hC | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases l9_generic D hn a ha hgcd hp hp7 hpn with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases l9_smooth2 D hn a ha hgcd hC with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact exc_dispatch_3 D hn a ha hgcd
  · exact exc_dispatch_4 D hn a ha hgcd
  · exact exc_dispatch_6 D hn a ha hgcd
  · exact exc_dispatch_8 D hn a ha hgcd
  · exact exc_dispatch_10 D hn a ha hgcd
  · exact exc_dispatch_12 D hn a ha hgcd
  · exact exc_dispatch_18 D hn a ha hgcd
  · exact exc_dispatch_24 D hn a ha hgcd
  · exact exc_dispatch_30 D hn a ha hgcd
  · exact exc_dispatch_60 D hn a ha hgcd


/-- **Non-vacuity of the hypotheses of `classify_commensurable`.**  The ladder dissection of a `(π/6, 2π/6, 3π/6)` triangle (`N = 4`) satisfies all of them
(`n = 6`, primitive tile numerators, `Covered 6`); the conclusion is then the similar alternative. -/
theorem classify_commensurable_hyps_witness :
    ∃ (N : ℕ) (D : CongruentDissection N) (a : Fin 3 → ℕ),
      (∀ k, D.model.angleAt k = a k * Real.pi / (6 : ℕ)) ∧
      Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 ∧ Covered 6 := by
  have hpi := Real.pi_pos
  obtain ⟨N, D, ⟨σ, m0, m1, m2⟩, -⟩ := ladder_with_angles (α := Real.pi / 6) (β := 2 * Real.pi / 6)
    (by positivity) (by positivity) (by linarith)
  refine ⟨N, D, fun l => (![1, 2, 3] : Fin 3 → ℕ) (σ.symm l), ?_, ?_,
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
  · intro l
    have : ∀ k, D.model.angleAt (σ k) = ((![1, 2, 3] : Fin 3 → ℕ) k : ℕ) * Real.pi / (6 : ℕ) := by
      intro k; fin_cases k
      · simpa using m0
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons]; push_cast; rw [m1]; try ring
      · simp only [Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]; push_cast
        rw [m2]; try ring
    simpa using this (σ.symm l)
  · have hdvd : ∀ l, Nat.gcd ((![1, 2, 3] : Fin 3 → ℕ) (σ.symm 0))
        (Nat.gcd ((![1, 2, 3] : Fin 3 → ℕ) (σ.symm 1)) ((![1, 2, 3] : Fin 3 → ℕ) (σ.symm 2))) ∣
        (![1, 2, 3] : Fin 3 → ℕ) (σ.symm l) := by
      intro l; fin_cases l
      · exact Nat.gcd_dvd_left _ _
      · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
      · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
    have := hdvd (σ 0)
    simp only [Equiv.symm_apply_apply, Matrix.cons_val_zero] at this
    exact Nat.dvd_one.mp this

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.classify_commensurable
