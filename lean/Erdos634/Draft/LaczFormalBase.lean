-- Draft/LaczFormalBase.lean -- shared vocabulary for the Laczkovich-classification formalization
-- ((private working notes, not included)): `TileAngles`, irrationality helpers, isosceles-target
-- bookkeeping.  Statements of atoms L2a, L5, L6 follow Beeson-Rosu (arXiv 2607.23453) Lemma 1,
-- Thm 3, Thm 7 / Table 3, which quote Laczkovich (1995, DM 140; 2012, DCG 48), Beeson (Iso, Eq), SWW.
-- UNAUDITED.  No sorry, no native_decide.
import Erdos634.Draft.LemmaCFinal

open scoped Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
  Erdos634.Draft.LemmaCFinal

namespace Erdos634.Draft.LaczFormal

/-- The three angles of a triangle sum to `π`. -/
theorem angleAt_sum (T : Tri) : T.angleAt 0 + T.angleAt 1 + T.angleAt 2 = Real.pi := by
  show cornerAngle (T.pts 1) (T.pts 0) (T.pts 2) +
       cornerAngle (T.pts 2) (T.pts 1) (T.pts 0) +
       cornerAngle (T.pts 0) (T.pts 2) (T.pts 1) = Real.pi
  exact Erdos634.Geometry.cornerAngle_sum T

/-- The model's angles are `x, y, z` in some order. -/
def TileAngles {N : ℕ} (D : CongruentDissection N) (x y z : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3), D.model.angleAt (σ 0) = x ∧ D.model.angleAt (σ 1) = y ∧
    D.model.angleAt (σ 2) = z

theorem TileAngles.swap {N : ℕ} {D : CongruentDissection N} {x y z : ℝ}
    (h : TileAngles D x y z) : TileAngles D y x z := by
  obtain ⟨σ, h0, h1, h2⟩ := h
  refine ⟨(Equiv.swap (0 : Fin 3) 1).trans σ, ?_, ?_, ?_⟩
  · simp only [Equiv.trans_apply, Equiv.swap_apply_left]; exact h1
  · simp only [Equiv.trans_apply, Equiv.swap_apply_right]; exact h0
  · simp only [Equiv.trans_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]; exact h2

theorem TileAngles.swap23 {N : ℕ} {D : CongruentDissection N} {x y z : ℝ}
    (h : TileAngles D x y z) : TileAngles D x z y := by
  obtain ⟨σ, h0, h1, h2⟩ := h
  refine ⟨(Equiv.swap (1 : Fin 3) 2).trans σ, ?_, ?_, ?_⟩
  · simp only [Equiv.trans_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]; exact h0
  · simp only [Equiv.trans_apply, Equiv.swap_apply_left]; exact h2
  · simp only [Equiv.trans_apply, Equiv.swap_apply_right]; exact h1

theorem TileAngles.cast {N : ℕ} {D : CongruentDissection N} {x y z x' y' z' : ℝ}
    (h : TileAngles D x y z) (ex : x = x') (ey : y = y') (ez : z = z') :
    TileAngles D x' y' z' := by
  subst ex ey ez; exact h

theorem TileAngles.congr3 {N : ℕ} {D : CongruentDissection N} {x y z z' : ℝ}
    (h : TileAngles D x y z) (e : z = z') : TileAngles D x y z' := by
  obtain ⟨σ, h0, h1, h2⟩ := h
  exact ⟨σ, h0, h1, h2.trans e⟩

theorem tgt_congr3 {N : ℕ} {D : CongruentDissection N} {x y z z' : ℝ}
    (h : TgtAngles D x y z) (e : z = z') : TgtAngles D x y z' := by
  obtain ⟨σ, h0, h1, h2⟩ := h
  exact ⟨σ, h0, h1, h2.trans e⟩

theorem irrPi_ne {α : ℝ} (h : IrrPi α) (q : ℚ) : α ≠ (q : ℝ) * Real.pi := fun e => h ⟨q, e⟩

theorem irrPi_of_irrational {α : ℝ} (h : Irrational (α / Real.pi)) : IrrPi α := by
  rintro ⟨r, hr⟩
  apply h
  exact ⟨r, by rw [hr]; field_simp [Real.pi_pos.ne']⟩

/-- Independence of `α` and `π` over `ℚ` when `α ∉ ℚπ`. -/
theorem irr_eq {α : ℝ} (hα : IrrPi α) (a1 b1 a2 b2 : ℚ)
    (h : (a1 : ℝ) * α + (b1 : ℝ) * Real.pi = (a2 : ℝ) * α + (b2 : ℝ) * Real.pi) :
    a1 = a2 ∧ b1 = b2 := by
  have hb : a1 = a2 := by
    by_contra hne
    have hne' : ((a1 : ℝ) - a2) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hne
    apply hα
    refine ⟨(b2 - b1) / (a1 - a2), ?_⟩
    push_cast
    field_simp
    linear_combination h
  subst hb
  refine ⟨rfl, ?_⟩
  have h1 : ((b1 : ℝ) - b2) * Real.pi = 0 := by linarith
  have h2 := (mul_eq_zero.mp h1).resolve_right Real.pi_pos.ne'
  exact_mod_cast sub_eq_zero.mp h2

theorem tgt_eq_third {N : ℕ} {D : CongruentDissection N} (hEq : Equilateral D) {x y z : ℝ}
    (h : TgtAngles D x y z) : x = Real.pi / 3 ∧ y = Real.pi / 3 ∧ z = Real.pi / 3 := by
  obtain ⟨σ, h0, h1, h2⟩ := h
  exact ⟨h0 ▸ hEq _, h1 ▸ hEq _, h2 ▸ hEq _⟩

/-- If the target has two equal angles, two of the listed angles coincide. -/
theorem tgt_iso {N : ℕ} {D : CongruentDissection N} {x y z : ℝ} (h : TgtAngles D x y z)
    (hiso : ∃ i j : Fin 3, i ≠ j ∧ D.target.angleAt i = D.target.angleAt j) :
    x = y ∨ x = z ∨ y = z := by
  obtain ⟨σ, h0, h1, h2⟩ := h
  obtain ⟨i, j, hij, he⟩ := hiso
  obtain ⟨a, rfl⟩ := σ.surjective i
  obtain ⟨b, rfl⟩ := σ.surjective j
  have hab : a ≠ b := fun e => hij (by rw [e])
  have fin3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  rcases fin3 a with rfl | rfl | rfl <;> rcases fin3 b with rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hab
    | (left; rw [← h0, ← h1]; first | exact he | exact he.symm)
    | (right; left; rw [← h0, ← h2]; first | exact he | exact he.symm)
    | (right; right; rw [← h1, ← h2]; first | exact he | exact he.symm)

/-- A target with two angles `x` has angles `(x, x, π − 2x)`. -/
theorem tgt_of_two {N : ℕ} (D : CongruentDissection N) (i j : Fin 3) (hij : i ≠ j) (x : ℝ)
    (hi : D.target.angleAt i = x) (hj : D.target.angleAt j = x) :
    TgtAngles D x x (Real.pi - 2 * x) := by
  obtain ⟨k, hik, hjk⟩ := (by decide : ∀ p q : Fin 3, p ≠ q → ∃ r, p ≠ r ∧ q ≠ r) i j hij
  refine ⟨permOf i j k hij hik hjk, ?_, ?_, ?_⟩
  · rw [permOf_0]; exact hi
  · rw [permOf_1]; exact hj
  · rw [permOf_2]
    have h3 : D.target.angleAt i + D.target.angleAt j + D.target.angleAt k
        = D.target.angleAt 0 + D.target.angleAt 1 + D.target.angleAt 2 :=
      sum3 (fun m => D.target.angleAt m) i j k hij hik hjk
    have hs := angleAt_sum D.target
    linarith

/-- A tile with two distinct corners of angles `x, y` has angles `(x, y, π − x − y)`. -/
theorem tile_of_two {N : ℕ} (D : CongruentDissection N) (p q : Fin 3) (hpq : p ≠ q) (x y : ℝ)
    (hp : D.model.angleAt p = x) (hq : D.model.angleAt q = y) :
    TileAngles D x y (Real.pi - x - y) := by
  obtain ⟨r, hpr, hqr⟩ := (by decide : ∀ p q : Fin 3, p ≠ q → ∃ r, p ≠ r ∧ q ≠ r) p q hpq
  refine ⟨permOf p q r hpq hpr hqr, ?_, ?_, ?_⟩
  · rw [permOf_0]; exact hp
  · rw [permOf_1]; exact hq
  · rw [permOf_2]
    have h3 : D.model.angleAt p + D.model.angleAt q + D.model.angleAt r
        = D.model.angleAt 0 + D.model.angleAt 1 + D.model.angleAt 2 :=
      sum3 (fun m => D.model.angleAt m) p q r hpq hpr hqr
    have hs := angleAt_sum D.model
    linarith

/-- Two target/tile angles of the shapes `a·α + b·π` cannot coincide when `α ∉ ℚπ` unless the
coefficients do: so a target whose listed angles have pairwise distinct coefficient vectors is not
isosceles. -/
theorem noniso {N : ℕ} {D : CongruentDissection N}
    (hiso : ∃ i j : Fin 3, i ≠ j ∧ D.target.angleAt i = D.target.angleAt j)
    {α : ℝ} (hα : IrrPi α) {x y z : ℝ} (h : TgtAngles D x y z) (a1 b1 a2 b2 a3 b3 : ℚ)
    (hx : x = (a1 : ℝ) * α + (b1 : ℝ) * Real.pi) (hy : y = (a2 : ℝ) * α + (b2 : ℝ) * Real.pi)
    (hz : z = (a3 : ℝ) * α + (b3 : ℝ) * Real.pi)
    (n12 : ¬ (a1 = a2 ∧ b1 = b2)) (n13 : ¬ (a1 = a3 ∧ b1 = b3))
    (n23 : ¬ (a2 = a3 ∧ b2 = b3)) : False := by
  rcases tgt_iso h hiso with e | e | e
  · exact n12 (irr_eq hα _ _ _ _ (by rw [← hx, ← hy]; exact e))
  · exact n13 (irr_eq hα _ _ _ _ (by rw [← hx, ← hz]; exact e))
  · exact n23 (irr_eq hα _ _ _ _ (by rw [← hy, ← hz]; exact e))

end Erdos634.Draft.LaczFormal
