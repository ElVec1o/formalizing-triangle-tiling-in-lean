import Erdos634.Draft.LaczFormal9v

/-!
# Laczkovich DM 140 (1995), Theorem 2.6: the six dissections of the isosceles triangle `(α, α, π - 2α)`, `α = 6x`

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.6 (proof), Theorems 2.3, 2.4, 2.5), Beeson, Beeson-Zhang, Zhang.
Formalization debt, not /goal progress.

`core26`: `0 < x < π/72`, `sin x = s ∈ ℚ`, `√3 cos x = u ∈ ℚ`, `α = 6x` (so `sin(α/6)` and `√3 cos(α/6)` rational, as in the printed proof).  Every
triangle `T` with angles `(α, α, π - 2α)` is a union of finitely many congruent triangles of each of the six shapes of `sixX/sixY/sixZ`
(LaczFormal9v): the triple 1 trivially, the triple 2 by the altitude, the triple 3 by Theorem 2.3 (`cos α ∈ ℚ`), the triple 4 by Theorem 2.4
(`sin(α/2) ∈ ℚ`), the triple 5 by Theorem 2.4 with `α' = (π - 2α)/3` (`sin(α'/2) ∈ ℚ`, `T` of kind `(β', β', 3α')`), the triple 6 by
Theorem 2.5 (`√3 sin α`, `cos α ∈ ℚ`).  `SixShapes T` also records that the six triples are pairwise non-permutations of each other.
-/

open scoped Classical
open Erdos634.Geometry Erdos634.LaczL35 EuclideanGeometry

namespace Erdos634.Laczkovich9w

open Erdos634.Laczkovich9v Erdos634.Laczkovich9u

/-- `T` is dissected into congruent triangles of six pairwise non-similar shapes. -/
def SixShapes (T : Tri) : Prop :=
  ∃ x y z : Fin 6 → ℝ, (∀ i, PrintedConcl T (x i) (y i) (z i)) ∧
    ∀ i j : Fin 6, i ≠ j → ∀ σ : Equiv.Perm (Fin 3),
      ¬ (∀ k, (![x j, y j, z j] : Fin 3 → ℝ) (σ k) = (![x i, y i, z i] : Fin 3 → ℝ) k)

section rat
variable (x : ℝ) (s u : ℚ) (hs : Real.sin x = s) (hu : Real.sqrt 3 * Real.cos x = u)

include hs

theorem cos_sq_eq : Real.cos x ^ 2 = 1 - (s : ℝ) ^ 2 := by
  have := Real.sin_sq_add_cos_sq x; rw [hs] at this; linarith

theorem rat_cos6 : ∃ q : ℚ, Real.cos (6 * x) = q := by
  refine ⟨2 * (1 - s ^ 2) * (1 - 4 * s ^ 2) ^ 2 - 1, ?_⟩
  have hc2 := cos_sq_eq x s hs
  have h6 : Real.cos (6 * x) = 2 * Real.cos (3 * x) ^ 2 - 1 := by
    rw [show 6 * x = 2 * (3 * x) by ring, Real.cos_two_mul]
  rw [h6, Real.cos_three_mul]
  have : (4 * Real.cos x ^ 3 - 3 * Real.cos x) ^ 2 = Real.cos x ^ 2 * (4 * Real.cos x ^ 2 - 3) ^ 2 := by ring
  rw [this, hc2]; push_cast; ring

theorem rat_sin_half : ∃ q : ℚ, Real.sin (6 * x / 2) = q := by
  refine ⟨3 * s - 4 * s ^ 3, ?_⟩
  rw [show 6 * x / 2 = 3 * x by ring, Real.sin_three_mul, hs]; push_cast; ring

include hu

theorem rat_sin_alpha' : ∃ q : ℚ, Real.sin (((Real.pi - 2 * (6 * x)) / 3) / 2) = q := by
  refine ⟨(1 - 2 * s ^ 2) / 2 - s * u, ?_⟩
  have e : ((Real.pi - 2 * (6 * x)) / 3) / 2 = Real.pi / 6 - 2 * x := by ring
  rw [e, Real.sin_sub, Real.sin_pi_div_six, Real.cos_pi_div_six, Real.cos_two_mul, Real.sin_two_mul]
  have hc2 := cos_sq_eq x s hs
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have : Real.sqrt 3 / 2 * (2 * Real.sin x * Real.cos x) = s * u := by
    rw [hs]; push_cast; rw [← hu]; ring
  rw [mul_sub, this, hc2]; push_cast; ring

theorem rat_sqrt3_sin6 : ∃ q : ℚ, Real.sqrt 3 * Real.sin (6 * x) = q := by
  refine ⟨2 * (3 * s - 4 * s ^ 3) * (u * (1 - 4 * s ^ 2)), ?_⟩
  have hc2 := cos_sq_eq x s hs
  have e6 : Real.sin (6 * x) = 2 * Real.sin (3 * x) * Real.cos (3 * x) := by
    rw [show 6 * x = 2 * (3 * x) by ring, Real.sin_two_mul]
  have e3 : Real.sqrt 3 * Real.cos (3 * x) = u * (1 - 4 * (s : ℝ) ^ 2) := by
    rw [Real.cos_three_mul]
    have : Real.sqrt 3 * (4 * Real.cos x ^ 3 - 3 * Real.cos x)
        = (Real.sqrt 3 * Real.cos x) * (4 * Real.cos x ^ 2 - 3) := by ring
    rw [this, hu, hc2]; ring
  rw [e6, Real.sin_three_mul, hs]
  have : Real.sqrt 3 * (2 * (3 * (s : ℝ) - 4 * s ^ 3) * Real.cos (3 * x))
      = 2 * (3 * (s : ℝ) - 4 * s ^ 3) * (Real.sqrt 3 * Real.cos (3 * x)) := by ring
  rw [this, e3]; push_cast; ring

end rat

theorem core26 (x : ℝ) (hx0 : 0 < x) (hx1 : x < Real.pi / 72) (s u : ℚ) (hs : Real.sin x = s)
    (hu : Real.sqrt 3 * Real.cos x = u) (T : Tri) (hT : HasAngles T (6 * x) (6 * x) (Real.pi - 2 * (6 * x))) :
    SixShapes T := by
  have hpi := Real.pi_pos
  set α := 6 * x with hα
  have h0 : 0 < α := by rw [hα]; linarith
  have h1 : α < Real.pi / 12 := by rw [hα]; linarith
  have h13 : α < Real.pi / 3 := by linarith
  -- triple 1
  have p0 : PrintedConcl T α α (Real.pi - 2 * α) := by
    obtain ⟨T', hc, e0, e1, e2⟩ := hT.canon
    exact ⟨T', e0, e1, e2, 1, Erdos634.Laczkovich9.selfDissection T', by
      show T'.carrier = T.carrier; exact hc, Erdos634.Geometry.Tri.Congruent.refl _⟩
  -- triple 2 (altitude)
  have p1 : PrintedConcl T α (Real.pi / 2 - α) (Real.pi / 2) := by
    obtain ⟨T', hc, e0, e1, e2⟩ := hT.canon
    have hiso : dist (T'.pts 2) (T'.pts 0) = dist (T'.pts 2) (T'.pts 1) :=
      iso_apex2 T' (by rw [e0, e1]) (by rw [e2]; intro h; linarith)
    obtain ⟨D, hDt, hDm⟩ := Erdos634.Laczkovich9.isosceles_split T' hiso
    obtain ⟨a0, a1, a2⟩ := Erdos634.Laczkovich9.isosceles_split_angles T' hiso
    have ha : T'.angleAt 0 = α := e0
    refine ⟨permT (Erdos634.Laczkovich9.halfTri0 T') (Equiv.swap 1 2), ?_, ?_, ?_, 2, D, ?_, ?_⟩
    · rw [vang_permT, show (Equiv.swap (1 : Fin 3) 2) 0 = 0 by decide]
      show (Erdos634.Laczkovich9.halfTri0 T').angleAt 0 = α
      rw [a0, ha]
    · rw [vang_permT, show (Equiv.swap (1 : Fin 3) 2) 1 = 2 by decide]
      show (Erdos634.Laczkovich9.halfTri0 T').angleAt 2 = _
      rw [a2, ha]
    · rw [vang_permT, show (Equiv.swap (1 : Fin 3) 2) 2 = 1 by decide]
      exact a1
    · rw [hDt, hc]
    · rw [hDm]; exact Erdos634.Geometry.Tri.congruent_relabel _ _
  -- triple 3 (Theorem 2.3)
  have p2 : PrintedConcl T α (2 * α) (Real.pi - 3 * α) :=
    thm23_printed α h0 h13 (rat_cos6 x s hs) T hT
  -- triple 4 (Theorem 2.4)
  have p3 : PrintedConcl T α ((Real.pi - 3 * α) / 2) ((Real.pi + α) / 2) :=
    Erdos634.LaczL35.thm24_printed α _ _ h0 h13 (by
      obtain ⟨q, hq⟩ := rat_sin_half x s hs; exact ⟨q, hq⟩) rfl rfl T (Or.inl hT)
  -- triple 5 (Theorem 2.4 with α')
  have p4 : PrintedConcl T (Real.pi / 3 - 2 * α / 3) α (2 * Real.pi / 3 - α / 3) := by
    have hα'0 : 0 < (Real.pi - 2 * α) / 3 := by linarith
    have hα'1 : (Real.pi - 2 * α) / 3 < Real.pi / 3 := by linarith
    have e1 : α = (Real.pi - 3 * ((Real.pi - 2 * α) / 3)) / 2 := by ring
    have e2 : Real.pi - 2 * α = 3 * ((Real.pi - 2 * α) / 3) := by ring
    have hT' : HasAngles T ((Real.pi - 3 * ((Real.pi - 2 * α) / 3)) / 2) ((Real.pi - 3 * ((Real.pi - 2 * α) / 3)) / 2)
        (3 * ((Real.pi - 2 * α) / 3)) := by
      obtain ⟨σ, a0, a1, a2⟩ := hT
      exact ⟨σ, a0.trans e1, a1.trans e1, a2.trans e2⟩
    have := Erdos634.LaczL35.thm24_printed ((Real.pi - 2 * α) / 3) _ _ hα'0 hα'1 (by
      obtain ⟨q, hq⟩ := rat_sin_alpha' x s u hs hu; exact ⟨q, hq⟩) rfl rfl T
      (Or.inr (Or.inr (Or.inl hT')))
    have ea : (Real.pi - 2 * α) / 3 = Real.pi / 3 - 2 * α / 3 := by ring
    have eb : (Real.pi - 3 * ((Real.pi - 2 * α) / 3)) / 2 = α := e1.symm
    have ec : (Real.pi + (Real.pi - 2 * α) / 3) / 2 = 2 * Real.pi / 3 - α / 3 := by ring
    rw [eb, ec, ea] at this
    exact this
  -- triple 6 (Theorem 2.5)
  have p5 : PrintedConcl T α (Real.pi / 3 - α) (2 * Real.pi / 3) :=
    Erdos634.LaczL35.thm25_printed α _ _ h0 h13 (by
      obtain ⟨q, hq⟩ := rat_sqrt3_sin6 x s u hs hu; exact ⟨q, hq⟩) (rat_cos6 x s hs) rfl rfl T (Or.inl hT)
  refine ⟨sixX α, sixY α, sixZ α, ?_, six_distinct α h0 h1⟩
  intro i
  fin_cases i
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5

end Erdos634.Laczkovich9w

#print axioms Erdos634.Laczkovich9w.core26
