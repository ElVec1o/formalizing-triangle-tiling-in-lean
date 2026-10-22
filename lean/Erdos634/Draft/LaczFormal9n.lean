import Erdos634.Draft.LaczFormalL24Disj

/-!
# Laczkovich DM 140 (1995), Theorem 2.3: the hull-of-three-points calculus (Fig. 3, cover part)

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.3, Fig. 3), Beeson, Beeson-Zhang, Zhang.  Formalization debt,
not /goal progress.

`H P Q R` is the set of convex combinations of three points of the plane (degenerate allowed).  Two decomposition lemmas:
`H_fan` (a point `B` with all barycentric weights positive cuts `H X Y Z` into the three cones from `B`) and `H_cev`
(a point on side `YZ` cuts `H X Y Z` into two).  They are used in `LaczFormal9o` to prove the cover of the target triangle
by the five pieces of Fig. 3 without any sign case analysis on the pieces themselves.
-/

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

namespace Erdos634.Laczkovich9n

/-- Convex combinations of three points. -/
def H (P Q R : Plane) : Set Plane :=
  {z | ∃ s t u : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ 0 ≤ u ∧ s + t + u = 1 ∧ z = s • P + t • Q + u • R}

theorem H_mk {P Q R : Plane} (s t u : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hu : 0 ≤ u) (h : s + t + u = 1) :
    s • P + t • Q + u • R ∈ H P Q R := ⟨s, t, u, hs, ht, hu, h, rfl⟩

theorem H_left (P Q R : Plane) : P ∈ H P Q R := ⟨1, 0, 0, by norm_num, le_refl _, le_refl _, by norm_num, by simp⟩
theorem H_mid (P Q R : Plane) : Q ∈ H P Q R := ⟨0, 1, 0, le_refl _, by norm_num, le_refl _, by norm_num, by simp⟩
theorem H_right (P Q R : Plane) : R ∈ H P Q R := ⟨0, 0, 1, le_refl _, le_refl _, by norm_num, by norm_num, by simp⟩

theorem H_rot (P Q R : Plane) : H P Q R ⊆ H Q R P := by
  rintro z ⟨s, t, u, hs, ht, hu, hsum, rfl⟩
  exact ⟨t, u, s, ht, hu, hs, by linarith, by module⟩

theorem H_swap (P Q R : Plane) : H P Q R ⊆ H P R Q := by
  rintro z ⟨s, t, u, hs, ht, hu, hsum, rfl⟩
  exact ⟨s, u, t, hs, hu, ht, by linarith, by module⟩

theorem H_convex (P Q R : Plane) : Convex ℝ (H P Q R) := by
  rintro x ⟨s, t, u, hs, ht, hu, hsum, rfl⟩ y ⟨s', t', u', hs', ht', hu', hsum', rfl⟩ a b ha hb hab
  refine ⟨a * s + b * s', a * t + b * t', a * u + b * u', by positivity, by positivity, by positivity, ?_, ?_⟩
  · have : a * (s + t + u) + b * (s' + t' + u') = 1 := by rw [hsum, hsum']; linarith
    linarith
  · module

theorem H_sub_convex {S : Set Plane} (hS : Convex ℝ S) {P Q R : Plane} (hP : P ∈ S) (hQ : Q ∈ S) (hR : R ∈ S) :
    H P Q R ⊆ S := by
  rintro z ⟨s, t, u, hs, ht, hu, hsum, rfl⟩
  have := hS.sum_mem (t := (Finset.univ : Finset (Fin 3))) (w := ![s, t, u]) (z := ![P, Q, R])
    (by intro i _; fin_cases i <;> simp [hs, ht, hu]) (by simp [Fin.sum_univ_three, hsum])
    (by intro i _; fin_cases i <;> simp [hP, hQ, hR])
  simpa [Fin.sum_univ_three] using this

theorem tri_sub_H (T : Tri) : T.carrier ⊆ H (T.pts 0) (T.pts 1) (T.pts 2) := by
  refine convexHull_min ?_ (H_convex _ _ _)
  rintro _ ⟨k, rfl⟩
  fin_cases k
  · exact H_left _ _ _
  · exact H_mid _ _ _
  · exact H_right _ _ _

theorem H_sub_tri (T : Tri) : H (T.pts 0) (T.pts 1) (T.pts 2) ⊆ T.carrier :=
  H_sub_convex T.convex (subset_convexHull ℝ _ ⟨0, rfl⟩) (subset_convexHull ℝ _ ⟨1, rfl⟩)
    (subset_convexHull ℝ _ ⟨2, rfl⟩)

theorem vm (T : Tri) (k : Fin 3) : T.pts k ∈ T.carrier := subset_convexHull ℝ _ ⟨k, rfl⟩

/-- Cevian cut: `D = p Y + q Z` on the side `YZ`. -/
theorem H_cev {X Y Z D : Plane} {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : p + q = 1) (hD : D = p • Y + q • Z) :
    H X Y Z ⊆ H X Y D ∪ H X D Z := by
  rintro z ⟨s, t, u, hs, ht, hu, hsum, rfl⟩
  rcases le_total (u * p) (t * q) with h | h
  · -- in `H X Y D`: weights s, t - u p / q, u / q
    left
    refine ⟨s, t - u * p / q, u / q, hs, ?_, by positivity, ?_, ?_⟩
    · have : u * p / q ≤ t := by rw [div_le_iff₀ hq]; linarith
      linarith
    · field_simp; nlinarith
    · subst hD
      have hq' : q ≠ 0 := hq.ne'
      have e : u = (u / q) * q := by field_simp
      have e2 : u * p / q = (u / q) * p := by ring
      rw [e2]
      set w := u / q
      rw [e]
      module
  · right
    refine ⟨s, t / p, u - t * q / p, hs, by positivity, ?_, ?_, ?_⟩
    · have : t * q / p ≤ u := by rw [div_le_iff₀ hp]; linarith
      linarith
    · field_simp; nlinarith
    · subst hD
      have hp' : p ≠ 0 := hp.ne'
      have e : t = (t / p) * p := by field_simp
      have e2 : t * q / p = (t / p) * q := by ring
      rw [e2]
      set w := t / p
      rw [e]
      module

theorem rat_mul {x y m : ℝ} (hm : 0 < m) (h : x ≤ y / m) : x * m ≤ y := by
  have := mul_le_mul_of_nonneg_right h hm.le
  rwa [div_mul_cancel₀ _ hm.ne'] at this

/-- Fan cut from a point `B = l X + m Y + n Z` with all weights positive. -/
theorem H_fan {X Y Z B : Plane} {l m n : ℝ} (hl : 0 < l) (hm : 0 < m) (hn : 0 < n) (hsum : l + m + n = 1)
    (hB : B = l • X + m • Y + n • Z) : H X Y Z ⊆ H B X Y ∪ H B Y Z ∪ H B Z X := by
  rintro z ⟨s, t, u, hs, ht, hu, hz, rfl⟩
  have c1 : s / l ≤ t / m → s / l ≤ u / n → s • X + t • Y + u • Z ∈ H B Y Z := by
    intro h1 h2
    have e1 : s / l * m ≤ t := rat_mul hm h1
    have e2 : s / l * n ≤ u := rat_mul hn h2
    refine ⟨s / l, t - s / l * m, u - s / l * n, by positivity, by linarith, by linarith, ?_, ?_⟩
    · have : s / l * l = s := by field_simp
      nlinarith
    · subst hB
      have e : s = (s / l) * l := by field_simp
      set w := s / l
      rw [e]
      module
  have c2 : t / m ≤ u / n → t / m ≤ s / l → s • X + t • Y + u • Z ∈ H B Z X := by
    intro h1 h2
    have e1 : t / m * n ≤ u := rat_mul hn h1
    have e2 : t / m * l ≤ s := rat_mul hl h2
    refine ⟨t / m, u - t / m * n, s - t / m * l, by positivity, by linarith, by linarith, ?_, ?_⟩
    · have : t / m * m = t := by field_simp
      nlinarith
    · subst hB
      have e : t = (t / m) * m := by field_simp
      set w := t / m
      rw [e]
      module
  have c3 : u / n ≤ s / l → u / n ≤ t / m → s • X + t • Y + u • Z ∈ H B X Y := by
    intro h1 h2
    have e1 : u / n * l ≤ s := rat_mul hl h1
    have e2 : u / n * m ≤ t := rat_mul hm h2
    refine ⟨u / n, s - u / n * l, t - u / n * m, by positivity, by linarith, by linarith, ?_, ?_⟩
    · have : u / n * n = u := by field_simp
      nlinarith
    · subst hB
      have e : u = (u / n) * n := by field_simp
      set w := u / n
      rw [e]
      module
  rcases le_total (s / l) (t / m) with h12 | h12 <;> rcases le_total (s / l) (u / n) with h13 | h13 <;>
    rcases le_total (t / m) (u / n) with h23 | h23
  · exact Or.inl (Or.inr (c1 h12 h13))
  · exact Or.inl (Or.inr (c1 h12 h13))
  · exact Or.inl (Or.inr (c1 h12 (by linarith)))
  · exact Or.inl (Or.inl (c3 h13 h23))
  · exact Or.inr (c2 h23 h12)
  · exact Or.inr (c2 (by linarith) h12)
  · exact Or.inr (c2 h23 h12)
  · exact Or.inl (Or.inl (c3 h13 h23))

end Erdos634.Laczkovich9n

#print axioms Erdos634.Laczkovich9n.H_fan
#print axioms Erdos634.Laczkovich9n.H_cev
#print axioms Erdos634.Laczkovich9n.H_sub_convex
#print axioms Erdos634.Laczkovich9n.tri_sub_H
