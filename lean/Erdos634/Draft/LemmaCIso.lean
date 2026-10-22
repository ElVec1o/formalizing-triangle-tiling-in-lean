-- Draft/LemmaCIso.lean — Lemma C, isosceles tile: an irrational-angle isosceles tile tiling a
-- triangle ABC forces ABC ~ T (`SimilarTM`).  No lattice/F2 needed: the two-value corner sum and
-- irrationality force the corner totals (2,1).  Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.Draft.LemmaCSimilar

open scoped Classical
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.LemmaCFigures

namespace Erdos634.Draft.LemmaCIso

/-- Two-value analogue of `corner_figure`. -/
theorem corner_fig2 {N : ℕ} (D : CongruentDissection N) (a b : ℝ)
    (hmod : ∀ k : Fin 3, cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2)) = a
      ∨ cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2)) = b)
    (hab : a ≠ b) (ha0 : 0 < a) (hb0 : 0 < b) (haπ : a < Real.pi) (hbπ : b < Real.pi) (k : Fin 3) :
    D.target.pts k ∈ cornerPts D.toDissection ∧
    (({i | (D.tile i).localAngle (D.target.pts k) = a} : Finset (Fin N)).card : ℝ) * a
      + (({i | (D.tile i).localAngle (D.target.pts k) = b} : Finset (Fin N)).card : ℝ) * b
      = cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) ∧
    1 ≤ ({i | (D.tile i).localAngle (D.target.pts k) = a} : Finset (Fin N)).card
      + ({i | (D.tile i).localAngle (D.target.pts k) = b} : Finset (Fin N)).card := by
  have hpi := Real.pi_pos
  set x0 := cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) with hx0
  set x1 := cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) with hx1
  set x2 := cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) with hx2
  have hxab : ∀ y, (y = x0 ∨ y = x1 ∨ y = x2) → y = a ∨ y = b := by
    intro y hy
    rcases hy with rfl | rfl | rfl
    · exact hmod 0
    · exact hmod 1
    · exact hmod 2
  have hvals : ∀ i, (D.tile i).localAngle (D.target.pts k) ∈ ({a, b, Real.pi, 0} : Finset ℝ) := by
    intro i
    have hmem := congruentDissection_localAngle_mem_all D x0 x1 x2 rfl rfl rfl (D.target.pts k) i
    have h2 := Erdos634.Geometry.Dissection.localAngle_ne_two_pi_of_not_mem_interior
      (D.toDissection.target_vertex_not_interior_tile k i)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
    rcases hmem with h | h | h | h | h | h
    · rcases hxab _ (Or.inl rfl) with e | e <;> [exact Or.inl (h.trans e); exact Or.inr (Or.inl (h.trans e))]
    · rcases hxab _ (Or.inr (Or.inl rfl)) with e | e <;> [exact Or.inl (h.trans e); exact Or.inr (Or.inl (h.trans e))]
    · rcases hxab _ (Or.inr (Or.inr rfl)) with e | e <;> [exact Or.inl (h.trans e); exact Or.inr (Or.inl (h.trans e))]
    · exact Or.inr (Or.inr (Or.inl h))
    · exact absurd h h2
    · exact Or.inr (Or.inr (Or.inr h))
  have hsumv := VertexFigureReal.sum_by_value ({a, b, Real.pi, 0} : Finset ℝ)
    (fun i => (D.tile i).localAngle (D.target.pts k)) hvals
  rw [show ({a, b, Real.pi, 0} : Finset ℝ) = insert a (insert b (insert Real.pi {0})) from rfl] at hsumv
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hab, haπ.ne, ha0.ne'⟩),
      Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hbπ.ne, hb0.ne'⟩),
      Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hpi.ne'),
      Finset.sum_singleton] at hsumv
  beta_reduce at hsumv
  have hθ := Erdos634.VertexFigureReal.corner_angle_sum D.toDissection k
  have hθlt := Erdos634.RouteOneVertexKill.cornerAngle_lt_pi D.target k
  have hθpos := Erdos634.MarchFlank.cornerAngle_pos D.target k
  set cα := (({i | (D.tile i).localAngle (D.target.pts k) = a} : Finset (Fin N)).card : ℝ) with hca
  set cβ := (({i | (D.tile i).localAngle (D.target.pts k) = b} : Finset (Fin N)).card : ℝ) with hcb
  set cπ := (({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card : ℝ) with hcp
  have hc0 : 0 ≤ cα := Nat.cast_nonneg _
  have hc1 : 0 ≤ cβ := Nat.cast_nonneg _
  have hcπ0 : cπ = 0 := by
    by_contra hne
    have : 1 ≤ cπ := by
      have : (({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card) ≠ 0 := by
        intro h; apply hne; simp [cπ, h]
      exact Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr this)
    nlinarith [mul_nonneg hc0 ha0.le, mul_nonneg hc1 hb0.le]
  rw [hcπ0] at hsumv
  have hF : cα * a + cβ * b = cornerAngle (D.target.pts (k + 1)) (D.target.pts k)
      (D.target.pts (k + 2)) := by linarith
  have hFpos : 0 < cα * a + cβ * b := by rw [hF]; exact hθpos
  have hsum1 : 1 ≤ ({i | (D.tile i).localAngle (D.target.pts k) = a} : Finset (Fin N)).card
      + ({i | (D.tile i).localAngle (D.target.pts k) = b} : Finset (Fin N)).card := by
    by_contra hlt
    have h0 : ({i | (D.tile i).localAngle (D.target.pts k) = a} : Finset (Fin N)).card = 0 := by omega
    have h1 : ({i | (D.tile i).localAngle (D.target.pts k) = b} : Finset (Fin N)).card = 0 := by omega
    have e0 : cα = 0 := by simp [cα, h0]
    have e1 : cβ = 0 := by simp [cβ, h1]
    rw [e0, e1] at hFpos; simp at hFpos
  refine ⟨?_, hF, hsum1⟩
  have : ∃ i, (D.tile i).localAngle (D.target.pts k) = a ∨ (D.tile i).localAngle (D.target.pts k) = b := by
    by_contra hno
    push Not at hno
    have hz : ∀ (θ : ℝ), (∀ i, (D.tile i).localAngle (D.target.pts k) ≠ θ) →
        ({i | (D.tile i).localAngle (D.target.pts k) = θ} : Finset (Fin N)).card = 0 := by
      intro θ h; simp [h]
    have := hz a (fun i => (hno i).1)
    have := hz b (fun i => (hno i).2)
    omega
  obtain ⟨i, hi⟩ := this
  have hne : ∀ θ, (D.tile i).localAngle (D.target.pts k) = θ → 0 < θ → θ < Real.pi →
      D.target.pts k ∈ cornerPts D.toDissection := by
    intro θ h h0 hpi'
    obtain ⟨m, hm⟩ := vertex_of_localAngle_corner (D.tile i) h h0.ne' hpi'.ne (by linarith)
    rw [← hm]; exact mem_cornerPts D.toDissection i m
  rcases hi with h | h
  · exact hne a h ha0 haπ
  · exact hne b h hb0 hbπ


theorem iso_arith (a b : ℝ) (hb : 2 * a + b = Real.pi) (hirr : IrrPi a) (m n : ℤ)
    (h : (m : ℝ) * a + (n : ℝ) * b = 0) : m = 0 ∧ n = 0 := by
  have hpi := Real.pi_pos
  have h2 : ((m : ℝ) - 2 * n) * a + (n : ℝ) * Real.pi = 0 := by
    have : b = Real.pi - 2 * a := by linarith
    rw [this] at h; linarith
  by_cases hm : (m : ℝ) - 2 * n = 0
  · rw [hm] at h2
    have hn : (n : ℝ) = 0 := by
      rcases mul_eq_zero.mp (by linarith : (n : ℝ) * Real.pi = 0) with h | h
      · exact h
      · exact absurd h hpi.ne'
    have hn' : n = 0 := by exact_mod_cast hn
    refine ⟨?_, hn'⟩
    have : (m : ℝ) = 0 := by rw [hn] at hm; linarith
    exact_mod_cast this
  · exfalso
    apply hirr
    refine ⟨(-(n : ℚ)) / ((m : ℚ) - 2 * n), ?_⟩
    push_cast
    have hm' : ((m : ℝ) - 2 * n) ≠ 0 := hm
    rw [div_mul_eq_mul_div, eq_div_iff hm']
    linarith

/-- `f = g ∘ swap i j` for two functions with one exceptional value each. -/
theorem swap_match (f g : Fin 3 → ℝ) (a b : ℝ) (i j : Fin 3)
    (hf : f i = b ∧ ∀ k, k ≠ i → f k = a) (hg : g j = b ∧ ∀ k, k ≠ j → g k = a) :
    ∀ k, f k = g (Equiv.swap i j k) := by
  intro k
  by_cases hki : k = i
  · subst hki; rw [Equiv.swap_apply_left, hf.1, hg.1]
  · by_cases hkj : k = j
    · subst hkj
      rw [Equiv.swap_apply_right, hf.2 _ hki]
      have : k ≠ i := hki
      exact (hg.2 i (fun h => hki h.symm)).symm
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj, hf.2 _ hki, hg.2 _ hkj]


theorem iso_similar {N : ℕ} (D : CongruentDissection N) (p q r : Fin 3)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (heq : D.model.angleAt p = D.model.angleAt q)
    (hirr : ∃ i, IrrPi (D.model.angleAt i)) : SimilarTM D := by
  have hpi := Real.pi_pos
  have key : ∀ p q r k : Fin 3, p ≠ q → p ≠ r → q ≠ r → k = p ∨ k = q ∨ k = r := by decide
  have hall : ∀ k, k = p ∨ k = q ∨ k = r := fun k => key p q r k hpq hpr hqr
  have huniv : (Finset.univ : Finset (Fin 3)) = {p, q, r} := by
    ext k; simp [hall k]
  have hsumA : D.model.angleAt 0 + D.model.angleAt 1 + D.model.angleAt 2 = Real.pi :=
    Erdos634.Geometry.cornerAngle_sum D.model
  have hpqr : D.model.angleAt p + D.model.angleAt q + D.model.angleAt r = Real.pi := by
    have h := Fin.sum_univ_three (fun k => D.model.angleAt k)
    rw [huniv, Finset.sum_insert (by simp [hpq, hpr]), Finset.sum_insert (by simp [hqr]),
      Finset.sum_singleton] at h
    linarith
  set a := D.model.angleAt p with ha
  set b := D.model.angleAt r with hb
  have h2ab : 2 * a + b = Real.pi := by rw [← heq] at hpqr; linarith
  have hirra : IrrPi a := by
    obtain ⟨i, hi⟩ := hirr
    rcases hall i with rfl | rfl | rfl
    · exact hi
    · rw [← heq] at hi; exact hi
    · rintro ⟨s, hs⟩
      apply hi
      refine ⟨1 - 2 * s, ?_⟩
      push_cast
      have : b = Real.pi - 2 * a := by linarith
      rw [show D.model.angleAt i = b from rfl, this, hs]; ring
  have hposA : ∀ k, 0 < D.model.angleAt k := fun k => Erdos634.MarchFlank.cornerAngle_pos D.model k
  have hltA : ∀ k, D.model.angleAt k < Real.pi := fun k => Erdos634.RouteOneVertexKill.cornerAngle_lt_pi D.model k
  have ha0 := hposA p
  have hb0 := hposA r
  have haπ := hltA p
  have hbπ := hltA r
  have hab : a ≠ b := by
    intro h
    apply hirra
    refine ⟨1 / 3, ?_⟩
    push_cast
    linarith
  have hmod : ∀ k : Fin 3, cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2)) = a
      ∨ cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2)) = b := by
    intro k
    rcases hall k with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inl heq.symm
    · exact Or.inr rfl
  have hcor := fun k => corner_fig2 D a b hmod hab ha0 hb0 haπ hbπ k
  have e0 := (hcor 0).2
  have e1 := (hcor 1).2
  have e2 := (hcor 2).2
  simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl,
    show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl,
    show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl] at e0 e1 e2
  have hT := Erdos634.Geometry.cornerAngle_sum D.target
  set A : Fin 3 → ℕ := fun k => ({i | (D.tile i).localAngle (D.target.pts k) = a} : Finset (Fin N)).card
    with hA
  set B : Fin 3 → ℕ := fun k => ({i | (D.tile i).localAngle (D.target.pts k) = b} : Finset (Fin N)).card
    with hB
  have hreal : ((A 0 + A 1 + A 2 : ℕ) : ℝ) * a + ((B 0 + B 1 + B 2 : ℕ) : ℝ) * b = Real.pi := by
    push_cast
    have := e0.1; have := e1.1; have := e2.1
    simp only [hA, hB]
    linarith [e0.1, e1.1, e2.1]
  have hz := iso_arith a b h2ab hirra ((A 0 + A 1 + A 2 : ℕ) - 2 : ℤ) ((B 0 + B 1 + B 2 : ℕ) - 1 : ℤ)
    (by push_cast; nlinarith [hreal])
  have hA2 : A 0 + A 1 + A 2 = 2 := by have := hz.1; omega
  have hB1 : B 0 + B 1 + B 2 = 1 := by have := hz.2; omega
  have hp0 : 1 ≤ A 0 + B 0 := e0.2
  have hp1 : 1 ≤ A 1 + B 1 := e1.2
  have hp2 : 1 ≤ A 2 + B 2 := e2.2
  have fin3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  have hpick : ∃ i, B i = 1 ∧ ∀ k, k ≠ i → B k = 0 := by
    have : (B 0 = 1 ∧ B 1 = 0 ∧ B 2 = 0) ∨ (B 0 = 0 ∧ B 1 = 1 ∧ B 2 = 0)
        ∨ (B 0 = 0 ∧ B 1 = 0 ∧ B 2 = 1) := by omega
    rcases this with h | h | h
    · refine ⟨0, h.1, fun k hk => ?_⟩
      rcases fin3 k with rfl | rfl | rfl
      · exact absurd rfl hk
      · exact h.2.1
      · exact h.2.2
    · refine ⟨1, h.2.1, fun k hk => ?_⟩
      rcases fin3 k with rfl | rfl | rfl
      · exact h.1
      · exact absurd rfl hk
      · exact h.2.2
    · refine ⟨2, h.2.2, fun k hk => ?_⟩
      rcases fin3 k with rfl | rfl | rfl
      · exact h.1
      · exact h.2.1
      · exact absurd rfl hk
  obtain ⟨i, hi1, hi0⟩ := hpick
  have hAk : ∀ k, A k + B k = 1 := by
    intro k; rcases fin3 k with rfl | rfl | rfl <;> omega
  have hθ : ∀ k, (A k : ℝ) * a + (B k : ℝ) * b = D.target.angleAt k := by
    intro k; rcases fin3 k with rfl | rfl | rfl
    · exact e0.1
    · exact e1.1
    · exact e2.1
  have hf : D.target.angleAt i = b ∧ ∀ k, k ≠ i → D.target.angleAt k = a := by
    refine ⟨?_, fun k hk => ?_⟩
    · rw [← hθ i]; have := hAk i; have : A i = 0 := by omega
      rw [this, hi1]; simp
    · rw [← hθ k]; have := hAk k; have h0 := hi0 k hk
      have : A k = 1 := by omega
      rw [this, h0]; simp
  have hg : D.model.angleAt r = b ∧ ∀ k, k ≠ r → D.model.angleAt k = a := by
    refine ⟨rfl, fun k hk => ?_⟩
    rcases hall k with rfl | rfl | rfl
    · rfl
    · exact heq.symm
    · exact absurd rfl hk
  have hτ := swap_match (fun k => D.target.angleAt k) (fun k => D.model.angleAt k) a b i r hf hg
  obtain ⟨μ, hμ⟩ := Erdos634.Draft.LemmaCSimilar.sides_of_angles D.target D.model (Equiv.swap i r) hτ
  exact ⟨μ, Equiv.swap i r, fun k => ⟨hτ k, hμ k⟩⟩

end Erdos634.Draft.LemmaCIso

#print axioms Erdos634.Draft.LemmaCIso.iso_similar
